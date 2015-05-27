structure VM =
struct
structure Scope :
          sig
              type t
              val empty: t
              val register: t -> string -> string -> t
              val add: t -> string -> t
              val find: t -> string -> string option
              val getId: t -> string -> int
              val findWithId: t -> string -> (string * int) option
          end
= struct
type t = (string * string) list
val empty = []

fun register scope name renamed = (name, renamed) :: scope
fun add scope name = register scope name (Id.f name)

fun find [] key = NONE
  | find ((name:string, renamed)::scope) (key:string) =
    if name = key
    then SOME renamed
    else find scope key

fun getId scope (key:string) = let
    fun aux ((_, renamed:string)::scope) i =
      if key = renamed
      then i
      else aux scope (i + 1)
      | aux [] _ = raise Fail "cannot find ID"
in
    aux (List.rev scope) 0
    
end

fun findWithId scope key = let
    val renamed = find scope key
    val id = Option.map (getId scope) renamed
    fun conj (SOME x) (SOME y) = SOME (x, y)
      | conj _ _ = NONE
in
    conj renamed id
end
end

datatype opcode
  = Not
  | Add
  | Eq
  | Gt
  | Jump of string
  | Jtrue of string
  | Call
  | Ret
  | Push of vmvalue
  | Pop
  | Lref of int
  | Lset of int
  | Gref of int
  | Gset of int
  | Nop

and vmvalue
  = Int of int
  | Bool of bool
  | Lambda of opcode list


fun dumpCode Not = "Not"
  | dumpCode Add = "Add"
  | dumpCode Eq =  "Eq"
  | dumpCode Gt = "Gt"
  | dumpCode (Jump x) = "Jump " ^ x
  | dumpCode (Jtrue x) = "Jtrue " ^ x
  | dumpCode Call = "Call" 
  | dumpCode Ret = "Ret"
  | dumpCode (Push v) = "Push " ^ (dumpValue v)
  | dumpCode Pop = "Pop"
  | dumpCode (Lref i) = "Lref " ^ (Int.toString i)
  | dumpCode (Lset i) = "Lset " ^ (Int.toString i)
  | dumpCode (Gref i) = "Gref " ^ (Int.toString i)
  | dumpCode (Gset i) = "Gset " ^ (Int.toString i)
  | dumpCode Nop = "Nop"
and dumpValue (Int i) = Int.toString i
  | dumpValue (Bool b) = Bool.toString b
  | dumpValue (Lambda ops) = ""

structure BaseBlock =
struct

type t = string * opcode list

fun new label = (label, [])
fun add (label, ops) opcode = (label, opcode::ops)
fun gen (label, ops) = (label, List.rev ops)
fun dump (label, ops) = let
    val ops = String.concatWith "\n" (List.map (fn x => "  " ^ (dumpCode x)) ops)
in
    label ^ ":\n" ^ ops
end
end

structure Block =
struct
type t = BaseBlock.t list
fun new label = [BaseBlock.new label]
fun add bs b = b::bs
fun addCode (bb::bbs) b = (BaseBlock.add bb b)::bbs
  | addCode [] b = raise Fail "BaseBlock nil"
fun gen t = List.rev (List.map BaseBlock.gen t)

fun dump bs = String.concatWith "\n" (List.map BaseBlock.dump bs)
end


structure CodeGen = struct
type t = Block.t list * Scope.t list
fun new () = ([Block.new (Id.f "main")], [Scope.empty])

fun pushBlock (bs, ss) b = (b::bs, ss)
fun popBlock(b::bs, ss) = (bs, ss)
  | popBlock ([], ss) = raise Fail "block nil"

fun pushBaseBlock (b::bs, ss) bb = ((Block.add b bb)::bs, ss)
  | pushBaseBlock ([], _) _ = raise Fail "block nil"


fun pushScope (bs, ss) s =  (bs, s::ss)
fun popScope (bs, s::ss) =  (bs, ss)
  | popScope (bs, []) = raise Fail "scope nil"
fun isGlobalScope (bs, ss) = (List.length ss) = 1

fun intern (bs, s::ss) name = let
    val renamed = Id.f name
    val s = Scope.register s name renamed
    val i = Scope.getId s renamed
in
    ((bs, s::ss), i)
end
  | intern (bs, []) name = raise Fail "scope nil"

fun findLocalWithId (bs, []) _ = raise Fail "scope nil" 
  | findLocalWithId (bs, s::ss) key = Scope.findWithId s key

fun findGlobalWithId (bs, ss) key = let
    fun aux [] = raise Fail "scope nil"
      | aux [s] = Scope.findWithId s key
      | aux (s::ss) = aux ss
in
    aux ss
end

fun add (b::bs, ss) code = ((Block.addCode b code)::bs, ss)
  | add ([], ss) code = raise Fail "block nil"

fun gen (bs, ss) = List.rev (List.map Block.gen bs)

fun dump bs = String.concat (List.map Block.dump bs)
end




structure A = AST
structure C = CodeGen

exception Type


fun doMonoOp gen mop x = let
    val gen = compile gen x
in
    case mop of
        A.Not => C.add gen Not    
end

and doBinOp gen bop x y = let
    val gen = compile gen x
    val gen = compile gen y
in
    case bop of
        A.Equal => C.add gen Eq
      | A.GreaterThan => C.add gen Gt
      | A.Add => C.add gen Add
        
end

and doBind gen (A.Var name) value = let
(* :TODO: interreferencial defiinition *)
    val (gen, id) = C.intern gen name
    val gen = compile gen value
    val gen =     if C.isGlobalScope gen
                  then C.add gen (Gset id)
                  else C.add gen (Lset id)
    val gen = C.add gen (Push (Bool true))
in
    gen
end
  | doBind _ _ _ = raise Type


and doVar gen name =
    if C.isGlobalScope gen
    then case C.findGlobalWithId gen name of
                    SOME(_, id) => C.add gen (Gref id)
                  (* :TODO: interreferencial defiinition *)
                  | NONE => raise Fail "Unknown var"
    else case C.findLocalWithId gen name of
        SOME(_, id) => C.add gen (Lref id)
      | NONE => case C.findGlobalWithId gen name of
                    SOME(_, id) => C.add gen (Gref id)
                  (* :TODO: interreferencial defiinition *)
                  | NONE => raise Fail "Unknown var"

and doIf gen cnd thn els = let
    val thenLabel = (Id.f "then")
    val elseLabel = (Id.f "else")
    val endLabel = (Id.f "end")
    val gen = compile gen cnd
    val gen = C.add gen (Jtrue thenLabel)
    val gen = C.add gen (Jump elseLabel)
    val gen = C.pushBaseBlock gen (BaseBlock.new thenLabel)
    val gen = compile gen thn
    val gen = C.add gen (Jump endLabel)
    val gen = C.pushBaseBlock gen (BaseBlock.new elseLabel)
    val gen = compile gen els
    val gen = C.add gen (Jump endLabel)
    val gen = C.pushBaseBlock gen (BaseBlock.new endLabel)
in
    gen
end

and doConst gen x = C.add gen (Push x)

and doLambda gen params body = let
    val gen = C.pushScope gen Scope.empty
    val f   = (Block.new (Id.f "lambda"))
    val gen = C.pushBlock gen f
    val gen = List.foldl (fn (A.Var(p), gen) => let val (gen, id) = C.intern gen p
                                            in gen end)
                         gen params
    val gen = compile gen body
    val gen = C.add gen Ret
    (* :TODO: local variable handling *)
    val gen = C.popScope gen
in
    gen
end

and doCall gen lambda args = let
    val gen = List.foldl (fn (ast, gen) => compile gen ast) gen args
    val gen = compile gen lambda
    val gen = C.add gen Call
in
    gen
end

and doProgn gen [exp] = compile gen exp
  | doProgn gen (exp::exps) = let
    val gen = compile gen exp
    val gen = C.add gen Pop
in
    doProgn gen exps
end
  | doProgn gen [] = raise Fail "progn invalid"

and compile gen ast =
  case ast of
      A.MonoOp(monoop, x) => doMonoOp gen monoop x
    | A.BinOp(binop, x, y) => doBinOp gen binop x y
    | A.Bind(var, value) => doBind gen var value
    | A.If(cnd, thn, els) => doIf gen cnd thn els
    | A.Var(name) => doVar gen name
    | A.Lambda(params, body) => doLambda gen params body
    | A.Call(lambda, args) => doCall gen lambda args
    | A.Progn(exps) => doProgn gen exps
    | A.Int x => doConst gen (Int x)
    | A.Bool x => doConst gen (Bool x)
      

fun c ast = print(C.dump (C.gen (compile (CodeGen.new ()) ast)))

end
val _ = VM.c AST.fib
