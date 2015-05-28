structure VM =
struct
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
  | End

and vmvalue
    = Int of int
    | Bool of bool
    | Undefined
    | Lambda of string


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
  | dumpCode End = "End"
and dumpValue (Int i) = Int.toString i
  | dumpValue (Bool b) = Bool.toString b
  | dumpValue Undefined = "Undefined"
  | dumpValue (Lambda label) = "Lambda " ^ label




structure Compile =
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
(* Scope *)

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
(* BaseBlock *)

structure Block =
struct
type t = BaseBlock.t list
fun new label = [BaseBlock.new label]
fun add bs b:t = b::bs
fun addCode (bb::bbs) b = (BaseBlock.add bb b)::bbs
  | addCode [] b = raise Fail "BaseBlock nil"
fun gen t = List.rev (List.map BaseBlock.gen t)

fun dump bs = String.concatWith "\n" (List.map BaseBlock.dump bs)
end
(* Block *)


structure CodeGen =
struct
type t = {
    main: Block.t,
    fAcc: Block.t list,
    scopes: Scope.t list
}

fun new ()= {
    main = Block.new (Id.f "main"),
    fAcc = [],
    scopes = [Scope.empty]
}

fun pushFun ({main, fAcc, scopes}: t) f= {
    main = main,
    fAcc = f:: fAcc,
    scopes = scopes
}

fun swapMain ({main, fAcc, scopes}: t) newMain = ({
      main = newMain,
      fAcc = fAcc,
      scopes = scopes
  }, main)

fun pushBaseBlock ({main, fAcc, scopes}: t) bb = {
      main = Block.add main bb,
      fAcc = fAcc,
      scopes = scopes
  }


fun pushScope ({main, fAcc, scopes}: t) s =  {
    main = main,
    fAcc = fAcc,
    scopes = s::scopes
}

fun popScope ({scopes = [], ...}: t) = raise Fail "scope nil"
  | popScope ({main, fAcc, scopes = s::ss}: t) =  {
      main = main,
      fAcc = fAcc,
      scopes = ss
  }

fun isGlobalScope ({scopes, ...}: t) = (List.length scopes) = 1

fun intern ({scopes = [], ...}: t) name = raise Fail "scope nil"
  | intern ({main,  fAcc, scopes = s::ss}: t) name = let
    val renamed = Id.f name
    val s = Scope.register s name renamed
    val i = Scope.getId s renamed
in
    ({
        main = main,
        fAcc = fAcc,
        scopes = s::ss
    }, i)
end

fun findLocalWithId ({scopes = [], ...}: t) _ = raise Fail "scope nil" 
  | findLocalWithId ({scopes = s::ss, ...}: t) key = Scope.findWithId s key

fun findGlobalWithId ({scopes, ...}: t) key = let
    fun aux [] = raise Fail "scope nil"
      | aux [s] = Scope.findWithId s key
      | aux (s::ss) = aux ss
in
    aux scopes
end

fun add ({main, fAcc, scopes}:t) code = {
    main = (Block.addCode main code),
    fAcc = fAcc,
    scopes = scopes
}


fun gen ({main, fAcc, scopes = [_]}: t) = let
      val db = []
      val blocks = (Block.gen main) :: (List.map Block.gen fAcc)
      val buffer = Array.array(30, Nop)
      fun addCodes [] i = i
        | addCodes (code::codes) i =
            addCodes codes (i + 1) before Array.update(buffer, i, code)
      fun addBaseBlocks [] i db = (db, i)
        | addBaseBlocks ((label, bbs)::bs) i db = let
            val db = (label, i)::db
            val i = addCodes bbs i
        in
            addBaseBlocks bs i db
        end

      fun addBlocks [] i db = (db, i)
        | addBlocks (b::bs) i db = let
            val (db, i) = addBaseBlocks b i db
        in
            addBlocks bs i db
        end
      val (db, i) = addBlocks blocks 0 db
  in
      (buffer, db, i)
  end
 | gen  _ = raise Fail "ICE"

fun dump (buffer, db, i) = let
    val dumpLine = (fn (i, code, str) => str ^ ((Int.toString i) ^ "\t" ^ (dumpCode code)) ^ "\n")
    val codes = Array.foldli dumpLine  "" buffer
    val dbs = List.foldl (fn ((label, index), acc) => acc ^ (label ^ " " ^ (Int.toString index) ^ "\n")) "" db
in
    codes ^ dbs
end
end
(* CodeGen *)


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
    val label = (Id.f "lambda")
    val block   = (Block.new label)
    val (gen, main) = C.swapMain gen block
    val gen = List.foldl (fn (A.Var(p), gen) => let val (gen, id) = C.intern gen p
                                              in gen end)
                         gen params
    val gen = compile gen body
    val gen = C.add gen Ret
    (* :TODO: local variable handling *)
    val gen = C.popScope gen
    val (gen, block) = C.swapMain gen main
    val gen = C.pushFun gen block
    val gen = C.add gen (Push (Lambda label))
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
                           

fun c ast = let
    val gen = (compile (CodeGen.new ()) ast)
    val gen = C.add gen End
in
    gen
end
end
(* Compile *)


val STACK_SIZE = 16
val CONST_POOL_SIZE = 10

type ci = {
    fp: int,
    sp: int,
    pc: int
}

type vm = {
    stack: vmvalue array,
    sp: int ref,
    fp: int ref,
    pc: int ref,
    pool: vmvalue array,
    ci: ci list ref,
    labelDb: (string * int) list
}

exception Type
exception Exit

fun new () = {
    stack = Array.array(STACK_SIZE, Undefined),
    fp = ref 0,
    sp = ref 0,
    pc = ref 0,
    pool = Array.array(CONST_POOL_SIZE, Undefined),
    ci = ref [],
    labelDb = []
}

fun push ({stack, sp, ...}: vm) v = (
    Array.update(stack, (!sp), v);
    sp := (!sp) + 1
)

fun pop ({stack, sp, ...}: vm) = (
    Array.update(stack, !sp, Undefined); (* for debug *)
    sp := (!sp) - 1;
    Array.sub(stack, !sp)
)

fun addLabels ({stack, fp, sp, pc, pool, ci, labelDb}: vm) db = {
    stack = stack,
    fp = fp,
    sp = sp,
    pc = pc,
    pool = pool,
    ci = ci,
    labelDb = db @ labelDb
}
  

fun pushCi (vm as {ci, fp, sp, pc, ...}: vm) = 
  ci := {fp = !fp, sp = !sp, pc = !pc} :: (!ci)

fun popCi (vm as  {ci, fp, sp, pc, ...}: vm) = let
    val ({fp = cfp, sp = csp, pc = cpc}::tl) = !ci
in
    fp := cfp;
    sp := csp;
    pc := cpc
end

fun findLabel [] key = raise Fail "ICE"
  | findLabel ((label:string, index)::db) (key: string) =
    if key = label
    then index
    else findLabel db key

fun doOp (vm as {pool, stack, sp, pc, labelDb, ... } : vm) opcode =
  case opcode of
      Not => (case pop vm of
                 Bool x => push vm (Bool (not x))
               | _ => raise Type)
    | Add => (case (pop vm, pop vm) of
                 (Int x, Int y) => push vm (Int (x + y))
               | _ => raise Type)
    | Eq => (case (pop vm, pop vm) of
                (Int x, Int y) => push vm (Bool (x = y))
              | (Bool x, Bool y) => push vm (Bool (x = y))
              | _ => raise Type)
    | Gt => (case (pop vm, pop vm) of
                (Int x, Int y) => push vm (Bool (x < y))
              | _ => raise Type)
    | Jump label => pc := ((findLabel labelDb label) - 1)
    | Jtrue label => (case pop vm of
                         Bool true => pc := ((findLabel labelDb label) - 1)
                       | Bool false => ()
                       | _ => raise Type)
    | Call => (case (pop vm) of
                  Lambda label => pushCi vm before pc := ((findLabel labelDb label) - 1)
               | _ => raise Type)
    | Ret => popCi vm
    | Push v => push vm v
    | Pop => (pop vm;())
    | Lref i => push vm (Array.sub(stack, (!sp) - i))
    | Lset i =>  (Array.update(stack, (!sp) - i, pop vm)) before push vm (Bool true)
    | Gref i => push vm (Array.sub(pool, i))
    | Gset i =>  Array.update(pool, i, pop vm) before push vm (Bool true)
    | Nop => ()
    | End => raise Exit
                

fun run (vm as {pc, stack, ...} : vm) (obj as (ops, labelDb, opLen)) = let
    val vm = addLabels vm labelDb
    val len = Array.length ops
    fun aux () = if (!pc) < len
                 then (doOp vm (Array.sub(ops, !pc));
                       pc := (!pc) + 1;
                       aux ())
                      handle Exit => ()
                      handle _ => print (Compile.C.dump obj)
                 else ()
in
    aux ();
    stack
end
                                         
end
open VM

val _ = run (new ())
            (Array.fromList[
                  Push (Lambda "label"),
                  Gset 0,
                  Push (Int 1),
                  Push (Int 2),
                  Add
            ], [("label", 1)], 0)


