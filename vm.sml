structure AST =
struct

datatype monoop
  = Not

fun mopToString Not = "!"

datatype binop
  = Equal
  | GreaterThan
  | Add

fun bopToString Equal = "="
  | bopToString GreaterThan = ">"
  | bopToString Add = "+"

datatype t
  = Int of int
  | Bool of bool
  | MonoOp of monoop * t
  | BinOp of binop * t * t
  | Bind of t * t
  | If of t * t * t
  | Var of string
  | Lambda of t list * t
  | Call of t * t list
  | Progn of t list                  

fun toString (Int x) = Int.toString x
  | toString (Bool x) = Bool.toString x
  | toString (MonoOp(mop, x)) = "(" ^ (mopToString mop) ^ " " ^ (toString x) ^ ")"
  | toString (BinOp(bop, x, y)) = "(" ^ (bopToString bop) ^ " " ^ (toString x) ^ " " ^ (toString y) ^ ")"
  | toString (Bind(var, value)) = "(setf " ^ (toString var) ^ " " ^ (toString value) ^ ")"
  | toString (If(cnd, thn, els)) = "(if " ^ (toString cnd) ^
                                " " ^ (toString thn) ^
                                " " ^ (toString els) ^ ")"
  | toString (Var name) =  name
  | toString (Lambda(params, body)) = "(lambda (" ^ (String.concatWith " " (List.map toString params))
                                        ^ ") " ^ (toString body) ^ ")"
  | toString (Progn(exps)) = "(progn " ^ (String.concatWith " " (List.map toString exps)) ^ ")"

end


structure Interp =
struct

exception Type
exception Argument
exception Variable of string
structure A = AST

structure Scope: sig
    type t
    val empty: t
    val add: t -> string -> AST.t -> t
    val find: t -> string -> AST.t option
end =
struct
structure A = AST
type t = (string * AST.t) list
val empty = []
fun add scope name value = (name , value) :: scope
fun find [] key = NONE
  | find ((name:string, value)::xs) (key:string) = if name = key
                                      then SOME value
                                      else find xs key
end
structure Env: sig
    type t
    val empty: t
    val push: t -> Scope.t -> t
    val pop: t -> t
    val add: t -> string -> AST.t -> t
    val depth: t -> int
    val find: t -> string -> (AST.t * int) option
end =
struct
structure S = Scope

type t = S.t list * int

val empty = ([], 0)
fun push (scopes, depth) scope = (scope :: scopes, depth + 1)
fun pop ([], _) =  raise Fail "scope empty"
  | pop (scope::scopes, depth) = (scopes, depth - 1)
fun add ([], _) key value = raise Fail "scope empty"
  | add (scope::scopes, depth) key value = ((S.add scope key value) :: scopes, depth)
fun depth (_, depth) = depth
fun find ([], _) _ = NONE
  | find (env as (scope::_, depth)) key =
    case S.find scope key of
        SOME x => SOME(x, depth)
      | NONE =>  find (pop env) key
end
                                       
fun doMOP inter mop operand =
  let
      val (inter, op1) = f inter operand
  in
      case mop of
          A.Not => (case op1 of
                     A.Bool x => (inter, A.Bool(not x))
                   | _ => raise Type)
  end

and doBOP inter bop operand1 operand2 =
    let
        val (inter, op1) = f inter operand1
        val (inter, op2) = f inter operand2
    in
        case bop of
            A.Equal => (case (op1, op2) of
                         (A.Int x, A.Int y) => (inter, A.Bool(x = y))
                       | (A.Bool x, A.Bool y) => (inter, A.Bool(x = y))
                       | _ => raise Type)
          | A.GreaterThan => (case (op1, op2) of
                               (A.Int x, A.Int y) => (inter, A.Bool(x > y))
                              | _ => raise Type before (print ((AST.toString op1) ^ " "
                            ^ (AST.toString op2))))
          | A.Add => (case (op1, op2) of
                         (A.Int x, A.Int y) => (inter, A.Int(x + y))
                       | _ => raise Type)
    end

and doIf inter cnd thn els =
    case f inter cnd of
        (inter, A.Bool true) => f inter thn
      | (inter, A.Bool false) => f inter els
      | _ => raise Type

and doVar inter name =
    case Env.find inter name of
        SOME (x, _) => (inter, x)
      | NONE => raise Variable name

and doBind inter (A.Var name) value = (Env.add inter name value, A.Bool true)
  | doBind _ _ _ = raise Argument
and doLambda inter params body = (inter, A.Lambda(params, body))
and doCall inter lambda args  = let
    val (inter, lambda) = f inter lambda
    val (A.Lambda(params, body)) = lambda
    fun bindArgs _ [] [] scope = scope
      | bindArgs inter ((A.Var name)::params) (arg::args) scope = let
          val (inter , arg) = f inter arg
      in
          bindArgs inter params args (Scope.add scope name arg)
      end
      | bindArgs _ _ _ _ = raise Argument
    val inter = Env.push inter (bindArgs inter params args Scope.empty)
    val (inter, x) =  f inter body
in
    (Env.pop inter, x)
end

and doProgn inter progs = List.foldl (fn (t, (inter, _)) => f inter t) (inter, A.Bool false) progs

and f inter ast =
    case ast of
        A.MonoOp(mop, op1) => doMOP inter mop op1
      | A.BinOp(bop, op1, op2) => doBOP inter bop op1 op2
      | A.Bind(var, value) => doBind inter var value
      | A.If(cnd, thn, els) => doIf inter cnd thn els
      | A.Var(name) => doVar inter name
      | A.Lambda(params, body) => doLambda inter params body
      | A.Call(lambda, args) => doCall inter lambda args
      | A.Progn(progs) => doProgn inter progs
      | x => (inter, x)

fun run ast = let
    val (_, v) = f (Env.push Env.empty Scope.empty) ast
in
    print ((A.toString v) ^ "\n")
end

end


structure VM = struct

structure Scope :
          sig
              type t
              val empty: t
              val register: t -> string -> string -> t
              val add: t -> string -> t
              val find: t -> string -> string option
              val findId: t -> string -> int
          end
= struct
type t = (string * string) list
val empty = []

val alpha = let
    val id = ref 0
in
    fn name => name ^ "@" ^ (Int.toString (! id)) before id <- (!id) + 1
end

fun register scope name renamed = (name, renamed) :: scope
fun add scope name = register scope name (alpha name)

fun find [] key = NONE
  | find ((name:string, renamed)::scope) (key:string) =
    if name = key
    then SOME renamed
    else find scope key

fun findId scope (key:string) = let
    fun aux ((_, renamed:string)::scope) i =
      if key = renamed
      then i
      else aux scope (i + 1)
      | aux [] _ = raise Fail "cannot find ID"
in
    aux (List.rev scope) 0
    
end
end


structure CodeGen = struct
type t = opcode list
val empty = {codes = [], scopes = [], tailPos = true}
fun setCodes {codes, scopes, tailPos} newCodes = {
    codes = newCodes,
    scopes = scopes,
    tailPos = tailPos
}

fun setScopes {codes, scopeDepth, tailPos} newScopes = {
    codes = codes,
    scopes = newScopes,
    tailPos = tailPos
}

fun setTailPos {codes, scopes, tailPos} newTailPos = {
    codes = codes,
    scopes = scopes,
    tailPos = newTailPos
}

fun add (gen as {codes, ...}) code = setCodes gen code::codes
fun tailPos gen = setTailPos gen true
fun nonTailPos gen = setTailPos gen false
fun pushScope (gen as {scopes, ...}) =  setScopeDepth gen ([] ::scope )
fun popScope (gen as {scopes = scope::scopes, ...}) =  setScopes gen scopes
fun isGlobalScope {scopes, ...} = (List.len scopes) = 0

fun intern (gen as {scopes = scope::scopes, ...}) name = let
    val renamed = Scope.alpha name
    val scope = Scope.register scope name renamed
    val i = Scope.findId scope renamed
in
    ((setScopes gen (scope::scopes)), i)
end

fun generate {codegen, ...} = List.rev codegen
end

datatype opcode
  = Not
  | Add
  | Eq
  | Gt
  | Jump
  | Jtrue
  | Call
  | Ret
  | Push of t
  | Lref of int
  | Lset of int
  | Gref of int
  | Gset of int
  | Nop


structure A = AST
structure C = CodeGen

exception Type


fun doMonoOp gen mop x = let
    val gen =  compile gen x
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
    val (gen, id) = C.intern name
    val gen = compile gen value
in
    if C.isGlobalScope
    then C.add gen (Gset(id))
    else C.add gen (Gset(id))
end
  | doBind _ _ _ = raise Type


and doVar (gen as {scopes = scope::scopes, ...}) name = let
    val renamed = Scope.find scope name
    val id = Scope.findId scope renamed
in
end

and doIf gen cnd thn els = gen

and doConst gen x = C.add gen (Push x)

and doLambda gen params body = gen

and doCall gen lambda args = gen

and doProgn gen (exp::exps) = let
    val gen = compile (C.nonTailPos gen) exp
in
    doProgn gen exps
end
  | doProgn gen [exp] = compile (C.tailPos gen) exp
  | doProgn gen [] = raise Fail "progn invalid"
    

and compile gen ast =
  case ast of
      MonoOp(monoop, x) => doMonoOp gen monoop x
    | BinOp(binop, x, y) => doBinOp gen binop x y
    | Bind(var, value) => doBind gen var value
    | If(cnd, thn, els) => doIf gen cnd thn els
    | Var(name) => doVar gen name
    | Lambda(params, body) => doLambda gen params body
    | Call(lambda, args) => doCall gen lambda args
    | Progn(exps) => doProgn gen exps
    | x => doConst gen x
      

end
open AST

val fib = (Progn [
                Bind (Var "fib",
                      Lambda([Var "n"],
                               (If (BinOp(GreaterThan,
                                          (Int 2),
                                          (Var "n")),
                                    Int(1),
                                    BinOp(Add,
                                          Call(Var "fib", [BinOp(Add,
                                                                 Var "n",
                                                                 Int ~1)]),
                                          Call(Var "fib", [BinOp(Add,
                                                                 Var "n",
                                                                 Int ~2)])))))),
                Call(Var "fib", [Int 1])])

(* val () = Interp.run  fib *)
