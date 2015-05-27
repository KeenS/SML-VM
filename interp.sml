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
(* val () = Interp.run  AST.fib *)
