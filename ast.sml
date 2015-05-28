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
  | toString (Call(lambda, args)) = "(" ^ (toString lambda) ^ " " ^ (String.concatWith " " (List.map toString args)) ^ ")"
  | toString (Progn(exps)) = "(progn " ^ (String.concatWith " " (List.map toString exps)) ^ ")"

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

val add3 = (Progn [
                 Bind (Var "add3",
                       Lambda([],
                              BinOp(Add, Int 1, Int 2)
                      )),
                 Call(Var "add3", [])])
end

