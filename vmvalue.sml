structure VMValue =
struct
datatype t
    = Int of int
    | Bool of bool
    | Undefined
    | Lambda of int

fun toString (Int i) = Int.toString i
  | toString (Bool b) = Bool.toString b
  | toString Undefined = "Undefined"
  | toString (Lambda i) = "Lambda " ^ (Int.toString i)
end
