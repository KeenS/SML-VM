structure OpCode =
struct
structure V = VMValue

datatype t
  = Not
  | Add
  | Eq
  | Gt
  | Jump of int
  | Jtrue of int
  | Call of int
  | Ret
  | Push of V.t
  | Pop
  | Lref of int
  | Lset of int
  | Gref of int
  | Gset of int
  | Nop
  | End

fun toString Not = "Not"
  | toString Add = "Add"
  | toString Eq =  "Eq"
  | toString Gt = "Gt"
  | toString (Jump i) = "Jump " ^ (Int.toString i)
  | toString (Jtrue i) = "Jtrue " ^ (Int.toString i)
  | toString (Call i) = "Call " ^ (Int.toString i)
  | toString Ret = "Ret"
  | toString (Push v) = "Push " ^ (V.toString v)
  | toString Pop = "Pop"
  | toString (Lref i) = "Lref " ^ (Int.toString i)
  | toString (Lset i) = "Lset " ^ (Int.toString i)
  | toString (Gref i) = "Gref " ^ (Int.toString i)
  | toString (Gset i) = "Gset " ^ (Int.toString i)
  | toString Nop = "Nop"
  | toString End = "End"

end
