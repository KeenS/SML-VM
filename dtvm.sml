structure DTVM =
struct
open VM

type oparg = {string: string, int: int, vmvalue: vmvalue}
val noArg: oparg= {string = "", int = 0, vmvalue = Undefined}
fun intArg int: oparg = {string = "", int = int, vmvalue = Undefined}
fun stringArg string: oparg = {string = string, int = 0, vmvalue = Undefined}
fun vmvalueArg vmvalue: oparg = {string = "", int = 0, vmvalue = vmvalue}

fun opToIndex Not = (0, noArg)
  | opToIndex Add =  (1, noArg)
  | opToIndex Eq = (2, noArg)
  | opToIndex Gt = (3, noArg)
  | opToIndex (Jump label) = (4, stringArg label)
  | opToIndex (Jtrue label) = (5, stringArg label)
  | opToIndex (Call i) = (6, intArg i)
  | opToIndex Ret = (7, noArg)
  | opToIndex (Push v) = (8, vmvalueArg v)
  | opToIndex Pop = (9, noArg)
  | opToIndex (Lref i) = (10, intArg i)
  | opToIndex (Lset i) = (11, intArg i)
  | opToIndex (Gref i) = (12, intArg i)
  | opToIndex (Gset i) = (13, intArg i)
  | opToIndex Nop = (14, noArg)
  | opToIndex End = (15, noArg)


fun run (vm as {pool, stack, fp, sp, pc, ...} : vm) (obj as (ops, labelDb, opLen)) = let
    val len = Array.length ops
    val opArray = Array.fromList [
            (* Not *)
            (fn _ =>
                case pop vm of
                    Bool x => push vm (Bool (not x))
                  | _ => raise Type),
            (* Add *)
            (fn _ =>
                case (pop vm, pop vm) of
                    (Int x, Int y) => push vm (Int (x + y))
                  | _ => raise Type),
            (* Eq *)
            (fn _ =>
                case (pop vm, pop vm) of
                    (Int x, Int y) => push vm (Bool (x = y))
                  | (Bool x, Bool y) => push vm (Bool (x = y))
                  | _ => raise Type),
            (* Gt *)
            (fn _ =>
                case (pop vm, pop vm) of
                    (Int x, Int y) => push vm (Bool (x < y))
                  | _ => raise Type),
            (* Jump *)
            (fn ({string = label, ...}: oparg) =>
                pc := ((findLabel labelDb label) - 1)),
            (* Jtrue *)
            (fn ({string = label, ...}: oparg) =>
                case pop vm of
                    Bool true => pc := ((findLabel labelDb label) - 1)
                  | Bool false => ()
                  | _ => raise Type),
            (* Call *)
            (fn ({int = i, ...}: oparg) =>
                case (pop vm) of
                    Lambda label => (
                     pushCi vm;
                     fp := (!fp) - i;
                     pc := ((findLabel labelDb label) - 1))
                  | _ => raise Type),
            (* Ret *)
            (fn _ =>
                (Array.update(stack, !fp, Array.sub(stack, (!sp) - 1));
                 popCi vm;
                 pc := (!pc))),
            (* Push *)
            (fn ({vmvalue = v, ...}: oparg) =>
                push vm v),
            (* Pop *)
            (fn _ =>
                (pop vm;())),
            (* Lref *)
            (fn ({int = i, ...}: oparg) =>
                push vm (Array.sub(stack, (!fp) + i))),
            (* Lset *)
            (fn ({int = i, ...}: oparg) =>
                ((Array.update(stack, (!fp) + i, pop vm));
                 push vm (Bool true))),
            (* Gref *)
            (fn ({int = i, ...}: oparg) =>
                push vm (Array.sub(pool, i))),
            (* Gset *)
            (fn ({int = i, ...}: oparg) =>
                (Array.update(pool, i, pop vm); push vm (Bool true))),
            (* Nop *)
            (fn _ =>
                ()),
            (fn _ =>
                raise Exit)
        ]
    fun aux () = if (!pc) < len
                 then (let val (index, arg) = opToIndex (Array.sub(ops, !pc)) in 
                           Array.sub(opArray, index) arg;
                           pc := (!pc) + 1;
                           aux ()
                               
                       end)
                      handle Exit => ()
                 else ()
in
    aux ()
    handle _ => printVM vm obj;
    stack
end
                                         
end

