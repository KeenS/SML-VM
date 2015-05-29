structure DTVM =
struct
open VM

type oparg = {int: int, vmvalue: V.t}
val noArg: oparg= {int = 0, vmvalue = V.Undefined}
fun intArg int: oparg = {int = int, vmvalue = V.Undefined}
fun vmvalueArg vmvalue: oparg = {int = 0, vmvalue = vmvalue}

fun opToIndex O.Not = (0, noArg)
  | opToIndex O.Add =  (1, noArg)
  | opToIndex O.Eq = (2, noArg)
  | opToIndex O.Gt = (3, noArg)
  | opToIndex (O.Jump label) = (4, intArg label)
  | opToIndex (O.Jtrue label) = (5, intArg label)
  | opToIndex (O.Call i) = (6, intArg i)
  | opToIndex O.Ret = (7, noArg)
  | opToIndex (O.Push v) = (8, vmvalueArg v)
  | opToIndex O.Pop = (9, noArg)
  | opToIndex (O.Lref i) = (10, intArg i)
  | opToIndex (O.Lset i) = (11, intArg i)
  | opToIndex (O.Gref i) = (12, intArg i)
  | opToIndex (O.Gset i) = (13, intArg i)
  | opToIndex O.Nop = (14, noArg)
  | opToIndex O.End = (15, noArg)

val opcodeSize = 16

fun compile ast = let
    val ops = Compile.f ast
    val len = Array.length ops
    val cops = Array.array(len, (opToIndex O.Nop))
    val () = Array.appi (fn (i, opcode) => Array.update(cops, i, (opToIndex opcode))) ops
in
    cops
end


fun run (vm as {pool, stack, fp, sp, pc, ...} : vm) cops = let
    val opArray = Array.array(opcodeSize, fn _ => ())
    fun next () = let
        val () = pc := (!pc) + 1;
        val (index, arg) = Array.sub(cops, !pc) in
        Array.sub(opArray, index) arg
    end
    val () = Array.appi (fn (i, f) => Array.update(opArray, i, f)) (Array.fromList [
            (* Not *)
            fn _ =>
                (case pop vm of
                    V.Bool x => push vm (V.Bool (not x))
                  | _ => raise Type;
                next ()),
            (* Add *)
            fn _ =>
                (case (pop vm, pop vm) of
                    (V.Int x, V.Int y) => push vm (V.Int (x + y))
                  | _ => raise Type;
                 next ()),
            (* Eq *)
            fn _ =>
                (case (pop vm, pop vm) of
                    (V.Int x, V.Int y) => push vm (V.Bool (x = y))
                  | (V.Bool x, V.Bool y) => push vm (V.Bool (x = y))
                  | _ => raise Type;
                  next ()),
            (* Gt *)
            fn _ =>
                (case (pop vm, pop vm) of
                    (V.Int x, V.Int y) => push vm (V.Bool (x < y))
                  | _ => raise Type;
                 next ()),
            (* Jump *)
            fn ({int = label, ...}: oparg) =>
               (pc := (label - 1);
               next ()),
            (* Jtrue *)
            fn ({int = label, ...}: oparg) =>
                (case pop vm of
                    V.Bool true => pc := (label - 1)
                  | V.Bool false => ()
                  | _ => raise Type;
                next ()),
            (* Call *)
            fn ({int = i, ...}: oparg) =>
                (case (pop vm) of
                    V.Lambda label => (
                     pushCi vm;
                     fp := (!fp) - i;
                     pc := (label - 1))
                  | _ => raise Type;
                next ()),
            (* Ret *)
            fn _ =>
                (Array.update(stack, !fp, Array.sub(stack, (!sp) - 1));
                 popCi vm;
                 pc := (!pc);
                next ()),
            (* Push *)
            fn ({vmvalue = v, ...}: oparg) =>
               (push vm v;
               next ()),
            (* Pop *)
            fn _ =>
               (pop vm;
                next ()),
            (* Lref *)
            fn ({int = i, ...}: oparg) =>
               (push vm (Array.sub(stack, (!fp) + i));
               next ()),
            (* Lset *)
            fn ({int = i, ...}: oparg) =>
                ((Array.update(stack, (!fp) + i, pop vm));
                 push vm (V.Bool true);
                next ()),
            (* Gref *)
            fn ({int = i, ...}: oparg) =>
               (push vm (Array.sub(pool, i));
               next ()),
            (* Gset *)
            fn ({int = i, ...}: oparg) =>
               (Array.update(pool, i, pop vm);
                push vm (V.Bool true);
               next ()),
            (* Nop *)
            (fn _ =>
                next ()),
            (fn _ =>
                raise Exit)
        ])
    fun aux () = let val (index, arg) = Array.sub(cops, !pc) in
                     Array.sub(opArray, index) arg
                 end
in
    aux ()
    handle Exit => ();
    stack
end
                                         
end

