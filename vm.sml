structure VM =
struct

structure O = OpCode
structure V = VMValue


val STACK_SIZE = 500
val CONST_POOL_SIZE = 10

type ci = {
    fp: int,
    sp: int,
    pc: int
}

type t = {
    stack: V.t array,
    sp: int ref,
    fp: int ref,
    pc: int ref,
    pool: V.t array,
    ci: ci list ref
}

type opcode = O.t

fun printStack ({stack, sp, fp, ...}: t) = 
  Array.appi (fn (i, value) => (
                  print (Int.toString i);
                  print "\t";
                  print (V.toString value); 
                  (if i = (!sp)
                   then print " <-sp"
                   else ());
                  (if i = (!fp)
                   then print " <-fp"
                   else ());
                  print "\n")) stack

fun printOps pc buffer = (
    Array.appi (fn (i, opcode) => (
                    print (Int.toString i);
                    print "\t";
                    print (O.toString opcode);
                    (if i = pc
                     then print " <-pc"
                     else ());
                    print "\n")) buffer
)

fun printVM (vm as {pc, ...}: t) ops = (
    printStack vm;
    printOps (!pc) ops
)

exception Type
exception Exit

fun new (): t = {
    stack = Array.array(STACK_SIZE, V.Undefined),
    fp = ref 0,
    sp = ref 0,
    pc = ref 0,
    pool = Array.array(CONST_POOL_SIZE, V.Undefined),
    ci = ref []
}

fun push ({stack, sp, ...}: t) v = (
    Array.update(stack, (!sp), v);
    sp := (!sp) + 1
)

fun pop ({stack, sp, ...}: t) = (
    Array.update(stack, !sp, V.Undefined); (* for debug *)
    sp := (!sp) - 1;
    Array.sub(stack, !sp)
)
                                   

fun pushCi (vm as {ci, fp, sp, pc, ...}: t) = (
    ci := {fp = !fp, sp = !sp, pc = !pc} :: (!ci);
    fp := (!sp)
) 
                                                 

fun popCi (vm as  {ci, fp, sp, pc, ...}: t) = let
    val ({fp = cfp, sp = csp, pc = cpc}::tl) = !ci
in
    fp := cfp;
    sp := csp;
    pc := cpc;
    ci := tl
end

val compile = Compile.f

fun run (vm as {pool, stack, fp, sp, pc, ...} : t) ops = let
    fun aux () = (
        case  (Array.sub(ops, !pc)) of
            O.Not => (case pop vm of
                         V.Bool x => push vm (V.Bool (not x))
                       | _ => raise Type)
          | O.Add => (case (pop vm, pop vm) of
                         (V.Int x, V.Int y) => push vm (V.Int (x + y))
                       | _ => raise Type)
          | O.Eq => (case (pop vm, pop vm) of
                        (V.Int x, V.Int y) => push vm (V.Bool (x = y))
                      | (V.Bool x, V.Bool y) => push vm (V.Bool (x = y))
                      | _ => raise Type)
          | O.Gt => (case (pop vm, pop vm) of
                        (V.Int x, V.Int y) => push vm (V.Bool (x < y))
                      | _ => raise Type)
          | O.Jump label => pc := (label - 1)
          | O.Jtrue label => (case pop vm of
                                 V.Bool true => pc := (label - 1)
                               | V.Bool false => ()
                               | _ => raise Type)
          | O.Call i => (case (pop vm) of
                            V.Lambda label => (
                             pushCi vm;
                             fp := (!fp) - i;
                             pc := (label - 1))
                          | _ => raise Type)
          | O.Ret => (Array.update(stack, !fp, Array.sub(stack, (!sp) - 1));
                     popCi vm;
                     pc := (!pc))
          | O.Push v => push vm v
          | O.Pop => (pop vm;())
          | O.Lref i => push vm (Array.sub(stack, (!fp) + i))
          | O.Lset i =>  ((Array.update(stack, (!fp) + i, pop vm));
                         push vm (V.Bool true))
          | O.Gref i => push vm (Array.sub(pool, i))
          | O.Gset i =>  (Array.update(pool, i, pop vm); push vm (V.Bool true))
          | O.Nop => ()
          | O.End => raise Exit
      ;
        pc := (!pc) + 1;
      aux ())
in
    aux ()
    handle Exit => ();
    print (V.toString (Array.sub(stack, 0)))
end
                                                            
end
