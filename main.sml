use "ast.sml";
use "id.sml";
use "interp.sml";
use "vmvalue.sml";
use "opcode.sml";
use "compile.sml";
use "vm.sml";
use "dtvm.sml";
use "benchmark.sml";

val target = (AST.fib 35)
val compiled = VM.compile target
val dtcompiled = DTVM.compile target
val vm = VM.new ()
val dtvm = DTVM.new ()

val _ = Benchmark.benchset "fib 35" 1 [
        ("Interpreter",
         fn () => (Interp.run target; ())),
        ("Normal VM",
         fn () => (VM.run vm compiled; ())),
        ("Direct Threaded VM",
         fn () => (DTVM.run dtvm dtcompiled; ()))
    ]
     
