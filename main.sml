use "ast.sml";
use "id.sml";
use "interp.sml";
use "vm.sml";
use "dtvm.sml";
use "benchmark.sml";

val target = (AST.fib 24)
val compiled = VM.Compile.f target
val dtcompiled = DTVM.Compile.f target
val vm = VM.new ()
val dtvm = DTVM.new ()

val _ = Benchmark.benchset "fib" 1 [
        ("interpreter",
         fn () => (Interp.run target; ())),
        ("normal VM",
         fn () => (VM.run vm compiled; ())),
        ("Direct Threaded VM",
         fn () => (DTVM.run dtvm dtcompiled; ()))
    ]
     
