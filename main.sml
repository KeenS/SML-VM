#use "ast.sml";
#use "id.sml";
#use "vm.sml";
#use "dtvm.sml";
#use "benchmark.sml";

val _ = Benchmark.benchset "fib" 1 [
        ("normal vm",
         fn () => VM.run (new ()) (Compile.f (AST.fib 24))),
        ("DT vm",
         fn () => DTVM.run (new ()) (Compile.f (AST.fib 24)))
    ]
     
