structure Id :
          sig
              val f: string -> string
          end
= struct
val f = let
    val id = ref 0
in
    fn name => name ^ "@" ^ (Int.toString (! id)) before id := (!id) + 1
end


end

