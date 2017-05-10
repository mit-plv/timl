(* for mlton *)
val ret = Main.main (CommandLine.name (), CommandLine.arguments ())

val () = OS.Process.exit ret
