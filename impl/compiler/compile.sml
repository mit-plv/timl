structure Compile =
struct
  open OS.Process
  open Util
  structure PTC = PreTypeCheck
  structure UE = UnderscoredExpr
  structure E = Expr

  infixr 0 $

  fun main (prog_name, args : string list) : int =
    let
      val (prog, gctx, admits) =
        case args of
          [] => ("Usage: THIS filename1 filename2 ..."; exit failure)
        | _ => TiML.main args
    in
      0
    end
      handle TiML.Error msg => (println msg; 1)
           | IO.Io e => (println (sprintf "IO Error doing $ on $" [#function e, #name e]); 1)
           | Impossible msg => (println ("Impossible: " ^ msg); 1)
           | Expr.ModuleUVar msg => (println ("ModuleUVar: " ^ msg); 1)
           | _ => (println "Internal Error"; 1)
end
