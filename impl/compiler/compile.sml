structure Compile =
struct
  open OS.Process
  open OS.Path
  open Util
  structure PTC = PreTypeCheck
  structure UE = UnderscoredExpr
  structure E = Expr

  infixr $

  fun main (prog_name : string, args : string list) : int =
    let
      val result =
        if length args < 2 then
          (println "Usage: THIS main filename1 [filename2 ...]"; exit failure)
        else
          TiML.main $ tl args
      val prog : UE.prog = #1 result
      val gctx : PTC.sigcontext = #2 result
      val admits : (string * E.prop) list = #3 result
      val entry : string = hd args
      val (mod_name, func_name) =
        let
          val base_ext = splitBaseExt entry
          val base = #base base_ext
          val ext = #ext base_ext
        in
          case ext of
            SOME ext => (base, ext)
          | NONE => (println $ entry ^ " should be like Main.main"; exit failure)
        end
      val entry_is_legal = List.exists (fn (k, v) =>
        if k = mod_name then
          case v of
            PTC.Sig (_, _, _, tctx) => List.exists (fn (k, v) =>
              if k = func_name then
                case v of
                  E.Mono (E.Arrow (E.Unit _, _, E.BaseType (E.Int, _))) => true
                | _ => false
              else
                false) tctx
          | PTC.FunctorBind _ => false
        else
          false) gctx
      val () =
        case entry_is_legal of
          true => ()
        | false => (println $ entry ^ " does not exist or not have type unit -> int"; exit failure)
    in
      0
    end
      handle TiML.Error msg => (println msg; 1)
           | IO.Io e => (println (sprintf "IO Error doing $ on $" [#function e, #name e]); 1)
           | Impossible msg => (println $ "Impossible: " ^ msg; 1)
           | E.ModuleUVar msg => (println $ "ModuleUVar: " ^ msg; 1)
           | _ => (println "Internal Error"; 1)
end
