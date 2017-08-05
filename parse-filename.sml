structure ParseFilename = struct

open Util
       
infixr 0 $
         
fun parse_filename (on_file, on_error) filename =
    let
      val (dir, base, ext) = split_dir_file_ext filename
    in
      if ext = SOME "pkg" then
        let
          (* val split_lines = String.tokens (fn c => c = #"\n") *)
          (* val read_lines = split_lines o read_file *)
          val filenames = read_lines filename
          val filenames = map trim filenames
          (* val () = app println filenames *)
          val filenames = List.filter (fn s => not (String.isPrefix "(*" s andalso String.isSuffix "*)" s)) filenames
          (* val () = app println filenames *)
          val filenames = List.filter (fn s => s <> "") filenames
          val filenames = map (curry join_dir_file dir) filenames
        in
          parse_filenames (on_file, on_error) filenames
        end
      else if ext = SOME "timl" then
        on_file filename
      else on_error $ sprintf "Unknown filename extension $ of $" [default "<EMPTY>" ext, filename]
    end
      
and parse_filenames params filenames =
    app (parse_filename params) filenames

fun expand_pkg on_error filename =
  let
    val r = ref []
    fun on_file a = push_ref r a
    val () = parse_filename (on_file, on_error) filename
  in
    rev $ !r
  end
    
end
