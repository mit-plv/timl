structure TextToken =
  struct
    type token = string
    type style = unit
    fun string t = t
    fun style t = ()
    fun size t = String.size t
  end

(* structure PP = PPDebugFn(PPStreamFn( *)
(*     structure Token = TextToken *)
(*     structure Device = SimpleTextIODev)) *)

structure PP = PPStreamFn(
  structure Token = TextToken
  structure Device = SimpleTextIODev)

structure WithPP = struct

fun withPP (name, wid, dst) ppFn =
  let
    (* val saveStrm = !PP.debugStrm *)
    (* val _ = PP.debugStrm := TextIO.openAppend("debug-out.txt") *)
    val ppStrm =
	PP.openStream(SimpleTextIODev.openDev{dst=dst, wid=wid})
  in
    (* print(concat[name, ": width = ", Int.toString wid, "\n"]); *)
    ppFn ppStrm;
    PP.closeStream ppStrm;
    TextIO.output (dst, "\n");
    (* TextIO.closeOut (!PP.debugStrm); *)
    (* PP.debugStrm := saveStrm; *)
    ()
  end

(* a test *)
fun t40 () = withPP ("Test 20 [C code]", 20, TextIO.stdOut) (fn strm => (
      PP.openHBox strm;
	PP.string strm "if";
	PP.space strm 1;
	PP.string strm "(x < y)";
	PP.space strm 1;
	PP.string strm "{";
	PP.openHVBox strm (PP.Abs 2);
	  PP.space strm 1;
	  PP.string strm "stmt1;"; PP.space strm 1;
	  PP.openHBox strm;
	    PP.string strm "if";
	    PP.space strm 1;
	    PP.string strm "(w < z)";
	    PP.space strm 1;
	    PP.string strm "{";
	    PP.openHVBox strm (PP.Abs 4);
	      PP.space strm 1; PP.string strm "stmt2;";
	      PP.space strm 1; PP.string strm "stmt3;";
	      PP.space strm 1; PP.string strm "stmt4;";
	    PP.closeBox strm; PP.newline strm;
	    PP.string strm "}";
	  PP.closeBox strm;
	  PP.space strm 1; PP.string strm "stmt5;";
	  PP.space strm 1; PP.string strm "stmt6;";
	PP.closeBox strm; PP.newline strm;
	PP.string strm "}";
        PP.closeBox strm))

end

