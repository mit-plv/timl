(* turn on exception back-trace *)
CM.make "$smlnj-tdp/back-trace.cm";
SMLofNJ.Internals.TDP.mode := true;

Control.Elab.valueRestrictionTopWarn := false;

Control.Print.printDepth := 100;

Control.polyEqWarn := false;

Control.MC.matchNonExhaustiveError := true;
Control.MC.bindNonExhaustiveError := true;
