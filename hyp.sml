structure Hyp = struct

open Util
       
datatype ('var, 'prop) hyp = 
         VarH of 'var
         | PropH of 'prop
                      
fun append_hyps_vc hs vc = mapFst (fn hs' => hs' @ hs) vc
fun add_hyp_vc h vc = append_hyps_vc [h] vc
fun append_hyps hs vcs = map (append_hyps_vc hs) vcs
fun add_hyp h vcs = append_hyps [h] vcs
                                
fun hyps2ctx hs = List.mapPartial (fn h => case h of VarH (name, _) => SOME name | _ => NONE) hs

end
