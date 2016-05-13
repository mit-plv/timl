structure VC = struct
open Util
open Region
open NoUVar
open NoUVarExpr
open NoUVarSubst
infixr 1 -->
infixr 0 $
         
local
    fun find_unique ls name =
        if not (mem op= name ls) then
	    name
        else
	    let fun loop n =
		    let val name' = name ^ "_x" ^ str_int n in
		        if not (mem op= name' ls) then name' else loop (n + 1)
		    end in
	        loop 2
	    end
in
fun uniquefy_ls names = foldr (fn (name, acc) => find_unique acc name :: acc) [] names
fun uniquefy ctx p =
    case p of
        Quan (q, bs, (name, r), p, r_all) =>
        let
            val name = find_unique ctx name
        in
            Quan (q, bs, (name, r), uniquefy (name :: ctx) p, r_all)
        end
      | Not (p, r) => Not (uniquefy ctx p, r)
      | BinConn (opr, p1, p2) => BinConn (opr, uniquefy ctx p1, uniquefy ctx p2)
      | BinPred _ => p
      | True _ => p
      | False _ => p
end

datatype hyp = 
         VarH of string * base_sort
       | PropH of prop 

type vc = hyp list * prop

fun str_vc show_region filename ((hyps, p) : vc) =
    let 
        val region = if show_region then 
                         [str_region "" filename (get_region_p p)] 
                     else []
        fun g (h, (hyps, ctx)) =
            case h of
                VarH (name, bs) => (sprintf "$ : $" [name, str_b bs] :: hyps, name :: ctx)
              | PropH p => (str_p ctx p :: hyps, ctx)
        val (hyps, ctx) = foldr g ([], []) hyps
        val hyps = rev hyps
        val p = str_p ctx p
    in
        region @
        hyps @
        ["==============="] @
        [p]
    end 

fun simp_hyp h =
    case h of
        VarH a => VarH a
      | PropH p => PropH (simp_p p)

fun hyps2ctx hs = List.mapPartial (fn h => case h of VarH (name, _) => SOME name | _ => NONE) hs

fun simp_vc ((hyps, p) : vc) : vc =
    let
      val hyps = map simp_hyp hyps
      (* val () = println $ "Before: " ^ str_p (hyps2ctx hyps) p *)
      val p = simp_p p
      (* val () = println $ "After:  " ^ str_p (hyps2ctx hyps) p *)
    in
      (hyps, p)
    end

fun get_base bs =
    case bs of
        Base b => b
      | UVarBS u => exfalso u

fun append_hyps hs vcs = map (mapFst (fn hs' => hs' @ hs)) vcs
fun add_hyp h vcs = append_hyps [h] vcs
                                      
fun prop2vcs p =
    let
    in
        case p of
            Quan (Forall, bs, (name, r), p, r_all) =>
            let
                val ps = prop2vcs p
                val ps = add_hyp (VarH (name, get_base bs)) ps
            in
                ps
            end
          | BinConn (Imply, p1, p) =>
            let
                val ps = prop2vcs p
                val ps = add_hyp (PropH p1) ps
            in
                ps
            end
          | BinConn (And, p1, p2) =>
            prop2vcs p1 @ prop2vcs p2
          | _ => [([], p)]
    end

fun vc2prop (hs, p) =
    foldl (fn (h, p) => case h of VarH (name, b) => Quan (Forall, Base b, (name, dummy), p, get_region_p p) | PropH p1 => p1 --> p) p hs

fun simp_vc_vcs vc = prop2vcs $ simp_p $ vc2prop $ vc
          
fun shiftx_hyp x n hyp =
    case hyp of
        VarH _ => hyp
      | PropH p => PropH (shiftx_i_p x n p)
                         
fun shiftx_hyps x n hyps =
    case hyps of
        [] => hyps
      | hyp :: hyps =>
        let
            val d = case hyp of
                        VarH _ => 1
                      | PropH _ => 0
        in
            shiftx_hyp x n hyp :: shiftx_hyps (x + d) n hyps
        end
            
fun find_hyp forget shift pred x hyps =
    let
        exception Error
        fun runError m _ =
            SOME (m ())
            handle
            Error => NONE
            | ForgetError _ => NONE
        fun do_forget hyp x =
            case hyp of
                VarH _ => forget x
              | PropH _ => x
        fun do_shift hyp (p as (y, hyps)) =
            case hyp of
                VarH _ => (shift y, shiftx_hyps 0 1 hyps)
              | PropH _ => p
        fun loop x hyps () =
            let
                val (hyp, hyps) = case hyps of hyp :: hyps => (hyp, hyps) | [] => raise Error
                val x = do_forget hyp x
            in
                case pred x hyps hyp of
                    SOME y => do_shift hyp (y, hyps)
                  | NONE => do_shift hyp (loop x hyps ())
            end
    in
        runError (loop x hyps) ()
    end
        
end
