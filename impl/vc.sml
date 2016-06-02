structure VC = struct
open Util
open Region
open NoUVar
open NoUVarExpr
open Subst
open Simp
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
        Quan (q, bs, Bind ((name, r), p), r_all) =>
        let
            val name = find_unique ctx name
        in
            Quan (q, bs, Bind ((name, r), uniquefy (name :: ctx) p), r_all)
        end
      | Not (p, r) => Not (uniquefy ctx p, r)
      | BinConn (opr, p1, p2) => BinConn (opr, uniquefy ctx p1, uniquefy ctx p2)
      | BinPred _ => p
      | True _ => p
      | False _ => p
end

(* datatype hyp =  *)
(*          VarH of string * base_sort *)
(*        | PropH of prop  *)

(* type vc = hyp list * prop *)

type vc = (string * base_sort, prop) hyp list * prop

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
          
end
