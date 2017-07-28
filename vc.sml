signature VC_PARAMS = sig
  structure Idx : IDX where type name = string * Region.region
                                 and type region = Region.region
                                 (* and type var = int LongId.long_id *)
  val get_region_p : Idx.prop -> Region.region
  val str_bs : Idx.bsort -> string
  val str_p : ToStringUtil.global_context -> ToStringUtil.scontext -> Idx.prop -> string
  val simp_p : Idx.prop -> Idx.prop
end

functor VCFn (Params : VC_PARAMS) = struct

open Params
open Idx
       
open Gctx
open List
open Util
open Hyp
open Region
open Bind

structure IdxUtil = IdxUtilFn (Idx)
open IdxUtil

infixr 1 -->
         
infixr 0 $
         
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
      | PTrueFalse _ => p

type vc = (string * bsort, prop) hyp list * prop

fun str_vc show_region filename ((hyps, p) : vc) =
    let 
        val region = if show_region then 
                         [str_region "" filename (get_region_p p)] 
                     else []
        fun g (h, (hyps, ctx)) =
            case h of
                VarH (name, bs) => (sprintf "$ : $" [name, str_bs bs] :: hyps, name :: ctx)
              | PropH p => (str_p empty ctx p :: hyps, ctx)
        val (hyps, ctx) = foldr g ([], []) hyps
        val hyps = rev hyps
        val p = str_p empty ctx p
    in
        region @
        (self_compose 2 indent) (hyps @
                           ["==============="] @
                           [p])
    end 

fun simp_hyp h =
    case h of
        VarH a => VarH a
      | PropH p => PropH (simp_p p)

fun simp_vc ((hyps, p) : vc) : vc =
    let
      val hyps = map simp_hyp hyps
      val p = simp_p p
    in
      (hyps, p)
    end

fun prop2vcs p : vc list =
    let
    in
        case p of
            Quan (Forall, bs, Bind ((name, r), p), r_all) =>
            let
                val ps = prop2vcs p
                val ps = add_hyp (VarH (name, bs)) ps
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

fun vc2prop ((hs, p) : vc) =
    foldl (fn (h, p) => case h of VarH (name, b) => Quan (Forall, b, Bind ((name, dummy), p), get_region_p p) | PropH p1 => p1 --> p) p hs

fun simp_vc_vcs (vc : vc) : vc list = prop2vcs $ simp_p $ vc2prop $ vc
          
end
