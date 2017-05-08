(* a special version of forget that allows [uvar] in [uvar arg1 ...] to ignore offending arguments *)

structure UVarForget = struct
open Util
open Expr
open Subst
open Normalize
open FreshUVar

infixr 0 $
infix 0 !!

structure S = IntBinarySet
fun to_set ls = S.addList (S.empty, ls)
fun member x s = S.member (s, x)
        
fun forget_i_i x n b =
  let
    (* val () = println $ sprintf "Start forgetting $ in $" [str_int x, str_i [] [] b] *)
    val b = normalize_i b
    exception AppUVarFailed
    exception AppUVarSucceeded of idx
    fun on_App_UVar () =
      let
        fun is_inl x = case x of inl a => SOME a | inr _ => NONE
        fun is_inr x = case x of inr a => SOME a | inl _ => NONE
        fun max_ls init ls = foldl (uncurry max) init ls
        val body = b
        val forget = forget_i_i x n
        val ((uvar, r), args) = is_IApp_UVarI body !! (fn () => raise AppUVarFailed)
        val (_, ctx, bsort) = get_uvar_info uvar !! (fn () => raise Impossible "should be fresh")
        fun try_forget (loc, arg) =
          let
            val arg = forget arg
          in
            inl arg
          end
          handle ForgetError _ => inr loc
        val results = mapi try_forget args
        val args = List.mapPartial is_inl results
        val () =
            if length args = length results then
              raise AppUVarSucceeded $ combine_IApp (UVarI (uvar, r)) args
            else ()
        val locs = List.mapPartial is_inr results
        val () = assert (fn () => not (null locs)) "not (null locs)"
        val max_loc = max_ls 0 locs
        fun extend_ctx n (ctx, bsort) =
          if n < length ctx then (ctx, bsort)
          else
            let
              val len = length ctx
              val more = n + 1 - len
              val (args, b) = collect_BSArrow bsort
              val () = assert (fn () => more <= length args) "more <= length args"
              val (args1, args2) = (take more args, drop more args)
              val bsort = combine_BSArrow (args2, bsort)
              val args1 = rev args1
              fun var_name n = "__x" ^ str_int n
              val ctx = mapi (mapFst var_name) args1 @ ctx
            in
              (ctx, bsort)
            end
        val (ctx, bsort) = extend_ctx max_loc (ctx, bsort)
        val length_ctx = length ctx
        val () = assert (fn () => max_loc < length_ctx) "max_loc < length ctx"
        val locs = map (fn n => length_ctx - 1 - n) locs
        val locs = to_set locs
        fun remove_at_locs locs ls = rev $ foldli (fn (n, x, acc) => if member n locs then acc else x :: acc) [] ls
        val ctx' = remove_at_locs locs ctx
        val new_uvar = UVarI (fresh_uvar_i ctx' bsort, r)
        val ret = IApps new_uvar args
        val inner_args = range length_ctx
        val inner_args = remove_at_locs locs inner_args
        val ins = IApps new_uvar (map (V r) $ rev inner_args)
        val ins = IAbsMany (ctx, ins, r)
        val () = refine uvar ins
      in
        ret
      end
    fun structural () =
      let
        val f = forget_i_i
        val on_v = forget_v
      in
        case b of
	    VarI y => VarI $ on_v_long_id on_v x n y
	  | ConstIN n => ConstIN n
	  | ConstIT x => ConstIT x
          | UnOpI (opr, i, r) => UnOpI (opr, f x n i, r)
          | DivI (i1, n2) => DivI (f x n i1, n2)
          | ExpI (i1, n2) => ExpI (f x n i1, n2)
	  | BinOpI (opr, i1, i2) => BinOpI (opr, f x n i1, f x n i2)
          | Ite (i1, i2, i3, r) => Ite (f x n i1, f x n i2, f x n i3, r)
	  | TTI r => TTI r
	  | TrueI r => TrueI r
	  | FalseI r => FalseI r
          | IAbs (b, bind, r) => IAbs (b, on_i_ibind f x n bind, r)
          | AdmitI r => AdmitI r
          | UVarI a => b (* uvars are closed, so no need to deal with *)
      end
    val ret =
        on_App_UVar ()
        handle AppUVarFailed => structural ()
             | AppUVarSucceeded i => i
    (* val () = println $ "Finish forgetting" *)
  in
    ret
  end

fun forget_i_p x n b = on_i_p forget_i_i x n b
fun forget_i_s x n b = on_i_s forget_i_i forget_i_p x n b
fun forget_i_k x n b = on_i_k forget_i_s x n b
fun forget_i_mt x n b = on_i_mt forget_i_i forget_i_s forget_i_k x n b
fun forget_t_mt x n b = on_t_mt forget_v x n b
fun forget_i_t x n b = on_i_t forget_i_mt x n b
fun forget_t_t x n b = on_t_t forget_t_mt x n b

fun forget_m_i x n b = on_m_i forget_v x n b
fun forget_m_p x n b = on_m_p forget_m_i x n b
fun forget_m_s x n b = on_m_s forget_m_i forget_m_p x n b
fun forget_m_k x n b = on_m_k forget_m_s x n b
fun forget_m_mt x n b = on_m_mt forget_v forget_m_i forget_m_s forget_m_k x n b
fun forget_m_t x n b = on_m_t forget_m_mt x n b

fun forget_e_e x n b = on_e_e forget_v x n b
                              
end
