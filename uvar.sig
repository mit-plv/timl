(* unification variables ('uvars') for indices and sorts *)                  
signature UVAR_I = sig
  (* all uvars denotate closed entities, which means they cannot be instantiated with things that contain variables (even module variables) *)
  type 'bsort uvar_bs
  type ('bsort, 'idx) uvar_i
  type ('bsort, 'sort) uvar_s
end

(* unification variables ('uvars') for types *)                  
signature UVAR_T = sig
  (* all uvars denotate closed entities, which means they cannot be instantiated with things that contain variables (even module variables) *)
  type ('sort, 'kind, 'mtype) uvar_mt
end

