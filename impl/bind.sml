structure Bind = struct
open Util
infixr 0 $

(* a series of dependent binds ({name1 : classifier1} {name2 : classifier2} {name3 : classifier3}, inner) *)
         
datatype ('classifier, 'body) bind = Bind of 'body

datatype ('classifier, 'name, 'inner) binds =
         BindNil of 'inner
         | BindCons of 'classifier * ('classifier, 'name * ('classifier, 'name, 'inner) binds) bind

fun unfold_binds binds =
    case binds of
        BindNil inner => ([], inner)
      | BindCons (classifier, Bind (name, binds)) =>
        let val (name_classifiers, inner) = unfold_binds binds
        in
          ((name, classifier) :: name_classifiers, inner)
        end

fun fold_binds (binds, inner) =
    foldr (fn ((name, classifier), binds) => BindCons (classifier, Bind (name, binds))) (BindNil inner) binds

fun binds_length binds = length $ fst $ unfold_binds binds
                                  
end

structure ExprUtil = struct
open Util
infixr 0 $

datatype 'a ibind = BindI of 'a

(* for a series of sorting binds ({name1 : anno1} {name2 : anno2} {name3 : anno3}, inner) *)
datatype ('anno, 'name, 'inner) ibinds =
         NilIB of 'inner
         | ConsIB of 'anno * ('name * ('anno, 'name, 'inner) ibinds) ibind

fun unfold_ibinds ibinds =
    case ibinds of
        NilIB inner => ([], inner)
      | ConsIB (anno, BindI (name, ibinds)) =>
        let val (name_annos, inner) = unfold_ibinds ibinds
        in
          ((name, anno) :: name_annos, inner)
        end

fun fold_ibinds (binds, inner) =
    foldr (fn ((name, anno), ibinds) => ConsIB (anno, BindI (name, ibinds))) (NilIB inner) binds

fun ibinds_length ibinds = length $ fst $ unfold_ibinds ibinds
                                  
end

