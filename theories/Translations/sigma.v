(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

Local Set Primitive Projections.
Import MonadNotation.

#[universes(template)]
Record sigma A B :=
  mk_sig { π1 : A ; π2 : B π1 }.

Arguments π1 {A B} _.
Arguments π2 {A B} _.
Arguments mk_sig {A B} _ _.

Declare Scope sigma_scope.
Open Scope sigma_scope.

Notation "{ x  &&  P }" := (sigma (fun x => P)) : type_scope.
Notation "{ t : A && P }" := (sigma A (fun t => P)) : type_scope.
Notation "( x ; y )" := (mk_sig x y) : sigma_scope.
Notation "x .1" := (π1 x) : sigma_scope.
Notation "x .2" := (π2 x) : sigma_scope.
Notation "'∃' x .. y , p" := (sigma _ (fun x => .. (sigma _ (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∃'  '/  ' x  ..  y ,  '/  ' p ']'")
                                  : type_scope.

Notation " A × B " := (sigma A (fun _ => B)) (at level 80, right associativity) : type_scope.


MetaRocq Quote Definition tSigma := sigma.
MetaRocq Quote Definition tPair := @mk_sig.
Definition pair (typ1 typ2 t1 t2 : term) : term
  := tApp tPair [ typ1 ; typ2 ; t1 ; t2].
Definition pack (t u : term) : term
  := tApp tSigma [ t ; u ].
MetaRocq Run (t <- tmQuote sigma ;;
            match t with
            | tInd i _ => tmDefinition "sigma_ind" i
            | _ => tmFail "bug"
            end).
Definition proj1 (t : term) : term
  := tProj (mkProjection sigma_ind 2 0) t.
Definition proj2 (t : term) : term
  := tProj (mkProjection sigma_ind 2 1) t.
Definition proj (b : bool) (t : term) : term
  := tProj (mkProjection sigma_ind 2 (if b then 0 else 1)) t.
