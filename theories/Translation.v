From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst SLiftSubst Typing ITyping XTyping.

(* We'll see later if we really need weakening, uniqueness and inversion of
   typing.
 *)

Section Translation.

Open Scope x_scope.

(* Transport in the target *)
(* Maybe it should be added to the common syntax *)
Context (transport : sort -> sterm -> sterm -> sterm -> sterm -> sterm).
Context (tEq : sort -> sterm -> sterm -> sterm -> sterm).
Context (type_transport :
  forall Σ Γ s T1 T2 p t ,
    Σ ;;; Γ |-- p : sEq (succ_sort s) (sSort s) T1 T2 ->
    Σ ;;; Γ |-- t : T1 ->
    Σ ;;; Γ |-- transport s T1 T2 p t : T2
).

(*! Relation for translated expressions *)
Inductive trel (E : list (nat * nat)) : sterm -> sterm -> Prop :=
| trel_assumption x y :
    In (x,y) E ->
    trel E (sRel x) (sRel y)

| trel_Rel x :
    trel E (sRel x) (sRel x)

| trel_transportl t1 t2 s T1 T2 p :
    trel E t1 t2 ->
    trel E (transport s T1 T2 p t1) t2

| trel_transportr t1 t2 s T1 T2 p :
    trel E t1 t2 ->
    trel E t1 (transport s T1 T2 p t2)

| trel_Prod n1 n2 A1 A2 B1 B2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E (sProd n1 A1 B1) (sProd n2 A2 B2)

| trel_Eq s A1 A2 u1 u2 v1 v2 :
    trel E A1 A2 ->
    trel E u1 u2 ->
    trel E v1 v2 ->
    trel E (sEq s A1 u1 v1) (sEq s A2 u2 v2)

| trel_Sort s :
    trel E (sSort s) (sSort s)

| trel_Lambda n1 n2 A1 A2 B1 B2 u1 u2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E u1 u2 ->
    trel E (sLambda n1 A1 B1 u1) (sLambda n2 A2 B2 u2)

(* TODO *)
.

End Translation.