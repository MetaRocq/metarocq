Set Warnings "-notation-overridden".

Local Set Primitive Projections.
Record sigT {A} (P : A -> Type) : Type := existT
  { projT1 : A ; projT2 : P projT1 }.
Local Unset Primitive Projections.

Definition sigT_ind {A} (B : A -> Type) (P : @sigT A B -> Type)
           (H : forall x y, P (existT _ _ x y))
  : forall s, P s.
Proof.
  destruct s; apply H.
Defined.


Record unit : Type := tt { }.


Generalizable All Variables.

Local Unset Elimination Schemes.
Inductive paths (A : Type) (a : A) : A -> Type :=  idpath : paths A a a.
Definition paths_ind : forall A a (P : forall y, paths A a y -> Type),
    P a (idpath A a) -> forall y p, P y p.
  intros A a P X y p. destruct p; assumption.
Defined.
Definition paths_ind_beta : forall A a P u, paths _ (paths_ind A a P u a (idpath A a)) u.
  reflexivity.
Defined.




(* *********************************************** *)

Arguments sigT {A}%_type P%_type.
Arguments existT {A}%_type P%_type _ _.
Arguments projT1 {A P} _ / .
Arguments projT2 {A P} _ / .

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.

Definition relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : relation A) :=
  reflexivity : forall x : A, R x x.

Class Symmetric {A} (R : relation A) :=
  symmetry : forall x y, R x y -> R y x.

Class Transitive {A} (R : relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.

Class PreOrder {A} (R : relation A) :=
  { PreOrder_Reflexive : Reflexive R ;
    PreOrder_Transitive : Transitive R }.

Global Existing Instance PreOrder_Reflexive.
Global Existing Instance PreOrder_Transitive.

Arguments reflexivity {A R _} / _.
Arguments symmetry {A R _} / _ _ _.
Arguments transitivity {A R _} / {_ _ _} _ _.

Ltac reflexivity :=
  Corelib.Init.Ltac.reflexivity
  || (intros;
      let R := match goal with |- ?R ?x ?y => constr:(R) end in
      let pre_proof_term_head := constr:(@reflexivity _ R _) in
      let proof_term_head := (eval cbn in pre_proof_term_head) in
      apply (pre_proof_term_head : forall x, R x x)).

Ltac symmetry :=
  let R := match goal with |- ?R ?x ?y => constr:(R) end in
  let x := match goal with |- ?R ?x ?y => constr:(x) end in
  let y := match goal with |- ?R ?x ?y => constr:(y) end in
  let pre_proof_term_head := constr:(@symmetry _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head y x _); change (R y x).

Tactic Notation "etransitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  let pre_proof_term_head := constr:(@transitivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head x y z _ _); [ change (R x y) | change (R y z) ].

Tactic Notation "etransitivity" := etransitivity _.

Ltac transitivity x := etransitivity x.

Abbreviation idmap := (fun x => x).

Declare Scope equiv_scope.
Declare Scope path_scope.
Declare Scope fibration_scope.
Declare Scope trunc_scope.

Delimit Scope equiv_scope with equiv.
Delimit Scope function_scope with function.
Delimit Scope path_scope with path.
Delimit Scope fibration_scope with fibration.
Delimit Scope trunc_scope with trunc.

Open Scope trunc_scope.
Open Scope equiv_scope.
Open Scope path_scope.
Open Scope fibration_scope.
Open Scope nat_scope.
Open Scope function_scope.
Open Scope type_scope.
Open Scope core_scope.

Definition const {A B} (b : B) := fun x : A => b.

Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Bind Scope fibration_scope with sigT.
Abbreviation pr1 := projT1.
Abbreviation pr2 := projT2.
Notation "x .1" := (pr1 x) : fibration_scope.
Notation "x .2" := (pr2 x) : fibration_scope.

Abbreviation compose := (fun g f x => g (f x)).
Notation "g 'o' f" := (compose g%function f%function) (at level 40, left associativity) : function_scope.

(* Instance iff_compose : Transitive iff | 1 *)
(*   := fun A B C f g => (fst g o fst f , snd f o snd g). *)
(* Arguments iff_compose {A B C} f g : rename. *)

(* Instance iff_inverse : Symmetric iff | 1 *)
(*   := fun A B f => (snd f , fst f). *)
(* Arguments iff_inverse {A B} f : rename. *)

(* Instance iff_reflexive : Reflexive iff | 1 *)
(*   := fun A => (idmap , idmap). *)

Definition composeD {A B C} (g : forall b, C b) (f : A -> B) := fun x : A => g (f x).
Global Arguments composeD {A B C}%_type_scope (g f)%_function_scope x.
#[global]
Hint Unfold composeD : core.
Notation "g 'oD' f" := (composeD g f) (at level 40, left associativity) : function_scope.

Notation "x = y :> A" := (paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Bind Scope path_scope with paths.
Open Scope path_scope.

Arguments paths {A} _ _.
Arguments idpath {A a} , [A] a.
Arguments paths_ind [A] a P f y p.

Global Instance reflexive_paths {A} : Reflexive (@paths A) | 0 := @idpath A.
Arguments reflexive_paths / .
Notation "1" := (idpath _) : path_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y := paths_ind x (fun y _ => P y) u y p.

Arguments transport {A}%_type_scope P%_function_scope {x y} p%_path_scope u : simpl nomatch.

Definition transport_beta {A} (P : A -> Type) {x : A} (u : P x)
  : transport P 1 u = u
  := paths_ind_beta A x (fun y _ => P y) u.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := transport (fun x' => x' = x) p 1.

Global Instance symmetric_paths {A} : Symmetric (@paths A) | 0 := @inverse A.
Arguments symmetric_paths / .

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  (* := transport (paths _ x) q (transport (fun y => x = y) p 1). *)
  now destruct p, q.
Defined.

Arguments concat {A x y z} p q : simpl nomatch.

Global Instance transitive_paths {A} : Transitive (@paths A) | 0 := @concat A.
Arguments transitive_paths / .

Notation "p @ q" := (concat p%path q%path) (at level 20) : path_scope.
Notation "p ^" := (inverse p%path) (at level 3, format "p '^'") : path_scope.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := transport (fun y => f x = f y) p 1.

Global Arguments ap {A B}%_type_scope f%_function_scope {x y} p%_path_scope.

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Global Arguments pointwise_paths {A}%_type_scope {P} (f g)%_function_scope.

#[global]
Hint Unfold pointwise_paths : typeclass_instances.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => transport (fun g => f x = g x) h 1.

Global Arguments apD10 {A%_type_scope B} {f g}%_function_scope h%_path_scope _.

Definition ap10 {A B} {f g:A->B} (h:f=g) : f == g
  := apD10 h.

Global Arguments ap10 {A B}%_type_scope {f g}%_function_scope h%_path_scope _.

Definition ap11 {A B} {f g:A->B} (h:f=g) {x y:A} (p:x=y) : f x = g y
  := ap10 h x @ ap g p.

Global Arguments ap11 {A B}%_type_scope {f g}%_function_scope h%_path_scope {x y} p%_path_scope.

Arguments ap {A B} f {x y} p : simpl nomatch.

Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  := paths_ind x (fun y p => p # (f x) = f y) (transport_beta _ _) y p.

Arguments apD {A%_type_scope B} f%_function_scope {x y} p%_path_scope : simpl nomatch.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Global Arguments Sect {A B}%_type_scope (s r)%_function_scope.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
                                               equiv_inv : B -> A ;
                                               eisretr : Sect equiv_inv f;
                                               eissect : Sect f equiv_inv;
                                               eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
                                             }.

Arguments eisretr {A B}%_type_scope f%_function_scope {_} _.
Arguments eissect {A B}%_type_scope f%_function_scope {_} _.
Arguments eisadj {A B}%_type_scope f%_function_scope {_} _.
Arguments IsEquiv {A B}%_type_scope f%_function_scope.

Record Equiv A B := BuildEquiv {
                        equiv_fun : A -> B ;
                        equiv_isequiv : IsEquiv equiv_fun
                      }.

Coercion equiv_fun : Equiv >-> Funclass.

Global Existing Instance equiv_isequiv.

Arguments equiv_fun {A B} _ _.
Arguments equiv_isequiv {A B} _.

Bind Scope equiv_scope with Equiv.

Notation "A <~> B" := (Equiv A B) (at level 90) : type_scope.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : function_scope.

Definition ap10_equiv {A B : Type} {f g : A <~> B} (h : f = g) : f == g
  := ap10 (ap equiv_fun h).

Class Contr (A : Type) :=
  BuildContr { center : A ;
               contr : (forall y : A, center = y) }.

Arguments center A {_}.


Class Funext := { isequiv_apD10 : forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

#[export] Existing Instance isequiv_apD10.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) : f == g -> f = g
  := (@apD10 A P f g)^-1.

Global Arguments path_forall {_ A%_type_scope P} (f g)%_function_scope _.

Definition path_forall2 `{Funext} {A B : Type} {P : A -> B -> Type} (f g : forall x y, P x y) :
  (forall x y, f x y = g x y) -> f = g
  :=
    (fun E => path_forall f g (fun x => path_forall (f x) (g x) (E x))).

Global Arguments path_forall2 {_} {A B}%_type_scope {P} (f g)%_function_scope _.



(* PathGroupoid.v *)

Definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ 1 = p.
  now destruct p.
Defined.

Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  1 @ p = p.
  now destruct p.
Defined.


Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r.
  now destruct p, q, r.
Defined.

Definition concat_pp_p {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p @ q) @ r = p @ (q @ r).
  now destruct p, q, r.
Defined.

Definition concat_pV {A : Type} {x y : A} (p : x = y) :
  p @ p^ = 1.
  now destruct p.
Defined.

Definition concat_Vp {A : Type} {x y : A} (p : x = y) :
  p^ @ p = 1.
  now destruct p.
Defined.

Definition concat_V_pp {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  p^ @ (p @ q) = q.
  now destruct p, q.
Defined.

Definition concat_p_Vp {A : Type} {x y z : A} (p : x = y) (q : x = z) :
  p @ (p^ @ q) = q.
  now destruct p, q.
Defined.

Definition concat_pp_V {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q) @ q^ = p.
  now destruct p, q.
Defined.

Definition concat_pV_p {A : Type} {x y z : A} (p : x = z) (q : y = z) :
  (p @ q^) @ q = p.
  now destruct p, q.
Defined.

Definition inv_pp {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q)^ = q^ @ p^.
  now destruct p, q.
Defined.

Definition inv_Vp {A : Type} {x y z : A} (p : y = x) (q : y = z) :
  (p^ @ q)^ = q^ @ p.
  now destruct p, q.
Defined.

Definition inv_pV {A : Type} {x y z : A} (p : x = y) (q : z = y) :
  (p @ q^)^ = q @ p^.
  now destruct p, q.
Defined.

Definition inv_VV {A : Type} {x y z : A} (p : y = x) (q : z = y) :
  (p^ @ q^)^ = q @ p.
  now destruct p, q.
Defined.

Definition inv_V {A : Type} {x y : A} (p : x = y) :
  p^^ = p.
  now destruct p.
Defined.

Definition moveR_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  p = r^ @ q -> r @ p = q.
Proof.
  destruct r.
  intro h. exact (concat_1p _ @ h @ concat_1p _).
Defined.

Definition moveR_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r = q @ p^ -> r @ p = q.
Proof.
  destruct p.
  intro h. exact (concat_p1 _ @ h @ concat_p1 _).
Defined.

Definition moveR_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  p = r @ q -> r^ @ p = q.
Proof.
  destruct r.
  intro h. exact (concat_1p _ @ h @ concat_1p _).
Defined.

Definition moveR_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  r = q @ p -> r @ p^ = q.
Proof.
  destruct p.
  intro h. exact (concat_p1 _ @ h @ concat_p1 _).
Defined.

Definition moveL_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r^ @ q = p -> q = r @ p.
Proof.
  destruct r.
  intro h. exact ((concat_1p _)^ @ h @ (concat_1p _)^).
Defined.

Definition moveL_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q @ p^ = r -> q = r @ p.
Proof.
  destruct p.
  intro h. exact ((concat_p1 _)^ @ h @ (concat_p1 _)^).
Defined.

Definition moveL_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> q = r^ @ p.
Proof.
  destruct r.
  intro h. exact ((concat_1p _)^ @ h @ (concat_1p _)^).
Defined.

Definition moveL_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  q @ p = r -> q = r @ p^.
Proof.
  destruct p.
  intro h. exact ((concat_p1 _)^ @ h @ (concat_p1 _)^).
Defined.

Definition moveL_1M {A : Type} {x y : A} (p q : x = y) :
  p @ q^ = 1 -> p = q.
Proof.
  destruct q.
  intro h. exact ((concat_p1 _)^ @ h).
Defined.

Definition moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  q^ @ p = 1 -> p = q.
Proof.
  destruct q.
  intro h. exact ((concat_1p _)^ @ h).
Defined.

Definition moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  p @ q = 1 -> p = q^.
Proof.
  destruct q.
  intro h. exact ((concat_p1 _)^ @ h).
Defined.

Definition moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  q @ p = 1 -> p = q^.
Proof.
  destruct q.
  intro h. exact ((concat_1p _)^ @ h).
Defined.

Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  1 = p^ @ q -> p = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_1p _)).
Defined.

Definition moveR_1M {A : Type} {x y : A} (p q : x = y) :
  1 = q @ p^ -> p = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_p1 _)).
Defined.

Definition moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = q @ p -> p^ = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_p1 _)).
Defined.

Definition moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = p @ q -> p^ = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_1p _)).
Defined.

Definition moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : u = p^ # v -> p # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : u = p # v -> p^ # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : p # u = v -> u = p^ # v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : p^ # u = v -> u = p # v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveR_transport_p_V {A : Type} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (q : u = p^ # v)
  : (moveR_transport_p P p u v q)^ = moveL_transport_p P p v u q^.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveR_transport_V_V {A : Type} (P : A -> Type) {x y : A}
           (p : y = x) (u : P x) (v : P y) (q : u = p # v)
  : (moveR_transport_V P p u v q)^ = moveL_transport_V P p v u q^.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveL_transport_V_V {A : Type} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (q : p # u = v)
  : (moveL_transport_V P p u v q)^ = moveR_transport_V P p v u q^.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveL_transport_p_V {A : Type} (P : A -> Type) {x y : A}
           (p : y = x) (u : P x) (v : P y) (q : p^ # u = v)
  : (moveL_transport_p P p u v q)^ = moveR_transport_p P p v u q^.
Proof.
  destruct p; reflexivity.
Defined.


Definition ap_1 {A B : Type} (x : A) (f : A -> B) :
  ap f 1 = 1 :> (f x = f x)
  := 1.

Definition apD_1 {A B} (x : A) (f : forall x : A, B x) :
  apD f 1 = 1 :> (f x = f x)
  := 1.

Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q).
  now destruct p, q.
Defined.

Definition ap_p_pp {A B : Type} (f : A -> B) {w : B} {x y z : A}
  (r : w = f x) (p : x = y) (q : y = z) :
  r @ (ap f (p @ q)) = (r @ ap f p) @ (ap f q).
Proof.
  destruct p, q. simpl. exact (concat_p_pp r 1 1).
Defined.

Definition ap_pp_p {A B : Type} (f : A -> B) {x y z : A} {w : B}
  (p : x = y) (q : y = z) (r : f z = w) :
  (ap f (p @ q)) @ r = (ap f p) @ (ap f q @ r).
Proof.
  destruct p, q. simpl. exact (concat_pp_p 1 1 r).
Defined.

Definition inverse_ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  (ap f p)^ = ap f (p^).
  now destruct p.
Defined.

Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (p^) = (ap f p)^.
  now destruct p.
Defined.

Definition ap_idmap {A : Type} {x y : A} (p : x = y) :
  ap idmap p = p.
  now destruct p.
Defined.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g o f) p = ap g (ap f p).
  now destruct p.
Defined.

Definition ap_compose' {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun a => g (f a)) p = ap g (ap f p).
  now destruct p.
Defined.

Definition ap_const {A B : Type} {x y : A} (p : x = y) (z : B) :
  ap (fun _ => z) p = 1.
  now destruct p.
Defined.

Definition concat_Ap {A B : Type} {f g : A -> B} (p : forall x, f x = g x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ (ap g q).
  destruct q. cbn. now rewrite concat_p1, concat_1p.
Defined.

Definition concat_A1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ q.
  destruct q. cbn. now rewrite concat_p1, concat_1p.
Defined.

Definition concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) =  q @ (p y).
  destruct q. cbn. now rewrite concat_p1, concat_1p.
Defined.

Definition concat_pA_pp {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {w z : B} (r : w = f x) (s : g y = z)
  :
  (r @ ap f q) @ (p y @ s) = (r @ p x) @ (ap g q @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_pA_p {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {w : B} (r : w = f x)
  :
  (r @ ap f q) @ p y = (r @ p x) @ ap g q.
Proof.
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_A_pp {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {z : B} (s : g y = z)
  :
  (ap f q) @ (p y @ s) = (p x) @ (ap g q @ s).
Proof.
  destruct q, s; cbn.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
Defined.

Definition concat_pA1_pp {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = f x) (s : y = z)
  :
  (r @ ap f q) @ (p y @ s) = (r @ p x) @ (q @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_pp_A1p {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = x) (s : g y = z)
  :
  (r @ p x) @ (ap g q @ s) = (r @ q) @ (p y @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_pA1_p {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w : A} (r : w = f x)
  :
  (r @ ap f q) @ p y = (r @ p x) @ q.
Proof.
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_A1_pp {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {z : A} (s : y = z)
  :
  (ap f q) @ (p y @ s) = (p x) @ (q @ s).
Proof.
  destruct q, s; cbn.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
Defined.

Definition concat_pp_A1 {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w : A} (r : w = x)
  :
  (r @ p x) @ ap g q = (r @ q) @ p y.
Proof.
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_p_A1p {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {z : A} (s : g y = z)
  :
  p x @ (ap g q @ s) = q @ (p y @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
Defined.

Lemma concat_1p_1 {A} {x : A} (p : x = x) (q : p = 1)
: concat_1p p @ q = ap (fun p' => 1 @ p') q.
Proof.
  rewrite <- (inv_V q).
  set (r := q^). clearbody r; clear q; destruct r.
  reflexivity.
Defined.

Lemma concat_p1_1 {A} {x : A} (p : x = x) (q : p = 1)
: concat_p1 p @ q = ap (fun p' => p' @ 1) q.
Proof.
  rewrite <- (inv_V q).
  set (r := q^). clearbody r; clear q; destruct r.
  reflexivity.
Defined.

Definition apD10_1 {A} {B:A->Type} (f : forall x, B x) (x:A)
  : apD10 (idpath f) x = 1
:= 1.

Definition apD10_pp {A} {B:A->Type} {f f' f'' : forall x, B x}
  (h:f=f') (h':f'=f'') (x:A)
: apD10 (h @ h') x = apD10 h x @ apD10 h' x.
Proof.
  case h, h'; reflexivity.
Defined.

Definition apD10_V {A} {B:A->Type} {f g : forall x, B x} (h:f=g) (x:A)
  : apD10 (h^) x = (apD10 h x)^.
  now destruct h.
Defined.

Definition ap10_1 {A B} {f:A->B} (x:A) : ap10 (idpath f) x = 1
  := 1.

Definition ap10_pp {A B} {f f' f'':A->B} (h:f=f') (h':f'=f'') (x:A)
  : ap10 (h @ h') x = ap10 h x @ ap10 h' x
:= apD10_pp h h' x.

Definition ap10_V {A B} {f g : A->B} (h : f = g) (x:A)
  : ap10 (h^) x = (ap10 h x)^
:= apD10_V h x.

Definition apD10_ap_precompose {A B C} (f : A -> B) {g g' : forall x:B, C x} (p : g = g') a
: apD10 (ap (fun h : forall x:B, C x => h oD f) p) a = apD10 p (f a).
Proof.
  destruct p; reflexivity.
Defined.

Definition ap10_ap_precompose {A B C} (f : A -> B) {g g' : B -> C} (p : g = g') a
: ap10 (ap (fun h : B -> C => h o f) p) a = ap10 p (f a)
  := apD10_ap_precompose f p a.

Definition apD10_ap_postcompose {A B C} (f : forall x, B x -> C) {g g' : forall x:A, B x} (p : g = g') a
: apD10 (ap (fun h : forall x:A, B x => fun x => f x (h x)) p) a = ap (f a) (apD10 p a).
Proof.
  destruct p; reflexivity.
Defined.

Definition ap10_ap_postcompose {A B C} (f : B -> C) {g g' : A -> B} (p : g = g') a
: ap10 (ap (fun h : A -> B => f o h) p) a = ap f (ap10 p a)
:= apD10_ap_postcompose (fun a => f) p a.


Definition transport_1 {A : Type} (P : A -> Type) {x : A} (u : P x)
  : 1 # u = u
:= 1.

Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u.
  now destruct p, q.
Defined.

Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : p # p^ # z = z
  := (transport_pp P p^ p z)^
  @ ap (fun r => transport P r z) (concat_Vp p).

Definition transport_Vp {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P x)
  : p^ # p # z = z
  := (transport_pp P p p^ z)^
  @ ap (fun r => transport P r z) (concat_pV p).

Definition transport_p_pp {A : Type} (P : A -> Type)
  {x y z w : A} (p : x = y) (q : y = z) (r : z = w)
  (u : P x)
  : ap (fun e => e # u) (concat_p_pp p q r)
    @ (transport_pp P (p@q) r u) @ ap (transport P r) (transport_pp P p q u)
  = (transport_pp P p (q@r) u) @ (transport_pp P q r (p#u))
  :> ((p @ (q @ r)) # u = r # q # p # u) .
Proof.
  destruct p, q, r.  simpl.  exact 1.
Defined.

Definition transport_pVp {A} (P : A -> Type) {x y:A} (p:x=y) (z:P x)
  : transport_pV P p (transport P p z)
  = ap (transport P p) (transport_Vp P p z).
Proof.
  destruct p; reflexivity.
Defined.

Definition transport_VpV {A} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : transport_Vp P p (transport P p^ z)
    = ap (transport P p^) (transport_pV P p z).
Proof.
  destruct p; reflexivity.
Defined.

Definition ap_transport_transport_pV {A} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (e : transport P p u = v)
  : ap (transport P p) (moveL_transport_V P p u v e)
       @ transport_pV P p v = e.
Proof.
    now destruct e, p.
Defined.

Definition moveL_transport_V_1 {A} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x)
  : moveL_transport_V P p u (p # u) 1 = (transport_Vp P p u)^.
Proof.
  destruct p; reflexivity.
Defined.



Definition ap11_is_ap10_ap01 {A B} {f g:A->B} (h:f=g) {x y:A} (p:x=y)
: ap11 h p = ap10 h x @ ap g p.
  now destruct h, p.
Defined.

Definition transportD {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y)
  : C x2 (p # y).
  now destruct p.
Defined.

Definition transportD2 {A : Type} (B C : A -> Type) (D : forall a:A, B a -> C a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D x1 y z)
  : D x2 (p # y) (p # z).
  now destruct p.
Defined.

Definition ap011 {A B C} (f : A -> B -> C) {x x' y y'} (p : x = x') (q : y = y')
: f x y = f x' y'
:= ap11 (ap f p) q.

Definition ap011D {A B C} (f : forall (a:A), B a -> C)
           {x x'} (p : x = x') {y y'} (q : p # y = y')
: f x y = f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition ap01D1 {A B C} (f : forall (a:A), B a -> C a)
           {x x'} (p : x = x') {y y'} (q : p # y = y')
: transport C p (f x y) = f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition apD011 {A B C} (f : forall (a:A) (b:B a), C a b)
           {x x'} (p : x = x') {y y'} (q : p # y = y')
: transport (C x') q (transportD B C p y (f x y)) = f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport2 {A : Type} (P : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : P x)
  : p # z = q # z
  := ap (fun p' => p' # z) r.

Definition transport2_is_ap10 {A : Type} (Q : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : Q x)
  : transport2 Q r z = ap10 (ap (transport Q) r) z.
  now destruct r.
Defined.

Definition transport2_p2p {A : Type} (P : A -> Type) {x y : A} {p1 p2 p3 : x = y}
  (r1 : p1 = p2) (r2 : p2 = p3) (z : P x)
  : transport2 P (r1 @ r2) z = transport2 P r1 z @ transport2 P r2 z.
Proof.
  destruct r1, r2; reflexivity.
Defined.

Definition transport2_V {A : Type} (Q : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : Q x)
  : transport2 Q (r^) z = (transport2 Q r z)^.
  now destruct r.
Defined.

Definition concat_AT {A : Type} (P : A -> Type) {x y : A} {p q : x = y}
  {z w : P x} (r : p = q) (s : z = w)
  : ap (transport P p) s  @  transport2 P r w
    = transport2 P r z  @  ap (transport P q) s.
  now destruct r, s.
Defined.

Lemma ap_transport {A} {P Q : A -> Type} {x y : A} (p : x = y) (f : forall x, P x -> Q x) (z : P x) :
  f y (p # z) = (p # (f x z)).
  now destruct p.
Defined.

Lemma ap_transportD {A : Type}
      (B : A -> Type) (C1 C2 : forall a : A, B a -> Type)
      (f : forall a b, C1 a b -> C2 a b)
      {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C1 x1 y)
: f x2 (p # y) (transportD B C1 p y z)
  = transportD B C2 p y (f x1 y z).
Proof.
  now destruct p.
Defined.

Lemma ap_transportD2 {A : Type}
      (B C : A -> Type) (D1 D2 : forall a, B a -> C a -> Type)
      (f : forall a b c, D1 a b c -> D2 a b c)
      {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D1 x1 y z)
: f x2 (p # y) (p # z) (transportD2 B C D1 p y z w)
  = transportD2 B C D2 p y z (f x1 y z w).
Proof.
  now destruct p.
Defined.

Lemma ap_transport_pV {X} (Y : X -> Type) {x1 x2 : X} (p : x1 = x2)
      {y1 y2 : Y x2} (q : y1 = y2)
: ap (transport Y p) (ap (transport Y p^) q) =
  transport_pV Y p y1 @ q @ (transport_pV Y p y2)^.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_pV_ap {X} (P : X -> Type) (f : forall x, P x)
      {x1 x2 : X} (p : x1 = x2)
: ap (transport P p) (apD f p^) @ apD f p = transport_pV P p (f x2).
Proof.
  destruct p; reflexivity.
Defined.

Definition apD_pp {A} {P : A -> Type} (f : forall x, P x)
           {x y z : A} (p : x = y) (q : y = z)
  : apD f (p @ q)
    = transport_pp P p q (f x) @ ap (transport P q) (apD f p) @ apD f q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition apD_V {A} {P : A -> Type} (f : forall x, P x)
           {x y : A} (p : x = y)
  : apD f p^ = moveR_transport_V _ _ _ _ (apD f p)^.
Proof.
  destruct p; reflexivity.
Defined.
Definition transport_const {A B : Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport (fun x => B) p y = y.
Proof.
  destruct p.  exact 1.
Defined.

Definition transport2_const {A B : Type} {x1 x2 : A} {p q : x1 = x2}
  (r : p = q) (y : B)
  : transport_const p y = transport2 (fun _ => B) r y @ transport_const q y.
  destruct r. symmetry; apply concat_1p.
Defined.

Lemma transport_compose {A B} {x y : A} (P : B -> Type) (f : A -> B)
  (p : x = y) (z : P (f x))
  : transport (fun x => P (f x)) p z  =  transport P (ap f p) z.
Proof.
  destruct p; reflexivity.
Defined.

Lemma transportD_compose {A A'} B {x x' : A} (C : forall x : A', B x -> Type) (f : A -> A')
      (p : x = x') y (z : C (f x) y)
: transportD (B o f) (C oD f) p y z
  = transport (C (f x')) (transport_compose B f p y)^ (transportD B C (ap f p) y z).
Proof.
  destruct p; reflexivity.
Defined.

Lemma transport_apD_transportD {A} B (f : forall x : A, B x) (C : forall x, B x -> Type)
      {x1 x2 : A} (p : x1 = x2) (z : C x1 (f x1))
: apD f p # transportD B C p _ z
  = transport (fun x => C x (f x)) p z.
Proof.
  destruct p; reflexivity.
Defined.

Lemma transport_precompose {A B C} (f : A -> B) (g g' : B -> C) (p : g = g')
: transport (fun h : B -> C => g o f = h o f) p 1 =
  ap (fun h => h o f) p.
Proof.
  destruct p; reflexivity.
Defined.

Definition transport_idmap_ap A (P : A -> Type) x y (p : x = y) (u : P x)
: transport P p u = transport idmap (ap P p) u.
  now destruct p.
Defined.

(** Sometimes, it's useful to have the goal be in terms of [ap], so we can use lemmas about [ap].  However, we can't just [rewrite !transport_idmap_ap], as that's likely to loop.  So, instead, we provide a tactic [transport_to_ap], that replaces all [transport P p u] with [transport idmap (ap P p) u] for non-[idmap] [P]. *)
Ltac transport_to_ap :=
  repeat match goal with
           | [ |- context[transport ?P ?p ?u] ]
             => match P with
                  | idmap => fail 1 (* we don't want to turn [transport idmap (ap _ _)] into [transport idmap (ap idmap (ap _ _))] *)
                  | _ => idtac
                end;
               progress rewrite (transport_idmap_ap _ P _ _ p u)
         end.

Definition transport_transport {A B} (C : A -> B -> Type)
           {x1 x2 : A} (p : x1 = x2) {y1 y2 : B} (q : y1 = y2)
           (c : C x1 y1)
: transport (C x2) q (transport (fun x => C x y1) p c)
  = transport (fun x => C x y2) p (transport (C x1) q c).
Proof.
  destruct p, q; reflexivity.
Defined.

Lemma apD_const {A B} {x y : A} (f : A -> B) (p: x = y) :
  apD f p = transport_const p (f x) @ ap f p.
Proof.
  destruct p; reflexivity.
Defined.

Definition concat2 {A} {x y z : A} {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q')
  : p @ q = p' @ q'.
  now destruct h, h'.
Defined.

Notation "p @@ q" := (concat2 p q)%path (at level 20) : path_scope.

Arguments concat2 : simpl nomatch.

Lemma concat2_ap_ap {A B : Type} {x' y' z' : B}
           (f : A -> (x' = y')) (g : A -> (y' = z'))
           {x y : A} (p : x = y)
: (ap f p) @@ (ap g p) = ap (fun u => f u @ g u) p.
Proof.
    now destruct p.
Defined.

Definition inverse2 {A : Type} {x y : A} {p q : x = y} (h : p = q)
  : p^ = q^
:= ap inverse h.

Lemma ap_pp_concat_pV {A B} (f : A -> B) {x y : A} (p : x = y)
: ap_pp f p p^ @ ((1 @@ ap_V f p) @ concat_pV (ap f p))
  = ap (ap f) (concat_pV p).
Proof.
  destruct p; reflexivity.
Defined.

Lemma ap_pp_concat_Vp {A B} (f : A -> B) {x y : A} (p : x = y)
: ap_pp f p^ p @ ((ap_V f p @@ 1) @ concat_Vp (ap f p))
  = ap (ap f) (concat_Vp p).
Proof.
  destruct p; reflexivity.
Defined.

Lemma concat_pV_inverse2 {A} {x y : A} (p q : x = y) (r : p = q)
: (r @@ inverse2 r) @ concat_pV q = concat_pV p.
Proof.
  destruct r, p; reflexivity.
Defined.

Lemma concat_Vp_inverse2 {A} {x y : A} (p q : x = y) (r : p = q)
: (inverse2 r @@ r) @ concat_Vp q = concat_Vp p.
Proof.
  destruct r, p; reflexivity.
Defined.

Definition whiskerL {A : Type} {x y z : A} (p : x = y)
  {q r : y = z} (h : q = r) : p @ q = p @ r
:= 1 @@ h.

Definition whiskerR {A : Type} {x y z : A} {p q : x = y}
  (h : p = q) (r : y = z) : p @ r = q @ r
:= h @@ 1.

Definition cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
: (p @ q = p @ r) -> (q = r)
:= fun h => (concat_V_pp p q)^ @ whiskerL p^ h @ (concat_V_pp p r).

Definition cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p @ r = q @ r) -> (p = q)
:= fun h => (concat_pp_V p r)^ @ whiskerR h r^ @ (concat_pp_V q r).

Definition whiskerR_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  (concat_p1 p) ^ @ whiskerR h 1 @ concat_p1 q = h.
  now destruct h, p.
Defined.

Definition whiskerR_1p {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  whiskerR 1 q = 1 :> (p @ q = p @ q).
  reflexivity.
Defined.

Definition whiskerL_p1 {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  whiskerL p 1 = 1 :> (p @ q = p @ q).
  reflexivity.
Defined.

Definition whiskerL_1p {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  (concat_1p p) ^ @ whiskerL 1 h @ concat_1p q = h.
  now destruct h, p.
Defined.

Definition whiskerR_p1_1 {A} {x : A} (h : idpath x = idpath x)
: whiskerR h 1 = h.
Proof.
  refine (_ @ whiskerR_p1 h); simpl.
  symmetry; refine (concat_p1 _ @ concat_1p _).
Defined.

Definition whiskerL_1p_1 {A} {x : A} (h : idpath x = idpath x)
: whiskerL 1 h = h.
Proof.
  refine (_ @ whiskerL_1p h); simpl.
  symmetry; refine (concat_p1 _ @ concat_1p _).
Defined.

Definition concat2_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  h @@ 1 = whiskerR h 1 :> (p @ 1 = q @ 1).
  now destruct h.
Defined.

Definition concat2_1p {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  1 @@ h = whiskerL 1 h :> (1 @ p = 1 @ q).
  now destruct h.
Defined.

Definition cancel2L {A : Type} {x y z : A} {p p' : x = y} {q q' : y = z}
           (g : p = p') (h k : q = q')
: (g @@ h = g @@ k) -> (h = k).
Proof.
  intro r. destruct g, p, q.
  refine ((whiskerL_1p h)^ @ _). refine (_ @ (whiskerL_1p k)).
  refine (whiskerR _ _). refine (whiskerL _ _).
  apply r.
Defined.

Definition cancel2R {A : Type} {x y z : A} {p p' : x = y} {q q' : y = z}
           (g h : p = p') (k : q = q')
: (g @@ k = h @@ k) -> (g = h).
Proof.
  intro r. destruct k, p, q.
  refine ((whiskerR_p1 g)^ @ _). refine (_ @ (whiskerR_p1 h)).
  refine (whiskerR _ _). refine (whiskerL _ _).
  apply r.
Defined.

Definition whiskerL_pp {A} {x y z : A} (p : x = y) {q q' q'' : y = z}
           (r : q = q') (s : q' = q'')
: whiskerL p (r @ s) = whiskerL p r @ whiskerL p s.
Proof.
  destruct p, r, s; reflexivity.
Defined.

Definition whiskerR_pp {A} {x y z : A} {p p' p'' : x = y} (q : y = z)
           (r : p = p') (s : p' = p'')
: whiskerR (r @ s) q = whiskerR r q @ whiskerR s q.
Proof.
  destruct q, r, s; reflexivity.
Defined.

Definition whiskerL_VpL {A} {x y z : A} (p : x = y)
           {q q' : y = z} (r : q = q')
: (concat_V_pp p q)^ @ whiskerL p^ (whiskerL p r) @ concat_V_pp p q'
  = r.
Proof.
  destruct p, r, q. reflexivity.
Defined.

Definition whiskerL_pVL {A} {x y z : A} (p : y = x)
           {q q' : y = z} (r : q = q')
: (concat_p_Vp p q)^ @ whiskerL p (whiskerL p^ r) @ concat_p_Vp p q'
  = r.
Proof.
  destruct p, r, q. reflexivity.
Defined.

Definition whiskerR_pVR {A} {x y z : A} {p p' : x = y}
           (r : p = p') (q : y = z)
: (concat_pp_V p q)^ @ whiskerR (whiskerR r q) q^ @ concat_pp_V p' q
  = r.
Proof.
  destruct p, r, q. reflexivity.
Defined.

Definition whiskerR_VpR {A} {x y z : A} {p p' : x = y}
           (r : p = p') (q : z = y)
: (concat_pV_p p q)^ @ whiskerR (whiskerR r q^) q @ concat_pV_p p' q
  = r.
Proof.
  destruct p, r, q. reflexivity.
Defined.

Definition concat_concat2 {A : Type} {x y z : A} {p p' p'' : x = y} {q q' q'' : y = z}
  (a : p = p') (b : p' = p'') (c : q = q') (d : q' = q'') :
  (a @@ c) @ (b @@ d) = (a @ b) @@ (c @ d).
Proof.
  case d.
  case c.
  case b.
  case a.
  reflexivity.
Defined.

Definition concat_whisker {A} {x y z : A} (p p' : x = y) (q q' : y = z) (a : p = p') (b : q = q') :
  (whiskerR a q) @ (whiskerL p' b) = (whiskerL p b) @ (whiskerR a q').
  destruct b, a; symmetry; eapply concat_1p.
Defined.

Definition pentagon {A : Type} {v w x y z : A} (p : v = w) (q : w = x) (r : x = y) (s : y = z)
  : whiskerL p (concat_p_pp q r s)
      @ concat_p_pp p (q@r) s
      @ whiskerR (concat_p_pp p q r) s
  = concat_p_pp p q (r@s) @ concat_p_pp (p@q) r s.
Proof.
  case p, q, r, s.  reflexivity.
Defined.

Definition triangulator {A : Type} {x y z : A} (p : x = y) (q : y = z)
  : concat_p_pp p 1 q @ whiskerR (concat_p1 p) q
  = whiskerL p (concat_1p q).
Proof.
  case p, q.  reflexivity.
Defined.

Definition eckmann_hilton {A : Type} {x:A} (p q : 1 = 1 :> (x = x)) : p @ q = q @ p :=
  (whiskerR_p1 p @@ whiskerL_1p q)^
  @ (concat_p1 _ @@ concat_p1 _)
  @ (concat_1p _ @@ concat_1p _)
  @ (concat_whisker _ _ _ _ p q)
  @ (concat_1p _ @@ concat_1p _)^
  @ (concat_p1 _ @@ concat_p1 _)^
  @ (whiskerL_1p q @@ whiskerR_p1 p).

Definition ap02 {A B : Type} (f:A->B) {x y:A} {p q:x=y} (r:p=q) : ap f p = ap f q.
  now destruct r.
Defined.

Definition ap02_pp {A B} (f:A->B) {x y:A} {p p' p'':x=y} (r:p=p') (r':p'=p'')
  : ap02 f (r @ r') = ap02 f r @ ap02 f r'.
Proof.
  case r, r'; reflexivity.
Defined.

Definition ap02_p2p {A B} (f:A->B) {x y z:A} {p p':x=y} {q q':y=z} (r:p=p') (s:q=q')
  : ap02 f (r @@ s) =   ap_pp f p q
                      @ (ap02 f r  @@  ap02 f s)
                      @ (ap_pp f p' q')^.
Proof.
  case r, s, p, q. reflexivity.
Defined.

Definition apD02 {A : Type} {B : A -> Type} {x y : A} {p q : x = y}
  (f : forall x, B x) (r : p = q)
  : apD f p = transport2 B r (f x) @ apD f q.
  destruct r; symmetry; eapply concat_1p.
Defined.

Definition apD02_const {A B : Type} (f : A -> B) {x y : A} {p q : x = y} (r : p = q)
: apD02 f r = (apD_const f p)
              @ (transport2_const r (f x) @@ ap02 f r)
              @ (concat_p_pp _ _ _)^
              @ (whiskerL (transport2 _ r (f x)) (apD_const f q)^).
  now destruct r, p.
Defined.

Definition apD02_pp {A} (B : A -> Type) (f : forall x:A, B x) {x y : A}
  {p1 p2 p3 : x = y} (r1 : p1 = p2) (r2 : p2 = p3)
  : apD02 f (r1 @ r2)
  = apD02 f r1
  @ whiskerL (transport2 B r1 (f x)) (apD02 f r2)
  @ concat_p_pp _ _ _
  @ (whiskerR (transport2_p2p B r1 r2 (f x))^ (apD f p3)).
Proof.
  destruct r1, r2. destruct p1. reflexivity.
Defined.

Definition ap_transport_Vp_idmap {A B} (p q : A = B) (r : q = p) (z : A)
: ap (transport idmap q^) (ap (fun s => transport idmap s z) r)
  @ ap (fun s => transport idmap s (p # z)) (inverse2 r)
  @ transport_Vp idmap p z
  = transport_Vp idmap q z.
Proof.
  now destruct r, q.
Defined.

Definition ap_transport_pV_idmap {A B} (p q : A = B) (r : q = p) (z : B)
: ap (transport idmap q) (ap (fun s => transport idmap s^ z) r)
  @ ap (fun s => transport idmap s (p^ # z)) r
  @ transport_pV idmap p z
  = transport_pV idmap q z.
Proof.
  now destruct r, q.
Defined.

Abbreviation concatR := (fun p q => concat q p).

#[global]
Hint Resolve
  concat_1p concat_p1 concat_p_pp
  inv_pp inv_V
 : path_hints.

#[global]
Hint Rewrite
@concat_p1
@concat_1p
@concat_p_pp (* there is a choice here !*)
@concat_pV
@concat_Vp
@concat_V_pp
@concat_p_Vp
@concat_pp_V
@concat_pV_p
(*@inv_pp*) (* I am not sure about this one *)
@inv_V
@moveR_Mp
@moveR_pM
@moveL_Mp
@moveL_pM
@moveL_1M
@moveL_M1
@moveR_M1
@moveR_1M
@ap_1
(* @ap_pp
@ap_p_pp ?*)
@inverse_ap
@ap_idmap
(* @ap_compose
@ap_compose'*)
@ap_const
(* Unsure about naturality of [ap], was absent in the old implementation*)
@apD10_1
:paths.

Ltac hott_simpl :=
  autorewrite with paths in * |- * ; auto with path_hints.

(* Contractible.v *)


(** If a space is contractible, then any two points in it are connected by a path in a canonical way. *)
Definition path_contr `{Contr A} (x y : A) : x = y
  := (contr x)^ @ (contr y).

(** Similarly, any two parallel paths in a contractible space are homotopic, which is just the principle UIP. *)
Definition path2_contr `{Contr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
    intro r; destruct r; symmetry; now apply concat_Vp.
  transitivity (path_contr x y). apply K. symmetry; apply K.
Defined.

(** It follows that any space of paths in a contractible space is contractible. *)
(** Because [Contr] is a notation, and [Contr_internal] is the record, we need to iota expand to fool Rocq's typeclass machinery into accepting supposedly "mismatched" contexts. *)

Global Instance contr_paths_contr `{Contr A} (x y : A) : Contr (x = y) | 10000 := let c := {|
  center := (contr x)^ @ contr y;
  contr := path2_contr ((contr x)^ @ contr y)
|} in c.

(** Also, the total space of any based path space is contractible.  We define the [contr] fields as separate definitions, so that we can give them [simpl nomatch] annotations. *)

Definition path_basedpaths {X : Type} {x y : X} (p : x = y)
: (x;1) = (y;p) :> {z:X & x=z}.
Proof.
  destruct p; reflexivity.
Defined.

Arguments path_basedpaths {X x y} p : simpl nomatch.

Global Instance contr_basedpaths {X : Type} (x : X) : Contr {y : X & x = y} | 100.
Proof.
  exists (x ; 1).
  intros [y p]; apply path_basedpaths.
Defined.

(* ??? *)
Definition path_basedpaths' {X : Type} {x y : X} (p : y = x)
: @existT _ (fun z => @paths X z x) x 1 = (y; p).
Proof.
  destruct p; reflexivity.
Defined.

Global Instance contr_basedpaths' {X : Type} (x : X) : Contr {y : X & y = x} | 100.
Proof.
  refine (BuildContr _ (@existT _ (fun z => @paths X z x) x 1) _).
  intros [y p]; apply path_basedpaths'.
Defined.

Arguments path_basedpaths' {X x y} p : simpl nomatch.

Definition ap_pr1_path_contr_basedpaths {X : Type}
           {x y z : X} (p : x = y) (q : x = z)
: ap pr1 (path_contr ((y;p):{y':X & x = y'}) (z;q)) = p^ @ q.
Proof.
  destruct p,q; reflexivity.
Defined.

Definition ap_pr1_path_contr_basedpaths' {X : Type}
           {x y z : X} (p : y = x) (q : z = x)
: ap pr1 (path_contr ((y;p):{y':X & y' = x}) (z;q)) = p @ q^.
Proof.
  destruct p,q; reflexivity.
Defined.

Definition ap_pr1_path_basedpaths {X : Type}
           {x y : X} (p : x = y)
: ap pr1 (path_basedpaths p) = p.
Proof.
  destruct p; reflexivity.
Defined.

Definition ap_pr1_path_basedpaths' {X : Type}
           {x y : X} (p : y = x)
: ap pr1 (path_basedpaths' p) = p^.
Proof.
  destruct p; reflexivity.
Defined.

(** If the domain is contractible, the function is propositionally constant. *)
Definition contr_dom_equiv {A B} (f : A -> B) `{Contr A} : forall x y : A, f x = f y
  := fun x y => ap f ((contr x)^ @ contr y).


(* Equivalences.v *)

Global Instance isequiv_idmap (A : Type) : IsEquiv idmap | 0 :=
  BuildIsEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).

Definition equiv_idmap (A : Type) : A <~> A := BuildEquiv A A idmap _.

Arguments equiv_idmap {A} , A.

Notation "1" := equiv_idmap : equiv_scope.

Global Instance reflexive_equiv : Reflexive Equiv | 0 := @equiv_idmap.

(** The composition of equivalences is an equivalence. *)
Global Instance isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g}
  : IsEquiv (compose g f) | 1000
  := BuildIsEquiv A C (compose g f)
    (compose f^-1 g^-1)
    (fun c => ap g (eisretr f (g^-1 c)) @ eisretr g c)
    (fun a => ap (f^-1) (eissect g (f a)) @ eissect f a)
    (fun a =>
      (whiskerL _ (eisadj g (f a))) @
      (ap_pp g _ _)^ @
      ap02 g
      ( (concat_A1p (eisretr f) (eissect g (f a)))^ @
        (ap_compose f^-1 f _ @@ eisadj f a) @
        (ap_pp f _ _)^
      ) @
      (ap_compose f g _)^
    ).

(* An alias of [isequiv_compose], with some arguments explicit; often convenient when type class search fails. *)
Definition isequiv_compose'
  {A B : Type} (f : A -> B) (_ : IsEquiv f)
  {C : Type} (g : B -> C) (_ : IsEquiv g)
  : IsEquiv (g o f)
  := isequiv_compose.

Definition equiv_compose {A B C : Type} (g : B -> C) (f : A -> B)
  `{IsEquiv B C g} `{IsEquiv A B f}
  : A <~> C
  := BuildEquiv A C (compose g f) _.

Definition equiv_compose' {A B C : Type} (g : B <~> C) (f : A <~> B)
  : A <~> C
  := equiv_compose g f.

(** We put [g] and [f] in [equiv_scope] explcitly.  This is a partial work-around for https://coq.inria.fr/bugs/show_bug.cgi?id=3990, which is that implicitly bound scopes don't nest well. *)
Notation "g 'oE' f" := (equiv_compose' g%equiv f%equiv) (at level 40, left associativity) : equiv_scope.

(* The TypeClass [Transitive] has a different order of parameters than [equiv_compose].  Thus in declaring the instance we have to switch the order of arguments. *)
Global Instance transitive_equiv : Transitive Equiv | 0 :=
  fun _ _ _ f g => equiv_compose g f.


(** Anything homotopic to an equivalence is an equivalence. *)
Section IsEquivHomotopic.

  Context {A B : Type} (f : A -> B) {g : A -> B}.
  Context `{IsEquiv A B f}.
  Hypothesis h : f == g.

  Let sect := (fun b:B => (h (f^-1 b))^ @ eisretr f b).
  Let retr := (fun a:A => (ap f^-1 (h a))^ @ eissect f a).

  (* We prove the triangle identity with rewrite tactics.  Since we lose control over the proof term that way, we make the result opaque with "Qed". *)
  Let adj (a : A) : sect (g a) = ap g (retr a).
  Proof.
    unfold sect, retr.
    rewrite ap_pp. apply moveR_Vp.
    rewrite concat_p_pp, <- concat_Ap, concat_pp_p, <- concat_Ap.
    rewrite ap_V; apply moveL_Vp.
    rewrite <- ap_compose; rewrite (concat_A1p (eisretr f) (h a)).
    apply whiskerR, eisadj.
  Qed.

  (* This should not be an instance; it can cause the unifier to spin forever searching for functions to be hoomotpic to. *)
  Definition isequiv_homotopic : IsEquiv g
    := BuildIsEquiv _ _ g (f ^-1) sect retr adj.

  Definition equiv_homotopic : A <~> B
    := BuildEquiv _ _ g isequiv_homotopic.

End IsEquivHomotopic.


(** The inverse of an equivalence is an equivalence. *)
Section EquivInverse.

  Context {A B : Type} (f : A -> B) {feq : IsEquiv f}.

  Theorem other_adj (b : B) : eissect f (f^-1 b) = ap f^-1 (eisretr f b).
  Proof.
    (* First we set up the mess. *)
    rewrite <- (concat_1p (eissect _ _)).
    rewrite <- (concat_Vp (ap f^-1 (eisretr f (f (f^-1 b))))).
    rewrite (whiskerR (inverse2 (ap02 f^-1 (eisadj f (f^-1 b)))) _).
    refine (whiskerL _ (concat_1p (eissect _ _))^ @ _).
    rewrite <- (concat_Vp (eissect f (f^-1 (f (f^-1 b))))).
    rewrite <- (whiskerL _ (concat_1p (eissect f (f^-1 (f (f^-1 b)))))).
    rewrite <- (concat_pV (ap f^-1 (eisretr f (f (f^-1 b))))).
    apply moveL_M1.
    repeat rewrite concat_p_pp.
    (* Now we apply lots of naturality and cancel things. *)
    rewrite <- (concat_pp_A1 (fun a => (eissect f a)^) _ _).
    rewrite (ap_compose' f f^-1).
    rewrite <- (ap_p_pp _ _ (ap f (ap f^-1 (eisretr f (f (f^-1 b))))) _).
    rewrite <- (ap_compose f^-1 f).
    rewrite (concat_A1p (eisretr f) _).
    rewrite ap_pp, concat_p_pp.
    rewrite (concat_pp_V _ (ap f^-1 (eisretr f (f (f^-1 b))))).
    repeat rewrite <- ap_V; rewrite <- ap_pp.
    rewrite <- (concat_pA1 (fun y => (eissect f y)^) _).
    rewrite ap_compose', <- (ap_compose f^-1 f).
    rewrite <- ap_p_pp.
    rewrite (concat_A1p (eisretr f) _).
    rewrite concat_p_Vp.
    rewrite <- ap_compose.
    rewrite (concat_pA1_p (eissect f) _).
    rewrite concat_pV_p; apply concat_Vp.
  Qed.

  Global Instance isequiv_inverse : IsEquiv f^-1 | 10000
    := BuildIsEquiv B A f^-1 f (eissect f) (eisretr f) other_adj.
End EquivInverse.

(** If the goal is [IsEquiv _^-1], then use [isequiv_inverse]; otherwise, don't pretend worry about if the goal is an evar and we want to add a [^-1]. *)
#[global]
Hint Extern 0 (IsEquiv _^-1) => apply @isequiv_inverse : typeclass_instances.

(** [Equiv A B] is a symmetric relation. *)
Theorem equiv_inverse {A B : Type} : (A <~> B) -> (B <~> A).
Proof.
  intro e.
  exists (e^-1).
  apply isequiv_inverse.
Defined.

Notation "e ^-1" := (@equiv_inverse _ _ e) : equiv_scope.

Global Instance symmetric_equiv : Symmetric Equiv | 0 := @equiv_inverse.

(** If [g \o f] and [f] are equivalences, so is [g].  This is not an Instance because it would require Rocq to guess [f]. *)
Definition cancelR_isequiv {A B C} (f : A -> B) {g : B -> C}
  `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : IsEquiv g
  := isequiv_homotopic (compose (compose g f) f^-1)
       (fun b => ap g (eisretr f b)).

Definition cancelR_equiv {A B C} (f : A -> B) {g : B -> C}
  `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : B <~> C
  := BuildEquiv B C g (cancelR_isequiv f).

(** If [g \o f] and [g] are equivalences, so is [f]. *)
Definition cancelL_isequiv {A B C} (g : B -> C) {f : A -> B}
  `{IsEquiv B C g} `{IsEquiv A C (g o f)}
  : IsEquiv f
  := isequiv_homotopic (compose g^-1 (compose g f))
       (fun a => eissect g (f a)).

Definition cancelL_equiv {A B C} (g : B -> C) {f : A -> B}
  `{IsEquiv B C g} `{IsEquiv A C (g o f)}
  : A <~> B
  := BuildEquiv _ _ f (cancelL_isequiv g).

(** Combining these with [isequiv_compose], we see that equivalences can be transported across commutative squares. *)
Definition isequiv_commsq {A B C D}
           (f : A -> B) (g : C -> D) (h : A -> C) (k : B -> D)
           (p : k o f == g o h)
           `{IsEquiv _ _ f} `{IsEquiv _ _ h} `{IsEquiv _ _ k}
: IsEquiv g.
Proof.
  refine (@cancelR_isequiv _ _ _ h g _ _).
  refine (isequiv_homotopic _ p).
Defined.

Definition isequiv_commsq' {A B C D}
           (f : A -> B) (g : C -> D) (h : A -> C) (k : B -> D)
           (p : g o h == k o f)
           `{IsEquiv _ _ g} `{IsEquiv _ _ h} `{IsEquiv _ _ k}
: IsEquiv f.
Proof.
  refine (@cancelL_isequiv _ _ _ k f _ _).
  refine (isequiv_homotopic _ p).
Defined.

(** Transporting is an equivalence. *)
Section EquivTransport.

  Context {A : Type} (P : A -> Type) (x y : A) (p : x = y).

  Global Instance isequiv_transport : IsEquiv (transport P p) | 0
    := BuildIsEquiv (P x) (P y) (transport P p) (transport P p^)
    (transport_pV P p) (transport_Vp P p) (transport_pVp P p).

  Definition equiv_transport : P x <~> P y
    := BuildEquiv _ _ (transport P p) _.

End EquivTransport.

(** In all the above cases, we were able to directly construct all the structure of an equivalence.  However, as is evident, sometimes it is quite difficult to prove the adjoint law.

   The following adjointification theorem allows us to be lazy about this if we wish.  It says that if we have all the data of an (adjoint) equivalence except the triangle identity, then we can always obtain the triangle identity by modifying the datum [equiv_is_section] (or [equiv_is_retraction]).  The proof is the same as the standard categorical argument that any equivalence can be improved to an adjoint equivalence.

   As a stylistic matter, we try to avoid using adjointification in the library whenever possible, to preserve the homotopies specified by the user.  *)

Section Adjointify.

  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : Sect g f) (issect : Sect f g).

  (* This is the modified [eissect]. *)
  Let issect' := fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

  Let is_adjoint' (a : A) : isretr (f a) = ap f (issect' a).
  Proof.
    unfold issect'.
    apply moveR_M1.
    repeat rewrite ap_pp, concat_p_pp; rewrite <- ap_compose.
    rewrite (concat_pA1 (fun b => (isretr b)^) (ap f (issect a)^)).
    repeat rewrite concat_pp_p; rewrite ap_V; apply moveL_Vp; rewrite concat_p1.
    rewrite concat_p_pp, <- ap_compose.
    rewrite (concat_pA1 (fun b => (isretr b)^) (isretr (f a))).
    rewrite concat_pV, concat_1p; reflexivity.
  Qed.

  (** We don't make this a typeclass instance, because we want to control when we are applying it. *)
  Definition isequiv_adjointify : IsEquiv f
    := BuildIsEquiv A B f g isretr issect' is_adjoint'.

  Definition equiv_adjointify : A <~> B
    := BuildEquiv A B f isequiv_adjointify.

End Adjointify.

Arguments isequiv_adjointify {A B}%_type_scope (f g)%_function_scope isretr issect.
Arguments equiv_adjointify {A B}%_type_scope (f g)%_function_scope isretr issect.

(** An involution is an endomap that is its own inverse. *)
Definition isequiv_involution {X : Type} (f : X -> X) (isinvol : Sect f f)
: IsEquiv f
  := isequiv_adjointify f f isinvol isinvol.

Definition equiv_involution {X : Type} (f : X -> X) (isinvol : Sect f f)
: X <~> X
  := equiv_adjointify f f isinvol isinvol.

(** Several lemmas useful for rewriting. *)
Definition moveR_equiv_M `{IsEquiv A B f} (x : A) (y : B) (p : x = f^-1 y)
  : (f x = y)
  := ap f p @ eisretr f y.

Definition moveL_equiv_M `{IsEquiv A B f} (x : A) (y : B) (p : f^-1 y = x)
  : (y = f x)
  := (eisretr f y)^ @ ap f p.

Definition moveR_equiv_V `{IsEquiv A B f} (x : B) (y : A) (p : x = f y)
  : (f^-1 x = y)
  := ap (f^-1) p @ eissect f y.

Definition moveL_equiv_V `{IsEquiv A B f} (x : B) (y : A) (p : f y = x)
  : (y = f^-1 x)
  := (eissect f y)^ @ ap (f^-1) p.

(** Equivalence preserves contractibility (which of course is trivial under univalence). *)
Lemma contr_equiv A {B} (f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
Proof.
  exists (f (center A)).
  intro y.
  apply moveR_equiv_M.
  apply contr.
Qed.

Definition contr_equiv' A {B} `(f : A <~> B) `{Contr A}
  : Contr B
  := contr_equiv A f.

(** Any two contractible types are equivalent. *)
Global Instance isequiv_contr_contr {A B : Type}
       `{Contr A} `{Contr B} (f : A -> B)
  : IsEquiv f
  := BuildIsEquiv _ _ f (fun _ => (center A))
                  (fun x => path_contr _ _)
                  (fun x => path_contr _ _)
                  (fun x => path_contr _ _).

Lemma equiv_contr_contr {A B : Type} `{Contr A} `{Contr B}
  : (A <~> B).
Proof.
  apply equiv_adjointify with (fun _ => center B) (fun _ => center A);
  intros ?; apply contr.
Defined.

(** Assuming function extensionality, composing with an equivalence is itself an equivalence *)

Global Instance isequiv_precompose `{Funext} {A B C : Type}
  (f : A -> B) `{IsEquiv A B f}
  : IsEquiv (fun (g:B->C) => g o f) | 1000
  := isequiv_adjointify (fun (g:B->C) => g o f)
    (fun h => h o f^-1)
    (fun h => path_forall _ _ (fun x => ap h (eissect f x)))
    (fun g => path_forall _ _ (fun y => ap g (eisretr f y))).

Definition equiv_precompose `{Funext} {A B C : Type}
  (f : A -> B) `{IsEquiv A B f}
  : (B -> C) <~> (A -> C)
  := BuildEquiv _ _ (fun (g:B->C) => g o f) _.

Definition equiv_precompose' `{Funext} {A B C : Type} (f : A <~> B)
  : (B -> C) <~> (A -> C)
  := BuildEquiv _ _ (fun (g:B->C) => g o f) _.

Global Instance isequiv_postcompose `{Funext} {A B C : Type}
  (f : B -> C) `{IsEquiv B C f}
  : IsEquiv (fun (g:A->B) => f o g) | 1000
  := isequiv_adjointify (fun (g:A->B) => f o g)
    (fun h => f^-1 o h)
    (fun h => path_forall _ _ (fun x => eisretr f (h x)))
    (fun g => path_forall _ _ (fun y => eissect f (g y))).

Definition equiv_postcompose `{Funext} {A B C : Type}
  (f : B -> C) `{IsEquiv B C f}
  : (A -> B) <~> (A -> C)
  := BuildEquiv _ _ (fun (g:A->B) => f o g) _.

Definition equiv_postcompose' `{Funext} {A B C : Type} (f : B <~> C)
  : (A -> B) <~> (A -> C)
  := BuildEquiv _ _ (fun (g:A->B) => f o g) _.

(** Conversely, if pre- or post-composing with a function is always an equivalence, then that function is also an equivalence.  It's convenient to know that we only need to assume the equivalence when the other type is the domain or the codomain. *)

Definition isequiv_isequiv_precompose {A B : Type} (f : A -> B)
  (precomp := (fun (C : Type) (h : B -> C) => h o f))
  (Aeq : IsEquiv (precomp A)) (Beq : IsEquiv (precomp B))
  : IsEquiv f.
Proof.
  assert (H : forall (C D : Type)
                     (Ceq : IsEquiv (precomp C)) (Deq : IsEquiv (precomp D))
                     (k : C -> D) (h : A -> C),
                k o (precomp C)^-1 h = (precomp D)^-1 (k o h)).
  { intros C D ? ? k h.
    transitivity ((precomp D)^-1 (k o (precomp C ((precomp C)^-1 h)))).
    - transitivity ((precomp D)^-1 (precomp D (k o ((precomp C)^-1 h)))).
      + rewrite (eissect (precomp D) _); reflexivity.
      + reflexivity.
    - rewrite (eisretr (precomp C) h); reflexivity. }
  refine (isequiv_adjointify f ((precomp A)^-1 idmap) _ _).
  - intros x.
    change ((f o (precomp A)^-1 idmap) x = idmap x).
    apply ap10.
    rewrite (H A B Aeq Beq).
    change ((precomp B)^-1 (precomp B idmap) = idmap).
    apply eissect.
  - intros x.
    change ((precomp A ((precomp A)^-1 idmap)) x = idmap x).
    apply ap10, eisretr.
Qed.

(*
Definition isequiv_isequiv_postcompose {A B : Type} (f : A -> B)
  (postcomp := (fun (C : Type) (h : C -> A) => f o h))
  (feq : forall C:Type, IsEquiv (postcomp C))
  : IsEquiv f.
(* TODO *)
*)

(** If [f] is an equivalence, then so is [ap f].  We are lazy and use [adjointify]. *)
Global Instance isequiv_ap `{IsEquiv A B f} (x y : A)
  : IsEquiv (@ap A B f x y) | 1000
  := isequiv_adjointify (ap f)
  (fun q => (eissect f x)^  @  ap f^-1 q  @  eissect f y)
  (fun q =>
    ap_pp f _ _
    @ whiskerR (ap_pp f _ _) _
    @ ((ap_V f _ @ inverse2 (eisadj f _)^)
      @@ (ap_compose f^-1 f _)^
      @@ (eisadj f _)^)
    @ concat_pA1_p (eisretr f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _)
  (fun p =>
    whiskerR (whiskerL _ (ap_compose f f^-1 _)^) _
    @ concat_pA1_p (eissect f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _).

(** The function [equiv_ind] says that given an equivalence [f : A <~> B], and a hypothesis from [B], one may always assume that the hypothesis is in the image of [e].

In fibrational terms, if we have a fibration over [B] which has a section once pulled back along an equivalence [f : A <~> B], then it has a section over all of [B].  *)

Definition equiv_ind `{IsEquiv A B f} (P : B -> Type)
  : (forall x:A, P (f x)) -> forall y:B, P y
  := fun g y => transport P (eisretr f y) (g (f^-1 y)).

Arguments equiv_ind {A B} f {_} P _ _.

Definition equiv_ind_comp `{IsEquiv A B f} (P : B -> Type)
  (df : forall x:A, P (f x)) (x : A)
  : equiv_ind f P df (f x) = df x.
Proof.
  unfold equiv_ind.
  rewrite eisadj.
  rewrite <- transport_compose.
  exact (apD df (eissect f x)).
Defined.

(** Using [equiv_ind], we define a handy little tactic which introduces a variable and simultaneously substitutes it along an equivalence. *)

Ltac equiv_intro E x :=
  match goal with
    | |- forall y, @?Q y =>
      refine (equiv_ind E Q _); intros x
  end.

(** [equiv_composeR'], a flipped version of [equiv_compose'], is (like [concatR]) most often useful partially applied, to give the “first half” of an equivalence one is constructing and leave the rest as a subgoal. One could similarly define [equiv_composeR] as a flip of [equiv_compose], but it doesn’t seem so useful since it doesn’t leave the remaining equivalence as a subgoal. *)
Definition equiv_composeR' {A B C} (f : A <~> B) (g : B <~> C)
  := equiv_compose' g f.

(* Shouldn't this become transitivity mid ? *)
Ltac equiv_via mid :=
  apply @equiv_composeR' with (B := mid).

(** It's often convenient when constructing a chain of equivalences to use [equiv_compose'], etc.  But when we treat an [Equiv] object constructed in that way as a function, via the coercion [equiv_fun], Rocq sometimes needs a little help to realize that the result is the same as ordinary composition.  This tactic provides that help. *)
Ltac ev_equiv :=
  repeat match goal with
           | [ |- context[equiv_fun (equiv_compose' ?g ?f) ?a] ] =>
             change ((equiv_compose' g f) a) with (g (f a))
           | [ |- context[equiv_fun (equiv_compose ?g ?f) ?a] ] =>
             change ((equiv_compose g f) a) with (g (f a))
           | [ |- context[equiv_fun (equiv_inverse ?f) ?a] ] =>
             change ((equiv_inverse f) a) with (f^-1 a)
         end.


(* Types/Paths.v *)

Definition transport_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y)
  : transport (fun x => x = y) p q = p^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport (fun y => x = y) p q = q @ p.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1)
  : transport (fun x => x = x) p q = p^ @ q @ p.
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y)
  : transport (fun x => f x = y) p q = (ap f p)^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_Fr {A B : Type} {g : A -> B} {y1 y2 : A} {x : B}
  (p : y1 = y2) (q : x = g y1)
  : transport (fun y => x = g y) p q = q @ (ap g p).
Proof.
  destruct p. symmetry; apply concat_p1.
Defined.

Definition transport_paths_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1)
  : transport (fun x => f x = g x) p q = (ap f p)^ @ q @ (ap g p).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FlFr_D {A : Type} {B : A -> Type}
  {f g : forall a, B a} {x1 x2 : A} (p : x1 = x2) (q : f x1 = g x1)
: transport (fun x => f x = g x) p q
  = (apD f p)^ @ ap (transport B p) q @ (apD g p).
Proof.
  destruct p; simpl.
  exact ((ap_idmap _)^ @ (concat_1p _)^ @ (concat_p1 _)^).
Defined.

Definition transport_paths_FFlr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = x1)
  : transport (fun x => g (f x) = x) p q = (ap g (ap f p))^ @ q @ p.
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_lFFr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = g (f x1))
  : transport (fun x => x = g (f x)) p q = p^ @ q @ (ap g (ap f p)).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths2 {A : Type} {x y : A}
           (p : x = y) (q : idpath x = idpath x)
: transport (fun a => idpath a = idpath a) p q
  =  (concat_Vp p)^
    @ whiskerL p^ ((concat_1p p)^ @ whiskerR q p @ concat_1p p)
    @ concat_Vp p.
Proof.
  destruct p. simpl.
  refine (_ @ (concat_p1 _)^).
  refine (_ @ (concat_1p _)^).
  assert (H : forall (p : x = x) (q : 1 = p),
                (q @ (concat_p1 p)^) @ (concat_1p (p @ 1))^
                = whiskerL (idpath x) (idpath 1 @ whiskerR q 1 @ idpath (p @ 1))).
  { intros p' q'. destruct q'. reflexivity. }
  transitivity (q @ (concat_p1 1)^ @ (concat_1p 1)^).
  { simpl; exact ((concat_p1 _)^ @ (concat_p1 _)^). }
  refine (H 1 q).
Defined.

Definition equiv_ap `(f : A -> B) `{IsEquiv A B f} (x y : A)
  : (x = y) <~> (f x = f y)
  := BuildEquiv _ _ (ap f) _.

Global Arguments equiv_ap (A B)%_type_scope f%_function_scope _ _ _.

Definition equiv_ap' `(f : A <~> B) (x y : A)
  : (x = y) <~> (f x = f y)
  := equiv_ap f x y.

(* TODO: Is this really necessary? *)
Definition equiv_inj `(f : A -> B) `{IsEquiv A B f} {x y : A}
  : (f x = f y) -> (x = y)
  := (ap f)^-1.

(** ** Path operations are equivalences *)

Global Instance isequiv_path_inverse {A : Type} (x y : A)
  : IsEquiv (@inverse A x y) | 0.
Proof.
  refine (BuildIsEquiv _ _ _ (@inverse A y x)
                       (@inv_V A y x) (@inv_V A x y) _).
  intros p; destruct p; reflexivity.
Defined.

Definition equiv_path_inverse {A : Type} (x y : A)
  : (x = y) <~> (y = x)
  := BuildEquiv _ _ (@inverse A x y) _.

Global Instance isequiv_concat_l {A : Type} `(p : x = y:>A) (z : A)
  : IsEquiv (@transitivity A _ _ x y z p) | 0.
Proof.
  refine (BuildIsEquiv _ _ _ (concat p^)
                       (concat_p_Vp p) (concat_V_pp p) _).
  intros q; destruct p; destruct q; reflexivity.
Defined.

Definition equiv_concat_l {A : Type} `(p : x = y) (z : A)
  : (y = z) <~> (x = z)
  := BuildEquiv _ _ (concat p) _.

Global Instance isequiv_concat_r {A : Type} `(p : y = z) (x : A)
  : IsEquiv (fun q:x=y => q @ p) | 0.
Proof.
  refine (BuildIsEquiv _ _ (fun q => q @ p) (fun q => q @ p^)
           (fun q => concat_pV_p q p) (fun q => concat_pp_V q p) _).
  intros q; destruct p; destruct q; reflexivity.
Defined.

Definition equiv_concat_r {A : Type} `(p : y = z) (x : A)
  : (x = y) <~> (x = z)
  := BuildEquiv _ _ (fun q => q @ p) _.

Global Instance isequiv_concat_lr {A : Type} {x x' y y' : A} (p : x' = x) (q : y = y')
  : IsEquiv (fun r:x=y => p @ r @ q) | 0
  := @isequiv_compose _ _ (fun r => p @ r) _ _ (fun r => r @ q) _.

Definition equiv_concat_lr {A : Type} {x x' y y' : A} (p : x' = x) (q : y = y')
  : (x = y) <~> (x' = y')
  := BuildEquiv _ _ (fun r:x=y => p @ r @ q) _.

Global Instance isequiv_whiskerL {A} {x y z : A} (p : x = y) {q r : y = z}
: IsEquiv (@whiskerL A x y z p q r).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - apply cancelL.
  - intros k. unfold cancelL.
    rewrite !whiskerL_pp.
    refine ((_ @@ 1 @@ _) @ whiskerL_pVL p k).
    + destruct p, q; reflexivity.
    + destruct p, r; reflexivity.
  - intros k. unfold cancelL.
    refine ((_ @@ 1 @@ _) @ whiskerL_VpL p k).
    + destruct p, q; reflexivity.
    + destruct p, r; reflexivity.
Defined.

Definition equiv_whiskerL {A} {x y z : A} (p : x = y) (q r : y = z)
: (q = r) <~> (p @ q = p @ r)
  := BuildEquiv _ _ (whiskerL p) _.

Definition equiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
: (p @ q = p @ r) <~> (q = r)
  := equiv_inverse (equiv_whiskerL p q r).

Definition isequiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
  : IsEquiv (cancelL p q r).
Proof.
  change (IsEquiv (equiv_cancelL p q r)); exact _.
Defined.

Global Instance isequiv_whiskerR {A} {x y z : A} {p q : x = y} (r : y = z)
: IsEquiv (fun h => @whiskerR A x y z p q h r).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - apply cancelR.
  - intros k. unfold cancelR.
    rewrite !whiskerR_pp.
    refine ((_ @@ 1 @@ _) @ whiskerR_VpR k r).
    + destruct p, r; reflexivity.
    + destruct q, r; reflexivity.
  - intros k. unfold cancelR.
    refine ((_ @@ 1 @@ _) @ whiskerR_pVR k r).
    + destruct p, r; reflexivity.
    + destruct q, r; reflexivity.
Defined.

Definition equiv_whiskerR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p = q) <~> (p @ r = q @ r)
  := BuildEquiv _ _ (fun h => whiskerR h r) _.

Definition equiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p @ r = q @ r) <~> (p = q)
  := equiv_inverse (equiv_whiskerR p q r).

Definition isequiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
  : IsEquiv (cancelR p q r).
Proof.
  change (IsEquiv (equiv_cancelR p q r)); exact _.
Defined.

(** We can use these to build up more complicated equivalences.

In particular, all of the [move] family are equivalences.

(Note: currently, some but not all of these [isequiv_] lemmas have corresponding [equiv_] lemmas.  Also, they do *not* currently contain the computational content that e.g. the inverse of [moveR_Mp] is [moveL_Vp]; perhaps it would be useful if they did? *)

Global Instance isequiv_moveR_Mp
 {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveR_Mp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveR_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (p = r^ @ q) <~> (r @ p = q)
:= BuildEquiv _ _ (moveR_Mp p q r) _.

Global Instance isequiv_moveR_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveR_pM p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveR_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (r = q @ p^) <~> (r @ p = q)
:= BuildEquiv _ _ (moveR_pM p q r) _.

Global Instance isequiv_moveR_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: IsEquiv (moveR_Vp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveR_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: (p = r @ q) <~> (r^ @ p = q)
:= BuildEquiv _ _ (moveR_Vp p q r) _.

Global Instance isequiv_moveR_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: IsEquiv (moveR_pV p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveR_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: (r = q @ p) <~> (r @ p^ = q)
:= BuildEquiv _ _ (moveR_pV p q r) _.

Global Instance isequiv_moveL_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveL_Mp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveL_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (r^ @ q = p) <~> (q = r @ p)
:= BuildEquiv _ _ (moveL_Mp p q r) _.

Definition isequiv_moveL_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveL_pM p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveL_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q @ p^ = r <~> q = r @ p
  := BuildEquiv _ _ _ (isequiv_moveL_pM p q r).

Global Instance isequiv_moveL_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: IsEquiv (moveL_Vp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveL_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: r @ q = p <~> q = r^ @ p
:= BuildEquiv _ _ (moveL_Vp p q r) _.

Global Instance isequiv_moveL_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: IsEquiv (moveL_pV p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveL_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: q @ p = r <~> q = r @ p^
:= BuildEquiv _ _ (moveL_pV p q r) _.

Definition isequiv_moveL_1M {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveL_1M p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveL_M1 p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveL_1V p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveL_V1 p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveR_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveR_M1 p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Definition isequiv_moveR_1M {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveR_1M p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Definition isequiv_moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveR_1V p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Definition isequiv_moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveR_V1 p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.


Definition moveR_moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (q : transport P p u = v)
  : moveR_transport_p P p u v (moveL_transport_V P p u v q) = q.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveL_moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (q : u = transport P p^ v)
  : moveL_transport_V P p u v (moveR_transport_p P p u v q) = q.
Proof.
  destruct p; reflexivity.
Defined.

Global Instance isequiv_moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: IsEquiv (moveR_transport_p P p u v).
Proof.
  unshelve eapply isequiv_adjointify.
  apply moveL_transport_V.
  intro q; apply moveR_moveL_transport_V.
  intro q; apply moveL_moveR_transport_p.
Defined.

Definition equiv_moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: u = transport P p^ v <~> transport P p u = v
:= BuildEquiv _ _ (moveR_transport_p P p u v) _.


Definition moveR_moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
           (p : y = x) (u : P x) (v : P y) (q : transport P p^ u = v)
  : moveR_transport_V P p u v (moveL_transport_p P p u v q) = q.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveL_moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
           (p : y = x) (u : P x) (v : P y) (q : u = transport P p v)
  : moveL_transport_p P p u v (moveR_transport_V P p u v q) = q.
Proof.
  destruct p; reflexivity.
Defined.

Global Instance isequiv_moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: IsEquiv (moveR_transport_V P p u v).
Proof.
  unshelve eapply isequiv_adjointify.
  apply moveL_transport_p.
  intro q; apply moveR_moveL_transport_p.
  intro q; apply moveL_moveR_transport_V.
Defined.

Definition equiv_moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: u = transport P p v <~> transport P p^ u = v
:= BuildEquiv _ _ (moveR_transport_V P p u v) _.

Global Instance isequiv_moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: IsEquiv (moveL_transport_V P p u v).
Proof.
  unshelve eapply isequiv_adjointify.
  apply moveR_transport_p.
  intro q; apply moveL_moveR_transport_p.
  intro q; apply moveR_moveL_transport_V.
Defined.

Definition equiv_moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: transport P p u = v <~> u = transport P p^ v
:= BuildEquiv _ _ (moveL_transport_V P p u v) _.

Global Instance isequiv_moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: IsEquiv (moveL_transport_p P p u v).
Proof.
  unshelve eapply isequiv_adjointify.
  apply moveR_transport_V.
  intro q; apply moveL_moveR_transport_V.
  intro q; apply moveR_moveL_transport_p.
Defined.

Definition equiv_moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: transport P p^ u = v <~> u = transport P p v
:= BuildEquiv _ _ (moveL_transport_p P p u v) _.

Global Instance isequiv_moveR_equiv_M `{IsEquiv A B f} (x : A) (y : B)
: IsEquiv (@moveR_equiv_M A B f _ x y).
Proof.
  unfold moveR_equiv_M.
  refine (@isequiv_compose _ _ (ap f) _ _ (fun q => q @ eisretr f y) _).
Defined.

Definition equiv_moveR_equiv_M `{IsEquiv A B f} (x : A) (y : B)
  : (x = f^-1 y) <~> (f x = y)
  := BuildEquiv _ _ (@moveR_equiv_M A B f _ x y) _.

Global Instance isequiv_moveR_equiv_V `{IsEquiv A B f} (x : B) (y : A)
: IsEquiv (@moveR_equiv_V A B f _ x y).
Proof.
  unfold moveR_equiv_V.
  refine (@isequiv_compose _ _ (ap f^-1) _ _ (fun q => q @ eissect f y) _).
Defined.

Definition equiv_moveR_equiv_V `{IsEquiv A B f} (x : B) (y : A)
  : (x = f y) <~> (f^-1 x = y)
  := BuildEquiv _ _ (@moveR_equiv_V A B f _ x y) _.

Global Instance isequiv_moveL_equiv_M `{IsEquiv A B f} (x : A) (y : B)
: IsEquiv (@moveL_equiv_M A B f _ x y).
Proof.
  unfold moveL_equiv_M.
  refine (@isequiv_compose _ _ (ap f) _ _ (fun q => (eisretr f y)^ @ q) _).
Defined.

Definition equiv_moveL_equiv_M `{IsEquiv A B f} (x : A) (y : B)
  : (f^-1 y = x) <~> (y = f x)
  := BuildEquiv _ _ (@moveL_equiv_M A B f _ x y) _.

Global Instance isequiv_moveL_equiv_V `{IsEquiv A B f} (x : B) (y : A)
: IsEquiv (@moveL_equiv_V A B f _ x y).
Proof.
  unfold moveL_equiv_V.
  refine (@isequiv_compose _ _ (ap f^-1) _ _ (fun q => (eissect f y)^ @ q) _).
Defined.

Definition equiv_moveL_equiv_V `{IsEquiv A B f} (x : B) (y : A)
  : (f y = x) <~> (y = f^-1 x)
  := BuildEquiv _ _ (@moveL_equiv_V A B f _ x y) _.

(** *** Dependent paths *)

(** Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a path space, these dependent paths have a more convenient description: rather than transporting the left side both forwards and backwards, we transport both sides of the equation forwards, forming a sort of "naturality square".

   We use the same naming scheme as for the transport lemmas. *)

Definition dpath_path_l {A : Type} {x1 x2 y : A}
  (p : x1 = x2) (q : x1 = y) (r : x2 = y)
  : q = p @ r
  <~>
  transport (fun x => x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_r (concat_1p r) q).
Defined.

Definition dpath_path_r {A : Type} {x y1 y2 : A}
  (p : y1 = y2) (q : x = y1) (r : x = y2)
  : q @ p = r
  <~>
  transport (fun y => x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_lr {A : Type} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = x1) (r : x2 = x2)
  : q @ p = p @ r
  <~>
  transport (fun x => x = x) p q = r.
Proof.
  destruct p; simpl.
  transitivity (q @ 1 = r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y) (r : f x2 = y)
  : q = ap f p @ r
  <~>
  transport (fun x => f x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_r (concat_1p r) q).
Defined.

Definition dpath_path_Fr {A B : Type} {g : A -> B} {x : B} {y1 y2 : A}
  (p : y1 = y2) (q : x = g y1) (r : x = g y2)
  : q @ ap g p = r
  <~>
  transport (fun y => x = g y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1) (r : f x2 = g x2)
  : q @ ap g p = ap f p @ r
  <~>
  transport (fun x => f x = g x) p q = r.
Proof.
  destruct p; simpl.
  transitivity (q @ 1 = r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_FFlr {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (p : x1 = x2) (q : g (f x1) = x1) (r : g (f x2) = x2)
  : q @ p = ap g (ap f p) @ r
  <~>
  transport (fun x => g (f x) = x) p q = r.
Proof.
  destruct p; simpl.
  transitivity (q @ 1 = r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_lFFr {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (p : x1 = x2) (q : x1 = g (f x1)) (r : x2 = g (f x2))
  : q @ ap g (ap f p) = p @ r
  <~>
  transport (fun x => x = g (f x)) p q = r.
Proof.
  destruct p; simpl.
  transitivity (q @ 1 = r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_paths2 {A : Type} {x y : A}
           (p : x = y) (q : idpath x = idpath x)
           (r : idpath y = idpath y)
: (concat_1p p)^ @ whiskerR q p @ concat_1p p
  = (concat_p1 p)^ @ whiskerL p r @ concat_p1 p
  <~>
  transport (fun a => idpath a = idpath a) p q = r.
Proof.
  destruct p. simpl.
  refine (_ oE (equiv_whiskerR _ _ 1)^-1).
  refine (_ oE (equiv_whiskerL 1 _ _)^-1).
  refine (equiv_concat_lr _ _).
  - symmetry; apply whiskerR_p1_1.
  - apply whiskerL_1p_1.
Defined.

(** ** Universal mapping property *)

Global Instance isequiv_paths_ind `{Funext} {A : Type} (a : A)
  (P : forall x, (a = x) -> Type)
  : IsEquiv (paths_ind a P) | 0.
Proof.
  refine (isequiv_adjointify (paths_ind a P) (fun f => f a 1) _ _).
  - intros f.
    apply path_forall; intros x.
    apply path_forall; intros p.
    destruct p; reflexivity.
  - intros u. reflexivity.
Defined.

Definition equiv_paths_ind `{Funext} {A : Type} (a : A)
  (P : forall x, (a = x) -> Type)
  : P a 1 <~> forall x p, P x p
  := BuildEquiv _ _ (paths_ind a P) _.


(* Types/Forall.v *)

Section AssumeFunext.
Context `{Funext}.

(** ** Paths *)

(** Paths [p : f = g] in a function type [forall x:X, P x] are equivalent to functions taking values in path types, [H : forall x:X, f x = g x], or concisely, [H : f == g].

This equivalence, however, is just the combination of [apD10] and function extensionality [funext], and as such, [path_forall], et seq. are given in the [Overture]:  *)

(** Now we show how these things compute. *)

Definition apD10_path_forall `{P : A -> Type}
  (f g : forall x, P x) (h : f == g)
  : apD10 (path_forall _ _ h) == h
  := apD10 (eisretr apD10 h).

Definition eta_path_forall `{P : A -> Type}
  (f g : forall x, P x) (p : f = g)
  : path_forall _ _ (apD10 p) = p
  := eissect apD10 p.

Definition path_forall_1 `{P : A -> Type} (f : forall x, P x)
  : (path_forall f f (fun x => 1)) = 1
  := eta_path_forall f f 1.

(** The identification of the path space of a dependent function space, up to equivalence, is of course just funext. *)

Definition equiv_apD10 `{Funext} {A : Type} (P : A -> Type) f g
: (f = g) <~> (f == g)
  := BuildEquiv _ _ (@apD10 A P f g) _.

Global Instance isequiv_path_forall `{P : A -> Type} (f g : forall x, P x)
  : IsEquiv (path_forall f g) | 0
  := @isequiv_inverse _ _ (@apD10 A P f g) _.

Definition equiv_path_forall `{P : A -> Type} (f g : forall x, P x)
  : (f == g)  <~>  (f = g)
  := BuildEquiv _ _ (path_forall f g) _.

Global Arguments equiv_path_forall {A%_type_scope P} (f g)%_function_scope.

(** ** Path algebra *)

Definition path_forall_pp `{P : A -> Type} (f g h : forall x, P x)
           (p : f == g) (q : g == h)
: path_forall f h (fun x => p x @ q x) = path_forall f g p @ path_forall g h q.
Proof.
  revert p q.
  equiv_intro (@apD10 A P f g) p.
  equiv_intro (@apD10 A P g h) q.
  transitivity (path_forall f h (apD10 (p @ q))).
  - apply ap, path_forall; intros x.
    symmetry; apply apD10_pp.
  - refine (eta_path_forall _ _ _ @ _).
    apply concat2; symmetry; apply eta_path_forall.
Defined.


Definition path_forall_V `{P : A -> Type} (f g : forall x, P x)
           (p : f == g)
  : path_forall _ _ (fun x => (p x)^) = (path_forall _ _ p)^.
Proof.
  transitivity (path_forall _ _ (fun x => (apD10 (path_forall _ _ p) x)^)).
  eapply ap. symmetry. apply (@ap _ _ (fun h x => (h x)^)). apply eisretr.
 transitivity (path_forall _ _ (apD10 (path_forall _ _ p)^)).
  apply ap, inverse. apply path_forall; intros x. apply apD10_V.
  apply eissect.
Defined.

(** ** Transport *)

(** The concrete description of transport in sigmas and pis is rather trickier than in the other types. In particular, these cannot be described just in terms of transport in simpler types; they require the full Id-elim rule by way of "dependent transport" [transportD].

  In particular this indicates why "transport" alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory). A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? *)
Definition transport_forall
  {A : Type} {P : A -> Type} {C : forall x, P x -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : P x1, C x1 y)
  : (transport (fun x => forall y : P x, C x y) p f)
    == (fun y =>
       transport (C x2) (transport_pV _ _ _) (transportD _ _ p _ (f (p^ # y)))).
  now destruct p.
Defined.

(** A special case of [transport_forall] where the type [P] does not depend on [A],
    and so it is just a fixed type [B]. *)
Definition transport_forall_constant
  {A B : Type} {C : A -> B -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : B, C x1 y)
  : (transport (fun x => forall y : B, C x y) p f)
    == (fun y => transport (fun x => C x y) p (f y)).
  now destruct p.
Defined.

Definition apD_transport_forall_constant
  {A B : Type} (C : A -> B -> Type)
  {x1 x2 : A} (p : x1 = x2) (f : forall y : B, C x1 y)
  {y1 y2 : B} (q : y1 = y2)
: apD (transport (fun x => forall y : B, C x y) p f) q
  = ap (transport (C x2) q) (transport_forall_constant p f y1)
    @ transport_transport C p q (f y1)
    @ ap (transport (fun x : A => C x y2) p) (apD f q)
    @ (transport_forall_constant p f y2)^.
Proof.
  destruct p, q; reflexivity.
Defined.

(** ** Maps on paths *)

(** The action of maps given by application. *)
Definition ap_apply_lD {A} {B : A -> Type} {f g : forall x, B x} (p : f = g) (z : A)
  : ap (fun f => f z) p = apD10 p z
:= 1.

Definition ap_apply_lD2 {A} {B : A -> Type} { C : forall x, B x -> Type}
           {f g : forall x y, C x y} (p : f = g) (z1 : A) (z2 : B z1)
  : ap (fun f => f z1 z2) p = apD10 (apD10 p z1) z2.
Proof.
  now destruct p.
Defined.


(** The action of maps given by lambda. *)
Definition ap_lambdaD {A B : Type} {C : B -> Type} {x y : A} (p : x = y) (M : forall a b, C b) :
  ap (fun a b => M a b) p =
  path_forall _ _ (fun b => ap (fun a => M a b) p).
Proof.
  destruct p;
  symmetry;
  simpl; apply path_forall_1.
Defined.

(** ** Dependent paths *)

(** Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a function space, these dependent paths have a more convenient description: rather than transporting the argument of [y1] forwards and backwards, we transport only forwards but on both sides of the equation, yielding a "naturality square". *)

Definition dpath_forall
  {A:Type} (B:A -> Type) (C:forall a, B a -> Type) (x1 x2:A) (p:x1=x2)
  (f:forall y1:B x1, C x1 y1) (g:forall (y2:B x2), C x2 y2)
  : (forall (y1:B x1), transportD B C p y1 (f y1) = g (transport B p y1))
  <~>
  (transport (fun x => forall y:B x, C x y) p f = g).
Proof.
  destruct p.
  apply equiv_path_forall.
Defined.

Definition dpath_forall_constant
  {A B:Type} (C : A -> B -> Type) (x1 x2:A) (p:x1=x2)
  (f:forall (y1:B), C x1 y1) (g:forall (y2:B), C x2 y2)
  : (forall (y1:B), transport (fun x => C x y1) p (f y1) = g y1)
  <~>
  (transport (fun x => forall y:B, C x y) p f = g).
Proof.
  destruct p.
  apply equiv_path_forall.
Defined.

(** ** Functorial action *)

(** The functoriality of [forall] is slightly subtle: it is contravariant in the domain type and covariant in the codomain, but the codomain is dependent on the domain. *)
Definition functor_forall `{P : A -> Type} `{Q : B -> Type}
    (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
  : (forall a:A, P a) -> (forall b:B, Q b)
  := (fun g b => f1 _ (g (f0 b))).

Definition ap_functor_forall `{P : A -> Type} `{Q : B -> Type}
    (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
    (g g' : forall a:A, P a) (h : g == g')
  : ap (functor_forall f0 f1) (path_forall _ _ h)
    = path_forall _ _ (fun b:B => (ap (f1 b) (h (f0 b)))).
Proof.
  revert h.  equiv_intro (@apD10 A P g g') h.
  destruct h.  simpl.
  transitivity (idpath (functor_forall f0 f1 g)).
  - exact (ap (ap (functor_forall f0 f1)) (path_forall_1 g)).
  - symmetry.  apply path_forall_1.
Defined.

Definition functor_forall_compose
           `{P : A -> Type} `{Q : B -> Type} `{R : C -> Type}
           (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
           (g0 : C -> B) (g1 : forall c:C, Q (g0 c) -> R c)
           (k : forall a, P a)
  : functor_forall g0 g1 (functor_forall f0 f1 k) == functor_forall (f0 o g0) (fun c => g1 c o f1 (g0 c)) k
  := fun a => 1.

(** ** Equivalences *)

Global Instance isequiv_functor_forall `{P : A -> Type} `{Q : B -> Type}
  `{IsEquiv B A f} `{forall b, @IsEquiv (P (f b)) (Q b) (g b)}
  : IsEquiv (functor_forall f g) | 1000.
Proof.
  simple refine (isequiv_adjointify (functor_forall f g)
    (functor_forall (f^-1)
      (fun (x:A) (y:Q (f^-1 x)) => eisretr f x # (g (f^-1 x))^-1 y
      )) _ _);
  try assumption; (* https://coq.inria.fr/bugs/show_bug.cgi?id=3848 *)
  intros h.
  - abstract (
        apply path_forall; intros b; unfold functor_forall;
        rewrite eisadj;
        rewrite <- transport_compose;
        rewrite ap_transport;
        rewrite eisretr;
        apply apD
      ).
  - abstract (
        apply path_forall; intros a; unfold functor_forall;
        rewrite eissect;
        apply apD
      ).
Defined.

Definition equiv_functor_forall `{P : A -> Type} `{Q : B -> Type}
  (f : B -> A) `{IsEquiv B A f}
  (g : forall b, P (f b) -> Q b)
  `{forall b, @IsEquiv (P (f b)) (Q b) (g b)}
  : (forall a, P a) <~> (forall b, Q b)
  := BuildEquiv _ _ (functor_forall f g) _.

Definition equiv_functor_forall' `{P : A -> Type} `{Q : B -> Type}
  (f : B <~> A) (g : forall b, P (f b) <~> Q b)
  : (forall a, P a) <~> (forall b, Q b)
  := equiv_functor_forall f g.

Definition equiv_functor_forall_id `{P : A -> Type} `{Q : A -> Type}
  (g : forall a, P a <~> Q a)
  : (forall a, P a) <~> (forall a, Q a)
  := equiv_functor_forall (equiv_idmap A) g.

Definition equiv_functor_forall_pb {A B : Type} {P : A -> Type}
  (f : B <~> A)
  : (forall a, P a) <~> (forall b, P (f b))
  := equiv_functor_forall' (Q := P o f) f (fun b => equiv_idmap).

Definition equiv_functor_forall_pf {A B : Type} {Q : B -> Type}
  (f : B <~> A)
  : (forall a, (Q (f^-1 a))) <~> (forall b, Q b).
Proof.
  simple refine (equiv_functor_forall' (P := Q o f^-1) f _).
  intros b; exact (equiv_transport Q _ _ (eissect f b)).
Defined.

(** There is another way to make forall functorial that acts on on equivalences only. *)

Definition equiv_functor_forall_covariant
           `{P : A -> Type} `{Q : B -> Type}
           (f : A <~> B) (g : forall a, P a <~> Q (f a))
  : (forall a, P a) <~> (forall b, Q b).
Proof.
  refine (equiv_adjointify
           (fun (k:forall a, P a) b => eisretr f b # (g (f^-1 b) (k (f^-1 b))))
           (fun h a => (g a)^-1 (h (f a)))
           _ _).
  - intros h; apply path_forall; intros b.
    refine (_ @ apD h (eisretr f b)).
    apply ap, eisretr.
  - intros k; apply path_forall; intros a.
    refine (_ @ apD k (eissect f a)).
    apply moveR_equiv_V.
    refine (_ @ (ap_transport (eissect f a) g (k (f^-1 (f a))))^).
    refine (_ @ (transport_compose Q f (eissect f a) _)^).
    refine (ap (fun p => transport Q p _) (eisadj f a)).
Defined.

Definition equiv_functor_forall_covariant_compose
           `{P : A -> Type} `{Q : B -> Type} `{R : C -> Type}
           (f0 : A <~> B) (f1 : forall a, P a <~> Q (f0 a))
           (g0 : B <~> C) (g1 : forall b, Q b <~> R (g0 b))
           (h : forall a, P a) (c : C)
  : equiv_functor_forall_covariant g0 g1 (equiv_functor_forall_covariant f0 f1 h) c
    = equiv_functor_forall_covariant (g0 oE f0) (fun a => g1 (f0 a) oE f1 a) h c.
Proof.
  cbn.
  rewrite (ap_transport _ g1 _).
  rewrite (transport_compose R g0 _ _).
  symmetry; apply transport_pp.
Qed.

(** ** Truncatedness: any dependent product of n-types is an n-type *)

Global Instance contr_forall `{P : A -> Type} `{forall a, Contr (P a)}
  : Contr (forall a, P a) | 100.
Proof.
  exists (fun a => center (P a)).
  intro f.  apply path_forall.  intro a.  apply contr.
Defined.

(* Global Instance trunc_forall `{P : A -> Type} `{forall a, IsTrunc n (P a)} *)
(*   : IsTrunc n (forall a, P a) | 100. *)
(* Proof. *)
(*   generalize dependent P. *)
(*   simple_induction n n IH; simpl; intros P ?. *)
(*   (* case [n = -2], i.e. contractibility *) *)
(*   - exact _. *)
(*   (* case n = n'.+1 *) *)
(*   - intros f g; apply (trunc_equiv _ (apD10 ^-1)). *)
(* Defined. *)

(** ** Contractibility: A product over a contractible type is equivalent to the fiber over the center. *)

Definition equiv_contr_forall `{Contr A} `(P : A -> Type)
: (forall a, P a) <~> P (center A).
Proof.
  simple refine (equiv_adjointify (fun (f:forall a, P a) => f (center A)) _ _ _).
  - intros p a; exact (transport P (path_contr _ _) p).
  - intros p.
    refine (transport2 P (q := 1) _ p).
    apply path_contr.
  - intros f; apply path_forall; intros a.
    apply apD.
Defined.

(** ** Symmetry of curried arguments *)

(** Using the standard Haskell name for this, as it’s a handy utility function.

Note: not sure if [P] will usually be deducible, or whether it would be better explicit. *)
Definition flip `{P : A -> B -> Type}
  : (forall a b, P a b) -> (forall b a, P a b)
  := fun f b a => f a b.

Global Instance isequiv_flip `{P : A -> B -> Type}
  : IsEquiv (@flip _ _ P) | 0.
Proof.
  set (flip_P := @flip _ _ P).
  set (flip_P_inv := @flip _ _ (flip P)).
  set (flip_P_is_sect := (fun f => 1) : Sect flip_P flip_P_inv).
  set (flip_P_is_retr := (fun g => 1) : Sect flip_P_inv flip_P).
  exists flip_P_inv flip_P_is_retr flip_P_is_sect.
  intro g.  exact 1.
Defined.

Definition equiv_flip `(P : A -> B -> Type)
  : (forall a b, P a b) <~> (forall b a, P a b)
  := BuildEquiv _ _ (@flip _ _ P) _.

End AssumeFunext.



(* Types/Sigma.v *)


(** In homotopy type theory, We think of elements of [Type] as spaces, homotopy types, or weak omega-groupoids. A type family [P : A -> Type] corresponds to a fibration whose base is [A] and whose fiber over [x] is [P x].

From such a [P] we can build a total space over the base space [A] so that the fiber over [x : A] is [P x]. This is just Rocq's dependent sum construction, written as [sigT P] or [{x : A & P x}]. The elements of [{x : A & P x}] are pairs, written [existT P x y] in Rocq, where [x : A] and [y : P x].  In [Common.v] we defined the notation [(x;y)] to mean [existT _ x y].

The base and fiber components of a point in the total space are extracted with the two projections [pr1] and [pr2]. *)

(** ** Unpacking *)

(** Sometimes we would like to prove [Q u] where [u : {x : A & P x}] by writing [u] as a pair [(pr1 u ; pr2 u)]. This is accomplished by [sigT_unpack]. We want tight control over the proof, so we just write it down even though is looks a bit scary. *)

Definition unpack_sigma `{P : A -> Type} (Q : sigT P -> Type) (u : sigT P)
: Q (u.1; u.2) -> Q u
  := idmap.

Arguments unpack_sigma / .

(** ** Eta conversion *)

Definition eta_sigma `{P : A -> Type} (u : sigT P)
  : (u.1; u.2) = u
  := 1.

Arguments eta_sigma / .

Definition eta2_sigma `{P : forall (a : A) (b : B a), Type}
           (u : sigT (fun a => sigT (P a)))
  : (u.1; (u.2.1; u.2.2)) = u
  := 1.

Arguments eta2_sigma / .

Definition eta3_sigma `{P : forall (a : A) (b : B a) (c : C a b), Type}
           (u : sigT (fun a => sigT (fun b => sigT (P a b))))
  : (u.1; (u.2.1; (u.2.2.1; u.2.2.2))) = u
  := 1.

Arguments eta3_sigma / .

(** ** Paths *)

(** A path in a total space is commonly shown component wise. Because we use this over and over, we write down the proofs by hand to make sure they are what we think they should be. *)

(** With this version of the function, we often have to give [u] and [v] explicitly, so we make them explicit arguments. *)
Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 = v.1 & p # u.2 = v.2})
: u = v.
  destruct u, v, pq; cbn in *.
  now destruct projT7, projT8.
Defined.

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
           (p : u.1 = v.1) (q : p # u.2 = v.2)
: u = v
  := path_sigma_uncurried P u v (p;q).

(** A contravariant instance of [path_sigma_uncurried] *)
Definition path_sigma_uncurried_contra {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 = v.1 & u.2 = p^ # v.2})
: u = v
  := (path_sigma_uncurried P v u (pq.1^;pq.2^))^.

(** A variant of [Forall.dpath_forall] from which uses dependent sums to package things. It cannot go into [Forall] because [Sigma] depends on [Forall]. *)

Definition dpath_forall'
           {A : Type } (P : A -> Type) (Q: sigT P -> Type) {x y : A} (h : x = y)
           (f : forall p, Q (x ; p)) (g : forall p, Q (y ; p))
:
  (forall p, transport Q (path_sigma P (x ; p) (y; _) h 1) (f p) = g (h # p))
    <~>
    (forall p, transportD P (fun x => fun p => Q ( x ; p)) h p (f p) = g (transport P h p)).
Proof.
  destruct h.
  apply 1%equiv.
Defined.


(** This version produces only paths between pairs, as opposed to paths between arbitrary inhabitants of dependent sum types.  But it has the advantage that the components of those pairs can more often be inferred, so we make them implicit arguments. *)
Definition path_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
           (p : x = x') (q : p # y = y')
: (x;y) = (x';y')
  := path_sigma P (x;y) (x';y') p q.


(** Projections of paths from a total space. *)

Definition pr1_path `{P : A -> Type} {u v : sigT P} (p : u = v)
: u.1 = v.1
  :=
    ap pr1 p.
(* match p with idpath => 1 end. *)

Notation "p ..1" := (pr1_path p) (at level 3) : fibration_scope.

Definition pr2_path `{P : A -> Type} {u v : sigT P} (p : u = v)
: p..1 # u.2 = v.2
  := (transport_compose P pr1 p u.2)^
     @ (@apD {x:A & P x} _ pr2 _ _ p).

Notation "p ..2" := (pr2_path p) (at level 3) : fibration_scope.

(** Now we show how these things compute. *)

Definition pr1_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
           (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
: (path_sigma_uncurried _ _ _ pq)..1 = pq.1.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition pr2_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
           (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
: (path_sigma_uncurried _ _ _ pq)..2
  = ap (fun s => transport P s u.2) (pr1_path_sigma_uncurried pq) @ pq.2.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition eta_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
           (p : u = v)
: path_sigma_uncurried _ _ _ (p..1; p..2) = p.
Proof.
  destruct p. reflexivity.
Defined.

Lemma transport_pr1_path_sigma_uncurried
      `{P : A -> Type} {u v : sigT P}
      (pq : { p : u.1 = v.1 & transport P p u.2 = v.2 })
      Q
: transport (fun x => Q x.1) (@path_sigma_uncurried A P u v pq)
  = transport _ pq.1.
Proof.
  destruct pq as [p q], u, v; simpl in *.
  destruct p, q; simpl in *.
  reflexivity.
Defined.

Definition pr1_path_sigma `{P : A -> Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p # u.2 = v.2)
: (path_sigma _ _ _ p q)..1 = p
  := pr1_path_sigma_uncurried (p; q).

(* Writing it the other way can help [rewrite]. *)
Definition ap_pr1_path_sigma {A:Type} {P : A -> Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p # u.2 = v.2)
  : ap pr1 (path_sigma _ _ _ p q) = p
  := pr1_path_sigma p q.

Definition pr2_path_sigma `{P : A -> Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p # u.2 = v.2)
: (path_sigma _ _ _ p q)..2
  = ap (fun s => transport P s u.2) (pr1_path_sigma p q) @ q
  := pr2_path_sigma_uncurried (p; q).

Definition eta_path_sigma `{P : A -> Type} {u v : sigT P} (p : u = v)
: path_sigma _ _ _ (p..1) (p..2) = p
  := eta_path_sigma_uncurried p.

Definition transport_pr1_path_sigma
           `{P : A -> Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p # u.2 = v.2)
           Q
: transport (fun x => Q x.1) (@path_sigma A P u v p q)
  = transport _ p
  := transport_pr1_path_sigma_uncurried (p; q) Q.

(** This lets us identify the path space of a sigma-type, up to equivalence. *)

Global Instance isequiv_path_sigma `{P : A -> Type} {u v : sigT P}
: IsEquiv (path_sigma_uncurried P u v) | 0.
Proof.
  simple refine (BuildIsEquiv
            _ _
            _ (fun r => (r..1; r..2))
            eta_path_sigma
            _ _).
  all: destruct u, v; intros [p q].
  all: simpl in *.
  all: destruct q, p; simpl in *.
  all: reflexivity.
Defined.

Definition equiv_path_sigma `(P : A -> Type) (u v : sigT P)
: {p : u.1 = v.1 &  p # u.2 = v.2} <~> (u = v)
  := BuildEquiv _ _ (path_sigma_uncurried P u v) _.

(* A contravariant version of [isequiv_path_sigma'] *)
#[export] Instance isequiv_path_sigma_contra `{P : A -> Type} {u v : sigT P}
  : IsEquiv (path_sigma_uncurried_contra P u v) | 0.
  unshelve eapply (isequiv_adjointify (path_sigma_uncurried_contra P u v)).
  - intros []. exists 1. reflexivity.
  - intro r; destruct r; destruct u as [u1 u2]; reflexivity.
  - destruct u, v; intros [p q].
    simpl in *.
    destruct p; simpl in q.
    destruct q; reflexivity.
Defined.

(* A contravariant version of [equiv_path_sigma] *)
Definition equiv_path_sigma_contra {A : Type} `(P : A -> Type) (u v : sigT P)
  : {p : u.1 = v.1 & u.2 = p^ # v.2} <~> (u = v)
  := BuildEquiv _ _ (path_sigma_uncurried_contra P u v) _.

(** This identification respects path concatenation. *)

Definition path_sigma_pp_pp {A : Type} (P : A -> Type) {u v w : sigT P}
           (p1 : u.1 = v.1) (q1 : p1 # u.2 = v.2)
           (p2 : v.1 = w.1) (q2 : p2 # v.2 = w.2)
: path_sigma P u w (p1 @ p2)
             (transport_pp P p1 p2 u.2 @ ap (transport P p2) q1 @ q2)
  = path_sigma P u v p1 q1 @ path_sigma P v w p2 q2.
Proof.
  destruct u, v, w. simpl in *.
  destruct p1, p2, q1, q2.
  reflexivity.
Defined.

Definition path_sigma_pp_pp' {A : Type} (P : A -> Type)
           {u1 v1 w1 : A} {u2 : P u1} {v2 : P v1} {w2 : P w1}
           (p1 : u1 = v1) (q1 : p1 # u2 = v2)
           (p2 : v1 = w1) (q2 : p2 # v2 = w2)
: path_sigma' P (p1 @ p2)
              (transport_pp P p1 p2 u2 @ ap (transport P p2) q1 @ q2)
  = path_sigma' P p1 q1 @ path_sigma' P p2 q2
  := @path_sigma_pp_pp A P (u1;u2) (v1;v2) (w1;w2) p1 q1 p2 q2.

Definition path_sigma_p1_1p' {A : Type} (P : A -> Type)
           {u1 v1 : A} {u2 : P u1} {v2 : P v1}
           (p : u1 = v1) (q : p # u2 = v2)
: path_sigma' P p q
  = path_sigma' P p 1 @ path_sigma' P 1 q.
Proof.
  destruct p, q.
  reflexivity.
Defined.

(** [pr1_path] also commutes with the groupoid structure. *)

Definition pr1_path_1 {A : Type} {P : A -> Type} (u : sigT P)
: (idpath u) ..1 = idpath (u .1)
  := 1.

Definition pr1_path_pp {A : Type} {P : A -> Type} {u v w : sigT P}
           (p : u = v) (q : v = w)
: (p @ q) ..1 = (p ..1) @ (q ..1)
  := ap_pp _ _ _.

Definition pr1_path_V {A : Type} {P : A -> Type} {u v : sigT P} (p : u = v)
: p^ ..1 = (p ..1)^
  := ap_V _ _.

(** Applying [existT] to one argument is the same as [path_sigma] with reflexivity in the first place. *)

Definition ap_existT {A : Type} (P : A -> Type) (x : A) (y1 y2 : P x)
           (q : y1 = y2)
: ap (existT P x) q = path_sigma' P 1 q.
Proof.
  destruct q; reflexivity.
Defined.

(** Dependent transport is the same as transport along a [path_sigma]. *)

Definition transportD_is_transport
           {A:Type} (B:A->Type) (C:sigT B -> Type)
           (x1 x2:A) (p:x1=x2) (y:B x1) (z:C (x1;y))
: transportD B (fun a b => C (a;b)) p y z
  = transport C (path_sigma' B p 1) z.
Proof.
  destruct p. reflexivity.
Defined.


(** Applying a two variable function to a [path_sigma]. *)

(* Definition ap_path_sigma {A B} (P : A -> Type) (F : forall a : A, P a -> B) *)
(*            {x x' : A} {y : P x} {y' : P x'} (p : x = x') (q : p # y = y') *)
(*   : ap (fun w => F w.1 w.2) (path_sigma' P p q) *)
(*     = ap _ (moveL_transport_V _ p _ _ q) *)
(*          @ (transport_arrow_toconst _ _ _)^ @ ap10 (apD F p) y'. *)
(* Proof. *)
(*   destruct p, q; reflexivity. *)
(* Defined. *)
(* Remark: this is also equal to: *)
(*     = ap10 (apD F p^)^ y @ transport_arrow_toconst _ _ _ *)
(*                          @ ap (F x') (transport2 _ (inv_V p) y @ q). *)



(** And we can simplify when the first equality is [1]. *)
Lemma ap_path_sigma_1p {A B : Type} {P : A -> Type} (F : forall a, P a -> B)
      (a : A) {x y : P a} (p : x = y)
  : ap (fun w => F w.1 w.2) (path_sigma' P 1 p) = ap (fun z => F a z) p.
Proof.
  destruct p; reflexivity.
Defined.


(** Applying a function constructed with [sigT_ind] to a [path_sigma] can be computed.  Technically this computation should probably go by way of a 2-variable [ap], and should be done in the dependently typed case. *)

(* Definition ap_sigT_rec_path_sigma {A : Type} (P : A -> Type) {Q : Type} *)
(*            (x1 x2:A) (p:x1=x2) (y1:P x1) (y2:P x2) (q:p # y1 = y2) *)
(*            (d : forall a, P a -> Q) *)
(* : ap (sigT_ind (fun _ => Q) d) (path_sigma' P p q) *)
(*   = (transport_const p _)^ *)
(*     @ (ap ((transport (fun _ => Q) p) o (d x1)) (transport_Vp _ p y1))^ *)

(*     @ (transport_arrow p _ _)^ *)
(*     @ ap10 (apD d p) (p # y1) *)
(*       @ ap (d x2) q. *)
(* Proof. *)
(*   destruct p. destruct q. reflexivity. *)
(* Defined. *)


(** A path between paths in a total space is commonly shown component wise. *)

(** With this version of the function, we often have to give [u] and [v] explicitly, so we make them explicit arguments. *)
Definition path_path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (p q : u = v)
           (rs : {r : p..1 = q..1 & transport (fun x => transport P x u.2 = v.2) r p..2 = q..2})
: p = q.
Proof.
  destruct rs, p, u.
  etransitivity; [ | apply eta_path_sigma ].
  destruct projT4, projT3. reflexivity.
Defined.

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
           (p q : u = v)
           (r : p..1 = q..1)
           (s : transport (fun x => transport P x u.2 = v.2) r p..2 = q..2)
: p = q
  := path_path_sigma_uncurried P u v p q (r; s).

(** ** Transport *)

(** The concrete description of transport in sigmas (and also pis) is rather trickier than in the other types.  In particular, these cannot be described just in terms of transport in simpler types; they require also the dependent transport [transportD].

  In particular, this indicates why "transport" alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory).  A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? *)

Definition transport_sigma {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
           {x1 x2 : A} (p : x1 = x2) (yz : { y : B x1 & C x1 y })
: transport (fun x => { y : B x & C x y }) p yz
  = (p # yz.1 ; transportD _ _ p yz.1 yz.2).
Proof.
  destruct p.  destruct yz as [y z]. reflexivity.
Defined.

(** The special case when the second variable doesn't depend on the first is simpler. *)
Definition transport_sigma' {A B : Type} {C : A -> B -> Type}
           {x1 x2 : A} (p : x1 = x2) (yz : { y : B & C x1 y })
: transport (fun x => { y : B & C x y }) p yz =
  (yz.1 ; transport (fun x => C x yz.1) p yz.2).
Proof.
  destruct p. destruct yz. reflexivity.
Defined.

(** Or if the second variable contains a first component that doesn't depend on the first.  Need to think about the naming of these. *)

Definition transport_sigma_' {A : Type} {B C : A -> Type}
           {D : forall a:A, B a -> C a -> Type}
           {x1 x2 : A} (p : x1 = x2)
           (yzw : { y : B x1 & { z : C x1 & D x1 y z } })
: transport (fun x => { y : B x & { z : C x & D x y z } }) p yzw
  = (p # yzw.1 ; (p # yzw.2.1 ; transportD2 _ _ _ p yzw.1 yzw.2.1 yzw.2.2)).
Proof.
  destruct p. reflexivity.
Defined.

(** ** Functorial action *)

Definition functor_sigma `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) (g : forall a, P a -> Q (f a))
: sigT P -> sigT Q
  := fun u => (f u.1 ; g u.1 u.2).

Definition ap_functor_sigma `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) (g : forall a, P a -> Q (f a))
           (u v : sigT P) (p : u.1 = v.1) (q : p # u.2 = v.2)
: ap (functor_sigma f g) (path_sigma P u v p q)
  = path_sigma Q (functor_sigma f g u) (functor_sigma f g v)
               (ap f p)
               ((transport_compose Q f p (g u.1 u.2))^
                @ (@ap_transport _ P (fun x => Q (f x)) _ _ p g u.2)^
                @ ap (g v.1) q).
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in p, q.
  destruct p; simpl in q.
  destruct q.
  reflexivity.
Defined.

(** ** Equivalences *)

Global Instance isequiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
         `{IsEquiv A B f} `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
: IsEquiv (functor_sigma f g) | 1000.
Proof.
  refine (isequiv_adjointify (functor_sigma f g)
                             (functor_sigma (f^-1)
                                            (fun x y => ((g (f^-1 x))^-1 ((eisretr f x)^ # y)))) _ _);
  intros [x y].
  - refine (path_sigma' _ (eisretr f x) _); simpl.
    abstract (
        rewrite (eisretr (g (f^-1 x)));
        apply transport_pV
      ).
  - refine (path_sigma' _ (eissect f x) _); simpl.
    refine ((ap_transport (eissect f x) (fun x' => (g x') ^-1)
                          (transport Q (eisretr f (f x)) ^ (g x y)))^ @ _).
    abstract (
        rewrite transport_compose, eisadj, transport_pV;
        apply eissect
      ).
Defined.

Definition equiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) `{IsEquiv A B f}
           (g : forall a, P a -> Q (f a))
           `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
: sigT P <~> sigT Q
  := BuildEquiv _ _ (functor_sigma f g) _.

Definition equiv_functor_sigma' `{P : A -> Type} `{Q : B -> Type}
           (f : A <~> B)
           (g : forall a, P a <~> Q (f a))
: sigT P <~> sigT Q
  := equiv_functor_sigma f g.

Definition equiv_functor_sigma_id `{P : A -> Type} `{Q : A -> Type}
           (g : forall a, P a <~> Q a)
: sigT P <~> sigT Q
  := equiv_functor_sigma' 1 g.

(** Lemma 3.11.9(i): Summing up a contractible family of types does nothing. *)

Global Instance isequiv_pr1_contr {A} {P : A -> Type}
         `{forall a, Contr (P a)}
: IsEquiv (@pr1 A P) | 100.
Proof.
  refine (isequiv_adjointify (@pr1 A P)
                             (fun a => (a ; center (P a))) _ _).
  - intros a; reflexivity.
  - intros [a p].
    refine (path_sigma' P 1 (contr _)).
Defined.

Definition equiv_sigma_contr {A : Type} (P : A -> Type)
           `{forall a, Contr (P a)}
: sigT P <~> A
  := BuildEquiv _ _ pr1 _.

(** Lemma 3.11.9(ii): Dually, summing up over a contractible type does nothing. *)

Definition equiv_contr_sigma {A : Type} (P : A -> Type) `{Contr A}
: { x : A & P x } <~> P (center A).
Proof.
  refine (equiv_adjointify (fun xp => (contr xp.1)^ # xp.2)
                           (fun p => (center A ; p)) _ _).
  - intros p; simpl.
    exact (ap (fun q => q # p) (path_contr _ 1)).
  - intros [a p].
    refine (path_sigma' _ (contr a) _).
    apply transport_pV.
Defined.

(** ** Associativity *)

Definition equiv_sigma_assoc `(P : A -> Type) (Q : {a : A & P a} -> Type)
: {a : A & {p : P a & Q (a;p)}} <~> sigT Q
  := @BuildEquiv
       _ _ _
       (@BuildIsEquiv
          {a : A & {p : P a & Q (a;p)}} (sigT Q)
          (fun apq => ((apq.1; apq.2.1); apq.2.2))
          (fun apq => (apq.1.1; (apq.1.2; apq.2)))
          (fun _ => 1)
          (fun _ => 1)
          (fun _ => 1)).

(* Definition equiv_sigma_prod `(Q : (A * B) -> Type) *)
(* : {a : A & {b : B & Q (a,b)}} <~> sigT Q *)
(*   := @BuildEquiv *)
(*        _ _ _ *)
(*        (@BuildIsEquiv *)
(*           {a : A & {b : B & Q (a,b)}} (sigT Q) *)
(*           (fun apq => ((apq.1, apq.2.1); apq.2.2)) *)
(*           (fun apq => (fst apq.1; (snd apq.1; apq.2))) *)
(*           (fun _ => 1) *)
(*           (fun _ => 1) *)
(*           (fun _ => 1)). *)

(* Definition equiv_sigma_prod0 A B *)
(* : {a : A & B} <~> A * B *)
(*   := BuildEquiv _ _ _ *)
(*        (BuildIsEquiv *)
(*           {a : A & B} (A * B) *)
(*           (fun (ab : {a:A & B}) => (ab.1 , ab.2)) *)
(*           (fun (ab : A*B) => (fst ab ; snd ab)) *)
(*           (fun _ => 1) (fun _ => 1) (fun _ => 1)). *)

(* (** ** Symmetry *) *)

(* Definition equiv_sigma_symm `(P : A -> B -> Type) *)
(* : {a : A & {b : B & P a b}} <~> {b : B & {a : A & P a b}} *)
(*   := ((equiv_sigma_prod (fun x => P (snd x) (fst x)))^-1) *)
(*        oE (equiv_functor_sigma' (equiv_prod_symm A B) *)
(*                                 (fun x => equiv_idmap (P (fst x) (snd x)))) *)
(*        oE (equiv_sigma_prod (fun x => P (fst x) (snd x))). *)

(* Definition equiv_sigma_symm0 (A B : Type) *)
(* : {a : A & B} <~> {b : B & A}. *)
(* Proof. *)
(*   refine (BuildEquiv _ _ (fun (w:{a:A & B}) => (w.2 ; w.1)) _). *)
(*   simple refine (BuildIsEquiv _ _ _ (fun (z:{b:B & A}) => (z.2 ; z.1)) *)
(*                        _ _ _); intros [x y]; reflexivity. *)
(* Defined. *)

(* (** ** Universal mapping properties *) *)

(* (** *** The positive universal property. *) *)
(* Global Instance isequiv_sigT_ind `{P : A -> Type} *)
(*          (Q : sigT P -> Type) *)
(* : IsEquiv (sigT_ind Q) | 0 *)
(*   := BuildIsEquiv *)
(*        _ _ *)
(*        (sigT_ind Q) *)
(*        (fun f x y => f (x;y)) *)
(*        (fun _ => 1) *)
(*        (fun _ => 1) *)
(*        (fun _ => 1). *)

(* Definition equiv_sigT_ind `{P : A -> Type} *)
(*            (Q : sigT P -> Type) *)
(* : (forall (x:A) (y:P x), Q (x;y)) <~> (forall xy, Q xy) *)
(*   := BuildEquiv _ _ (sigT_ind Q) _. *)

(* (** *** The negative universal property. *) *)

(* Definition sigT_coind_uncurried *)
(*            `{A : X -> Type} (P : forall x, A x -> Type) *)
(* : { f : forall x, A x & forall x, P x (f x) } *)
(*   -> (forall x, sigT (P x)) *)
(*   := fun fg => fun x => (fg.1 x ; fg.2 x). *)

(* Definition sigT_coind *)
(*            `{A : X -> Type} (P : forall x, A x -> Type) *)
(*            (f : forall x, A x) (g : forall x, P x (f x)) *)
(* : (forall x, sigT (P x)) *)
(*   := sigT_coind_uncurried P (f;g). *)

(* Global Instance isequiv_sigT_coind *)
(*          `{A : X -> Type} {P : forall x, A x -> Type} *)
(* : IsEquiv (sigT_coind_uncurried P) | 0 *)
(*   := BuildIsEquiv *)
(*        _ _ *)
(*        (sigT_coind_uncurried P) *)
(*        (fun h => existT (fun f => forall x, P x (f x)) *)
(*                         (fun x => (h x).1) *)
(*                         (fun x => (h x).2)) *)
(*        (fun _ => 1) *)
(*        (fun _ => 1) *)
(*        (fun _ => 1). *)

(* Definition equiv_sigT_coind *)
(*            `(A : X -> Type) (P : forall x, A x -> Type) *)
(* : { f : forall x, A x & forall x, P x (f x) } *)
(*     <~> (forall x, sigT (P x)) *)
(*   := BuildEquiv _ _ (sigT_coind_uncurried P) _. *)

(* (** ** Sigmas preserve truncation *) *)

(* Global Instance trunc_sigma `{P : A -> Type} *)
(*          `{IsTrunc n A} `{forall a, IsTrunc n (P a)} *)
(* : IsTrunc n (sigT P) | 100. *)
(* Proof. *)
(*   generalize dependent A. *)
(*   induction n; simpl; intros A P ac Pc. *)
(*   { exists (center A; center (P (center A))). *)
(*     intros [a ?]. *)
(*     refine (path_sigma' P (contr a) (path_contr _ _)). } *)
(*   { intros u v. *)
(*     refine (trunc_equiv _ (path_sigma_uncurried P u v)). } *)
(* Defined. *)

(* (** The sigma of an arbitrary family of *disjoint* hprops is an hprop. *) *)
(* Definition ishprop_sigma_disjoint *)
(*            `{P : A -> Type} `{forall a, IsHProp (P a)} *)
(* : (forall x y, P x -> P y -> x = y) -> IsHProp { x : A & P x }. *)
(* Proof. *)
(*   intros dj; apply hprop_allpath; intros [x px] [y py]. *)
(*   refine (path_sigma' P (dj x y px py) _). *)
(*   apply path_ishprop. *)
(* Defined. *)

(* (** ** Subtypes (sigma types whose second components are hprops) *) *)

(* (** To prove equality in a subtype, we only need equality of the first component. *) *)
(* Definition path_sigma_hprop {A : Type} {P : A -> Type} *)
(*            `{forall x, IsHProp (P x)} *)
(*            (u v : sigT P) *)
(* : u.1 = v.1 -> u = v *)
(*   := path_sigma_uncurried P u v o pr1^-1. *)

(* Global Instance isequiv_path_sigma_hprop {A P} `{forall x : A, IsHProp (P x)} {u v : sigT P} *)
(* : IsEquiv (@path_sigma_hprop A P _ u v) | 100 *)
(*   := isequiv_compose. *)

(* Hint Immediate isequiv_path_sigma_hprop : typeclass_instances. *)

(* Definition equiv_path_sigma_hprop {A : Type} {P : A -> Type} *)
(*            {HP : forall a, IsHProp (P a)} (u v : sigT P) *)
(* : (u.1 = v.1) <~> (u = v) *)
(*   := BuildEquiv _ _ (path_sigma_hprop _ _) _. *)

(* Definition isequiv_pr1_path_hprop {A} {P : A -> Type} *)
(*          `{forall a, IsHProp (P a)} *)
(*          x y *)
(* : IsEquiv (@pr1_path A P x y) *)
(*   := _ : IsEquiv (path_sigma_hprop x y)^-1. *)

(* Hint Immediate isequiv_pr1_path_hprop : typeclass_instances. *)

(* (** We define this for ease of [SearchAbout IsEquiv ap pr1] *) *)
(* Definition isequiv_ap_pr1_hprop {A} {P : A -> Type} *)
(*            `{forall a, IsHProp (P a)} *)
(*            x y *)
(* : IsEquiv (@ap _ _ (@pr1 A P) x y) *)
(*   := _. *)

(* Definition path_sigma_hprop_1 {A : Type} {P : A -> Type} *)
(*            `{forall x, IsHProp (P x)} (u : sigT P) *)
(* : path_sigma_hprop u u 1 = 1. *)
(* Proof. *)
(*   unfold path_sigma_hprop. *)
(*   unfold isequiv_pr1_contr; simpl. *)
(*   (** Ugh *) *)
(*   refine (ap (fun p => match p in (_ = v2) return (u = (u.1; v2)) with 1 => 1 end) *)
(*              (contr (idpath u.2))). *)
(* Defined. *)

(* (** The inverse of [path_sigma_hprop] has its own name, so we give special names to the section and retraction homotopies to help [rewrite] out. *) *)
(* Definition path_sigma_hprop_ap_pr1 {A : Type} {P : A -> Type} *)
(*            `{forall x, IsHProp (P x)} (u v : sigT P) (p : u = v) *)
(* : path_sigma_hprop u v (ap pr1 p) = p *)
(*   := eisretr (path_sigma_hprop u v) p. *)
(* Definition path_sigma_hprop_pr1_path {A : Type} {P : A -> Type} *)
(*            `{forall x, IsHProp (P x)} (u v : sigT P) (p : u = v) *)
(* : path_sigma_hprop u v p..1 = p *)
(*   := eisretr (path_sigma_hprop u v) p. *)
(* Definition ap_pr1_path_sigma_hprop {A : Type} {P : A -> Type} *)
(*            `{forall x, IsHProp (P x)} (u v : sigT P) (p : u.1 = v.1) *)
(* : ap pr1 (path_sigma_hprop u v p) = p *)
(*   := eissect (path_sigma_hprop u v) p. *)
(* Definition pr1_path_path_sigma_hprop {A : Type} {P : A -> Type} *)
(*            `{forall x, IsHProp (P x)} (u v : sigT P) (p : u.1 = v.1) *)
(* : (path_sigma_hprop u v p)..1 = p *)
(*   := eissect (path_sigma_hprop u v) p. *)
