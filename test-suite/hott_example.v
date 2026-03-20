Set Universe Polymorphism.

(* Basic notations *)

Inductive sigT {A:Type} (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.

Inductive prod (A B : Type) : Type :=  pair : A -> B -> prod A B.

Arguments pair {_ _} _ _.

Set Warnings "-notation-overridden".
Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z): type_scope.

Section projections.
  Context {A : Type} {B : Type}.

  Definition fst (p:prod A B) := prod_rect _ _ (fun _ => A) (fun x y => x) p.

  Definition snd (p:prod A B) := prod_rect _ _ (fun _ => B) (fun x y => y) p.

End projections.

Inductive eq@{i} (A:Type@{i}) (x:A) : A -> Type@{i} :=
    eq_refl : eq A x x.

Notation "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

Arguments eq_refl {_ _}.

Definition projT1 {A} {P:A -> Type} (p:sigT P) : A :=
  sigT_rect _ _ (fun _ => A) (fun x y => x) p.

Definition projT2  {A} {P:A -> Type} (p:sigT P) : P (projT1 p) :=
  sigT_rect _ _ (fun x => P (projT1 x)) (fun x y => y) p.

Abbreviation id := (fun x => x).

Abbreviation compose := (fun g f x => g (f x)).

Module Hott_Notations.
Notation "g ∘ f" := (compose g%function f%function) (at level 1): function_scope.

Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x).
Notation "x .2" := (projT2 x).
Notation " ( x ; p ) " := (existT _ x p).

Notation "f == g" := (forall x, f x = g x) (at level 70).
End Hott_Notations.
Import Hott_Notations.

(* Equality-related definitions *)

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with eq_refl => eq_refl end.

Definition ap2 {A A' B:Type} (f:A -> A' -> B) {x y:A} (p:x = y)
  {x' y':A'} (q:x' = y') : f x x' = f y y'
  := match p with eq_refl => match q with eq_refl => eq_refl end end.

Definition ap3 {A A' A'' B:Type} (f:A -> A' -> A'' -> B) {x y:A} (p:x = y)
  {x' y':A'} (p':x' = y') {x'' y'':A''} (p'':x'' = y'') : f x x' x''= f y y' y''
  := match p with eq_refl => match p' with eq_refl => match p'' with eq_refl => eq_refl end end end.

Definition ap4 {A A' A'' A''' B:Type} (f:A -> A' -> A'' -> A''' -> B) {x y:A} (p:x = y)
           {x' y':A'} (p':x' = y') {x'' y'':A''} (p'':x'' = y'')
           {x''' y''':A'''} (p''':x''' = y''') : f x x' x'' x'''= f y y' y'' y'''
  := match p with eq_refl =>
     match p' with eq_refl =>
     match p'' with eq_refl =>
     match p''' with eq_refl => eq_refl end end end end.


Definition eq_sym {A} {x y : A} (H : x = y) : y = x :=
  match H with eq_refl => eq_refl end.


(* HSet *)

Class HSet A := {is_hset : forall (x y : A) (e e' : x = y), e = e'}.


(* From HoTT/Rocq *)

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with eq_refl => eq_refl  end.

Definition transport_eq {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with eq_refl => u end.

Notation "p # x" := (transport_eq _ p x) (right associativity, at level 65, only parsing).

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  destruct p; exact q. Show Proof.
Defined.

Notation "p @ q" := (concat p q) (at level 20).

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
    := match p with eq_refl => eq_refl end.

Notation "p ^" := (inverse p) (at level 3, format "p '^'").

Definition transportD {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y)
  : C x2 (p # y)
  :=
  match p with eq_refl => z end.

Definition transportD2 {A : Type} (B : A -> Type) (B' : A -> Type) (C : forall a:A, B a -> B' a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1)  (y' : B' x1) (z : C x1 y y')
  : C x2 (p # y) (p # y')
  :=
  match p with eq_refl => z end.

Definition transportD3 {A : Type} (B : A -> Type) (B' : A -> Type) B''
           (C : forall (a:A) (x: B a) (y: B' a), B'' a x y -> Type)
  {x1 x2 : A} (p : x1 = x2) y y' y'' (z : C x1 y y' y'')
  : C x2 (p # y) (p # y') (transportD2 _ _ _ p _ _ y'')
  :=
    match p with eq_refl => z end.

Definition transport_double A (P : A -> A -> Type) x y (e : x = y) (f : forall a, P a a) :
  transport_eq (fun X => P X _ ) e (transport_eq (fun X => P _ X) e (f x)) = f y.
  destruct e. reflexivity.
Defined.

Definition transport_forall A B (f : forall x : A , B x)  y z (e : z = y) :
  e # (f z) = f y.
Proof.
  destruct e. reflexivity.
Defined.

Definition transport_forall2 (P:Type->Type) A A' B (f : P A -> P A') (y z : P A) (H : z = y)
                 (g : forall x , B A x -> B A' (f x))
                 (h : forall x , B A x) :
                 (transport_eq (B _) (ap _ H)
                               (g z (h z))) =
                 g y (h y).
Proof.
  destruct H; reflexivity.
Defined.

Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u :=
  match q with eq_refl =>
    match p with eq_refl => eq_refl end
  end.

Definition inverse_left_inverse A (x y : A) (p : x = y) : eq_refl = (p ^ @ p).
Proof. destruct p; reflexivity. Defined.

Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : p # p^ # z = z.
Proof.
  destruct p; reflexivity.
Defined.

Definition transport_Vp {A : Type} (P : A -> Type) {x y : A} (p : y = x) (z : P y)
  : p^ # p # z = z.
Proof.
  destruct p; reflexivity.
Defined.


Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (p^) = (ap f p)^.
Proof.
  destruct p; reflexivity.
Defined.

Definition concat_refl A (x y :A) (e: x = y) : e @ eq_refl = e.
Proof.
  destruct e; reflexivity.
Defined.

Definition inv_inv A (x y :A) (e: x = y) : e^ @ e = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Definition transport_ap {A B : Type} (P : B -> Type) (f : A -> B) {x y : A}
           (p : x = y) (z : P (f x)) : transport_eq P (ap f p) z =
                                       transport_eq (fun x => P (f x)) p z.
Proof.
  destruct p; reflexivity.
Defined.

Definition naturality  {A B} `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B)
           (e' : forall a, Q (f a) -> P a) a b (e : a = b)(z : Q (f a)):
  e' _ (transport_eq (Q ∘ f) e z) = e # (e' _ z).
Proof.
  destruct e. reflexivity.
Defined.

Definition concat_inv {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q)^ = q^ @ p^.
             Proof.
  destruct p, q; reflexivity.
Defined.

Definition ap_inv {A B:Type} (f:A -> B) {x y:A} (p:x = y) : ap f p^ = (ap f p)^.
Proof.
  destruct p; reflexivity.
Defined.

Definition transport_inv {A : Type} (P : A -> Type) {x y : A} (p : x = y) u v :
  p # u = v -> u = transport_eq P p^ v.
Proof.
  destruct p. exact id.
Defined.

Definition transport_commute A B (P : A -> B -> Type) x y (e : x = y) x' y' (e' : x' = y') u:
  transport_eq (fun X => P X _ ) e (transport_eq (fun X => P _ X) e' u) =
  transport_eq (fun X => P _ X ) e' (transport_eq (fun X => P X _) e u).
  destruct e, e'. reflexivity.
Defined.

Definition transport_double' A B (P : A -> B -> Type) x y (e : x = y) g (f : forall a, P a (g a)) :
  transport_eq (fun X => P X _ ) e (transport_eq (fun X => P _ (g X)) e (f x)) = f y.
  destruct e. reflexivity.
Defined.

Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 = v.1 & u.2 = p^ # v.2})
: u = v.
Proof.
  destruct pq as [p q]. destruct u, v. simpl in *. destruct p.
  simpl in q; destruct q; reflexivity.
Defined.

Definition pr1_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v) : u.1 = v.1 := ap projT1 p.

Notation "p ..1" := (pr1_path p) (at level 50).

Definition pr2_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v)
  : u.2 = p..1^ # v.2.
  destruct p. reflexivity.
Defined.

Notation "p ..2" := (pr2_path p) (at level 50).

Definition path_prod_uncurried {A B : Type} (u v : A * B)
           (pq : (fst u = fst v) * (snd u = snd v))
: u = v.
Proof.
  destruct pq as [p q]. destruct u, v. simpl in *. destruct p.
  simpl in q; destruct q; reflexivity.
Defined.

Definition ap_id A (x y:A) (e:x = y) : ap id e = e.
Proof.
  destruct e; reflexivity.
Defined.

Definition refl_V {A : Type} {x : A} (p : x = x) :
  p^ = eq_refl -> p = eq_refl.
Proof.
  pose (ep := inv_inv _ _ _ p).
  intro e; rewrite e in ep. exact ep.
Defined.

Definition unpack_prod {A B} `{P : A * B -> Type} (u : A * B) :
  P (fst u, snd u) -> P u.
  destruct u. exact id.
Defined.

Definition pack_prod {A B} `{P : A * B -> Type} (u : A * B) :
  P u -> P (fst u, snd u).
  destruct u; exact id.
Defined.

Lemma transport_path_prod_uncurried {A B} (P : A * B -> Type) {x y : A * B}
      (H : (fst x = fst y) * (snd x = snd y))
      (Px : P x)
: transport_eq P (path_prod_uncurried _ _ H) Px
  = unpack_prod _ (transport_eq (fun x => P (x, snd y))
              (fst H)
              (transport_eq (fun y => P (fst x, y))
                         (snd H)
                         (pack_prod _ Px))).
Proof.
  destruct x, y, H; simpl in *.
  destruct e, e0.
  reflexivity.
Defined.

Lemma path_prod_uncurried_inv {A B} {x y : A * B}
      (H : (fst x = fst y) * (snd x = snd y))
  : (path_prod_uncurried _ _ H)^
    = path_prod_uncurried _ _ ((fst H)^, (snd H)^).
Proof.
  destruct H, x ,y. cbn in *. destruct e, e0. reflexivity.
Defined.

Definition transport_prod {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
  (z : P a * Q a)
  : transport_eq (fun a => prod (P a) (Q a)) p z  =  (p # (fst z), p # (snd z)).
  destruct p, z. reflexivity.
Defined.

Definition transport_const {A B : Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport_eq (fun x => B) p y = y.
Proof.
  destruct p.  exact eq_refl.
Defined.

Definition transport_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y)
  : transport_eq (fun x => x = y) p q = p^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport_eq (fun y => x = y) p q = q @ p.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y)
  : transport_eq (fun x => f x = y) p q = (ap f p)^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_Fr {A B : Type} {g : A -> B} {y1 y2 : A} {x : B}
  (p : y1 = y2) (q : x = g y1)
  : transport_eq (fun y => x = g y) p q = q @ (ap g p).
Proof.
  destruct p. symmetry. simpl. apply concat_refl.
Defined.

Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q).
  destruct p; reflexivity.
Defined.

Definition concat_Ap {A B : Type} {f g : A -> B} (p : forall x, f x = g x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ (ap g q).
  destruct q. simpl. apply eq_sym. apply concat_refl.
Defined.

Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r.
  destruct p, q; reflexivity.
Defined.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g ∘ f) p = ap g (ap f p).
  destruct p. reflexivity. Defined.

Definition concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) =  q @ (p y).
  destruct q; simpl. apply concat_refl.
Defined.

Definition inv_inv' A (x y :A) (e: x = y) : e @ e^ = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Definition transport_switch {A : Type} (P : A -> Type) {x y : A} (p : y = x) (z : P y) z'
  : z = p^ # z' -> p # z = z'.
Proof.
  destruct p; auto.
Defined.

Definition naturality'  {A B} `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B)
           (e' : forall a, P a -> Q (f a)) a b (e : a = b) z:
  transport_eq (Q ∘ f) e (e' _ z) = e' _ (e # z).
Proof.
  destruct e. reflexivity.
Defined.

Definition inv2 A (x y :A) (e: x = y) : e^ ^ = e.
Proof.
  destruct e; reflexivity.
Defined.



(* Equivalences *)

Class IsEquiv {A : Type} {B : Type} (f : A -> B) := BuildIsEquiv {
  e_inv : B -> A ;
  e_sect : forall x, e_inv (f x) = x;
  e_retr : forall y, f (e_inv y) = y;
  e_adj : forall x : A, e_retr (f x) = ap f (e_sect x);
}.

Coercion e_inv : IsEquiv >-> Funclass.

(** A class that includes all the data of an adjoint equivalence. *)
Class Equiv A B := BuildEquiv {
  e_fun : A -> B ;
  e_isequiv :: IsEquiv e_fun
}.

Coercion e_fun : Equiv >-> Funclass.

Notation "A ≃ B" := (Equiv A B) (at level 20).

Arguments e_fun {_ _} _ _.
Arguments e_inv {_ _} _ {_} _.
Arguments e_sect {_ _} _ {_} _.
Arguments e_retr {_ _} _ {_} _.
Arguments e_adj {_ _} _ {_} _.
Arguments e_isequiv {_ _ _}.

#[global]
Typeclasses Transparent e_fun e_inv.

Definition univalent_transport {A B : Type} {e: A ≃ B} : A -> B := e_fun e.

Notation "↑" := univalent_transport (at level 65, only parsing).

Definition e_inv' {A B : Type} (e : A ≃ B) : B -> A := e_inv (e_fun e).
Definition e_sect' {A B : Type} (e : A ≃ B) := e_sect (e_fun e).
Definition e_retr' {A B : Type} (e : A ≃ B) := e_retr (e_fun e).
Definition e_adj' {A B : Type} (e : A ≃ B) := e_adj (e_fun e).

Definition issect'  {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g ∘ f == id) (isretr : f  ∘ g == id) :=
  fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.



Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  eq_refl = p^ @ q -> p = q.
Proof.
  destruct p. exact id.
Defined.

Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  eq_refl @ p = p := eq_refl.

Definition moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  eq_refl = q @ p^ -> p = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_refl _ _ _  _)).
Defined.

Definition moveL_M1' {A : Type} {x y : A} (p q : x = y) :
  q^ @ p = eq_refl -> p = q.
Proof.
  destruct p. intro e. rewrite concat_refl in e.
  rewrite <- inv2. rewrite e. reflexivity.
Defined.

Definition concat_A1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ q.
  destruct q. cbn. apply inverse. apply concat_refl.
Defined.

Definition moveL_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> r = p @ q ^.
Proof.
  destruct r. cbn in *. destruct 1. destruct q. reflexivity.
Defined.

Definition is_adjoint' {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g∘ f == id) (isretr : f  ∘ g == id) (a : A) :
  isretr (f a) = ap f (issect' f g issect isretr a).
Proof.
  unfold issect'.
  apply moveL_M1.
  repeat rewrite ap_pp. rewrite <- concat_p_pp; rewrite <- ap_compose.
  pose  (concat_pA1 (fun b => (isretr b)^) (ap f (issect a))).
  eapply concat. 2: { apply ap2. reflexivity. exact e. }
  cbn. clear e.
  pose (concat_pA1 (fun b => (isretr b)^) (isretr (f a))).
  rewrite <- concat_p_pp.
  pose (concat_A1p (fun b => (isretr b)) (isretr (f a))).
  apply moveL_Vp in e0.
  rewrite <- concat_p_pp in e0. rewrite inv_inv' in e0.
  rewrite concat_refl in e0.
  rewrite ap_compose in e0.
  eapply concat.
  2: { apply ap2. reflexivity. rewrite concat_p_pp. eapply concat.
       2: { apply ap2. eapply concat.
            2:{ apply ap2. symmetry. apply e0. reflexivity. }
              symmetry. apply inv_inv'. reflexivity. }
              reflexivity. }
  repeat rewrite <- ap_compose.
  cbn. symmetry. eapply concat. refine (ap_pp ((f ∘ g) ∘f) _ _)^.
  rewrite inv_inv. reflexivity.
Defined.

Definition isequiv_adjointify {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g∘ f == id) (isretr : f  ∘ g == id)  : IsEquiv f
  := BuildIsEquiv A B f g (issect' f g issect isretr) isretr
                  (is_adjoint' f g issect isretr).
