From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure.Typed Require Import Utils.
From MetaRocq.Erasure.Typed Require Import ExAst.
From MetaRocq.Erasure.Typed Require Import Transform.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Erasure Require Import ELiftSubst.

Module Ex := ExAst.

Section annots.
Context {A : Type}.

Fixpoint annots (t : term) : Type :=
  match t with
  | tEvar _ ts => A × bigprod annots ts
  | tLambda _ body => A × annots body
  | tLetIn _ val body => A × annots val × annots body
  | tApp hd arg => A × annots hd × annots arg
  | tCase _ discr brs => A × annots discr × bigprod (annots ∘ snd) brs
  | tProj _ t => A × annots t
  | tFix defs _
  | tCoFix defs _ => A × bigprod (annots ∘ dbody) defs
  | _ => A
  end.

Definition annot {t} : annots t -> A :=
  match t with
  | tEvar _ _
  | tLambda _ _
  | tLetIn _ _ _
  | tApp _ _
  | tCase _ _ _
  | tProj _ _
  | tFix _ _
  | tCoFix _ _ => fst
  | _ => id
  end.

Definition map_annot (f : A -> A) {t} : annots t -> annots t :=
  match t with
  | tEvar _ _
  | tLambda _ _
  | tLetIn _ _ _
  | tApp _ _
  | tCase _ _ _
  | tProj _ _
  | tFix _ _
  | tCoFix _ _ => fun p => (f p.1, p.2)
  | _ => f
  end.

Definition map_annots (f : A -> A) : forall {t}, annots t -> annots t.
Proof.
  fix map_annots 1.
  intros []; try exact f.
  - cbn.
    intros (a & la).
    exact (f a, bigprod_map_id map_annots la).
  - intros (a & ta).
    exact (f a, map_annots _ ta).
  - intros (a & vala & bodya).
    exact (f a, (map_annots _ vala, map_annots _ bodya)).
  - intros (a & hda & arga).
    exact (f a, (map_annots _ hda, map_annots _ arga)).
  - cbn.
    intros (a & discra & brsa).
    refine (f a, (map_annots _ discra, bigprod_map_id _ brsa)).
    intros.
    exact (map_annots _ X).
  - intros (a & ta).
    exact (f a, map_annots _ ta).
  - intros (a & defsa).
    refine (f a, bigprod_map_id _ defsa).
    intros.
    exact (map_annots _ X).
  - intros (a & defsa).
    refine (f a, bigprod_map_id _ defsa).
    intros.
    exact (map_annots _ X).
Defined.

Definition annot_lift (n : nat) :
  forall (k : nat) {t : term} (ta : annots t), annots (lift n k t).
Proof.
  fix f 2.
  intros k t ta.
  destruct t; cbn in *; try exact ta.
  - destruct (_ <=? _); exact ta.
  - refine (ta.1, _).
    apply bigprod_map; [|exact ta.2].
    apply f.
  - exact (ta.1, f _ _ ta.2).
  - exact (ta.1, (f _ _ ta.2.1, f _ _ ta.2.2)).
  - exact (ta.1, (f _ _ ta.2.1, f _ _ ta.2.2)).
  - refine (ta.1, (f _ _ ta.2.1, bigprod_map _ ta.2.2)).
    intros.
    exact (f _ _ X).
  - exact (ta.1, f _ _ ta.2).
  - refine (ta.1, bigprod_map _ ta.2).
    intros.
    exact (f _ _ X).
  - refine (ta.1, bigprod_map _ ta.2).
    intros.
    exact (f _ _ X).
Defined.

Inductive All_nth_error_type {X} (T : X -> Type) : option X -> Type :=
| all_nth_error_Some x : T x -> All_nth_error_type T (Some x)
| all_nth_error_None : All_nth_error_type T None.

Definition All_nth_error_spec {X} {T : X -> Type} (xs : list X) (i : nat) (a : All T xs) :
  All_nth_error_type T (nth_error xs i).
Proof.
  revert i.
  induction a.
  - intros []; apply all_nth_error_None.
  - intros [].
    + apply (all_nth_error_Some _ _ p).
    + apply IHa.
Defined.

Definition annot_subst {s} (sa : All annots s) :
  forall k {t} (ta : annots t), annots (subst s k t).
Proof.
  fix f 2.
  intros k t ta.
  destruct t; cbn in *; try exact ta.
  - destruct (_ <=? _); [|exact ta].
    destruct (All_nth_error_spec _ (n - k) sa).
    + apply annot_lift.
      exact a.
    + exact ta.
  - refine (ta.1, bigprod_map _ ta.2).
    apply f.
  - exact (ta.1, f _ _ ta.2).
  - exact (ta.1, (f _ _ ta.2.1, f _ _ ta.2.2)).
  - exact (ta.1, (f _ _ ta.2.1, f _ _ ta.2.2)).
  - refine (ta.1, (f _ _ ta.2.1, bigprod_map _ ta.2.2)).
    intros.
    exact (f _ _ X).
  - exact (ta.1, f _ _ ta.2).
  - refine (ta.1, bigprod_map _ ta.2).
    intros.
    exact (f _ _ X).
  - refine (ta.1, bigprod_map _ ta.2).
    intros.
    exact (f _ _ X).
Defined.

Definition annot_subst1 {s} (sa : annots s) (k : nat) {t} (ta : annots t) : annots (subst1 s k t) :=
  annot_subst (All_cons sa All_nil) k ta.

Definition annot_mkApps
           {hd} (hda : annots hd)
           (* For each argument an annotation for the induced application and
              annotations for the argument *)
           {args} (argsa : All (fun t => A * annots t) args) : annots (mkApps hd args).
Proof.
  revert hd hda.
  induction argsa; intros hd hda; [exact hda|].
  cbn.
  apply IHargsa.
  cbn.
  exact (p.1, (hda, p.2)).
Defined.

Definition constant_body_annots (cst : Ex.constant_body) : Type :=
  match Ex.cst_body cst with
  | Some body => annots body
  | None => unit
  end.

Definition global_decl_annots (decl : Ex.global_decl) : Type :=
  match decl with
  | Ex.ConstantDecl cst => constant_body_annots cst
  | _ => unit
  end.

Definition env_annots (Σ : global_env) : Type :=
  bigprod (global_decl_annots ∘ snd) Σ.

Definition annot_transform_type (t : ExtractTransform) :=
  forall Σ (a : env_annots Σ),
    match t Σ with
    | Ok Σ => env_annots Σ
    | Err _ => unit
    end.

(** * More utility functions *)

Fixpoint Edecompose_lam_annot (t : term) : (annots t) -> (list BasicAst.name) × (∑t, annots t) :=
  match t return annots t -> (list BasicAst.name) × (∑t, annots t) with
  | tLambda n b => fun '(bt, a) =>
      let '(ns, (b; a)) := Edecompose_lam_annot b a in
      (n :: ns, (b; a))
  | t => fun bt => ([], (t; bt))
  end.

Fixpoint Edecompose_app_annot (t : term) : (annots t) -> (∑t, annots t) × (list (∑t, annots t)) :=
  match t return annots t -> (∑t, annots t) × list (∑t, annots t) with
  | tApp f a => fun '(bt, (fa, arga)) =>
      let '(ba, l) := Edecompose_app_annot f fa in
      (ba, (a; arga) :: l)
  | t => fun bt => ((t; bt), [])
  end.

Section lam_body_annot_cont.
  Context {B : Type}.
  Context (f : forall t, annots t -> B).
  Fixpoint lam_body_annot_cont (t : term) (a : annots t) : B :=
    match t return annots t -> B with
    | tLambda na b => fun '(_, ba) => lam_body_annot_cont b ba
    | _ => fun _ => f t a
    end a.
End lam_body_annot_cont.

End annots.

Arguments annots : clear implicits.
Arguments constant_body_annots : clear implicits.
Arguments global_decl_annots : clear implicits.
Arguments env_annots : clear implicits.
Arguments annot_transform_type : clear implicits.
