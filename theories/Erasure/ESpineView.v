(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import List ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require Import EAst EAstUtils EInduction EReflect.
From MetaRocq.PCUIC Require Import PCUICSize.
From Equations Require Import Equations.
Set Equations Transparent.

Module TermSpineView.

Inductive t : term -> Set :=
| tBox       : t EAst.tBox
| tRel (n : nat) : t (EAst.tRel n)
| tVar (n : ident) : t (EAst.tVar n)
| tEvar (n : nat) (e : list term) : t (EAst.tEvar n e)
| tLambda n b : t (EAst.tLambda n b)
| tLetIn n b b' : t (EAst.tLetIn n b b')
| tApp (f : term) (l : list term) (napp : ~~ isApp f) (nnil : l <> nil) : t (mkApps f l)
| tConst kn : t (tConst kn)
| tConstruct i n args : t (tConstruct i n args)
| tCase ci p brs : t (tCase ci p brs)
| tProj p c : t (tProj p c)
| tFix mfix idx : t (tFix mfix idx)
| tCoFix mfix idx : t (tCoFix mfix idx)
| tPrim p : t (tPrim p)
| tLazy p : t (tLazy p)
| tForce p : t (tForce p).
Derive Signature for t.

Definition view : forall x : term, t x :=
  MkAppsInd.case (P:=fun x => t x)
    tBox tRel tVar
    (fun n l => tEvar n l)
    (fun n t => tLambda n t)
    (fun n b t => tLetIn n b t)
    (fun f l napp nnil => tApp f l napp nnil)
    tConst
    tConstruct
    (fun p t l => tCase p t l)
    (fun p t => tProj p t)
    (fun mfix n => tFix mfix n)
    (fun mfix n => tCoFix mfix n)
    (fun p => tPrim p)
    tLazy
    tForce.

Lemma view_mkApps {f v} (vi : t (mkApps f v)) : ~~ isApp f -> v <> [] ->
  exists hf vn, vi = tApp f v hf vn.
Proof.
  intros ha hv.
  depelim vi.
  all: try (revert H; eapply DepElim.simplification_sigma1; intros H'; solve_discr).
  intros He.
  epose proof (DepElim.pr2_uip (A:=EAst.term) He). subst vi0.
  do 2 eexists; reflexivity.
Qed.

End TermSpineView.