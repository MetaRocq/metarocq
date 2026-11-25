(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv
  EWellformed EWcbvEval.
From MetaRocq.Utils Require Import bytestring MRString.
From MetaRocq.Erasure Require Import EWcbvEvalCstrsAsBlocksFixLambdaInd.
From Stdlib Require Import Relations.Relations.

From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

Set Default Proof Using "Type*".
Create HintDb rw_hints.

Ltac simple := repeat (
    assumption ||
    match goal with
    | |- All _ _ => apply Forall_All 
    | H : All _ _ |- _ => apply All_Forall in H
    | h : ?e = Some _ |- _ =>
          rewrite ->h in *
    | h : ?e = None |- _ =>
          rewrite ->h in *
    end ||
    autorewrite with rw_hints in * || 
    simpl in *
  ).


Hint Rewrite Nat.add_0_r : rw_hints.
Hint Rewrite Nat.add_succ_r : rw_hints.
Hint Rewrite <-@forallb_Forall : rw_hints.
Hint Rewrite Forall_forall : rw_hints.
Hint Rewrite @forallb_map : rw_hints.
Hint Rewrite andb_and : rw_hints.
Hint Rewrite length_map : rw_hints.
Hint Rewrite length_app : rw_hints.
Hint Rewrite <- @map_skipn : rw_hints.
Hint Rewrite @nth_error_map : rw_hints.
Hint Rewrite <-@map_repeat : rw_hints.
Hint Rewrite andb_and : rw_hints.
Hint Rewrite repeat_length : rw_hints.
Hint Rewrite length_seq : rw_hints.
Hint Rewrite if_same : rw_hints.
Hint Rewrite @skipn_0 : rw_hints.
Hint Rewrite <-map_rev : rw_hints.
Hint Rewrite head_mkApps : rw_hints.
Hint Rewrite head_tApp : rw_hints.
Hint Rewrite map_app : rw_hints.


Ltac my_discr :=
  let aux t t_head h name := 
    assert (head t = t_head) as name by now rewrite h; simple
  in
  try match goal with
  | h : mkApps ?head1 ?args1 = mkApps ?head2 ?args2 |- _ =>
      let name := fresh in
      assert ((head (mkApps head1 args1)) = (head (mkApps head2 args2))) as name by (now rewrite h);
      rewrite !head_mkApps in name 
  | h : ?t = mkApps (?t_head) _ |- _ => aux t t_head h fresh
  | h : mkApps (?t_head) _ = ?t |- _ =>
      aux t t_head (eq_sym h) fresh
  end; discriminate.
