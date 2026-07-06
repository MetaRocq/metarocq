(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require PCUICWcbvEval.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv EWellformed EWcbvEval.
From MetaRocq.Erasure.StepIndex Require Import Tactics.
From MetaRocq.Utils Require Import bytestring MRString.
From Stdlib Require Import ssreflect ssrbool.
Set Default Proof Using "Type*".

Print cunfold_fix.
Definition cunfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match nth_error mfix idx with
  | Some {| dbody := tLambda _ d |} => Some d
  | _ => None
  end.

  
Definition cunfold_cofix (mfix : mfixpoint term) (idx : nat) := option_map dbody (nth_error mfix idx).


Fixpoint All3_over {A B C : Type} {P : A -> B -> C -> Type} {la : list A} {lb : list B} {lc : list C}
  (a : All3 P la lb lc) (g : ∀ x y z, P x y z -> Type) : Type :=
  match a with
  | All3_nil => ()
  | All3_cons _ _ _ _ _ _ h t => (g _ _ _ h)  * All3_over t g 
  end.


Fixpoint map_All3_dep {A B C : Type} (P : A -> B -> C -> Type) {hP : ∀ a b c, P a b c -> Type} 
  (h: ∀ a b c e, hP a b c e) {la : list A} {lb : list B} {lc : list C}
  (ev : All3 P la lb lc) : All3_over ev hP :=
    match ev return All3_over ev hP with
    | All3_nil => tt
    | All3_cons _ _ _ _ _ _ Pabc ev => (h _ _ _ Pabc, map_All3_dep P h ev)
    end.


(* TODO: See to change the original def which forces X = term *)
Definition has_prim {X} {epfl : EPrimitiveFlags} (p : prim_val X) :=
  match p.π1 with
  | Primitive.primInt => has_primint
  | Primitive.primFloat => has_primfloat
  | Primitive.primString => has_primstring
  | Primitive.primArray => has_primarray
  end.


Lemma size_rev {A : Type} (l : list A) :
  #|List.rev l| = #|l|.
Proof.
  induction l as [|? ? IH]; now simple.
Qed.
Hint Rewrite @size_rev : rw_hints.


Lemma fold_left_map_def {A B : Set} (f : A -> B -> A) env (d : def A) : 
  fold_left (λ b d, map_def (λ t, f t d) b) env d = map_def (λ b, fold_left f env b) d.
Proof.
  unfold map_def; induction env in d |- *; destruct d; simpl; easy.
Qed.


Lemma Forall_same_In {A} (P : A -> A -> Prop) l :
  Forall2 P l l <-> ∀ x, In x l -> P x x.
Proof.
  induction l as [|a l IH]; split; simpl; try easy.
  - intros h x [->| hIn]; inversion h; subst; now simpl.
  - intros h; constructor; simpl; try easy.
    now apply IH.
Qed.
Hint Rewrite @Forall_same_In : rw_hints.


Lemma fix_subst_map l : fix_subst l = map (tFix l) (List.rev (seq 0 #|l|)).
Proof.
  unfold fix_subst.
  generalize #|l| as n.
  induction n; first reflexivity.
  now rewrite IHn seq_S rev_app_distr.
Qed.


Lemma cofix_subst_map l : cofix_subst l = map (tCoFix l) (List.rev (seq 0 #|l|)).
Proof.
  unfold cofix_subst.
  generalize #|l| as n.
  induction n; first reflexivity.
  now rewrite IHn seq_S rev_app_distr.
Qed.



Lemma isCoFixApp_eval 
  {efl : EEnvFlags} {wfl : WcbvFlags} Σ t v :
  isCoFix (head t) ->
  eval Σ t v ->
  isCoFix (head v).
Proof.
  intros hCofixApp heval.
  induction heval; subst;
  rewrite ->?head_tApp in *; simple; try easy.
Qed.



(* From ImplementBox *)

Lemma wellformed_lookup_inductive_pars {efl : EEnvFlags} Σ kn mdecl :
  has_cstr_params = false ->
  wf_glob Σ ->
  lookup_minductive Σ kn = Some mdecl -> mdecl.(ind_npars) = 0.
Proof.
  intros hasp.
  induction 1; cbn => //.
  case: eqb_spec => [|].
  - intros ->. destruct d => //. intros [= <-].
    cbn in H0. unfold wf_minductive in H0.
    rtoProp. cbn in H0. rewrite hasp in H0; now eapply eqb_eq in H0.
  - intros _. eapply IHwf_glob.
Qed.

Lemma wellformed_lookup_constructor_pars {efl : EEnvFlags} {Σ kn c mdecl idecl cdecl} :
  has_cstr_params = false ->
  wf_glob Σ ->
  lookup_constructor Σ kn c = Some (mdecl, idecl, cdecl) -> mdecl.(ind_npars) = 0.
Proof.
  intros hasp wf. cbn -[lookup_minductive].
  destruct lookup_minductive eqn:hl => //.
  do 2 destruct nth_error => //.
  eapply wellformed_lookup_inductive_pars in hl => //. congruence.
Qed.

Lemma lookup_constructor_pars_args_spec {efl : EEnvFlags} {Σ ind n mdecl idecl cdecl} :
  wf_glob Σ ->
  lookup_constructor Σ ind n = Some (mdecl, idecl, cdecl) ->
  lookup_constructor_pars_args Σ ind n = Some (mdecl.(ind_npars), cdecl.(cstr_nargs)).
Proof.
  cbn -[lookup_constructor] => wfΣ.
  destruct lookup_constructor as [[[mdecl' idecl'] [pars args]]|] eqn:hl => //.
  intros [= -> -> <-]. cbn. f_equal.
Qed.

Lemma wellformed_lookup_constructor_pars_args {efl : EEnvFlags} {Σ ind k n block_args} :
  wf_glob Σ ->
  has_cstr_params = false ->
  wellformed Σ k (EAst.tConstruct ind n block_args) ->
  ∑ args, lookup_constructor_pars_args Σ ind n = Some (0, args).
Proof.
  intros wfΣ hasp wf. cbn -[lookup_constructor] in wf.
  destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
  exists cdecl.(cstr_nargs).
  pose proof (wellformed_lookup_constructor_pars hasp wfΣ hl).
  eapply lookup_constructor_pars_args_spec in hl => //. congruence.
  destruct has_tConstruct => //.
Qed.

Lemma constructor_isprop_pars_decl_params {efl : EEnvFlags} {Σ ind c b pars cdecl} :
  has_cstr_params = false -> wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = Some (b, pars, cdecl) -> pars = 0.
Proof.
  intros hasp hwf.
  rewrite /constructor_isprop_pars_decl /lookup_constructor /lookup_inductive.
  destruct lookup_minductive as [mdecl|] eqn:hl => /= //.
  do 2 destruct nth_error => //.
  eapply wellformed_lookup_inductive_pars in hl => //. congruence.
Qed.



(* Search tCoFix tConstruct.

Definition make_construct_app {wfl : WcbvFlags} ind c args :=
  if with_constructor_as_block
  then tConstruct ind c args
  else mkApps (tConstruct ind c []) args.

Definition eval_cofix_case' {wfl : WcbvFlags} Σ := 
  ∀ discr mfix idx args narg fn ind c con_args pars cdecl brs br res,
  eval Σ discr (mkApps (tCoFix mfix idx) args) ->
  EGlobalEnv.cunfold_cofix mfix idx = Some (narg, fn) ->
  eval Σ (mkApps fn args) (make_construct_app ind c con_args) ->
  constructor_isprop_pars_decl Σ ind c = Some (false, pars, cdecl) ->
  nth_error brs c = Some br ->
  #|con_args| = pars + cdecl.(cstr_nargs) ->
  #|skipn pars con_args| = #|br.1| ->
  eval Σ (iota_red pars con_args br) res ->
  eval Σ (tCase (ind, pars) discr brs) res.


Lemma case_inv {wfl : WcbvFlags} Σ ip discr brs res :
  eval Σ (tCase ip discr brs) res ->
  (eval Σ discr tBox) + (∑ l ind c args,
    forall n t1 t2, 
    nth_error l n = Some (mkApps (tCoFix (mfix1 idx1) args1)) -> 
    nth_error l (S n) = Some (mkApps (tCoFix (mfix2 idx2) args2)) -> 
  
  eval Σ discr (make_construct_app ind c args)).
Proof.
  intros e.
  depind e; unfold make_construct_app.
  - rewrite e1. eauto.
  - rewrite e1. eauto.
  - eauto.
  - pose proof IHe2 _ _ _ eq_refl. (* Maybe sized induction ? *)
  - easy.



Lemma test {wfl : WcbvFlags} Σ discr mfix idx args narg fn ip brs res :
  eval_cofix_case' Σ ->
  eval Σ discr (mkApps (tCoFix mfix idx) args) ->
  EGlobalEnv.cunfold_cofix mfix idx = Some (narg, fn) ->
  eval Σ (tCase ip (mkApps fn args) brs) res ->
  eval Σ (tCase ip discr brs) res.
Proof.
  intros my_eval_cofix_case' e1 heq1 e2.
  destruct ip as (ind, pars).
  eapply my_eval_cofix_case'; tea. *)
