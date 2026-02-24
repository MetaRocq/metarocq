(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames Primitive.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EGlobalEnv.
From MetaRocq.PCUIC Require Import PCUICTactics.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Stdlib Require Import ssreflect ssrbool.

Definition isSome {A} (o : option A) :=
  match o with
  | None => false
  | Some _ => true
  end.

Class EPrimitiveFlags :=
  { has_primint : bool;
    has_primfloat : bool;
    has_primstring : bool;
    has_primarray : bool }.

Definition has_prim {epfl : EPrimitiveFlags} (p : prim_val term) :=
  match p.π1 with
  | primInt => has_primint
  | primFloat => has_primfloat
  | primString => has_primstring
  | primArray => has_primarray
  end.

Class ETermFlags :=
  { has_tBox : bool
  ; has_tRel : bool
  ; has_tVar : bool
  ; has_tEvar : bool
  ; has_tLambda : bool
  ; has_tLetIn : bool
  ; has_tApp : bool
  ; has_tConst : bool
  ; has_tConstruct : bool
  ; has_tCase : bool
  ; has_tProj : bool
  ; has_tFix : bool
  ; has_tCoFix : bool
  ; has_tPrim :: EPrimitiveFlags
  ; has_tLazy_Force : bool
  }.

Class EEnvFlags := {
  has_axioms : bool;
  has_cstr_params : bool;
  term_switches :: ETermFlags ;
  cstr_as_blocks : bool ;
  }.

Definition all_primitive_flags :=
  {| has_primint := true;
     has_primfloat := true;
     has_primstring := true;
     has_primarray := true |}.

Lemma has_prim_all_primitive_flags p : @has_prim all_primitive_flags p.
Proof. destruct p as [? []]; auto. Qed.
#[global] Hint Resolve has_prim_all_primitive_flags : core.

Definition all_term_flags :=
  {| has_tBox := true
    ; has_tRel := true
    ; has_tVar := true
    ; has_tEvar := true
    ; has_tLambda := true
    ; has_tLetIn := true
    ; has_tApp := true
    ; has_tConst := true
    ; has_tConstruct := true
    ; has_tCase := true
    ; has_tProj := true
    ; has_tFix := true
    ; has_tCoFix := true
    ; has_tPrim := all_primitive_flags
    ; has_tLazy_Force := true
  |}.

Definition all_env_flags :=
  {| has_axioms := true;
     term_switches := all_term_flags;
     has_cstr_params := true ;
     cstr_as_blocks := false |}.

Definition all_env_flags_blocks :=
  {| has_axioms := true;
     term_switches := all_term_flags;
     has_cstr_params := true ;
     cstr_as_blocks := true |}.

Section wf.

  Context {efl  : EEnvFlags}.
  Variable Σ : global_context.

  (* a term term is wellformed if
    - it is closed up to k,
    - it only contains constructors as indicated by sw,
    - all occuring constructors are defined,
    - all occuring constants are defined, and
    - all occuring fixpoints have lambdas as bodies
    - if has_axioms is false, all occuring constants have bodies
    - all cases are exhaustive w.r.t the global declaration *)

  Definition wf_fix_gen (wf : nat -> term -> bool) k mfix idx :=
    let k' := List.length mfix + k in
    (idx <? #|mfix|) && List.forallb (test_def (wf k')) mfix.

  Definition is_nil {A} (l : list A) := match l with [] => true | _ => false end.

  Definition wf_brs ind brsl :=
    match lookup_inductive Σ ind with
    | Some (mib, oib) => #|oib.(ind_ctors)| == brsl
    | None => false
    end.

  Fixpoint wellformed k (t : term) : bool :=
    match t with
    | tRel i => has_tRel && Nat.ltb i k
    | tEvar ev args => has_tEvar && List.forallb (wellformed k) args
    | tLambda _ M => has_tLambda && wellformed (S k) M
    | tApp u v => has_tApp && wellformed k u && wellformed k v
    | tLetIn na b b' => has_tLetIn && wellformed k b && wellformed (S k) b'
    | tCase ind c brs => has_tCase &&
      let brs' := List.forallb (fun br => wellformed (#|br.1| + k) br.2) brs in
      wf_brs ind.1 #|brs| && wellformed k c && brs'
    | tProj p c => has_tProj && isSome (lookup_projection Σ p) && wellformed k c
    | tFix mfix idx => has_tFix && List.forallb (isLambda ∘ dbody) mfix && wf_fix_gen wellformed k mfix idx
    | tCoFix mfix idx => has_tCoFix && wf_fix_gen wellformed k mfix idx
    | tBox => has_tBox
    | tConst kn => has_tConst &&
      match lookup_constant Σ kn with
      | Some d => has_axioms || isSome d.(cst_body)
      | _ => false
      end
    | tConstruct ind c block_args => has_tConstruct && isSome (lookup_constructor Σ ind c) &&
      if cstr_as_blocks then match lookup_constructor_pars_args Σ ind c with
        | Some (p, a) => (p + a) == #|block_args|
        | _ => true end
        && forallb (wellformed k) block_args else is_nil block_args
    | tVar _ => has_tVar
    | tPrim p => has_prim p && test_prim (wellformed k) p
    | tLazy t => has_tLazy_Force && wellformed k t
    | tForce t => has_tLazy_Force && wellformed k t
    end.

End wf.

Lemma has_prim_map_prim {efl : EEnvFlags} f p : has_prim (map_prim f p) = has_prim p.
Proof.
  destruct p as [? []]; cbn; auto.
Qed.
#[global] Hint Rewrite @has_prim_map_prim : map.

Notation wf_fix Σ := (wf_fix_gen (wellformed Σ)).

Lemma wf_fix_inv {efl : EEnvFlags} Σ k mfix idx : reflect (idx < #|mfix| /\ forallb (test_def (wellformed Σ (#|mfix| + k))) mfix) (wf_fix Σ k mfix idx).
Proof.
  unfold wf_fix.
  destruct (idx <? #|mfix|) eqn:lt; cbn; [|econstructor].
  destruct forallb; constructor. now eapply Nat.ltb_lt in lt.
  now eapply Nat.ltb_lt in lt.
  now eapply Nat.ltb_nlt in lt.
Qed.

Definition wf_projections idecl :=
  match idecl.(ind_projs) with
  | [] => true
  | _ =>
    match idecl.(ind_ctors) with
    | [cstr] => #|idecl.(ind_projs)| == cstr.(cstr_nargs)
    | _ => false
    end
  end.

Definition wf_inductive (idecl : one_inductive_body) :=
  wf_projections idecl.

Definition wf_minductive {efl : EEnvFlags} (mdecl : mutual_inductive_body) :=
  (has_cstr_params || (mdecl.(ind_npars) == 0)) && forallb wf_inductive mdecl.(ind_bodies).

Definition wf_global_decl {efl : EEnvFlags} Σ d : bool :=
  match d with
  | ConstantDecl cb => option_default (fun b => wellformed Σ 0 b) cb.(cst_body) has_axioms
  | InductiveDecl idecl => wf_minductive idecl
  end.

Inductive wf_glob {efl : EEnvFlags} : global_declarations -> Prop :=
| wf_glob_nil : wf_glob []
| wf_glob_cons kn d Σ :
  wf_glob Σ ->
  wf_global_decl Σ d ->
  fresh_global kn Σ ->
  wf_glob ((kn, d) :: Σ).
Derive Signature for wf_glob.

Implicit Types (efl : EEnvFlags).

Section EEnvFlags.
  Context {efl : EEnvFlags}.
  Context {Σ : global_declarations}.
  Notation wellformed := (wellformed Σ).

  Lemma wellformed_closed {k t} : wellformed k t -> closedn k t.
  Proof using Type.
    induction t in k |- * using EInduction.term_forall_list_ind; intros;
      simpl in * ; rewrite -> ?andb_and in *;
      autorewrite with map;
      simpl wellformed in *; intuition auto;
      unfold wf_fix, test_def, test_snd in *;
      try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; simpl in *; solve_all)]; try easy.
    destruct cstr_as_blocks. 2: destruct args; eauto; solve_all.
    rtoProp. solve_all.
  Qed.

  Lemma wellformed_closed_decl {t} : wf_global_decl Σ t -> closed_decl t.
  Proof using Type.
    destruct t => /= //.
    destruct (cst_body c) => /= //.
    eapply wellformed_closed.
  Qed.

  Lemma wellformed_up {k t} : wellformed k t -> forall k', k <= k' -> wellformed k' t.
  Proof using Type.
    induction t in k |- * using EInduction.term_forall_list_ind; intros;
      simpl in * ; rewrite -> ?andb_and in *;
      autorewrite with map;
      simpl wellformed in *; intuition auto;
      unfold wf_fix, test_def, test_snd in *;
        try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; simpl in *; solve_all)]; try easy.
    - eapply Nat.ltb_lt. now eapply Nat.ltb_lt in H2.
    - destruct cstr_as_blocks; eauto. solve_all.
      destruct lookup_constructor_pars_args as [ [] |]; rtoProp; repeat solve_all.
  Qed.

  Lemma wellformed_lift n k k' t : wellformed k t -> wellformed (k + n) (lift n k' t).
  Proof using Type.
    revert k.
    induction t in n, k' |- * using EInduction.term_forall_list_ind; intros;
      simpl in *; rewrite -> ?andb_and in *;
      autorewrite with map;
      simpl closed in *; solve_all;
      unfold wf_fix, test_def, test_snd in *;
        try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; simpl in *; solve_all)]; try easy.

    - elim (Nat.leb_spec k' n0); intros. simpl; rewrite H0 /=.
      elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H1. lia.
      simpl; rewrite H0 /=. elim (Nat.ltb_spec); auto. intros.
      apply Nat.ltb_lt in H1. lia.
    - destruct cstr_as_blocks; eauto. destruct lookup_constructor_pars_args as [ [] | ]; rtoProp; repeat solve_all.
      destruct args; firstorder.
  Qed.

  Lemma wellformed_subst_eq {s k k' t} :
    forallb (wellformed k) s ->
    wellformed (k + k' + #|s|) t ->
    wellformed (k + k') (subst s k' t).
  Proof using Type.
    intros Hs. solve_all. revert Hs.
    induction t in H, k' |- * using EInduction.term_forall_list_ind; intros;
      simpl in *; auto;
      autorewrite with map => //;
      simpl wellformed in *; try change_Sk;
      unfold wf_fix, test_def in *; simpl in *;
      rtoProp; intuition auto;
      solve_all.

    - elim (Nat.leb_spec k' n); intros. simpl.
      destruct nth_error eqn:Heq.
      -- simpl. rewrite wellformed_lift //.
        now eapply nth_error_all in Heq; simpl; eauto; simpl in *.
      -- simpl. elim (Nat.ltb_spec); auto. rtoProp; intuition auto.
        apply nth_error_None in Heq. intros.
        apply Nat.ltb_lt in H0. lia.
      -- simpl. f_equal. rewrite H /=.
        elim: Nat.ltb_spec => //. intros. apply Nat.ltb_lt in H0. lia.
    - f_equal. simpl. solve_all.
      specialize (IHt (S k')).
      rewrite <- Nat.add_succ_comm in IHt.
      rewrite IHt //.
    - specialize (IHt2 (S k')).
      rewrite <- Nat.add_succ_comm in IHt2.
      eapply IHt2; auto.
    - destruct cstr_as_blocks; eauto.
      destruct lookup_constructor_pars_args as [ [] | ]; rtoProp; repeat solve_all. now destruct args; inv H0.
    - specialize (a (#|x.1| + k')) => //.
      rewrite Nat.add_assoc (Nat.add_comm k) in a.
      rewrite !Nat.add_assoc. eapply a => //.
      now rewrite !Nat.add_assoc in b.
    - destruct (dbody x) => //.
    - specialize (a (#|m| + k')).
      len. now rewrite !Nat.add_assoc !(Nat.add_comm k) in a, b0 |- *.
    - specialize (a (#|m| + k')); len.
      now rewrite !Nat.add_assoc !(Nat.add_comm k) in a, b |- *.
  Qed.

  Lemma wellformed_subst s k t :
    forallb (wellformed k) s -> wellformed (#|s| + k) t ->
    wellformed k (subst0 s t).
  Proof using Type.
    intros.
    unshelve epose proof (wellformed_subst_eq (k':=0) (t:=t) H); auto.
    rewrite Nat.add_0_r in H1.
    now rewrite Nat.add_comm in H1.
  Qed.

  Lemma wellformed_csubst t k u :
    wellformed 0 t ->
    wellformed (S k) u ->
    wellformed k (ECSubst.csubst t 0 u).
  Proof using Type.
    intros.
    rewrite ECSubst.closed_subst //.
    now eapply wellformed_closed.
    eapply wellformed_subst => /= //.
    rewrite andb_true_r. eapply wellformed_up; tea. lia.
  Qed.

  Lemma wellformed_substl ts k u :
    forallb (wellformed 0) ts ->
    wellformed (#|ts| + k) u ->
    wellformed k (ECSubst.substl ts u).
  Proof using Type.
    induction ts in u |- *; cbn => //.
    move/andP=> [] cla clts.
    intros clu. eapply IHts => //.
    eapply wellformed_csubst => //.
  Qed.

  Lemma wellformed_fix_subst mfix {hast : has_tFix}:
    forallb (isLambda ∘ dbody) mfix ->
    forallb (EAst.test_def (wellformed (#|mfix| + 0))) mfix ->
    forallb (wellformed 0) (fix_subst mfix).
  Proof using Type.
    intros hm hm'. unfold fix_subst.
    generalize (Nat.le_refl #|mfix|).
    move: {1 3}#|mfix| => n.
    induction n => //.
    intros hn. cbn. rewrite hast /=. rewrite /wf_fix_gen hm' /= andb_true_r.
    rewrite hm. cbn.
    apply/andP; split. apply Nat.ltb_lt. lia. apply IHn. lia.
  Qed.

  Lemma wellformed_cofix_subst mfix {hasco : has_tCoFix}:
    forallb (EAst.test_def (wellformed (#|mfix| + 0))) mfix ->
    forallb (wellformed 0) (cofix_subst mfix).
  Proof using Type.
    intros hm. unfold cofix_subst.
    generalize (Nat.le_refl #|mfix|).
    move: {1 3}#|mfix| => n.
    induction n => //.
    intros hn. cbn. rewrite hasco /=. rewrite /wf_fix_gen hm /= andb_true_r.
    apply/andP; split. apply Nat.ltb_lt. lia. apply IHn. lia.
  Qed.

  Lemma wellformed_cunfold_fix mfix idx n f :
    wellformed 0 (EAst.tFix mfix idx) ->
    cunfold_fix mfix idx = Some (n, f) ->
    wellformed 0 f.
  Proof using Type.
    move=> cl.
    rewrite /cunfold_fix.
    destruct nth_error eqn:heq => //.
    cbn in cl. move/andP: cl => [/andP[] hastf isfix /andP[] hidx cl].
    have := (nth_error_forallb heq cl) => cld.
    move=> [=] _ <-.
    eapply wellformed_substl => //. now eapply wellformed_fix_subst.
    rewrite fix_subst_length.
    apply cld.
  Qed.

  Lemma wellformed_cunfold_cofix mfix idx n f :
    wellformed 0 (EAst.tCoFix mfix idx) ->
    cunfold_cofix mfix idx = Some (n, f) ->
    wellformed 0 f.
  Proof using Type.
    move=> cl.
    rewrite /cunfold_cofix.
    destruct nth_error eqn:heq => //.
    cbn in cl. move/andP: cl => [hastf /andP[] _ cl].
    have := (nth_error_forallb heq cl) => cld.
    move=> [=] _ <-.
    eapply wellformed_substl => //. now eapply wellformed_cofix_subst.
    rewrite cofix_subst_length.
    apply cld.
  Qed.

  Lemma wellformed_iota_red pars c args brs br :
    forallb (wellformed 0) args ->
    nth_error brs c = Some br ->
    #|skipn pars args| = #|br.1| ->
    wellformed #|br.1| br.2 ->
    wellformed 0 (iota_red pars args br).
  Proof using Type.
    intros clargs hnth hskip clbr.
    rewrite /iota_red.
    eapply wellformed_substl => //.
    now rewrite forallb_rev forallb_skipn.
    now rewrite List.length_rev hskip Nat.add_0_r.
  Qed.

  Lemma wellformed_iota_red_brs pars c args brs br :
    forallb (wellformed 0) args ->
    nth_error brs c = Some br ->
    #|skipn pars args| = #|br.1| ->
    forallb (fun br => wellformed (#|br.1| + 0) br.2) brs ->
    wellformed 0 (iota_red pars args br).
  Proof using Type.
    intros clargs hnth hskip clbr.
    eapply wellformed_iota_red; tea => //.
    eapply nth_error_forallb in clbr; tea.
    now rewrite Nat.add_0_r in clbr.
  Qed.

  Lemma wellformed_mkApps n f args {hast : has_tApp} : wellformed n (mkApps f args) = wellformed n f && forallb (wellformed n) args.
  Proof using Type.
    induction args using rev_ind; cbn; auto => //.
    - now rewrite andb_true_r.
    - now rewrite mkApps_app /= IHargs hast /= forallb_app /= // !andb_assoc andb_true_r.
  Qed.

End EEnvFlags.

Lemma wellformed_closed_env {efl} {Σ : global_declarations} : wf_glob Σ -> closed_env Σ.
Proof.
  induction 1; cbn; auto.
  apply/andP; split.
  - unfold test_snd => /=.
    now eapply wellformed_closed_decl.
  - eapply IHwf_glob.
Qed.

Lemma extends_lookup {efl} {Σ Σ' c decl} :
  wf_glob Σ' ->
  extends Σ Σ' ->
  lookup_env Σ c = Some decl ->
  lookup_env Σ' c = Some decl.
Proof.
  intros wfΣ' Hl; apply Hl.
Qed.


Lemma extends_lookup_inductive {efl} {Σ Σ'} :
  wf_glob Σ' -> extends Σ Σ' ->
  forall ind b, lookup_inductive Σ ind = Some b ->
    lookup_inductive Σ' ind = Some b.
Proof.
  intros wf ex ind b.
  rewrite /lookup_inductive /lookup_minductive.
  destruct lookup_env eqn:lookup => //=.
  now rewrite (extends_lookup wf ex lookup).
Qed.


Lemma extends_lookup_constructor {efl} {Σ Σ'} :
  wf_glob Σ' -> extends Σ Σ' ->
  forall ind c b, lookup_constructor Σ ind c = Some b ->
    lookup_constructor Σ' ind c = Some b.
Proof.
  intros wf ex ind c b.
  rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  destruct lookup_env eqn:lookup => //.
  now rewrite (extends_lookup wf ex lookup).
Qed.

Lemma extends_constructor_isprop_pars_decl {efl} {Σ Σ'} :
  wf_glob Σ' -> extends Σ Σ' ->
  forall ind c b, constructor_isprop_pars_decl Σ ind c = Some b ->
    constructor_isprop_pars_decl Σ' ind c = Some b.
Proof.
  intros wf ex ind c b.
  rewrite /constructor_isprop_pars_decl.
  destruct lookup_constructor eqn:lookup => //.
  now rewrite (extends_lookup_constructor wf ex _ _ _ lookup).
Qed.

Lemma extends_is_propositional {efl} {Σ Σ'} :
  wf_glob Σ' -> extends Σ Σ' ->
  forall ind b, inductive_isprop_and_pars Σ ind = Some b -> inductive_isprop_and_pars Σ' ind = Some b.
Proof.
  intros wf ex ind b.
  rewrite /inductive_isprop_and_pars /lookup_inductive /lookup_minductive.
  destruct lookup_env eqn:lookup => //.
  now rewrite (extends_lookup wf ex lookup).
Qed.

Lemma extends_wellformed {efl} {Σ Σ'} :
  wf_glob Σ' -> extends Σ Σ' ->
  forall t n, wellformed Σ n t -> wellformed Σ' n t.
Proof.
  intros wf ex t.
  induction t using EInduction.term_forall_list_ind; cbn => //; intros; rtoProp; intuition auto; solve_all.
  all:try destruct lookup_env eqn:hl => //; try rewrite (extends_lookup wf ex hl).
  all:try destruct g => //.
  - destruct cstr_as_blocks; eauto; solve_all.
    destruct lookup_constructor_pars_args as [ [] | ]; rtoProp; repeat solve_all.
  - move: H0. rewrite /wf_brs. destruct lookup_inductive eqn:hl => //.
    now rewrite (extends_lookup_inductive wf ex _ _ hl).
  - move/andP: H0 => [] hn hf. unfold wf_fix. rewrite hn /=. solve_all.
  - move/andP: H0 => [] hn hf. unfold wf_fix. rewrite hn /=. solve_all.
Qed.

Lemma extends_wf_global_decl {efl} {Σ Σ'} :
  wf_glob Σ' -> extends Σ Σ' ->
  forall t, wf_global_decl Σ t -> wf_global_decl Σ' t.
Proof.
  intros wf ex []; cbn => //.
  destruct (cst_body c) => /= //.
  now eapply extends_wellformed.
Qed.

Lemma extends_fresh Σ kn d :
  fresh_global kn Σ ->
  extends Σ ((kn, d) :: Σ).
Proof.
  induction 1 in d |- *. red. cbn => //.
  intros kn' decl.
  cbn.
  destruct (eqb_spec x.1 kn) => //.
  destruct (eqb_spec kn' x.1) => //.
  - intros [= <-]. subst kn'.
    destruct (eqb_spec x.1 kn) => //.
  - intros hl.
    destruct (eqb_spec kn' kn) => //.
    subst. eapply (IHForall d) in hl.
    now cbn in hl; move: hl; rewrite eqb_refl.
Qed.

Lemma lookup_env_wellformed {efl} {Σ kn decl} : wf_glob Σ ->
  EGlobalEnv.lookup_env Σ kn = Some decl -> wf_global_decl Σ decl.
Proof.
  induction Σ; cbn => //.
  intros wf. depelim wf => /=.
  destruct (eqb_spec kn kn0).
  move=> [= <-]. eapply extends_wf_global_decl; tea. constructor; auto.
  now apply extends_fresh.
  intros hn.
  eapply extends_wf_global_decl; tea. 3:eapply IHΣ => //.
  now constructor.
  now apply extends_fresh.
Qed.
