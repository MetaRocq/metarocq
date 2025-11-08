From MetaRocq.Utils Require Export bytestring.
From MetaRocq.Utils Require Import utils MRList.
From MetaRocq.Common Require Import MonadBasicAst.
From MetaRocq.Template Require Import MonadAst TemplateMonad Ast Loader.
From MetaRocq.Quotation Require Export CommonUtils.
From Equations.Prop Require Import Classes.
From Stdlib Require Import Lists.List.
Export TemplateMonad.Common (export, local, global).
Import ListNotations.

Local Set Primitive Projections.
Local Unset Universe Minimization ToSet.
Local Open Scope bs.
Import MRMonadNotation.

Class quotation_of {T} (t : T) := quoted_term_of : Ast.term.
#[global] Arguments quoted_term_of {T} t {_}.
Class ground_quotable T := quote_ground : forall t : T, quotation_of t.
Class inductive_quotation_of {T} (t : T)
  := { qinductive : inductive
     ; qinst : Instance.t
     ; qquotation : quotation_of t := tInd qinductive qinst }.
Definition default_inductive_quotation_of {T} {t : T} (qt : quotation_of t) (pf : cls_is_true match qt with tInd _ _ => true | _ => false end)
  : inductive_quotation_of t
  := match qt return cls_is_true match qt with tInd _ _ => true | _ => false end -> _ with
     | tInd ind u => fun _ => @Build_inductive_quotation_of T t ind u
     | _ => fun pf : false = true => match diff_false_true pf with end
     end pf.

(* returns false iff a term is suitable for quotation at the top-level, i.e., returns true iff it mentions functor-bound arguments or is a local variable or evar *)
Definition head_term_is_bound (cur_modpath : modpath) (t : term) : bool
  := match t with
     | tConst kn _
     | tInd {| inductive_mind := kn |} _
     | tConstruct {| inductive_mind := kn |} _ _
     | tProj {| proj_ind := {| inductive_mind := kn |} |} _
     | tCase {| ci_ind := {| inductive_mind := kn |} |} _ _ _
       => negb (kername_is_okay cur_modpath kn)
     | tVar _
     | tEvar _ _
       => true
     | _ => false
     end.

Fixpoint head (t : term) : term
  := match t with
     | tCast t _ _
     | tApp t _
       => head t
     | _ => t
     end.

Polymorphic Definition infer_replacement_inductive {debug : debug_opt} (qt : term) : TemplateMonad (option inductive).
Proof.
  simple
    refine (match qt with
            | tInd ind u
            | tConstruct ind _ u
            | tCase {| ci_ind := ind |} {| puinst := u |} _ _
              => (indv <- tmUnquote (tInd ind u);;
                  let '(existT_typed_term _ indv) := indv in
                  v <- (tmInferInstance None (inductive_quotation_of indv));;
                  match v with
                  | my_Some v => ret (Some (replace_inductive_kn ind v.(qinductive)))
                  | my_None => (if debug then tmPrint (inductive_quotation_of indv) else ret tt);; ret None
                  end)
            | tProj {| proj_ind := ind |} t
              => (t <- tmUnquote t;;
                  let '(existT_typed_term ty _) := t in
                  ty <- tmEval hnf ty;;
                  ty <- tmQuote ty;;
                  let indv := head ty in
                  indv <- tmUnquote indv;;
                  let '(existT_typed_term _ indv) := indv in
                  v <- (tmInferInstance None (inductive_quotation_of indv));;
                  match v with
                  | my_Some v => ret (Some (replace_inductive_kn ind v.(qinductive)))
                  | my_None => (if debug then tmPrint (qt, inductive_quotation_of ind) else ret tt);; ret None
                  end)
            | _ => ret None
            end).
Defined.

Polymorphic Fixpoint replace_quotation_of' {debug : debug_opt} (do_top_inference : bool) (qt : term) : TemplateMonad term.
Proof.
  specialize (replace_quotation_of' debug).
  simple
    refine
    (let replace_quotation_of' := replace_quotation_of' true in
     let tmTryInferQuotation t
       := (t <- tmUnquote t;;
           let '(existT_typed_term _ t) := t in
           v <- tmInferInstance None (quotation_of t);;
           match v return TemplateMonad (option_instance Ast.term) with
           | my_Some v => ret (@my_Some _ v)
           | my_None => (if debug then tmPrint (quotation_of t) else ret tt);; ret (@my_None _)
           end) in
     let tmInferQuotation t
       := (v <- tmTryInferQuotation t;;
           match v return TemplateMonad Ast.term with
           | my_Some v => ret v
           | my_None => tmFail "No typeclass instance"
           end) in
     let tmMaybeInferQuotation 'tt :=
       if do_top_inference then tmInferQuotation qt else tmFail "Avoiding loops" in
     cur_modpath <- tmCurrentModPath tt;;
     match qt return TemplateMonad Ast.term with
     | tRel _
     | tSort _
     | tInt _
     | tFloat _
     | tString _
     | tArray _ _ _ _
     | tConst _ _
       => if head_term_is_bound cur_modpath qt
          then tmMaybeInferQuotation tt
          else ret qt
     | tConstruct ind idx u
       => if head_term_is_bound cur_modpath qt
          then (ind <- infer_replacement_inductive qt;;
                match ind with
                | Some ind => ret (tConstruct ind idx u)
                | None => tmMaybeInferQuotation tt
                end)
          else ret qt
     | tInd ind u
       => if head_term_is_bound cur_modpath qt
          then if do_top_inference
               then (ind <- infer_replacement_inductive qt;;
                     match ind with
                     | Some ind => ret (tInd ind u)
                     | None => tmMaybeInferQuotation tt
                     end)
               else tmFail "Avoiding ind loops"
          else ret qt
     | tVar _
       => tmMaybeInferQuotation tt
     | tEvar ev args => args <- monad_map replace_quotation_of' args;; ret (tEvar ev args)
     | tLambda na T M => T <- replace_quotation_of' T;; M <- replace_quotation_of' M;; ret (tLambda na T M)
     | tApp u v => u <- replace_quotation_of' u;; v <- monad_map replace_quotation_of' v;; ret (mkApps u v)
     | tProd na A B => A <- replace_quotation_of' A;; B <- replace_quotation_of' B;; ret (tProd na A B)
     | tCast c kind ty => c <- replace_quotation_of' c;; ty <- replace_quotation_of' ty;; ret (tCast c kind ty)
     | tLetIn na b ty b' => b <- replace_quotation_of' b;; ty <- replace_quotation_of' ty;; b' <- replace_quotation_of' b';; ret (tLetIn na b ty b')
     | tProj p c
       => res <- (if head_term_is_bound cur_modpath qt
                  then (ind <- infer_replacement_inductive qt;;
                        match ind with
                        | Some ind
                          => let p := {| proj_ind := ind ; proj_npars := p.(proj_npars) ; proj_arg := p.(proj_arg) |} in
                             ret (inr p)
                        | None
                          => res <- tmMaybeInferQuotation tt;;
                             ret (inl res)
                        end)
                  else ret (inr p));;
          match res with
          | inl res => ret res
          | inr p => c <- replace_quotation_of' c;;
                     ret (tProj p c)
          end
     | tFix mfix idx =>
         mfix' <- monad_map (monad_map_def replace_quotation_of' replace_quotation_of') mfix;;
         ret (tFix mfix' idx)
     | tCoFix mfix idx =>
         mfix' <- monad_map (monad_map_def replace_quotation_of' replace_quotation_of') mfix;;
         ret (tCoFix mfix' idx)
     | tCase ci p c brs
       => res <- (if head_term_is_bound cur_modpath qt
                  then (ind <- infer_replacement_inductive qt;;
                        match ind with
                        | Some ind
                          => ret (inr {| ci_ind := ind ; ci_npar := ci.(ci_npar) ; ci_relevance := ci.(ci_relevance) |})
                        | None
                          => res <- tmMaybeInferQuotation tt;;
                             ret (inl res)
                        end)
                  else ret (inr ci));;
          match res with
          | inl res => ret res
          | inr ci
            => p' <- monad_map_predicate ret replace_quotation_of' replace_quotation_of' p;;
               brs' <- monad_map_branches replace_quotation_of' brs;;
               c <- replace_quotation_of' c;;
               ret (tCase ci p' c brs')
          end
     end);
    try exact _.
Defined.

Polymorphic Definition replace_quotation_of {debug : debug_opt} {T} (t : T) : TemplateMonad term
  := qt <- tmQuote t;;
     replace_quotation_of' false qt.

(** for fancier goals when we have [ground_quotable] for some subterms but not for subterms of those subterms *)
Polymorphic Definition make_quotation_of {debug : debug_opt} {T} (t : T) : TemplateMonad (quotation_of t).
Proof.
  simple
    refine
    (qt <- tmQuote t;;
     let tmInferQuotation t
       := (t <- tmUnquote t;;
           let '(existT_typed_term _ t) := t in
           v <- tmInferInstance None (quotation_of t);;
           match v with
           | my_Some v => ret v
           | my_None => (if debug then tmPrint (quotation_of t) else ret tt);; tmFail "No typeclass instance"
           end) in
     cur_modpath <- tmCurrentModPath tt;;
     if head_term_is_bound cur_modpath qt
     then ((if debug then tmPrint qt else ret tt);; tmFail "bound argument is not ground")
     else
       match qt return TemplateMonad Ast.term with
       | tSort _
       | tConst _ _
       | tConstruct _ _ _
       | tInt _
       | tFloat _
       | tString _
       | tArray _ _ _ _
       | tInd _ _
         => ret qt
       | tCast t kind v
         => tmInferQuotation t
       | tApp f args
         => match List.rev args with
            | []
              => tmInferQuotation f
            | [x]
              => qf <- tmInferQuotation f;;
                 qx <- tmInferQuotation x;;
                 ret (mkApp qf qx)
            | x :: xs
              => qfxs <- tmInferQuotation (mkApps f (List.rev xs));;
                 qx <- tmInferQuotation x;;
                 ret (mkApp qfxs qx)
            end
       | tProj proj t => tmFail "Proj is not reduced"
       | tRel n => tmFail "Rel is not ground"
       | tVar id => tmFail "Var is not ground"
       | tEvar ev args => tmFail "Evar is not ground"
       | tProd na ty body => tmFail "Prod not yet handled"
       | tLambda na ty body => tmFail "Lambda not yet handled"
       | tLetIn na def def_ty body => tmFail "LetIn not yet handled"
       | tCase ci type_info discr branches => tmFail "Case not yet handled"
       | tFix mfix idx => tmFail "Fix not yet handled"
       | tCoFix mfix idx => tmFail "CoFix not yet handled"
       end);
    exact _.
Defined.

Ltac replace_quotation_of_goal _ :=
  let t := match goal with |- quotation_of ?t => t end in
  let T := match goal with |- @quotation_of ?T ?t => T end in
  run_template_program (@replace_quotation_of _ T t) (fun v => exact v).

Ltac make_quotation_of_goal _ :=
  let t := match goal with |- quotation_of ?t => t end in
  let T := match goal with |- @quotation_of ?T ?t => T end in
  run_template_program (@make_quotation_of _ T t) (fun v => exact v).

Ltac adjust_quotation_of_by_econstructor_then tac1 tac2 :=
  let f := match goal with |- ?f _ => f end in
  unshelve (let g := open_constr:(f _) in
            change g);
  [ unshelve econstructor
  | ];
  [ ..
  | repeat match goal with |- context[?ev] => is_evar ev; generalize ev; intro end ];
  [ tac1 () ..
  | tac2 () ].

Ltac adjust_ground_quotable_by_econstructor_inversion _ :=
  let pf := fresh "pf" in
  intro pf;
  adjust_quotation_of_by_econstructor_then ltac:(fun _ => inversion pf; try assumption) ltac:(fun _ => try exact _).

Ltac revert_quotable_hyp _ :=
  match goal with
  | [ H : _ |- quotation_of ?v ]
    => lazymatch v with
       | H => fail
       | context[H] => idtac
       end;
       revert H;
       lazymatch goal with
       | [ |- forall x : ?A, quotation_of (@?P x) ]
         => assert (quotation_of P);
            [
            | intro H;
              pose proof (_ : quotation_of H);
              change (quotation_of (P H)); exact _ ]
       end
  end.
Ltac revert_quotable_hyps _ :=
  repeat revert_quotable_hyp ().

Create HintDb quotation discriminated.

Module Export Instances.
  (* some performance settings *)
  #[export] Set Typeclasses Unique Instances.
  #[export] Instance default_debug : debug_opt | 1000 := false.
  #[export] Existing Instance quote_ground.
  #[export] Typeclasses Opaque quotation_of.
  #[export] Hint Constants Opaque : typeclass_instances.
  #[export] Typeclasses Transparent Relation_Definitions.relation. (* for setoid_rewrite *)
  #[export] Hint Extern 0 => progress intros : typeclass_instances.
  #[export] Hint Extern 0 (quotation_of _) => progress repeat autounfold with quotation in * : typeclass_instances.
  #[export] Hint Extern 0 (ground_quotable _) => progress repeat autounfold with quotation in * : typeclass_instances.
  #[export]
   Hint Extern 0 (quotation_of match ?t with _ => _ end) => is_var t; destruct t : typeclass_instances.
  #[export]
   Hint Extern 0 (ground_quotable match ?t with _ => _ end) => is_var t; destruct t : typeclass_instances.
  #[export]
   Hint Extern 1 (quotation_of _) => replace_quotation_of_goal () : typeclass_instances.
  #[export]
   Hint Extern 2 (quotation_of _) => make_quotation_of_goal () : typeclass_instances.
  (*#[export]
   Hint Extern 100 (quotation_of _) => progress revert_quotable_hyps () : typeclass_instances.*)
  #[export] Hint Mode cls_is_true + : typeclass_instances.
  #[export] Existing Instances qquotation | 10.
  (* Hack around COQBUG(https://github.com/coq/coq/issues/16760) *)
  #[export] Hint Extern 10 (@inductive_quotation_of ?T ?t) => simple notypeclasses refine (@default_inductive_quotation_of T t _ _) : typeclass_instances.
  #[export] Hint Extern 10 (cls_is_true ?b)
  => tryif is_evar b then refine (eq_refl true) else tryif has_evar b then fail else vm_compute; reflexivity
       : typeclass_instances.
  #[export] Hint Cut [
      ( _ * )
        qquotation
        ( _ * )
        qquotation
    ] : typeclass_instances.
End Instances.

Module PolymorphicInstances.
  #[export] Polymorphic Instance quote_relax_universe@{a b c} {A : Type@{a}} {q : @quotation_of Type@{b} A} : @quotation_of Type@{c} A | 100 := (q : Ast.term).
  #[export] Hint Cut [
      ( _ * )
        quote_relax_universe
        ( _ * )
        quote_relax_universe
    ] : typeclass_instances.
End PolymorphicInstances.

Module StrongerInstances.
  #[export]
   Hint Extern 1 (quotation_of match ?t with _ => _ end) => destruct t : typeclass_instances.
  #[export]
   Hint Extern 1 (ground_quotable match ?t with _ => _ end) => destruct t : typeclass_instances.
End StrongerInstances.

(** Some helper lemmas for defining quotations *)
Definition ground_quotable_of_bp {b P} (H : b = true -> P) {qH : quotation_of H} (H_for_safety : P -> b = true) : ground_quotable P.
Proof.
  intro p.
  exact (Ast.mkApps qH [_ : quotation_of (@eq_refl bool true)]).
Defined.

Definition ground_quotable_neg_of_bp {b P} (H : b = false -> ~P) {qH : quotation_of H} (H_for_safety : ~P -> b = false) : ground_quotable (~P).
Proof.
  intro p.
  exact (Ast.mkApps qH [_ : quotation_of (@eq_refl bool false)]).
Defined.

Definition ground_quotable_of_dec {P} (H : {P} + {~P}) {qP : quotation_of P} {qH : quotation_of H} : ground_quotable P
  := ground_quotable_of_bp bp_of_dec pb_of_dec.
Definition ground_quotable_neg_of_dec {P} (H : {P} + {~P}) {qP : quotation_of P} {qH : quotation_of H} : ground_quotable (~P)
  := ground_quotable_neg_of_bp neg_bp_of_dec neg_pb_of_dec.
Definition ground_quotable_neq_of_EqDec {A x y} {qA : quotation_of A} {quoteA : ground_quotable A} {H : EqDec A} {qH : quotation_of H} : ground_quotable (x <> y :> A)
  := ground_quotable_neg_of_dec (H x y).
#[export] Hint Extern 1 (ground_quotable (?x <> ?y :> ?A)) => simple notypeclasses refine (@ground_quotable_neq_of_EqDec A x y _ _ _ _) : typeclass_instances.

(* avoid universe inconsistencies *)
#[export] Polymorphic Instance qfst_cps {A B} {qA : quotation_of A} {qB : quotation_of B} : quotation_of (@fst A B) | 0
  := tApp <% @fst %> [qA; qB].
#[export] Polymorphic Instance qsnd_cps {A B} {qA : quotation_of A} {qB : quotation_of B} : quotation_of (@snd A B) | 0
  := tApp <% @snd %> [qA; qB].
#[export] Polymorphic Instance qpair_cps {A B} {qA : quotation_of A} {qB : quotation_of B} : quotation_of (@pair A B) | 0
  := tApp <% @pair %> [qA; qB].
#[export] Polymorphic Instance qprod_cps {A B} {qA : quotation_of A} {qB : quotation_of B} : quotation_of (@prod A B) | 0
  := tApp <% @prod %> [qA; qB].
#[export] Polymorphic Instance qSome_cps {A} {qA : quotation_of A} : quotation_of (@Some A) | 0
  := tApp <% @Some %> [qA].
#[export] Polymorphic Instance qNone_cps {A} {qA : quotation_of A} : quotation_of (@None A) | 0
  := tApp <% @None %> [qA].
#[export] Polymorphic Instance qoption_cps {A} {qA : quotation_of A} : quotation_of (@option A) | 0
  := tApp <% @option %> [qA].
#[export] Polymorphic Instance qcons_cps {A} {qA : quotation_of A} : quotation_of (@cons A) | 0
  := tApp <% @cons %> [qA].
#[export] Polymorphic Instance qnil_cps {A} {qA : quotation_of A} : quotation_of (@nil A) | 0
  := tApp <% @nil %> [qA].
#[export] Polymorphic Instance qlist_cps {A} {qA : quotation_of A} : quotation_of (@list A) | 0
  := tApp <% @list %> [qA].

Polymorphic Definition ground_quotable_of_iffT {A B} {quoteA : ground_quotable A} {qA : quotation_of A} {qB : quotation_of B} (H : A <~> B) {qH : quotation_of H} : ground_quotable B.
Proof.
  intro b.
  change (@quotation_of B (fst H (snd H b))).
  make_quotation_of_goal ().
Defined.
(* Transparent versions *)
Definition proj1 {A B} (x : A /\ B) : A := ltac:(apply x).
Definition proj2 {A B} (x : A /\ B) : B := ltac:(apply x).
Definition ground_quotable_of_iff {A B : Prop} {quoteA : ground_quotable A} {qA : quotation_of A} {qB : quotation_of B} (H : iff A B) {qH : quotation_of H} : ground_quotable B.
Proof.
  intro b.
  change (@quotation_of B (proj1 H (proj2 H b))).
  exact _.
Defined.
Definition quote_neg_of_iffT {A B} {quoteA : ground_quotable (A -> False)} {qA : quotation_of A} {qB : quotation_of B} (H : A <~> B) {qH : quotation_of H} : ground_quotable (B -> False).
Proof.
  intro nb.
  assert (na : A -> False) by (intro a; apply nb, H, a).
  change (@quotation_of (B -> False) (fun b => na (snd H b))).
  exact _.
Defined.
Definition quote_neg_of_iff {A B : Prop} {quoteA : ground_quotable (~A)} {qA : quotation_of A} {qB : quotation_of B} (H : iff A B) {qH : quotation_of H} : ground_quotable (~B).
Proof.
  intro nb.
  assert (na : ~A) by (intro a; apply nb, H, a).
  change (@quotation_of (~B) (fun b => na (proj2 H b))).
  exact _.
Defined.

Ltac unfold_quotation_of _ :=
  lazymatch goal with
  | [ |- @quotation_of ?A ?t ]
    => first [ progress cbv delta [t]
             | change (@quotation_of A (transparentify t)) ]
  end.

(* for universe adjustment with [tmDeclareQuotationOfModule], [tmMakeQuotationOfModule] *)
#[export] Unset MetaRocq Strict Unquote Universe Mode.
(* N.B. We need to kludge around COQBUG(https://github.com/coq/coq/issues/17303) in Kernames :-( *)
Polymorphic Definition tmMakeQuotationOfConstants_gen@{d t u _T _above_u'} {debug:debug_opt} (work_around_coq_bug_17303 : bool) (include_submodule : list ident -> bool) (include_supermodule : list ident -> list ident -> bool) (existing_instance : option hint_locality) (base : modpath) (cs : list global_reference) (tmDoWithDefinition : ident -> forall A : Type@{d}, A -> TemplateMonad@{t u} A) : TemplateMonad@{t u} unit
  := let warn_bad_ctx c ctx :=
       (_ <- tmMsg "tmPrepareMakeQuotationOfModule: cannot handle polymorphism";;
        _ <- tmPrint c;;
        _ <- tmPrint ctx;;
        tmReturn tt) in
     let tmDebugMsg s := (if debug
                          then tmMsg s
                          else tmReturn tt) in
     let tmDebugPrint {T : Type@{_T}} (v : T)
       := (if debug
           then tmPrint v
           else tmReturn tt) in
     let on_bad_relevance r :=
       (_ <- tmDebugMsg "skipping irrelevant constant";;
        _ <- tmDebugPrint r;;
        tmReturn tt) in
     let make_qname '(mp, name)
       (* ideally we'd replace _ with __ so that there can't be any collision, but the utility functions aren't written and we don't need it in practice *)
       := option_map
            (fun n => "q" ++ n)%bs
            match split_common_prefix base mp with
            | None => if include_supermodule [] []
                      then Some name
                      else None
            | Some (_, (_common, [], [])) => Some name
            | Some (_, (_common, [], postfix))
              => if include_submodule postfix
                 then Some (String.concat "__DOT__" postfix ++ "__" ++ name)
                 else None
            | Some (_, (_common, base_postfix, postfix))
              => if include_supermodule base_postfix postfix
                 then Some ("__DOT_DOT__" ++ String.concat "__DOT__" base_postfix ++ "__SLASH__" ++ String.concat "__DOT__" postfix ++ "__" ++ name)
                 else None
            end%bs in
     let tmDebugSkipGR '(mp, name) :=
       _ <- tmDebugMsg ("tmMakeQuotationOfConstants_gen: skipping excluded constant " ++ name);;
       _ <- tmDebugPrint (split_common_prefix base mp);;
       ret tt in
     let make_definition '(name, tyv)
       := ((let tmTyv := tmRetypeAroundMetaRocqBug853 name tyv in
            _ <- tmDebugPrint tmTyv;;
            '{| my_projT1 := ty ; my_projT2 := v |} <- tmTyv;;
            tmDef_name <- tmEval cbv (@tmDoWithDefinition (name:string));;
            let tmn := tmDef_name ty v in
            _ <- tmDebugPrint tmn;;
            n <- tmn;;
            _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: tmQuoteToGlobalReference";;
            qn <- tmQuoteToGlobalReference n;;
            tmReturn qn) : TemplateMonad global_reference) in
     let make_instance p
       := (match existing_instance return TemplateMonad unit with
           | Some locality
             => let tmEx := tmExistingInstance locality p in
                _ <- tmDebugPrint tmEx;;
                tmEx
           | None => tmReturn tt
           end) in
     let cs := dedup_grefs cs in
     cs <- tmEval cbv cs;;
     _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: looking up module constants";;
     ps <- monad_map@{_ _ Set _above_u'}
             (fun r
              => _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: handling";;
                 _ <- tmDebugPrint r;;
                 match r with
                 | ConstRef cr
                   => match make_qname cr with
                      | None => tmDebugSkipGR cr
                      | Some qname
                        => '(univs, rel) <- tmQuoteConstantUniversesAndRelevance cr false;;
                           match rel with
                           | Irrelevant => on_bad_relevance cr
                           | Relevant
                             => inst <- match univs with
                                        | Monomorphic_ctx => tmReturn ([] : Instance.t)
                                        | (Polymorphic_ctx (univs, constraints)) as ctx
                                          => _ <- warn_bad_ctx cr ctx;;
                                             tmReturn ([] : Instance.t)
                                        end;;
                                let c := tConst cr inst in
                                _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: tmUnquote";;
                                '{| my_projT1 := cty ; my_projT2 := cv |} <- tmUnquote c;;
                                _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: tmUnquote done";;
                                def <- make_definition
                                         (qname, if work_around_coq_bug_17303
                                                 then {| my_projT1 := term ; my_projT2 := c |}
                                                 else {| my_projT1 := @quotation_of cty cv ; my_projT2 := c |});;
                                make_instance def
                           end
                      end
                 | IndRef ind
                   => let '{| inductive_mind := r |} := ind in
                      match make_qname r with
                      | None => tmDebugSkipGR r
                      | Some qname
                        => inst <- (univs <- tmQuoteInductiveUniverses r;;
                                    match univs with
                                    | Monomorphic_ctx => tmReturn ([] : Instance.t)
                                    | (Polymorphic_ctx (univs, constraints)) as ctx
                                      => _ <- warn_bad_ctx r ctx;;
                                         tmReturn ([] : Instance.t)
                                    end);;
                           let c := tInd ind inst in
                           _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: tmUnquote";;
                           '{| my_projT1 := cty ; my_projT2 := cv |} <- tmUnquote c;;
                           _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: tmUnquote done";;
                           let tmcty := tmRetypeRelaxSetInCodomain@{t t u} qname cty in
                           _ <- tmDebugPrint tmcty;;
                           cty <- tmcty;;
                           let tmcv := tmObj_magic (B:=cty) cv in
                           _ <- tmDebugPrint tmcv;;
                           cv <- tmcv;;
                           let ty := @inductive_quotation_of cty cv in
                           let v : ty := {| qinductive := ind ; qinst := inst |} in
                           def <- make_definition
                                    (qname, {| my_projT1 := ty ; my_projT2 := v |});;
                           make_instance def
                      end
                 | ConstructRef _ _ | VarRef _ => tmReturn tt
                 end)
             cs;;
     ret tt.

Definition tmMakeQuotationOfConstants {debug:debug_opt} (include_submodule : list ident -> bool) (include_supermodule : list ident -> list ident -> bool) (existing_instance : option hint_locality) (base : modpath) (cs : list global_reference) : TemplateMonad unit
  := tmMakeQuotationOfConstants_gen false include_submodule include_supermodule existing_instance base cs (fun name ty body => @tmDefinition name ty body).

Definition tmMakeQuotationOfConstantsWorkAroundRocqBug17303 {debug:debug_opt} (include_submodule : list ident -> bool) (include_supermodule : list ident -> list ident -> bool) (base : modpath) (cs : list global_reference) : TemplateMonad unit
  := tmMakeQuotationOfConstants_gen true include_submodule include_supermodule None base cs (fun name ty body => @tmDefinition name ty body).

Definition tmDeclareQuotationOfConstants {debug:debug_opt} (include_submodule : list ident -> bool) (include_supermodule : list ident -> list ident -> bool) (existing_instance : option hint_locality) (base : modpath) (cs : list global_reference) : TemplateMonad unit
  := tmMakeQuotationOfConstants_gen false include_submodule include_supermodule existing_instance base cs (fun name ty _ => @tmAxiom name ty).

Variant submodule_inclusion : Set := only_toplevel | all_submodules_except (_ : list (list ident)) | toplevel_and_submodules (_ : list (list ident)) | everything.

#[local] Typeclasses Transparent ident IdentOT.t.
Definition is_submodule_of (super : list ident) (sub : list ident) : bool
  := firstn #|super| sub == super.
Definition is_supermodule_of (sub : list ident) (super : list ident) : bool
  := is_submodule_of super sub.
Definition include_submodule_of_submodule_inclusion (si : submodule_inclusion) : list ident -> bool
  := match si with
     | only_toplevel => fun _ => false
     | all_submodules_except ls => fun i => negb (existsb (is_supermodule_of i) ls)
     | toplevel_and_submodules ls => fun i => existsb (is_supermodule_of i) ls
     | everything => fun _ => true
     end.
Definition include_supermodule_of_submodule_inclusion (si : submodule_inclusion) : list ident -> list ident -> bool
  := match si with
     | everything => fun _ _ => true
     | _ => fun _ _ => false
     end.

Definition tmMakeQuotationOfModule {debug:debug_opt} (include_submodule : submodule_inclusion) (existing_instance : option hint_locality) (m : qualid) : TemplateMonad _
  := cs <- tmQuoteModule m;;
     base <- tmLocateModule1 m;;
     let include_supermodule := include_supermodule_of_submodule_inclusion include_submodule in
     let include_submodule := include_submodule_of_submodule_inclusion include_submodule in
     tmMakeQuotationOfConstants include_submodule include_supermodule existing_instance base cs.
Global Arguments tmMakeQuotationOfModule {_%_bool} _ _ _%_bs.

Definition tmMakeQuotationOfModuleWorkAroundRocqBug17303 {debug:debug_opt} (include_submodule : submodule_inclusion) (m : qualid) : TemplateMonad _
  := cs <- tmQuoteModule m;;
     base <- tmLocateModule1 m;;
     let include_supermodule := include_supermodule_of_submodule_inclusion include_submodule in
     let include_submodule := include_submodule_of_submodule_inclusion include_submodule in
     tmMakeQuotationOfConstantsWorkAroundRocqBug17303 include_submodule include_supermodule base cs.
Global Arguments tmMakeQuotationOfModuleWorkAroundRocqBug17303 {_%_bool} _ _%_bs.

Definition tmDeclareQuotationOfModule {debug:debug_opt} (include_submodule : submodule_inclusion) (existing_instance : option hint_locality) (m : qualid) : TemplateMonad _
  := cs <- tmQuoteModule m;;
     base <- tmLocateModule1 m;;
     let include_supermodule := include_supermodule_of_submodule_inclusion include_submodule in
     let include_submodule := include_submodule_of_submodule_inclusion include_submodule in
     tmDeclareQuotationOfConstants include_submodule include_supermodule existing_instance base cs.
Global Arguments tmDeclareQuotationOfModule {_%_bool} _ _ _%_bs.

(*
From Stdlib Require Import MSetPositive.
Instance: debug_opt := true.
MetaRocq Run (tmMakeQuotationOfModule None "Stdlib.MSets.MSetPositive.PositiveSet"%bs).
*)
