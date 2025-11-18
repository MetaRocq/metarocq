(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Uint63 FloatOps FloatAxioms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Primitive EnvMap.
From MetaRocq.Common Require Import MonadBasicAst.
From MetaRocq.Template Require Import AstUtils MonadAst.
From MetaRocq.Template Require TemplateProgram.
From MetaRocq.Template Require TemplateMonad.Core.
From MetaRocq.Template Require Import TemplateMonad.Common.
From MetaRocq.PCUIC Require Import PCUICAst PCUICPrimitive PCUICCases PCUICProgram.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC.

Import MRMonadNotation.
Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Section with_tc.
  Universes t u.
  Context {T : Type@{t} -> Type@{u}}.
  Context {M : Monad@{t u} T}.

  Section helpers.
    Context (monad_trans : Ast.term -> T term)
      (tmQuoteInductive : kername -> T Ast.Env.mutual_inductive_body)
      (tmFail : forall {A:Type@{t}}, string -> T A).

    Definition monad_trans_decl' (d : Ast.Env.context_decl) :=
      let '{| decl_body := decl_body ; decl_type := decl_type ; decl_name := decl_name |} := d in
      decl_body <- monad_option_map@{t u t t} monad_trans decl_body;;
      decl_type <- monad_trans decl_type;;
      ret {| decl_name := decl_name;
            decl_body := decl_body;
            decl_type := decl_type |}.

    Definition monad_trans_local' Γ := monad_map monad_trans_decl' Γ.

    Definition monad_trans_constructor_body' (d : Ast.Env.constructor_body) :=
      let '{| Ast.Env.cstr_args := cstr_args ; Ast.Env.cstr_name := cstr_name ; Ast.Env.cstr_indices := cstr_indices ; Ast.Env.cstr_type := cstr_type ; Ast.Env.cstr_arity := cstr_arity |} := d in
      cstr_args <- monad_trans_local' cstr_args;;
      cstr_indices <- monad_map@{t u t t} monad_trans cstr_indices;;
      cstr_type <- monad_trans cstr_type;;
      ret {| cstr_name := cstr_name;
            cstr_args := cstr_args;
            cstr_indices := cstr_indices;
            cstr_type := cstr_type;
            cstr_arity := cstr_arity |}.

    Definition monad_trans_projection_body' (d : Ast.Env.projection_body) :=
      let '{| Ast.Env.proj_name := proj_name ; Ast.Env.proj_type := proj_type ; Ast.Env.proj_relevance := proj_relevance |} := d in
      proj_type <- monad_trans proj_type;;
      ret {| proj_name := proj_name;
            proj_type := proj_type;
            proj_relevance := proj_relevance |}.

    Definition monad_trans_one_ind_body' (d : Ast.Env.one_inductive_body) :=
      let '{| Ast.Env.ind_name := ind_name;
             Ast.Env.ind_relevance := ind_relevance;
             Ast.Env.ind_indices := ind_indices;
             Ast.Env.ind_sort := ind_sort;
             Ast.Env.ind_type := ind_type;
             Ast.Env.ind_kelim := ind_kelim;
             Ast.Env.ind_ctors := ind_ctors;
             Ast.Env.ind_projs := ind_projs |} := d in
      ind_indices <- monad_trans_local' ind_indices;;
      ind_type <- monad_trans ind_type;;
      ind_ctors <- monad_map@{t u t t} monad_trans_constructor_body' ind_ctors;;
      ind_projs <- monad_map@{t u t t} monad_trans_projection_body' ind_projs;;
      ret {| ind_name := ind_name;
            ind_relevance := ind_relevance;
            ind_indices := ind_indices;
            ind_sort := ind_sort;
            ind_type := ind_type;
            ind_kelim := ind_kelim;
            ind_ctors := ind_ctors;
            ind_projs := ind_projs |}.

    Definition monad_trans_constant_body' bd :=
      let '{| Ast.Env.cst_type := cst_type;
             Ast.Env.cst_body := cst_body;
             Ast.Env.cst_universes := cst_universes;
             Ast.Env.cst_relevance := cst_relevance |} := bd in
      cst_type <- monad_trans cst_type;;
      cst_body <- monad_option_map@{t u t t} monad_trans cst_body;;
      ret {| cst_type := cst_type;
            cst_body := cst_body;
            cst_universes := cst_universes;
            cst_relevance := cst_relevance |}.

    Definition monad_trans_minductive_body' md :=
      let '{| Ast.Env.ind_finite := ind_finite;
             Ast.Env.ind_npars := ind_npars;
             Ast.Env.ind_params := ind_params;
             Ast.Env.ind_bodies := ind_bodies;
             Ast.Env.ind_universes := ind_universes;
             Ast.Env.ind_variance := ind_variance |} := md in
      ind_params <- monad_trans_local' ind_params;;
      ind_bodies <- monad_map@{t u t t} monad_trans_one_ind_body' ind_bodies;;
      ret {| ind_finite := ind_finite;
            ind_npars := ind_npars;
            ind_params := ind_params;
            ind_bodies := ind_bodies;
            ind_universes := ind_universes;
            ind_variance := ind_variance |}.

    Definition monad_trans_global_decl' (d : Ast.Env.global_decl) :=
      match d with
      | Ast.Env.ConstantDecl bd => bd <- monad_trans_constant_body' bd;; ret (ConstantDecl bd)
      | Ast.Env.InductiveDecl bd => bd <- monad_trans_minductive_body' bd;; ret (InductiveDecl bd)
      end.

    Definition tmQuoteInductive' (mind : kername) : T mutual_inductive_body :=
      bd <- tmQuoteInductive mind;;
      monad_trans_minductive_body' bd.

    Definition TransLookup_lookup_inductive' (ind : inductive) : T (mutual_inductive_body × one_inductive_body) :=
      let '{| inductive_mind := inductive_mind ; inductive_ind := inductive_ind |} := ind in
      mdecl <- tmQuoteInductive' inductive_mind;;
      let '{| ind_bodies := ind_bodies |} := mdecl in
      match nth_error ind_bodies inductive_ind with
      | Some idecl => ret (mdecl, idecl)
      | None => tmFail _ "TransLookup.lookup_inductive: nth_error: Not_found"
      end.

  End helpers.

  Section with_helper.
    Context (TransLookup_lookup_inductive' : inductive -> T (mutual_inductive_body × one_inductive_body))
      (tmEval : forall {A:Type@{t}}, A -> T A).

    Fixpoint monad_trans' (t : Ast.term) : T term
      := match t with
         | Ast.tRel n => ret (tRel n)
         | Ast.tVar n => ret (tVar n)
         | Ast.tEvar ev args => args <- monad_map@{t u t t} monad_trans' args;; ret (tEvar ev args)
         | Ast.tSort u => ret (tSort u)
         | Ast.tConst c u => ret (tConst c u)
         | Ast.tInd c u => ret (tInd c u)
         | Ast.tConstruct c k u => ret (tConstruct c k u)
         | Ast.tLambda na T M => T <- monad_trans' T;; M <- monad_trans' M;; ret (tLambda na T M)
         | Ast.tApp u v => u <- monad_trans' u;; v <- monad_map@{t u t t} monad_trans' v;; ret (mkApps u v)
         | Ast.tProd na A B => A <- monad_trans' A;; B <- monad_trans' B;; ret (tProd na A B)
         | Ast.tCast c kind t => t <- monad_trans' t;; c <- monad_trans' c;; ret (tApp (tLambda (mkBindAnn nAnon Relevant) t (tRel 0)) c)
         | Ast.tLetIn na b t b' => b <- monad_trans' b;; t <- monad_trans' t;; b' <- monad_trans' b';; ret (tLetIn na b t b')
         | Ast.tCase ci p c brs =>
             let '{| ci_ind := ci_ind |} := ci in
             p' <- monad_map_predicate ret monad_trans' monad_trans' p;;
             let '{| Ast.pparams := pparams ; Ast.puinst := puinst ; Ast.pcontext := pcontext ; Ast.preturn := preturn |} := p' in
             brs' <- monad_map@{t u t t} (monad_map_branch monad_trans') brs;;
             '(mdecl, idecl) <- TransLookup_lookup_inductive' ci_ind;;
             let '{| ind_ctors := ind_ctors |} := idecl in
             tp <- tmEval _ (trans_predicate ci_ind mdecl idecl pparams puinst pcontext preturn);;
             tbrs <- tmEval
                       _ (map2 (fun cdecl '{| Ast.bcontext := bcontext ; Ast.bbody := bbody |} => trans_branch ci_ind mdecl cdecl bcontext bbody)
                            ind_ctors brs');;
             c <- monad_trans' c;;
             ret (tCase ci tp c tbrs)
         | Ast.tProj p c => c <- monad_trans' c;; ret (tProj p c)
         | Ast.tFix mfix idx =>
             mfix' <- monad_map@{t u t t} (monad_map_def monad_trans' monad_trans') mfix;;
             ret (tFix mfix' idx)
         | Ast.tCoFix mfix idx =>
             mfix' <- monad_map@{t u t t} (monad_map_def monad_trans' monad_trans') mfix;;
             ret (tCoFix mfix' idx)
         | Ast.tInt n => ret (tPrim (primInt; primIntModel n))
         | Ast.tFloat n => ret (tPrim (primFloat; primFloatModel n))
         | Ast.tString n => ret (tPrim (primString; primStringModel n))
         | Ast.tArray l v d ty =>
            v' <- monad_map@{t u t t} monad_trans' v ;;
            d' <- monad_trans' d ;;
            ty' <- monad_trans' ty ;;
            ret (tPrim ((primArray; primArrayModel {| array_universe := l; array_value := v'; array_default := d'; array_type := ty' |})))
      end.
  End with_helper.
End with_tc.

Import TemplateMonad.Core.

Class eval_pcuic_quotation : Set := pcuic_quotation_red_strategy : option reductionStrategy.
#[export] Instance default_eval_pcuic_quotation : eval_pcuic_quotation := None.

Definition tmMaybeEval@{t u} `{eval_pcuic_quotation} {A : Type@{t}} (v : A) : TemplateMonad@{t u} A
  := match pcuic_quotation_red_strategy with
     | None => tmReturn v
     | Some s => tmEval s v
     end.

Definition monad_trans@{t u} `{eval_pcuic_quotation} : Ast.term -> TemplateMonad@{t u} term
  := tmFix@{u u t u}
       (fun monad_trans v
        => bind@{t u} (@monad_trans'@{t u} TemplateMonad@{t u} TemplateMonad_OptimizedMonad@{t u}
                  (@TransLookup_lookup_inductive'@{t u} TemplateMonad@{t u} TemplateMonad_OptimizedMonad@{t u} monad_trans tmQuoteInductive@{t u} (@tmFail@{t u}))
                  (fun A => tmMaybeEval@{t u})
                  v) tmMaybeEval@{t u}).

Definition monad_trans_decl@{t u} `{eval_pcuic_quotation} := @monad_trans_decl'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_local@{t u} `{eval_pcuic_quotation} := @monad_trans_local'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_constructor_body@{t u} `{eval_pcuic_quotation} := @monad_trans_constructor_body'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_projection_body@{t u} `{eval_pcuic_quotation} := @monad_trans_projection_body'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_one_ind_body@{t u} `{eval_pcuic_quotation} := @monad_trans_one_ind_body'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_constant_body@{t u} `{eval_pcuic_quotation} := @monad_trans_constant_body'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_minductive_body@{t u} `{eval_pcuic_quotation} := @monad_trans_minductive_body'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_global_decl@{t u} `{eval_pcuic_quotation} := @monad_trans_global_decl'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition tmQuoteInductive@{t u} `{eval_pcuic_quotation} := @tmQuoteInductive'@{t u} TemplateMonad TemplateMonad_Monad monad_trans tmQuoteInductive.
