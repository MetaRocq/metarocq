From MetaRocq.PCUIC Require Import PCUICAst PCUICReduction.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Stdlib.Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Equations.Type.
From MetaRocq.Quotation.ToPCUIC.Utils Require Import (hints) All_Forall.
From MetaRocq.Quotation.ToPCUIC.Common Require Import (hints) BasicAst Universes Kernames.
From MetaRocq.Quotation.ToPCUIC.PCUIC Require Import (hints) PCUICAst PCUICPrimitive.

#[export] Instance quote_red1 {Σ Γ t u} : ground_quotable (@red1 Σ Γ t u).
Proof.
  cbv [ground_quotable].
  revert Γ t u.
  fix quote_red1 4.
  change (forall Γ t u, ground_quotable (@red1 Σ Γ t u)) in quote_red1.
  destruct 1.
  all: [ > replace_quotation_of_goal () .. ].
Defined.

(*#[export] Instance quote_red1_ctx {Σ Γ Δ} : ground_quotable (@red1_ctx Σ Γ Δ) := ltac:(cbv [red1_ctx]; exact _).*)
(*#[export] Instance quote_red1_ctx_rel {Σ Γ Δ} : ground_quotable (@red1_ctx_rel Σ Γ Δ) := ltac:(cbv [red1_ctx_rel]; exact _).*)

#[export] Instance quote_red {Σ Γ t u} : ground_quotable (@red Σ Γ t u) := ltac:(cbv [red]; exact _).

(* TODO: is it worth writing quotation functions for all these other types? *)

(*
Definition red_one_ctx_rel (Σ : global_env) (Γ : context) :=
  OnOne2_local_env
    (on_one_decl (fun (Δ : context) (t t' : term) => red Σ (Γ,,, Δ) t t')).

Definition red_ctx_rel Σ Γ := clos_refl_trans (red1_ctx_rel Σ Γ).
 *)
(*
Inductive red_decls Σ (Γ Γ' : context) : forall (x y : context_decl), Type :=
| red_vass na T T' :
    red Σ Γ T T' ->
    red_decls Σ Γ Γ' (vass na T) (vass na T')

| red_vdef_body na b b' T T' :
    red Σ Γ b b' ->
    red Σ Γ T T' ->
    red_decls Σ Γ Γ' (vdef na b T) (vdef na b' T').
Derive Signature NoConfusion for red_decls.

Definition red_context Σ := All2_fold (red_decls Σ).
Definition red_context_rel Σ Γ :=
  All2_fold (fun Δ Δ' => red_decls Σ (Γ ,,, Δ) (Γ ,,, Δ')).


  Inductive term_context :=
  | tCtxHole : term_context
  | tCtxEvar      : nat -> list_context -> term_context
  | tCtxProd_l      : aname -> term_context (* the type *) -> term -> term_context
  | tCtxProd_r      : aname -> term (* the type *) -> term_context -> term_context
  | tCtxLambda_l    : aname -> term_context (* the type *) -> term -> term_context
  | tCtxLambda_r    : aname -> term (* the type *) -> term_context -> term_context
  | tCtxLetIn_l     : aname -> term_context (* the term *) -> term (* the type *) ->
                    term -> term_context
  | tCtxLetIn_b     : aname -> term (* the term *) -> term_context (* the type *) ->
                    term -> term_context
  | tCtxLetIn_r     : aname -> term (* the term *) -> term (* the type *) ->
                    term_context -> term_context
  | tCtxApp_l       : term_context -> term -> term_context
  | tCtxApp_r       : term -> term_context -> term_context
  | tCtxCase_pars   : case_info -> list_context (* params *)
                      -> Instance.t -> context -> term -> (* predicate *)
                         term (* discriminee *) -> list (branch term) (* branches *) -> term_context
  | tCtxCase_pred   : case_info -> list term (* params *) -> Instance.t ->
        context -> (* context of predicate *)
        term_context (* type info *)
                         -> term (* discriminee *) -> list (branch term) (* branches *) -> term_context
  | tCtxCase_discr      : case_info -> predicate term (* type info *)
                 -> term_context (* discriminee *) -> list (branch term) (* branches *) -> term_context
  | tCtxCase_branch      : case_info -> predicate term (* type info *)
                           -> term (* discriminee *) -> branch_context (* branches *) -> term_context
  | tCtxProj      : projection -> term_context -> term_context
  (* | tCtxFix       : mfixpoint_context -> nat -> term_context harder because types of fixpoints are necessary *)
  (* | tCtxCoFix     : mfixpoint_context -> nat -> term_context *)

  with list_context :=
   | tCtxHead : term_context -> list term -> list_context
   | tCtxTail : term -> list_context -> list_context

  with branch_context :=
   | tCtxHead_nat : (context * term_context) -> list (branch term) -> branch_context
   | tCtxTail_nat : (branch term) -> branch_context -> branch_context.


  Inductive contextual_closure (red : forall Γ, term -> term -> Type) : context -> term -> term -> Type@{wf_context_i} :=
  | ctxclos_atom Γ t : atom t -> contextual_closure red Γ t t
  | ctxclos_ctx Γ (ctx : term_context) (u u' : term) :
      red (hole_context ctx Γ) u u' -> contextual_closure red Γ (fill_context u ctx) (fill_context u' ctx).

    Abbreviation red1_one_term Γ :=
      (@OnOne2 (term × _) (Trel_conj (on_Trel (red1 Σ Γ) fst) (on_Trel eq snd))).
    Abbreviation red_one_term Γ :=
      (@OnOne2 (term × _) (Trel_conj (on_Trel (red Σ Γ) fst) (on_Trel eq snd))).

    Abbreviation red1_one_context_decl Γ :=
      (@OnOne2 (context × _) (Trel_conj (on_Trel (red1_ctx_rel Σ Γ) fst) (on_Trel eq snd))).

    Definition red_one_context_decl_rel Σ Γ :=
      (OnOne2_local_env (on_one_decl (fun Δ t t' => red Σ (Γ ,,, Δ) t t'))).

    Abbreviation red_one_context_decl Γ :=
      (@OnOne2 (context × _)
      (Trel_conj (on_Trel (red_ctx_rel Σ Γ) fst) (on_Trel eq snd))).

    Abbreviation red1_one_branch p Γ :=
      (@OnOne2 _ (fun br br' =>
        let ctx := inst_case_context p.(pparams) p.(puinst) (snd br) in
        Trel_conj (on_Trel (red1 Σ (Γ ,,, ctx)) fst) (on_Trel eq snd) br br')).
    Abbreviation red_one_branch p Γ :=
      (@OnOne2 _ (fun br br' =>
        let ctx := inst_case_context p.(pparams) p.(puinst) (snd br) in
        Trel_conj (on_Trel (red Σ (Γ ,,, ctx)) fst) (on_Trel eq snd) br br')).

    Inductive redl {T A} {P} l : list (T × A) -> Type :=
    | refl_redl : redl l l
    | trans_redl :
        forall l1 l2,
          redl l l1 ->
          P l1 l2 ->
          redl l l2.
    Derive Signature for redl.

    Definition redl_term {A} Γ := @redl term A (red1_one_term Γ).
    Definition redl_context {A} Γ := @redl context A (red1_one_context_decl Γ).
    Definition redl_branch p Γ := @redl term _ (red1_one_branch p Γ).
*)
