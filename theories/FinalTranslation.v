(* Translation from our special ITT to TemplateCoq itself  *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst SLiftSubst SCommon
                             Typing ITyping Checker Template.
Import MonadNotation.

Module T := Typing.

(* From Simon Boulier *)
Inductive tsl_error :=
| NotEnoughFuel
| TranslationNotFound (id : ident)
| TranslationNotHandled
| TypingError (t : type_error).

Inductive tsl_result A :=
| Success : A -> tsl_result A
| Error : tsl_error -> tsl_result A.

Arguments Success {_} _.
Arguments Error {_} _.

Instance tsl_monad : Monad tsl_result :=
  {| ret A a := Success a ;
     bind A B m f :=
       match m with
       | Success a => f a
       | Error e => Error e
       end
  |}.

Instance monad_exc : MonadExc tsl_error tsl_result :=
  { raise A e := Error e;
    catch A m f :=
      match m with
      | Success a => m
      | Error t => f t
      end
  }.

Open Scope t_scope.

(* We need to assert somewhere that we ask a Σ containing Σ-types, eq-types,
   UIP and funext.
   The rest will be obtained through quoting.
 *)

Definition J (A : Type) (u : A) (P : forall (x : A), u = x -> Type)
           (w : P u (eq_refl u)) (v : A) (p : u = v) : P v p :=
  match p with
  | eq_refl => w
  end.

Definition transport {T1 T2 : Type} (p : T1 = T2) (t : T1) : T2 :=
  J Type T1 (fun X e => T1 -> X) (fun x => x) T2 p t.

Axiom UIP : forall {A} {x y : A} (p q : x = y), p = q.
Axiom funext : forall {A B} {f g : forall (x : A), B x}, (forall x, f x = g x) -> f = g.

Quote Definition tEq := @eq.
Quote Definition tRefl := @eq_refl.
Quote Definition tJ := J.
Quote Definition tTransport := @transport.
Quote Definition tUip := @UIP.
Quote Definition tFunext := @funext.

Definition mkEq (A u v : term) : term :=
  tApp tEq [ A ; u ; v ].

Definition mkRefl (A u : term) : term :=
  tApp tRefl [A ; u].

Definition mkJ (A u P w v p : term) : term :=
  tApp tJ [ A ; u ; P ; w ; v ; p ].

Definition mkTransport (T1 T2 p t : term) : term :=
  tApp tTransport [ T1 ; T2 ; p ; t ].

Definition mkUip (A u v p q : term) : term :=
  tApp tUip [ A ; u ; v ; p ; q ].

Definition mkFunext (A B f g e : term) : term :=
  tApp tFunext [ A ; B ; f ; g ; e ].

Definition heq {A} (a : A) {B} (b : B) :=
  { p : A = B & transport p a = b }.

Quote Definition tHeq := @heq.

Definition mkHeq (A a B b : term) : term :=
  tApp tHeq [ A ; a ; B ; b ].

Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (Γ : context) (t : sterm)
  : tsl_result term :=
  match fuel with
  | 0 => raise NotEnoughFuel
  | S fuel =>
    match t with
    | sRel n => ret (tRel n)
    | sSort s => ret (tSort s)
    | sProd n A B =>
      A' <- tsl_rec fuel Σ Γ A ;;
      B' <- tsl_rec fuel Σ (Γ ,, vass n A') B ;;
      ret (tProd n A' B')
    | sLambda n A B t =>
      A' <- tsl_rec fuel Σ Γ A ;;
      t' <- tsl_rec fuel Σ (Γ ,, vass n A') t ;;
      ret (tLambda n A' t')
    | sApp u n A B v =>
      u' <- tsl_rec fuel Σ Γ u ;;
      v' <- tsl_rec fuel Σ Γ v ;;
      ret (tApp u' [v'])
    | sEq A u v =>
      A' <- tsl_rec fuel Σ Γ A ;;
      (* match infer Σ Γ A' with *)
      (* | Checked (tSort s) => *)

      (* | Checked T => raise (TypingError (NotASort T)) *)
      (* | TypeError t => raise (TypingError t) *)
      (* end *)
      u' <- tsl_rec fuel Σ Γ u ;;
      v' <- tsl_rec fuel Σ Γ v ;;
      ret (mkEq A' u' v')
    | sRefl A u =>
      A' <- tsl_rec fuel Σ Γ A ;;
      u' <- tsl_rec fuel Σ Γ u ;;
      ret (mkRefl A' u')
    | sJ A u P w v p =>
      A' <- tsl_rec fuel Σ Γ A ;;
      u' <- tsl_rec fuel Σ Γ u ;;
      P' <- tsl_rec fuel Σ (Γ ,, vass nAnon A' ,, vass nAnon (mkEq (LiftSubst.lift0 1 A') (LiftSubst.lift0 1 u') (tRel 0))) P ;;
      w' <- tsl_rec fuel Σ Γ w ;;
      v' <- tsl_rec fuel Σ Γ v ;;
      p' <- tsl_rec fuel Σ Γ p ;;
      ret (mkJ A' u' P' w' v' p')
    | sTransport T1 T2 p t =>
      T1' <- tsl_rec fuel Σ Γ T1 ;;
      T2' <- tsl_rec fuel Σ Γ T1 ;;
      p' <- tsl_rec fuel Σ Γ p ;;
      t' <- tsl_rec fuel Σ Γ t ;;
      ret (mkTransport T1' T2' p' t')
    | _ => raise TranslationNotHandled
    end
  end.

(* Delimit Scope i_scope with i. *)

Fixpoint tsl_ctx (fuel : nat) (Σ : global_context) (Γ : scontext)
  : tsl_result context :=
  match Γ with
  | [] => ret []
  | a :: Γ =>
    Γ' <- tsl_ctx fuel Σ Γ ;;
    A' <- tsl_rec fuel Σ Γ' (sdecl_type a) ;;
    ret (Γ' ,, vass (sdecl_name a) A')
  end.

Fixpoint extract_mind_decl_from_program (id : ident) (p : program)
  : option minductive_decl
  := match p with
     | PConstr _ _ _ _ p => extract_mind_decl_from_program id p
     | PType id' n inds p => if string_dec id id' then
                              Some (Build_minductive_decl n inds)
                            else extract_mind_decl_from_program id p
     | PAxiom _ _ _ p => extract_mind_decl_from_program id p
     | PIn _ => None
     end.

Fixpoint extract_cst_decl_from_program (id : ident) (p : program)
  : option constant_decl
  := match p with
     | PConstr id' uist t1 t2 p => if string_dec id id' then
                                    Some (Build_constant_decl id uist t1 (Some t2))
                                  else extract_cst_decl_from_program id p
     | PType id' n inds p => extract_cst_decl_from_program id p
     | PAxiom _ _ _ p => extract_cst_decl_from_program id p
     | PIn _ => None
     end.

Definition option_get {A} (default : A) (x : option A) : A
  := match x with
     | Some x => x
     | None => default
     end.

Open Scope string_scope.

Definition get_idecl id prog := option_get (Build_minductive_decl 0 []) (extract_mind_decl_from_program id prog).
Definition get_cdecl id prog := option_get (Build_constant_decl "XX" [] (tRel 0) None) (extract_cst_decl_from_program id prog).

Quote Recursively Definition eq_prog := @eq.
Definition eq_decl :=
  Eval compute in (get_idecl "Coq.Init.Logic.eq" eq_prog).

Quote Recursively Definition J_prog := J.
Definition J_decl :=
  Eval compute in (get_cdecl "Top.J" J_prog).

Quote Recursively Definition Transport_prog := @transport.
Definition Transport_decl :=
  Eval compute in (get_cdecl "Top.transport" Transport_prog).

Definition Σ : global_context :=
  [ InductiveDecl "Coq.Init.Logic.eq" eq_decl ;
    ConstantDecl "Top.J" J_decl ;
    ConstantDecl "Top.transport" Transport_decl
  ].

(* Checking for the sake of checking *)
Compute (infer Σ [] tEq).
Compute (infer Σ [] tJ).
Compute (infer Σ [] tTransport).

Theorem soundness :
  forall {Γ t A},
    Σ ;;; Γ |-i t : A ->
    forall {fuel Γ' t' A'},
      tsl_ctx fuel Σ Γ = Success Γ' ->
      tsl_rec fuel Σ Γ' t = Success t' ->
      tsl_rec fuel Σ Γ' A = Success A' ->
      Σ ;;; Γ' |-- t' : A'.
Proof.
  intros Γ t A h.
  dependent induction h ; intros fuel Γ' t' A' hΓ ht hA.
  all: destruct fuel ; try discriminate.

  - cbn in ht. inversion_clear ht.
    admit.

  - cbn in ht, hA. inversion_clear ht. inversion_clear hA.
    apply T.type_Sort.

  - cbn in hA. inversion_clear hA.
    simpl in ht. inversion ht.
    admit.

  - admit.

  - admit.

  - cbn in hA. inversion_clear hA.
    cbn in ht.
    destruct (tsl_rec fuel Σ Γ' A) ; destruct (tsl_rec fuel Σ Γ' u) ; try (now inversion ht).
    destruct (tsl_rec fuel Σ Γ' v) ; inversion_clear ht.
    eapply T.type_App.
    + econstructor. econstructor. split.
      * econstructor.
      * cbn. f_equal.
    + econstructor.
Abort.