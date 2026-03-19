(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Translations Require Import translation_utils sigma.
Import MonadNotation.

Infix "<=" := Nat.leb.

Definition default_term := tVar "constant_not_found".
Definition debug_term msg:= tVar ("debug: " ^ msg).


(** * ****************** WARNING : WIP ! ****************** * **)

(** Uses unsafe termination for the translation function *)
Print Typing Flags.
Unset Guard Checking.


MetaRocq Quote Definition tUnit := unit.
MetaRocq Quote Definition ttt := tt.

Fixpoint kproj (k : nat) (t : term) :=
  match k with
  | 0 => t
  | S k => kproj k (proj1 t)
  end.

Notation app0 := (fun t => subst_app t [tRel 0]).



Fixpoint tsl (ΣE : tsl_context) (Γ : context) (t : term) {struct t}
  : tsl_result term :=
  match t with
  | tSort s => Γ' <- tsl_ctx ΣE Γ ;;
              ret (tLambda (nNamed "γ") Γ' (tSort s))
  | tRel k => Γ' <- tsl_ctx ΣE Γ ;;
             ret (tLambda (nNamed "γ") Γ' (proj2 (kproj k (tRel 0))))
  (* | tEvar k ts => tEvar k (map (tsl_rec0 n) ts) *)
  | tCast t c A => Γ' <- tsl_ctx ΣE Γ ;;
                  t' <- tsl ΣE Γ t ;;
                  A' <- tsl ΣE Γ A ;;
                  ret (tLambda (nNamed "γ") Γ'
                               (tCast (app0 t') c (app0 A')))
  | tProd na A B => Γ' <- tsl_ctx ΣE Γ ;;
                   A' <- tsl ΣE Γ A ;;
                   B' <- tsl ΣE (Γ ,, vass na A) B ;;
                   ret (tLambda (nNamed "γ") Γ'
                                (tProd na (app0 A')
                                   (subst_app B' [pair Γ' A' (tRel 1) (tRel 0)])))
  | tLambda na A t => Γ' <- tsl_ctx ΣE Γ ;;
                     A' <- tsl ΣE Γ A ;;
                     t' <- tsl ΣE (Γ ,, vass na A) t ;;
                     ret (tLambda (nNamed "γ") Γ'
                            (tLambda na (app0 A')
                               (subst_app t' [pair Γ' (up A') (tRel 1) (tRel 0)])))
  | tLetIn na t A u => Γ' <- tsl_ctx ΣE Γ ;;
                      t' <- tsl ΣE Γ t ;;
                      A' <- tsl ΣE Γ A ;;
                      u' <- tsl ΣE (Γ ,, vdef na t A) u ;;
                      ret (tLambda (nNamed "γ") Γ' (tLetIn na t' A' u'))
  | tApp t lu => Γ' <- tsl_ctx ΣE Γ ;;
                t' <- tsl ΣE Γ t ;;
                lu' <- monad_map (tsl ΣE Γ) lu ;;
                ret (tLambda (nNamed "γ") Γ' (mkApps (app0 t') (map app0 lu')))
  (* | tCase ik t u br => tCase ik (tsl_rec0 n t) (tsl_rec0 n u) *)
  (*                           (map (fun x => (fst x, tsl_rec0 n (snd x))) br) *)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | tConst s univs => Γ' <- tsl_ctx ΣE Γ ;;
                     t' <- lookup_tsl_table' (snd ΣE) (ConstRef s) ;;
                     ret (tLambda (nNamed "γ") Γ' (subst_app t' [ttt]))
  | tInd i univs => lookup_tsl_table' (snd ΣE) (IndRef i)
  | tConstruct i n univs => lookup_tsl_table' (snd ΣE) (ConstructRef i n)
  | tProj p t => Γ' <- tsl_ctx ΣE Γ ;;
                t' <- tsl ΣE Γ t ;;
                ret (tLambda (nNamed "γ") Γ' (tProj p t'))

  | _ => ret t
  end
with tsl_ctx (ΣE : tsl_context) (Γ : context) {struct Γ} : tsl_result term :=
       match Γ with
       | [] => ret tUnit
       | {| decl_body := None; decl_type := A |} :: Γ =>
            Γ' <- tsl_ctx ΣE Γ ;;
            A' <- tsl ΣE Γ A ;;
            ret (pack Γ' A')
       | _ => todo "tsl"
       end.


#[global]
Instance param : Translation :=
  {| tsl_id := tsl_ident ;
     tsl_tm := fun ΣE => tsl ΣE [] ;
     tsl_ty := Some (fun ΣE t => t' <- tsl ΣE [] t ;; ret (subst_app t' [ttt])) ;
     tsl_ind := todo "tsl" |}.

(* Definition toto := ((fun A (x : A) => x) (Type : Type)). *)
Definition toto := fun (f : forall A, A -> A) => f Type.
MetaRocq Run (Translate emptyTC "toto").
Check (totoᵗ : unit -> (forall A, A -> A) -> Type -> Type).


Definition FALSE := forall X, X.
MetaRocq Run (TC <- Translate emptyTC "FALSE" ;; tmPrint "toto" ;;
   Implement TC "a" (forall (A : Set) (A0 : A -> Set) (x : A), FALSE -> A0 x)).
Next Obligation.
  compute in X. apply X.
Defined.


Definition T := forall A, A -> A.
MetaRocq Run (Translate emptyTC "T").


Definition tm := ((fun A (x:A) => x) (Type -> Type) (fun x => x)).
MetaRocq Run (Translate emptyTC "tm").
