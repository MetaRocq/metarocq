
(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPretty.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

Local Set Keyed Unification.
Set Equations Transparent.

Inductive ConversionError :=
| NotFoundConstants (c1 c2 : kername)

| NotFoundConstant (c : kername)

| LambdaNotConvertibleTypes
    (Γ1 : context) (na : aname) (A1 t1 : term)
    (Γ2 : context) (na' : aname) (A2 t2 : term)
    (e : ConversionError)

| LambdaNotConvertibleAnn
    (Γ1 : context) (na : aname) (A1 t1 : term)
    (Γ2 : context) (na' : aname) (A2 t2 : term)

| ProdNotConvertibleDomains
    (Γ1 : context) (na : aname) (A1 B1 : term)
    (Γ2 : context) (na' : aname) (A2 B2 : term)
    (e : ConversionError)

| ProdNotConvertibleAnn
    (Γ1 : context) (na : aname) (A1 B1 : term)
    (Γ2 : context) (na' : aname) (A2 B2 : term)

| ContextNotConvertibleAnn
    (Γ : context) (decl : context_decl)
    (Γ' : context) (decl' : context_decl)
| ContextNotConvertibleType
    (Γ : context) (decl : context_decl)
    (Γ' : context) (decl' : context_decl)
| ContextNotConvertibleBody
    (Γ : context) (decl : context_decl)
    (Γ' : context) (decl' : context_decl)
| ContextNotConvertibleLength

| CaseOnDifferentInd
    (Γ1 : context)
    (ci : case_info) (p : predicate term) (c : term) (brs : list (branch term))
    (Γ2 : context)
    (ci' : case_info) (p' : predicate term) (c' : term) (brs' : list (branch term))

| CasePredParamsUnequalLength
    (Γ1 : context)
    (ci : case_info) (p : predicate term) (c : term) (brs : list (branch term))
    (Γ2 : context)
    (ci' : case_info) (p' : predicate term) (c' : term) (brs' : list (branch term))

| CasePredUnequalUniverseInstances
    (Γ1 : context)
    (ci : case_info) (p : predicate term) (c : term) (brs : list (branch term))
    (Γ2 : context)
    (ci' : case_info) (p' : predicate term) (c' : term) (brs' : list (branch term))

| DistinctStuckProj
    (Γ : context) (p : projection) (c : term)
    (Γ' : context) (p' : projection) (c' : term)

| CannotUnfoldFix
    (Γ : context) (mfix : mfixpoint term) (idx : nat)
    (Γ' : context) (mfix' : mfixpoint term) (idx' : nat)

| FixRargMismatch (idx : nat)
    (Γ : context) (u : def term) (mfix1 mfix2 : mfixpoint term)
    (Γ' : context) (v : def term) (mfix1' mfix2' : mfixpoint term)

| FixMfixMismatch (idx : nat)
    (Γ : context) (mfix : mfixpoint term)
    (Γ' : context) (mfix' : mfixpoint term)

| DistinctCoFix
    (Γ : context) (mfix : mfixpoint term) (idx : nat)
    (Γ' : context) (mfix' : mfixpoint term) (idx' : nat)

| CoFixRargMismatch (idx : nat)
    (Γ : context) (u : def term) (mfix1 mfix2 : mfixpoint term)
    (Γ' : context) (v : def term) (mfix1' mfix2' : mfixpoint term)

| CoFixMfixMismatch (idx : nat)
    (Γ : context) (mfix : mfixpoint term)
    (Γ' : context) (mfix' : mfixpoint term)

| DistinctPrimTags
  (Γ : context) (p : prim_val)
  (Γ' : context) (p' : prim_val)

| DistinctPrimValues
  (Γ : context) (p : prim_val)
  (Γ' : context) (p' : prim_val)

| ArrayNotConvertibleLevels
  (Γ : context) (a : array_model term) (Γ' : context) (a' : array_model term)

| ArrayValuesNotSameLength
  (Γ : context) (a : array_model term) (Γ' : context) (a' : array_model term)

| ArrayNotConvertibleValues
  (Γ : context) (a : array_model term) (Γ' : context) (a' : array_model term)
  (e : ConversionError)

| ArrayNotConvertibleDefault
  (Γ : context) (a : array_model term) (Γ' : context) (a' : array_model term)
  (e : ConversionError)

| ArrayNotConvertibleTypes
  (Γ : context) (a : array_model term) (Γ' : context) (a' : array_model term)
  (e : ConversionError)

| StackHeadError
    (leq : conv_pb)
    (Γ1 : context)
    (t1 : term) (args1 : list term) (u1 : term) (l1 : list term)
    (Γ2 : context)
    (t2 : term) (u2 : term) (l2 : list term)
    (e : ConversionError)

| StackTailError (leq : conv_pb)
    (Γ1 : context)
    (t1 : term) (args1 : list term) (u1 : term) (l1 : list term)
    (Γ2 : context)
    (t2 : term) (u2 : term) (l2 : list term)
    (e : ConversionError)

| StackMismatch
    (Γ1 : context) (t1 : term) (args1 l1 : list term)
    (Γ2 : context) (t2 : term) (l2 : list term)

| HeadMismatch
    (leq : conv_pb)
    (Γ1 : context) (t1 : term)
    (Γ2 : context) (t2 : term).

Inductive type_error :=
| UnboundRel (n : nat)
| UnboundVar (id : string)
| UnboundEvar (ev : nat)
| UndeclaredConstant (c : kername)
| UndeclaredInductive (c : inductive)
| UndeclaredConstructor (c : inductive) (i : nat)
| NotCumulSmaller {abstract_structure} (le : bool)
  (G : abstract_structure) (Γ : context) (t u t' u' : term) (e : ConversionError)
| NotConvertible {abstract_structure}
  (G : abstract_structure)
  (Γ : context) (t u : term)
| NotASort (t : term)
| NotAProduct (t t' : term)
| NotAnInductive (t : term)
| NotAnArity (t : term)
| IllFormedFix (m : mfixpoint term) (i : nat)
| UnsatisfiedConstraints (c : UnivConstraintSet.t)
| Msg (s : string).
Derive NoConfusion for type_error.

Definition print_level := string_of_level.

Definition string_of_Z z :=
  if (z <=? 0)%Z then "-" ^ string_of_nat (Z.to_nat (- z)) else string_of_nat (Z.to_nat z).

Definition print_edge '(l1, n, l2)
  := "(" ^ print_level l1 ^ ", " ^ string_of_Z n ^ ", "
         ^ print_level l2 ^ ")".

Definition print_universes_graph (G : universes_graph) :=
  let levels := LevelSet.elements G.1.1 in
  let edges := wGraph.EdgeSet.elements G.1.2 in
  string_of_list print_level levels
  ^ nl ^ string_of_list print_edge edges.

Definition string_of_conv_pb (c : conv_pb) : string :=
  match c with
  | Conv => "conversion"
  | Cumul => "cumulativity"
  end.

Definition print_term Σ Γ t :=
  let ids := fresh_names Σ [] Γ in
  print_term Σ true ids true false t.

Definition print_context_decl Σ Γ (decl : context_decl) : string :=
  fresh_name Σ [] (binder_name (decl_name decl)) (Some (decl_type decl))
  ^ " : "
  ^ print_term Σ Γ (decl_type decl)
  ^ match decl_body decl with
    | Some body => " := " ^ print_term Σ Γ body
    | None => ""
    end.

Fixpoint string_of_conv_error Σ (e : ConversionError) : string :=
  match e with
  | NotFoundConstants c1 c2 =>
      "Both constants " ^ string_of_kername c1 ^ " and " ^ string_of_kername c2 ^
      " are not found in the environment."
  | NotFoundConstant c =>
      "Constant " ^ string_of_kername c ^
      " common in both terms is not found in the environment."
  | LambdaNotConvertibleAnn Γ1 na A1 t1 Γ2 na' A2 t2 =>
      "When comparing" ^ nl ^ print_term Σ Γ1 (tLambda na A1 t1) ^
      nl ^ "and" ^ nl ^ print_term Σ Γ2 (tLambda na' A2 t2) ^
      nl ^ "binding annotations are not convertible" ^ nl
  | LambdaNotConvertibleTypes Γ1 na A1 t1 Γ2 na' A2 t2 e =>
      "When comparing" ^ nl ^ print_term Σ Γ1 (tLambda na A1 t1) ^
      nl ^ "and" ^ nl ^ print_term Σ Γ2 (tLambda na' A2 t2) ^
      nl ^ "types are not convertible:" ^ nl ^
      string_of_conv_error Σ e
  | ProdNotConvertibleAnn Γ1 na A1 B1 Γ2 na' A2 B2 =>
      "When comparing" ^ nl ^ print_term Σ Γ1 (tProd na A1 B1) ^
      nl ^ "and" ^ nl ^ print_term Σ Γ2 (tProd na' A2 B2) ^
      nl ^ "binding annotations are not convertible:" ^ nl
  | ProdNotConvertibleDomains Γ1 na A1 B1 Γ2 na' A2 B2 e =>
      "When comparing" ^ nl ^ print_term Σ Γ1 (tProd na A1 B1) ^
      nl ^ "and" ^ nl ^ print_term Σ Γ2 (tProd na' A2 B2) ^
      nl ^ "domains are not convertible:" ^ nl ^
      string_of_conv_error Σ e
  | CaseOnDifferentInd Γ ci p c brs Γ' ci' p' c' brs' =>
      "The two stuck pattern-matches" ^ nl ^
      print_term Σ Γ (tCase ci p c brs) ^
      nl ^ "and" ^ nl ^ print_term Σ Γ' (tCase ci' p' c' brs') ^
      nl ^ "are done on distinct inductive types."
  | CasePredParamsUnequalLength Γ ci p c brs Γ' ci' p' c' brs' =>
      "The predicates of the two stuck pattern-matches" ^ nl ^
      print_term Σ Γ (tCase ci p c brs) ^
      nl ^ "and" ^ nl ^ print_term Σ Γ' (tCase ci' p' c' brs') ^
      nl ^ "have an unequal number of parameters."
  | CasePredUnequalUniverseInstances Γ ci p c brs Γ' ci' p' c' brs' =>
      "The predicates of the two stuck pattern-matches" ^ nl ^
      print_term Σ Γ (tCase ci p c brs) ^
      nl ^ "and" ^ nl ^ print_term Σ Γ' (tCase ci' p' c' brs') ^
      nl ^ "have unequal universe instances."
  | ContextNotConvertibleAnn Γ decl Γ' decl' =>
      "When comparing the declarations" ^ nl ^
      print_context_decl Σ Γ decl ^ nl ^
      "and" ^ nl ^
      print_context_decl Σ Γ' decl' ^ nl ^
      "the binder annotations are not equal"
  | ContextNotConvertibleType Γ decl Γ' decl' =>
      "When comparing the declarations" ^ nl ^
      print_context_decl Σ Γ decl ^ nl ^
      "and" ^ nl ^
      print_context_decl Σ Γ' decl' ^ nl ^
      "the types are not convertible"
  | ContextNotConvertibleBody Γ decl Γ' decl' =>
      "When comparing the declarations" ^ nl ^
      print_context_decl Σ Γ decl ^ nl ^
      "and" ^ nl ^
      print_context_decl Σ Γ' decl' ^ nl ^
      "the bodies are not convertible"
  | ContextNotConvertibleLength => "The contexts have unequal length"

  | DistinctStuckProj Γ p c Γ' p' c' =>
      "The two stuck projections" ^ nl ^
      print_term Σ Γ (tProj p c) ^
      nl ^ "and" ^ nl ^
      print_term Σ Γ' (tProj p' c') ^
      nl ^ "are syntactically different."
  | CannotUnfoldFix Γ mfix idx Γ' mfix' idx' =>
      "The two fixed-points" ^ nl ^
      print_term Σ Γ (tFix mfix idx) ^
      nl ^ "and" ^ nl ^ print_term Σ Γ' (tFix mfix' idx') ^
      nl ^ "correspond to syntactically distinct terms that can't be unfolded."
  | FixRargMismatch idx Γ u mfix1 mfix2 Γ' v mfix1' mfix2' =>
      "The two fixed-points" ^ nl ^
      print_term Σ Γ (tFix (mfix1 ++ u :: mfix2) idx) ^
      nl ^ "and" ^ nl ^ print_term Σ Γ' (tFix (mfix1' ++ v :: mfix2') idx) ^
      nl ^ "have a mismatch in the function number " ^ string_of_nat #|mfix1| ^
      ": arguments " ^ string_of_nat u.(rarg) ^
      " and " ^ string_of_nat v.(rarg) ^ "are different."
  | FixMfixMismatch idx Γ mfix Γ' mfix' =>
      "The two fixed-points" ^ nl ^
      print_term Σ Γ (tFix mfix idx) ^
      nl ^ "and" ^ nl ^
      print_term Σ Γ' (tFix mfix' idx) ^
      nl ^ "have a different number of mutually defined functions."
  | DistinctCoFix Γ mfix idx Γ' mfix' idx' =>
      "The two cofixed-points" ^ nl ^
      print_term Σ Γ (tCoFix mfix idx) ^
      nl ^ "and" ^ nl ^ print_term Σ Γ' (tCoFix mfix' idx') ^
      nl ^ "correspond to syntactically distinct terms."
  | CoFixRargMismatch idx Γ u mfix1 mfix2 Γ' v mfix1' mfix2' =>
      "The two co-fixed-points" ^ nl ^
      print_term Σ Γ (tCoFix (mfix1 ++ u :: mfix2) idx) ^
      nl ^ "and" ^ nl ^ print_term Σ Γ' (tCoFix (mfix1' ++ v :: mfix2') idx) ^
      nl ^ "have a mismatch in the function number " ^ string_of_nat #|mfix1| ^
      ": arguments " ^ string_of_nat u.(rarg) ^
      " and " ^ string_of_nat v.(rarg) ^ "are different."
  | CoFixMfixMismatch idx Γ mfix Γ' mfix' =>
      "The two co-fixed-points" ^ nl ^
      print_term Σ Γ (tCoFix mfix idx) ^
      nl ^ "and" ^ nl ^
      print_term Σ Γ' (tCoFix mfix' idx) ^
      nl ^ "have a different number of mutually defined functions."
  | ArrayValuesNotSameLength Γ a Γ' a' =>
      "The two arrays " ^ nl ^
      print_term Σ Γ (tPrim (primArray; primArrayModel a)) ^
      nl ^ "and" ^ nl ^
      print_term Σ Γ (tPrim (primArray; primArrayModel a')) ^
      nl ^ " have different length"
  | ArrayNotConvertibleValues Γ a Γ' a' e =>
      "The two arrays " ^ nl ^
      print_term Σ Γ (tPrim (primArray; primArrayModel a)) ^
      nl ^ "and" ^ nl ^
      print_term Σ Γ (tPrim (primArray; primArrayModel a')) ^
      nl ^ " have non-convertible values: " ^
      nl ^ string_of_conv_error Σ e
  | ArrayNotConvertibleLevels Γ a Γ' a' =>
      "The two arrays " ^ nl ^
      print_term Σ Γ (tPrim (primArray; primArrayModel a)) ^
      nl ^ "and" ^ nl ^
      print_term Σ Γ (tPrim (primArray; primArrayModel a')) ^
      nl ^ " have non-convertible universe levels"
  | ArrayNotConvertibleTypes Γ a Γ' a' e =>
      "The two arrays " ^ nl ^
      print_term Σ Γ (tPrim (primArray; primArrayModel a)) ^
      nl ^ "and" ^ nl ^
      print_term Σ Γ (tPrim (primArray; primArrayModel a')) ^
      nl ^ " have non-convertible types: " ^
      nl ^ string_of_conv_error Σ e
  | ArrayNotConvertibleDefault Γ a Γ' a' e =>
      "The two arrays " ^ nl ^
      print_term Σ Γ (tPrim (primArray; primArrayModel a)) ^
      nl ^ "and" ^ nl ^
      print_term Σ Γ (tPrim (primArray; primArrayModel a')) ^
      nl ^ " have non-convertible default values: " ^
      nl ^ string_of_conv_error Σ e
  | DistinctPrimTags Γ p Γ' p' =>
      "The two primitive values " ^ nl ^
      print_term Σ Γ (tPrim p) ^
      nl ^ "and" ^ nl ^
      print_term Σ Γ (tPrim p') ^
      nl ^ " have distinct tags"
  | DistinctPrimValues Γ p Γ' p' =>
      "The two primitive values " ^ nl ^
      print_term Σ Γ (tPrim p) ^
      nl ^ "and" ^ nl ^
      print_term Σ Γ (tPrim p') ^
      nl ^ " have distinct values"
  | StackHeadError leq Γ1 t1 args1 u1 l1 Γ2 t2 u2 l2 e =>
      "TODO stackheaderror" ^ nl ^
      string_of_conv_error Σ e
  | StackTailError leq Γ1 t1 args1 u1 l1 Γ2 t2 u2 l2 e =>
      "TODO stacktailerror" ^ nl ^
      string_of_conv_error Σ e
  | StackMismatch Γ1 t1 args1 l1 Γ2 t2 l2 =>
      "Convertible terms" ^ nl ^
      print_term Σ Γ1 t1 ^
      nl ^ "and" ^ nl ^ print_term Σ Γ2 t2 ^
      "are convertible/convertible (TODO) but applied to a different number" ^
      " of arguments."
  | HeadMismatch leq Γ1 t1 Γ2 t2 =>
      "Terms" ^ nl ^
      print_term Σ Γ1 t1 ^
      nl ^ "and" ^ nl ^ print_term Σ Γ2 t2 ^
      nl ^ "do not have the same head when comparing for " ^
      string_of_conv_pb leq
  end.

Definition string_of_type_error Σ (e : type_error) : string :=
  match e with
  | UnboundRel n => "Unbound rel " ^ string_of_nat n
  | UnboundVar id => "Unbound var " ^ id
  | UnboundEvar ev => "Unbound evar " ^ string_of_nat ev
  | UndeclaredConstant c => "Undeclared constant " ^ string_of_kername c
  | UndeclaredInductive c => "Undeclared inductive " ^ string_of_kername (inductive_mind c)
  | UndeclaredConstructor c i => "Undeclared inductive " ^ string_of_kername (inductive_mind c)
  | NotCumulSmaller _ le G Γ t u t' u' e => "Types are not " ^
      (if le then "<= for cumulativity:" ^ nl
       else "convertible:" ^ nl) ^
      print_term Σ Γ t ^ nl ^ "and:" ^ nl ^ print_term Σ Γ u ^
      nl ^ "after reduction:" ^ nl ^
      print_term Σ Γ t' ^ nl ^ "and:" ^ nl ^ print_term Σ Γ u' ^
      nl ^ "error:" ^ nl ^ string_of_conv_error Σ e ^
      (* nl ^ "in universe graph:" ^ nl ^ print_universes_graph G ^ nl ^ *)
      " and context: " ^ nl ^ print_context Σ [] Γ
  | NotConvertible _ G Γ t u => "Terms are not convertible:" ^ nl ^
      print_term Σ Γ t ^ nl ^ "and:" ^ nl ^ print_term Σ Γ u ^
      (* nl ^ "in universe graph:" ^ nl ^ print_universes_graph G ^ nl ^ *)
      " and context: " ^ nl ^ print_context Σ [] Γ
  | NotASort t => "Not a sort: " ^ print_term Σ [] t
  | NotAProduct t t' => "Not a product" ^ print_term Σ [] t ^ nl ^
    "(after reducing to " ^ print_term Σ [] t'
  | NotAnArity t => print_term Σ [] t ^ " is not an arity"
  | NotAnInductive t => "Not an inductive: " ^ print_term Σ [] t
  | IllFormedFix m i => "Ill-formed recursive definition"
  | UnsatisfiedConstraints c => "Unsatisfied constraints"
  | Msg s => "Msg: " ^ s
  end.

Inductive typing_result (A : Type) :=
| Checked (a : A)
| TypeError (t : type_error).
Global Arguments Checked {A} a.
Global Arguments TypeError {A} t.
Inductive typing_result_comp (A : Type) :=
| Checked_comp (a : A)
| TypeError_comp (t : type_error) (a : A -> False).
Global Arguments Checked_comp {A} a.
Global Arguments TypeError_comp {A} t a.

Coercion typing_error_forget {A : Type} (t : typing_result_comp A) :
  typing_result A :=
  match t with
    | Checked_comp a => Checked a
    | TypeError_comp e a => TypeError e
  end.

#[global]
 Instance typing_monad : Monad typing_result :=
  {| ret A a := Checked a ;
     bind A B m f :=
       match m with
       | Checked a => f a
       | TypeError t => TypeError t
       end
  |}.

#[global]
Instance monad_exc : MonadExc type_error typing_result :=
  { raise A e := TypeError e;
    catch A m f :=
      match m with
      | Checked a => m
      | TypeError t => f t
      end
  }.

Inductive env_error :=
| IllFormedDecl (e : string) (e : type_error)
| AlreadyDeclared (id : string).

Definition string_of_env_error Σ (e : env_error) :=
  match e with
  | IllFormedDecl decl_name typ_error =>
      "Type error on " ^ decl_name ^ " " ^ string_of_type_error Σ typ_error
  | AlreadyDeclared decl_name =>
      "Name is already declared in environment " ^ decl_name
  end.

Section EnvCheck.

  Context (abstract_structure : Type).


Inductive EnvCheck (A : Type) :=
| CorrectDecl (a : A)
| EnvError (Σ : abstract_structure) (e : env_error).
Global Arguments EnvError {A} Σ e.
Global Arguments CorrectDecl {A} a.

Global Instance envcheck_monad : Monad EnvCheck :=
  {| ret A a := CorrectDecl a ;
      bind A B m f :=
        match m with
        | CorrectDecl a => f a
        | EnvError g e => EnvError g e
        end
  |}.

Global Instance envcheck_monad_exc
  : MonadExc (abstract_structure * env_error) EnvCheck :=
  { raise A '(g, e) := EnvError g e;
    catch A m f :=
      match m with
      | CorrectDecl a => m
      | EnvError g t => f (g, t)
      end
  }.

Definition wrap_error {A} Σ (id : string) (check : typing_result A) : EnvCheck A :=
  match check with
  | Checked a => CorrectDecl a
  | TypeError e => EnvError Σ (IllFormedDecl id e)
  end.

Lemma monad_map_All2 (X Y : Type) (f : X -> typing_result Y) (l1 : list X) (a1 : list Y) :
  monad_map f l1 = ret a1 -> All2 (fun a b => f a = ret b) l1 a1.
Proof using Type.
  induction l1 in a1 |- *; cbn; intros.
  - inv H. econstructor.
  - revert H.
    case_eq (f a). all: try discriminate. intros b eb.
    simpl.
    case_eq (monad_map f l1). all: try discriminate. intros l' el.
    simpl. intro h. inv h.
    econstructor ; eauto.
Qed.

Lemma monad_map_Forall2 (X Y : Type) (f : X -> typing_result Y) (l1 : list X) (a1 : list Y) :
  monad_map f l1 = Checked a1 -> Forall2 (fun a b => f a = Checked b) l1 a1.
Proof using Type.
  intros. now eapply All2_Forall2, monad_map_All2.
Qed.

Lemma monad_length_map X Y (f : X -> typing_result Y) (l1  : list X) a :
  monad_map f l1 = Checked a -> #|l1| = #|a|.
Proof using Type.
  revert a; induction l1; cbn; intros.
  - invs H. cbn. congruence.
  - revert H.
    case_eq (f a). all: try discriminate. intros x' ex.
    simpl.
    case_eq (monad_map f l1). all: try discriminate. intros l' el.
    simpl. intro h. inv h.
    simpl. f_equal. eauto.
Qed.

Lemma monad_map_app X Y (f : X -> typing_result Y) (l1 l2 : list X) a1 a2 :
  monad_map f l1 = Checked a1 -> monad_map f l2 = Checked a2 -> monad_map f (l1 ++ l2) = Checked (a1 ++ a2).
Proof using Type.
  revert a1. induction l1; intros.
  - cbn in *. invs H. eauto.
  - cbn in *.
    revert H.
    case_eq (f a). all: try discriminate. intros b eb.
    simpl.
    case_eq (monad_map f l1). all: try discriminate. intros l' el.
    simpl. intro h. inv h.
    rewrite (IHl1 _ el H0). simpl. reflexivity.
Qed.

Lemma monad_map_app_invs X Y (f : X -> typing_result Y) (l1 l2 : list X) a :
  monad_map f (l1 ++ l2) = Checked a -> exists a1 a2, monad_map f l1 = Checked a1 /\
  monad_map f l2 = Checked a2 /\ (a = a1 ++ a2).
Proof using Type.
  intros. revert a H. induction l1; intros.
  - cbn in *. eauto.
  - cbn in *.
    revert H.
    case_eq (f a). all: try discriminate. intros b eb.
    simpl.
    case_eq (monad_map f (l1 ++ l2)). all: try discriminate. intros l' el.
    simpl. intro h. inv h.
    destruct (IHl1 _ el) as (? & ? & ? & ? & ->).
    eexists _,_. rewrite -> H, H0. intuition eauto.
Qed.

End EnvCheck.
