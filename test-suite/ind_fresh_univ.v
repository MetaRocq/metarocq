From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
Import MRMonadNotation.

(** MWE du bug sur les niveaux d'univers frais.*)

Notation nameAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.

(* Inductive Ind (T : Type) : Prop :=. *)
(* MetaRocq Run (tmQuote Ind >>= tmPrint). *)
(* Modify this based on the current file. *)
Definition ind : term :=
  tInd {| inductive_mind := (MPfile ["ind_fresh_univ";"TestSuite";"MetaRocq"], "Ind") ; inductive_ind := 0 |} [].

(* AST of [Inductive Ind (T : Type) : Prop :=.]. *)
Definition AST_Ind := {|
  ind_finite := Finite;
  ind_npars := 1;
  ind_params := [{|
    decl_name := {| binder_name := nNamed "T"; binder_relevance := Relevant |};
    decl_body := None;
    decl_type := tSort (sType fresh_universe)
  |}];
  ind_bodies := [{|
      ind_name := "Ind";
      ind_indices := [];
      ind_sort := sProp;
      ind_type :=
        tProd {| binder_name := nNamed "T"; binder_relevance := Relevant |}
          (tSort (sType fresh_universe)) (tSort sProp);
      ind_kelim := IntoPropSProp;
      ind_ctors :=[];
      ind_projs := [];
      ind_relevance := Relevant
    |}];
  ind_universes := Monomorphic_ctx;
  ind_variance := None
|}.

(* AST of [fun T : Type => Ind T]. *)
Definition AST_fun :=
  tLambda
    {| binder_name := nNamed "T"; binder_relevance := Relevant |}
    (tSort (sType fresh_universe))
    (tApp ind [tRel 0]).

Definition define_ind : TemplateMonad unit :=
 tmMkInductive true (mind_body_to_entry AST_Ind).

Definition define_fun : TemplateMonad unit :=
  tmMkDefinition "def" AST_fun.



Unset MetaRocq Strict Unquote Universe Mode.

MetaRocq Run (_ <- define_ind;;
                 define_fun).
