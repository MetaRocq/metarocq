From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From MetaRocq.Common Require Import
     BasicAst.
From MetaRocq.Template Require Import
     Ast Loader.
From MetaRocq.Utils Require Import
     utils.
From MetaRocq.Template.TemplateMonad Require Import
     Common Extractable.

Local Open Scope bs_scope.
Import MonadNotation.

Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p))
   (only parsing).

MetaRocq Run
    (tmBind (tmReturn 1) (fun x => tmMsg (string_of_nat x))).

MetaRocq Run
    (tmPrint <% 1 + 1 : nat %>).

Fail MetaRocq Run (tmFail "success").

MetaRocq Run
    (tmBind (tmEval cbv <% 1 + 1 %>)
            (fun t => tmPrint t)).

MetaRocq Run
    (tmBind (tmDefinition "two"%bs None <% 1 + 1 %>)
            (fun kn => tmPrint (Ast.tConst kn nil))).

MetaRocq Run
    (tmBind (tmAxiom "assume" <% nat %>)
            (fun kn => tmPrint (Ast.tConst kn nil))).


MetaRocq Run
    (tmBind (tmFreshName "blah")
            (fun i => tmBind (tmMsg i)
                          (fun _ => tmAxiom i <% bool %>))).
Print blah.
Fail Print blah0.
MetaRocq Run
    (tmBind (tmFreshName "blah0")
            (fun i => tmBind (tmMsg i)
                          (fun _ => tmAxiom i <% bool %>))).
Print blah0.

MetaRocq Test Quote nat.
MetaRocq Run
    (tmBind (tmQuoteInductive (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"))
            (fun mi => tmMsg (string_of_nat (length mi.(ind_bodies))))).

Definition nAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.

MetaRocq Run
    (tmInductive true {| mind_entry_record := None
                  ; mind_entry_finite := Finite
                  ; mind_entry_params := nil
                  ; mind_entry_inds :=
                      {| mind_entry_typename := "thing"
                       ; mind_entry_arity := <% Set %>
                       ; mind_entry_consnames := "thing1" :: "thing2" :: nil
                       ; mind_entry_lc := tProd nAnon <% bool %> (tRel 1) ::
                                          tProd nAnon <% string %> (tRel 1) :: nil
                       |} :: nil
                  ; mind_entry_universes := Monomorphic_entry ContextSet.empty
                  ; mind_entry_template := false
                  ; mind_entry_variance := None
                  ; mind_entry_private := None |}).
Print thing.

MetaRocq Run
    (tmBind tmCurrentModPath
            (fun s => tmMsg (string_of_modpath s))).

MetaRocq Test Quote plus.
MetaRocq Run (tmQuoteInductive (MPfile ["Datatypes"; "Init"; "Corelib"], "nat")).

MetaRocq Run (tmQuoteConstant (MPfile ["Nat"; "Init"; "Corelib"], "add") true).
