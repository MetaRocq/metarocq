From MetaRocq Require Import Template.All Utils.bytestring Template.Pretty.
From Stdlib Require Export List.
Open Scope bs_scope.
Import ListNotations.
Import MonadNotation.

Inductive test (X : Type) := test_T : test X -> test X.

Definition tmLocateInd (q : qualid) : TemplateMonad kername :=
  l <- tmLocate q ;;
  match l with
  | [] => tmFail ("Inductive [" ++ q ++ "] not found")
  | (IndRef ind) :: _ => tmReturn ind.(inductive_mind)
  | _ :: _ => tmFail ("[" ++ q ++ "] not an inductive")
  end.

MetaRocq Run (tmLocateInd "Datatypes.unit" >>= tmDefinition "q_unit").
MetaRocq Run (tmLocateInd "test" >>= tmDefinition "q_test").

Definition nAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition nNamed s := {| binder_name := nNamed s; binder_relevance := Relevant |}.

Definition T :=
tFix
  [mkdef term (nNamed "f") (tProd (nNamed "x") (tApp (tInd (mkInd q_test 0) []) [tInd (mkInd q_unit 0) []]) (tInd (mkInd q_unit 0) []))
     (tLambda (nNamed "x") (tApp (tInd (mkInd q_test 0) []) [tRel 0])
        (tCase {|ci_ind := mkInd q_test 0; ci_npar := 1; ci_relevance := Relevant |}
          {| pparams := [tInd (mkInd q_unit 0) []]; puinst := [];
             pcontext := [nNamed "X"];
             preturn := (tInd (mkInd q_unit 0) []) |}
           (tRel 0)
           [{| bcontext := [nNamed "x0"]; bbody := (tApp (tRel 2) [tRel 0]) |}]))
     0] 0.

(* MetaRocq Run (tmEval cbv (print_term (empty_ext []) [] true T) >>= tmPrint).   *)
Fail MetaRocq Run (tmUnquote T >>= tmPrint).

Fail Definition bla := (existT_typed_term (test unit -> unit) (fix f (x : test f) : unit := match x with
                                                                              | test_T _ x0 => f x0
                                                                              end)).
Fail MetaRocq Run (tmUnquote T >>= tmDefinition "fails").
