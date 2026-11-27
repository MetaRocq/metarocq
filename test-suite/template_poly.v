(** Quoting and unquoting of template polymorphic inductive types.

    They are quoted as universe polymorphic inductive types over their template
    universes, and their occurrences get the universe instance Rocq infers:
    the universes of the sorts of the arguments for the template parameters,
    and the default universes for the missing ones. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

Import MonadNotation.
Open Scope bs_scope.

Universe big.

(** The universe instance of an inductive type or constructor applied to
    arguments, or of a pattern matching. *)
Definition inst_of (t : term) : option Instance.t :=
  match t with
  | tApp (tInd _ u) _ | tApp (tConstruct _ _ u) _
  | tInd _ u | tConstruct _ _ u => Some u
  | tLambda _ _ (tApp (tInd _ u) _) => Some u
  | tLambda _ _ (tCase _ p _ _) => Some p.(puinst)
  | _ => None
  end.

MetaRocq Quote Definition q_big := Type@{big}.
Definition big_univ :=
  match q_big with tSort (sType u) => u | _ => Universe.zero end.

Definition set := Universe.of_level Level.lzero.

(** Occurrences of template polymorphic inductive types. *)

MetaRocq Quote Definition q_list_nat := (list nat).
Check eq_refl : inst_of q_list_nat == Some [set] = true.

MetaRocq Quote Definition q_list_big := (list Type@{big}).
Check eq_refl : inst_of q_list_big == Some [Universe.succ big_univ] = true.

MetaRocq Quote Definition q_prod := (prod nat Type@{big}).
Check eq_refl : inst_of q_prod == Some [set; Universe.succ big_univ] = true.

(* Without arguments, the default universes. *)
MetaRocq Quote Definition q_list := list.
Check eq_refl : option_map (@List.length _) (inst_of q_list) = Some 1.
Check eq_refl : inst_of q_list == Some [set] = false.

(** Constructors and pattern matchings. *)

MetaRocq Quote Definition q_nil_big := (@nil Type@{big}).
Check eq_refl : inst_of q_nil_big == Some [Universe.succ big_univ] = true.

MetaRocq Quote Definition q_cons_nat := (cons 0 nil).
Check eq_refl : inst_of q_cons_nat == Some [set] = true.

MetaRocq Quote Definition q_match :=
  (fun x : list Type@{big} => match x with nil => 0 | cons _ _ => 1 end).
Check eq_refl : inst_of q_match == Some [Universe.succ big_univ] = true.

(** Arguments in Prop or SProp: MetaRocq has no sort qualities, so their
    universe is Set. Hence [prod True True] lives in Set in MetaRocq, while
    it lives in Prop in Rocq. *)

MetaRocq Quote Definition q_prod_prop := (prod True True).
Check eq_refl : inst_of q_prod_prop == Some [set; set] = true.

MetaRocq Quote Definition q_prod_prop_nat := (prod True nat).
Check eq_refl : inst_of q_prod_prop_nat == Some [set; set] = true.

MetaRocq Quote Definition q_list_prop := (list True).
Check eq_refl : inst_of q_list_prop == Some [set] = true.

(* Under binders, the universes of the sorts of the variables. *)
MetaRocq Quote Definition q_prod_var := (fun A : Prop => prod A A).
Check eq_refl : inst_of q_prod_var == Some [set; set] = true.

MetaRocq Quote Definition q_list_var := (fun A : Type@{big} => list A).
Check eq_refl : inst_of q_list_var == Some [big_univ] = true.

(** Declarations: universe polymorphic over the template universes, with
    irrelevant variances. *)

MetaRocq Quote Recursively Definition p_list := (list nat).

Definition list_decl :=
  match lookup_env p_list.1 (MPfile ["Datatypes"; "Init"; "Corelib"], "list") with
  | Some (InductiveDecl mdecl) => Some mdecl
  | _ => None
  end.

Check eq_refl :
  option_map (fun m => match m.(ind_universes) with
    | Polymorphic_ctx (names, _) => #|names|
    | Monomorphic_ctx => 0
    end) list_decl = Some 1.

Check eq_refl :
  option_map ind_variance list_decl = Some (Some [Variance.Irrelevant]).

(* The parameter is a type in the bound template universe. *)
Check eq_refl :
  option_map (fun m => List.map (fun d => match d.(decl_type) with
    | tSort (sType u) => u == Universe.of_level (Level.lvar 0)
    | _ => false
    end) m.(ind_params)) list_decl = Some [true].

(** Unquoting drops the inferred instances: Rocq gives template polymorphic
    inductive types the empty instance. *)

MetaRocq Unquote Definition u_list_big := q_list_big.
Check eq_refl : u_list_big = list Type@{big}.

MetaRocq Unquote Definition u_nil_big := q_nil_big.
Check eq_refl : u_nil_big = @nil Type@{big}.

MetaRocq Unquote Definition u_match := q_match.
Check eq_refl : u_match =
  fun x : list Type@{big} => match x with nil => 0 | cons _ _ => 1 end.

MetaRocq Run (t <- tmQuote (option Type@{big}) ;;
              t' <- tmUnquoteTyped Type t ;;
              tmDefinition "u_option_big" t').
Check eq_refl : u_option_big = option Type@{big}.
