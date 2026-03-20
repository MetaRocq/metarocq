From Stdlib Require Import Lists.List.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Template Require Import Ast Loader TemplateMonad.Extractable.
Import TemplateMonad.Extractable.
From MetaRocq.Template Require Import AstUtils Ast.

Open Scope bs_scope.

Abbreviation TemplateMonad := TM.
Fixpoint mconcat (ls : list (TemplateMonad unit)) : TM unit :=
  match ls with
  | nil => tmReturn tt
  | m :: ms => tmBind m (fun _ => mconcat ms)
  end.

Fixpoint print_all_kns (t : Ast.term) : TM unit :=
  match t with
  | tEvar _ ls =>
    mconcat (List.map print_all_kns ls)
  | tCast a _ b
  | tProd _ a b
  | tLambda _ a b =>
    tmBind (print_all_kns a) (fun _ => print_all_kns b)
  | tApp a b =>
    tmBind (print_all_kns a) (fun _ => mconcat (List.map print_all_kns b))
  | tLetIn _ a b c =>
    tmBind (print_all_kns a) (fun _ => tmBind (print_all_kns b) (fun _ => print_all_kns c))
  | tConst c _ => tmMsg (string_of_kername c)
  | tInd i _ => tmMsg (string_of_kername i.(inductive_mind))
  | tConstruct i _ _ => tmMsg (string_of_kername i.(inductive_mind))
  | tProj p b =>
    tmBind (tmMsg (string_of_kername p.(proj_ind).(inductive_mind))) (fun _ => print_all_kns b)
  | _ => tmReturn tt
  end.

Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p))
  (only parsing).


(* Definition gr_to_kername (gr : global_reference) : kername := *)
(*   match gr with *)
(*   | ConstRef kn => kn *)
(*   | IndRef ind => ind.(inductive_mind) *)
(*   | ConstructRef ind _ => ind.(inductive_mind) *)
(*   end. *)

Definition tmResolve (nm : String.t) : TM (option kername) :=
  tmBind (tmLocate nm)
         (fun gr =>
            match gr with
            | (ConstRef kn) :: _ => tmReturn (Some kn)
            | (IndRef ind) :: _ => tmReturn (Some ind.(inductive_mind))
            | (ConstructRef ind _) :: _ => tmReturn (Some ind.(inductive_mind))
            | _ => tmReturn None
            end).


(* ^^ Everything above here is generic *)

From MetaRocq Require Import ExtractedPluginDemo.Lens.

Set Primitive Projections.
Set Universe Polymorphism.

Record Info  :=
{ type : ident
; ctor : ident
; fields : list projection_body
}.

Fixpoint countTo (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S m => countTo m ++ (m :: nil)
  end.

Definition prepend (ls : String.t) (i : ident) : ident :=
  ls ++ i.

Definition cBuild_Lens := <% Build_Lens %>.

From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.


(* check to see if Var 0 is referenced in any of the terms *)
Definition mentions (v : nat) (ls : list projection_body) : bool :=
  false.

Definition nAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition nNamed s := {| binder_name := nNamed s; binder_relevance := Relevant |}.

Definition mkLens (At : term) (fields : list projection_body) (i : nat)
: option (ident * term) :=
  match At with
  | tInd ind args =>
    let ctor := tConstruct ind 0 args in
    match nth_error fields i with
    | None => None
    | Some {| proj_name := name; proj_type := Bt |} =>
      if mentions 1 (skipn (S i) fields)
      then None
      else
        let p (x : nat) : projection := {| proj_ind := ind; proj_npars := 0; proj_arg := x |} in
        let get_body := tProj (p i) (tRel 0) in
        let f x :=
            let this := tProj (p x) (tRel 0) in
            if PeanoNat.Nat.eqb x i
            then tApp (tRel 1) (this :: nil)
            else this
        in
        let update_body :=
            tApp ctor (map f (countTo (List.length fields)))
        in
        Some ( prepend "_" name
             , tApp cBuild_Lens
                    (At :: At :: Bt :: Bt ::
                        tLambda nAnon At get_body ::
                        tLambda nAnon (tProd nAnon Bt Bt) (tLambda nAnon At update_body) ::
                        nil))
    end
  | _ => None
  end.

Definition getFields (mi : mutual_inductive_body)
: option Info :=
  match mi.(ind_bodies) with
  | oib :: nil =>
    match oib.(ind_ctors) with
    | ctor :: nil =>
      Some {| type := oib.(ind_name)
            ; ctor := ctor.(cstr_name)
            ; fields := oib.(ind_projs)
           |}
    | _ => None
    end
  | _ => None
  end.

(* baseName should not contain any paths. For example, if the full name
is A.B.C#D#E#F, baseName should be F. Also, by import ordering,
ensure that F resolves to  A.B.C#D#E#F. Use Locate to check this.

If the definition of F refers to any other inductive, they should not
be in the current section(s).
 *)

Definition opBind {A B} (a: option A) (f: A -> option B) : option B :=
  match a with
  | Some a => f a
  | None  => None
  end.

Definition genLensN (baseName : String.t) : TM unit :=
  tmBind (tmLocate baseName) (fun gr =>
    match gr with
    | (IndRef kn) :: _ =>
      let name := kn.(inductive_mind) in
      let ty := Ast.tInd
        {| Kernames.inductive_mind := name
         ; Kernames.inductive_ind := 0 (* TODO: fix for mutual records *) |} List.nil in
      tmBind (tmQuoteInductive name) (fun ind =>
          match getFields ind with
          | Some info =>
            let gen i :=
                match mkLens ty info.(fields) i return TemplateMonad unit with
                | None => tmFail "failed to build lens"
                | Some x =>
                  tmBind (tmEval Common.cbv (snd x)) (fun d =>
                  tmBind (tmDefinition (fst x) None d) (fun _ =>
                  tmReturn tt))
                end
            in
            mconcat (map gen (countTo (List.length info.(fields))))
          | None => tmFail ("failed to get inductive info but quote succeeded")
          end)
    | _ => tmFail "not an inductive"
    end).


Definition tmQuoteConstantR (nm : String.t) (bypass : bool) : TM _ :=
  tmBind (tmLocate nm)
         (fun gr =>
            match gr with
            | (ConstRef kn) :: _ =>
              tmBind (tmQuoteConstant kn bypass)
                     (fun x => tmReturn (Some x))
            | _ => tmReturn None
            end).

Definition lookupPrint (baseName : String.t) : TM unit :=
  tmBind (tmQuoteConstantR baseName true)
         (fun b =>
            match b with
            | None => tmFail "not a constant"
            | Some b =>
              match b.(cst_body) with
              | None => tmReturn tt
              | Some bd => tmPrint bd
              end
            end).

Definition x := <% 0 %>.

Definition lookup baseName : TM unit :=
  tmBind (tmQuoteConstant baseName true)
         (fun b => tmReturn tt).

Definition genLensNInst  : TM unit := genLensN "Point".


Definition showoffOld : TM unit :=
  tmBind (tmMsg "showing off tmDefn" )
         (fun _ =>
            tmBind (tmDefinition "zeroE" None x)
                   (fun _ => tmReturn tt)).

Definition showoff : TM unit := genLensNInst.
