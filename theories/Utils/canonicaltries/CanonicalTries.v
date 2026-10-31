(** * The extensional binary tries based on a canonical representation *)

(* Authors: Andrew W. Appel, Princeton University,
            Xavier Leroy, Collège de France and Inria.
   Copyright: Andrew W. Appel and Inria.
   License: BSD-3-Clause. *)

From Stdlib Require Import Program FunctionalExtensionality.
From MetaRocq.Utils Require Import String2pos.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Set Implicit Arguments.

Module PTree.

   (** ** Representation of tries *)

   (** The type [tree'] of nonempty tries.  Each constructor is of the form
       [NodeXYZ], where the bit [X] says whether there is a left subtree,
       [Y] whether there is a value at this node, and [Z] whether there is
       a right subtree. *)

   Inductive tree' (A: Type) : Type :=
   | Node001: tree' A -> tree' A
   | Node010: A -> tree' A
   | Node011: A -> tree' A -> tree' A
   | Node100: tree' A -> tree' A
   | Node101: tree' A -> tree' A ->tree' A
   | Node110: tree' A -> A -> tree' A
   | Node111: tree' A -> A -> tree' A -> tree' A.

   (** The type [tree] of tries, empty or nonempty. *)

   Inductive tree (A: Type) : Type :=
   | Empty: tree A
   | Nodes: tree' A -> tree A.

   Arguments Node001 {A} _.
   Arguments Node010 {A} _.
   Arguments Node011 {A} _ _.
   Arguments Node100 {A} _.
   Arguments Node101 {A} _ _.
   Arguments Node110 {A} _ _.
   Arguments Node111 {A} _ _ _.

   Arguments Empty {A}.
   Arguments Nodes {A} _.

   Definition t := tree.

   Scheme tree'_ind := Induction for tree' Sort Prop.

   (** A smart constructor similar to the [Node'] smart constructor
       of the original implementation.  Given a (possibly empty) left subtree,
       a (possibly absent) value, and a (possibly empty) right subtree,
       it builds the corresponding tree. *)

   Definition Node {A} (l: tree A) (o: option A) (r: tree A) : tree A :=
     match l,o,r with
     | Empty, None, Empty => Empty
     | Empty, None, Nodes r' => Nodes (Node001 r')
     | Empty, Some x, Empty => Nodes (Node010 x)
     | Empty, Some x, Nodes r' => Nodes (Node011 x r')
     | Nodes l', None, Empty => Nodes (Node100 l')
     | Nodes l', None, Nodes r' => Nodes (Node101 l' r')
     | Nodes l', Some x, Empty => Nodes (Node110 l' x)
     | Nodes l', Some x, Nodes r' => Nodes (Node111 l' x r')
     end.

   (** ** Basic operations: [empty], [get], [set], [remove] *)

   Definition empty (A: Type) : tree A := Empty.

   (** Operations such as [get] follow a common pattern:
       first, a recursive function [get'] over nonempty tries;
       then, a non-recursive function [get] to handle empty tries too. *)

   Fixpoint get' {A} (p: positive) (m: tree' A) : option A :=
   match p, m with
   | xH, Node001 _ => None
   | xH, Node010 x => Some x
   | xH, Node011 x _ => Some x
   | xH, Node100 _ => None
   | xH, Node101 _ _ => None
   | xH, Node110 _ x => Some x
   | xH, Node111 _ x _ => Some x
   | xO q, Node001 _ => None
   | xO q, Node010 _ => None
   | xO q, Node011 _ _ => None
   | xO q, Node100 m' => get' q m'
   | xO q, Node101 m' _ => get' q m'
   | xO q, Node110 m' _ => get' q m'
   | xO q, Node111 m' _ _ => get' q m'
   | xI q, Node001 m' => get' q m'
   | xI q, Node010 _ => None
   | xI q, Node011 _ m' => get' q m'
   | xI q, Node100 m' => None
   | xI q, Node101 _ m' => get' q m'
   | xI q, Node110 _ _ => None
   | xI q, Node111 _ _ m' => get' q m'
   end.

   Definition get {A} (p: positive) (m: tree A) : option A :=
   match m with
   | Empty => None
   | Nodes m' => get' p m'
   end.

   (** [set0 p x] constructs the singleton trie that maps [p] to [x]
       and has no other bindings. *)

   Fixpoint set0 {A} (p: positive) (x: A) : tree' A :=
   match p with
   | xH => Node010 x
   | xO q => Node100 (set0 q x)
   | xI q => Node001 (set0 q x)
   end.

   Fixpoint set' {A} (p: positive) (x: A) (m: tree' A) : tree' A :=
   match p, m with
   | xH, Node001 r => Node011 x r
   | xH, Node010 _ => Node010 x
   | xH, Node011 _ r => Node011 x r
   | xH, Node100 l => Node110 l x
   | xH, Node101 l r => Node111 l x r
   | xH, Node110 l _ => Node110 l x
   | xH, Node111 l _ r => Node111 l x r
   | xO q, Node001 r => Node101 (set0 q x) r
   | xO q, Node010 y => Node110 (set0 q x) y
   | xO q, Node011 y r => Node111 (set0 q x) y r
   | xO q, Node100 l => Node100 (set' q x l)
   | xO q, Node101 l r => Node101 (set' q x l) r
   | xO q, Node110 l y => Node110 (set' q x l) y
   | xO q, Node111 l y r => Node111 (set' q x l) y r
   | xI q, Node001 r => Node001 (set' q x r)
   | xI q, Node010 y => Node011 y (set0 q x)
   | xI q, Node011 y r => Node011 y (set' q x r)
   | xI q, Node100 l => Node101 l (set0 q x)
   | xI q, Node101 l r => Node101 l (set' q x r)
   | xI q, Node110 l y => Node111 l y (set0 q x)
   | xI q, Node111 l y r => Node111 l y (set' q x r)
   end.

   Definition set {A} (p: positive) (x: A) (m: tree A) : tree A :=
   match m with
   | Empty => Nodes (set0 p x)
   | Nodes m' => Nodes (set' p x m')
   end.

   (** Removal in a nonempty trie produces a possibly empty trie.
       To simplify the code, we use the [Node] smart constructor in the
       cases where the result can be empty or nonempty, depending on the
       results of the recursive calls. *)

   Fixpoint rem' {A} (p: positive) (m: tree' A) : tree A :=
   match p, m with
   | xH, Node001 r => Nodes m
   | xH, Node010 _ => Empty
   | xH, Node011 _ r => Nodes (Node001 r)
   | xH, Node100 l => Nodes m
   | xH, Node101 l r => Nodes m
   | xH, Node110 l _ => Nodes (Node100 l)
   | xH, Node111 l _ r => Nodes (Node101 l r)
   | xO q, Node001 r => Nodes m
   | xO q, Node010 y => Nodes m
   | xO q, Node011 y r => Nodes m
   | xO q, Node100 l => Node (rem' q l) None Empty
   | xO q, Node101 l r => Node (rem' q l) None (Nodes r)
   | xO q, Node110 l y => Node (rem' q l) (Some y) Empty
   | xO q, Node111 l y r => Node (rem' q l) (Some y) (Nodes r)
   | xI q, Node001 r => Node Empty None (rem' q r)
   | xI q, Node010 y => Nodes m
   | xI q, Node011 y r => Node Empty (Some y) (rem' q r)
   | xI q, Node100 l => Nodes m
   | xI q, Node101 l r => Node (Nodes l) None (rem' q r)
   | xI q, Node110 l y => Nodes m
   | xI q, Node111 l y r => Node (Nodes l) (Some y) (rem' q r)
   end.

   (** This use of [Node] causes some run-time overhead, which we eliminate
       by asking Rocq to unfold the definition of [Node] in [rem'],
       then simplify the definition.  This is a form of partial evaluation. *)

   Definition remove' := Eval cbv [rem' Node] in @rem'.

   Definition remove {A} (p: positive) (m: tree A) : tree A :=
   match m with
   | Empty => Empty
   | Nodes m' => remove' p m'
   end.

   (** ** Good variable properties for the basic operations *)

   Theorem gempty:
     forall (A: Type) (i: positive), get i (empty A) = None.
   Proof. reflexivity. Qed.

   Lemma gss0: forall {A} p (x: A), get' p (set0 p x) = Some x.
   Proof. induction p; simpl; auto. Qed.

   Lemma gso0: forall {A} p q (x: A), p<>q -> get' p (set0 q x) = None.
   Proof.
    induction p; destruct q; simpl; intros; auto; try apply IHp; congruence.
   Qed.

   Theorem gss:
     forall (A: Type) (i: positive) (x: A) (m: tree A), get i (set i x m) = Some x.
   Proof.
    intros. destruct m as [|m]; simpl.
    - apply gss0.
    - revert m; induction i; destruct m; simpl; intros; auto using gss0.
   Qed.

   Theorem gso:
     forall (A: Type) (i j: positive) (x: A) (m: tree A),
     i <> j -> get i (set j x m) = get i m.
   Proof.
    intros. destruct m as [|m]; simpl.
    - apply gso0; auto.
    - revert m j H; induction i; destruct j,m; simpl; intros; auto;
      solve [apply IHi; congruence | apply gso0; congruence | congruence].
   Qed.

   Lemma gNode:
     forall {A} (i: positive) (l: tree A) (x: option A) (r: tree A),
     get i (Node l x r) = match i with xH => x | xO j => get j l | xI j => get j r end.
   Proof.
     intros. destruct l, x, r; simpl; auto; destruct i; auto.
   Qed.

   Theorem grs:
     forall (A: Type) (i: positive) (m: tree A), get i (remove i m) = None.
   Proof.
     Local Opaque Node.
     destruct m as [ |m]; simpl. auto.
     change (remove' i m) with (rem' i m).
     revert m. induction i; destruct m; simpl; auto; rewrite gNode; auto.
   Qed.

   Theorem gro:
     forall (A: Type) (i j: positive) (m: tree A),
     i <> j -> get i (remove j m) = get i m.
   Proof.
     Local Opaque Node.
     destruct m as [ |m]; simpl. auto.
     change (remove' j m) with (rem' j m).
     revert j m. induction i; destruct j, m; simpl; intros; auto;
     solve [ congruence
           | rewrite gNode; auto; apply IHi; congruence ].
   Qed.

   (** ** The [map_filter] collective operation over tries *)

   Section MAP_FILTER.

   Variables A B: Type.

   Definition option_map (f: A -> option B) (o: option A): option B :=
     match o with None => None | Some a => f a end.

   Fixpoint map_filter' (f: A -> option B) (m: tree' A) : tree B :=
     match m with
     | Node001 r => Node Empty None (map_filter' f r)
     | Node010 x => Node Empty (f x) Empty
     | Node011 x r => Node Empty (f x) (map_filter' f r)
     | Node100 l => Node (map_filter' f l) None Empty
     | Node101 l r => Node (map_filter' f l) None (map_filter' f r)
     | Node110 l x => Node (map_filter' f l) (f x) Empty
     | Node111 l x r => Node (map_filter' f l) (f x) (map_filter' f r)
     end.

   Definition map_filter'_opt := Eval cbv [map_filter' Node] in map_filter'.

   Definition map_filter (f: A -> option B) (m: tree A) : tree B :=
     match m with
     | Empty => Empty
     | Nodes m' => map_filter'_opt f m'
     end.

   Theorem gmap_filter':
     forall (f: A -> option B) (m: tree' A) (i: positive),
     get i (map_filter' f m) = option_map f (get' i m).
   Proof using Type.
     induction m; simpl; intros; rewrite gNode; destruct i; simpl; auto.
   Qed.

   Theorem gmap_filter:
     forall (f: A -> option B) (m: tree A) (i: positive),
     get i (map_filter f m) = option_map f (get i m).
   Proof using Type.
     intros. destruct m as [ | m]; simpl. auto.
     change (map_filter'_opt f m) with (map_filter' f m).
     apply gmap_filter'.
   Qed.

   Lemma unroll_map_filter:
     forall (f: A -> option B) (l: tree A) (o: option A) (r: tree A),
     map_filter f (Node l o r) = Node (map_filter f l) (option_map f o) (map_filter f r).
   Proof using Type.
     intros. unfold map_filter. change map_filter'_opt with map_filter'.
     destruct l, o, r; reflexivity.
   Qed.

   End MAP_FILTER.

   (** ** Custom case analysis principles and induction principles *)

   (** We can view canonical tries as being of one of two (non-exclusive)
       cases: either [Empty] for an empty trie, or [Node l o r] for a
       possibly nonempty trie, with [l] and [r] the left and right subtrees
       and [o] an optional value.  These are exactly the two cases of
       the original implementation of tries (module [Original]).

       The [Empty] constructor and the [Node] smart function defined above
       provide one half of the view: the one that lets us construct values
       of type [tree A].

       We now define the other half of the view: the one that lets us
       inspect and recurse over values of type [tree A].  This is achieved
       by defining appropriate principles for case analysis and induction. *)

   Definition not_trivially_empty {A} (l: tree A) (o: option A) (r: tree A) :=
     match l, o, r with
     | Empty, None, Empty => False
     | _, _, _ => True
     end.

   (** *** A case analysis principle *)

   Section TREE_CASE.

   Context {A B: Type}
           (empty: B)
           (node: tree A -> option A -> tree A -> B).

   Definition tree_case (m: tree A) : B :=
     match m with
     | Empty => empty
     | Nodes (Node001 r) => node Empty None (Nodes r)
     | Nodes (Node010 x) => node Empty (Some x) Empty
     | Nodes (Node011 x r) => node Empty (Some x) (Nodes r)
     | Nodes (Node100 l) => node (Nodes l) None Empty
     | Nodes (Node101 l r) => node (Nodes l) None (Nodes r)
     | Nodes (Node110 l x) => node (Nodes l) (Some x) Empty
     | Nodes (Node111 l x r) => node (Nodes l) (Some x) (Nodes r)
     end.

   (** In terms of the original implementation of tries, the function
       [tree_case] corresponds to a simple pattern matching:
   <<
       Definition tree_case (m: tree A) : B :=
         match m with Leaf => empty | Node l o r => node l o r end.
   >>
   *)

   Lemma unroll_tree_case: forall l o r,
     not_trivially_empty l o r ->
     tree_case (Node l o r) = node l o r.
   Proof using Type.
     destruct l, o, r; simpl; intros; auto. contradiction.
   Qed.

   (** Alternatively, we can omit the [not_trivially_empty] hypothesis
       if the [node] case for trivially empty nodes agrees with the [empty] case. *)

   Hypothesis node_empty: node Empty None Empty = empty.

   Lemma unroll_tree_case_gen: forall l o r,
     tree_case (Node l o r) = node l o r.
   Proof using A B empty node node_empty.
     destruct l, o, r; simpl; auto.
   Qed.

   End TREE_CASE.

   (** *** A recursion principle *)

   Section TREE_REC.

   Context {A B: Type}
           (empty: B)
           (node: tree A -> B -> option A -> tree A -> B -> B).

   Fixpoint tree_rec' (m: tree' A) : B :=
     match m with
     | Node001 r => node Empty empty None (Nodes r) (tree_rec' r)
     | Node010 x => node Empty empty (Some x) Empty empty
     | Node011 x r => node Empty empty (Some x) (Nodes r) (tree_rec' r)
     | Node100 l => node (Nodes l) (tree_rec' l) None Empty empty
     | Node101 l r => node (Nodes l) (tree_rec' l) None (Nodes r) (tree_rec' r)
     | Node110 l x => node (Nodes l) (tree_rec' l) (Some x) Empty empty
     | Node111 l x r => node (Nodes l) (tree_rec' l) (Some x) (Nodes r) (tree_rec' r)
     end.

   Definition tree_rec (m: tree A) : B :=
     match m with
     | Empty => empty
     | Nodes m' => tree_rec' m'
     end.

   (** In terms of the original implementation of tries, the function
       [tree_rec] corresponds to the basic recursion principle for type
       [Original.tree]:
   <<
       Fixpoint tree_rec (m: tree A) : B :=
         match m with
         | Leaf => empty
         | Node l o r => node l (tree_rec l) o r (tree_rec r)
         end.
   >>
   *)

   Lemma unroll_tree_rec: forall l o r,
     not_trivially_empty l o r ->
     tree_rec (Node l o r) = node l (tree_rec l) o r (tree_rec r).
   Proof using Type.
     destruct l, o, r; simpl; intros; auto. contradiction.
   Qed.

   Hypothesis node_empty: node Empty empty None Empty empty = empty.

   Lemma unroll_tree_rec_gen: forall l o r,
     tree_rec (Node l o r) = node l (tree_rec l) o r (tree_rec r).
   Proof using A B empty node node_empty.
     destruct l, o, r; simpl; auto.
   Qed.

   End TREE_REC.

   (** *** An induction principle *)

   (** We now define a more general induction principle that supports
       a result type that depends on the argument value.
       This principle is usable both for computations and for proofs. *)

   Section TREE_IND.

   Context {A: Type} (P: tree A -> Type)
           (empty: P Empty)
           (node: forall l, P l -> forall o r, P r -> not_trivially_empty l o r ->
                  P (Node l o r)).

   Program Fixpoint tree_ind' (m: tree' A) : P (Nodes m) :=
     match m with
     | Node001 r => @node Empty empty None (Nodes r) (tree_ind' r) _
     | Node010 x => @node Empty empty (Some x) Empty empty _
     | Node011 x r => @node Empty empty (Some x) (Nodes r) (tree_ind' r) _
     | Node100 l => @node (Nodes l) (tree_ind' l) None Empty empty _
     | Node101 l r => @node (Nodes l) (tree_ind' l) None (Nodes r) (tree_ind' r) _
     | Node110 l x => @node (Nodes l) (tree_ind' l) (Some x) Empty empty _
     | Node111 l x r => @node (Nodes l) (tree_ind' l) (Some x) (Nodes r) (tree_ind' r) _
     end.

   Definition tree_ind (m: tree A) : P m :=
     match m with
     | Empty => empty
     | Nodes m' => tree_ind' m'
     end.

   (** [tree_ind] defined above has almost the same type as the
       induction principle automatically derived by Rocq for the
       [Original.tree] type of the original trie implementation.
       The only difference is that the [node] case receives an additional
       hypothesis [not_trivially_empty l o r], which is useful to apply
       the [unroll_tree_case] and [unroll_tree_rec] equations. *)

   End TREE_IND.

   (** Example of use: alternate proofs for the [set] operation. *)

   Lemma set_Empty: forall A (v: A) p,
     set p v Empty =
       match p with
       | xH => Node Empty (Some v) Empty
       | xO q => Node (set q v Empty) None Empty
       | xI q => Node Empty None (set q v Empty)
       end.
   Proof.
     destruct p; reflexivity.
   Qed.

   Lemma set_Node: forall A (v: A) l o r p,
     set p v (Node l o r) =
       match p with
       | xH => Node l (Some v) r
       | xO q => Node (set q v l) o r
       | xI q => Node l o (set q v r)
       end.
   Proof.
     destruct l, o, r, p; reflexivity.
   Qed.

   Theorem gss_alt_proof:
     forall (A: Type) (i: positive) (x: A) (m: tree A), get i (set i x m) = Some x.
   Proof.
     induction i; induction m using tree_ind; intros;
     (rewrite set_Empty || rewrite set_Node); rewrite gNode; auto.
   Qed.

   Theorem gso_alt_proof:
     forall (A: Type) (i j: positive) (x: A) (m: tree A),
     i <> j -> get i (set j x m) = get i m.
   Proof.
     induction i; destruct j; induction m using tree_ind; intros;
     (rewrite set_Empty || rewrite set_Node); rewrite ! gNode; auto;
     try (apply IHi); congruence.
   Qed.

   (** ** The [combine] collective operation over pairs of tries *)

   Section COMBINE.

   Variables A B C: Type.
   Variable f: option A -> option B -> option C.
   Hypothesis f_None_None: f None None = None.

   Definition combine'_l := map_filter' (fun a => f (Some a) None).
   Definition combine'_r := map_filter' (fun b => f None (Some b)).

   (** First definition of [combine'], done by writing 49 cases (7x7) by hand. *)

   Fixpoint combine'_direct (m1: tree' A) (m2: tree' B) {struct m1} : tree C :=
    let c := combine'_direct in
    let f1 x1 := f (Some x1) None in
    let f2 x2 := f None (Some x2) in
    let f' x1 x2 := f (Some x1) (Some x2) in
    let c1 := combine'_l in
    let c2 := combine'_r in
    match m1, m2 with
    | Node001 r1, Node001 r2 => Node Empty None (c r1 r2)
    | Node001 r1, Node010 x2 => Node Empty (f2 x2) (c1 r1)
    | Node001 r1, Node011 x2 r2 => Node Empty (f2 x2) (c r1 r2)
    | Node001 r1, Node100 l2 => Node (c2 l2) None (c1 r1)
    | Node001 r1, Node101 l2 r2 => Node (c2 l2) None (c r1 r2)
    | Node001 r1, Node110 l2 x2 => Node (c2 l2) (f2 x2) (c1 r1)
    | Node001 r1, Node111 l2 x2 r2 => Node (c2 l2) (f2 x2) (c r1 r2)

    | Node010 x1, Node001 r2 => Node Empty (f1 x1) (c2 r2)
    | Node010 x1, Node010 x2 => Node Empty (f' x1 x2) Empty
    | Node010 x1, Node011 x2 r2 => Node Empty (f' x1 x2) (c2 r2)
    | Node010 x1, Node100 l2 => Node (c2 l2) (f1 x1) Empty
    | Node010 x1, Node101 l2 r2 => Node (c2 l2) (f1 x1) (c2 r2)
    | Node010 x1, Node110 l2 x2 => Node (c2 l2) (f' x1 x2) Empty
    | Node010 x1, Node111 l2 x2 r2 => Node (c2 l2) (f' x1 x2) (c2 r2)

    | Node011 x1 r1, Node001 r2 => Node Empty (f1 x1) (c r1 r2)
    | Node011 x1 r1, Node010 x2 => Node Empty (f' x1 x2) (c1 r1)
    | Node011 x1 r1, Node011 x2 r2 => Node Empty (f' x1 x2) (c r1 r2)
    | Node011 x1 r1, Node100 l2 => Node (c2 l2) (f1 x1) (c1 r1)
    | Node011 x1 r1, Node101 l2 r2 => Node (c2 l2) (f1 x1) (c r1 r2)
    | Node011 x1 r1, Node110 l2 x2 => Node (c2 l2) (f' x1 x2) (c1 r1)
    | Node011 x1 r1, Node111 l2 x2 r2 => Node (c2 l2) (f' x1 x2) (c r1 r2)

    | Node100 l1, Node001 r2 => Node (c1 l1) None (c2 r2)
    | Node100 l1, Node010 x2 => Node (c1 l1) (f2 x2) Empty
    | Node100 l1, Node011 x2 r2 => Node (c1 l1) (f2 x2) (c2 r2)
    | Node100 l1, Node100 l2 => Node (c l1 l2) None Empty
    | Node100 l1, Node101 l2 r2 => Node (c l1 l2) None (c2 r2)
    | Node100 l1, Node110 l2 x2 => Node (c l1 l2) (f2 x2) Empty
    | Node100 l1, Node111 l2 x2 r2 => Node (c l1 l2) (f2 x2) (c2 r2)

    | Node101 l1 r1, Node001 r2 => Node (c1 l1) None (c r1 r2)
    | Node101 l1 r1, Node010 x2 => Node (c1 l1) (f2 x2) (c1 r1)
    | Node101 l1 r1, Node011 x2 r2 => Node (c1 l1) (f2 x2) (c r1 r2)
    | Node101 l1 r1, Node100 l2 => Node (c l1 l2) None (c1 r1)
    | Node101 l1 r1, Node101 l2 r2 => Node (c l1 l2) None (c r1 r2)
    | Node101 l1 r1, Node110 l2 x2 => Node (c l1 l2) (f2 x2) (c1 r1)
    | Node101 l1 r1, Node111 l2 x2 r2 => Node (c l1 l2) (f2 x2) (c r1 r2)

    | Node110 l1 x1, Node001 r2 => Node (c1 l1) (f1 x1) (c2 r2)
    | Node110 l1 x1, Node010 x2 => Node (c1 l1) (f' x1 x2) Empty
    | Node110 l1 x1, Node011 x2 r2 => Node (c1 l1) (f' x1 x2) (c2 r2)
    | Node110 l1 x1, Node100 l2 => Node (c l1 l2) (f1 x1) Empty
    | Node110 l1 x1, Node101 l2 r2 => Node (c l1 l2) (f1 x1) (c2 r2)
    | Node110 l1 x1, Node110 l2 x2 => Node (c l1 l2) (f' x1 x2) Empty
    | Node110 l1 x1, Node111 l2 x2 r2 => Node (c l1 l2) (f' x1 x2) (c2 r2)

    | Node111 l1 x1 r1, Node001 r2 => Node (c1 l1) (f1 x1) (c r1 r2)
    | Node111 l1 x1 r1, Node010 x2 => Node (c1 l1) (f' x1 x2) (c1 r1)
    | Node111 l1 x1 r1, Node011 x2 r2 => Node (c1 l1) (f' x1 x2) (c r1 r2)
    | Node111 l1 x1 r1, Node100 l2 => Node (c l1 l2) (f1 x1) (c1 r1)
    | Node111 l1 x1 r1, Node101 l2 r2 => Node (c l1 l2) (f1 x1) (c r1 r2)
    | Node111 l1 x1 r1, Node110 l2 x2 => Node (c l1 l2) (f' x1 x2) (c1 r1)
    | Node111 l1 x1 r1, Node111 l2 x2 r2 => Node (c l1 l2) (f' x1 x2) (c r1 r2)
   end.

   (** We now prove the expected "get-combine" equation for [combine'_direct].
       This is a great way to find mistakes in the definition above. *)

   Lemma gcombine'_l: forall m i, get i (combine'_l m) = f (get' i m) None.
   Proof using A B C f f_None_None.
     intros. unfold combine'_l. rewrite gmap_filter'. destruct (get' i m); auto.
   Qed.

   Lemma gcombine'_r: forall m i, get i (combine'_r m) = f None (get' i m).
   Proof using A B C f f_None_None.
     intros. unfold combine'_r. rewrite gmap_filter'. destruct (get' i m); auto.
   Qed.

   Lemma gcombine'_direct: forall m1 m2 i,
     get i (combine'_direct m1 m2) = f (get' i m1) (get' i m2).
   Proof using A B C f f_None_None.
     induction m1; destruct m2; intros; simpl; rewrite gNode;
     destruct i; simpl; auto using gcombine'_l, gcombine'_r.
   Qed.

   (** Second definition of [combine'], using tactics to fill out the 49 cases. *)

   Fixpoint combine'_by_tac (m1: tree' A) (m2: tree' B) {struct m1} : tree C.
   Proof using A B C f.
     destruct m1 as [ r1 | x1 | x1 r1 | l1 | l1 r1 | l1 x1 | l1 x1 r1 ];
     destruct m2 as [ r2 | x2 | x2 r2 | l2 | l2 r2 | l2 x2 | l2 x2 r2 ];
     (apply Node;
      [ solve [ exact (combine'_by_tac l1 l2)
              | exact (combine'_l l1)
              | exact (combine'_r l2)
              | exact Empty]
      | solve [ exact (f (Some x1) (Some x2))
              | exact (f None (Some x2))
              | exact (f (Some x1) None)
              | exact None]
      | solve [ exact (combine'_by_tac r1 r2)
              | exact (combine'_l r1)
              | exact (combine'_r r2)
              | exact Empty ]
      ]).
   Defined.

   (** Again, proving the "get-combine" equation for [combine'_by_tac]
       brings much confidence that we got the tactics-based definition right.
       The proof script is identical to the proof for [gcombine'_direct],
       which is not surprising in light of the Lemma [combine'_by_tac_eq],
       below! *)

   Lemma gcombine'_by_tac: forall m1 m2 i,
     get i (combine'_by_tac m1 m2) = f (get' i m1) (get' i m2).
   Proof using A B C f f_None_None.
     induction m1; destruct m2; intros; simpl; rewrite gNode;
     destruct i; simpl; auto using gcombine'_l, gcombine'_r.
   Qed.

   (** Actually, the tactics produced exactly the same definition as
       the one we wrote by hand before. *)

   Lemma combine'_by_tac_eq: combine'_by_tac = combine'_direct.
   Proof using Type.
     reflexivity.
   Qed.

   (** We can now finish the definition of [combine], adding cases
       for when one or both of the tries are empty. *)

   Definition combine (m1: tree A) (m2: tree B) : tree C :=
     match m1, m2 with
     | Empty, Empty => Empty
     | Empty, Nodes m2 => combine'_r m2
     | Nodes m1, Empty => combine'_l m1
     | Nodes m1, Nodes m2 => combine'_by_tac m1 m2
     end.

   Theorem gcombine:
     forall (m1: tree A) (m2: tree B) (i: positive),
     get i (combine m1 m2) = f (get i m1) (get i m2).
   Proof using A B C f f_None_None.
     intros. destruct m1 as [ | m1], m2 as [ | m2]; simpl.
     - auto.
     - apply gcombine'_r.
     - apply gcombine'_l.
     - apply gcombine'_by_tac.
   Qed.

   (** An alternate definition of [combine] is possible, using the
       2-constructor view of tries and the custom induction principles
       introduced earlier. *)

   Definition combine_view_gen (m1: tree A) (m2: tree B) : tree C :=
     tree_rec
       (map_filter (fun b => f None (Some b)))
       (fun l1 lrec o1 r1 rrec =>
         tree_case
           (map_filter (fun a => f (Some a) None) (Node l1 o1 r1))
           (fun l2 o2 r2 => Node (lrec l2) (f o1 o2) (rrec r2)))
       m1 m2.

   (** The custom principles add a lot of run-time overhead.  Partial evaluation
       can eliminate most (but not all) of this overhead.  *)

   Definition combine_view :=
     Eval cbv [combine_view_gen tree_rec tree_rec' tree_case] in combine_view_gen.

   (** The combine equation can be proved directly on the [combine_view]
       implementation, using [tree_ind] to perform induction on [m1]
       and case analysis on [m2]. *)

   Theorem gcombine_view:
     forall (m1: tree A) (m2: tree B) (i: positive),
     get i (combine_view m1 m2) = f (get i m1) (get i m2).
   Proof using A B C f f_None_None.
     change combine_view with combine_view_gen. unfold combine_view_gen.
     induction m1 using tree_ind; intros.
   - simpl. rewrite gmap_filter. destruct (get i m2); auto.
   - rewrite unroll_tree_rec by auto.
     induction m2 using tree_ind; intros.
     + simpl. rewrite gmap_filter. destruct (get i (Node m1_1 o m1_2)); auto.
     + rewrite unroll_tree_case by auto. rewrite ! gNode. destruct i; auto.
   Qed.

   End COMBINE.

   (** ** Extensionality property *)

   (** This is the key property of canonical tries that makes them extensional:
       every [tree' A] contains at least one key-value pair. *)

   Lemma tree'_not_empty:
     forall (A: Type) (m: tree' A), exists i, get' i m <> None.
   Proof.
    induction m; simpl; try destruct IHm as [p H].
    - exists (xI p); auto.
    - exists xH; simpl; congruence.
    - exists xH; simpl; congruence.
    - exists (xO p); auto.
    - destruct IHm1 as [p H]; exists (xO p); auto.
    - exists xH; simpl; congruence.
    - exists xH; simpl; congruence.
   Qed.

   (** As a corollary, the only [tree A] that contains no key-value pairs
       is [Empty]. *)

   Corollary extensionality_empty:
     forall (A: Type) (m: tree A),
     (forall i, get i m = None) -> m = Empty.
   Proof.
     intros. destruct m as [ | m]; auto. destruct (tree'_not_empty m) as [i GET].
     elim GET. apply H.
   Qed.

   (** Extensionality follows by a simple inductive argument.
       We can use [tree_ind] as the induction principle so as to reduce the
       number of cases to consider to 4. *)

   Theorem extensionality:
     forall (A: Type) (m1 m2: tree A),
     (forall i, get i m1 = get i m2) -> m1 = m2.
   Proof.
     intros A. induction m1 using tree_ind; induction m2 using tree_ind; intros.
   - auto.
   - symmetry. apply extensionality_empty. intros; symmetry; apply H0.
   - apply extensionality_empty. apply H0.
   - f_equal.
     + apply IHm1_1. intros. specialize (H1 (xO i)); rewrite ! gNode in H1. auto.
     + specialize (H1 xH); rewrite ! gNode in H1. auto.
     + apply IHm1_2. intros. specialize (H1 (xI i)); rewrite ! gNode in H1. auto.
   Qed.

End PTree.
