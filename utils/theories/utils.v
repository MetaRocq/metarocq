(* Distributed under the terms of the MIT license. *)

(** ** This file exports utilities and notations used in MetaRocq. *)
(** If you don't want to have the following scopes opened you should *)
(** not import this file or close them. *)

From Corelib Require Import ssreflect ssrfun ssrbool.
From Stdlib Require Export Bool ZArith Arith Lia List.
From Corelib Require Import RelationClasses.
From MetaRocq.Utils Require Export MRUtils monad_utils.

Global Set Asymmetric Patterns.

Global Open Scope bs_scope.

Global Open Scope list_scope.

(** With nat here, the default intepretation of [=?] is for nat. *)
Global Open Scope nat_scope.

(** We keep [++] for lists and use [^] for stings. *)
Declare Scope string_scope2.
Notation "s1 ^ s2" := (bytestring.String.append s1 s2) : string_scope2.
Open Scope string_scope2.

(** We want [*] from type_scope but [+] from nat_scope. *)
(** Warning: [*] is left associative, prefer [×] when chaining products *)
(** so that it behaves as sigma types. *)
Declare Scope type_scope2.
Notation "A * B" := (prod A B) : type_scope2.
Global Open Scope type_scope2.

Global Open Scope metarocq_scope.

#[global] Hint Constructors unit : core.
