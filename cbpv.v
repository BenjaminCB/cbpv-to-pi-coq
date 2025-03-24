From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Autosubst Require Import Autosubst.

Set Implicit Arguments.
Unset Strict Implicit.

Inductive term :=
| Value (v : value)
| Abs (m : {bind term})
| App (m n : term)
| Force (v : value)
| Return (v : value)
| Bind (m : term) (n : {bind term})

with value :=
| Var (x : var)
| Thunk (m : term).

Global Instance Ids_value : Ids value. derive. Defined.
Global Instance Rename_value : Rename value. derive. Defined.
Global Instance Subst_value : Subst value. derive. Defined.
Global Instance SubstLemmas_value : SubstLemmas value. derive. Qed.

Global Instance Rename_term : Rename term. derive. Defined.
Global Instance Subst_term : Subst term. derive. Defined.
Global Instance Ids_term : Ids term. derive. Defined.

Global Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

