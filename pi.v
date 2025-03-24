From Autosubst Require Import Autosubst.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive proc : Type :=
| null
| in (a : var) (