From stdpp Require Import base finite.
From granite.core Require Import Bits.

From granite.core Require Import
  Bits
  Pair
  Program.

Declare Scope spec_scope.
Notation "f '⋆' g" := (PairSpec f g) (at level 80, right associativity ) : spec_scope.
Notation "f '#' g" := (PairMethod f g) (at level 80, right associativity ) : spec_scope.
Delimit Scope spec_scope with spec_scope.

Ltac _extract_method_t spec_t :=
  match type of spec_t with
  | Spec _ ?t => exact t
  end.
Ltac _extract_vmethod_t spec_t :=
  match type of spec_t with
  | Spec ?t _ => exact t
  end.


