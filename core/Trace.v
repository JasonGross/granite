From stdpp Require Import base.
From granite.core Require Import
  Program.                  

Inductive Event {M: Type -> Type} : Type :=
| CallEvent {R : Type} (m: M R).

Arguments Event: clear implicits.
Definition Trace M := list (Event M).

Definition filterTrace {M} (fn: forall {R}, M R -> bool) (tr: Trace M) : Trace M :=
  List.filter (fun ev => match ev with 
                     | CallEvent m => fn m
                     end) tr.

Fixpoint execTrace {VM M} (spec: Spec VM M) (tr: Trace M) (st: spec.(State)) : spec.(State) :=
  match tr with
  | [] => st 
  | (CallEvent m)::tr => execTrace spec tr (snd (spec.(EvalMethod) m st))
  end.
