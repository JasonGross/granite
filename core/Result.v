From stdpp Require Import base list tactics.

Inductive result {F S} :=
| Success (s: S)
| Failure (f: F).
Arguments result : clear implicits.

Lemma Failure_ne_Success {A F} (x : A) (f: F): Failure f ≠ Success x.
Proof. congruence. Qed.
Lemma Success_ne_Failure {A F} (x : A) (f: F): Success x ≠ Failure f.
Proof. congruence. Qed.

Lemma eq_Failure_ne_Success {S F} (mx : result F S) : (∀ x, mx ≠ Success x) ↔ exists f, mx = Failure f.
Proof. destruct mx; split; naive_solver. Qed.
Lemma eq_Failure_ne_Success_1 {A F} (mx : result F A) f x : mx = Failure f → mx ≠ Success x.
Proof. intros ?. congruence. Qed.
Global Instance Success_inj {A F} : Inj (=) (=) (@Success A F ).
Proof. congruence. Qed.

Definition from_result {A B F} (f : A → B) (y : B) (mx : result F A) : B :=
  match mx with Failure _ => y | Success x => f x end.
Global Instance: Params (@from_result) 2 := {}.
Global Arguments from_result {_ _ _} _ _ !_ / : assert.

(** The eliminator with the identity function. *)
Notation default := (from_result id).
Definition is_success {F S} (r: result F S) :=
  match r with
  | Success s => true
  | Failure f => false
  end.

Definition extract_success {F S} (r: result F S) (pr: is_success r = true) :=
  match r return is_success r = true -> S with
  | Success s => fun _ => s
  | Failure f => fun pr => match Bool.diff_false_true pr with end
  end pr.


Definition is_Success {S} {F} (mx: result F S) := exists s, mx = Success s.
Global Instance: Params (@is_Success) 1 := {}.
Definition is_Failure {S} {F} (mx: result F S) := exists f, mx = Failure f.
Global Instance: Params (@is_Failure) 1 := {}.

(** We avoid calling [done] recursively as that can lead to an unresolved evar. *)
Global Hint Extern 0 (is_Success _) => eexists; fast_done : core.

Lemma is_Success_alt {S} {F} (mx : result F S) :
  is_Success mx ↔ match mx with Success _ => True | Failure _ => False end.
Proof. unfold is_Success. destruct mx; naive_solver. Qed.
Lemma mk_is_Success {S} {F} (mx : result F S) x : mx = Success x → is_Success mx.
Proof. by intros ->. Qed.
Global Hint Resolve mk_is_Success: core.
Lemma is_Success_Failure {S} {F} f : ¬is_Success(@Failure S F f).
Proof. by destruct 1. Qed.
Global Hint Resolve is_Success_Failure : core.
Lemma is_Failure_Success {S} {F} f : ¬is_Failure (@Success S F f).
Proof. by destruct 1. Qed.
Global Hint Resolve is_Failure_Success : core.

Global Instance is_Success_pi {S} {F} (mx : result F S) : ProofIrrel (is_Success mx).
Proof.
  set (P (mx : result F S) := match mx with Success _ => True | _ => False end).
  set (f mx := match mx return P mx → is_Success mx with
    Success _ => λ _, ex_intro _ _ eq_refl | Failure _ => False_rect _ end).
  set (g mx (H : is_Success mx) :=
    match H return P mx with ex_intro _ _ p => eq_rect _ _ I _ (eq_sym p) end).
  assert (∀ mx H, f mx (g mx H) = H) as f_g by (by intros ? [??]; subst).
  intros p1 p2. rewrite <-(f_g _ p1), <-(f_g _ p2). by destruct mx, p1.
Qed.
Global Instance is_Failure_pi {S} {F} (mx : result F S) : ProofIrrel (is_Failure mx).
Proof.
  set (P (mx : result F S) := match mx with Success _ => False | _ => True end).
  set (f mx := match mx return P mx → is_Failure mx with
   Failure _ => λ _, ex_intro _ _ eq_refl | Success _ => False_rect _ end).
  set (g mx (H : is_Failure mx) :=
    match H return P mx with ex_intro _ _ p => eq_rect _ _ I _ (eq_sym p) end).
  assert (∀ mx H, f mx (g mx H) = H) as f_g by (by intros ? [??]; subst).
  intros p1 p2. rewrite <-(f_g _ p1), <-(f_g _ p2). by destruct mx, p1.
Qed.
Global Instance is_Success_dec {S} {F} (mx : result F S) : Decision (is_Success mx) :=
  match mx with
  | Success x => left (ex_intro _ x eq_refl)
  | Failure f => right (is_Success_Failure f)
  end.
Global Instance is_Failure_dec {S} {F} (mx : result F S) : Decision (is_Failure mx) :=
  match mx with
  | Failure x => left (ex_intro _ x eq_refl)
  | Success f => right (is_Failure_Success f)
  end.


Definition is_Success_proj {S} {F} {mx : result F S} : is_Success mx → S :=
  match mx with Success x => λ _, x | Failure f => False_rect _ ∘ (is_Success_Failure f) end.

Inductive result_Forall2 {A B } (R: A → B → Prop) {F: Type} : result F A → result F B → Prop :=
  | Some_Forall2 x y : R x y → result_Forall2 R (Success x) (Success y)
  | None_Forall2 : forall f1 f2, result_Forall2 R (Failure f1) (Failure f2).
Arguments result_Forall2 {_ _} _  _ _  _   : assert.
Section Forall2.
  Context {A} (R : relation A).
  Context {F: Type}.

  Global Instance result_Forall2_refl : Reflexive R → Reflexive (result_Forall2 R F).
  Proof. intros ? [?|]; by constructor. Qed.
  Global Instance result_Forall2_sym : Symmetric R → Symmetric (result_Forall2 R F).
  Proof. destruct 2; by constructor. Qed.
  Global Instance result_Forall2_trans : Transitive R → Transitive (result_Forall2 R F).
  Proof. destruct 2; inv 1; constructor; etrans; eauto. Qed.
  Global Instance result_Forall2_equiv : Equivalence R → Equivalence (result_Forall2 R F).
  Proof. destruct 1; split; apply _. Qed.

End Forall2.
Global Instance result_equiv `{Equiv A} {F: Type} : Equiv (result F A) := result_Forall2 (≡) F.

Section setoids.
  Context `{Equiv A}.
  Context {F: Type}.
  Implicit Types mx my : result F A.

  Lemma result_equiv_Forall2 mx my : mx ≡ my ↔ result_Forall2 (≡) F mx my.
  Proof. done. Qed.

  Global Instance result_equivalence :
    Equivalence (≡@{A}) → Equivalence (≡@{result F A}).
  Proof. apply _. Qed.

  Global Instance Success_proper : Proper ((≡) ==> (≡@{result F A})) Success.
  Proof. by constructor. Qed.
  Global Instance Some_equiv_inj : Inj (≡) (≡@{result F A}) Success.
  Proof. by inv 1. Qed.

  Lemma Success_equiv_eq mx y : mx ≡ Success y ↔ ∃ y', mx = Success y' ∧ y' ≡ y.
  Proof. split; [inv 1; naive_solver|naive_solver (by constructor)]. Qed.

End setoids.

Global Typeclasses Opaque result_equiv.

Global Instance result_eq_dec `{dec : EqDecision A} `{dec_F: EqDecision F} : EqDecision (result F A).
Proof.
 refine (λ mx my,
  match mx, my with
  | Success x, Success y => cast_if (decide (x = y))
  | Failure f1, Failure f2 => cast_if (decide(f1=f2))
  | _, _ => right _
  end); clear dec; try abstract congruence.
Defined.

Definition result_map {F S T} (fn: S -> T) (mx: result F S) : result F T :=
  match mx with
  | Success s => Success (fn s)
  | Failure f => Failure f
  end.
Definition get_Success {F S} (r: result F S) : option S :=
  match r with
  | Success s => Some s
  | Failure _ => None
  end.

Definition get_Failure {F S} (r: result F S) : option F :=
  match r with
  | Success s => None
  | Failure f => Some f
  end.

Definition res_from_opt {F S} (o: option S) (f: F): result F S :=
  match o with
  | Some x => Success x
  | None => Failure f
  end.

Definition unpack_result {A} `{MThrow E M, MRet M} (r : result E A) : M A :=
  match r with
  | Success val => mret val
  | Failure err => mthrow err
  end.

(** * Monadic operations *)
Section ResultMonad.
  Context {E: Type}.
  Global Instance result_ret : MRet (result E) := @Success E.
  Global Instance result_throw : MThrow E (result E) := @Failure E.
  Global Instance result_bind : MBind (result E) := fun _ _ f mx =>
    match mx with Success x => f x | Failure f => Failure f end.
  Global Instance result_join : MJoin (result E) := fun _ r =>
    match r with
    | Failure f => Failure f
    | Success (Failure f) => Failure f
    | Success (Success v) => Success v
    end.

  Global Instance result_fmap : FMap (result E) :=
    fun _ _ f r =>
      match r with
      | Success v => Success (f v)
      | Failure e => Failure e
      end.

End ResultMonad.

(* Error map *)
Definition mapE {E E' A} (f: E -> E') (r: result E A) : result E' A :=
  match r with
  | Success v => Success v
  | Failure err => Failure (f err)
  end.

Definition res_opt_bind {A} {B} {C} (res: result B (option A)) (f: A -> result B (option C)) : result B (option C) :=
  match res with
  | Success (Some body) => f body
  | Success None => Success None
  | Failure f => Failure f
  end.


Definition opt_bind_to_res {A B} {C} (c: C) (o: option A) (f: A -> result C (option B)) : result C (option B) :=
  match o with
  | Some x => f x
  | None => Failure c
  end.

Definition option_default {A: Type} (opt_v: option A) (default: A) : A :=
  match opt_v with
  | Some v => v
  | None => default
  end.

Notation "'let/res' var ':=' expr 'in' body" :=
  (match expr with
   | Success var => body
   | Failure f => Failure f
   end)
    (at level 200).

Notation "'let/res2' v1 ',' v2 ':=' expr 'in' body" :=
  (match expr with
   | Success (v1,v2) => body
   | Failure f => Failure f
   end)
    (at level 200).

Notation "'let/res3' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
  (match expr with
   | Success (v1,v2,v3) => body
   | Failure f => Failure f
   end)
    (at level 200).

Notation "'let/opt' v1 ':=' expr 'in' body" :=
  (match expr with
   | Some v1 => body
   | None => None
   end)
    (at level 200).

Notation "'let/opt2' v1 ',' v2 ':=' expr 'in' body" :=
  (match expr with
   | Some (v1, v2) => body
   | None => None
   end)
    (at level 200).

Notation "'let/opt3' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
  (match expr with
   | Some (v1, v2, v3) => body
   | None => None
   end)
    (at level 200).

Notation "'let/opt4' v1 ',' v2 ',' v3 ',' v4 ':=' expr 'in' body" :=
  (match expr with
   | Some (v1, v2, v3, v4) => body
   | None => None
   end)
    (at level 200).

Notation "'let/resopt' var ':=' expr 'in' body" :=
  (res_opt_bind expr (fun var => body)) (at level 200).

Notation "'let/resopt2' v1 ',' v2 ':=' expr 'in' body" :=
  (res_opt_bind expr (fun '(v1, v2) => body)) (at level 200).

Notation "'let/resopt3' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
  (res_opt_bind expr (fun '(v1, v2, v3) => body)) (at level 200).

Notation "'let/resopt4' v1 ',' v2 ',' v3 ',' v4 ':=' expr 'in' body" :=
  (res_opt_bind expr (fun '(v1, v2, v3, v4) => body)) (at level 200).

Notation "'let/optres' var ':=' expr 'in' body" :=
  (opt_bind_to_res tt expr (fun var => body)) (at level 200).

Notation "'let/optres2' v1 ',' v2 ':=' expr 'in' body" :=
  (opt_bind_to_res tt expr (fun '(v1, v2) => body)) (at level 200).

Notation "'let/optres3' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
  (opt_bind_to_res tt expr (fun '(v1, v2, v3) => body)) (at level 200).

Section Lists.
  Import ListNotations.
  Fixpoint map2 {A B C D: Type} (f: A -> B -> C) (l: list A) (l': list B) (err: D): result D (list C) :=
    match l, l' with
    | [], [] =>
      Success []
    | x::tl, y::tl' =>
      let/res tail := map2 f tl tl' err in
      Success ((f x y)::tail)
    | _, _ =>
      Failure err
    end.
End Lists.

(* Section result_list_map. *)
(*   Context {A B F: Type}. *)
(*   Context (f: A -> result F B). *)

(*   (* Written this way to allow use in fixpoints *) *)
(*   Fixpoint result_list_map (la: list A): result F (list B) := *)
(*     mapM f la.  *)

(* End result_list_map. *)

Section result_list_fold.
  Context {A B F: Type}.
  Context (f: A -> B -> result F A).

  Fixpoint result_list_fold_left (lb: list B) (acc: result F A) : result F A :=
    match lb with
    | [] => acc
    | b::lb => let/res acc := acc in
             result_list_fold_left lb (f acc b)
    end.

End result_list_fold.
