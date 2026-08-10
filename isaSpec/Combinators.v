From Stdlib Require Import Lia.
From granite.core Require Import
  Tactics.                   
Section Combinators.

  Context [State: Type] (step: State -> (State -> Prop) -> Prop).

  Inductive eventually(P: State -> Prop)(initial: State): Prop :=
    | eventually_done:
        P initial ->
        eventually P initial
    | eventually_step: forall midset,
        step initial midset ->
        (forall mid, midset mid -> eventually P mid) ->
        eventually P initial.

  Hint Constructors eventually : eventually_hints.

  Lemma eventually_trans: forall P Q initial,
    eventually P initial ->
    (forall middle, P middle -> eventually Q middle) ->
    eventually Q initial.
  Proof.
    induction 1; eauto with eventually_hints.
  Qed.

  Hint Resolve eventually_trans : eventually_hints.

  Lemma eventually_weaken: forall (P Q : State -> Prop) initial,
    eventually P initial ->
    (forall final, P final -> Q final) ->
    eventually Q initial.
  Proof.
    eauto with eventually_hints.
  Qed.

  Lemma eventually_step_cps: forall initial P,
      step initial (eventually P) ->
      eventually P initial.
  Proof. intros. eapply eventually_step; eauto. Qed.

  Lemma eventually_trans_cps: forall (Q : State -> Prop) (initial : State),
      eventually (eventually Q) initial ->
      eventually Q initial.
  Proof.
    intros. eapply eventually_trans; eauto.
  Qed.

  Inductive always(P: State -> Prop)(initial: State): Prop :=
  | mk_always
      (invariant: State -> Prop)
      (Establish: invariant initial)
      (Preserve: forall s, invariant s -> step s invariant)
      (Use: forall s, invariant s -> P s).

  Context (step_weaken: forall s P Q, (forall x, P x -> Q x) -> step s P -> step s Q).

  Lemma hd_always: forall P initial, always P initial -> P initial.
  Proof. inversion 1. eauto. Qed.

  Lemma tl_always: forall P initial, always P initial -> step initial (always P).
  Proof. inversion 1. eauto using mk_always. Qed.

  Lemma always_elim: forall P initial,
    always P initial -> P initial /\ step initial (always P).
  Proof. split; [apply hd_always | apply tl_always]; assumption. Qed.

  (* Not a very useful intro rule because it already requires an `always` in a
     hypothesis. Typically, one would use `mk_always` instead and provide an invariant.
     But if the first step is somehow special, and the invariant only holds after that
     first step, this rule might be handy. *)
  Lemma always_intro: forall P initial,
      P initial ->
      step initial (always P) ->
      always P initial.
  Proof.
    intros. eapply mk_always with (invariant := fun s => P s /\ step s (always P)).
    - auto.
    - intros * [Hd Tl]. eapply step_weaken. 2: exact Tl. 1: apply always_elim.
    - intros * [Hd Tl]. assumption.
  Qed.

  Lemma always_unfold1: forall P initial,
    always P initial <-> P initial /\ step initial (always P).
  Proof.
    split.
    - apply always_elim.
    - intuition eauto using always_intro.
  Qed.

  (* Don't need a projection for Q, turn off the warning. *)
  #[warnings="-cannot-define-projection"]
  CoInductive always' (P : State -> Prop) s : Prop := always'_step {
    hd_always' : P s; Q ; _ : step s Q; _ s' : Q s' -> always' P s' }.

  CoFixpoint always'_always P s : always P s -> always' P s.
  Proof. inversion 1; esplit; eauto using mk_always. Qed.

  Lemma tl_always' P s : always' P s -> step s (always' P).
  Proof. inversion 1; eauto. Qed.

  Lemma always_always' P s : always' P s -> always P s.
  Proof. exists (always' P); try inversion 1; eauto. Qed.

  Fixpoint after_n (fuel: nat) (post: State -> Prop) (st: State) : Prop :=
    match fuel with
    | 0%nat => post st 
    | S fuel => after_n fuel (fun st' => step st' post) st
    end.

  Fixpoint forall_n_steps (fuel: nat) (inv: State -> Prop) (st: State) : Prop :=
    match fuel with
    | 0%nat => inv st 
    | S fuel => forall_n_steps fuel (fun st' => inv st' /\ step st' inv) st
    end.

  Lemma forall_n_weaken:
    forall n (st: State) (P Q: State -> Prop),
    (forall x, P x -> Q x) ->
    forall_n_steps n P st ->
    forall_n_steps n Q st.
  Proof.
    induction n; cbn; auto.
    intros. 
    eapply IHn; eauto. cbn.
    propositional.
    split; auto.
    eapply step_weaken; eauto.
  Qed.

  Lemma forall_n_implies_after_n :
    forall n n' st post,
      n' <= n ->
      forall_n_steps n post st->
      after_n n' post st.
  Proof.
    induction n; auto.
    - intros. destruct n'; try lia. auto.
    - intros * hlt hforall.
      cbn in hforall.
      destruct (Nat.eqb n' (S n)) eqn:Heqb.
      { apply PeanoNat.Nat.eqb_eq in Heqb. subst.
        cbn.
        apply IHn; try lia.
        eapply forall_n_weaken; eauto. cbn. propositional.
      }
      { apply PeanoNat.Nat.eqb_neq in Heqb.
        apply IHn; try lia.
        eapply forall_n_weaken.
        2: { apply hforall. }
        cbn. propositional.
      }
  Qed.

  Lemma after_Sn:
    forall n post st,
    after_n (S n) post st <->
    step st (fun st' => after_n n post st').
  Proof.
    induction n; auto.
    cbn. intros. split.
    - intros. apply IHn. auto.
    - intros. apply IHn. auto.
  Qed.

  Lemma eventually_after_n:
    forall n st post, 
      after_n n post st ->
      eventually post st.
  Proof.
    induction n; cbn; intros * hn.
    - apply eventually_done; auto.
    - setoid_rewrite after_Sn in hn.
      eapply eventually_step; eauto.
  Qed.

  Lemma after_n_weaken:
    forall n (st: State) (P Q: State -> Prop),
    (forall x, P x -> Q x) ->
    after_n n P st ->
    after_n n Q st.
  Proof.
    induction n; cbn; auto.
    intros. eapply IHn; eauto. cbn. intros; eauto.
  Qed.

End Combinators.
