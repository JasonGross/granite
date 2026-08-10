From stdpp Require Import base option.
From granite.core Require Import Result.

Ltac destruct_match_pairs :=
  repeat match goal with
         | H: context[let '(_,_) := ?x in _] |- _ =>
           destruct x eqn:?
         | |- context[let '(_,_) := ?x in _] =>
           destruct x eqn:?
         end.
Ltac match_innermost_in H :=
  match type of H with
  | context[match ?E with _ => _ end] =>
    match E with
    | context[match _ with _ => _ end] => fail 1
    | _ => destruct E eqn:?; simpl in *
    end
  end; subst; try congruence; eauto.

Ltac match_innermost_in_goal :=
  match goal with
  | [ |- context[match ?E with _ => _ end] ]=>
    match E with
    | context[match _ with _ => _ end] => fail 1
    | _ => destruct E eqn:?; simpl in *
    end
  end; subst; try congruence; eauto.

Ltac fast_match_innermost_in_goal :=
    match goal with
    | [ |- context[match ?E with _ => _ end] ]=>
      match E with
      | context[match _ with _ => _ end] => fail 1
      | _ => destruct E eqn:?
      end
    end.

Ltac destruct_one_match_in H :=
  lazymatch type of H with
  | context[match ?d with | _ => _ end] =>
      let H1 := fresh H in
      destruct d eqn:H1
  end.

Ltac vm_reflect := vm_compute; reflexivity.
Ltac compute_change t1 t2 :=
  let H := fresh in
  assert (t1 = t2) as H by (vm_reflect); rewrite H in *; clear H.

Ltac get_innermost_match_in_goal :=
  match goal with
  | [ |- context[match ?E with _ => _ end] ]=>
    match E with
    | context[match _ with _ => _ end] => fail 1
    | _ => E
    end
  | [ |- context[res_opt_bind ?E _]] =>
    match E with
    | context[match _ with _ => _ end] => fail 1
    | _ => E
    end

  end.

Ltac get_innermost_match_in_hyp H :=
  match type of H with
  | context[match ?E with _ => _ end] =>
    match E with
    | context[match _ with _ => _ end] => fail 1
    | _ => E
    end
  | context[res_opt_bind ?E _] =>
    match E with
    | context[match _ with _ => _ end] => fail 1
    | _ => E
    end
  end.
Ltac match_outermost_in H :=
  match type of H with
  | context[match ?x with | _ => _ end] =>
      match x with
      | @bool_decide ?P ?dec =>
          let Hd := fresh in 
          destruct_decide (@bool_decide_reflect P dec) as Hd
      | @decide ?P ?dec =>
          let Hd := fresh in 
          destruct_decide (@decide P dec) as Hd
      | _ => destruct x eqn:?
      end
  end.

Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
      destruct_matches_in d
  | _ =>
      destruct e eqn:?(* ; intros *)
  end.

Ltac destruct_matches_in_as H e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
      destruct_matches_in_as H d
  | _ =>
      destruct e eqn:H(* ; intros *)
  end.

Ltac destruct_matches_in_hyp_as H Hnew :=
  lazymatch type of H with
  | context [ match ?d with
              | _ => _
              end ] => destruct_matches_in_as Hnew d
  | ?v =>  destruct v eqn:Hnew
  end.

Ltac destruct_matches_in_hyp H :=
  lazymatch type of H with
  | context[match ?d with | _ => _ end] =>
      destruct_matches_in d
  | ?v =>
      let H1 := fresh H in
      destruct v eqn:H1(* ; intros *)
  end.



Ltac simpl_match :=
  let repl_match_goal d d' :=
      replace d with d';
      lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      | _ => idtac
      end in
  let repl_match_hyp H d d' :=
      replace d with d' in H;
      lazymatch type of H with
      | context[match d' with _ => _ end] => fail
      | _ => idtac
      end in
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
      repl_match_goal d d'
  | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
      repl_match_goal d d'
  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
      repl_match_hyp H d d'
  | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
      repl_match_hyp H d d'
  end.
Ltac dep_simpl_match :=
  let check_match_goal d d' :=
      lazymatch goal with
      | [ |- context[match d' return _ with _ => _ end] ] => fail
      | _ => idtac
      end in
  let check_match_hyp H d d' :=
      lazymatch type of H with
      | context[match d' return _ with _ => _ end] => fail
      | _ => idtac
      end in
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d return _ with _ => _ end] ] =>
      setoid_rewrite Heq;
      check_match_goal d d'
  | [ Heq: ?d' = ?d |- context[match ?d return _ with _ => _ end] ] =>
      setoid_rewrite<-Heq;
      check_match_goal d d' 
  | [ Heq: ?d = ?d', H: context[match ?d return _ with _ => _ end] |- _ ] =>
      setoid_rewrite Heq in H;
      check_match_hyp H d d'
  | [ Heq: ?d' = ?d, H: context[match ?d return _ with _ => _ end] |- _ ] =>
      setoid_rewrite<-Heq in H;
      check_match_hyp H d d'
  end.

Ltac destruct_all_matches :=
  repeat (try simpl_match;
          try match goal with
              | [ |- context[match ?d with | _ => _ end] ] =>
                  destruct_matches_in d
              | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                  destruct_matches_in d
              end);
  subst;
  try congruence;
  auto.

Ltac destruct_all_matches_in_hyps :=
  repeat (try simpl_match;
          try match goal with
              | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                  destruct_matches_in d
              end);
  subst;
  auto.

Ltac rewrite_solve :=
  match goal with
  | [ H: _ |- _ ] => solve[rewrite H; try congruence; auto]
  end.

Tactic Notation "assert_length_match_eq" "as" ident(H) :=
  match goal with
  | |- match ?s with | [] => _ | _ => _ end =
       match ?t with | [] => _ | _ => _ end =>
      assert (length s = length t) as H
  end.

Ltac split_ors_in H:=
  repeat match type of H with
  | _ \/ _ =>
    destruct H as [H | H]; split_ors_in H
  end.
Lemma simple_tuple_inversion:
  forall {A} {B} (a: A) (b: B) x y,
  (a,b) = (x,y) ->
  a = x /\ b = y.
Proof.
  intros. inversion H. auto.
Qed.

Ltac simplify_tuples :=
  repeat match goal with
  | [ H: (_,_) = (_,_) |- _ ] =>
      let H1 := fresh H in
      let H2 := fresh H in
    apply simple_tuple_inversion in H; destruct H as [H1 H2]
  end.

Ltac simplify_tupless := simplify_tuples; subst.
Ltac propositional_with t :=
  repeat match goal with
  | [ H : _ /\ _  |- _ ] =>
      let H1 := fresh H in
      let H2 := fresh H in
      destruct H as [H1 H2]
  | [ H : _ <-> _  |- _ ] =>
      let H1 := fresh H in
      let H2 := fresh H in
      destruct H as [H1 H2]
  | |- forall _, _ => intros
  | [ H: False |- _ ] => solve [ destruct H ]
  | [ |- True ] => exact I
  | [ H : exists (varname: _ ), _ |- _ ] =>
      let newvar := fresh varname in
      let Hpref  := fresh H in
      destruct H as [newvar Hpref]
  | [ H: ?P -> _ |- _ ] =>
    lazymatch type of P with
    | Prop => match goal with
          | [ H': P |- _ ] => specialize (H H')
          | _ => specialize (H ltac:(try t))
          end
    end
  | [ H: forall x, x = _ -> _ |- _ ] =>
    specialize (H _ eq_refl)
  | [ H: forall x, _ = x -> _ |- _ ] =>
    specialize (H _ eq_refl)
  | [ H: exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]
  | [ H: ?P |- ?P ] => exact H
  | _ => progress subst
  | _ => solve [ t ]
  end.

Tactic Notation "propositional" := propositional_with auto.
Tactic Notation "propositional" tactic(t) := propositional_with t.

Ltac safe_propositional_with t :=
  repeat match goal with
  | [ H : _ /\ _  |- _ ] =>
      let H1 := fresh H in
      let H2 := fresh H in
      destruct H as [H1 H2]
  | [ H : _ <-> _  |- _ ] =>
      let H1 := fresh H in
      let H2 := fresh H in
      destruct H as [H1 H2]
  | |- forall _, _ => intros
  | [ H: False |- _ ] => solve [ destruct H ]
  | [ |- True ] => exact I
  | [ H : exists (varname: _ ), _ |- _ ] =>
      let newvar := fresh varname in
      let Hpref  := fresh H in
      destruct H as [newvar Hpref]
  | [ H: ?P -> _ |- _ ] =>
    lazymatch type of P with
    | Prop => match goal with
          | [ H': P |- _ ] => specialize (H H')
          | _ => specialize (H ltac:(try t))
          end
    end
  (* | [ H: forall x, x = _ -> _ |- _ ] => *)
  (*   specialize (H _ eq_refl) *)
  (* | [ H: forall x, _ = x -> _ |- _ ] => *)
  (*   specialize (H _ eq_refl) *)
  | [ H: exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]
  | [ H: ?P |- ?P ] => exact H
  | _ => progress subst
  | _ => solve [ t ]
  end.

Tactic Notation "safe_propositional" := safe_propositional_with auto.
Tactic Notation "safe_propositional" tactic(t) := safe_propositional_with t.
Definition ltac_something (P:Type) (e:P) := e.

Notation "'Something'" :=
  (@ltac_something _ _).

Lemma ltac_something_eq : ∀(e:Type),
  e = (@ltac_something _ e).
Proof. auto. Qed.

Lemma ltac_something_hide : ∀(e:Type),
  e → (@ltac_something _ e).
Proof. auto. Qed.

Lemma ltac_something_show : ∀(e:Type),
  (@ltac_something _ e) → e.
Proof. auto. Qed.

Tactic Notation "hide_def" hyp(x) :=
  let x' := constr:(x) in
  let T := eval unfold x in x' in
  change T with (@ltac_something _ T) in x.

Tactic Notation "show_def" hyp(x) :=
  let x' := constr:(x) in
  let U := eval unfold x in x' in
  match U with @ltac_something _ ?T =>
    change U with T in x end.
Tactic Notation "show_def" :=
  unfold ltac_something.

Tactic Notation "show_def" "in" "*" :=
  unfold ltac_something in *.

Tactic Notation "hide_defs" :=
  repeat match goal with H := ?T |- _ =>
    match T with
    | @ltac_something _ _ => fail 1
    | _ => change T with (@ltac_something _ T) in H
    end
  end.
Tactic Notation "show_hyp" hyp(H) :=
  apply ltac_something_show in H.

Tactic Notation "hide_hyp" hyp(H) :=
  apply ltac_something_hide in H.
Tactic Notation "show_hyps" :=
  repeat match goal with
    H: @ltac_something _ _ |- _ => show_hyp H end.

Tactic Notation "hide_hyps" :=
  repeat match goal with H: ?T |- _ =>
    match type of T with
    | Prop =>
      match T with
      | @ltac_something _ _ => fail 2
      | _ => hide_hyp H
      end
    | _ => fail 1
    end
  end.
Tactic Notation "show_defs" :=
  repeat match goal with H := (@ltac_something _ ?T) |- _ =>
    change (@ltac_something _ T) with T in H end.
Tactic Notation "hide" hyp(H) :=
  first [hide_def H | hide_hyp H].

Tactic Notation "show" hyp(H) :=
  first [show_def H | show_hyp H].

Tactic Notation "hide_all" :=
  hide_hyps; hide_defs.

Tactic Notation "show_all" :=
  unfold ltac_something in *.
Tactic Notation "hide_term" constr(E) :=
  change E with (@ltac_something _ E).
Tactic Notation "show_term" constr(E) :=
  change (@ltac_something _ E) with E.
Tactic Notation "show_term" :=
  unfold ltac_something.

Tactic Notation "hide_term" constr(E) "in" hyp(H) :=
  change E with (@ltac_something _ E) in H.
Tactic Notation "show_term" constr(E) "in" hyp(H) :=
  change (@ltac_something _ E) with E in H.
Tactic Notation "show_term" "in" hyp(H) :=
  unfold ltac_something in H.

Ltac destruct_tuples :=
  match goal with
  | H: _ * _ |- _ => destruct H
  end.
Ltac bash_destruct H :=
    repeat destruct_matches_in_hyp H; simpl in H; simplify_tupless; try (contradiction || congruence).
Tactic Notation "case_match_in" ident(H) "eqn" ":" ident(Hd) :=
  match type of H with
  | context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  end.
Tactic Notation "case_match_in" ident(H) "eqn" ":" ident(Hd) :=
  match type of H with
  | context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  end.

Tactic Notation "case_goal_match" "eqn" ":" ident(Hd) :=
  match goal with
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  end.
Tactic Notation "case_goal_match"  :=
  match goal with
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:?
  end.
Ltac get_outermost_match_in_goal :=
  match goal with
  | [ |- context[match ?E with _ => _ end] ]=>
      E
  end.
Ltac option_simpl :=
  repeat match goal with
  | H: Some _  = Some _ |- _ => apply Some_inj in H
  | H: mret _  = Some _ |- _ => apply Some_inj in H
  | H : mfail = Some _ |- _ => clear - H; inversion H
  | H : None = Some _ |- _ => clear - H; discriminate
  end.
Ltac simplify_match_term t :=
  match t with
  | map _ ?x =>
      match goal with
      | H: ?x = _ |- _ => rewrite  H
      end
  | ?x && _ =>
      match goal with
      | H: ?x = false |- _ => rewrite H
      | H: ?x = true |- _ => rewrite H
      end
  | negb ?x =>
      match goal with
      | H: ?x = false |- _ => rewrite H
      | H: ?x = true |- _ => rewrite H
      end
  end.
Ltac simplify_match :=
  let t := get_outermost_match_in_goal in
  simplify_match_term t.

Ltac simplify_eqs :=
  repeat match goal with
  | H: ?x = _ ,
    H1: ?x = _ |- _ =>
      rewrite H in H1; clear H
  | _ => progress simplify_tupless
  end.

Ltac assert_pre H :=
  match type of H with
  | ?x -> _ => assert x
  end.

Ltac assert_pre_as Hnew H :=
  match type of H with
  | ?x -> _ => assert x as Hnew
  end.

Ltac assert_pre_and_specialize H :=
  match type of H with
  | ?x -> _ =>
    let Hnew := fresh in
    assert x as Hnew; [ | specialize H with (1 := Hnew); clear Hnew]
  end.
Ltac destruct_pairs :=
  repeat match goal with
  | H: _ * _ |- _ => destruct H
  end.

Ltac consider H :=
  unfold H in *.
Ltac option_helper :=
  match goal with
  | H : Some _ = Some _ |- _ => apply (inj Some) in H
  end.
  Ltac assert_left_as H :=
    match goal with
    | |- ?t /\ _ => assert t as H; [ | split; auto]
    end.
  Ltac assert_right_as H :=
    match goal with
    | |- _ /\ ?x => assert x as H; [ | split; auto]
    end.

  Ltac inversions H :=
    inversion H; subst; clear H.
  Ltac destruct_match_pairs' :=
    repeat
     match goal with
     | H:context [ let '(_, _) := ?x in _ ] |- _ =>
         let H' := fresh H in destruct x eqn:H'
     | |- context [ let '(_, _) := ?x in _ ] => destruct x eqn:?
     end.
