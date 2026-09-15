From stdpp Require Import base tactics.
From RecordUpdate Require Import RecordSet.
From granite.core Require Import
  Bits
  Object
  Pair
  Program
  ProgramOps
  ProgramTactics
  Reg
  Simulates
  Tactics
  Trace 
  TraceFacts
  Utils.
From granite.core Require PairFacts.
From granite.app Require Import
  MultiplierAPI 
  Multiplier  
  MultiplierSpec.
Import RecordSetNotations.
From quartz.lang Require domain.
Import domain.Zmod.
Section WithContext.
  Context {params: Params.Params}.
  Context {implParams: MultiplierParams}.

  Notation concrete_spec := Multiplier.multiplier_spec.
  Notation impl_st_t := Multiplier.St.

   Definition evalITrace (tr: trace_t) : impl_st_t := 
    execTrace concrete_spec (map (CallEvent) tr) 
              concrete_spec.(initialState).

   Definition lift_leakage_event (ev: LeakEvent) : ActionMethod unit :=
     match ev with
     | LeakEnq zero_arg =>
         Enq (if zero_arg then 
                {| input_a := zeroes; input_b := zeroes |}
              else 
                {| input_a := bits.of_Z _ 1; input_b := bits.of_Z _ 1 |}
             )                     
     | LeakDeq => Deq 
     | LeakTick => Tick
     end.

   Definition evalLeakageTrace (tr: leakage_trace_t) : impl_st_t :=
     evalITrace (map lift_leakage_event tr).

   Definition default_peek (tr: trace_t) : bits (Params.width + Params.width) :=
     let st := evalITrace tr in
     (concrete_spec.(EvalVMethod) (Peek) st). 
   Definition resp_ready (leakage: leakage_trace_t) : bool :=
     let st: impl_st_t := evalLeakageTrace leakage in 
      (concrete_spec.(EvalVMethod) (RespReady) st). 

   Definition is_full (leakage: leakage_trace_t) : bool :=
     let st := evalLeakageTrace leakage in 
      (concrete_spec.(EvalVMethod) (Full) st). 
 
   #[export] Instance multiplierParams : SpecParams :=  
     {| MultiplierSpec.default_peek := default_peek;
        MultiplierSpec.resp_ready := resp_ready;
        MultiplierSpec.is_full := is_full
     |}.
   Notation abstract_spec := MultiplierSpec.spec.
   Notation spec_st_t := (State abstract_spec).

   (* Run the spec machine *)
   Definition evalSTrace (tr: trace_t) := 
    execTrace abstract_spec (map (CallEvent) tr) 
              abstract_spec.(initialState).

   Record RelBase (impl: State concrete_spec) (spec: spec_st_t) :=
     { impl_hist_rel: evalITrace spec.(hist) = impl
     ; spec_hist_rel: evalSTrace spec.(hist) = spec
     }.                                                          

   Definition SignalsEq (impl pubImpl: impl_st_t) :=
     impl.(Valid) = pubImpl.(Valid) /\
     impl.(Nstep) = pubImpl.(Nstep) /\
     impl.(Finished) = pubImpl.(Finished).

   Notation PubImpl spec :=
     (evalLeakageTrace (leakage spec.(hist)):St).

   Definition shortCircuitEq (impl pubImpl: St) :=
     (impl.(Op1) = zeroes \/ impl.(Op2) = zeroes ) <->
     (pubImpl.(Op1) = zeroes \/ pubImpl.(Op2) = zeroes).

   Inductive RelCore (impl: St) (spec: spec_st_t) : Prop :=
   | CaseEmpty (pfINotValid: impl.(Valid) = false)
               (pfINotFinished: impl.(Finished) = false)
               (pfSEmpty: spec.(reqs) = [])
               (pfSignalsEq: SignalsEq impl (PubImpl spec))
   | CaseBusy  (pfIValid: impl.(Valid) = true)
               (pfINotFinished: impl.(Finished) = false)
               (pfReq: spec.(reqs) = [Build_req_t impl.(Op1) impl.(Op2)] )
               (pfLeakage: let pubImpl := PubImpl spec in 
                           SignalsEq impl pubImpl /\ 
                           shortCircuitEq impl pubImpl
               )
   | CaseFinished (pfIValid: impl.(Valid) = true)
                  (pfIFinished: impl.(Finished) = true)
                  (pfReq: exists req, spec.(reqs) = [req] /\ impl.(Result) = handle_req req)
                  (pfSignalsEq: SignalsEq impl (PubImpl spec))
   .
   Record Rel (impl: St) (spec: spec_st_t) : Prop :=
     { Rel_base: RelBase impl spec;
       Rel_core: RelCore impl spec
     }.

   Lemma Rel_init : Rel (initialState concrete_spec) (initialState abstract_spec).
   Proof.
     constructor; cbn; constructor; cbn; auto. 
     unfold SignalsEq; auto.
   Qed.

   (* Arguments St_of_prod: simpl never. *)
   Open Scope prog_scope.

   Ltac start_value_method := 
     intros s1 s2 * Rel *; pose proof Rel as rel; inv rel; cbn.    
   Lemma RelImplSignalsEq:
     forall s1 s2,
     Rel s1 s2 ->
     SignalsEq s1 (PubImpl s2).
   Proof.
     intros * rel. apply Rel_core in rel.
     destruct rel; cbn in *; propositional.
   Qed.

   Lemma resp_ready_eq (leakage_tr : leakage_trace_t) :
     resp_ready leakage_tr = (evalLeakageTrace leakage_tr).(Finished).
   Proof.
     unfold resp_ready. cbn. apply nonzero_bool.
   Qed.

   Lemma is_full_eq (leakage_tr : leakage_trace_t) :
     is_full leakage_tr = (evalLeakageTrace leakage_tr).(Valid).
   Proof.
     unfold is_full. cbn. apply nonzero_bool.
   Qed.

   Lemma default_peek_eq (tr : trace_t) :
     default_peek tr = (evalITrace tr).(Result).
   Proof.
     unfold default_peek. cbn. reflexivity.
   Qed.

   Create HintDb mul.
   Lemma evalITrace_app:
     forall xs ys,
     evalITrace (xs ++ ys) = 
     Trace.execTrace concrete_spec (map (CallEvent) ys)
               (evalITrace xs).
   Proof.
     intros; unfold evalITrace. rewrite execTrace_mapApp. reflexivity.
     (* rewrite St_from_to. reflexivity. *)
   Qed.
   Lemma evalSTrace_app:
     forall xs ys,
     evalSTrace (xs ++ ys) =
     Trace.execTrace abstract_spec (map (CallEvent) ys)
               (evalSTrace xs).
   Proof.
     intros; unfold evalSTrace. rewrite execTrace_mapApp. auto.
   Qed.
   Hint Rewrite evalITrace_app :  mul.
   Hint Rewrite evalSTrace_app :  mul.
   Hint Rewrite @execTrace_mapApp : mul.

   Hint Rewrite map_app: mul.

   Lemma evalLeakageTrace_app:
     forall xs ys,
     evalLeakageTrace (xs ++ ys) =
     Trace.execTrace concrete_spec 
       (map (CallEvent) (map lift_leakage_event ys))
       (evalLeakageTrace xs).
   Proof.
     intros; unfold evalLeakageTrace. 
     unfold evalITrace. rewrite map_app. rewrite map_app. 
     rewrite execTrace_app. rewrite map_map. auto.
     (* rewrite St_from_to. auto. *)
   Qed.
   Hint Rewrite @evalLeakageTrace_app : mul.
   Hint Rewrite resp_ready_eq : mul.
   Hint Rewrite is_full_eq : mul.

   Ltac mul_simplify :=
     repeat match goal with
     | H: RelBase _ ?s2 |- context[evalITrace (hist ?s2)] =>
           rewrite impl_hist_rel with (1 := H)
     | H: RelBase _ ?s2 
       |- context[evalSTrace (hist ?s2)] =>
       setoid_rewrite spec_hist_rel with (1 := H)
     | H: ?x _ = ?x (evalLeakageTrace _) |- context[?x (evalLeakageTrace _)] => setoid_rewrite<-H
     | H : () |- _ => destruct H
     | H : ?x = ?x |- _ => clear H
     | _ => progress (repeat simpl_match; auto)
     end.

   Ltac mul_simp :=
     repeat progress (cbn in *; propositional; mul_simplify; autorewrite with mul).

   Ltac simp_signalsEq :=
     mul_simp; repeat dep_simpl_match; repeat simpl_match; consider SignalsEq; mul_simp.

   Lemma respReady_Bool_eq (s1 : impl_st_t) (s2 : spec_st_t) :
     Rel s1 s2 ->
     s1.(Finished) = MultiplierSpec.respReady s2.
   Proof.
     intros Hrel. inv Hrel.
     unfold MultiplierSpec.respReady.
     inv Rel_core0.
     - (* CaseEmpty: reqs = [], Finished = false *)
       rewrite pfSEmpty. exact pfINotFinished.
     - (* CaseBusy: reqs = [_], Finished = false *)
       rewrite pfReq. cbn. rewrite resp_ready_eq.
       mul_simp; simp_signalsEq.
     - (* CaseFinished: reqs = [req], Finished = true *)
       destruct pfReq as [req [-> _]]. cbn. rewrite resp_ready_eq.
       simp_signalsEq.
   Qed.

   Lemma full_Bool_eq (s1 : impl_st_t) (s2 : spec_st_t) :
     Rel s1 s2 ->
     s1.(Valid) = MultiplierSpec.full s2.
   Proof.
     intros Hrel.
     unfold MultiplierSpec.full.
     rewrite is_full_eq.
     exact (proj1 (RelImplSignalsEq _ _ Hrel)).
   Qed.

   Lemma peek_eq (s1 : impl_st_t) (s2 : spec_st_t) :
     Rel s1 s2 ->
     s1.(Result) = MultiplierSpec.peek s2.
   Proof.
     intros Hrel. inv Hrel.
     unfold MultiplierSpec.peek.
     rewrite resp_ready_eq.
     inv Rel_core0; simp_signalsEq.
   Qed.

   Lemma RespReadyOk:
     forall (s1: impl_st_t) s2,
     Rel s1 s2 ->
     EvalVMethod concrete_spec (RespReady) s1 =
       EvalVMethod abstract_spec (RespReady) s2.
   Proof.
     intros s1 s2 Hrel. cbn.
     f_equal.
     exact (respReady_Bool_eq s1 s2 Hrel).
   Qed.

   Lemma FullOk:
     forall (s1: impl_st_t) s2,
     Rel s1 s2 ->
     EvalVMethod concrete_spec (Full) s1 =
       EvalVMethod abstract_spec (Full) s2.
   Proof.
     intros s1 s2 Hrel. cbn.
     f_equal.
     exact (full_Bool_eq s1 s2 Hrel).
   Qed.

   Lemma PeekOk:
     forall (s1: impl_st_t) s2,
     Rel s1 s2 ->
     EvalVMethod concrete_spec (Peek) s1 =
       EvalVMethod abstract_spec (Peek) s2.
   Proof.
     intros s1 s2 Hrel. cbn.
     exact (peek_eq s1 s2 Hrel).
   Qed.

   Ltac start_action_method :=
     intros s1 s1' r s2 * Rel *; pose proof Rel as rel; inv rel;
     cbn; intros himpl; mul_simplify;
     eexists; split; simplify_tupless; eauto;
     unfold set; cbn.

   Arguments evalSTrace : simpl never.
   Arguments evalITrace : simpl never.

   Lemma one_neq_zero:
     forall n,
     (n <> 0)%Z ->
     bits.of_Z n 1 = (zeroes : bits n) ->
     False.
   Proof.
     intros n H H0. apply (f_equal Zmod.unsigned) in H0.
     rewrite unsigned_literal, Zmod.unsigned_of_Z in H0.
     destruct (Z.le_gt_cases 1 n) as [Hn|Hn].
     - rewrite Z.mod_small in H0; [lia | pose proof (proj1 (Z.pow_gt_1 2 n ltac:(lia)) ltac:(lia)); lia].
     - rewrite Z.pow_neg_r, Z.mod_0_r in H0; lia.
   Qed.
   Lemma EnqOk:
     forall (s1 s1': impl_st_t) r s2 arg,
     Rel s1 s2 ->
     EvalMethod concrete_spec ((Enq arg)) s1 = (r, s1')
     → ∃ s2' : spec_st_t,
         EvalMethod abstract_spec ((Enq arg)) s2 = (r, s2')
         ∧ Rel s1' s2'.
   Proof.
     start_action_method.
     constructor.
     - constructor; cbn; mul_simp; unfold snd, set; mul_simp.
     - mul_simp. destruct s2. unfold enq; cbn.
       inv Rel_core0; dep_simpl_match;
         consider SignalsEq; destruct s1; mul_simp;
         simplify_tupless; mul_simp.
       + (* Empty → Busy *)
         apply CaseBusy; cbn; eauto.
         { destruct arg; eauto. }
         { mul_simp. simp_signalsEq.
           unfold shortCircuitEq. cbn.
           case_bool_decide as Hzero_arg; cbn; auto; repeat split; try by auto.
           intros HFalse. split_ors_in HFalse; apply one_neq_zero in HFalse; try by auto.
           all: apply Params.pfWidthNeZero.
         }
       + (* Busy → Busy *)
         apply CaseBusy; cbn; eauto. split.
         { simp_signalsEq. }
         { simp_signalsEq. }
       + (* Finished → Finished *)
         apply CaseFinished; cbn; eauto.
         simp_signalsEq.
   Qed.

   Lemma DeqOk:
     forall s1 r (s1': impl_st_t) s2,
     Rel s1 s2 ->
     EvalMethod concrete_spec (Deq) s1 = (r, s1')
     → ∃ s2' : spec_st_t,
         EvalMethod abstract_spec (Deq) s2 = (r, s2')
         ∧ Rel s1' s2'.
   Proof.
     start_action_method.
     constructor.
     - constructor; cbn; mul_simp; unfold snd, set; mul_simp.
     - mul_simp. destruct s2. unfold deq; cbn.
       inv Rel_core0; dep_simpl_match;
         consider SignalsEq; destruct s1; mul_simp;
         simplify_tupless; mul_simp.
       + apply CaseEmpty; cbn in *; simp_signalsEq.
       + apply CaseBusy; cbn in *; simp_signalsEq.
       + apply CaseEmpty; cbn in *; simp_signalsEq.
   Qed.
   
   Lemma unfold_match_andb:
     forall b1 b2 {A} (x y: A),
     (if b1 && b2 then x else y) =
     (if b1 then if b2 then x else y else y).                            
   Proof.
     intros. destruct b1; auto.
   Qed.
   
   Lemma unfold_match_negb:
     forall b1 {A} (x y: A),
     (if negb b1 then x else y) =
     (if b1 then y else x).                            
   Proof.
     intros. destruct b1; auto.
   Qed.

   Create HintDb progStep.
   Hint Rewrite unfold_match_andb: progStep.
   Hint Rewrite unfold_match_negb: progStep.

   Lemma bv_mul'_zero:
     forall m n (op1 op2: bits n),
     op1 = zeroes \/ op2 = zeroes ->
     bv_mul' m op1 op2 = zeroes.
   Proof.
     intros. unfold bv_mul'. apply Zmod.unsigned_inj.
     rewrite Zmod.unsigned_of_Z, !unsigned_literal.
     destruct H; subst; rewrite unsigned_literal, ?Z.mul_0_l, ?Z.mul_0_r.
     all: destruct (Z.eq_dec (2^m) 0) as [->|]; [apply Z.mod_0_r | apply Z.mod_0_l; assumption].
   Qed.

   Lemma TickOk:
     forall s1 r (s1': impl_st_t) s2 ,
     Rel s1 s2 ->
     EvalMethod concrete_spec (Tick) s1 = (r, s1')
     → ∃ s2' : spec_st_t,
         EvalMethod abstract_spec (Tick) s2 = (r, s2')
         ∧ Rel s1' s2'.
   Proof.
     start_action_method.
     constructor.
     - constructor; mul_simp; unfold set; cbn; mul_simp.
       set (evalProg _ _ _) in *. destruct p; simplify_tupless; auto.
     - mul_simp. 
       destruct s2. unfold tick; cbn.
       rewrite unfold_match_andb in *.
       inv Rel_core0; simp_signalsEq; destruct s1; simplify_tupless; mul_simp.
       
       + (* Empty *)
         apply CaseEmpty; cbn; auto. mul_simp. rewrite unfold_match_andb.
         case_match eqn:Hvalid; [congruence | ]. cbn.
         simp_signalsEq.
       + (* Busy *) 
         
         case_decide as hshort; mul_simp; simplify_tupless; mul_simp.
         * apply CaseFinished; cbn; eauto. 
           { eexists; split; eauto. unfold handle_req.
             by rewrite bv_mul'_zero.
           }
           { mul_simp. autorewrite with progStep.
             repeat simpl_match. cbn. 
             consider shortCircuitEq. cbn in *. 
             case_decide as Hzeroes; [ propositional; done | ].
             case_decide as Hnstep; propositional; done.
           } 
         * case_decide as hnstep; mul_simp; simplify_tupless; mul_simp.
           { apply CaseFinished; cbn; eauto. mul_simp; autorewrite with progStep.
             repeat simpl_match. 
             consider shortCircuitEq. cbn in *. 
             case_decide as Hzeroes; [ propositional; done | ].
             case_decide as Hnstep; done.
           }
           { apply CaseBusy; cbn; eauto.
             mul_simp.
             autorewrite with progStep.
             repeat simpl_match. cbn.
             consider shortCircuitEq. cbn in *. 
             case_decide as Hzeroes; [ propositional; done | ].
             case_decide as Hnstep; propositional; done.
           }
       + (* Finished *) 
         simplify_tupless. mul_simp.
         apply CaseFinished; cbn; eauto. mul_simp.
         rewrite unfold_match_andb.
         case_match eqn:Hvalid; [ | congruence].
         rewrite unfold_match_negb.
         case_match eqn:Hfinish; [ | congruence ].
         cbn. simp_signalsEq. 
   Qed.

   Theorem refines :
     refines concrete_spec abstract_spec Rel.
   Proof.
     cbv[refines]. intros * Rel *. 
     split.
     - destruct vmethod.
       + by apply RespReadyOk.
       + by apply FullOk.
       + by apply PeekOk.
     - destruct method; intros.
       + by eapply EnqOk. 
       + by eapply DeqOk.
       + by eapply TickOk.
   Qed.

   Corollary simulates :
     simulates concrete_spec abstract_spec. 
   Proof.
     unfold simulates. exists Rel.
     split; [by apply Rel_init | by apply refines].
   Qed.
    
End WithContext.
