(*! Connection between riscv-coq's omnisemantics and granite's reference semantics.

    This file only STATES the theorems we expect to prove once the open issues of
    mit-plv/granite#1 are resolved.  Every non-trivial proof is [Admitted] by
    design.  The open issues are named [Hypothesis] parameters of the sections
    below so that they can be discharged one by one later.

    Layout:

    - Section [OmniSimulation]: the generic, semantics-independent part.  One
      core assumption ([core], a step-wise forward simulation of the concrete
      system by the abstract one, up to measured stuttering) yields both the
      transfer of coqutil's [always] and the transfer of [eventually]
      (= riscv-coq's [runsTo]).  All the work shared between the two corollaries
      lives here.

    - Section [Connection]: the instantiation.  The abstract system is riscv-coq
      ([run1] under an arbitrary [PrimitivesParams] platform on
      [MetricRiscvMachine]), the concrete one is granite's reference semantics
      ([isaSpec/Spec.v], one clock cycle of [semantics.machine] paired with the
      MMIO events abstracted so far).  The one lemma to prove is [cycle_sim]; the
      corollaries are two-line applications of the generic section.

    Direction of the simulation.  Both transfers start from a riscv-coq
    hypothesis of the form "every riscv-coq outcome satisfies Q" (an
    omnisemantics weakest precondition).  To turn that into a statement about
    granite we must show that granite's (deterministic, input-driven) outcome is
    one of the riscv-coq outcomes; i.e. every granite step is matched by a
    riscv-coq step: a forward simulation from granite to riscv-coq.  A backward
    simulation (every riscv-coq step matched by a granite step) would not let us
    use the WP hypothesis, since it says nothing about the outcomes granite does
    not take.  The same forward direction is what bedrock2's Kami connection
    proves ([processor/KamiRiscvStep.v], [kamiStep_sound]). *)

From Stdlib Require Import ZArith Lists.List Strings.String Wf_nat Lia Btauto.
Import ListNotations.
From coqutil Require Import Map.Interface Word.Bitwidth Byte Z.BitOps Z.bitblast Map.Memory Word.LittleEndianList Datatypes.List.
From coqutil Require Semantics.OmniSmallstepCombinators.
From riscv Require Import Utility.Utility Utility.Monads Spec.Decode
  Spec.Primitives Spec.LeakageOfInstr Platform.RiscvMachine
  Platform.MetricRiscvMachine Platform.Run Utility.MkMachineWidth
  Utility.runsToNonDet Utility.Words32Naive Utility.FreeMonad
  Platform.MetricLogging Platform.MaterializeRiscvProgram
  Platform.MetricMaterializeRiscvProgram Platform.MinimalMMIO Platform.MetricMinimalMMIO.
From riscv Require Spec.Machine.
From stdpp Require Import list_numbers finite vector.
From RecordUpdate Require Import RecordSet. Import RecordSetNotations.
From granite.core Require Import Bits.
From granite.isaSpec Require Import Common IFC Memory RegisterFile Riscv Spec.
From granite.isaSpec Require Machine.

Import OmniSmallstepCombinators.

(** * Generic part: transferring [always] and [eventually] along a simulation *)

Section OmniSimulation.
  Context {A B : Type}.
  (* omnisemantics steps: [step s P] means every successor of [s] satisfies [P].
     [stepB] ranges over all admissible inputs of the concrete system; [stepBf]
     over a fair subclass.  [always] is
     transferred for [stepB]; [eventually] needs fairness, since a stuttering
     input that is always admissible would make every [eventually] false. *)
  Context (stepA : A -> (A -> Prop) -> Prop).
  Context (stepB stepBf : B -> (B -> Prop) -> Prop).
  (* the state relation, concrete state on the left *)
  Context (R : B -> A -> Prop).
  (* decreases on every stuttering fair B-step; bounds how long B can stutter *)
  Context (measure : B -> nat).

  Hypothesis stepB_weaken : forall b P Q, (forall x, P x -> Q x) -> stepB b P -> stepB b Q.

  (* The core assumptions, both instances of one per-input lemma in the
     instantiation below.  From related [b], [a] and a WP [Q] for one A-step,
     every B-step either retires (lands in a state related to an A-successor
     allowed by [Q]) or stutters (stays related to [a]); on fair inputs a
     stutter also decreases the measure. *)
  Hypothesis core : forall b a Q,
      R b a -> stepA a Q ->
      stepB b (fun b' => (exists a', R b' a' /\ Q a') \/ R b' a).
  Hypothesis core_fair : forall b a Q,
      R b a -> stepA a Q ->
      stepBf b (fun b' => (exists a', R b' a' /\ Q a') \/ (R b' a /\ measure b' < measure b)).

  (* what an A-property becomes on the B side *)
  Definition lift (P : A -> Prop) (b : B) : Prop := exists a, R b a /\ P a.

  Lemma lift_mono : forall (P Q : A -> Prop), (forall a, P a -> Q a) -> forall b, lift P b -> lift Q b.
  Proof. unfold lift. intros P Q HPQ b [a [Ha HP]]. eauto. Qed.

  (* [always] transfer: the B-invariant is [lift I] for the A-invariant [I];
     [core] with [Q := I]; stuttering steps keep [lift I] with the same [a]. *)
  Lemma transfer_always : forall (P : A -> Prop) a b,
      R b a -> always stepA P a -> always stepB (lift P) b.
  Proof.
    intros P a b HR [I E Pr U].
    apply (mk_always _ _ _ (fun b => exists a, R b a /\ I a)).
    - eauto.
    - intros b0 [a0 [HR0 HI0]].
      eapply stepB_weaken. 2: exact (core _ _ _ HR0 (Pr _ HI0)).
      intros b' [[a' [HR' HI']] | HR']; eauto.
    - intros b0 [a0 [HR0 HI0]]. exists a0. eauto.
  Qed.

  (* [eventually] transfer: outer induction on [eventually stepA P a], inner
     strong induction on [measure b] for the stuttering steps.  [core_fair]
     with [Q := midset] hands each retiring B-successor to the outer induction
     hypothesis and each stuttering one to the inner. *)
  Lemma transfer_eventually : forall (P : A -> Prop) a b,
      R b a -> eventually stepA P a -> eventually stepBf (lift P) b.
  Proof.
    intros P a b HR H. revert b HR.
    induction H.
    - intros b HR. apply eventually_done. eexists; eauto.
    - intros b. remember (measure b) as n eqn:Hn. revert b Hn.
      induction n as [n IHn] using lt_wf_ind. intros b Hn HR.
      eapply eventually_step. 1: exact (core_fair _ _ _ HR ltac:(eassumption)).
      intros b' [[a' [HR' Hmid]] | [HR' Hlt]].
      + eauto.
      + eapply IHn; eauto. lia.
  Qed.

  (* [runsTo] ([riscv.Utility.runsToNonDet]) is [eventually] constructor for
     constructor; same proof *)
  Lemma transfer_runsTo : forall (P : A -> Prop) a b,
      R b a -> runsTo stepA a P -> eventually stepBf (lift P) b.
  Proof.
    intros P a b HR H. revert b HR.
    induction H.
    - intros b HR. apply eventually_done. eexists; eauto.
    - intros b. remember (measure b) as n eqn:Hn. revert b Hn.
      induction n as [n IHn] using lt_wf_ind. intros b Hn HR.
      eapply eventually_step. 1: exact (core_fair _ _ _ HR ltac:(eassumption)).
      intros b' [[a' [HR' Hmid]] | [HR' Hlt]].
      + eauto.
      + eapply IHn; eauto. lia.
  Qed.

  (* the shape of bedrock2's event-loop theorems ([always (eventually good)]):
     under any admissible inputs, always, under fair inputs eventually [P] *)
  Lemma transfer_always_eventually : forall (P : A -> Prop) a b,
      R b a ->
      always stepA (eventually stepA P) a ->
      always stepB (eventually stepBf (lift P)) b.
  Proof.
    intros P a b HR H.
    pose proof (transfer_always _ _ _ HR H) as [I E Pr U].
    apply (mk_always _ _ _ I E Pr).
    intros b0 HI. destruct (U b0 HI) as [a0 [HR0 Hev]].
    exact (transfer_eventually _ _ _ HR0 Hev).
  Qed.
End OmniSimulation.

(** * Instantiation: riscv-coq [run1] on the left, granite [Spec.v] on the right *)

Section Connection.
  (* riscv-coq side.  Granite is 32-bit ([Common.WIDTH]). *)
  Local Notation word := (bits 32).
  (* riscv-coq registers are indexed by [Z] (its [Register]); granite's [Register] is [bits 5] *)
  Context {Registers : map.map Z word} {Registers_ok : map.ok Registers} {Mem : map.map word byte}.
  Local Notation MetricRiscvMachine := (@MetricRiscvMachine 32 Words32Naive Registers Mem).

  (* The platform is the concrete [MetricMinimalMMIO] one (bedrock2's compiler
     and fiat-crypto's GarageDoor run on it).  An abstract [PrimitivesParams]
     would not do: riscv-coq's [Primitives] class only gives sufficient
     conditions for [mcomp_sat], so a hypothesis [mcomp_sat run1 m Q] on an
     abstract platform says nothing about the successor riscv-coq takes; the
     Kami connection inverts the concrete interpreter for the same reason. *)
  Context {mmio_spec : @MMIOSpec 32 Words32Naive Mem}.
  Local Notation M := (free (@action 32 Words32Naive) (@result 32 Words32Naive)).
  Local Notation RVM := (@MetricMaterializeWithLeakage 32 Words32Naive).
  Local Notation RVP := (@Spec.Machine.RVP _ _ M word _ _ RVM).
  (* [translate] etc.: the default identity translation (no alignment traps) *)
  Context {RVS : @Spec.Machine.RiscvMachine M word _ _ RVP}.
  Local Notation PP := (@MetricMinimalMMIOPrimitivesParams 32 Words32Naive Mem Registers mmio_spec).

  Definition iset : InstructionSet := RV32IM.

  (* one riscv-coq instruction as an omnisemantics step *)
  Definition run1_step (m : MetricRiscvMachine) (P : MetricRiscvMachine -> Prop) : Prop :=
    mcomp_sat (PrimitivesParams := PP) (run1 (RVS := RVS) iset) m (fun (_ : unit) m' => P m').

  Lemma run1_step_weaken : forall m P Q,
      (forall x, P x -> Q x) -> run1_step m P -> run1_step m Q.
  Proof.
    unfold run1_step. cbv [mcomp_sat PP MetricMinimalMMIOPrimitivesParams]. intros m P Q HPQ H.
    exact (free.interp_weaken_post _ MetricMinimalMMIO.interp_action_weaken_post _ _ _ _
             (fun r s HP => HPQ s HP) H).
  Qed.

  (* granite side: the reference semantics machine of [isaSpec/Spec.v] *)
  Context {defaultMachine : Machine.machine IFC.Input IFC.Output}.
  Context {isaParams : instrs.params.IsaParams instrs.Instr}.
  Context (pub_init : PubInit) (sec_init : SecInit).

  Local Notation GSt := (semantics.St defaultMachine).
  Local Notation GM := (semantics.machine defaultMachine pub_init sec_init).
  Local Notation GInput := ((IFC.Input * IFC.DriverOut)%type).

  (* MMIO events in the vocabulary of bedrock2's [SPI.mmio_trace_abstraction_relation]:
     ("ld", addr, value) or ("st", addr, value) *)
  Definition MMIOEvent : Type := string * word * word.

  (* granite keeps no history in [St]; pair the state with the abstracted MMIO
     log, as bedrock2's Kami connection does with [KState] *)
  Definition GState : Type := GSt * list MMIOEvent.

  (* The MMIO events of one clock cycle, read off the ready/valid handshake of
     [Spec.v] ([consumeMMIOReq], [consumeMMIOResp]): a store is logged when
     its request is accepted (granite valid, environment ready), a load when
     its response is accepted (granite ready, environment valid); the response
     carries the address.  Vocabulary of bedrock2's
     [SPI.mmio_trace_abstraction_relation]. *)
  Definition cycle_mmio (s : GSt) (i : GInput) : list MMIOEvent :=
    let pub := fst (fst i) in
    let sec := snd (fst i) in
    (if s.(semantics.PubOutputWires).(PubOutput_mmio).(PubHandshake_valid)
        && pub.(PubInput_mmio).(PubHandshake_ready)
     then match s.(semantics.MMIOReqBuffer) with
          | specMemory.MMIOStore a v :: _ => [("st"%string, a, v)]
          | _ => []
          end
     else []) ++
    (if s.(semantics.PubOutputWires).(PubOutput_mmio).(PubHandshake_ready)
        && pub.(PubInput_mmio).(PubHandshake_valid)
     then [("ld"%string, sec.(SecInput_mmioData).(mem_resp_addr), sec.(SecInput_mmioData).(mem_resp_data))]
     else []).

  (* Which per-cycle inputs the theorems quantify over.  RESTRICTIONS (not
     discrepancies): riscv-coq has no interrupts, so no input asserts one; and
     one cycle executes at most three driver micro-steps.  Three is what
     granite's own driver uses to retire exactly one instruction per cycle
     ([None; None; None] in Spec.v's and TestSpec.v's examples: leak, execute,
     interrupt poll), and the phase cycle StepLeak -> StepInstr ->
     StepInterrupt -> StepLeak means that at most one instruction retires in
     three micro-steps, which is what the one-step [core] shape needs.
     Whether arbitrary driver lists must be supported (a multi-step [core]
     with a list of riscv-coq steps) is a question for the PR. *)
  Definition admissible (i : GInput) : Prop :=
    (fst (fst i)).(PubInput_interruptValid) = false /\
    (length (snd i).(DriverOut_nSteps) <= 3)%nat.

  (* fair inputs, for [eventually]: the driver schedules a micro-step and the
     MMIO handshake is ready and valid, so that granite cannot stutter forever *)
  Definition fair (i : GInput) : Prop :=
    admissible i /\
    (snd i).(DriverOut_nSteps) <> [] /\
    (fst (fst i)).(PubInput_mmio).(PubHandshake_ready) = true /\
    (fst (fst i)).(PubInput_mmio).(PubHandshake_valid) = true.

  Definition next (g : GState) (i : GInput) : GState :=
    (fst (Machine.step GM (fst g) i), cycle_mmio (fst g) i ++ snd g).

  (* one granite clock cycle as an omnisemantics step *)
  Definition granite_step (g : GState) (P : GState -> Prop) : Prop :=
    forall i, admissible i -> P (next g i).
  Definition granite_step_fair (g : GState) (P : GState -> Prop) : Prop :=
    forall i, fair i -> P (next g i).

  Lemma granite_step_weaken : forall g P Q,
      (forall x, P x -> Q x) -> granite_step g P -> granite_step g Q.
  Proof. unfold granite_step. eauto. Qed.

  (** ** The state relation *)

  (* which granite addresses are memory-mapped I/O; must agree with the
     platform's [MMIOSpec.isMMIOAddr] *)
  Context (isMMIOAddr_g : word -> Prop).

  (* granite bytes are [bits 8]; riscv-coq bytes are [coqutil.Byte.byte] *)
  Definition to_byte (b : Common.Byte) : byte := byte.of_Z (Zmod.unsigned b).
  Local Arguments to_byte : simpl never.

  Definition regs_related (rf : registerFile.RegFile) (rr : Registers) : Prop :=
    forall i : Z, (0 < i < 32)%Z ->
      map.get rr i = Some (registerFile.readReg (bits.of_Z LOG_NREGS i) rf).

  Lemma encode_fin_inj `{Finite A} (x y : A) : encode_fin x = encode_fin y -> x = y.
  Proof. intros E. rewrite <- (decode_encode_fin x), <- (decode_encode_fin y), E. reflexivity. Qed.

  (* register [zeroes] on both sides *)
  Lemma register_zero_iff : forall r : Register, Zmod.unsigned r = 0%Z <-> r = zeroes.
  Proof.
    intros r. split; intro E.
    - apply Zmod.unsigned_inj. rewrite E. reflexivity.
    - subst r. reflexivity.
  Qed.
  Lemma register_range : forall r : Register, (0 <= Zmod.unsigned r < 32)%Z.
  Proof. intros r. pose proof (bits.unsigned_range r ltac:(unfold LOG_NREGS; lia)). unfold LOG_NREGS in *. lia. Qed.

  Lemma regs_related_get : forall rf rr (r : Register),
      regs_related rf rr -> getReg rr (Zmod.unsigned r) = registerFile.readReg r rf.
  Proof.
    intros rf rr r H. unfold getReg, registerFile.readReg.
    destruct (decide (r = zeroes)) as [E | NE].
    - subst r. cbn. apply Zmod.unsigned_inj. reflexivity.
    - pose proof (register_range r) as Hr.
      assert (Hne : Zmod.unsigned r <> 0%Z) by (intro E; apply NE, register_zero_iff, E).
      replace ((0 <? Zmod.unsigned r)%Z && (Zmod.unsigned r <? 32)%Z) with true
        by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
      rewrite H by lia. unfold registerFile.readReg. rewrite Zmod.of_Z_unsigned.
      destruct (decide (r = zeroes)); [contradiction | reflexivity].
  Qed.

  Lemma regs_related_set : forall rf rr (r : Register) v,
      regs_related rf rr -> regs_related (registerFile.writeReg r v rf) (setReg (Zmod.unsigned r) v rr).
  Proof.
    intros rf rr r v H i Hi. unfold setReg, registerFile.writeReg.
    assert (Hi0 : bits.of_Z LOG_NREGS i <> zeroes).
    { intro E. apply (f_equal Zmod.unsigned) in E. rewrite unsigned_literal in E.
      rewrite Zmod.unsigned_of_Z_small in E by (unfold LOG_NREGS; lia). lia. }
    destruct (decide (r = zeroes)) as [E | NE].
    - subst r. change (Zmod.unsigned (zeroes : Register)) with 0%Z. cbn [Z.ltb Z.compare andb].
      rewrite H by lia. unfold registerFile.readReg.
      case_decide; [contradiction |].
      f_equal. symmetry. apply vlookup_insert_ne.
      intro E. apply encode_fin_inj in E. apply Hi0. symmetry. exact E.
    - pose proof (register_range r) as Hr.
      assert (Hne : Zmod.unsigned r <> 0%Z) by (intro E; apply NE, register_zero_iff, E).
      replace ((0 <? Zmod.unsigned r)%Z && (Zmod.unsigned r <? 32)%Z) with true
        by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
      destruct (Z.eq_dec i (Zmod.unsigned r)) as [Ei | Ni].
      + subst i. rewrite map.get_put_same. unfold registerFile.readReg.
        rewrite Zmod.of_Z_unsigned.
        case_decide; [contradiction |].
        f_equal. symmetry. apply vlookup_insert.
      + rewrite map.get_put_diff by exact Ni. rewrite H by lia. unfold registerFile.readReg.
        case_decide; [contradiction |].
        f_equal. symmetry. apply vlookup_insert_ne.
        intro E. apply encode_fin_inj in E. apply Ni.
        apply (f_equal Zmod.unsigned) in E. rewrite Zmod.unsigned_of_Z_small in E by (unfold LOG_NREGS; lia).
        symmetry. exact E.
  Qed.

  (* granite is Harvard (separate [Imem]/[Dmem], both total); riscv-coq has one
     partial byte map plus the executable-address set [getXAddrs].  Relate the
     data memory everywhere outside MMIO, and require the instruction memory to
     agree with it on the executable addresses.  A riscv-coq store removes its
     addresses from [getXAddrs], so this is preserved; a fetch requires
     [isXAddr4], so it reads the same bytes granite fetches from [Imem]. *)
  Definition mem_related (imem dmem : baseMem.Mem) (xaddrs : list word) (m : Mem) : Prop :=
    (forall a, ~ isMMIOAddr_g a -> map.get m a = Some (to_byte (baseMem.load_byte (to_N a) dmem))) /\
    (forall a, isMMIOAddr_g a -> map.get m a = None) /\
    (forall a, In a xaddrs -> baseMem.load_byte (to_N a) dmem = baseMem.load_byte (to_N a) imem) /\
    (forall a, In a xaddrs -> ~ isMMIOAddr_g a) /\
    (* granite addresses memory by [N] without wrap-around *)
    (forall a, In a xaddrs -> (Zmod.unsigned a + 4 <= 2 ^ 32)%Z).

  (* the abstracted granite log is the abstraction of riscv-coq's [getLog]
     (bedrock2's [mmio_trace_abstraction_relation], stated here abstractly) *)
  Context (log_related : list MMIOEvent -> list LogItem -> Prop).

  (* OPEN ISSUE (leakage): granite's per-instruction leakage versus riscv-coq's
     [getTrace].  For all instructions but [mul], granite's event is a function
     of riscv-coq's ([LeakageOfInstr]); granite's [mul] additionally leaks
     whether an operand is zero.  Stated abstractly until aligned:
     [leak_related] between instructions, [leak_related_ahead] after granite's
     [StepLeak] micro-step, when granite has emitted the event of the next
     instruction and riscv-coq has not stepped yet. *)
  Context (leak_related leak_related_ahead : IFC.L_leakage -> option (list LeakageOfInstr.LeakageEvent) -> Prop).
  (* the leakage granite has produced so far is not in [St] either.  Until the
     leakage alignment is done it is modelled as an abstract function of the
     architectural core of the state (phase, architectural state, MMIO
     buffers, interrupt latch), so that the cycle bookkeeping (default
     machine, wires, log) does not disturb it. *)
  Definition core_of (s : GSt) :=
    (s.(semantics.Phase), s.(semantics.ArchSt), s.(semantics.MMIOReqBuffer),
     s.(semantics.MMIORespBuffer), s.(semantics.InterruptSt)).
  Context (granite_leaks_core : StepPhase instrs.Instr (specMemory.memReqEvent * option Register)
                                * semantics.ArchState * list specMemory.memReqEvent
                                * list mem_resp_t * option mword -> IFC.L_leakage).
  Definition granite_leaks (g : GState) : IFC.L_leakage := granite_leaks_core (core_of (fst g)).
  Local Arguments granite_leaks : simpl never.

  (* the ISA parameters the theorems are about: granite's decoder, and an MMIO
     predicate that agrees with the platform's *)
  Hypothesis params_decode : forall w, instrs.params.decode w = instrs.Decode.decode w.
  Hypothesis params_isMMIO : forall a, Zmod.unsigned (instrs.params.isMMIOAddr a) = 1%Z <-> isMMIOAddr_g a.
  Hypothesis mmio_spec_agrees : forall a, mmio_spec.(isMMIOAddr) a <-> isMMIOAddr_g a.

  (* what idle and post-leak states share: idle wires, empty MMIO buffers, no
     interrupt latched, and the architectural components in relation *)
  Record core_related (s : GSt) (l : list MMIOEvent) (m : MetricRiscvMachine) : Prop := {
    cr_wires : s.(semantics.PubOutputWires) = IFC.default_PubOutput;
    cr_req : s.(semantics.MMIOReqBuffer) = [];
    cr_resp : s.(semantics.MMIORespBuffer) = [];
    cr_int : s.(semantics.InterruptSt) = None;
    cr_regs : regs_related s.(semantics.ArchSt).(semantics.Rf) m.(getRegs);
    cr_pc : m.(getPc) = s.(semantics.ArchSt).(semantics.Pc);
    cr_npc : m.(getNextPc) = Zmod.add s.(semantics.ArchSt).(semantics.Pc) (bits.of_Z 32 4);
    cr_mem : mem_related s.(semantics.ArchSt).(semantics.Imem) s.(semantics.ArchSt).(semantics.Dmem)
                         m.(getXAddrs) m.(getMem);
    cr_log : log_related l m.(getLog);
  }.

  (* the MMIO wait phase, related to the riscv-coq state BEFORE the instruction;
     its definition is part of the MMIO wait work *)
  Context (inflight_related : GState -> MetricRiscvMachine -> Prop).

  (* metrics are not related (as in bedrock2's Kami connection, [getMetrics] is unconstrained) *)
  Inductive related : GState -> MetricRiscvMachine -> Prop :=
  | related_idle : forall (g : GState) (m : MetricRiscvMachine),
      ((fst g).(semantics.Phase) = StepLeak \/ (fst g).(semantics.Phase) = StepInterrupt) ->
      core_related (fst g) (snd g) m ->
      leak_related (granite_leaks g) m.(getTrace) ->
      related g m
  (* after granite's [StepLeak] micro-step: the next instruction is decoded
     from the word at [Pc], riscv-coq has not stepped *)
  | related_instr : forall (g : GState) (m : MetricRiscvMachine) inst,
      (fst g).(semantics.Phase) = StepInstr inst ->
      inst = instrs.Decode.decode (baseMem.LoadWord (fst g).(semantics.ArchSt).(semantics.Pc)
                                                    (fst g).(semantics.ArchSt).(semantics.Imem)) ->
      core_related (fst g) (snd g) m ->
      leak_related_ahead (granite_leaks g) m.(getTrace) ->
      related g m
  | related_wait : forall (g : GState) (m : MetricRiscvMachine), inflight_related g m -> related g m.


  (** ** Assumptions standing in for the open issues of granite#1 *)

  (* the word riscv-coq fetches next, if any *)
  Definition next_instr (m : MetricRiscvMachine) : option Instruction :=
    match Memory.loadWord m.(getMem) m.(getPc) with
    | Some w => Some (Decode.decode iset (Zmod.unsigned w))
    | None => None
    end.

  Definition granite_decodes (w : word) : Prop :=
    match instrs.Decode.decode w with
    | instrs.InvalidInstr _ => False
    | _ => True
    end.

  (* OPEN ISSUE (missing instructions): granite implements 14 instructions; the
     bedrock2 compiler emits 38.  Every word riscv-coq executes from a related
     state must decode on the granite side.  Discharged per program today, by
     growing granite's ISA eventually. *)
  Hypothesis isa_coverage : forall g m w,
      related g m -> Memory.loadWord m.(getMem) m.(getPc) = Some w -> granite_decodes w.

  (** ** Decoder agreement on the covered subset *)

  (* granite's [Csr] enumeration back to its CSR index *)
  Definition csr_index (c : Csr) : Z :=
    match c with
    | mtvec => 773 | mepc => 833 | mcause => 834 | mtval => 835 | mie => 0x304
    end.

  (* granite's decoded instruction as riscv-coq's.  Immediates are written the
     way riscv-coq's [decode] computes them ([signExtend k] of the unsigned
     field), so that [decode_agree] is about unsigned fields only; the
     semantic lemmas use [signExtend k (unsigned x) = signed x]. *)
  Definition to_riscv (i : instrs.Instr) : Instruction :=
    let u := fun {n} (x : bits n) => Zmod.unsigned x in
    match i with
    | instrs.Strt (instrs.Addi rd rs1 imm12) => IInstruction (Decode.Addi (u rd) (u rs1) (signExtend 12 (u imm12)))
    | instrs.Strt (instrs.Add rd rs1 rs2) => IInstruction (Decode.Add (u rd) (u rs1) (u rs2))
    | instrs.Strt (instrs.Mul rd rs1 rs2) => MInstruction (Decode.Mul (u rd) (u rs1) (u rs2))
    | instrs.Strt (instrs.Csrrw rd rs1 csr) => CSRInstruction (Decode.Csrrw (u rd) (u rs1) (csr_index csr))
    | instrs.Strt (instrs.Auipc rd off) => IInstruction (Decode.Auipc (u rd) (signExtend 32 (Z.shiftl (u off) 12)))
    | instrs.Strt (instrs.Xor rd rs1 rs2) => IInstruction (Decode.Xor (u rd) (u rs1) (u rs2))
    | instrs.Strt (instrs.Slli rd rs1 sh) => IInstruction (Decode.Slli (u rd) (u rs1) (u sh))
    | instrs.Strt (instrs.Srli rd rs1 sh) => IInstruction (Decode.Srli (u rd) (u rs1) (u sh))
    | instrs.Strt (instrs.Lui rd imm20) => IInstruction (Decode.Lui (u rd) (signExtend 32 (Z.shiftl (u imm20) 12)))
    | instrs.Ctrl (instrs.Beq rs1 rs2 off) => IInstruction (Decode.Beq (u rs1) (u rs2) (signExtend 13 (u off)))
    | instrs.Ctrl (instrs.Jalr rd rs1 off) => IInstruction (Decode.Jalr (u rd) (u rs1) (signExtend 12 (u off)))
    | instrs.Ctrl (instrs.Bne rs1 rs2 off) => IInstruction (Decode.Bne (u rs1) (u rs2) (signExtend 13 (u off)))
    | instrs.Mem (instrs.Lw rd rs1 off) => IInstruction (Decode.Lw (u rd) (u rs1) (signExtend 12 (u off)))
    | instrs.Mem (instrs.Sw rs1 rs2 off) => IInstruction (Decode.Sw (u rs1) (u rs2) (signExtend 12 (u off)))
    | instrs.InvalidInstr w => InvalidInstruction (u w)
    end.

  (* riscv-coq's [bitSlice] on the unsigned value is granite's [Zmod.slice] *)
  Lemma bitSlice_slice : forall lo hi (w : word), (0 <= lo <= hi)%Z ->
      bitSlice (Zmod.unsigned w) lo hi = Zmod.unsigned (Zmod.slice lo hi w).
  Proof. intros. rewrite bitSlice_alt by lia. rewrite bits.unsigned_slice by lia. reflexivity. Qed.

  Lemma bitSlice_firstn : forall n (w : word), (0 <= n)%Z ->
      bitSlice (Zmod.unsigned w) 0 n = Zmod.unsigned (Zmod.firstn n w).
  Proof.
    intros. rewrite bitSlice_alt by lia. rewrite bits.unsigned_firstn.
    rewrite Z.pow_0_r, Z.div_1_r, Z.sub_0_r. reflexivity.
  Qed.

  (* the two facts about bits 25..31 that the shift-immediate decoding needs *)
  Lemma funct7_zero_facts : forall x : Z, (0 <= x)%Z -> bitSlice x 25 32 = 0%Z ->
      bitSlice x 26 32 = 0%Z /\ bitSlice x 25 26 = 0%Z /\ bitSlice x 20 26 = bitSlice x 20 25.
  Proof.
    intros x Hx H. rewrite !bitSlice_alt in * by lia.
    replace (2 ^ (32 - 25))%Z with 128%Z in H by reflexivity.
    replace (2 ^ (32 - 26))%Z with 64%Z by reflexivity.
    replace (2 ^ (26 - 25))%Z with 2%Z by reflexivity.
    replace (2 ^ (26 - 20))%Z with 64%Z by reflexivity.
    replace (2 ^ (25 - 20))%Z with 32%Z by reflexivity.
    replace (x / 2 ^ 26)%Z with (x / 2 ^ 25 / 2)%Z by (rewrite Z.div_div by lia; reflexivity).
    replace (x / 2 ^ 25)%Z with (x / 2 ^ 20 / 32)%Z in * by (rewrite Z.div_div by lia; reflexivity).
    set (y := (x / 2 ^ 20)%Z) in *.
    assert (Hy : (0 <= y)%Z) by (subst y; apply Z.div_pos; lia).
    assert (Hq : (y / 32 = 128 * (y / 32 / 128))%Z) by (apply Z.div_exact; [lia | exact H]).
    set (q := (y / 32 / 128)%Z) in *.
    replace (y mod 64)%Z with (y mod (32 * 2))%Z by reflexivity.
    rewrite (Z.rem_mul_r y 32 2) by lia.
    rewrite Hq.
    replace (128 * q)%Z with (q * 64 * 2)%Z by lia.
    rewrite Z.div_mul by lia. rewrite !Z.mod_mul by lia.
    repeat split; lia.
  Qed.

  Lemma funct7_zero_slices : forall w : word, Zmod.unsigned (Zmod.slice 25 32 w) = 0%Z ->
      Zmod.unsigned (Zmod.slice 26 32 w) = 0%Z /\ Zmod.unsigned (Zmod.slice 25 26 w) = 0%Z /\
      Zmod.unsigned (Zmod.slice 20 26 w) = Zmod.unsigned (Zmod.slice 20 25 w).
  Proof.
    intros w H. rewrite <- !bitSlice_slice by lia.
    apply funct7_zero_facts; [apply bits.unsigned_range; lia | rewrite bitSlice_slice by lia; exact H].
  Qed.

  (* [l = literal] on granite fields becomes [Zmod.unsigned l = value] *)
  Local Ltac field_fact H :=
    lazymatch type of H with
    | ?l = ?r =>
        let v := eval vm_compute in (Zmod.unsigned r) in
        let F := fresh "F" in
        assert (F : Zmod.unsigned l = v) by (rewrite H; vm_compute; reflexivity);
        clear H
    | _ /\ _ => let H1 := fresh H in let H2 := fresh H in destruct H as [H1 H2]; field_fact H1; field_fact H2
    end.

  Local Ltac riscv_cbv :=
    cbv -[Zmod.unsigned Zmod.slice Zmod.firstn Zmod.app Z.shiftl Z.lor Z.shiftr Z.land Z.lnot
          signExtend bitSlice Z.smodulo andb orb Z.eqb csr_index].

  Local Ltac riscv_reduce :=
    unfold Decode.decode; cbv beta zeta;
    rewrite ?(bitSlice_firstn 7) by lia;
    repeat (rewrite bitSlice_slice by lia);
    repeat match goal with F : Zmod.unsigned _ = _ |- _ => rewrite F; clear F end;
    riscv_cbv;
    repeat (progress (cbn [andb orb Z.eqb Pos.eqb];
                      rewrite ?Bool.andb_false_r, ?Bool.andb_true_r; riscv_cbv)).

  (* fold closed literal arithmetic *)
  Local Ltac norm_lits :=
    repeat match goal with
      | |- context [(Z.pos ?a - Z.pos ?b)%Z] =>
          let v := eval vm_compute in (Z.pos a - Z.pos b)%Z in change (Z.pos a - Z.pos b)%Z with v
      | |- context [(Z.pos ?a + Z.pos ?b)%Z] =>
          let v := eval vm_compute in (Z.pos a + Z.pos b)%Z in change (Z.pos a + Z.pos b)%Z with v
      end.

  (* granite assembles the B-type immediate with nested [Zmod.app]; riscv-coq
     with shifted [Z.lor]s.  No range facts are needed: [unsigned_app] turns
     each [app] into a shifted [lor], and the rest is [lor] associativity. *)
  Lemma b_imm_agree : forall w : word,
      Zmod.unsigned (Zmod.app (zeroes : bits 1)
                       (Zmod.app (Zmod.slice 8 12 w)
                          (Zmod.app (Zmod.slice 25 31 w)
                             (Zmod.app (Zmod.slice 7 8 w) (Zmod.slice 31 32 w)))))
      = Z.lor (Z.lor (Z.lor (Z.shiftl (Zmod.unsigned (Zmod.slice 31 32 w)) 12)
                            (Z.shiftl (Zmod.unsigned (Zmod.slice 25 31 w)) 5))
                     (Z.shiftl (Zmod.unsigned (Zmod.slice 8 12 w)) 1))
              (Z.shiftl (Zmod.unsigned (Zmod.slice 7 8 w)) 11).
  Proof.
    intros w.
    rewrite !bits.unsigned_app by lia.
    rewrite unsigned_literal.
    generalize (Zmod.unsigned (Zmod.slice 8 12 w)) as a.
    generalize (Zmod.unsigned (Zmod.slice 25 31 w)) as b.
    generalize (Zmod.unsigned (Zmod.slice 7 8 w)) as c.
    generalize (Zmod.unsigned (Zmod.slice 31 32 w)) as d.
    intros d c b a.
    rewrite !Z.shiftl_lor, !Z.shiftl_shiftl by lia. cbn [Z.add Pos.add Pos.succ].
    Z.bitblast.
  Qed.

  (* [rewrite] must match [Zmod.unsigned] arguments up to conversion (the
     modulus annotations differ between granite's field types and the lemmas) *)
  Local Set Keyed Unification.

  Lemma decode_agree : forall w : word,
      granite_decodes w -> to_riscv (instrs.Decode.decode w) = Decode.decode iset (Zmod.unsigned w).
  Proof.
    intros w Hdec. unfold granite_decodes in Hdec.
    unfold instrs.Decode.decode in *. cbv zeta in *. unfold WIDTH in *.
    pose proof (bits.unsigned_range w ltac:(lia)) as Hw.
    repeat case_decide; try (exfalso; exact Hdec).
    all: repeat match goal with H : ~ _ |- _ => clear H end.
    all: repeat match goal with H : _ = _ /\ _ |- _ => field_fact H | H : Zmod.firstn _ _ = _ |- _ => field_fact H end.
    all: cbn [to_riscv].
    (* csrrw: the CSR index must be one granite knows *)
    all: lazymatch goal with
         | |- context [lookupCSR ?c] =>
             destruct (lookupCSR c) as [csr|] eqn:Hl; [cbn [to_riscv] | destruct Hdec]
         | _ => idtac
         end.
    (* slli/srli: bits 25..31 are zero *)
    all: try match goal with
         | F : Zmod.unsigned (Zmod.slice 25 32 _) = 0%Z |- _ =>
             pose proof (funct7_zero_slices _ F) as [? [? ?]]
         end.
    all: riscv_reduce.
    all: try reflexivity.
    (* csrrw: read the index off [lookupCSR] *)
    all: try match goal with
         | Hl : lookupCSR _ = Some _ |- _ =>
             f_equal; f_equal; unfold lookupCSR in Hl; repeat case_bool_decide; try discriminate;
             inversion Hl; subst; cbn [csr_index];
             match goal with H : Zmod.slice 20 32 _ = _ |- _ => rewrite H end; vm_compute; reflexivity
         end.
    (* sw: granite assembles the S immediate with [Zmod.app] *)
    all: try (f_equal; f_equal; f_equal;
              rewrite (bits.unsigned_app (n := 12 - 7) (m := 32 - 25)) by lia;
              rewrite Z.lor_comm; reflexivity).
    (* beq/bne: the B immediate *)
    all: f_equal; f_equal; f_equal; apply b_imm_agree.
  Qed.

  (* CSRs, traps, MPIE, mtvec, mie (granite#1, riscv-coq#61): the relation has
     no CSR component and the trap paths differ.  On this platform CSR accesses
     are impossible ([GetCSRField]/[SetCSRField] interpret to [False],
     [MinimalMMIO.interpret_action]) and every trap goes through
     [raiseExceptionWithInfo], which writes CSR fields; so no riscv-coq run in
     a hypothesis executes a CSR instruction or takes a trap, and granite's
     trap behaviour never matters.  This is a lemma, not an assumption. *)
  Lemma csr_primitives_stuck :
    (forall f m (post : MachineInt -> MetricRiscvMachine -> Prop),
        ~ mcomp_sat (PrimitivesParams := PP) (Spec.Machine.getCSRField (RiscvProgram := RVP) f) m post) /\
    (forall f v m (post : unit -> MetricRiscvMachine -> Prop),
        ~ mcomp_sat (PrimitivesParams := PP) (Spec.Machine.setCSRField (RiscvProgram := RVP) f v) m post).
  Proof. split; intros; exact id. Qed.

  (* OPEN ISSUE (misaligned data accesses): granite traps, riscv-coq's default
     [translate] does not.  Either the platform's [translate] checks alignment
     (then misaligned accesses are excluded by [csr_primitives_stuck]) or the
     program never misaligns.  [data_access_aligned m] says the next instruction
     of [m] does not access memory at a misaligned address. *)
  Context (data_access_aligned : MetricRiscvMachine -> Prop).
  Hypothesis no_misaligned_access : forall g m, related g m -> data_access_aligned m.

  (* OPEN ISSUE (leakage alignment): the projection between the two leakage
     vocabularies is compatible with one retired instruction *)
  Hypothesis leak_step : forall g m g' m',
      related g m -> related g' m' -> True. (* placeholder: to be stated with the projection *)

  (* Progress (only for [eventually]): fair inputs schedule a micro-step every
     cycle and keep the MMIO handshake ready and valid, so granite cannot
     stutter forever.  [measure] is the number of stuttering cycles until the
     next retirement on a one-micro-step-per-cycle driver: the phase distance
     to [StepInstr], then the MMIO wait (request to send, response to receive). *)
  Definition phase_measure (s : GSt) : nat :=
    match s.(semantics.Phase) with
    | StepInterrupt => 5
    | StepLeak => 4
    | StepInstr _ => 3
    | StepWaitMMIOResp _ =>
        match s.(semantics.MMIOReqBuffer) with
        | _ :: _ => 2
        | [] => match s.(semantics.MMIORespBuffer) with [] => 1 | _ => 0 end
        end
    end.
  Definition measure (g : GState) : nat := phase_measure (fst g).

  Lemma wait_measure_le : forall s req,
      s.(semantics.Phase) = StepWaitMMIOResp req -> (phase_measure s <= 2)%nat.
  Proof.
    intros s req H. unfold phase_measure. rewrite H.
    destruct (semantics.MMIOReqBuffer s); [destruct (semantics.MMIORespBuffer s) |]; lia.
  Qed.
  Lemma nonwait_measure_ge : forall s,
      (forall req, s.(semantics.Phase) <> StepWaitMMIOResp req) -> (3 <= phase_measure s)%nat.
  Proof.
    intros s H. unfold phase_measure. destruct (semantics.Phase s) eqn:E; try lia.
    exfalso. eapply H. reflexivity.
  Qed.

  (** ** The core lemma *)

  (* One granite clock cycle from a related idle-or-in-flight state, against a
     riscv-coq WP for the next instruction: either the cycle retires the
     instruction and the new state is related to a riscv-coq successor allowed
     by the WP, or it stutters (silent driver cycle, MMIO wait, interrupt poll),
     stays related to the same riscv-coq state, and decreases the measure.
     This is the only lemma with real content: one case per granite
     instruction ([execStrt]/[execCtrl]/[execMem] of [Spec.v] against
     [ExecuteI]/[ExecuteM] unfolded through the platform), the MMIO wait
     sequence, and the phase bookkeeping. *)
  (** *** One cycle, decomposed *)

  (* the cycle prologue: latch the interrupt input, then the MMIO handshake
     ([Spec.v], [specStep]) *)
  Definition prologue (s : GSt) (i : GInput) : GSt :=
    let pub := fst (fst i) in
    let sec := snd (fst i) in
    semantics.consumeMMIOReq
      (semantics.consumeMMIOResp
         (s <| semantics.InterruptSt :=
                 if pub.(PubInput_interruptValid) then Some pub.(PubInput_interruptSrc) else None |>)
         pub.(PubInput_mmio).(PubHandshake_valid) sec.(SecInput_mmioData))
      pub.(PubInput_mmio).(PubHandshake_ready).

  (* one driver micro-step followed by the wire update, as [doDriverSteps] does *)
  Definition mstep (dmd : mem_req_t) (s : GSt) (x : option unit) : GSt :=
    semantics.update_mmio (fst (semantics.doDriverStep s x)) dmd.
  Definition msteps (dmd : mem_req_t) (xs : list (option unit)) (s : GSt) : GSt :=
    fold_left (mstep dmd) xs s.

  (* the default machine's contribution to the cycle: its next state and the
     MMIO data it drives when granite has none *)
  Definition nd_of (g : GState) (i : GInput) : Machine.state defaultMachine :=
    fst (Machine.step defaultMachine (fst g).(semantics.DefaultMachine) (fst i)).
  Definition dmd_of (g : GState) (i : GInput) : mem_req_t :=
    (snd (snd (Machine.step defaultMachine (fst g).(semantics.DefaultMachine) (fst i)))).(SecOutput_mmioData).

  Lemma doDriverSteps_fst : forall xs s l dmd,
      fst (fold_left (fun '(st, leakage) step =>
                        let '(st', leak') := semantics.doDriverStep st step in
                        (semantics.update_mmio st' dmd, leakage ++ leak')) xs (s, l))
      = msteps dmd xs s.
  Proof.
    unfold msteps. induction xs as [| x xs IH]; intros s l dmd; cbn; [reflexivity |].
    destruct (semantics.doDriverStep s x) as [s' leak'] eqn:E.
    rewrite IH. change (mstep dmd s x) with (semantics.update_mmio (fst (semantics.doDriverStep s x)) dmd).
    rewrite E. reflexivity.
  Qed.

  Lemma next_unfold : forall g i,
      fst (next g i) =
        (semantics.update_mmio (msteps (dmd_of g i) (snd i).(DriverOut_nSteps) (prologue (fst g) i)) (dmd_of g i))
          <| semantics.DefaultMachine := nd_of g i |>.
  Proof.
    intros [s l] [[pub sec] drv]. unfold next, nd_of, dmd_of, prologue. cbn [fst snd Machine.step semantics.machine].
    unfold semantics.specStep, semantics.step'.
    destruct (Machine.step defaultMachine (semantics.DefaultMachine s) (pub, sec)) as [nd [dpub dsec]] eqn:E.
    cbn [fst snd].
    unfold semantics.doDriverSteps.
    match goal with
    | |- context [fold_left ?f ?xs ?init] =>
        destruct (fold_left f xs init) as [s2 leak] eqn:E2;
        pose proof (f_equal fst E2) as H; rewrite doDriverSteps_fst in H; cbn [fst] in H
    end.
    rewrite <- H. reflexivity.
  Qed.

  (** *** What the in-flight relation must satisfy (properties of the parameter) *)

  (* the abstract in-flight relation covers the MMIO wait phase *)
  Hypothesis inflight_phase : forall g m, inflight_related g m ->
      exists req, (fst g).(semantics.Phase) = StepWaitMMIOResp req.
  (* it ignores the default machine and the wires *)
  Hypothesis inflight_set_default : forall s l m nd,
      inflight_related (s, l) m -> inflight_related (s <| semantics.DefaultMachine := nd |>, l) m.
  Hypothesis inflight_update_mmio : forall s l m dmd,
      inflight_related (s, l) m -> inflight_related (semantics.update_mmio s dmd, l) m.
  (* ADMIT-HYP: MMIO wait phases.  The handshake in the prologue moves a request
     out of, or a response into, the buffers of a waiting state; the in-flight
     relation must absorb that together with the logged event. *)
  Hypothesis inflight_prologue : forall s l m i,
      inflight_related (s, l) m -> admissible i ->
      inflight_related (prologue s i, cycle_mmio s i ++ l) m.

  (** *** The relation across the cycle bookkeeping *)

  Lemma related_phase : forall g m, related g m ->
      (fst g).(semantics.Phase) = StepLeak \/ (fst g).(semantics.Phase) = StepInterrupt \/
      (exists inst, (fst g).(semantics.Phase) = StepInstr inst) \/
      (exists req, (fst g).(semantics.Phase) = StepWaitMMIOResp req).
  Proof.
    intros g m H. inversion H; subst.
    - destruct H0; auto.
    - eauto.
    - destruct (inflight_phase _ _ H0); eauto.
  Qed.

  (* the bookkeeping operations only touch the default machine and the wires *)
  Lemma core_related_set_default : forall s l m nd,
      core_related s l m -> core_related (s <| semantics.DefaultMachine := nd |>) l m.
  Proof. intros s l m nd [ ]; constructor; unfold RecordSet.set; cbn; first [assumption | reflexivity]. Qed.

  Lemma core_related_update_mmio : forall s l m dmd,
      (forall req, s.(semantics.Phase) <> StepWaitMMIOResp req) ->
      core_related s l m -> core_related (semantics.update_mmio s dmd) l m.
  Proof.
    intros s l m dmd Hph [ ]. unfold semantics.update_mmio, RecordSet.set.
    destruct (semantics.Phase s) eqn:E; try (exfalso; eapply Hph; reflexivity);
      constructor; cbn; first [assumption | reflexivity].
  Qed.

  Lemma core_related_prologue : forall s l m i,
      core_related s l m -> admissible i ->
      core_related (prologue s i) (cycle_mmio s i ++ l) m /\ cycle_mmio s i = [].
  Proof.
    intros s l m i [ ] [Hint Hlen].
    unfold prologue, cycle_mmio, RecordSet.set, semantics.consumeMMIOResp, semantics.consumeMMIOReq.
    rewrite cr_wires0, Hint. cbn. split; [| reflexivity].
    constructor; cbn; first [assumption | reflexivity].
  Qed.

  Lemma granite_leaks_set_default : forall s l nd,
      granite_leaks (s <| semantics.DefaultMachine := nd |>, l) = granite_leaks (s, l).
  Proof. intros. unfold granite_leaks, core_of, RecordSet.set. cbn. reflexivity. Qed.
  Lemma granite_leaks_update_mmio : forall s l dmd,
      granite_leaks (semantics.update_mmio s dmd, l) = granite_leaks (s, l).
  Proof.
    intros. unfold granite_leaks, core_of, semantics.update_mmio, RecordSet.set. cbn [fst].
    destruct (semantics.Phase s); try reflexivity.
    destruct (semantics.MMIOReqBuffer s); [destruct (semantics.MMIORespBuffer s) |]; reflexivity.
  Qed.
  Lemma granite_leaks_prologue : forall s l l' i,
      admissible i -> s.(semantics.InterruptSt) = None -> s.(semantics.PubOutputWires) = IFC.default_PubOutput ->
      granite_leaks (prologue s i, l') = granite_leaks (s, l).
  Proof.
    intros s l l' i [Hint _] HI HW.
    unfold granite_leaks, core_of, prologue, RecordSet.set, semantics.consumeMMIOResp, semantics.consumeMMIOReq.
    rewrite HW, Hint, HI. reflexivity.
  Qed.

  Lemma related_set_default : forall s l m nd,
      related (s, l) m -> related (s <| semantics.DefaultMachine := nd |>, l) m.
  Proof.
    intros s l m nd H. inversion H; subst; cbn in *.
    - eapply related_idle; cbn; eauto using core_related_set_default;
        rewrite granite_leaks_set_default; assumption.
    - eapply related_instr; cbn; eauto using core_related_set_default;
        rewrite granite_leaks_set_default; assumption.
    - apply related_wait. apply inflight_set_default. assumption.
  Qed.

  Lemma related_update_mmio : forall s l m dmd,
      related (s, l) m -> related (semantics.update_mmio s dmd, l) m.
  Proof.
    intros s l m dmd H. inversion H; subst; cbn in *.
    - eapply related_idle; cbn.
      + unfold semantics.update_mmio, RecordSet.set. destruct H0 as [H0 | H0]; rewrite H0; cbn; auto.
      + apply core_related_update_mmio; [| assumption]. intros req E. destruct H0; congruence.
      + rewrite granite_leaks_update_mmio. assumption.
    - match goal with HP : semantics.Phase s = StepInstr _ |- _ =>
      eapply related_instr; cbn;
        [ unfold semantics.update_mmio, RecordSet.set; rewrite HP; reflexivity
        | unfold semantics.update_mmio, RecordSet.set; rewrite HP; reflexivity
        | apply core_related_update_mmio; [intros req E; congruence | assumption]
        | rewrite granite_leaks_update_mmio; assumption ]
      end.
    - apply related_wait. apply inflight_update_mmio. assumption.
  Qed.

  Lemma prologue_phase : forall s i, (prologue s i).(semantics.Phase) = s.(semantics.Phase).
  Proof.
    intros. unfold prologue, RecordSet.set, semantics.consumeMMIOResp, semantics.consumeMMIOReq. cbn.
    repeat (destruct (_ && _)); reflexivity.
  Qed.
  Lemma prologue_arch : forall s i, (prologue s i).(semantics.ArchSt) = s.(semantics.ArchSt).
  Proof.
    intros. unfold prologue, RecordSet.set, semantics.consumeMMIOResp, semantics.consumeMMIOReq. cbn.
    repeat (destruct (_ && _)); reflexivity.
  Qed.

  (* in idle and post-leak states the wires are idle, so the handshake consumes
     nothing and logs nothing; the interrupt latch stays [None] for admissible inputs *)
  Lemma related_prologue : forall s l m i,
      related (s, l) m -> admissible i -> related (prologue s i, cycle_mmio s i ++ l) m.
  Proof.
    intros s l m i H Hi. inversion H; subst; cbn in *.
    - match goal with Hc : core_related s l m |- _ =>
      destruct (core_related_prologue _ _ _ _ Hc Hi) as [Hc' He];
      eapply related_idle; cbn;
        [ rewrite prologue_phase; assumption | exact Hc'
        | rewrite (granite_leaks_prologue _ l) by (try assumption; apply Hc); assumption ]
      end.
    - match goal with Hc : core_related s l m, HP : semantics.Phase s = StepInstr _ |- _ =>
      destruct (core_related_prologue _ _ _ _ Hc Hi) as [Hc' He];
      eapply related_instr; cbn;
        [ rewrite prologue_phase; exact HP | rewrite prologue_arch; reflexivity | exact Hc'
        | rewrite (granite_leaks_prologue _ l) by (try assumption; apply Hc); assumption ]
      end.
    - apply related_wait. apply inflight_prologue; assumption.
  Qed.

  (** *** Fetch: the word riscv-coq loads at [pc] is the word granite fetches *)

  Lemma to_byte_unsigned : forall b : Common.Byte, byte.unsigned (to_byte b) = Zmod.unsigned b.
  Proof.
    intros. unfold to_byte. rewrite byte.unsigned_of_Z. unfold byte.wrap.
    apply Z.mod_small. apply bits.unsigned_range. lia.
  Qed.

  (* coqutil's little-endian combine of the converted bytes is granite's *)
  Lemma le_combine_granite : forall bs : list Common.Byte,
      LittleEndianList.le_combine (List.map to_byte bs) = little_endian_to_bits 8 bs.
  Proof.
    induction bs as [| b bs IH]; [reflexivity |].
    unfold little_endian_to_bits in *.
    change (LittleEndianList.le_combine (List.map to_byte (b :: bs)))
      with (Z.lor (byte.unsigned (to_byte b)) (Z.shiftl (LittleEndianList.le_combine (List.map to_byte bs)) 8)).
    change (little_endian_to_Z 8 (List.map Zmod.unsigned (b :: bs)))
      with (Z.lor (Zmod.unsigned b) (Z.shiftl (little_endian_to_Z 8 (List.map Zmod.unsigned bs)) 8)).
    rewrite to_byte_unsigned, IH. reflexivity.
  Qed.

  (* [lia] does not evaluate [2 ^ 32] *)
  Local Ltac pow32 := change (2 ^ 32)%Z with 4294967296%Z in *.

  (* granite addresses memory by [N] without wrap-around; within an executable
     word the two address arithmetics agree *)
  Lemma to_N_add_small : forall (a : word) (k : Z),
      (0 <= k)%Z -> (Zmod.unsigned a + k < 2 ^ 32)%Z ->
      to_N (Zmod.add a (bits.of_Z 32 k)) = (to_N a + Z.to_N k)%N.
  Proof.
    intros a k Hk Hlt. unfold to_N.
    pose proof (bits.unsigned_range a ltac:(lia)).
    rewrite Zmod.unsigned_add, bits.unsigned_of_Z_small by (pow32; lia).
    pow32. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma fetch_related : forall s l m,
      core_related s l m ->
      isXAddr4 m.(getPc) m.(getXAddrs) ->
      Memory.loadWord m.(getMem) m.(getPc) =
        Some (baseMem.LoadWord s.(semantics.ArchSt).(semantics.Pc) s.(semantics.ArchSt).(semantics.Imem)).
  Proof.
    intros s l m Hc Hx. destruct Hc as [_ _ _ _ _ Hpc _ [Hm1 [Hm2 [Hm3 [Hm4 Hm5]]]] _].
    rewrite Hpc in *. set (pc := s.(semantics.ArchSt).(semantics.Pc)) in *.
    set (imem := s.(semantics.ArchSt).(semantics.Imem)) in *.
    set (dmem := s.(semantics.ArchSt).(semantics.Dmem)) in *.
    destruct Hx as [X0 [X1 [X2 X3]]]. unfold isXAddr1 in *.
    pose proof (bits.unsigned_range pc ltac:(unfold WIDTH; lia)) as Hpcr.
    (* the four executable addresses, in footprint form *)
    assert (F : forall k, (0 <= k <= 3)%Z ->
              In (Zmod.add pc (bits.of_Z 32 k)) m.(getXAddrs) /\
              to_N (Zmod.add pc (bits.of_Z 32 k)) = (to_N pc + Z.to_N k)%N).
    { intros k Hk. pose proof (Hm5 _ X0) as Hb.
      assert (Hk4 : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3)%Z) by lia.
      split.
      - destruct Hk4 as [-> | [-> | [-> | ->]]].
        + replace (Zmod.add pc (bits.of_Z 32 0)) with pc; [exact X0 |].
          apply Zmod.unsigned_inj. rewrite Zmod.unsigned_add, bits.unsigned_of_Z_small by (pow32; lia).
          rewrite Z.add_0_r. symmetry. apply Z.mod_small. pow32. lia.
        + exact X1.
        + exact X2.
        + exact X3.
      - apply to_N_add_small; lia. }
    (* each byte is present in riscv-coq's memory and equal to granite's *)
    assert (G : forall k, (0 <= k <= 3)%Z ->
              map.get m.(getMem) (Zmod.add pc (bits.of_Z 32 k)) =
              Some (to_byte (baseMem.load_byte (to_N pc + Z.to_N k) imem))).
    { intros k Hk. destruct (F k Hk) as [Fin Fn].
      rewrite Hm1 by (apply Hm4; exact Fin). rewrite Hm3 by exact Fin. rewrite Fn. reflexivity. }
    unfold Memory.loadWord, coqutil.Map.Memory.load_Z, coqutil.Map.Memory.load_bytes, coqutil.Map.Memory.footprint.
    cbn [List.map List.seq option_all].
    rewrite (G 0%Z), (G 1%Z), (G 2%Z), (G 3%Z) by lia. cbn [option_all].
    unfold baseMem.LoadWord. cbn [baseMem.load_bytes].
    rewrite <- le_combine_granite. cbn [List.map].
    cbn [Z.to_N N.of_nat Pos.of_succ_nat].
    unfold baseMem.load_byte.
    replace (to_N pc + 0)%N with (to_N pc) by lia.
    replace (to_N pc + 1 + 1 + 1)%N with (to_N pc + 3)%N by lia.
    replace (to_N pc + 1 + 1)%N with (to_N pc + 2)%N by lia.
    reflexivity.
  Qed.

  (** *** The micro-steps *)

  (* [StepInterrupt] with no interrupt pending: back to [StepLeak], nothing
     else changes (Spec.v, [doDriverStep] with [InterruptSt = None]) *)
  Lemma mstutter_interrupt : forall s l m x dmd,
      related (s, l) m -> s.(semantics.Phase) = StepInterrupt ->
      related (mstep dmd s x, l) m /\ (mstep dmd s x).(semantics.Phase) = StepLeak.
  Proof. (* ADMIT: interrupts (the [InterruptSt = None] invariant) *) Admitted.

  (* [StepLeak]: fetch from [Imem], decode, emit the leakage event, move to
     [StepInstr]; riscv-coq has not stepped yet, so this is a stutter into an
     in-flight state whose leakage is one event ahead of [getTrace] *)
  Lemma mstutter_leak : forall s l m x dmd,
      related (s, l) m -> s.(semantics.Phase) = StepLeak ->
      related (mstep dmd s x, l) m /\ exists inst, (mstep dmd s x).(semantics.Phase) = StepInstr inst.
  Proof. (* ADMIT: leakage alignment (granite's event vs riscv-coq's fetchInstr/executeInstr pair) *) Admitted.

  (* [StepInstr]: the retiring micro-step.  One lemma per instruction class;
     each unfolds [run1_step] through the free-monad interpreter for that
     instruction ([decode_agree] identifies the decoded instruction) and
     granite's [execStrt]/[execCtrl]/[execMem]. *)
  Definition retired (s : GSt) (l : list MMIOEvent) (Q : MetricRiscvMachine -> Prop) : Prop :=
    exists m', related (s, l) m' /\ Q m' /\ s.(semantics.Phase) = StepInterrupt.

  Local Opaque Decode.decode.
  (* reduce [run1_step] to the fetch and the rest of the instruction; [decode]
     stays folded until the fetched word is known *)
  Local Ltac reduce_run1 H :=
    unfold run1_step, run1 in H;
    cbv [mcomp_sat PP MetricMinimalMMIOPrimitivesParams] in H;
    cbn [Bind free.Monad_free free.bind free.interp free.interp_fix free.interp_body
         interp_action interpret_action
         Spec.Machine.getPC Spec.Machine.loadWord Spec.Machine.leakEvent Spec.Machine.RVP
         Spec.Machine.getRegister Spec.Machine.setRegister Spec.Machine.setPC
         Spec.Machine.endCycleNormal Spec.Machine.getPrivMode Spec.Machine.getCSRField
         MetricMaterializeWithLeakage MetricMaterialize fst snd
         getMachine getMetrics getRegs getPc getNextPc getMem getXAddrs getLog getTrace
         RiscvMachine.withLeakageEvent] in H.

  (* ADMIT-HYP: leakage alignment.  After granite's [StepLeak] micro-step
     ([leak_related_ahead]), riscv-coq's step for the same instruction (its
     [fetchInstr] and [executeInstr] events) realigns the two leakage traces
     with granite's state after the instruction.  [mul] is excluded: granite's
     [Mul_leakage] carries the zero-operand bit, riscv-coq's does not. *)
  Hypothesis leak_retire : forall s l m inst,
      related (s, l) m -> s.(semantics.Phase) = StepInstr inst ->
      (match inst with instrs.Strt (instrs.Mul _ _ _) => False | _ => True end) ->
      run1_step m (fun m' => leak_related (granite_leaks (semantics.execute inst s, l)) m'.(getTrace)).

  Lemma mstep_instr : forall (s : GSt) x dmd inst,
      s.(semantics.Phase) = StepInstr inst ->
      mstep dmd s x = semantics.update_mmio (semantics.execute inst s) dmd.
  Proof. intros s x dmd inst H. unfold mstep, semantics.doDriverStep. rewrite H. reflexivity. Qed.

  Lemma update_mmio_phase : forall (s : GSt) dmd,
      (semantics.update_mmio s dmd).(semantics.Phase) = s.(semantics.Phase).
  Proof.
    intros. unfold semantics.update_mmio, RecordSet.set. cbn.
    destruct (semantics.Phase s); try reflexivity.
    destruct (semantics.MMIOReqBuffer s); [destruct (semantics.MMIORespBuffer s) |]; reflexivity.
  Qed.

  Lemma lit4 : (4%Zmod : mword) = bits.of_Z 32 4.
  Proof. apply Zmod.unsigned_inj. vm_compute. reflexivity. Qed.

  Lemma regs_related_set' : forall rf rr (r : Register) v1 v2,
      v1 = v2 -> regs_related rf rr ->
      regs_related (registerFile.writeReg r v1 rf) (setReg (Zmod.unsigned r) v2 rr).
  Proof. intros; subst; apply regs_related_set; assumption. Qed.

  (* the 20-bit immediates: granite sign-extends then shifts in the machine
     word, riscv-coq shifts then sign-extends in [Z] *)
  Lemma imm20_agree : forall (x : bits 20),
      Zmod.slu (bits.of_Z 32 (Zmod.signed x)) 12 = Zmod.of_Z (2 ^ 32) (signExtend 32 (Z.shiftl (Zmod.unsigned x) 12)).
  Proof.
    intros x. apply Zmod.unsigned_inj. unfold signExtend.
    rewrite bits.unsigned_slu, !Zmod.unsigned_of_Z, Z.mod_smod, !Z.shiftl_mul_pow2 by lia.
    rewrite <- bits.smod_unsigned.
    set (u := Zmod.unsigned x). set (a := Z.smodulo u (2 ^ 20)).
    pose proof (Z.mod_smod u (2 ^ 20)) as Hmod. fold a in Hmod.
    change (2 ^ 32)%Z with 4294967296%Z in *. change (2 ^ 20)%Z with 1048576%Z in *. change (2 ^ 12)%Z with 4096%Z in *.
    rewrite Z.mul_mod_idemp_l by lia.
    pose proof (Z.div_mod a 1048576 ltac:(lia)) as Ha. pose proof (Z.div_mod u 1048576 ltac:(lia)) as Hu.
    rewrite Hmod in Ha.
    set (qa := (a / 1048576)%Z) in *. set (qu := (u / 1048576)%Z) in *. set (r := (u mod 1048576)%Z) in *.
    clearbody qa qu r.
    replace (a * 4096)%Z with (r * 4096 + qa * 4294967296)%Z by lia.
    replace (u * 4096)%Z with (r * 4096 + qu * 4294967296)%Z by lia.
    rewrite !Z.mod_add by lia. reflexivity.
  Qed.

  (* the common part of a retiring ALU micro-step: the riscv-coq successor is
     the witness, the phase is [StepInterrupt], the wires and buffers are the
     idle ones, memory and log are untouched, the leakage is [leak_retire];
     what remains is the value written to [rd] *)
  Local Ltac alu_reduce H :=
    cbn [LeakageOfInstr.leakage_of_instr LeakageOfInstr.instr_leakage LeakageOfInstr.leakage_of_instr_I
         Bind Return free.Monad_free free.bind free.interp_fix free.interp_body interp_action interpret_action
         id Option.option_map2
         Execute.execute ExecuteI.execute
         Spec.Machine.getRegister Spec.Machine.setRegister Spec.Machine.getPC Spec.Machine.setPC
         Spec.Machine.endCycleNormal Spec.Machine.leakEvent Spec.Machine.RVP
         MetricMaterializeWithLeakage MetricMaterialize fst snd option_map
         getMachine getMetrics RiscvMachine.withLeakageEvent
         MetricRiscvMachine.withRegs MetricRiscvMachine.withPc MetricRiscvMachine.withNextPc
         RiscvMachine.withRegs RiscvMachine.withPc RiscvMachine.withNextPc updatePc
         RiscvMachine.getRegs RiscvMachine.getPc RiscvMachine.getNextPc RiscvMachine.getMem
         RiscvMachine.getXAddrs RiscvMachine.getLog RiscvMachine.getTrace] in H.

  Local Ltac alu_finish s l Egi HF HD HQ HR Hph Hc :=
    let HL := fresh "HL" in
    pose proof (leak_retire s l _ _ HR Hph I) as HL;
    reduce_run1 HL; destruct HL as [_ HL]; unfold Memory.loadWord in HL; rewrite HF in HL;
    rewrite <- HD in HL; alu_reduce HL;
    unfold retired; rewrite (mstep_instr s _ _ _ Hph);
    eexists; split; [| split; [exact HQ | rewrite update_mmio_phase; reflexivity]];
    apply related_update_mmio;
    eapply related_idle; cbn [fst snd];
    [ right; reflexivity
    | destruct Hc as [Hw Hreq Hresp Hint Hregs Hpc Hnpc Hmem Hlog];
      cbn [getMachine getRegs getPc getNextPc getMem getXAddrs getLog getTrace
           RiscvMachine.getRegs RiscvMachine.getPc RiscvMachine.getNextPc RiscvMachine.getMem
           RiscvMachine.getXAddrs RiscvMachine.getLog RiscvMachine.getTrace] in Hpc, Hnpc, Hmem, Hlog |- *;
      unfold semantics.execute, semantics.stepStrt, semantics.execStrt, semantics.nextPc, RecordSet.set;
      cbn [fst snd];
      constructor; cbn;
      [ exact Hw | exact Hreq | exact Hresp | exact Hint
      | idtac
      | rewrite Hnpc, lit4; reflexivity
      | rewrite Hnpc, lit4; reflexivity
      | exact Hmem | exact Hlog ]
    | cbn [getTrace getMachine RiscvMachine.getTrace]; exact HL ].

  Lemma retire_alu : forall s l m Q x dmd inst,
      related (s, l) m -> run1_step m Q -> s.(semantics.Phase) = StepInstr inst ->
      (match inst with
       | instrs.Strt (instrs.Addi _ _ _) | instrs.Strt (instrs.Add _ _ _) | instrs.Strt (instrs.Xor _ _ _)
       | instrs.Strt (instrs.Slli _ _ _) | instrs.Strt (instrs.Srli _ _ _)
       | instrs.Strt (instrs.Lui _ _) | instrs.Strt (instrs.Auipc _ _) => True
       | _ => False end) ->
      retired (mstep dmd s x) l Q.
  Proof.
    intros s l m Q x dmd inst HR HQ Hph Hcls.
    pose proof HR as HR0.
    inversion HR; subst; cbn in *.
    - match goal with Hd : _ \/ _ |- _ => destruct Hd as [Hd | Hd]; rewrite Hph in Hd; discriminate end.
    - match goal with HP : semantics.Phase s = StepInstr _ |- _ => rewrite Hph in HP; inversion HP; subst inst end.
      match goal with Hc : core_related s l m |- _ =>
      destruct m as [[regs pc npc mem xaddrs log trace] metrics];
      reduce_run1 HQ;
      destruct HQ as [HX HQ]; specialize (HX eq_refl);
      pose proof (fetch_related s l _ Hc HX) as HF; cbn [getMachine getMem getPc] in HF;
      unfold Memory.loadWord in HF; rewrite HF in HQ;
      set (w := baseMem.LoadWord (semantics.Pc (semantics.ArchSt s)) (semantics.Imem (semantics.ArchSt s))) in *;
      assert (Hdec : granite_decodes w) by (unfold granite_decodes; destruct (instrs.Decode.decode w); solve [exact I | exact Hcls]);
      pose proof (decode_agree w Hdec) as HD;
      destruct (instrs.Decode.decode w) as [si | ci | mi | w'] eqn:Egi;
      [ destruct si; try (exfalso; exact Hcls) | exfalso; exact Hcls | exfalso; exact Hcls | exfalso; exact Hcls ];
      cbn [to_riscv] in HD; rewrite <- HD in HQ; alu_reduce HQ;
      alu_finish s l Egi HF HD HQ HR0 Hph Hc
      end.
      + (* addi *) eapply regs_related_set'; [| exact Hregs].
        rewrite (regs_related_get _ _ _ Hregs). unfold signExtend. rewrite bits.smod_unsigned. reflexivity.
      + (* add *) eapply regs_related_set'; [| exact Hregs].
        rewrite !(regs_related_get _ _ _ Hregs). reflexivity.
      + (* auipc *) eapply regs_related_set'; [| exact Hregs].
        unfold WIDTH. rewrite imm20_agree, Hpc. apply Zmod.add_comm.
      + (* xor *) eapply regs_related_set'; [| exact Hregs].
        rewrite !(regs_related_get _ _ _ Hregs). reflexivity.
      + (* slli *) eapply regs_related_set'; [| exact Hregs].
        rewrite (regs_related_get _ _ _ Hregs). reflexivity.
      + (* srli *) eapply regs_related_set'; [| exact Hregs].
        rewrite (regs_related_get _ _ _ Hregs). reflexivity.
      + (* lui *) eapply regs_related_set'; [| exact Hregs].
        unfold WIDTH. apply imm20_agree.
    - match goal with Hi : inflight_related _ _ |- _ =>
        destruct (inflight_phase _ _ Hi) as [req Hw]; cbn in Hw; rewrite Hph in Hw; discriminate end.
  Qed.

  Lemma retire_mul : forall s l m Q x dmd inst,
      related (s, l) m -> run1_step m Q -> s.(semantics.Phase) = StepInstr inst ->
      (match inst with instrs.Strt (instrs.Mul _ _ _) => True | _ => False end) ->
      retired (mstep dmd s x) l Q.
  Proof. (* ADMIT: leakage alignment (granite's mul leaks the zero-operand bit) *) Admitted.

  (* the alignment tests: riscv-coq's [remu addr 4 /= 0], granite's [is_word_aligned 4] *)
  Lemma aligned_agree : forall t : word,
      negb (Zmod.eqb (Zmod.umod t (Zmod.of_Z (2 ^ 32) 4)) (Zmod.of_Z (2 ^ 32) 0)) =
      negb (semantics.is_word_aligned 4 t).
  Proof.
    intros t. unfold semantics.is_word_aligned. f_equal.
    assert (H3 : Zmod.unsigned (Zmod.sub (of_N 32 4) (1%Zmod : mword)) = 3%Z) by (vm_compute; reflexivity).
    assert (Ht : Zmod.unsigned (Zmod.umod t (Zmod.of_Z (2 ^ 32) 4)) = Zmod.unsigned (Zmod.and t (Zmod.sub (of_N 32 4) 1%Zmod))).
    { rewrite Zmod.unsigned_umod, Zmod.unsigned_and, H3.
      change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia.
      rewrite (Zmod.unsigned_of_Z_small (m := 2 ^ 32) 4) by (change (2 ^ 32)%Z with 4294967296%Z; lia).
      change (2 ^ 2)%Z with 4%Z.
      rewrite (Z.mod_small (Zmod.unsigned t mod 4) (2 ^ 32)); [reflexivity |].
      pose proof (Z.mod_pos_bound (Zmod.unsigned t) 4 ltac:(lia)) as Hb. pow32.
      lia. }
    destruct (Zmod.eqb_spec (Zmod.umod t (Zmod.of_Z (2 ^ 32) 4)) (Zmod.of_Z (2 ^ 32) 0)) as [E | NE];
      case_bool_decide as E'; try reflexivity; exfalso.
    - apply E'. apply Zmod.unsigned_inj. rewrite <- Ht, E. vm_compute. reflexivity.
    - apply NE. apply Zmod.unsigned_inj. rewrite Ht, E'. vm_compute. reflexivity.
  Qed.

  Lemma lnot1 : Zmod.xor (Zmod.of_Z (2 ^ 32) 1) (bits.of_Z 32 (2 ^ 32 - 1)) = Zmod.not (1%Zmod : mword).
  Proof. apply Zmod.unsigned_inj. vm_compute. reflexivity. Qed.

  Local Ltac ctrl_reduce H :=
    cbn [LeakageOfInstr.leakage_of_instr LeakageOfInstr.instr_leakage LeakageOfInstr.leakage_of_instr_I
         Bind Return free.Monad_free free.bind free.interp_fix free.interp_body interp_action interpret_action
         id Option.option_map2 when
         Execute.execute ExecuteI.execute
         Spec.Machine.getRegister Spec.Machine.setRegister Spec.Machine.getPC Spec.Machine.setPC
         Spec.Machine.endCycleNormal Spec.Machine.leakEvent Spec.Machine.RVP
         Spec.Machine.raiseExceptionWithInfo Spec.Machine.getCSRField Spec.Machine.setCSRField
         MetricMaterializeWithLeakage MetricMaterialize fst snd option_map
         getMachine getMetrics RiscvMachine.withLeakageEvent
         MetricRiscvMachine.withRegs MetricRiscvMachine.withPc MetricRiscvMachine.withNextPc
         RiscvMachine.withRegs RiscvMachine.withPc RiscvMachine.withNextPc updatePc
         RiscvMachine.getRegs RiscvMachine.getPc RiscvMachine.getNextPc RiscvMachine.getMem
         RiscvMachine.getXAddrs RiscvMachine.getLog RiscvMachine.getTrace
         reg_eqb remu add and xor maxUnsigned ZToReg MachineWidth_XLEN lnot] in H.

  (* the common tail of a retiring control micro-step, after the branch
     decision and the alignment test have been resolved in [HQ] and the
     granite side has been unfolded; [pc] is the riscv-coq pc variable *)
  Local Ltac ctrl_prep s l HF HD HR Hph HL :=
    pose proof (leak_retire s l _ _ HR Hph I) as HL;
    reduce_run1 HL; destruct HL as [_ HL]; unfold Memory.loadWord in HL; rewrite HF in HL;
    rewrite <- HD in HL; ctrl_reduce HL.

  Local Ltac ctrl_finish s HQ HL Hph :=
    unfold retired; rewrite (mstep_instr s _ _ _ Hph);
    eexists; split; [| split; [exact HQ | rewrite update_mmio_phase; reflexivity]];
    apply related_update_mmio;
    eapply related_idle; cbn [fst snd];
    [ right; reflexivity
    | unfold semantics.execute, semantics.stepCtrl, semantics.execCtrl, semantics.nextPc,
        semantics.assert_or_error, RecordSet.set, WIDTH
    | cbn [getTrace getMachine RiscvMachine.getTrace]; exact HL ].

  Lemma retire_ctrl : forall s l m Q x dmd inst,
      related (s, l) m -> run1_step m Q -> s.(semantics.Phase) = StepInstr inst ->
      (match inst with instrs.Ctrl _ => True | _ => False end) ->
      retired (mstep dmd s x) l Q.
  Proof.
    intros s l m Q x dmd inst HR HQ Hph Hcls.
    pose proof HR as HR0.
    inversion HR; subst; cbn in *.
    - match goal with Hd : _ \/ _ |- _ => destruct Hd as [Hd | Hd]; rewrite Hph in Hd; discriminate end.
    - match goal with HP : semantics.Phase s = StepInstr _ |- _ => rewrite Hph in HP; inversion HP; subst inst end.
      match goal with Hc : core_related s l m |- _ => rename Hc into Hcore end.
      destruct m as [[regs pc npc mem xaddrs log trace] metrics].
      reduce_run1 HQ.
      destruct HQ as [HX HQ]; specialize (HX eq_refl).
      pose proof (fetch_related s l _ Hcore HX) as HF; cbn [getMachine getMem getPc] in HF.
      unfold Memory.loadWord in HF; rewrite HF in HQ.
      set (w := baseMem.LoadWord (semantics.Pc (semantics.ArchSt s)) (semantics.Imem (semantics.ArchSt s))) in *.
      assert (Hdec : granite_decodes w) by (unfold granite_decodes; destruct (instrs.Decode.decode w); solve [exact I | exact Hcls]).
      pose proof (decode_agree w Hdec) as HD.
      destruct (instrs.Decode.decode w) as [si | ci | mi | w'] eqn:Egi;
      [ exfalso; exact Hcls | destruct ci | exfalso; exact Hcls | exfalso; exact Hcls ];
      cbn [to_riscv] in HD; rewrite <- HD in HQ; ctrl_reduce HQ;
      pose proof Hcore as Hc0;
      destruct Hc0 as [Hw Hreq Hresp Hint Hregs Hpc Hnpc Hmem Hlog];
      cbn [getMachine getRegs getPc getNextPc getMem getXAddrs getLog getTrace
           RiscvMachine.getRegs RiscvMachine.getPc RiscvMachine.getNextPc RiscvMachine.getMem
           RiscvMachine.getXAddrs RiscvMachine.getLog RiscvMachine.getTrace] in Hregs, Hpc, Hnpc, Hmem, Hlog.
      + (* beq *)
        ctrl_prep s l HF HD HR0 Hph HL.
        rewrite !(regs_related_get _ _ _ Hregs) in HQ, HL.
        unfold signExtend in HQ, HL; rewrite ?bits.smod_unsigned in HQ, HL.
        rewrite aligned_agree in HQ, HL.
        revert HQ HL.
        match goal with |- context [when (@Zmod.eqb ?md ?a ?b) _] =>
          destruct (@Zmod.eqb md a b) eqn:Heqb;
          [ pose proof (proj1 (Zmod.eqb_eq a b) Heqb) as Heq
          | assert (Hne : a <> b) by (intro E; apply (proj2 (@Zmod.eqb_eq md a b)) in E; congruence) ] end;
        cbn [when];
        [ match goal with |- context [semantics.is_word_aligned 4 ?t] =>
            destruct (semantics.is_word_aligned 4 t) eqn:Hal end; cbn [negb] |];
        intros HQ HL; ctrl_reduce HQ; ctrl_reduce HL.
        * (* taken, aligned *)
          ctrl_finish s HQ HL Hph.
          case_bool_decide; [| contradiction].
          rewrite <- Hpc, Hal. cbn [fst snd].
          constructor; cbn;
          [ exact Hw | exact Hreq | exact Hresp | exact Hint | exact Hregs
          | first [reflexivity | rewrite lit4; reflexivity]
          | first [reflexivity | rewrite lit4; reflexivity]
          | exact Hmem | exact Hlog ].
        * (* taken, misaligned: riscv-coq traps, which this platform cannot do *)
          exfalso; exact HQ.
        * (* not taken *)
          ctrl_finish s HQ HL Hph.
          case_bool_decide; [contradiction |]. cbn [fst snd].
          constructor; cbn;
          [ exact Hw | exact Hreq | exact Hresp | exact Hint | exact Hregs
          | rewrite Hnpc, lit4; reflexivity
          | rewrite Hnpc, lit4; reflexivity
          | exact Hmem | exact Hlog ].
      + (* jalr *)
        ctrl_prep s l HF HD HR0 Hph HL.
        rewrite !(regs_related_get _ _ _ Hregs) in HQ, HL.
        unfold signExtend in HQ, HL; rewrite ?bits.smod_unsigned in HQ, HL.
        rewrite lnot1, aligned_agree in HQ, HL.
        revert HQ HL.
        match goal with |- context [semantics.is_word_aligned 4 ?t] =>
          destruct (semantics.is_word_aligned 4 t) eqn:Hal end; cbn [negb];
        intros HQ HL; ctrl_reduce HQ; ctrl_reduce HL.
        * (* aligned *)
          ctrl_finish s HQ HL Hph.
          rewrite Hal. cbn [fst snd].
          constructor; cbn;
          [ exact Hw | exact Hreq | exact Hresp | exact Hint
          | eapply regs_related_set'; [| exact Hregs]; rewrite lit4, Hpc; reflexivity
          | first [reflexivity | rewrite lit4; reflexivity]
          | first [reflexivity | rewrite lit4; reflexivity]
          | exact Hmem | exact Hlog ].
        * exfalso; exact HQ.
      + (* bne *)
        ctrl_prep s l HF HD HR0 Hph HL.
        rewrite !(regs_related_get _ _ _ Hregs) in HQ, HL.
        unfold signExtend in HQ, HL; rewrite ?bits.smod_unsigned in HQ, HL.
        rewrite aligned_agree in HQ, HL.
        revert HQ HL.
        match goal with |- context [when (negb (@Zmod.eqb ?md ?a ?b)) _] =>
          destruct (@Zmod.eqb md a b) eqn:Heqb;
          [ pose proof (proj1 (Zmod.eqb_eq a b) Heqb) as Heq
          | assert (Hne : a <> b) by (intro E; apply (proj2 (@Zmod.eqb_eq md a b)) in E; congruence) ] end;
        cbn [negb when];
        [ | match goal with |- context [semantics.is_word_aligned 4 ?t] =>
              destruct (semantics.is_word_aligned 4 t) eqn:Hal end; cbn [negb] ];
        intros HQ HL; ctrl_reduce HQ; ctrl_reduce HL.
        * (* not taken *)
          ctrl_finish s HQ HL Hph.
          case_bool_decide; [contradiction |]. cbn [fst snd].
          constructor; cbn;
          [ exact Hw | exact Hreq | exact Hresp | exact Hint | exact Hregs
          | rewrite Hnpc, lit4; reflexivity
          | rewrite Hnpc, lit4; reflexivity
          | exact Hmem | exact Hlog ].
        * (* taken, aligned *)
          ctrl_finish s HQ HL Hph.
          case_bool_decide; [| contradiction].
          rewrite <- Hpc, Hal. cbn [fst snd].
          constructor; cbn;
          [ exact Hw | exact Hreq | exact Hresp | exact Hint | exact Hregs
          | first [reflexivity | rewrite lit4; reflexivity]
          | first [reflexivity | rewrite lit4; reflexivity]
          | exact Hmem | exact Hlog ].
        * exfalso; exact HQ.
    - match goal with Hi : inflight_related _ _ |- _ =>
        destruct (inflight_phase _ _ Hi) as [req Hw]; cbn in Hw; rewrite Hph in Hw; discriminate end.
  Qed.

  (* memory: a non-MMIO access retires; an MMIO access issues its request and
     waits, with the request in the buffer *)
  Lemma retire_mem : forall s l m Q x dmd inst,
      related (s, l) m -> run1_step m Q -> s.(semantics.Phase) = StepInstr inst ->
      (match inst with instrs.Mem _ => True | _ => False end) ->
      retired (mstep dmd s x) l Q \/
      (related (mstep dmd s x, l) m /\
       exists req, (mstep dmd s x).(semantics.Phase) = StepWaitMMIOResp req /\
                   (mstep dmd s x).(semantics.MMIOReqBuffer) <> []).
  Proof. (* ADMIT: misaligned access (no_misaligned_access) and MMIO wait phases *) Admitted.

  Lemma retire_csr_or_invalid : forall s l m Q inst,
      related (s, l) m -> run1_step m Q -> s.(semantics.Phase) = StepInstr inst ->
      (match inst with instrs.Strt (instrs.Csrrw _ _ _) | instrs.InvalidInstr _ => True | _ => False end) ->
      False.
  Proof.
    intros s l m Q inst HR HQ Hph Hcls.
    inversion HR; subst; cbn in *.
    - match goal with Hd : _ \/ _ |- _ => destruct Hd as [Hd | Hd]; rewrite Hph in Hd; discriminate end.
    - match goal with HP : semantics.Phase s = StepInstr _ |- _ => rewrite Hph in HP; inversion HP; subst inst end.
      match goal with Hc : core_related s l m |- _ =>
      destruct m as [[regs pc npc mem xaddrs log trace] metrics];
      reduce_run1 HQ;
      destruct HQ as [HX HQ]; specialize (HX eq_refl);
      pose proof (fetch_related s l _ Hc HX) as HF; cbn [getMachine getMem getPc] in HF;
      unfold Memory.loadWord in HF; rewrite HF in HQ;
      set (w := baseMem.LoadWord (semantics.Pc (semantics.ArchSt s)) (semantics.Imem (semantics.ArchSt s))) in *;
      destruct (instrs.Decode.decode w) as [si | ci | mi | w'] eqn:Egi;
      [ destruct si; try (exfalso; exact Hcls) | exfalso; exact Hcls | exfalso; exact Hcls | ]
      end.
      + (* csrrw: on this platform reading the privilege mode is impossible *)
        assert (Hdec : granite_decodes w) by (unfold granite_decodes; rewrite Egi; exact I).
        pose proof (decode_agree w Hdec) as HD. rewrite Egi in HD. cbn [to_riscv] in HD.
        rewrite <- HD in HQ.
        cbn [LeakageOfInstr.leakage_of_instr LeakageOfInstr.instr_leakage Return free.Monad_free
             free.bind free.interp_fix free.interp_body interp_action interpret_action
             Execute.execute ExecuteCSR.execute ExecuteCSR.checkPermissions
             Spec.Machine.getPrivMode Spec.Machine.leakEvent Spec.Machine.RVP
             MetricMaterializeWithLeakage MetricMaterialize fst snd option_map
             getMachine getMetrics RiscvMachine.withLeakageEvent] in HQ.
        exact HQ.
      + (* an instruction granite does not implement: excluded by isa_coverage *)
        pose proof (isa_coverage (s, l) _ w HR) as HC. cbn [getMachine getMem getPc] in HC.
        unfold Memory.loadWord in HC. specialize (HC HF).
        unfold granite_decodes in HC. rewrite Egi in HC. exact HC.
    - match goal with Hi : inflight_related _ _ |- _ =>
        destruct (inflight_phase _ _ Hi) as [req Hw]; cbn in Hw; rewrite Hph in Hw; discriminate end.
  Qed.


  Lemma mretire : forall s l m Q x dmd inst,
      related (s, l) m -> run1_step m Q -> s.(semantics.Phase) = StepInstr inst ->
      retired (mstep dmd s x) l Q \/
      (related (mstep dmd s x, l) m /\
       exists req, (mstep dmd s x).(semantics.Phase) = StepWaitMMIOResp req /\
                   (mstep dmd s x).(semantics.MMIOReqBuffer) <> []).
  Proof.
    intros s l m Q x dmd inst HR HQ Hph.
    destruct inst as [si | ci | mi | w'].
    - destruct si;
        first [ left; exact (retire_alu s l m Q x dmd _ HR HQ Hph I)
              | left; exact (retire_mul s l m Q x dmd _ HR HQ Hph I)
              | exfalso; exact (retire_csr_or_invalid s l m Q _ HR HQ Hph I) ].
    - left. exact (retire_ctrl s l m Q x dmd _ HR HQ Hph I).
    - exact (retire_mem s l m Q x dmd _ HR HQ Hph I).
    - exfalso. exact (retire_csr_or_invalid s l m Q _ HR HQ Hph I).
  Qed.

  (* [StepWaitMMIOResp]: retire when a response is buffered, else stutter in place *)
  Lemma mwait : forall s l m Q x dmd req,
      related (s, l) m -> run1_step m Q -> s.(semantics.Phase) = StepWaitMMIOResp req ->
      retired (mstep dmd s x) l Q \/
      (related (mstep dmd s x, l) m /\ (mstep dmd s x).(semantics.Phase) = StepWaitMMIOResp req).
  Proof. (* ADMIT: MMIO wait phases *) Admitted.

  (* one micro-step from any related state: retire (into [StepInterrupt]) or stutter *)
  Lemma mstep_sim : forall s l m Q x dmd,
      related (s, l) m -> run1_step m Q ->
      retired (mstep dmd s x) l Q \/ related (mstep dmd s x, l) m.
  Proof.
    intros s l m Q x dmd HR HQ.
    destruct (related_phase _ _ HR) as [Hph | [Hph | [[inst Hph] | [req Hph]]]].
    - right. apply (mstutter_leak s l m x dmd HR Hph).
    - right. apply (mstutter_interrupt s l m x dmd HR Hph).
    - destruct (mretire s l m Q x dmd inst HR HQ Hph) as [H | [H _]]; auto.
    - destruct (mwait s l m Q x dmd req HR HQ Hph) as [H | [H _]]; auto.
  Qed.

  (* after a retirement the next two micro-steps stutter (StepInterrupt, then StepLeak) *)
  Lemma msteps_after_retire : forall xs s l m2 dmd,
      (length xs <= 2)%nat ->
      related (s, l) m2 -> s.(semantics.Phase) = StepInterrupt ->
      related (msteps dmd xs s, l) m2.
  Proof.
    intros xs s l m2 dmd Hlen HR Hph.
    destruct xs as [| a [| b [| c rest]]]; cbn in Hlen; try lia; unfold msteps; cbn.
    - exact HR.
    - apply (mstutter_interrupt s l m2 a dmd HR Hph).
    - destruct (mstutter_interrupt s l m2 a dmd HR Hph) as [HR1 Hph1].
      apply (mstutter_leak _ l m2 b dmd HR1 Hph1).
  Qed.

  (* at most three micro-steps from a related state: one retirement or none *)
  Lemma msteps_sim : forall xs s l m Q dmd,
      (length xs <= 3)%nat ->
      related (s, l) m -> run1_step m Q ->
      (exists m2, related (msteps dmd xs s, l) m2 /\ Q m2) \/ related (msteps dmd xs s, l) m.
  Proof.
    intros xs s l m Q dmd Hlen HR HQ.
    destruct xs as [| a [| b [| c [| d rest]]]]; cbn in Hlen; try lia.
    - right. exact HR.
    - destruct (mstep_sim s l m Q a dmd HR HQ) as [[m2 [HR2 [HQ2 _]]] | HR2].
      + left. eauto.
      + right. exact HR2.
    - destruct (mstep_sim s l m Q a dmd HR HQ) as [[m2 [HR2 [HQ2 Hph2]]] | HR2].
      + left. exists m2. split; [| exact HQ2].
        exact (msteps_after_retire [b] _ l m2 dmd ltac:(cbn; lia) HR2 Hph2).
      + destruct (mstep_sim _ l m Q b dmd HR2 HQ) as [[m2 [HR3 [HQ3 _]]] | HR3].
        * left. eauto.
        * right. exact HR3.
    - destruct (mstep_sim s l m Q a dmd HR HQ) as [[m2 [HR2 [HQ2 Hph2]]] | HR2].
      + left. exists m2. split; [| exact HQ2].
        exact (msteps_after_retire [b; c] _ l m2 dmd ltac:(cbn; lia) HR2 Hph2).
      + destruct (mstep_sim _ l m Q b dmd HR2 HQ) as [[m2 [HR3 [HQ3 Hph3]]] | HR3].
        * left. exists m2. split; [| exact HQ3].
          exact (msteps_after_retire [c] _ l m2 dmd ltac:(cbn; lia) HR3 Hph3).
        * destruct (mstep_sim _ l m Q c dmd HR3 HQ) as [[m2 [HR4 [HQ4 _]]] | HR4].
          { left. eauto. }
          { right. exact HR4. }
  Qed.

  (** *** The measure across the cycle *)

  Lemma phase_measure_set_default : forall s nd,
      phase_measure (s <| semantics.DefaultMachine := nd |>) = phase_measure s.
  Proof. intros. unfold phase_measure, RecordSet.set. reflexivity. Qed.
  Lemma phase_measure_update_mmio : forall s dmd,
      phase_measure (semantics.update_mmio s dmd) = phase_measure s.
  Proof.
    intros. unfold phase_measure, semantics.update_mmio, RecordSet.set. cbn.
    destruct (semantics.Phase s); try reflexivity.
    destruct (semantics.MMIOReqBuffer s); [destruct (semantics.MMIORespBuffer s) |]; reflexivity.
  Qed.
  Lemma phase_measure_prologue_nonwait : forall s i,
      (forall req, s.(semantics.Phase) <> StepWaitMMIOResp req) ->
      phase_measure (prologue s i) = phase_measure s.
  Proof.
    intros s i H. unfold phase_measure. rewrite prologue_phase.
    destruct (semantics.Phase s) eqn:E; try reflexivity. exfalso. eapply H. reflexivity.
  Qed.

  (* one stuttering micro-step decreases the measure, except that a waiting
     state may keep waiting *)
  Lemma mstep_measure : forall s l m Q x dmd,
      related (s, l) m -> run1_step m Q ->
      retired (mstep dmd s x) l Q \/
      (related (mstep dmd s x, l) m /\
       ((phase_measure (mstep dmd s x) < phase_measure s)%nat \/
        exists req, (mstep dmd s x).(semantics.Phase) = StepWaitMMIOResp req)).
  Proof.
    intros s l m Q x dmd HR HQ.
    destruct (related_phase _ _ HR) as [Hph | [Hph | [[inst Hph] | [req Hph]]]].
    - destruct (mstutter_leak s l m x dmd HR Hph) as [HR' [inst Hph']].
      right. split; [exact HR' |]. left.
      set (s' := mstep dmd s x) in *; clearbody s'.
      unfold phase_measure. rewrite Hph, Hph'. lia.
    - destruct (mstutter_interrupt s l m x dmd HR Hph) as [HR' Hph'].
      right. split; [exact HR' |]. left.
      set (s' := mstep dmd s x) in *; clearbody s'.
      unfold phase_measure. rewrite Hph, Hph'. lia.
    - destruct (mretire s l m Q x dmd inst HR HQ Hph) as [H | [HR' [req [Hph' Hbuf]]]]; [left; exact H |].
      right. split; [exact HR' |]. left.
      set (s' := mstep dmd s x) in *; clearbody s'.
      unfold phase_measure. rewrite Hph, Hph'.
      destruct (semantics.MMIOReqBuffer s'); [exfalso; apply Hbuf; reflexivity | lia].
    - destruct (mwait s l m Q x dmd req HR HQ Hph) as [H | [HR' Hph']]; [left; exact H |].
      right. split; [exact HR' | right]. eauto.
  Qed.

  (* at most three micro-steps, at least one, from a related state that is not
     waiting on MMIO: a retirement or a measure decrease *)
  Lemma msteps_measure : forall xs s l m Q dmd,
      xs <> [] -> (length xs <= 3)%nat ->
      (forall req, s.(semantics.Phase) <> StepWaitMMIOResp req) ->
      related (s, l) m -> run1_step m Q ->
      (exists m2, related (msteps dmd xs s, l) m2 /\ Q m2) \/
      (related (msteps dmd xs s, l) m /\ (phase_measure (msteps dmd xs s) < phase_measure s)%nat).
  Proof.
    intros xs s l m Q dmd Hne Hlen Hnw HR HQ.
    pose proof (nonwait_measure_ge s Hnw) as Hge.
    (* a state below [s] stays below [s] after a stutter *)
    assert (Hdec : forall s1 s2, (phase_measure s1 < phase_measure s)%nat ->
              ((phase_measure s2 < phase_measure s1)%nat \/
               exists req, s2.(semantics.Phase) = StepWaitMMIOResp req) ->
              (phase_measure s2 < phase_measure s)%nat).
    { intros s1 s2 H1 [H2 | [req H2]]; [lia | pose proof (wait_measure_le _ _ H2); lia]. }
    assert (Hdec0 : forall s2,
              ((phase_measure s2 < phase_measure s)%nat \/
               exists req, s2.(semantics.Phase) = StepWaitMMIOResp req) ->
              (phase_measure s2 < phase_measure s)%nat).
    { intros s2 [H2 | [req H2]]; [lia | pose proof (wait_measure_le _ _ H2); lia]. }
    destruct xs as [| a [| b [| c [| d rest]]]]; cbn in Hlen; try lia; [exfalso; apply Hne; reflexivity | ..];
      unfold msteps; cbn [fold_left].
    - destruct (mstep_measure s l m Q a dmd HR HQ) as [[m2 [HR2 [HQ2 _]]] | [HR2 Hm2]].
      + left. eauto.
      + right. split; [exact HR2 | exact (Hdec0 _ Hm2)].
    - destruct (mstep_measure s l m Q a dmd HR HQ) as [[m2 [HR2 [HQ2 Hph2]]] | [HR2 Hm2]].
      + left. exists m2. split; [| exact HQ2].
        exact (msteps_after_retire [b] _ l m2 dmd ltac:(cbn; lia) HR2 Hph2).
      + pose proof (Hdec0 _ Hm2) as Hlt2.
        destruct (mstep_measure _ l m Q b dmd HR2 HQ) as [[m2 [HR3 [HQ3 _]]] | [HR3 Hm3]].
        * left. eauto.
        * right. split; [exact HR3 | exact (Hdec _ _ Hlt2 Hm3)].
    - destruct (mstep_measure s l m Q a dmd HR HQ) as [[m2 [HR2 [HQ2 Hph2]]] | [HR2 Hm2]].
      + left. exists m2. split; [| exact HQ2].
        exact (msteps_after_retire [b; c] _ l m2 dmd ltac:(cbn; lia) HR2 Hph2).
      + pose proof (Hdec0 _ Hm2) as Hlt2.
        destruct (mstep_measure _ l m Q b dmd HR2 HQ) as [[m2 [HR3 [HQ3 Hph3]]] | [HR3 Hm3]].
        * left. exists m2. split; [| exact HQ3].
          exact (msteps_after_retire [c] _ l m2 dmd ltac:(cbn; lia) HR3 Hph3).
        * pose proof (Hdec _ _ Hlt2 Hm3) as Hlt3.
          destruct (mstep_measure _ l m Q c dmd HR3 HQ) as [[m2 [HR4 [HQ4 _]]] | [HR4 Hm4]].
          { left. eauto. }
          { right. split; [exact HR4 | exact (Hdec _ _ Hlt3 Hm4)]. }
  Qed.

  (* a fair cycle from an MMIO wait: the prologue sends the pending request
     (ready) or delivers the response (valid), and a delivered response
     retires at the first micro-step; the measure counts these two cycles *)
  Lemma wait_cycle_progress : forall s l m Q i req,
      related (s, l) m -> run1_step m Q -> s.(semantics.Phase) = StepWaitMMIOResp req -> fair i ->
      (exists m2, related (next (s, l) i) m2 /\ Q m2) \/
      (related (next (s, l) i) m /\ (measure (next (s, l) i) < measure (s, l))%nat).
  Proof. (* ADMIT: MMIO wait phases *) Admitted.

  Lemma cycle_sim_i : forall g m Q i,
      related g m -> run1_step m Q -> admissible i ->
      (exists m2, related (next g i) m2 /\ Q m2) \/ related (next g i) m.
  Proof.
    intros g m Q i HR HQ Hi.
    assert (Hnext : next g i =
      ((semantics.update_mmio (msteps (dmd_of g i) (snd i).(DriverOut_nSteps) (prologue (fst g) i)) (dmd_of g i))
         <| semantics.DefaultMachine := nd_of g i |>, cycle_mmio (fst g) i ++ snd g)).
    { rewrite <- next_unfold. unfold next at 2. reflexivity. }
    rewrite Hnext.
    destruct g as [s l]. cbn [fst snd] in *.
    pose proof (related_prologue s l m i HR Hi) as HRp.
    destruct Hi as [_ Hlen].
    destruct (msteps_sim _ _ _ m Q (dmd_of (s, l) i) Hlen HRp HQ) as [[m2 [HR2 HQ2]] | HR2].
    - left. exists m2. split; [| exact HQ2].
      apply related_set_default. apply related_update_mmio. exact HR2.
    - right. apply related_set_default. apply related_update_mmio. exact HR2.
  Qed.

  Lemma cycle_sim_fair_i : forall g m Q i,
      related g m -> run1_step m Q -> fair i ->
      (exists m2, related (next g i) m2 /\ Q m2) \/
      (related (next g i) m /\ (measure (next g i) < measure g)%nat).
  Proof.
    intros g m Q i HR HQ Hf.
    assert (Hnext : next g i =
      ((semantics.update_mmio (msteps (dmd_of g i) (snd i).(DriverOut_nSteps) (prologue (fst g) i)) (dmd_of g i))
         <| semantics.DefaultMachine := nd_of g i |>, cycle_mmio (fst g) i ++ snd g)).
    { rewrite <- next_unfold. unfold next at 2. reflexivity. }
    destruct g as [s l].
    destruct (related_phase _ _ HR) as [Hph | [Hph | [[inst Hph] | [req Hph]]]]; cbn [fst] in Hph;
      [ | | | exact (wait_cycle_progress s l m Q i req HR HQ Hph Hf) ];
      (assert (Hnw : forall req, s.(semantics.Phase) <> StepWaitMMIOResp req) by (intros req' E; rewrite Hph in E; discriminate));
      destruct Hf as [Hi [Hne [_ _]]];
      pose proof (related_prologue s l m i HR Hi) as HRp;
      destruct Hi as [_ Hlen];
      (assert (Hnwp : forall req, (prologue s i).(semantics.Phase) <> StepWaitMMIOResp req)
        by (rewrite prologue_phase; exact Hnw));
      rewrite Hnext; unfold measure; cbn [fst snd];
      (destruct (msteps_measure _ _ _ m Q (dmd_of (s, l) i) Hne Hlen Hnwp HRp HQ) as [[m2 [HR2 HQ2]] | [HR2 Hlt]];
       [ left; exists m2; split; [| exact HQ2]; apply related_set_default; apply related_update_mmio; exact HR2
       | right; split;
         [ apply related_set_default; apply related_update_mmio; exact HR2
         | rewrite phase_measure_set_default, phase_measure_update_mmio;
           rewrite (phase_measure_prologue_nonwait s i Hnw) in Hlt; exact Hlt ] ]).
  Qed.

  (* the two forms the generic section consumes *)
  Lemma cycle_sim : forall g m Q,
      related g m -> run1_step m Q ->
      granite_step g (fun g' => (exists m', related g' m' /\ Q m') \/ related g' m).
  Proof.
    intros g m Q HR HQ i Hi. exact (cycle_sim_i g m Q i HR HQ Hi).
  Qed.

  Lemma cycle_sim_fair : forall g m Q,
      related g m -> run1_step m Q ->
      granite_step_fair g (fun g' => (exists m', related g' m' /\ Q m') \/
                                     (related g' m /\ measure g' < measure g)).
  Proof.
    intros g m Q HR HQ i Hi. exact (cycle_sim_fair_i g m Q i HR HQ Hi).
  Qed.

  (** ** Corollaries: two-line applications of the generic section *)

  Definition lift_g : (MetricRiscvMachine -> Prop) -> GState -> Prop := lift related.

  (* [always] transfer, the shape bedrock2's end-to-end pipeline consumes
     (an invariant preserved by [run1]) *)
  Corollary granite_always : forall (P : MetricRiscvMachine -> Prop) g m,
      related g m ->
      always run1_step P m ->
      always granite_step (lift_g P) g.
  Proof.
    intros P g m HR H.
    exact (transfer_always run1_step granite_step related granite_step_weaken cycle_sim P m g HR H).
  Qed.

  (* [eventually]/[runsTo] transfer: granite reaches, in finitely many cycles
     along any admissible inputs, a state related to a riscv-coq state satisfying [P] *)
  Corollary granite_eventually : forall (P : MetricRiscvMachine -> Prop) g m,
      related g m ->
      eventually run1_step P m ->
      eventually granite_step_fair (lift_g P) g.
  Proof.
    intros P g m HR H.
    exact (transfer_eventually run1_step granite_step_fair related measure cycle_sim_fair P m g HR H).
  Qed.

  Corollary granite_runsTo : forall (P : MetricRiscvMachine -> Prop) g m,
      related g m ->
      runsTo run1_step m P ->
      eventually granite_step_fair (lift_g P) g.
  Proof.
    intros P g m HR H.
    exact (transfer_runsTo run1_step granite_step_fair related measure cycle_sim_fair P m g HR H).
  Qed.

  (* the bedrock2 event-loop shape ([always (eventually good_trace)],
     [CompilerInvariant.always_eventually_good_trace]; fiat-crypto's
     [garagedoor_correct]) *)
  Corollary granite_always_eventually : forall (P : MetricRiscvMachine -> Prop) g m,
      related g m ->
      always run1_step (eventually run1_step P) m ->
      always granite_step (eventually granite_step_fair (lift_g P)) g.
  Proof.
    intros P g m HR H.
    exact (transfer_always_eventually run1_step granite_step granite_step_fair related measure
             granite_step_weaken cycle_sim cycle_sim_fair P m g HR H).
  Qed.

  (** ** Composition with a trace property (GarageDoor / End2EndLightbulb shape) *)

  (* a property of the abstracted MMIO log, stated on both sides *)
  Context (io_spec : list MMIOEvent -> Prop).
  Context (io_spec_riscv : list LogItem -> Prop).
  Hypothesis io_spec_compat : forall l l', log_related l l' -> (io_spec_riscv l' <-> io_spec l).

  (* From fiat-crypto's [garagedoor_correct]:
       initial_conditions m -> always run1 (eventually run1 (fun m' => io_spec (getLog m'))) m
     and an initial granite state related to such an [m], the granite machine
     always eventually has a log satisfying [io_spec].  The remaining
     ingredient, not stated here because it needs fiat-crypto as a dependency,
     is the initial-state lemma: from [pub_init]/[sec_init] holding the compiled
     program at the code start (with [Dmem] agreeing with [Imem] on the code
     range) build an [m] with [initial_conditions m /\ related (init, []) m]. *)
  Corollary granite_io_spec : forall g m,
      related g m ->
      always run1_step (eventually run1_step (fun m' => io_spec_riscv m'.(getLog))) m ->
      always granite_step (eventually granite_step_fair (fun g' => io_spec (snd g'))) g.
  Proof.
    intros g m HR H.
    pose proof (granite_always_eventually _ g m HR H) as H'.
    (* ADMIT: MMIO wait phases (roadblock, not a discrepancy).  The weakening
       from [lift_g (fun m' => io_spec_riscv (getLog m'))] to [io_spec (snd g')]
       needs [log_related (snd g') (getLog m')] for every [related g' m'].
       Idle and post-leak states have it ([cr_log]); a waiting state does not:
       granite logs an MMIO store when the request leaves the buffer, riscv-coq
       when the instruction completes, so during the wait the two logs differ
       by that event.  The states that [transfer_eventually] produces are never
       waiting (a retirement lands in [StepInterrupt]), but the generic section
       does not record that.  The fix is to give the generic section a second
       relation for the retirement targets (or to strengthen [related] in the
       [retired] clause) and to prove [log_related] for those; that changes
       [cycle_sim]'s statement and is left for the MMIO wait work. *)
    admit.
  Admitted.

End Connection.
