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
From coqutil Require Import Map.Interface Word.Bitwidth Byte Z.BitOps Z.bitblast.
From coqutil Require Semantics.OmniSmallstepCombinators.
From riscv Require Import Utility.Utility Utility.Monads Spec.Decode
  Spec.Primitives Spec.LeakageOfInstr Platform.RiscvMachine
  Platform.MetricRiscvMachine Platform.Run Utility.MkMachineWidth
  Utility.runsToNonDet Utility.Words32Naive Utility.FreeMonad
  Platform.MetricLogging Platform.MaterializeRiscvProgram
  Platform.MetricMaterializeRiscvProgram Platform.MinimalMMIO Platform.MetricMinimalMMIO.
From riscv Require Spec.Machine.
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
  Context {Registers : map.map Z word} {Mem : map.map word byte}.
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

  (* the MMIO events of one clock cycle, read off the ready/valid handshake of
     [Spec.v] ([consumeMMIOReq], [consumeMMIOResp], [update_mmio]): a store when
     its request is accepted, a load when its response is accepted *)
  Context (cycle_mmio : GSt -> GInput -> list MMIOEvent).

  (* Which per-cycle inputs the theorems quantify over.  RESTRICTIONS (not
     discrepancies): riscv-coq has no interrupts, so no input asserts one; and
     one cycle executes at most one driver micro-step, so that a cycle retires
     at most one instruction (a driver list of length 3 would retire a whole
     instruction, of length 6 two; the one-step [core] shape needs at most one). *)
  Definition admissible (i : GInput) : Prop :=
    (fst (fst i)).(PubInput_interruptValid) = false /\
    (length (snd i).(DriverOut_nSteps) <= 1)%nat.

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

  Definition regs_related (rf : registerFile.RegFile) (rr : Registers) : Prop :=
    forall i : Z, (0 < i < 32)%Z ->
      map.get rr i = Some (registerFile.readReg (bits.of_Z LOG_NREGS i) rf).

  (* granite is Harvard (separate [Imem]/[Dmem], both total); riscv-coq has one
     partial byte map plus the executable-address set [getXAddrs].  Relate the
     data memory everywhere outside MMIO, and require the instruction memory to
     agree with it on the executable addresses.  A riscv-coq store removes its
     addresses from [getXAddrs], so this is preserved; a fetch requires
     [isXAddr4], so it reads the same bytes granite fetches from [Imem]. *)
  Definition mem_related (imem dmem : baseMem.Mem) (xaddrs : list word) (m : Mem) : Prop :=
    (forall a, ~ isMMIOAddr_g a -> map.get m a = Some (to_byte (baseMem.load_byte (to_N a) dmem))) /\
    (forall a, isMMIOAddr_g a -> map.get m a = None) /\
    (forall a, In a xaddrs -> baseMem.load_byte (to_N a) dmem = baseMem.load_byte (to_N a) imem).

  (* the abstracted granite log is the abstraction of riscv-coq's [getLog]
     (bedrock2's [mmio_trace_abstraction_relation], stated here abstractly) *)
  Context (log_related : list MMIOEvent -> list LogItem -> Prop).

  (* OPEN ISSUE (leakage): granite's per-instruction leakage versus riscv-coq's
     [getTrace].  For all instructions but [mul], granite's event is a function
     of riscv-coq's ([LeakageOfInstr]); granite's [mul] additionally leaks
     whether an operand is zero.  Stated abstractly until aligned. *)
  Context (leak_related : IFC.L_leakage -> option (list LeakageOfInstr.LeakageEvent) -> Prop).
  (* the leakage granite has produced so far is not in [St] either; it is a
     function of the execution, abstracted here *)
  Context (granite_leaks : GState -> IFC.L_leakage).

  (* in-flight states: granite between the micro-steps of one instruction
     ([StepInstr], [StepWaitMMIOResp], [StepInterrupt] phases), related to the
     riscv-coq state BEFORE the instruction; one constructor per phase in the
     real development *)
  Context (inflight_related : GState -> MetricRiscvMachine -> Prop).

  (* metrics are not related (as in bedrock2's Kami connection, [getMetrics] is unconstrained) *)
  Inductive related : GState -> MetricRiscvMachine -> Prop :=
  | related_idle : forall (g : GState) (m : MetricRiscvMachine),
      (fst g).(semantics.Phase) = StepLeak ->
      (fst g).(semantics.MMIOReqBuffer) = [] ->
      (fst g).(semantics.MMIORespBuffer) = [] ->
      (fst g).(semantics.InterruptSt) = None ->
      regs_related (fst g).(semantics.ArchSt).(semantics.Rf) m.(getRegs) ->
      m.(getPc) = (fst g).(semantics.ArchSt).(semantics.Pc) ->
      m.(getNextPc) = Zmod.add (fst g).(semantics.ArchSt).(semantics.Pc) (bits.of_Z 32 4) ->
      mem_related (fst g).(semantics.ArchSt).(semantics.Imem)
                  (fst g).(semantics.ArchSt).(semantics.Dmem) m.(getXAddrs) m.(getMem) ->
      log_related (snd g) m.(getLog) ->
      leak_related (granite_leaks g) m.(getTrace) ->
      related g m
  | related_inflight : forall (g : GState) (m : MetricRiscvMachine), inflight_related g m -> related g m.

  (** ** Assumptions standing in for the open issues of granite#1 *)

  (* the word riscv-coq fetches next, if any *)
  Definition next_instr (m : MetricRiscvMachine) : option Instruction :=
    match Memory.loadWord m.(getMem) m.(getPc) with
    | Some w => Some (decode iset (Zmod.unsigned w))
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
    unfold decode; cbv beta zeta;
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
     with shifted [Z.lor]s.  Provable by bit extensionality ([Z.bits_inj'] with
     [Z.lor_spec]/[Z.shiftl_spec]); decoder bookkeeping, not a discrepancy. *)
  Lemma b_imm_agree : forall w : word,
      Zmod.unsigned (Zmod.app (zeroes : bits 1)
                       (Zmod.app (Zmod.slice 8 12 w)
                          (Zmod.app (Zmod.slice 25 31 w)
                             (Zmod.app (Zmod.slice 7 8 w) (Zmod.slice 31 32 w)))))
      = Z.lor (Z.lor (Z.lor (Z.shiftl (Zmod.unsigned (Zmod.slice 31 32 w)) 12)
                            (Z.shiftl (Zmod.unsigned (Zmod.slice 25 31 w)) 5))
                     (Z.shiftl (Zmod.unsigned (Zmod.slice 8 12 w)) 1))
              (Z.shiftl (Zmod.unsigned (Zmod.slice 7 8 w)) 11).
  Proof. (* ADMIT: decoder immediate bookkeeping (B-type), not a discrepancy *) Admitted.

  (* [rewrite] must match [Zmod.unsigned] arguments up to conversion (the
     modulus annotations differ between granite's field types and the lemmas) *)
  Local Set Keyed Unification.

  Lemma decode_agree : forall w : word,
      granite_decodes w -> to_riscv (instrs.Decode.decode w) = decode iset (Zmod.unsigned w).
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

  (* OPEN ISSUE (progress, only for [eventually]): the driver schedules
     micro-steps and MMIO responses arrive, so that granite cannot stutter
     forever.  [measure] counts the cycles until the next instruction retires. *)
  Context (measure : GState -> nat).

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
  Lemma cycle_sim_i : forall g m Q i,
      related g m -> run1_step m Q -> admissible i ->
      (exists m', related (next g i) m' /\ Q m') \/
      (related (next g i) m /\ (fair i -> measure (next g i) < measure g)).
  Proof. Admitted.

  (* the two forms the generic section consumes *)
  Lemma cycle_sim : forall g m Q,
      related g m -> run1_step m Q ->
      granite_step g (fun g' => (exists m', related g' m' /\ Q m') \/ related g' m).
  Proof.
    intros g m Q HR HQ i Hi. destruct (cycle_sim_i g m Q i HR HQ Hi) as [H | [H _]]; eauto.
  Qed.

  Lemma cycle_sim_fair : forall g m Q,
      related g m -> run1_step m Q ->
      granite_step_fair g (fun g' => (exists m', related g' m' /\ Q m') \/
                                     (related g' m /\ measure g' < measure g)).
  Proof.
    intros g m Q HR HQ i Hi. destruct (cycle_sim_i g m Q i HR HQ (proj1 Hi)) as [H | [H Hlt]]; eauto.
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
    (* weaken [lift_g (fun m' => io_spec_riscv (getLog m'))] to [io_spec (snd g')]
       through [io_spec_compat] and the [log_related] component of [related] *)
    admit.
  Admitted.

End Connection.
