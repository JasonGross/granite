From stdpp Require Import base finite nmap stringmap vector.
From granite.core Require Import Bits.
From quartz.lang Require Import domain Syntax. (* Import (coercions) domain.Zmod. *)
From quartz.lang Require Import ident_to_string let_lift.
From quartz.examples Require Import Processor.
Import type.
From granite.core Require Import
  Tactics.

From granite.isaSpec Require Import
  Common
  Pipelined
  Pipelined_QuartzImpl
  QuartzLib.

Import domain.Zmod.
Import InterfaceExample.

Definition lift_fields (flds: interp Decode.DecodeFields) : IsaParams.DecodeFields :=
  let '(rs1Idx, (rs2Idx, (rdIdx, (csrIdx, (immI, (immS, (immB, (immU, (csr, (opcode, (funct3, (funct7, _)))))))))))) := flds in
    {| IsaParams.DOut_rs1Idx := rs1Idx;
           IsaParams.DOut_rs2Idx := rs2Idx;
           IsaParams.DOut_rdIdx := rdIdx;
           IsaParams.DOut_csrIdx := csrIdx;
           IsaParams.DOut_immI := immI;
           IsaParams.DOut_immS := immS;
           IsaParams.DOut_immB := immB;
           IsaParams.DOut_immU := immU;
           IsaParams.DOut_csr := csr;
           IsaParams.DOut_opcode := opcode;
           IsaParams.DOut_funct3 := funct3;
           IsaParams.DOut_funct7 := funct7 |}.
    (* Hint Rewrite unsigned_of_Z : zmod. *)
    (* Hint Rewrite Z_to_bv_unsigned : zmod. *)
Create HintDb bv_simp.
Hint Rewrite @bits.unsigned_slice using lia : bv_simp.
Hint Rewrite @Zmod.unsigned_of_Z : bv_simp.
Hint Rewrite @Zmod.signed_of_Z : bv_simp.
Hint Rewrite @Zmod.of_Z_unsigned : bv_simp.
(* Hint Rewrite @bv_concat_signed : bv_simp. *)
Lemma unsigned_skipn_0 {n} (x : bits n) : Zmod.unsigned (Zmod.skipn 0 x) = Zmod.unsigned x.
Proof.
  etransitivity; [apply bits.unsigned_skipn; lia|].
  rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
Qed.
Lemma firstn_skipn_0 {n} k (x : bits n) : Zmod.firstn k (Zmod.skipn 0 x) = Zmod.firstn k x.
Proof. apply Zmod.unsigned_inj. rewrite !bits.unsigned_firstn, unsigned_skipn_0. reflexivity. Qed.
Hint Rewrite @firstn_skipn_0 : bv_simp.
Lemma isMemEq: forall x,
 nonzero (Bits.mk_bit (IsaParams.IsMem x)) =
 nonzero
   (Zmod.or (Bits.mk_bit (Zmod.eqb x Decode.Inst_Store))
      (Bits.mk_bit (Zmod.eqb x Decode.Inst_Load))).
Proof.
  intro x.
  pose proof (elem_of_enum x) as Hin.
  repeat (setoid_rewrite elem_of_cons in Hin).
  rewrite elem_of_nil in Hin. vm_compute in Hin.
  repeat match goal with
  | [Hin : _ = _ ∨ _ |- _] => destruct Hin as [-> | Hin]
  | [Hin : False |- _] => contradiction
  end; reflexivity.
Qed.
Lemma bv_not_simp:
  forall (b: bits 1),
  embed_bool (negb (nonzero b)) = Zmod.not b.
Proof.
  intro b. apply Zmod.unsigned_inj.
  pose proof (elem_of_enum b) as Hin.
  repeat (setoid_rewrite elem_of_cons in Hin).
  rewrite elem_of_nil in Hin. vm_compute in Hin.
  destruct Hin as [->|[->|H]]; [reflexivity | reflexivity | contradiction].
Qed.
Lemma bv_not_simp':
  forall (b: bits 1),
  Bits.mk_bit (negb (nonzero b)) = Zmod.not b.
Proof. exact bv_not_simp. Qed.
Lemma bv_and_embed_bool:
  ∀ b1 b2 : bool,
    Zmod.and (embed_bool b1) ((embed_bool b2)) = embed_bool (b1 && b2).
Proof.
  intros. apply Zmod.unsigned_inj. destruct b1, b2; reflexivity. 
Qed.
From quartz.lang Require Import Syntax.
Import fn.
Import type.
Import Processor.
Import InterfaceExample.
  Import (notations) eexpr expr. Local Open Scope string_scope.

  Definition q_isMMIOAddr {var} : fn.fn var cpu.mword Bool :=
    Fn (fun (addr : var cpu.mword) => quartz_eexpr:(
      return ((32 'd Riscv.instrs.MMIO_BASE) <= #addr ) &
             (#addr < _ 'd Riscv.instrs.MMIO_TOP))).
Lemma mk_bit_bv_and:
  forall x y,
  Zmod.and (Bits.mk_bit x) (Bits.mk_bit y) = Bits.mk_bit (x && y).
Proof.
  intros x y. destruct x, y; apply Zmod.unsigned_inj; reflexivity.
Qed.


  Lemma isMMIOOk:
    fn.interp q_isMMIOAddr = @Riscv.instrs.params.isMMIOAddr _ Riscv.instrs.isaParams .
  Proof.
    apply FunctionalExtensionality.functional_extensionality.
    intros; cbn. 
    apply Zmod.unsigned_inj.
    rewrite mk_bit_bv_and.
    rewrite !Zmod.unsigned_of_Z.
    rewrite !Z.mod_small
      by (unfold Riscv.instrs.MMIO_BASE, Riscv.instrs.MMIO_TOP; lia).
    reflexivity.
  Qed.

Lemma embed_nonzero:
  forall (x: bits 1),
  embed_bool (nonzero x) = x.
Proof.
  intro x.
  pose proof (elem_of_enum x) as Hin.
  repeat (setoid_rewrite elem_of_cons in Hin).
  rewrite elem_of_nil in Hin. vm_compute in Hin.
  destruct Hin as [->|[->|H]]; [reflexivity | reflexivity | contradiction].
Qed.
Definition getFieldsEq:
  forall i,
  IsaParams.getFields i = lift_fields (fn.interp Decode.getFields i).
Proof.
  unfold lift_fields. intros.
  case_goal_match. cbn in f. destruct_pairs.
  cbn in Heqi0.  simplify_tupless.
  unfold IsaParams.getFields. cbn.
  repeat f_equal; autorewrite with bv_simp; auto.
  apply Zmod.unsigned_inj. symmetry. apply unsigned_skipn_0.
Qed.
Definition lift_instrProps (props: interp Decode.InstrProps) : IsaParams.InstrProps :=
  let '(rs1Valid, (rs2Valid, (rdValid, (itype, (immediateType, _))))) := props in
  {| IsaParams.rs1Valid := rs1Valid;
     IsaParams.rs2Valid := rs2Valid;
     IsaParams.rdValid := rdValid;
     IsaParams.itype := itype;
     IsaParams.immediateType := immediateType |}.

(* ------------------------------------------------------------------ *)
(* Helper lemmas relating bool_decide / decide conditions to           *)
(* the nonzero (bv_and (embed_bool ...)) form used by fn.interp        *)
(* ------------------------------------------------------------------ *)

(* nonzero (bv_and (embed_bool b1) (embed_bool b2)) = b1 && b2 *)
Lemma nonzero_and_embed_bool (b1 b2 : bool) :
  nonzero (Zmod.and (embed_bool b1) (embed_bool b2)) = b1 && b2.
Proof. destruct b1, b2; reflexivity. Qed.

(* nonzero (bv_and (bv_and (embed_bool b1) (embed_bool b2)) (embed_bool b3)) = b1 && b2 && b3 *)
Lemma nonzero_and3_embed_bool (b1 b2 b3 : bool) :
  nonzero (Zmod.and (Zmod.and (embed_bool b1) (embed_bool b2)) (embed_bool b3)) = b1 && b2 && b3.
Proof. destruct b1, b2, b3; reflexivity. Qed.

Lemma nonzero_or_embed_bool (b1 b2 : bool) :
  nonzero (Zmod.or (embed_bool b1) (embed_bool b2)) = b1 || b2.
Proof. destruct b1, b2; reflexivity. Qed.
Hint Rewrite @nonzero_or_embed_bool : bv_simp.

(* bool_decide (x = y) = (bv_unsigned x =? bv_unsigned y)  for bv n *)
(* bool_decide (x = y) = (bv_unsigned x =? bv_unsigned y)  for bv n *)
Lemma bool_decide_bv_unsigned_eq {n} (x y : bits n) :
  bool_decide (x = y) = (Zmod.unsigned x =? Zmod.unsigned y)%Z.
Proof.
  case_bool_decide; subst; auto.
  - rewrite Z.eqb_refl. reflexivity.
  - symmetry. rewrite Z.eqb_neq. rewrite <-Zmod.unsigned_inj_iff in H. auto.
Qed.
Hint Rewrite @bool_decide_bv_unsigned_eq : bv_simp.

(* bool_decide (x = a /\ y = b) = (bv_unsigned x =? bv_unsigned a) && (bv_unsigned y =? bv_unsigned b) *)
Lemma bool_decide_bv_and2 {n m} (x a : bits n) (y b : bits m) :
  bool_decide (x = a /\ y = b) =
  (Zmod.unsigned x =? Zmod.unsigned a)%Z && (Zmod.unsigned y =? Zmod.unsigned b)%Z.
Proof.
  rewrite bool_decide_and.
  repeat rewrite bool_decide_bv_unsigned_eq.
  reflexivity.
Qed.

(* bool_decide (x = a /\ y = b /\ z = c) = ... for triple conjunctions (ADD/MUL decode) *)
Lemma bool_decide_bv_and3 {n1 n2 n3} (x a : bits n1) (y b : bits n2) (z c : bits n3) :
  bool_decide (x = a /\ y = b /\ z = c) =
  (Zmod.unsigned x =? Zmod.unsigned a)%Z &&
  (Zmod.unsigned y =? Zmod.unsigned b)%Z &&
  (Zmod.unsigned z =? Zmod.unsigned c)%Z.
Proof.
  rewrite bool_decide_and, bool_decide_and.
  repeat rewrite bool_decide_bv_unsigned_eq.
  rewrite andb_assoc. reflexivity.
Qed.

(* Distribute lift_instrProps through if-else *)
Lemma lift_instrProps_if (b : bool) A B :
  lift_instrProps (if b then A else B) =
  if b then lift_instrProps A else lift_instrProps B.
Proof. destruct b; reflexivity. Qed.

(* bv_not (embed_bool b) = embed_bool (negb b)
   (embed_bool = bool_to_bv 1, so this is bv_not_bool_to_bv) *)
Lemma embed_bool_negb (b : bool) :
  Zmod.not (embed_bool b) = embed_bool (negb b).
Proof. apply Zmod.unsigned_inj. destruct b; reflexivity. Qed.

Opaque Decode.getFields.
Lemma lookupCSR_some: forall v,
  Utils.is_some (lookupCSR v) =
  nonzero (fn.interp Decode.lookupCSR v).
Proof.
  intros v.
  cbn [fn.interp Decode.lookupCSR eexpr.interp]. cbn.
  unfold Utils.is_some, lookupCSR.
  repeat rewrite nonzero_or_embed_bool.
  repeat rewrite bool_decide_bv_unsigned_eq.
  cbv [csrFile.CSR_mtvec csrFile.CSR_mepc csrFile.CSR_mcause
       csrFile.CSR_mtval csrFile.CSR_mie
       CSR_mtvec CSR_mepc CSR_mcause CSR_mtval CSR_mie Zmod.eqb].
  repeat rewrite Zmod.unsigned_of_Z.
  repeat rewrite Z.mod_small by lia.
  repeat rewrite unsigned_literal.
  cbv[mret option_ret].
  repeat match goal with
  | |- context[Z.eqb ?x ?y] =>
      let H := fresh in
      destruct (Z.eqb x y) eqn:H; try setoid_rewrite H
  end.
  all: vm_compute; reflexivity.
Qed.
Opaque Decode.lookupCSR.

Definition getInstrPropsEq:
  forall i,
  IsaParams.getInstrProps i = lift_instrProps (fn.interp Decode.getInstrProps i).
Proof.
  intros i.
  unfold IsaParams.getInstrProps. cbn.
  (* Normalize Quartz (RHS) conditions:
       nonzero (bv_and (embed_bool b1) (embed_bool b2)) → b1 && b2
       nonzero (bv_and (bv_and ...) (embed_bool b3)) → b1 && b2 && b3 *)
  repeat rewrite nonzero_and3_embed_bool.
  repeat rewrite nonzero_and_embed_bool.
  repeat rewrite nonzero_bool.
  repeat rewrite decide_bool_decide.
  (* Normalize Granite (LHS) conditions:
       decide (x = a /\ y = b) → (=?) && (=?) *)
  repeat (setoid_rewrite bool_decide_bv_and3 || setoid_rewrite bool_decide_bv_and2 ||
          setoid_rewrite bool_decide_bv_unsigned_eq).
  (* Both sides now have identical (=?)-based boolean conditions.
     Distribute lift_instrProps through the RHS if-else tree. *)
  repeat rewrite lift_instrProps_if.
  autorewrite with bv_simp.
  repeat match goal with
  | |- (if ?x then _ else _) = (if ?y then _ else _) =>
      replace x with y by reflexivity;
      case_goal_match; [cbn; f_equal; try apply Zmod.unsigned_inj; auto| ]
  end .
  { rewrite<-lookupCSR_some.
    unfold Utils.is_some. 
    destruct (lookupCSR (Zmod.slice 20 32 i)) eqn:?.
    - setoid_rewrite Heqo. f_equal; apply Zmod.unsigned_inj; done.
    - setoid_rewrite Heqo. f_equal; apply Zmod.unsigned_inj; done.
  }
  { cbn. f_equal; apply Zmod.unsigned_inj; auto. }
Qed.
Opaque Decode.getFields. Opaque IsaParams.getFields.
Opaque IsaParams.getInstrProps.
Opaque Decode.getInstrProps.
Lemma getImm_eq:
  forall x0 ,
  IsaParams.getImm (IsaParams.decode x0) =
  fn.interp Decode.getImm ((fn.interp Decode.getFields x0), fn.interp Decode.getInstrProps x0).
Proof.
  intros x0.
  unfold IsaParams.getImm, IsaParams.decode. cbn.
  (* Relate getInstrProps sides via getInstrPropsEq *)
  rewrite getInstrPropsEq.
  (* Destruct the props tuple to expose immediateType *)
  destruct (fn.interp Decode.getInstrProps x0) as (rs1v & rs2v & rdv & ity & immT & []).
  unfold lift_instrProps. cbn.
  (* Relate getFields sides via getFieldsEq *)
  rewrite getFieldsEq.
  destruct (fn.interp Decode.getFields x0) as
    (rs1Idx & rs2Idx & rdIdx & csrIdx & immI & immS & immB & immU & csr & opcode & funct3 & funct7 & []).
  unfold lift_fields. cbn.
  (* Normalize conditions on both sides to (=?) form *)
  repeat rewrite nonzero_and_embed_bool.
  repeat rewrite nonzero_bool.
  repeat rewrite decide_bool_decide.
  repeat (setoid_rewrite bool_decide_bv_and2 || setoid_rewrite bool_decide_bv_unsigned_eq).
  (* Both sides are now matching if-else trees *)
  repeat match goal with
  | |- (if ?x then _ else _) = (if ?y then _ else _) =>
      replace x with y by reflexivity;
      case_goal_match; [cbn; f_equal; try apply Zmod.unsigned_inj; auto| ]
  end .
  apply Zmod.unsigned_inj; reflexivity.
Qed.

Opaque IsaParams.getImm.
Opaque Decode.getImm.
Lemma execALU_eq:
  forall x0 rs1val rs2val csrval pc,
  IsaParams.execALU (IsaParams.decode x0) rs1val rs2val csrval pc =
  (let '(alu_out, (csr_out, _)) :=
     fn.interp Decode.execALU ((fn.interp Decode.getFields x0), (fn.interp Decode.getInstrProps x0, ((rs1val, (rs2val, (csrval, (pc, ()))))))) in
     (alu_out, csr_out)).
Proof.
  intros x0 rs1val rs2val csrval pc. cbn.
  unfold IsaParams.execALU. cbn.
  rewrite getInstrPropsEq.
  rewrite getFieldsEq.
  rewrite getImm_eq.
  (* Destruct props and fields tuples *)
  destruct (fn.interp Decode.getInstrProps x0) as (rs1v & rs2v & rdv & ity & immT & []).
  destruct (fn.interp Decode.getFields x0) as
    (rs1Idx & rs2Idx & rdIdx & csrIdx & immI & immS & immB & immU & csr & opcode & funct3 & funct7 & []).
  unfold lift_instrProps, lift_fields. cbn.
  (* Normalize conditions *)
  repeat rewrite nonzero_and_embed_bool.
  repeat rewrite nonzero_bool.
  repeat rewrite decide_bool_decide.
  repeat (setoid_rewrite bool_decide_bv_and2 || setoid_rewrite bool_decide_bv_unsigned_eq).
  repeat match goal with
  | |- (if ?x then _ else _) = (let '(_, _) := (if ?y then _ else _) in _) =>
      replace x with y by reflexivity;
      case_goal_match; [cbn; f_equal; try apply Zmod.unsigned_inj; auto| ]
  | |- ((if ?x then _ else _), _) = (let '(_, _) := (if ?y then _ else _) in _) =>
      replace x with y by reflexivity;
      case_goal_match; [cbn; f_equal; try apply Zmod.unsigned_inj; auto| ]
  end.
  f_equal. apply Zmod.unsigned_inj; reflexivity.
Qed.
Lemma isStore_eq:
  forall x, IsaParams.IsStore x = (Zmod.unsigned x =? Zmod.unsigned Decode.Inst_Store)%Z.
Proof.
  unfold IsaParams.IsStore.
  intros. case_bool_decide; subst; auto. symmetry. rewrite Z.eqb_neq. 
  intros Heq. apply H, Zmod.unsigned_inj, Heq.
Qed.
Opaque IsaParams.IsStore.
Definition memAddrEq:
  forall i rs1val,
  IsaParams.memAddr (IsaParams.decode i) rs1val =
    let '(addr, (isExn, (exnCode, (exnMtval, _)))) :=
     fn.interp Decode.memAddr (((fn.interp Decode.getFields i, fn.interp Decode.getInstrProps i) ,rs1val)) in
    (addr, (isExn, exnCode, exnMtval)).
Proof.
  intros i rs1val.
  unfold IsaParams.memAddr; cbn.
  rewrite getInstrPropsEq, (* getFieldsEq,  *)getImm_eq.
  destruct (fn.interp Decode.getInstrProps i) as (rs1v & rs2v & rdv & ity & immT & []).
  destruct (fn.interp Decode.getFields i) as
    (rs1Idx & rs2Idx & rdIdx & csrIdx & immI & immS & immB & immU & csr & opcode & funct3 & funct7 & []).
  unfold lift_instrProps, lift_fields; cbn.
  repeat rewrite nonzero_and_embed_bool.
  rewrite<-isMemEq.
  repeat rewrite nonzero_or_embed_bool.
  repeat rewrite nonzero_bool.
  repeat rewrite decide_bool_decide.
  repeat (setoid_rewrite bool_decide_bv_and2 || setoid_rewrite bool_decide_bv_unsigned_eq).
  repeat rewrite embed_bool_negb.
  repeat match goal with
  | |- (if ?x then _ else _) = (let '(_, _) := (if ?y then _ else _) in _) =>
      replace x with y by reflexivity;
      case_goal_match; [cbn; f_equal; try apply Zmod.unsigned_inj; auto | ]
  end.
  all: repeat f_equal; try apply Zmod.unsigned_inj; try done.
  rewrite isStore_eq.
  repeat match goal with
  | |- context[Z.eqb ?x ?y] =>
      let H := fresh in
      destruct (Z.eqb x y) eqn:H; try setoid_rewrite H; auto
  end.
Qed.
Set Printing Coercions.

Lemma bool_decide_bv_unsigned_neq {n} (x y : bits n) :
  bool_decide (x <> y) = (negb (Zmod.unsigned x =? Zmod.unsigned y)%Z).
Proof.
  case_bool_decide; subst; auto.
  - symmetry. apply negb_true_iff.
    rewrite <-Zmod.unsigned_inj_iff in H. apply Z.eqb_neq. done.
  - symmetry. apply negb_false_iff.
    apply Z.eqb_refl.
Qed.
Hint Rewrite @bool_decide_bv_unsigned_neq : bv_simp.

Lemma execCtrl_eq:
  forall x0 pc rs1val rs2val,
  IsaParams.execControl (IsaParams.decode x0) pc rs1val rs2val =
  (let '(taken, (nextPC, (isCtrlExn, (ctrlExnCode, (ctrlExnMtval, _))))) :=
     fn.interp Decode.execControl ((fn.interp Decode.getFields x0), (fn.interp Decode.getInstrProps x0, ((pc , (rs1val , (rs2val, ())))))) in
     (taken, nextPC, (isCtrlExn, ctrlExnCode, ctrlExnMtval))).
Proof.
  intros x0 pc rs1val rs2val.
  unfold IsaParams.execControl. cbn.
  rewrite getInstrPropsEq.
  rewrite getFieldsEq.
  rewrite getImm_eq.
  (* Destruct props and fields tuples *)
  destruct (fn.interp Decode.getInstrProps x0) as (rs1v & rs2v & rdv & ity & immT & []).
  destruct (fn.interp Decode.getFields x0) as
    (rs1Idx & rs2Idx & rdIdx & csrIdx & immI & immS & immB & immU & csr & opcode & funct3 & funct7 & []).
  unfold lift_instrProps, lift_fields. cbn.
  cbv [Zmod.eqb].
  (* Normalize conditions *)
  repeat rewrite nonzero_and_embed_bool.
  repeat rewrite nonzero_bool.
  repeat rewrite decide_bool_decide.
  repeat (setoid_rewrite bool_decide_bv_and2 || setoid_rewrite bool_decide_bv_unsigned_eq || setoid_rewrite bool_decide_bv_unsigned_neq).
  (* bv_not (embed_bool b) = embed_bool (negb b) for alignment flags *)
  repeat rewrite embed_bool_negb.
  (* Both sides are now matching if-else trees; case-split and close *)

Ltac simp_ctrl := 
  repeat match goal with
  | |- (if ?x then _ else _) = (let '(_, _) := (if ?y then _ else _) in _) =>
      replace x with y by reflexivity;
      case_goal_match; [cbn; f_equal; try apply Zmod.unsigned_inj; auto| ]
  | |- ((if ?x then _ else _), _) = (let '(_, _) := (if ?y then _ else _) in _) =>
      replace x with y by reflexivity;
      case_goal_match; [cbn; f_equal; try apply Zmod.unsigned_inj; auto| ]
  | |- ((if ?x then _ else _)) = (if ?y then _ else _) =>
      replace x with y by reflexivity;
      case_goal_match; [ cbn; f_equal; try apply Zmod.unsigned_inj; auto | ] 
  end.
  simp_ctrl.
  { repeat f_equal. apply Zmod.unsigned_inj; done. }
  { replace (Zmod.unsigned Decode.funct3_BNE) with
              (Zmod.unsigned (Riscv.instrs.Decode.funct3_BNE)) by reflexivity.
    case_goal_match; [ cbn; repeat f_equal; try apply Zmod.unsigned_inj; auto | ]; 
      autorewrite with bv_simp.
    { rewrite nonzero_bool; auto. }
    { setoid_rewrite nonzero_bool. 
      repeat f_equal.
      apply Zmod.unsigned_inj. auto.
    }
  }
  { repeat f_equal; apply Zmod.unsigned_inj; done. }
Qed.
