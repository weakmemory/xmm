Require Import Lia Setoid Program.Basics.
Require Import AuxDef AuxRel.
Require Import ThreadTrace.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import imm_s.
From imm Require Import SubExecution.
From imm Require Import FinExecution.
From imm Require Import FinThreads.

From RecordUpdate Require Import RecordSet.
(* Import RecordSetNotations. *)
Open Scope program_scope.

Import ListNotations.

Set Implicit Arguments.

#[export] Instance eta_execution : Settable _ :=
  settable! Build_execution
    <acts_set; threads_set; lab; rmw; data; addr; ctrl; rmw_dep; rf; co>
.

Section RfComplete.

Variable G : execution.
Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'R'" := (is_r lab).
Notation "'rf'" := (rf G).

Definition rf_complete : Prop :=
    E ∩₁ R ⊆₁ codom_rel rf.

End RfComplete.

Section Race.
Variable G : execution.
Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'same_loc'" := (same_loc lab).
Notation "'mod'" := (mod lab).
Notation "'W'" := (is_w lab).
Notation "'hb'" := (hb G).
Notation "'ppo'" := (ppo G).
Notation "'bob'" := (bob G).
Notation "'rf'" := (rf G).
Notation "'sb'" := (sb G).
Notation "'eco'" := (eco G).

Definition one (s : actid -> Prop) : relation actid :=
    fun x y => s x \/ s y.

Definition race := restr_rel E (one W ∩ same_loc \ clos_sym hb).

Definition race_mod (o : mode) := race ∩ one (fun e => mode_le (mod e) o).
End Race.

Module WCore.

Record t := {
  G : execution;
  sc : relation actid;
}.

Definition init_exec G : execution :=
  Build_execution (acts_set G ∩₁ is_init) (threads_set G) (lab G) ∅₂ ∅₂ ∅₂ ∅₂ ∅₂ ∅₂ ∅₂.

#[global]
Hint Unfold init_exec : unfolderDb.

Section Consistency.

Variable G : execution.
Variable sc : relation actid.
Notation "'hb'" := (hb G).
Notation "'fr'" := (fr G).
Notation "'co'" := (co G).
Notation "'eco'" := (eco G).
Notation "'rmw'" := (rmw G).

Record is_cons : Prop := {
  cons_coherence : irreflexive (hb ⨾ eco^?);
  cons_atomicity : rmw ∩ (fr ⨾ co) ≡ ∅₂;
  cons_sc : acyclic sc;
}.

End Consistency.

Section RestrEq.

Variable X X' : t.
Variable s : actid -> Prop.

Notation "'G''" := (G X').
Notation "'E''" := (acts_set G').
Notation "'threads_set''" := (threads_set G').
Notation "'lab''" := (lab G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'rmw_dep''" := (rmw_dep G').

Notation "'G'" := (G X).
Notation "'E'" := (acts_set G).
Notation "'threads_set'" := (threads_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'R'" := (is_r lab).
Notation "'sc'" := (sc X).

Record exec_restr_eq : Prop := {
  ereq_acts : E ∩₁ s ≡₁ E' ∩₁ s;
  ereq_threads : threads_set ≡₁ threads_set';
  ereq_lab : eq_dom s lab lab';
  ereq_rf : restr_rel s rf ≡ restr_rel s rf';
  ereq_co : restr_rel s co ≡ restr_rel s co';
  ereq_rmw : restr_rel s rmw ≡ restr_rel s rmw';
  ereq_data : restr_rel s data ≡ restr_rel s data';
  ereq_ctrl : restr_rel s ctrl ≡ restr_rel s ctrl';
  ereq_rmw_dep : restr_rel s rmw_dep ≡ restr_rel s rmw_dep';
}.

Lemma ereq_sb
    (EREQ : exec_restr_eq) :
  restr_rel s sb ≡ restr_rel s sb'.
Proof using.
  unfold sb. rewrite <- !restr_relE, !restr_restr.
  now rewrite (ereq_acts EREQ).
Qed.

End RestrEq.

Section Wf.

Variable X X' : t.
Variable cmt : actid -> Prop.

Notation "'G''" := (G X').
Notation "'E''" := (acts_set G').
Notation "'threads_set''" := (threads_set G').
Notation "'lab''" := (lab G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'rmw_dep''" := (rmw_dep G').

Notation "'G'" := (G X).
Notation "'E'" := (acts_set G).
Notation "'threads_set'" := (threads_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'R'" := (is_r lab).
Notation "'sc'" := (sc X).

Record wf := {
  wf_g : Wf G;
  wf_ereq : exec_restr_eq X X' (E ∩₁ cmt);
  wf_rfc : rf_complete (restrict G' cmt);
  wf_sub_rfD : E ∩₁ R ⊆₁ codom_rel rf ∪₁ cmt;
  wf_sc : wf_sc G sc;
}.

End Wf.

Section AddEvent.

Variable sc sc' : relation actid.
Variable X X' : t.
Variable e : actid.
Variable l : label.
Variable cmt : actid -> Prop.

Notation "'G''" := (G X').
Notation "'G'" := (G X).

Notation "'E''" := (acts_set G').
Notation "'threads_set''" := (threads_set G').
Notation "'lab''" := (lab G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'rmw_dep''" := (rmw_dep G').
Notation "'W''" := (is_w lab').
Notation "'R''" := (is_r lab').
Notation "'same_loc''" := (same_loc lab').
Notation "'same_val''" := (same_val lab').

Notation "'E'" := (acts_set G).
Notation "'threads_set'" := (threads_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'same_loc'" := (same_loc lab).

Definition sb_delta : relation actid :=
  (E ∩₁ (is_init ∪₁ same_tid e)) × eq e.

Definition rf_delta_R w : relation actid :=
  eq_opt w × (eq e ∩₁ R').

Definition rf_delta_W R1 : relation actid :=
  (eq e ∩₁ W') × R1.

Definition co_delta W1 W2 : relation actid :=
  (eq e ∩₁ W') × W1 ∪ W2 × (eq e ∩₁ W').

Definition rmw_delta r : relation actid :=
  eq_opt r × (eq e ∩₁ W').

Definition right_after_e r :=
  match r with
  | Some r => immediate sb' r e
  | None => True
  end.

Record add_event_gen r R1 w W1 W2 : Prop := {
  add_event_new : ~E e;
  add_event_ninit : ~is_init e;
  add_event_tid_e : tid e <> tid_init;
  (**)
  add_event_wD : eq_opt w ⊆₁ W';
  add_event_wE : eq_opt w ⊆₁ E;
  add_event_wL : eq_opt w ⊆₁ same_loc' e;
  add_event_wv : eq_opt w ⊆₁ same_val' e;
  (**)
  add_event_rD : eq_opt r ⊆₁ R';
  add_event_rE : eq_opt r ⊆₁ E;
  add_event_rL : eq_opt r ⊆₁ same_loc' e;
  add_event_ri : right_after_e r;
  (**)
  add_event_W1D : W1 ⊆₁ W';
  add_event_W1E : W1 ⊆₁ E;
  add_event_W1L : W1 ⊆₁ same_loc' e;
  (**)
  add_event_W2D : W2 ⊆₁ W';
  add_event_W2E : W2 ⊆₁ E;
  add_event_W2L : W2 ⊆₁ same_loc' e;
  (**)
  add_event_R1D : R1 ⊆₁ R';
  add_event_R1E : R1 ⊆₁ E;
  add_event_R1L : R1 ⊆₁ same_loc' e;
  add_event_R1V : R1 ⊆₁ same_val' e;
  (**)
  add_event_co_tr : transitive co';
  add_event_rff : functional (rf'⁻¹);
  (*=================*)
  add_event_acts : E' ≡₁ E ∪₁ eq e;
  add_event_threads : threads_set' ≡₁ threads_set;
  add_event_lab : lab' = upd lab e l;
  add_event_rf : rf' ≡ rf ∪ rf_delta_R w ∪ rf_delta_W R1;
  add_event_co : co' ≡ co ∪ co_delta W1 W2;
  add_event_rmw : rmw' ≡ rmw ∪ rmw_delta r;
  add_event_data : data' ≡ data;
  add_event_addr : addr' ≡ addr;
  add_event_ctrl : ctrl' ≡ ctrl;
  add_event_rmw_dep : rmw_dep' ≡ rmw_dep;
  add_event_sb : sb' ≡ sb ∪ sb_delta;
}.

Definition add_event :=
  exists r R1 w W1 W2, add_event_gen r R1 w W1 W2.

Lemma middle_seq A (r1 r2 r3 r4 r5 : relation A) :
  r1 ⨾ r2 ⨾ r3 ⨾ r4 ⨾ r5 ≡ r1 ⨾ (r2 ⨾ r3 ⨾ r4) ⨾ r5.
Proof using.
  basic_solver.
Qed.

Lemma add_event_wf r R1 w W1 W2
  (ADD : add_event_gen r R1 w W1 W2)
  (WF : Wf (WCore.G X))
  (NCTRL : ctrl ≡ ∅₂) :
  Wf (WCore.G X').
Proof using.
  assert (NIN : ~ E e).
  { apply (add_event_new ADD). }
  assert (EISR : E ∩₁ R' ≡₁ E ∩₁ R).
  { unfold is_r. rewrite (add_event_lab ADD).
    unfolder; split; intros x (INE & LAB).
    all: now rewrite updo in * by congruence. }
  assert (EISW : E ∩₁ W' ≡₁ E ∩₁ W).
  { unfold is_w. rewrite (add_event_lab ADD).
    unfolder; split; intros x (INE & LAB).
    all: now rewrite updo in * by congruence. }
  assert (EISREX : E ∩₁ R_ex lab ≡₁ E ∩₁ R_ex lab').
  { unfold R_ex. rewrite (add_event_lab ADD).
    unfolder; split; intros x (INE & LAB).
    all: now rewrite updo in * by congruence. }
  assert (EINTER : E ∩₁ E' ≡₁ E).
  { rewrite (add_event_acts ADD). basic_solver. }
  assert (EINE : E ⊆₁ E').
  { rewrite (add_event_acts ADD). basic_solver. }
  assert (SLE : ⦗E⦘ ⨾ same_loc ⨾ ⦗E⦘ ⊆ same_loc').
  { rewrite (add_event_lab ADD).
    unfolder; intros x y (EX & SL & EY).
    unfold same_loc in *. unfold loc in *.
    do 2 rewrite updo in * by congruence.
    eauto. }
  constructor.
  { assert (ENINIT : ~is_init e) by apply ADD.
    intros a b (INA & INB & NEQ & TIDS & NINIT).
    apply ADD in INA, INB.
    destruct INA as [INA | AEQE],
             INB as [INB | BEQE].
    all: subst; ins.
    { now apply WF. }
    { unfold is_init in *. desf. ins. congruence. }
    destruct b as [bl | bt bn]; ins.
    { exfalso. now apply (add_event_tid_e ADD). }
    unfold is_init in *. desf. ins. congruence. }
  all: ins.
  { rewrite (add_event_data ADD). rewrite (add_event_sb ADD).
    rewrite (data_in_sb WF). basic_solver. }
  { rewrite (add_event_data ADD), (wf_dataE WF).
    rewrite (wf_dataD WF) at 1. rewrite !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    now rewrite EISR, EISW. }
  { rewrite (add_event_addr ADD). rewrite (add_event_sb ADD).
    rewrite (addr_in_sb WF). basic_solver. }
  { rewrite (add_event_addr ADD), (wf_addrE WF).
    rewrite (wf_addrD WF) at 1. rewrite !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    do 2 rewrite set_inter_union_r.
    now rewrite EISR, EISW. }
  { rewrite (add_event_ctrl ADD). rewrite (add_event_sb ADD).
    rewrite (ctrl_in_sb WF). basic_solver. }
  { rewrite (add_event_ctrl ADD), (wf_ctrlE WF).
    rewrite (wf_ctrlD WF) at 1. rewrite !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    now rewrite EISR. }
  { rewrite (add_event_ctrl ADD). rewrite (add_event_sb ADD).
    rewrite seq_union_r. apply inclusion_union_l; eauto.
    { rewrite (ctrl_sb WF). basic_solver. }
    rewrite NCTRL. basic_solver. }
  { split; [| basic_solver].
    rewrite (add_event_rmw ADD), (wf_rmwE WF).
    rewrite (wf_rmwD WF) at 1. rewrite !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    rewrite seq_union_l. rewrite seq_union_r.
    apply inclusion_union_l.
    { rewrite <- middle_seq.
      seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
      rewrite EISR, EISW. left. apply H. }
    unfold rmw_delta. rewrite !seqA. seq_rewrite !seq_eqv.
    rewrite !set_interC with (s' := E).
    rewrite <- (add_event_rD ADD).
    basic_solver 42. }
  { rewrite (add_event_rmw ADD). rewrite (wf_rmwE WF), (wf_rmwl WF).
    apply inclusion_union_l; eauto.
    unfold rmw_delta. rewrite (add_event_rL ADD).
    basic_solver. }
  { rewrite (add_event_rmw ADD). 
    apply inclusion_union_l. 
    { rewrite (add_event_sb ADD). intros x y RMW. 
      unfold immediate; splits; ins.
      { destruct WF. unfold immediate in wf_rmwi. 
        destruct wf_rmwi with (x := x) (y := y); eauto.
        basic_solver. }
      destruct R0, R2.
      { destruct WF. destruct wf_rmwi with (x := x) (y := y); eauto. }
      { assert (YIN : E y). 
        { assert (HH : (⦗E⦘ ⨾ rmw ⨾ ⦗E⦘) x y).
          { apply wf_rmwE; basic_solver. }
          destruct HH. destruct H1. destruct H2. 
          destruct H2. destruct H3. basic_solver. }
        unfold sb_delta in H0. assert (EQ : e = y).
        { destruct H0; eauto. }
        subst. basic_solver. }
      { assert (EQ : c = e).
        { destruct H; eauto. }
        subst. apply wf_sbE in H0; eauto.
        destruct H0. destruct H0. 
        destruct H0. basic_solver. }
      assert (YIN : E y). 
        { assert (HH : (⦗E⦘ ⨾ rmw ⨾ ⦗E⦘) x y).
          { apply wf_rmwE; basic_solver. }
        destruct HH. destruct H1. destruct H2. 
        destruct H2. destruct H3. basic_solver. }
      unfold sb_delta in H0. assert (EQ : e = y).
      { destruct H0; eauto. }
      subst. basic_solver. }
    unfold rmw_delta. destruct ADD. unfold right_after_e in add_event_ri0.
    destruct r.
    { intros x y H. assert (EQ1 : x = a).
      { destruct H; eauto. }
      assert (EQ2 : y = e).
      { destruct H. destruct H0; eauto. }
      subst; eauto. }
    basic_solver. }
  { split; [| basic_solver].
    rewrite (add_event_rf ADD), (wf_rfE WF).
    rewrite !seq_union_l. rewrite !seq_union_r. rewrite !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    rewrite EINTER. apply inclusion_union_l.
    { apply inclusion_union_l.
      {  basic_solver 8. }
      assert (RFDIN1 : eq_opt w × (eq e ∩₁ (fun a : actid => R' a)) ⊆
                ⦗E'⦘ ⨾ eq_opt w × (eq e ∩₁ (fun a : actid => R' a))).
      { rewrite <- EINE. rewrite <- (add_event_wE ADD). basic_solver 21. }
      assert (RFDIN2 : eq_opt w × (eq e ∩₁ (fun a : actid => R' a)) ⊆
                eq_opt w × (eq e ∩₁ (fun a : actid => R' a)) ⨾ ⦗E'⦘).
      { rewrite (add_event_acts ADD). basic_solver 42. }
      unfold rf_delta_R. rewrite RFDIN1 at 1. rewrite RFDIN2 at 1.
      basic_solver 8. }
      assert (RFDIN1 : (eq e ∩₁ (fun a : actid => W' a)) × R1 ⊆
                ⦗E'⦘ ⨾ (eq e ∩₁ (fun a : actid => W' a)) × R1).
      { rewrite (add_event_acts ADD). basic_solver 42. }
      assert (RFDIN2 : (eq e ∩₁ (fun a : actid => W' a)) × R1 ⊆
                (eq e ∩₁ (fun a : actid => W' a)) × R1 ⨾ ⦗E'⦘).
      { rewrite <- EINE. rewrite <- (add_event_R1E ADD). basic_solver 21. }
      unfold rf_delta_W. rewrite RFDIN1 at 1. rewrite RFDIN2 at 1.
      basic_solver 8. }
  { split; [| basic_solver].
    rewrite (add_event_rf ADD), (wf_rfE WF).
    rewrite (wf_rfD WF) at 1. rewrite !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    rewrite seq_union_l. rewrite seq_union_r.
    apply inclusion_union_l.
    { apply inclusion_union_l.
      { rewrite seq_union_l. rewrite seq_union_r. rewrite <- middle_seq.
        seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
        rewrite EISR, EISW. do 2 left. apply H. }
      unfold rf_delta_R. rewrite seq_union_l.
      rewrite !seqA. seq_rewrite !seq_eqv.
      rewrite !seq_union_r. assert (EOW : eq_opt w × (eq e ∩₁ (fun a : actid => R' a)) ≡
                  ⦗fun a : actid => W' a⦘ ⨾ eq_opt w × (eq e ∩₁ (fun a : actid => R' a))).
      { split; [| basic_solver]. rewrite <- (add_event_wD ADD). basic_solver 21. }
      rewrite EOW. rewrite (wf_rfD WF) at 1. rewrite !seqA.
      basic_solver 21. }
    unfold rf_delta_W. rewrite <- (add_event_R1D ADD). basic_solver 21. }
  { rewrite (add_event_rf ADD). apply inclusion_union_l.
    { apply inclusion_union_l.
      { rewrite (wf_rfE WF). rewrite (wf_rfl WF).
        apply SLE. }
      unfold rf_delta_R. rewrite (add_event_wL ADD).
      basic_solver. }
    unfold rf_delta_W. rewrite (add_event_R1L ADD).
    basic_solver. }
  { rewrite (add_event_rf ADD).
    repeat apply funeq_union.
    { rewrite (add_event_lab ADD).
      unfolder. intros a b RF. unfold val.
      rupd; try now apply WF.
      all: apply (wf_rfE WF) in RF.
      all: unfolder in RF; desf.
      all: congruence. }
    { unfold rf_delta_R. unfolder.
      intros a b (EQA & EQB & BISR).
      subst b. symmetry.
      apply (add_event_wv ADD).
      desf. }
    unfold rf_delta_W. unfolder.
    intros a b ((EQA & BISW) & EQB).
    subst a. now apply (add_event_R1V ADD). }
  { apply (add_event_rff ADD). }
  { rewrite (add_event_co ADD). rewrite (add_event_acts ADD).
    split; [| basic_solver]. apply inclusion_union_l.
    { rewrite (wf_coE WF). basic_solver. }
    unfold co_delta. rewrite !seq_union_l. rewrite !seq_union_r.
    apply inclusion_union_l.
    { assert (W1IN : (eq e ∩₁ (fun a : actid => W' a)) × W1 ⊆
            (eq e ∩₁ (fun a : actid => W' a)) × W1 ⨾ ⦗E ∪₁ eq e⦘).
      { rewrite <- (add_event_W1E ADD). basic_solver. }
      assert (W2IN : (eq e ∩₁ (fun a : actid => W' a)) × W1 ⊆
            ⦗E ∪₁ eq e⦘ ⨾ (eq e ∩₁ (fun a : actid => W' a)) × W1).
      { rewrite <- (add_event_W1E ADD). basic_solver. }
      rewrite W1IN at 1. rewrite W2IN at 1. basic_solver 21. }
    assert (W1IN : W2 × (eq e ∩₁ (fun a : actid => W' a)) ⊆
                   W2 × (eq e ∩₁ (fun a : actid => W' a)) ⨾ ⦗E ∪₁ eq e⦘).
    { rewrite <- (add_event_W2E ADD). basic_solver. }
    assert (W2IN : W2 × (eq e ∩₁ (fun a : actid => W' a)) ⊆
                ⦗E ∪₁ eq e⦘ ⨾ W2 × (eq e ∩₁ (fun a : actid => W' a))).
    { rewrite <- (add_event_W2E ADD). basic_solver. }
    rewrite W1IN at 1. rewrite W2IN at 1. basic_solver 21. }
  { rewrite (add_event_co ADD). split; [| basic_solver].
    apply inclusion_union_l.
    { rewrite (wf_coE WF).
      rewrite (wf_coD WF) at 1. rewrite !seqA.
      seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
      rewrite seq_union_l. rewrite seq_union_r. rewrite <- middle_seq.
      seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
      rewrite EISW. left. apply H. }
    unfold co_delta. rewrite !seq_union_l. rewrite !seq_union_r.
    apply inclusion_union_l.
    { assert (W1IN : (eq e ∩₁ (fun a : actid => W' a)) × W1 ⊆
            (eq e ∩₁ (fun a : actid => W' a)) × W1 ⨾ ⦗fun a : actid => W' a⦘).
      { rewrite <- (add_event_W1D ADD) at 3. basic_solver 21. }
      assert (W2IN : (eq e ∩₁ (fun a : actid => W' a)) × W1 ⊆
            ⦗fun a : actid => W' a⦘ ⨾ (eq e ∩₁ (fun a : actid => W' a)) × W1).
      { basic_solver 21. }
      rewrite W1IN at 1. rewrite W2IN at 1. basic_solver 21. }
    assert (W1IN : W2 × (eq e ∩₁ (fun a : actid => W' a)) ⊆
            ⦗fun a : actid => W' a⦘ ⨾ W2 × (eq e ∩₁ (fun a : actid => W' a))).
    { rewrite <- (add_event_W2D ADD) at 2. basic_solver 21. }
    assert (W2IN : W2 × (eq e ∩₁ (fun a : actid => W' a)) ⊆
            W2 × (eq e ∩₁ (fun a : actid => W' a)) ⨾ ⦗fun a : actid => W' a⦘).
    { basic_solver 21. }
    rewrite W1IN at 1. rewrite W2IN at 1. basic_solver 21. }
  { rewrite (add_event_co ADD). apply inclusion_union_l.
    { rewrite (wf_coE WF), (wf_col WF). apply SLE. }
    unfold co_delta. rewrite (add_event_W1L ADD), (add_event_W2L ADD).
    basic_solver 21. }
  { apply (add_event_co_tr ADD); eauto. }
  { unfold is_total. ins. destruct IWa as [[INA AISW] Aloc]. 
    destruct IWb as [[INB BISW] Bloc].
    apply ADD in INA, INB.
    destruct INA as [INA | AEQE],
            INB as [INB | BEQE].
    { assert (COBASE : co a b \/ co b a).
      { assert (ANEQ : a <> e).
        { intros EQ. subst. apply NIN; eauto. }
        assert (ALAB : lab a = lab' a).
        { rewrite (add_event_lab ADD). unfold upd; basic_solver. }
        assert (BNEQ : b <> e).
        { intros EQ. subst. apply NIN; eauto. }
        assert (BLAB : lab b = lab' b).
        { rewrite (add_event_lab ADD). unfold upd; basic_solver. }
        eapply (wf_co_total WF); eauto.
        all: split; eauto. 
        { split; eauto. unfold is_w. unfold is_w in AISW.
          rewrite ALAB. congruence. }
        { split; eauto. unfold is_w. unfold is_w in BISW.
          rewrite BLAB. congruence. }
        subst. unfold loc in *. rewrite ALAB, BLAB; eauto. }
      destruct COBASE. 
      { left. apply (add_event_co ADD). basic_solver. }
      right. apply (add_event_co ADD). basic_solver. }
    { subst. left. apply (add_event_co ADD). 
      unfold co_delta. do 2 right. admit. }
    { subst. left. apply (add_event_co ADD). 
      unfold co_delta. right. left. admit. }
    subst; ins. }
  { rewrite (add_event_co ADD). apply irreflexive_union; split.
    { apply (co_irr WF). }
    unfold co_delta. apply irreflexive_union; split.
    { rewrite (add_event_W1E ADD). basic_solver. }
    rewrite (add_event_W2E ADD). basic_solver. }
  { admit. }
  { rewrite (add_event_lab ADD). destruct classic with ((InitEvent l0) = e).
    { destruct ADD. destruct H. ins. }
    unfold upd. destruct WF. destruct wf_init_lab with (l := l0).
    basic_solver. }
  { rewrite (add_event_rmw_dep ADD). rewrite (add_event_sb ADD).
    rewrite (rmw_dep_in_sb WF). basic_solver. }
  { rewrite (add_event_rmw_dep ADD). rewrite (wf_rmw_depD WF).
    rewrite (wf_rmw_depE WF).
    rewrite (wf_rmw_depD WF) at 1. rewrite !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    rewrite <- !set_interA. rewrite EISR.
    rewrite !set_interC with (s' := (fun a : actid => R_ex lab a)).
    rewrite !set_interA. rewrite <- EISREX.
    basic_solver 8. }
  destruct classic with (e0 = e).
  { subst. destruct ADD. destruct e as [el | et en]; ins.
    admit. }
  assert (E e0) as EE0.
  { apply (add_event_acts ADD) in EE. destruct EE; basic_solver 8. }
  apply wf_threads; eauto.
Admitted.

End AddEvent.

#[global]
Hint Unfold sb_delta rf_delta_R rf_delta_W co_delta rmw_delta : unfolderDb.

Section GuidedStep.

Variable cmt : actid -> Prop.
Variable XC X1 X2 : t.

Record guided_step_gen e l : Prop := {
  gsg_add_step : add_event X1 X2 e l;
  gsg_wf : wf X2 XC cmt;
}.

Definition guided_step :=
  exists e l, guided_step_gen e l.

End GuidedStep.

Section ExecuteStep.

Variables X X' : t.

Notation "'sc''" := (sc X').
Notation "'G''" := (G X').

Record exec_inst e l := {
  exec_add_event : add_event X X' e l;
  exec_rfc : rf_complete G';
  exec_new_cons : is_cons G' sc';
}.

End ExecuteStep.

Section ReexecStep.

Variables X X' : t.
Variable cmt : actid -> Prop.

Notation "'G''" := (G X').
Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'rf''" := (rf G').
Notation "'sb''" := (sb G').
Notation "'rpo''" := (rpo G').
Notation "'rmw''" := (rmw G').
Notation "'co''" := (co G').

Notation "'G'" := (G X).
Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'rf'" := (rf G).
Notation "'sb'" := (sb G).
Notation "'rpo'" := (rpo G).
Notation "'rmw'" := (rmw G).
Notation "'co'" := (co G).
Notation "'sc'" := (sc X).

Definition X_start dtrmt :=
  Build_t (restrict G dtrmt) (restr_rel dtrmt sc).

Record stable_uncmt_reads_gen thrdle : Prop :=
  { surg_init_least : least_elt thrdle tid_init;
    surg_init_wmin : wmin_elt thrdle tid_init;
    surg_order : strict_partial_order thrdle;
    surg_uncmt : rf' ⨾ ⦗E' \₁ cmt⦘ ⊆ sb' ∪ tid ↓ thrdle; }.

Record commit_embedded f : Prop :=
{ reexec_embd_inj : inj_dom cmt f;
  reexec_embd_tid : forall e (CMT : cmt e), tid (f e) = tid e;
  reexec_embd_lab : forall e (CMT : cmt e), lab' (f e) = lab e;
  reexec_embd_rpo : f ↑ restr_rel cmt rpo' ⊆ rpo;
  reexec_embd_rf : f ↑ restr_rel cmt rf' ⊆ rf;
  reexec_embd_co : f ↑ restr_rel cmt co' ⊆ co;
  reexec_embd_rmw : f ↑ restr_rel cmt rmw' ⊆ rmw; }.

Record reexec_gen f thrdle dtrmt : Prop :=
{ (* Correct start *)
  dtrmt_cmt : dtrmt ⊆₁ f ↑₁ cmt;
  reexec_embd_dom : cmt ⊆₁ E';
  reexec_sur : stable_uncmt_reads_gen thrdle;
  (* Correct embedding *)
  reexec_embd_corr : commit_embedded f;
  (* Reproducable steps *)
  reexec_start_wf : wf (X_start dtrmt) X' cmt;
  rexec_final_cons : is_cons G' sc;
  reexec_steps : (guided_step cmt X')＊ (X_start dtrmt) X'; }.

Definition reexec : Prop :=
  exists f thrdle dtrmt, reexec_gen f thrdle dtrmt.

End ReexecStep.

End WCore.