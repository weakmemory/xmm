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
Notation "'loc''" := (loc lab').
Notation "'val''" := (val lab').
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
Notation "'Loc_'' l" := (fun e => loc' e = l) (at level 1).
Notation "'Val_'' l" := (fun e => val' e = l) (at level 1).

Notation "'E'" := (acts_set G).
Notation "'threads_set'" := (threads_set G).
Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
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
Notation "'same_val'" := (same_val lab).
Notation "'Loc_' l" := (fun e => loc e = l) (at level 1).
Notation "'Val_' v" := (fun e => val e = v) (at level 1).

Definition lab_val :=
  match l with
  | Aload _ _ _ v | Astore _ _ _ v => Some v
  | Afence _ => None
  end.

Definition lab_loc :=
  match l with
  | Aload _ _ l _ | Astore _ _ l _ => Some l
  | Afence _ => None
  end.

Definition lab_is_r : actid -> Prop :=
  match l with
  | Aload _ _ _ _ => ⊤₁
  | _ => ∅
  end.

Definition lab_is_w : actid -> Prop :=
  match l with
  | Astore _ _ _ _ => ⊤₁
  | _ => ∅
  end.

Definition sb_delta : relation actid :=
  (E ∩₁ (is_init ∪₁ same_tid e)) × eq e.

Definition rf_delta_R w : relation actid :=
  eq_opt w × (eq e ∩₁ lab_is_r).

Definition rf_delta_W R1 : relation actid :=
  (eq e ∩₁ lab_is_w) × R1.

Definition co_delta W1 W2 : relation actid :=
  (eq e ∩₁ lab_is_w) × W1 ∪ W2 × (eq e ∩₁ lab_is_w).

Definition rmw_delta r : relation actid :=
  eq_opt r × (eq e ∩₁ lab_is_w).

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
  add_event_wD : eq_opt w ⊆₁ W;
  add_event_wE : eq_opt w ⊆₁ E;
  add_event_wL : eq_opt w ⊆₁ Loc_ lab_loc;
  add_event_wv : eq_opt w ⊆₁ Val_ lab_val;
  (**)
  add_event_rD : eq_opt r ⊆₁ R;
  add_event_rE : eq_opt r ⊆₁ E;
  add_event_rL : eq_opt r ⊆₁ Loc_ lab_loc;
  add_event_ri : right_after_e r;
  (**)
  add_event_W1D : W1 ⊆₁ W;
  add_event_W1E : W1 ⊆₁ E;
  add_event_W1L : W1 ⊆₁ Loc_ lab_loc;
  (**)
  add_event_W2D : W2 ⊆₁ W;
  add_event_W2E : W2 ⊆₁ E;
  add_event_W2L : W2 ⊆₁ Loc_ lab_loc;
  (**)
  add_event_R1D : R1 ⊆₁ R;
  add_event_R1E : R1 ⊆₁ E;
  add_event_R1L : R1 ⊆₁ Loc_ lab_loc;
  add_event_R1V : R1 ⊆₁ Val_ lab_val;
  (**)
  add_event_co_tr : transitive co';
  add_event_rff : functional (rf'⁻¹);
  (**)
  add_event_total : forall ol,
                    is_total
                      (E' ∩₁ W' ∩₁ Loc_' ol)
                      co';
  add_event_init : forall l (SOME : lab_loc = Some l),
                    E (InitEvent l);
  add_event_thrd : threads_set (tid e);
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

Lemma same_loc_eq s
    (IN : s ⊆₁ Loc_' (loc' e)) :
  s × eq e ⊆ same_loc'.
Proof using.
  unfolder in *. unfold same_loc.
  ins. desf. eauto.
Qed.

Lemma same_loc_sym A B
    (SUB : A × B ⊆ same_loc') :
  B × A ⊆ same_loc'.
Proof using.
  unfold same_loc in *. unfolder in *.
  ins. desf. symmetry. eauto.
Qed.

Lemma funeq_sym {A B : Type} (f : A -> B) s1 s2
    (FUN : funeq f (s1 × s2)) :
  funeq f (s2 × s1).
Proof using.
  unfolder in *. ins. desf. symmetry. eauto.
Qed.

Lemma funeq_eq {A B : Type} (f : A -> B) s x
    (SUB : s ⊆₁ (fun y => f y = f x)) :
  funeq f (s × eq x).
Proof using.
  basic_solver.
Qed.

Lemma funeq_val r
    (SUB : r ⊆ same_val') :
  funeq val' r.
Proof using.
  unfold same_val, val in *. unfolder in *. ins.
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
  assert (EISL : E ∩₁ Loc_' lab_loc ≡₁ E ∩₁ Loc_ lab_loc).
  { unfold loc. rewrite (add_event_lab ADD).
    unfolder; split; intros x (INE & LAB).
    all: now rewrite updo in * by congruence. }
  assert (EISV : E ∩₁ Val_' lab_val ≡₁ E ∩₁ Val_ lab_val).
  { unfold val. rewrite (add_event_lab ADD).
    unfolder; split; intros x (INE & LAB).
    all: now rewrite updo in * by congruence. }
  assert (EQLOC : loc' e = lab_loc).
  { rewrite (add_event_lab ADD). unfold loc, lab_loc.
    now rupd. }
  assert (EQVAL : val' e = lab_val).
  { rewrite (add_event_lab ADD). unfold val, lab_val.
    now rupd. }
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
  assert (VLE : ⦗E⦘ ⨾ same_val ⨾ ⦗E⦘ ⊆ same_val').
  { rewrite (add_event_lab ADD).
    unfolder; intros x y (EX & SL & EY).
    unfold same_val in *. unfold val in *.
    do 2 rewrite updo in * by congruence.
    eauto. }
  constructor.
  { assert (ENINIT : ~is_init e) by apply ADD.
    intros a b (INA & INB & NEQ & TIDS & NINIT).
    apply (add_event_acts ADD) in INA, INB.
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
    rewrite !seq_union_l, !seq_union_r, !seqA.
    apply union_mori.
    { rewrite (wf_rmwD WF) at 1. rewrite !seqA.
      seq_rewrite <- !id_inter.
      now rewrite EISW, !set_interC with (s' := E), EISR. }
    unfold rmw_delta.
    seq_rewrite <- cross_inter_l.
    seq_rewrite <- cross_inter_r.
    rewrite set_inter_absorb_l with (s' := R'),
            set_inter_absorb_r with (s' := W').
    all: ins.
    { rewrite (add_event_lab ADD).
      unfold lab_is_w, is_w. unfolder.
      intros x (XIN & LAB). subst x. rupd. desf. }
    transitivity (E ∩₁ R); [| rewrite <- EISR; basic_solver].
    apply set_subset_inter_r. split; apply ADD. }
  { rewrite (add_event_rmw ADD), (wf_rmwE WF), (wf_rmwl WF).
    apply inclusion_union_l; eauto. unfold rmw_delta.
    transitivity (eq_opt r × eq e); [basic_solver |].
    arewrite (eq_opt r ⊆₁ E ∩₁ Loc_ lab_loc).
    { apply set_subset_inter_r. split; apply ADD. }
    apply same_loc_eq. rewrite EQLOC, <- EISL.
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
    rewrite !seq_union_l, !seq_union_r, !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    rewrite EINTER. repeat apply union_mori; ins.
    all: rewrite (add_event_acts ADD).
    { unfold rf_delta_R.
      seq_rewrite <- cross_inter_l.
      seq_rewrite <- cross_inter_r.
      rewrite set_inter_absorb_l with (s := eq_opt w),
              set_inter_absorb_r with (s := eq e ∩₁ lab_is_r).
      all: rewrite ?(add_event_wE ADD).
      all: basic_solver. }
    unfold rf_delta_W.
    seq_rewrite <- cross_inter_l.
    seq_rewrite <- cross_inter_r.
    rewrite set_inter_absorb_r with (s := R1),
            set_inter_absorb_l with (s := eq e ∩₁ lab_is_w).
    all: rewrite ?(add_event_R1E ADD).
    all: basic_solver. }
  { split; [| basic_solver].
    rewrite (add_event_rf ADD), (wf_rfE WF).
    rewrite (wf_rfD WF) at 1.
    rewrite !seq_union_l, !seq_union_r, !seqA.
    repeat apply union_mori.
    { seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
      now rewrite EISR, EISW. }
    { unfold rf_delta_R.
      seq_rewrite <- cross_inter_l.
      seq_rewrite <- cross_inter_r.
      rewrite set_inter_absorb_l with (s := eq_opt w),
              set_inter_absorb_r with (s := eq e ∩₁ lab_is_r).
      all: ins.
      { rewrite (add_event_lab ADD).
        unfolder. unfold lab_is_r, is_r.
        intros x (HEQ & LAB). subst x. rupd. desf. }
      transitivity (E ∩₁ W); [| rewrite <- EISW; basic_solver].
      apply set_subset_inter_r. split; apply ADD. }
    unfold rf_delta_W.
    seq_rewrite <- cross_inter_l.
    seq_rewrite <- cross_inter_r.
    rewrite set_inter_absorb_r with (s := R1),
            set_inter_absorb_l with (s := eq e ∩₁ lab_is_w).
    all: ins.
    { rewrite (add_event_lab ADD).
      unfolder. unfold lab_is_w, is_w.
      intros x (HEQ & LAB). subst x. rupd. desf. }
    transitivity (E ∩₁ R); [| rewrite <- EISR; basic_solver].
    apply set_subset_inter_r. split; apply ADD. }
  { rewrite (add_event_rf ADD), (wf_rfE WF), (wf_rfl WF).
    repeat apply inclusion_union_l; eauto.
    all: unfold rf_delta_R, rf_delta_W.
    { transitivity (eq_opt w × eq e); [basic_solver |].
      arewrite (eq_opt w ⊆₁ E ∩₁ Loc_ lab_loc).
      { apply set_subset_inter_r. split; apply ADD. }
      apply same_loc_eq. rewrite EQLOC, <- EISL.
      basic_solver. }
    transitivity (eq e × R1); [basic_solver |].
    arewrite (R1 ⊆₁ E ∩₁ Loc_ lab_loc).
    { apply set_subset_inter_r. split; apply ADD. }
    apply same_loc_sym, same_loc_eq. rewrite EQLOC, <- EISL.
    basic_solver. }
  { rewrite (add_event_rf ADD).
    repeat apply funeq_union.
    { enough (rf ⊆ same_val') by ins.
      transitivity (⦗E⦘ ⨾ same_val ⨾ ⦗E⦘); ins.
      rewrite (wf_rfE WF). repeat apply seq_mori; ins.
      apply WF. }
    { apply funeq_mori with (x := eq_opt w × eq e).
      { unfold flip, rf_delta_R. basic_solver. }
      apply funeq_eq. rewrite EQVAL.
      transitivity (E ∩₁ Val_' lab_val); [| basic_solver].
      rewrite EISV. apply set_subset_inter_r.
      split; apply ADD. }
    apply funeq_mori with (x := eq e × R1).
    { unfold flip, rf_delta_W. basic_solver. }
    apply funeq_sym, funeq_eq. rewrite EQVAL.
    transitivity (E ∩₁ Val_' lab_val); [| basic_solver].
    rewrite EISV. apply set_subset_inter_r.
    split; apply ADD. }
  { apply (add_event_rff ADD). }
  { split; [| basic_solver].
    rewrite (add_event_co ADD), (wf_coE WF).
    rewrite !seq_union_l, !seq_union_r, !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    rewrite EINTER. repeat apply union_mori; ins.
    all: rewrite (add_event_acts ADD).
    unfold co_delta.
    rewrite !seq_union_l, !seq_union_r.
    seq_rewrite <- !cross_inter_l.
    seq_rewrite <- !cross_inter_r.
    rewrite set_inter_absorb_r with (s := W1),
            set_inter_absorb_l with (s := eq e ∩₁ lab_is_w),
            set_inter_absorb_l with (s := W2),
            set_inter_absorb_r with (s := eq e ∩₁ lab_is_w).
    all: rewrite ?(add_event_W1E ADD), ?(add_event_W2E ADD).
    all: basic_solver. }
  { split; [| basic_solver].
    rewrite (add_event_co ADD), (wf_coE WF).
    rewrite (wf_coD WF) at 1.
    rewrite !seq_union_l, !seq_union_r, !seqA.
    repeat apply union_mori.
    { seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
      now rewrite EISW. }
    unfold co_delta. rewrite !seq_union_l, !seq_union_r.
    seq_rewrite <- !cross_inter_l.
    seq_rewrite <- !cross_inter_r.
    rewrite set_inter_absorb_r with (s := W1),
            set_inter_absorb_l with (s := eq e ∩₁ lab_is_w),
            set_inter_absorb_l with (s := W2),
            set_inter_absorb_r with (s := eq e ∩₁ lab_is_w).
    all: ins.
    { rewrite (add_event_lab ADD).
      unfold lab_is_w, is_w. unfolder.
      intros x (XIN & LAB). subst x. rupd. desf. }
    { transitivity (E ∩₁ W); [| rewrite <- EISW; basic_solver].
      apply set_subset_inter_r. split; apply ADD. }
    { rewrite (add_event_lab ADD).
      unfold lab_is_w, is_w. unfolder.
      intros x (XIN & LAB). subst x. rupd. desf. }
    transitivity (E ∩₁ W); [| rewrite <- EISW; basic_solver].
    apply set_subset_inter_r. split; apply ADD. }
  { rewrite (add_event_co ADD). unfold co_delta.
    repeat apply inclusion_union_l.
    { transitivity (⦗E⦘ ⨾ same_loc ⨾ ⦗E⦘); ins.
      rewrite (wf_coE WF). repeat apply seq_mori; ins.
      apply WF. }
    { apply funeq_mori with (x := eq e × W1).
      { unfold flip. basic_solver. }
      apply funeq_sym, funeq_eq. rewrite EQLOC.
      transitivity (E ∩₁ Loc_' lab_loc); [| basic_solver].
      rewrite EISL. apply set_subset_inter_r.
      split; apply ADD. }
    apply funeq_mori with (x := W2 × eq e).
    { unfold flip. basic_solver. }
    apply funeq_eq. rewrite EQLOC.
    transitivity (E ∩₁ Loc_' lab_loc); [| basic_solver].
    rewrite EISL. apply set_subset_inter_r.
    split; apply ADD. }
  { apply (add_event_co_tr ADD). }
  { apply (add_event_total ADD). }
  { rewrite (add_event_co ADD). apply irreflexive_union; split.
    { apply (co_irr WF). }
    unfold co_delta. apply irreflexive_union; split.
    { rewrite (add_event_W1E ADD). basic_solver. }
    rewrite (add_event_W2E ADD). basic_solver. }
  { destruct H as (b & INE & HLOC). apply EINE.
    apply (add_event_acts ADD) in INE.
    destruct INE as [INE | HEQ].
    { apply WF. unfold loc in *.
      rewrite (add_event_lab ADD) in HLOC.
      rewrite updo in HLOC by congruence.
      eauto. }
    subst b. apply (add_event_init ADD).
    rewrite <- HLOC, (add_event_lab ADD).
    unfold lab_loc, loc. now rupd. }
  { rewrite (add_event_lab ADD). destruct classic with ((InitEvent l0) = e).
    { destruct ADD. rewrite H. rewrite upds. destruct add_event_ninit0.
      unfold is_init. basic_solver. }
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
  apply (add_event_acts ADD) in EE.
  destruct EE as [EE | EQE].
  { now apply ADD, (wf_threads WF). }
  subst. apply ADD, (add_event_thrd ADD).
Qed.

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
    surg_init_min : min_elt thrdle tid_init;
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