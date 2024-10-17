Require Import Lia Setoid Program.Basics.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms.

Require Import Core.

Set Implicit Arguments.

Section AddEvent.

Variable sc sc' : relation actid.
Variable X X' : WCore.t.
Variable e : actid.
Variable l : label.
Variable cmt : actid -> Prop.

Notation "'G''" := (WCore.G X').
Notation "'G'" := (WCore.G X).

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
Notation "'W''" := (fun a => is_true (is_w lab' a)).
Notation "'R''" := (fun a => is_true (is_r lab' a)).
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
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'same_loc'" := (same_loc lab).
Notation "'same_val'" := (same_val lab).
Notation "'Loc_' l" := (fun e => loc e = l) (at level 1).
Notation "'Val_' v" := (fun e => val e = v) (at level 1).

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
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2)
    (WF : Wf (WCore.G X)) :
  Wf (WCore.G X').
Proof using.
  assert (NCTRL : ctrl ≡ ∅₂).
  { split; [| basic_solver].
    rewrite <- (WCore.add_event_ctrl ADD).
    apply ADD. }
  assert (NIN : ~ E e).
  { apply (WCore.add_event_new ADD). }
  assert (EISR : E ∩₁ R' ≡₁ E ∩₁ R).
  { unfold is_r. rewrite (WCore.add_event_lab ADD).
    unfolder; split; intros x (INE & LAB).
    all: now rewrite updo in * by congruence. }
  assert (EISW : E ∩₁ W' ≡₁ E ∩₁ W).
  { unfold is_w. rewrite (WCore.add_event_lab ADD).
    unfolder; split; intros x (INE & LAB).
    all: now rewrite updo in * by congruence. }
  assert (EISREX : E ∩₁ R_ex lab ≡₁ E ∩₁ R_ex lab').
  { unfold R_ex. rewrite (WCore.add_event_lab ADD).
    unfolder; split; intros x (INE & LAB).
    all: now rewrite updo in * by congruence. }
  assert (EISL : E ∩₁ Loc_' (WCore.lab_loc l) ≡₁ E ∩₁ Loc_ (WCore.lab_loc l)).
  { unfold loc. rewrite (WCore.add_event_lab ADD).
    unfolder; split; intros x (INE & LAB).
    all: now rewrite updo in * by congruence. }
  assert (EISV : E ∩₁ Val_' (WCore.lab_val l) ≡₁ E ∩₁ Val_ (WCore.lab_val l)).
  { unfold val. rewrite (WCore.add_event_lab ADD).
    unfolder; split; intros x (INE & LAB).
    all: now rewrite updo in * by congruence. }
  assert (EQLOC : loc' e = WCore.lab_loc l).
  { rewrite (WCore.add_event_lab ADD). unfold loc, WCore.lab_loc.
    now rupd. }
  assert (EQVAL : val' e = WCore.lab_val l).
  { rewrite (WCore.add_event_lab ADD). unfold val, WCore.lab_val.
    now rupd. }
  assert (EINTER : E ∩₁ E' ≡₁ E).
  { rewrite (WCore.add_event_acts ADD). basic_solver. }
  assert (EINE : E ⊆₁ E').
  { rewrite (WCore.add_event_acts ADD). basic_solver. }
  assert (SLE : ⦗E⦘ ⨾ same_loc ⨾ ⦗E⦘ ⊆ same_loc').
  { rewrite (WCore.add_event_lab ADD).
    unfolder; intros x y (EX & SL & EY).
    unfold same_loc in *. unfold loc in *.
    do 2 rewrite updo in * by congruence.
    eauto. }
  assert (VLE : ⦗E⦘ ⨾ same_val ⨾ ⦗E⦘ ⊆ same_val').
  { rewrite (WCore.add_event_lab ADD).
    unfolder; intros x y (EX & SL & EY).
    unfold same_val in *. unfold val in *.
    do 2 rewrite updo in * by congruence.
    eauto. }
  constructor.
  { assert (ENINIT : ~is_init e) by apply ADD.
    intros a b (INA & INB & NEQ & TIDS & NINIT).
    apply (WCore.add_event_acts ADD) in INA, INB.
    destruct INA as [INA | AEQE],
             INB as [INB | BEQE].
    all: subst; ins.
    { now apply WF. }
    { unfold is_init in *. desf. ins. congruence. }
    destruct b as [bl | bt bn]; ins.
    { exfalso. now apply (WCore.add_event_tid_e ADD). }
    unfold is_init in *. desf. ins. congruence. }
  all: ins.
  { rewrite (WCore.add_event_data ADD). rewrite (WCore.add_event_sb ADD).
    rewrite (data_in_sb WF). basic_solver. }
  { rewrite (WCore.add_event_data ADD), (wf_dataE WF).
    rewrite (wf_dataD WF) at 1. rewrite !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    now rewrite EISR, EISW. }
  { rewrite (WCore.add_event_addr ADD). rewrite (WCore.add_event_sb ADD).
    rewrite (addr_in_sb WF). basic_solver. }
  { rewrite (WCore.add_event_addr ADD), (wf_addrE WF).
    rewrite (wf_addrD WF) at 1. rewrite !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    do 2 rewrite set_inter_union_r.
    now rewrite EISR, EISW. }
  { rewrite (WCore.add_event_ctrl ADD). rewrite (WCore.add_event_sb ADD).
    rewrite (ctrl_in_sb WF). basic_solver. }
  { rewrite (WCore.add_event_ctrl ADD), (wf_ctrlE WF).
    rewrite (wf_ctrlD WF) at 1. rewrite !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    now rewrite EISR. }
  { rewrite (WCore.add_event_ctrl ADD). rewrite (WCore.add_event_sb ADD).
    rewrite seq_union_r. apply inclusion_union_l; eauto.
    { rewrite (ctrl_sb WF). basic_solver. }
    rewrite NCTRL. basic_solver. }
  { rewrite (WCore.add_event_rmw ADD), !seq_union_l,
            !seq_union_r.
    apply union_more.
    { rewrite (wf_rmwD WF) at 1.
      rewrite (wf_rmwE WF), !seqA.
      seq_rewrite <- !id_inter.
      now rewrite EISW, !set_interC with (s' := E), EISR. }
    unfold WCore.rmw_delta.
    destruct classic with (W' e) as [ISW|NW].
    all: try now (rewrite (WCore.add_event_r ADD NW); basic_solver).
    rewrite <- cross_inter_r, <- cross_inter_l.
    apply cross_more; [| basic_solver].
    arewrite (eq_opt r ≡₁ E ∩₁ eq_opt r).
    { rewrite set_inter_absorb_l; ins. apply ADD. }
    rewrite <- set_interA, set_interC with (s := R'),
            EISR, set_interA.
    apply set_equiv_inter; ins.
    rewrite set_inter_absorb_l; [ins | apply ADD]. }
  { rewrite (WCore.add_event_rmw ADD), (wf_rmwE WF), (wf_rmwl WF).
    apply inclusion_union_l; eauto. unfold WCore.rmw_delta.
    arewrite (eq_opt r ⊆₁ E ∩₁ Loc_ (WCore.lab_loc l)).
    { apply set_subset_inter_r. split; apply ADD. }
    apply same_loc_eq. rewrite EQLOC, <- EISL.
    basic_solver. }
  { rewrite (WCore.add_event_rmw ADD).
    apply inclusion_union_l; [| apply ADD].
    rewrite (WCore.add_event_sb ADD). intros x y RMW.
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
      unfold WCore.sb_delta in H0. assert (EQ : e = y).
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
    unfold WCore.sb_delta in H0. assert (EQ : e = y).
    { destruct H0; eauto. }
    subst. basic_solver. }
  { rewrite (WCore.add_event_rf ADD), !seq_union_l, !seq_union_r.
    repeat apply union_more; ins.
    { rewrite (wf_rfE WF). rewrite !seqA.
      basic_solver 7. }
    { unfold WCore.rf_delta_R. rewrite (WCore.add_event_acts ADD).
      rewrite <- cross_inter_r, <- cross_inter_l.
      apply cross_more; [| basic_solver].
      rewrite set_inter_absorb_l; ins.
      rewrite (WCore.add_event_wE ADD). basic_solver. }
    unfold WCore.rf_delta_W. rewrite (WCore.add_event_acts ADD).
    rewrite <- cross_inter_r, <- cross_inter_l.
    apply cross_more; [basic_solver |].
    rewrite set_inter_absorb_r; ins.
    rewrite (WCore.add_event_R1E ADD). basic_solver. }
  { rewrite (WCore.add_event_rf ADD), !seq_union_l, !seq_union_r.
    repeat apply union_more; ins.
    { rewrite (wf_rfD WF) at 1.
      rewrite (wf_rfE WF), !seqA.
      seq_rewrite <- !id_inter.
      now rewrite !set_interC with (s' := E), EISW, EISR. }
    { unfold WCore.rf_delta_R.
      destruct classic with (R' e) as [ISR|NR].
      all: try now (rewrite (WCore.add_event_w ADD NR); basic_solver).
      rewrite <- cross_inter_r, <- cross_inter_l.
      apply cross_more; [| basic_solver].
      arewrite (eq_opt w ≡₁ E ∩₁ eq_opt w).
      { rewrite set_inter_absorb_l; ins. apply ADD. }
      rewrite <- set_interA, set_interC with (s := W'),
              EISW, set_interA.
      apply set_equiv_inter; ins.
      rewrite set_inter_absorb_l; [ins | apply ADD]. }
    unfold WCore.rf_delta_W.
    destruct classic with (W' e) as [ISW|NW].
    all: try now (rewrite (WCore.add_event_R1 ADD NW); basic_solver).
    rewrite <- cross_inter_r, <- cross_inter_l.
    apply cross_more; [basic_solver |].
    arewrite (R1 ≡₁ E ∩₁ R1).
    { rewrite set_inter_absorb_l; ins. apply ADD. }
    rewrite set_interA, set_interC with (s' := R'),
            <- set_interA, EISR, set_interA.
    apply set_equiv_inter; ins.
    rewrite set_inter_absorb_l; [ins | apply ADD]. }
  { rewrite (WCore.add_event_rf ADD), (wf_rfE WF), (wf_rfl WF).
    repeat apply inclusion_union_l; eauto.
    all: unfold WCore.rf_delta_R, WCore.rf_delta_W.
    { transitivity (eq_opt w × eq e); [basic_solver |].
      arewrite (eq_opt w ⊆₁ E ∩₁ Loc_ (WCore.lab_loc l)).
      { apply set_subset_inter_r. split; apply ADD. }
      apply same_loc_eq. rewrite EQLOC, <- EISL.
      basic_solver. }
    transitivity (eq e × R1); [basic_solver |].
    arewrite (R1 ⊆₁ E ∩₁ Loc_ (WCore.lab_loc l)).
    { apply set_subset_inter_r. split; apply ADD. }
    apply same_loc_sym, same_loc_eq. rewrite EQLOC, <- EISL.
    basic_solver. }
  { rewrite (WCore.add_event_rf ADD).
    repeat apply funeq_union.
    { enough (rf ⊆ same_val') by ins.
      transitivity (⦗E⦘ ⨾ same_val ⨾ ⦗E⦘); ins.
      rewrite (wf_rfE WF). repeat apply seq_mori; ins.
      apply WF. }
    { apply funeq_mori with (x := eq_opt w × eq e).
      { unfold flip, WCore.rf_delta_R. basic_solver. }
      apply funeq_eq. rewrite EQVAL.
      transitivity (E ∩₁ Val_' (WCore.lab_val l)); [| basic_solver].
      rewrite EISV. apply set_subset_inter_r.
      split; apply ADD. }
    apply funeq_mori with (x := eq e × R1).
    { unfold flip, WCore.rf_delta_W. basic_solver. }
    apply funeq_sym, funeq_eq. rewrite EQVAL.
    transitivity (E ∩₁ Val_' (WCore.lab_val l)); [| basic_solver].
    rewrite EISV. apply set_subset_inter_r.
    split; apply ADD. }
  { apply (WCore.add_event_rff ADD). }
  { rewrite (WCore.add_event_co ADD), !seq_union_l, !seq_union_r.
    apply union_more.
    { rewrite (wf_coE WF), !seqA.
      seq_rewrite <- !id_inter.
      basic_solver 7. }
    unfold WCore.co_delta. rewrite seq_union_l, seq_union_r.
    apply union_more.
    { rewrite (WCore.add_event_acts ADD).
      rewrite <- cross_inter_r, <- cross_inter_l.
      apply cross_more; [basic_solver |].
      rewrite set_inter_absorb_r; ins.
      rewrite (WCore.add_event_W1E ADD). basic_solver. }
    rewrite (WCore.add_event_acts ADD).
    rewrite <- cross_inter_r, <- cross_inter_l.
    apply cross_more; [| basic_solver].
    rewrite set_inter_absorb_l; ins.
    rewrite (WCore.add_event_W2E ADD). basic_solver. }
  { rewrite (WCore.add_event_co ADD), !seq_union_l, !seq_union_r.
    repeat apply union_more; ins.
    { rewrite (wf_coD WF) at 1.
      rewrite (wf_coE WF), !seqA.
      seq_rewrite <- !id_inter.
      now rewrite !set_interC with (s' := E), EISW. }
    unfold WCore.co_delta.
    destruct classic with (W' e) as [ISW|NW].
    all: try now (rewrite (WCore.add_event_W1 ADD NW), (WCore.add_event_W2 ADD NW); basic_solver).
    rewrite seq_union_l, seq_union_r.
    rewrite <- !cross_inter_r, <- !cross_inter_l.
    apply union_more.
    { apply cross_more; [basic_solver |].
      arewrite (W1 ≡₁ E ∩₁ W1).
      { rewrite set_inter_absorb_l; ins. apply ADD. }
      rewrite set_interA, set_interC with (s' := W'),
              <- set_interA, EISW, set_interA.
      apply set_equiv_inter; ins.
      rewrite set_inter_absorb_l; [ins | apply ADD]. }
    apply cross_more; [| basic_solver].
    arewrite (W2 ≡₁ E ∩₁ W2).
    { rewrite set_inter_absorb_l; ins. apply ADD. }
    rewrite <- set_interA, set_interC with (s := W'),
            EISW, set_interA.
    apply set_equiv_inter; ins.
    rewrite set_inter_absorb_l; [ins | apply ADD]. }
  { rewrite (WCore.add_event_co ADD). unfold WCore.co_delta.
    repeat apply inclusion_union_l.
    { transitivity (⦗E⦘ ⨾ same_loc ⨾ ⦗E⦘); ins.
      rewrite (wf_coE WF). repeat apply seq_mori; ins.
      apply WF. }
    { apply funeq_mori with (x := eq e × W1).
      { unfold flip. basic_solver. }
      apply funeq_sym, funeq_eq. rewrite EQLOC.
      transitivity (E ∩₁ Loc_' (WCore.lab_loc l)); [| basic_solver].
      rewrite EISL. apply set_subset_inter_r.
      split; apply ADD. }
    apply funeq_mori with (x := W2 × eq e).
    { unfold flip. basic_solver. }
    apply funeq_eq. rewrite EQLOC.
    transitivity (E ∩₁ Loc_' (WCore.lab_loc l)); [| basic_solver].
    rewrite EISL. apply set_subset_inter_r.
    split; apply ADD. }
  { apply (WCore.add_event_co_tr ADD). }
  { apply (WCore.add_event_total ADD). }
  { rewrite (WCore.add_event_co ADD). apply irreflexive_union; split.
    { apply (co_irr WF). }
    unfold WCore.co_delta. apply irreflexive_union; split.
    { rewrite (WCore.add_event_W1E ADD). basic_solver. }
    rewrite (WCore.add_event_W2E ADD). basic_solver. }
  { destruct H as (b & INE & HLOC). apply EINE.
    apply (WCore.add_event_acts ADD) in INE.
    destruct INE as [INE | HEQ].
    { apply WF. unfold loc in *.
      rewrite (WCore.add_event_lab ADD) in HLOC.
      rewrite updo in HLOC by congruence.
      eauto. }
    subst b. now apply (WCore.add_event_init ADD). }
  { rewrite (WCore.add_event_lab ADD), updo.
    { apply WF. }
    intro FALSO. apply (WCore.add_event_ninit ADD).
    subst e. clear. auto. }
  { rewrite (WCore.add_event_rmw_dep ADD). rewrite (WCore.add_event_sb ADD).
    rewrite (rmw_dep_in_sb WF). basic_solver. }
  { rewrite (WCore.add_event_rmw_dep ADD). rewrite (wf_rmw_depD WF).
    rewrite (wf_rmw_depE WF).
    rewrite (wf_rmw_depD WF) at 1. rewrite !seqA.
    seq_rewrite !seq_eqv. rewrite !set_interC with (s' := E).
    rewrite <- !set_interA. rewrite EISR.
    rewrite !set_interC with (s' := (fun a : actid => R_ex lab a)).
    rewrite !set_interA. rewrite <- EISREX.
    basic_solver 8. }
  apply (WCore.add_event_acts ADD) in EE.
  destruct EE as [EE | EQE].
  { now apply ADD, (wf_threads WF). }
  subst. apply ADD, (WCore.add_event_thrd ADD).
Qed.

End AddEvent.