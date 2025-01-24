Require Import ReordSimrel ReorderingEq ReorderingMapper.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import PorfPrefix.
Require Import ConsistencyCommon.
Require Import ConsistencyMonotonicity.
Require Import ConsistencyReadExtent.
Require Import ConsistencyWriteExtent.
Require Import ReorderingRpo.

Require Import SubToFullExec.
Require Import Thrdle.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Section ReordCons.

Variable X_s X_t : WCore.t.
Variable a_t b_t : actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'lab_t'" := (lab G_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'val_t'" := (val lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rhb_t'" := (rhb G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'rpo_t'" := (rpo G_t).
Notation "'rpo_imm_t'" := (rpo_imm G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'W_t'" := (fun e => is_true (is_w lab_t e)).
Notation "'R_t'" := (fun e => is_true (is_r lab_t e)).
Notation "'F_t'" := (fun e => is_true (is_f lab_t e)).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).
Notation "'Val_t_' l" := (fun e => val_t e = l) (at level 1).
Notation "'same_loc_t'" := (same_loc lab_t).
Notation "'same_val_t'" := (same_val lab_t).
Notation "'Acq_t'" := (fun e => is_true (is_acq lab_t e)).
Notation "'Rel_t'" := (fun e => is_true (is_rel lab_t e)).
Notation "'Rlx_t'" := (fun e => is_true (is_rlx lab_t e)).

Notation "'G_s'" := (WCore.G X_s).
Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rhb_s'" := (rhb G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'rpo_imm_s'" := (rpo_imm G_s).
Notation "'W_s'" := (fun e => is_true (is_w lab_s e)).
Notation "'R_s'" := (fun e => is_true (is_r lab_s e)).
Notation "'F_s'" := (fun e => is_true (is_f lab_s e)).
Notation "'b_s'" := (mapper b_t).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'same_val_s'" := (same_val lab_s).
Notation "'Acq_s'" := (fun e => is_true (is_acq lab_s e)).
Notation "'Rel_s'" := (fun e => is_true (is_rel lab_s e)).
Notation "'Rlx_s'" := (fun e => is_true (is_rlx lab_s e)).

Notation "'is_init'" := (fun e => is_true (is_init e)).
Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).
Notation "'mapper'" := (mapper a_t b_t).
Notation "'A_s'" := (extra_a X_t a_t b_t b_t).

Hypothesis INV : reord_step_pred X_t a_t b_t.
Hypothesis CONS : WCore.is_cons G_t.
Hypothesis SIMREL : reord_simrel X_s X_t a_t b_t mapper.

Lemma rsr_Gs_wf : Wf G_s.
Proof using INV SIMREL.
  eapply G_s_wf; eauto.
Qed.

Hint Resolve rsr_Gs_wf : xmm.

Lemma rsr_cons_exa_helper
    (BIN : E_t b_t)
    (ANOTIN : ~E_t a_t)
    (SMEXA : A_s ≡₁ eq b_t) :
  WCore.is_cons G_s.
Proof using INV SIMREL CONS.
  assert (NEQ : a_t <> b_t) by apply (rsr_at_neq_bt INV).
  assert (SBFROMA : ⦗eq b_t⦘ ⨾ sb_s ⊆ eq b_t × eq a_t).
  { now apply (rsr_sb_froma INV SIMREL). }
  assert (DISJ : set_disjoint (mapper ↑₁ E_t) (eq b_t)).
  { apply set_disjointE. split; auto with hahn.
    unfolder. intros x ((y & YIN & YEQ) & XEQ). subst x.
    apply ANOTIN. rewrite <- (rsr_mapper_inv_bt y NEQ); auto. }
  assert (AINS : E_s a_t).
  { apply (rsr_acts SIMREL). left.
    exists b_t. now rewrite rsr_mapper_bt; auto. }
  assert (BINS : E_s b_t).
  { apply (rsr_acts SIMREL). right. now apply SMEXA. }
  assert (AINRW : eq a_t ⊆₁ R_s ∪₁ W_s).
  { rewrite <- (simrel_a_lab_wr INV SIMREL).
    clear - AINS. basic_solver. }
  assert (BINRW : eq b_t ⊆₁ R_s ∪₁ W_s).
  { rewrite <- (simrel_b_lab_wr INV SIMREL).
    clear - BINS. basic_solver. }
  assert (AINNREL : eq a_t ⊆₁ set_compl Rel_s).
  { transitivity (set_compl (Rel_s ∪₁ Acq_s))
      ; [| basic_solver].
    rewrite <- (rsr_bs_rlx INV SIMREL).
    clear - AINS. basic_solver. }
  assert (BINACQ : eq b_t ⊆₁ set_compl Acq_s).
  { transitivity (set_compl (Rel_s ∪₁ Acq_s))
      ; [| basic_solver].
    rewrite <- (rsr_as_rlx INV SIMREL).
    clear - BINS. basic_solver. }
  assert (SLOC : ~ same_loc_s b_t a_t).
  { intro FALSO.
    apply (rsr_as_bs_loc INV SIMREL) with a_t b_t.
    clear - AINS BINS FALSO. basic_solver. }
  assert (RPOCOD : codom_rel (⦗eq b_t⦘ ⨾ rpo_s) ≡₁ ∅).
  { split; auto with hahn.
    rewrite reord_rpo_emp; eauto.
    clear. basic_solver. }
  assert (EEQ : E_s ≡₁ mapper ↑₁ E_t ∪₁ eq b_t).
  { now rewrite (rsr_acts SIMREL), SMEXA. }
  assert (SUB : E_s \₁ eq b_t ⊆₁ mapper ↑₁ E_t).
  { rewrite EEQ. basic_solver. }
  assert (RPOMAP : rpo_s ⨾ ⦗E_s \₁ eq b_t⦘ ⊆ mapper ↑ rpo_t).
  { apply reord_map_rpo with (a := a_t); auto with xmm.
    all: try symmetry; try now apply SIMREL.
    eapply rsr_sb_nexa with (a := a_t); auto.
    now rewrite (rsr_sb SIMREL), SMEXA, rsr_mapper_bt. }
  assert (SLOCD : codom_rel (⦗eq b_t⦘ ⨾ sb_s ∩ same_loc_s) ≡₁ ∅).
  { apply reord_ab_loc_codom with (a := a_t); auto. }
  assert (SBLOCMAP : sb_s ∩ same_loc_s ⨾ ⦗E_s \₁ eq b_t⦘ ⊆ mapper ↑ (sb_t ∩ same_loc_t)).
  { apply reord_sbloc_to_nb with (a := a_t); auto with xmm.
    all: try symmetry; try now apply SIMREL.
    eapply rsr_sb_nexa with (a := a_t); auto.
    now rewrite (rsr_sb SIMREL), SMEXA, rsr_mapper_bt. }
  destruct (simrel_b_lab_wr INV SIMREL) with b_t
        as [ISR | ISW].
  { apply set_subset_single_l. rewrite (rsr_acts SIMREL).
    rewrite SMEXA. basic_solver. }
  { apply XmmCons.read_extent with (G_t := G_t)
        (a := b_t) (m := mapper); eauto with xmm.
    all: try now apply SIMREL.
    all: try now apply INV.
    { now apply BINACQ. }
    all: rewrite ?(rsr_rf SIMREL), ?(rsr_co SIMREL), SMEXA.
    { arewrite (eq b_t ∩₁ R_s ≡₁ eq b_t); basic_solver. }
    arewrite (eq b_t ∩₁ W_s ≡₁ ∅); [| basic_solver 11].
    split; auto with hahn.
    clear - ISR. unfold is_r, is_w in *.
    unfolder. ins. desf. }
  apply XmmCons.write_extent with (G_t := G_t)
      (a := b_t) (m := mapper); eauto with xmm.
  all: try now apply SIMREL.
  all: try now apply INV.
  all: rewrite ?(rsr_rf SIMREL), ?(rsr_co SIMREL), SMEXA.
  { arewrite (eq b_t ∩₁ R_s ≡₁ ∅); [| basic_solver 11].
    split; auto with hahn.
    clear - ISW. unfold is_r, is_w in *.
    unfolder. ins. desf. }
  arewrite (eq b_t ∩₁ W_s ≡₁ eq b_t) by basic_solver.
  arewrite (same_loc_s b_t ≡₁ Loc_s_ (loc_s b_t)) by basic_solver.
  unfold extra_co_D, add_max. basic_solver 11.
Qed.

Lemma rsr_cons : WCore.is_cons G_s.
Proof using INV SIMREL CONS.
  destruct (classic (~ E_t a_t /\ E_t b_t)) as [EMP|NEMP].
  { apply rsr_cons_exa_helper; desf.
    rewrite extra_a_some; auto. }
  assert (NEXA : A_s ≡₁ ∅) by now apply extra_a_none.
  assert (SUB : E_s ⊆₁ mapper ↑₁ E_t).
  { now rewrite (rsr_acts SIMREL), NEXA, set_union_empty_r. }
  assert (SBEQ : sb_s ≡ mapper ↑ swap_rel sb_t (eq b_t ∩₁ E_t) (eq a_t ∩₁ E_t)).
  { rewrite (rsr_sb SIMREL), NEXA.
    now rewrite cross_false_l, cross_false_r, !union_false_r. }
  assert (RPOMAP : rpo_s ⊆ mapper ↑ rpo_t).
  { apply reord_rpo_map' with (a := a_t) (b := b_t).
    all: auto with xmm.
    { symmetry. apply SIMREL. }
    { apply SIMREL. }
    all: rewrite 1?set_unionC with (s := R_t).
    all: try now apply INV.
    all: rewrite ?(rsr_at_rlx INV), ?(rsr_bt_rlx INV).
    all: clear; basic_solver. }
  assert (SLOCMAP : sb_s ∩ same_loc_s ⊆ mapper ↑ (sb_t ∩ same_loc_t)).
  { apply reord_sbloc' with (a := a_t) (b := b_t).
    all: auto with xmm.
    all: rewrite 1?set_unionC with (s := R_t).
    all: try now apply INV.
    symmetry. apply SIMREL. }
  apply XmmCons.monoton_cons with (G_t := G_t)
              (m := mapper); eauto with xmm.
  all: try now apply SIMREL.
  all: try now apply INV.
  all: rewrite ?(rsr_acts SIMREL), ?(rsr_rf SIMREL), ?(rsr_co SIMREL).
  all: simpl; rewrite ?NEXA; basic_solver 8.
Qed.

End ReordCons.