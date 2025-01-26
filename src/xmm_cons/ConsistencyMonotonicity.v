Require Import Setoid Program.Basics.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel3 AuxInj.
Require Import Srf Rhb.
Require Import ConsistencyCommon.
Require Import MapDoms.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
Require Import xmm_s_hb.

Open Scope program_scope.

Set Implicit Arguments.

Module XmmCons.

Section ConsistencyMonotonicity.

Variable G_s G_t : execution.
Variable sc_s sc_t : relation actid.
Variable m : actid -> actid.

Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'W_s'" := (fun a => is_true (is_w lab_s a)).
Notation "'R_s'" := (fun a => is_true (is_r lab_s a)).
Notation "'F_s'" := (fun a => is_true (is_f lab_s a)).
Notation "'Rel_s'" := (fun a => is_true (is_rel lab_s a)).
Notation "'Acq_s'" := (fun a => is_true (is_acq lab_s a)).
Notation "'Rlx_s'" := (fun e => is_true (is_rlx lab_s e)).
Notation "'release_s'" := (release G_s).
Notation "'rs_s'" := (rs G_s).
Notation "'hb_s'" := (hb G_s).
Notation "'rhb_s'" := (rhb G_s).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'vf_s'" := (vf G_s).
Notation "'srf_s'" := (srf G_s).
Notation "'eco_s'" := (eco G_s).
Notation "'psc_s'" := (imm.psc G_s).
Notation "'fr_s'" := (fr G_s).
Notation "'sw_s'" := (sw G_s).

Notation "'lab_t'" := (lab G_t).
Notation "'val_t'" := (val lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'rpo_t'" := (rpo G_t).
Notation "'W_t'" := (fun a => is_true (is_w lab_t a)).
Notation "'R_t'" := (fun a => is_true (is_r lab_t a)).
Notation "'F_t'" := (fun a => is_true (is_f lab_t a)).
Notation "'Rel_t'" := (fun a => is_true (is_rel lab_t a)).
Notation "'Acq_t'" := (fun a => is_true (is_acq lab_t a)).
Notation "'Rlx_t'" := (fun e => is_true (is_rlx lab_t e)).
Notation "'release_t'" := (release G_t).
Notation "'rs_t'" := (rs G_t).
Notation "'hb_t'" := (hb G_t).
Notation "'rhb_t'" := (rhb G_t).
Notation "'same_loc_t'" := (same_loc lab_t).
Notation "'vf_t'" := (vf G_t).
Notation "'srf_t'" := (srf G_t).
Notation "'eco_t'" := (eco G_t).
Notation "'psc_t'" := (imm.psc G_t).
Notation "'fr_t'" := (fr G_t).
Notation "'sw_t'" := (sw G_t).

Hypothesis (INJ : inj_dom E_t m).
Hypothesis (E_MAP : E_s ⊆₁ m ↑₁ E_t).
Hypothesis (RPO_MAP : rpo_s ⊆ m ↑ rpo_t).
Hypothesis (RF_MAP : rf_s ⊆ m ↑ rf_t).
Hypothesis (CO_MAP : co_s ⊆ m ↑ co_t).
Hypothesis (RMW_MAP : rmw_s ⊆ m ↑ rmw_t).
Hypothesis (LAB_MAP : eq_dom E_t (lab_s ∘ m) lab_t).
Hypothesis (SBLOC_MAP : sb_s ∩ same_loc_s ⊆ m ↑ (sb_t ∩ same_loc_t)).
Hypothesis (WF_t : Wf G_t).
Hypothesis (WF_s : Wf G_s).

(*MONOTONICITY*)

Lemma monoton_fr_sub :
  fr_s ⊆ m ↑ fr_t.
Proof using RF_MAP CO_MAP INJ WF_t.
  unfold fr. rewrite RF_MAP. rewrite CO_MAP.
  rewrite <- collect_rel_transp.
  rewrite collect_rel_seq; vauto.
  assert (IN1 : codom_rel rf_t⁻¹ ⊆₁ E_t).
  { rewrite codom_transp. induction 1 as (x0 & COND).
    apply wf_rfE in COND; eauto.
    destruct COND as (x1 & INE & COND); apply INE. }
  assert (IN2 : dom_rel co_t ⊆₁ E_t).
  { induction 1 as (x0 & COND). apply wf_coE in COND; eauto.
    destruct COND as (x1 & INE & COND); apply INE. }
  rewrite IN1, IN2. basic_solver.
Qed.

Lemma monoton_eco_sub :
  eco_s ⊆ m ↑ eco_t.
Proof using RF_MAP CO_MAP INJ WF_t.
  unfold eco. repeat rewrite collect_rel_union.
  repeat apply inclusion_union_l.
  { rewrite RF_MAP; vauto. }
  { rewrite CO_MAP, RF_MAP.
    case_refl _.
    { basic_solver 12. }
    rewrite crE. rewrite seq_union_r.
    rewrite collect_rel_union. rewrite <- !unionA.
    rewrite collect_rel_seq with (rr := co_t) (rr' := rf_t); vauto.
    assert (IN1 : codom_rel co_t ⊆₁ E_t).
    { rewrite wf_coE; eauto. basic_solver. }
    assert (IN2 : dom_rel rf_t ⊆₁ E_t).
    { rewrite wf_rfE; eauto. basic_solver. }
    rewrite IN1, IN2. basic_solver. }
  rewrite monoton_fr_sub, RF_MAP; eauto.
  case_refl _.
  { basic_solver 12. }
  rewrite crE. rewrite !seq_union_r.
  rewrite !collect_rel_union. rewrite <- !unionA.
  rewrite collect_rel_seq with (rr := fr_t) (rr' := rf_t); vauto.
  assert (IN1 : codom_rel fr_t ⊆₁ E_t).
  { rewrite wf_frE; eauto. basic_solver. }
  assert (IN2 : dom_rel rf_t ⊆₁ E_t).
  { rewrite wf_rfE; eauto. basic_solver. }
  rewrite IN1, IN2. basic_solver.
Qed.

Lemma monoton_sw_helper_rf_rmw :
  rf_s ⨾ rmw_s ⊆ m ↑ (rf_t ⨾ rmw_t).
Proof using RF_MAP RMW_MAP INJ WF_t.
  rewrite RF_MAP, RMW_MAP.
  apply collect_rel_seq.
  rewrite (wf_rfE WF_t), (wf_rmwE WF_t).
  eapply inj_dom_mori; eauto.
  red. basic_solver.
Qed.

Lemma monoton_sw_helper_rs :
  ⦗E_s⦘ ⨾ rs_s ⊆ m ↑ (⦗E_t⦘ ⨾ rs_t).
Proof using RF_MAP RMW_MAP INJ WF_t LAB_MAP E_MAP.
  unfold rs.
  rewrite monoton_sw_helper_rf_rmw.
  arewrite (⦗E_s⦘ ⨾ ⦗W_s⦘ ⊆ m ↑ (⦗E_t⦘ ⨾ ⦗W_t⦘)).
  { rewrite E_MAP, <- !id_inter, collect_rel_eqv.
    apply eqv_rel_mori.
    rewrite set_interC, set_interC with (s := E_t).
    rewrite set_collect_is_w; auto.
    now symmetry. }
  rewrite <- !cr_of_ct, !crE, !seq_union_r, !seq_id_r.
  rewrite collect_rel_union. apply union_mori; [reflexivity |].
  arewrite (rf_t ⨾ rmw_t ≡ restr_rel E_t (rf_t ⨾ rmw_t)).
  { rewrite (wf_rfE WF_t), (wf_rmwE WF_t).
    rewrite !restr_relE, !seqA. basic_solver 11. }
  rewrite <- collect_rel_ct_inj, <- collect_rel_seq.
  { basic_solver. }
  all: eapply inj_dom_mori; eauto.
  all: rewrite 1?restr_ct; red; basic_solver.
Qed.

Lemma monoton_sw_helper_release :
  ⦗E_s⦘ ⨾ release_s ⊆ m ↑ (⦗E_t⦘ ⨾ release_t).
Proof using RPO_MAP RF_MAP RMW_MAP INJ WF_t LAB_MAP WF_s E_MAP.
  assert (LAB_MAP' : eq_dom E_t lab_t (lab_s ∘ m)).
  { by symmetry. }
  unfold release.
  rewrite (wf_rsD WF_s).
  arewrite (
    ⦗E_s⦘ ⨾ ⦗Rel_s⦘ ⨾ (⦗F_s⦘ ⨾ sb_s)^? ⨾ ⦗Rlx_s⦘ ⨾ ⦗W_s⦘ ⨾ rs_s ⨾ ⦗W_s⦘ ⊆
      ⦗E_s⦘ ⨾ ⦗Rel_s⦘ ⨾ (⦗F_s⦘ ⨾ sb_s)^? ⨾ ⦗Rlx_s⦘ ⨾ ⦗W_s⦘ ⨾ ⦗E_s⦘ ⨾ rs_s ⨾ ⦗W_s⦘
  ).
  { do 2 hahn_frame_r.
    rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l.
    apply union_mori; [clear; basic_solver |].
    rewrite wf_sbE. do 2 hahn_frame_l. basic_solver. }
  arewrite (
    ⦗Rel_s⦘ ⨾ (⦗F_s⦘ ⨾ sb_s)^? ⨾ ⦗Rlx_s⦘ ⨾ ⦗W_s⦘ ⊆
      ⦗Rel_s⦘ ⨾ (⦗F_s⦘ ⨾ rpo_s)^? ⨾ ⦗Rlx_s⦘
  ).
  { rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l.
    apply union_mori; [basic_solver |].
    rewrite !seqA. seq_rewrite <- !id_inter.
    unfold rpo. rewrite <- ct_step.
    unfold rpo_imm. basic_solver 11. }
  rewrite (@inclusion_seq_eqv_r _ rs_s W_s).
  sin_rewrite monoton_sw_helper_rs.
  rewrite RPO_MAP, E_MAP, <- collect_rel_eqv, rpo_in_sb.
  rewrite mapdom_rewrite_rel
    with (r := ⦗E_t⦘ ⨾ rs_t) (G := G_t);
    [| rewrite (wf_rsE WF_t); clear; basic_solver 11].
  seq_rewrite mapdom_rewrite_l.
  rewrite set_collect_rel; eauto.
  seq_rewrite <- (id_inter Rlx_s (m ↑₁ E_t)).
  rewrite set_collect_rlx; eauto.
  rewrite mapdom_rewrite_rel with (r := sb_t); eauto using wf_sbE.
  seq_rewrite <- (id_inter F_s (m ↑₁ E_t)).
  rewrite set_collect_is_f; eauto.
  rewrite !crE, !seq_union_l, !seq_union_r,
          !seq_id_l, collect_rel_union.
  apply union_mori.
  all: rewrite <- !collect_rel_eqv, <- !collect_rel_seq.
  all: try eapply inj_dom_mori; eauto.
  all: try (apply collect_rel_mori; auto; basic_solver 11).
  all: rewrite 1?(wf_rsE WF_t), 1?(wf_sbE G_t).
  all: unfold flip; basic_solver.
Qed.

Lemma monoton_sw_sub_helper :
  sw_s ⊆ m ↑ sw_t.
Proof using RPO_MAP RF_MAP RMW_MAP INJ WF_t LAB_MAP WF_s E_MAP.
  assert (LAB_MAP' : eq_dom E_t lab_t (lab_s ∘ m)).
  { by symmetry. }
  rewrite (wf_swE WF_s).
  unfold sw. rewrite !seqA.
  sin_rewrite monoton_sw_helper_release.
  arewrite (
    rf_s ⨾ ⦗Rlx_s⦘ ⨾ (sb_s ⨾ ⦗F_s⦘)^? ⨾ ⦗Acq_s⦘ ⊆
      rf_s ⨾ ⦗Rlx_s⦘ ⨾ (rpo_s ⨾ ⦗F_s⦘)^? ⨾ ⦗Acq_s⦘
  ).
  { rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l.
    apply union_mori; [reflexivity |].
    rewrite (wf_rfD WF_s), !seqA. do 2 hahn_frame_l.
    seq_rewrite <- !id_inter.
    unfold rpo. rewrite <- ct_step.
    unfold rpo_imm. basic_solver 11. }
  sin_rewrite RF_MAP.
  rewrite RPO_MAP, E_MAP, <- collect_rel_eqv.
  rewrite rpo_in_sb.
  rewrite mapdom_rewrite_rel
    with (r := rf_t) (G := G_t);
    [| apply (wf_rfE WF_t)].
  rewrite !seqA.
  seq_rewrite mapdom_rewrite_l'.
  rewrite set_collect_rlx; eauto.
  rewrite mapdom_rewrite_rel with (r := sb_t); eauto using wf_sbE.
  rewrite !seqA, mapdom_rewrite_l'.
  rewrite set_collect_is_f; eauto.
  seq_rewrite mapdom_rewrite_r.
  rewrite set_collect_acq; eauto.
  rewrite !crE, !seq_union_l, !seq_union_r,
          !seq_id_l, collect_rel_union.
  apply union_mori.
  all: rewrite <- !collect_rel_eqv, <- !collect_rel_seq.
  all: try eapply inj_dom_mori; eauto.
  all: try (apply collect_rel_mori; auto; basic_solver 11).
  all: rewrite 1?(wf_releaseE WF_t), 1?(wf_rfE WF_t),
               1?(wf_sbE G_t).
  all: unfold flip; basic_solver.
Qed.

Lemma monoton_rhb_sub :
  rhb_s ⊆ m ↑ rhb_t.
Proof using SBLOC_MAP RPO_MAP RF_MAP RMW_MAP INJ WF_t LAB_MAP WF_s E_MAP.
  unfold rhb.
  rewrite monoton_sw_sub_helper, SBLOC_MAP, RPO_MAP.
  rewrite <- !collect_rel_union.
  arewrite (
    sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t ≡
      restr_rel E_t (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)
  ).
  { rewrite wf_sbE, wf_rpoE, (wf_swE WF_t) at 1.
    rewrite seq_eqv_inter_ll, seq_eqv_inter_lr.
    rewrite <- !seq_union_r, <- !seq_union_l.
    now rewrite restr_relE. }
  rewrite collect_rel_ct_inj; auto with hahn.
Qed.

Lemma monoton_cons
    (CONS : WCore.is_cons G_t) :
  WCore.is_cons G_s.
Proof using SBLOC_MAP CO_MAP RPO_MAP RF_MAP RMW_MAP INJ WF_t LAB_MAP WF_s E_MAP.
  constructor.
  { case_refl _.
    { rewrite hb_helper; eauto. rewrite irreflexive_union. split.
      { apply sb_irr; eauto. }
      rewrite monoton_rhb_sub.
      arewrite (rhb_t ≡ restr_rel E_t rhb_t).
      { rewrite restr_relE. now rewrite (wf_rhbE WF_t) at 1. }
      apply collect_rel_irr_inj; auto.
      rewrite restr_relE, <- (wf_rhbE WF_t).
      arewrite (rhb_t ⊆ hb_t ⨾ eco_t^?); [| apply CONS].
      rewrite rhb_in_hb. basic_solver. }
    apply (rhb_eco_irr_equiv WF_s).
    rewrite monoton_eco_sub, monoton_rhb_sub.
    rewrite (wf_rhbE WF_t), (wf_ecoE WF_t).
    rewrite <- collect_rel_seq;
      [| eapply inj_dom_mori; eauto; red; basic_solver].
    arewrite (
      (⦗E_t⦘ ⨾ rhb_t ⨾ ⦗E_t⦘) ⨾ ⦗E_t⦘ ⨾ eco_t ⨾ ⦗E_t⦘ ⊆
        restr_rel E_t (rhb_t ⨾ eco_t)
    ).
    { rewrite !seqA. basic_solver. }
    apply collect_rel_irr_inj; auto.
    arewrite (restr_rel E_t (rhb_t ⨾ eco_t) ⊆ rhb_t ⨾ eco_t).
    arewrite (rhb_t ⨾ eco_t ⊆ hb_t ⨾ eco_t^?); [| apply CONS].
    rewrite rhb_in_hb. basic_solver. }
  split; [| basic_solver].
  rewrite RMW_MAP, CO_MAP, monoton_fr_sub; eauto.
  rewrite <- collect_rel_seq.
  { rewrite <- XmmCons.coll_rel_inter; eauto.
    { destruct CONS. rewrite cons_atomicity.
      basic_solver. }
    assert (IN1 : dom_rel rmw_t ⊆₁ E_t).
    { rewrite wf_rmwE; eauto. basic_solver. }
    assert (IN2 : codom_rel rmw_t ⊆₁ E_t).
    { rewrite wf_rmwE; eauto. basic_solver. }
    assert (IN3 : dom_rel (fr_t ⨾ co_t) ⊆₁ E_t).
    { rewrite wf_frE, wf_coE; eauto. basic_solver. }
    assert (IN4 : codom_rel (fr_t ⨾ co_t) ⊆₁ E_t).
    { rewrite wf_frE, wf_coE; eauto. basic_solver. }
    rewrite IN1, IN2, IN3, IN4. basic_solver. }
  assert (IN1 : codom_rel fr_t ⊆₁ E_t).
  { rewrite wf_frE; eauto. basic_solver. }
  assert (IN2 : dom_rel co_t ⊆₁ E_t).
  { rewrite wf_coE; eauto. basic_solver. }
  rewrite IN1, IN2. basic_solver.
Qed.

End ConsistencyMonotonicity.

End XmmCons.