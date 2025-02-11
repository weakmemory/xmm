Require Import Setoid Program.Basics.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2 AuxRel3 AuxInj.
Require Import Srf Rhb MapDoms.
Require Import ConsistencyCommon.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
Require Import xmm_s_hb.

Open Scope program_scope.

Set Implicit Arguments.

Module XmmCons.

Section ConsistencyReadExtent.

Variable G_s G_t : execution.
Variable sc_s sc_t : relation actid.
Variable drf : relation actid.
Variable a : actid.
Variable m : actid -> actid.

Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
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
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).
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
Hypothesis (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a).
Hypothesis (IS_NACQ : ~Acq_s a).
Hypothesis (IS_NREL : ~Rel_s a).
Hypothesis (NIN : set_disjoint (m ↑₁ E_t) (eq a)).
Hypothesis (CODOM_RPO : ⦗eq a⦘ ⨾ rpo_s ⊆ ∅₂).
Hypothesis (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t).
Hypothesis (CODOM_SB_SL : ⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s) ⊆ ∅₂).
Hypothesis (SB_SL_MAP : (sb_s ∩ same_loc_s) ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t)).
Hypothesis (RF_MAP : rf_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rf_t).
Hypothesis (CO_MAP : co_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ co_t).
Hypothesis (RFRE : rf_s ⊆ ⦗E_s \₁ eq a⦘ ⨾ rf_s).
Hypothesis (RMW_MAP : rmw_s ⊆ m ↑ rmw_t).
Hypothesis (WF_t : Wf G_t).
Hypothesis (WF_s : Wf G_s).
Hypothesis (LABS : eq_dom E_t (lab_s ∘ m) lab_t).

Lemma acts_set_helper : E_s \₁ eq a ≡₁ m ↑₁ E_t.
Proof using E_MAP NIN.
  rewrite E_MAP. rewrite set_minus_union_l.
  rewrite set_minusK. rewrite set_union_empty_r.
  apply set_minus_disjoint; eauto.
Qed.

Lemma read_codom_sw : ⦗eq a⦘ ⨾ sw_s ⊆ ∅₂.
Proof using IS_NREL WF_s.
  rewrite (wf_swD WF_s).
  seq_rewrite <- id_inter.
  clear - IS_NREL. basic_solver 11.
Qed.

Lemma read_sw_helper_rf_rmw :
  rf_s ⨾ rmw_s ⊆ m ↑ (rf_t ⨾ rmw_t).
Proof using INJ E_MAP NIN RF_MAP RMW_MAP
            WF_t WF_s.
  rewrite RMW_MAP.
  rewrite (wf_rmwE WF_t) at 1.
  rewrite !collect_rel_seqi.
  rewrite collect_rel_eqv, <- acts_set_helper.
  sin_rewrite RF_MAP.
  rewrite collect_rel_seq; [basic_solver 11 |].
  rewrite (wf_rfE WF_t), (wf_rmwE WF_t).
  eapply inj_dom_mori; eauto.
  unfold flip. clear. basic_solver.
Qed.

Lemma read_sw_helper_rs :
  ⦗E_s \₁ eq a⦘ ⨾ rs_s ⊆ m ↑ (⦗E_t⦘ ⨾ rs_t).
Proof using RF_MAP RMW_MAP INJ WF_t LABS E_MAP WF_s NIN.
  unfold rs.
  rewrite read_sw_helper_rf_rmw.
  arewrite (⦗E_s \₁ eq a⦘ ⨾ ⦗W_s⦘ ⊆ m ↑ (⦗E_t⦘ ⨾ ⦗W_t⦘)).
  { rewrite acts_set_helper, <- !id_inter, collect_rel_eqv.
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

Lemma read_sw_helper_release :
  ⦗E_s \₁ eq a⦘ ⨾ release_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (⦗E_t⦘ ⨾ release_t).
Proof using RPO_MAP RF_MAP RMW_MAP INJ WF_t LABS WF_s E_MAP RFRE NIN.
  assert (LAB_MAP' : eq_dom E_t lab_t (lab_s ∘ m)).
  { by symmetry. }
  unfold release.
  rewrite (wf_rsD WF_s).
  arewrite (
    ⦗E_s \₁ eq a⦘ ⨾ ⦗Rel_s⦘ ⨾ (⦗F_s⦘ ⨾ sb_s)^? ⨾ ⦗Rlx_s⦘ ⨾ ⦗W_s⦘ ⨾ rs_s ⨾ ⦗W_s⦘ ⊆
      ⦗E_s \₁ eq a⦘ ⨾ ⦗Rel_s⦘ ⨾ (⦗F_s⦘ ⨾ sb_s)^? ⨾ ⦗Rlx_s⦘ ⨾ ⦗W_s⦘ ⨾ ⦗E_s⦘ ⨾ rs_s ⨾ ⦗W_s⦘
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
  arewrite (
    ⦗E_s⦘ ⨾ rs_s ⨾ ⦗W_s⦘ ⨾ ⦗E_s \₁ eq a⦘ ⊆
      ⦗E_s \₁ eq a⦘ ⨾ rs_s ⨾ ⦗W_s⦘
  ).
  { unfold rs.
    rewrite <- cr_of_ct, crE, !seqA.
    rewrite !seq_union_l, !seq_union_r.
    apply union_mori; [clear; basic_solver |].
    rewrite RFRE at 1. rewrite seqA, ct_seq_eqv_l.
    sin_rewrite (@inclusion_seq_eqv_l _ rf_s (E_s \₁ eq a)).
    clear. basic_solver 11. }
  rewrite (@inclusion_seq_eqv_r _ rs_s W_s).
  sin_rewrite read_sw_helper_rs.
  arewrite (
    (⦗F_s⦘ ⨾ rpo_s)^? ⨾ ⦗Rlx_s⦘ ⨾ m ↑ (⦗E_t⦘ ⨾ rs_t) ⊆
      (⦗F_s⦘ ⨾ rpo_s ⨾ ⦗E_s \₁ eq a⦘)^? ⨾ ⦗Rlx_s⦘ ⨾ m ↑ (⦗E_t⦘ ⨾ rs_t)
  ).
  { rewrite !crE.
    rewrite !seq_union_l. apply union_mori; [reflexivity |].
    arewrite (⦗E_t⦘ ⨾ rs_t ⊆ ⦗E_t⦘ ⨾ (⦗E_t⦘ ⨾ rs_t)) by basic_solver.
    rewrite collect_rel_seqi.
    rewrite collect_rel_eqv, acts_set_helper.
    clear. hahn_frame_r. basic_solver 11. }
  sin_rewrite RPO_MAP.
  rewrite acts_set_helper, <- collect_rel_eqv, rpo_in_sb.
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

Lemma read_sw_sub_helper :
  sw_s ⊆ m ↑ sw_t.
Proof using RPO_MAP RF_MAP RMW_MAP INJ WF_t LABS WF_s E_MAP RFRE
            SB_SL_MAP NIN IS_NREL IS_NACQ CO_MAP CODOM_SB_SL CODOM_RPO.
  assert (LAB_MAP' : eq_dom E_t lab_t (lab_s ∘ m)).
  { by symmetry. }
  rewrite (wf_swE WF_s).
  unfold sw. rewrite !seqA.
  rewrite set_union_minus
     with (s := E_s) (s' := eq a)
       at 1; [| rewrite E_MAP; basic_solver].
  rewrite id_union, seq_union_l.
  arewrite_false (⦗eq a⦘ ⨾ release_s).
  { unfold release. basic_solver 11. }
  rewrite seq_false_l, union_false_r.
  rewrite RFRE. rewrite !seqA.
  sin_rewrite read_sw_helper_release.
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
  rewrite set_union_minus
     with (s := E_s) (s' := eq a)
       at 1; [| rewrite E_MAP; basic_solver].
  rewrite id_union, seq_union_r.
  arewrite_false (⦗Acq_s⦘ ⨾ ⦗eq a⦘).
  { basic_solver. }
  rewrite union_false_r.
  rewrite (wf_rfE WF_s) at 1. rewrite !seqA.
  rewrite set_union_minus
     with (s := E_s) (s' := eq a)
       at 2; [| rewrite E_MAP; basic_solver].
  sin_rewrite (@inclusion_seq_eqv_l _ rf_s E_s).
  rewrite id_union, seq_union_l.
  arewrite_false (
    ⦗eq a⦘ ⨾ ⦗Rlx_s⦘ ⨾ (rpo_s ⨾ ⦗F_s⦘)^? ⨾
      ⦗Acq_s⦘ ⨾ ⦗E_s \₁ eq a⦘
  ).
  { rewrite <- union_false_r with (r := ∅₂).
    rewrite crE, !seq_union_l, !seq_union_r.
    apply union_mori; [basic_solver 11 |].
    seq_rewrite (seq_eqvC (eq a) Rlx_s).
    rewrite !seqA.
    sin_rewrite CODOM_RPO.
    rewrite seq_false_l, seq_false_r.
    reflexivity. }
  rewrite union_false_r.
  arewrite (
    (rpo_s ⨾ ⦗F_s⦘)^? ⨾ ⦗Acq_s⦘ ⨾ ⦗E_s \₁ eq a⦘ ⊆
      (rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⨾ ⦗F_s⦘)^? ⨾ ⦗Acq_s⦘ ⨾ ⦗E_s \₁ eq a⦘
  ).
  { rewrite !crE.
    rewrite !seq_union_l.
    apply union_mori; [basic_solver |].
    basic_solver. }
  sin_rewrite RF_MAP.
  sin_rewrite RPO_MAP.
  rewrite acts_set_helper, <- collect_rel_eqv.
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

Lemma read_rhb_imm_codom :
    ⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⊆ ∅₂.
Proof using INJ E_MAP IS_NACQ IS_NREL NIN CODOM_RPO RPO_MAP
            CODOM_SB_SL SB_SL_MAP RF_MAP CO_MAP RMW_MAP
            LABS WF_t WF_s.
  rewrite !seq_union_r.
  sin_rewrite read_codom_sw.
  sin_rewrite CODOM_RPO.
  sin_rewrite CODOM_SB_SL.
  now rewrite !union_false_r.
Qed.

Lemma read_rhb_imm_start :
    ⦗E_s \₁ eq a⦘
      ⨾  (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)
        ⨾ ⦗E_s \₁ eq a⦘ ≡
          (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘.
Proof using INJ E_MAP IS_NACQ IS_NREL NIN CODOM_RPO RPO_MAP
            CODOM_SB_SL SB_SL_MAP RF_MAP CO_MAP RMW_MAP
            LABS WF_t WF_s RFRE.
  split; [clear; basic_solver|].
  remember (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) as rhbimm.
  arewrite (rhbimm ⊆ ⦗E_s⦘ ⨾ rhbimm ⨾ ⦗E_s⦘).
  { subst rhbimm.
    arewrite (
      sb_s ∩ same_loc_s ⊆
        ⦗E_s⦘ ⨾ (sb_s ∩ same_loc_s) ⨾ ⦗E_s⦘
    ).
    { rewrite wf_sbE at 1.
      rewrite <- seq_eqv_inter_lr.
      rewrite <- seq_eqv_inter_ll.
      reflexivity. }
    rewrite wf_rpoE, (wf_swE WF_s) at 1.
    clear. basic_solver 11. }
  arewrite (⦗E_s⦘ ⨾ ⦗E_s \₁ eq a⦘ ⊆ ⦗E_s \₁ eq a⦘).
  rewrite set_union_minus
     with (s := E_s) (s' := eq a)
       at 1; [| rewrite E_MAP; basic_solver].
  rewrite id_union, !seq_union_l.
  arewrite_false (⦗eq a⦘ ⨾ rhbimm).
  { subst rhbimm. apply read_rhb_imm_codom. }
  now rewrite seq_false_l, union_false_r.
Qed.

Lemma read_rhb_codom :
    ⦗eq a⦘ ⨾ rhb_s ⊆ ∅₂.
Proof using INJ E_MAP IS_NACQ NIN CODOM_RPO RPO_MAP
            CODOM_SB_SL SB_SL_MAP RF_MAP CO_MAP RMW_MAP
            LABS IS_NREL WF_t WF_s.
  unfold rhb. rewrite ct_begin.
  sin_rewrite read_rhb_imm_codom.
  now rewrite seq_false_l.
Qed.

Lemma read_rhb_start :
    ⦗E_s \₁ eq a⦘ ⨾ rhb_s ⨾ ⦗E_s \₁ eq a⦘ ≡ rhb_s ⨾ ⦗E_s \₁ eq a⦘.
Proof using INJ E_MAP IS_NACQ IS_NREL NIN CODOM_RPO RPO_MAP
            CODOM_SB_SL SB_SL_MAP RF_MAP CO_MAP RMW_MAP
            LABS WF_t WF_s RFRE.
  split; [clear; basic_solver|].
  rewrite (wf_rhbE WF_s) at 1.
  rewrite set_union_minus
     with (s := E_s) (s' := eq a)
       at 1; [| rewrite E_MAP; basic_solver].
  rewrite id_union, seq_union_l.
  sin_rewrite read_rhb_codom.
  rewrite seq_false_l, union_false_r.
  basic_solver 11.
Qed.

Lemma read_rhb_sub :
  rhb_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rhb_t.
Proof using INJ E_MAP IS_NREL IS_NACQ NIN CODOM_RPO RPO_MAP
            CODOM_SB_SL SB_SL_MAP RF_MAP CO_MAP RMW_MAP
            LABS WF_t WF_s RFRE.
  rewrite <- read_rhb_start, <- restr_relE.
  unfold rhb.
  assert (UP : upward_closed
    (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)
    (E_s \₁ eq a)
  ).
  { unfold upward_closed.
    intros x y HREL YIN.
    assert (HREL' :
      ((sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)
        ⨾ ⦗E_s \₁ eq a⦘) x y
    ).
    { exists y. split; auto.
      red. auto. }
    apply read_rhb_imm_start in HREL'.
    forward apply HREL'. clear. basic_solver. }
  rewrite restr_rel_ct; auto.
  arewrite (
    sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t ≡
      restr_rel E_t (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)
  ).
  { rewrite restr_relE. apply dom_helper_3.
    arewrite (
      sb_t ∩ same_loc_t ⊆
        ⦗E_t⦘ ⨾ (sb_t ∩ same_loc_t) ⨾ ⦗E_t⦘
    ).
    { rewrite wf_sbE at 1.
      rewrite <- seq_eqv_inter_lr.
      rewrite <- seq_eqv_inter_ll.
      reflexivity. }
    rewrite wf_rpoE, (wf_swE WF_t).
    clear. basic_solver 11. }
  rewrite collect_rel_ct_inj; [| exact INJ].
  apply clos_trans_mori.
  arewrite (
    restr_rel (E_s \₁ eq a)
      (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⊆
        m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)
  ).
  { rewrite !collect_rel_union, !restr_union.
    rewrite !restr_relE.
    sin_rewrite RPO_MAP.
    sin_rewrite SB_SL_MAP.
    sin_rewrite read_sw_sub_helper.
    rewrite acts_set_helper.
    clear. basic_solver 11. }
  rewrite wf_sbE at 1.
  rewrite wf_rpoE at 1.
  rewrite (wf_swE WF_t) at 1.
  clear. basic_solver 11.
Qed.

End ConsistencyReadExtent.

End XmmCons.