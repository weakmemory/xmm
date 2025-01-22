Require Import Setoid Program.Basics.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel3 AuxInj.
Require Import Srf Rhb.
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
Variable a : actid.

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

Lemma read_fr_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    fr_s ⊆ m ↑ fr_t ∪ (srf_s ⨾ ⦗eq a⦘)⁻¹ ⨾ co_s.
Proof using.
    unfold fr. rewrite RF_MAP. rewrite transp_union.
    rewrite seq_union_l. rewrite CO_MAP. rewrite transp_seq, seqA.
    rewrite <- collect_rel_transp.
    assert (EQ : m ↑ (rf_t⁻¹ ⨾ co_t) ≡ m ↑ rf_t⁻¹ ⨾ m ↑ co_t).
    { eapply collect_rel_seq. assert (IN1 : codom_rel rf_t⁻¹ ⊆₁ E_t).
      { rewrite codom_transp. induction 1 as (y & COND). apply wf_rfE in COND; eauto.
        destruct COND as (x1 & COND & REST). apply COND. }
      assert (IN2 : dom_rel co_t ⊆₁ E_t).
      { induction 1 as (y & COND). apply wf_coE in COND; eauto.
        destruct COND as (x1 & COND & REST). apply COND. }
      rewrite IN1, IN2. basic_solver. }
    rewrite EQ; basic_solver.
Qed.

Lemma read_eco_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    eco_s ⊆ m ↑ eco_t ∪ srf_s ⨾ ⦗eq a⦘ ∪ co_s ⨾ (srf_s ⨾ ⦗eq a⦘) ∪
                fr_s ⨾ (srf_s ⨾ ⦗eq a⦘) ∪ (srf_s ⨾ ⦗eq a⦘)⁻¹ ⨾ co_s ⨾ rf_s^?.
Proof using.
    unfold eco. repeat rewrite collect_rel_union.
    repeat apply inclusion_union_l. rewrite RF_MAP.
    apply inclusion_union_l. 1, 2 : clear; basic_solver 21.
    { rewrite CO_MAP. case_refl _.
        { clear; basic_solver 21. }
        rewrite RF_MAP. rewrite seq_union_r.
        apply inclusion_union_l. 2 : clear; basic_solver 21.
        do 5 left. right. assert (EQ : m ↑ (co_t ⨾ rf_t) ≡ m ↑ co_t ⨾ m ↑ rf_t).
        { eapply collect_rel_seq. assert (IN1 : codom_rel co_t ⊆₁ E_t).
          { induction 1 as (x1 & COND). apply wf_coE in COND; eauto.
            destruct COND as (x2 & P1 & (x3 & P2 & (EQ & P3))); vauto. }
          assert (IN2 : dom_rel rf_t ⊆₁ E_t).
          { induction 1 as (x1 & COND). apply wf_rfE in COND; eauto.
            destruct COND as (x2 & P1 & P2); apply P1. }
          rewrite IN1, IN2. basic_solver. }
          apply symmetry in EQ. apply EQ in H.
          assert (IN : (m ↑ (co_t ⨾ rf_t)) x y -> (m ↑ (co_t ⨾ rf_t^?)) x y).
            { apply collect_rel_mori; eauto. basic_solver. }
          apply IN in H. basic_solver. }
    case_refl _.
    { unfold fr. rewrite CO_MAP. rewrite RF_MAP. rewrite transp_union.
      rewrite seq_union_l. apply inclusion_union_l.
      { rewrite <- collect_rel_transp. assert (EQ : m ↑ rf_t⁻¹ ⨾ m ↑ co_t ≡ m ↑ (rf_t⁻¹ ⨾ co_t)).
        { assert (IN1 : codom_rel rf_t⁻¹ ⊆₁ E_t).
          { rewrite codom_transp. induction 1 as (x0 & COND). apply wf_rfE in COND; eauto.
            destruct COND as (x2 & P1 & P2); apply P1. }
          assert (IN2 : dom_rel co_t ⊆₁ E_t).
          { induction 1 as (y & COND). apply wf_coE in COND; eauto.
            destruct COND as (x2 & P1 & P2); apply P1. }
          erewrite collect_rel_seq; eauto. rewrite IN1, IN2. basic_solver. }
        rewrite EQ. clear; basic_solver 21. }
      clear; basic_solver 12. }
    unfold fr. rewrite CO_MAP. rewrite RF_MAP.
    rewrite transp_union. rewrite seq_union_l.
    rewrite seq_union_l. apply inclusion_union_l. 2 : clear; basic_solver 21.
    rewrite seq_union_r. apply inclusion_union_l. 2 : clear; basic_solver 21.
    assert (EQ :  m ↑ ((rf_t⁻¹ ⨾ co_t) ⨾ rf_t) ≡ ((m ↑ rf_t)⁻¹ ⨾ m ↑ co_t) ⨾ m ↑ rf_t).
    { rewrite <- collect_rel_transp.
      assert (IN1 : codom_rel rf_t⁻¹ ⊆₁ E_t).
      { rewrite codom_transp. induction 1 as (y & COND). apply wf_rfE in COND; eauto.
        destruct COND as (x2 & P1 & P2); apply P1. }
      assert (IN2 : dom_rel co_t ⊆₁ E_t).
      { induction 1 as (y & COND). apply wf_coE in COND; eauto.
        destruct COND as (x2 & P1 & P2); apply P1. }
      assert (IN3 : dom_rel rf_t ⊆₁ E_t).
      { induction 1 as (y & COND). apply wf_rfE in COND; eauto.
        destruct COND as (x2 & P1 & P2); apply P1. }
      erewrite collect_rel_seq. erewrite collect_rel_seq. basic_solver.
      { rewrite IN1, IN2. basic_solver. }
      assert (COD_IN : codom_rel (rf_t⁻¹ ⨾ co_t) ⊆₁ E_t).
      { rewrite codom_seq. induction 1 as (y & COND). apply wf_coE in COND; eauto.
        destruct COND as (x2 & P1 & (x3 & P2 & (EQ & P3))); vauto. }
      rewrite COD_IN, IN3. basic_solver. }
    symmetry in EQ. rewrite EQ. clear; basic_solver 21.
Qed.

Lemma acts_set_helper (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    E_s \₁ eq a ≡₁ m ↑₁ E_t.
Proof using.
    rewrite E_MAP. rewrite set_minus_union_l.
    rewrite set_minusK. rewrite set_union_empty_r.
    apply set_minus_disjoint; eauto.
Qed.

Lemma read_codom_sw (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    codom_rel (⦗eq a⦘ ⨾ sw_s) ≡₁ ∅.
Proof using.
    assert (READ : ⦗eq a⦘ ≡ ⦗eq a⦘ ⨾ ⦗R_s⦘) by basic_solver.
    rewrite READ.
    assert (EMP : (⦗fun a0 : actid => R_s a0⦘ ⨾ sw_s) ≡ ∅₂).
    { unfold sw. unfold release. unfold rs. split; vauto.
      rewrite crE. rewrite !seqA. rewrite !seq_union_l.
      rewrite !seq_union_r. apply inclusion_union_l.
      { intros x y PATH.
        destruct PATH as (x0 & (EQ1 & C1) & (x1 & (EQ2 & C2) & (x2 & (EQ3 & C3)
            & (x3 & (EQ4 & C4) & (x4 & (EQ5 & C5) & P6))))). subst.
        unfold is_r in C1. unfold is_w in C5.
        desf. }
      rewrite seqA. intros x y PATH.
      destruct PATH as (x0 & (EQ1 & C1) & (x1 & (EQ2 & C2) & (x2 & (EQ3 & C3)
            & (x3 & (EQ4 & C4) & P5)))). subst.
        unfold is_r in C1. unfold is_f in C3.
        desf. }
    rewrite seqA. rewrite EMP. clear; basic_solver.
Qed.

Lemma read_sw_helper_rf_rmw (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
  rf_s ⨾ rmw_s ⊆ m ↑ (rf_t ⨾ rmw_t).
Proof using.
  rewrite RF_MAP, RMW_MAP. rewrite seq_union_l.
  apply inclusion_union_l.
  { rewrite collect_rel_seq; vauto.
    assert (IN1 : codom_rel rf_t ⊆₁ E_t).
    { rewrite wf_rfE; eauto. basic_solver. }
    assert (IN2 : dom_rel rmw_t ⊆₁ E_t).
    { rewrite wf_rmwE; eauto. basic_solver. }
    rewrite IN1, IN2. basic_solver. }
  rewrite seqA. rewrite wf_rmwE; eauto.
  rewrite collect_rel_seqi. intros x y PATH.
  destruct PATH as (x0 & (P1 & (x1 & (P2 & (x2
            & (P3 & (x3 & (x4 & P5)))))))).
  destruct P2. subst. exfalso.
  destruct NIN with x1; eauto.
  destruct P3 as (x1' & x2' & ((EQ & INE) & MAP1 & MAP2)).
  subst. unfold set_collect. exists x2'. split; vauto.
Qed.

Lemma read_sw_helper_release (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
  ⦗E_s \₁ eq a⦘ ⨾ release_s ⊆
      m ↑ (⦗E_t⦘ ⨾ release_t).
Proof using.
  assert (MAPEQ : E_s \₁ eq a ≡₁ m ↑₁ E_t) by now apply acts_set_helper.
  unfold release. rewrite !crE. rewrite !seq_union_l.
  rewrite !seq_union_r. rewrite collect_rel_union.
  apply union_mori.
  { rels. unfold rs.
    rels. seq_rewrite <- !id_inter.
    intros x y (x' & ((EQ & DOM) & HREL)).
    subst x'.
    assert (XIN : (E_s \₁ eq a) x) by apply DOM.
    assert (YIN : (E_s \₁ eq a) y).
    { apply rtE in HREL. destruct HREL as [EQ | PATH].
      { destruct EQ. subst; eauto. }
      apply ct_end in PATH. destruct PATH as (x0 & (P1 & (x1 & (P2 & P3)))).
      apply wf_rmwD in P3; eauto. destruct P3 as (x2 & (P4 & x3 & (P5 & (P6 & P7)))).
      subst. apply wf_rmwE in P5; eauto. destruct P5 as (x3 & (P8 & (x4 & (P9 & P10)))).
      destruct P10 as (EQ & INE); vauto. unfold set_minus. split; vauto.
      unfold is_w in P7. unfold is_r in IS_R. intros HH. desf. }
    apply MAPEQ in XIN. apply MAPEQ in YIN.
    destruct XIN as (x' & XIN & XEQ), YIN as (y' & YIN & YEQ).
    exists x', y'. splits; ins. split with x'; split.
    { unfolder. unfolder in DOM. desf.
      unfold is_w, is_rel, is_rlx, mod in *.
      rewrite <- LABS with x'; eauto. }
    assert (HREL' : singl_rel x y ⊆ (rf_s ⨾ rmw_s)＊).
    { intros x0 y0 PATH. destruct PATH; vauto. }
    rewrite RF_MAP, seq_union_l in HREL'.
    assert (EMP : (srf_s ⨾ ⦗eq a⦘) ⨾ rmw_s ≡ ∅₂).
    { rewrite seqA. rewrite RMW_MAP.
      rewrite wf_rmwE; eauto. split; [|basic_solver].
      rewrite collect_rel_seqi. intros x0 y0 PATH.
      destruct PATH as (x1 & (P1 & (x2 & ((EQ & EQA) & (x3
              & (P3 & (x4 & (x5 & P4)))))))).
      symmetry in MAPEQ.
      destruct P4 as ((x5' & P4 & (EQ' & EIN)) & MAP1 & MAP2).
      subst. destruct MAPEQ as (IN1 & IN2). destruct IN1 with x2; eauto.
      destruct P3 as (x2' & x4' & INE & MAP1 & MAP2).
      unfold set_collect. exists x2'; split; vauto.
      destruct INE as (EQ & INE); vauto. }
    rewrite EMP in HREL'. rewrite union_false_r in HREL'.
    rewrite RMW_MAP in HREL'.
    rewrite <- collect_rel_seq in HREL'.
    2: { assert (IN1 : codom_rel rf_t ⊆₁ E_t).
        { rewrite wf_rfE; eauto. basic_solver. }
        assert (IN2 : dom_rel rmw_t ⊆₁ E_t).
        { rewrite wf_rmwE; eauto. basic_solver. }
        rewrite IN1, IN2. basic_solver. }
    apply rtE in HREL. destruct HREL as [EQ | PATH].
    { destruct EQ. subst.
      assert (EQ : x' = y').
      { apply INJ; vauto. }
      subst. apply rtE; left. clear; basic_solver. }
    apply rtE. right.
    assert (TREQ : (rf_s ⨾ rmw_s)⁺ ⊆ (m ↑ (rf_t ⨾ rmw_t))⁺).
    { apply clos_trans_mori; apply read_sw_helper_rf_rmw; eauto. }
    apply TREQ in PATH.
    assert (REST : (rf_t ⨾ rmw_t) ≡ restr_rel E_t (rf_t ⨾ rmw_t)).
    { rewrite restr_relE. rewrite wf_rfE, wf_rmwE; eauto.
      clear; basic_solver 21. }
    assert (TREQ' : (m ↑ (rf_t ⨾ rmw_t))⁺ ≡ (m ↑ restr_rel E_t (rf_t ⨾ rmw_t))⁺).
    { split; apply clos_trans_mori; rewrite <- REST; vauto. }
    apply TREQ' in PATH. apply collect_rel_ct_inj in PATH; vauto.
    unfold collect_rel in PATH. destruct PATH as (x0 & y0 & (PATH & MAP1 & MAP2)).
    assert (TREQ'' : (restr_rel E_t (rf_t ⨾ rmw_t))⁺ ⊆ (rf_t ⨾ rmw_t)⁺).
    { apply clos_trans_mori; basic_solver. }
    apply TREQ'' in PATH.
    assert (X0IN : E_t x0).
    { apply ct_begin in PATH.
      destruct PATH as (x1 & (x2 & (P1 & P2)) & P3).
      apply wf_rfE in P1; vauto.
      destruct P1 as (x3 & (EQ & INE) & P1); vauto. }
    assert (Y0IN : E_t y0).
    { apply ct_end in PATH.
      destruct PATH as (x1 & P1 & (x2 & (P2 & P3))).
      apply wf_rmwE in P3; vauto.
      destruct P3 as (x3 & P3 & (x4 & P4 & (EQ & INE))); vauto. }
    assert (EQXX : x0 = x') by now apply INJ.
    assert (EQYY : y0 = y') by now apply INJ.
    vauto. }
  assert (sb_t ∩ same_loc_t ≡ ⦗E_t⦘ ⨾ sb_t ∩ same_loc_t ⨾ ⦗E_t⦘) as EAA.
  { split; [|clear; basic_solver 10].
    rewrite wf_sbE at 1. clear; basic_solver 10. }
  assert (sb_s ∩ same_loc_s ≡ ⦗E_s⦘ ⨾ sb_s ∩ same_loc_s ⨾ ⦗E_s⦘) as EAA'.
  { split; [|clear; basic_solver 10].
    rewrite wf_sbE at 1. clear; basic_solver 10. }
  unfold rs. rels. rewrite !seqA.
  arewrite ((⦗Rel_s⦘ ⨾ ⦗F_s⦘ ⨾ sb_s ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ ⦗W_s⦘)
          ⊆ ⦗Rel_s⦘ ⨾ ⦗F_s⦘ ⨾ rpo_s ⨾ ⦗W_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘).
    { unfold rpo; unfold rpo_imm. rewrite <- ct_step. clear; basic_solver 21. }
  rewrite wf_rpoE; eauto. rewrite !seqA.
  arewrite (⦗E_s⦘ ⨾ ⦗W_s⦘ ⊆ ⦗E_s \₁ eq a⦘ ⨾ ⦗W_s⦘).
    { unfold set_minus. intros x y COND.
      destruct COND as (x' & (EQ1 & INE) & (EQ2 & ISW)).
      subst. unfolder. splits; vauto.
      intros F. unfold is_w, is_r in *.
      basic_solver. }
  do 3 rewrite <- seqA.
  rewrite <- seqA with (r3 := ⦗W_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ (rf_s ⨾ rmw_s)＊).
  rewrite RPO_MAP. rewrite !seqA.
  intros x y PATH. destruct PATH as (x0 & ((EQ1 & C1) & (x1 & ((EQ2 & C2) & (x2
          & ((EQ3 & C3) & (x3 & (P4 & (x4 & (P5 & (x5 & ((EQ6 & C6) & x6 & ((EQ7 & P7) & P8))))))))))))).
  subst. apply MAPEQ in C1. destruct C1 as (x2' & INE & MAP).
  unfold collect_rel. apply rtE in P8. destruct P8 as [EQ | PATH].
  { destruct EQ as (EQ & T). destruct P5 as (x3' & x6' & P5 & M1 & M2).
    exists x2', x6'. splits; vauto. unfold seq.
    exists x2'. splits; vauto.
    exists x2'. splits.
    { apply LABS in INE. unfold compose in INE.
      red. splits; vauto. unfold is_rel in *.
      unfold mod in *. rewrite <- INE; vauto. }
    exists x2'. splits.
    { apply LABS in INE. unfold compose in INE.
      red. splits; vauto. unfold is_f in *.
      rewrite <- INE; vauto. }
    exists x6'. splits.
    { destruct P4 as (MEQ & INE').
      apply INJ in MEQ; vauto.
      { apply rpo_in_sb in P5; vauto. }
      apply wf_rpoE in P5; vauto.
      destruct P5 as (x' & INE'' & P'); apply INE''. }
    assert (XE : E_t x6').
    { apply wf_rpoE in P5; vauto.
      destruct P5 as (x4' & (EQ1 & INE1) & (x5'
              & P' & (EQ2 & INE2))); vauto. }
    exists x6'. splits.
    { red; splits; vauto.
      apply LABS in XE. unfold compose in XE.
      unfold is_rlx in *. unfold mod in *.
      rewrite <- XE; vauto. }
    exists x6'. splits.
    { red; splits; vauto.
      apply LABS in XE. unfold compose in XE.
      unfold is_w in *. rewrite <- XE; vauto. }
    apply rtE. left. clear; basic_solver. }
  assert (TREQ : (rf_s ⨾ rmw_s)⁺ ⊆ (m ↑ (rf_t ⨾ rmw_t))⁺).
  { apply clos_trans_mori; apply read_sw_helper_rf_rmw; eauto. }
  apply TREQ in PATH.
  assert (REST : (rf_t ⨾ rmw_t) ≡ restr_rel E_t (rf_t ⨾ rmw_t)).
  { rewrite restr_relE. rewrite wf_rfE, wf_rmwE; eauto.
    clear; basic_solver 21. }
  assert (TREQ' : (m ↑ (rf_t ⨾ rmw_t))⁺ ≡ (m ↑ restr_rel E_t (rf_t ⨾ rmw_t))⁺).
  { split; apply clos_trans_mori; rewrite <- REST; vauto. }
  apply TREQ' in PATH. apply collect_rel_ct_inj in PATH; vauto.
  unfold collect_rel in PATH. destruct PATH as (x0 & y0 & (COND & M1 & M2)).
  assert (TREQ'' : (restr_rel E_t (rf_t ⨾ rmw_t))⁺ ⊆ (rf_t ⨾ rmw_t)⁺).
  { apply clos_trans_mori; basic_solver. }
  apply TREQ'' in COND.
  exists x2', y0. splits; vauto.
  unfold seq.
  exists x2'. splits; vauto.
  exists x2'. splits.
  { apply LABS in INE. unfold compose in INE.
    red. splits; vauto. unfold is_rel in *.
    unfold mod in *. rewrite <- INE; vauto. }
  exists x2'. splits.
  { apply LABS in INE. unfold compose in INE.
    red. splits; vauto. unfold is_f in *.
    rewrite <- INE; vauto. }
  assert (XE : E_t x0).
  { apply ct_begin in COND.
    destruct COND as (x1 & (x1' & P1 & P2) & P3).
    apply wf_rfE in P1; vauto.
    destruct P1 as (x'' & INE' & REST'); apply INE'. }
  exists x0. splits.
  { destruct P5 as (x3' & x0' & (COND' & M1' & M2')).
    apply rpo_in_sb in COND'; vauto.
    apply INJ in M2'; vauto.
    { destruct P4 as (MEQ & INE').
      apply INJ in MEQ; vauto.
      apply wf_sbE in COND'; vauto.
      destruct COND' as (x4' & EQ' & P').
      apply EQ'. }
    destruct COND' as (x1' & C1' & (x4' & C2' & (EQ' & INE'))); vauto. }
  destruct P5 as (x3' & x0' & P5 & M1 & M2).
  exists x0. splits.
  { red; splits; vauto.
    apply LABS in XE. unfold compose in XE.
    unfold is_rlx in *. unfold mod in *.
    rewrite <- XE; vauto. }
  exists x0. splits.
  { red; splits; vauto.
    apply LABS in XE. unfold compose in XE.
    unfold is_w in *. rewrite <- XE; vauto. }
  apply rtE. right. basic_solver.
Qed.

Lemma read_sw_helper_rf (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    rf_s ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ (sb_s ⨾ ⦗F_s⦘)^? ⨾ ⦗Acq_s⦘ ⨾ ⦗E_s \₁ eq a⦘
    ⊆ m ↑ (rf_t ⨾ ⦗fun a0 : actid => is_rlx lab_t a0⦘⨾ (sb_t ⨾ ⦗F_t⦘)^? ⨾ ⦗Acq_t⦘).
Proof using.
    assert (MAPEQ : E_s \₁ eq a ≡₁ m ↑₁ E_t) by now apply acts_set_helper.
    rewrite !crE. rewrite !seq_union_l.
    rewrite !seq_union_r. rewrite collect_rel_union.
    apply union_mori.
    { rewrite RF_MAP. rewrite seq_union_l. apply inclusion_union_l.
      { rels. rewrite MAPEQ. intros x y PATH.
        destruct PATH as (x0 & (PATH & (x1 & ((EQ1 & C1) & (x2 & ((EQ2 & C2) & (EQ3 & C3))))))).
        subst; unfolder.
        destruct PATH as (x' & y' & PATH & M1 & M2).
        exists x', y'. splits; vauto.
        all : unfold is_acq, is_rlx, mod in *.
        all : rewrite <- LABS with y'; splits; eauto.
        all : apply wf_rfE in PATH; eauto.
        all : destruct PATH as (x2 & (INE & (x3 & (P1 & P2)))).
        all : destruct P2; vauto. }
      rewrite seqA. clear; basic_solver 21. }
    rewrite RF_MAP. rewrite seq_union_l. apply inclusion_union_l.
    { rewrite !seqA.
      arewrite (m ↑ rf_t ⊆ m ↑ rf_t ⨾ ⦗R_s⦘).
      { rewrite wf_rfD; eauto. intros x y PATH. unfold collect_rel in PATH.
        destruct PATH as (x' & y' & (PATH & M1 & M2)).
        destruct PATH as (x1' & (EQ1 & C1) & (x2' & (PATH & (EQ2 & C2)))); subst.
        unfolder. splits.
        { exists x1', y'. splits; vauto. }
        specialize (LABS y'). unfold compose in LABS.
        apply wf_rfE in PATH; vauto.
        destruct PATH as (x2' & (P1 & (x3' & (P2 & P3)))).
        destruct P3 as (EQ & P3); subst. apply LABS in P3.
        unfold is_r in *. rewrite P3; vauto. }
      arewrite ((⦗R_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ sb_s ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘)
              ⊆ ⦗R_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ rpo_s ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘).
        { unfold rpo; unfold rpo_imm. rewrite <- ct_step. clear; basic_solver 21. }
      arewrite (rpo_s ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘ ⨾ ⦗E_s \₁ eq a⦘
                ⊆ rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘) by basic_solver.
      do 2 rewrite <- seqA. rewrite <- seqA with (r3 := ⦗F_s⦘ ⨾ ⦗Acq_s⦘).
      rewrite RPO_MAP. rewrite !seqA.
      intros x y PATH. unfold seq at 1 in PATH.
      destruct PATH as (x0 & P0 & (x1 & (EQ1 & C1) & x2 & (EQ2 & C2) & (x3
            & P3 & (x4 & (EQ4 & C4) & (EQ & P5))))); subst.
      unfold collect_rel in P0, P3.
      destruct P0 as (x' & x2' & (P0 & M1 & M2)); subst.
      destruct P3 as (x2'' & y' & (P2 & M3 & M4)); subst.
      unfold collect_rel. exists x', y'. splits; vauto.
      unfold seq at 1. exists x2'. splits; vauto.
      unfold seq. exists x2'.
      assert (ZE : E_t x2').
      { apply wf_rfE in P0; vauto.
        destruct P0 as (x0' & (INE1 & (x1' & (P0 & INE2)))).
        destruct INE2; vauto. }
      assert (ZEQ : x2'' = x2').
      { apply INJ; vauto.
        apply wf_rpoE in P2; vauto.
        destruct P2 as (x3' & (INE1 & (x4' & (P2 & INE2)))).
        destruct INE1; vauto. }
      subst. splits; vauto.
      { red. splits; vauto.
        apply LABS in ZE. unfold compose in ZE.
        unfold is_rlx in *. unfold mod in *.
        rewrite <- ZE; vauto. }
      exists y'. splits; vauto.
      { apply rpo_in_sb in P2; vauto. }
      exists y'.
      assert (EY : E_t y').
      { apply wf_rpoE in P2; vauto.
        destruct P2 as (x3' & (INE1 & (x4' & (P2 & INE2)))).
        destruct INE2; vauto. }
      splits; vauto.
      { apply LABS in EY. unfold compose in EY.
        unfold is_f in *. rewrite EY in C4; vauto. }
      apply LABS in EY. unfold compose in EY.
      unfold is_acq in *. unfold mod in *.
      rewrite EY in P5; vauto. }
    rewrite !seqA.
    arewrite (⦗eq a⦘ ⊆ ⦗eq a⦘ ⨾ ⦗fun a0 : actid => is_r lab_s a0⦘).
    { unfold is_r in IS_R. basic_solver. }
    arewrite ((⦗R_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ sb_s ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘) ⊆ rpo_s).
    { unfold rpo; unfold rpo_imm. rewrite <- ct_step. clear; basic_solver 21. }
    destruct CODOM_RPO. unfold codom_rel in H.
    assert (EMP : ⦗eq a⦘ ⨾ rpo_s ≡ ∅₂).
    { split; [|clear; basic_solver].
      intros x y HH. destruct H with y; exists x; vauto. }
    destruct EMP. rewrite <- seqA with (r3 := ⦗E_s \₁ eq a⦘).
    rewrite H1. clear; basic_solver.
Qed.

Lemma read_sw_sub_helper (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    sw_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ sw_t.
Proof using.
  assert (MAPEQ : E_s \₁ eq a ≡₁ m ↑₁ E_t) by now apply acts_set_helper.
  assert (START : sw_s ≡ ⦗E_s \₁ eq a⦘ ⨾ sw_s).
  { unfold set_minus. split; [|basic_solver].
    intros x y PATH. unfold seq. exists x. split; vauto.
    split; vauto. split.
    { apply wf_swE in PATH; eauto. destruct PATH as (x' & INE & REST).
      apply INE. }
    assert (CODOM : codom_rel (⦗eq a⦘ ⨾ sw_s) ≡₁ ∅).
    { apply read_codom_sw with (m := m); eauto. }
    intros F. subst.
    assert (VERT : eq y ⊆₁ codom_rel (⦗eq x⦘ ⨾ sw_s)).
    { intros z EQ. subst. basic_solver 12. }
    destruct CODOM as (IN1 & IN2). rewrite <- VERT in IN1.
    destruct IN1 with (x := y); vauto. }
  rewrite START. rewrite seqA.
  unfold sw. rewrite !seqA.
  rewrite <- seqA.
  rewrite read_sw_helper_release; eauto.
  rewrite read_sw_helper_rf; eauto.
  rewrite <- collect_rel_seq; vauto.
  2 : { assert (IN1 : codom_rel (⦗E_t⦘ ⨾ release_t) ⊆₁ E_t).
        { rewrite wf_releaseE; vauto. rewrite seq_union_r. basic_solver. }
        assert (IN2 : dom_rel (rf_t ⨾ ⦗fun a0 : actid => is_rlx lab_t a0⦘ ⨾
            (sb_t ⨾ ⦗fun a0 : actid => F_t a0⦘)^? ⨾ ⦗fun a0 : actid => Acq_t a0⦘) ⊆₁ E_t).
        { induction 1 as (x0 & COND). destruct COND as (x1 & P1 & P2).
          apply wf_rfE in P1; eauto.
          destruct P1 as (x2 & INE & REST).
          apply INE. }
        rewrite IN1, IN2. basic_solver. }
  clear; basic_solver 21.
Qed.

Lemma read_sw_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    sw_s ⊆ m ↑ sw_t.
Proof using.
    rewrite <- read_sw_sub_helper; eauto.
    arewrite (sw_s ⊆ sw_s ⨾ ⦗E_s⦘) at 1.
    { rewrite wf_swE; eauto. basic_solver. }
    rewrite E_MAP at 1. rewrite id_union.
    rewrite seq_union_r.
    apply inclusion_union_l.
    { hahn_frame. rewrite E_MAP.
      apply eqv_rel_mori. rewrite set_minus_union_l.
      arewrite (m ↑₁ E_t ⊆₁ m ↑₁ E_t \₁ eq a).
      { unfold set_minus.
        intros x SET. split; vauto.
        intros EQ. destruct NIN with x; vauto. }
      basic_solver 12. }
    arewrite (sw_s ⊆ sw_s ⨾ ⦗Acq_s⦘).
    { rewrite wf_swD; eauto. basic_solver. }
    unfold is_acq in *. basic_solver 21.
Qed.

Lemma codom_ct_alt (A : Type) (r r' : relation A)
        (EMP : codom_rel (r ⨾ r') ≡₁ ∅) :
    codom_rel (r ⨾ r'⁺) ≡₁ ∅.
Proof using.
    split; try basic_solver. intros x H. induction H.
    destruct H. destruct H. induction H0.
        { apply EMP. basic_solver. }
    apply EMP in IHclos_trans1; eauto.
    apply EMP in IHclos_trans1.
    basic_solver.
Qed.

Lemma empty_codom_irr (A : Type) (r r' : relation A)
        (EMP : codom_rel r ≡₁ ∅) :
    irreflexive (r ⨾ r').
Proof using.
    apply empty_irr. split; try basic_solver.
    intros x y H. destruct H. destruct H. assert (Q : ∅ x0).
    { apply EMP. basic_solver. }
    destruct Q.
Qed.

Lemma empty_seq_codom (A : Type) (r r' : relation A)
        (EMP : codom_rel r ≡₁ ∅) :
    codom_rel (r ⨾ r') ≡₁ ∅.
Proof using.
    split; try basic_solver. intros x H. induction H.
    destruct H. destruct H. destruct EMP.
    assert (IN : codom_rel r x1).
    { exists x0; eauto. }
    assert (F : ∅ x1).
    { apply H1 in IN; eauto. }
    basic_solver.
Qed.

Lemma read_rhb_codom (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅.
Proof using.
    unfold rhb. rewrite ct_begin. rewrite <- seqA. rewrite !seq_union_r.
    rewrite !seq_union_l. rewrite !codom_union.
    assert (EMP1 : codom_rel ((⦗eq a⦘ ⨾ rpo_s) ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)＊) ≡₁ ∅).
    { apply empty_seq_codom; eauto. }
    assert (EMP2 : codom_rel (⦗eq a⦘ ⨾ sw_s) ≡₁ ∅).
    { rewrite wf_swD; eauto. assert (READ : ⦗eq a⦘ ≡ ⦗eq a⦘ ⨾ ⦗R_s⦘).
      { basic_solver. }
      rewrite READ. rewrite seqA.
      assert (F : ⦗fun a0 : actid => R_s a0⦘
          ⨾ ⦗((fun a0 : actid => is_f lab_s a0) ∪₁ (fun a0 : actid => W_s a0))
            ∩₁ (fun a0 : actid => is_rel lab_s a0)⦘ ≡ ∅₂).
      { rewrite seq_eqv. rewrite set_inter_union_l. rewrite set_inter_union_r.
        rewrite <- set_interA. rewrite <- set_interA.
        unfold is_f, is_w, is_r. basic_solver. }
      rewrite <- seqA. rewrite <- seqA. apply empty_seq_codom.
      split; try basic_solver. rewrite READ. rewrite seqA.
      rewrite codom_seq. rewrite F. apply codom_empty. }
    assert (EMP3 : codom_rel ((⦗eq a⦘ ⨾ sw_s) ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)＊) ≡₁ ∅).
    { apply empty_seq_codom; eauto. }
    assert (EMP4 : codom_rel (⦗eq a⦘ ⨾ sb_s ∩ same_loc_s) ≡₁ ∅) by vauto.
    assert (EMP5 : codom_rel ((⦗eq a⦘ ⨾ sb_s ∩ same_loc_s) ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)＊) ≡₁ ∅).
    { apply empty_seq_codom; eauto. }
    rewrite EMP1, EMP3, EMP5. clear; basic_solver.
Qed.

Lemma read_rhb_start (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    ⦗E_s \₁ eq a⦘ ⨾ rhb_s ⨾ ⦗E_s \₁ eq a⦘ ≡ rhb_s ⨾ ⦗E_s \₁ eq a⦘.
Proof using.
    split; [clear; basic_solver|].
    hahn_frame_r. unfold rhb. rewrite ct_begin. hahn_frame_r.
    rewrite !seq_union_r. apply union_mori.
    { apply union_mori.
      { intros x y PATH. unfold seq. exists x. split; vauto.
        red; split; vauto. assert (PATH' : (sb_s ∩ same_loc_s) x y) by apply PATH.
        destruct PATH as (P1 & P2). apply wf_sbE in P1.
        destruct P1 as (x' & (EQ & INE) & REST); subst.
        unfold set_minus; split; vauto.
        intros F; subst. unfold codom_rel in CODOM_SB_SL.
        destruct CODOM_SB_SL as (IN1 & IN2). destruct IN1 with y.
        exists x'. split with x'. split; vauto. }
      intros x y PATH. unfold seq. exists x. split; vauto.
      red; split; vauto. assert (PATH' : (rpo_s) x y) by apply PATH.
      apply wf_rpoE in PATH; vauto.
      destruct PATH as (x' & (EQ & INE) & REST); subst.
      unfold set_minus; split; vauto.
      intros F; subst. unfold codom_rel in CODOM_RPO.
      destruct CODOM_RPO. destruct H with y.
      exists x'. split with x'. split; vauto. }
    intros x y PATH. unfold seq. exists x. split; vauto.
    red; split; vauto. assert (PATH' : (sw_s) x y) by apply PATH.
    apply wf_swE in PATH; vauto.
    destruct PATH as (x0 & (EQ & INE) & REST); subst.
    unfold set_minus; split; vauto.
    intros F; subst. apply wf_swD in PATH'; vauto.
    destruct PATH' as (x1 & COND' & REST').
    destruct COND' as (EQ & COND'); subst.
    destruct COND' as (P1 & P2).
    destruct P1 as [F | W].
    { unfold is_f, is_w, is_r in *. desf. }
    unfold is_f, is_w, is_r in *. desf.
Qed.

Lemma read_rhb_imm_start (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    ⦗E_s \₁ eq a⦘ ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ≡
                    (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s).
Proof using.
    split; [clear; basic_solver|]. unfold rhb.
    rewrite !seq_union_r. apply union_mori.
    { apply union_mori.
      { intros x y PATH. unfold seq. exists x. split; vauto.
        red; split; vauto. assert (PATH' : (sb_s ∩ same_loc_s) x y) by apply PATH.
        destruct PATH as (P1 & P2). apply wf_sbE in P1.
        destruct P1 as (x' & (EQ & INE) & REST); subst.
        unfold set_minus; split; vauto.
        intros F; subst. unfold codom_rel in CODOM_SB_SL.
        destruct CODOM_SB_SL as (IN1 & IN2). destruct IN1 with y.
        exists x'. split with x'. split; vauto. }
      intros x y PATH. unfold seq. exists x. split; vauto.
      red; split; vauto. assert (PATH' : (rpo_s) x y) by apply PATH.
      apply wf_rpoE in PATH; vauto.
      destruct PATH as (x' & (EQ & INE) & REST); subst.
      unfold set_minus; split; vauto.
      intros F; subst. unfold codom_rel in CODOM_RPO.
      destruct CODOM_RPO. destruct H with y.
      exists x'. split with x'. split; vauto. }
    intros x y PATH. unfold seq. exists x. split; vauto.
    red; split; vauto. assert (PATH' : (sw_s) x y) by apply PATH.
    apply wf_swE in PATH; vauto.
    destruct PATH as (x0 & (EQ & INE) & REST); subst.
    unfold set_minus; split; vauto.
    intros F; subst. apply wf_swD in PATH'; vauto.
    destruct PATH' as (x1 & COND' & REST').
    destruct COND' as (EQ & COND'); subst.
    destruct COND' as (P1 & P2).
    destruct P1 as [F | W].
    { unfold is_f, is_w, is_r in *. desf. }
    unfold is_f, is_w, is_r in *. desf.
Qed.

Lemma rhb_fin (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t).
Proof using.
    rewrite !seq_union_l.
    rewrite !collect_rel_union.
    apply union_mori.
    { apply union_mori.
      { rewrite SB_SL_MAP. clear; basic_solver. }
      rewrite RPO_MAP. clear; basic_solver. }
    rewrite read_sw_sub_helper; eauto.
    clear; basic_solver.
Qed.

Lemma read_rhb_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    rhb_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rhb_t.
Proof using.
    unfold rhb.
    assert (IND1 : (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘
                  ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺).
    { rewrite rhb_fin; vauto. intros x y PATH. unfold collect_rel in *.
      destruct PATH as (x' & y' & (PATH & M1 & M2)). exists x', y'. splits; vauto. }
    assert (IND2 : m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺ ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘
                  ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺).
    { assert (TRIN : m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺ ⨾ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺
              ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺).
      { intros x y PATH. destruct PATH as (x0 & P1 & P2).
        unfold collect_rel in P1, P2. unfold collect_rel.
        destruct P1 as (x' & x0' & (P1 & M1 & M2)).
        destruct P2 as (x0'' & y' & (P2 & M3 & M4)).
        exists x', y'. splits; vauto.
        assert (EQ : x0'' = x0').
        { apply INJ; vauto.
          { apply ct_begin in P2.
            destruct P2 as (x1 & P2 & P3).
            apply wf_rhb_immE in P2; vauto.
            destruct P2 as (x2 & INE & REST).
            apply INE. }
          apply ct_end in P1.
          destruct P1 as (x1 & P1 & P1').
          apply wf_rhb_immE in P1'; vauto.
          destruct P1' as (x2 & P3 & (x3 & P4 & (EQ & P5))); vauto. }
        subst. apply ct_ct.
        unfold seq. exists x0'. splits; vauto. }
      rewrite <- TRIN at 2. apply seq_mori; vauto. }
    assert (IND3 : ((sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘)⁺
                  ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺).
    { apply inclusion_t_ind_right; vauto. }
    assert (IND4 : (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)⁺ ⨾ ⦗E_s \₁ eq a⦘ ⊆
                  ((sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘)⁺).
    { induction 1 as (x0 & (P1 & P2)). destruct P2 as (EQ & COND); subst.
      induction P1 as [x y STT | x].
      { apply ct_step. unfold seq. exists y. splits; vauto. }
      apply ct_begin in P1_2.
      destruct P1_2 as (x0 & P1 & P2).
      eapply read_rhb_imm_start in P1; vauto.
      destruct P1 as (x1 & (EQ' & COND') & P1); subst.
      apply IHP1_1 in COND'.
      apply IHP1_2 in COND.
      apply ct_ct. unfold seq. exists x1. splits; vauto. }
    rewrite IND4; vauto.
Qed.

Lemma read_extent (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
        (IS_ACQ : ~(is_acq lab_s a))
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    WCore.is_cons G_s.
Proof using.
    assert (MAPEQ : E_s \₁ eq a ≡₁ m ↑₁ E_t).
    { apply acts_set_helper; eauto; basic_solver. }
    constructor.
    { case_refl _.
        { rewrite hb_helper; eauto. rewrite irreflexive_union. split.
          { apply sb_irr; eauto. }
          intros x PATH. destruct classic with (P := (E_s \₁ eq a) x) as [EQ | EQ].
          { assert (VERT : (rhb_s ⨾ ⦗E_s \₁ eq a⦘) x x).
            { do 2 unfold seq. exists x; split; vauto. }
            assert (VERT' : (m ↑ rhb_t) x x).
            { apply read_rhb_sub; eauto. }
            assert (IRR : irreflexive rhb_t).
            { apply irreflexive_inclusion with (r' := hb_t); eauto.
              apply rhb_in_hb; eauto. destruct CONS. apply hb_irr; eauto. }
            assert (REST : (rhb_t) ≡ restr_rel E_t (rhb_t)).
            { rewrite restr_relE. rewrite wf_rhbE; eauto.
              clear; basic_solver 21. }
            assert (IRR' : irreflexive (restr_rel E_t (rhb_t))).
            { rewrite <- REST. apply IRR. }
            assert (IRR'' : irreflexive (m ↑ restr_rel E_t rhb_t)).
            { apply collect_rel_irr_inj; eauto. }
            rewrite <- REST in IRR''. basic_solver. }
          assert (EQA : eq a x).
          { assert (ALTNIN : ~ (m ↑₁ E_t) x).
            { intros NEG. apply acts_set_helper in NEG; eauto. }
            unfold set_minus in EQ. apply not_and_or in EQ.
            destruct EQ as [NOTIN | NEQ].
            { assert (G : rhb_s ≡ ⦗E_s⦘ ⨾ rhb_s ⨾ ⦗E_s⦘).
              { rewrite wf_rhbE; eauto. clear; basic_solver. }
              apply G in PATH. exfalso. apply NOTIN.
              destruct PATH as (x' & INE & REST); apply INE. }
            unfold not in NEQ. destruct classic with (P := eq a x) as [EQ' | EQ'].
            { basic_solver. }
            exfalso. apply NEQ. basic_solver. }
          rewrite <- EQA in EQ. destruct read_rhb_codom with (m := m) as (IN1 & IN2); eauto.
          unfold codom_rel in IN1. specialize (IN1 a).
          apply IN1. exists a. basic_solver. }
        apply rhb_eco_irr_equiv; eauto. rewrite read_eco_sub; eauto.
        repeat rewrite seq_union_r. repeat rewrite irreflexive_union; splits.
        { assert (MAPPING : m ↑ eco_t ≡ ⦗E_s \₁ eq a⦘ ⨾ m ↑ eco_t).
          { rewrite acts_set_helper; eauto.
            rewrite <- collect_rel_eqv. rewrite <- collect_rel_seq.
            { assert (EQ : eco_t ≡ ⦗E_t⦘ ⨾ eco_t).
              { rewrite wf_ecoE; eauto. basic_solver. }
              rewrite <- EQ. basic_solver. }
            assert (IN1 : codom_rel ⦗E_t⦘ ⊆₁ E_t).
            { induction 1; eauto.
              destruct H. destruct H; eauto. }
            assert (IN2 : dom_rel eco_t ⊆₁ E_t).
            { induction 1 as (y & COND). apply wf_ecoE in COND; eauto.
              destruct COND as (x' & INE & REST); apply INE. }
            rewrite IN1, IN2. rewrite set_unionK. basic_solver. }
          rewrite MAPPING. apply irreflexive_inclusion with (r' := m ↑ rhb_t ⨾ m ↑ eco_t); eauto.
          { rewrite <- seqA. rewrite read_rhb_sub; eauto; basic_solver. }
          rewrite <- collect_rel_seq.
          2 : { assert (IN1 : codom_rel rhb_t ⊆₁ E_t).
                { induction 1 as (y & COND). apply wf_rhbE in COND; eauto.
                  destruct COND as (x0 & INE1 & (x2 & COND & (EQ & INE2))); vauto. }
                assert (IN2 : dom_rel eco_t ⊆₁ E_t).
                { induction 1 as (y & COND). apply wf_ecoE in COND; eauto.
                  destruct COND as (x0 & INE1 & REST); apply INE1. }
                rewrite IN1, IN2. basic_solver. }
          assert (REST : (rhb_t ⨾ eco_t) ≡ restr_rel E_t (rhb_t ⨾ eco_t)).
            { rewrite restr_relE. rewrite wf_rhbE; eauto.
              rewrite wf_ecoE; eauto. clear; basic_solver 21. }
          assert (IRR : irreflexive (restr_rel E_t (rhb_t ⨾ eco_t))).
            { rewrite <- REST. rewrite rhb_eco_irr_equiv; eauto.
              destruct CONS. unfold irreflexive; intros x COND.
              unfold irreflexive in cons_coherence.
              assert (F : (hb_t ⨾ eco_t^?) x x -> False).
                { apply cons_coherence. }
                apply F. unfold seq. unfold seq in COND.
                destruct COND as (x0 & C1 & C2).
                exists x0. split; auto. }
            rewrite REST. apply collect_rel_irr_inj with (rr := rhb_t ⨾ eco_t); eauto. }
        { rotate 1. eapply empty_irr.
          split; [| clear; basic_solver].
          intros x y PATH. destruct PATH as (x0 & EQA & (x1 & P1 & P2)).
          assert (F : (⦗eq a⦘ ⨾ rhb_s) x x1).
          { unfold seq. exists x0. split; auto. }
          assert (T : codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅).
          { apply read_rhb_codom with (m := m); eauto. }
          assert (Q : ∅ x1).
          { apply T; basic_solver. }
          destruct Q. }
        { rotate 1. eapply empty_irr.
          split; [| clear; basic_solver].
          intros x y PATH. destruct PATH as (x0 & EQA & (x1 & P1 & P2)).
          assert (F : (⦗eq a⦘ ⨾ rhb_s) x x1).
          { unfold seq. exists x0. split; auto. }
          assert (T : codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅).
          { apply read_rhb_codom with (m := m); eauto. }
          assert (Q : ∅ x1).
          { apply T; basic_solver. }
          destruct Q. }
        { rotate 1. eapply empty_irr.
          split; [| clear; basic_solver].
          intros x y PATH. destruct PATH as (x0 & EQA & (x1 & P1 & P2)).
          assert (F : (⦗eq a⦘ ⨾ rhb_s) x x1).
          { unfold seq. exists x0. split; auto. }
          assert (T : codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅).
          { apply read_rhb_codom with (m := m); eauto. }
          assert (Q : ∅ x1).
          { apply T; basic_solver. }
          destruct Q. }
        assert (IN' : rhb_s ⨾ (srf_s ⨾ ⦗eq a⦘)⁻¹ ⨾ co_s ⨾ rf_s^? ⊆ rhb_s ⨾ (srf_s ⨾ ⦗eq a⦘)⁻¹ ⨾ co_s ⨾ ⦗W_s⦘ ⨾ rf_s^? ).
        { rewrite wf_coD; eauto. basic_solver 21. } rewrite IN'.
        rotate 3. rewrite transp_seq. rewrite transp_eqv_rel.
        arewrite (rhb_s ⊆ rhb_s^? ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)).
        { unfold rhb. rewrite ct_end at 1. hahn_frame.
          basic_solver. }
        assert (IN : co_s ⨾ ⦗W_s⦘ ⨾ rf_s^? ⨾ rhb_s ⨾ (srf_s ⨾ ⦗eq a⦘)⁻¹
                                ⊆ co_s ⨾ vf_s ⨾ (srf_s ⨾ ⦗eq a⦘)⁻¹).
          { rewrite <- rf_rhb_sub_vf; basic_solver. }
        rewrite rhb_in_hb. arewrite (co_s ⊆ co_s ⨾ ⦗E_s⦘).
        { rewrite wf_coE; eauto. basic_solver. }
        arewrite (⦗E_s⦘ ⨾ ⦗W_s⦘ ⨾ rf_s^? ⨾ hb_s^? ⊆ vf_s).
        rewrite rpo_in_sb. rewrite !seq_union_l.
        rewrite !seq_union_r. apply irreflexive_union.
        split.
        { apply irreflexive_union. split.
          { unfold srf. basic_solver 12. }
          unfold srf. basic_solver 12. }
        rewrite read_sw_sub; eauto.
        arewrite (m ↑ sw_t ⊆ m ↑ sw_t ⨾ ⦗m ↑₁ E_t⦘).
        { rewrite wf_swE; eauto. basic_solver. }
        arewrite (⦗m ↑₁ E_t⦘ ⨾ ⦗eq a⦘ ⊆ ∅₂).
        { intros x y (z & (EQ1 & COND1) & (EQ2 & COND2)); subst.
          destruct NIN with y; vauto. }
        basic_solver 21. }
    split; try basic_solver. rewrite RMW_MAP; eauto.
    rewrite read_fr_sub; eauto. rewrite seq_union_l. rewrite inter_union_r.
    apply inclusion_union_l.
    { rewrite CO_MAP. assert (IN2 : dom_rel co_t ⊆₁ E_t).
      { induction 1 as (y & PATH). apply wf_coE in PATH; eauto.
        destruct PATH as (x0 & INE & PATH); apply INE. }
      assert (IN3 : codom_rel fr_t ⊆₁ E_t).
      { induction 1 as (y & PATH). apply wf_frE in PATH; eauto.
        destruct PATH as (x0 & INE1 & (x1 & PATH & (EQ & INE2))); vauto. }
      erewrite <- collect_rel_seq.
      { rewrite <- XmmCons.coll_rel_inter; eauto.
        { destruct CONS. rewrite cons_atomicity; eauto. basic_solver. }
        assert (IN1' : dom_rel rmw_t ⊆₁ E_t).
        { rewrite wf_rmwE; eauto. basic_solver. }
        assert (IN2' : codom_rel rmw_t ⊆₁ E_t).
        { rewrite wf_rmwE; eauto. basic_solver. }
        assert (IN3' : dom_rel (fr_t ⨾ co_t) ⊆₁ E_t).
        { rewrite wf_frE, wf_coE; eauto. basic_solver. }
        assert (IN4' : codom_rel (fr_t ⨾ co_t) ⊆₁ E_t).
        { rewrite wf_frE, wf_coE; eauto. basic_solver. }
        rewrite IN1', IN2', IN3', IN4'. basic_solver. }
      rewrite IN2, IN3. rewrite set_unionK.
      basic_solver. }
    rewrite transp_seq. do 2 rewrite seqA.
    rewrite transp_eqv_rel.
    intros x y PATH. destruct PATH as (MAPPED & (x0 & (EQ & EQA) & PATH)).
    assert (RMWE : rmw_t ≡ ⦗E_t⦘ ⨾ rmw_t).
    { rewrite wf_rmwE; eauto. basic_solver. }
    assert (RMWN : m ↑ rmw_t ≡ ⦗E_s \₁ eq a⦘ ⨾ m ↑ rmw_t).
    { rewrite acts_set_helper; eauto. rewrite <- collect_rel_eqv.
      rewrite <- collect_rel_seq.
      { rewrite <- RMWE. basic_solver. }
      assert (IN1 : codom_rel ⦗E_t⦘ ⊆₁ E_t).
      { induction 1 as (x2 & COND).
        destruct COND; vauto. }
      assert (IN2 : dom_rel rmw_t ⊆₁ E_t).
      { induction 1 as (x2 & COND). apply wf_rmwE in COND; eauto.
        destruct COND as (x' & INE & COND); apply INE. }
      rewrite IN1, IN2. rewrite set_unionK. all : basic_solver. }
    apply RMWN in MAPPED.
    destruct MAPPED as (x' & M1 & M2); subst.
    destruct M1 as (EQ & (INE & NEQ)).
    basic_solver.
Qed.

End ConsistencyReadExtent.

End XmmCons.