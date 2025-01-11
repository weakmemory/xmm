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

Section ConsistencyMonotonicity.

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

(*MONOTONICITY*)

Lemma monoton_fr_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t)
        (RPO_MAP : rpo_s ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ⊆ m ↑ rf_t)
        (CO_MAP : co_s ⊆ m ↑ co_t)
        (RMW_MAP : rmw_s ⊆ m ↑ rmw_t)
        (HB_MAP : rhb_s ⊆ m ↑ rhb_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    fr_s ⊆ m ↑ fr_t.
Proof using.
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

Lemma monoton_eco_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t)
        (RPO_MAP : rpo_s ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ⊆ m ↑ rf_t)
        (CO_MAP : co_s ⊆ m ↑ co_t)
        (RMW_MAP : rmw_s ⊆ m ↑ rmw_t)
        (HB_MAP : rhb_s ⊆ m ↑ rhb_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    eco_s ⊆ m ↑ eco_t.
Proof using.
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

Lemma monoton_cons (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t)
        (RPO_MAP : rpo_s ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ⊆ m ↑ rf_t)
        (CO_MAP : co_s ⊆ m ↑ co_t)
        (RMW_MAP : rmw_s ⊆ m ↑ rmw_t)
        (HB_MAP : rhb_s ⊆ m ↑ rhb_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    WCore.is_cons G_s sc_s.
Proof using.
  constructor.
  { case_refl _.
    { rewrite hb_helper; eauto. rewrite irreflexive_union. split.
      { apply sb_irr; eauto. }
      intros x PATH.
      assert (VERT' : (m ↑ rhb_t) x x).
      { destruct HB_MAP with (x := x) (y := x); vauto. }
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
    apply rhb_eco_irr_equiv; eauto.
    apply irreflexive_inclusion with (r' := m ↑ rhb_t ⨾ m ↑ eco_t); eauto.
    { apply seq_mori; vauto. apply monoton_eco_sub; vauto. }
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
  { split; [| basic_solver].
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
    rewrite IN1, IN2. basic_solver. }
  admit. (* sc *)
Admitted.

End ConsistencyMonotonicity.

End XmmCons.