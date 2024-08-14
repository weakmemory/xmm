Require Import Lia Setoid Program.Basics.
Require Import AuxDef AuxInj.
Require Import Core.
Require Import Rhb Srf.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import CombRelations.

Module Consistency.

Section HB.

Open Scope program_scope.

Variable G : execution.
Variable sc : relation actid.

Notation "'lab'" := (lab G).
Notation "'val'" := (val lab).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'rpo'" := (rpo G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'data'" := (data G).
Notation "'ctrl'" := (ctrl G).
Notation "'addr'" := (addr G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'F'" := (is_f lab).
Notation "'hb'" := (hb G).
Notation "'rhb'" := (rhb G).
Notation "'same_loc'" := (same_loc lab).
Notation "'vf'" := (vf G).
Notation "'srf'" := (srf G).
Notation "'eco'" := (eco G).
Notation "'psc'" := (imm.psc G).
Notation "'fr'" := (fr G).
Notation "'sw'" := (sw G).

Lemma hb_eco_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) :
    irreflexive (hb ⨾ eco).
Proof using.
    destruct CONS. apply irreflexive_inclusion
                        with (r' := hb ⨾ eco^?); eauto.
    apply inclusion_seq_mon; basic_solver.
Qed.

Lemma vf_hb_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) :
    irreflexive (vf ⨾ hb).
Proof using.
    unfold vf. arewrite_id ⦗W⦘; arewrite_id ⦗E⦘.
    rels. arewrite (rf^? ⊆ eco^?).
    generalize (eco_trans WF); ins; relsf.
    generalize (@hb_trans G); ins; relsf.
    relsf; repeat (splits; try apply irreflexive_union).
    by rotate 1; apply CONS.
Qed.

Lemma srf_hb_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) :
    irreflexive (srf ⨾ hb).
Proof using.
    rewrite srf_in_vf; try apply vf_hb_irr; eauto.
Qed.

Lemma rhb_in_hb :
    rhb ⊆ hb.
Proof using.
    unfold rhb; unfold hb.
    apply clos_trans_mori.
    rewrite rpo_in_sb; basic_solver.
Qed.

Lemma sb_sw_in_rpo_sw :
    sb ⨾ sw ⊆ rpo ⨾ sw.
Proof using.
  transitivity (sb ⨾ ⦗fun a => is_rel lab a⦘ ⨾ sw).
  { arewrite (sw ⊆ (⦗fun a => is_rel lab a⦘) ⨾ sw) at 1; [|done].
    unfold sw. unfold release. basic_solver 21. }
  hahn_frame_r.
  unfold rpo, rpo_imm. rewrite <- ct_step.
  eauto with hahn.
Qed.

Lemma sw_sb_in_rpo :
    sw ⨾ sb ⊆ sw ⨾ rpo.
Proof using.
  transitivity (sw ⨾ ⦗fun a => is_acq lab a⦘ ⨾ sb).
  { arewrite (sw ⊆ sw ;; (⦗fun a => is_acq lab a⦘)) at 1; [|done].
    unfold sw. basic_solver 21. }
  hahn_frame_l.
  unfold rpo, rpo_imm. rewrite <- ct_step.
  eauto with hahn.
Qed.

Lemma sb_sw_trans_in_rpo_sw_trans :
    sb ⨾ sw⁺ ⊆ rpo ⨾ sw⁺.
Proof using.
  now rewrite ct_begin, <- !seqA, sb_sw_in_rpo_sw.
Qed.

(* TODO: remove *)
Lemma sb_sw_trans_trans :
    (sb ⨾ sw⁺)⁺ ⊆ (rpo ⨾ sw⁺)⁺.
Proof using.
  now rewrite sb_sw_trans_in_rpo_sw_trans.
Qed.

(*
Lemma sb_rpo_start x x0 y
        (SB : sb x x0)
        (SW : sw x0 y) :
    rpo x x0.
Proof using.
    unfold rpo. left. left. right. destruct SW. destruct H.
    unfold release in H. assert (REL : is_rel lab x0).
    { destruct H. destruct H. destruct H. basic_solver. }
    basic_solver.
Qed.

Lemma rpo_sb_end x x0 y
        (RPO : sw x x0)
        (SB : sb x0 y) :
    rpo x0 y.
Proof using.
    unfold rpo. left. left. left. right. destruct RPO. destruct H.
    assert (ACQ : is_acq lab x0).
    { destruct H0. destruct H0. destruct H1. destruct H1.
      destruct H2. basic_solver. }
    basic_solver.
Qed.
*)

(* TODO: move to AuxRel.v *)
Lemma ct_unit_left A (r : relation A) :
    r ⨾ r⁺ ⊆ r⁺.
Proof.
  arewrite (r ⊆ r⁺) at 1. apply ct_ct.
Qed.

(*
Lemma ct_unit_helper A (r r' : relation A) :
    r ⨾ r⁺ ⨾ r' ⊆ r⁺ ⨾ r'.
Proof using.
  unfold seq, inclusion; ins; desf; vauto.
  exists z0; split; vauto.
Qed.
*)

(* TODO: move *)
Lemma trans_helper_swapped A (r r' : relation A)
        (TRANS : transitive r) :
    r ⨾ (r' ∪ r)⁺ ⊆ r ∪ (r ⨾ r'⁺)⁺ ⨾ r^?.
Proof using.
  rewrite path_union2. rewrite !seq_union_r.
  arewrite (r ⨾ r＊ ⊆ r⁺).
  arewrite (r ⨾ r⁺ ⊆ r⁺) by apply ct_unit_left.
  arewrite (r⁺ ⊆ r).
  arewrite (r'⁺ ⊆ r'＊).
  rels.
  rewrite rtE at 1. rewrite seq_union_r, seq_id_r.
  unionL; eauto with hahn.
  all: unionR right.
  { rewrite <- ct_step with (r := r ;; r'⁺).
    basic_solver 10. }
  rewrite ct_rotl, <- !seqA.
  rewrite <- ct_begin.
  rewrite !seqA.
  rewrite rtE, !seq_union_r, seq_id_r.
  arewrite ((r ⨾ r'⁺)⁺ ⨾ r ⨾ r'⁺ ⊆ (r ⨾ r'⁺)⁺).
  { now rewrite ct_unit. }
  rewrite crE, seq_union_r, seq_id_r.
  eauto with hahn.
Qed.

(* TODO: remove this lemma *)
Lemma swap_helper A (r r' : relation A) :
    r ⨾ (r' ∪ r)⁺ ≡ r ⨾ (r ∪ r')⁺.
Proof using.
  now rewrite unionC.
Qed.

Lemma trans_helper A (r r' : relation A)
        (TRANS : transitive r) :
    r ⨾ (r ∪ r')⁺ ⊆ r ∪ (r ⨾ r'⁺)⁺ ⨾ r^?.
Proof using.
    rewrite <- swap_helper. apply trans_helper_swapped; vauto.
Qed.

Lemma hb_helper :
    hb ≡ sb ∪ rhb.
Proof using.
    split.
    2: { rewrite rhb_in_hb; eauto.
         rewrite inclusion_union_l with
            (r := sb) (r' := hb) (r'' := hb); try basic_solver.
            unfold hb. rewrite path_ut_last. basic_solver. }
    unfold hb, rhb. intros x y H. apply clos_trans_t1n in H.
    assert (IN : sw＊ ⨾ (rpo ⨾ sw＊)⁺ ⊆ sw＊ ⨾ ((sb ∩ same_loc ∪ rpo) ⨾ sw＊)⁺).
    { apply inclusion_seq_mon; [basic_solver |].
      apply inclusion_t_t. apply inclusion_seq_mon; basic_solver. }
    induction H.
    { destruct H; try basic_solver. right. apply ct_step. basic_solver. }
    destruct H; destruct IHclos_trans_1n.
    { left. assert (TRANS : transitive sb). apply sb_trans.
      unfold transitive in TRANS. basic_solver. }
    { assert (TRANS : transitive sb).
      { apply sb_trans. }
      rewrite <- clos_trans_t1n_iff in H0.
      assert (PATH : (sb ⨾ (sb ∪ sw)⁺) x z).
      { basic_solver. }
      apply trans_helper in PATH; eauto. destruct PATH.
      { left. basic_solver. }
      destruct H2. destruct H2. destruct H3. 2 :
      { apply sb_sw_trans_trans in H2. assert (H' := H2).
        apply ct_end in H2. destruct H2. destruct H2.
        destruct H4. destruct H4. apply ct_end in H5.
        destruct H5. destruct H5. assert (RPO : rpo x0 z).
        { apply rpo_sb_end with (x0 := x0) (x := x3); eauto. }
        right. apply ct_ct. unfold seq. exists x0. split.
        { apply ct_unionE. right.
          apply IN. unfold seq. exists x. split; vauto.
          assert (EQ : (fun x4 y0 : actid =>
                exists z0 : actid, rpo x4 z0 /\ sw＊ z0 y0)⁺ ≡ (rpo ⨾ sw＊)⁺).
          { unfold seq. basic_solver. }
          apply EQ.
          apply inclusion_t_t with (r := rpo ⨾ sw⁺); vauto.
          apply inclusion_seq_mon; vauto.
          apply inclusion_t_rt. }
        apply ct_step. basic_solver. }
      destruct H3. apply sb_sw_trans_trans in H2. assert (H' := H2).
      right. apply ct_unionE. right. apply IN. unfold seq. exists x. split; vauto.
      assert (EQ : (fun x4 y0 : actid =>
            exists z0 : actid, rpo x4 z0 /\ sw＊ z0 y0)⁺ ≡ (rpo ⨾ sw＊)⁺).
      { unfold seq. basic_solver. }
      apply EQ.
      apply inclusion_t_t with (r := rpo ⨾ sw⁺); basic_solver. }
    { assert (RPO : rpo y z).
      { apply rpo_sb_end with (x := x); eauto. }
      right. apply ct_ct. unfold seq. exists y. split; vauto. apply ct_step; vauto. }
    right. apply ct_ct. unfold seq. exists y. split; auto.
    apply ct_step. basic_solver.
Qed.

Lemma hb_locs :
    hb ∩ same_loc ≡ rhb ∩ same_loc.
Proof using.
  admit.
Admitted.

Lemma sb_in_hb :
    sb ⊆ hb.
Proof using.
    rewrite hb_helper; eauto. basic_solver.
Qed.

Lemma vf_hb :
    vf ⨾ hb ⨾ hb^? ⊆ vf.
Proof using.
    unfold vf.
    generalize (@hb_trans G); basic_solver 21.
Qed.

Lemma rf_rhb_sub_vf
        (WF  : Wf G):
    ⦗W⦘ ⨾ rf^? ⨾ rhb ⊆ vf.
Proof using.
    unfold vf. rewrite rhb_in_hb; eauto.
    assert (EQ1 : rf ≡ ⦗E⦘ ⨾ ⦗W⦘ ⨾ rf).
    { rewrite wf_rfD; eauto. rewrite wf_rfE; eauto. basic_solver. }
    case_refl _.
    { rewrite <- inclusion_id_cr with (r := rf).
      rewrite <- inclusion_step_cr with (r := hb) (r' := hb). 2 : basic_solver.
      rels. assert (EQ2 : hb ≡ ⦗E⦘ ⨾ hb ⨾ ⦗E⦘).
      { rewrite wf_hbE; eauto. basic_solver. }
      rewrite EQ2. basic_solver. }
    rewrite <- inclusion_step_cr with (r := hb) (r' := hb). 2 : basic_solver.
    rewrite <- inclusion_step_cr with (r := rf) (r' := rf). 2 : basic_solver.
    rewrite EQ1. basic_solver.
Qed.

Lemma rhb_eco_irr_equiv
        (WF  : Wf G):
    irreflexive (rhb ⨾ eco) <-> irreflexive (hb ⨾ eco).
Proof using.
    split.
    { intros H. unfold irreflexive. intros x H0. destruct H0. destruct H0.
      assert (SAME_LOC : same_loc x x0). apply loceq_eco in H1; eauto.
      unfold same_loc; eauto. assert (RHB : rhb x x0).
      { eapply hb_locs. basic_solver. }
      destruct H with (x := x). basic_solver. }
    intros IR. apply irreflexive_inclusion
                    with (r' := hb ⨾ eco); eauto.
    apply inclusion_seq_mon. apply rhb_in_hb; eauto. vauto.
Qed.

(* Lemma rmw_in_rpo
        (WF : Wf G) :
    rmw ⊆ rpo.
Proof using.
    (* seems to be incorrect in new
      definitions -- check if it's needed*)
    admit.
Admitted. *)

End HB.

Section Draft.

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
Notation "'W_s'" := (is_w lab_s).
Notation "'R_s'" := (is_r lab_s).
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
Notation "'W_t'" := (is_w lab_t).
Notation "'R_t'" := (is_r lab_t).
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
        (INJ : inj_dom ⊤₁ m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t)
        (RPO_MAP : rpo_s ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ⊆ m ↑ rf_t)
        (CO_MAP : co_s ⊆ m ↑ co_t)
        (RMW_MAP : rmw_s ⊆ m ↑ rmw_t)
        (HB_MAP : hb_s ⊆ m ↑ hb_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    fr_s ⊆ m ↑ fr_t.
Proof using.
    unfold fr. rewrite RF_MAP. rewrite CO_MAP.
    rewrite <- collect_rel_transp.
    rewrite collect_rel_seq; vauto.
    assert (SUB : E_t ⊆₁ ⊤₁). { basic_solver. }
    assert (IN1 : codom_rel rf_t⁻¹ ⊆₁ E_t).
    { rewrite codom_transp. induction 1. apply wf_rfE in H; eauto.
      destruct H. destruct H. apply H. }
    assert (IN2 : dom_rel co_t ⊆₁ E_t).
    { induction 1. apply wf_coE in H; eauto.
      destruct H. destruct H. apply H. }
    rewrite IN1, IN2. basic_solver.
Qed.

Lemma monoton_eco_sub (m : actid -> actid)
        (INJ : inj_dom ⊤₁ m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t)
        (RPO_MAP : rpo_s ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ⊆ m ↑ rf_t)
        (CO_MAP : co_s ⊆ m ↑ co_t)
        (RMW_MAP : rmw_s ⊆ m ↑ rmw_t)
        (HB_MAP : hb_s ⊆ m ↑ hb_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    eco_s ⊆ m ↑ eco_t.
Proof using.
    unfold eco. repeat rewrite collect_rel_union.
    assert (SUB : E_t ⊆₁ ⊤₁). { basic_solver. }
    repeat apply inclusion_union_l.
    { rewrite RF_MAP; vauto. }
    { rewrite CO_MAP, RF_MAP.
      rewrite collect_rel_seq; vauto.
      { case_refl _. all : basic_solver 22. }
      assert (IN1 : dom_rel rf_t^? ⊆₁ E_t).
      { induction 1. destruct H; vauto.
        { admit. } apply wf_rfE in H; eauto.
      destruct H. destruct H. destruct H; vauto. }
      assert (IN2 : codom_rel co_t ⊆₁ E_t).
      { induction 1. apply wf_coE in H; eauto.
        destruct H. destruct H. destruct H0. destruct H0.
        destruct H1; vauto. }
      rewrite IN1, IN2. basic_solver. }
    rewrite monoton_fr_sub, RF_MAP; eauto.
    (* rewrite collect_rel_seq; vauto.  // doesn't work for 2nd
    { case_refl _. all : basic_solver 22. }
    assert (IN1 : dom_rel rf_t^? ⊆₁ E_t).
    { induction 1. destruct H; vauto.
      { admit. } apply wf_rfE in H; eauto.
    destruct H. destruct H. destruct H; vauto. }
    assert (IN2 : codom_rel fr_t ⊆₁ E_t).
    { induction 1. apply wf_frE in H; eauto.
      destruct H. destruct H. destruct H0. destruct H0.
      destruct H1; vauto. }
    rewrite IN1, IN2. basic_solver. *)
    admit.
Admitted.

Lemma monoton_cons (m : actid -> actid)
        (INJ : inj_dom ⊤₁ m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t)
        (RPO_MAP : rpo_s ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ⊆ m ↑ rf_t)
        (CO_MAP : co_s ⊆ m ↑ co_t)
        (RMW_MAP : rmw_s ⊆ m ↑ rmw_t)
        (HB_MAP : hb_s ⊆ m ↑ hb_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    WCore.is_cons G_s sc_s.
Proof using.
  assert (SUB : E_t ⊆₁ ⊤₁). { basic_solver. }
  constructor.
  { case_refl _.
    { assert(HBIRR : irreflexive hb_t).
      { destruct CONS. apply hb_irr; eauto. }
      assert (REST : (hb_t) ≡ restr_rel E_t (hb_t)).
      { rewrite restr_relE. rewrite wf_hbE; eauto.
        basic_solver 21. }
      assert (IRR' : irreflexive (restr_rel E_t (hb_t))).
      { rewrite <- REST. apply HBIRR. }
      assert (IRR'' : irreflexive (m ↑ restr_rel E_t hb_t)).
      { apply collect_rel_irr_inj; eauto. basic_solver. }
      rewrite <- REST in IRR''. basic_solver. }
    assert (IRR : irreflexive (m ↑ hb_t ⨾ m ↑ eco_t)).
    { rewrite <- collect_rel_seq.
      { assert (REST : (hb_t ⨾ eco_t) ≡ restr_rel E_t (hb_t ⨾ eco_t)).
        { rewrite restr_relE. rewrite wf_hbE, wf_ecoE; eauto.
          basic_solver 21. }
        assert (IRR' : irreflexive (restr_rel E_t (hb_t ⨾ eco_t))).
        { rewrite <- REST. destruct CONS. admit. }
        assert (IRR'' : irreflexive (m ↑ restr_rel E_t (hb_t ⨾ eco_t))).
        { apply collect_rel_irr_inj; eauto. basic_solver. }
        rewrite <- REST in IRR''; vauto. }
      assert (IN1 : codom_rel hb_t ⊆₁ E_t).
      { rewrite wf_hbE; eauto. basic_solver. }
      assert (IN2 : dom_rel eco_t ⊆₁ E_t).
      { rewrite wf_ecoE; eauto. basic_solver. }
      rewrite IN1, IN2. basic_solver. }
    rewrite monoton_eco_sub; eauto.
    rewrite HB_MAP; eauto. }
  { split; [| basic_solver].
    rewrite RMW_MAP, CO_MAP, monoton_fr_sub; eauto.
    rewrite <- collect_rel_seq.
    { rewrite <- collect_rel_interE; eauto.
      destruct CONS. rewrite cons_atomicity.
      basic_solver. }
    assert (IN1 : codom_rel fr_t ⊆₁ E_t).
    { rewrite wf_frE; eauto. basic_solver. }
    assert (IN2 : dom_rel co_t ⊆₁ E_t).
    { rewrite wf_coE; eauto. basic_solver. }
    rewrite IN1, IN2. basic_solver. }
  admit.
Admitted.

(*READ--EXTENSIBILITY*)

Lemma read_fr_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
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
      { rewrite codom_transp. induction 1. apply wf_rfE in H; eauto.
        destruct H. destruct H. apply H. }
      assert (IN2 : dom_rel co_t ⊆₁ E_t).
      { induction 1. apply wf_coE in H; eauto.
        destruct H. destruct H. apply H. }
      rewrite IN1, IN2. basic_solver. }
    rewrite EQ; basic_solver.
Qed.

Lemma eco_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
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
    apply inclusion_union_l. 1, 2 : basic_solver 21.
    { rewrite CO_MAP. case_refl _.
        { basic_solver 21. }
        rewrite RF_MAP. rewrite seq_union_r.
        apply inclusion_union_l. 2 : basic_solver 21.
        do 5 left. right. assert (EQ : m ↑ (co_t ⨾ rf_t) ≡ m ↑ co_t ⨾ m ↑ rf_t).
        { eapply collect_rel_seq. assert (IN1 : codom_rel co_t ⊆₁ E_t).
          { induction 1. apply wf_coE in H0; eauto.
            destruct H0. destruct H0. destruct H1. destruct H1.
            destruct H2. rewrite H2 in H3. apply H3. }
          assert (IN2 : dom_rel rf_t ⊆₁ E_t).
          { induction 1. apply wf_rfE in H0; eauto.
            destruct H0. destruct H0. apply H0. }
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
          { rewrite codom_transp. induction 1. apply wf_rfE in H; eauto.
            destruct H. destruct H. apply H. }
          assert (IN2 : dom_rel co_t ⊆₁ E_t).
          { induction 1. apply wf_coE in H; eauto.
            destruct H. destruct H. apply H. }
          erewrite collect_rel_seq; eauto. rewrite IN1, IN2. basic_solver. }
        rewrite EQ. basic_solver 21. }
      basic_solver 12. }
    unfold fr. rewrite CO_MAP. rewrite RF_MAP.
    rewrite transp_union. rewrite seq_union_l.
    rewrite seq_union_l. apply inclusion_union_l. 2 : basic_solver 21.
    rewrite seq_union_r. apply inclusion_union_l. 2 : basic_solver 21.
    assert (EQ :  m ↑ ((rf_t⁻¹ ⨾ co_t) ⨾ rf_t) ≡ ((m ↑ rf_t)⁻¹ ⨾ m ↑ co_t) ⨾ m ↑ rf_t).
    { rewrite <- collect_rel_transp.
      assert (IN1 : codom_rel rf_t⁻¹ ⊆₁ E_t).
      { rewrite codom_transp. induction 1. apply wf_rfE in H; eauto.
        destruct H. destruct H. apply H. }
      assert (IN2 : dom_rel co_t ⊆₁ E_t).
      { induction 1. apply wf_coE in H; eauto.
        destruct H. destruct H. apply H. }
      assert (IN3 : dom_rel rf_t ⊆₁ E_t).
      { induction 1. apply wf_rfE in H; eauto.
        destruct H. destruct H. apply H. }
      erewrite collect_rel_seq. erewrite collect_rel_seq. basic_solver.
      { rewrite IN1, IN2. basic_solver. }
      assert (COD_IN : codom_rel (rf_t⁻¹ ⨾ co_t) ⊆₁ E_t).
      { rewrite codom_seq. induction 1. apply wf_coE in H; eauto.
        destruct H. destruct H. destruct H0. destruct H0.
        destruct H1. rewrite H1 in H2. apply H2. }
      rewrite COD_IN, IN3. basic_solver. }
    symmetry in EQ. rewrite EQ. basic_solver 21.
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

Lemma sw_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    sw_s ⊆ m ↑ sw_t.
Proof using.
    unfold sw. unfold release. unfold rs.
    admit.
Admitted.

Lemma rhb_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    rhb_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rhb_t ∪ rhb_s ⨾ ⦗eq a⦘.
Proof using.
    unfold rhb. intros x y H. destruct H. destruct H.
    destruct H0. destruct H0. apply ct_unionE in H.
    destruct H. admit.
Admitted.

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

Lemma rhb_codom (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
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
    assert (EMP4 : codom_rel (⦗eq a⦘ ⨾ sb_s ∩ same_loc_s) ≡₁ ∅).
    { admit. (*???*) }
    assert (EMP5 : codom_rel ((⦗eq a⦘ ⨾ sb_s ∩ same_loc_s) ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)＊) ≡₁ ∅).
    { apply empty_seq_codom; eauto. }
    rewrite EMP1, EMP3, EMP5. basic_solver.
Admitted.

Lemma read_extent (m : actid -> actid)
        (INJ : inj_dom ⊤₁ m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    WCore.is_cons G_s sc_s.
Proof using.
    constructor.
    assert (SUB : E_t ⊆₁ ⊤₁). { basic_solver. }
    { case_refl _.
        { rewrite hb_helper; eauto. rewrite irreflexive_union. split.
          { apply sb_irr; eauto. }
          intros x H. destruct classic with (P := (E_s \₁ eq a) x) as [EQ | EQ].
          { assert (VERT : (rhb_s ⨾ ⦗E_s \₁ eq a⦘) x x).
            { do 2 unfold seq. exists x; split; vauto. }
            assert (VERT' : (m ↑ rhb_t ∪ rhb_s ⨾ ⦗eq a⦘) x x).
            { apply rhb_sub; eauto. basic_solver. }
            destruct VERT'.
            { assert (IRR : irreflexive rhb_t).
              { apply irreflexive_inclusion with (r' := hb_t); eauto.
                apply rhb_in_hb; eauto. destruct CONS. apply hb_irr; eauto. }
              assert (REST : (rhb_t) ≡ restr_rel E_t (rhb_t)).
              { rewrite restr_relE. rewrite wf_rhbE; eauto.
                basic_solver 21. }
              assert (IRR' : irreflexive (restr_rel E_t (rhb_t))).
              { rewrite <- REST. apply IRR. }
              assert (IRR'' : irreflexive (m ↑ restr_rel E_t rhb_t)).
              { apply collect_rel_irr_inj; eauto. basic_solver. }
              rewrite <- REST in IRR''. basic_solver. }
            unfold seq in VERT. destruct VERT. destruct H1. destruct H2.
            destruct H0. destruct H0. destruct H4.
            rewrite H4 in H5. rewrite H5 in EQ. destruct EQ.
            destruct H7; vauto. }
          assert (EQA : eq a x).
          { assert (ALTNIN : ~ (m ↑₁ E_t) x).
            { intros NEG. apply acts_set_helper in NEG; eauto.
            basic_solver. }
            unfold set_minus in EQ. apply not_and_or in EQ.
            destruct EQ.
            { assert (G : rhb_s ≡ ⦗E_s⦘ ⨾ rhb_s ⨾ ⦗E_s⦘).
              { rewrite wf_rhbE; eauto. basic_solver. }
            apply G in H. exfalso. apply H0. destruct H. destruct H. apply H. }
            unfold not in H0. destruct classic with (P := eq a x) as [EQ' | EQ'].
            { basic_solver. }
            exfalso. apply H0. basic_solver. }
          rewrite <- EQA in H. destruct rhb_codom with (m := m); eauto.
          { basic_solver. }
          unfold codom_rel in H0. specialize (H0 a).
          apply H0. exists a. basic_solver. }
        apply rhb_eco_irr_equiv; eauto. rewrite eco_sub; eauto.
        repeat rewrite seq_union_r. repeat rewrite irreflexive_union; splits.
        { assert (H : m ↑ eco_t ≡ ⦗E_s \₁ eq a⦘ ⨾ m ↑ eco_t).
          { rewrite acts_set_helper; eauto.
            rewrite <- collect_rel_eqv. rewrite <- collect_rel_seq.
            { assert (EQ : eco_t ≡ ⦗E_t⦘ ⨾ eco_t).
              { rewrite wf_ecoE; eauto. basic_solver. }
              rewrite <- EQ. basic_solver. }
            assert (IN1 : codom_rel ⦗E_t⦘ ⊆₁ E_t).
              { induction 1; eauto.
              destruct H. destruct H; eauto. }
            assert (IN2 : dom_rel eco_t ⊆₁ E_t).
              { induction 1. apply wf_ecoE in H; eauto.
              destruct H. destruct H. apply H. }
            rewrite IN1, IN2. rewrite set_unionK. all : basic_solver. }
          rewrite H. apply irreflexive_inclusion with (r' := m ↑ rhb_t ⨾ m ↑ eco_t); eauto.
          { rewrite <- seqA. rewrite rhb_sub; eauto; [ | basic_solver].
            rewrite seq_union_l. apply inclusion_union_l; [ basic_solver |].
            rewrite H. basic_solver. }
          rewrite <- collect_rel_seq.
          2 : { assert (IN1 : codom_rel rhb_t ⊆₁ E_t).
                  { induction 1. apply wf_rhbE in H0; eauto.
                    destruct H0. destruct H0. destruct H1. destruct H1.
                    destruct H2. rewrite H2 in H3. apply H3. }
                    assert (IN2 : dom_rel eco_t ⊆₁ E_t).
                  { induction 1. apply wf_ecoE in H0; eauto.
                    destruct H0. destruct H0. apply H0. }
                    rewrite IN1, IN2. basic_solver. }
          assert (REST : (rhb_t ⨾ eco_t) ≡ restr_rel E_t (rhb_t ⨾ eco_t)).
            { rewrite restr_relE. rewrite wf_rhbE; eauto.
              rewrite wf_ecoE; eauto. basic_solver 21. }
          assert (IRR : irreflexive (restr_rel E_t (rhb_t ⨾ eco_t))).
            { rewrite <- REST. rewrite rhb_eco_irr_equiv; eauto.
              destruct CONS. unfold irreflexive; ins. unfold irreflexive in cons_coherence.
              assert (F : (hb_t ⨾ eco_t^?) x x -> False).
                { apply cons_coherence. }
                apply F. unfold seq. unfold seq in H0. destruct H0. destruct H0.
                exists x0. split; auto. }
            rewrite REST. apply collect_rel_irr_inj with (rr := rhb_t ⨾ eco_t); eauto.
            basic_solver. }
        { rotate 1. eapply empty_irr.
          split; try basic_solver.
          intros x y H. destruct H. destruct H. destruct H0. destruct H0.
          assert (F : (⦗eq a⦘ ⨾ rhb_s) x x1).
          { unfold seq. exists x0. split; auto. }
          assert (T : codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅).
          { apply rhb_codom with (m := m); eauto. basic_solver. }
          assert (Q : ∅ x1). apply T. basic_solver.
          destruct Q. }
        { rotate 1. apply empty_irr.
          split; try basic_solver.
          intros x y H. destruct H. destruct H. destruct H0. destruct H0.
          assert (F : (⦗eq a⦘ ⨾ rhb_s) x x1).
          { unfold seq. exists x0. split; auto. }
          assert (T : codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅).
          { apply rhb_codom with (m := m); eauto. basic_solver. }
          assert (Q : ∅ x1). apply T. basic_solver.
          destruct Q. }
        { rotate 1. apply empty_irr.
          split; try basic_solver.
          intros x y H. destruct H. destruct H. destruct H0. destruct H0.
          assert (F : (⦗eq a⦘ ⨾ rhb_s) x x1).
          { unfold seq. exists x0. split; auto. }
          assert (T : codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅).
          { apply rhb_codom with (m := m); eauto. basic_solver. }
          assert (Q : ∅ x1). apply T. basic_solver.
          destruct Q. }
    2 : basic_solver.
    assert (IN' : rhb_s ⨾ (srf_s ⨾ ⦗eq a⦘)⁻¹ ⨾ co_s ⨾ rf_s^? ⊆ rhb_s ⨾ (srf_s ⨾ ⦗eq a⦘)⁻¹ ⨾ co_s ⨾ ⦗W_s⦘ ⨾ rf_s^? ).
    { rewrite wf_coD; eauto. basic_solver 21. } rewrite IN'.
    rotate 3. assert (IN : co_s ⨾ ⦗W_s⦘ ⨾ rf_s^? ⨾ rhb_s ⨾ (srf_s ⨾ ⦗eq a⦘)⁻¹
                            ⊆ co_s ⨾ vf_s ⨾ (srf_s ⨾ ⦗eq a⦘)⁻¹).
      { rewrite <- rf_rhb_sub_vf; basic_solver. }
    rewrite IN. arewrite_id ⦗eq a⦘. rels.
    (* unfold srf. basic_solver 21.  *)
    admit.
    }
    { assert (SUB : E_t ⊆₁ ⊤₁). { basic_solver. }
      split; try basic_solver. rewrite RMW_MAP; eauto.
      rewrite read_fr_sub; eauto. rewrite seq_union_l. rewrite inter_union_r.
      apply inclusion_union_l.
      { rewrite CO_MAP. assert (IN2 : dom_rel co_t ⊆₁ E_t).
        { induction 1. apply wf_coE in H; eauto.
          destruct H. destruct H. apply H. }
        assert (IN3 : codom_rel fr_t ⊆₁ E_t).
        { induction 1. apply wf_frE in H; eauto.
          destruct H. destruct H. destruct H0. destruct H0.
          destruct H1. destruct H1. apply H2. }
        erewrite <- collect_rel_seq.
        { rewrite <- collect_rel_interE.
          all: try now eapply inj_dom_mori; eauto; ins.
          destruct CONS. rewrite cons_atomicity; eauto. basic_solver. }
          rewrite IN2, IN3. rewrite set_unionK.
          basic_solver. }
        rewrite transp_seq. do 2 rewrite seqA.
        rewrite transp_eqv_rel.
        intros x y H. destruct H. destruct H0. destruct H0.
        destruct H0. destruct H2. assert (RMWE : rmw_t ≡ ⦗E_t⦘ ⨾ rmw_t).
        { rewrite wf_rmwE; eauto. basic_solver. }
        assert (RMWN : m ↑ rmw_t ≡ ⦗E_s \₁ eq a⦘ ⨾ m ↑ rmw_t).
        { rewrite acts_set_helper; eauto. rewrite <- collect_rel_eqv.
          rewrite <- collect_rel_seq.
          { rewrite <- RMWE. basic_solver. }
          assert (IN1 : codom_rel ⦗E_t⦘ ⊆₁ E_t).
          { induction 1. destruct H2. destruct H2. apply H3. }
          assert (IN2 : dom_rel rmw_t ⊆₁ E_t).
          { induction 1. apply wf_rmwE in H2; eauto.
            destruct H2. destruct H2. destruct H2. apply H4. }
          rewrite IN1, IN2. rewrite set_unionK. all : basic_solver. }
        apply RMWN in H. destruct H. destruct H.
        destruct H. destruct H3. destruct H4; eauto.
        all : basic_solver. }
    admit.
Admitted.

(*MAX-WRITE-EXTENDED*)

Lemma write_fr_sub (m : actid -> actid)
        (INJ : inj_dom ⊤₁ m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    fr_s ⊆ m ↑ fr_t ∪ m ↑ rf_t⁻¹ ⨾ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a.
Proof using.
    assert (SUB : E_t ⊆₁ ⊤₁). { basic_solver. }
    unfold fr. rewrite RF_MAP. rewrite CO_MAP.
    rewrite seq_union_r. rewrite <- collect_rel_transp.
    rewrite collect_rel_seq.
    { apply inclusion_union_l; basic_solver 12. }
    assert (IN1 : codom_rel rf_t⁻¹ ⊆₁ E_t).
    { rewrite codom_transp. induction 1. apply wf_rfE in H; eauto.
      destruct H. destruct H. apply H. }
    assert (IN2 : dom_rel co_t ⊆₁ E_t).
    { induction 1. apply wf_coE in H; eauto.
      destruct H. destruct H. apply H. }
    rewrite IN1, IN2. basic_solver.
Qed.

Lemma collect_rel_cr_equiv (A B : Type) (f : A -> B) (r : relation A)
    (F_FULL : forall y : B, exists x : A, f x = y) :
    f ↑ r^? ≡ (f ↑ r)^?.
Proof using.
    split; [by apply collect_rel_cr|].
    unfolder; ins; desf; eauto.
    { destruct F_FULL with y.
      repeat eexists; eauto. }
    exists x'; eauto.
Qed.

Lemma write_eco_sub (m : actid -> actid)
        (INJ : inj_dom ⊤₁ m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    eco_s ⊆ m ↑ eco_t
          ∪ (((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a) ⨾ (m ↑ rf_t^?)
          ∪ (m ↑ rf_t^?) ⨾ (((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a) ⨾ (m ↑ rf_t^?).
Proof using.
    unfold eco. repeat rewrite collect_rel_union. rewrite RF_MAP.
    repeat apply inclusion_union_l.
    { repeat left; vauto. }
    { rewrite CO_MAP. rewrite seq_union_l. apply inclusion_union_l.
      { do 3 left. right. destruct H. destruct H.
        apply collect_rel_seq.
        { admit. }
        unfold seq. exists x0. split; auto.
        apply collect_rel_cr_equiv; eauto.
        ins. unfold inj_dom in INJ.
        admit. }
        left. right.
      admit. }
    admit.
Admitted.

Lemma write_sw_sub (m : actid -> actid)
        (INJ : inj_dom ⊤₁ m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    sw_s ⊆ m ↑ sw_t.
Proof using.
  admit.
Admitted.

Lemma write_rhb_sub (m : actid -> actid)
        (INJ : inj_dom ⊤₁ m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    rhb_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rhb_t.
Proof using.
  admit.
Admitted.

Lemma write_rhb_codom (m : actid -> actid)
        (INJ : inj_dom ⊤₁ m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅.
Proof using.
  assert (SUB : E_t ⊆₁ ⊤₁). { basic_solver. }
  unfold rhb. rewrite ct_begin. rewrite <- seqA. rewrite !seq_union_r.
  rewrite !seq_union_l. rewrite !codom_union.
  assert (EMP1 : codom_rel ((⦗eq a⦘ ⨾ rpo_s) ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)＊) ≡₁ ∅).
  { apply empty_seq_codom; eauto. }
  assert (EMP2 : codom_rel (⦗eq a⦘ ⨾ sw_s) ≡₁ ∅).
  { split; [|basic_solver]. rewrite write_sw_sub; eauto.
    unfold codom_rel. intros x H. destruct H.
    destruct H. destruct H.
    assert (IN : (m ↑₁ E_t) x1).
    { destruct H0. destruct H0. destruct H0. destruct H1.
      rewrite <- H1. apply wf_swE in H0; eauto.
      destruct H0. destruct H0. destruct H0.
      basic_solver. }
    apply acts_set_helper in IN; eauto.
    { destruct H. desf. destruct IN. basic_solver. }
    basic_solver. }
  assert (EMP3 : codom_rel ((⦗eq a⦘ ⨾ sw_s) ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)＊) ≡₁ ∅).
  { apply empty_seq_codom; eauto. }
  assert (EMP4 : codom_rel (⦗eq a⦘ ⨾ sb_s ∩ same_loc_s) ≡₁ ∅).
  { admit. (*???*) }
  assert (EMP5 : codom_rel ((⦗eq a⦘ ⨾ sb_s ∩ same_loc_s) ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)＊) ≡₁ ∅).
  { apply empty_seq_codom; eauto. }
  rewrite EMP1, EMP3, EMP5. basic_solver.
Admitted.

Lemma write_extent (m : actid -> actid)
        (INJ : inj_dom ⊤₁ m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    WCore.is_cons G_s sc_s.
Proof using.
  constructor.
  assert (SUB : E_t ⊆₁ ⊤₁). { basic_solver. }
  { case_refl _.
      { rewrite hb_helper; eauto. rewrite irreflexive_union. split.
        { apply sb_irr; eauto. }
        intros x H. destruct classic with (P := (E_s \₁ eq a) x) as [EQ | EQ].
        { assert (VERT : (rhb_s ⨾ ⦗E_s \₁ eq a⦘) x x).
          { do 2 unfold seq. exists x; split; vauto. }
          assert (VERT' : (m ↑ rhb_t) x x).
          { apply write_rhb_sub; eauto. }
          assert (IRR : irreflexive rhb_t).
          { apply irreflexive_inclusion with (r' := hb_t); eauto.
            apply rhb_in_hb; eauto. destruct CONS. apply hb_irr; eauto. }
          assert (REST : (rhb_t) ≡ restr_rel E_t (rhb_t)).
          { rewrite restr_relE. rewrite wf_rhbE; eauto.
            basic_solver 21. }
          assert (IRR' : irreflexive (restr_rel E_t (rhb_t))).
          { rewrite <- REST. apply IRR. }
          assert (IRR'' : irreflexive (m ↑ restr_rel E_t rhb_t)).
          { apply collect_rel_irr_inj; eauto. basic_solver. }
          rewrite <- REST in IRR''. basic_solver 22. }
        assert (EQA : eq a x).
        { assert (ALTNIN : ~ (m ↑₁ E_t) x).
          { intros NEG. apply acts_set_helper in NEG; eauto.
          basic_solver. }
          unfold set_minus in EQ. apply not_and_or in EQ.
          destruct EQ.
          { assert (G : rhb_s ≡ ⦗E_s⦘ ⨾ rhb_s ⨾ ⦗E_s⦘).
            { rewrite wf_rhbE; eauto. basic_solver. }
          apply G in H. exfalso. apply H0. destruct H. destruct H. apply H. }
          unfold not in H0. destruct classic with (P := eq a x) as [EQ' | EQ'].
          { basic_solver. }
          exfalso. apply H0. basic_solver. }
        rewrite <- EQA in H. assert (CD : codom_rel (⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅).
        { apply write_rhb_codom with (m := m); eauto. }
        unfold codom_rel in CD. destruct CD.
        specialize (H0 a). apply H0. exists a. basic_solver. }
      apply rhb_eco_irr_equiv; eauto. rewrite write_eco_sub; eauto.
      repeat rewrite seq_union_r. repeat rewrite irreflexive_union; splits.
      { assert (H : m ↑ eco_t ≡ ⦗E_s \₁ eq a⦘ ⨾ m ↑ eco_t).
        { rewrite acts_set_helper; eauto.
          rewrite <- collect_rel_eqv. rewrite <- collect_rel_seq.
          { assert (EQ : eco_t ≡ ⦗E_t⦘ ⨾ eco_t).
            { rewrite wf_ecoE; eauto. basic_solver. }
            rewrite <- EQ. basic_solver. }
          assert (IN1 : codom_rel ⦗E_t⦘ ⊆₁ E_t).
            { induction 1; eauto.
            destruct H. destruct H; eauto. }
          assert (IN2 : dom_rel eco_t ⊆₁ E_t).
            { induction 1. apply wf_ecoE in H; eauto.
            destruct H. destruct H. apply H. }
          rewrite IN1, IN2. rewrite set_unionK. all : basic_solver. }
        rewrite H. apply irreflexive_inclusion with (r' := m ↑ rhb_t ⨾ m ↑ eco_t); eauto.
        { rewrite <- seqA. rewrite write_rhb_sub; eauto; basic_solver. }
        rewrite <- collect_rel_seq.
        2 : { assert (IN1 : codom_rel rhb_t ⊆₁ E_t).
                { induction 1. apply wf_rhbE in H0; eauto.
                  destruct H0. destruct H0. destruct H1. destruct H1.
                  destruct H2. rewrite H2 in H3. apply H3. }
                  assert (IN2 : dom_rel eco_t ⊆₁ E_t).
                { induction 1. apply wf_ecoE in H0; eauto.
                  destruct H0. destruct H0. apply H0. }
                  rewrite IN1, IN2. basic_solver. }
        assert (REST : (rhb_t ⨾ eco_t) ≡ restr_rel E_t (rhb_t ⨾ eco_t)).
          { rewrite restr_relE. rewrite wf_rhbE; eauto.
            rewrite wf_ecoE; eauto. basic_solver 21. }
        assert (IRR : irreflexive (restr_rel E_t (rhb_t ⨾ eco_t))).
          { rewrite <- REST. rewrite rhb_eco_irr_equiv; eauto.
            destruct CONS. unfold irreflexive; ins. unfold irreflexive in cons_coherence.
            assert (F : (hb_t ⨾ eco_t^?) x x -> False).
              { apply cons_coherence. }
              apply F. unfold seq. unfold seq in H0. destruct H0. destruct H0.
              exists x0. split; auto. }
          rewrite REST. apply collect_rel_irr_inj with (rr := rhb_t ⨾ eco_t); eauto.
          basic_solver. }
      { unfold irreflexive. intros x H. unfold seq in H. destruct H. destruct H.
        destruct H0. destruct H0.
        assert (EQA : x1 = a).
        { destruct H0; basic_solver. }
        rewrite EQA in H1. destruct H1. destruct H1. destruct H1. destruct H2.
        destruct H1.
        { rewrite H1 in H2. rewrite H2 in H3. rewrite <- H3 in H.
          assert (CD : codom_rel (⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅).
          { apply write_rhb_codom with (m := m); eauto. }
          unfold codom_rel in CD. destruct CD.
          specialize (H4 x0). apply H4. exists a. basic_solver. }
        assert (ET : E_t x2).
        { apply wf_rfE in H1; eauto. destruct H1. destruct H1.
          destruct H1. apply H5. }
        assert (ET' : (m ↑₁ E_t) a).
        { rewrite <- H2. basic_solver. }
        basic_solver. }
      unfold irreflexive. intros x H. unfold seq in H. destruct H. destruct H.
      destruct H0. destruct H0. destruct H1. destruct H1.
      assert (EQA : x2 = a).
      { destruct H1; basic_solver. }
      rewrite EQA in H2. destruct H2. destruct H2. destruct H2. destruct H3.
      destruct H2.
      { rewrite H2 in H3. rewrite H3 in H4. rewrite <- H4 in H.
        assert (CD : codom_rel (⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅).
        { apply write_rhb_codom with (m := m); eauto. }
        unfold codom_rel in CD. destruct CD.
        specialize (H5 x0). apply H5. exists a. basic_solver. }
      assert (ET : E_t x3).
      { apply wf_rfE in H2; eauto. destruct H2. destruct H2.
        destruct H2. apply H6. }
      assert (ET' : (m ↑₁ E_t) a).
      { rewrite <- H3. basic_solver. }
      basic_solver. }
  { assert (SUB : E_t ⊆₁ ⊤₁). { basic_solver. }
    split; try basic_solver. rewrite RMW_MAP, CO_MAP; eauto.
    rewrite write_fr_sub; eauto. rewrite !seq_union_l. rewrite !seq_union_r.
    rewrite !inter_union_r. repeat apply inclusion_union_l.
    { assert (IN2 : dom_rel co_t ⊆₁ E_t).
      { induction 1. apply wf_coE in H; eauto.
        destruct H. destruct H. apply H. }
      assert (IN3 : codom_rel fr_t ⊆₁ E_t).
      { induction 1. apply wf_frE in H; eauto.
        destruct H. destruct H. destruct H0. destruct H0.
        destruct H1. destruct H1. apply H2. }
      erewrite <- collect_rel_seq.
      { rewrite <- collect_rel_interE; eauto.
        destruct CONS. rewrite cons_atomicity; eauto. basic_solver. }
        rewrite IN2, IN3. rewrite set_unionK.
        basic_solver. }
    { intros x y H. destruct H. destruct H0. destruct H0.
      assert (EQA : y = a).
      { destruct H1; basic_solver. }
      rewrite EQA in H. destruct H. destruct H.
      destruct H. destruct H2.
      assert (ET : E_t x2).
      { apply wf_rmwE in H; eauto. destruct H. destruct H.
        destruct H4. destruct H4. destruct H5. rewrite H5 in H6; eauto. }
      assert (ET' : (m ↑₁ E_t) a).
      { rewrite <- H3. basic_solver. }
      basic_solver. }
    { intros x y H. destruct H. destruct H0. destruct H0.
      destruct H0. destruct H0.
      assert (EQA : x0 = a).
      { destruct H2; basic_solver. }
      rewrite EQA in H1. destruct H1. destruct H1.
      destruct H1. destruct H3.
      assert (ET : E_t x2).
      { apply wf_coE in H1; eauto. destruct H1. destruct H1.
        destruct H1; eauto. }
      assert (ET' : (m ↑₁ E_t) a).
      { rewrite <- H3. basic_solver. }
      basic_solver. }
    intros x y H. destruct H. destruct H0. destruct H0.
    assert (EQA : y = a).
    { destruct H1; basic_solver. }
    rewrite EQA in H. destruct H. destruct H.
    destruct H. destruct H2.
    assert (ET : E_t x2).
    { apply wf_rmwE in H; eauto. destruct H. destruct H.
      destruct H4. destruct H4. destruct H5. rewrite H5 in H6; eauto. }
    assert (ET' : (m ↑₁ E_t) a).
    { rewrite <- H3. basic_solver. }
    basic_solver. }
  admit.
Admitted.

End Draft.

End Consistency.

