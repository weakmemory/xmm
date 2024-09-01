Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import ThreadTrace.
Require Import Core.
Require Import TraceSwap.
Require Import SubToFullExec.
Require Import ReorderingCommon.
Require Import AuxRel.
Require Import ExecEquiv.
Require Import ExecOps.
Require Import CfgOps.
Require Import StepOps.
Require Import Steps.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
From imm Require Import imm_s_ppo.
Require Import xmm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.
Require Import xmm_comb_rel. 

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

Lemma srf_sub_vf :
    srf ⊆ vf.
Proof using.
    unfold srf. basic_solver.
Qed.

Lemma srf_hb_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) :
    irreflexive (srf ⨾ hb).
Proof using.
    rewrite srf_sub_vf; try apply vf_hb_irr; eauto.
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

(* TODO: remove *)
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
      destruct H2. destruct H2. destruct H3. basic_solver. }
    basic_solver.
Qed.


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
    rewrite hb_helper; eauto; split.
    2: { basic_solver. }
    rewrite inter_union_l. rewrite inclusion_union_l with (r := sb ∩ same_loc)
        (r' := rhb ∩ same_loc) (r'' := rhb ∩ same_loc); try basic_solver.
    unfold rhb. rewrite <- ct_step. unfold rpo. basic_solver 8.
Qed.

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

Lemma wf_rhb_immE 
        (WF : Wf G) :
    (sb ∩ same_loc ∪ rpo ∪ sw) ≡ ⦗E⦘ ⨾ (sb ∩ same_loc ∪ rpo ∪ sw) ⨾ ⦗E⦘.
Proof using.
    split; [| basic_solver].
    rewrite wf_sbE, wf_rpoE, wf_swE; eauto. basic_solver 42.
Qed.

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
Notation "'W_s'" := (fun a => is_true (is_w lab_s a)).
Notation "'R_s'" := (fun a => is_true (is_r lab_s a)).
Notation "'F_s'" := (fun a => is_true (is_f lab_s a)).
Notation "'Rel_s'" := (fun a => is_true (is_rel lab_s a)).
Notation "'Acq_s'" := (fun a => is_true (is_acq lab_s a)).
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
        (HB_MAP : hb_s ⊆ m ↑ hb_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    fr_s ⊆ m ↑ fr_t.
Proof using.
    unfold fr. rewrite RF_MAP. rewrite CO_MAP.
    rewrite <- collect_rel_transp.
    rewrite collect_rel_seq; vauto.
    assert (IN1 : codom_rel rf_t⁻¹ ⊆₁ E_t).
    { rewrite codom_transp. induction 1. apply wf_rfE in H; eauto.
      destruct H. destruct H. apply H. }
    assert (IN2 : dom_rel co_t ⊆₁ E_t).
    { induction 1. apply wf_coE in H; eauto.
      destruct H. destruct H. apply H. }
    rewrite IN1, IN2. basic_solver.
Qed.

Lemma monoton_eco_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
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

Lemma collect_rel_interEE (A B : Type) (f : A -> B) r r'
    (INJ : inj_dom (dom_rel r ∪₁ codom_rel r ∪₁ dom_rel r' ∪₁ codom_rel r') f) :
  f ↑ (r ∩ r') ≡ f ↑ r ∩ f ↑ r'.
Proof using.
  split; [apply collect_rel_inter |].
  unfolder; intros x y REL; desf.
  apply INJ in REL1, REL2; ins; desf.
  { exists x'0, y'0; splits; ins. }
  all: basic_solver 11.
Qed.

Lemma monoton_cons (m : actid -> actid)
        (INJ : inj_dom E_t m)
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
      { apply collect_rel_irr_inj; eauto. }
      rewrite <- REST in IRR''. basic_solver. }
    assert (IRR : irreflexive (m ↑ hb_t ⨾ m ↑ eco_t)).
    { rewrite <- collect_rel_seq.
      { assert (REST : (hb_t ⨾ eco_t) ≡ restr_rel E_t (hb_t ⨾ eco_t)).
        { rewrite restr_relE. rewrite wf_hbE, wf_ecoE; eauto.
          basic_solver 21. }
        assert (IRR' : irreflexive (restr_rel E_t (hb_t ⨾ eco_t))).
        { rewrite <- REST. destruct CONS. unfold irreflexive; ins.
          rewrite crE in cons_coherence.
          unfold irreflexive in cons_coherence.
          specialize (cons_coherence x).
          apply cons_coherence. red. destruct H. 
          destruct H. exists x0. split; vauto. }
        assert (IRR'' : irreflexive (m ↑ restr_rel E_t (hb_t ⨾ eco_t))).
        { apply collect_rel_irr_inj; eauto. }
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
    { rewrite <- collect_rel_interEE; eauto. 
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

(*READ--EXTENSIBILITY*)

Lemma read_fr_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
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

Lemma codom_sw (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
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
    assert (READ : ⦗eq a⦘ ≡ ⦗eq a⦘ ⨾ ⦗R_s⦘).
    { basic_solver. }
    rewrite READ. 
    assert (EMP : (⦗fun a0 : actid => R_s a0⦘ ⨾ sw_s) ≡ ∅₂).
    { unfold sw. unfold release. unfold rs. split; vauto.
      rewrite crE. rewrite !seqA. rewrite !seq_union_l.
      rewrite !seq_union_r. apply inclusion_union_l.
      { intros x y H. destruct H. destruct H. 
        destruct H0. destruct H0. destruct H1. destruct H1.
        destruct H2. destruct H2. destruct H. destruct H0.
        destruct H1. destruct H2. subst. unfold is_r in H4.
        unfold is_w in H7. 
        desf. }
      intros x y H. destruct H. destruct H.
      destruct H0. destruct H0. destruct H1. destruct H1.
      destruct H1. destruct H1. destruct H. destruct H0.
      destruct H1. subst. unfold is_r in H4. 
      unfold is_f in H6. desf. }
    rewrite seqA. rewrite EMP. basic_solver.
Qed.

Lemma sw_helper_rf_rmw (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
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
  rewrite collect_rel_seqi. intros x y HH.
  destruct HH as (z & (HH & (y0 & (H1 & H2)))).
  destruct H2 as (y1 & (H3 & (y2 & (H4 & H5)))).
  destruct H1. subst. exfalso.
  destruct NIN with y0; eauto.
  destruct H3 as (y3 & y4 & ((H6 & H6') & H7 & H8)).
  subst. unfold set_collect. exists y4. split; vauto.
Qed.

Lemma sw_helper_release (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
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
    { apply rtE in HREL. destruct HREL.
      { destruct H. subst; eauto. }
      apply ct_end in H. destruct H as (y0 & (H2 & (y1 & (H3 & H4)))).
      apply wf_rmwD in H4; eauto. destruct H4 as (y2 & (H5 & y3 & (H7 & (H8 & H9)))).
      subst. apply wf_rmwE in H7; eauto. destruct H7 as (y4 & (H10 & (y5 & (H11 & H12)))).
      destruct H12; vauto. unfold set_minus. split; vauto.
      unfold is_w in H9. unfold is_r in IS_R. intros HH. desf. }
    apply MAPEQ in XIN. apply MAPEQ in YIN.
    destruct XIN as (x' & XIN & XEQ), YIN as (y' & YIN & YEQ).
    exists x', y'. splits; ins. split with x'; split.
    { unfolder. unfolder in DOM. desf.
      unfold is_w, is_rel, is_rlx, mod in *.
      rewrite <- LABS with x'; eauto. }
    assert (HREL' : singl_rel x y ⊆ (rf_s ⨾ rmw_s)＊).
    { intros x0 y0 HH. destruct HH; vauto. }
    rewrite RF_MAP, seq_union_l in HREL'.
    assert (EMP : (srf_s ⨾ ⦗eq a⦘) ⨾ rmw_s ≡ ∅₂).
    { rewrite seqA. rewrite RMW_MAP.
      rewrite wf_rmwE; eauto. split; [|basic_solver].
      rewrite collect_rel_seqi. intros x0 y0 HH.
      destruct HH as (z & (HH & (y1 & (H1 & H2)))).
      destruct H2 as (y2 & (H3 & (y3 & (y4 & H5)))).
      destruct H1. symmetry in MAPEQ. destruct H3. 
      destruct H1. destruct H1. destruct H2. subst.
      destruct MAPEQ. destruct H with (m x1); eauto.
      destruct H1. basic_solver. }
    rewrite EMP in HREL'. rewrite union_false_r in HREL'.
    rewrite RMW_MAP in HREL'.
    rewrite <- collect_rel_seq in HREL'.
    2: { assert (IN1 : codom_rel rf_t ⊆₁ E_t).
        { rewrite wf_rfE; eauto. basic_solver. }
        assert (IN2 : dom_rel rmw_t ⊆₁ E_t).
        { rewrite wf_rmwE; eauto. basic_solver. }
        rewrite IN1, IN2. basic_solver. }
    apply rtE in HREL. destruct HREL.
    { destruct H. subst. 
      assert (EQ : x' = y').
      { apply INJ; vauto. }
      subst. apply rtE; left. basic_solver. }
    apply rtE. right. 
    assert (TREQ : (rf_s ⨾ rmw_s)⁺ ⊆ (m ↑ (rf_t ⨾ rmw_t))⁺).
    { apply clos_trans_mori; apply sw_helper_rf_rmw; eauto. }
    apply TREQ in H. 
    assert (REST : (rf_t ⨾ rmw_t) ≡ restr_rel E_t (rf_t ⨾ rmw_t)).
    { rewrite restr_relE. rewrite wf_rfE, wf_rmwE; eauto.
      basic_solver 21. }
    assert (TREQ' : (m ↑ (rf_t ⨾ rmw_t))⁺ ≡ (m ↑ restr_rel E_t (rf_t ⨾ rmw_t))⁺).
    { split; apply clos_trans_mori; rewrite <- REST; vauto. }
    apply TREQ' in H. apply collect_rel_ct_inj in H; vauto.
    unfold collect_rel in H. destruct H as (x0 & y0 & (H1 & H2 & H3)).
    assert (TREQ'' : (restr_rel E_t (rf_t ⨾ rmw_t))⁺ ⊆ (rf_t ⨾ rmw_t)⁺).
    { apply clos_trans_mori; basic_solver. }
    apply TREQ'' in H1. 
    assert (X0IN : E_t x0).
    { apply ct_begin in H1. destruct H1. destruct H.
      destruct H. destruct H. apply wf_rfE in H; vauto.
      destruct H. destruct H. apply H. }
    assert (Y0IN : E_t y0).
    { apply ct_end in H1. destruct H1. destruct H.
      destruct H0. destruct H0.
      apply wf_rmwE in H1; vauto.
      destruct H1. destruct H1.
      destruct H4. destruct H4.
      destruct H5; vauto. }
    assert (EQXX : x0 = x').
    { apply INJ; vauto. }
    assert (EQYY : y0 = y').
    { apply INJ; vauto. }
    vauto. }
  assert (sb_t ∩ same_loc_t ≡ ⦗E_t⦘ ⨾ sb_t ∩ same_loc_t ⨾ ⦗E_t⦘) as EAA.
  { split; [|clear; basic_solver 10].
    rewrite wf_sbE at 1. clear. basic_solver 10. }
  assert (sb_s ∩ same_loc_s ≡ ⦗E_s⦘ ⨾ sb_s ∩ same_loc_s ⨾ ⦗E_s⦘) as EAA'.
  { split; [|clear; basic_solver 10].
    rewrite wf_sbE at 1. clear. basic_solver 10. }
  unfold rs. rels. rewrite !seqA.
  arewrite ((⦗Rel_s⦘ ⨾ ⦗F_s⦘ ⨾ sb_s ⨾ ⦗W_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘) 
          ⊆ ⦗Rel_s⦘ ⨾ ⦗F_s⦘ ⨾ rpo_s ⨾ ⦗W_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘).
    { unfold rpo; unfold rpo_imm. rewrite <- ct_step. basic_solver 21. }
  rewrite wf_rpoE; eauto. rewrite !seqA.
  arewrite (⦗E_s⦘ ⨾ ⦗W_s⦘ ⊆ ⦗E_s \₁ eq a⦘ ⨾ ⦗W_s⦘).
    { unfold set_minus. intros x y HH.
      destruct HH. destruct H. destruct H.
      destruct H0; subst. 
      unfolder. splits; vauto. 
      intros F. unfold is_w, is_r in *. 
      basic_solver. }
  do 3 rewrite <- seqA.
  rewrite <- seqA with (r3 := ⦗W_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ (rf_s ⨾ rmw_s)＊).
  rewrite RPO_MAP. rewrite !seqA.
  intros x y H. destruct H as (x0 & (H1 & (x1 & (H2 & (x2 & (H3 & (x3 &
                (H4 & (x4 & (H5 & (x5 & (H6 & x6 & (H7 & H8))))))))))))).
  destruct H1, H2, H3, H4, H6, H6, H7; subst.
  apply MAPEQ in H0. destruct H0 as (x' & H0 & H0').
  unfold collect_rel. 
  apply rtE in H8. destruct H8.
  { destruct H. destruct H5. destruct H3.
    destruct H3 as (HH1 & HH2 & HH3).
    exists x', x0. splits; vauto.
    unfold seq.
    exists x'. splits; vauto.
    exists x'. splits.
    { apply LABS in H0. unfold compose in H0.
      red. splits; vauto. unfold is_rel in *. 
      unfold mod in *. basic_solver 21. }
    exists x'. splits.
    { apply LABS in H0. unfold compose in H0.
      red. splits; vauto. unfold is_f in *. 
      basic_solver 21. }
    exists x0. splits.
    { apply INJ in HH2; vauto. 
      { apply rpo_in_sb in HH1; vauto. }
      apply wf_rpoE in HH1; vauto. 
      destruct HH1. destruct H.
      destruct H; vauto. }
    assert (XE : E_t x0).
    { apply wf_rpoE in HH1; vauto. 
      destruct HH1. destruct H. destruct H3.
      destruct H3. destruct H4; vauto. }
    exists x0. splits.
    { red; splits; vauto.
      apply LABS in XE. unfold compose in XE.
      unfold is_w in *. basic_solver. }
    exists x0. splits.
    { red; splits; vauto.
      apply LABS in XE. unfold compose in XE.
      unfold is_rlx in *. unfold mod in *. basic_solver. }
    apply rtE. left. basic_solver. }
  assert (TREQ : (rf_s ⨾ rmw_s)⁺ ⊆ (m ↑ (rf_t ⨾ rmw_t))⁺).
  { apply clos_trans_mori; apply sw_helper_rf_rmw; eauto. }
  apply TREQ in H. 
  assert (REST : (rf_t ⨾ rmw_t) ≡ restr_rel E_t (rf_t ⨾ rmw_t)).
  { rewrite restr_relE. rewrite wf_rfE, wf_rmwE; eauto.
    basic_solver 21. }
  assert (TREQ' : (m ↑ (rf_t ⨾ rmw_t))⁺ ≡ (m ↑ restr_rel E_t (rf_t ⨾ rmw_t))⁺).
  { split; apply clos_trans_mori; rewrite <- REST; vauto. }
  apply TREQ' in H. apply collect_rel_ct_inj in H; vauto.
  unfold collect_rel in H. destruct H as (x0 & y0 & (HH1 & HH2 & HH3)).
  assert (TREQ'' : (restr_rel E_t (rf_t ⨾ rmw_t))⁺ ⊆ (rf_t ⨾ rmw_t)⁺).
  { apply clos_trans_mori; basic_solver. }
  apply TREQ'' in HH1.
  exists x', y0. splits; vauto.
  unfold seq.
  exists x'. splits; vauto.
  exists x'. splits.
  { apply LABS in H0. unfold compose in H0.
    red. splits; vauto. unfold is_rel in *. 
    unfold mod in *. basic_solver 21. }
  exists x'. splits.
  { apply LABS in H0. unfold compose in H0.
    red. splits; vauto. unfold is_f in *. 
    basic_solver 21. }
  exists x0. splits.
  { destruct H5 as (z1 & z2 & (HH2 & HH3 & HH4)).
    apply rpo_in_sb in HH2; vauto. 
    apply INJ in HH3; vauto. 
    { apply INJ in HH4; vauto. 
      { apply wf_sbE in HH2; vauto. 
        destruct HH2. destruct H. destruct H.
        destruct H. destruct H1. destruct H. 
        destruct H1; vauto. }
      apply ct_begin in HH1. destruct HH1. destruct H.
      destruct H. destruct H. apply wf_rfE in H; vauto.
      destruct H. destruct H. apply H. }
    apply wf_sbE in HH2; vauto.
    destruct HH2. destruct H. destruct H; vauto. }
  destruct H5. destruct H. destruct H as (HH3 & HH4 & HH5).
  assert (XE : E_t x0).
  { apply wf_rpoE in HH3; vauto. 
    destruct HH3. destruct H. destruct H.
    destruct H1. destruct H1.
    destruct H4; subst. 
    apply INJ in HH5; vauto.
    apply ct_begin in HH1. destruct HH1. destruct H.
    destruct H. destruct H. apply wf_rfE in H; vauto.
    destruct H. destruct H. apply H. }
  exists x0. splits.
  { red; splits; vauto.
    apply LABS in XE. unfold compose in XE.
    unfold is_w in *. basic_solver. }
  exists x0. splits.
  { red; splits; vauto.
    apply LABS in XE. unfold compose in XE.
    unfold is_rlx in *. unfold mod in *. basic_solver. }
  apply rtE. right. basic_solver.
Qed.

Lemma sw_helper_rf (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
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
      { rels. rewrite MAPEQ. intros x y HH.
        destruct HH as (z & (HH & (y' & (H1 & (z' & (H2 & H3)))))).
        destruct H1, H2, H3; subst. unfolder.
        destruct HH. destruct H.
        destruct H as (H5 & H6 & H7). 
        exists x0, x1. splits; vauto.
        all : unfold is_acq, is_rlx, mod in *.
        all : rewrite <- LABS with x1; splits; eauto.
        all : apply wf_rfE in H5; eauto. 
        all : destruct H5 as (x2 & (HH6 & (x3 & (HH9 & HH10)))).
        all : destruct HH10; vauto. }
      rewrite seqA. basic_solver 21. }
    rewrite RF_MAP. rewrite seq_union_l. apply inclusion_union_l.
    { rewrite !seqA. 
      arewrite (m ↑ rf_t ⊆ m ↑ rf_t ⨾ ⦗R_s⦘).
      { rewrite wf_rfD; eauto. intros x y H. unfold collect_rel in H.
        destruct H as (x' & y' & (H1 & H2 & H3)).
        destruct H1 as (x1 & (H5 & H6) & (x2 & (H7 & (H8 & H9)))); subst. 
        unfolder. splits.
        { exists x1, y'. splits; vauto. }
        specialize (LABS y'). unfold compose in LABS.
        apply wf_rfE in H7; vauto.
        destruct H7 as (x3 & (H10 & (x4 & (H11 & H12)))).
        destruct H12; subst. apply LABS in H0.
        unfold is_r in *. basic_solver. }
      arewrite ((⦗R_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ sb_s ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘) 
              ⊆ ⦗R_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ rpo_s ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘).
        { unfold rpo; unfold rpo_imm. rewrite <- ct_step. basic_solver 21. }
      arewrite (rpo_s ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘ ⨾ ⦗E_s \₁ eq a⦘ 
                ⊆ rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘) by basic_solver.
      do 2 rewrite <- seqA. rewrite <- seqA with (r3 := ⦗F_s⦘ ⨾ ⦗Acq_s⦘).
      rewrite RPO_MAP. rewrite !seqA.
      intros x y H. unfold seq at 1 in H. destruct H as (z & H & H').
      destruct H' as (z1 & H0 & (z2 & H1 & (z3 & H2 & (z4 & H3 & (z5 & H4))))).
      destruct H0, H1, H3; subst. 
      unfold collect_rel in H, H2.
      destruct H as (x0 & z0 & (HH0 & HH1 & HH2)); subst.
      destruct H2 as (z1 & y0 & (HH3 & HH4 & HH5)); subst.
      unfold collect_rel. exists x0, y0. splits; vauto.
      unfold seq at 1. exists z0. splits; vauto.
      unfold seq. exists z1. 
      assert (ZE : E_t z0).
      { apply wf_rfE in HH0; vauto.
        destruct HH0 as (x1 & (HH6 & (x2 & (HH9 & HH10)))).
        destruct HH10; vauto. }
      assert (ZEQ : z0 = z1).
      { apply INJ; vauto.
        apply wf_rpoE in HH3; vauto.
        destruct HH3 as (x1 & (HH6 & (x2 & (HH9 & HH10)))).
        destruct HH6; vauto. }
      subst. splits; vauto. 
      { red. splits; vauto.
        apply LABS in ZE. unfold compose in ZE. 
        unfold is_rlx in *. unfold mod in *.
        basic_solver 21. }
      exists y0. splits; vauto.
      { apply rpo_in_sb in HH3; vauto. }
      exists y0.
      assert (EY : E_t y0).
      { apply wf_rpoE in HH3; vauto.
        destruct HH3 as (x1 & (HH6 & (x2 & (HH9 & HH10)))).
        destruct HH10; vauto. }
      splits; vauto.
      { apply LABS in EY. unfold compose in EY.
        unfold is_f in *. basic_solver 21. }
      apply LABS in EY. unfold compose in EY.
      unfold is_acq in *. unfold mod in *. 
      basic_solver 21. }
    rewrite !seqA.
    arewrite (⦗eq a⦘ ⊆ ⦗eq a⦘ ⨾ ⦗fun a0 : actid => is_r lab_s a0⦘).
    { unfold is_r in IS_R. basic_solver. }
    arewrite ((⦗R_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ sb_s ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘) ⊆ rpo_s).
    { unfold rpo; unfold rpo_imm. rewrite <- ct_step. basic_solver 21. }
    destruct CODOM_RPO. unfold codom_rel in H.
    assert (EMP : ⦗eq a⦘ ⨾ rpo_s ≡ ∅₂).
    { split; [|clear; basic_solver].
      intros x y HH. destruct H with y; exists x; vauto. }
    destruct EMP. rewrite <- seqA with (r3 := ⦗E_s \₁ eq a⦘).
    rewrite H1. basic_solver.
Qed.

Lemma sw_sub_helper (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
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
    intros x y H. unfold seq. exists x. split; vauto.
    split; vauto. split. 
    { apply wf_swE in H; eauto. destruct H. destruct H.
      apply H. }
    assert (CODOM : codom_rel (⦗eq a⦘ ⨾ sw_s) ≡₁ ∅).
    { apply codom_sw with (m := m); eauto. }
    intros F. subst. 
    assert (VERT : eq y ⊆₁ codom_rel (⦗eq x⦘ ⨾ sw_s)).
    { intros z HH. subst. basic_solver 12. }
    destruct CODOM. rewrite <- VERT in H0.
    destruct H0 with (x := y); vauto. }
  rewrite START. rewrite seqA. 
  unfold sw. rewrite !seqA.
  rewrite <- seqA.
  rewrite sw_helper_release; eauto.
  rewrite sw_helper_rf; eauto.
  rewrite <- collect_rel_seq; vauto.
  2 : { assert (IN1 : codom_rel (⦗E_t⦘ ⨾ release_t) ⊆₁ E_t).
        { rewrite wf_releaseE; vauto. rewrite seq_union_r. basic_solver. }
        assert (IN2 : dom_rel (rf_t ⨾ ⦗fun a0 : actid => is_rlx lab_t a0⦘ ⨾ (sb_t ⨾ ⦗fun a0 : actid => F_t a0⦘)^? ⨾ ⦗fun a0 : actid => Acq_t a0⦘) ⊆₁ E_t).
        { induction 1. destruct H. destruct H.
          apply wf_rfE in H; eauto. destruct H. destruct H. 
          destruct H; vauto. }
        rewrite IN1, IN2. basic_solver. }
  basic_solver 21.
Qed.

Lemma sw_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
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
    sw_s ⊆ m ↑ sw_t ∪ sw_s ⨾ ⦗eq a⦘.
Proof using.
    rewrite <- sw_sub_helper; eauto.
    rewrite wf_swE; eauto. rewrite !seqA.
    rewrite <- !seq_union_r.
    do 2 hahn_frame_l. intros x y H.
    destruct H as (z & H); subst.
    unfold seq. exists y; eauto.
    split; vauto. unfold union.
    destruct classic with (P := eq y a); vauto.
    left. unfold set_minus. split; vauto.
    split; vauto. basic_solver.
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

Lemma rhb_codom (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (IS_R : is_r lab_s a)
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
    assert (EMP4 : codom_rel (⦗eq a⦘ ⨾ sb_s ∩ same_loc_s) ≡₁ ∅).
    { vauto. }
    assert (EMP5 : codom_rel ((⦗eq a⦘ ⨾ sb_s ∩ same_loc_s) ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)＊) ≡₁ ∅).
    { apply empty_seq_codom; eauto. }
    rewrite EMP1, EMP3, EMP5. basic_solver.
Qed.

Lemma rhb_start (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
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
    split; [basic_solver|].
    hahn_frame_r. unfold rhb. rewrite ct_begin. hahn_frame_r.
    rewrite !seq_union_r. apply union_mori.
    { apply union_mori.
      { intros x y H. unfold seq. exists x. split; vauto. 
        red; split; vauto. assert (H' : (sb_s ∩ same_loc_s) x y) by apply H.
        destruct H. apply wf_sbE in H.
        destruct H. destruct H. destruct H; subst.
        unfold set_minus; split; vauto.
        intros F; subst. unfold codom_rel in CODOM_SB_SL.
        destruct CODOM_SB_SL. destruct H with y.
        exists x0. split with x0. split; vauto. }
      intros x y H. unfold seq. exists x. split; vauto.
      red; split; vauto. assert (H' : (rpo_s) x y) by apply H.
      apply wf_rpoE in H; vauto. destruct H. destruct H. destruct H; subst.
      unfold set_minus; split; vauto.
      intros F; subst. unfold codom_rel in CODOM_RPO.
      destruct CODOM_RPO. destruct H with y.
      exists x0. split with x0. split; vauto. }
    intros x y H. unfold seq. exists x. split; vauto.
    red; split; vauto. assert (H' : (sw_s) x y) by apply H.
    apply wf_swE in H; vauto. destruct H. destruct H. destruct H; subst.
    unfold set_minus; split; vauto.
    intros F; subst. apply wf_swD in H'; vauto.
    destruct H'. destruct H. 
    destruct H; subst. destruct H3.
    destruct H.
    { unfold is_f, is_w, is_r in *. desf. }
    unfold is_f, is_w, is_r in *. desf.
Qed.

Lemma rhb_imm_start (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
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
    split; [basic_solver|]. 
    rewrite !seq_union_r. apply union_mori.
    { apply union_mori.
      { intros x y H. unfold seq. exists x. split; vauto. 
        red; split; vauto. assert (H' : (sb_s ∩ same_loc_s) x y) by apply H.
        destruct H. apply wf_sbE in H.
        destruct H. destruct H. destruct H; subst.
        unfold set_minus; split; vauto.
        intros F; subst. unfold codom_rel in CODOM_SB_SL.
        destruct CODOM_SB_SL. destruct H with y.
        exists x0. split with x0. split; vauto. }
      intros x y H. unfold seq. exists x. split; vauto.
      red; split; vauto. assert (H' : (rpo_s) x y) by apply H.
      apply wf_rpoE in H; vauto. destruct H. destruct H. destruct H; subst.
      unfold set_minus; split; vauto.
      intros F; subst. unfold codom_rel in CODOM_RPO.
      destruct CODOM_RPO. destruct H with y.
      exists x0. split with x0. split; vauto. }
    intros x y H. unfold seq. exists x. split; vauto.
    red; split; vauto. assert (H' : (sw_s) x y) by apply H.
    apply wf_swE in H; vauto. destruct H. destruct H. destruct H; subst.
    unfold set_minus; split; vauto.
    intros F; subst. apply wf_swD in H'; vauto.
    destruct H'. destruct H. 
    destruct H; subst. destruct H3.
    destruct H.
    { unfold is_f, is_w, is_r in *. desf. }
    unfold is_f, is_w, is_r in *. desf.
Qed.

Lemma rhb_fin (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
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
      { rewrite SB_SL_MAP. basic_solver. }
      rewrite RPO_MAP. basic_solver. }
    rewrite sw_sub_helper; eauto.
    basic_solver.
Qed.

Lemma rhb_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
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
    { rewrite rhb_fin; vauto. intros x y HH. unfold collect_rel in *. 
      destruct HH as (x' & y' & (H1 & H2 & H3)). exists x', y'. splits; vauto. }
    assert (IND2 : m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺ ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘
                  ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺).
    { assert (TRIN : m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺ ⨾ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺ 
              ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺).
      { intros x y HH. destruct HH. destruct H.
        unfold collect_rel in H, H0. unfold collect_rel.
        destruct H as (x' & y' & (H1 & H2 & H3)).
        destruct H0 as (x'' & y'' & (H4 & H5 & H6)).
        exists x', y''. splits; vauto.
        assert (EQ : x'' = y'). 
        { apply INJ; vauto. 
          { apply ct_begin in H4. destruct H4. destruct H.
            apply wf_rhb_immE in H; vauto. destruct H. destruct H.
            apply H. }
          apply ct_end in H1. destruct H1. destruct H.
          apply wf_rhb_immE in H0; vauto. destruct H0. destruct H0.
          destruct H1. destruct H1. 
          destruct H2; subst; vauto. }
        subst. apply ct_ct.
        unfold seq. exists y'. splits; vauto. }
      rewrite <- TRIN at 2. apply seq_mori; vauto. }
    assert (IND3 : ((sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘)⁺
                  ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺).
    { apply inclusion_t_ind_right; vauto. }
    assert (IND4 : (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)⁺ ⨾ ⦗E_s \₁ eq a⦘ ⊆ 
                  ((sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘)⁺).
    { induction 1. destruct H. destruct H0; subst.
      induction H. 
      { apply ct_step. unfold seq. exists y. splits; vauto. }
      apply ct_begin in H0. destruct H0. destruct H0.
      eapply rhb_imm_start in H0; vauto.
      destruct H0. destruct H0.
      destruct H0; subst.
      apply IHclos_trans1 in H4.
      apply IHclos_trans2 in H1.
      apply ct_ct. unfold seq. exists x1. splits; vauto. }
    rewrite IND4; vauto.
Qed.

Lemma read_extent (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_R : is_r lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (CO_MAP : co_s ≡ m ↑ co_t)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    WCore.is_cons G_s sc_s.
Proof using.
    assert (MAPEQ : E_s \₁ eq a ≡₁ m ↑₁ E_t).
    { apply acts_set_helper; eauto; basic_solver. }
    constructor.
    { case_refl _.
        { rewrite hb_helper; eauto. rewrite irreflexive_union. split.
          { apply sb_irr; eauto. }
          intros x H. destruct classic with (P := (E_s \₁ eq a) x) as [EQ | EQ].
          { assert (VERT : (rhb_s ⨾ ⦗E_s \₁ eq a⦘) x x).
            { do 2 unfold seq. exists x; split; vauto. }
            assert (VERT' : (m ↑ rhb_t) x x).
            { apply rhb_sub; eauto. }
            assert (IRR : irreflexive rhb_t).
            { apply irreflexive_inclusion with (r' := hb_t); eauto.
              apply rhb_in_hb; eauto. destruct CONS. apply hb_irr; eauto. }
            assert (REST : (rhb_t) ≡ restr_rel E_t (rhb_t)).
            { rewrite restr_relE. rewrite wf_rhbE; eauto.
              basic_solver 21. }
            assert (IRR' : irreflexive (restr_rel E_t (rhb_t))).
            { rewrite <- REST. apply IRR. }
            assert (IRR'' : irreflexive (m ↑ restr_rel E_t rhb_t)).
            { apply collect_rel_irr_inj; eauto. }
            rewrite <- REST in IRR''. basic_solver. }
          assert (EQA : eq a x). 
          { assert (ALTNIN : ~ (m ↑₁ E_t) x). 
            { intros NEG. apply acts_set_helper in NEG; eauto. }
            unfold set_minus in EQ. apply not_and_or in EQ.
            destruct EQ. 
            { assert (G : rhb_s ≡ ⦗E_s⦘ ⨾ rhb_s ⨾ ⦗E_s⦘).
              { rewrite wf_rhbE; eauto. basic_solver. }
            apply G in H. exfalso. apply H0. destruct H. destruct H. apply H. }
            unfold not in H0. destruct classic with (P := eq a x) as [EQ' | EQ'].
            { basic_solver. }
            exfalso. apply H0. basic_solver. }
          rewrite <- EQA in H. destruct rhb_codom with (m := m); eauto.
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
          { rewrite <- seqA. rewrite rhb_sub; eauto; basic_solver. }
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
            rewrite REST. apply collect_rel_irr_inj with (rr := rhb_t ⨾ eco_t); eauto. }
        { rotate 1. eapply empty_irr.
          split; try basic_solver.
          intros x y H. destruct H. destruct H. destruct H0. destruct H0.
          assert (F : (⦗eq a⦘ ⨾ rhb_s) x x1).
          { unfold seq. exists x0. split; auto. }
          assert (T : codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅).
          { apply rhb_codom with (m := m); eauto. }
          assert (Q : ∅ x1). apply T. basic_solver.
          destruct Q. }
        { rotate 1. apply empty_irr.
          split; try basic_solver.
          intros x y H. destruct H. destruct H. destruct H0. destruct H0.
          assert (F : (⦗eq a⦘ ⨾ rhb_s) x x1).
          { unfold seq. exists x0. split; auto. }
          assert (T : codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅). 
          { apply rhb_codom with (m := m); eauto. }
          assert (Q : ∅ x1). apply T. basic_solver.
          destruct Q. }
        { rotate 1. apply empty_irr.
          split; try basic_solver.
          intros x y H. destruct H. destruct H. destruct H0. destruct H0.
          assert (F : (⦗eq a⦘ ⨾ rhb_s) x x1).
          { unfold seq. exists x0. split; auto. }
          assert (T : codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅).
          { apply rhb_codom with (m := m); eauto. }
          assert (Q : ∅ x1). apply T. basic_solver.
          destruct Q. }
    assert (IN' : rhb_s ⨾ (srf_s ⨾ ⦗eq a⦘)⁻¹ ⨾ co_s ⨾ rf_s^? ⊆ rhb_s ⨾ (srf_s ⨾ ⦗eq a⦘)⁻¹ ⨾ co_s ⨾ ⦗W_s⦘ ⨾ rf_s^? ).
    { rewrite wf_coD; eauto. basic_solver 21. } rewrite IN'.
    rotate 3. assert (IN : co_s ⨾ ⦗W_s⦘ ⨾ rf_s^? ⨾ rhb_s ⨾ (srf_s ⨾ ⦗eq a⦘)⁻¹
                            ⊆ co_s ⨾ vf_s ⨾ (srf_s ⨾ ⦗eq a⦘)⁻¹).
      { rewrite <- rf_rhb_sub_vf; basic_solver. }
    rewrite IN. arewrite_id ⦗eq a⦘. rels. unfold srf. basic_solver 21. }
    { split; try basic_solver. rewrite RMW_MAP; eauto. 
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
        { rewrite <- collect_rel_interEE; eauto.
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
    admit. (* sc *)
Admitted. 

(*MAX-WRITE-EXTENDED*)

Lemma write_fr_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    fr_s ⊆ m ↑ fr_t ∪ m ↑ rf_t⁻¹ ⨾ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a.
Proof using.
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

Lemma write_eco_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    eco_s ⊆ m ↑ eco_t 
          ∪ (((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a) ⨾ rf_s^?
          ∪ (m ↑ rf_t⁻¹) ⨾ (((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a) ⨾ rf_s^?.
Proof using.
    unfold eco. repeat rewrite collect_rel_union. rewrite RF_MAP.
    repeat apply inclusion_union_l.
    { repeat left; vauto. }
    { rewrite CO_MAP. rewrite seq_union_l. apply inclusion_union_l.
      { case_refl _.
        { rewrite crE. rewrite seq_union_r.
          rewrite collect_rel_union. rewrite <- !unionA. rels.
          do 4 left. right. vauto. }
        rewrite crE. rewrite seq_union_r.
        rewrite collect_rel_union. rewrite <- !unionA. rels.
        rewrite collect_rel_seq with (rr := co_t) (rr' := rf_t).
        { do 3 left. right. vauto. }
        assert (IN1 : codom_rel co_t ⊆₁ E_t).
        { rewrite wf_coE; eauto. basic_solver. }
        assert (IN2 : dom_rel rf_t ⊆₁ E_t).
        { rewrite wf_rfE; eauto. basic_solver. }
        rewrite IN1, IN2. basic_solver. }
      rewrite crE. rewrite seq_union_r.
      apply inclusion_union_l.
      { rels. }
      rewrite <- !unionA. rewrite !seq_union_r.
      rewrite <- !unionA. do 2 left. right; vauto. }
    rewrite write_fr_sub; vauto.
    rewrite seq_union_l. apply inclusion_union_l.
    { rewrite crE. rewrite seq_union_r.
      apply inclusion_union_l.
      { rels. do 2 left. right. unfold collect_rel.
        destruct H as (x0 & y0 & (H1 & H2 & H3)). 
        exists x0, y0. splits; vauto. 
        unfold seq. exists y0. splits; vauto. }
      do 2 left. right. unfold collect_rel.
      destruct H as (z & ((x0' & z0' & (H1 & H2 & H3)) &
                                 x0 & (z0 & H4 & (H5 & H6)))). 
      exists x0', z0. splits; vauto. 
      unfold seq. exists z0'. splits; vauto. 
      assert (EQ : x0 = z0').
      { apply INJ; vauto.
        { apply wf_rfE in H4; vauto.
          destruct H4. destruct H. apply H. }
        apply wf_frE in H1; vauto.
        destruct H1. destruct H.
        destruct H0. destruct H0.
        destruct H1; vauto. }
      subst. vauto. }
    rewrite seqA; right; basic_solver 8.
Qed.

Lemma write_codom_sw (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    codom_rel (⦗eq a⦘ ⨾ sw_s) ≡₁ ∅.
Proof using.
    split; vauto.
    unfold sw. unfold release. unfold rs.
    arewrite_id ⦗Rel_s⦘; rels.
    rewrite crE. intros x H.
    destruct H. destruct H. destruct H.
    destruct H; subst. apply seq_union_l in H0.
    destruct H0.
    { destruct H. destruct H. destruct H; subst.
      destruct H0. destruct H. destruct H; subst.
      destruct H0. destruct H. destruct H; subst.
      destruct H0. destruct H. 
      apply rtE in H. destruct H.
      { destruct H; subst. destruct H0. destruct H.
        apply RF_MAP in H. unfold collect_rel in H.
        destruct H as (x' & y' & (HH1 & HH2 & HH3)).
        apply wf_rfE in HH1; vauto. destruct HH1. destruct H.
        destruct H; subst. destruct NIN with (m x0); vauto. }
      apply ct_begin in H. destruct H. destruct H.
      destruct H. destruct H.
      apply RF_MAP in H. unfold collect_rel in H.
      destruct H as (x' & y' & (HH1 & HH2 & HH3)).
      apply wf_rfE in HH1; vauto. destruct HH1. destruct H.
      destruct H; subst. destruct NIN with (m x0); vauto. }
    destruct H. destruct H. destruct H. destruct H.
    destruct H; subst. mode_solver.
Qed.

Lemma write_sw_helper_rf_rmw (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    rf_s ⨾ rmw_s ≡ m ↑ (rf_t ⨾ rmw_t).
Proof using.
    rewrite RF_MAP, RMW_MAP. 
    rewrite collect_rel_seq; vauto.
    assert (IN1 : codom_rel rf_t ⊆₁ E_t).
    { rewrite wf_rfE; eauto. basic_solver. }
    assert (IN2 : dom_rel rmw_t ⊆₁ E_t).
    { rewrite wf_rmwE; eauto. basic_solver. }
    rewrite IN1, IN2. basic_solver.
Qed.

Lemma write_sw_helper_release (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
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
    { apply rtE in HREL. destruct HREL.
      { destruct H. subst; eauto. }
      apply ct_end in H. destruct H as (y0 & (H2 & (y1 & (H3 & H4)))).
      apply RMW_MAP in H4. unfold collect_rel in H4. 
      destruct H4 as (y2 & y3 & (H5 & H6 & H7)).
      apply wf_rmwE in H5; vauto. destruct H5. destruct H.
      destruct H0. destruct H0. destruct H1; subst.
      apply MAPEQ; vauto. }
    apply MAPEQ in XIN. apply MAPEQ in YIN.
    destruct XIN as (x' & XIN & XEQ), YIN as (y' & YIN & YEQ).
    exists x', y'. splits; ins. split with x'; split.
    { unfolder. unfolder in DOM. desf.
      unfold is_w, is_rel, is_rlx, mod in *.
      rewrite <- LABS with x'; eauto. }
    assert (HREL' : singl_rel x y ⊆ (rf_s ⨾ rmw_s)＊).
    { intros x0 y0 HH. destruct HH; vauto. }
    rewrite RF_MAP in HREL'. 
    rewrite RMW_MAP in HREL'.
    rewrite <- collect_rel_seq in HREL'.
    2: { assert (IN1 : codom_rel rf_t ⊆₁ E_t).
        { rewrite wf_rfE; eauto. basic_solver. }
        assert (IN2 : dom_rel rmw_t ⊆₁ E_t).
        { rewrite wf_rmwE; eauto. basic_solver. }
        rewrite IN1, IN2. basic_solver. }
    apply rtE in HREL. destruct HREL.
    { destruct H. subst. 
      assert (EQ : x' = y').
      { apply INJ; vauto. }
      subst. apply rtE; left. basic_solver. }
    apply rtE. right. 
    assert (TREQ : (rf_s ⨾ rmw_s)⁺ ⊆ (m ↑ (rf_t ⨾ rmw_t))⁺).
    { apply clos_trans_mori; apply write_sw_helper_rf_rmw; eauto. }
    apply TREQ in H. 
    assert (REST : (rf_t ⨾ rmw_t) ≡ restr_rel E_t (rf_t ⨾ rmw_t)).
    { rewrite restr_relE. rewrite wf_rfE, wf_rmwE; eauto.
      basic_solver 21. }
    assert (TREQ' : (m ↑ (rf_t ⨾ rmw_t))⁺ ≡ (m ↑ restr_rel E_t (rf_t ⨾ rmw_t))⁺).
    { split; apply clos_trans_mori; rewrite <- REST; vauto. }
    apply TREQ' in H. apply collect_rel_ct_inj in H; vauto.
    unfold collect_rel in H. destruct H as (x0 & y0 & (H1 & H2 & H3)).
    assert (TREQ'' : (restr_rel E_t (rf_t ⨾ rmw_t))⁺ ⊆ (rf_t ⨾ rmw_t)⁺).
    { apply clos_trans_mori; basic_solver. }
    apply TREQ'' in H1. 
    assert (X0IN : E_t x0).
    { apply ct_begin in H1. destruct H1. destruct H.
      destruct H. destruct H. apply wf_rfE in H; vauto.
      destruct H. destruct H. apply H. }
    assert (Y0IN : E_t y0).
    { apply ct_end in H1. destruct H1. destruct H.
      destruct H0. destruct H0.
      apply wf_rmwE in H1; vauto.
      destruct H1. destruct H1.
      destruct H4. destruct H4.
      destruct H5; vauto. }
    assert (EQXX : x0 = x').
    { apply INJ; vauto. }
    assert (EQYY : y0 = y').
    { apply INJ; vauto. }
    vauto. }
  assert (sb_t ∩ same_loc_t ≡ ⦗E_t⦘ ⨾ sb_t ∩ same_loc_t ⨾ ⦗E_t⦘) as EAA.
  { split; [|clear; basic_solver 10].
    rewrite wf_sbE at 1. clear. basic_solver 10. }
  assert (sb_s ∩ same_loc_s ≡ ⦗E_s⦘ ⨾ sb_s ∩ same_loc_s ⨾ ⦗E_s⦘) as EAA'.
  { split; [|clear; basic_solver 10].
    rewrite wf_sbE at 1. clear. basic_solver 10. }
  unfold rs. rels. rewrite !seqA.
  arewrite ((⦗Rel_s⦘ ⨾ ⦗F_s⦘ ⨾ sb_s ⨾ ⦗W_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘) 
          ⊆ ⦗Rel_s⦘ ⨾ ⦗F_s⦘ ⨾ rpo_s ⨾ ⦗W_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘).
    { unfold rpo; unfold rpo_imm. rewrite <- ct_step. basic_solver 21. }
  rewrite rtE.
  admit. 
Admitted.

Lemma write_sw_helper_rf (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
  rf_s ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ (sb_s ⨾ ⦗F_s⦘)^? ⨾ ⦗Acq_s⦘ ⨾ ⦗E_s \₁ eq a⦘
    ⊆ m ↑ (rf_t ⨾ ⦗fun a0 : actid => is_rlx lab_t a0⦘⨾ (sb_t ⨾ ⦗F_t⦘)^? ⨾ ⦗Acq_t⦘).
Proof using.
  assert (MAPEQ : E_s \₁ eq a ≡₁ m ↑₁ E_t) by now apply acts_set_helper.
  rewrite !crE. rewrite !seq_union_l.
  rewrite !seq_union_r. rewrite collect_rel_union.
  apply union_mori.
  { rewrite RF_MAP. 
    rels. rewrite MAPEQ. intros x y HH.
    destruct HH as (z & (HH & (y' & (H1 & (z' & (H2 & H3)))))).
    destruct H1, H2, H3; subst. unfolder.
    destruct HH. destruct H.
    destruct H as (H5 & H6 & H7). 
    exists x0, x1. splits; vauto.
    all : unfold is_acq, is_rlx, mod in *.
    all : rewrite <- LABS with x1; splits; eauto.
    all : apply wf_rfE in H5; eauto. 
    all : destruct H5 as (x2 & (HH6 & (x3 & (HH9 & HH10)))).
    all : destruct HH10; vauto. }
  rewrite RF_MAP. 
  rewrite !seqA. 
  arewrite (m ↑ rf_t ⊆ m ↑ rf_t ⨾ ⦗R_s⦘).
  { rewrite wf_rfD; eauto. intros x y H. unfold collect_rel in H.
    destruct H as (x' & y' & (H1 & H2 & H3)).
    destruct H1 as (x1 & (H5 & H6) & (x2 & (H7 & (H8 & H9)))); subst. 
    unfolder. splits.
    { exists x1, y'. splits; vauto. }
    specialize (LABS y'). unfold compose in LABS.
    apply wf_rfE in H7; vauto.
    destruct H7 as (x3 & (H10 & (x4 & (H11 & H12)))).
    destruct H12; subst. apply LABS in H0.
    unfold is_r in *. basic_solver. }
  arewrite ((⦗R_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ sb_s ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘) 
          ⊆ ⦗R_s⦘ ⨾ ⦗fun a0 : actid => is_rlx lab_s a0⦘ ⨾ rpo_s ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘).
    { unfold rpo; unfold rpo_imm. rewrite <- ct_step. basic_solver 21. }
  arewrite (rpo_s ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘ ⨾ ⦗E_s \₁ eq a⦘ 
            ⊆ rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⨾ ⦗F_s⦘ ⨾ ⦗Acq_s⦘) by basic_solver.
  do 2 rewrite <- seqA. rewrite <- seqA with (r3 := ⦗F_s⦘ ⨾ ⦗Acq_s⦘).
  rewrite RPO_MAP. rewrite !seqA.
  intros x y H. unfold seq at 1 in H. destruct H as (z & H & H').
  destruct H' as (z1 & H0 & (z2 & H1 & (z3 & H2 & (z4 & H3 & (z5 & H4))))).
  destruct H0, H1, H3; subst. 
  unfold collect_rel in H, H2.
  destruct H as (x0 & z0 & (HH0 & HH1 & HH2)); subst.
  destruct H2 as (z1 & y0 & (HH3 & HH4 & HH5)); subst.
  unfold collect_rel. exists x0, y0. splits; vauto.
  unfold seq at 1. exists z0. splits; vauto.
  unfold seq. exists z1. 
  assert (ZE : E_t z0).
  { apply wf_rfE in HH0; vauto.
    destruct HH0 as (x1 & (HH6 & (x2 & (HH9 & HH10)))).
    destruct HH10; vauto. }
  assert (ZEQ : z0 = z1).
  { apply INJ; vauto.
    apply wf_rpoE in HH3; vauto.
    destruct HH3 as (x1 & (HH6 & (x2 & (HH9 & HH10)))).
    destruct HH6; vauto. }
  subst. splits; vauto. 
  { red. splits; vauto.
    apply LABS in ZE. unfold compose in ZE. 
    unfold is_rlx in *. unfold mod in *.
    basic_solver 21. }
  exists y0. splits; vauto.
  { apply rpo_in_sb in HH3; vauto. }
  exists y0.
  assert (EY : E_t y0).
  { apply wf_rpoE in HH3; vauto.
    destruct HH3 as (x1 & (HH6 & (x2 & (HH9 & HH10)))).
    destruct HH10; vauto. }
  splits; vauto.
  { apply LABS in EY. unfold compose in EY.
    unfold is_f in *. basic_solver 21. }
  apply LABS in EY. unfold compose in EY.
  unfold is_acq in *. unfold mod in *. 
  basic_solver 21. 
Qed.

Lemma write_sw_sub_helper (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    sw_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ sw_t.
Proof using.
  assert (MAPEQ : E_s \₁ eq a ≡₁ m ↑₁ E_t) by now apply acts_set_helper.
  assert (START : sw_s ≡ ⦗E_s \₁ eq a⦘ ⨾ sw_s).
  { unfold set_minus. split; [|basic_solver].
    intros x y H. unfold seq. exists x. split; vauto.
    split; vauto. split. 
    { apply wf_swE in H; eauto. destruct H. destruct H.
      apply H. }
    assert (CODOM : codom_rel (⦗eq a⦘ ⨾ sw_s) ≡₁ ∅).
    { apply write_codom_sw with (m := m); eauto. }
    intros F. subst. 
    assert (VERT : eq y ⊆₁ codom_rel (⦗eq x⦘ ⨾ sw_s)).
    { intros z HH. subst. basic_solver 12. }
    destruct CODOM. rewrite <- VERT in H0.
    destruct H0 with (x := y); vauto. }
  rewrite START. rewrite seqA. 
  unfold sw. rewrite !seqA.
  rewrite <- seqA.
  rewrite write_sw_helper_release; eauto.
  rewrite write_sw_helper_rf; eauto.
  rewrite <- collect_rel_seq; vauto.
  2 : { assert (IN1 : codom_rel (⦗E_t⦘ ⨾ release_t) ⊆₁ E_t).
        { rewrite wf_releaseE; vauto. rewrite seq_union_r. basic_solver. }
        assert (IN2 : dom_rel (rf_t ⨾ ⦗fun a0 : actid => is_rlx lab_t a0⦘ ⨾ (sb_t ⨾ ⦗fun a0 : actid => F_t a0⦘)^? ⨾ ⦗fun a0 : actid => Acq_t a0⦘) ⊆₁ E_t).
        { induction 1. destruct H. destruct H.
          apply wf_rfE in H; eauto. destruct H. destruct H. 
          destruct H; vauto. }
        rewrite IN1, IN2. basic_solver. }
  basic_solver 21.
Qed.

Lemma write_sw_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    sw_s ⊆ m ↑ sw_t ∪ sw_s ⨾ ⦗eq a⦘.
Proof using.
  rewrite <- write_sw_sub_helper; eauto.
  rewrite wf_swE; eauto. rewrite !seqA.
  rewrite <- !seq_union_r.
  do 2 hahn_frame_l. intros x y H.
  destruct H as (z & H); subst.
  unfold seq. exists y; eauto.
  split; vauto. unfold union.
  destruct classic with (P := eq y a); vauto.
  left. unfold set_minus. split; vauto.
  split; vauto. basic_solver.
Qed.

Lemma write_rhb_codom (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅.
Proof using.
  unfold rhb. rewrite ct_begin. rewrite <- seqA. rewrite !seq_union_r.
  rewrite !seq_union_l. rewrite !codom_union.
  assert (EMP1 : codom_rel ((⦗eq a⦘ ⨾ rpo_s) ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)＊) ≡₁ ∅).
  { apply empty_seq_codom; eauto. }
  assert (EMP2 : codom_rel (⦗eq a⦘ ⨾ sw_s) ≡₁ ∅).
  { split; [|basic_solver]. rewrite write_sw_sub; eauto.
    unfold codom_rel. intros x H. destruct H.
    destruct H. destruct H. 
    assert (IN : (m ↑₁ E_t) x1).
    { destruct H0.
      { destruct H0. destruct H0. destruct H0. destruct H1.
        unfold set_collect. exists x2. split; vauto. 
        apply wf_swE in H0; vauto. destruct H0. 
        destruct H0. apply H0. }
      destruct H0. destruct H0.
      assert (PATH : (⦗eq a⦘ ⨾ sw_s) x0 x2).
      { unfold seq. exists x1. split; vauto. }
      destruct write_codom_sw with (m := m); vauto.
      destruct H2 with x2. basic_solver. }
    apply acts_set_helper in IN; eauto.
    destruct H. desf. destruct IN. basic_solver. }
  assert (EMP3 : codom_rel ((⦗eq a⦘ ⨾ sw_s) ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)＊) ≡₁ ∅).
  { apply empty_seq_codom; eauto. }
  assert (EMP4 : codom_rel (⦗eq a⦘ ⨾ sb_s ∩ same_loc_s) ≡₁ ∅).
  { vauto. }
  assert (EMP5 : codom_rel ((⦗eq a⦘ ⨾ sb_s ∩ same_loc_s) ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)＊) ≡₁ ∅).
  { apply empty_seq_codom; eauto. }
  rewrite EMP1, EMP3, EMP5. basic_solver.
Qed.

Lemma write_rhb_start (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    ⦗E_s \₁ eq a⦘ ⨾ rhb_s ⨾ ⦗E_s \₁ eq a⦘ ≡ rhb_s ⨾ ⦗E_s \₁ eq a⦘.
Proof using.
  split; [basic_solver|].
  hahn_frame_r. unfold rhb. rewrite ct_begin. hahn_frame_r.
  rewrite !seq_union_r. apply union_mori.
  { apply union_mori.
    { intros x y H. unfold seq. exists x. split; vauto. 
      red; split; vauto. assert (H' : (sb_s ∩ same_loc_s) x y) by apply H.
      destruct H. apply wf_sbE in H.
      destruct H. destruct H. destruct H; subst.
      unfold set_minus; split; vauto.
      intros F; subst. unfold codom_rel in CODOM_SB_SL.
      destruct CODOM_SB_SL. destruct H with y.
      exists x0. split with x0. split; vauto. }
    intros x y H. unfold seq. exists x. split; vauto.
    red; split; vauto. assert (H' : (rpo_s) x y) by apply H.
    apply wf_rpoE in H; vauto. destruct H. destruct H. destruct H; subst.
    unfold set_minus; split; vauto.
    intros F; subst. unfold codom_rel in CODOM_RPO.
    destruct CODOM_RPO. destruct H with y.
    exists x0. split with x0. split; vauto. }
  intros x y H. unfold seq. exists x. split; vauto.
  red; split; vauto. destruct write_codom_sw with (m := m); vauto.
  unfold set_minus; split. 
  { apply wf_swE in H; vauto. destruct H. destruct H. apply H. }
  intros F; subst. destruct H0 with y. basic_solver 21. 
Qed.

Lemma write_rhb_imm_start (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
  ⦗E_s \₁ eq a⦘ ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ≡ 
    (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s).
Proof using.
  split; [basic_solver|]. 
  rewrite !seq_union_r. apply union_mori.
  { apply union_mori.
    { intros x y H. unfold seq. exists x. split; vauto. 
      red; split; vauto. assert (H' : (sb_s ∩ same_loc_s) x y) by apply H.
      destruct H. apply wf_sbE in H.
      destruct H. destruct H. destruct H; subst.
      unfold set_minus; split; vauto.
      intros F; subst. unfold codom_rel in CODOM_SB_SL.
      destruct CODOM_SB_SL. destruct H with y.
      exists x0. split with x0. split; vauto. }
    intros x y H. unfold seq. exists x. split; vauto.
    red; split; vauto. assert (H' : (rpo_s) x y) by apply H.
    apply wf_rpoE in H; vauto. destruct H. destruct H. destruct H; subst.
    unfold set_minus; split; vauto.
    intros F; subst. unfold codom_rel in CODOM_RPO.
    destruct CODOM_RPO. destruct H with y.
    exists x0. split with x0. split; vauto. }
  intros x y H. unfold seq. exists x. split; vauto.
  red; split; vauto. destruct write_codom_sw with (m := m); vauto.
  unfold set_minus; split. 
  { apply wf_swE in H; vauto. destruct H. destruct H. apply H. }
  intros F; subst. destruct H0 with y. basic_solver 21.
Qed. 

Lemma write_rhb_fin (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t).
Proof using.
    rewrite !seq_union_l.
    rewrite !collect_rel_union.
    apply union_mori.
    { apply union_mori.
      { rewrite SB_SL_MAP. basic_solver. }
        rewrite RPO_MAP. basic_solver. }
    rewrite write_sw_sub_helper; eauto.
    basic_solver.
Qed.

Lemma write_rhb_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    rhb_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rhb_t.
Proof using.
  unfold rhb.
  assert (IND1 : (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘ 
                ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺).
  { rewrite write_rhb_fin; vauto. intros x y HH. unfold collect_rel in *. 
    destruct HH as (x' & y' & (H1 & H2 & H3)). exists x', y'. splits; vauto. }
  assert (IND2 : m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺ ⨾ (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘
                ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺).
  { assert (TRIN : m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺ ⨾ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺ 
            ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺).
    { intros x y HH. destruct HH. destruct H.
      unfold collect_rel in H, H0. unfold collect_rel.
      destruct H as (x' & y' & (H1 & H2 & H3)).
      destruct H0 as (x'' & y'' & (H4 & H5 & H6)).
      exists x', y''. splits; vauto.
      assert (EQ : x'' = y'). 
      { apply INJ; vauto. 
        { apply ct_begin in H4. destruct H4. destruct H.
          apply wf_rhb_immE in H; vauto. destruct H. destruct H.
          apply H. }
        apply ct_end in H1. destruct H1. destruct H.
        apply wf_rhb_immE in H0; vauto. destruct H0. destruct H0.
        destruct H1. destruct H1. 
        destruct H2; subst; vauto. }
      subst. apply ct_ct.
      unfold seq. exists y'. splits; vauto. }
    rewrite <- TRIN at 2. apply seq_mori; vauto. }
  assert (IND3 : ((sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘)⁺
                ⊆ m ↑ (sb_t ∩ same_loc_t ∪ rpo_t ∪ sw_t)⁺).
  { apply inclusion_t_ind_right; vauto. }
  assert (IND4 : (sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s)⁺ ⨾ ⦗E_s \₁ eq a⦘ ⊆ 
                ((sb_s ∩ same_loc_s ∪ rpo_s ∪ sw_s) ⨾ ⦗E_s \₁ eq a⦘)⁺).
  { induction 1. destruct H. destruct H0; subst.
    induction H. 
    { apply ct_step. unfold seq. exists y. splits; vauto. }
    apply ct_begin in H0. destruct H0. destruct H0.
    eapply write_rhb_imm_start in H0; vauto.
    destruct H0. destruct H0.
    destruct H0; subst.
    apply IHclos_trans1 in H4.
    apply IHclos_trans2 in H1.
    apply ct_ct. unfold seq. exists x1. splits; vauto. }
  rewrite IND4; vauto.
Qed.

Lemma write_extent (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (LABS : eq_dom E_t (lab_s ∘ m) lab_t)
        (IS_W : is_w lab_s a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (CODOM_SB_SL : codom_rel (⦗eq a⦘ ⨾ (sb_s ∩ same_loc_s)) ≡₁ ∅)
        (SB_SL_MAP : (sb_s ∩ same_loc_s)⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ (sb_t ∩ same_loc_t))
        (RF_MAP : rf_s ≡ m ↑ rf_t)
        (CO_MAP : co_s ≡ m ↑ co_t ∪ ((W_s \₁ eq a) ∩₁ same_loc_s a) × eq a)
        (RMW_MAP : rmw_s ≡ m ↑ rmw_t)
        (CONS : WCore.is_cons G_t sc_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    WCore.is_cons G_s sc_s.
Proof using.
  constructor.
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
          { apply collect_rel_irr_inj; eauto. }
          rewrite <- REST in IRR''. basic_solver 22. }
        assert (EQA : eq a x). 
        { assert (ALTNIN : ~ (m ↑₁ E_t) x). 
          { intros NEG. apply acts_set_helper in NEG; eauto. }
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
          rewrite REST. apply collect_rel_irr_inj with (rr := rhb_t ⨾ eco_t); eauto. }
      { unfold irreflexive. intros x H. unfold seq in H. destruct H. destruct H.
        destruct H0. destruct H0. 
        assert (EQA : x1 = a).
        { destruct H0; basic_solver. }
        rewrite EQA in H1. destruct H1.
        { destruct write_rhb_codom with (m := m); eauto. 
          subst. destruct H2 with x0.
          basic_solver 21. }
        apply RF_MAP in H1. unfold collect_rel in H1.
        destruct H1 as (x' & y' & (H1 & H2 & H3)).
        destruct NIN with (m x'); eauto.
        apply wf_rfE in H1; eauto.
        destruct H1. destruct H1. destruct H1; subst.
        basic_solver. }
      unfold irreflexive. intros x H. unfold seq in H. destruct H. destruct H.
      destruct H0. destruct H0. destruct H1. destruct H1. 
      assert (EQA : x2 = a).
      { destruct H1; basic_solver. }
      rewrite EQA in H2. destruct H2.
      { destruct write_rhb_codom with (m := m); eauto. 
        subst. destruct H3 with x0.
        basic_solver 21. }
      apply RF_MAP in H2. unfold collect_rel in H2.
      destruct H2 as (x' & y' & (H2 & H3 & H4)).
      destruct NIN with (m x'); eauto.
      apply wf_rfE in H2; eauto.
      destruct H2. destruct H2. destruct H2; subst.
      basic_solver. }
  { split; try basic_solver. rewrite RMW_MAP, CO_MAP; eauto. 
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
      { rewrite <- collect_rel_interEE; eauto.
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

