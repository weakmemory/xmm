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
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.
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
    unfold rhb; unfold hb. rewrite rpo_in_sb; basic_solver.
Qed.

Lemma seqA4 A (r r' r'' r''' : relation A) :
    (r ⨾ r' ⨾ r'') ⨾ r''' ≡ r ⨾ r' ⨾ r'' ⨾ r'''.
Proof using.
    rewrite seqA. rewrite seqA. basic_solver.
Qed.

Lemma sb_trans_sw_in_rpo_sw :
    ⦗(fun a : actid => R a) ∪₁ (fun a : actid => W a)⦘ ⨾ sb⁺ ⨾ sw ⊆ rpo ⨾ sw.
Proof using.
    assert (TRANS : transitive sb). apply sb_trans. 
    assert (SB_TR : sb⁺ ≡ sb). apply ct_of_trans; eauto.
    rewrite SB_TR. unfold rpo. intros x y H. apply seq_union_l; left.
    apply seq_union_l; right. assert (REL_SW : sw ≡ (⦗fun a : actid => is_rel lab a⦘) ⨾ sw).
    { unfold sw. unfold release. basic_solver 21. }
    assert (SAME : ⦗(fun a : actid => R a) ∪₁ (fun a : actid => W a)⦘ ⨾ sb ⨾ sw ≡
                   ⦗(fun a : actid => R a) ∪₁ (fun a : actid => W a)⦘ ⨾ sb ⨾ 
                   (⦗fun a : actid => is_rel lab a⦘) ⨾ sw).
    { rewrite <- REL_SW; eauto. }
    apply SAME in H. apply seqA4. eauto.
Qed.

Lemma sb_rpo_start x x0 y
        (SB : sb x x0)
        (SW : sw x0 y) 
        (RX : ((fun a : actid => R a) ∪₁ (fun a : actid => W a)) x) :
    rpo x x0.
Proof using.
    unfold rpo. left. right.
    destruct SW. destruct H.
    unfold release in H. assert (REL : is_rel lab x0).
    { destruct H. destruct H. destruct H. basic_solver. }
    basic_solver.
Qed.

Lemma trans_union A (r r' : relation A) : 
    (r ∪ r')⁺ ≡ r＊ ⨾ r' ⨾ (r^? ⨾ r'^?)＊.
Proof using.
    admit. 
Admitted.

Lemma hb_helper :
    hb ≡ sb ∪ rhb.
Proof using.
    split.
    2: { rewrite rhb_in_hb; eauto. 
         rewrite inclusion_union_l with 
            (r := sb) (r' := hb) (r'' := hb); try basic_solver.
            unfold hb. rewrite path_ut_last. basic_solver. }
    unfold hb, rhb. intros x y H. apply clos_trans_t1n in H.
    induction H. 
    { destruct H; try basic_solver. right. apply ct_step. basic_solver. }
    destruct H; destruct IHclos_trans_1n. 
    { left. assert (TRANS : transitive sb). apply sb_trans. 
      unfold transitive in TRANS. basic_solver. }
    { induction H0. assert (TRANS : transitive sb). apply sb_trans. 
        { destruct H0.
          { left. unfold transitive in TRANS. basic_solver. }
          destruct classic with 
                (P := (((fun a : actid => R a) ∪₁ (fun a : actid => W a)) x)) as [RX | WX].
          { assert (START1 : (⦗(fun a : actid => R a) ∪₁ (fun a : actid => W a)⦘ ⨾ sb ⨾ sw) x y). basic_solver.
            assert (START2 : (rpo ⨾ sw) x y). 
            { apply sb_trans_sw_in_rpo_sw. basic_solver. }
            unfold seq in START2. destruct START2. destruct H2.
            right. apply ct_begin. unfold seq. exists x1. split. 
            { left; eauto. }
            apply inclusion_t_rt. apply ct_step.
            right; eauto. }
          admit. }
        assert (TRANS : transitive sb). apply sb_trans. 
        unfold transitive in TRANS. destruct classic with 
        (P := (((fun a : actid => R a) ∪₁ (fun a : actid => W a)) x)) as [RX | WX].
        { destruct H0.
          { admit. }
          assert (START : rpo x x0). 
          { apply sb_rpo_start with (y := y); eauto. }
          right. apply ct_begin. unfold seq. exists x0. split.
          { left; eauto. }
          apply inclusion_t_rt; eauto. }
        admit. }
    { admit. }
    right. apply ct_ct. unfold seq. exists y. split; auto.
    apply ct_step. basic_solver.
Admitted.

(* TODO : try without hb_helper *)
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

(* 
Lemma rhb_srf_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) :
    irreflexive (rhb ⨾ srf).
Proof using.
    apply irreflexive_inclusion with (r' := hb ⨾ srf).
    { rewrite hb_helper; basic_solver. }
    rotate 1; apply srf_hb_irr; auto.
Qed.

Lemma vf_hb_hb_irr 
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) :
    irreflexive (vf ⨾ hb ⨾ hb).
Proof using.
    arewrite (vf ⨾ hb ⊆ vf).
    generalize @vf_hb; basic_solver 21.
    apply vf_hb_irr; eauto.
Qed.

Lemma rhb_sb_srf_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) :
    irreflexive (rhb ⨾ sb ⨾ srf^?).
Proof using.
    rewrite rhb_in_hb; eauto. rewrite srf_sub_vf; eauto.
    rewrite sb_in_hb; eauto. case_refl _. 
    2: { rotate 1. apply vf_hb_hb_irr; eauto. }
    generalize (@hb_trans G); ins; relsf.
    apply hb_irr; eauto. apply CONS.
Qed.

Lemma rhb_fr_srf_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) :
    irreflexive (rhb ⨾ fr ⨾ srf^?).
Proof using.
    case_refl _. 
    { rewrite fr_in_eco; eauto. rewrite rhb_in_hb; eauto.
      apply hb_eco_irr; eauto. }
    unfold fr.
Admitted.

Lemma rhb_srf_sb_rf_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) :
    irreflexive (rhb ⨾ srf⁻¹ ⨾ sb ⨾ rf).
Proof using.
    admit.
Admitted. *)

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

Lemma fr_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (MO_MAP : co_s ≡ m ↑ co_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    fr_s ⊆ m ↑ fr_t ∪ srf_s⁻¹ ⨾ co_s.
Proof using.
    unfold fr. rewrite RF_MAP. rewrite transp_union.
    rewrite seq_union_l. rewrite MO_MAP. rewrite transp_seq, seqA.
    rewrite <- collect_rel_transp. arewrite_id ⦗eq a⦘.
    rels. assert (EQ : m ↑ (rf_t⁻¹ ⨾ co_t) ≡ m ↑ rf_t⁻¹ ⨾ m ↑ co_t).
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
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (MO_MAP : co_s ≡ m ↑ co_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    eco_s ⊆ m ↑ eco_t ∪ srf_s ⨾ ⦗eq a⦘ ∪ co_s ⨾ (srf_s ⨾ ⦗eq a⦘) ∪ 
                fr_s ⨾ (srf_s ⨾ ⦗eq a⦘) ∪ (srf_s ⨾ ⦗eq a⦘)⁻¹ ⨾ co_s ⨾ rf_s^?.
Proof using.
    unfold eco. repeat rewrite collect_rel_union.
    repeat apply inclusion_union_l. rewrite RF_MAP.
    apply inclusion_union_l. 1, 2 : basic_solver 21.
    { rewrite MO_MAP. case_refl _.
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
    { unfold fr. rewrite MO_MAP. rewrite RF_MAP. rewrite transp_union. 
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
    unfold fr. rewrite MO_MAP. rewrite RF_MAP.
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
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (MO_MAP : co_s ≡ m ↑ co_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    E_s \₁ eq a ≡₁ m ↑₁ E_t.
Proof using.
    rewrite E_MAP. rewrite set_minus_union_l.
    rewrite set_minusK. rewrite set_union_empty_r.
    apply set_minus_disjoint; eauto.
Qed.

Lemma rhb_sub (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (MO_MAP : co_s ≡ m ↑ co_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    rhb_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rhb_t. 
Proof using.
    unfold rhb. admit. 
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

Lemma rhb_codom (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (MO_MAP : co_s ≡ m ↑ co_t)
        (WF_t : Wf G_t)
        (WF_s : Wf G_s) :
    codom_rel(⦗eq a⦘ ⨾ rhb_s) ≡₁ ∅.
Proof using.
    unfold rhb. rewrite path_ut_first.
    rewrite seq_union_r. rewrite codom_union.
    assert (EMP : codom_rel(⦗eq a⦘ ⨾ rpo_s⁺) ≡₁ ∅).
        { apply codom_ct_alt; eauto. }
    assert (EMP' : codom_rel (⦗eq a⦘ ⨾ rpo_s＊ ⨾ sw_s ⨾ (rpo_s ∪ sw_s)＊) ≡₁ ∅).
        { rewrite <- ct_of_cr. admit. }
    rewrite EMP, EMP'. basic_solver.
Admitted.

Lemma read_extent (m : actid -> actid)
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (NIN : set_disjoint (m ↑₁ E_t) (eq a))
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (MO_MAP : co_s ≡ m ↑ co_t)
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
          { assert (F : (rhb_s ⨾ ⦗E_s \₁ eq a⦘) x x <-> rhb_s x x).
            { unfold seq. split; auto. ins. exists x. split; eauto.
              destruct EQ. basic_solver. }
            apply F in H. assert (F' : (m ↑ rhb_t) x x).
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
            rewrite IN1, IN2. basic_solver. }
          rewrite H. apply irreflexive_inclusion with (r' := m ↑ rhb_t ⨾ m ↑ eco_t); eauto.
          { rewrite <- rhb_sub; eauto. basic_solver. }
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
    all : admit.
Admitted. 

End Draft.

End Consistency. 

