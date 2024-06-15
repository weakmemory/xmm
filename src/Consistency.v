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
            admit. }
        destruct H0. 
        { destruct H2. destruct H2.
            { left. assert (TRANS : transitive sb). apply sb_trans.
              unfold transitive in TRANS. basic_solver. }
            { assert (TRANS : transitive sb). apply sb_trans.
              unfold transitive in TRANS. assert (SB : sb x y). basic_solver.
              apply IHclos_trans_1n in SB. basic_solver. 
              apply ct_step. right. basic_solver. }
            assert (TRANS : transitive sb). apply sb_trans.
            unfold transitive in TRANS. assert (SB : sb x y). basic_solver.
            apply IHclos_trans_1n. basic_solver. admit. }
        admit. }
    { admit. }
    right. apply ct_ct. admit.
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

Lemma rhb_srf_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) :
    irreflexive (rhb ⨾ srf).
Proof using.
    apply irreflexive_inclusion with (r' := hb ⨾ srf).
    { rewrite hb_helper; basic_solver. }
    rotate 1; apply srf_hb_irr; auto.
Qed.

Lemma vf_hb :
    vf ⨾ hb ⨾ hb^? ⊆ vf.
Proof using.
    unfold vf.
    generalize (@hb_trans G); basic_solver 21.
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
Admitted.

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

Lemma rhb_eco_irr_equiv :
    irreflexive (rhb_s ⨾ eco_s) <-> irreflexive (hb_s ⨾ eco_s).
Proof using.
    split. admit.
    intros IR. apply irreflexive_inclusion 
                    with (r' := hb_s ⨾ eco_s); eauto.
    apply inclusion_seq_mon. apply rhb_in_hb; eauto. vauto.
Admitted.

Lemma fr_sub (m : actid -> actid) 
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (MO_MAP : co_s ≡ m ↑ co_t) :  
    fr_s ⊆ m ↑ fr_t ∪ srf_s⁻¹ ⨾ co_s.
Proof using.
    unfold fr. rewrite RF_MAP. rewrite transp_union.
    rewrite seq_union_l. rewrite MO_MAP. rewrite transp_seq, seqA.
    rewrite <- collect_rel_transp. arewrite_id ⦗eq a⦘.
    rels. assert (EQ : m ↑ (rf_t⁻¹ ⨾ co_t) ≡ m ↑ rf_t⁻¹ ⨾ m ↑ co_t).
    { eapply collect_rel_seq. assert (IN1 : codom_rel rf_t⁻¹ ⊆₁ E_t).
      { rewrite codom_transp. induction 1. admit. }
      assert (IN2 : dom_rel co_t ⊆₁ E_t).
      { induction 1. admit. }
      rewrite IN1, IN2. basic_solver. }
    rewrite EQ; basic_solver.
Admitted.

Lemma eco_sub (m : actid -> actid) 
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (MO_MAP : co_s ≡ m ↑ co_t) :  
    eco_s ⊆ m ↑ eco_t ∪ srf_s ∪ co_s ⨾ srf_s^? ∪ fr_s ⨾ srf_s^? ∪ srf_s⁻¹ ⨾ co_s ⨾ rf_s.
Proof using.
    unfold eco. repeat rewrite collect_rel_union. 
    repeat apply inclusion_union_l. rewrite RF_MAP. 
    apply inclusion_union_l. 1, 2 : basic_solver 21.
    { rewrite MO_MAP. case_refl _. 
        { basic_solver 21. }
        rewrite RF_MAP. rewrite seq_union_r.
        apply inclusion_union_l. 2 : basic_solver 21.
        admit. }
    case_refl _. basic_solver 21. unfold fr.
    rewrite MO_MAP. rewrite RF_MAP. admit.
Admitted. 

Lemma rhb_sub (m : actid -> actid) 
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (MO_MAP : co_s ≡ m ↑ co_t) :  
    rhb_s ⊆ m ↑ rhb_t. (*TODO : fix*)
Proof using.
    admit.
Admitted.

Lemma read_extent (m : actid -> actid) 
        (INJ : inj_dom E_t m)
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
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
        { admit. }
        apply rhb_eco_irr_equiv. rewrite eco_sub; eauto.
        repeat rewrite seq_union_r. repeat rewrite irreflexive_union; splits.
        { rewrite rhb_sub; eauto. erewrite <- collect_rel_seq. all: admit. }
    all : admit. }
    all : admit.
Admitted. 

End Draft.

End Consistency. 

