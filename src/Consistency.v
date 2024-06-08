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

(*???????????*)
Definition furr := ⦗W⦘ ⨾ rf^? ⨾ hb^? ⨾ sc^? ⨾ hb^?.
Definition coh_sc sc := irreflexive (sc ⨾ hb ⨾ (eco ⨾ hb)^?).

Lemma furr_hb_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) 
        (CSC  : coh_sc sc) :
    irreflexive (furr ⨾ hb).
Proof using.
    unfold furr. arewrite_id ⦗W⦘. rels. arewrite (rf^? ⊆ eco^?).
    generalize (eco_trans WF); ins; relsf. rewrite (crE sc).
    generalize (@hb_trans G); ins; relsf.
    relsf; repeat (splits; try apply irreflexive_union).
    { rotate 1. destruct CONS. apply cons_coherence. }
    rewrite crE at 1; relsf; repeat (splits; try apply irreflexive_union).
    { rotate 1; relsf; destruct CONS. admit. }
    rewrite crE; relsf; apply irreflexive_union; splits.
    { rewrite (dom_r (wf_ecoD WF)). admit. }
    revert CSC; unfold coh_sc; basic_solver 21.
Admitted. 

Lemma srf_sub_vf 
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) :
    srf ⊆ vf.
Proof using.
    unfold srf. basic_solver. 
Qed.

Lemma furr_hb_sc_hb 
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) 
        (CSC  : coh_sc sc) :
    furr ⨾ hb ⨾ sc^? ⨾ hb^? ⊆ furr.
Proof using.
    admit.
Admitted.

Lemma furr_hb_sc_hb_irr 
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) 
        (CSC  : coh_sc sc) :
  irreflexive (furr ⨾ hb ⨾ (sc ⨾ hb)^?).
Proof using.
    case_refl _. apply furr_hb_irr; eauto.
    arewrite (furr ⨾ hb ⨾ sc ⊆ furr).
    generalize @furr_hb_sc_hb; basic_solver 21.
    apply furr_hb_irr; eauto.
Qed.

Lemma vf_in_furr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) 
        (CSC  : coh_sc sc) :
    vf ⊆ furr.
Proof using.
  destruct CONS. cdes cons_coherence.
  unfold vf; unfold furr; eauto.
  rewrite (dom_l WF.(wf_rfD)) at 1.
  (*???*) admit.
Admitted.

Lemma srf_in_furr 
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) 
        (CSC  : coh_sc sc) :
    srf ⊆ furr.
Proof using. 
    rewrite srf_sub_vf; eauto. 
    apply vf_in_furr; eauto. 
Qed.

Lemma srf_hb_sc_hb_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) 
        (CSC  : coh_sc sc) :
    irreflexive (srf ⨾ hb ⨾ (sc ⨾ hb)^?).
Proof using.
    rewrite srf_in_furr; try apply furr_hb_sc_hb_irr; eauto.
Admitted.

Lemma srf_hb_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) 
        (CSC  : coh_sc sc) :
    irreflexive (srf ⨾ hb).
Proof using.
    generalize srf_hb_sc_hb_irr.
    basic_solver 10.
Qed.

Lemma hb_helper : hb ≡ co ∪ rhb.
Proof using.
    admit.
Admitted.

Lemma hb_locs : hb ∩ same_loc ≡ rhb ∩ same_loc.
Proof using.
    admit. 
Admitted.

Lemma rhb_srf_irr
        (WF  : Wf G)
        (CONS : WCore.is_cons G sc) 
        (CSC  : coh_sc sc) :
    irreflexive (rhb ⨾ srf).
Proof using.
    apply irreflexive_inclusion with (r' := hb ⨾ srf).
    { rewrite hb_helper. basic_solver. }
    rotate 1; apply srf_hb_irr; auto.
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
Notation "'srf_s'" := (srf G_s).

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
Notation "'srf_t'" := (srf G_t).

Lemma read_extent (m : actid -> actid) 
        (TID_MAP : forall x, tid x = tid (m x))
        (LAB_MAP : same_lab_u2v (lab_s ∘ m) lab_t) 
        (E_MAP : E_s ≡₁ m ↑₁ E_t ∪₁ eq a)
        (CODOM_RPO : codom_rel (⦗eq a⦘ ⨾ rpo_s) ≡₁ ∅)
        (RPO_MAP : rpo_s ⨾ ⦗E_s \₁ eq a⦘ ⊆ m ↑ rpo_t)
        (RF_MAP : rf_s ≡ (m ↑ rf_t) ∪ (srf_s ⨾ ⦗eq a⦘))
        (MO_MAP : co_s ≡ m ↑ co_t) :  
    WCore.is_cons G_t sc_t ->  WCore.is_cons G_s sc_s.
Proof using.
    admit.
Admitted.



End Draft.

End Consistency.

