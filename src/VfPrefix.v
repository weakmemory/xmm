From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_hb.
From imm Require Import SubExecution.

From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.

Require Import Srf.

Set Implicit Arguments.

Module VfPrefixInternal.

Section VfPrefixInternal.

Variable G G' : execution.
Variable e : actid.

Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'loc''" := (loc lab').
Notation "'same_loc''" := (same_loc lab').
Notation "'co''" := (co G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'hb''" := (hb G').
Notation "'sw''" := (sw G').
Notation "'W''" := (fun a => is_true (is_w lab' a)).
Notation "'R''" := (fun a => is_true (is_r lab' a)).
Notation "'F''" := (fun a => is_true (is_f lab' a)).
Notation "'Acq''" := (fun a => is_true (is_acq lab' a)).
Notation "'Rel''" := (fun a => is_true (is_rel lab' a)).
Notation "'Rlx''" := (fun a => is_true (is_rlx lab' a)).
Notation "'vf''" := (vf G').
Notation "'srf''" := (srf G').
Notation "'release''" := (release G').
Notation "'rs''" := (rs G').
Notation "'rmw''" := (rmw G').
Notation "'Loc_'' l" := (fun x => loc' x = Some l) (at level 1).
Notation "'eco''" := (eco G').

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'co'" := (co G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'hb'" := (hb G).
Notation "'sw'" := (sw G).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'vf'" := (vf G).
Notation "'srf'" := (srf G).
Notation "'release'" := (release G).
Notation "'rs'" := (rs G).
Notation "'rmw'" := (rmw G).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Record prf_pred : Prop := {
  prfp_wf : Wf G';
  prfp_ine : E e;
  prfp_sub : sub_execution G' G ∅₂ ∅₂;
  prfp_coh : irreflexive (hb' ⨾ eco'^?);
  prfp_sbp : eq e × (E' \₁ E) ⊆ ⦗eq e⦘ ⨾ hb';
  prfp_ini : E' ∩₁ is_init ⊆₁ E;
}.

Lemma prfp_sc_per_loc
    (PP : prf_pred) :
  sc_per_loc G'.
Proof using.
  unfold sc_per_loc. rewrite sb_in_hb.
  rewrite inclusion_step_cr with (r := eco') (r' := eco').
  { apply PP. }
  auto with hahn.
Qed.

Lemma prfp_sbp'
    (PP : prf_pred) :
  E' \₁ E ⊆₁ hb' e.
Proof using.
  transitivity ((⦗eq e⦘ ⨾ hb') e); [| basic_solver].
  intros x XIN. apply (prfp_sbp PP). split; auto.
Qed.

Lemma prf_no_rsa_cyc
    (PP : prf_pred) :
  irreflexive (rs' ⨾ rf' ⨾ hb').
Proof using.
  rewrite rs_in_co.
  all: auto using prfp_sc_per_loc, prfp_wf.
  rotate 1.
  arewrite (⦗W'⦘ ⨾ co'^? ⨾ rf' ⊆ eco').
  { transitivity (co'^? ⨾ rf'); [basic_solver |].
    rewrite crE, seq_union_l, seq_id_l.
    rewrite co_rf_in_eco, rf_in_eco.
    auto with hahn. }
  rewrite inclusion_step_cr with (r := eco') (r' := eco').
  { apply PP. }
  auto with hahn.
Qed.

Lemma prf_sbrfirr
    (PP : prf_pred) :
  irreflexive (rf' ⨾ hb').
Proof using.
  rotate 1.
  rewrite rf_in_eco.
  rewrite inclusion_step_cr with (r := eco') (r' := eco').
  { apply PP. }
  auto with hahn.
Qed.

Lemma prf_rs
    (PP : prf_pred) :
  rs' ⨾ rf' ⨾ ⦗eq e⦘ ⊆ rs ⨾ rf ⨾ ⦗eq e⦘.
Proof using.
  rewrite <- 2!seqA with (r3 := ⦗eq e⦘).
  intros y e' (e'' & YREL & EQ).
  unfolder in EQ. desf.
  exists e; split; [| basic_solver].
  assert (ZIN : E e) by now apply PP.
  unfolder in *.
  destruct YREL as (y1 & RS & RF).
  assert (Y1IN' : E' y1).
  { apply (wf_rfE (prfp_wf PP)) in RF.
    unfolder in RF; desf. }
  assert (Y1IN : E y1).
  { destruct classic with (E y1) as [IN|NIN]; auto.
    exfalso. apply (prf_sbrfirr PP) with (x := y1).
    exists e; split; auto. apply (prfp_sbp' PP).
    split; auto. }
  assert (RF' : rf y1 e).
  { apply (sub_rf (prfp_sub PP)). basic_solver. }
  exists y1; split; auto.
  clear - RS RF PP Y1IN.
  assert (YIN' : E' y).
  { apply (wf_rsE (prfp_wf PP)) in RS.
    unfolder in RS. desf.
    apply (wf_rfE (prfp_wf PP)) in RF.
    unfolder in RF; desf. }
  assert (YIN : E y).
  { destruct classic with (E y) as [IN|NIN]; auto.
    exfalso. apply (prf_no_rsa_cyc PP) with (x := y).
    exists y1; split; auto. exists e; split; auto.
    apply (prfp_sbp' PP). split; auto. }
  unfold rs in *. rewrite (sub_lab (prfp_sub PP)).
  hahn_rewrite <- seqA in RS.
  unfold seq in RS at 2.
  destruct RS as (y2 & (y2' & ISW & SB) & RS).
  unfolder in ISW. destruct ISW as (EQ & ISW). subst y2'.
  assert (Y2IN' : E' y2).
  { apply crE in SB. destruct SB as [EQ | [SB LOC]].
    { unfolder in EQ; desf. }
    apply wf_sbE in SB. unfolder in SB. desf. }
  assert (Y2IN : E y2).
  { destruct classic with (E y2) as [IN|NIN]; auto.
    exfalso. apply (prf_no_rsa_cyc PP) with (x := y2).
    exists y1; split.
    { enough (RR : singl_rel y2 y1 ⊆ rs') by now apply RR.
      unfold rs.
      rewrite <- inclusion_eqv_cr with (dom := W').
      seq_rewrite <- !id_inter. rewrite !set_interK.
      forward apply RS. clear. basic_solver. }
    exists e. split; auto.
    apply (prfp_sbp' PP). split; auto. }
  hahn_rewrite <- seqA. exists y2. split.
  { exists y. split; [basic_solver |].
    hahn_rewrite crE in SB. destruct SB as [EQ | (SB & LOC)].
    { unfolder in EQ. desf. apply r_refl. }
    apply r_step. split; auto.
    apply (sub_sb (prfp_sub PP)). basic_solver. }
  clear SB ISW YIN.
  destruct RS as (y2' & (EQ & ISW) & RS). subst y2'.
  exists y2. split; [basic_solver |].
  apply clos_rt_rt1n_iff in RS.
  apply clos_rt_rt1n_iff.
  induction RS as [y2| y3 y2 y1 RS RST IHRS].
  { apply rt1n_refl. }
  rename Y2IN into Y3IN. clear Y2IN'.
  unfolder in RS. destruct RS as (y' & RFY & RMWY).
  assert (Y2W : W' y2).
  { apply (wf_rmwD (prfp_wf PP)) in RMWY.
    unfolder in RMWY. desf. }
  assert (Y2IN' : E' y2).
  { apply (wf_rmwE (prfp_wf PP)) in RMWY.
    unfolder in RMWY. desf. }
  assert (Y2IN : E y2).
  { destruct classic with (E y2) as [IN|NIN]; auto.
    exfalso. apply (prf_no_rsa_cyc PP) with (x := y2).
    exists y1; split.
    { enough (RR : singl_rel y2 y1 ⊆ rs') by now apply RR.
      unfold rs.
      rewrite <- inclusion_eqv_cr with (dom := W').
      seq_rewrite <- !id_inter. rewrite !set_interK.
      apply clos_rt_rt1n_iff in RST.
      forward apply RST. clear - Y2W.
      unfolder; ins; desf. }
    exists e. split; auto.
    apply (prfp_sbp' PP). split; auto. }
  assert (Y'IN' : E' y').
  { apply (wf_rmwE (prfp_wf PP)) in RMWY.
    unfolder in RMWY. desf. }
  assert (Y'IN : E y').
  { destruct classic with (E y') as [IN|NIN]; auto.
    exfalso. apply (prf_no_rsa_cyc PP) with (x := y2).
    exists y1; split.
    { enough (RR : singl_rel y2 y1 ⊆ rs') by now apply RR.
      unfold rs.
      rewrite <- inclusion_eqv_cr with (dom := W').
      seq_rewrite <- !id_inter. rewrite !set_interK.
      apply clos_rt_rt1n_iff in RST.
      forward apply RST. clear - Y2W.
      unfolder; ins; desf. }
    exists e. split; auto.
    apply hb_trans with y'.
    { apply (prfp_sbp' PP). split; auto. }
    now apply sb_in_hb, (wf_rmwi (prfp_wf PP)). }
  apply Relation_Operators.rt1n_trans with y2.
  { exists y'. split.
    { apply (sub_rf (prfp_sub PP)). basic_solver. }
    apply (sub_rmw (prfp_sub PP)). basic_solver. }
  apply IHRS; auto.
Qed.

Lemma prfp_wfG
    (PP : prf_pred) :
  Wf G.
Proof using.
  apply sub_WF with (G := G') (sc := ∅₂) (sc' := ∅₂).
  all: try now apply PP.
  rewrite set_interC. apply PP.
Qed.

Lemma prf_release
    (PP : prf_pred) :
  release' ⨾ rf' ⨾ ⦗eq e⦘ ⊆ release ⨾ rf ⨾ ⦗eq e⦘.
Proof using.
  unfold release. rewrite (sub_lab (prfp_sub PP)).
  rewrite !seqA, (prf_rs PP).
  hahn_frame_l.
  rewrite <- 3!seqA with (r3 := ⦗eq e⦘).
  intros y e' (e'' & YREL & EQ).
  unfolder in EQ. desf.
  exists e; split; [| basic_solver].
  destruct YREL as (y1 & FSB & RSRF).
  exists y1. split; auto.
  apply crE in FSB. destruct FSB as [EQ | (y1' & ISF & SB)].
  { unfolder in EQ. desf. auto with hahn. }
  red in ISF. destruct ISF as (EQ & ISF). subst y1'.
  apply r_step. exists y. split; [basic_solver |].
  assert (Y1IN : E y1).
  { hahn_rewrite (wf_rsE (prfp_wfG PP)) in RSRF.
    hahn_rewrite (wf_rfE (prfp_wfG PP)) in RSRF.
    unfolder in RSRF. desf. }
  destruct classic with (E y) as [INY | NIN].
  { apply (sub_sb (prfp_sub PP)). unfolder.
    splits; auto. }
  exfalso. apply (prf_no_rsa_cyc PP) with (x := y1).
  hahn_rewrite <- seqA.
  exists e. split.
  { hahn_rewrite <- (sub_rs_in (prfp_sub PP)).
    now hahn_rewrite <- (sub_rf_in (prfp_sub PP)). }
  apply hb_trans with y; [| now apply sb_in_hb].
  apply (prfp_sbp' PP). split; auto.
  apply wf_sbE in SB. unfolder in SB. desf.
Qed.

End VfPrefixInternal.

End VfPrefixInternal.

Section VfPrefix.

Variable G G' : execution.

Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'loc''" := (loc lab').
Notation "'same_loc''" := (same_loc lab').
Notation "'co''" := (co G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'hb''" := (hb G').
Notation "'sw''" := (sw G').
Notation "'W''" := (fun a => is_true (is_w lab' a)).
Notation "'R''" := (fun a => is_true (is_r lab' a)).
Notation "'F''" := (fun a => is_true (is_f lab' a)).
Notation "'Acq''" := (fun a => is_true (is_acq lab' a)).
Notation "'Rel''" := (fun a => is_true (is_rel lab' a)).
Notation "'Rlx''" := (fun a => is_true (is_rlx lab' a)).
Notation "'vf''" := (vf G').
Notation "'srf''" := (srf G').
Notation "'release''" := (release G').
Notation "'rs''" := (rs G').
Notation "'rmw''" := (rmw G').
Notation "'Loc_'' l" := (fun x => loc' x = Some l) (at level 1).
Notation "'eco''" := (eco G').

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'co'" := (co G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'hb'" := (hb G).
Notation "'sw'" := (sw G).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'vf'" := (vf G).
Notation "'srf'" := (srf G).
Notation "'release'" := (release G).
Notation "'rs'" := (rs G).
Notation "'rmw'" := (rmw G).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Lemma prf_sw e
    (PP : VfPrefixInternal.prf_pred G G' e) :
  sw' ⨾ ⦗eq e⦘ ⊆ sw ⨾ ⦗eq e⦘.
Proof using.
  unfold sw.
  rewrite 2!crE, !seqA.
  rewrite !seq_union_l, !seq_union_r.
  rewrite !seq_id_l, !seqA.
  rewrite (sub_lab (VfPrefixInternal.prfp_sub PP)).
  apply union_mori.
  { rewrite !seq_eqvC with (domb := eq e).
    hahn_frame_r.
    now apply VfPrefixInternal.prf_release. }
  rewrite !seq_eqvC with (domb := eq e).
  hahn_frame_r.
  rewrite !seq_eqvC with (domb := eq e).
  hahn_frame_r.
  rewrite <- seqA with (r1 := release').
  rewrite <- seqA with (r1 := release).
  intros x y (e' & RELRF & SB).
  unfolder in SB. destruct SB as (SB & YEQ). subst y.
  assert (HBIRR : irreflexive hb').
  { apply irreflexive_mori with (x := hb' ⨾ eco'^?).
    all: try now apply PP.
    red. basic_solver. }
  assert (INE'' : E' e').
  { apply wf_sbE in SB. unfolder in SB. desf. }
  assert (INE' : E e').
  { destruct classic with (E e') as [INE'|NINE']; auto.
    assert (NSB : (⦗eq e⦘ ⨾ hb') e e').
    { apply PP. clear - INE'' NINE'. basic_solver. }
    exfalso. apply HBIRR with e'.
    apply hb_trans with e.
    { now apply sb_in_hb. }
    unfolder in NSB. desf. }
  assert (SB' : sb e' e).
  { apply (sub_sb (VfPrefixInternal.prfp_sub PP)). unfolder.
    splits; auto || apply PP. }
  exists e'; split; [| clear - SB'; basic_solver].
  enough (RELS : (release ⨾ rf ⨾ ⦗eq e'⦘) x e').
  { hahn_rewrite <- seqA in RELS.
    forward apply RELS. clear. basic_solver. }
  enough (RELS : release' ⨾ rf' ⨾ ⦗eq e'⦘ ⊆ release ⨾ rf ⨾ ⦗eq e'⦘).
  { apply RELS. forward apply RELRF. clear. basic_solver 11. }
  apply VfPrefixInternal.prf_release.
  constructor; auto; try now apply PP.
  unfolder. intros x' y (XEQ & YINE & YNIN). subst x'.
  split; auto. apply hb_trans with e.
  { now apply (sub_hb_in (VfPrefixInternal.prfp_sub PP)), sb_in_hb. }
  enough (GOAL : (⦗eq e⦘ ⨾ hb') e y).
  { unfolder in GOAL. desf. }
  apply PP. basic_solver.
Qed.

Lemma prf_hb e
    (PP : VfPrefixInternal.prf_pred G G' e) :
  hb' ⨾ ⦗eq e⦘ ⊆ hb ⨾ ⦗eq e⦘.
Proof using.
  assert (HBIRR : irreflexive hb').
  { apply irreflexive_mori with (x := hb' ⨾ eco'^?).
    all: try now apply PP.
    red. basic_solver. }
  unfold hb.
  unfolder. intros x y (HB & EQ).
  subst y. split; auto.
  apply clos_trans_t1n_iff.
  apply clos_trans_t1n_iff in HB.
  induction HB as [x e HB | e1 e2 e [SB | SW] HB IHHB'].
  { apply t1n_step.
    destruct HB as [SB | SW]; [left | right].
    { assert (XIN' : E' x).
      { apply wf_sbE in SB. unfolder in SB. desf. }
      assert (INE : E x).
      { apply sb_in_hb in SB.
        destruct classic with (E x) as [XIN|XNN]; auto.
        exfalso. eapply HBIRR.
        apply hb_trans with e; eauto.
        enough (SB' : (⦗eq e⦘ ⨾ hb') e x).
        { forward apply SB'. clear. basic_solver. }
        apply (VfPrefixInternal.prfp_sbp PP). basic_solver. }
      apply (sub_sb (VfPrefixInternal.prfp_sub PP)).
      unfolder; splits; auto || apply PP. }
    enough (SW' : (sw ⨾ ⦗eq e⦘) x e).
    { forward apply SW'. clear. basic_solver. }
    apply prf_sw; auto. basic_solver. }
  all: apply Relation_Operators.t1n_trans with e2.
  all: assert (IHHB : clos_trans_1n actid (fun x y => sb x y \/ sw x y) e2 e); auto.
  all: clear IHHB'.
  { left.
    assert (E2IN : E e2).
    { apply clos_trans_t1n_iff in IHHB.
      apply (wf_hbE (VfPrefixInternal.prfp_wfG PP)) in IHHB.
      unfolder in IHHB. desf. }
    assert (XIN' : E' e1).
    { apply wf_sbE in SB. unfolder in SB. desf. }
    assert (INE : E e1).
    { apply sb_in_hb in SB.
      destruct classic with (E e1) as [XIN|XNN]; auto.
      exfalso. eapply HBIRR.
      apply hb_trans with e2; eauto.
      apply hb_trans with e.
      { apply clos_trans_t1n_iff in HB.
        apply HB. }
      enough (SB' : (⦗eq e⦘ ⨾ hb') e e1).
      { forward apply SB'. clear. basic_solver. }
      apply (VfPrefixInternal.prfp_sbp PP). basic_solver. }
    apply (sub_sb (VfPrefixInternal.prfp_sub PP)).
    unfolder; splits; auto || apply PP. }
  right.
  assert (E2IN : E e2).
  { apply clos_trans_t1n_iff in IHHB.
    apply (wf_hbE (VfPrefixInternal.prfp_wfG PP)) in IHHB.
    unfolder in IHHB. desf. }
  assert (XIN' : E' e1).
  { apply (wf_swE (VfPrefixInternal.prfp_wf PP)) in SW. unfolder in SW. desf. }
  assert (INE : E e1).
  { apply sw_in_hb in SW.
    destruct classic with (E e1) as [XIN|XNN]; auto.
    exfalso. eapply HBIRR.
    apply hb_trans with e2; eauto.
    apply hb_trans with e.
    { apply clos_trans_t1n_iff in HB.
      apply HB. }
    enough (SB' : (⦗eq e⦘ ⨾ hb') e e1).
    { forward apply SB'. clear. basic_solver. }
    apply (VfPrefixInternal.prfp_sbp PP). basic_solver. }
  enough (SW' : (sw ⨾ ⦗eq e2⦘) e1 e2).
  { forward apply SW'. clear. basic_solver. }
  apply prf_sw; [| basic_solver].
  constructor; auto; try now apply PP.
  unfolder. intros x y (XEQ & YIN & YNIN).
  subst x. split; auto.
  apply hb_trans with e.
  { apply clos_trans_t1n_iff in HB.
    apply HB. }
  enough (SB' : (⦗eq e⦘ ⨾ hb') e y).
  { forward apply SB'. clear. basic_solver. }
  apply PP. basic_solver.
Qed.

Lemma prf_vf' e
    (WF : Wf G')
    (INE : E e)
    (SUB : sub_execution G' G ∅₂ ∅₂)
    (COH : irreflexive (hb' ⨾ eco'^?))
    (SBP : eq e × (E' \₁ E) ⊆ ⦗eq e⦘ ⨾ hb')
    (INI : E' ∩₁ is_init ⊆₁ E) :
  vf' ⨾ ⦗eq e⦘ ⊆ vf ⨾ ⦗eq e⦘.
Proof using.
  assert (WF' : Wf G).
  { eapply sub_WF; eauto.
    rewrite <- INI. clear. basic_solver. }
  unfold vf.
  rewrite (sub_lab SUB).
  rewrite crE with (r := hb'),
          crE with (r := hb).
  rewrite !seq_union_r, !seq_union_l.
  apply union_mori.
  all: rewrite ?seq_id_r, !seqA.
  { rewrite crE with (r := rf'),
            crE with (r := rf).
    rewrite !seq_union_l, seq_id_l.
    rewrite !seq_union_r.
    apply union_mori; [basic_solver |].
    unfolder. intros x y ((XIN' & XW) & RF & YEQ).
    subst y.
    assert (XIN : E x).
    { destruct classic with (E x) as [XIN|XNN]; auto.
      exfalso. apply COH with e.
      exists x. split.
      { enough (RR : (⦗eq e⦘ ⨾ hb') e x).
        { forward apply RR. clear. basic_solver. }
        apply SBP. basic_solver. }
      now apply r_step, rf_in_eco. }
    splits; auto.
    apply (sub_rf SUB). basic_solver. }
  rewrite prf_hb.
  { rewrite crE with (r := rf'),
            crE with (r := rf).
    rewrite !seq_union_l, seq_id_l.
    rewrite !seq_union_r.
    apply union_mori; [rewrite (wf_hbE WF'); basic_solver |].
    unfolder. intros x y ((XIN' & XW) & z & RF & HB & YEQ).
    subst y.
    assert (XIN : E x).
    { destruct classic with (E x) as [XIN|XNN]; auto.
      exfalso. apply COH with z.
      exists x. split.
      { apply (sub_hb_in SUB) in HB.
        apply hb_trans with e; auto.
        enough (RR : (⦗eq e⦘ ⨾ hb') e x).
        { forward apply RR. clear. basic_solver. }
        apply SBP. basic_solver. }
      now apply r_step, rf_in_eco. }
    assert (ZIN : E z).
    { apply (wf_hbE WF') in HB.
      unfolder in HB. desf. }
    splits; auto. exists z; splits; auto.
    apply (sub_rf SUB). basic_solver. }
  constructor; auto.
Qed.

End VfPrefix.