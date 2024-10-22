From imm Require Import Events Execution Execution_eco.
From imm Require Import SubExecution.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.

Require Import Srf xmm_s_hb.

Set Implicit Arguments.

Module HbPrefixInternal.

Section HbPrefixInternal.

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

Record hb_pref_pred : Prop := {
  hb_pref_wf : Wf G';
  hb_pref_ine : E e;
  hb_pref_sub : sub_execution G' G ∅₂ ∅₂;
  hb_pref_no_rsa_cyc : irreflexive (rs' ⨾ rf' ⨾ hb');
  hb_pref_no_hb_cyc : irreflexive hb';
  hb_pref_sbp : eq e × (E' \₁ E) ⊆ ⦗eq e⦘ ⨾ hb';
  hb_pref_ini : E' ∩₁ is_init ⊆₁ E;
}.

Lemma hb_pref_sbp'
    (PP : hb_pref_pred) :
  E' \₁ E ⊆₁ hb' e.
Proof using.
  transitivity ((⦗eq e⦘ ⨾ hb') e); [| basic_solver].
  intros x XIN. apply (hb_pref_sbp PP). split; auto.
Qed.

Lemma hb_pref_sbrfirr
    (PP : hb_pref_pred) :
  irreflexive (rf' ⨾ hb').
Proof using.
  arewrite (rf' ⊆ rs' ⨾ rf'); [| apply PP].
  unfold rs.
  rewrite <- cr_of_ct, <- inclusion_id_cr,
          seq_id_r.
  rewrite (wf_rfD (hb_pref_wf PP)).
  basic_solver.
Qed.

Lemma hb_pref_rs
    (PP : hb_pref_pred) :
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
  { apply (wf_rfE (hb_pref_wf PP)) in RF.
    unfolder in RF; desf. }
  assert (Y1IN : E y1).
  { destruct classic with (E y1) as [IN|NIN]; auto.
    exfalso. apply (hb_pref_sbrfirr PP) with (x := y1).
    exists e; split; auto. apply (hb_pref_sbp' PP).
    split; auto. }
  assert (RF' : rf y1 e).
  { apply (sub_rf (hb_pref_sub PP)). basic_solver. }
  exists y1; split; auto.
  clear - RS RF PP Y1IN.
  assert (YIN' : E' y).
  { apply (wf_rsE (hb_pref_wf PP)) in RS.
    unfolder in RS. desf.
    apply (wf_rfE (hb_pref_wf PP)) in RF.
    unfolder in RF; desf. }
  assert (YIN : E y).
  { destruct classic with (E y) as [IN|NIN]; auto.
    exfalso. apply (hb_pref_no_rsa_cyc PP) with (x := y).
    exists y1; split; auto. exists e; split; auto.
    apply (hb_pref_sbp' PP). split; auto. }
  unfold rs in *. rewrite (sub_lab (hb_pref_sub PP)).
  (* hahn_rewrite <- seqA in RS. *)
  unfold seq in RS at 1.
  destruct RS as (y' & (EQ & ISW) & RS). subst y'.
  exists y. split; [basic_solver |].
  apply clos_rt_rt1n_iff in RS.
  apply clos_rt_rt1n_iff.
  induction RS as [y2| y3 y2 y1 RS RST IHRS].
  { apply rt1n_refl. }
  unfolder in RS. destruct RS as (y' & RFY & RMWY).
  assert (Y2W : W' y2).
  { apply (wf_rmwD (hb_pref_wf PP)) in RMWY.
    unfolder in RMWY. desf. }
  assert (Y2IN' : E' y2).
  { apply (wf_rmwE (hb_pref_wf PP)) in RMWY.
    unfolder in RMWY. desf. }
  assert (Y2IN : E y2).
  { destruct classic with (E y2) as [IN|NIN]; auto.
    exfalso. apply (hb_pref_no_rsa_cyc PP) with (x := y2).
    exists y1; split.
    { enough (RR : singl_rel y2 y1 ⊆ rs') by now apply RR.
      unfold rs.
      apply clos_rt_rt1n_iff in RST.
      forward apply RST. clear - Y2W.
      unfolder; ins; desf. }
    exists e. split; auto.
    apply (hb_pref_sbp' PP). split; auto. }
  assert (Y'IN' : E' y').
  { apply (wf_rmwE (hb_pref_wf PP)) in RMWY.
    unfolder in RMWY. desf. }
  assert (Y'IN : E y').
  { destruct classic with (E y') as [IN|NIN]; auto.
    exfalso. apply (hb_pref_no_rsa_cyc PP) with (x := y2).
    exists y1; split.
    { enough (RR : singl_rel y2 y1 ⊆ rs') by now apply RR.
      unfold rs.
      apply clos_rt_rt1n_iff in RST.
      forward apply RST. clear - Y2W.
      unfolder; ins; desf. }
    exists e. split; auto.
    apply hb_trans with y'.
    { apply (hb_pref_sbp' PP). split; auto. }
    now apply sb_in_hb, (wf_rmwi (hb_pref_wf PP)). }
  apply Relation_Operators.rt1n_trans with y2.
  { exists y'. split.
    { apply (sub_rf (hb_pref_sub PP)). basic_solver. }
    apply (sub_rmw (hb_pref_sub PP)). basic_solver. }
  apply IHRS; auto.
Qed.

Lemma hb_pref_wfG
    (PP : hb_pref_pred) :
  Wf G.
Proof using.
  apply sub_WF with (G := G') (sc := ∅₂) (sc' := ∅₂).
  all: try now apply PP.
  rewrite set_interC. apply PP.
Qed.

Lemma hb_pref_release
    (PP : hb_pref_pred) :
  release' ⨾ rf' ⨾ ⦗eq e⦘ ⊆ release ⨾ rf ⨾ ⦗eq e⦘.
Proof using.
  unfold release. rewrite (sub_lab (hb_pref_sub PP)).
  rewrite !seqA, (hb_pref_rs PP).
  hahn_frame_l.
  rewrite <- 4!seqA with (r3 := ⦗eq e⦘).
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
  { hahn_rewrite (wf_rsE (hb_pref_wfG PP)) in RSRF.
    hahn_rewrite (wf_rfE (hb_pref_wfG PP)) in RSRF.
    unfolder in RSRF. desf. }
  destruct classic with (E y) as [INY | NIN].
  { apply (sub_sb (hb_pref_sub PP)). unfolder.
    splits; auto. }
  exfalso. apply (hb_pref_no_rsa_cyc PP) with (x := y1).
  hahn_rewrite <- seqA.
  exists e. split.
  { hahn_rewrite <- (sub_rs_in (hb_pref_sub PP)).
    hahn_rewrite <- (sub_rf_in (hb_pref_sub PP)).
    destruct RSRF as (y1' & ISRLX & RSRF).
    unfolder in ISRLX. desf. }
  apply hb_trans with y; [| now apply sb_in_hb].
  apply (hb_pref_sbp' PP). split; auto.
  apply wf_sbE in SB. unfolder in SB. desf.
Qed.

End HbPrefixInternal.

End HbPrefixInternal.

Section HbPrefix.

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
    (PP : HbPrefixInternal.hb_pref_pred G G' e) :
  sw' ⨾ ⦗eq e⦘ ⊆ sw ⨾ ⦗eq e⦘.
Proof using.
  unfold sw.
  rewrite 2!crE, !seqA.
  rewrite !seq_union_l, !seq_union_r.
  rewrite !seq_id_l, !seqA.
  rewrite (sub_lab (HbPrefixInternal.hb_pref_sub PP)).
  apply union_mori.
  { seq_rewrite !(seq_eqvC _ (eq e)).
    rewrite !seqA.
    do 2 hahn_frame_r.
    now apply HbPrefixInternal.hb_pref_release. }
  rewrite !seq_eqvC with (domb := eq e).
  hahn_frame_r.
  rewrite !seq_eqvC with (domb := eq e).
  hahn_frame_r.
  rewrite <- seqA with (r1 := release').
  rewrite <- seqA with (r1 := release).
  intros x y (e' & RELRF & e'' & RLX & SB).
  unfolder in RLX. destruct RLX as (EEQ & RLX). subst e''.
  unfolder in SB. destruct SB as (SB & YEQ). subst y.
  assert (INE'' : E' e').
  { apply wf_sbE in SB. unfolder in SB. desf. }
  assert (INE' : E e').
  { destruct classic with (E e') as [INE'|NINE']; auto.
    assert (NSB : (⦗eq e⦘ ⨾ hb') e e').
    { apply PP. clear - INE'' NINE'. basic_solver. }
    exfalso. apply (HbPrefixInternal.hb_pref_no_hb_cyc PP) with e'.
    apply hb_trans with e.
    { now apply sb_in_hb. }
    unfolder in NSB. desf. }
  assert (SB' : sb e' e).
  { apply (sub_sb (HbPrefixInternal.hb_pref_sub PP)). unfolder.
    splits; auto || apply PP. }
  hahn_rewrite <- seqA.
  exists e'; split; [| clear - SB'; basic_solver].
  exists e'; split; [| basic_solver].
  enough (RELS : (release ⨾ rf ⨾ ⦗eq e'⦘) x e').
  { hahn_rewrite <- seqA in RELS.
    forward apply RELS. clear. basic_solver. }
  enough (RELS : release' ⨾ rf' ⨾ ⦗eq e'⦘ ⊆ release ⨾ rf ⨾ ⦗eq e'⦘).
  { apply RELS. forward apply RELRF. clear. basic_solver 11. }
  apply HbPrefixInternal.hb_pref_release.
  constructor; auto; try now apply PP.
  unfolder. intros x' y (XEQ & YINE & YNIN). subst x'.
  split; auto. apply hb_trans with e.
  { now apply (sub_hb_in (HbPrefixInternal.hb_pref_sub PP)), sb_in_hb. }
  enough (GOAL : (⦗eq e⦘ ⨾ hb') e y).
  { unfolder in GOAL. desf. }
  apply PP. basic_solver.
Qed.

Lemma hb_pref_hb e
    (PP : HbPrefixInternal.hb_pref_pred G G' e) :
  hb' ⨾ ⦗eq e⦘ ⊆ hb ⨾ ⦗eq e⦘.
Proof using.
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
        exfalso. eapply (HbPrefixInternal.hb_pref_no_hb_cyc PP).
        apply hb_trans with e; eauto.
        enough (SB' : (⦗eq e⦘ ⨾ hb') e x).
        { forward apply SB'. clear. basic_solver. }
        apply (HbPrefixInternal.hb_pref_sbp PP). basic_solver. }
      apply (sub_sb (HbPrefixInternal.hb_pref_sub PP)).
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
      apply (wf_hbE (HbPrefixInternal.hb_pref_wfG PP)) in IHHB.
      unfolder in IHHB. desf. }
    assert (XIN' : E' e1).
    { apply wf_sbE in SB. unfolder in SB. desf. }
    assert (INE : E e1).
    { apply sb_in_hb in SB.
      destruct classic with (E e1) as [XIN|XNN]; auto.
      exfalso. eapply (HbPrefixInternal.hb_pref_no_hb_cyc PP).
      apply hb_trans with e2; eauto.
      apply hb_trans with e.
      { apply clos_trans_t1n_iff in HB.
        apply HB. }
      enough (SB' : (⦗eq e⦘ ⨾ hb') e e1).
      { forward apply SB'. clear. basic_solver. }
      apply (HbPrefixInternal.hb_pref_sbp PP). basic_solver. }
    apply (sub_sb (HbPrefixInternal.hb_pref_sub PP)).
    unfolder; splits; auto || apply PP. }
  right.
  assert (E2IN : E e2).
  { apply clos_trans_t1n_iff in IHHB.
    apply (wf_hbE (HbPrefixInternal.hb_pref_wfG PP)) in IHHB.
    unfolder in IHHB. desf. }
  assert (XIN' : E' e1).
  { apply (wf_swE (HbPrefixInternal.hb_pref_wf PP)) in SW. unfolder in SW. desf. }
  assert (INE : E e1).
  { apply sw_in_hb in SW.
    destruct classic with (E e1) as [XIN|XNN]; auto.
    exfalso. eapply (HbPrefixInternal.hb_pref_no_hb_cyc PP).
    apply hb_trans with e2; eauto.
    apply hb_trans with e.
    { apply clos_trans_t1n_iff in HB.
      apply HB. }
    enough (SB' : (⦗eq e⦘ ⨾ hb') e e1).
    { forward apply SB'. clear. basic_solver. }
    apply (HbPrefixInternal.hb_pref_sbp PP). basic_solver. }
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

Lemma hb_pref_vf e
    (WF : Wf G')
    (INE : E e)
    (SUB : sub_execution G' G ∅₂ ∅₂)
    (COH1 : irreflexive (rs' ⨾ rf' ⨾ hb'))
    (COH2 : irreflexive hb')
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
      exfalso. admit. (* hb-rf cycle *) }
    splits; auto.
    apply (sub_rf SUB). basic_solver. }
  rewrite hb_pref_hb.
  { rewrite crE with (r := rf'),
            crE with (r := rf).
    rewrite !seq_union_l, seq_id_l.
    rewrite !seq_union_r.
    apply union_mori; [rewrite (wf_hbE WF'); basic_solver |].
    unfolder. intros x y ((XIN' & XW) & z & RF & HB & YEQ).
    subst y.
    assert (XIN : E x).
    { destruct classic with (E x) as [XIN|XNN]; auto.
      exfalso. admit. (* hb-rf cycle *) }
    assert (ZIN : E z).
    { apply (wf_hbE WF') in HB.
      unfolder in HB. desf. }
    splits; auto. exists z; splits; auto.
    apply (sub_rf SUB). basic_solver. }
  constructor; auto.
Admitted.

Lemma hb_pref_vfsb e
    (WF : Wf G')
    (INE : E' e)
    (SUB : sub_execution G' G ∅₂ ∅₂)
    (COH1 : irreflexive (rs' ⨾ rf' ⨾ hb'))
    (COH2 : irreflexive hb')
    (MAX : eq e × (E' \₁ E \₁ eq e) ⊆ ⦗eq e⦘ ⨾ sb')
    (INI : E' ∩₁ is_init ⊆₁ E) :
  vf' ⨾ sb' ⨾ ⦗eq e⦘ ≡ vf ⨾ sb' ⨾ ⦗eq e⦘.
Proof using.
  split.
  { rewrite <- seqA with (r1 := vf) (r2 := sb').
    intros x e' (y & VF & e'' & SB & EQ).
    unfolder in EQ. destruct EQ as (EQ1 & EQ2).
    subst e'. subst e''.
    exists e. split; [| basic_solver].
    exists y. split; auto.
    enough (RR : (vf ⨾ ⦗eq y⦘) x y).
    { forward apply RR. clear. basic_solver. }
    assert (NEQ : y <> e).
    { intro FALSO. subst y. eapply sb_irr; eauto. }
    assert (XINE' : E' y).
    { apply (wf_vfE WF) in VF. unfolder in VF. desf. }
    assert (XINE : E y).
    { destruct classic with (E y) as [XINE|NINX]; auto.
      exfalso. eapply sb_irr.
      apply sb_trans with e; eauto.
      enough (RR : (⦗eq e⦘ ⨾ sb') e y).
      { forward apply RR. clear. basic_solver. }
      apply MAX. basic_solver. }
    apply hb_pref_vf; auto; [| basic_solver].
    rewrite <- sb_in_hb. unfolder.
    intros x0 z (XEQ & ZIN & ZNIN).
    subst x0. split; auto.
    destruct classic with (z = e) as [ZEQ|ZNEQ].
    { subst z. auto. }
    apply sb_trans with e; auto.
    enough (RR : (⦗eq e⦘ ⨾ sb') e z).
    { forward apply RR. clear. basic_solver. }
    apply MAX. basic_solver. }
  rewrite sub_vf_in; eauto.
  reflexivity.
Qed.

End HbPrefix.