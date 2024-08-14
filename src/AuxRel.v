From imm Require Import Events Execution imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

Require Import Program.Basics.
Require Import AuxDef.

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

Section AuxRel.

Variable G : execution.
Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'is_acq'" := (is_acq lab).
Notation "'is_rel'" := (is_rel lab).
Notation "'is_rlx'" := (is_rlx lab).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'ppo'" := (ppo G).
Notation "'hb'" := (hb G).
Notation "'psc'" := (imm.psc G).
Notation "'sw'" := (sw G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'F'" := (is_f lab).
Notation "'bob'" := (bob G).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Definition ppo_alt := (sb ∩ same_loc ∪ bob)⁺.
Definition hb_alt := (ppo_alt ∪ rf)⁺.
Definition rpo_imm :=
  ⦗R ∩₁ is_rlx⦘ ⨾ sb ⨾ ⦗F ∩₁ is_acq⦘ ∪
  ⦗is_acq⦘ ⨾ sb ∪
  sb ⨾ ⦗is_rel⦘ ∪
  ⦗F ∩₁ is_rel⦘ ⨾ sb ⨾ ⦗W ∩₁ is_rlx⦘.
Definition rpo := rpo_imm⁺.
Definition rhb := (sb ∩ same_loc ∪ rpo ∪ sw)⁺.
Definition vf := ⦗E⦘ ⨾ ⦗W⦘ ⨾ rf^? ⨾ hb^?.
Definition srf := (vf ∩ same_loc) ⨾ ⦗R⦘ \ (co ⨾ vf).

Lemma thrdle_sb_closed thrdle
    (INIT_LEAST : least_elt thrdle tid_init)
    (INIT_MIN : wmin_elt thrdle tid_init) :
  sb^? ⨾ tid ↓ thrdle ⨾ sb^? ⊆ tid ↓ thrdle.
Proof.
  rewrite crE, !seq_union_l, !seq_union_r, !seq_id_l, !seq_id_r, !unionA.
  apply inclusion_union_l; try done.
  arewrite (tid ↓ thrdle ⨾ sb ⊆ tid ↓ thrdle).
  { unfolder. intros x y (z & TID & SB).
    apply sb_tid_init in SB.
    destruct SB as [EQ|INIT]; try by rewrite <- EQ.
    apply is_init_tid in INIT; rewrite INIT in *.
    apply INIT_MIN in TID; rewrite <- TID.
    apply INIT_LEAST. }
  arewrite (sb ⨾ tid ↓ thrdle ⊆ tid ↓ thrdle).
  { unfold map_rel.
    intros x y [z [SB TID]].
    apply sb_tid_init in SB.
    destruct SB as [EQ|INIT]; try by rewrite -> EQ.
    apply is_init_tid in INIT; rewrite INIT in *.
    apply INIT_LEAST. }
  basic_solver.
Qed.

Lemma rpo_imm_in_sb : rpo_imm ⊆ sb.
Proof using.
  unfold rpo_imm.
  basic_solver.
Qed.

Lemma rpo_in_sb : rpo ⊆ sb.
Proof using.
  unfold rpo. rewrite rpo_imm_in_sb.
  apply ct_of_trans. apply sb_trans.
Qed.

Lemma wf_rpoE
    (WF : Wf G) :
  rpo ≡ ⦗E⦘ ⨾ rpo ⨾ ⦗E⦘.
Proof using.
  split; [| basic_solver].
  unfolder. intros x y REL.
  splits; ins.
  all: apply rpo_in_sb in REL.
  all: unfold sb in REL; unfolder in REL; desf.
Qed.

Lemma wf_vfE
    (WF : Wf G) :
  vf ≡ ⦗E⦘ ⨾ vf ⨾ ⦗E⦘.
Proof using.
  split; [| basic_solver].
  unfold vf.
  rewrite (wf_hbE WF), (wf_rfE WF).
  basic_solver 12.
Qed.

Lemma vf_dom : dom_rel vf ⊆₁ W.
Proof using.
  unfold vf. basic_solver.
Qed.

Lemma wf_srfE
    (WF : Wf G) :
  srf ≡ ⦗E⦘ ⨾ srf ⨾ ⦗E⦘.
Proof using.
  split; [| basic_solver]. unfold srf.
  rewrite wf_vfE at 1 by auto.
  unfolder. ins. desf. splits; eauto.
Qed.

Lemma wf_srfD : srf ≡ ⦗W⦘ ⨾ srf ⨾ ⦗R⦘.
Proof using.
  split; [| basic_solver]. unfold srf.
  intros x y SRF. unfolder in SRF. desf.
  unfolder; ins; desf; splits; ins.
  { apply vf_dom. now exists y. }
  exists y; ins.
Qed.

Lemma wf_srf_loc : srf ⊆ same_loc.
Proof using.
  unfold srf. intros x y SRF.
  unfolder in SRF; desf.
Qed.

Lemma wf_rhbE
    (WF : Wf G) :
  rhb ≡ ⦗E⦘ ⨾ rhb ⨾ ⦗E⦘.
Proof using.
  unfold rhb. rewrite wf_swE, wf_rpoE, wf_sbE; auto.
  assert (SB_SAMELOC : (⦗E⦘ ⨾ sb ⨾ ⦗E⦘) ∩ same_loc ≡ ⦗E⦘ ⨾ sb ∩ same_loc ⨾ ⦗E⦘).
  { basic_solver 10. }
  rewrite SB_SAMELOC.
  rewrite <- !seq_union_r, <- !seq_union_l.
  seq_rewrite <- ct_seq_eqv_l. rewrite <- seqA.
  now seq_rewrite <- ct_seq_eqv_r.
Qed.

Lemma rf_sub_vf (WF : Wf G) : rf ⊆ vf.
Proof using.
  rewrite WF.(wf_rfD), WF.(wf_rfE).
  unfold vf; unfolder; ins; desf.
  splits; eauto.
Qed.

Lemma wf_srff'
    (CO_TOT : forall ol,
      is_total (E ∩₁ W ∩₁ (fun x => loc x = ol)) co
    ) :
  functional srf⁻¹.
Proof using.
  unfolder; unfold srf. intros x y z (VF1 & CO1) (VF2 & CO2).
  tertium_non_datur (y = z) as [EQ|NEQ]; ins; exfalso.
  destruct CO_TOT with (a := y) (b := z)
                       (ol := loc x) as [CO|CO].
  all: ins; unfolder in *; desf; splits; eauto.
  all: try now (apply vf_dom; eexists; eauto).
  { unfold vf in VF1. unfolder in VF1; desf. }
  unfold vf in VF2. unfolder in VF2; desf.
Qed.

Lemma wf_srff (WF : Wf G) : functional srf⁻¹.
Proof using.
  apply wf_srff', WF.
Qed.

Lemma srf_exists b
    (HIN : E b)
    (FIN_ACTS : set_finite (E \₁ is_init))
    (WF : Wf G)
    (IS_R : R b) :
  exists a, srf a b.
Proof using.
  assert (HLOC : exists l, loc b = Some l); desf.
  { unfold is_r in IS_R. unfold loc. desf. eauto. }
  assert (HINIT : E (InitEvent l)).
  { apply WF; eauto. }
  assert (INILAB : lab (InitEvent l) = Astore Xpln Opln l 0).
  { apply WF. }
  assert (INILOC : loc (InitEvent l) = Some l).
  { unfold loc. now rewrite (wf_init_lab WF). }
  assert (INIW : W (InitEvent l)).
  { unfold is_w, loc. desf. }
  assert (INISB : sb (InitEvent l) b).
  { eapply init_ninit_sb, read_or_fence_is_not_init; eauto. }
  assert (INIVF : vf (InitEvent l) b).
  { unfold vf. exists (InitEvent l).
    splits; ins.
    hahn_rewrite <- sb_in_hb.
    basic_solver 21. }
  assert (ACT_LIST : exists El, E ∩₁ Loc_ l ≡₁ (fun x => In x El)); desf.
  { apply set_finiteE in FIN_ACTS. desf.
    exists (InitEvent l :: filterP (Loc_ l) findom). split; intros x HSET.
    { destruct HSET as [EX LX].
      ins. destruct x as [xl | xt xn]; ins; eauto.
      { unfold loc in LX. rewrite (wf_init_lab WF) in LX.
        desf. eauto. }
      right.
      apply in_filterP_iff; split; try now apply LX.
      apply FIN_ACTS0. split; ins. }
    ins. desf. apply in_filterP_iff in HSET.
    destruct HSET as [INX LX]. split; ins.
    now apply FIN_ACTS0. }
  forward (eapply last_exists with (s:= co ⨾ ⦗fun x => vf x b⦘)
                                   (dom := filterP W El)
                                   (a := InitEvent l)).
  { eapply acyclic_mon.
    apply trans_irr_acyclic; [apply co_irr | apply co_trans]; eauto.
    basic_solver. }
  { ins.
    assert (A: (co ⨾ ⦗fun x : actid => vf x b⦘)^? (InitEvent l) c).
    { apply rt_of_trans; try done.
      apply transitiveI.
      arewrite_id ⦗fun x : actid => vf x b⦘ at 1.
      rewrite seq_id_l.
      arewrite (co ⨾ co ⊆ co); [|done].
      apply transitiveI.
      eapply co_trans; eauto. }
    unfolder in A; desf.
    { apply in_filterP_iff; split; auto.
      by apply ACT_LIST. }
    apply in_filterP_iff.
    hahn_rewrite WF.(wf_coE) in A.
    hahn_rewrite WF.(wf_coD) in A.
    hahn_rewrite WF.(wf_col) in A.
    unfold same_loc in *; unfolder in *; desf; splits; eauto.
    apply ACT_LIST. split; ins.
    rewrite <- A3. unfold loc.
    now rewrite (wf_init_lab WF). }
  ins; desc.
  assert (A: (co ⨾ ⦗fun x : actid => vf x b⦘)^? (InitEvent l) b0).
  { apply rt_of_trans; [|by subst].
    apply transitiveI.
    arewrite_id ⦗fun x : actid => vf x b⦘ at 1.
    rewrite seq_id_l.
    arewrite (co ⨾ co ⊆ co); [|done].
    apply transitiveI.
    eapply co_trans; eauto. }
  assert (loc b0 = Some l).
  { unfolder in A; desf.
    hahn_rewrite WF.(wf_col) in A.
    unfold same_loc in *; desf; unfolder in *; congruence. }
  exists b0; red; split.
  { unfold urr, same_loc.
    unfolder in A; desf; unfolder; ins; desf; splits; try basic_solver 21; congruence. }
  unfold max_elt in *.
  unfolder in *; ins; desf; intro; desf; basic_solver 11.
Qed.

Lemma srf_in_sb_rf :
  srf ⊆ (sb ∪ rf)⁺.
Proof using.
  admit.
Admitted.

End AuxRel.