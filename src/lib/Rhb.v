From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.

Require Import AuxRel.
Require Import xmm_s_hb.

Set Implicit Arguments.

Section Rhb.
Variable G : execution.
Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'Acq'" := (fun e => is_true (is_acq lab e)).
Notation "'Rel'" := (fun e => is_true (is_rel lab e)).
Notation "'Rlx'" := (fun e => is_true (is_rlx lab e)).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'rs'" := (rs G).
Notation "'hb'" := (hb G).
Notation "'sw'" := (sw G).
Notation "'eco'" := (eco G).
Notation "'W'" := (fun e => is_true (is_w lab e)).
Notation "'R'" := (fun e => is_true (is_r lab e)).
Notation "'F'" := (fun e => is_true (is_f lab e)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).

Definition rpo_imm :=
  ⦗R ∩₁ Rlx⦘ ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ∪
  ⦗Acq⦘ ⨾ sb ∪
  sb ⨾ ⦗Rel⦘ ∪
  ⦗F ∩₁ Rel⦘ ⨾ sb ⨾ ⦗W ∩₁ Rlx⦘.
Definition rpo := rpo_imm⁺.
Definition rhb := (sb ∩ same_loc ∪ rpo ∪ sw)⁺.

Lemma rpo_imm_in_sb : rpo_imm ⊆ sb.
Proof using.
  unfold rpo_imm.
  basic_solver.
Qed.

Lemma no_rpo_imm_to_init :
  rpo_imm ≡ rpo_imm ⨾ ⦗fun e => ~is_init e⦘.
Proof using.
  split; [| basic_solver].
  unfold rpo_imm.
  rewrite !seq_union_l.
  repeat apply union_mori.
  all: rewrite !seqA.
  all: rewrite no_sb_to_init at 1.
  all: basic_solver 11.
Qed.

Lemma rpo_in_sb : rpo ⊆ sb.
Proof using.
  unfold rpo. rewrite rpo_imm_in_sb.
  apply ct_of_trans. apply sb_trans.
Qed.

Lemma no_rpo_to_init :
  rpo ≡ rpo ⨾ ⦗fun e => ~is_init e⦘.
Proof using.
  split; [| basic_solver].
  unfold rpo.
  rewrite no_rpo_imm_to_init at 1.
  apply inclusion_ct_seq_eqv_r.
Qed.

Lemma wf_rpoE :
  rpo ≡ ⦗E⦘ ⨾ rpo ⨾ ⦗E⦘.
Proof using.
  split; [| basic_solver].
  unfolder. intros x y REL.
  splits; ins.
  all: apply rpo_in_sb in REL.
  all: unfold sb in REL; unfolder in REL; desf.
Qed.

Lemma wf_rhb_immE
        (WF : Wf G) :
    (sb ∩ same_loc ∪ rpo ∪ sw) ≡ ⦗E⦘ ⨾ (sb ∩ same_loc ∪ rpo ∪ sw) ⨾ ⦗E⦘.
Proof using.
    split; [| basic_solver].
    rewrite wf_sbE, wf_rpoE, wf_swE; eauto. basic_solver 42.
Qed.

Lemma wf_rhbE
    (WF : Wf G) :
  rhb ≡ ⦗E⦘ ⨾ rhb ⨾ ⦗E⦘.
Proof using.
  apply dom_helper_3.
  unfold rhb.
  rewrite (wf_rhb_immE WF).
  rewrite ct_seq_eqv_l.
  rewrite <- seqA.
  rewrite ct_seq_eqv_r.
  basic_solver.
Qed.

Lemma no_rhb_to_init
    (WF : Wf G) :
  rhb ≡ rhb ⨾ ⦗fun e => ~is_init e⦘.
Proof using.
  split; [| basic_solver].
  unfold rhb.
  rewrite (no_sw_to_init WF) at 1.
  rewrite no_sb_to_init at 1.
  rewrite no_rpo_to_init at 1.
  rewrite seq_eqv_inter_lr.
  rewrite <- !seq_union_l.
  apply inclusion_ct_seq_eqv_r.
Qed.

Lemma rpo_imm_upward_closed s
    (SBUP : upward_closed sb s) :
  upward_closed rpo_imm s.
Proof using.
  unfold upward_closed, rpo_imm.
  unfolder. intros x y HREL IN; desf.
  all: eapply SBUP; eauto.
Qed.

Lemma rpo_upward_closed s
    (SBUP : upward_closed sb s) :
  upward_closed rpo s.
Proof using.
  unfold upward_closed, rpo.
  intros x y REL.
  apply clos_trans_tn1 in REL.
  induction REL as [y REL | y z HEAD TAIL IHREL].
  { intro HIN. eapply rpo_imm_upward_closed; eauto. }
  intro HIN. apply IHREL.
  eapply rpo_imm_upward_closed; eauto.
Qed.

Lemma rpo_to_rpo_imm a b
    (SBIMM : immediate sb a b)
    (RPO : rpo a b) :
  rpo_imm a b.
Proof using.
  unfold rpo in RPO.
  apply clos_trans_tn1 in RPO.
  destruct RPO as [y RPO | y z HEAD TAIL]; ins.
  apply clos_tn1_trans in TAIL.
  apply rpo_in_sb in TAIL.
  apply rpo_imm_in_sb in HEAD.
  exfalso. now apply SBIMM with y.
Qed.

Lemma rpo_trans : transitive rpo.
Proof using.
  unfold rpo. apply transitive_ct.
Qed.

Lemma rhb_trans : transitive rhb.
Proof using.
  unfold rhb. apply transitive_ct.
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
  transitivity (sb ⨾ ⦗Rel⦘ ⨾ sw).
  { arewrite (sw ⊆ (⦗Rel⦘) ⨾ sw) at 1; [|done].
    unfold sw. unfold release. basic_solver 42. }
  hahn_frame_r.
  unfold rpo, rpo_imm. rewrite <- ct_step.
  eauto with hahn.
Qed.

Lemma sw_sb_in_rpo :
    sw ⨾ sb ⊆ sw ⨾ rpo.
Proof using.
  transitivity (sw ⨾ ⦗Acq⦘ ⨾ sb).
  { arewrite (sw ⊆ sw ;; (⦗Acq⦘)) at 1; [|done].
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

Lemma rpo_in_rhb :
  rpo ⊆ rhb.
Proof using.
  unfold rhb. auto with hahn.
Qed.

Lemma sw_in_rhb :
  sw ⊆ rhb.
Proof using.
  unfold rhb. auto with hahn.
Qed.

Lemma sb_loc_in_rhb :
  sb ∩ same_loc ⊆ rhb.
Proof using.
  unfold rhb. auto with hahn.
Qed.

Lemma hb_helper :
    hb ≡ sb ∪ rhb.
Proof using.
  split; [| rewrite rhb_in_hb, sb_in_hb; auto with hahn].
  unfold hb, rhb. intros x y HH. apply clos_trans_t1n in HH.
  assert (IN : sw＊ ⨾ (rpo ⨾ sw＊)⁺ ⊆ sw＊ ⨾ ((sb ∩ same_loc ∪ rpo) ⨾ sw＊)⁺).
  { apply inclusion_seq_mon; [basic_solver |].
    apply inclusion_t_t. apply inclusion_seq_mon; basic_solver. }
  induction HH as [x y START | x y z STEP1 STEP2 IHSTEP].
  { destruct START as [P1 | P2]; try basic_solver.
    right. apply ct_step. basic_solver. }
  destruct STEP1 as [P1 | P2]; destruct IHSTEP as [P3 | P4].
  { left. assert (TRANS : transitive sb). apply sb_trans.
    unfold transitive in TRANS. basic_solver. }
  { assert (TRANS : transitive sb) by apply sb_trans.
    rewrite <- clos_trans_t1n_iff in STEP2.
    assert (PATH : (sb ⨾ (sb ∪ sw)⁺) x z) by basic_solver.
    apply trans_helper in PATH; eauto.
    destruct PATH as [PATH1 | PATH2]; [left; basic_solver |].
    destruct PATH2 as (x0 & (PTH1 & [EQ | NEQ])). 2 :
    { apply sb_sw_trans_trans in PTH1. assert (PTH1' := PTH1).
      apply ct_end in PTH1. destruct PTH1 as (x1 & PTH1 & (x2 & PTH2 & PTH3)).
      apply ct_end in PTH3. destruct PTH3 as (x3 & PTH3 & PTH4).
      assert (RPO : rpo x0 z).
      { apply rpo_sb_end with (x0 := x0) (x := x3); eauto. }
      right. apply ct_ct. unfold seq. exists x0. split.
      { apply ct_unionE. right. apply IN.
        unfold seq. exists x. split; vauto.
        assert (EQ : (fun x4 y0 : actid =>
              exists z0 : actid, rpo x4 z0 /\ sw＊ z0 y0)⁺ ≡ (rpo ⨾ sw＊)⁺).
        { unfold seq. basic_solver. }
        apply EQ.
        apply inclusion_t_t with (r := rpo ⨾ sw⁺); vauto.
        apply inclusion_seq_mon; vauto.
        apply inclusion_t_rt. }
      apply ct_step. basic_solver. }
    destruct EQ. apply sb_sw_trans_trans in PTH1. assert (PTH1' := PTH1).
    right. apply ct_unionE. right. apply IN. unfold seq. exists x. split; vauto.
    assert (EQ : (fun x4 y0 : actid =>
          exists z0 : actid, rpo x4 z0 /\ sw＊ z0 y0)⁺ ≡ (rpo ⨾ sw＊)⁺).
    { unfold seq. basic_solver. }
    apply EQ.
    apply inclusion_t_t with (r := rpo ⨾ sw⁺); basic_solver. }
  { enough (RR : sw x y /\ rpo y z).
    { right.
      apply rhb_trans with y.
      all: try now apply sw_in_rhb, RR.
      all: try now apply rpo_in_rhb, RR. }
    split; auto.
    apply rpo_sb_end with (x := x); eauto. }
  right. apply rhb_trans with y; auto.
  now apply sw_in_rhb.
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

Lemma rhb_eco_irr_equiv
    (WF  : Wf G):
  irreflexive (rhb ⨾ eco) <-> irreflexive (hb ⨾ eco).
Proof using.
    split.
    { intros HH. unfold irreflexive. intros x PATH.
      destruct PATH as (x0 & PTH1 & PTH2).
      assert (SAME_LOC : same_loc x x0). apply loceq_eco in PTH2; eauto.
      unfold same_loc; eauto. assert (RHB : rhb x x0).
      { eapply hb_locs. basic_solver. }
      destruct HH with (x := x). basic_solver. }
    intros IR. apply irreflexive_inclusion
                    with (r' := hb ⨾ eco); eauto.
    apply inclusion_seq_mon. apply rhb_in_hb; eauto. vauto.
Qed.

Lemma sw_with_rpo dtrmt
    (SUBE : dtrmt ⊆₁ E)
    (SB : sb ⨾ ⦗dtrmt⦘ ⊆ ⦗dtrmt⦘ ⨾ sb ⨾ ⦗dtrmt⦘)
    (RPO : rpo ⨾ ⦗E \₁ dtrmt⦘ ⊆ ⦗dtrmt⦘ ⨾ rpo ⨾ ⦗E \₁ dtrmt⦘) :
  sw ⨾ ⦗E \₁ dtrmt⦘ ⊆
    dtrmt × (E \₁ dtrmt) ∪
    ⦗Rel⦘ ⨾ rs ⨾ rf ⨾ ⦗Rlx⦘ ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⨾ ⦗E \₁ dtrmt⦘.
Proof using.
  unfold sw, release.
  rewrite !seqA.
  rewrite crE at 1.
  rewrite seq_union_l, !seq_union_r,
          seq_id_l, !seqA.
  rewrite unionC with (r1 := dtrmt × (E \₁ dtrmt)).
  apply union_mori.
  { seq_rewrite <- !id_inter.
    repeat apply seq_mori; auto with hahn.
    basic_solver. }
  unfold rs. rewrite !seqA.
  arewrite (⦗Rel⦘ ⨾ ⦗F⦘ ⨾ sb ⨾ ⦗Rlx⦘ ⨾ ⦗W⦘ ⊆ rpo ⨾ ⦗Rlx⦘ ⨾ ⦗W⦘).
  { unfold rpo.
    seq_rewrite <- !id_inter.
    rewrite <- inclusion_step_t
       with (r' := rpo_imm)
            (r := ⦗Rel ∩₁ F⦘ ⨾ sb ⨾ ⦗Rlx ∩₁ W⦘).
    all: unfold rpo_imm; basic_solver 11. }
  arewrite (rpo ⊆ rpo ⨾ ⦗dtrmt ∪₁ E \₁ dtrmt⦘).
  { rewrite <- set_union_strict.
    rewrite set_union_absorb_l
       with (s := dtrmt) (s' := E).
    all: auto.
    rewrite wf_rpoE at 1.
    basic_solver 11. }
  rewrite id_union, seq_union_l, !seq_union_r.
  apply inclusion_union_l.
  { arewrite (rpo ⨾ ⦗dtrmt⦘ ⊆ ⦗dtrmt⦘ ⨾ sb ⨾ ⦗dtrmt⦘).
    { now rewrite rpo_in_sb. }
    basic_solver 11. }
  rewrite <- seqA, RPO.
  basic_solver 11.
Qed.

End Rhb.