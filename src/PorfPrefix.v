From imm Require Import Events Execution imm_s_hb.
From imm Require Import imm_s_hb.

Require Import Program.Basics.
Require Import AuxRel AuxDef Core.
Require Import Srf Rhb.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.

Section PorfPrefix.

Variable X X' : WCore.t.
Variable e : actid.
Variable l : label.

Notation "'G''" := (WCore.G X').
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
Notation "'rpo''" := (rpo G').
Notation "'rpo_imm''" := (rpo_imm G').

Notation "'G'" := (WCore.G X).
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
Notation "'rpo'" := (rpo G).
Notation "'rpo_imm'" := (rpo_imm G).

Lemma porf_pref_rs
    (WF : Wf G)
    (EQL : eq_dom E lab' lab)
    (SB : sb' ⨾ ⦗E⦘ ≡ sb ⨾ ⦗E⦘)
    (RF : rf' ⨾ ⦗E⦘ ≡ rf ⨾ ⦗E⦘)
    (RMW : rmw' ⨾ ⦗E⦘ ≡ rmw ⨾ ⦗E⦘) :
  rs' ⨾ ⦗E⦘ ≡ rs ⨾ ⦗E⦘.
Proof using.
  assert (DOMA : doma ((rf' ⨾ rmw') ⨾ ⦗E⦘) E).
  { rewrite !seqA, RMW, (wf_rmwE WF).
    rewrite !seqA. seq_rewrite RF.
    rewrite (wf_rfE WF), !seqA.
    basic_solver. }
  assert (EQW : ⦗W'⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ ⦗W⦘).
  { rewrite <- !id_inter, set_interC. apply eqv_rel_more.
    unfold is_w. unfolder. split; intros x (XINE & LAB).
    all: splits; ins.
    all: rewrite EQL in *; ins. }
  unfold rs at 1. rewrite !seqA.
  arewrite ((rf' ⨾ rmw')＊ ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ (rf ⨾ rmw)＊ ⨾ ⦗E⦘).
  { rewrite <- !cr_of_ct, !crE, !seq_union_l.
    rewrite clos_trans_doma_r_strong; ins.
    rewrite !seqA, RMW. rewrite (wf_rmwE WF) at 1.
    rewrite !seqA. seq_rewrite RF.
    rewrite seq_id_l, seq_union_r, !seqA.
    apply union_more; [basic_solver |].
    rewrite ct_seq_eqv_l at 1.
    arewrite (⦗E⦘ ⨾ rf ⨾ ⦗E⦘ ⨾ rmw ⨾ ⦗E⦘ ⨾ ⦗E⦘ ≡ rf ⨾ rmw ⨾ ⦗E⦘).
    { seq_rewrite <- (wf_rfE WF). basic_solver 11. }
    rewrite <- seqA, (ct_seq_eqv_r E (rf ⨾ rmw)).
    arewrite ((rf ⨾ rmw) ⨾ ⦗E⦘ ≡ rf ⨾ rmw); ins.
    rewrite (wf_rmwE WF). basic_solver 11. }
  seq_rewrite EQW. rewrite !seqA.
  arewrite ((sb' ∩ same_loc')^? ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ (sb ∩ same_loc)^?).
  { rewrite !crE, seq_union_l, seq_union_r.
    apply union_more; [basic_solver |].
    rewrite <- seq_eqv_inter_lr, SB, <- seq_eqv_inter_ll.
    arewrite (sb ⨾ ⦗E⦘ ≡ sb) by (unfold sb; basic_solver).
    arewrite (⦗E⦘ ⨾ sb ≡ sb) by (unfold sb; basic_solver).
    unfold sb, same_loc, loc. unfolder.
    split; intros x y ((XINE & ESB & YINE) & EQ).
    all: splits; ins.
    all: rewrite 2!EQL in *; ins. }
  seq_rewrite EQW. rewrite !seqA.
  rewrite (wf_rsE WF), seq_union_l, !seqA.
  unfold rs. basic_solver 20.
Qed.

Lemma porf_pref_release
    (WF : Wf G)
    (EQL : eq_dom E lab' lab)
    (SB : sb' ⨾ ⦗E⦘ ≡ sb ⨾ ⦗E⦘)
    (RF : rf' ⨾ ⦗E⦘ ≡ rf ⨾ ⦗E⦘)
    (RMW : rmw' ⨾ ⦗E⦘ ≡ rmw ⨾ ⦗E⦘) :
  release' ⨾ ⦗E⦘ ≡ release ⨾ ⦗E⦘.
Proof using.
  unfold release at 1. rewrite !seqA.
  rewrite (porf_pref_rs WF); ins.
  arewrite (rs ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ rs ⨾ ⦗E⦘).
  { rewrite (wf_rsE WF) at 1. rewrite seq_union_l.
    split; [| basic_solver 7].
    arewrite (⦗W⦘ ⨾ ⦗E⦘ ⊆ ⦗E⦘ ⨾ rs ⨾ ⦗E⦘); [| basic_solver].
    unfold rs. basic_solver 11. }
  rewrite crE.
  seq_rewrite seq_union_l.
  rewrite seq_id_l, !seqA.
  seq_rewrite SB. rewrite !seqA.
  arewrite (sb ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘).
  { unfold sb. rewrite !seqA.
    seq_rewrite <- !id_inter.
    now rewrite set_interK. }
  arewrite (⦗F'⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ ⦗F⦘).
  { rewrite <- !id_inter, set_interC. apply eqv_rel_more.
    unfold is_f. unfolder. split; intros x (XINE & LAB).
    all: splits; ins.
    all: rewrite EQL in *; ins. }
  rewrite <- seq_union_r.
  arewrite (⦗Rel'⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ ⦗Rel⦘).
  { rewrite <- !id_inter, set_interC. apply eqv_rel_more.
    unfold is_rel, mod. unfolder. split; intros x (XINE & LAB).
    all: splits; ins.
    all: rewrite EQL in *; ins. }
  arewrite (release ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ release ⨾ ⦗E⦘).
  { rewrite (wf_releaseE WF) at 1.  rewrite seq_union_l.
    split; [| basic_solver 7].
    arewrite (⦗W ∩₁ Rel⦘ ⨾ ⦗E⦘ ⊆ ⦗E⦘ ⨾ release ⨾ ⦗E⦘); [| basic_solver].
    unfold release. rewrite <- inclusion_id_cr, seq_id_l.
    unfold rs. rewrite <- cr_of_ct, <- !inclusion_id_cr.
    seq_rewrite !seq_id_r. basic_solver 11. }
  unfold release.
  rewrite crE, !seq_union_l, seq_id_l.
  unfold sb. basic_solver 42.
Qed.

Lemma porf_pref_sw
    (WF : Wf G)
    (EQL : eq_dom E lab' lab)
    (SB : sb' ⨾ ⦗E⦘ ≡ sb ⨾ ⦗E⦘)
    (RF : rf' ⨾ ⦗E⦘ ≡ rf ⨾ ⦗E⦘)
    (RMW : rmw' ⨾ ⦗E⦘ ≡ rmw ⨾ ⦗E⦘) :
  sw' ⨾ ⦗E⦘ ≡ sw ⨾ ⦗E⦘.
Proof using.
  unfold sw at 1. rewrite !seqA.
  arewrite (⦗Acq'⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ ⦗Acq⦘).
  { rewrite <- !id_inter, set_interC. apply eqv_rel_more.
    unfold is_acq, mod. unfolder. split; intros x (XINE & LAB).
    all: splits; ins.
    all: rewrite EQL in *; ins. }
  rewrite crE. seq_rewrite seq_union_l.
  rewrite seq_id_l, !seqA.
  arewrite (⦗F'⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ ⦗F⦘).
  { rewrite <- !id_inter, set_interC. apply eqv_rel_more.
    unfold is_f. unfolder. split; intros x (XINE & LAB).
    all: splits; ins.
    all: rewrite EQL in *; ins. }
  seq_rewrite SB.
  arewrite (sb ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ sb).
  { unfold sb. rewrite !seqA.
    seq_rewrite <- !id_inter.
    now rewrite set_interK. }
  seq_rewrite <- seq_union_r.
  seq_rewrite RF.
  arewrite (rf ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ rf).
  { rewrite (wf_rfE WF). basic_solver. }
  seq_rewrite (porf_pref_release WF); ins.
  arewrite (release ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ release).
  { rewrite (wf_releaseE WF), seq_union_l, seq_union_r.
    basic_solver 11. }
  arewrite (⦗Acq⦘ ∪ sb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ≡ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘).
  { now rewrite crE, seq_union_l, seq_id_l, !seqA. }
  replace (release ⨾ rf ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘)
    with sw; ins.
  rewrite (wf_swE WF). basic_solver.
Qed.

Lemma porf_pref_hb
    (WF : Wf G)
    (EQL : eq_dom E lab' lab)
    (SB : sb' ⨾ ⦗E⦘ ≡ sb ⨾ ⦗E⦘)
    (RF : rf' ⨾ ⦗E⦘ ≡ rf ⨾ ⦗E⦘)
    (RMW : rmw' ⨾ ⦗E⦘ ≡ rmw ⨾ ⦗E⦘) :
  hb' ⨾ ⦗E⦘ ≡ hb ⨾ ⦗E⦘.
Proof using.
  assert (DOMA : doma ((sb' ∪ sw') ⨾ ⦗E⦘) E).
  { rewrite seq_union_l, SB, (porf_pref_sw WF); ins.
    rewrite (wf_swE WF). unfold sb. basic_solver 11. }
  unfold hb.
  rewrite clos_trans_doma_r_strong; ins.
  rewrite seq_union_l, seq_union_r.
  rewrite SB, (porf_pref_sw WF); ins.
  rewrite <- (wf_swE WF), <- wf_sbE.
  change ((sb ∪ sw)⁺) with hb.
  rewrite (wf_hbE WF). basic_solver.
Qed.

Lemma porf_pref_vf
    (WF : Wf G)
    (ACTS : E ⊆₁ E')
    (EQL : eq_dom E lab' lab)
    (SB : sb' ⨾ ⦗E⦘ ≡ sb ⨾ ⦗E⦘)
    (RF : rf' ⨾ ⦗E⦘ ≡ rf ⨾ ⦗E⦘)
    (RMW : rmw' ⨾ ⦗E⦘ ≡ rmw ⨾ ⦗E⦘) :
  vf' ⨾ ⦗E⦘ ≡ vf ⨾ ⦗E⦘.
Proof using.
  unfold vf. rewrite !seqA.
  arewrite (hb'^? ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ hb^? ⨾ ⦗E⦘).
  { rewrite !crE, !seq_union_l, seq_union_r.
    apply union_more; [basic_solver |].
    rewrite (porf_pref_hb WF); ins.
    rewrite (wf_hbE WF) at 1. basic_solver. }
  arewrite (rf'^? ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ rf^?).
  { rewrite !crE, !seq_union_l, seq_union_r.
    apply union_more; [basic_solver |].
    rewrite RF. rewrite (wf_rfE WF). basic_solver. }
  arewrite (⦗W'⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ ⦗W⦘).
  { rewrite <- !id_inter, set_interC. apply eqv_rel_more.
    unfold is_w. unfolder. split; intros x (XINE & LAB).
    all: splits; ins.
    all: rewrite EQL in *; ins. }
  seq_rewrite <- id_inter.
  now rewrite set_inter_absorb_l; ins.
Qed.

Lemma porf_pref_srf
    (WF : Wf G)
    (ACTS : E ⊆₁ E')
    (EQL : eq_dom E lab' lab)
    (SB : sb' ⨾ ⦗E⦘ ≡ sb ⨾ ⦗E⦘)
    (RF : rf' ⨾ ⦗E⦘ ≡ rf ⨾ ⦗E⦘)
    (CO : ⦗E⦘ ⨾ co' ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ co ⨾ ⦗E⦘)
    (RMW : rmw' ⨾ ⦗E⦘ ≡ rmw ⨾ ⦗E⦘) :
  srf' ⨾ ⦗E⦘ ≡ srf ⨾ ⦗E⦘.
Proof using.
  unfold srf at 1.
  rewrite !seq_eqv_minus_r, !seqA.
  arewrite (⦗R'⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ ⦗R⦘).
  { rewrite <- !id_inter, set_interC. apply eqv_rel_more.
    unfold is_r. unfolder. split; intros x (XINE & LAB).
    all: splits; ins.
    all: rewrite EQL in *; ins. }
  seq_rewrite <- seq_eqv_inter_lr.
  rewrite !seqA.
  arewrite (sb' ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ sb).
  { rewrite SB, wf_sbE. basic_solver. }
  seq_rewrite (porf_pref_vf WF); ins.
  arewrite (vf ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ vf).
  { rewrite (wf_vfE WF). basic_solver. }
  arewrite ((⦗E⦘ ⨾ vf ⨾ sb) ∩ same_loc' ≡ (⦗E⦘ ⨾ vf ⨾ sb) ∩ same_loc).
  { seq_rewrite wf_sbE. unfold same_loc, loc. unfolder.
    split; intros x y ((XINE & z & VF & ZINE & ESB & YINE) & LOC).
    all: splits; eauto.
    all: rewrite 2!EQL in *; ins. }
  arewrite ((⦗E⦘ ⨾ vf ⨾ sb) ∩ same_loc ⨾ ⦗R⦘ \ co' ⨾ ⦗E⦘ ⨾ vf ⨾ sb ≡
            (⦗E⦘ ⨾ vf ⨾ sb) ∩ same_loc ⨾ ⦗R⦘ \ ⦗E⦘ ⨾ co' ⨾ ⦗E⦘ ⨾ vf ⨾ sb).
  { set (A := (⦗E⦘ ⨾ vf ⨾ sb) ∩ same_loc ⨾ ⦗R⦘).
    set (B := co' ⨾ ⦗E⦘ ⨾ vf ⨾ sb).
    unfolder. split; intros x y HREL; desf.
    all: splits; ins; try tauto.
    enough (HIN : E x) by tauto.
    subst A. unfolder in HREL. desf. }
  seq_rewrite CO. seq_rewrite <- (wf_coE WF).
  rewrite seq_eqv_inter_ll, !seqA, seq_eqv_minus_ll.
  change ((vf ⨾ sb) ∩ same_loc ⨾ ⦗R⦘ \ co ⨾ vf ⨾ sb)
    with srf.
  rewrite wf_srfE. basic_solver.
Qed.

Lemma porf_pref_rpoimm
    (WF : Wf G)
    (EQL : eq_dom E lab' lab)
    (SB : sb' ⨾ ⦗E⦘ ≡ sb ⨾ ⦗E⦘) :
  rpo_imm' ⨾ ⦗E⦘ ≡ rpo_imm ⨾ ⦗E⦘.
Proof using.
  unfold rpo_imm.
  rewrite !seq_union_l, !seqA.
  arewrite (⦗F' ∩₁ Acq'⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ ⦗F ∩₁ Acq⦘ ⨾ ⦗E⦘).
  { unfolder. split; ins; desf.
    all: splits; ins.
    all: unfold is_acq, is_f, mod in *.
    all: rewrite EQL in *; ins. }
  arewrite (⦗W' ∩₁ Rlx'⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ ⦗W ∩₁ Rlx⦘ ⨾ ⦗E⦘).
  { unfolder. split; ins; desf.
    all: splits; ins.
    all: unfold is_rlx, is_w, mod in *.
    all: rewrite EQL in *; ins. }
  arewrite (⦗Rel'⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ ⦗Rel⦘ ⨾ ⦗E⦘).
  { unfolder. split; ins; desf.
    all: splits; ins.
    all: unfold is_rel, mod in *.
    all: rewrite EQL in *; ins. }
  seq_rewrite !SB. rewrite !seqA.
  arewrite (sb ≡ ⦗E⦘ ⨾ sb).
  { rewrite wf_sbE. basic_solver. }
  arewrite (⦗R' ∩₁ Rlx'⦘ ⨾ ⦗E⦘ ≡ ⦗R ∩₁ Rlx⦘ ⨾ ⦗E⦘).
  { unfolder. split; ins; desf.
    all: splits; ins.
    all: unfold is_rlx, is_r, mod in *.
    all: rewrite EQL in *; ins. }
  arewrite (⦗Acq'⦘ ⨾ ⦗E⦘ ≡ ⦗Acq⦘ ⨾ ⦗E⦘).
  { unfolder. split; ins; desf.
    all: splits; ins.
    all: unfold is_acq, mod in *.
    all: rewrite EQL in *; ins. }
  arewrite (⦗F' ∩₁ Rel'⦘ ⨾ ⦗E⦘ ≡ ⦗F ∩₁ Rel⦘ ⨾ ⦗E⦘).
  { unfolder. split; ins; desf.
    all: splits; ins.
    all: unfold is_f, is_rel, mod in *.
    all: rewrite EQL in *; ins. }
  seq_rewrite <- !wf_sbE.
  assert (SBR : ⦗E⦘ ⨾ sb ≡ sb).
  { rewrite wf_sbE. basic_solver. }
  now seq_rewrite !SBR.
Qed.

Lemma porf_pref_rpo
    (WF : Wf G)
    (EQL : eq_dom E lab' lab)
    (ESB : sb' ⨾ ⦗E⦘ ≡ sb ⨾ ⦗E⦘) :
  rpo' ⨾ ⦗E⦘ ≡ rpo ⨾ ⦗E⦘.
Proof using.
  unfold rpo.
  rewrite !ct_l_upward_closed.
  { rewrite porf_pref_rpoimm; ins. }
  all: apply rpo_imm_upward_closed.
  all: unfold upward_closed.
  { unfold sb. basic_solver. }
  intros x y SB XINE.
  enough (SB' : sb x y).
  { generalize SB'. unfold sb.
    basic_solver. }
  enough (SB' : (sb' ⨾ ⦗E⦘) x y).
  { apply ESB in SB'. generalize SB'.
    basic_solver. }
  basic_solver.
Qed.

End PorfPrefix.