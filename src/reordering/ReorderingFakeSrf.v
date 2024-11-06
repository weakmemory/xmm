(*
  A set of weapons to deal with the mischievous
  srf relation.

  Srf cannot be constructed by 'definition', as
  it leads to a tough recusion.

  This is mitigated by constructing a 'fake' srf,
  inside some subgraph. It is then shown that the
  'fake' srf equal to normal srf.

  This file also provides a theorem for adjusting
  a label, so its value matches the one in srf
*)

Require Import ReordSimrel.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import PorfPrefix.
Require Import AddEventWf.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics Lia.
Require Import xmm_s_hb.

Section FakeSrf.

(*
    G_s -- the subgraph for srf search
    G_s' -- the graph we want to find srf for
    e -- the event we want to find fake srf for
    l_e -- e's desired label
*)
Variable G_s G_s' : execution.
Variable e : actid.
Variable l_e : label.

Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'vf_s'" := (vf G_s).
Notation "'vf_rhb_s'" := (vf_rhb G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'hb_s'" := (hb G_s).
Notation "'rhb_s'" := (rhb G_s).
Notation "'W_s'" := (fun x => is_true (is_w lab_s x)).
Notation "'R_s'" := (fun x => is_true (is_r lab_s x)).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).

Notation "'lab_s''" := (lab G_s').
Notation "'val_s''" := (val lab_s').
Notation "'loc_s''" := (loc lab_s').
Notation "'same_loc_s''" := (same_loc lab_s').
Notation "'E_s''" := (acts_set G_s').
Notation "'sb_s''" := (sb G_s').
Notation "'rf_s''" := (rf G_s').
Notation "'co_s''" := (co G_s').
Notation "'vf_s''" := (vf G_s').
Notation "'srf_s''" := (srf G_s').
Notation "'rmw_s''" := (rmw G_s').
Notation "'W_s''" := (fun x => is_true (is_w lab_s' x)).
Notation "'R_s''" := (fun x => is_true (is_r lab_s' x)).
Notation "'Loc_s_'' l" := (fun e => loc_s' e = l) (at level 1).

Definition fake_sb :=
  ⦗E_s ∪₁ eq e⦘ ⨾ ext_sb ⨾⦗ E_s ∪₁ eq e⦘.

(*
  NOTE:
  fake_srf purposefully doesn't
  use anything from G_s' to avoid the
  dependency cycle.

  This way G_s' can be constructed safely
  by using fake_srf.
*)
Definition fake_srf :=
  (
    ⦗Loc_s_ (WCore.lab_loc l_e)⦘ ⨾ vf_s ⨾ fake_sb
  ) \ (co_s ⨾ vf_s ⨾ fake_sb).
Definition fake_srf_rhb :=
  (
    ⦗Loc_s_ (WCore.lab_loc l_e)⦘ ⨾ vf_rhb_s ⨾ fake_sb
  ) \ (co_s ⨾ vf_rhb_s ⨾ fake_sb).

Lemma fake_srfE_left :
  fake_srf ⊆ ⦗E_s⦘ ⨾ fake_srf.
Proof using.
  unfold fake_srf. rewrite <- seq_eqv_minus_ll.
  apply minus_rel_mori; [| red; auto with hahn].
  seq_rewrite seq_eqvC.
  rewrite wf_vfE_left at 1.
  rewrite 2!seqA. reflexivity.
Qed.

Lemma fake_srfD_left :
  fake_srf ⊆ ⦗W_s⦘ ⨾ fake_srf.
Proof using.
  unfold fake_srf. rewrite <- seq_eqv_minus_ll.
  apply minus_rel_mori; [| red; auto with hahn].
  seq_rewrite seq_eqvC. rewrite vf_d_left at 1.
  rewrite 2!seqA. reflexivity.
Qed.

Lemma fake_srfl :
  fake_srf ⊆ ⦗Loc_s_ (WCore.lab_loc l_e)⦘ ⨾ fake_srf.
Proof using.
  unfold fake_srf. rewrite <- seq_eqv_minus_ll.
  apply minus_rel_mori; [| red; auto with hahn].
  seq_rewrite seq_eqvK. reflexivity.
Qed.

Lemma fake_srf_in_vfsb :
  fake_srf ⊆ vf_s ⨾ fake_sb.
Proof using.
  unfold fake_srf.
  rewrite inclusion_minus_rel, inclusion_seq_eqv_l.
  reflexivity.
Qed.

Lemma fake_srff
    (WF : Wf G_s) :
  functional fake_srf⁻¹.
Proof using.
  rewrite fake_srfE_left, fake_srfD_left, fake_srfl.
  unfolder. intros x y z (((YINE & YW) & YL) & SRF1) (((ZINE & ZW) & ZL) & SRF2).
  destruct (classic (y = z)) as [EQ|NEQ]; ins.
  destruct (wf_co_total WF)
      with (a := y) (b := z)
           (ol := WCore.lab_loc l_e)
        as [CO|CO].
  { unfold set_inter; splits; assumption. }
  { unfold set_inter; splits; assumption. }
  { exact NEQ. }
  { exfalso. apply SRF1.
    apply fake_srf_in_vfsb in SRF2.
    red; eauto. }
  exfalso. apply SRF2.
  apply fake_srf_in_vfsb in SRF1.
  red; eauto.
Qed.

(*
  NOTE:
  this statement is much weaker, than srf_exists,
  but it is sufficient for most stuff
*)
Lemma fake_srf_exists
    (WF : Wf G_s) :
  exists w,
    eq_opt w ≡₁ dom_rel (fake_srf ⨾ ⦗eq e ∩₁ WCore.lab_is_r l_e⦘).
Proof using.
  destruct classic
      with (dom_rel (fake_srf ⨾ ⦗eq e ∩₁ WCore.lab_is_r l_e⦘) ≡₁ ∅)
        as [EMP|NEMP].
  { exists None. rewrite EMP. auto with hahn. }
  apply set_nonemptyE in NEMP. destruct NEMP as (x & DOM).
  exists (Some x). rewrite eq_opt_someE.
  split; red; [congruence|]. intros x' DOM'.
  apply (fake_srff WF) with e.
  { unfolder in DOM. desf. }
  unfolder in DOM'. desf.
Qed.

Lemma fake_srf_lab_adjustment
    (WF : Wf G_s) :
  exists l_e',
    << U2V : same_label_u2v l_e' l_e >> /\
    << VAL : dom_rel (fake_srf ⨾ ⦗eq e ∩₁ WCore.lab_is_r l_e⦘) ⊆₁ Val_s_ (WCore.lab_val l_e') >>.
Proof using.
  destruct (fake_srf_exists WF)
        as (w & SRF_W).
  destruct w as [w|].
  { assert (ISR : WCore.lab_is_r l_e e).
    { unfolder in SRF_W. destruct SRF_W as [ISR _].
      clear - ISR. destruct ISR with w; desf. }
    assert (ISW : W_s w).
    { unfold fake_srf, vf in SRF_W.
      unfolder in SRF_W. destruct SRF_W as [ISW _].
      destruct ISW with w; desf. }
    red in ISR.
    destruct l_e
          as [aex amo al av | axmo amo al av | amo]
          eqn:HEQA; ins.
    unfold is_w in ISW.
    destruct (lab_s w)
          as [wex wmo wl wv | wxmo wmo wl wv | wmo]
          eqn:HEQW; ins.
    exists (Aload aex amo al wv).
    split; red.
    { red. desf. }
    arewrite (dom_rel (fake_srf ⨾ ⦗eq e ∩₁ ⊤₁⦘) ⊆₁ Val_s_ (val_s w)).
    { rewrite <- SRF_W. clear. basic_solver. }
    unfold val. rewrite HEQW; ins. }
  exists l_e. split; red.
  { red. desf. }
  rewrite <- SRF_W. clear. basic_solver.
Qed.

Lemma fake_srf_is_srf
    (WF : Wf G_s)
    (SB : sb_s' ≡ fake_sb)
    (NIN : ~E_s e)
    (LAB : lab_s' = upd lab_s e l_e)
    (VF : vf_s' ⨾ sb_s' ⨾ ⦗eq e⦘ ≡ vf_s ⨾ sb_s' ⨾ ⦗eq e⦘)
    (CO : co_s' ⨾ ⦗E_s⦘ ≡ co_s ⨾ ⦗E_s⦘) :
  fake_srf ⨾ ⦗eq e ∩₁ WCore.lab_is_r l_e⦘ ≡
    srf_s' ⨾ ⦗eq e ∩₁ WCore.lab_is_r l_e⦘.
Proof using.
  unfold fake_srf, srf.
  rewrite !seq_eqv_minus_r, !seqA, <- id_inter.
  arewrite (
    R_s' ∩₁ (eq e ∩₁ WCore.lab_is_r l_e) ≡₁
    eq e ∩₁ WCore.lab_is_r l_e
  ).
  { rewrite LAB. clear. unfold WCore.lab_is_r.
    unfolder. split; ins; desf.
    unfold is_r. now rewrite upds. }
  rewrite id_inter.
  arewrite (
    (vf_s' ⨾ sb_s') ∩ same_loc_s' ⨾ ⦗eq e⦘ ≡
    (vf_s' ⨾ sb_s' ⨾ ⦗eq e⦘) ∩ (same_loc_s' ⨾ ⦗eq e⦘)
  ).
  { basic_solver 11. }
  seq_rewrite <- seq_eqv_inter_rr.
  rewrite <- SB.
  seq_rewrite !VF.
  rewrite !seqA.
  arewrite (co_s' ⨾ vf_s ≡ co_s ⨾ vf_s).
  { rewrite wf_vfE_left. seq_rewrite CO.
    now rewrite seqA. }
  apply minus_rel_more; auto.
  transitivity (
    (⦗Loc_s_ (WCore.lab_loc l_e)⦘ ⨾ (vf_s ⨾ sb_s' ⨾ ⦗eq e⦘)) ⨾ ⦗WCore.lab_is_r l_e⦘
  ).
  { now rewrite !seqA. }
  remember (vf_s ⨾ sb_s' ⨾ ⦗eq e⦘)
        as vfsb.
  rewrite <- seqA, seq_eqv_inter_rr.
  apply seq_more; auto.
  arewrite (vfsb ≡ ⦗E_s⦘ ⨾ vfsb).
  { subst vfsb. rewrite wf_vfE_left at 1.
    clear. basic_solver. }
  unfold same_loc. rewrite LAB. subst vfsb.
  clear - NIN.
  unfolder. split; ins; desf; splits; eauto.
  all: unfold loc, WCore.lab_loc in *.
  all: rewrite ?upds in *.
  all: rewrite ?updo in *; congruence.
Qed.

Lemma fake_sb_trans :
  transitive fake_sb.
Proof using.
  unfolder. ins. desf.
  unfold fake_sb in *.
  unfolder in *; splits; desf; eauto.
  all: eapply ext_sb_trans; eauto.
Qed.

Lemma vf_fake_sb :
  vf_s ⨾ fake_sb ≡ vf_rhb_s ⨾ fake_sb.
Proof using.
  unfold vf, vf_rhb.
  rewrite !seqA.
  split; [| now rewrite rhb_in_hb].
  rewrite hb_helper, cr_union_r,
          seq_union_l.
  arewrite (sb_s ⊆ fake_sb).
  { unfold sb, fake_sb. unfolder.
    ins. desf; splits; eauto. }
  rewrite rewrite_trans by apply fake_sb_trans.
  basic_solver 11.
Qed.

Lemma fake_srf_with_rhb :
  fake_srf ≡ fake_srf_rhb.
Proof using.
  unfold fake_srf, fake_srf_rhb.
  now rewrite vf_fake_sb.
Qed.

End FakeSrf.

Lemma fake_srf_u2v G e l_e l_e'
    (U2V : same_label_u2v l_e l_e') :
  fake_srf G e l_e ≡ fake_srf G e l_e'.
Proof using.
  unfold fake_srf.
  apply minus_rel_more; auto.
  repeat apply seq_more; auto.
  apply eqv_rel_more.
  unfolder.
  unfold WCore.lab_loc, loc, same_label_u2v in *.
  split; ins; do 2 desf.
Qed.