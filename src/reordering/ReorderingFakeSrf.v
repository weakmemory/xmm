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
Notation "'rmw_s'" := (rmw G_s).
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

Lemma fake_srfE_left
    (WF : Wf G_s) :
  fake_srf ⊆ ⦗E_s⦘ ⨾ fake_srf.
Proof using.
  (* { unfold srf_s'. rewrite <- seq_eqv_minus_ll.
    apply minus_rel_mori; [| red; auto with hahn].
    seq_rewrite seq_eqvC. rewrite VFE at 1.
    rewrite 2!seqA. reflexivity. } *)
Admitted.

Lemma fake_srfD_left
    (WF : Wf G_s) :
  fake_srf ⊆ ⦗W_s⦘ ⨾ fake_srf.
Proof using.
  (* { unfold srf_s'. rewrite <- seq_eqv_minus_ll.
    apply minus_rel_mori; [| red; auto with hahn].
    seq_rewrite seq_eqvC. rewrite vf_d_left at 1.
    rewrite 2!seqA. reflexivity. } *)
Admitted.

Lemma fake_srfl
    (WF : Wf G_s) :
  fake_srf ⊆ ⦗Loc_s_ (WCore.lab_loc l_e)⦘ ⨾ fake_srf.
Proof using.
  (* { unfold srf_s'. rewrite <- seq_eqv_minus_ll.
    apply minus_rel_mori; [| red; auto with hahn].
    seq_rewrite seq_eqvK. reflexivity. } *)
Admitted.

Lemma fake_srf_in_vfsb
    (WF : Wf G_s) :
  fake_srf ⊆ vf_s ⨾ sb_s'.
Proof using.
  (* { unfold srf_s'. clear.
    rewrite inclusion_minus_rel, inclusion_seq_eqv_l.
    reflexivity. } *)
Admitted.

Lemma fake_srff
    (WF : Wf G_s) :
  functional fake_srf⁻¹.
Proof using.
  (* { rewrite SRFE, SRFD, SRFL. clear - WF_S SRFVF.
    unfolder. intros x y z (((YINE & YW) & YL) & SRF1) (((ZINE & ZW) & ZL) & SRF2).
    destruct (classic (y = z)) as [EQ|NEQ]; ins.
    destruct (wf_co_total WF_S) with (a := y) (b := z)
                        (ol := WCore.lab_loc l_a) as [CO|CO].
    { unfold set_inter; splits; assumption. }
    { unfold set_inter; splits; assumption. }
    { exact NEQ. }
    { exfalso. apply SRF1. apply SRFVF in SRF2.
      clear - CO SRF2. red; eauto. }
    exfalso. apply SRF2. apply SRFVF in SRF1.
    clear - CO SRF1. red; eauto. } *)
Admitted.

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
  (* { clear - FUN.
    destruct classic
        with (dom_rel (srf_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘) ≡₁ ∅)
          as [EMP|NEMP].
    { exists None. rewrite EMP. clear. auto with hahn. }
    apply set_nonemptyE in NEMP. destruct NEMP as (x & DOM).
    exists (Some x). rewrite eq_opt_someE.
    split; red; [congruence|]. intros x' DOM'.
    apply FUN with b_t; red.
    { clear - DOM. unfolder in DOM. desf. }
    clear - DOM'. unfolder in DOM'. desf. } *)
Admitted.

Lemma fake_srf_lab_adjustment
    (WF : Wf G_s) :
  exists l_e',
    << U2V : same_label_u2v l_e' l_e >> /\
    << VAL : dom_rel (fake_srf ⨾ ⦗eq e ∩₁ WCore.lab_is_r l_e⦘) ⊆₁ Val_s_ (WCore.lab_val l_e') >>.
Proof using.
  (* { destruct w as [w|].
    { assert (ISR : WCore.lab_is_r l_a b_t).
      { unfolder in SRF_W. destruct SRF_W as [ISR _].
        clear - ISR. destruct ISR with w; desf. }
      assert (ISW : W_s w).
      { unfold srf_s', vf in SRF_W.
        unfolder in SRF_W. destruct SRF_W as [ISW _].
        destruct ISW with w; desf. }
      red in ISR.
      destruct l_a
           as [aex amo al av | axmo amo al av | amo]
           eqn:HEQA; ins.
      unfold is_w in ISW.
      destruct (lab_s w)
           as [wex wmo wl wv | wxmo wmo wl wv | wmo]
           eqn:HEQW; ins.
      exists (Aload aex amo al wv).
      split; red.
      { red. desf. }
      arewrite (dom_rel (srf_s' ⨾ ⦗eq b_t ∩₁ ⊤₁⦘) ⊆₁ Val_s_ (val_s w)).
      { rewrite <- SRF_W. clear. basic_solver. }
      unfold val. rewrite HEQW; ins. }
    exists l_a. split; red.
    { red. desf. }
    rewrite <- SRF_W. clear. basic_solver. } *)
Admitted.

Lemma fake_srf_is_srf
    (WF : Wf G_s)
    (SB : sb_s' ≡ fake_sb)
    (VF : vf_s' ⨾ sb_s' ⨾ ⦗eq e⦘ ≡ vf_s ⨾ sb_s' ⨾ ⦗eq e⦘)
    (CO : co_s' ⨾ ⦗E_s⦘ ≡ co_s ⨾ ⦗E_s⦘) :
  fake_srf ⨾ ⦗eq e ∩₁ WCore.lab_is_r l_e⦘ ≡
    srf_s' ⨾ ⦗eq e ∩₁ WCore.lab_is_r l_e⦘.
Proof using.
  admit.
Admitted.

End FakeSrf.