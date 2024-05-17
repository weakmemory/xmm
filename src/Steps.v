Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import Core.
Require Import SubToFullExec.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

From RecordUpdate Require Import RecordSet.

Import ListNotations.

Lemma wf_after_steps traces X X'
    (WF_START : WCore.wf X)
    (STEP : (WCore.cfg_add_event_uninformative traces)＊ X X') :
  WCore.wf X'.
Proof using.
  induction STEP as [X X' STEP | X | X X'' X' STEP1 WF1 STEP2 WF2].
  all: eauto.
  do 2 (red in STEP; desf). apply STEP.
Qed.

(* TODO: lemma about subset of acts *)

Section Steps.

Variable X X' : WCore.t.
Variable traces : thread_id -> trace label -> Prop.

Notation "'G'" := (WCore.G X).
Notation "'G''" := (WCore.G X').
Notation "'cmt'" := (WCore.cmt X).

Lemma enumd_diff_seq
    (STARTWF : WCore.wf X)
    (STEP : (WCore.cfg_add_event_uninformative traces)＊ X X') :
  exists l, SubToFullExecInternal.enumd_diff G G' cmt l.
Proof using.
  assert (WFEND : Wf G') by eauto using WCore.wf_g, wf_after_steps.
  induction STEP as [X X' STEP | X | X X'' X' STEP1 DIFF1 STEP2 DIFF2].
  { destruct STEP as [e STEP]. exists [e].
    red in STEP. desf. constructor; ins.
    all: rewrite (WCore.e_new STEP).
    { unfolder; split; intros x HSET; desf; eauto.
      split; auto. apply STEP. }
    { unfolder; intros x y HREL; ins; desf.
      exfalso. eapply sb_irr; eauto. }
    { unfolder; intros x y HREL; ins; desf.
      exfalso. eapply rf_irr; eauto. }
    unfolder; intros x HSET; ins; desf.
    assert (HIN : acts_set G' x).
    { apply (wf_rfE WFEND) in HSET. unfolder in HSET.
      desf. }
    apply (WCore.e_new STEP) in HIN. apply HIN. }
  { exists []. constructor; ins.
    all: basic_solver. }
  destruct DIFF1 as [l1 DIFF1], DIFF2 as [l2 DIFF2]; ins.
  all: eauto using wf_after_steps, WCore.wf_g.
  assert (SUB1 : acts_set (WCore.G X'') ⊆₁ acts_set G').
  { admit. }
  assert (DISJ : set_disjoint (acts_set G' \₁ acts_set (WCore.G X'')) (acts_set G)).
  { admit. }
  assert (SUB : sub_execution G' (WCore.G X'') ∅₂ ∅₂).
  { admit. }
  exists (l1 ++ l2). constructor; ins.
  { apply nodup_append.
    { apply DIFF1. }
    { apply DIFF2. }
    admit. (* TODO: easy *) }
  { arewrite ((fun x => In x (l1 ++ l2)) ≡₁
                (fun x => In x l1) ∪₁ (fun x => In x l2)).
    { unfolder. split; ins.
      all: rewrite in_app_iff in *; desf. }
    rewrite <- (SubToFullExecInternal.diff_elems DIFF1),
            <- (SubToFullExecInternal.diff_elems DIFF2).
    rewrite set_union_minus with (s := acts_set G')
                                 (s' := acts_set (WCore.G X'')) at 1.
    all: ins.
    rewrite set_minus_union_l, set_minus_disjoint; ins.
    basic_solver. }
  { admit. }
  { rewrite set_union_minus with (s := acts_set G')
                                 (s' := acts_set (WCore.G X'')) at 1.
    all: ins.
    rewrite set_minus_union_l, set_minus_disjoint.
    all: ins.
    unfolder. intros x y HREL. desf.
    { apply total_order_from_list_r.
      apply (SubToFullExecInternal.diff_rf DIFF2).
      unfolder. splits; eauto.
      admit. }
    { apply total_order_from_list_bridge.
      { apply DIFF1. split; ins. }
      apply DIFF2. split; ins. }
    { exfalso. apply HREL1.
      assert (IS_R : is_r (lab (WCore.G X'')) y).
      { apply (wf_rfD WFEND) in HREL.
        unfolder in HREL. desf.
        arewrite (lab (WCore.G X'') = lab G'); ins.
        apply SUB. }
      destruct (WCore.sub_rfD) with (X := X'') (x := y) as [RF | CMT].
      all: eauto using wf_after_steps; try now split.
      { exfalso. destruct RF as [x' RF]; ins.
        apply (sub_rf SUB) in RF. unfolder in RF. desf.
        apply HREL5.
        rewrite (wf_rff WFEND) with (x := y) (y := x) (z := x').
        all: ins. }
      admit. }
    apply total_order_from_list_l.
    apply (SubToFullExecInternal.diff_rf DIFF1).
    unfolder. splits; eauto.
    admit. }
  admit.
Admitted.