Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import Core.
Require Import SubToFullExec.
Require Import ThreadTrace.

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

Set Implicit Arguments.

Lemma wf_after_steps traces X X'
    (WF_START : WCore.wf X)
    (STEP : (WCore.cfg_add_event_uninformative traces)＊ X X') :
  WCore.wf X'.
Proof using.
  induction STEP as [X X' STEP | X | X X'' X' STEP1 WF1 STEP2 WF2].
  all: eauto.
  do 2 (red in STEP; desf).
Qed.

Lemma cmt_after_steps traces X X'
    (STEP : (WCore.cfg_add_event_uninformative traces)＊ X X') :
  WCore.cmt X' ≡₁ WCore.cmt X.
Proof using.
  induction STEP as [X X' STEP | X | X X'' X' STEP1 EQ1 STEP2 EQ2].
  all: eauto.
  { do 2 (red in STEP; desf).
    apply STRUCT. }
  now rewrite EQ2, EQ1.
Qed.

Lemma gc_after_steps traces X X'
    (STEP : (WCore.cfg_add_event_uninformative traces)＊ X X') :
  WCore.GC X' = WCore.GC X.
Proof using.
  induction STEP as [X X' STEP | X | X X'' X' STEP1 EQ1 STEP2 EQ2].
  all: try congruence.
  do 2 (red in STEP; desf).
  apply STRUCT.
Qed.

Lemma init_events_after_steps traces X X'
    (STEP : (WCore.cfg_add_event_uninformative traces)＊ X X') :
  acts_set (WCore.G X') ∩₁ is_init ≡₁ acts_set (WCore.G X) ∩₁ is_init.
Proof using.
  induction STEP as [X X' STEP | X | X X'' X' STEP1 EQ1 STEP2 EQ2].
  { do 2 (red in STEP; desf).
    rewrite (WCore.caes_e_new STRUCT), set_inter_union_l.
    arewrite (eq e ∩₁ is_init ≡₁ ∅).
    { unfolder; split; ins; desf.
      now apply (WCore.caes_e_notinit STRUCT). }
    now rewrite set_union_empty_r. }
  { ins. }
  now rewrite EQ2, EQ1.
Qed.

Lemma events_after_steps traces X X'
    (STEP : (WCore.cfg_add_event_uninformative traces)＊ X X') :
  acts_set (WCore.G X) ⊆₁ acts_set (WCore.G X').
Proof using.
  induction STEP as [X X' STEP | X | X X'' X' STEP1 SUB1 STEP2 SUB2].
  { do 2 (red in STEP; desf).
    rewrite (WCore.caes_e_new STRUCT).
    basic_solver. }
  all: basic_solver.
Qed.

Lemma execution_after_steps traces X X'
    (STARTWF : WCore.wf X)
    (STEP : (WCore.cfg_add_event_uninformative traces)＊ X X') :
  sub_execution (WCore.G X') (WCore.G X) ∅₂ ∅₂.
Proof using.
  induction STEP as [X X' STEP | X | X X'' X' STEP1 SUB1 STEP2 SUB2].
  { admit. (* TODO: deltas *) }
  { constructor; ins.
    all: admit. (* TODO: spam WF *) }
  admit. (* Sub exection is trans? *)
Admitted.

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
    all: rewrite (WCore.caes_e_new STRUCT).
    { unfolder; split; intros x HSET; desf; eauto.
      split; auto. apply STRUCT. }
    { unfolder; intros x y HREL; ins; desf.
      exfalso. eapply sb_irr; eauto. }
    { unfolder; intros x y HREL; ins; desf.
      exfalso. eapply rf_irr; eauto. }
    intros x [[[INX | XEQE] NINX] IS_R]; ins.
    subst x.
    destruct (classic (cmt e)) as [CMT|NCMT].
    { apply set_subset_single_l.
      transitivity (codom_rel (
        restr_rel (WCore.cmt X') (rf (WCore.GC X')))
      ).
      all: admit. (* EASY *) }
    admit. (* True because ncmt reads must have an rf-edge *) }
  { exists []. constructor; ins.
    all: basic_solver. }
  destruct DIFF1 as [l1 DIFF1], DIFF2 as [l2 DIFF2]; ins.
  all: eauto using wf_after_steps, WCore.wf_g.
  assert (SUB1 : acts_set (WCore.G X'') ⊆₁ acts_set G').
  { eauto using events_after_steps. }
  assert (DISJ : set_disjoint (acts_set G' \₁ acts_set (WCore.G X'')) (acts_set G)).
  { apply set_disjoint_subset_r with (s' := acts_set (WCore.G X'')).
    all: eauto using events_after_steps.
    basic_solver. }
  assert (SUB : sub_execution G' (WCore.G X'') ∅₂ ∅₂).
  { eauto using execution_after_steps, wf_after_steps. }
  exists (l1 ++ l2). constructor; ins.
  { apply nodup_append.
    { apply DIFF1. }
    { apply DIFF2. }
    red. intros x IN1 IN2.
    apply DIFF1 in IN1. apply DIFF2 in IN2.
    destruct IN1, IN2; ins. }
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
  { rewrite set_union_minus with (s := acts_set G')
                                 (s' := acts_set (WCore.G X'')) at 1.
    all: ins.
    rewrite set_minus_union_l, set_minus_disjoint.
    all: ins.
    unfolder. intros x y HREL. desf.
    { apply total_order_from_list_r.
      apply (SubToFullExecInternal.diff_sb DIFF2).
      unfolder. splits; eauto. }
    { apply total_order_from_list_bridge.
      { apply DIFF1. split; ins. }
      apply DIFF2. split; ins. }
    { exfalso. apply HREL3.
      apply ext_sb_dense with (e2 := y).
      { eauto using WCore.wf_g_cont, wf_after_steps. }
      { intro F.
        assert (WF : WCore.wf X').
        { eauto using wf_after_steps. }
        assert (INIT : is_init x).
        { apply (WCore.wf_gc_acts WF). split; ins.
          apply (sub_E (WCore.wf_g_sub_gc WF)). ins. }
        apply HREL3.
        eapply init_events_after_steps with (X := X'') (X' := X').
        all: eauto.
        split; ins. }
      { ins. }
      red in HREL. unfolder in HREL. desf. }
    apply total_order_from_list_l.
    apply (SubToFullExecInternal.diff_sb DIFF1).
    unfolder. splits; eauto.
    apply (sub_sb SUB). unfolder. splits; ins. }
  { rewrite set_union_minus with (s := acts_set G')
                                 (s' := acts_set (WCore.G X'')) at 1.
    all: ins.
    rewrite set_minus_union_l, set_minus_disjoint.
    all: ins.
    unfolder. intros x y HREL. desf.
    { apply total_order_from_list_r.
      apply (SubToFullExecInternal.diff_rf DIFF2).
      unfolder. splits; eauto.
      intro F. eapply cmt_after_steps with (X := X) in F; eauto. }
    { apply total_order_from_list_bridge.
      { apply DIFF1. split; ins. }
      apply DIFF2. split; ins. }
    { exfalso. apply HREL1.
      assert (IS_R : is_r (lab (WCore.G X'')) y).
      { apply (wf_rfD WFEND) in HREL.
        unfolder in HREL. desf.
        arewrite (lab (WCore.G X'') = lab G'); ins.
        apply SUB. }
      destruct (WCore.wf_sub_rfD) with (X := X'') (x := y) as [RF | CMT].
      all: eauto using wf_after_steps; try now split.
      { exfalso. destruct RF as [x' RF]; ins.
        apply (sub_rf SUB) in RF. unfolder in RF. desf.
        apply HREL5.
        rewrite (wf_rff WFEND) with (x := y) (y := x) (z := x').
        all: ins. }
      eapply cmt_after_steps with (X := X) in CMT; eauto. }
    apply total_order_from_list_l.
    apply (SubToFullExecInternal.diff_rf DIFF1).
    unfolder. splits; eauto.
    apply (sub_rf SUB). unfolder. splits; ins. }
  admit. (* Should be easy too *)
Admitted.

End Steps.