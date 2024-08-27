Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import Core.
Require Import SubToFullExec.
Require Import ThreadTrace.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
From imm Require Import imm_s_ppo.
Require Import xmm_s_hb.
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
  admit.
Admitted.

End Steps.