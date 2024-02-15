Require Import Lia Setoid Program.Basics.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

Section ThreadSeqSet.

Definition seq_set (N : nat) : nat -> Prop := fun x => x < N.
Definition thread_seq_set (t : thread_id) (N : nat) : actid -> Prop :=
  (ThreadEvent t) ↑₁ seq_set N.

Lemma seq_set_step (N : nat) (t : thread_id) :
thread_seq_set t (S N) ≡₁ thread_seq_set t N ∪₁ (eq (ThreadEvent t N)).
Proof using.
  unfold thread_seq_set, seq_set.
  assert (HH : (fun x => x < S N) ≡₁ (fun x => x < N) ∪₁ eq N) by (
    unfolder; splits; ins; desf; lia
  ).
  rewrite HH, set_collect_union. basic_solver.
Qed.

Lemma thread_seq_set_size (t : thread_id) (N : nat) :
  set_size (thread_seq_set t N) = NOnum N.
Proof using.
  induction N.
  { apply set_size_empty.
    unfold thread_seq_set, seq_set.
    assert (HH : (fun x => x < 0) ≡₁ ∅) by (unfolder; splits; lia).
    rewrite HH; basic_solver. }
  rewrite seq_set_step. replace (S N) with (N + 1) by lia.
  apply set_size_union_disjoint; auto using set_size_single.
  apply set_disjoint_eq_r. unfold thread_seq_set, seq_set.
  unfolder; intro F; desf; lia.
Qed.

End ThreadSeqSet.

Section ThreadTrace.

Variable (G : execution) (t : thread_id) (N : nat).

Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).

Definition thread_events : actid -> Prop := (fun e => t = tid e) ∩₁ E.

Hypothesis NOT_INIT : t <> tid_init.
Hypothesis THREAD_EVENTS : thread_events ≡₁ thread_seq_set t N.

Definition thread_actid_trace : trace actid :=
  trace_map (ThreadEvent t) (
    match set_size (thread_events) with
    | NOinfinity => trace_inf (fun x => x)
    | NOnum n => trace_fin (List.seq 0 n)
    end
  ).

Lemma thread_actid_trace_form :
  thread_actid_trace = trace_map (ThreadEvent t) (trace_fin (List.seq 0 N)).
Proof using THREAD_EVENTS.
  unfold thread_actid_trace.
  now rewrite THREAD_EVENTS, thread_seq_set_size.
Qed.

Lemma thread_actid_trace_length :
  trace_length thread_actid_trace = NOnum N.
Proof using THREAD_EVENTS.
  rewrite thread_actid_trace_form. simpl.
  now rewrite map_length, seq_length.
Qed.

Lemma thread_actid_trace_nth n (d : actid) (LT : n < N) :
  trace_nth n thread_actid_trace d = ThreadEvent t n.
Proof using THREAD_EVENTS NOT_INIT.
  rewrite trace_nth_indep with (d' := ThreadEvent t 0) by (rewrite thread_actid_trace_length; simpl; lia).
  rewrite thread_actid_trace_form; simpl; by rewrite map_nth, seq_nth.
Qed.

Lemma trace_elems_eq_thread_events :
  thread_events ≡₁ trace_elems thread_actid_trace.
Proof using THREAD_EVENTS.
  rewrite thread_actid_trace_form, THREAD_EVENTS, trace_elems_map.
  unfold thread_seq_set, seq_set. simpl.
  enough (HH : (fun x => x < N) ≡₁ (fun a => In a (List.seq 0 N))) by now rewrite HH.
  unfolder; splits; intros x; by rewrite in_seq0_iff.
Qed.

Lemma thread_actid_nodup : trace_nodup thread_actid_trace.
Proof using THREAD_EVENTS NOT_INIT.
  unfold trace_nodup.
  rewrite thread_actid_trace_length. simpl.
  intros i j LT SZ d. rewrite !thread_actid_trace_nth by lia.
  injection; lia.
Qed.

Lemma thread_actid_trace_correct :
  trace_order thread_actid_trace ≡ restr_rel thread_events sb.
Proof using THREAD_EVENTS NOT_INIT.
  unfold trace_order, sb, ext_sb. unfolder.
  splits; intros a b.
  { intros (NODUP & i & j & LT & SZ & NA & NB). splits.
    all: try rewrite <- NA; try rewrite <- NB.
    all: try apply trace_elems_eq_thread_events, trace_nth_in; eauto with hahn.
    rewrite thread_actid_trace_length in SZ; simpl in SZ.
    rewrite !thread_actid_trace_nth by lia.
    splits; auto. }
  intros ((_ & SB & _) & IA & IB).
  split; auto using thread_actid_nodup.
  exists (index a), (index b).
  apply THREAD_EVENTS in IA, IB.
  unfold thread_seq_set, seq_set, set_collect in IA, IB.
  desf; simpl.
  rewrite thread_actid_trace_length, !thread_actid_trace_nth by lia.
  splits; basic_solver.
Qed.

Definition thread_trace : trace label := trace_map lab thread_actid_trace.

Lemma thread_trace_eq :
  lab ↑₁ thread_events ≡₁ trace_elems thread_trace.
Proof using THREAD_EVENTS.
  unfold thread_trace.
  now rewrite trace_elems_map, trace_elems_eq_thread_events by easy.
Qed.

End ThreadTrace.