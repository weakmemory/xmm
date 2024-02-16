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

Definition seq_set (n : nat) : nat -> Prop := fun x => x < n.
Definition thread_seq_set t n : actid -> Prop :=
  ThreadEvent t ↑₁ seq_set n.

#[global]
Hint Unfold seq_set thread_seq_set : unfolderDb.

Lemma seq_set_0 : seq_set 0 ≡₁ ∅.
Proof using.
  unfolder; splits; ins; desf; lia.
Qed.

Lemma seq_set_S n : seq_set (S n) ≡₁ seq_set n ∪₁ eq n.
Proof using. unfolder; splits; ins; desf; lia. Qed.

Lemma thread_set_S n t :
  thread_seq_set t (1 + n) ≡₁ thread_seq_set t n ∪₁ eq (ThreadEvent t n).
Proof using.
  unfold thread_seq_set.
  rewrite seq_set_S, set_collect_union.
  basic_solver.
Qed.

Lemma thread_seq_set_size t n :
  set_size (thread_seq_set t n) = NOnum n.
Proof using.
  induction n.
  { apply set_size_empty.
    unfold thread_seq_set.
    arewrite (seq_set 0 ≡₁ ∅).
    2: basic_solver.
    unfolder; ins; desf; splits; lia. }
  rewrite thread_set_S.
  erewrite set_size_union_disjoint with (a:=n) (b:=1);
    auto using set_size_single.
  { f_equal. lia. }
  unfolder. ins. desf. lia.
Qed.

Section ThreadTrace.

Variable (G : execution) (t : thread_id) (N : nat).

Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).

(* Notation instead of Definition? *)
Definition thread_events : actid -> Prop := E ∩₁ (fun e => t = tid e).

Hypothesis NOT_INIT : t <> tid_init.
Hypothesis THREAD_EVENTS : thread_events ≡₁ thread_seq_set t N.

Definition thread_actid_trace : trace actid :=
  trace_map (ThreadEvent t) (
    match set_size thread_events with
    | NOinfinity => trace_inf (fun x => x)
    | NOnum n    => trace_fin (List.seq 0 n)
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
  rewrite trace_nth_indep with (d' := ThreadEvent t 0).
  2: { rewrite thread_actid_trace_length; ins; lia. }
  rewrite thread_actid_trace_form; ins.
  now rewrite map_nth, seq_nth.
Qed.

(* TODO: make it a lemma about (List.seq 0 N)? *)
Lemma trace_elems_eq_thread_events :
  thread_events ≡₁ trace_elems thread_actid_trace.
Proof using THREAD_EVENTS.
  rewrite thread_actid_trace_form, THREAD_EVENTS, trace_elems_map.
  unfold thread_seq_set. ins.
  apply set_collect_more; auto.
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
  now rewrite trace_elems_map, trace_elems_eq_thread_events.
Qed.

End ThreadTrace.