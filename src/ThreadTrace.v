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

Section ThreadTrace.

Variable (G : execution).

Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).

Definition thread_events (t : thread_id) : actid -> Prop := (fun e => t = tid e) ∩₁ E.
Definition seq_set (t : thread_id) (n : nat) (x : actid) :=
  In x (map (ThreadEvent t) (List.seq 0 n)).

Hypothesis WF : Wf G.
Hypothesis THREAD_EVENTS : forall t, exists n, thread_events t ≡₁ seq_set t n.

Lemma seq_set_fin (t : thread_id) (n : nat) : set_finite (seq_set t n).
Proof.
  unfolder.
  exists (map (ThreadEvent t) (List.seq 0 n)).
  now unfold seq_set.
Qed.

Lemma all_finite (t : thread_id) : set_finite (thread_events t).
Proof using THREAD_EVENTS.
  destruct (THREAD_EVENTS t) as [n HEQ].
  rewrite HEQ. apply seq_set_fin.
Qed.

Lemma seq_set_step (n : nat) (t : thread_id) :
  seq_set t (S n) ≡₁ seq_set t n ∪₁ (eq (ThreadEvent t n)).
Proof using.
  unfold seq_set. rewrite seqS, map_app.
  simpl. unfolder; splits; intros x HIN.
  { apply in_app_iff in HIN.
    simpl in HIN. basic_solver. }
  apply in_app_iff.
  destruct HIN as [HIN|HIN]; simpl; auto.
Qed.

Lemma seq_set_size (t : thread_id) (n : nat):
  set_size (seq_set t n) = NOnum n.
Proof using.
  induction n.
  { apply set_size_empty.
    unfold seq_set. now rewrite seq0. }
  rewrite seq_set_step.
  replace (S n) with (n + 1) by lia.
  apply set_size_union_disjoint; auto.
  { apply set_size_single. }
  admit.
Admitted.

Lemma actid_form (t : thread_id) (n : nat)
  (LT : NOmega.lt_nat_l n (set_size (thread_events t))) :
  E (ThreadEvent t n).
Proof using THREAD_EVENTS.
  eapply set_subset_inter_l.
  { right. apply set_subset_refl2. }
  destruct (THREAD_EVENTS t) as [N HEQ].
  apply HEQ.
  unfold seq_set. apply in_map.
  apply in_seq.
  simpl. splits; try lia.
  now rewrite HEQ, seq_set_size in LT.
Qed.

Lemma actid_form_inv (t : thread_id) (x : actid)
  (IN : thread_events t x) :
  NOmega.lt_nat_l (index x) (set_size (thread_events t)).
Proof using THREAD_EVENTS.
  destruct (THREAD_EVENTS t) as [N HEQ].
  apply HEQ in IN. rewrite HEQ.
  rewrite seq_set_size. simpl.
  unfold seq_set in IN. apply in_map_iff in IN.
  destruct IN as [n [EQ IN]]. subst x. simpl.
  apply in_seq in IN. lia.
Qed.

Definition thread_actid_trace (t : thread_id) : trace actid :=
  trace_map (ThreadEvent t) (
    match set_size (thread_events t) with
    | NOinfinity => trace_inf (fun x => x)
    | NOnum n => trace_fin (List.seq 0 n)
    end
  ).

Lemma thread_actid_trace_form (t : thread_id) (n : nat)
  (LT : NOmega.lt_nat_l n (trace_length (thread_actid_trace t))):
  trace_nth n (thread_actid_trace t) (ThreadEvent t 0) = ThreadEvent t n.
Proof using.
  unfold thread_actid_trace in *.
  destruct set_size as [ | N] in *; try easy.
  simpl in *. rewrite map_length, seq_length in LT.
  now rewrite map_nth, seq_nth.
Qed.

Lemma thread_actid_trace_size (t : thread_id) :
  trace_length (thread_actid_trace t) = set_size (thread_events t).
Proof using.
  unfold thread_actid_trace.
  destruct set_size as [ | n ]; try easy.
  simpl. now rewrite length_map, seq_length.
Qed.

Lemma thread_actid_trace_correct_elemes (t : thread_id) :
  trace_elems (thread_actid_trace t) ≡₁ thread_events t.
Proof using.
  unfolder.
  splits; intros x HIN.
  { admit. }
  admit.
Admitted.

Lemma thread_actid_trace_correct (t : thread_id) (x y : nat)
  (CORR : NOmega.lt_nat_l y (trace_length (thread_actid_trace t)))
  (LT : x < y) :
  sb (trace_nth x (thread_actid_trace t) (ThreadEvent t 0))
     (trace_nth y (thread_actid_trace t) (ThreadEvent t 0)).
Proof using THREAD_EVENTS.
  assert (HLT : NOmega.lt_nat_l x
    (trace_length
     (thread_actid_trace t))) by (eapply NOmega.lt_lt_nat; eauto).
  rewrite !thread_actid_trace_form by assumption.
  unfold sb, ext_sb.
  unfolder. splits; try easy.
  all: try apply actid_form.
  all: now rewrite <- thread_actid_trace_size.
Qed.

Definition thread_trace (t : thread_id) : trace label :=
  trace_map lab (thread_actid_trace t).

End ThreadTrace.