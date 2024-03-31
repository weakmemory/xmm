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

Require Import AuxDef.

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

Lemma seq_set_sub n n'
    (LE : n' <= n) :
  seq_set n' ⊆₁ seq_set n.
Proof using.
  unfolder; ins; lia.
Qed.

Lemma seq_set_diff n n' :
  seq_set n' \₁ seq_set n ≡₁ fun x => n <= x < n'.
Proof using.
  unfolder; split; ins; desf; lia.
Qed.

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
    unfold thread_seq_set. rewrite seq_set_0.
    basic_solver. }
  rewrite thread_set_S.
  erewrite set_size_union_disjoint with (a:=n) (b:=1);
    auto using set_size_single.
  { f_equal. lia. }
  unfolder. ins. desf. lia.
Qed.

Lemma thread_seq_N_eq_set_size t n n'
    (EQ : set_size (thread_seq_set t n') = NOnum n) :
  thread_seq_set t n' ≡₁ thread_seq_set t n.
Proof using.
  rewrite thread_seq_set_size in EQ.
  desf.
Qed.

Lemma thread_seq_set_sub t n n'
    (LE : n' <= n) :
  thread_seq_set t n' ⊆₁ thread_seq_set t n.
Proof using.
  unfold thread_seq_set.
  now apply set_subset_collect, seq_set_sub.
Qed.

Section ThreadTrace.

Variable (G : execution) (t : thread_id) (N : nat).

Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'Et'" := (E ∩₁ (fun e => t = tid e)).

(* Hypothesis NOT_INIT : t <> tid_init. *)
Hypothesis THREAD_EVENTS : Et ≡₁ thread_seq_set t N.

Definition thread_actid_trace : trace actid :=
  trace_map (ThreadEvent t) (
    match set_size Et with
    | NOinfinity => trace_inf (fun x => x)
    | NOnum n    => trace_fin (List.seq 0 n)
    end
  ).

Lemma thread_seq_helper thr K :
  In (ThreadEvent thr K) (map (ThreadEvent thr) (List.seq 0 N)) <-> K < N.
Proof using.
  rewrite in_map_iff, <- in_seq0_iff.
  split; ins; desf; eauto.
Qed.

Lemma thread_seq_helper_inv thr K
    (LT : N <= K) :
  ~In (ThreadEvent thr K) (map (ThreadEvent thr) (List.seq 0 N)).
Proof using.
  rewrite thread_seq_helper; lia.
Qed.

Lemma thread_actid_trace_form :
  thread_actid_trace = trace_map (ThreadEvent t) (trace_fin (List.seq 0 N)).
Proof using THREAD_EVENTS.
  unfold thread_actid_trace.
  now rewrite THREAD_EVENTS, thread_seq_set_size.
Qed.

Lemma thread_actid_trace_iff K :
  trace_elems thread_actid_trace (ThreadEvent t K) <-> K < N.
Proof using THREAD_EVENTS.
  rewrite thread_actid_trace_form; ins.
  apply thread_seq_helper.
Qed.

Lemma thread_actid_trace_iff_inv K
    (LT : N <= K) :
  ~trace_elems thread_actid_trace (ThreadEvent t K).
Proof using THREAD_EVENTS.
  rewrite thread_actid_trace_iff; lia.
Qed.

Lemma thread_actid_trace_length :
  trace_length thread_actid_trace = NOnum N.
Proof using THREAD_EVENTS.
  rewrite thread_actid_trace_form. simpl.
  now rewrite map_length, seq_length.
Qed.

Lemma thread_actid_trace_nth n (d : actid) (LT : n < N) :
  trace_nth n thread_actid_trace d = ThreadEvent t n.
Proof using THREAD_EVENTS.
  rewrite trace_nth_indep with (d' := ThreadEvent t 0).
  2: { rewrite thread_actid_trace_length; ins; lia. }
  rewrite thread_actid_trace_form; ins.
  now rewrite map_nth, seq_nth.
Qed.

(* TODO: make it a lemma about (List.seq 0 N)? *)
Lemma trace_elems_eq_thread_events :
  Et ≡₁ trace_elems thread_actid_trace.
Proof using THREAD_EVENTS.
  rewrite thread_actid_trace_form, THREAD_EVENTS, trace_elems_map.
  unfold thread_seq_set. ins.
  apply set_collect_more; auto.
  unfolder; splits; intros x; by rewrite in_seq0_iff.
Qed.

Lemma thread_actid_nodup : trace_nodup thread_actid_trace.
Proof using THREAD_EVENTS.
  unfold trace_nodup.
  rewrite thread_actid_trace_length. simpl.
  intros i j LT SZ d. rewrite !thread_actid_trace_nth by lia.
  injection; lia.
Qed.

Lemma thread_actid_trace_correct :
  trace_order thread_actid_trace ≡ restr_rel Et sb.
Proof using THREAD_EVENTS.
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
  lab ↑₁ Et ≡₁ trace_elems thread_trace.
Proof using THREAD_EVENTS.
  unfold thread_trace.
  now rewrite trace_elems_map, trace_elems_eq_thread_events.
Qed.

End ThreadTrace.

Definition trace_coherent traces G : Prop :=
  forall thr (NOT_INIT : thr <> tid_init), exists tr,
    ⟪ IN_TRACES : traces thr tr ⟫ /\
    ⟪ PREFIX : trace_prefix (thread_trace G thr) tr ⟫.

Definition exec_trace_prefix G G' : Prop :=
  forall thr, trace_prefix (thread_actid_trace G' thr) (thread_actid_trace G thr).

Definition contigious_actids G : Prop := forall t (NOT_INIT : t <> tid_init),
  exists N, (acts_set G) ∩₁ (fun e => t = tid e) ≡₁ thread_seq_set t N.

Lemma thread_actid_trace_prefix t G G'
    (SUB : acts_set G' ∩₁ (fun e => t = tid e) ⊆₁
           acts_set G ∩₁ (fun e => t = tid e)) :
  trace_prefix (thread_actid_trace G' t) (thread_actid_trace G t).
Proof using.
  assert (LE : le_new (set_size (acts_set G' ∩₁ (fun e => t = tid e)))
                      (set_size (acts_set G ∩₁ (fun e => t = tid e)))).
  { now apply set_size_mori. }
  unfold thread_actid_trace; desf; ins.
  { setoid_rewrite Heq in LE. (* Interesting... *)
    setoid_rewrite Heq0 in LE.
    easy. }
  { rewrite nth_indep with (d' := ThreadEvent t 0); auto.
    rewrite map_nth, seq_nth; auto.
    now autorewrite with calc_length in LLEN. }
  setoid_rewrite Heq in LE. (* Interesting... *)
  setoid_rewrite Heq0 in LE.
  unfold le_new in LE.
  exists (map (ThreadEvent t) (List.seq n (n0 - n))).
  rewrite <- map_app, <- seq_app.
  do 2 f_equal. lia.
Qed.

Lemma contactids_eq N t G
    (NOT_INIT : t <> tid_init)
    (CONT : contigious_actids G)
    (SZ_EQ : set_size (acts_set G ∩₁ (fun e => t = tid e)) = NOnum N) :
  acts_set G ∩₁ (fun e => t = tid e) ≡₁ thread_seq_set t N.
Proof using.
  set (CONT_APP := CONT t NOT_INIT). desf.
  rewrite CONT_APP in SZ_EQ.
  rewrite CONT_APP, thread_seq_N_eq_set_size; eauto.
Qed.

Lemma add_event_to_contigious e N G G'
    (NOT_INIT : tid e <> tid_init)
    (SZ_EQ : set_size (acts_set G ∩₁ same_tid e) = NOnum N)
    (CONT : contigious_actids G)
    (CONT' : contigious_actids G')
    (NEW : ~ acts_set G e)
    (ADD : acts_set G' ≡₁ acts_set G ∪₁ eq e) :
  e = ThreadEvent (tid e) N.
Proof using.
  destruct e as [l | t idx]; ins.
  f_equal; enough (N <= idx < N + 1) by lia.
  apply seq_set_diff.
  enough (HIN : (thread_seq_set t (N + 1) \₁ thread_seq_set t N)
          (ThreadEvent t idx)).
  { unfolder in HIN; split; desf; eauto. }
  split; [| intro F; eapply NEW, in_restr_acts, contactids_eq; eauto ].
  eapply contactids_eq, in_restr_acts, ADD; eauto; try now right.
  change (fun e => t = tid e) with (same_tid (ThreadEvent t idx)).
  erewrite new_event_plus, SZ_EQ; eauto.
Qed.

Lemma add_event_to_actid_trace e N G G'
    (NOT_INIT : tid e <> tid_init)
    (SZ_EQ : set_size (acts_set G ∩₁ same_tid e) = NOnum N)
    (CONT : contigious_actids G)
    (CONT' : contigious_actids G')
    (NEW : ~ acts_set G e)
    (ADD : acts_set G' ≡₁ acts_set G ∪₁ eq e) :
  thread_actid_trace G' (tid e) =
    trace_app (thread_actid_trace G (tid e)) (trace_fin [e]).
Proof using.
  erewrite add_event_to_contigious with (G := G) (G' := G') (e := e); ins.
  all: eauto.
  rewrite thread_actid_trace_form with (G := G ) (N := N    ),
          thread_actid_trace_form with (G := G') (N := N + 1).
  { ins. now rewrite PeanoNat.Nat.add_1_r, seqS,
                     PeanoNat.Nat.add_0_l, !map_app. }
  all: apply contactids_eq; eauto.
  change (fun x => tid e = tid x) with (same_tid e).
  erewrite new_event_plus, SZ_EQ; eauto.
Qed.

Lemma event_not_in_actid_trace e N G
    (NOT_INIT : tid e <> tid_init)
    (SZ_EQ : set_size (acts_set G ∩₁ same_tid e) = NOnum N)
    (CONT : contigious_actids G)
    (NOTIN : ~ acts_set G e) :
  ~trace_elems (thread_actid_trace G (tid e)) e.
Proof using.
  intro F. eapply trace_elems_eq_thread_events in F.
  { eapply NOTIN, in_restr_acts; eauto. }
  apply contactids_eq; eauto.
Qed.

Lemma add_event_to_trace e l N G G'
    (NOT_INIT : tid e <> tid_init)
    (LABEQ : lab G' = upd (lab G) e l)
    (SZ_EQ : set_size (acts_set G ∩₁ same_tid e) = NOnum N)
    (CONT : contigious_actids G)
    (CONT' : contigious_actids G')
    (NEW : ~ acts_set G e)
    (ADD : acts_set G' ≡₁ acts_set G ∪₁ eq e) :
  thread_trace G' (tid e) =
    trace_app (thread_trace G (tid e)) (trace_fin [lab G' e]).
Proof using.
  unfold thread_trace; erewrite add_event_to_actid_trace, LABEQ; eauto.
  destruct (thread_actid_trace G (tid e)) eqn:Heq; ins.
  { rewrite map_app, map_upd_irr; ins.
    intro F; eapply event_not_in_actid_trace; eauto.
    rewrite Heq; ins. }
  exfalso.
  erewrite thread_actid_trace_form in Heq; ins.
  eapply contactids_eq; eauto.
Qed.

(* TODO: make G' prefix G *)
Lemma trace_coherent_sub traces G G' sc sc'
    (TRACE_COH : trace_coherent traces G)
    (PREFIX : exec_trace_prefix G G')
    (SUB : sub_execution G G' sc sc') :
  trace_coherent traces G'.
Proof using.
  unfold trace_coherent, exec_trace_prefix in *.
  ins. specialize (TRACE_COH thr NOT_INIT). desf.
  exists tr. splits; auto. specialize (PREFIX thr).
  assert (THREAD_PREF : trace_prefix (thread_trace G' thr) (thread_trace G thr)).
  { unfold thread_trace. destruct SUB. rewrite sub_lab. 
    unfold trace_map. desf.
    { unfold trace_prefix. ins. desf.
      exists (map (lab G) l'').
      rewrite map_app. do 2 f_equal. }
    { unfold trace_prefix. ins.
      specialize (PREFIX i). rewrite length_map in LLEN.
      specialize (PREFIX LLEN).
      rewrite nth_indep with (d' := lab G (ThreadEvent thr 0)),
      map_nth; [| now rewrite map_length].
      now f_equal. }
      unfold trace_prefix. ins. now f_equal. } 
  eapply trace_prefix_trans. { apply THREAD_PREF. }
  apply PREFIX0.
Qed.

Lemma trace_form_sub G G'
    (CONT : contigious_actids G)
    (PREFIX : exec_trace_prefix G G') :
  contigious_actids G'.
Proof using.
  admit. 
Admitted. 

  
  