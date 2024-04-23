Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import ThreadTrace.
Require Import Core.
Require Import TraceSwap.
Require Import SubToFullExec.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.
From imm Require Import CombRelations.

Section ExtraRel.

Variable G : execution.
Variable traces : thread_id -> trace label -> Prop.

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'is_acq'" := (is_acq lab).
Notation "'is_rel'" := (is_rel lab).
Notation "'is_rlx'" := (is_rlx lab).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'ppo'" := (ppo G).
Notation "'hb'" := (hb G).
Notation "'psc'" := (imm.psc G).
Notation "'sw'" := (sw G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'F'" := (is_f lab).

Definition rpo :=
  sb ∩ same_loc ∪
  ⦗is_acq⦘ ⨾ sb ⨾ ⦗is_rel⦘ ∪
  ⦗R ∩₁ is_rlx⦘ ⨾ sb ⨾ ⦗F ∩₁ is_acq⦘ ∪
  ⦗is_acq⦘ ⨾ sb ⨾ ⦗R ∪₁ W⦘ ∪
  ⦗R ∪₁ W⦘ ⨾ sb ⨾ ⦗is_rel⦘ ∪
  ⦗F ∩₁ is_rel⦘ ⨾ sb ⨾ ⦗W ∩₁ is_rlx⦘.
Definition rhb := (rpo ∪ sw)⁺.
Definition vf := ⦗W⦘ ⨾ rf^? ⨾ hb^? ⨾ psc^? ⨾ hb^?.
Definition srf := (vf ∩ same_loc) ⨾ ⦗R⦘ \ (co ⨾ vf).

Definition thread_terminated (t : thread_id) : Prop :=
  traces t (thread_trace G t).
Definition machine_terminated := forall t, thread_terminated t.
(* TODO: fix behavior to be a function from location to
         ordered by co (possibly infinite) set of values written to the location *)
Definition behavior := co.

Lemma wf_rpoE
    (WF : Wf G) :
  rpo ≡ ⦗E⦘ ⨾ rpo ⨾ ⦗E⦘.
Proof using.
  unfold rpo.
  rewrite !seq_union_l, !seq_union_r.
  repeat apply union_more.
  all: rewrite wf_sbE at 1; try rewrite !seq_seq_inter.
  all: basic_solver 7.
Qed.

Lemma wf_vfE
    (WF : Wf G) :
  vf ≡ ⦗E⦘ ⨾ vf ⨾ ⦗E⦘.
Proof using.
  unfold vf.
  admit.
  (* rewrite wf_hbE, wf_pscE. *)
Admitted.

Lemma wf_srfE
    (WF : Wf G) :
  srf ≡ ⦗E⦘ ⨾ srf ⨾ ⦗E⦘.
Proof using.
  unfold srf. rewrite wf_vfE, wf_coE; auto.
  admit.
Admitted.

Lemma wf_rhbE
    (WF : Wf G) :
  rhb ≡ ⦗E⦘ ⨾ rhb ⨾ ⦗E⦘.
Proof using.
  unfold rhb. rewrite wf_swE, wf_rpoE; auto.
  arewrite (⦗E⦘ ⨾ rpo ⨾ ⦗E⦘ ∪ ⦗E⦘ ⨾ sw ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ (rpo ⨾ ⦗E⦘ ∪ ⦗E⦘ ⨾ sw) ⨾ ⦗E⦘).
  { basic_solver 7. }
  rewrite <- seqA with (r2 := rpo ⨾ ⦗E⦘ ∪ ⦗E⦘ ⨾ sw) at 2.
  now rewrite <- ct_seq_eqv_r, seqA, <- ct_seq_eqv_l.
Qed.

End ExtraRel.

Module ReordCommon.

Section ReorderingDefs.

Open Scope program_scope.

Variable G G' : execution.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable a b : actid.

Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'rpo''" := (rpo G').
Notation "'rmw_dep''" := (rmw_dep G').

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'rpo'" := (rpo G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).


Definition mapper := upd (upd id a b) b a.
Definition traces_swapped :=
    forall t' (B_LT_SZ : NOmega.lt (NOnum (index b)) (trace_length t')),
      traces' (tid a) t' <-> exists t,
      << IN : traces (tid a) t >> /\
      << SWAP : trace_swapped label t t' (index a) (index b) >>.

Definition mapped_G : execution := {|
  acts_set := mapper ↑₁ E;
  threads_set := threads_set G;
  lab := lab ∘ mapper;
  rmw := mapper ↑ rmw;
  data := ∅₂;
  addr := ∅₂;
  ctrl := ∅₂;
  rmw_dep := mapper ↑ rmw_dep;
  rf := mapper ↑ rf;
  co := mapper ↑ co;
|}.

(* TODO computational swap_trace? *)
Record reord : Prop :=
{ a_not_init : ~is_init a;
  events_diff : a <> b;
  events_locs_diff : loc a <> loc b;
  events_lab : lab' = lab ∘ mapper;
  events_same : E' ≡₁ mapper ↑₁ E;
  events_imm : immediate sb a b;
  event_threadset : threads_set G' ≡₁ threads_set G;

  events_no_rpo1 : ~rpo a b;
  events_no_rpo2 : ~rpo' b a;

  map_sb : immediate sb' ≡ mapper ↑ immediate sb \ singl_rel a b ∪
                                                   singl_rel b a;
  map_rf : rf' ≡ mapper ↑ rf;
  map_co : co' ≡ mapper ↑ co;
  map_rmw : rmw' ≡ mapper ↑ rmw;
  map_rpo : rpo' ≡ mapper ↑ rpo;
  map_rmw_dep : rmw_dep' ≡ mapper ↑ rmw_dep;

  traces_corr : traces_swapped;

  g_data : data G ≡ ∅₂;
  g_addr : addr G ≡ ∅₂;
  g_ctrl : ctrl G ≡ ∅₂;
  gp_data : data G' ≡ ∅₂;
  gp_addr : addr G' ≡ ∅₂;
  gp_ctrl : ctrl G' ≡ ∅₂;
}.

Hypothesis REORD : reord.

Lemma mapped_exec_equiv : exec_equiv G' mapped_G.
Proof using REORD.
  constructor; ins; apply REORD.
Qed.

Lemma mapper_set_iff s
    (SAME : s a <-> s b) :
  mapper ↑₁ s ≡₁ s.
Proof using.
  unfold mapper; unfolder; split; ins; desf.
  { destruct (classic (y = a)) as [EQA|EQA],
             (classic (y = b)) as [EQB|EQB].
    all: try subst y; subst.
    all: try now (rupd; eauto).
    rewrite EQB; rupd; eauto. }
  destruct (classic (x = a)) as [EQA|EQA],
           (classic (x = b)) as [EQB|EQB].
  all: try subst x; subst.
  all: eexists; try now (split; ins; rupd; eauto).
  { split; [now apply SAME0 | now rupd]. }
  split; [eauto | rupd].
Qed.

Lemma mapped_exec_acts_diff
    (INA : E a)
    (NINB : ~E b) :
  acts_set mapped_G ≡₁ E \₁ eq a ∪₁ eq b.
Proof using.
  unfold mapped_G; ins.
  unfold mapper; unfolder; split; ins; desf.
  { destruct (classic (y = a)) as [EQA|EQA],
             (classic (y = b)) as [EQB|EQB].
    all: try subst y; subst.
    all: try now (rupd; eauto).
    exfalso; apply NINB; now rewrite <- EQB. }
  { exists x; rupd; [congruence |].
    intro F; apply NINB; now rewrite <- F. }
  exists a; split; ins; rupd; ins.
  intro F; apply NINB; now rewrite <- F.
Qed.

Lemma eq_tid : tid a = tid b.
Proof using REORD.
  enough (OR : tid a = tid b \/ is_init a).
  { desf. exfalso. now apply REORD in OR. }
  eapply sb_tid_init, immediate_in, REORD.
Qed.

Lemma b_not_init : ~is_init b.
Proof using REORD.
  enough (SB : (sb ⨾ ⦗set_compl is_init⦘) a b).
  { unfolder in SB; desf. }
  apply no_sb_to_init, immediate_in, REORD.
Qed.

Lemma mapper_eq_b : mapper b = a.
Proof using.
  unfold mapper; now rewrite upds.
Qed.

Lemma mapper_eq_a : mapper a = b.
Proof using.
  destruct (classic (a = b)) as [EQ|EQ].
  { unfold mapper. rewrite EQ. now rupd. }
  unfold mapper; rupd; eauto.
Qed.

Lemma mapper_neq x (NEQ_A : x <> a) (NEQ_B : x <> b) : mapper x = x.
Proof using.
  unfold mapper; rupd.
Qed.

Lemma mapper_inj (NEQ : a <> b) : inj_dom ⊤₁ mapper.
Proof using.
  unfold mapper; unfolder. intros x y _ _.
  destruct (classic (x = a)) as [HEQXA|HEQXA],
           (classic (y = b)) as [HEQYB|HEQYB],
           (classic (y = a)) as [HEQYA|HEQYA],
           (classic (x = b)) as [HEQXB|HEQXB].
  all: subst; rupd; ins.
  all: unfold id in *; congruence.
Qed.

Lemma mapper_inj_dom s (NEQ : a <> b) : inj_dom s mapper.
Proof using.
  unfold inj_dom; ins.
  apply mapper_inj; ins.
Qed.

End ReorderingDefs.

Global Hint Unfold mapper : unfolderDB.

End ReordCommon.