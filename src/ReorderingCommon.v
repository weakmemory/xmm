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

Variable G_s G_t : execution.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable a b : actid.

Notation "'lab_t'" := (lab G_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'rpo_t'" := (rpo G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).

Notation "'lab_s'" := (lab G_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (is_w lab_s).
Notation "'R_s'" := (is_r lab_s).


Definition mapper := upd (upd id a b) b a.
Definition traces_swapped :=
    forall t' (B_LT_SZ : NOmega.lt (NOnum (index b)) (trace_length t')),
      traces' (tid a) t' <-> exists t,
      << IN : traces (tid a) t >> /\
      << SWAP : trace_swapped label t t' (index a) (index b) >>.
Definition mapped_G_t : execution := {|
  acts_set := mapper ↑₁ E_t;
  threads_set := threads_set G_t;
  lab := lab_t ∘ mapper;
  rmw := mapper ↑ rmw_t;
  data := mapper ↑ data_t;
  addr := mapper ↑ addr_t;
  ctrl := mapper ↑ ctrl_t;
  rmw_dep := mapper ↑ rmw_dep_t;
  rf := mapper ↑ rf_t;
  co := mapper ↑ co_t;
|}.

(* TODO computational swap_trace? *)
Record reord : Prop :=
{ a_not_init : ~is_init a;
  events_diff : a <> b;
  events_locs_diff : loc_s a <> loc_s b;
  events_lab : lab_s = lab_t ∘ mapper;
  events_same : E_s ≡₁ mapper ↑₁ E_t;
  events_imm : immediate sb_s a b;
  event_threadset : threads_set G_s ≡₁ threads_set G_t;

  events_no_rpo1 : ~rpo_s a b;

  map_sb : immediate sb_s ≡ mapper ↑ immediate sb_t \ singl_rel b a ∪
                                                      singl_rel a b;
  map_rf : rf_s ≡ mapper ↑ rf_t;
  map_co : co_s ≡ mapper ↑ co_t;
  map_rmw : rmw_s ≡ mapper ↑ rmw_t;
  map_rpo : rpo_s ≡ mapper ↑ rpo_t;
  map_rmw_dep : rmw_dep_s ≡ mapper ↑ rmw_dep_t;

  traces_corr : traces_swapped;

  gs_data : data G_s ≡ ∅₂;
  gs_addr : addr G_s ≡ ∅₂;
  gs_ctrl : ctrl G_s ≡ ∅₂;
  gt_data : data G_t ≡ ∅₂;
  gt_addr : addr G_t ≡ ∅₂;
  gt_ctrl : ctrl G_t ≡ ∅₂;
}.

Hypothesis REORD : reord.

Lemma mapped_exec_equiv : exec_equiv G_s mapped_G_t.
Proof using REORD.
  constructor; ins; try apply REORD.
  { now rewrite REORD.(gs_data), REORD.(gt_data), collect_rel_empty. }
  { now rewrite REORD.(gs_addr), REORD.(gt_addr), collect_rel_empty. }
  now rewrite REORD.(gs_ctrl), REORD.(gt_ctrl), collect_rel_empty.
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
    (INA : E_t b)
    (NINB : ~E_t a) :
  acts_set mapped_G_t ≡₁ E_t \₁ eq b ∪₁ eq a.
Proof using.
  unfold mapped_G_t; ins.
  unfold mapper; unfolder; split; ins; desf.
  { destruct (classic (y = a)) as [EQA|EQA],
             (classic (y = b)) as [EQB|EQB].
    all: try subst y; subst.
    all: try now (rupd; eauto). }
  { exists x; rupd; congruence. }
  exists b; split; ins; rupd; ins.
Qed.

Lemma eq_tid : tid a = tid b.
Proof using REORD.
  enough (OR : tid a = tid b \/ is_init a).
  { desf. exfalso. now apply REORD in OR. }
  eapply sb_tid_init, immediate_in, REORD.
Qed.

Lemma b_not_init : ~is_init b.
Proof using REORD.
  enough (SB : (sb_s ⨾ ⦗set_compl is_init⦘) a b).
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