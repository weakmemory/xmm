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

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'rpo'" := (rpo G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).


Definition mapper := upd (upd id a b) b a.

(* TODO computational swap_trace? *)
Record reord : Prop :=
{ a_not_init : ~is_init a;
  events_diff : a <> b;
  events_locs_diff : loc a <> loc b;
  events_lab : lab' = upd (upd lab a (lab b)) b (lab a);
  events_same : E' ≡₁ E;
  events_imm : immediate sb a b;

  events_no_rpo1 : ~rpo a b;
  events_no_rpo2 : ~rpo' b a;

  map_sb : immediate sb' ≡ mapper ↑ immediate sb \ singl_rel a b ∪
                                                   singl_rel b a;
  map_rf : rf' ≡ mapper ↑ rf;
  map_co : co' ≡ mapper ↑ co;
  map_rmw : rmw' ≡ mapper ↑ rmw;
  map_rpo : rpo' ≡ mapper ↑ rpo;

  traces_corr : forall t' (B_LT_SZ : NOmega.lt (NOnum (index b)) (trace_length t')),
    traces' (tid a) t' <->
    exists t, traces (tid a) t /\ trace_swapped label t t' (index a) (index b);
}.

Hypothesis REORD : reord.

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

Lemma mapper_eq_a : mapper a = b.
Proof using REORD.
  unfold mapper; rupd; eauto using events_diff.
Qed.

Lemma mapper_eq_b : mapper b = a.
Proof using.
  unfold mapper; now rewrite upds.
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

End ReorderingDefs.

Global Hint Unfold mapper : unfolderDB.

End ReordCommon.