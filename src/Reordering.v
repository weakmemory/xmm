Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import ThreadTrace.
Require Import Core.

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

Section ReorderingDefs.

Variable a b : actid.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable G G' : execution.

Notation "'T'" := (tid a).

Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).

Definition mapper (x : actid) : actid :=
    ifP x = a then b
    else ifP x = b then a
    else x.

Record trace_swapped_gen d n m (t t' : trace label) : Prop :=
{   swap_n : trace_nth n t' d = trace_nth m t d;
    swap_m : trace_nth m t' d = trace_nth n t d;
    swap_others : forall x (NEQ_N : x <> n) (NEQ_M : x <> m),
        trace_nth x t' d = trace_nth x t d;
}.

Definition trace_swapped n m t t' : Prop := forall a, trace_swapped_gen a n m t t'.

Lemma swapped_same_elems n m t t'
    (SWAP : trace_swapped n m t t') :
    trace_elems t ≡₁ trace_elems t.
Proof using.
    unfold trace_swapped in SWAP.
    split; unfolder; ins.
Qed.

Record reord : Prop :=
{   a_not_init : ~is_init a;
    b_not_init : ~is_init b;

    events_imm : immediate sb a b;
    events_diff : a <> b;
    events_locs_diff : loc a <> loc b;
    events_lab : lab' = upd (upd lab a (lab b)) b (lab a);
    events_same : E' ≡₁ E;

    map_rf : rf ≡ mapper ↓ rf';
    map_co : co ≡ mapper ↓ co';
    map_rmw : rmw ≡ mapper ↓ rmw';

    traces_corr : forall t', traces' T t'
        <-> exists t, traces T t /\ trace_swapped (index a) (index b) t t';
}.

Lemma same_tid (REORD : reord) : tid a = tid b.
Proof using.
    destruct (sb_tid_init (immediate_in (events_imm REORD))).
    all: auto || (exfalso; now apply REORD).
Qed.

End ReorderingDefs.