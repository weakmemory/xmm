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
Notation "'ppo''" := (ppo G').

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'ppo'" := (ppo G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).


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

    traces_corr : forall t' (SIZE : NOmega.lt (NOnum (index b)) (trace_length t')),
        traces' (tid a) t' <->
        exists t, traces (tid a) t /\ trace_swapped (index a) (index b) t t';
}.

Lemma same_tid (REORD : reord) : tid a = tid b.
Proof using.
    destruct (sb_tid_init (immediate_in (events_imm REORD))); auto.
    exfalso; now apply REORD.
Qed.

Definition P m a' : Prop := lab a' = lab a /\ immediate sb a' (m b).

Record simrel_not_rw m : Prop :=
{   not_rw : R a -> W b -> False;
    reordered : reord;

    m_inj : forall x y, m x = m y -> x = y;
    m_comp : lab = lab' ∘ m;

    m_case1 : ~ E' b -> ~ E' a -> E ≡₁ m ↑₁ E';
    m_case2 :   E' b -> ~ E' a -> E ≡₁ m ↑₁ E' ∪₁ P m;
    m_case3 :   E' b ->   E' a -> E ≡₁ m ↑₁ E';

    m_ppo : ppo ≡ m ↑ ppo';
    m_rf : rf ≡ m ↑ rf';
    m_co : co ≡ m ↑ co;
}.

End ReorderingDefs.

Section GraphDefs.

Variable G : execution.
Variable traces : thread_id -> trace label -> Prop.

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'hb'" := (hb G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'psc'" := (imm.psc G).
Notation "'same_loc'" := (same_loc lab).

Definition trace_eq (t1 t2 : trace label) : Prop :=
    forall n d, trace_nth n t1 d = trace_nth n t2 d.
Definition thread_terminated thr : Prop :=
    exists t, traces thr t /\ trace_eq t (thread_trace G thr).
Definition machine_terminated := forall thr, thread_terminated thr.
Definition behavior := co.

Definition vf := ⦗W⦘ ⨾ rf^? ⨾ hb^? ⨾ psc^? ⨾ hb^?.
Definition srf := (vf ∩ same_loc) ⨾ ⦗R⦘ \ (co ⨾ vf).

End GraphDefs.

(* TODO: G_init = ? *)
(* TODO: simrel_not_rw -> G wcore consistent -> G' wcore consistent *)
(* TODO: simrel_not_rw -> G WRC11 consistent -> G' WRC11 consistent *)