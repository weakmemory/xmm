Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import ThreadTrace.
Require Import Core.
Require Import TraceSwap.

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

Definition thread_terminated thr : Prop :=
    exists t, traces thr t /\ t = thread_trace G thr.
Definition machine_terminated := forall thr, thread_terminated thr.
Definition behavior := co.

Definition vf := ⦗W⦘ ⨾ rf^? ⨾ hb^? ⨾ psc^? ⨾ hb^?.
Definition srf := (vf ∩ same_loc) ⨾ ⦗R⦘ \ (co ⨾ vf).

End GraphDefs.

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
Notation "'mapper'" := (upd (upd id a b) b a).

Hypothesis EVENTS_ADJ : immediate sb a b.
Hypothesis A_NOT_INIT : ~is_init a.

Lemma same_tid : tid a = tid b.
Proof using EVENTS_ADJ A_NOT_INIT.
    apply immediate_in, sb_tid_init in EVENTS_ADJ.
    now destruct EVENTS_ADJ.
Qed.

Lemma b_not_init : ~is_init b.
Proof using EVENTS_ADJ.
    apply immediate_in, no_sb_to_init in EVENTS_ADJ.
    unfolder in EVENTS_ADJ. apply EVENTS_ADJ.
Qed.

Lemma events_neq : a <> b.
Proof using EVENTS_ADJ A_NOT_INIT.
    intros F; subst a.
    eapply sb_irr, immediate_in; eauto.
Qed.

Lemma mapper_eq_a : mapper a = b.
Proof using EVENTS_ADJ A_NOT_INIT.
    rupd; auto using events_neq.
Qed.

Lemma mapper_eq_b : mapper b = a.
Proof using.
    now rewrite upds.
Qed.

Lemma mapper_neq x (NEQ_A : x <> a) (NEQ_B : x <> b) : mapper x = x.
Proof using.
    rupd.
Qed.

Record reord : Prop :=
{   events_locs_diff : loc a <> loc b;
    events_lab : lab' = upd (upd lab a (lab b)) b (lab a);
    events_same : E' ≡₁ E;

    map_rf : rf ≡ mapper ↓ rf';
    map_co : co ≡ mapper ↓ co';
    map_rmw : rmw ≡ mapper ↓ rmw';

    traces_corr : forall t' (SIZE : NOmega.lt (NOnum (index b)) (trace_length t')),
        traces' (tid a) t' <->
        exists t, traces (tid a) t /\ trace_swapped label t t' (index a) (index b);
}.

Definition P m a' : Prop := lab a' = lab a /\ immediate sb a' (m b).

(* TODO: use `mapper` instead of m? *)
Record simrel_not_rw m : Prop :=
{   not_rw : forall (READ : R a) (WRITE : W b), False;

    m_inj : inj_dom ⊤₁ m;
    m_comp : lab = lab' ∘ m;

    m_case1 :   forall (SAME : E' a <-> E' b), E ≡₁ m ↑₁ E';
    m_case2 :   forall (INB : E' b) (NOTINA : ~ E' a), E ≡₁ m ↑₁ E' ∪₁ P m;

    m_ppo : ppo ≡ m ↑ ppo';
    m_rf : rf ≡ m ↑ rf';
    m_co : co ≡ m ↑ co';
}.

End ReorderingDefs.

Section ReorderingSubLemma.

Variable G G' : execution.
Variable C : actid -> Prop.
Variable l : list actid.
Variable traces : thread_id -> trace label -> Prop.

Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'rmw_dep''" := (rmw_dep G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'sb''" := (sb G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).

(* TODO: remove *)
Notation "'U'" := (E' \₁ C).
Notation "'f'" := (fun x => Some x).
Notation "'D'" := (E' \₁ E).

Notation "'enum_ord'" := (total_order_from_list l).

Lemma equiv_seq_eq
  A
  (S : A -> Prop)
  (r : relation A) :
  ⦗S⦘ ⨾ r ⨾ ⦗S⦘ ≡ ⦗S⦘ ⨾ (⦗S⦘ ⨾ r ⨾ ⦗S⦘) ⨾ ⦗S⦘.
Proof using.
  basic_solver.
Qed.

Lemma sub_sym
    (WF_G : Wf G')
    (PREFIX : sub_execution G' G ∅₂ ∅₂)
    (ENUM_D : D ≡₁ ∅)
    : sub_execution G G' ∅₂ ∅₂.
Proof using.
    assert (E_EQ : E = E').
    { apply set_extensionality.
      split; eauto using sub_E.
      now apply set_subsetE. }
    constructor.
    all: try solve [symmetry; apply PREFIX].
    { now rewrite <- E_EQ. }
    { rewrite wf_rmwE, (sub_rmw PREFIX), E_EQ by auto.
      apply equiv_seq_eq. }
    { rewrite wf_dataE, (sub_data PREFIX), E_EQ by auto.
      apply equiv_seq_eq. }
    { rewrite wf_addrE, (sub_addr PREFIX), E_EQ by auto.
      apply equiv_seq_eq. }
    { rewrite wf_ctrlE, (sub_ctrl PREFIX), E_EQ by auto.
      apply equiv_seq_eq. }
    { rewrite wf_rmw_depE, (sub_frmw PREFIX), E_EQ by auto.
      apply equiv_seq_eq. }
    { rewrite wf_rfE, (sub_rf PREFIX), E_EQ by auto.
      apply equiv_seq_eq. }
    { rewrite wf_coE, (sub_co PREFIX), E_EQ by auto.
      apply equiv_seq_eq. }
    basic_solver.
Qed.

Print execution.

Lemma sub_eq
    (WF_G : Wf G')
    (PREFIX : sub_execution G' G ∅₂ ∅₂)
    (ENUM_D : D ≡₁ ∅)
     : G = G'.
Proof using.
  assert (PREFIX' : sub_execution G G' ∅₂ ∅₂).
  { now apply sub_sym. }
  assert (E_EQ : E = E').
  { apply set_extensionality.
    split; eauto using sub_E. }
  destruct G eqn:HEQ, G' eqn:HEQ'. f_equal.
  all: try apply rel_extensionality.
  all: try apply PREFIX; auto.
  { apply set_extensionality; apply PREFIX. }
  { echange rmw with (rmw G).
    rewrite sub_rmw.

  }

  assert (EQ_RMW : rmw = rmw').
  { apply rel_extensionality.
    rewrite sub_rmw, E_EQ, <- wf_rmwE; eauto. }
  assert (EQ_RMW : rmw = rmw').
  { apply rel_extensionality.
    rewrite sub_rmw, E_EQ, <- wf_rmwE; eauto. }
Qed.

Lemma steps
    (WF : Wf G)
    (PREFIX : G_restr E G' G)
    (C_SUB : C ⊆₁ E')
    (VALID_ENUM : NoDup l)
    (ENUM_D : (fun x => In x l) ≡₁ D)
    (ORD_SB : sb' ⊆ enum_ord)
    (ORD_RF : rf' ⨾ ⦗U⦘ ⊆ enum_ord) :
    exists f',
    (WCore.silent_cfg_add_step traces)＊
    (WCore.Build_t G G' C f)
    (WCore.Build_t G' G' C f').
Proof using.
    generalize G G' C WF PREFIX C_SUB VALID_ENUM ENUM_D ORD_SB ORD_RF.
    clear G G' C WF PREFIX C_SUB VALID_ENUM ENUM_D ORD_SB ORD_RF.
    induction l as [ | hl tl IHl ]; ins.
    { exists f.
      enough (G' = G) by (subst; constructor).
      apply sub_eq; eauto.
      { admit. }
      admit. }
    eexists (upd ?[f] hl (Some hl)). eapply rt_trans.
    { edestruct (IHl G); admit.
    }
    admit.
Admitted.

End ReorderingSubLemma.

Section ReorderingLemmas.

Open Scope program_scope.

Lemma simrel_init G G' traces traces' a b m (REORD : reord G G' traces traces' a b)
    (NOTRW : forall (READ : is_r (lab G) a) (WRITE : is_w (lab G) b), False)
    (M_INJ : inj_dom ⊤₁ m) (M_COMP : lab G = lab G' ∘ m):
    simrel_not_rw (WCore.init_exec G) (WCore.init_exec G') a b m.
Proof using.
    admit.
Admitted.

End ReorderingLemmas.

(* TODO: G_init = ? *)
(* TODO: simrel_not_rw -> G wcore consistent -> G' wcore consistent *)
(* TODO: simrel_not_rw -> G WRC11 consistent -> G' WRC11 consistent *)