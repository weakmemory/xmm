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

Record exec_equiv G G' : Prop := {
  exeeqv_acts : acts_set G ≡₁ acts_set G';
  exeeqv_threads : threads_set G ≡₁ threads_set G';
  exeeqv_lab : lab G = lab G';
  exeeqv_rmw : rmw G ≡ rmw G';
  exeeqv_data : data G ≡ data G';
  exeeqv_addr : addr G ≡ addr G';
  exeeqv_ctrl : ctrl G ≡ ctrl G';
  exeeqv_rmw_dep : rmw_dep G ≡ rmw_dep G';
  exeeqv_rf : rf G ≡ rf G';
  exeeqv_co : co G ≡ co G';
}.

Lemma exec_equiv_eq G G'
  (EQV : exec_equiv G G') :
  G = G'.
Proof using.
  destruct EQV, G, G'; f_equal.
  all: try apply set_extensionality.
  all: try apply rel_extensionality.
  all: assumption.
Qed.

Lemma sub_sub_equiv sc sc' G G'
  (WF : Wf G')
  (SUB : sub_execution G G' sc sc')
  (SUB' : sub_execution G' G sc' sc) :
  exec_equiv G G'.
Proof using.
  assert (HEQ : acts_set G ≡₁ acts_set G').
  { split; eauto using sub_E. }
  constructor; eauto using sub_lab, sub_threads.
  all: rewrite 1?sub_rmw,
    1?sub_data,
    1?sub_addr,
    1?sub_ctrl,
    1?sub_frmw,
    1?sub_rf,
    1?sub_co at 1; eauto.
  all: try rewrite HEQ.
  all: now rewrite <- 1?wf_rmwE,
    <- 1?wf_dataE,
    <- 1?wf_addrE,
    <- 1?wf_ctrlE,
    <- 1?wf_rmw_depE,
    <- 1?wf_rfE,
    <- 1?wf_coE; auto.
Qed.

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
Variable traces : thread_id -> trace label -> Prop.

Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'rmw_dep''" := (rmw_dep G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'R''" := (E' ∩₁ (fun x => is_r lab x)).

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'W'" := (E ∩₁ (fun x => is_w lab x)).

(* TODO: remove *)
Notation "'U'" := (E' \₁ C).
Notation "'f'" := (fun (x : actid) => Some x).
Notation "'D'" := (E' \₁ E).

Hypothesis THREAD_EVENTS : forall t, exists N,
  E' ∩₁ (fun e => t = tid e) ≡₁ thread_seq_set t N.

Record reord_lemma_enum (E E' C : actid -> Prop) l : Prop :=
{ relenum_sub : C ⊆₁ E';
  relenum_nodup : NoDup l;
  relenum_no_init : (fun x => In x l) ⊆₁ set_compl (fun a => is_init a);
  relenum_d : (fun x => In x l) ≡₁ E' \₁ E;
  relenum_sb : restr_rel (fun x => In x l) (sb G') ⊆ total_order_from_list l;
  relenum_rf : restr_rel (fun x => In x l) rf' ⨾ ⦗E' \₁ C⦘ ⊆ total_order_from_list l;
}.

Lemma equiv_seq_eq {A} (s : A -> Prop)
  (r : relation A) :
  ⦗s⦘ ⨾ (⦗s⦘ ⨾ r ⨾ ⦗s⦘) ⨾ ⦗s⦘ ≡ ⦗s⦘ ⨾ r ⨾ ⦗s⦘.
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
    all: try now symmetry; apply PREFIX.
    all: try now rewrite seq_false_l, seq_false_r.
    { now rewrite E_EQ. }
    all: rewrite 1?wf_rmwE,
                 1?wf_dataE,
                 1?wf_addrE,
                 1?wf_ctrlE,
                 1?wf_rmw_depE,
                 1?wf_rfE,
                 1?wf_coE; auto.
    all: symmetry.
    all: rewrite 1?sub_rmw,
                 1?sub_data,
                 1?sub_addr,
                 1?sub_ctrl,
                 1?sub_frmw,
                 1?sub_rf,
                 1?sub_co; eauto.
    all: rewrite E_EQ.
    all: apply equiv_seq_eq.
Qed.

Lemma sub_eq
    (WF_G : Wf G')
    (PREFIX : sub_execution G' G ∅₂ ∅₂)
    (ENUM_D : D ≡₁ ∅)
     : G = G'.
Proof using.
  eapply exec_equiv_eq, sub_sub_equiv; eauto.
  now apply sub_sym.
Qed.

Lemma step_once_read h t (f : actid -> option actid)
  (WF : WCore.wf (WCore.Build_t G' G' C f))
  (PREFIX : restr_exec E G' G)
  (ENUM : reord_lemma_enum E E' C (h :: t))
  (IS_R : is_r lab' h) :
  exists f' G'',
  (WCore.silent_cfg_add_step traces)
  (WCore.Build_t G G' C f)
  (WCore.Build_t G'' G' C f').
Proof using THREAD_EVENTS.
  assert (G_WF : Wf G).
  { eapply sub_WF; try now apply PREFIX.
    { rewrite <- restr_init_sub; eauto.
      unfolder; ins; desf. }
    apply WF. }
  assert (IN_D : D h).
  { apply ENUM; now constructor. }
  assert (NOT_W : ~ is_w lab' h).
  { generalize IS_R. unfold is_w, is_r.
    now destruct (lab' h). }

  edestruct (WCore.f_rfD WF) as [RF | CMT]; eauto.
  { destruct RF as [w RF]; ins.
    set (G'' := {|
      acts_set := E ∪₁ (eq h);
      threads_set := threads_set G ∪₁ (eq (tid h));
      lab := lab;
      rmw := rmw;
      data := ∅₂;
      addr := ∅₂;
      ctrl := ∅₂;
      rmw_dep := rmw_dep;
      rf := rf ∪ (eq w × eq h);
      co := co;
    |}).
    assert (G_SB_SUB : sb G ⊆ sb G'').
    { unfold sb; subst G''; ins.
      basic_solver 2. }
    exists f, G'', h, (lab' h), None, None, (Some w), ∅, ∅, (Some h).
    constructor; try easy; ins.
    { unfolder; ins; desf; apply IN_D. }
    { unfolder; ins; desf; apply ENUM; now constructor. }
    { now rewrite eq_opt_noneE, set_union_empty_r. }
    { admit. }
    { rewrite eq_opt_someE; auto with hahn. }
    { now erewrite sub_lab, updI by apply PREFIX. }
    { unfold WCore.rf_delta_W.
      arewrite (⦗f ↓₁ eq (Some h)⦘ ⨾ rf' ≡ ∅₂).
      { rewrite wf_rfD, <- seqA; try now apply WF.
        arewrite (⦗f ↓₁ eq (Some h)⦘ ⨾ ⦗fun a : actid => is_w lab' a⦘ ≡ ∅₂).
        2: try basic_solver 1.
        unfolder; splits; ins; desf. }
      rewrite codom_empty, set_collect_empty, set_map_empty,
            cross_false_r, union_false_r.
      arewrite (eq w × eq h ∩ (fun a : actid => is_w lab a) ×
        (fun a : actid => is_r lab a) ≡ eq w × eq h); auto.
      apply wf_rfD in RF; try now apply WF. unfolder in RF.
      erewrite sub_lab by now apply PREFIX.
      basic_solver. }
    { unfold WCore.co_delta.
      arewrite (is_w lab h = false); try now rewrite union_false_r.
      erewrite sub_lab by now apply PREFIX.
      destruct (is_w lab' h); auto.
      exfalso; auto. }
    { unfold WCore.rmw_delta.
      now rewrite eq_opt_noneE, set_inter_empty_r,
                  cross_false_l, union_false_r. }
    { change (Some h) with (f h).
      now rewrite updI. }
    constructor; ins; try now apply WF.
    { constructor; subst G''; ins.
      { admit. }
      all: try now rewrite 1?seq_false_l, 1?seq_false_r.
      all: try now apply G_WF.
      { setoid_transitivity (immediate (sb G)); try now apply G_WF.
        admit. (* Need info about new sb *) }
      { admit. } (* Need that w in E *)
      { rewrite seq_union_l, seq_union_r, <- wf_rfD; auto.
        arewrite (⦗fun a => is_w lab a⦘
          ⨾ eq w × eq h ⨾ ⦗fun a => is_r lab a⦘ ≡ eq w × eq h); auto.
        apply wf_rfD in RF; try now apply WF. unfolder in RF.
        erewrite sub_lab by now apply PREFIX.
        basic_solver. }
      { apply inclusion_union_l; try now apply G_WF.
        erewrite sub_lab by now apply PREFIX.
        setoid_transitivity rf'; try now apply WF.
        basic_solver. }
      { apply funeq_union; try now apply G_WF.
        arewrite (eq w × eq h ⊆ rf') by basic_solver.
        erewrite sub_lab by now apply PREFIX.
        apply WF. }
      { apply functional_union; try now apply G_WF.
        { unfolder; ins; desf. }
        unfolder.
        intros h' [y RF'] [w' [HEQ1 HEQ2]].
        subst w' h'. apply wf_rfE in RF'; auto.
        unfolder in RF'.
        apply IN_D, RF'. }
      { rewrite wf_coE; try now apply G_WF.
        rewrite !seqA.
        arewrite (⦗E⦘ ⨾ ⦗E ∪₁ eq h⦘ ≡ ⦗E⦘) by basic_solver 4.
        rewrite <- seqA with (r1 := ⦗E ∪₁ eq h⦘).
        arewrite (⦗E ∪₁ eq h⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘) by basic_solver 4. }
      { arewrite ((E ∪₁ eq h) ∩₁ (fun a : actid => is_w lab a)
        ≡₁ E ∩₁ (fun a : actid => is_w lab a)); try apply G_WF.
        rewrite set_inter_union_l.
        arewrite (eq h ∩₁ (fun a : actid => is_w lab a) ≡₁ ∅).
        all: try now rewrite set_union_empty_r.
        erewrite sub_lab by now apply PREFIX.
        unfolder; splits; ins; desf. }
      { left. desf.
        destruct H; try now (apply G_WF; eauto); subst.
        enough (IIN : ((fun x => is_init x) ∩₁ E) (InitEvent l)).
        { apply IIN. }
        apply PREFIX. split; auto.
        apply wf_init; try now apply WF.
        erewrite <- sub_lab; try now apply PREFIX.
        exists h; subst h; split; auto.
        apply IN_D. }
      { setoid_transitivity (sb G); auto.
        now apply G_WF. }
      destruct EE; subst.
      { left; now apply G_WF. }
      now right. }
    { now erewrite sub_lab; try now apply PREFIX. }
    { admit. }
    { admit. }
    admit. }
  set (G'' := {|
    acts_set := E ∪₁ (eq h);
    threads_set := threads_set G ∪₁ (eq (tid h));
    lab := lab;
    rmw := rmw;
    data := ∅₂;
    addr := ∅₂;
    ctrl := ∅₂;
    rmw_dep := rmw_dep;
    rf := rf;
    co := co;
  |}).
  exists f, G'', h, (lab' h), None, None, None, ∅, ∅, (Some h).
  assert (G_SB_SUB : sb G ⊆ sb G'').
  { unfold sb; subst G''; ins.
    basic_solver 2. }
  constructor; try easy; ins.
  { unfolder; ins; desf; apply IN_D. }
  { unfolder; ins; desf; apply ENUM; now constructor. }
  { now rewrite eq_opt_noneE, set_union_empty_r. }
  { admit. }
  { rewrite eq_opt_someE; auto with hahn. }
  { now erewrite sub_lab, updI by apply PREFIX. }
  { unfold WCore.rf_delta_W.
    arewrite (⦗f ↓₁ eq (Some h)⦘ ⨾ rf' ≡ ∅₂).
    { rewrite wf_rfD, <- seqA; try now apply WF.
      arewrite (⦗f ↓₁ eq (Some h)⦘ ⨾ ⦗fun a : actid => is_w lab' a⦘ ≡ ∅₂).
      2: try basic_solver 1.
      unfolder; splits; ins; desf. }
    now rewrite codom_empty, set_collect_empty, set_map_empty,
          cross_false_r, !union_false_r. }
  { unfold WCore.co_delta.
    arewrite (is_w lab h = false); try now rewrite union_false_r.
    erewrite sub_lab by now apply PREFIX.
    destruct (is_w lab' h); auto.
    exfalso; auto. }
  { unfold WCore.rmw_delta.
    now rewrite eq_opt_noneE, set_inter_empty_r,
                cross_false_l, union_false_r. }
  { change (Some h) with (f h).
    now rewrite updI. }
  constructor; ins; try now apply WF.
  { constructor; subst G''; ins.
    { admit. }
    all: try now rewrite 1?seq_false_l, 1?seq_false_r.
    all: try now apply G_WF.
    { setoid_transitivity (immediate (sb G)); try now apply G_WF.
      admit. (* Need info about new sb *) }
    { admit. } (* Need that w in E *)
    { rewrite wf_coE; try now apply G_WF.
      rewrite !seqA.
      arewrite (⦗E⦘ ⨾ ⦗E ∪₁ eq h⦘ ≡ ⦗E⦘) by basic_solver 4.
      rewrite <- seqA with (r1 := ⦗E ∪₁ eq h⦘).
      arewrite (⦗E ∪₁ eq h⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘) by basic_solver 4. }
    { arewrite ((E ∪₁ eq h) ∩₁ (fun a : actid => is_w lab a)
      ≡₁ E ∩₁ (fun a : actid => is_w lab a)); try apply G_WF.
      rewrite set_inter_union_l.
      arewrite (eq h ∩₁ (fun a : actid => is_w lab a) ≡₁ ∅).
      all: try now rewrite set_union_empty_r.
      erewrite sub_lab by now apply PREFIX.
      unfolder; splits; ins; desf. }
    { left. desf.
      destruct H; try now (apply G_WF; eauto); subst.
      enough (IIN : ((fun x => is_init x) ∩₁ E) (InitEvent l)).
      { apply IIN. }
      apply PREFIX. split; auto.
      apply wf_init; try now apply WF.
      erewrite <- sub_lab; try now apply PREFIX.
      exists h; subst h; split; auto.
      apply IN_D. }
    { setoid_transitivity (sb G); auto.
      now apply G_WF. }
    destruct EE; subst.
    { left; now apply G_WF. }
    now right. }
  { now erewrite sub_lab; try now apply PREFIX. }
  { admit. }
  { admit. }
  admit.
Admitted.

Lemma step_once h t (f : actid -> option actid)
  (WF : WCore.wf (WCore.Build_t G G' C f))
  (PREFIX : restr_exec E G' G)
  (C_SUB : C ⊆₁ E')
  (VALID_ENUM : NoDup (h :: t))
  (NOT_INIT : (fun x => In x (h :: t)) ⊆₁ set_compl (fun a => is_init a))
  (ENUM_D : (fun x => In x (h :: t)) ≡₁ D)
  (ORD_SB : restr_rel (fun x => In x (h :: t)) (sb G') ⊆ total_order_from_list (h :: t))
  (ORD_RF : restr_rel (fun x => In x (h :: t)) rf' ⨾ ⦗U⦘ ⊆ total_order_from_list (h :: t)) :
  exists f' G'',
  (WCore.silent_cfg_add_step traces)
  (WCore.Build_t G G' C f)
  (WCore.Build_t G'' G' C f').
Proof using.
  eexists (upd f h (Some h)), _, h, (lab' h).
  destruct (lab' h) eqn:HEQ_LAB.
  { exists None, None.
    econstructor.
    exists ∅, ∅, (Some h).
    constructor; try easy; ins.
    { unfolder. } }
  all: admit.
Admitted.

Lemma steps
    (WF : Wf G)
    (PREFIX : restr_exec E G' G)
    (C_SUB : C ⊆₁ E')
    (VALID_ENUM : NoDup l)
    (ENUM_D : (fun x => In x l) ≡₁ D)
    (ORD_SB : sb G' ⊆ enum_ord)
    (ORD_RF : rf' ⨾ ⦗U⦘ ⊆ enum_ord) :
    exists f',
    (WCore.silent_cfg_add_step traces)＊
    (WCore.Build_t G G' C f)
    (WCore.Build_t G' G' C f').
Proof using.
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