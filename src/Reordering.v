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

Section SubGraphLemma.

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
Notation "'W''" := (fun x => is_w lab' x).
Notation "'R''" := (fun x => is_r lab' x).

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'W'" := (fun x => is_w lab x).
Notation "'R'" := (fun x => is_r lab x).

Lemma partial_id_iff {A} (f : A -> option A) x
    (F_ID : forall x y (SOME : f x = Some y), y = x) :
  (is_some ∘ f) x <-> f x = Some x.
Proof using.
  unfold compose, is_some.
  split; ins; desf.
  f_equal. now apply F_ID.
Qed.

Lemma partial_id_rel {A} (f : A -> option A) (r : relation A)
    (F_ID : forall x y (SOME : f x = Some y), y = x) :
  Some ↓ (f ↑ r) ≡ restr_rel (is_some ∘ f) r.
Proof using.
  symmetry.
  unfolder. splits; ins; desf.
  { do 2 eexists. rewrite <- !partial_id_iff; auto. }
  rewrite (F_ID x' x), (F_ID y' y); splits; auto.
  all: unfold is_some, compose; desf.
Qed.

Lemma partial_id_set {A} (f : A -> option A) (s : A -> Prop)
    (F_ID : forall x y (SOME : f x = Some y), y = x) :
  Some ↓₁ (f ↑₁ s) ≡₁ s ∩₁ (is_some ∘ f).
Proof using.
  symmetry.
  unfolder. splits; ins; desf.
  { eexists. rewrite <- !partial_id_iff; auto. }
  rewrite (F_ID y x); auto.
  all: unfold is_some, compose; desf.
Qed.

Lemma over_exec_wf f
    (WF : Wf G')
    (CTRL : ctrl' ≡ ∅₂)
    (ADDR : addr' ≡ ∅₂)
    (DATA : data' ≡ ∅₂)
    (F_ID : forall x y (SOME : f x = Some y), y = x)
    (A_CORRECT : is_some ∘ f ⊆₁ E)
    (C_CORRECT : C ⊆₁ is_some ∘ f)
    (SUB_INIT : E' ∩₁ is_init ⊆₁ E)
    (G_RF_D : E ∩₁ R ⊆₁ codom_rel rf ∪₁ (Some ↓₁ (f ↑₁ C)))
    (G_TIDS : ~(tid ↑₁ (E' ∩₁ set_compl is_init)) tid_init)
    (G_ACTS : forall thr (NOT_INIT : thr <> tid_init),
      exists N, E ∩₁ (fun x => thr = tid x) ≡₁ thread_seq_set thr N)
    (SUB : sub_execution G' G ∅₂ ∅₂) :
  WCore.wf (WCore.Build_t G G' C f).
Proof using.
  assert (ACT_SUB : E ∩₁ set_compl is_init ⊆₁ E' ∩₁ set_compl is_init).
  { apply set_subset_inter; auto; apply SUB. }
  constructor; ins.
  { rewrite sub_ctrl, CTRL; eauto; basic_solver. }
  { rewrite sub_addr, ADDR; eauto; basic_solver. }
  { rewrite sub_data, DATA; eauto; basic_solver. }
  { eapply sub_WF; eauto. now rewrite set_interC. }
  { unfolder; intro INIT_IN; desf.
    apply G_TIDS. eexists.
    split; eauto; now apply ACT_SUB. }
  { transitivity E; auto. apply SUB. }
  { rewrite partial_id_set; eauto.
    basic_solver. }
  { unfolder; ins; desf.
    apply F_ID. rewrite <- EQ.
    now apply partial_id_iff. }
  { rewrite sub_sb with (G' := G); eauto.
    rewrite partial_id_rel, !restr_relE; auto.
    basic_solver. }
  { rewrite sub_rf with (G' := G); eauto.
    rewrite partial_id_rel, !restr_relE; auto.
    basic_solver. }
  { unfolder. intros x y (HEQ & XIN & YIN).
    apply F_ID in HEQ; now subst. }
  { unfold WCore.unwrap_g2gc, same_lab_u2v_dom,
          is_some, compose.
    unfolder. ins. desf.
    erewrite sub_lab, (F_ID e a); eauto.
    red. desf. }
  apply C_CORRECT, partial_id_iff in IN; auto.
  unfold WCore.unwrap_g2gc, val.
  erewrite sub_lab; eauto.
  ins. now rewrite IN.
Qed.

End SubGraphLemma.

Section ReorderingSubLemma.

(* G ⊂ G' *)
Definition delta_G G G' e :=
  {| acts_set := acts_set G ∪₁ eq e;
     threads_set := threads_set G;
     lab := lab G;
     rmw := rmw G ∪ (⦗acts_set G⦘ ⨾ (rmw G') ⨾ ⦗eq e⦘);
     data := ∅₂;
     addr := ∅₂;
     ctrl := ∅₂;
     rmw_dep := ⦗acts_set G ∪₁ eq e⦘ ⨾ rmw_dep G' ⨾ ⦗acts_set G ∪₁ eq e⦘;
     rf := rf G ∪ (⦗acts_set G⦘ ⨾ (rf G') ⨾ ⦗eq e⦘) ∪
                  (⦗eq e⦘ ⨾ (rf G') ⨾ ⦗acts_set G⦘);
     co := co G ∪ (⦗acts_set G⦘ ⨾ (co G') ⨾ ⦗eq e⦘) ∪
                  (⦗eq e⦘ ⨾ (co G') ⨾ ⦗acts_set G⦘);
  |}.


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
Notation "'W''" := (fun x => is_w lab' x).
Notation "'R''" := (fun x => is_r lab' x).

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'W'" := (fun x => is_w lab x).
Notation "'R'" := (fun x => is_r lab x).

(* TODO: remove *)
Notation "'U'" := (E' \₁ C).
Notation "'D'" := (E' \₁ E).

Lemma delta_G_sub e f
    (NOT_INIT : tid e <> tid_init)
    (WF : WCore.wf (WCore.Build_t G G' C f))
    (IN : E' e)
    (NEW : ~E e)
    (SUB : sub_execution G' G ∅₂ ∅₂) :
  sub_execution G' (delta_G G G' e) ∅₂ ∅₂.
Proof using.
  assert (WF' : Wf G').
  { apply WF. }
  assert (SUBE : E ⊆₁ E').
  { apply SUB. }
  constructor; ins.
  all: try apply SUB.
  { unfolder. ins. desf.
    now apply SUB. }
  { rewrite !id_union, seq_union_l,
            !seq_union_r, <- (sub_rmw SUB).
    rewrite one_dir_irrefl; eauto using rmw_one_dir.
    destruct (classic (dom_rel (rmw' ⨾ ⦗E⦘) e)) as [HIN1|HIN1].
    { rewrite one_dir_assym_1, !union_false_r;
        eauto using rmw_one_dir, one_dir_dom.
      unfolder in HIN1. desf.
      enough (EINE : E e).
      { arewrite (⦗eq e⦘ ≡ ⦗eq e⦘ ⨾ ⦗E⦘); try basic_solver. }
      apply wf_rmwi, immediate_in in HIN1; eauto.
      change E with (acts_set (WCore.G {|
        WCore.G := G;
        WCore.GC := G';
        WCore.cmt := C;
        WCore.g2gc := f
      |})).
      eapply WCore.ext_sb_dense; eauto.
      unfold sb in HIN1. unfolder in HIN1.
      desf. }
    destruct (classic (codom_rel (⦗E⦘ ⨾ rmw') e)) as [HIN2|HIN2].
    { rewrite one_dir_assym_2, !union_false_r;
      eauto using rmw_one_dir, one_dir_dom. }
    rewrite one_dir_assym_helper_1, one_dir_assym_helper_2,
            !union_false_r; eauto. }
  { rewrite (WCore.cc_data_empty WF); basic_solver. }
  { rewrite (WCore.cc_addr_empty WF); basic_solver. }
  { rewrite (WCore.cc_ctrl_empty WF); basic_solver. }
  { rewrite !id_union, seq_union_l,
            !seq_union_r, <- (sub_rf SUB).
    rewrite one_dir_irrefl; eauto using rf_one_dir.
    now rewrite union_false_r. }
  { rewrite !id_union, seq_union_l,
            !seq_union_r, <- (sub_co SUB).
    arewrite (⦗eq e⦘ ⨾ co' ⨾ ⦗eq e⦘ ≡ ∅₂).
    { set (IRR := co_irr WF').
      unfold irreflexive in IRR.
      split; [| basic_solver].
      unfolder; ins; desf; eauto. }
    now rewrite union_false_r. }
  basic_solver.
Qed.

Hypothesis THREAD_EVENTS : forall t, exists N,
  E' ∩₁ (fun e => t = tid e) ≡₁ thread_seq_set t N.

Record reord_lemma_enum (E E' C : actid -> Prop) l : Prop :=
{ relenum_nodup : NoDup l;
  relenum_no_init : (fun x => In x l) ⊆₁ set_compl (fun a => is_init a);
  relenum_d : (fun x => In x l) ≡₁ D;
  relenum_sb : restr_rel (fun x => In x l) (sb G') ⊆ total_order_from_list l;
  relenum_rf : restr_rel (fun x => In x l) rf' ⨾ ⦗E' \₁ C⦘ ⊆ total_order_from_list l;
  relenum_rf_w : dom_rel (rf' ⨾ ⦗fun x => In x l⦘) ⊆₁ E ∪₁ fun x => In x l;
}.

(* TODO move to AuxDef.v *)
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

Lemma new_event_not_in_C e f
    (WF : WCore.wf (WCore.Build_t G G' C f))
    (NEW : D e) :
  ~(Some ↓₁ (f ↑₁ C)) e.
Proof using.
  intro IN_C.
  enough (E e) by now apply NEW.
  apply (WCore.f_codom WF).
  enough (Some ↓₁ (f ↑₁ C) ⊆₁ Some ↓₁ (f ↑₁ E')) by auto.
  apply set_map_mori, set_subset_collect; eauto.
  apply (WCore.C_sub_EC WF).
Qed.

(* NOTE: do not change threads_set! It must remain constant *)
(* TODO: either rename or move into module *)
Lemma step_once_read h t f
    (F_ID : forall x y (SOME : f x = Some y), y = x)
    (WF : WCore.wf (WCore.Build_t G G' C f))
    (WF' : WCore.wf (WCore.Build_t G' G' C f))
    (PREFIX : restr_exec E G' G)
    (ENUM : reord_lemma_enum E E' C (h :: t))
    (COH : trace_coherent traces G')
    (IS_R : R' h) :
  exists f' G'',
    WCore.cfg_add_step_uninformative traces
      (WCore.Build_t G   G' C f)
      (WCore.Build_t G'' G' C f').
Proof using THREAD_EVENTS.
  assert (IN_D : D h).
  { apply ENUM; now constructor. }
  assert (NOT_W : ~ W' h).
  { generalize IS_R. unfold is_w, is_r.
    now destruct (lab' h). }
  assert (R_IN_G' : (E' ∩₁ R') h).
  { split; try apply IN_D; eauto. }
  destruct (WCore.f_rfD WF' R_IN_G') as [RF | CMT]; ins.
  all: try now (exfalso; eapply new_event_not_in_C with (f := f); eauto).
  destruct RF as [w RF]; ins.
  set (G'' := delta_G G G' h).
  assert (G_SB_SUB : sb G ⊆ sb G'').
  { unfold sb; subst G''; ins. basic_solver 2. }
  assert (IS_W : W' w).
  { eapply wf_rfD in RF; try now apply WF. unfolder in RF; desf. }
  exists (upd f h (Some h)), G'',
          h, (lab' h),
          None, (Some w), ∅, ∅, (Some h).
  constructor.
  all: try easy.
  all: ins; desf.
  { apply IN_D. }
  { apply ENUM; now constructor. }
  { admit. }
  { erewrite sub_lab with (G := G'); try apply PREFIX.
    apply functional_extensionality; ins.
    destruct (classic (x = h)) as [EQ|NEQ]; subst.
    all: now rupd. }
  { apply union_more; [apply union_more; auto |].
    { admit. }
    rewrite wf_rfD, seqA; try apply WF.
    unfold WCore.rf_delta_W.
    arewrite (⦗eq h⦘ ⨾ ⦗W'⦘ ≡ ∅₂); try basic_solver.
    rewrite seq_false_l.
    arewrite (upd f h (Some h) ↓₁ eq (Some h) ≡₁ eq h).
    { unfolder; split; intros x HEQ; subst.
      { destruct (classic (h = x)) as [EQ|NEQ]; auto.
        rewrite updo in HEQ; auto. }
      now rewrite upds. }
    arewrite (⦗eq h⦘ ⨾ rf' ≡ ∅₂).
    { rewrite wf_rfD; try apply WF'.
      basic_solver. }
    basic_solver. }
  { admit. }
  { admit. }
  apply over_exec_wf.
  all: try apply WF'.
  { intros x y.
    destruct (classic (x = h)) as [EQ|NEQ]; desf.
    { rewrite upds; congruence. }
    rewrite updo; auto. }
  { unfolder. unfold is_some, compose. ins.
    destruct (classic (x = h)) as [EQ|NEQ]; desf.
    { now right. }
    rewrite updo in Heq; auto.
    left. apply (WCore.f_codom WF). ins.
    assert (ID : f x = Some x) by now rewrite <- (F_ID x a) at 2.
    exists x. split; [apply WF, partial_id_iff |]; auto. }
  { transitivity (is_some ∘ f); try apply WF.
    unfolder. unfold is_some, compose. ins.
    destruct (classic (x = h)) as [EQ|NEQ]; desf.
    { rewrite upds in Heq. congruence. }
    rewrite updo in Heq; auto.
    congruence. }
  { subst G''. ins.
    transitivity (E ∩₁ is_init); try apply PREFIX.
    transitivity E; basic_solver. }
  { subst G''. ins.
    rewrite set_inter_union_l, codom_union.
    admit.
    (* split this into 2 refineable inclusions *) }
  { subst G''. ins.
    admit.
    (* Infer it from trace coherency. *) }
  subst G''. eapply delta_G_sub.
  { admit. }
  { apply WF. }
  { apply IN_D. }
  { apply IN_D. }
  apply PREFIX.
Admitted.

Lemma step_once h t (f : actid -> option actid)
  (WF : WCore.wf (WCore.Build_t G G' C f))
  (PREFIX : restr_exec E G' G)
  (C_SUB : C ⊆₁ E')
  (VALID_ENUM : NoDup (h :: t))
  (NOT_INIT : (fun x => In x (h :: t)) ⊆₁ set_compl is_init)
  (ENUM_D : (fun x => In x (h :: t)) ≡₁ D)
  (ORD_SB : restr_rel (fun x => In x (h :: t)) (sb G') ⊆ total_order_from_list (h :: t))
  (ORD_RF : restr_rel (fun x => In x (h :: t)) rf' ⨾ ⦗U⦘ ⊆ total_order_from_list (h :: t)) :
  exists f' G'',
  (WCore.cfg_add_step_uninformative traces)
  (WCore.Build_t G G' C f)
  (WCore.Build_t G'' G' C f').
Proof using.
  eexists (upd f h (Some h)), _, h, (lab' h).
  destruct (lab' h) eqn:HEQ_LAB.
  all: admit.
Admitted.

(* Lemma steps l
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
Admitted. *)

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