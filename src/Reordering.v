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

Lemma over_exec_wf f
    (WF : Wf G')
    (F_ID : partial_id f)
    (CTRL : ctrl' ≡ ∅₂)
    (ADDR : addr' ≡ ∅₂)
    (DATA : data' ≡ ∅₂)
    (A_CORRECT : partial_id_dom f ⊆₁ E)
    (C_CORRECT : C ⊆₁ is_some ∘ f)
    (SUB_INIT : E' ∩₁ is_init ⊆₁ E)
    (G_RF_D : E ∩₁ R ⊆₁ codom_rel rf ∪₁ (Some ↓₁ (f ↑₁ C)))
    (G_TIDS : (tid ↓₁ eq tid_init) ∩₁ E' ⊆₁ is_init)
    (G_ACTS : forall thr (NOT_INIT : thr <> tid_init),
      exists N, E ∩₁ (fun x => thr = tid x) ≡₁ thread_seq_set thr N)
    (SUB : sub_execution G' G ∅₂ ∅₂) :
  WCore.wf (WCore.Build_t G G' C f).
Proof using.
  unfold partial_id_dom in *.
  assert (ACT_SUB : E ⊆₁ E').
  { apply SUB. }
  constructor; ins.
  { rewrite sub_ctrl, CTRL; eauto; basic_solver. }
  { rewrite sub_addr, ADDR; eauto; basic_solver. }
  { rewrite sub_data, DATA; eauto; basic_solver. }
  { eapply sub_WF; eauto. now rewrite set_interC. }
  { now rewrite ACT_SUB. }
  { transitivity E; auto. }
  { rewrite partial_id_set; eauto; basic_solver. }
  { now apply partial_id_inj. }
  { rewrite sub_sb with (G' := G), partial_id_rel, !restr_relE; eauto.
    basic_solver. }
  { rewrite sub_rf with (G' := G), partial_id_rel, !restr_relE; eauto.
    basic_solver. }
  { rewrite partial_id_sub_eq; auto; basic_solver. }
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
Notation "'sb''" := (sb G').
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

Hypothesis THREAD_EVENTS : contigious_actids G'.

Record reord_lemma_enum (E E' C : actid -> Prop) l : Prop :=
{ relenum_nodup : NoDup l;
  relenum_no_init : (fun x => In x l) ⊆₁ set_compl (fun a => is_init a);
  relenum_d : (fun x => In x l) ≡₁ D;
  relenum_sb : restr_rel (fun x => In x l) sb' ⊆ total_order_from_list l;
  (* C substraction seems to be redundant *)
  relenum_rf : restr_rel (fun x => In x l) rf' ⨾ ⦗E' \₁ C⦘ ⊆ total_order_from_list l;
  relenum_rf_w : dom_rel (rf' ⨾ ⦗fun x => In x l⦘) ⊆₁ E ∪₁ fun x => In x l;
}.

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
  { unfolder. ins. desf. now apply SUB. }
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
    arewrite (⦗eq e⦘ ⨾ co' ⨾ ⦗eq e⦘ ≡ ∅₂); [| now rewrite union_false_r].
    split; [| basic_solver].
    unfolder; ins; desf.
    eapply co_irr; eauto. }
  basic_solver.
Qed.

Lemma delta_G_prefix h t
    (ENUM : reord_lemma_enum E E' C (h :: t))
    (PREFIX : exec_trace_prefix G' G)
    (SUB : sub_execution G' G ∅₂ ∅₂) :
  exec_trace_prefix G' (delta_G G G' h).
Proof using.
  unfold exec_trace_prefix. ins.
  destruct (classic (thr = (tid h))) as [HEQ|NEQ]; subst.
  { assert (ESUB : E ∪₁ eq h ⊆₁ E').
    { unfolder; ins; desf; [now apply SUB | apply ENUM; desf]. }
    apply thread_actid_trace_prefix; ins.
    now apply set_subset_inter. }
  unfold thread_actid_trace; ins.
  arewrite ((E ∪₁ eq h) ∩₁ (fun e => thr = tid e) ≡₁
            E ∩₁ (fun e => thr = tid e)).
  { unfolder; split; ins; desf; auto. }
  apply PREFIX.
Qed.

Lemma delta_G_actid_trace_h f f' h t
    (ENUM : reord_lemma_enum E E' C (h :: t))
    (PREFIX : exec_trace_prefix G' G)
    (SUB : sub_execution G' G ∅₂ ∅₂)
    (WF : WCore.wf (WCore.Build_t G G' C f))
    (WF' : WCore.wf (WCore.Build_t G' G' C f')) :
  thread_trace (delta_G G G' h) (tid h) =
  trace_app (thread_trace G (tid h)) (trace_fin [lab' h]).
Proof using.
  admit.
Admitted.

Lemma new_event_not_in_C e f
    (F_ID : partial_id f)
    (WF : WCore.wf (WCore.Build_t G G' C f))
    (NEW : D e) :
  ~C e.
Proof using.
  intro F. apply NEW.
  change E with (acts_set (WCore.G (WCore.Build_t G G' C f))).
  apply WCore.f_codom, partial_id_set; auto; ins.
  split; [apply NEW | apply WF; ins].
Qed.

Lemma reord_lemma_enum_head h t f
    (F_ID : partial_id f)
    (WF : WCore.wf (WCore.Build_t G G' C f))
    (ENUM : reord_lemma_enum E E' C (h :: t)) :
  dom_rel (rf' ⨾ ⦗eq h⦘) ⊆₁ E.
Proof using.
  intros e IN.
  assert (NINC : ~ C h).
  { eapply new_event_not_in_C; eauto.
    apply ENUM; desf. }
  edestruct (relenum_rf_w E E' C (h :: t) ENUM) as [EIN|EIN]; eauto.
  { enough (SUB : eq e ⊆₁ dom_rel (rf' ⨾ ⦗fun x => In x (h :: t)⦘)).
    { now apply SUB. }
    transitivity (dom_rel (rf' ⨾ ⦗eq h⦘)); [| basic_solver].
    red; ins; desf. }
  exfalso. enough (LT : total_order_from_list (h::t) e h).
  { eapply list_min_elt; [apply ENUM | apply LT]. }
  apply (relenum_rf E E' C (h :: t) ENUM).
  unfolder; split.
  { unfolder in IN; desf. }
  split; eauto.
  apply ENUM; desf.
Qed.

Lemma wf_partial_id_dome f
    (F_ID : partial_id f)
    (WF : WCore.wf (WCore.Build_t G G' C f)) :
  partial_id_dom f ⊆₁ E.
Proof using.
  unfold partial_id_dom.
  intros x HIN. apply WF; ins.
  unfolder. exists x; split.
  { now apply WF. }
  now apply partial_id_iff.
Qed.

(* NOTE: do not change threads_set! It must remain constant *)
(* TODO: either rename or move into module *)
Lemma step_once_read h t f f'
    (F_ID : partial_id f')
    (SUB_ID : sub_fun f f')
    (WF : WCore.wf (WCore.Build_t G G' C f))
    (WF' : WCore.wf (WCore.Build_t G' G' C f'))
    (G_PREFIX : restr_exec E G' G)
    (SUB_TRACE : exec_trace_prefix G' G)
    (ENUM : reord_lemma_enum E E' C (h :: t))
    (COH : trace_coherent traces G')
    (IS_R : R' h) :
  WCore.cfg_add_step_uninformative traces
    (WCore.Build_t G                G' C f)
    (WCore.Build_t (delta_G G G' h) G' C (upd f h (Some h))).
Proof using THREAD_EVENTS.
  (* Information about h *)
  assert (IN_D : D h).
  { apply ENUM; desf. }
  assert (NOT_INIT : ~is_init h).
  { apply ENUM; desf. }
  assert (H_TID : tid h <> tid_init).
  { eapply WCore.wf_actid_tid; eauto.
    apply IN_D. }
  assert (NOT_W : ~W' h).
  { generalize IS_R; unfold is_w, is_r.
    destruct (lab' h); auto. }
  assert (PART : partial_id f).
  { eapply partial_id_mori; eauto. }
  assert (DELTA_SUB : sub_execution G' (delta_G G G' h) ∅₂ ∅₂).
  { eapply delta_G_sub.
    { eapply WCore.wf_actid_tid; eauto.
      apply IN_D. }
    { apply WF. }
    { apply IN_D. }
    { apply IN_D. }
    apply G_PREFIX. }
  assert (DELTA_PREF : exec_trace_prefix G' (delta_G G G' h)).
  { eapply delta_G_prefix; eauto; apply G_PREFIX. }
  assert (DELTA_COH : trace_coherent traces (delta_G G G' h)).
  { eapply trace_coherent_sub; eauto. }

  edestruct WCore.f_rfD as [[w RF] | CMT]; ins.
  { apply WF'. }
  { ins. split; eauto. apply IN_D. }
  all: ins.
  (* CASE 1: h is reading *)
  { (* TODO: formula for rf *)
    assert (W_IN_E : E w).
    { eapply reord_lemma_enum_head with (f := f); eauto.
      unfolder; exists h, h; now splits. }
    assert (W_IN_W : W' w).
    { apply wf_rfD in RF; [| apply WF].
      unfolder in RF; desf. }
    assert (UPDID : partial_id (upd f h (Some h))).
    { apply upd_partial_id. eapply partial_id_mori; eauto. }
    exists h, (lab' h), None, (Some w), ∅, ∅, (Some h).
    constructor; ins.
    { apply IN_D. }
    (* TODO: prettify *)
    { set (DCOH := DELTA_COH (tid h) H_TID). ins. desf.
      unfold WCore.new_event_correct. desf.
      { exists tr.
        erewrite sub_lab; eauto.
        erewrite delta_G_actid_trace_h in PREFIX; eauto; try now apply G_PREFIX.
        split; ins. now rewrite Heq in PREFIX. }
      set (FIN := WCore.all_trace_fin WF H_TID).
      ins. rewrite Heq in FIN.
      unfold trace_finite in FIN. desf. }
    { erewrite sub_lab; [now rewrite updI | apply G_PREFIX]. }
    (* TODO: prettify? *)
    { apply union_more; [apply union_more; auto |].
      { split; [| basic_solver].
        erewrite sub_lab by apply G_PREFIX.
        intros w' h' (w'' & WINE' & h''' & RF' & WINH).
        destruct WINE', WINH; subst h''' w'' h'.
        erewrite wf_rff with (y := w') (z := w); eauto; try now apply WF.
        basic_solver. }
      unfold WCore.rf_delta_W; ins.
      rewrite partial_id_collect_eq, upds, partial_id_set; eauto.
      rewrite <- seqA with (r2 := rf') (r3 := ⦗E⦘).
      arewrite (⦗eq h⦘ ⨾ rf' ≡ ∅₂); [| basic_solver].
      rewrite wf_rfD; [| apply WF].
      basic_solver. }
    { unfold WCore.co_delta.
      erewrite sub_lab; [| apply G_PREFIX].
      arewrite (is_w lab' h = false).
      { destruct (is_w lab' h); desf. }
      rewrite wf_coD with (G := G'); [| apply WF].
      basic_solver. }
    { unfold WCore.rmw_delta, W_ex.
      rewrite wf_rmwD with (G := G'); [| apply WF].
      rewrite wf_rmwD with (G := G); [| apply WF].
      basic_solver. }
    apply over_exec_wf; ins.
    all: try now apply WF.
    { rewrite partial_id_upd_dom. apply set_subset_union; auto.
      apply wf_partial_id_dome; eauto. }
    { transitivity (is_some ∘ f); [apply WF |].
      now apply partial_id_dom_mori, partial_id_upd_sub. }
    { rewrite <- restr_init_sub; eauto.
      transitivity E; basic_solver. }
    (* TODO prettify? *)
    { arewrite (⦗eq h⦘ ⨾ rf' ⨾ ⦗E⦘ ≡ ∅₂).
      { rewrite wf_rfD; [basic_solver | apply WF]. }
      rewrite union_false_r, codom_union, set_inter_union_l.
      arewrite (codom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘) ≡₁ eq h).
      { basic_solver. }
      transitivity (codom_rel rf ∪₁
        Some ↓₁ (upd f h (Some h) ↑₁ C) ∪₁ eq h); [| basic_solver].
      apply set_subset_union; [| basic_solver].
      transitivity (codom_rel rf ∪₁
        Some ↓₁ (f ↑₁ C)); [apply WF |].
      apply set_subset_union; eauto.
      rewrite !partial_id_set, partial_id_upd_dom; eauto.
      basic_solver. }
    enough (CONT : contigious_actids (delta_G G G' h)).
    { now apply CONT. }
    eapply trace_form_sub; eauto. }
  (* CASE 2: h is commited *)
  exfalso.
  eapply new_event_not_in_C; eauto.
  apply partial_id_set in CMT; eauto.
  apply CMT.
Qed.

(* TODO: write case *)

(* TODO: fence case *)

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