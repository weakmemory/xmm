Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import ThreadTrace.
Require Import Core.
Require Import TraceSwap.
Require Import SubToFullExec.
Require Import ReorderingCommon.
Require Import AuxRel.
Require Import ExecEquiv.
Require Import ExecOps.
Require Import CfgOps.
Require Import StepOps.
Require Import Steps.

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

Section SimRel.

Variable G_s G_t : execution.
Variable a b : actid.

Notation "'lab_t'" := (lab G_t).
Notation "'val_t'" := (val lab_t).
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
Notation "'val_s'" := (val lab_s).
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
Notation "'srf_s'" := (srf G_s).

Notation "'mapper'" := (ReordCommon.mapper a b).

Record reord_simrel_rw_actids : Prop := {
  rsrw_ninit_a : ~is_init a;
  rsrw_ninit_b : ~is_init b;
  rsrw_a_is_w : is_w lab_t a;
  rsrw_b_is_r : is_r lab_t b;
  rsrw_a_b_ord : immediate ext_sb a b;
}.

Record reord_simrel_rw_core : Prop :=
{ rsrw_actids_t_ord : forall (INB : E_t b) (NOTINA : ~E_t a), False;
  rsrw_a_max : forall (INA : E_t a) (NOTINB : ~E_t b),
                  max_elt (sb G_t) a; }.

Record reord_simrel_rw_struct : Prop := {
  rsrw_lab_val_end : forall (INA : E_t a) (INB : E_t b),
                       val lab_s a = val_t b;
  rsrw_lab_u2v : same_lab_u2v (lab_s ∘ mapper) lab_t;
  rsrw_lab_val : forall e (NOTB : e <> b),
                       (val_s ∘ mapper) e = val_t e;
  rsrw_threads : threads_set G_s ≡₁ threads_set G_t;
  rsrw_rmw : rmw_s ≡ mapper ↑ rmw_t;

  (* TODO: infer *)
  (* rsrw_sb1 : forall (SAME : E_t a <-> E_t b), immediate sb_s ≡ immediate sb_t;
  rsrw_sb2 : forall (INA : E_t a) (NOTINB : ~E_t b),
                immediate sb_s ≡ immediate sb_t ∪ singl_rel a b;
   *)

  rsrw_init : E_s ∩₁ is_init ≡₁ mapper ↑₁ E_t ∩₁ is_init;
  rsrw_actids1 : forall (SAME : E_t a <-> E_t b), E_s ≡₁ mapper ↑₁ E_t;
  rsrw_actids2 : forall (INA : E_t a) (NOTINB : ~E_t b),
                 E_s ≡₁ mapper ↑₁ E_t ∪₁ eq a;
  rsrw_rf1 : forall (SAME : E_t a <-> E_t b), rf_s ≡ mapper ↑ rf_t;
  rsrw_rf2 : forall (INA : E_t a) (NOTINB : ~ E_t b),
                    rf_s ≡ mapper ↑ rf_t ∪ (srf_s ⨾ ⦗eq b⦘);
  rsrw_data : data_s ≡ mapper ↑ data_t;
  rsrw_addr : addr_s ≡ mapper ↑ addr_t;
  rsrw_ctrl : ctrl_s ≡ mapper ↑ ctrl_t;
  rsrw_rmwdep : rmw_dep_s ≡ mapper ↑ rmw_dep_t;
  rsrw_co : co_s ≡ mapper ↑ co_t;
}.

Record reord_simrel_rw : Prop :=
{ rsrw_actids : reord_simrel_rw_actids;
  rsrw_core : reord_simrel_rw_core;
  rsrw_struct : reord_simrel_rw_struct; }.

Hypothesis RSRW_ACTIDS : reord_simrel_rw_actids.

Lemma rsrw_a_neq_b : a <> b.
Proof using RSRW_ACTIDS.
  intro F. destruct RSRW_ACTIDS.
  rewrite F in rsrw_a_is_w0.
  unfold is_w, is_r in *. desf.
Qed.

Lemma rsrw_tid_a_tid_b : tid a = tid b.
Proof using RSRW_ACTIDS.
  destruct RSRW_ACTIDS. unfolder in rsrw_a_b_ord0.
  unfold ext_sb, is_init in *. desf.
  ins. desf.
Qed.

Lemma rsrw_struct_same_lab
    (STRUCT : reord_simrel_rw_struct) :
  lab_s = upd (lab_t ∘ mapper) a (lab_s a).
Proof using RSRW_ACTIDS.
  apply functional_extensionality. intro x.
  tertium_non_datur (x = a) as [HEQ|NEQ]; subst; rupd; ins.
  apply same_label_u2v_val.
  { rewrite <- Combinators.compose_id_right with (f := lab_s),
            <- ReordCommon.mapper_mapper_compose with (a := a) (b := b),
            <- Combinators.compose_assoc; auto using rsrw_a_neq_b.
    apply same_lab_u2v_compose; ins. apply STRUCT. }
  unfold val, compose.
  destruct ReordCommon.mapper_surj with (y := x) (a := a) (b := b)
          as [y HEQ].
  { apply rsrw_a_neq_b. }
  subst. rewrite ReordCommon.mapper_self_inv; [| apply rsrw_a_neq_b].
  apply STRUCT. intro F; subst.
  now rewrite ReordCommon.mapper_eq_b in NEQ.
Qed.

Lemma rsrw_struct_same_lab1
    (INA : E_t a)
    (INB : E_t b)
    (STRUCT : reord_simrel_rw_struct) :
  lab_s = (lab_t ∘ mapper).
Proof using RSRW_ACTIDS.
  rewrite rsrw_struct_same_lab; ins.
  apply functional_extensionality. intro x.
  tertium_non_datur (x = a) as [HEQ|NEQ]; subst; rupd; ins.
  apply same_label_u2v_val.
  { rewrite <- Combinators.compose_id_right with (f := lab_s),
            <- ReordCommon.mapper_mapper_compose with (a := a) (b := b),
            <- Combinators.compose_assoc; auto using rsrw_a_neq_b.
    apply same_lab_u2v_compose; ins. apply STRUCT. }
  rewrite STRUCT.(rsrw_lab_val_end); ins.
  unfold val, compose. now rewrite ReordCommon.mapper_eq_a.
Qed.

Lemma rsrw_struct_same1
    (INA : E_t a)
    (INB : E_t b)
    (SAME : E_t a <-> E_t b) :
  reord_simrel_rw_struct <->
    exec_equiv G_s (exec_mapped G_t mapper (lab_t ∘ mapper)).
Proof using RSRW_ACTIDS.
  split; [intro STRUCT | intro EQUIV].
  { constructor; ins.
    all: try now apply STRUCT.
    apply rsrw_struct_same_lab1; ins. }
  assert (EQVLAB : lab_s = lab_t ∘ mapper).
  { rewrite EQUIV.(exeeqv_lab _ _). ins. }
  constructor; ins.
  all: try now apply EQUIV.
  { rewrite EQVLAB. unfold val, compose.
    now rewrite ReordCommon.mapper_eq_a. }
  { rewrite EQVLAB.
    rewrite Combinators.compose_assoc, ReordCommon.mapper_mapper_compose,
            Combinators.compose_id_right by apply rsrw_a_neq_b.
    do 3 red. ins. desf. }
  { rewrite EQVLAB.
    change (val (lab_t ∘ mapper) ∘ mapper)
      with (val (lab_t ∘ mapper ∘ mapper)).
    now rewrite Combinators.compose_assoc, ReordCommon.mapper_mapper_compose,
            Combinators.compose_id_right by apply rsrw_a_neq_b. }
  now rewrite EQUIV.(exeeqv_acts _ _).
Qed.

Lemma rsrw_struct_same2
    (INA : ~E_t a)
    (INB : ~E_t b)
    (SAME : E_t a <-> E_t b)
    (U2V  : same_label_u2v (lab_s a) (lab_t b)) :
  reord_simrel_rw_struct <->
    exec_equiv G_s (exec_upd_lab
      (exec_mapped G_t mapper (lab_t ∘ mapper))
    a (lab_s a)).
Proof using RSRW_ACTIDS.
  split; [intro STRUCT | intro EQUIV].
  { constructor; ins.
    all: try now apply STRUCT.
    apply rsrw_struct_same_lab; ins. }
  assert (EQVLAB : lab_s = upd (lab_t ∘ mapper) a (lab_s a)).
  { rewrite EQUIV.(exeeqv_lab _ _) at 1. ins. }
  constructor; ins.
  all: try now apply EQUIV.
  { rewrite EQVLAB, upd_compose; [|apply ReordCommon.mapper_inj, rsrw_a_neq_b].
    rewrite Combinators.compose_assoc, ReordCommon.mapper_mapper_compose,
            Combinators.compose_id_right by apply rsrw_a_neq_b.
    rewrite ReordCommon.mapper_eq_a. do 2 red. intros e _.
    tertium_non_datur (e = b) as [HEQ|NEQ]; subst; rupd; ins.
    red. desf. }
  { rewrite EQVLAB, upd_compose; [|apply ReordCommon.mapper_inj, rsrw_a_neq_b].
    rewrite ReordCommon.mapper_eq_a.
    change (val (upd lab_t b (lab_s a) ∘ mapper) ∘ mapper)
    with (val (upd lab_t b (lab_s a) ∘ mapper ∘ mapper)).
    rewrite Combinators.compose_assoc, ReordCommon.mapper_mapper_compose,
            Combinators.compose_id_right by apply rsrw_a_neq_b.
    unfold val. rewrite updo; ins. }
  rewrite EQUIV.(exeeqv_acts _ _); ins.
Qed.

Lemma rsrw_struct_niff
    (INA : E_t a)
    (NOTINB : ~E_t b)
    (U2V  : same_label_u2v (lab_s a) (lab_t b))
    (EQVLAB : lab_s = upd (lab_t ∘ mapper) a (lab_s a)) :
  reord_simrel_rw_struct <->
    exec_equiv G_s (exec_add_rf
      (exec_add_read_event_nctrl
        (exec_upd_lab
          (exec_mapped G_t mapper (lab_t ∘ mapper))
          a (lab_s a)) a)
      (srf_s ⨾ ⦗eq b⦘)).
Proof using RSRW_ACTIDS.
  split; [intro STRUCT | intro EQUIV].
  { constructor; ins.
    all: try now apply STRUCT. }
  constructor; ins.
  all: try now apply EQUIV.
  all: try now (exfalso; apply NOTINB, SAME, INA).
  { rewrite EQVLAB, upd_compose; [| apply ReordCommon.mapper_inj, rsrw_a_neq_b].
    rewrite Combinators.compose_assoc, ReordCommon.mapper_mapper_compose,
            Combinators.compose_id_right by apply rsrw_a_neq_b.
    rewrite ReordCommon.mapper_eq_a. do 2 red. intros e _.
    tertium_non_datur (e = b) as [HEQ|NEQ]; subst; rupd; ins.
    red. desf. }
  { rewrite EQVLAB, upd_compose; [| apply ReordCommon.mapper_inj, rsrw_a_neq_b].
    rewrite ReordCommon.mapper_eq_a.
    change (val (upd lab_t b (lab_s a) ∘ mapper) ∘ mapper)
      with (val (upd lab_t b (lab_s a)) ∘ mapper ∘ mapper).
    rewrite Combinators.compose_assoc, ReordCommon.mapper_mapper_compose,
            Combinators.compose_id_right by apply rsrw_a_neq_b.
    unfold val. rupd. }
  rewrite EQUIV.(exeeqv_acts _ _); ins.
  rewrite set_inter_union_l.
  arewrite (eq a ∩₁ is_init ≡₁ ∅); [| now rewrite set_union_empty_r].
  split; [| basic_solver]. intros x (EQ & INIT). subst.
  red. now apply RSRW_ACTIDS.(rsrw_ninit_a).
Qed.

End SimRel.

Module ReordRwSimRelProps.

Section Basic.

Variable G_s G_t : execution.
Variable a b : actid.

Notation "'lab_t'" := (lab G_t).
Notation "'val_t'" := (val lab_t).
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
Notation "'srf_t'" := (srf G_t).

Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
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

Notation "'mapper'" := (ReordCommon.mapper a b).

Lemma sim_rel_init
    (ACTIDS : reord_simrel_rw_actids G_t a b)
    (STRUCT : reord_simrel_rw_struct G_s G_t a b) :
  reord_simrel_rw (WCore.init_exec G_s) (WCore.init_exec G_t) a b.
Proof using.
  constructor; constructor; ins.
  all: try now (rewrite collect_rel_empty; ins).
  all: try now (exfalso; apply ACTIDS.(rsrw_ninit_a G_t a b), INA).
  all: try now apply ACTIDS.
  all: try now apply STRUCT.
  { apply ACTIDS.(rsrw_ninit_b G_t a b), INB. }
  all: rewrite STRUCT.(rsrw_init _ _ _ _).
  all: rewrite set_collect_interE, ReordCommon.mapper_is_init; ins.
  all: try now apply ACTIDS.
  all: eapply ReordCommon.mapper_inj, rsrw_a_neq_b; eauto.
Qed.

End Basic.

Section SimrelExec.

Variable G_t G_t' G_s : execution.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable a b : actid.

Notation "'lab_t'" := (lab G_t).
Notation "'val_t'" := (val lab_t).
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
Notation "'W_t'" := (is_w lab_t).
Notation "'R_t'" := (is_r lab_t).

Notation "'lab_t''" := (lab G_t').
Notation "'val_t''" := (val lab_t').
Notation "'E_t''" := (acts_set G_t').
Notation "'sb_t''" := (sb G_t').
Notation "'rf_t''" := (rf G_t').
Notation "'co_t''" := (co G_t').
Notation "'rmw_t''" := (rmw G_t').
Notation "'rpo_t''" := (rpo G_t').
Notation "'rmw_dep_t''" := (rmw_dep G_t').
Notation "'data_t''" := (data G_t').
Notation "'ctrl_t''" := (ctrl G_t').
Notation "'addr_t''" := (addr G_t').
Notation "'W_t''" := (is_w lab_t').
Notation "'R_t''" := (is_r lab_t').

Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
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
Notation "'srf_s'" := (srf G_s).

Notation "'mapper'" := (ReordCommon.mapper a b).

Hypothesis SWAPPED_TRACES : ReordCommon.traces_swapped traces traces' a b.

(*
  Big case 1: both events are in the target execution.

  At this point out labeling function must match up with
  the target execution.
*)
Lemma simrel_exec_iff_helper_1 sc e
    (SAME : E_t a <-> E_t b)
    (INA : E_t a)
    (INB : E_t b)
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons G_t sc)
    (STEP : WCore.exec_inst G_t G_t' sc traces e)
    (SIM_ACTS : reord_simrel_rw_actids G_t a b)
    (NRMWDEP : ~rmw_dep_t' a b)
    (NRMW : ~rmw_t' a b)
    (NRMWCODOM : ~codom_rel rmw_t' a)
    (NRMWDOM : ~dom_rel rmw_t' b) :
  WCore.exec_inst
    (exec_mapped G_t  mapper (lab_t'  ∘ mapper))
    (exec_mapped G_t' mapper (lab_t'  ∘ mapper))
    (mapper ↑ sc)
    traces'
    e.
Proof using.
  (* Useful props *)
  assert (NEQ : a <> b).
  { intro F; eapply ext_sb_irr with (x := a).
    rewrite F at 2. apply SIM_ACTS. }
  assert (FIN_LAB : lab G_t' = lab_t).
  { symmetry. eapply sub_lab.
    eapply WCore.wf_g_sub_gc
    with (X := {|
      WCore.G := G_t;
      WCore.GC := G_t';
      WCore.sc := sc;
      WCore.cmt := ∅;
    |}).
    apply STEP. }
  assert (LABEQ : lab_t = lab_t ∘ mapper ∘ mapper).
  { now rewrite Combinators.compose_assoc,
                ReordCommon.mapper_mapper_compose,
                Combinators.compose_id_right. }
  assert (SAME' : E_t' a <-> E_t' b).
  { destruct STEP. split; intro HSET.
    all: apply (WCore.cae_e_new add_event).
    all: apply (WCore.cae_e_new add_event) in HSET.
    all: ins; unfolder; unfolder in HSET; desf.
    all: now left. }

  (* actual proof *)
  constructor; ins.
  { replace ∅ with (mapper ↑₁ ∅) by now rewrite set_collect_empty.
    apply ReordCommon.mapped_G_t_cfg with (X := {|
        WCore.sc := sc;
        WCore.G := G_t;
        WCore.GC := G_t';
        WCore.cmt := ∅;
    |}); ins.
    all: try now apply SIM_ACTS.
    all: try now apply STEP.
    eapply rsrw_tid_a_tid_b; eauto. }
  { destruct STEP. red in add_event. desf.
    exists (option_map mapper r), (option_map mapper w),
           (mapper ↑₁ W1), (mapper ↑₁ W2).
    splits; ins.
    { admit. }
    { replace ∅ with (mapper ↑₁ ∅) by now rewrite set_collect_empty.
      replace e with (mapper e) by now rewrite ReordCommon.mapper_neq.
      apply cfg_mapped_add_step_props with
        (X := {|
            WCore.sc := sc;
            WCore.G := G_t;
            WCore.GC := G_t';
            WCore.cmt := ∅;
        |})
        (X' := {|
            WCore.sc := sc;
            WCore.G := G_t';
            WCore.GC := G_t';
            WCore.cmt := ∅;
        |}).
      { now apply ReordCommon.mapper_inj. }
      { now apply ReordCommon.mapper_surj. }
      { ins. now rewrite FIN_LAB. }
      apply PROPS. }
    { admit. (* TODO: traces *) }
    replace ∅ with (mapper ↑₁ ∅) by now rewrite set_collect_empty.
    apply ReordCommon.mapped_G_t_cfg with (X := {|
      WCore.sc := sc;
      WCore.G := G_t';
      WCore.GC := G_t';
      WCore.cmt := ∅;
    |}); ins.
    all: try now apply SIM_ACTS.
    all: try now apply add_event.
    eapply rsrw_tid_a_tid_b; eauto. }
  admit. (* TODO: research *)
Admitted.

(*
  Big case 2: neither events are in the target graph.

  This means our labeling function must match target' almost
  1-to-1, allowing some liberties with b's label. This condition
  must be satisfied even right now, because we do not update our
  labeling function during simple instruction steps.
*)
Lemma simrel_exec_iff_helper_2 sc e l
    (U2V : same_label_u2v (lab_t' b) l)
    (SAME : E_t a <-> E_t b)
    (NINA : ~E_t a)
    (NINB : ~E_t b)
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons G_t sc)
    (STEP : WCore.exec_inst G_t G_t' sc traces e)
    (SIM_ACTS : reord_simrel_rw_actids G_t a b)
    (NRMWDEP : ~rmw_dep_t' a b)
    (NRMW : ~rmw_t' a b)
    (NRMWCODOM : ~codom_rel rmw_t' a)
    (NRMWDOM : ~dom_rel rmw_t' b) :
  WCore.exec_inst
    (exec_upd_lab
      (exec_mapped G_t  mapper (lab_t'  ∘ mapper))
      a l)
    (exec_upd_lab
      (exec_mapped G_t' mapper (lab_t' ∘ mapper))
      a l)
    (mapper ↑ sc)
    traces'
    e.
Proof using.
  (* Helper asserts *)
  assert (NEQ : a <> b).
  { intro F; eapply ext_sb_irr with (x := a).
    rewrite F at 2. apply SIM_ACTS. }
  assert (FIN_LAB : lab G_t' = lab_t).
  { symmetry. eapply sub_lab.
    eapply WCore.wf_g_sub_gc
    with (X := {|
      WCore.G := G_t;
      WCore.GC := G_t';
      WCore.sc := sc;
      WCore.cmt := ∅;
    |}).
    apply STEP. }
  assert (LABEQ : lab_t = lab_t ∘ mapper ∘ mapper).
  { now rewrite Combinators.compose_assoc,
                ReordCommon.mapper_mapper_compose,
                Combinators.compose_id_right. }
  assert (LABEQ' : upd lab_t b l = upd (lab_t ∘ mapper) a l ∘ mapper).
  { ins; unfold compose.
    apply functional_extensionality; intro x.
    tertium_non_datur (x = b) as [HEQ|HEQ]; subst.
    { now rewrite ReordCommon.mapper_eq_b, !upds. }
    rewrite !updo, ReordCommon.mapper_self_inv; ins.
    intro F; rewrite <- ReordCommon.mapper_eq_b with (b := b) in F.
    apply ReordCommon.mapper_inj in F; ins. }
  assert (NINA' : ~E_t' a).
  { intro F'. destruct STEP; ins.
    apply (WCore.cae_e_new add_event) in F'.
    ins. destruct F' as [HIN|HEQ]; desf. }
  assert (NINB' : ~E_t' b).
  { intro F'. destruct STEP; ins.
    apply (WCore.cae_e_new add_event) in F'.
    ins. destruct F' as [HIN|HEQ]; desf. }
  assert (ANREAD : ~ codom_rel (mapper ↑ rf_t') a).
  { unfolder. intro F. desf.
    rewrite ReordCommon.mapper_inj with (a := a) (b := b)
                                        (x := y') (y := b) in F.
    all: ins; try now rewrite ReordCommon.mapper_eq_b.
    apply NINB'.
    apply (wf_rfE (WCore.wf_gc (WCore.start_wf STEP))) in F.
    ins. unfolder in F. desf. }
  assert (BNREAD : ~ dom_rel (mapper ↑ rf_t') a).
  { unfolder. intro F. desf.
    rewrite ReordCommon.mapper_inj with (a := a) (b := b)
                                        (x := x') (y := b) in F.
    all: ins; try now rewrite ReordCommon.mapper_eq_b.
    apply NINB'.
    apply (wf_rfE (WCore.wf_gc (WCore.start_wf STEP))) in F.
    ins. unfolder in F. desf. }
  assert (ACTEQ : E_t' ≡₁ E_t ∪₁ eq e).
  { destruct STEP.
    rewrite (WCore.cae_e_new add_event). ins. }
  (* Actual proof *)
  destruct STEP; ins. red in add_event. desf.
  constructor; ins.
  { replace ∅ with (mapper ↑₁ ∅); [| now rewrite set_collect_empty].
    apply cfg_upd_lab_wf with (X := {|
      WCore.sc := mapper ↑ sc;
      WCore.G := exec_mapped G_t mapper (lab_t' ∘ mapper);
      WCore.GC := exec_mapped G_t' mapper (lab_t' ∘ mapper);
      WCore.cmt := mapper ↑₁ ∅
    |}); ins.
    { apply SIM_ACTS. }
    { unfold compose. now rewrite ReordCommon.mapper_eq_a. }
    apply ReordCommon.mapped_G_t_cfg with (X := {|
        WCore.sc := sc;
        WCore.G := G_t;
        WCore.GC := G_t';
        WCore.cmt := ∅;
    |}); ins.
    all: try now apply SIM_ACTS.
    eapply rsrw_tid_a_tid_b; eauto. }
  { exists (option_map mapper r), (option_map mapper w),
           (mapper ↑₁ W1), (mapper ↑₁ W2).
    splits.
    { constructor; ins.
      { rewrite ACTEQ, set_collect_union, set_collect_eq,
                ReordCommon.mapper_neq; ins. }
      { unfolder. intro F. desf.
        apply STRUCT. ins.
        rewrite ReordCommon.mapper_neq; ins.
        { intro EQ; subst. apply E_NOT_B.
          now rewrite ReordCommon.mapper_eq_a. }
        intro EQ; subst. apply E_NOT_A.
        now rewrite ReordCommon.mapper_eq_b. }
      apply STRUCT. }
    { replace ∅ with (mapper ↑₁ ∅) by now rewrite set_collect_empty.
      replace e with (mapper e) by now rewrite ReordCommon.mapper_neq.
      apply cfg_upd_lab_add_step_props with
        (X := {|
          WCore.sc := mapper ↑ sc;
          WCore.G := exec_mapped G_t  _ _;
          WCore.GC := exec_mapped G_t' _ _;
          WCore.cmt := mapper ↑₁ ∅
        |})
        (X' := {|
          WCore.sc := mapper ↑ sc;
          WCore.G := exec_mapped G_t'  _ _;
          WCore.GC := exec_mapped G_t' _ _;
          WCore.cmt := mapper ↑₁ ∅
        |}).
      { ins. unfold compose. now rewrite ReordCommon.mapper_eq_a. }
      apply cfg_mapped_add_step_props with
        (X := {|
            WCore.sc := sc;
            WCore.G := G_t;
            WCore.GC := G_t';
            WCore.cmt := ∅;
        |})
        (X' := {|
            WCore.sc := sc;
            WCore.G := G_t';
            WCore.GC := G_t';
            WCore.cmt := ∅;
        |}).
      { now apply ReordCommon.mapper_inj. }
      { now apply ReordCommon.mapper_surj. }
      { ins. now rewrite FIN_LAB. }
      apply PROPS. }
    { admit. (* traces *) }
    replace ∅ with (mapper ↑₁ ∅); [| now rewrite set_collect_empty].
    apply cfg_upd_lab_wf with (X := {|
      WCore.sc := mapper ↑ sc;
      WCore.G := exec_mapped G_t' mapper (lab_t' ∘ mapper);
      WCore.GC := exec_mapped G_t' mapper (lab_t' ∘ mapper);
      WCore.cmt := mapper ↑₁ ∅;
    |}); ins.
    { apply SIM_ACTS. }
    { unfold compose. now rewrite ReordCommon.mapper_eq_a. }
    apply ReordCommon.mapped_G_t_cfg with (X := {|
        WCore.sc := sc;
        WCore.G := G_t';
        WCore.GC := G_t';
        WCore.cmt := ∅;
    |}); ins.
    all: try now apply SIM_ACTS.
    all: try now apply add_event.
    eapply rsrw_tid_a_tid_b; eauto. }
  admit. (* TODO: Is_cons *)
Admitted.

Lemma simrel_exec_niff_helper sc e l sw
    (U2V : same_label_u2v (lab_t' b) l)
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (W_NOT_A : sw <> a)
    (W_NOT_B : sw <> b)
    (B_TID : tid a <> tid_init)
    (CONS : WCore.is_cons G_t sc)
    (STEP : WCore.exec_inst G_t G_t' sc traces e)
    (SIM_ACTS : reord_simrel_rw_actids G_t a b)
    (WB_LOC : same_loc (upd (lab_t' ∘ mapper) a l) a sw)
    (WB_VAL : val (upd (lab_t' ∘ mapper) a l) sw =
              val (upd (lab_t' ∘ mapper) a l) a)
    (HWIN : E_t sw)
    (W_IS : W_t sw)
    (INA :   E_t a)
    (NINB : ~E_t b)
    (BINIT : forall l0 (LOC : loc lab_t' b = Some l0), E_t' (InitEvent l0))
    (NRMWDEP : ~rmw_dep_t' a b)
    (NRMW : ~rmw_t' a b)
    (NRMWCODOM : ~codom_rel rmw_t' a)
    (NRMWDOM : ~dom_rel rmw_t' b) :
  WCore.exec_inst
    (exec_add_rf
      (exec_add_read_event_nctrl
        (exec_upd_lab
          (exec_mapped G_t mapper (lab_t' ∘ mapper))
          a l) a)
      (singl_rel sw a))
    (exec_add_rf
      (exec_add_read_event_nctrl
        (exec_upd_lab
          (exec_mapped G_t' mapper (lab_t' ∘ mapper))
          a l) a)
      (singl_rel sw a))
    (mapper ↑ sc)
    traces'
    e.
Proof using.
  assert (ANEQB : a <> b).
  { eapply rsrw_a_neq_b; eauto. }
  assert (INA' : E_t' a).
  { destruct STEP; ins.
    apply (WCore.cae_e_new add_event).
    ins. now left. }
  assert (NINB' : ~E_t' b).
  { intro F'. destruct STEP; ins.
    apply (WCore.cae_e_new add_event) in F'.
    ins. destruct F' as [HIN|HEQ]; desf. }
  assert (FIN_LAB : lab G_t' = lab_t).
  { symmetry. destruct STEP; ins.
    now apply WCore.wf_g_sub_gc
    with (X := {|
      WCore.G := G_t;
      WCore.GC := G_t';
      WCore.sc := sc;
      WCore.cmt := ∅;
    |}). }
  assert (LABEQ : lab_t' = lab_t' ∘ mapper ∘ mapper).
  { rewrite Combinators.compose_assoc.
    rewrite ReordCommon.mapper_mapper_compose; eauto. }
  assert (IS_W_SAME : is_w (upd (lab_t' ∘ mapper) a l) e = W_t' e).
  { unfold compose, is_w.
    now rewrite updo, ReordCommon.mapper_neq. }
  assert (A_NMAPPED : ~ (mapper ↑₁ E_t') a).
  { unfolder. intro F. desf.
    apply NINB'. arewrite (b = y); ins.
    apply ReordCommon.mapper_inj with (a := a) (b := b); ins.
    now rewrite ReordCommon.mapper_eq_b. }
  assert (A_IS_R : is_r (upd (lab_t' ∘ mapper) a l) a).
  { unfold is_r, compose. rewrite upds.
    red in U2V. desf; exfalso.
    all: enough (BNOTR : ~R_t b) by apply BNOTR, SIM_ACTS.
    all: now unfold is_r; rewrite <- FIN_LAB, Heq. }
  (* Actual proof *)
  constructor; ins.
  { replace ∅ with (mapper ↑₁ ∅); [| now rewrite set_collect_empty].
    apply WCore.wf_iff_struct_and_props; split.
    { destruct STEP. constructor; ins.
      { unfold FinThreads.fin_threads. ins.
        apply start_wf. }
      { now rewrite (WCore.wf_cc_ctrl_empty start_wf), collect_rel_empty. }
      { now rewrite (WCore.wf_cc_addr_empty start_wf), collect_rel_empty. }
      { now rewrite (WCore.wf_cc_data_empty start_wf), collect_rel_empty. }
      { apply exec_add_rf_cont. admit. (* TODO: need weaker lemma *) }
      { apply exec_add_rf_cont. admit. }
      { intros x [[INE | EQA] HINIT]; try now right.
        destruct INE as (x' & INE & HEQ).
        left. exists x'; split; eauto.
        apply (WCore.wf_g_init start_wf); split; ins.
        erewrite ReordCommon.mapper_inj with (x := x') (y := x)
                                             (a := a) (b := b).
        all: ins.
        destruct x as [xl | xtid xid]; ins.
        rewrite ReordCommon.mapper_init_actid with (a := a) (b := b).
        all: ins; now apply SIM_ACTS. }
      intros x [EQTID [INE | EQA]]; red in EQTID.
      { apply (WCore.wf_gc_acts start_wf); split; ins.
        destruct INE as (x' & INE & HEQ).
        rewrite ReordCommon.mapper_neq in HEQ; subst; ins.
        all: intro F'; subst x'; eauto.
        apply B_TID. erewrite rsrw_tid_a_tid_b; eauto.
        rewrite ReordCommon.mapper_eq_a; eauto. }
      subst; exfalso; apply SIM_ACTS.(rsrw_ninit_a _ _ _).
      apply (WCore.wf_gc_acts start_wf); split; ins. }
    apply cfg_add_event_nctrl_wf_props with (X := {|
      WCore.sc := mapper ↑ sc;
      WCore.G := exec_upd_lab _ a l;
      WCore.GC := exec_upd_lab _ a l;
      WCore.cmt := mapper ↑₁ ∅
    |}); ins.
    { apply SIM_ACTS. }
    { apply STEP. ins. }
    { admit. (* TODO: a is sb-max *) }
    { unfolder. exists (InitEvent l0).
      split; [| apply ReordCommon.mapper_init_actid].
      all: try now apply SIM_ACTS.
      apply BINIT. unfold loc in *.
      rewrite upds in LOC. red in U2V.
      do 2 desf. }
    { unfolder in DOM2. desf.
      unfolder in DOM1. desf.
      apply NINB'.
      rewrite ReordCommon.mapper_inj with (x := b) (y := y')
                                          (a := a) (b := b).
      all: ins; try now rewrite ReordCommon.mapper_eq_b.
      destruct STEP.
      apply (wf_rfE (WCore.wf_gc start_wf)) in DOM1.
      ins. unfolder in DOM1; desf. }
    { unfolder. ins. desf. }
    { unfolder. ins. desf. }
    { unfolder. splits; ins; desf.
      splits; eauto. left.
      exists sw. split; ins.
      rewrite ReordCommon.mapper_neq; ins. }
    { unfolder. splits; ins; desf.
      splits; eauto; unfold is_w, is_r, compose; rupd.
      rewrite ReordCommon.mapper_neq; ins. now rewrite FIN_LAB. }
    { unfolder. ins. desf. }
    { unfolder. eauto. }
    { apply cfg_upd_lab_wf_props with (e := a) (l := l) (X := {|
        WCore.sc := mapper ↑ sc;
        WCore.G := exec_mapped G_t mapper (lab_t' ∘ mapper);
        WCore.GC := exec_mapped G_t' mapper (lab_t' ∘ mapper);
        WCore.cmt := mapper ↑₁ ∅;
      |}); ins.
      { apply SIM_ACTS. }
      { unfold compose. now rewrite ReordCommon.mapper_eq_a. }
      { unfolder. intro F. desf.
        apply (wf_rfE (WCore.wf_gc (WCore.start_wf STEP))) in F.
        ins. unfolder in F. desf.
        apply NINB'.
        rewrite ReordCommon.mapper_inj with (a := a) (b := b)
                                            (x := b) (y := y').
        all: ins.
        now rewrite ReordCommon.mapper_eq_b. }
      { unfolder. intro F. desf.
        apply (wf_rfE (WCore.wf_gc (WCore.start_wf STEP))) in F.
        ins. unfolder in F. desf.
        apply NINB'.
        rewrite ReordCommon.mapper_inj with (a := a) (b := b)
                                            (x := b) (y := x').
        all: ins.
        now rewrite ReordCommon.mapper_eq_b. }
      apply cfg_mapped_wf_props with (X := {|
        WCore.sc := sc;
        WCore.G := G_t;
        WCore.GC := G_t';
        WCore.cmt := ∅;
      |}); ins.
      all: try now apply STEP.
      { apply ReordCommon.mapper_inj. eapply rsrw_a_neq_b; eauto. }
      { tertium_non_datur (y = a) as [EQ|NEQA].
        { subst. exists b. now rewrite ReordCommon.mapper_eq_b. }
        tertium_non_datur (y = b) as [EQ|NEQB].
        { subst. exists a. now rewrite ReordCommon.mapper_eq_a. }
        exists y. rewrite ReordCommon.mapper_neq; ins. }
      { apply ReordCommon.mapper_init_actid. apply SIM_ACTS.(rsrw_ninit_a G_t a b).
        apply SIM_ACTS.(rsrw_ninit_b G_t a b). }
      { apply ReordCommon.mapped_G_t_immsb_helper; ins.
        all: try now apply SIM_ACTS.
        apply STEP. }
      { apply ReordCommon.mapped_G_t_sb_helper; ins.
        all: try now apply SIM_ACTS.
        apply STEP. }
      (* FIXME: uses auto gen names *)
      { admit. (* TODO: lemma *) }
       admit. }
    { rewrite (WCore.wf_cc_ctrl_empty (WCore.start_wf STEP)).
      now rewrite collect_rel_empty. }
    admit. (* TODO *) }
  { replace ∅ with (mapper ↑₁ ∅) by now rewrite set_collect_empty.
    replace e with (mapper e) by now rewrite ReordCommon.mapper_neq.
    destruct STEP. red in add_event. desf. ins.
    exists (option_map mapper r), (option_map mapper w),
           (mapper ↑₁ W1), (mapper ↑₁ W2).
    splits.
    { admit. }
    { apply cfg_add_event_nctrl_add_step_props with
        (X := {|
          WCore.sc := mapper ↑ sc;
          WCore.G := exec_mapped G_t  _ _;
          WCore.GC := exec_mapped G_t' _ _;
          WCore.cmt := mapper ↑₁ ∅
        |})
        (X' := {|
          WCore.sc := mapper ↑ sc;
          WCore.G := exec_mapped G_t'  _ _;
          WCore.GC := exec_mapped G_t' _ _;
          WCore.cmt := mapper ↑₁ ∅
        |}).
      { ins. intro F. apply set_collect_empty in F.
        desf. }
      apply cfg_upd_lab_add_step_props with
        (X := {|
          WCore.sc := mapper ↑ sc;
          WCore.G := exec_mapped G_t  _ _;
          WCore.GC := exec_mapped G_t' _ _;
          WCore.cmt := mapper ↑₁ ∅
        |})
        (X' := {|
          WCore.sc := mapper ↑ sc;
          WCore.G := exec_mapped G_t'  _ _;
          WCore.GC := exec_mapped G_t' _ _;
          WCore.cmt := mapper ↑₁ ∅
        |}).
      { ins. unfold compose. now rewrite ReordCommon.mapper_eq_a. }
      apply cfg_mapped_add_step_props with
        (X := {|
            WCore.sc := sc;
            WCore.G := G_t;
            WCore.GC := G_t';
            WCore.cmt := ∅;
        |})
        (X' := {|
            WCore.sc := sc;
            WCore.G := G_t';
            WCore.GC := G_t';
            WCore.cmt := ∅;
        |}).
      { now apply ReordCommon.mapper_inj. }
      { now apply ReordCommon.mapper_surj. }
      { ins. }
      apply PROPS. }
    { admit. (* Trace *) }
    apply WCore.wf_iff_struct_and_props; split.
    { constructor; ins.
      { unfold FinThreads.fin_threads. ins.
        apply start_wf. }
      { now rewrite (WCore.wf_cc_ctrl_empty start_wf), collect_rel_empty. }
      { now rewrite (WCore.wf_cc_addr_empty start_wf), collect_rel_empty. }
      { now rewrite (WCore.wf_cc_data_empty start_wf), collect_rel_empty. }
      { apply exec_add_rf_cont. admit. (* TODO: need weaker lemma *) }
      { apply exec_add_rf_cont. admit. }
      { intros x [[INE | EQA] HINIT]; try now right.
        destruct INE as (x' & INE & HEQ).
        left. exists x'; split; eauto. }
      intros x [EQTID [INE | EQA]]; red in EQTID.
      { apply (WCore.wf_gc_acts start_wf); split; ins.
        destruct INE as (x' & INE & HEQ).
        rewrite ReordCommon.mapper_neq in HEQ; subst; ins.
        all: intro F'; subst x'; eauto.
        apply B_TID. erewrite rsrw_tid_a_tid_b; eauto.
        rewrite ReordCommon.mapper_eq_a; eauto. }
      subst; exfalso; apply SIM_ACTS.(rsrw_ninit_a _ _ _).
      apply (WCore.wf_gc_acts start_wf); split; ins. }
    apply cfg_add_event_nctrl_wf_props with (X := {|
      WCore.sc := mapper ↑ sc;
      WCore.G := exec_upd_lab _ a l;
      WCore.GC := exec_upd_lab _ a l;
       WCore.cmt := mapper ↑₁ ∅
    |}); ins.
    { apply SIM_ACTS. }
    { apply start_wf. ins. }
    { admit. }
    { admit. }
    { admit. }
    { unfolder. ins. desf. }
    { unfolder. ins. desf. }
    { admit. }
    { admit. }
    { unfolder. ins. desf. }
    { unfolder. eauto. }
    { apply cfg_upd_lab_wf_props with (X := {|
        WCore.sc := mapper ↑ sc;
        WCore.G := exec_mapped _ _ _;
        WCore.GC := exec_mapped _ _ _;
        WCore.cmt := mapper ↑₁ ∅;
      |}); ins.
      all: admit. }
    { rewrite (WCore.wf_cc_ctrl_empty start_wf).
      now rewrite collect_rel_empty. }
    admit. (* TODO *) }
  admit.
Admitted.

(*
  Lemma that unites to big cases into one megacase: iff.

  This is when both events are either present or absent in the
  target execution.
*)
Lemma simrel_exec_iff e sc
    (SAME : E_t a <-> E_t b)
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons G_t sc)
    (STEP : WCore.exec_inst G_t G_t' sc traces e)
    (SIM : reord_simrel_rw G_s G_t a b) :
  exists G_s' sc',
    WCore.exec_inst G_s G_s' sc' traces' e.
Proof using.
  assert (NRMWDEP : ~rmw_dep_t' a b).
  { admit. }
  assert (NRMW : ~rmw_t' a b).
  { admit. }
  assert (NRMWCODOM : ~codom_rel rmw_t' a).
  { admit. }
  assert (NRMWDOM : ~dom_rel rmw_t' b).
  { admit. }
  assert (HEQLAB : lab_t' = lab_t).
  { admit. }
  tertium_non_datur (E_t a) as [INA|NINA];
  tertium_non_datur (E_t b) as [INB|NINB].
  all: try now (desf; exfalso; eauto).
  { exists (exec_mapped G_t' mapper (lab_t'  ∘ mapper)),
           (mapper ↑ sc).
    replace G_s with (exec_mapped G_t mapper (lab_t ∘ mapper)).
    { replace lab_t with lab_t' by ins.
      apply simrel_exec_iff_helper_1; ins.
      apply SIM. }
    symmetry. apply exeeqv_eq. apply rsrw_struct_same1; ins.
    all: try now apply SIM. }
  assert (U2V : same_label_u2v (lab_s a) (lab_t b)).
  { rewrite <- ReordCommon.mapper_eq_b with (a := a) (b := b).
    change (lab_s (mapper b)) with ((lab_s ∘ mapper) b).
    now apply SIM. }
  exists (exec_upd_lab
          (exec_mapped G_t' mapper (lab_t' ∘ mapper))
        a (lab_s a)), (mapper ↑ sc).
  replace G_s with (exec_upd_lab
                      (exec_mapped G_t mapper (lab_t' ∘ mapper))
                    a (lab_s a)) at 1.
  { apply simrel_exec_iff_helper_2; ins.
    { rewrite HEQLAB. now apply same_label_u2v_comm. }
    apply SIM. }
  rewrite HEQLAB.
  symmetry. apply exeeqv_eq. apply rsrw_struct_same2; ins.
  all: apply SIM.
Admitted.

Lemma simrel_exec_b_helper sc sw l
    (U2V : same_label_u2v (lab_t' b) l)
    (WB_LOC : same_loc (upd (lab_t' ∘ mapper) a l) a sw)
    (WB_VAL : val (upd (lab_t' ∘ mapper) a l) sw =
              val (upd (lab_t' ∘ mapper) a l) a)
    (INA : ~E_t a)
    (NINB : ~E_t b)
    (SIM_ACTS : reord_simrel_rw_actids G_t a b)
    (W_NOT_A : sw <> a)
    (W_NOT_B : sw <> b)
    (CONS : WCore.is_cons G_t sc)
    (STEP : WCore.exec_inst G_t G_t' sc traces a)
    (HWIN : E_t sw)
    (W_IS : W_t sw)
    (NRMWDEP : ~rmw_dep_t' a b)
    (NRMW : ~rmw_t' a b)
    (NRMWCODOM : ~codom_rel rmw_t' a)
    (NRMWDOM : ~dom_rel rmw_t' b) :
  << STEP1 : WCore.exec_inst
              (exec_upd_lab
                (exec_mapped G_t  mapper (lab_t'  ∘ mapper))
                a l)
              (exec_add_rf
                (exec_add_read_event_nctrl
                  (exec_upd_lab
                    (exec_mapped G_t mapper (lab_t' ∘ mapper))
                    a l) a)
                (singl_rel sw a))
              (mapper ↑ sc)
              traces'
              a >> /\
  << STEP2 : WCore.exec_inst
              (exec_add_rf
                (exec_add_read_event_nctrl
                  (exec_upd_lab
                    (exec_mapped G_t mapper (lab_t' ∘ mapper))
                    a l) a)
                (singl_rel sw a))
              (exec_add_rf
                (exec_add_read_event_nctrl
                  (exec_upd_lab
                    (exec_mapped G_t' mapper (lab_t' ∘ mapper))
                    a l) a)
                (singl_rel sw a))
              (mapper ↑ sc)
              traces'
              b >>.
Proof using.
  assert (B_IS_R : R_t' b).
  { admit. }
  assert (W_IS_W' : W_t' sw).
  { admit. }
  split.
  { constructor; ins.
    { admit. (* Start wf *) }
    { red. eexists _, _, _, _.
      splits.
      { admit. (* TODO: struct *) }
      { red in U2V.
        apply cfg_add_event_nctrl_as_add_step; ins.
        all: unfold compose, is_w, is_r; rupd; ins.
        { rewrite ReordCommon.mapper_neq; ins. }
        unfold is_r in B_IS_R. desf. }
      { admit. (* traces *) }
      admit. (* End wf -- todo lemma *) }
    admit. (* IS_cons *) }
  constructor; ins.
  { admit. (* Start wf *) }
  { destruct STEP. red in add_event. desf.
    exists (option_map mapper r), (option_map mapper w),
           (mapper ↑₁ W1), (mapper ↑₁ W2).
    splits.
    { admit. (* Struct *) }
    { replace ∅ with (mapper ↑₁ ∅) by now rewrite set_collect_empty.
      apply cfg_add_event_nctrl_add_step_props with
        (X := {|
          WCore.sc := mapper ↑ sc;
          WCore.G := exec_mapped G_t  _ _;
          WCore.GC := exec_mapped G_t' _ _;
          WCore.cmt := mapper ↑₁ ∅
        |})
        (X' := {|
          WCore.sc := mapper ↑ sc;
          WCore.G := exec_mapped G_t'  _ _;
          WCore.GC := exec_mapped G_t' _ _;
          WCore.cmt := mapper ↑₁ ∅
        |}).
      { ins. intro F. apply set_collect_empty in F. desf. }
      apply cfg_upd_lab_add_step_props with
        (X := {|
          WCore.sc := mapper ↑ sc;
          WCore.G := exec_mapped G_t  _ _;
          WCore.GC := exec_mapped G_t' _ _;
          WCore.cmt := mapper ↑₁ ∅
        |})
        (X' := {|
          WCore.sc := mapper ↑ sc;
          WCore.G := exec_mapped G_t'  _ _;
          WCore.GC := exec_mapped G_t' _ _;
          WCore.cmt := mapper ↑₁ ∅
        |}).
      { ins. unfold compose. now rewrite ReordCommon.mapper_eq_a. }
      rewrite <- ReordCommon.mapper_eq_a with (a := a) (b := b) at 13.
      apply cfg_mapped_add_step_props with
        (X := {|
            WCore.sc := sc;
            WCore.G := G_t;
            WCore.GC := G_t';
            WCore.cmt := ∅;
        |})
        (X' := {|
            WCore.sc := sc;
            WCore.G := G_t';
            WCore.GC := G_t';
            WCore.cmt := ∅;
        |}).
      { apply ReordCommon.mapper_inj. eapply rsrw_a_neq_b; eauto. }
      { apply ReordCommon.mapper_surj. eapply rsrw_a_neq_b; eauto. }
      { ins. admit. (* easy easy *) }
      apply PROPS. }
    { admit. (* Trace stuff *) }
    apply WCore.wf_iff_struct_and_props; split.
    { admit. (* STRUCT *) }
    replace ∅ with (mapper ↑₁ ∅) by now rewrite set_collect_empty.
    apply cfg_add_event_nctrl_wf_props with (X := {|
      WCore.sc := mapper ↑ sc;
      WCore.G := exec_upd_lab _ a l;
      WCore.GC := exec_upd_lab _ a l;
       WCore.cmt := mapper ↑₁ ∅
    |}); ins.
    { apply SIM_ACTS. }
    { admit. (* TODO: condition *) }
    { admit. (* <-> b is not in E_t', which is true *) }
    { admit. (* a is a read in source *) }
    { admit. }
    { admit. (* WF-ness noise *) }
    { admit. (* Other wf-ness noise *) }
    { admit. (* True, because it implies b being in E_t *) }
    { admit. (* Hyp *) }
    { basic_solver. }
    { admit. (* Inferrable from hyps *) }
    { admit. (* Inferrable from hyps *) }
    { basic_solver. }
    { basic_solver. }
    { apply cfg_upd_lab_wf_props with (X := {|
        WCore.sc := mapper ↑ sc;
        WCore.G := exec_mapped _ _ _;
        WCore.GC := exec_mapped _ _ _;
        WCore.cmt := mapper ↑₁ ∅;
      |}); ins.
      { apply SIM_ACTS. }
      { unfold compose. now rewrite ReordCommon.mapper_eq_a. }
      { admit. (* True because b is not in E_t *) }
      { admit. (* True because b is not in E_t *) }
      apply cfg_mapped_wf_props with (X := {|
        WCore.sc := sc;
        WCore.G := G_t';
        WCore.GC := G_t';
        WCore.cmt := ∅;
      |}); ins.
      { apply ReordCommon.mapper_inj. eapply rsrw_a_neq_b; eauto. }
      { apply ReordCommon.mapper_surj. eapply rsrw_a_neq_b; eauto. }
      { admit. (* TODO: easy *) }
      { apply ReordCommon.mapper_init_actid.
        all: apply SIM_ACTS. }
      { apply ReordCommon.mapped_G_t_immsb_helper.
        all: admit. }
      { apply ReordCommon.mapped_G_t_sb_helper.
        all: admit. }
      { admit. (* TODO *) }
      { admit. (* WFness noise *) }
      { apply start_wf. }
      { apply start_wf. }
      { apply start_wf. }
      apply WF_NEW. }
    { admit. (* Easy *) }
    admit. (* Looks easy too *) }
  admit. (* IS_cons *)
Admitted.

Lemma simrel_exec_b sc
    (CONS : WCore.is_cons G_t sc)
    (CONS' : WCore.is_cons G_s (mapper ↑ sc))
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' sc traces a) :
  exists G_s' sc',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    exists G_s'_int,
      << STEP1 : WCore.exec_inst G_s G_s'_int sc' traces' a >> /\
      << STEP2 : WCore.exec_inst G_s'_int G_s' sc' traces' b >>.
Proof using SWAPPED_TRACES.
  admit. (* TODO: research *)
Admitted.

Lemma simrel_exec_a_helper sc w sw l
    (CONS : WCore.is_cons G_t sc)
    (CONS' : WCore.is_cons G_s (mapper ↑ sc))
    (RF : rf_t' w b)
    (SIM_ACTS : reord_simrel_rw_actids G_t a b)
    (STEP : WCore.exec_inst G_t G_t' sc traces b) :
  exists dtrmt cmt,
    WCore.reexec
      (exec_add_rf
        (exec_add_read_event_nctrl
          (exec_upd_lab
            (exec_mapped G_t mapper (lab_t' ∘ mapper))
            a l) a)
        (singl_rel sw a))
      (exec_mapped G_t' mapper (lab_t'  ∘ mapper))
      (mapper ↑ sc)
      traces'
      dtrmt
      cmt.
Proof using.
  (* Shorthands *)
  set (G_s_ := exec_add_rf
    (exec_add_read_event_nctrl
      (exec_upd_lab
        (exec_mapped G_t mapper (lab_t' ∘ mapper))
        a l) a)
    (singl_rel sw a)).
  set (G_s' :=
    exec_mapped G_t' mapper (lab_t'  ∘ mapper)).
  set (dtrmt := mapper ↑₁ E_t \₁ codom_rel (
    ⦗eq a⦘ ⨾ (sb G_s_ ∪ rf G_s_)＊
  )).
  set (delta := acts_set G_s' \₁ dtrmt).
  set (cmt := acts_set G_s_ \₁ eq a).
  set (f := fun x => ifP cmt x then Some x else None).
  (* Asserts *)
  assert (DTRMT_INIT : mapper ↑₁ E_t' ∩₁ is_init ⊆₁ dtrmt).
  { admit. }
  assert (ACTEQ : E_t' ≡₁ E_t ∪₁ eq b).
  { admit. (* TODO: use step *) }
  assert (WINE : E_t w).
  { admit. }
  (* Actual proof *)
  admit.
Admitted.

Lemma simrel_exec_a sc w
    (CONS : WCore.is_cons G_t sc)
    (CONS' : WCore.is_cons G_s (mapper ↑ sc))
    (RF : rf_t' w a)
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' sc traces b) :
  exists G_s' sc' dtrmt' cmt',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP : WCore.reexec G_s G_s' sc' traces' dtrmt' cmt' >>.
Proof using SWAPPED_TRACES.
  (* TODO: check article *)
  (* Case1 : Gt' *)
  (* Case2: mapped Gt but with executed a *)
  admit.
Admitted.

End SimrelExec.

Section SimrelReexec.

Variable G_t G_t' G_s : execution.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable a b : actid.

Notation "'lab_t'" := (lab G_t).
Notation "'val_t'" := (val lab_t).
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
Notation "'W_t'" := (is_w lab_t).
Notation "'R_t'" := (is_r lab_t).

Notation "'lab_t''" := (lab G_t').
Notation "'val_t''" := (val lab_t').
Notation "'E_t''" := (acts_set G_t').
Notation "'sb_t''" := (sb G_t').
Notation "'rf_t''" := (rf G_t').
Notation "'co_t''" := (co G_t').
Notation "'rmw_t''" := (rmw G_t').
Notation "'rpo_t''" := (rpo G_t').
Notation "'rmw_dep_t''" := (rmw_dep G_t').
Notation "'data_t''" := (data G_t').
Notation "'ctrl_t''" := (ctrl G_t').
Notation "'addr_t''" := (addr G_t').
Notation "'W_t''" := (is_w lab_t').
Notation "'R_t''" := (is_r lab_t').

Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
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
Notation "'srf_s'" := (srf G_s).

Notation "'mapper'" := (ReordCommon.mapper a b).

Hypothesis SWAPPED_TRACES : ReordCommon.traces_swapped traces traces' a b.

Lemma simrel_reexec sc dtrmt cmt
    (CONS : WCore.is_cons G_t sc)
    (CONS' : WCore.is_cons G_s (mapper ↑ sc))
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.reexec G_t G_t' sc traces dtrmt cmt) :
  exists G_s' sc' dtrmt' cmt',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP : WCore.reexec G_s G_s' sc' traces' dtrmt' cmt' >>.
Proof using SWAPPED_TRACES.
  admit.
Admitted.

End SimrelReexec.

Section SimrelMisc.

Variable G_t G_t' G_s : execution.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable a b : actid.

Notation "'lab_t'" := (lab G_t).
Notation "'val_t'" := (val lab_t).
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
Notation "'W_t'" := (is_w lab_t).
Notation "'R_t'" := (is_r lab_t).

Notation "'lab_t''" := (lab G_t').
Notation "'val_t''" := (val lab_t').
Notation "'E_t''" := (acts_set G_t').
Notation "'sb_t''" := (sb G_t').
Notation "'rf_t''" := (rf G_t').
Notation "'co_t''" := (co G_t').
Notation "'rmw_t''" := (rmw G_t').
Notation "'rpo_t''" := (rpo G_t').
Notation "'rmw_dep_t''" := (rmw_dep G_t').
Notation "'data_t''" := (data G_t').
Notation "'ctrl_t''" := (ctrl G_t').
Notation "'addr_t''" := (addr G_t').
Notation "'W_t''" := (is_w lab_t').
Notation "'R_t''" := (is_r lab_t').

Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
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
Notation "'srf_s'" := (srf G_s).

Notation "'mapper'" := (ReordCommon.mapper a b).

Lemma simrel_implies_cons sc
    (CONS : WCore.is_cons G_t sc)
    (SIM : reord_simrel_rw G_s G_t a b) :
  WCore.is_cons G_s (mapper ↑ sc).
Proof using.
  admit.
Admitted.

Lemma simrel_term sc
    (CONS : WCore.is_cons G_t sc)
    (SIM : reord_simrel_rw G_t G_s a b)
    (TERM : machine_terminated G_t traces) :
  << TERM' : machine_terminated G_s traces' >> /\
  << SIM' : ReordCommon.reord G_s G_t traces traces' a b >>.
Proof using.
  admit.
Admitted.

End SimrelMisc.

(* Lemma sim_rel_step : about any step *)

(*
 forall traces P_src, P_trgt. If target is a reordereing of src, then
 <..> (clarify cuz the theorem statement looks weird)
*)
(* Theorem reordering_rw : TODO.
Proof using.
  admit.
Admitted. *)


End ReordRwSimRelProps.