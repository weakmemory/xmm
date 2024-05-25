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
  rsrw_loc : ~same_loc (lab_t) a b;
  rsrw_a_nrmwp : ~codom_rel rmw_t a;
  rsrw_u2v : same_label_u2v (lab_s a) (lab_t b);
  rsrw_b_lab : forall (INB : E_t b), val_s a = val_t b;
  rsrw_srf_val : funeq (val
    (upd (lab_t ∘ mapper) a (lab_s a))
  ) (srf_s ⨾ ⦗eq a⦘);
}.

Record reord_simrel_rw_core : Prop :=
{ rsrw_actids_t_ord : forall (INB : E_t b) (NOTINA : ~E_t a), False;
  rsrw_a_max : forall (INA : E_t a) (NOTINB : ~E_t b),
                  max_elt (sb G_t) a; }.

Record reord_simrel_rw_struct : Prop := {
  rsrw_lab_val_end : forall (INB : E_t b),
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
                    rf_s ≡ mapper ↑ rf_t ∪ (srf_s ⨾ ⦗eq a⦘);
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

Lemma rsrw_mapper_inj : inj_dom ⊤₁ mapper.
Proof using RSRW_ACTIDS.
  eauto using ReordCommon.mapper_inj, rsrw_a_neq_b.
Qed.

Lemma rsrw_mapper_surj : surj_dom ⊤₁ mapper.
Proof using RSRW_ACTIDS.
  eauto using ReordCommon.mapper_surj, rsrw_a_neq_b.
Qed.

Lemma rsrw_tid_a_tid_b : tid a = tid b.
Proof using RSRW_ACTIDS.
  destruct RSRW_ACTIDS. unfolder in rsrw_a_b_ord0.
  unfold ext_sb, is_init in *. desf.
  ins. desf.
Qed.

Lemma rsrw_lab_a_eq_lab_b (BIN : E_t b) :
  lab_s a = lab_t b.
Proof using RSRW_ACTIDS.
  transitivity ((lab_t ∘ mapper) a).
  { apply same_label_u2v_val.
    all: unfold compose, val; ins.
    all: rewrite ReordCommon.mapper_eq_a.
    all: now apply RSRW_ACTIDS. }
  unfold compose.
  now rewrite ReordCommon.mapper_eq_a.
Qed.

Lemma rsrw_struct_same_lab
    (STRUCT : reord_simrel_rw_struct) :
  lab_s = upd (lab_t ∘ mapper) a (lab_s a).
Proof using RSRW_ACTIDS.
  apply functional_extensionality. intro x.
  tertium_non_datur (x = a) as [HEQ|NEQ]; subst; rupd; ins.
  apply same_label_u2v_val.
  { rewrite <- ReordCommon.mapper_mapper_compose'
      with (a := a) (b := b) (f := lab_s).
    all: auto using rsrw_a_neq_b.
    apply same_lab_u2v_compose; ins.
    apply STRUCT. }
  unfold val, compose.
  destruct ReordCommon.mapper_surj with (y := x) (a := a) (b := b)
          as [y HEQ].
  { apply rsrw_a_neq_b. }
  subst. rewrite ReordCommon.mapper_self_inv; [| apply rsrw_a_neq_b].
  apply STRUCT. intro F; subst.
  now rewrite ReordCommon.mapper_eq_b in NEQ.
Qed.

Definition rsrw_G_s_iff :=
  exec_upd_lab
    (exec_mapped G_t mapper (lab_t ∘ mapper))
  a (lab_s a).
Definition rsrw_G_s_niff :=
  exec_add_rf
    (exec_add_read_event_nctrl rsrw_G_s_iff a)
    (srf_s ⨾ ⦗eq a⦘).

Lemma rsrw_struct_same
    (SAME : E_t a <-> E_t b) :
  reord_simrel_rw_struct <-> exec_equiv G_s rsrw_G_s_iff.
Proof using RSRW_ACTIDS.
  unfold rsrw_G_s_iff.
  split; [intro STRUCT | intro EQUIV].
  { split; try constructor; ins.
    all: try now apply STRUCT.
    apply rsrw_struct_same_lab; ins. }
  assert (EQVLAB : lab_s = upd (lab_t ∘ mapper) a (lab_s a)).
  { now rewrite (exeeqv_lab EQUIV) at 1. }
  constructor; ins.
  all: try now apply EQUIV.
  all: try now (exfalso; now apply NOTINB, SAME).
  { now apply RSRW_ACTIDS. }
  { rewrite EQVLAB, upd_compose; [|apply ReordCommon.mapper_inj, rsrw_a_neq_b].
    rewrite ReordCommon.mapper_mapper_compose'.
    all: auto using rsrw_a_neq_b.
    rewrite ReordCommon.mapper_eq_a. do 2 red. intros e _.
    tertium_non_datur (e = b) as [HEQ|NEQ]; subst; rupd.
    all: try now apply RSRW_ACTIDS.
    red; desf. }
  { rewrite EQVLAB, upd_compose; [|apply ReordCommon.mapper_inj, rsrw_a_neq_b].
    rewrite ReordCommon.mapper_eq_a.
    change (val (upd lab_t b (lab_s a) ∘ mapper) ∘ mapper)
    with (val (upd lab_t b (lab_s a) ∘ mapper ∘ mapper)).
    rewrite ReordCommon.mapper_mapper_compose'.
    all: auto using rsrw_a_neq_b.
    unfold val. rewrite updo; ins. }
  rewrite EQUIV.(exeeqv_acts _ _); ins.
Qed.

Lemma rsrw_struct_niff
    (INA : E_t a)
    (NOTINB : ~E_t b)
    (U2V  : same_label_u2v (lab_s a) (lab_t b))
    (EQVLAB : lab_s = upd (lab_t ∘ mapper) a (lab_s a)) :
  reord_simrel_rw_struct <->
    exec_equiv G_s rsrw_G_s_niff.
Proof using RSRW_ACTIDS.
  unfold rsrw_G_s_niff, rsrw_G_s_iff.
  split; [intro STRUCT | intro EQUIV].
  { constructor; ins.
    all: try now apply STRUCT. }
  constructor; ins.
  all: try now apply EQUIV.
  all: try now (exfalso; apply NOTINB, SAME, INA).
  { rewrite EQVLAB, upd_compose; [| apply ReordCommon.mapper_inj, rsrw_a_neq_b].
    rewrite ReordCommon.mapper_mapper_compose'.
    all: auto using rsrw_a_neq_b.
    rewrite ReordCommon.mapper_eq_a. do 2 red. intros e _.
    tertium_non_datur (e = b) as [HEQ|NEQ]; subst; rupd; ins.
    red. desf. }
  { rewrite EQVLAB, upd_compose; [| apply ReordCommon.mapper_inj, rsrw_a_neq_b].
    rewrite ReordCommon.mapper_eq_a.
    change (val (upd lab_t b (lab_s a) ∘ mapper) ∘ mapper)
      with (val (upd lab_t b (lab_s a)) ∘ mapper ∘ mapper).
    rewrite ReordCommon.mapper_mapper_compose'.
    all: auto using rsrw_a_neq_b.
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
    (ACTIDS : reord_simrel_rw_actids G_s G_t a b)
    (STRUCT : reord_simrel_rw_struct G_s G_t a b) :
  reord_simrel_rw (WCore.init_exec G_s) (WCore.init_exec G_t) a b.
Proof using.
  constructor; constructor; ins.
  all: try now (rewrite collect_rel_empty; ins).
  all: try now (exfalso; apply ACTIDS.(rsrw_ninit_a G_s G_t a b), INA).
  all: try now (exfalso; apply ACTIDS.(rsrw_ninit_b G_s G_t a b), INB).
  all: try now apply ACTIDS.
  all: try now apply STRUCT.
  { unfolder. intros F. desf. }
  { admit. }
  all: rewrite STRUCT.(rsrw_init _ _ _ _).
  all: rewrite set_collect_interE, ReordCommon.mapper_is_init; ins.
  all: try now apply ACTIDS.
  all: eauto using rsrw_mapper_inj.
Admitted.

End Basic.

Section SimRelExec.

Variable G_t G_t' G_s : execution.
Variable sc : relation actid.
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

Hypothesis IS_CONS : WCore.is_cons G_t sc.
Hypothesis SWAPPED_TRACES : ReordCommon.traces_swapped traces traces' a b.

Lemma simrel_exec_iff e
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (SAME : E_t a <-> E_t b)
    (STEP : WCore.exec_inst G_t G_t' sc traces e)
    (SIM_ACTS : reord_simrel_rw_actids G_s G_t a b) :
  WCore.exec_inst
    (rsrw_G_s_iff G_s G_t  a b)
    (rsrw_G_s_iff G_s G_t' a b)
    (mapper ↑ sc)
    traces'
    e.
Proof using IS_CONS.
  (* Useful props *)
  assert (FIN_LAB : lab_t' = lab_t).
  { symmetry. eapply sub_lab.
    eapply WCore.wf_g_sub_gc
    with (X := {|
      WCore.G := G_t;
      WCore.GC := G_t';
      WCore.sc := sc;
      WCore.cmt := ∅;
    |}).
    apply STEP. }
  assert (SAME' : E_t' a <-> E_t' b).
  { rewrite <- !set_subset_single_l with (s := E_t'),
            (WCore.cae_e_new (WCore.add_event STEP)),
            !set_subset_single_l.
    ins. unfolder. split; ins; desf; eauto. }
  assert (WF' : WCore.wf {|
    WCore.sc := sc;
    WCore.G := G_t;
    WCore.GC := G_t';
    WCore.cmt := ∅;
  |}).
  { apply STEP. }
  assert (WF_G_t' : Wf G_t').
  { apply WF'. }
  assert (NEW_RF_WF :
    funeq
      (val
        (upd (lab_t' ∘ mapper) a
            (lab_s a)))
      (mapper ↑ rf_t')
  ).
  { rewrite upd_compose, ReordCommon.mapper_eq_a; eauto using rsrw_mapper_inj.
    unfolder. intros x y HREL. desf. unfold compose, val.
    destruct (classic (E_t b)) as [BIN|NBIN];
      [arewrite (lab_s a = lab_t' b) | rewrite !updo].
    all: rewrite ?updI, ?ReordCommon.mapper_self_inv.
    all: try now apply WF_G_t'.
    all: eauto using rsrw_a_neq_b.
    { rewrite FIN_LAB. eauto using rsrw_lab_a_eq_lab_b. }
    all: intro F; subst.
    all: apply (wf_rfE WF_G_t') in HREL.
    all: unfolder in HREL; desf; eauto.
    all: enough (NBIN' : ~E_t' b); eauto.
    all: intro F; apply (WCore.cae_e_new (WCore.add_event STEP)) in F.
    all: ins; unfolder in F; desf. }
  assert (U2V : same_label_u2v ((lab_t' ∘ mapper) a) (lab_s a)).
  { rewrite FIN_LAB. unfold compose.
    rewrite ReordCommon.mapper_eq_a.
    apply same_label_u2v_comm, SIM_ACTS. }
  (* actual proof *)
  constructor; ins.
  { replace ∅ with (mapper ↑₁ ∅) by now rewrite set_collect_empty.
    apply cfg_upd_lab_wf with (X := {|
      WCore.sc := mapper ↑ sc;
      WCore.G := exec_mapped G_t _ _;
      WCore.GC := exec_mapped G_t' _ _;
      WCore.cmt := mapper ↑₁ ∅;
    |}); ins.
    { apply SIM_ACTS. }
    rewrite <- FIN_LAB.
    apply ReordCommon.mapped_G_t_cfg with (X := {|
      WCore.sc := sc;
      WCore.G := G_t;
      WCore.GC := G_t';
      WCore.cmt := ∅;
    |}); ins.
    all: try now apply SIM_ACTS.
    all: eauto using rsrw_a_neq_b, rsrw_tid_a_tid_b.
    { admit. (* TODO: rsrw_a_b_nrmw_dep *) }
    { admit. (* TODO: nsame_loc_nrmw *) }
    { admit. (* TODO: supplied by simrel *) }
    admit. (* NOTE: unproveable *) }
  { destruct STEP. red in add_event. desf.
    exists (option_map mapper r), (option_map mapper w),
           (mapper ↑₁ W1), (mapper ↑₁ W2).
    splits; ins.
    { admit. }
    { replace ∅ with (mapper ↑₁ ∅) by now rewrite set_collect_empty.
      replace e with (mapper e) by now rewrite ReordCommon.mapper_neq.
      apply cfg_upd_lab_add_step_props with
        (X := {|
          WCore.sc := mapper ↑ sc;
          WCore.G := exec_mapped G_t _ _;
          WCore.GC := exec_mapped G_t' _ _;
          WCore.cmt := mapper ↑₁ ∅;
        |})
        (X' := {|
          WCore.sc := mapper ↑ sc;
          WCore.G := exec_mapped G_t' _ _;
          WCore.GC := exec_mapped G_t' _ _;
          WCore.cmt := mapper ↑₁ ∅;
        |}); ins.
      rewrite <- FIN_LAB.
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
      all: eauto using rsrw_mapper_inj, rsrw_mapper_surj.
      rewrite ReordCommon.mapper_mapper_compose'; ins.
      eapply rsrw_a_neq_b; eauto. }
    { admit. (* TODO: traces *) }
    replace ∅ with (mapper ↑₁ ∅) by now rewrite set_collect_empty.
    apply cfg_upd_lab_wf with (X := {|
      WCore.sc := mapper ↑ sc;
      WCore.G := exec_mapped G_t' _ _;
      WCore.GC := exec_mapped G_t' _ _;
      WCore.cmt := mapper ↑₁ ∅;
    |}); ins.
    { apply SIM_ACTS. }
    apply ReordCommon.mapped_G_t_cfg with (X := {|
      WCore.sc := sc;
      WCore.G := G_t';
      WCore.GC := G_t';
      WCore.cmt := ∅;
    |}); ins.
    all: try now apply SIM_ACTS.
    all: eauto using rsrw_a_neq_b, rsrw_tid_a_tid_b.
    { admit. (* TODO: see above *) }
    { admit. (* TODO: see above *) }
    { admit. (* TODO: see above *) }
    admit. (* TODO: see abouve *) }
  admit. (* TODO: is_cons *)
Admitted.

Lemma simrel_exec_niff e
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (B_TID : tid a <> tid_init)
    (STEP : WCore.exec_inst G_t G_t' sc traces e)
    (SIM_ACTS : reord_simrel_rw_actids G_s G_t a b)
    (INA :   E_t a)
    (NINB : ~E_t b)
    (BINIT : forall l0 (LOC : loc lab_t' b = Some l0), E_t' (InitEvent l0)) :
  WCore.exec_inst
    (rsrw_G_s_niff G_s G_t  a b)
    (rsrw_G_s_niff G_s G_t' a b)
    (mapper ↑ sc)
    traces'
    e.
Proof using IS_CONS.
  assert (INA' : E_t' a).
  { apply (WCore.cae_e_new (WCore.add_event STEP)).
    ins. now left. }
  assert (NINB' : ~E_t' b).
  { intro F'.
    apply (WCore.cae_e_new (WCore.add_event STEP)) in F'.
    ins.  destruct F' as [HIN|HEQ]; ins. }
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
  (* Actual proof *)
  constructor; ins.
  { replace ∅ with (mapper ↑₁ ∅); [| now rewrite set_collect_empty].
    apply WCore.wf_iff_struct_and_props; split.
    { constructor; ins.
      { apply STEP. }
      { now rewrite (WCore.wf_cc_ctrl_empty (WCore.start_wf STEP)),
                    collect_rel_empty. }
      { now rewrite (WCore.wf_cc_addr_empty (WCore.start_wf STEP)),
                    collect_rel_empty. }
      { now rewrite (WCore.wf_cc_data_empty (WCore.start_wf STEP)),
                    collect_rel_empty. }
      { admit. (* TODO: need weaker lemma *) }
      { admit. }
      { admit. (* TODO: easy *) }
      admit. }
    apply cfg_add_event_nctrl_wf_props with (X := {|
      WCore.sc := mapper ↑ sc;
      WCore.G := exec_upd_lab _ _ _;
      WCore.GC := exec_upd_lab _ _ _;
      WCore.cmt := mapper ↑₁ ∅
    |}); ins.
    { apply SIM_ACTS. }
    { admit. (* TODO: trivial *) }
    { admit. (* TODO: easy *) }
    { admit. (* TODO: Wf G_t' *) }
    { admit. (* TODO: a is sb max *) }
    { admit. }
    { admit. (* TODO: wf_srfE *) }
    { rewrite FIN_LAB.
      apply SIM_ACTS. }
    { admit. }
    { admit. (* TODO: wf_srf *) }
    { admit. (* TODO: wf_srfD *) }
    { admit. (* TODO: srf prop *) }
    { admit. (* TODO: srf exists *) }
    { apply cfg_upd_lab_wf_props with (e := a) (X := {|
        WCore.sc := mapper ↑ sc;
        WCore.G := exec_mapped _ _ _;
        WCore.GC := exec_mapped _ _ _;
        WCore.cmt := mapper ↑₁ ∅;
      |}); ins.
      { apply SIM_ACTS. }
      { unfold compose. rewrite FIN_LAB, ReordCommon.mapper_eq_a.
        apply same_label_u2v_comm. apply SIM_ACTS. (* NOTE: label *) }
      { admit. (* TODO: excludes srf edge, so must be easy *) }
      rewrite <- FIN_LAB.
      apply cfg_mapped_wf_props with (X := {|
        WCore.sc := sc;
        WCore.G := G_t;
        WCore.GC := G_t';
        WCore.cmt := ∅;
      |}); ins.
      all: eauto using rsrw_mapper_inj, rsrw_mapper_surj.
      all: try now apply STEP.
      { rewrite ReordCommon.mapper_mapper_compose'; ins.
        eauto using rsrw_a_neq_b. }
      { apply ReordCommon.mapper_init_actid.
        all: apply SIM_ACTS. }
      { apply ReordCommon.mapped_G_t_immsb_helper; ins.
        all: try now apply SIM_ACTS.
        all: admit. }
      { apply ReordCommon.mapped_G_t_sb_helper; ins.
        all: try now apply SIM_ACTS.
        all: admit. }
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
    { unfold rsrw_G_s_niff.
      assert (SRFEQ : exists sw, srf_s ⨾ ⦗eq a⦘ ≡ singl_rel sw a).
      { admit. }
      destruct SRFEQ as [sw SRFEQ].
      apply rel_extensionality in SRFEQ. rewrite SRFEQ.
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
      { admit. }
      rewrite <- FIN_LAB.
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
      all: eauto using rsrw_mapper_inj, rsrw_mapper_surj.
      rewrite ReordCommon.mapper_mapper_compose'; ins.
      eauto using rsrw_a_neq_b. }
    { admit. (* Trace *) }
    apply WCore.wf_iff_struct_and_props; split.
    { admit. }
    admit. (* TODO *) }
  admit. (* TODO: is cons *)
Admitted.

Lemma simrel_exec_not_a_not_b e
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (STEP : WCore.exec_inst G_t G_t' sc traces e)
    (SIM : reord_simrel_rw G_s G_t a b) :
  exists G_s' sc',
    WCore.exec_inst G_s G_s' sc' traces' e.
Proof using IS_CONS.
  destruct (classic (E_t a)) as [INA|NINA];
  destruct (classic (E_t b)) as [INB|NINB].
  admit.
Admitted.

Lemma simrel_exec_b_helper
    (INA : ~E_t a)
    (NINB : ~E_t b)
    (SIM_ACTS : reord_simrel_rw_actids G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' sc traces a) :
  << STEP1 : WCore.exec_inst
              (rsrw_G_s_iff  G_s G_t a b)
              (rsrw_G_s_niff G_s G_t a b)
              (mapper ↑ sc)
              traces'
              a >> /\
  << STEP2 : WCore.exec_inst
              (rsrw_G_s_niff G_s G_t  a b)
              (rsrw_G_s_niff G_s G_t' a b)
              (mapper ↑ sc)
              traces'
              b >>.
Proof using.
  assert (FIN_LAB : lab G_t' = lab_t).
  { admit. }
  assert (B_IS_R : R_t' b).
  { admit. }
  assert (SRFEQ : exists sw, srf_s ⨾ ⦗eq a⦘ ≡ singl_rel sw a).
  { admit. }
  destruct SRFEQ as [sw SRFEQ].
  apply rel_extensionality in SRFEQ.
  split.
  { constructor; ins.
    { admit. (* Start wf *) }
    { red. eexists _, _, _, _.
      splits.
      { admit. (* TODO: struct *) }
      { unfold rsrw_G_s_iff, rsrw_G_s_niff.
        rewrite SRFEQ.
        apply cfg_add_event_nctrl_as_add_step; ins.
        all: unfold compose, is_w, is_r; rupd; ins.
        all: admit. }
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
      unfold rsrw_G_s_iff, rsrw_G_s_niff. rewrite SRFEQ.
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
      { admit. }
      rewrite <- ReordCommon.mapper_eq_a with (a := a) (b := b) at 13.
      rewrite <- FIN_LAB.
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
      all: eauto using rsrw_mapper_inj, rsrw_mapper_surj.
      admit. }
    { admit. (* Trace stuff *) }
    apply WCore.wf_iff_struct_and_props; split.
    { admit. (* STRUCT *) }
    replace ∅ with (mapper ↑₁ ∅) by now rewrite set_collect_empty.
    unfold rsrw_G_s_iff, rsrw_G_s_niff. rewrite SRFEQ.
    apply cfg_add_event_nctrl_wf_props with (X := {|
      WCore.sc := mapper ↑ sc;
      WCore.G := exec_upd_lab _ _ _;
      WCore.GC := exec_upd_lab _ _ _;
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
    { admit. }
    { admit. (* Inferrable from hyps *) }
    { admit. (* Inferrable from hyps *) }
    { admit. }
    { admit. }
    { apply cfg_upd_lab_wf_props with (X := {|
        WCore.sc := mapper ↑ sc;
        WCore.G := exec_mapped _ _ _;
        WCore.GC := exec_mapped _ _ _;
        WCore.cmt := mapper ↑₁ ∅;
      |}); ins.
      { apply SIM_ACTS. }
      { admit. }
      { admit. (* True because b is not in E_t *) }
      apply cfg_mapped_wf_props with (X := {|
        WCore.sc := sc;
        WCore.G := G_t';
        WCore.GC := G_t';
        WCore.cmt := ∅;
      |}); ins.
      all: eauto using rsrw_mapper_inj, rsrw_mapper_surj.
      { admit. }
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

Lemma simrel_exec_b
   (CONS' : WCore.is_cons G_s (mapper ↑ sc))
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' sc traces a) :
  exists G_s' sc',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    exists G_s'_int,
      << STEP1 : WCore.exec_inst G_s G_s'_int sc' traces' a >> /\
      << STEP2 : WCore.exec_inst G_s'_int G_s' sc' traces' b >>.
Proof using SWAPPED_TRACES IS_CONS.
  admit. (* TODO: research *)
Admitted.

Lemma simrel_exec_a_helper w
    (CONS : WCore.is_cons G_t sc)
    (CONS' : WCore.is_cons G_s (mapper ↑ sc))
    (RF : rf_t' w b)
    (SIM_ACTS : reord_simrel_rw_actids G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' sc traces b) :
  WCore.reexec
    (rsrw_G_s_niff G_s G_t  a b)
    (rsrw_G_s_niff G_s G_t' a b)
    (mapper ↑ sc)
    traces'.
Proof using.
  (* Shorthands *)
  assert (SRFEQ : exists sw, srf_s ⨾ ⦗eq a⦘ ≡ singl_rel sw a).
  { admit. }
  destruct SRFEQ as [sw SRFEQ].
  unfold rsrw_G_s_iff, rsrw_G_s_niff.
  apply rel_extensionality in SRFEQ. rewrite SRFEQ.
  set (G_s_ := exec_add_rf
    (exec_add_read_event_nctrl
      (exec_upd_lab
        (exec_mapped G_t mapper (lab_t' ∘ mapper))
        a (lab_s a)) a)
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
  assert (CMTEQ : WCore.f_cmt f ≡₁ cmt).
  { subst f. unfold WCore.f_cmt, is_some, compose.
    unfolder. split; ins; desf. }
  assert (CMTEQ' : forall r,
    Some ↓ (f ↑ r) ≡ restr_rel cmt r).
  { admit. (* TODO: f is a partial id *) }
  (* Actual proof *)
  red. exists f, (fun x y => y = tid a), dtrmt.
  assert (INA : E_t a).
  { admit. (* TODO: lemma condition? *) }
  assert (START_WF : WCore.wf
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G :=
        WCore.reexec_start G_s_
          (exec_mapped G_t' mapper
            (lab_t' ∘ mapper)) dtrmt;
      WCore.GC :=
        exec_mapped G_t' mapper (lab_t' ∘ mapper);
      WCore.cmt :=
        fun x : actid => WCore.f_cmt f x
    |}).
  { admit. }
  assert (END_WF : WCore.wf
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G := exec_mapped G_t' mapper (lab_t' ∘ mapper);
      WCore.GC := exec_mapped G_t' mapper (lab_t' ∘ mapper);
      WCore.cmt :=
        fun x : actid =>
        WCore.f_cmt
          (fun x0 : actid =>
          ifP ((mapper ↑₁ E_t ∪₁ eq a) \₁ eq a) x0 then
          Some x0 else None) x
    |}).
  { admit. }
  assert (END_WF' : Wf G_t').
  { admit. }
  assert (WINE' : (mapper ↑₁ E_t') w).
  { admit. }
  subst f cmt G_s'. ins.
  constructor; ins.
  { admit. (* TODO: e <> a ==> all good *) }
  { rewrite CMTEQ, set_minus_union_l.
    subst dtrmt. basic_solver 11. }
  { admit. (* TODO *) }
  { constructor; ins.
    all: admit. }
  { admit. }
  { set (ENUM := WCore.g_acts_fin_enum END_WF).
    desf.
    set (l1 := filterP delta l).
    set (l2 := filterP (set_compl (eq a ∪₁ eq b)) l1).
    apply sub_to_full_exec with (l := l2 ++ [a; b]).
    all: subst l2 l1 delta.
    { admit. }
    { admit. }
    { constructor; ins.
      { apply nodup_app; splits.
        { now do 2 apply nodup_filterP. }
        { admit. (* TODO a <> b *) }
        intros x HL1 HL2.
        apply in_filterP_iff in HL1.
        destruct HL1 as [_ HL1]. ins.
        unfolder in HL1. desf; eauto. }
      { admit. (* TODO: easy *)  }
      { intros x y HREL.
        admit. (* Not obvious, but should be true *)}
      { admit. }
      admit. } (* TODO follows from wf-ness *)
    admit. (* TODO: trace coherency *) }
  admit.
Admitted.

Lemma simrel_exec_a w
    (CONS' : WCore.is_cons G_s (mapper ↑ sc))
    (RF : rf_t' w a)
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' sc traces b) :
  exists G_s' sc',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP : WCore.reexec G_s G_s' sc' traces' >>.
Proof using SWAPPED_TRACES IS_CONS.
  (* TODO: check article *)
  (* Case1 : Gt' *)
  (* Case2: mapped Gt but with executed a *)
  admit.
Admitted.

End SimRelExec.

Section SimRelReexec.

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


Lemma simrel_exec_iff_reexecstart_helper l dtrmt
    (A_NEQ_B : a <> b) :
  exec_equiv
    (WCore.reexec_start
      (exec_upd_lab
        (exec_mapped G_t mapper
            (lab_t' ∘ mapper)) a
        l)
      (exec_upd_lab
        (exec_mapped G_t' mapper
            (lab_t' ∘ mapper)) a
        l) (mapper ↑₁ dtrmt))
    (exec_upd_lab
        (exec_mapped (WCore.reexec_start G_t G_t' dtrmt)
          mapper (lab_t' ∘ mapper)) a l).
Proof using.
  constructor; ins.
  { rewrite set_collect_interE; eauto using ReordCommon.mapper_inj. }
  all: rewrite !collect_rel_seq, <- collect_rel_eqv; ins.
  all: eapply inj_dom_mori; eauto using ReordCommon.mapper_inj; ins.
Qed.

Lemma simrel_exec_iff_reexecstart_helper_eq l dtrmt
    (A_NEQ_B : a <> b) :
  WCore.reexec_start
    (exec_upd_lab
      (exec_mapped G_t mapper
          (lab_t' ∘ mapper)) a
      l)
    (exec_upd_lab
      (exec_mapped G_t' mapper
          (lab_t' ∘ mapper)) a
       l) (mapper ↑₁ dtrmt) =
  exec_upd_lab
    (exec_mapped (WCore.reexec_start G_t G_t' dtrmt)
      mapper (lab_t' ∘ mapper)) a l.
Proof using.
  now apply exeeqv_eq, simrel_exec_iff_reexecstart_helper.
Qed.

Lemma simrel_reexec_iff_helper l sc
    (U2V : same_label_u2v (lab_t' b) l)
    (SAME : E_t a <-> E_t b)
    (CONS : WCore.is_cons G_t sc)
    (STEP : WCore.reexec G_t G_t' sc traces)
    (SIM_ACTS : reord_simrel_rw_actids G_s G_t a b)
    (NRMWDEP : ~rmw_dep_t' a b)
    (NRMW : ~rmw_t' a b)
    (NRMWCODOM : ~codom_rel rmw_t' a)
    (NRMWDOM : ~dom_rel rmw_t' b) :
  WCore.reexec
    (exec_upd_lab
      (exec_mapped G_t  mapper (lab_t'  ∘ mapper))
      a l)
    (exec_upd_lab
      (exec_mapped G_t' mapper (lab_t' ∘ mapper))
      a l)
    (mapper ↑ sc)
    traces'.
Proof using.
  red in STEP. desf. red.
  assert (A_NEQ_B : a <> b).
  { admit. }
  assert (CMTEQ : WCore.f_cmt (option_map mapper ∘ f ∘ mapper) ≡₁
                  mapper ↑₁ WCore.f_cmt f).
  { unfold WCore.f_cmt, compose, is_some, option_map.
    unfolder. split; intros x HSET.
    { desf. exists (mapper x); split; desf.
      rewrite ReordCommon.mapper_self_inv; ins. }
    desf. rewrite ReordCommon.mapper_self_inv in Heq0; ins.
    desf. }
  exists (option_map mapper ∘ f ∘ mapper),
         thrdle,
         (mapper ↑₁ dtrmt).
  constructor; ins.
  { rewrite CMTEQ. now apply set_collect_mori, STEP. }
  { admit. (* NOTE: ignore for now, until new constraint drops *)  }
  { constructor; ins.
    { rewrite CMTEQ. admit. (* looks easy *) }
    { rewrite CMTEQ. now apply set_collect_mori, STEP. }
    { admit. (* f respects this property, mapper saves tids *) }
    { admit. (* f preserves label. With mapper it preserves it too *) }
    { admit. (* Looks easy too *) }
    rewrite CMTEQ, collect_rel_restr; eauto using ReordCommon.mapper_inj.
    transitivity (mapper ↑ (Some ↓ (f ↑ restr_rel (WCore.f_cmt f) rf_t'))).
    all: try now apply collect_rel_mori, STEP.
    apply conjugate_sub.
    all: eauto using ReordCommon.mapper_inj,
                     ReordCommon.mapper_surj.
    now rewrite ReordCommon.mapper_mapper_compose. }
  { admit. (* Basic start wf-ness *) }
  { rewrite simrel_exec_iff_reexecstart_helper_eq.
    all: eauto using rsrw_a_neq_b.
    destruct (enumd_diff_seq (WCore.reexec_start_wf STEP) (WCore.reexec_steps STEP))
             as (el & DIFF); ins.
    desf.
    edestruct sub_to_full_exec_sort_part with (tord := thrdle)
                                              (l := el)
                                         as (el' & SORT & ENUM).
    all: eauto.
    { apply STEP. }
    { admit. (* TODO *) }
    { admit. (* TODO: change condition *) }
    { admit. }
    apply sub_to_full_exec with el'.
    { admit. (* Start wf *) }
    { admit. (* end wf *) }
    { constructor; ins.
      { apply ENUM. }
      { rewrite <- (SubToFullExecInternal.diff_elems ENUM).
        ins. admit. }
      { admit. }
      { admit. }
      admit. }
    admit. (* Traces *) }
  admit. (* Is_cons *)
Admitted.

Lemma simrel_reexec sc
    (CONS : WCore.is_cons G_t sc)
    (CONS' : WCore.is_cons G_s (mapper ↑ sc))
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.reexec G_t G_t' sc traces) :
  exists G_s' sc',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP : WCore.reexec G_s G_s' sc' traces' >>.
Proof using SWAPPED_TRACES.
  admit.
Admitted.

End SimRelReexec.

Section ExecutionSteps.

(* Lemma simrel_implies_cons sc
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
Admitted. *)

End ExecutionSteps.

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