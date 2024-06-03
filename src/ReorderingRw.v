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

Set Implicit Arguments.

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
  rsrw_b_tid : tid b <> tid_init;
  rsrw_a_tid : tid a <> tid_init;
  rsrw_a_max : forall (INA : E_t a) (NOTINB : ~E_t b),
                  max_elt (sb G_t) a;
  rsrw_actids_t_ord : forall (INB : E_t b) (NOTINA : ~E_t a), False;
}.

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

Lemma rsrw_struct_iff
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
    (NOTINB : ~E_t b) :
  reord_simrel_rw_struct <->
    exec_equiv G_s rsrw_G_s_niff.
Proof using RSRW_ACTIDS.
  unfold rsrw_G_s_niff, rsrw_G_s_iff.
  split; [intro STRUCT | intro EQUIV].
  { constructor; ins.
    all: try now apply STRUCT.
    now apply rsrw_struct_same_lab. }
  constructor; ins.
  all: try now apply EQUIV.
  all: try now (exfalso; apply NOTINB, SAME, INA).
  { rewrite (exeeqv_lab EQUIV); ins. do 2 red.
    intros e _.
    rewrite upd_compose, ReordCommon.mapper_mapper_compose',
            ReordCommon.mapper_eq_a.
    all: eauto using rsrw_a_neq_b, rsrw_mapper_inj.
    destruct (classic (e = b)) as [EQ|NEQ]; subst; rupd.
    all: try now apply RSRW_ACTIDS.
    red. desf. }
  { rewrite (exeeqv_lab EQUIV); ins.
    change (val (upd (lab_t ∘ mapper) a (lab_s a)) ∘ mapper)
      with (val (upd (lab_t ∘ mapper) a (lab_s a)  ∘ mapper)).
    unfold val.
    rewrite upd_compose, ReordCommon.mapper_mapper_compose',
            ReordCommon.mapper_eq_a.
    all: eauto using rsrw_a_neq_b, rsrw_mapper_inj.
    destruct (classic (e = b)) as [EQ|NEQ]; subst; rupd.
    congruence. }
  rewrite (exeeqv_acts EQUIV); ins.
  rewrite set_inter_union_l.
  arewrite (eq a ∩₁ is_init ≡₁ ∅); [| now rewrite set_union_empty_r].
  split; [| basic_solver]. intros x (EQ & INIT). subst.
  red. now apply (rsrw_ninit_a RSRW_ACTIDS).
Qed.

Lemma rsrw_G_s_iff_sb
    (SAME : E_t a <-> E_t b) :
  sb rsrw_G_s_iff ≡ sb_t.
Proof using.
  unfold sb. ins.
  now rewrite ReordCommon.mapper_acts_iff.
Qed.

Lemma rsrw_G_s_niff_sb
    (INA : E_t a)
    (NINB : ~E_t b) :
  sb rsrw_G_s_niff ≡ sb_t ∪ ⦗E_t⦘ ⨾ ext_sb ⨾ ⦗eq b⦘.
Proof using RSRW_ACTIDS.
  unfold sb. ins.
  rewrite ReordCommon.mapper_acts_niff; ins.
  split; [| basic_solver].
  unfolder. intros x y (DOM & SB & CODOM).
  desf; eauto.
  { exfalso. eapply rsrw_a_max with y; ins.
    unfold sb; unfolder. splits; ins.
    apply ext_sb_trans with b; ins.
    apply RSRW_ACTIDS. }
  exfalso. eapply ext_sb_irr; eauto.
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
  assert (WF : Wf (WCore.init_exec G_s)).
  { constructor. all : try basic_solver.
    { ins. unfold is_total. ins. admit. } 
    { ins. destruct H. destruct H. assert (EQ : x = InitEvent l).
      { destruct H. admit. } rewrite <- EQ. apply H. }
    { ins. admit. }
    ins. rewrite is_init_tid; destruct EE. admit. eauto. }
  constructor; constructor; ins.
  all: try now (rewrite collect_rel_empty; ins).
  all: try now (exfalso; apply ACTIDS.(rsrw_ninit_a G_s G_t a b), INA).
  all: try now (exfalso; apply ACTIDS.(rsrw_ninit_b G_s G_t a b), INB).
  all: try now apply ACTIDS.
  all: try now apply STRUCT.
  { unfolder. intros F. desf. }
  { arewrite (srf (WCore.init_exec G_s) ≡ ∅₂).
    { rewrite wf_srfD, wf_srfE; ins.
      split; [| basic_solver].
      unfolder. intros _ y (_ & _ & (INY & INIT) & IS_R).
      eapply read_or_fence_is_not_init; eauto. }
    basic_solver. }
  all: rewrite (rsrw_init STRUCT).
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

Hypothesis WF : Wf G_s.
Hypothesis SIMREL : reord_simrel_rw G_s G_t a b.
Hypothesis IS_CONS : WCore.is_cons G_t sc.
Hypothesis SWAPPED_TRACES : ReordCommon.traces_swapped traces traces' a b.

Lemma simrel_niff_start_wf
    (INA : E_t' a)
    (NINB : ~E_t b)
    (NINB' : ~E_t' b)
    (SIM_ACTS : reord_simrel_rw_actids G_s G_t a b)
    (WF' : WCore.wf {|
      WCore.sc := sc;
      WCore.G := G_t;
      WCore.GC := G_t';
      WCore.cmt := ∅;
    |}) :
  WCore.wf {|
    WCore.sc := mapper ↑ sc;
    WCore.G := rsrw_G_s_niff G_s G_t a b;
    WCore.GC := rsrw_G_s_niff G_s G_t' a b;
    WCore.cmt := ∅;
  |}.
Proof using.
  assert (WF_G_t' : Wf G_t').
  { apply WF'. }
  assert (FIN_LAB : lab_t' = lab_t).
  { symmetry. apply WF'. }
  split.
  { admit. }
  replace ∅ with (mapper ↑₁ ∅) by  now rewrite set_collect_empty.
  apply cfg_add_event_nctrl_wf_props with (X := {|
    WCore.sc := mapper ↑ sc;
    WCore.G := exec_upd_lab _ _ _;
    WCore.GC := exec_upd_lab _ _ _;
    WCore.cmt := mapper ↑₁ ∅
  |}); ins.
  { apply SIM_ACTS. }
  { apply SIM_ACTS. }
  { admit. } 
  { admit. }
  { now apply WF_G_t'. }
  { admit. }
  { admit. }
  { apply NINB'.
    unfolder in DOM1. unfolder in DOM2.
    destruct DOM1 as (y & y' & x' & RF & _ & MAPX).
    destruct DOM2 as (_ & x'' & _ & EQ1 & EQ2).
    subst x'' x.
    admit. }
  { rewrite FIN_LAB.
    apply SIM_ACTS. }
  { rewrite transp_seq.
    arewrite (⦗eq a⦘⁻¹ ≡ ⦗eq a⦘).
    { basic_solver. }
    apply functional_seq; eauto using wf_srff.
    basic_solver. }
  { admit.
    (* rewrite <- (rsrw_actids2 (rsrw_struct SIMREL)); ins.
    rewrite wf_srfE at 1; ins. basic_solver.  *)
  }
  { rewrite exec_upd_lab_R with (G := exec_mapped G_t' mapper (lab_t' ∘ mapper)),
            exec_upd_lab_W with (G := exec_mapped G_t' mapper (lab_t' ∘ mapper)),
            exec_mapped_R with (G := G_t') (f := mapper) (lab' := lab_t' ∘ mapper),
            exec_mapped_W with (G := G_t') (f := mapper) (lab' := lab_t' ∘ mapper).
    all: try symmetry; ins.
    all: eauto using rsrw_mapper_inj, rsrw_mapper_surj,
                     ReordCommon.mapper_mapper_compose',
                     rsrw_a_neq_b.
    all: admit. }
  { admit. }
  { admit. }
  { now rewrite (WCore.wf_cc_ctrl_empty WF'),
            collect_rel_empty. }
  { admit. }
  apply cfg_upd_lab_wf_props with (e := a) (X := {|
    WCore.sc := mapper ↑ sc;
    WCore.G := exec_mapped _ _ _;
    WCore.GC := exec_mapped _ _ _;
    WCore.cmt := mapper ↑₁ ∅;
  |}); ins.
  { apply SIM_ACTS. }
  { rewrite FIN_LAB.
    erewrite rsrw_struct_same_lab with (G_s := G_s).
    all: eauto using rsrw_struct.
    unfold compose.
    rewrite upds, ReordCommon.mapper_eq_a.
    apply same_label_u2v_comm, SIM_ACTS. }
  { admit. }
  rewrite <- FIN_LAB.
  apply cfg_mapped_wf_props with (X := {|
    WCore.sc := sc;
    WCore.G := G_t;
    WCore.GC := G_t';
    WCore.cmt := ∅;
  |}); ins.
  all: try now apply WF'.
  all: eauto using rsrw_mapper_inj, rsrw_mapper_surj.
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
  { admit. }
  admit.
Admitted.

Lemma simrel_niff_end_wf
    (INA : E_t' a)
    (NINB' : ~E_t' b)
    (SIM_ACTS : reord_simrel_rw_actids G_s G_t a b)
    (WF' : WCore.wf {|
      WCore.sc := sc;
      WCore.G := G_t';
      WCore.GC := G_t';
      WCore.cmt := ∅;
    |}) :
  WCore.wf {|
    WCore.sc := mapper ↑ sc;
    WCore.G := rsrw_G_s_niff G_s G_t' a b;
    WCore.GC := rsrw_G_s_niff G_s G_t' a b;
    WCore.cmt := ∅;
  |}.
Proof using.
  admit.
Admitted.

Lemma target_labels e
    (STEP : WCore.exec_inst G_t G_t' sc traces e) : 
    lab_t' = lab_t.
Proof using.
  symmetry. eapply sub_lab.
  eapply WCore.wf_g_sub_gc
  with (X := {|
    WCore.G := G_t;
    WCore.GC := G_t';
    WCore.sc := sc;
    WCore.cmt := ∅;
  |}).
  apply STEP. 
Qed.

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
    { rewrite target_labels with (e := e). eauto using rsrw_lab_a_eq_lab_b. apply STEP. }
    all: intro F; subst.
    all: apply (wf_rfE WF_G_t') in HREL.
    all: unfolder in HREL; desf; eauto.
    all: enough (NBIN' : ~E_t' b); eauto.
    all: intro F; apply (WCore.cae_e_new (WCore.add_event STEP)) in F.
    all: ins; unfolder in F; desf. }
  assert (U2V : same_label_u2v ((lab_t' ∘ mapper) a) (lab_s a)).
  { rewrite target_labels with (e := e). unfold compose.
    rewrite ReordCommon.mapper_eq_a.
    apply same_label_u2v_comm, SIM_ACTS. apply STEP. }
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
    rewrite <- target_labels with (e := e).
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
  { assert ( STEP' : WCore.exec_inst G_t G_t' sc traces e ); eauto.
    destruct STEP. red in add_event. desf.
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
        rewrite <- target_labels with (e := e).
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
    (STEP : WCore.exec_inst G_t G_t' sc traces e)
    (SIM_ACTS : reord_simrel_rw_actids G_s G_t a b)
    (INA :   E_t a)
    (NINB : ~E_t b) :
  WCore.exec_inst
    (rsrw_G_s_niff G_s G_t  a b)
    (rsrw_G_s_niff G_s G_t' a b)
    (mapper ↑ sc)
    traces'
    e.
Proof using IS_CONS WF SIMREL.
  assert (INA' : E_t' a).
  { apply (WCore.cae_e_new (WCore.add_event STEP)).
    ins. now left. }
  assert (NINB' : ~E_t' b).
  { intro F'.
    apply (WCore.cae_e_new (WCore.add_event STEP)) in F'.
    ins.  destruct F' as [HIN|HEQ]; ins. }
  assert (WF' : WCore.wf {|
    WCore.sc := sc;
    WCore.G := G_t;
    WCore.GC := G_t';
    WCore.cmt := ∅;
  |}).
  { apply STEP. }
  assert (WF_G_t' : Wf G_t').
  { apply WF'. }
  (* Actual proof *)
  constructor; ins.
  { now apply simrel_niff_start_wf. }
  { replace ∅ with (mapper ↑₁ ∅) by now rewrite set_collect_empty.
    replace e with (mapper e) by now rewrite ReordCommon.mapper_neq.
    assert ( STEP' : WCore.exec_inst G_t G_t' sc traces e ); eauto.
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
      rewrite <- target_labels with (e := e).
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
    replace (mapper ↑₁ ∅) with (∅ : actid -> Prop).
    { apply simrel_niff_end_wf; ins. }
    now rewrite set_collect_empty. }
  admit. (* TODO: is cons *)
Admitted.

Lemma simrel_exec_not_a_not_b e
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (STEP : WCore.exec_inst G_t G_t' sc traces e) :
  exists G_s' sc',
    << SIM : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP : WCore.exec_inst G_s G_s' sc' traces' e >>.
Proof using IS_CONS SIMREL WF SWAPPED_TRACES.
  destruct (classic (E_t a)) as [INA|NINA];
  destruct (classic (E_t b)) as [INB|NINB].
  { exists (rsrw_G_s_iff G_s G_t' a b), (mapper ↑ sc).
    split; red.
    { assert (INA' : E_t' a).
      { apply (WCore.cae_e_new (WCore.add_event STEP)).
        ins. now left. }
      assert (INB' : E_t' b).
      { apply (WCore.cae_e_new (WCore.add_event STEP)).
        ins. basic_solver. }
      constructor. 
      { constructor; destruct SIMREL; destruct rsrw_actids0; eauto; ins.   
        { admit. }
        { admit. }
        { rewrite target_labels with (e := e); eauto. }
        { admit. }
        { ins. rewrite target_labels with (e := e). 2: apply STEP. 
          destruct rsrw_struct0. admit. }
        { admit. }
        admit. }
        constructor; destruct SIMREL; destruct rsrw_actids0; eauto; ins.
        { admit. }
        { admit. }
        admit. } 
    replace G_s with (rsrw_G_s_iff G_s G_t a b) at 1.
    { apply simrel_exec_iff; ins.
      apply SIMREL. }
    symmetry.
    apply exeeqv_eq, rsrw_struct_iff; ins.
    all: apply SIMREL. }
  { exists (rsrw_G_s_niff G_s G_t' a b), (mapper ↑ sc).
    split; red.
    { admit. }
    replace G_s with (rsrw_G_s_niff G_s G_t a b) at 1.
    { apply simrel_exec_niff; ins.
      apply SIMREL. }
    symmetry.
    apply exeeqv_eq, rsrw_struct_niff; ins.
    all: apply SIMREL. }
  { exfalso. now apply (rsrw_actids_t_ord (rsrw_actids SIMREL)). }
  exists (rsrw_G_s_iff G_s G_t' a b), (mapper ↑ sc).
  split; red.
  { admit. }
  replace G_s with (rsrw_G_s_iff G_s G_t a b) at 1.
  { apply simrel_exec_iff; ins.
    apply SIMREL. }
  symmetry.
  apply exeeqv_eq, rsrw_struct_iff; ins.
  all: apply SIMREL.
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
Proof using IS_CONS WF SIMREL.
  assert (NINB' : ~E_t' b).
  { intro F'.
    apply (WCore.cae_e_new (WCore.add_event STEP)) in F'.
    ins.  destruct F' as [HIN|HEQ]; ins.
    eapply rsrw_a_neq_b; eauto. }
  assert (WF' : WCore.wf {|
    WCore.sc := sc;
    WCore.G := G_t;
    WCore.GC := G_t';
    WCore.cmt := ∅;
  |}).
  { apply STEP. }
  assert (WF_G_t' : Wf G_t').
  { apply WF'. }
  assert (SRFEQ : exists sw, srf_s ⨾ ⦗eq a⦘ ≡ singl_rel sw a).
  { admit. }
  destruct SRFEQ as [sw SRFEQ].
  apply rel_extensionality in SRFEQ.
  split.
  { constructor; ins.
    { admit. (* Start wf -- a bit complex *) }
    { red. eexists _, _, _, _.
      splits.
      { admit. (* TODO: struct *) }
      { unfold rsrw_G_s_iff, rsrw_G_s_niff.
        rewrite SRFEQ.
        apply cfg_add_event_nctrl_as_add_step; ins.
        all: unfold compose, is_w, is_r; rupd; ins.
        all: admit. }
      { admit. (* traces *) }
      admit. }
    admit. (* IS_cons *) }
  constructor; ins.
  { apply simrel_niff_start_wf; ins.
    apply (WCore.cae_e_new (WCore.add_event STEP)).
    ins. now right. }
  { assert ( STEP' : WCore.exec_inst G_t G_t' sc traces a ); eauto.
    destruct STEP. red in add_event. desf.
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
        |}); ins.
      { admit. }
      rewrite <- ReordCommon.mapper_eq_a with (a := a) (b := b) at 13.
      rewrite <- target_labels with (e := a).
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
    { admit. (* Trace stuff *) }
    apply simrel_niff_end_wf; ins.
    apply (WCore.caes_e_new STRUCT).
    ins. now right. (* TODO: turn into assert *) }
  admit. (* IS_cons *)
Admitted.

Lemma simrel_exec_b
    (CONS' : WCore.is_cons G_s (mapper ↑ sc))
    (STEP : WCore.exec_inst G_t G_t' sc traces a) :
  exists G_s' sc',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    exists G_s'_int,
      << STEP1 : WCore.exec_inst G_s G_s'_int sc' traces' a >> /\
      << STEP2 : WCore.exec_inst G_s'_int G_s' sc' traces' b >>.
Proof using SWAPPED_TRACES IS_CONS SIMREL.
  destruct (classic (E_t a)) as [INA|NINA].
  { exfalso.
    now apply (WCore.cae_e_notin (WCore.add_event STEP)). }
  destruct (classic (E_t b)) as [INB|NINB].
  { exfalso. eapply rsrw_actids_t_ord; eauto.
    apply SIMREL. }
  exists (rsrw_G_s_niff G_s G_t' a b), (mapper ↑ sc).
  split.
  { admit. }
  exists (rsrw_G_s_niff G_s G_t a b).
  split; red.
  { replace G_s with (rsrw_G_s_iff G_s G_t a b) at 1.
    { apply simrel_exec_b_helper; ins.
      apply SIMREL. }
    symmetry.
    apply exeeqv_eq, rsrw_struct_iff; ins.
    all: apply SIMREL. }
  apply simrel_exec_b_helper; ins.
  apply SIMREL.
Admitted.

Lemma simrel_exec_a_helper w
    (INA : E_t a)
    (NINB : ~E_t b)
    (RF : rf_t' w b)
    (SIM_ACTS : reord_simrel_rw_actids G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' sc traces b) :
  exists dtrmt,
    WCore.reexec
      (rsrw_G_s_niff G_s G_t  a b)
      (rsrw_G_s_iff  G_s G_t' a b)
      (mapper ↑ sc)
      traces'
      dtrmt.
Proof using.
  (* Defs *)
  set (dtrmt := mapper ↑₁ E_t \₁ codom_rel (
    ⦗eq a⦘ ⨾ (
      sb (rsrw_G_s_niff G_s G_t a b) ∪
      rf (rsrw_G_s_niff G_s G_t a b)
    )＊
  )).
  set (delta := acts_set (rsrw_G_s_iff  G_s G_t' a b) \₁ dtrmt).
  set (cmt := acts_set (rsrw_G_s_niff G_s G_t a b) \₁ eq a).
  set (f := fun x => ifP cmt x then Some x else None).
  (* Assers *)
  assert (WF' : WCore.wf {|
    WCore.G := G_t;
    WCore.GC := G_t';
    WCore.sc := sc;
    WCore.cmt := ∅;
  |}).
  { apply STEP. }
  assert (WF_G_t' : Wf G_t').
  { apply WF'. }
  assert (INA' : E_t' a).
  { apply (WCore.cae_e_new (WCore.add_event STEP)).
    ins. now left. }
  assert (INB' : E_t' b).
  { apply (WCore.cae_e_new (WCore.add_event STEP)).
    ins. now right. }
  assert (CMTEQ : WCore.f_cmt f ≡₁ cmt).
  { subst f. unfold WCore.f_cmt, is_some, compose.
    unfolder. split; ins; desf. }
  assert (CMTEQ' : forall r,
    Some ↓ (f ↑ r) ≡ restr_rel cmt r).
  { admit. (* TODO: f is a partial id *) }
  (* Actual proof *)
  exists dtrmt.
  red. exists f, (fun x y => y = tid a).
  subst f cmt. constructor; ins.
  { rewrite target_labels with (e := b); eauto. }
  { rewrite CMTEQ, set_minus_union_l.
    subst dtrmt. basic_solver 11. }
  { admit. (* TODO *) }
  { constructor; ins.
    { rewrite CMTEQ. unfold inj_dom. ins. desf. }
    { rewrite CMTEQ. unfold set_union. unfold set_minus. admit. }
    { admit. }
    { rewrite target_labels with (e := b). desf. apply STEP. }
    all: admit. }
  { admit. (* start wf *) }
  { set (G_t_fin := WCore.wf_gc_fin_exec WF'); ins.
    apply set_finiteE in G_t_fin.
    destruct G_t_fin as (l & NODUP & LEQ). (* TODO: sort l *)
    set (l1 := filterP delta l).
    set (l2 := filterP (set_compl (eq a ∪₁ eq b)) l1).
    apply sub_to_full_exec with (l := l2 ++ [a; b]).
    all: subst l2 l1 delta.
    { admit. (* start wf *) }
    { constructor; ins.
      { apply nodup_app; splits.
        { now do 2 apply nodup_filterP. }
        { constructor; ins.
          apply and_not_or; split.
          all: try symmetry.
          all: eauto using rsrw_a_neq_b. }
        red. intros x IN1 IN2.
        apply in_filterP_iff in IN1; desf.
        unfolder in IN0. ins. desf; eauto. }
      { admit. (* TODO: easy *)  }
      { admit. }
      { admit. }
      admit. } (* TODO follows from wf-ness *)
    admit. (* TODO: trace coherency *) }
  admit.
Admitted.

Lemma simrel_exec_a_a_in_E
    (SIM : reord_simrel_rw G_s G_t a b) :
  E_t a.
Proof using.
  admit.
Admitted.

Lemma simrel_exec_a w
    (RF : rf_t' w b)
    (STEP : WCore.exec_inst G_t G_t' sc traces b) :
  exists G_s' sc',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP : exists dtrmt, WCore.reexec G_s G_s' sc' traces' dtrmt >>.
Proof using SWAPPED_TRACES IS_CONS SIMREL.
  destruct (classic (E_t b)) as [INB | NINB].
  { exfalso. apply (WCore.cae_e_notin (WCore.add_event STEP)).
    ins. }
  assert (INA : E_t a).
  { now apply simrel_exec_a_a_in_E. }
  exists (rsrw_G_s_iff G_s G_t' a b), (mapper ↑ sc).
  split; red.
  { admit. }
  edestruct simrel_exec_a_helper as (dtrmt & REEXEC); eauto.
  { apply SIMREL. }
  exists dtrmt.
  replace G_s with (rsrw_G_s_niff G_s G_t a b) at 1.
  { apply REEXEC. }
  symmetry. apply exeeqv_eq, rsrw_struct_niff.
  all: ins.
  all: apply SIMREL.
Admitted.

End SimRelExec.

Section SimRelReexec.

Variable G_t G_t' G_s : execution.
Variable sc : relation actid.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable dtrmt : actid -> Prop.
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
Hypothesis REEXEC : WCore.reexec G_t G_t' sc traces dtrmt.

Lemma simrel_reexec_rf thrdle f l
    (THRDLE : rf_t' ⨾ ⦗E_t' \₁ WCore.f_cmt f⦘ ⊆ tid ↓ thrdle)
    (LISTORD : restr_rel (fun x => In x l) (tid ↓ (thrdle \ ⦗⊤₁⦘) ∪ sb_t')
      ⊆ total_order_from_list l)
    (WF : Wf G_t')
    (DIFF : SubToFullExecInternal.enumd_diff
      (WCore.reexec_start G_t G_t' dtrmt) G_t'
      (fun x : actid => WCore.f_cmt f x) l)
    (SIM_ACTS : reord_simrel_rw_actids G_s G_t a b) :
  restr_rel
    (mapper ↑₁ E_t' \₁ mapper ↑₁ dtrmt ∩₁ mapper ↑₁ E_t)
    (mapper ↑ rf_t'
     ⨾ ⦗mapper ↑₁ E_t' \₁
        mapper ↑₁ (fun x : actid => WCore.f_cmt f x)⦘)
   ⊆ total_order_from_list l.
Proof using.
  rewrite <- set_collect_interE, <- !set_collect_diff,
          <- collect_rel_eqv, <- collect_rel_seq,
          collect_rel_restr.
  all: eauto using rsrw_mapper_inj.
  all: try now (eapply inj_dom_mori; eauto using rsrw_mapper_inj).
  intros x' y' (x & y & HREL & XEQ & YEQ). subst.
  destruct (classic (x = a)) as [XEQA|NXQA],
           (classic (x = b)) as [XEQB|NXQB],
           (classic (y = a)) as [YEQA|YXQA],
           (classic (y = b)) as [YEQB|YXQB].
  all: try subst x; try subst y.
  all: try now (exfalso; eapply rsrw_a_neq_b; eauto).
  all: rewrite ?ReordCommon.mapper_eq_a, ?ReordCommon.mapper_eq_b.
  all: rewrite ?ReordCommon.mapper_neq; ins.
  { exfalso. eapply rf_irr; eauto.
    unfolder in HREL. apply HREL. }
  { admit. (* Unsolveable *) }
  { admit. }
  all: admit.
Admitted.

Lemma simrel_reexec_iff_to_iff_d_iff
    (IFFD : (dtrmt ∩₁ E_t) a <-> (dtrmt ∩₁ E_t) b)
    (IFF' : E_t' a <-> E_t' b)
    (SIM_ACTS : reord_simrel_rw_actids G_s G_t a b) :
  WCore.reexec
    (rsrw_G_s_iff G_s G_t  a b)
    (rsrw_G_s_iff G_s G_t' a b)
    (mapper ↑ sc)
    traces'
    (mapper ↑₁ dtrmt).
Proof using REEXEC.
  red in REEXEC.
  destruct REEXEC as (f & thrdle & GREEXEC).
  assert (WF' : WCore.wf {|
    WCore.G := WCore.reexec_start G_t G_t' dtrmt;
    WCore.GC := G_t';
    WCore.sc := sc;
    WCore.cmt := WCore.f_cmt f;
  |}).
  { apply GREEXEC. }
  assert (WF_G_t' : Wf G_t').
  { apply WF'. }
  assert (CMTEQ : WCore.f_cmt (option_map mapper ∘ f ∘ mapper) ≡₁
                  mapper ↑₁ WCore.f_cmt f).
  { admit. }
  (* The proof *)
  exists (option_map mapper ∘ f ∘ mapper),
         thrdle.
  constructor; ins.
  { destruct (classic (e = a)) as [EQA|NEQA]; subst.
    all: rupd; ins.
    unfolder in DTRMT.
    destruct DTRMT as (e' & DTRMT & EQ).
    subst e. unfold compose.
    rewrite ReordCommon.mapper_self_inv; ins.
    { now apply GREEXEC. }
    eauto using rsrw_a_neq_b. }
  { rewrite CMTEQ. apply set_collect_mori; ins.
    apply GREEXEC. }
  { constructor; ins.
    all: try now apply GREEXEC.
    rewrite CMTEQ.
    admit. (* TODO: should be easy *) }
  { admit. (* TODO: should be easy *) }
  { admit. (* TODO: hard *) }
  { destruct (enumd_diff_seq
      WF'
      (WCore.reexec_steps GREEXEC)
    ) as (l & ENUM); ins.
    destruct (
      @sub_to_full_exec_sort_part _ _ _ _ l (thrdle \ ⦗⊤₁⦘)
      WF'
    ) as (ls & INCL & ENUM'); eauto.
    { apply partial_order_to_strict, GREEXEC. }
    { unfolder. intros x (THRDLE & RESTR).
      apply not_and_or in RESTR; desf.
      apply GREEXEC in THRDLE.
      congruence. }
    { arewrite ((tid ↓ (thrdle \ ⦗⊤₁⦘)^?) ≡ tid ↓ thrdle).
      { apply map_rel_more; ins.
        apply partial_order_to_strict_inv, GREEXEC. }
      transitivity (rf_t' ⨾ ⦗E_t' \₁ WCore.f_cmt f⦘).
      { basic_solver. }
      apply GREEXEC. }
    apply sub_to_full_exec with (l := ls).
    { admit. (* reexec wf start again *) }
    { constructor; ins.
      { apply ENUM'. }
      { rewrite <- set_collect_interE.
        all: eauto using rsrw_mapper_inj.
        rewrite !ReordCommon.mapper_acts_iff; ins.
        apply ENUM'. }
      { rewrite <- set_collect_interE.
        all: eauto using rsrw_mapper_inj.
        rewrite !ReordCommon.mapper_acts_iff,
                rsrw_G_s_iff_sb; ins.
        apply ENUM'. }
      { admit. }
      admit. }
    admit. }
  admit.
Admitted.

(*
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
Admitted. *)

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