Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import ThreadTrace.
Require Import Core.
Require Import TraceSwap.
Require Import SubToFullExec.
Require Import ReorderingCommon.

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

Record reord_simrel_rw_actids : Prop := {
  rsrw_ninit_a : ~is_init a;
  rsrw_ninit_b : ~is_init b;
  rsrw_a_is_w : is_w lab_t a;
  rsrw_b_is_r : is_r lab_t b;
  rsrw_a_b_ord : ext_sb a b;
}.

Record reord_simrel_rw_core G : Prop :=
{ rsrw_actids_t_ord : forall (INB : E_t b) (NOTINA : ~E_t a), False;
  rsrw_lab_val_end : forall (INA : E_t a) (INB : E_t b),
                       val (lab G) a = val_t b; }.

Record reord_simrel_rw_struct : Prop := {
  rsrw_lab_u2v : same_lab_u2v lab_s (lab_t ∘ mapper);
  rsrw_lab_val : forall e (NOTA : e <> a),
                       val_s e = (val_t ∘ mapper) e;
  rsrw_threads : threads_set G_s ≡₁ threads_set G_t;
  rsrw_rmw : rmw_s ≡ mapper ↑ rmw_t;
  rsrw_sb1 : forall (SAME : E_t a <-> E_t b), immediate sb_s ≡ immediate sb_t;
  rsrw_sb2 : forall (INA : E_t a) (NOTINB : ~E_t b),
                immediate sb_s ≡ immediate sb_t ∪ singl_rel a b;
  rsrw_init : E_s ∩₁ is_init ≡₁ E_t ∩₁ is_init;
  rsrw_actids1 : forall (SAME : E_t a <-> E_t b), E_s ≡₁ E_t;
  rsrw_actids2 : forall (INA : E_t a) (NOTINB : ~E_t b),
                 E_s ≡₁ E_t ∪₁ eq b;
  rsrw_rf1 : forall (SAME : E_t a <-> E_t b), rf_s ≡ mapper ↑ rf_t;
  rsrw_rf2 : forall (INA : E_t a) (NOTINB : ~ E_t b),
                    rf_s ≡ mapper ↑ rf_t ∪ mapper ↑ (srf_t ⨾ ⦗eq b⦘);
  rsrw_data : data_s ≡ mapper ↑ data_t;
  rsrw_addr : addr_s ≡ mapper ↑ addr_t;
  rsrw_ctrl : ctrl_s ≡ mapper ↑ ctrl_t;
  rsrw_rmwdep : rmw_dep_s ≡ mapper ↑ rmw_dep_t;
  rsrw_co : co_s ≡ mapper ↑ co_t;

  rsrw_a_max : forall (INA : E_t a) (NOTINB : ~E_t b), max_elt (sb G_t) a;
}.

Record reord_simrel_rw : Prop :=
{ rsrw_actids : reord_simrel_rw_actids;
  rsrw_core : reord_simrel_rw_core G_s;
  rsrw_struct : reord_simrel_rw_struct; }.

Hypothesis RSRW_ACTIDS : reord_simrel_rw_actids.

Lemma rsrw_struct_same
    (U2V  : same_label_u2v (lab_s a) ((lab_t ∘ mapper) a))
    (SAME : E_t a <-> E_t b) :
  reord_simrel_rw_struct <->
    exec_equiv G_s (ReordCommon.mapped_G_t G_t a b (lab_s a)).
Proof using.
  split; [intro STRUCT | intro EQUIV].
  { constructor; ins.
    all: try now apply STRUCT.
    apply functional_extensionality. intro x.
    tertium_non_datur (x = a) as [HEQ|HEQ]; subst; rupd; ins.
    apply same_label_u2v_val; apply STRUCT; ins. }
  constructor; ins.
  all: try now (exfalso; apply NOTINB, SAME, INA).
  all: try now apply EQUIV.
  { rewrite EQUIV.(exeeqv_lab).
    unfold same_lab_u2v, same_lab_u2v_dom. ins.
    tertium_non_datur (e = a) as [HEQ | HEQ]; subst; rupd; ins.
    unfold same_label_u2v; desf. }
  { rewrite EQUIV.(exeeqv_lab). unfold val; ins.
    rupd. }
  { symmetry. apply immediate_more.
    rewrite <- ReordCommon.mapped_G_t_sb.
    unfold sb. now rewrite EQUIV.(exeeqv_acts). }
  now rewrite EQUIV.(exeeqv_acts).
Qed.

Lemma rsrw_struct_niff
    (U2V  : same_label_u2v (lab_s a) ((lab_t ∘ mapper) a))
    (INA : E_t a)
    (NOTINB : ~E_t b)
    (A_MAX : max_elt (sb G_t) a) :
  reord_simrel_rw_struct <->
    exec_equiv G_s (ReordCommon.mapped_G_t_with_b_srf G_t a b (lab_s a)).
Proof using RSRW_ACTIDS.
  split; [intro STRUCT | intro EQUIV].
  { constructor; ins.
    all: try now apply STRUCT.
    apply functional_extensionality. intro x.
    tertium_non_datur (x = a) as [HEQ|HEQ]; subst; rupd; ins.
    apply same_label_u2v_val; apply STRUCT; ins. }
  constructor; ins.
  all: try now (exfalso; apply NOTINB, SAME, INA).
  all: try now apply EQUIV.
  { rewrite EQUIV.(exeeqv_lab).
    unfold same_lab_u2v, same_lab_u2v_dom. ins.
    tertium_non_datur (e = a) as [HEQ | HEQ]; subst; rupd; ins.
    unfold same_label_u2v; desf. }
  { rewrite EQUIV.(exeeqv_lab). unfold val; ins.
    rupd. }
  { rewrite <- ReordCommon.mapped_G_t_imm_sb; ins.
    all: try apply RSRW_ACTIDS.
    unfold sb. now rewrite EQUIV.(exeeqv_acts). }
  rewrite EQUIV.(exeeqv_acts). ins.
  split; [| basic_solver]. rewrite set_inter_union_l.
  intros x HIN. unfolder in HIN; desf.
  exfalso; now apply RSRW_ACTIDS.(rsrw_ninit_b).
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
  { apply immediate_more. unfold sb; ins.
    repeat apply seq_more; ins.
    all: apply eqv_rel_more, STRUCT. }
  rewrite !set_interA, set_interK.
  apply STRUCT.
Qed.

End Basic.

Section ExecutionSteps.

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
Notation "'srf_t'" := (srf G_t).
Notation "'W_t'" := (is_w lab_t).
Notation "'R_t'" := (is_r lab_t).

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

Record reord_context : Prop := {
  rctx_aninit : ~is_init a;
  rctx_bninit : ~is_init b;
  rctx_diff : a <> b;
  rctx_sb : ext_sb a b;
  rctx_is_w : W_t a;
  rctx_is_r : R_t b;
  rctx_amax : forall (INA : E_t a) (NOTINB : ~E_t b), max_elt (sb G_t) a;
}.

Hypothesis SWAPPED_TRACES : ReordCommon.traces_swapped traces traces' a b.
Hypothesis CTX : reord_context.

Lemma simrel_exec_mapper_iff1 e
    (SAME : E_t a <-> E_t b)
    (INA : E_t a)
    (INB : E_t b)
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons G_t)
    (STEP : WCore.exec_inst G_t G_t' traces e)
    (SIM_ACTS : reord_simrel_rw_actids G_t a b) :
  WCore.exec_inst
    (ReordCommon.mapped_G_t G_t a b (lab_t b))
    (ReordCommon.mapped_G_t G_t' a b (lab_t b))
    traces
    e.
Proof using.
  assert (NEQ : a <> b).
  { intro F; eapply ext_sb_irr with (x := a).
    rewrite F at 2. apply SIM_ACTS. }
  assert (EQ_LAB : upd (lab_t ∘ mapper) a (lab_t b) = lab_t ∘ mapper).
  { arewrite (lab_t b = (lab_t ∘ mapper) a); [| now rewrite updI].
    unfold compose. now rewrite ReordCommon.mapper_eq_a. }
  assert (FIN_LAB : lab G_t' = lab_t).
  { symmetry. destruct STEP, start_wf; ins. apply pfx. }
  constructor; ins.
  { admit. (* Conf wf *) }
  { destruct STEP. unfold WCore.cfg_add_event in add_event.
    desf. exists (option_map mapper r), (option_map mapper w),
                 (mapper ↑₁ W1), (mapper ↑₁ W2).
    constructor; ins.
    all: try now apply add_event.
    { admit. } (* TODO: research *)
    { rewrite add_event.(WCore.rf_new); ins.
      rewrite !collect_rel_union.
      repeat apply union_more; ins; unfold WCore.rf_delta_R, WCore.rf_delta_W;
        [| desf; basic_solver 12].
      destruct w as [w |]; ins; [| apply collect_rel_empty].
      rewrite ReordCommon.mapper_rel_inter, collect_rel_cross,
              collect_rel_singl, ReordCommon.mapper_neq with (x := e).
      all: ins.
      apply inter_rel_more; ins. rewrite FIN_LAB, EQ_LAB.
      rewrite ReordCommon.mapper_R_t, ReordCommon.mapper_W_t; ins.
      now rewrite ReordCommon.mapper_lab_same. }
      { rewrite add_event.(WCore.co_new); ins.
        rewrite !collect_rel_union. repeat apply union_more; ins.
        unfold WCore.co_delta; ins. unfold is_w, compose.
        rewrite updo, ReordCommon.mapper_neq; ins. desf.
        all: try apply collect_rel_empty.
        rewrite !collect_rel_union, !collect_rel_cross,
                set_collect_eq, ReordCommon.mapper_neq; ins. }
      { rewrite add_event.(WCore.rmw_new); ins.
        destruct start_wf, pfx; ins.
        rewrite !collect_rel_union. repeat apply union_more; ins.
        unfold WCore.rmw_delta; ins. rewrite <- pfx_sub.(sub_lab).
        rewrite <- ReordCommon.mapper_W_t, <- ReordCommon.mapper_R_t; ins.
        rewrite collect_rel_cross, !ReordCommon.mapper_inter_set; ins.
        rewrite set_collect_eq_opt, set_collect_eq,
                ReordCommon.mapper_neq; ins. }
      admit. (* Conf wf *) }
  admit. (* TODO: research *)
Admitted.

Lemma simrel_exec_mapper_iff2 e
    (SAME : E_t a <-> E_t b)
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons G_t)
    (STEP : WCore.exec_inst G_t G_t' traces e)
    (SIM_ACTS : reord_simrel_rw_actids G_t a b)
    (SIM_CORE : reord_simrel_core G_t a b) :
  WCore.exec_inst
    (ReordCommon.mapped_G_t G_t a b)
    (ReordCommon.mapped_G_t G_t' a b)
    traces
    e.

Lemma simrel_exec_mapper_iff e
    (SAME : E_t a <-> E_t b)
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons G_t)
    (STEP : WCore.exec_inst G_t G_t' traces e)
    (SIM_ACTS : reord_simrel_rw_actids G_t a b)
    (SIM_CORE : reord_simrel_core G_t a b) :
  WCore.exec_inst
    (ReordCommon.mapped_G_t G_t a b)
    (ReordCommon.mapped_G_t G_t' a b)
    traces
    e.

Lemma simrel_exec_not_a_not_b_same_helper e
    (SAME : E_t a <-> E_t b)
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons G_t)
    (CONS' : WCore.is_cons G_s)
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' traces e) :
  exists G_s',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP' : WCore.exec_inst G_s G_s' traces' e >>.
Proof using SWAPPED_TRACES CTX.
  (* assert (IFF : acts_set G_t' a <-> acts_set G_t' b).
  { destruct STEP. unfold WCore.cfg_add_event in add_event.
    desf. destruct add_event. ins.
    split; intro HIN; apply e_new in HIN; apply e_new; left.
    all: unfolder in HIN; desf; eauto. }
  exists (ReordCommon.mapped_G_t G_t' a b).
  split.
  { apply mapper_simrel_iff; ins; apply CTX. }
  constructor; ins.
  { admit. } (* TODO: make G_s into mapped G? *)
  { destruct STEP. unfold WCore.cfg_add_event in add_event.
    desf. unfolder.
    exists (option_map mapper r), (option_map mapper w),
           (mapper ↑₁ W1), (mapper ↑₁ W2).
    constructor; ins.
    { intro HIN. apply SIM.(rsrw_actids1 G_s G_t a b) in HIN; ins.
      apply add_event.(WCore.e_notin); ins. }
    { apply add_event. }
    { rewrite add_event.(WCore.e_new); ins.
      apply set_union_more; ins. symmetry.
      apply SIM.(rsrw_actids1 G_s G_t a b); ins. }
    { admit. } (* TODO: abuse trace swap *)
    { rewrite add_event.(WCore.rf_new); ins.
      rewrite !collect_rel_union. repeat apply union_more.
      { symmetry; apply SIM.(rsrw_rf1 G_s G_t a b); ins. }
      { unfold ReordCommon.mapped_G_t, WCore.rf_delta_R; ins.
        desf; [| now rewrite collect_rel_empty].
        tertium_non_datur (a0 = a) as [HEQ|HEQ].
        { ins; rewrite HEQ, ReordCommon.mapper_eq_a in Heq. desf.
          split; unfolder; ins; desf.
          { splits; rewrite ?ReordCommon.mapper_eq_a, ?ReordCommon.mapper_neq.
            all: ins.
            all: unfold compose, is_w, is_r.
            all: rewrite ?ReordCommon.mapper_eq_b, ?ReordCommon.mapper_neq.
            all: ins. }
          unfold compose, is_w, is_r in H0, H1.
          rewrite ReordCommon.mapper_eq_b in H0.
          rewrite ReordCommon.mapper_neq in H1; ins.
          exists a, e; splits; ins.
          all: rewrite ?ReordCommon.mapper_eq_a, ?ReordCommon.mapper_neq; ins. }
        tertium_non_datur (a0 = b) as [HEQ1|HEQ1].
        { ins; rewrite HEQ1, ReordCommon.mapper_eq_b in Heq. desf.
          split; unfolder; ins; desf.
          { splits; rewrite ?ReordCommon.mapper_eq_b, ?ReordCommon.mapper_neq.
            all: ins.
            all: unfold compose, is_w, is_r.
            all: rewrite ?ReordCommon.mapper_eq_a, ?ReordCommon.mapper_neq.
            all: ins. }
          unfold compose, is_w, is_r in H0, H1.
          rewrite ReordCommon.mapper_eq_a in H0.
          rewrite ReordCommon.mapper_neq in H1; ins.
          exists b, e; splits; ins.
          all: rewrite ?ReordCommon.mapper_eq_b, ?ReordCommon.mapper_neq; ins. }
        ins; rewrite ReordCommon.mapper_neq in Heq; ins. desf.
        split; unfolder; ins; desf.
        { splits; rewrite ?ReordCommon.mapper_neq; ins.
          all: unfold compose, is_w, is_r.
          all: rewrite ?ReordCommon.mapper_neq; ins. }
        unfold compose, is_w, is_r in H0, H1.
        rewrite ReordCommon.mapper_neq in H0; ins.
        rewrite ReordCommon.mapper_neq in H1; ins.
        exists a1, e; splits; ins.
        all: rewrite ?ReordCommon.mapper_neq; ins. }
      unfold WCore.rf_delta_W, ReordCommon.mapped_G_t; ins.
      unfold compose, is_w. rewrite ReordCommon.mapper_neq; ins.
      desf; try now apply collect_rel_empty.
      rewrite !set_inter_empty_l. basic_solver. }
    { rewrite add_event.(WCore.co_new); ins.
      unfold WCore.co_delta, ReordCommon.mapped_G_t; ins.
      unfold compose, is_w. rewrite ReordCommon.mapper_neq; ins.
      desf; try now (rewrite !union_false_r; symmetry; apply SIM).
      rewrite !collect_rel_union. repeat apply union_more.
      { symmetry; apply SIM. }
      { rewrite collect_rel_cross. apply cross_more; ins.
        rewrite set_collect_eq, ReordCommon.mapper_neq; ins. }
      rewrite collect_rel_cross. apply cross_more; ins.
      rewrite set_collect_eq, ReordCommon.mapper_neq; ins. }
    { rewrite add_event.(WCore.rmw_new); ins.
      unfold WCore.rmw_delta, ReordCommon.mapped_G_t; ins.
      rewrite !collect_rel_union. repeat apply union_more.
      { symmetry; apply SIM. }
      rewrite collect_rel_cross. apply cross_more.
      { destruct r; unfolder; ins; [| split; ins; desf].
        unfold compose.
        tertium_non_datur (a0 = a) as [HEQ|HEQ]; subst.
        { rewrite !ReordCommon.mapper_eq_a; split; ins; desf.
          { unfold is_r; rewrite !ReordCommon.mapper_eq_a, ReordCommon.mapper_eq_b.
            split; ins. }
          exists a; unfold is_r in H. rewrite ReordCommon.mapper_eq_b in H.
          split; ins. now rewrite ReordCommon.mapper_eq_a. }
        tertium_non_datur (a0 = b) as [HEQ1|HEQ1]; subst.
        { rewrite !ReordCommon.mapper_eq_b; split; ins; desf.
          { unfold is_r; rewrite ReordCommon.mapper_eq_b, ReordCommon.mapper_eq_a.
            split; ins. }
          exists b; unfold is_r in H. rewrite ReordCommon.mapper_eq_a in H.
          split; ins. now rewrite ReordCommon.mapper_eq_b. }
        rewrite !ReordCommon.mapper_neq; ins; split; ins; desf.
        { unfold is_r; rewrite !ReordCommon.mapper_neq; ins.
          all: rewrite !ReordCommon.mapper_neq; ins. }
        exists x. rewrite !ReordCommon.mapper_neq; ins.
        unfold is_r in H; rewrite ReordCommon.mapper_neq in H; ins. }
      split; unfolder; ins; unfold is_w, compose.
      { desf; rewrite !ReordCommon.mapper_neq in Heq; ins.
        all: try now (rewrite ReordCommon.mapper_neq; ins).
        all: exfalso; unfold is_w in H; now rewrite Heq in H. }
      desf; exists x. unfold is_w, compose in H.
      rewrite ReordCommon.mapper_neq in H; ins.
      rewrite ReordCommon.mapper_neq; ins. }
    admit. } (* mapped graph should be wf too! *)
  admit. (* consistency *)
Admitted.

Lemma simrel_exec_not_a_not_b e
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons G_t)
    (CONS' : WCore.is_cons G_s)
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' traces e) :
  exists G_s',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP' : WCore.exec_inst G_s G_s' traces' e >>.
Proof using SWAPPED_TRACES CTX.
  tertium_non_datur (E_t a) as [INA|INA].
  all: tertium_non_datur (E_t b) as [INB|INB].
  all: try now (exfalso; eapply rsrw_actids_t_ord; eauto).
  all: try now (apply simrel_exec_not_a_not_b_same_helper; ins).
  exists (ReordCommon.mapped_G_t_with_b G_t' a b).
  split.
  { apply mapper_simrel_niff; ins; try apply CTX.
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct add_event. ins. apply wf_new_conf. }
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct start_wf, pfx. ins.
      rewrite <- pfx_sub.(sub_lab). apply CTX. }
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct add_event. ins. apply e_new. now left. }
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct add_event. ins. intro F; apply INB.
      apply e_new in F; unfolder in F; desf. }
    admit. (* TODO: a remains max, because e is not b and therefore can't be added to a's thread *) } *)
  admit. (* NOTE: do not tackle this until the previous proof is prettified *)
Admitted.

Lemma simrel_exec_b
    (CONS : WCore.is_cons G_t)
    (CONS' : WCore.is_cons G_s)
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' traces a) :
  exists G_s',
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    exists G_s'_int,
      << STEP1 : WCore.exec_inst G_s G_s'_int traces' a >> /\
      << STEP2 : WCore.exec_inst G_s'_int G_s' traces' b >>.
Proof using SWAPPED_TRACES CTX.
  (* exists (ReordCommon.mapped_G_t_with_b G_t' a b); split.
  { apply mapper_simrel_niff; ins; try apply CTX.
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct add_event. ins. apply wf_new_conf. }
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct start_wf, pfx. ins.
      rewrite <- pfx_sub.(sub_lab). apply CTX. }
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
    desf. destruct add_event. ins. apply e_new. now right. }
    { destruct STEP. unfold WCore.cfg_add_event in add_event.
      desf. destruct add_event. ins. intro F; apply e_new in F.
      unfolder in F; desf; [| now apply CTX.(rctx_diff)].
      now apply SIM.(rsrw_actids_t_ord G_s G_t a b). }
    change G_t' with (WCore.G (WCore.Build_t G_t' G_t' ∅)).
    eapply WCore.new_event_max_sb; eapply STEP. } *)
  admit. (* TODO: research *)
Admitted.

Lemma simrel_exec_a w
    (CONS : WCore.is_cons G_t)
    (CONS' : WCore.is_cons G_s)
    (RF : G_t.(rf) w a)
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.exec_inst G_t G_t' traces b) :
  exists G_s' rfre,
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP : WCore.reexec G_s G_s' traces' rfre >>.
Proof using SWAPPED_TRACES.
  (* TODO: check article *)
  admit.
Admitted.

Lemma simrel_reexec rfre
    (CONS : WCore.is_cons G_t)
    (CONS' : WCore.is_cons G_s)
    (SIM : reord_simrel_rw G_s G_t a b)
    (STEP : WCore.reexec G_t G_t' traces rfre) :
  exists G_s' rfre,
    << SIM' : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP : WCore.reexec G_s G_s' traces' (mapper ↓ rfre) >>.
Proof using SWAPPED_TRACES.
  tertium_non_datur (E_t a) as [INA|INA].
  all: tertium_non_datur (E_t b) as [INB|INB].
  all: try now (exfalso; eapply rsrw_actids_t_ord; eauto).
  (* TODO adapt. *)
  (* all: try now (apply simrel_exec_not_a_not_b_same_helper; ins).
  exists (ReordCommon.mapped_G_t_with_b G_t' a b).
  split; [| apply mapper_simrel_niff; ins].
  all: try apply CTX.
  { admit. } (* TODO *)
  { destruct STEP. unfold WCore.cfg_add_event in add_event.
    desf. destruct add_event. ins. apply wf_new_conf. }
  { destruct STEP. unfold WCore.cfg_add_event in add_event.
    admit. } (* TODO ensure <G_t, G_t', cmt> is wf *)
  { destruct STEP. unfold WCore.cfg_add_event in add_event.
    desf. destruct add_event. ins. apply e_new. now left. }
  { destruct STEP. unfold WCore.cfg_add_event in add_event.
    desf. destruct add_event. ins. intro F; apply INB.
    apply e_new in F; unfolder in F; desf. } *)
Admitted.

End ExecutionSteps.

Section SimrelPreservations.

Variable Gs Gt : execution.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable a b : actid.

Lemma simrel_implies_cons
    (CONS : WCore.is_cons Gt)
    (SIM : reord_simrel_rw Gs Gt a b) :
  WCore.is_cons Gs.
Proof using.
  admit.
Admitted.

Lemma simrel_term
    (CONS : WCore.is_cons Gt)
    (SIM : reord_simrel_rw Gt Gs a b)
    (TERM : machine_terminated Gt traces) :
  << TERM' : machine_terminated Gs traces' >> /\
  << SIM' : ReordCommon.reord Gs Gt traces traces' a b >>.
Proof using.
  admit.
Admitted.

End SimrelPreservations.

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