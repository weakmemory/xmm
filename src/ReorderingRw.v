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
Require Import Instructions.

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
  rsrw_u2v : same_label_u2v (lab_s a) (lab_t b);
  rsrw_b_lab : forall (INB : E_t b), val_s a = val_t b;
  rsrw_srf_val : funeq (val
    (upd (lab_t ∘ mapper) a (lab_s a))
  ) (srf_s ⨾ ⦗eq a⦘);
  rsrw_b_tid : tid b <> tid_init;
  rsrw_a_tid : tid a <> tid_init;
  rsrw_actids_t_ord : forall (INB : E_t b) (NOTINA : ~E_t a), False;
}.

Record reord_simrel_rw_struct : Prop := {
  rsrw_lab_val_end : forall (INB : E_t b), val lab_s a = val_t b;
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

Definition rsrw_G_s_iff :=
  exec_upd_lab
    (exec_mapped G_t mapper (lab_t ∘ mapper))
  a (lab_s a).
Definition rsrw_G_s_niff_srf :=
  let srf := srf (exec_add_read_event_nctrl G_s a) in
    srf ⨾ ⦗eq a⦘.
Definition rsrw_G_s_niff :=
  exec_add_rf
    (exec_add_read_event_nctrl rsrw_G_s_iff a)
    rsrw_G_s_niff_srf.

Lemma rsrw_struct_iff
    (SAME : E_t a <-> E_t b) :
  reord_simrel_rw_struct <-> exec_equiv G_s rsrw_G_s_iff.
Proof using RSRW_ACTIDS.
  split; [intro STRUCT | intro EQUIV].
  { constructor; ins.
    all: try now apply STRUCT.
    admit. }
  assert (EQVLAB : lab_s = lab_t ∘ mapper).
  { admit. }
  constructor; ins.
  all: try now (exfalso; desf; eauto).
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
Admitted.

Lemma rsrw_struct_niff
    (INA : E_t a)
    (NOTINB : ~E_t b)
    (* (U2V  : same_label_u2v (lab_s a) (lab_t b))
    (EQVLAB : lab_s = upd (lab_t ∘ mapper) a (lab_s a))  *)
    :
  reord_simrel_rw_struct <-> exec_equiv G_s rsrw_G_s_niff.
Proof using RSRW_ACTIDS.
  split; [intro STRUCT | intro EQUIV].
  { constructor; ins.
    all: try now apply STRUCT.
    all: admit. }
  constructor; ins.
  all: try now apply EQUIV.
  all: try now (exfalso; desf; eauto).
  { admit. }
  { admit. }
  rewrite EQUIV.(exeeqv_acts _ _); ins.
  rewrite set_inter_union_l.
  arewrite (eq a ∩₁ is_init ≡₁ ∅); [| now rewrite set_union_empty_r].
  split; [| basic_solver]. intros x (EQ & INIT). subst.
  red. now apply RSRW_ACTIDS.(rsrw_ninit_a).
Admitted.

Lemma rsrw_G_s_in_E e
    (SIMREL : reord_simrel_rw)
    (NOTA : e <> a)
    (NOTB : e <> b) :
  E_s e <-> E_t e.
Proof using.
  rewrite <- 2!set_subset_single_l with (a := e).
  destruct (classic (E_t a)) as [INA|NINA],
           (classic (E_t b)) as [INB|NINB].
  { rewrite (rsrw_actids1 (rsrw_struct SIMREL)); ins.
    rewrite ReordCommon.mapper_acts_iff; ins. }
  { rewrite (rsrw_actids2 (rsrw_struct SIMREL)); ins.
    rewrite ReordCommon.mapper_acts_niff; ins.
    split; intros HSET; [| basic_solver].
    unfolder in *. specialize HSET with e.
    destruct HSET; ins; congruence. }
  { exfalso. now apply (rsrw_actids_t_ord (rsrw_actids SIMREL)). }
  rewrite (rsrw_actids1 (rsrw_struct SIMREL)); ins.
  rewrite ReordCommon.mapper_acts_iff; ins.
Qed.

Lemma G_t_niff_b_max
    (CONT : contigious_actids G_t)
    (INA : E_t a)
    (NINB : ~E_t b) :
  (fun x => ext_sb x b) ⊆₁ E_t ∩₁ same_tid b ∪₁ is_init.
Proof using RSRW_ACTIDS.
  assert (ANINIT : ~is_init a).
  { apply RSRW_ACTIDS. }
  assert (SMTID : tid a = tid b).
  { apply rsrw_tid_a_tid_b. }
  unfolder. intros x SB.
  destruct (classic (x = a)) as [EQ|NEQ]; subst.
  { left. split; ins. }
  destruct (classic (is_init x)) as [INIT|NINIT]; eauto.
  assert (SMTID' : tid x = tid a).
  { rewrite SMTID. red in SB. desf. ins. desf. }
  destruct (ext_sb_semi_total_r) with (x := b) (y := a) (z := x)
                                 as [SB'|SB'].
  all: eauto.
  { destruct x as [xl | x_t x_n], a as [al | a_t a_n]; ins.
    congruence. }
  { apply RSRW_ACTIDS. }
  { exfalso. eapply (rsrw_a_b_ord RSRW_ACTIDS); eauto. }
  left. split; [| red; congruence].
  apply ext_sb_dense with (e2 := a); ins.
  rewrite SMTID'. apply RSRW_ACTIDS.
Qed.

Lemma G_s_cont
    (STRUCT : reord_simrel_rw_struct)
    (CONT : contigious_actids G_t) :
  contigious_actids G_s.
Proof using RSRW_ACTIDS.
  destruct (classic (E_t a /\ ~E_t b)) as [NIFF|IFF].
  { desf.
    apply add_event_to_contigious with (G := G_t) (e := b); ins.
    { apply RSRW_ACTIDS. }
    { rewrite (rsrw_actids2 STRUCT); ins.
      now rewrite ReordCommon.mapper_acts_niff. }
    apply G_t_niff_b_max; ins. }
  assert (IFF' : E_t a <-> E_t b).
  { destruct (classic (E_t a)) as [INA|NINA],
            (classic (E_t b)) as [INB|NINB]; ins.
    { exfalso. eauto 11. }
    exfalso. apply (rsrw_actids_t_ord RSRW_ACTIDS).
    all: ins. }
  unfold contigious_actids. ins.
  destruct CONT with t as [N EQ]; ins.
  exists N. rewrite (rsrw_actids1 STRUCT); ins.
  rewrite ReordCommon.mapper_acts_iff; ins.
Qed.

End SimRel.

Section ReordSimRelInstrs.

Variable G_s G_t : execution.
Variable e2i_s e2i_t : actid -> I2Exec.intr_info.
Variable rmwi : I2Exec.instr_id -> Prop.
Variable ai bi : I2Exec.intr_info.

Record reord_simrel_rw_instrs_gen a b : Prop := {
  rwi_orig_simrel : reord_simrel_rw G_s G_t a b;
  rwi_s_wf : I2Exec.E2InstrWf G_s e2i_s rmwi;
  rwi_t_wf : I2Exec.E2InstrWf G_t e2i_t rmwi;
  rwi_e2i_s_a : e2i_s a = ai;
  rwi_e2i_s_b : e2i_s b = bi;
  rwi_e2i_t_a : e2i_t a = ai;
  rwi_e2i_t_b : e2i_t b = bi;
  rwi_ai : ~rmwi (I2Exec.instr ai);
  rwi_bi : ~rmwi (I2Exec.instr bi);
}.

Definition reord_simrel_rw_instrs := exists a b, reord_simrel_rw_instrs_gen a b.

End ReordSimRelInstrs.

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
  admit.
  (* constructor; constructor; ins.
  all: try now (rewrite collect_rel_empty; ins).
  all: try now (exfalso; apply ACTIDS.(rsrw_ninit_a G_t a b), INA).
  all: try now apply ACTIDS.
  all: try now apply STRUCT.
  { apply ACTIDS.(rsrw_ninit_b G_t a b), INB. }
  all: rewrite STRUCT.(rsrw_init _ _ _ _).
  all: rewrite set_collect_interE, ReordCommon.mapper_is_init; ins.
  all: try now apply ACTIDS.
  all: eapply ReordCommon.mapper_inj, rsrw_a_neq_b; eauto. *)
Admitted.

End Basic.

Section SimrelExec.

Variable G_t G_t' G_s : execution.
Variable sc : relation actid.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable a b : actid.
Variable e2i_s e2i_t : actid -> I2Exec.intr_info.
Variable rmwi : I2Exec.instr_id -> Prop.
Variable ai bi : I2Exec.intr_info.

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
Hypothesis SIMREL : reord_simrel_rw_instrs_gen G_s G_t e2i_s e2i_t rmwi ai bi a b.

Definition G_s' :=
  ifP E_t' a /\ ~E_t' b then rsrw_G_s_niff G_s G_t' a b
  else rsrw_G_s_iff G_s G_t' a b.

Notation "'lab_s''" := (lab G_s').
Notation "'val_s''" := (val lab_s').
Notation "'E_s''" := (acts_set G_s').
Notation "'loc_s''" := (loc lab_s').
Notation "'sb_s''" := (sb G_s').
Notation "'rf_s''" := (rf G_s').
Notation "'co_s''" := (co G_s').
Notation "'rmw_s''" := (rmw G_s').
Notation "'rpo_s''" := (rpo G_s').
Notation "'rmw_dep_s''" := (rmw_dep G_s').
Notation "'data_s''" := (data G_s').
Notation "'ctrl_s''" := (ctrl G_s').
Notation "'addr_s''" := (addr G_s').
Notation "'W_s''" := (is_w lab_s').
Notation "'R_s''" := (is_r lab_s').
Notation "'srf_s''" := (srf G_s').

Lemma G_s_niff
    (INA : E_t a)
    (NINB : ~E_t b) :
  G_s = rsrw_G_s_niff G_s G_t a b.
Proof using SIMREL.
  apply exeeqv_eq, rsrw_struct_niff; eauto.
  all: apply SIMREL.
Qed.

Lemma G_s_iff
    (INA : E_t a <-> E_t b) :
  G_s = rsrw_G_s_iff G_s G_t a b.
Proof using SIMREL.
  apply exeeqv_eq, rsrw_struct_iff; eauto.
  all: apply SIMREL.
Qed.

Lemma simrel_G_s' :
  reord_simrel_rw_instrs_gen G_s' G_t' e2i_s e2i_t rmwi ai bi a b.
Proof using SIMREL.
  admit.
Admitted.

Lemma srf_eq :
  exists sw,
    rsrw_G_s_niff_srf G_s a = singl_rel sw a.
Proof using.
  admit.
Admitted.

Definition X_t := {|
  WCore.G := G_t;
  WCore.GC := G_t';
  WCore.sc := sc;
  WCore.cmt := ∅;
|}.
Definition X_t' := {|
  WCore.G := G_t';
  WCore.GC := G_t';
  WCore.sc := sc;
  WCore.cmt := ∅;
|}.

Definition rsrw_X_s_iff := cfg_upd_lab
  (cfg_mapped X_t mapper (lab_t ∘ mapper))
  a (lab_s a).
Definition rsrw_X_s_niff := cfg_add_read_event_nctrl
  rsrw_X_s_iff a (rsrw_G_s_niff_srf G_s a).
Definition rsrw_X_s'_iff := cfg_upd_lab
  (cfg_mapped X_t' mapper (lab_t ∘ mapper))
  a (lab_s a).
Definition rsrw_X_s'_niff := cfg_add_read_event_nctrl
  rsrw_X_s'_iff a (rsrw_G_s_niff_srf G_s a).

Lemma G_t_labs
    (WF : WCore.wf X_t) :
  lab_t' = lab_t.
Proof using.
  symmetry. apply WF.
Qed.

Lemma rsrw_X_s_iff_eq
  (WF : WCore.wf X_t) :
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G := rsrw_G_s_iff G_s G_t a b;
      WCore.GC := rsrw_G_s_iff G_s G_t' a b;
      WCore.cmt := ∅
    |} = rsrw_X_s_iff.
Proof using.
  unfold rsrw_X_s_iff, cfg_upd_lab, cfg_mapped,
         cfg_add_read_event_nctrl,
         rsrw_G_s_iff, X_t.
  ins. f_equal; ins.
  { now rewrite G_t_labs. }
  apply set_extensionality. basic_solver.
Qed.

Lemma rsrw_X_s_niff_eq
  (WF : WCore.wf X_t) :
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G := rsrw_G_s_niff G_s G_t a b;
      WCore.GC := rsrw_G_s_niff G_s G_t' a b;
      WCore.cmt := ∅
    |} = rsrw_X_s_niff.
Proof using.
  unfold rsrw_X_s_niff.
  rewrite <- rsrw_X_s_iff_eq; ins.
Qed.

Lemma rsrw_X_s'_iff_eq
  (WF : WCore.wf X_t) :
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G := rsrw_G_s_iff G_s G_t' a b;
      WCore.GC := rsrw_G_s_iff G_s G_t' a b;
      WCore.cmt := ∅
    |} = rsrw_X_s'_iff.
Proof using.
  unfold rsrw_X_s'_iff, cfg_upd_lab, cfg_mapped,
         cfg_add_read_event_nctrl,
         rsrw_G_s_iff, X_t.
  ins. f_equal; ins.
  all: try now rewrite G_t_labs.
  apply set_extensionality. basic_solver.
Qed.

Lemma rsrw_X_s'_niff_eq
  (WF : WCore.wf X_t) :
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G := rsrw_G_s_niff G_s G_t' a b;
      WCore.GC := rsrw_G_s_niff G_s G_t' a b;
      WCore.cmt := ∅
    |} = rsrw_X_s'_niff.
Proof using.
  unfold rsrw_X_s'_niff.
  rewrite <- rsrw_X_s'_iff_eq; ins.
Qed.

Lemma simrel_exec_not_a_not_b e
    (E_NOT_A : e <> a)
    (E_NOT_B : e <> b)
    (CONS : WCore.is_cons G_t sc)
    (STEP : WCore.exec_inst G_t G_t' sc traces e) :
  exists G_s' sc',
    << SIMREL : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP : WCore.exec_inst G_s G_s' sc' traces' e >>.
Proof using SIMREL.
  (* Preamble *)
  destruct STEP as [STARTWF ADD]. red in ADD. desf.
  assert (INAIFF : E_t a <-> E_t' a).
  { rewrite <- 2!set_subset_single_l with (a := a).
    rewrite (WCore.caes_e_new STRUCT); ins.
    rewrite 2!set_subset_single_l.
    unfolder; split; ins; desf; eauto. }
  assert (INBIFF : E_t b <-> E_t' b).
  { rewrite <- 2!set_subset_single_l with (a := b).
    rewrite (WCore.caes_e_new STRUCT); ins.
    rewrite 2!set_subset_single_l.
    unfolder; split; ins; desf; eauto. }
  assert (IFFSHORTCUT : forall (CASE2 : ~ (E_t' a /\ ~E_t' b)),
                        E_t a <-> E_t b).
  { desf.
    destruct (classic (E_t a)) as [INA|NINA],
             (classic (E_t b)) as [INB|NINB]; ins.
    { exfalso. eauto 11. }
    exfalso. apply (rsrw_actids_t_ord
      (rsrw_actids (rwi_orig_simrel SIMREL))
    ).
    all: ins. }
  assert (IFFSHORTCUT' : forall (CASE2 : ~ (E_t' a /\ ~E_t' b)),
                        E_t' a <-> E_t' b).
  { ins. rewrite <- INAIFF, <- INBIFF. eauto. }
  (* Actual proof *)
  exists G_s', (mapper ↑ sc). split; constructor; ins.
  all: try now apply simrel_G_s'.
  { admit. (* TODO: simrel start wf *) }
  { apply sub_to_full_exec_single.
    { rewrite rsrw_G_s_in_E with (a := a) (b := b) (G_t := G_t).
      all: try now apply SIMREL.
      all: eauto.
      apply STRUCT. }
    { unfold G_s'.
      desf; desf; [rewrite G_s_niff | rewrite G_s_iff]; eauto; ins.
      all: rewrite (WCore.caes_e_new STRUCT), set_collect_union.
      all: rewrite set_collect_eq, ReordCommon.mapper_neq.
      all: ins.
      basic_solver 11. }
    { admit. (* TODO: wf start *) }
    { admit. (* TODO: traces *) }
    admit. (* TODO: rf edge-wfness *) }
  admit.
Admitted.

Lemma simrel_exec_b
    (CONS : WCore.is_cons G_t sc)
    (STEP : WCore.exec_inst G_t G_t' sc traces a) :
  exists G_s' sc' G_s'',
    << SIMREL : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP1 : WCore.exec_inst G_s   G_s'' sc' traces' a >> /\
    << STEP2 : WCore.exec_inst G_s'' G_s'  sc' traces' b >>.
Proof using SIMREL.
  (* Preamble *)
  destruct STEP as [STARTWF ADD]. red in ADD. desf.
  destruct (classic (E_t a)) as [INA|NINA].
  { exfalso. now apply (WCore.caes_e_notin STRUCT). }
  destruct (classic (E_t b)) as [INB|NINB].
  { exfalso. eapply rsrw_actids_t_ord; eauto.
    apply SIMREL. }
  assert (CASE2KILLER : ~~(E_t' a /\ ~E_t' b)).
  { admit. }
  assert (INTERNALSTARTWF : WCore.wf
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G := rsrw_G_s_iff G_s G_t a b;
      WCore.GC := rsrw_G_s_niff G_s G_t a b;
      WCore.cmt := ∅
    |}).
  { admit. }
  assert (INTERNALSTEP : WCore.cfg_add_event traces'
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G := rsrw_G_s_iff G_s G_t a b;
      WCore.GC := rsrw_G_s_niff G_s G_t a b;
      WCore.cmt := ∅
    |}
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G := rsrw_G_s_niff G_s G_t a b;
      WCore.GC := rsrw_G_s_niff G_s G_t a b;
      WCore.cmt := ∅
    |} a).
  { apply sub_to_full_exec_single; ins.
    { intro F. apply ReordCommon.mapper_acts_iff in F; ins. }
    { admit. (* TODO: traces *) }
    admit. (* srf stuff *) }
  assert (INTERNALWF : WCore.wf
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G := rsrw_G_s_niff G_s G_t a b;
      WCore.GC := rsrw_G_s_niff G_s G_t' a b;
      WCore.cmt := ∅
    |}).
  { admit. }
  (* Actual proof *)
  exists G_s', (mapper ↑ sc), (rsrw_G_s_niff G_s G_t a b).
  unfold NW. rewrite G_s_iff at 1; ins.
  unfold G_s'.
  splits; constructor; ins.
  all: try now apply simrel_G_s'.
  all: desf.
  { admit. (* TODO: intermediate cons *) }
  { desf. apply sub_to_full_exec_single; ins.
    { intros [INE | EQ].
      { apply ReordCommon.mapper_acts_iff in INE; ins. }
      eapply rsrw_a_neq_b; eauto. apply SIMREL. }
    { rewrite ReordCommon.mapper_acts_niff,
              ReordCommon.mapper_acts_iff.
      all: ins.
      rewrite (WCore.caes_e_new STRUCT). ins. }
    { admit. (* TODO: traces *) }
    admit. (* rf stuff *) }
  admit. (* TODO: cons of finish *)
Admitted.

Lemma simrel_exec_a w
    (RF : rf_t' w a)
    (CONS : WCore.is_cons G_t sc)
    (STEP : WCore.exec_inst G_t G_t' sc traces b) :
  exists G_s' sc' dtrmt' cmt',
    << SIM : reord_simrel_rw G_s' G_t' a b >> /\
    << STEP : WCore.reexec G_s G_s' sc' traces' dtrmt' cmt' >>.
Proof using SIMREL.
  (* Preamble *)
  destruct STEP as [STARTWF ADD]. red in ADD. desf.
  assert (INB' : E_t' b).
  { apply (WCore.caes_e_new STRUCT). basic_solver. }
  assert (INA' : E_t' a).
  { apply ext_sb_dense with (e2 := b); eauto.
    all: try now apply SIMREL.
    apply WF_NEW. }
  assert (INA : E_t a).
  { apply (WCore.caes_e_new STRUCT) in INA'. ins.
    destruct INA' as [INE | EQ]; ins.
    exfalso. symmetry in EQ.
    eapply rsrw_a_neq_b; eauto.
    apply SIMREL. }
  assert (NINB : ~ E_t b).
  { apply STRUCT. }
  assert (REXECBEGWF : WCore.wf
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G :=
        WCore.reexec_start G_s G_s'
          (E_s \₁ (eq a ∪₁ eq b));
      WCore.GC := G_s';
      WCore.cmt := E_s' \₁ eq a
    |}
  ).
  { admit. }
  assert (UNCMT : WCore.stable_uncmt_reads_gen G_s'
      (E_s' \₁ eq a)
      (fun _ y => y = tid a)
  ).
  { admit. }
  assert (ESEQ : E_s' ≡₁ E_s ∪₁ eq a).
  { unfold G_s'; desf; [desf; exfalso; eauto |].
    rewrite G_s_niff; ins.
    rewrite ReordCommon.mapper_acts_niff,
            ReordCommon.mapper_acts_iff; ins.
    rewrite (WCore.caes_e_new STRUCT); ins.
    basic_solver. }
  (* Actual proof *)
  exists G_s', (mapper ↑ sc),
        (E_s \₁ (eq a ∪₁ eq b)),
        (E_s' \₁ eq a).
  splits; [| exists (@id actid), (fun x y => y = tid a)].
  all: constructor; ins.
  all: try now apply simrel_G_s'.
  { admit. (* lab stuff *) }
  { rewrite ESEQ. basic_solver. }
  { basic_solver. }
  { constructor; ins.
    { rewrite ESEQ. basic_solver. }
    { admit. (* same lab for cmt *) }
    { admit. (* sb: sub *) }
    admit. (* rf sub *) }
  { eapply sub_to_full_exec_listless; eauto.
    { admit. (* trace coh *) }
    { admit. (* rf wf *) }
    admit. (* internal rf *) }
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