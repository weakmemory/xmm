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
Notation "'loc_t'" := (loc lab_t).
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
Notation "'F_t'" := (is_f lab_t).

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
Notation "'F_s'" := (is_f lab_s).
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

Lemma rsrw_E_iff
    (NIFF : ~(E_t a /\ ~E_t b)) :
  E_t a <-> E_t b.
Proof using RSRW_ACTIDS.
  destruct (classic (E_t a)) as [INA|NINA],
            (classic (E_t b)) as [INB|NINB]; ins.
  { exfalso. eauto 11. }
  exfalso. apply (rsrw_actids_t_ord RSRW_ACTIDS).
  all: ins.
Qed.

Lemma rsrw_loc_mapped
    (STRUCT : reord_simrel_rw_struct) :
  loc_s = loc_t ∘ mapper.
Proof using RSRW_ACTIDS.
  apply functional_extensionality. unfold compose. intro x.
  destruct ReordCommon.mapper_surj with (a := a) (b := b) (y := x)
                                     as [x' EQ].
  { apply rsrw_a_neq_b. }
  subst x. rewrite ReordCommon.mapper_self_inv; auto using rsrw_a_neq_b.
  assert (U2V : same_label_u2v (lab_s (mapper x')) (lab_t x')).
  { apply STRUCT. ins. }
  unfold same_label_u2v, loc in *. desf.
  all: desf.
Qed.

Lemma rsrw_sameloc
    (STRUCT : reord_simrel_rw_struct) :
  same_loc (lab_s) ≡ mapper ↑ same_loc (lab_t).
Proof using RSRW_ACTIDS.
  unfold same_loc. rewrite rsrw_loc_mapped; ins.
  unfold compose. unfolder. split.
  { intros x y HLOC. exists (mapper x), (mapper y).
    splits; ins.
    all: rewrite ReordCommon.mapper_self_inv.
    all: auto using rsrw_a_neq_b. }
  intros x y (x' & y' & LOC & XEQ & YEQ). subst.
  rewrite !ReordCommon.mapper_self_inv.
  all: auto using rsrw_a_neq_b.
Qed.

Lemma rsrw_mapped_r
    (STRUCT : reord_simrel_rw_struct) :
  R_s ≡₁ mapper ↑₁ R_t.
Proof using RSRW_ACTIDS.
  enough (SAME_R : R_t = R_s ∘ mapper).
  { rewrite SAME_R. unfold compose. unfolder.
    split; [intros x IS_R | ins; desf ].
    exists (mapper x).
    rewrite ReordCommon.mapper_self_inv.
    all: auto using rsrw_a_neq_b. }
  apply functional_extensionality; intros x.
  assert (U2V : same_label_u2v (lab_s (mapper x)) (lab_t x)).
  { apply STRUCT. ins. }
  unfold compose, same_label_u2v, is_r in *. desf.
Qed.

Lemma rsrw_mapped_w
    (STRUCT : reord_simrel_rw_struct) :
  W_s ≡₁ mapper ↑₁ W_t.
Proof using RSRW_ACTIDS.
  enough (SAME_W : W_t = W_s ∘ mapper).
  { rewrite SAME_W. unfold compose. unfolder.
    split; [intros x IS_W | ins; desf ].
    exists (mapper x).
    rewrite ReordCommon.mapper_self_inv.
    all: auto using rsrw_a_neq_b. }
  apply functional_extensionality; intros x.
  assert (U2V : same_label_u2v (lab_s (mapper x)) (lab_t x)).
  { apply STRUCT. ins. }
  unfold compose, same_label_u2v, is_w in *. desf.
Qed.

Lemma rsrw_mapped_f
    (STRUCT : reord_simrel_rw_struct) :
  F_s ≡₁ mapper ↑₁ F_t.
Proof using RSRW_ACTIDS.
  enough (SAME_F : F_t = F_s ∘ mapper).
  { rewrite SAME_F. unfold compose. unfolder.
    split; [intros x IS_F | ins; desf ].
    exists (mapper x).
    rewrite ReordCommon.mapper_self_inv.
    all: auto using rsrw_a_neq_b. }
  apply functional_extensionality; intros x.
  assert (U2V : same_label_u2v (lab_s (mapper x)) (lab_t x)).
  { apply STRUCT. ins. }
  unfold compose, same_label_u2v, is_f in *. desf.
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
    (SAME : E_t a <-> E_t b)
    (STRUCT : reord_simrel_rw_struct) :
  exec_equiv G_s rsrw_G_s_iff.
Proof using RSRW_ACTIDS.
  constructor; ins.
  all: try now apply STRUCT.
  now apply rsrw_struct_same_lab.
Qed.

Lemma rsrw_struct_niff
    (INA : E_t a)
    (NOTINB : ~E_t b)
    (STRUCT : reord_simrel_rw_struct) :
  exec_equiv G_s rsrw_G_s_niff.
Proof using RSRW_ACTIDS.
  constructor; ins.
  all: try now apply STRUCT.
  { now apply rsrw_struct_same_lab. }
  rewrite (rsrw_rf2 STRUCT) by ins.
  unfold rsrw_G_s_niff_srf.
  enough (EQ : G_s = exec_add_read_event_nctrl G_s a).
  { now rewrite EQ at 1. }
  apply exeeqv_eq. constructor; ins.
  enough (INA' : E_s a) by basic_solver.
  apply (rsrw_actids2 STRUCT); ins. now right.
Qed.

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
  { apply rsrw_E_iff; ins. }
  unfold contigious_actids. ins.
  destruct CONT with t as [N EQ]; ins.
  exists N. rewrite (rsrw_actids1 STRUCT); ins.
  rewrite ReordCommon.mapper_acts_iff; ins.
Qed.

Lemma rsrw_E_s_sub
    (STRUCT : reord_simrel_rw_struct) :
  E_s ⊆₁ mapper ↑₁ E_t ∪₁ eq a.
Proof using RSRW_ACTIDS.
  destruct (classic (E_t a /\ ~E_t b)) as [NIFF|IFF].
  { desf. rewrite (rsrw_actids2 STRUCT); ins. }
  rewrite (rsrw_actids1 STRUCT); [basic_solver 6|].
  eapply rsrw_E_iff; eauto.
Qed.

Lemma rsrw_sub_E_s
    (STRUCT : reord_simrel_rw_struct) :
  mapper ↑₁ E_t ⊆₁ E_s.
Proof using RSRW_ACTIDS.
  destruct (classic (E_t a /\ ~E_t b)) as [NIFF|IFF].
  { desf. rewrite (rsrw_actids2 STRUCT); ins. basic_solver. }
  rewrite (rsrw_actids1 STRUCT); [basic_solver 6|].
  eapply rsrw_E_iff; eauto.
Qed.

End SimRel.

Section ReordSimRelInstrs.

Variable G_s G_t : execution.
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

Lemma mapped_sb_subrel a b r
    (SIMREL : reord_simrel_rw_instrs_gen a b)
    (SUBORIG : r ⊆ sb_t)
    (RNOT : ~r a b) :
  ReordCommon.mapper a b ↑ r ⊆
    ⦗ReordCommon.mapper a b ↑₁ E_t⦘ ⨾ ext_sb ⨾ ⦗ReordCommon.mapper a b ↑₁ E_t⦘.
Proof using.
  apply ReordCommon.mapped_G_t_sb_helper with (lab' := lab_t).
  all: try now apply SIMREL.
  all: ins.
Qed.

Lemma mapped_rmw_helper a b
    (SIMREL : reord_simrel_rw_instrs_gen a b)
    (WF : Wf G_t) :
  ReordCommon.mapper a b ↑ rmw_t ⊆ immediate (
    ⦗ReordCommon.mapper a b ↑₁ E_t⦘ ⨾ ext_sb ⨾ ⦗ReordCommon.mapper a b ↑₁ E_t⦘
  ).
Proof using.
  apply ReordCommon.mapped_G_t_immsb_helper with (lab' := lab_t).
  all: try now apply SIMREL.
  { apply WF. }
  { intro F. apply (wf_rmwl WF) in F.
    eapply rsrw_loc; eauto. apply SIMREL. }
  { intro F.
    assert (INU : (dom_rel rmw_t ∪₁ codom_rel rmw_t) a).
    { basic_solver. }
    apply SIMREL in INU. unfold I2Exec.rmw_actids in INU.
    unfolder in INU. unfold compose in INU.
    rewrite (rwi_e2i_t_a SIMREL) in INU.
    now apply (rwi_ai SIMREL). }
  intro F.
  assert (INU : (dom_rel rmw_t ∪₁ codom_rel rmw_t) b).
  { basic_solver. }
  apply SIMREL in INU. unfold I2Exec.rmw_actids in INU.
  unfolder in INU. unfold compose in INU.
  rewrite (rwi_e2i_t_b SIMREL) in INU.
  now apply (rwi_bi SIMREL).
Qed.

Lemma G_s_wf a b
    (NCTRL : ctrl G_t ≡ ∅₂)
    (NDATA : data G_t ≡ ∅₂)
    (NADDR : addr G_t ≡ ∅₂)
    (WF : Wf G_t)
    (WF_TIDS : forall e (NINIT : ~is_init e) (INE : E_t e),
                tid e <> tid_init)
    (SIMREL : reord_simrel_rw_instrs_gen a b) :
  Wf G_s.
Proof using.
  assert (STRUCT : reord_simrel_rw_struct G_s G_t a b).
  { apply SIMREL. }
  assert (ACTIDS : reord_simrel_rw_actids G_s G_t a b).
  { apply SIMREL. }
  assert (NEQ : a <> b).
  { apply (rsrw_a_neq_b ACTIDS). }
  assert (TOT : forall ol,
    is_total (E_s ∩₁ W_s ∩₁ (fun x => loc_s x = ol)) co_s
  ).
  { admit. }
  assert (RF_S_SUB : rf_s ⊆ ReordCommon.mapper a b ↑ rf_t ∪ (srf_s ⨾ ⦗eq a⦘)).
  { destruct (classic (E_t a /\ ~E_t b)) as [NIFF|IFF].
    { desf. rewrite (rsrw_rf2 STRUCT); ins. }
    rewrite (rsrw_rf1 STRUCT); [basic_solver 6|].
    eapply rsrw_E_iff; eauto. }
  assert (E_S_SUB : E_s ⊆₁ eq a ∪₁ ReordCommon.mapper a b ↑₁ E_t).
  { rewrite rsrw_E_s_sub; eauto. basic_solver. }
  assert (SUB_E_S : ReordCommon.mapper a b ↑₁ E_t ⊆₁ E_s).
  { apply rsrw_sub_E_s; ins. }
  constructor.
  { intros x y (XINE & YINE & XYNEQ & TID & XNINIT).
    destruct x as [xl | xn xt]; ins.
    destruct y as [yl | yn yt]; [ins | ins; congruence].
    apply E_S_SUB in XINE. destruct XINE as [EQA | XINE].
    { exfalso. desf. apply (rsrw_a_tid ACTIDS). ins. }
    exfalso.
    apply WF_TIDS with (e := ReordCommon.mapper a b (ThreadEvent xn xt)).
    { intro F.
      apply ReordCommon.mapper_is_init with (a := a) (b := b)
                                         in F.
      all: try now apply ACTIDS.
      unfolder in F. destruct F as (y & INIT & EQ).
      apply ReordCommon.mapper_inj in EQ; ins.
      desf. }
    { unfolder in XINE. destruct XINE as (y & INE & EQ).
      rewrite <- EQ, ReordCommon.mapper_self_inv; ins. }
    change (tid (ReordCommon.mapper a b (ThreadEvent xn xt)))
      with ((tid ∘ ReordCommon.mapper a b) (ThreadEvent xn xt)).
    rewrite ReordCommon.mapper_tid; ins.
    apply (rsrw_tid_a_tid_b ACTIDS). }
  { rewrite (rsrw_data STRUCT), NDATA. basic_solver. }
  { rewrite (rsrw_data STRUCT), NDATA. basic_solver. }
  { rewrite (rsrw_addr STRUCT), NADDR. basic_solver. }
  { rewrite (rsrw_addr STRUCT), NADDR. basic_solver. }
  { rewrite (rsrw_ctrl STRUCT), NCTRL. basic_solver. }
  { rewrite (rsrw_ctrl STRUCT), NCTRL. basic_solver. }
  { rewrite (rsrw_ctrl STRUCT), NCTRL. basic_solver. }
  { rewrite (rsrw_rmw STRUCT), (rsrw_mapped_r ACTIDS STRUCT),
            (rsrw_mapped_w ACTIDS STRUCT).
    rewrite <- !collect_rel_eqv, <- !collect_rel_seq.
    all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
    now apply collect_rel_more, WF. }
  { rewrite (rsrw_rmw STRUCT), (rsrw_sameloc ACTIDS STRUCT).
    now apply collect_rel_mori, WF. }
  { rewrite (rsrw_rmw STRUCT), mapped_rmw_helper by ins.
    admit. }
  { split; [| basic_solver]. apply dom_helper_3.
    rewrite RF_S_SUB. apply inclusion_union_l.
    { rewrite (wf_rfE WF), !collect_rel_seq,
              !collect_rel_eqv, SUB_E_S.
      all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
      basic_solver. }
    admit. }
  { split; [| basic_solver]. apply dom_helper_3.
    rewrite RF_S_SUB. apply inclusion_union_l.
      { rewrite (wf_rfD WF), !collect_rel_seq,
              !collect_rel_eqv,
              <- (rsrw_mapped_w ACTIDS STRUCT),
              <- (rsrw_mapped_r ACTIDS STRUCT).
        all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
        basic_solver. }
      arewrite (srf_s ⨾ ⦗eq a⦘ ⊆ srf_s) by basic_solver.
      apply dom_helper_3, wf_srfD. }
  { rewrite RF_S_SUB. apply inclusion_union_l.
    { now rewrite (wf_rfl WF), (rsrw_sameloc ACTIDS STRUCT). }
    arewrite (srf_s ⨾ ⦗eq a⦘ ⊆ srf_s) by basic_solver.
    apply wf_srf_loc. }
  { rewrite RF_S_SUB. apply funeq_union.
    all: admit. (* TODO *) }
  { admit. (* functional stuff *) }
  { split; [| basic_solver]. apply dom_helper_3.
    rewrite (rsrw_co STRUCT), (wf_coE WF), !collect_rel_seq,
            !collect_rel_eqv, SUB_E_S.
    all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
    basic_solver. }
  { rewrite (rsrw_co STRUCT),
            (rsrw_mapped_w ACTIDS STRUCT),
            <- !collect_rel_eqv,
            <- !collect_rel_seq.
    all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
    apply collect_rel_more, WF; ins. }
  { rewrite (rsrw_co STRUCT), (rsrw_sameloc ACTIDS STRUCT).
    apply collect_rel_mori, WF; ins. }
  { rewrite (rsrw_co STRUCT).
    arewrite (co_t ≡ restr_rel ⊤₁ co_t) by basic_solver.
    apply transitive_collect_rel_inj.
    all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
    arewrite (restr_rel ⊤₁ co_t ≡ co_t) by basic_solver.
    apply WF. }
  { apply TOT. }
  { rewrite (rsrw_co STRUCT).
    arewrite (co_t ≡ restr_rel ⊤₁ co_t) by basic_solver.
    apply collect_rel_irr_inj.
    all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
    arewrite (restr_rel ⊤₁ co_t ≡ co_t) by basic_solver.
    apply WF. }
  { admit. (* loc-ey business *) }
  { admit. (* TODO *) }
  { admit. } (* apply mapped_sb_subrel *)
  { admit. }
  intros e INE. apply (rsrw_threads STRUCT).
  destruct (classic (E_t a /\ ~E_t b)) as [NIFF|IFF].
  { desf. apply (rsrw_actids2 STRUCT) in INE; ins.
    destruct INE as [INE | EQA]; subst.
    all: try now apply WF.
    unfolder in INE. destruct INE as (e' & INE & EQ); subst.
    change (tid (ReordCommon.mapper a b e'))
      with ((tid ∘ ReordCommon.mapper a b) e').
    rewrite ReordCommon.mapper_tid; try now apply WF.
    apply (rsrw_tid_a_tid_b ACTIDS). }
  apply (rsrw_actids1 STRUCT) in INE.
  all: try now eapply rsrw_E_iff; eauto.
  unfolder in INE. destruct INE as (e' & INE & EQ); subst.
  change (tid (ReordCommon.mapper a b e'))
    with ((tid ∘ ReordCommon.mapper a b) e').
  rewrite ReordCommon.mapper_tid; try now apply WF.
  apply (rsrw_tid_a_tid_b ACTIDS).
Admitted.

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

Lemma G_s_wf'
    (NCTRL : ctrl G_t' ≡ ∅₂)
    (NDATA : data G_t' ≡ ∅₂)
    (NADDR : addr G_t' ≡ ∅₂)
    (WF_TIDS : forall e (NINIT : ~ is_init e)
                      (INE : E_t' e),
                tid e <> tid_init)
    (WF : Wf G_t') :
  Wf G_s'.
Proof using SIMREL.
  eapply G_s_wf; eauto using simrel_G_s'.
Qed.

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

Lemma exec_start_cfg_wf
    (STARTWF : WCore.wf
      {|
        WCore.sc := sc;
        WCore.G := G_t;
        WCore.GC := G_t';
        WCore.cmt := ∅
      |}) :
  WCore.wf
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G := G_s;
      WCore.GC := G_s';
      WCore.cmt := ∅
    |}.
Proof using SIMREL.
  assert (NEQ : a <> b).
  { eapply rsrw_a_neq_b, SIMREL. }
  split; constructor; ins.
  { admit. (* TODO *) }
  { erewrite rsrw_ctrl, (WCore.wf_cc_ctrl_empty STARTWF),
              collect_rel_empty; ins.
    apply simrel_G_s'. }
  { erewrite rsrw_addr, (WCore.wf_cc_addr_empty STARTWF),
             collect_rel_empty; ins.
    apply simrel_G_s'. }
  { erewrite rsrw_data, (WCore.wf_cc_data_empty STARTWF),
             collect_rel_empty; ins.
    apply simrel_G_s'. }
  { eapply G_s_cont; try now apply SIMREL.
    apply STARTWF. }
  { eapply G_s_cont; try now apply simrel_G_s'.
    apply STARTWF. }
  { rewrite rsrw_E_s_sub with (G_s := G_s') (G_t := G_t'),
            <- rsrw_sub_E_s with (G_s := G_s) (G_t := G_t).
    all: try now apply SIMREL.
    all: try now apply simrel_G_s'.
    rewrite set_inter_union_l.
    arewrite (eq a ∩₁ is_init ≡₁ ∅).
    { split; [| basic_solver]. intros x (HEQ & INIT).
      subst x. red.
      eapply rsrw_ninit_a; try now apply SIMREL.
      ins. }
    rewrite set_union_empty_r.
    rewrite <- ReordCommon.mapper_is_init
          with (a := a) (b := b).
    all: try now apply SIMREL.
    rewrite <- set_collect_interE.
    all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
    apply set_collect_mori; ins. apply STARTWF. }
  { rewrite rsrw_E_s_sub; try now apply simrel_G_s'.
    rewrite set_inter_union_r.
    arewrite (tid ↓₁ eq tid_init ∩₁ eq a ≡₁ ∅).
    { split; [| basic_solver]. intros x (HEQ & INIT).
      subst x. red.
      eapply rsrw_a_tid; try now apply SIMREL.
      ins. }
    rewrite set_union_empty_r.
    arewrite (tid ↓₁ eq tid_init ∩₁ mapper ↑₁ E_t' ⊆₁
              mapper ↑₁ (tid ↓₁ eq tid_init ∩₁ E_t')).
    { rewrite set_collect_interE; eauto using ReordCommon.mapper_inj.
      apply set_subset_inter; ins. unfolder. intros x TID.
      exists (mapper x).
      split; [| rewrite ReordCommon.mapper_self_inv; ins].
      change (tid (mapper x)) with ((tid ∘ mapper) x).
      rewrite ReordCommon.mapper_tid; ins.
      eapply rsrw_tid_a_tid_b, SIMREL. }
    rewrite (WCore.wf_gc_acts STARTWF), ReordCommon.mapper_is_init.
    all: ins; apply SIMREL. }
  { apply G_s_wf'; try now apply STARTWF.
    ins. intro F. apply NINIT.
    apply (WCore.wf_gc_acts STARTWF); ins.
    unfolder. splits; ins. }
  { admit. (* TODO: remove sc? *) }
  { assert (STRUCT : reord_simrel_rw_struct G_s G_t a b).
    { apply SIMREL. }
    assert (STRUCT' : reord_simrel_rw_struct G_s' G_t' a b).
    { apply simrel_G_s'. }
    assert (SUB : sub_execution G_t' G_t ∅₂ ∅₂).
    { apply STARTWF. }
    constructor; ins.
    { admit. }
    { admit. }
    { admit. }
    { rewrite (rsrw_rmw STRUCT), (rsrw_rmw STRUCT'),
              (sub_rmw SUB), !collect_rel_seq,
              collect_rel_eqv.
      all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
      admit. }
    { rewrite (rsrw_data STRUCT), (rsrw_data STRUCT'),
              (sub_data SUB), !collect_rel_seq,
              collect_rel_eqv.
      all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
      rewrite (WCore.wf_cc_data_empty STARTWF). basic_solver. }
    { rewrite (rsrw_addr STRUCT), (rsrw_addr STRUCT'),
              (sub_addr SUB), !collect_rel_seq,
              collect_rel_eqv.
      all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
      rewrite (WCore.wf_cc_addr_empty STARTWF). basic_solver. }
    { rewrite (rsrw_ctrl STRUCT), (rsrw_ctrl STRUCT'),
              (sub_ctrl SUB), !collect_rel_seq,
              collect_rel_eqv.
      all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
      rewrite (WCore.wf_cc_ctrl_empty STARTWF). basic_solver. }
    { rewrite (rsrw_rmwdep STRUCT), (rsrw_rmwdep STRUCT'),
              (sub_frmw SUB), !collect_rel_seq,
              collect_rel_eqv.
      all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
      admit. }
    { admit. }
    { rewrite (rsrw_co STRUCT), (rsrw_co STRUCT'),
              (sub_co SUB), !collect_rel_seq,
              collect_rel_eqv.
      all: try now eapply inj_dom_mori, ReordCommon.mapper_inj; eauto.
      admit. }
    basic_solver. }
  { basic_solver. }
  { basic_solver. }
  { admit. (* TODO *) }
  basic_solver.
Admitted.

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
  assert (BEGWF : WCore.wf
    {|
      WCore.sc := mapper ↑ sc;
      WCore.G := G_s;
      WCore.GC := G_s';
      WCore.cmt := ∅
    |}).
  { now apply exec_start_cfg_wf. }
  (* Actual proof *)
  exists G_s', (mapper ↑ sc). split; constructor; ins.
  all: try now apply simrel_G_s'.
  { apply sub_to_full_exec_single; ins.
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
    { admit. (* TODO: traces *) }
    admit. (* TODO: rf edge-wfness *) }
  admit.
Admitted.

Lemma simrel_exec_b_helper
    (INA : ~E_t a)
    (NINB : ~E_t b)
    (ACTEQ : E_t' ≡₁ E_t ∪₁ eq a)
    (CONS1 : WCore.is_cons
              (rsrw_G_s_niff G_s G_t  a b)
              (mapper ↑ sc))
    (CONS2 : WCore.is_cons
              (rsrw_G_s_niff G_s G_t' a b)
              (mapper ↑ sc))
    (STEPS : (WCore.cfg_add_event_uninformative traces')＊
              (WCore.Build_t (mapper ↑ sc) G_s  G_s' ∅)
              (WCore.Build_t (mapper ↑ sc) G_s' G_s' ∅)
    ) :
  << STEP1 : WCore.exec_inst
              G_s
              (rsrw_G_s_niff G_s G_t  a b)
              (mapper ↑ sc)
              traces'
              a
  >> /\
  << STEP2 : WCore.exec_inst
              (rsrw_G_s_niff G_s G_t  a b)
              G_s'
              (mapper ↑ sc)
              traces'
              b
  >>.
Proof using SIMREL.
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
  (* The proof *)
  exists G_s', (mapper ↑ sc), (rsrw_G_s_niff G_s G_t a b).
  split; [apply simrel_G_s' |].
  apply simrel_exec_b_helper; ins.
  { apply (WCore.caes_e_new STRUCT). }
  { admit. (* intermediate graph cons *) }
  { admit. (* resulting graph cons *) }
  apply sub_to_full_exec
   with (l := [a; b]).
  { now apply exec_start_cfg_wf. }
  { constructor; ins.
    all: admit. (* all easy *) }
  admit. (* traces *)
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
  { admit. (* TODO: patch this re-exec cond first *) }
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