Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import ThreadTrace.
Require Import Core.
Require Import TraceSwap.
Require Import SubToFullExec.
(* Require Import ReorderingCommon. *)
Require Import AuxRel.
(* Require Import ExecEquiv.
Require Import ExecOps.
Require Import CfgOps.
Require Import StepOps.
Require Import Steps. *)
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
(* From imm Require Import SubExecution. *)
From imm Require Import CombRelations.

Set Implicit Arguments.

Section SimRel.

Variable X_s X_t : WCore.t.
Variable a_t b_t : actid.
Variable mapper : actid -> actid.

Notation "'G_t'" := (WCore.G X_t).
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

Notation "'G_s'" := (WCore.G X_s).
Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
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
Notation "'b_s'" := (mapper b_t).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).

Record extra_a_pred x : Prop := {
  ebp_is_r : R_s x;
  ebp_val : val_s x = val_s a_t;
  ebp_loc : loc_s x = loc_s a_t;
}.

Definition extra_a (a_s : actid) :=
  ifP ~E_t a_t /\ E_t b_t then eq a_s
  else ∅.

Record reord_simrel_gen a_s : Prop := {
  rsr_inj : inj_dom E_t mapper;
  rsr_codom : mapper ↑₁ E_t ⊆₁ E_s;
  rsr_tid : eq_dom E_t (tid ∘ mapper) tid;
  rsr_u2v : same_lab_u2v_dom (mapper ↓₁ extra_a a_s) (lab_s ∘ mapper) lab_t;
  rsr_lab : eq_dom (E_t \₁ mapper ↓₁ extra_a a_s) (lab_s ∘ mapper) lab_t;
  rsr_acts : E_s ≡₁ mapper ↑₁ E_t ∪₁ extra_a a_s;
  rsr_sb_imm : immediate sb_s ≡
    mapper ↑ (immediate sb_t \ singl_rel b_t a_t ∪ singl_rel a_t b_t ∩ E_t × E_t) ∪
    (mapper ↑₁ codom_rel (immediate sb_t ⨾ ⦗eq b_t⦘)) × (extra_a a_s) ∪
    (extra_a a_s) × eq b_s;
  rsr_rf : rf_s ≡ mapper ↑ rf_t ∪ srf_s ⨾ ⦗extra_a a_s ∩₁ R_s⦘;
  rsr_co : co_s ≡ mapper ↑ co_t ∪
            (W_s ∩₁ E_s ∩₁ Loc_s_ (loc_s a_s)) × (W_s ∩₁ extra_a a_s);
}.

Record reord_correct_graphs : Prop := {
  rsr_at_ninit : ~is_init a_t;
  rsr_bt_ninit : ~is_init b_t;
  rsr_Gt_wf : Wf G_t;
  rsr_Gt_rfc : rf_complete G_t;
  rsr_a_t_is_r_or_w : eq a_t ∩₁ E_t ⊆₁ (W_t ∪₁ R_t);
  rsr_b_t_is_r_or_w : eq b_t ∩₁ E_t ⊆₁ (W_t ∪₁ R_t);
  rsr_init_lab : eq_dom (E_t ∩₁ is_init)
                  lab_s lab_t;
  rsr_init_acts : E_s ∩₁ is_init ≡₁ E_t ∩₁ is_init;
}.

Definition reord_simrel := exists a_s, reord_simrel_gen a_s.

Lemma rsr_u2v_e
    (SIMREL : reord_simrel) :
  same_lab_u2v_dom E_t (lab_s ∘ mapper) lab_t.
Proof using.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  assert (EQ : E_t ≡₁ E_t \₁ mapper ↓₁ extra_a a_s ∪₁
              E_t ∩₁ mapper ↓₁ extra_a a_s).
  { split; [| basic_solver].
    apply set_subsetE. basic_solver 11. }
  unfold same_lab_u2v_dom. intros e INE.
  apply EQ in INE. destruct INE as [INE | ISA].
  { unfold same_label_u2v. rewrite (rsr_lab SIMREL); ins.
    desf. }
  apply SIMREL, ISA.
Qed.

Lemma rsr_sub_e s
    (SIMREL : reord_simrel)
    (SUB : s ⊆₁ E_t) :
  mapper ↑₁ s ⊆₁ E_s.
Proof using.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  rewrite (rsr_acts SIMREL). apply set_subset_union_r.
  left. now apply set_collect_mori.
Qed.

Lemma rsr_is_w s
    (SIMREL : reord_simrel)
    (SUB : s ⊆₁ E_t ∩₁ W_t) :
  mapper ↑₁ s ⊆₁ W_s.
Proof using.
  transitivity (mapper ↑₁ (s ∩₁ W_t)).
  { rewrite set_inter_absorb_r; ins.
    rewrite SUB. basic_solver. }
  unfolder. intros x (y & (INS & IS_W) & XEQ). subst x.
  change (W_s (mapper y)) with (is_w (lab_s ∘ mapper) y).
  apply same_lab_u2v_dom_is_w with (s := E_t) (lab2 := lab_t).
  { apply rsr_u2v_e; ins. }
  now apply SUB.
Qed.

Lemma rsr_is_r s
    (SIMREL : reord_simrel)
    (SUB : s ⊆₁ E_t ∩₁ R_t) :
  mapper ↑₁ s ⊆₁ R_s.
Proof using.
  transitivity (mapper ↑₁ (s ∩₁ R_t)).
  { rewrite set_inter_absorb_r; ins.
    rewrite SUB. basic_solver. }
  unfolder. intros x (y & (INS & IS_R) & XEQ). subst x.
  change (R_s (mapper y)) with (is_r (lab_s ∘ mapper) y).
  apply same_lab_u2v_dom_is_r with (s := E_t) (lab2 := lab_t).
  { apply rsr_u2v_e; ins. }
  now apply SUB.
Qed.

(* Lemma G_t_niff_b_max
    (CONT : contigious_actids G_t)
    (INA : E_t a)
    (NINB : ~E_t b) :
  (fun x => ext_sb x b) ⊆₁ E_t ∩₁ same_tid b ∪₁ is_init.
Proof using RSRW_ACTIDS.
  assert (ANINIT : ~is_init a).
  { apply RSRW_ACTIDS. }
  assert (SMTID : tid a = tid b).
  { apply rsr_tid_a_tid_b. }
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
  { exfalso. eapply (rsr_a_b_ord RSRW_ACTIDS); eauto. }
  left. split; [| red; congruence].
  apply ext_sb_dense with (e2 := a); ins.
  rewrite SMTID'. apply RSRW_ACTIDS.
Qed.

Lemma rsr_E_s_sub
    (STRUCT : reord_simrel_rw_struct) :
  E_s ⊆₁ mapper ↑₁ E_t ∪₁ eq a.
Proof using RSRW_ACTIDS.
  destruct (classic (E_t a /\ ~E_t b)) as [NIFF|IFF].
  { desf. rewrite (rsr_actids2 STRUCT); ins. }
  rewrite (rsr_actids1 STRUCT); [basic_solver 6|].
  eapply rsr_E_iff; eauto.
Qed.

Lemma rsr_sub_E_s
    (STRUCT : reord_simrel_rw_struct) :
  mapper ↑₁ E_t ⊆₁ E_s.
Proof using RSRW_ACTIDS.
  destruct (classic (E_t a /\ ~E_t b)) as [NIFF|IFF].
  { desf. rewrite (rsr_actids2 STRUCT); ins. basic_solver. }
  rewrite (rsr_actids1 STRUCT); [basic_solver 6|].
  eapply rsr_E_iff; eauto.
Qed. *)

End SimRel.

Section ReordSimRelInstrs.

Variable X_s X_t : WCore.t.

Variable e2i_s e2i_t : actid -> I2Exec.intr_info.
Variable rmwi : I2Exec.instr_id -> Prop.
Variable ai bi : I2Exec.intr_info.
Variable mapper : actid -> actid.

Notation "'G_t'" := (WCore.G X_t).
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

Notation "'G_s'" := (WCore.G X_s).
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
  rwi_orig_simrel : reord_simrel X_s X_t a b mapper;
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
  mapper ↑ r ⊆ ⦗mapper ↑₁ E_t⦘ ⨾ ext_sb ⨾ ⦗mapper ↑₁ E_t⦘.
Proof using.
  admit.
Admitted.

Lemma mapped_rmw_helper a b
    (SIMREL : reord_simrel_rw_instrs_gen a b)
    (WF : Wf G_t) :
  mapper ↑ rmw_t ⊆ immediate (⦗mapper ↑₁ E_t⦘ ⨾ ext_sb ⨾ ⦗mapper ↑₁ E_t⦘).
Proof using.
  admit.
Admitted.

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
  admit.
Admitted.

End ReordSimRelInstrs.

Module ReordRwSimRelProps.

Section Basic.


Variable X_t X_t' X_s : WCore.t.

Variable G_t G_t' G_s : execution.
Variable a_t b_t : actid.
Variable e2i_s e2i_t : actid -> I2Exec.intr_info.
Variable rmwi : I2Exec.instr_id -> Prop.
Variable ai bi : I2Exec.intr_info.
Variable mapper : actid -> actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'G_t''" := (WCore.G X_t').
Notation "'G_s'" := (WCore.G X_s).

Notation "'lab_t'" := (lab G_t).
Notation "'val_t'" := (val lab_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'same_loc_t'" := (same_loc lab_t).
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
Notation "'loc_t''" := (loc lab_t').
Notation "'same_loc_t''" := (same_loc lab_t').
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
Notation "'loc_s'" := (loc lab_s).
Notation "'same_loc_s'" := (same_loc lab_s).
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
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).

Hypothesis CORR : reord_correct_graphs X_s X_t a_t b_t.

Definition lab_loc l :=
  match l with
  | Aload _ _ l _ | Astore _ _ l _ => Some l
  | Afence _ => None
  end.

Definition lab_is_r l : actid -> Prop :=
  match l with
  | Aload _ _ _ _ => ⊤₁
  | _ => ∅
  end.

Definition lab_is_w l : actid -> Prop :=
  match l with
  | Astore _ _ _ _ => ⊤₁
  | _ => ∅
  end.


Lemma sim_rel_init :
  reord_simrel
    (WCore.Build_t (WCore.init_exec G_s) ∅₂)
    (WCore.Build_t (WCore.init_exec G_t) ∅₂)
    a_t b_t
    id.
Proof using CORR.
  assert (EXA : extra_a
    {|
      WCore.G :=
        WCore.init_exec G_t;
      WCore.sc := ∅₂
    |} a_t b_t a_t ≡₁ ∅).
  { unfold extra_a. desf; ins.
    destruct a as (_ & INB). exfalso.
    apply (rsr_bt_ninit CORR), INB. }
  exists a_t.
  constructor; ins.
  { rewrite (rsr_init_acts CORR). basic_solver. }
  { unfold same_lab_u2v_dom. unfolder.
    intros e IN. apply EXA in IN. destruct IN. }
  { rewrite EXA.
    rewrite set_map_empty, set_minusE, set_compl_empty,
            set_inter_full_r, Combinators.compose_id_right.
    apply CORR. }
  { rewrite EXA. rewrite (rsr_init_acts CORR). basic_solver 11. }
  rewrite EXA, !cross_false_r, !cross_false_l.
  arewrite (singl_rel a_t b_t ∩ (E_t ∩₁ is_init) × (E_t ∩₁ is_init) ≡ ∅₂).
  { enough (~is_init a_t) by basic_solver 12.
    apply CORR. }
  { rewrite !union_false_r, minus_disjoint.
    { unfold sb. ins. rewrite (rsr_init_acts CORR).
      set (r := ⦗E_t ∩₁ is_init⦘ ⨾ ext_sb ⨾ ⦗E_t ∩₁ is_init⦘).
      basic_solver 11. }
    split; [| basic_solver].
    unfold sb; unfolder. ins.
    apply (rsr_at_ninit CORR); desf. }
  { rewrite EXA. basic_solver. }
  rewrite EXA. basic_solver.
Qed.

Lemma rsrw_swap_mapper mapper'
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (MAPPER : eq_dom E_t mapper' mapper) :
  reord_simrel X_s X_t a_t b_t mapper'.
Proof using.
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  exists a_s. constructor; ins.
  { admit. }
  { rewrite set_collect_eq_dom with (g := mapper); ins.
    apply SIMREL. }
  { admit. }
  { admit. }
  { admit. }
  { rewrite set_collect_eq_dom with (g := mapper); ins.
    apply SIMREL. }
  admit.
Admitted.

Lemma simrel_exec_not_a_not_b e l
    (E_NOT_A : e <> a_t)
    (E_NOT_B : e <> b_t)
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' e l) :
  exists mapper' X_s',
    << SIMREL : reord_simrel X_s' X_t' a_t b_t mapper' >> /\
    << STEP : WCore.exec_inst X_s X_s' (mapper' e) l >>.
Proof using.
  (* Generate new actid *)
  assert (NEWE : exists e',
  << NOTIN : ~E_s e' >> /\
  << TID : tid e' = tid e >> /\
  << SB : ⦗E_s ∪₁ eq e'⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq e'⦘ ≡
          sb_s ∪ WCore.sb_delta X_s e' >>).
  { admit. }
  (* unfold hypotheses *)
  red in SIMREL. destruct SIMREL as (a_s & SIMREL).
  destruct NEWE as (e' & NOTIN & NEWTID & NEWSB).
  red in NOTIN, NEWTID, NEWSB.
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  (* Asserts *)
  set (mapper' := upd mapper e e').
  assert (ENOTIN : ~E_t e) by apply ADD.
  assert (EQACTS : E_t' ≡₁ E_t ∪₁ eq e) by apply ADD.
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    rupd. congruence. }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { split; unfolder; intros x (y & YINE & HEQ).
    { exists y; split; ins. rewrite <- MAPEQ; ins. }
    exists y. split; ins. subst mapper'. rupd; ins.
    congruence. }
  assert (LABSUB : eq_dom E_t lab_t' lab_t).
  { rewrite (WCore.add_event_lab ADD). unfolder.
    intros x XINE. rupd. congruence. }
  assert (MAPNEQ : forall x (IN : E_t x), mapper x <> e').
  { intros x XINE F. apply NOTIN, (rsr_codom SIMREL).
    basic_solver. }
  assert (A_PRESERVED : E_t' a_t <-> E_t a_t).
  { split; intros INA.
    { apply ADD in INA. destruct INA; congruence. }
    apply ADD. basic_solver. }
  assert (MAPER_E : mapper' ↑₁ eq e ≡₁ eq e').
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (EXEQ : extra_a X_t a_t b_t a_s ≡₁ extra_a X_t' a_t b_t a_s).
  { unfold extra_a; do 2 desf; exfalso; eauto.
    all: apply n; split; try intro F.
    { apply a. apply EQACTS in F. destruct F; congruence. }
    { apply EQACTS. basic_solver. }
    { apply a, EQACTS. basic_solver. }
    apply EQACTS in a0. destruct a0; congruence. }
  set (G_s' := {|
    acts_set := E_s ∪₁ eq e';
    threads_set := threads_set G_s;
    lab := upd lab_s e' l;
    rf := rf_s ∪ mapper' ↑ (rf_t' ⨾ ⦗eq e' ∩₁ R_t'⦘);
    co := co_s ∪
          mapper' ↑ (⦗eq e' ∩₁ W_t'⦘ ⨾ co_t') ∪
          mapper' ↑ (co_t' ⨾ ⦗eq e' ∩₁ W_t'⦘);
    rmw := mapper' ↑ rmw_t';
    rmw_dep := rmw_dep_s;
    ctrl := ctrl_s;
    data := data_s;
    addr := addr_s;
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).
  assert (SIMREL' : reord_simrel X_s' X_t' a_t b_t mapper').
  { exists a_s. constructor; ins.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { unfolder. intros x y XINE YINE. rewrite !MAPEQ; ins.
        now apply SIMREL. }
      { basic_solver. }
      rewrite MAPER_E, MAPSUB, (rsr_codom SIMREL). basic_solver. }
    { rewrite EQACTS, set_collect_union, MAPER_E, MAPSUB,
              (rsr_codom SIMREL).
      basic_solver. }
    { rewrite EQACTS. apply eq_dom_union. split.
      all: unfolder; unfold compose.
      { intros x XIN. rewrite MAPEQ; ins. now apply SIMREL. }
      now subst mapper'; ins; desf; rupd. }
    { admit. }
    { rewrite EQACTS, <- EXEQ. rewrite (WCore.add_event_lab ADD).
      assert (DISJ : set_disjoint (eq e) (mapper' ↓₁ extra_a X_t a_t b_t a_s)).
      { unfold extra_a; desf. admit. }
      rewrite set_minus_union_l, set_minus_disjoint with (s1 := eq e); ins.
      arewrite (mapper' ↓₁ extra_a X_t a_t b_t a_s ≡₁
                mapper ↓₁ extra_a X_t a_t b_t a_s).
      { admit. }
      apply eq_dom_union; split; subst mapper'.
      { unfolder. intros x (XIN & NXIN).
        unfold compose. rupd; try congruence; eauto.
        now rewrite <- (rsr_lab SIMREL) by basic_solver. }
      unfolder. ins. desf. unfold compose. now rupd. }
    { rewrite EQACTS, set_collect_union, MAPER_E, MAPSUB.
      rewrite (rsr_acts SIMREL), EXEQ. basic_solver 11. }
    { admit. }
    { admit. }
    admit. }
  (* Actual proof *)
  exists mapper', X_s'.
  split; red; ins.
  constructor.
  { exists (option_map mapper' r), (mapper' ↑₁ R1),
           (option_map mapper' w), (mapper' ↑₁ W1), (mapper' ↑₁ W2).
    constructor; ins.
    { subst mapper'. now rupd. }
    { admit. }
    { rewrite <- set_collect_eq_opt.
      apply rsr_is_w with (X_s := X_s') (X_t := X_t')
                          (a_t := a_t) (b_t := b_t).
      all: ins.
      apply set_subset_inter_r; split; try apply ADD.
      rewrite EQACTS. transitivity E_t; [| basic_solver].
      apply ADD. }
    { rewrite <- set_collect_eq_opt.
      apply rsr_sub_e with (X_s := X_s) (X_t := X_t)
                           (a_t := a_t) (b_t := b_t).
      { apply rsrw_swap_mapper; ins. now exists a_s. }
      apply ADD. }
    { admit. }
    { admit. }
    { rewrite <- set_collect_eq_opt.
      apply rsr_is_r with (X_s := X_s') (X_t := X_t')
                          (a_t := a_t) (b_t := b_t).
      all: ins.
      apply set_subset_inter_r; split; try apply ADD.
      rewrite EQACTS. transitivity E_t; [| basic_solver].
      apply ADD. }
    { rewrite <- set_collect_eq_opt.
      apply rsr_sub_e with (X_s := X_s) (X_t := X_t)
                           (a_t := a_t) (b_t := b_t).
      { apply rsrw_swap_mapper; ins. now exists a_s. }
      apply ADD. }
    { admit. }
    { admit. }
    { apply rsr_is_w with (X_s := X_s') (X_t := X_t')
                          (a_t := a_t) (b_t := b_t).
      all: ins.
      apply set_subset_inter_r; split; try apply ADD.
      rewrite EQACTS. transitivity E_t; [| basic_solver].
      apply ADD. }
    { apply rsr_sub_e with (X_s := X_s) (X_t := X_t)
                           (a_t := a_t) (b_t := b_t).
      { apply rsrw_swap_mapper; ins. now exists a_s. }
      apply ADD. }
    { admit. }
    { apply rsr_is_w with (X_s := X_s') (X_t := X_t')
                          (a_t := a_t) (b_t := b_t).
      all: ins.
      apply set_subset_inter_r; split; try apply ADD.
      rewrite EQACTS. transitivity E_t; [| basic_solver].
      apply ADD. }
    { apply rsr_sub_e with (X_s := X_s) (X_t := X_t)
                           (a_t := a_t) (b_t := b_t).
      { apply rsrw_swap_mapper; ins. now exists a_s. }
      apply ADD. }
    { admit. }
    { apply rsr_is_r with (X_s := X_s') (X_t := X_t')
                          (a_t := a_t) (b_t := b_t).
      all: ins.
      apply set_subset_inter_r; split; try apply ADD.
      rewrite EQACTS. transitivity E_t; [| basic_solver].
      apply ADD. }
    { apply rsr_sub_e with (X_s := X_s) (X_t := X_t)
                           (a_t := a_t) (b_t := b_t).
      { apply rsrw_swap_mapper; ins. now exists a_s. }
      apply ADD. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { unfold mapper'. now rupd. }
    { unfold mapper'. now rupd. }
    { admit. }
    { admit. }
    { admit. }
    admit.  }
  { admit. (* RFCOM *) }
  admit.
Admitted.

Lemma simrel_exec_b_step_1
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (BNOTIN : ~E_t b_t) :
  exists a_s l_a X_s'',
    << STEP1 : WCore.exec_inst X_s  X_s'' a_s l_a >>.
Proof using.
  (* Generate new actid *)
  assert (NEWE : exists a_s,
  << NOTIN : ~E_s a_s >> /\
  << TID : tid a_s = tid b_t >> /\
  << SB : ⦗E_s ∪₁ eq a_s⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq a_s⦘ ≡
          sb_s ∪ WCore.sb_delta X_s a_s >>).
  { admit. }
  (* unfold hypotheses *)
  red in SIMREL. destruct SIMREL as (a_s' & SIMREL).
  destruct NEWE as (a_s & NOTIN & NEWTID & NEWSB).
  red in NOTIN, NEWTID, NEWSB.
  (* The proof *)
Admitted.

Lemma simrel_exec_b l
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' b_t l) :
  exists a_s l_a X_s'' mapper' X_s',
    << SIMREL : reord_simrel X_s' X_t' a_t b_t mapper' >> /\
    << STEP1 : WCore.exec_inst X_s  X_s'' a_s l_a >> /\
    << STEP2 : WCore.exec_inst X_s'' X_s' (mapper' b_t) l >>.
Proof using.
  (* unfold hypotheses *)
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  (* Do step 1 *)
  destruct (simrel_exec_b_step_1 SIMREL)
        as (a_s & l_a & X_s'' & STEP1).
  { apply ADD. }
  exists a_s, l_a, X_s''.
  (* Generate new actid *)
  assert (NEWE : exists b_s,
  << NOTIN : ~(E_s ∪₁ eq a_s) b_s >> /\
  << TID : tid b_s = tid b_t >> /\
  << SB : ⦗E_s ∪₁ eq b_s⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq b_s⦘ ≡
          sb_s ∪ WCore.sb_delta X_s b_s >>).
  { admit. }
  red in SIMREL. destruct SIMREL as (a_s' & SIMREL).
  destruct NEWE as (b_s & NOTIN & NEWTID & NEWSB).
  red in NOTIN, NEWTID, NEWSB.
  set (mapper' := upd mapper b_t b_s).
  set (G_s' := {|
    acts_set := E_s ∪₁ eq a_s ∪₁ eq b_s;
    threads_set := threads_set G_s;
    lab := upd (upd lab_s a_s l_a) b_s l;
    rf := rf_s ∪
          mapper' ↑ (rf_t' ⨾ ⦗eq b_t ∩₁ R_t'⦘);
    co := co_s ∪
          mapper' ↑ (⦗eq b_t ∩₁ W_t'⦘ ⨾ co_t') ∪
          mapper' ↑ (co_t' ⨾ ⦗eq b_t ∩₁ W_t'⦘) ∪
          (W_s ∩₁ E_s ∩₁ Loc_s_ (lab_loc l_a)) × (eq a_s ∩₁ lab_is_w l_a);
    rmw := mapper' ↑ rmw_t';
    rmw_dep := rmw_dep_s;
    ctrl := ctrl_s;
    data := data_s;
    addr := addr_s;
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).
Admitted.

Lemma simrel_exec_a w l
    (RF : rf_t' w a_t)
    (STEP : WCore.exec_inst X_t X_t' a_t l) :
  exists mapper' X_s' cmt',
    << SIM : reord_simrel X_s' X_t' a_t b_t mapper' >> /\
    << STEP : WCore.reexec X_s X_s' cmt' >>.
Proof using.
  (* Preamble *)
  (* destruct STEP as [STARTWF ADD]. red in ADD. desf.
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
    eapply rsr_a_neq_b; eauto.
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
  admit. *)
Admitted.

Lemma simrel_reexec cmt
    (SIM : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.reexec X_t X_t' cmt) :
  exists mapper' X_s' cmt',
    << SIM' : reord_simrel X_s' X_t' a_t b_t mapper' >> /\
    << STEP : WCore.reexec X_s X_s' cmt' >>.
Proof using.
  admit.
Admitted.

Lemma simrel_implies_cons
    (CONS : WCore.is_cons G_t (WCore.sc X_t))
    (SIM : reord_simrel X_s X_t a_t b_t mapper) :
  WCore.is_cons G_s (WCore.sc X_s).
Proof using.
  admit.
Admitted.

(* Lemma simrel_term
    (CONS : WCore.is_cons G_t (WCore.sc X_t))
    (SIM : reord_simrel G_t G_s a_t b_t mapper)
    (TERM : machine_terminated G_t traces) :
  << TERM' : machine_terminated G_s traces' >> /\
  << SIM' : ReordCommon.reord G_s G_t traces traces' a b >>.
Proof using.
  admit.
Admitted. *)

End Basic.

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