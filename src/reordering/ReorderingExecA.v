Require Import ReordSimrel.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import SubToFullExec.
Require Import xmm_s_hb.
Require Import Thrdle.
Require Import ConsistencyCommon.
Require Import ConsistencyMonotonicity.
Require Import ConsistencyReadExtent.
Require Import ConsistencyWriteExtent.
Require Import ReorderingRpo ReorderingMapper.
Require Import ReorderingEq.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Section ExecA.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t : actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'G_t''" := (WCore.G X_t').
Notation "'G_s'" := (WCore.G X_s).

Notation "'R' G" := (fun e => is_true (is_r (lab G) e)) (at level 1).
Notation "'F' G" := (fun e => is_true (is_f (lab G) e)) (at level 1).
Notation "'W' G" := (fun e => is_true (is_w (lab G) e)) (at level 1).
Notation "'Acq' G" := (fun e => is_true (is_acq (lab G) e)) (at level 1).
Notation "'Rlx' G" := (fun e => is_true (is_rlx (lab G) e)) (at level 1).
Notation "'Rel' G" := (fun e => is_true (is_rel (lab G) e)) (at level 1).

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
Notation "'W_t'" := (fun x => is_true (is_w lab_t x)).
Notation "'R_t'" := (fun x => is_true (is_r lab_t x)).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).

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
Notation "'rhb_t''" := (rhb G_t').
Notation "'hb_t''" := (hb G_t').
Notation "'rmw_dep_t''" := (rmw_dep G_t').
Notation "'data_t''" := (data G_t').
Notation "'ctrl_t''" := (ctrl G_t').
Notation "'addr_t''" := (addr G_t').
Notation "'W_t''" := (fun x => is_true (is_w lab_t' x)).
Notation "'R_t''" := (fun x => is_true (is_r lab_t' x)).
Notation "'Loc_t_'' l" := (fun e => loc_t' e = l) (at level 1).

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
Notation "'W_s'" := (fun x => is_true (is_w lab_s x)).
Notation "'R_s'" := (fun x => is_true (is_r lab_s x)).
Notation "'F_s'" := (F G_s).
Notation "'vf_s'" := (vf G_s).
Notation "'srf_s'" := (srf G_s).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'Rlx_s'" := (Rlx G_s).
Notation "'Acq_s'" := (Acq G_s).
Notation "'Rel_s'" := (Rel G_s).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).
Notation "'mapper'" := (mapper a_t b_t).

Hypothesis INV : reord_step_pred X_t a_t b_t.
Hypothesis INV' : reord_step_pred X_t' a_t b_t.

Lemma prefix_exec_restr_eq X X' d
    (SUB : d ⊆₁ acts_set (WCore.G X))
    (PFX : SubToFullExec.prefix X X') :
  WCore.exec_restr_eq X X' d.
Proof using.
  constructor.
  all: try now apply PFX.
  { rewrite !set_inter_absorb_l; ins.
    now rewrite <- (prf_acts PFX). }
  { eapply eq_dom_mori; try now apply PFX.
    all: ins.
    unfold flip. rewrite SUB. basic_solver. }
  { now rewrite (prf_rf PFX), restr_restr, set_inter_absorb_l. }
  { now rewrite (prf_co PFX), restr_restr, set_inter_absorb_l. }
  { now rewrite (prf_rmw PFX), restr_restr, set_inter_absorb_l. }
  { now rewrite (prf_data PFX). }
  { now rewrite (prf_ctrl PFX). }
  now rewrite (prf_rmw_dep PFX).
Qed.

Lemma simrel_exec_a l
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' a_t l) :
  exists X_s' f' dtrmt' cmt',
    << SIMREL : reord_simrel X_s' X_t' a_t b_t mapper >> /\
    << STEP : WCore.reexec X_s X_s' f' dtrmt' cmt' >>.
Proof using INV INV'.
  assert (CORR : reord_step_pred X_t a_t b_t); ins.
  assert (CORR' : reord_step_pred X_t' a_t b_t); ins.
  (* Setup vars *)
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  set (G_s' := {|
    acts_set := E_s;
    threads_set := threads_set G_s;
    lab := upd lab_s b_t l;
    rf := rf_s ⨾ ⦗E_s \₁ eq b_t⦘ ∪
          mapper ↑ (rf_t' ⨾ ⦗eq a_t⦘);
    co := restr_rel (E_s \₁ eq b_t) co_s ∪
          mapper ↑ (⦗eq a_t⦘ ⨾ co_t') ∪
          mapper ↑ (co_t' ⨾ ⦗eq a_t⦘);
    rmw := mapper ↑ rmw_t';
    rmw_dep := rmw_dep_s;
    ctrl := ctrl_s;
    data := data_s;
    addr := addr_s;
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).
  set (cmt' := E_s \₁ eq b_t).
  set (dtrmt' := E_s \₁ eq b_t \₁ eq (mapper b_t)).
  set (thrdle' :=
    eq tid_init × set_compl (eq tid_init) ∪
    set_compl (eq (tid b_t)) × eq (tid b_t)
  ).
  assert (NEQ : a_t <> b_t) by apply CORR.
  assert (TEQ : tid a_t = tid b_t) by apply CORR.
  assert (INB' : E_t' b_t).
  { apply (rsr_at_bt_ord CORR'), (WCore.add_event_acts ADD).
    now right. }
  assert (INB : E_t b_t).
  { apply (WCore.add_event_acts ADD) in INB'.
    destruct INB' as [INB' | EQ]; ins. }
  assert (WF : Wf G_t) by apply CORR.
  assert (WF' : Wf G_t').
  { apply CORR'. }
  assert (ENINIT : ~is_init a_t) by apply ADD.
  assert (NOTINA : ~E_t a_t).
  { apply ADD. }
  assert (INA : E_t' a_t) by (apply ADD; now right).
  assert (AINS : E_s b_t).
  { apply (rsr_acts SIMREL). unfold extra_a. desf.
    { basic_solver. }
    exfalso; eauto. }
  assert (BINS : E_s (mapper b_t)).
  { rewrite (rsr_map_bt INB SIMREL).
    apply (rsr_acts SIMREL). left.
    exists b_t. split; eauto using rsr_map_bt. }
  assert (NOEXA : extra_a X_t' a_t b_t b_t ≡₁ ∅).
  { unfold extra_a; desf. desf. }
  assert (OLDEXA : extra_a X_t a_t b_t b_t ≡₁ eq b_t).
  { unfold extra_a; desf. exfalso; eauto. }
  assert (MAPER_E : mapper ↑₁ eq a_t ≡₁ eq b_t).
  { rewrite set_collect_eq. apply set_equiv_single_single.
    eauto with xmm. }
  assert (ANCODOM : ~ (mapper ↑₁ E_t) b_t).
  { intro FALSO. apply (rsr_codom SIMREL) in FALSO.
    now apply FALSO, OLDEXA. }
  assert (MAPNEQ : forall x (IN : E_t x), mapper x <> b_t).
  { intros x XIN EQ. apply (rsr_codom SIMREL) with (x := b_t).
    { basic_solver. }
    now apply OLDEXA. }
  assert (NEWSBSIM : sb G_s' ≡ mapper ↑ swap_rel sb_t' (eq b_t ∩₁ E_t') (eq a_t ∩₁ E_t')).
  { change (sb G_s') with sb_s.
    rewrite (rsr_sb SIMREL), OLDEXA.
    arewrite (eq a_t ∩₁ E_t ≡₁ ∅) by basic_solver.
    arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t) by basic_solver.
    arewrite (eq a_t ∩₁ E_t' ≡₁ eq a_t).
    { rewrite (WCore.add_event_acts ADD). basic_solver. }
    rewrite swap_rel_empty_r, (WCore.add_event_sb ADD),
            swap_rel_union.
    unfold swap_rel. rewrite !collect_rel_union.
    arewrite (sb_t \ eq b_t × eq a_t ≡ sb_t).
    { rewrite minus_disjoint; ins. unfold sb.
      rewrite <- restr_relE, restr_relEE.
      basic_solver. }
    unfold WCore.sb_delta. rewrite <- cross_minus_l.
    rewrite !collect_rel_cross, MAPER_E.
    arewrite (mapper ↑₁ eq b_t ≡₁ eq (mapper b_t)).
    { rewrite set_collect_eq. unfold mapper. rupd; ins. }
    arewrite ((is_init ∪₁ E_t ∩₁ same_tid a_t) \₁ eq b_t ≡₁
              dom_rel (sb_t ⨾ ⦗eq b_t⦘)).
    { rewrite sb_tid_init', seq_union_l, unionC, dom_union,
              set_minus_union_l.
      assert (NINIT : ~is_init b_t) by apply INV.
      arewrite (is_init \₁ eq b_t ≡₁ is_init).
      { split; [basic_solver|]. unfolder.
        ins. split; ins. intro FALSO; congruence. }
      arewrite (same_tid a_t ≡₁ same_tid b_t).
      { unfold same_tid. now rewrite (rsr_at_bt_tid INV). }
      apply set_union_more.
      { unfold sb. split; [|basic_solver 11].
        unfolder. ins. eexists. splits; eauto.
        { apply (rsr_init_acts INV); ins. }
        unfold ext_sb. desf; ins. }
      rewrite wf_sbE, <- seq_eqv_inter_lr, !seqA, <- id_inter.
      rewrite set_inter_absorb_l
          with (s := eq b_t)
            by basic_solver.
      unfolder. unfold same_tid.
      split; intros x HREL; desf; splits; ins.
      all: try now (intro FALSO; desf; eapply sb_irr; eauto).
      eexists; splits; eauto.
      destruct (sb_total G_t)
          with (tid b_t) x b_t
            as [RSB|LSB].
      all: ins; try congruence.
      { unfolder; splits; ins. intro FALSO; destruct x; ins.
        apply (rsr_at_tid CORR). now rewrite (rsr_at_bt_tid CORR). }
      exfalso. apply (rsr_bt_max CORR) with b_t x; ins.
      basic_solver 11. }
    basic_solver 12. }
  assert (SIMREL' : reord_simrel X_s' X_t' a_t b_t mapper).
  { constructor; ins.
    { eapply inj_dom_mori; eauto with xmm.
      red; auto with hahn. }
    { rewrite NOEXA. basic_solver. }
    { rewrite (WCore.add_event_acts ADD), set_collect_union,
              (rsr_codom SIMREL), NOEXA, OLDEXA.
      rewrite set_collect_eq, rsr_mapper_at; auto.
      basic_solver. }
    { apply SIMREL. }
    { eapply eq_dom_mori; eauto with xmm.
      red. auto with hahn. }
    { rewrite (WCore.add_event_acts ADD), (WCore.add_event_lab ADD).
      apply eq_dom_union; split.
      { unfolder. intros x XIN.
        unfold compose. rupd; try congruence; eauto.
        rewrite <- (rsr_lab SIMREL); ins. }
      unfolder. ins. desf. unfold compose.
      rewrite rsr_mapper_at; auto. now rupd. }
    { rewrite (WCore.add_event_acts ADD), NOEXA,
              set_union_empty_r, set_collect_union,
              (rsr_acts SIMREL).
      now rewrite OLDEXA, set_collect_eq, rsr_mapper_at. }
    { now rewrite NOEXA, cross_false_l, cross_false_r,
              !union_false_r. }
    { rewrite NOEXA, set_inter_empty_l,
              (rsr_rf SIMREL), seq_union_l, OLDEXA.
      rewrite (rf_delta_RE (rsr_Gt_wf CORR) ADD).
      arewrite_false ((srf_s ⨾ ⦗eq b_t ∩₁ R_s⦘) ⨾ ⦗E_s \₁ eq b_t⦘).
      { clear. basic_solver. }
      rewrite eqv_empty, seq_false_r, !union_false_r,
              (WCore.add_event_rf ADD), !collect_rel_union.
      arewrite (mapper ↑ rf_t ⨾ ⦗E_s \₁ eq b_t⦘ ≡ mapper ↑ rf_t).
      { split; [clear; basic_solver 7|].
        rewrite (wf_rfE WF), <- OLDEXA, <- (rsr_codom SIMREL).
        clear. basic_solver. }
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      now rewrite collect_rel_empty, !union_false_r. }
    { rewrite NOEXA, set_inter_empty_l, add_max_empty_r,
              union_false_r.
      rewrite (co_deltaE1 WF ADD),
              (co_deltaE2 WF ADD).
      rewrite (WCore.add_event_co ADD). unfold WCore.co_delta.
      rewrite !collect_rel_union, <- !unionA.
      repeat apply union_more; ins.
      rewrite (rsr_co SIMREL), restr_union.
      arewrite (restr_rel (E_s \₁ eq b_t) (mapper ↑ co_t) ≡ mapper ↑ co_t).
      { split; [clear; basic_solver 11 |].
        rewrite <- OLDEXA, <- (rsr_codom SIMREL),
                collect_rel_restr, restr_relE.
        { apply collect_rel_mori; ins. apply WF. }
        eapply inj_dom_mori with (x := E_t); eauto; [| apply SIMREL].
        unfold flip. rewrite (wf_coE WF). clear. basic_solver. }
      rewrite restr_add_max, OLDEXA.
      arewrite (eq b_t ∩₁ W_s ∩₁ (E_s \₁ eq b_t) ≡₁ ∅).
      { clear. basic_solver. }
      rewrite add_max_empty_r, union_false_r.
      apply collect_rel_eq_dom' with (s := E_t); ins.
      apply (wf_coE (rsr_Gt_wf CORR)). }
    { now rewrite (rsr_threads SIMREL), (WCore.add_event_threads ADD). }
    { rewrite (WCore.add_event_ctrl ADD). apply SIMREL. }
    { rewrite (WCore.add_event_data ADD). apply SIMREL. }
    { rewrite (WCore.add_event_addr ADD). apply SIMREL. }
    { rewrite (WCore.add_event_rmw_dep ADD). apply SIMREL. }
    { admit. }
    { unfolder. ins. desf.
      unfold id. auto with xmm. }
    { unfolder. ins. desf.
      rewrite rsr_mapper_bt; auto. }
    unfolder. ins. desf.
    rewrite rsr_mapper_at; auto. }
  assert (PFX : SubToFullExec.prefix (WCore.X_start X_s dtrmt') X_s').
  { assert (DT : dtrmt' ∩₁ E_s ≡₁ dtrmt').
    { unfold dtrmt'. basic_solver. }
    assert (INIT : is_init ⊆₁ dtrmt').
    { unfold dtrmt'.
      rewrite <- sico_init_acts_s; [| | apply INV].
      all: try now (eapply rsr_common; eauto).
      unfolder. intros x XNIT.
      splits; ins.
      all: intro FALSO; subst x.
      { eapply rsr_as_ninit with (X_t := X_t); eauto.
        now apply OLDEXA. }
      assert (TID : (tid ∘ mapper) b_t = tid_init).
      { unfold compose. destruct (mapper b_t); ins. }
      rewrite (rsr_tid SIMREL) in TID; ins.
      apply (rsr_at_tid INV).
      now rewrite (rsr_at_bt_tid INV). }
    unfold X_s'. constructor; ins.
    { now rewrite DT, INIT. }
    { basic_solver. }
    { rewrite DT, INIT, set_unionK.
      unfold dtrmt'. unfolder; ins; desf.
      rupd. congruence. }
    { unfolder. ins. rupd. congruence. }
    { rewrite DT, restr_union, restr_relE,
              !seqA, <- id_inter.
      arewrite ((E_s \₁ eq b_t) ∩₁ dtrmt' ≡₁ dtrmt').
      { unfold dtrmt'. basic_solver. }
      arewrite_false (restr_rel dtrmt' (mapper ↑ (rf_t' ⨾ ⦗eq a_t⦘)));
        [| clear; basic_solver].
      rewrite collect_rel_seqi, collect_rel_eqv,
              set_collect_eq, restr_relE, !seqA.
      rewrite rsr_mapper_at; auto.
      unfold dtrmt'. clear. basic_solver. }
    { rewrite DT, !restr_union, !restr_relE,
              !seqA, <- !id_inter.
      seq_rewrite <- !id_inter.
      rewrite set_interC.
      arewrite ((E_s \₁ eq b_t) ∩₁ dtrmt' ≡₁ dtrmt').
      { unfold dtrmt'. clear. basic_solver. }
      arewrite_false (⦗dtrmt'⦘ ⨾ mapper ↑ (⦗eq a_t⦘ ⨾ co_t')).
      { rewrite collect_rel_seqi, collect_rel_eqv,
                set_collect_eq, rsr_mapper_at; auto.
        unfold dtrmt'. clear. basic_solver. }
      arewrite_false (mapper ↑ (co_t' ⨾ ⦗eq a_t⦘) ⨾ ⦗dtrmt'⦘).
      { rewrite collect_rel_seqi, collect_rel_eqv,
                set_collect_eq, rsr_mapper_at; auto.
        unfold dtrmt'. clear. basic_solver. }
      now rewrite seq_false_l, seq_false_r, !union_false_r. }
    { rewrite DT, (WCore.add_event_rmw ADD),
              collect_rel_union, restr_union,
              !restr_relE, (rsr_rmw SIMREL).
      arewrite_false (mapper ↑ WCore.rmw_delta a_t r ⨾ ⦗dtrmt'⦘).
      { unfold WCore.rmw_delta.
        rewrite collect_rel_cross, set_collect_eq, rsr_mapper_at; auto.
        unfold dtrmt'. clear. basic_solver. }
      now rewrite seq_false_r, union_false_r. }
    { rewrite (rsr_data SIMREL), (rsr_ndata CORR). basic_solver. }
    { rewrite (rsr_ctrl SIMREL), (rsr_nctrl CORR). basic_solver. }
    { rewrite (rsr_addr SIMREL), (rsr_naddr CORR). basic_solver. }
    { rewrite (rsr_rmw_dep SIMREL), (rsr_nrmw_dep CORR). basic_solver. }
    { now rewrite DT. }
    unfold SubExecution.restrict. rewrite wf_sbE; ins.
    unfold sb at 2. ins.
    rewrite !seqA, <- id_inter, set_interC, !DT.
    unfolder. intros x y (XINE & SB & YD).
    splits; ins; [| red in SB; unfolder in SB; desf].
    apply (rsr_sb SIMREL') in SB.
    destruct SB as [[SB | ESB] | ESB].
    { destruct SB as (x' & y' & SB & XEQ & YEQ).
      subst. unfold swap_rel in SB.
      assert (YNB : y' <> b_t).
      { intro FALSO. apply YD. subst y'.
        unfold mapper. rupd. congruence. }
      assert (YNA : y' <> a_t).
      { intro FALSO. destruct YD as [YD _].
        apply YD. subst y'.
        unfold mapper. now rupd. }
      destruct SB as [SB | EX]; [|unfolder in EX; desf].
      destruct SB as [SB BAN].
      assert (XNA : x' <> a_t).
      { intro FALSO; subst. apply (WCore.add_event_sb ADD) in SB.
        destruct SB as [SB|SB].
        all: unfold sb in SB; unfolder in SB.
        all: desf. }
      assert (XNB : x' <> b_t).
      { intro FALSO; subst. apply (WCore.add_event_sb ADD) in SB.
        destruct SB as [SB|SB].
        all: unfold sb in SB; unfolder in SB.
        all: desf.
        eapply (rsr_bt_max INV); ins.
        unfold sb; basic_solver. }
      assert (XIN : E_t x').
      { unfold sb in SB. unfolder in SB.
        destruct SB as (SB & _ & _).
        apply (WCore.add_event_acts ADD) in SB.
        destruct SB; congruence. }
      unfold dtrmt'.
      rewrite rsr_mapper_bt, rsr_mappero; auto.
      rewrite rsr_mappero in XINE; auto.
      unfold dtrmt'. unfolder; splits; auto. }
    { enough (YIN : extra_a X_t' a_t b_t b_t y).
      { exfalso. apply extra_a_none_l in YIN; auto. }
      apply ESB. }
    enough (XIN : extra_a X_t' a_t b_t b_t x).
    { exfalso. apply extra_a_none_l in XIN; auto. }
    apply ESB. }
  assert (STARTWF : WCore.wf (WCore.X_start X_s dtrmt') X_s' cmt').
  { constructor; ins.
    { apply prefix_wf with (X := WCore.X_start X_s dtrmt') (X' := X_s').
      all: ins.
      { rewrite (rsr_data SIMREL), (rsr_ndata INV). basic_solver. }
      { rewrite (rsr_addr SIMREL), (rsr_naddr INV). basic_solver. }
      { rewrite (rsr_ctrl SIMREL), (rsr_nctrl INV). basic_solver. }
      { rewrite (rsr_rmw_dep SIMREL), (rsr_nrmw_dep INV). basic_solver. }
      eapply G_s_wf with (X_s := X_s') (X_t := X_t'); eauto. }
    { apply prefix_exec_restr_eq; ins.
      basic_solver. }
    { unfold rf_complete, G_s', cmt'. ins.
      arewrite ((E_s \₁ eq b_t) ∩₁ E_s ≡₁ E_s \₁ eq b_t).
      { basic_solver. }
      arewrite ((E_s \₁ eq b_t) ∩₁ is_r (upd lab_s b_t l) ≡₁
                (E_s \₁ eq b_t) ∩₁ R_s).
      { unfolder. split; ins; desf; splits; ins.
        all: unfold is_r in *.
        all: rewrite updo in *; congruence. }
      rewrite seq_union_l, seq_union_r, !seqA.
      rewrite codom_union.
      arewrite_false (mapper ↑ (rf_t' ⨾ ⦗eq a_t⦘) ⨾ ⦗E_s \₁ eq b_t⦘).
      { rewrite collect_rel_seqi, collect_rel_eqv,
                set_collect_eq, rsr_mapper_at; auto.
        clear. basic_solver. }
      rewrite seq_false_r, codom_empty, set_union_empty_r.
      seq_rewrite seq_eqvK. unfolder.
      intros x ((XINE & NEQ') & ISR).
      assert (RFC_S : rf_complete G_s).
      { eapply G_s_rfc with (X_t := X_t); eauto. }
      assert (WF_S : Wf G_s).
      { eapply G_s_wf with (X_t := X_t); eauto. }
      destruct RFC_S with x
            as (xw & RF); [split; ins|].
      exists xw; splits; ins.
      { apply (wf_rfE WF_S) in RF.
        unfolder in RF; desf. }
      intro FALSO; subst xw.
      apply (rsr_rf SIMREL) in RF.
      destruct RF as [RFT | SRF].
      { unfolder in RFT.
        destruct RFT as (x' & y' & RFT & EQ & _).
        apply MAPNEQ with x'; ins.
        apply (wf_rfE WF) in RFT.
        unfolder in RFT; desf. }
      unfolder in SRF. destruct SRF as (_ & EXA & _).
      apply OLDEXA in EXA. congruence. }
    { unfold dtrmt', cmt'. basic_solver 11. }
    admit. (* sc... *) }
  assert (STAB : WCore.stable_uncmt_reads_gen X_s' cmt' thrdle').
  { constructor; ins.
    { unfold thrdle'. clear. basic_solver. }
    { unfold thrdle'. clear - INV.
      unfolder. ins. desf.
      now apply (rsr_bt_tid INV). }
    { constructor; unfold thrdle'.
      { clear. basic_solver. }
      clear - INV. unfolder. ins. desf.
      { exfalso. now apply (rsr_bt_tid INV). }
      left. split; auto.
      intro FALSO.
      now apply (rsr_bt_tid INV). }
    arewrite (E_s \₁ cmt' ≡₁ eq b_t).
    { subst cmt'. rewrite !set_minus_minus_r.
      basic_solver. }
    arewrite (
      vf G_s' ⨾ same_tid ⊆
        (vf G_s' ⨾ same_tid) \ same_tid ∪
        (vf G_s' ⨾ same_tid) ∩ same_tid
    ).
    { rewrite unionC.
      rewrite <- split_rel
         with (s := ⊤₁) (s' := ⊤₁).
      reflexivity. }
    rewrite seq_union_l.
    apply union_mori; [| basic_solver].
    unfolder. unfold thrdle', same_tid.
    clear. basic_solver. }
  (* The proof *)
  exists X_s', id, dtrmt', cmt'.
  split; red; ins.
  red. exists thrdle'.
  constructor; ins.
  { assert (BNINI : ~is_init b_t) by apply INV.
    unfold dtrmt'. rewrite <- (rsr_init_acts_s INV SIMREL).
    rewrite rsr_mapper_bt; auto.
    clear - ENINIT BNINI.
    unfolder. ins. desf. splits; congruence. }
  { subst dtrmt' cmt'. basic_solver. }
  { subst cmt'. basic_solver. }
  { rewrite (rsr_sbE INV SIMREL).
    rewrite extra_a_some; auto.
    rewrite !seq_union_l, !seq_union_r.
    rewrite <- cross_inter_r.
    arewrite (eq a_t ∩₁ dtrmt' ≡₁ ∅).
    { unfold dtrmt'. rewrite rsr_mapper_bt; auto.
      clear. basic_solver. }
    rewrite !cross_false_r, seq_false_r, !union_false_r.
    unfold dtrmt'.
    rewrite (rsr_actsE INV SIMREL), extra_a_some; auto.
    rewrite rsr_mapper_bt; auto.
    clear - INB NOTINA INV. unfolder.
    intros x y (SB & (YIN & YEQ) & YNEQ).
    splits; auto.
    { red in SB; unfolder in SB; desf. eauto. }
    { intro FALSO. subst x.
      apply (rsr_bt_max INV) with b_t y; auto.
      basic_solver. }
    intro FALSO. subst x.
    red in SB; unfolder in SB; desf. }
  { admit. }
  { enough (RPOD : dom_rel (rpo G_s' ⨾ ⦗E_s \₁ dtrmt'⦘) ⊆₁ dtrmt').
    { forward apply RPOD. clear. basic_solver 11. }
    unfold dtrmt'.
    assert (EVEQ : E_s \₁ ((E_s \₁ eq b_t) \₁ eq (mapper b_t)) ≡₁ eq b_t ∪₁ eq a_t).
    { rewrite rsr_mapper_bt; auto. rewrite rsr_mapper_bt in BINS; auto.
      rewrite !set_minus_minus_r, set_minusK, set_union_empty_l.
      clear - AINS BINS INV SIMREL INB. basic_solver. }
    rewrite EVEQ, id_union, seq_union_r, dom_union.
    rewrite set_subset_union_l; split.
    { intros x COND.
      unfold dom_rel in COND. destruct COND as [y COND].
      destruct COND as (z & SB & XIN & YIN); subst z y.
      unfold set_minus. splits.
      { apply wf_rpoE in SB.
        destruct SB as (x0 & (EQ & INE) & _); vauto. }
      { apply rpo_in_sb in SB.
        intros FALSE; subst x.
        apply sb_irr in SB; vauto. }
      intros FALSE.
      rewrite rsr_map_bt with (X_s := X_s)
          (X_t := X_t) (a_t := a_t) (b_t := b_t) (mapper := mapper) in FALSE.
      { subst x. apply rpo_in_sb in SB.
        unfold sb in SB. unfolder in SB; desf.
        destruct INV. clear - SB0 rsr_at_bt_sb.
        assert (TRANS : ext_sb a_t a_t).
        { apply ext_sb_trans with (x := a_t)
              (y := b_t) (z := a_t); vauto. }
        apply ext_sb_irr in TRANS; vauto. }
      all : vauto. }
    intros x COND.
    unfold dom_rel in COND. destruct COND as [y COND].
    destruct COND as (z & SB & XIN & YIN); subst z y.
    unfold set_minus. splits.
    { apply wf_rpoE in SB.
      destruct SB as (x0 & (EQ & INE) & _); vauto. }
    { intros FALSE; subst x.
      apply (rsr_nrpo SIMREL') with b_t a_t.
      unfolder; ins. splits; vauto.
      { exists a_t; splits; ins. auto with xmm. }
      exists b_t; splits; ins. auto with xmm. }
    intros FALSE.
    rewrite rsr_map_bt with (X_s := X_s)
      (X_t := X_t) (a_t := a_t) (b_t := b_t) (mapper := mapper) in FALSE.
    { subst x. apply rpo_in_sb in SB.
      apply sb_irr in SB; vauto. }
    all : vauto. }
  { constructor; ins.
    { unfold id; ins. rupd. intro FALSO.
      now apply CMT. }
    { rewrite collect_rel_id. unfold rpo.
      arewrite (restr_rel cmt' (rpo_imm G_s')⁺ ⊆ (restr_rel cmt' (rpo_imm G_s'))⁺).
      { apply restr_rel_ct, rpo_imm_upward_closed.
        unfold cmt'. admit. }
      apply clos_trans_mori. unfold rpo_imm.
      rewrite !restr_union, !restr_relE, !seqA.
      arewrite (⦗cmt'⦘ ⨾ ⦗R G_s' ∩₁ Rlx G_s'⦘ ≡ ⦗R_s ∩₁ Rlx_s⦘ ⨾ ⦗cmt'⦘).
      { unfold cmt'. unfolder.
        split; ins; desf; splits; ins.
        all: unfold is_r, is_rlx, mod in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      arewrite (⦗cmt'⦘ ⨾ ⦗Acq G_s'⦘ ≡ ⦗Acq_s⦘ ⨾ ⦗cmt'⦘).
      { unfold cmt'. unfolder.
        split; ins; desf; splits; ins.
        all: unfold is_acq, mod in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      arewrite (⦗cmt'⦘ ⨾ ⦗F G_s' ∩₁ Rel G_s'⦘ ≡ ⦗F_s ∩₁ Rel_s⦘ ⨾ ⦗cmt'⦘).
      { unfold cmt'. unfolder.
        split; ins; desf; splits; ins.
        all: unfold is_f, is_rel, mod in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      arewrite (⦗F G_s' ∩₁ Acq G_s'⦘ ⨾ ⦗cmt'⦘ ≡ ⦗cmt'⦘ ⨾ ⦗F_s ∩₁ Acq_s⦘).
      { unfold cmt'. unfolder.
        split; ins; desf; splits; ins.
        all: unfold is_f, is_acq, mod in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      arewrite (⦗Rel G_s'⦘ ⨾ ⦗cmt'⦘ ≡ ⦗cmt'⦘ ⨾ ⦗Rel_s⦘).
      { unfold cmt'. unfolder.
        split; ins; desf; splits; ins.
        all: unfold is_rel, mod in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      arewrite (⦗W G_s' ∩₁ Rlx G_s'⦘ ⨾ ⦗cmt'⦘ ≡ ⦗cmt'⦘ ⨾ ⦗W_s ∩₁ Rlx_s⦘).
      { unfold cmt'. unfolder.
        split; ins; desf; splits; ins.
        all: unfold is_w, is_rlx, mod in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      seq_rewrite <- !restr_relE.
      now arewrite (restr_rel cmt' (sb G_s') ⊆ sb_s). }
    { rewrite collect_rel_id, restr_union.
      apply inclusion_union_l; [basic_solver |].
      unfolder. intros x y ((x' & y' & (RF & EQ) & XEQ & YEQ) & CX & CY).
      exfalso. apply CY. rewrite <- YEQ, <- EQ.
      symmetry. auto with xmm. }
    { rewrite collect_rel_id, !restr_union.
      repeat apply inclusion_union_l; [basic_solver | |].
      { unfolder. intros x y ((x' & y' & (EQ & CO) & XEQ & YEQ) & CX & CY).
        exfalso. apply CX. rewrite <- XEQ, <- EQ.
        symmetry. auto with xmm. }
      unfolder. intros x y ((x' & y' & (CO & EQ) & XEQ & YEQ) & CX & CY).
      exfalso. apply CY. rewrite <- YEQ, <- EQ.
      symmetry. auto with xmm. }
    { rewrite collect_rel_id, (WCore.add_event_rmw ADD), collect_rel_union,
              restr_union.
      rewrite (rsr_rmw SIMREL).
      apply inclusion_union_l; [clear; basic_solver 11 |].
      unfolder. intros x y ((x' & y' & (RO & EQ) & XEQ & YEQ) & CX & CY).
      exfalso. apply CY. rewrite <- YEQ, <- EQ.
      symmetry. auto with xmm. }
    arewrite (id ↑₁ cmt' ≡₁ cmt').
    { clear. basic_solver. }
    unfold cmt'. clear. basic_solver. }
  { apply (G_s_rfc INV' SIMREL'). }
  { assert (EXTRA : extra_a X_t' a_t b_t b_t ≡₁ ∅).
    { unfold extra_a. desf. }
    assert (RPOMAP : rpo G_s' ⊆ mapper ↑ (rpo G_t')).
    { apply reord_rpo_map' with (a := a_t) (b := b_t).
      all: rewrite 1?set_unionC with (s := R_t').
      all: try now apply INV'.
      all: try change G_s' with (WCore.G X_s').
      { eapply G_s_wf; eauto. }
      { now rewrite (rsr_acts SIMREL'), EXTRA, set_union_empty_r. }
      { symmetry. apply SIMREL'. }
      { apply SIMREL'. }
      rewrite (rsr_sb SIMREL'), EXTRA,
              cross_false_l, cross_false_r.
      now rewrite !union_false_r. }
    assert (SLOCMAP : sb G_s' ∩ same_loc (lab G_s') ⊆ mapper ↑ (sb_t' ∩ same_loc_t')).
    { apply reord_sbloc' with (a := a_t) (b := b_t).
      all: rewrite 1?set_unionC with (s := R_t').
      all: try now apply INV'.
      all: try change G_s' with (WCore.G X_s').
      { now rewrite (rsr_acts SIMREL'), EXTRA, set_union_empty_r. }
      { symmetry. apply SIMREL'. }
      rewrite (rsr_sb SIMREL'), EXTRA,
              cross_false_l, cross_false_r.
      now rewrite !union_false_r. }
    apply XmmCons.monoton_cons with (G_t := G_t')
                (sc_t := WCore.sc X_t') (m := mapper); eauto.
    all: try now apply SIMREL'.
    all: change (G_s') with (WCore.G X_s').
    { now rewrite (rsr_acts SIMREL'), NOEXA, set_union_empty_r. }
    { rewrite (rsr_rf SIMREL'), EXTRA. basic_solver 8. }
    eapply G_s_wf with (X_t := X_t'); eauto. }
  { arewrite (WCore.reexec_thread X_s' dtrmt' ≡₁ eq (tid b_t)).
    { unfold dtrmt', WCore.reexec_thread. ins.
      rewrite rsr_mapper_bt, !set_minus_minus_r; auto.
      rewrite set_minusK, set_inter_absorb_l; [| basic_solver].
      rewrite set_union_empty_l, set_collect_union, set_union_absorb_r.
      { clear. basic_solver. }
      clear - TEQ. basic_solver. }
    unfold dtrmt'. rewrite (rsr_acts SIMREL), OLDEXA.
    rewrite rsr_mapper_bt; auto.
    clear - TEQ NEQ INB NOTINA. rewrite !set_minus_union_l.
    rewrite !set_minus_minus_l. split; [| basic_solver].
    unfolder.
    intros x' [(x & (XIN & XEQ)) | XEQ]; [| desf; eauto].
    subst x'.
    assert (XNA : x <> a_t) by congruence.
    destruct classic with (x = b_t) as [XEQ | XNB].
    { subst x. right. split; eauto.
      erewrite <- rsr_mapper_tid; eauto.
      all: done. }
    do 2 left. split; eauto. rewrite rsr_mappero; auto.
    apply and_not_or; split; congruence. }
  apply sub_to_full_exec_listless with (thrdle := thrdle'); ins.
  { eapply G_s_rfc with (X_s := X_s'); eauto. }
  { admit. }
  { arewrite (E_s \₁ dtrmt' ∩₁ E_s ≡₁ eq b_t ∪₁ eq (mapper b_t)).
    { rewrite set_minus_inter_r, set_minusK, set_union_empty_r.
      subst dtrmt'.
      rewrite !set_minus_minus_r, set_minusK, set_union_empty_l.
      rewrite !set_inter_absorb_l; ins; [| basic_solver].
      rewrite (rsr_acts SIMREL). basic_solver. }
    apply set_finite_union. split; apply set_finite_eq. }
  { eapply G_s_wf with (X_s := X_s'); eauto. }
  { unfold dtrmt'.
    rewrite set_inter_absorb_r; [| basic_solver].
    rewrite !set_minus_minus_r, set_minusK, set_union_empty_l.
    apply set_subset_union_l. split.
    { unfolder. intros x (INE & XEQ) FALSO. subst x.
      eapply rsr_as_ninit with (x := b_t) (X_t := X_t); eauto.
      { apply extra_a_some; ins. }
      eapply rsr_ninit_acts_s with (X_t := X_t); eauto.
      red; eauto. }
    unfolder. intros x (INE & XEQ) FALSO. subst x.
    assert (INIT : is_init b_t).
    { change (tid (mapper b_t)) with ((tid ∘ mapper) b_t) in FALSO.
      rewrite (rsr_tid SIMREL) in FALSO; ins.
      apply (rsr_ninit_acts CORR). split; ins. }
    apply (rsr_bt_ninit CORR); ins. }
  { admit. (* TODO: sc... *) }
  { now rewrite (rsr_data SIMREL), (rsr_ndata CORR). }
  { now rewrite (rsr_addr SIMREL), (rsr_naddr CORR). }
  { now rewrite (rsr_ctrl SIMREL), (rsr_nctrl CORR). }
  now rewrite (rsr_rmw_dep SIMREL), (rsr_nrmw_dep CORR).
Admitted.

End ExecA.