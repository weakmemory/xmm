Require Import ReordSimrel.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import SubToFullExec.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Section ExecA.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t a_t' b_t' : actid.
Variable mapper : actid -> actid.

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

Hypothesis INV : reord_step_pred X_t a_t b_t.
Hypothesis INV' : reord_step_pred X_t' a_t' b_t'.

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
    (EQA : a_t = a_t')
    (EQB : b_t = b_t')
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' a_t l) :
  exists mapper' X_s' f' dtrmt' cmt',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP : WCore.reexec X_s X_s' f' dtrmt' cmt' >>.
Proof using INV INV'.
  subst a_t'. subst b_t'.
  assert (CORR : reord_step_pred X_t a_t b_t); ins.
  assert (CORR' : reord_step_pred X_t' a_t b_t); ins.
  (* Setup vars *)
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  set (mapper' := upd mapper a_t b_t).
  set (G_s' := {|
    acts_set := E_s;
    threads_set := threads_set G_s;
    lab := upd lab_s b_t l;
    rf := rf_s ⨾ ⦗E_s \₁ eq b_t⦘ ∪
          mapper' ↑ (rf_t' ⨾ ⦗eq a_t⦘);
    co := restr_rel (E_s \₁ eq b_t) co_s ∪
          mapper' ↑ (⦗eq a_t⦘ ⨾ co_t') ∪
          mapper' ↑ (co_t' ⨾ ⦗eq a_t⦘);
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
  set (cmt' := E_s \₁ eq b_t).
  set (dtrmt' := E_s \₁ eq b_t \₁ eq (mapper b_t)).
  set (thrdle' := fun x y =>
    << YNINIT : y <> tid_init >> /\
    << XVAL : x = tid_init \/ x = tid b_t >> /\
    << XYVAL : y = tid b_t -> x = tid_init >>
  ).
  assert (INB' : E_t' b_t).
  { apply (rsr_at_bt_ord CORR'), (WCore.add_event_acts ADD).
    now right. }
  assert (INB : E_t b_t).
  { apply (WCore.add_event_acts ADD) in INB'.
    destruct INB' as [INB' | EQ]; ins.
    exfalso. now apply (rsr_at_neq_bt CORR). }
  assert (WF : Wf G_t) by apply CORR.
  assert (WF' : Wf G_t').
  { apply CORR'. }
  assert (ENINIT : ~is_init a_t) by apply ADD.
  assert (NOTINA : ~E_t a_t).
  { apply ADD. }
  assert (INA : E_t' a_t) by (apply ADD; now right).
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    rupd. congruence. }
  assert (MAPEQ2 : eq_dom E_t mapper mapper').
  { subst mapper'. unfolder. intros x XINE.
    rupd. congruence. }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { split; unfolder; intros x (y & YINE & HEQ).
    { exists y; split; ins. rewrite <- MAPEQ; ins. }
    exists y. split; ins. subst mapper'. rupd; ins.
    congruence. }
  assert (AINS : E_s b_t).
  { apply (rsr_acts SIMREL). unfold extra_a. desf.
    { basic_solver. }
    exfalso; eauto. }
  assert (BINS : E_s (mapper b_t)).
  { admit. }
  assert (NOEXA : extra_a X_t' a_t b_t b_t ≡₁ ∅).
  { unfold extra_a; desf. desf. }
  assert (OLDEXA : extra_a X_t a_t b_t b_t ≡₁ eq b_t).
  { unfold extra_a; desf. exfalso; eauto. }
  assert (MAPER_E : mapper' ↑₁ eq a_t ≡₁ eq b_t).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (ANCODOM : ~ (mapper ↑₁ E_t) b_t).
  { intro FALSO. apply (rsr_codom SIMREL) in FALSO.
    now apply FALSO, OLDEXA. }
  assert (MAPNEQ : forall x (IN : E_t x), mapper x <> b_t).
  { intros x XIN EQ. apply (rsr_codom SIMREL) with (x := b_t).
    { basic_solver. }
    now apply OLDEXA. }
  assert (FMAP : fixset is_init mapper').
  { unfold mapper'. unfolder. ins. rupd; [| congruence].
    now apply (rsr_init SIMREL). }
  assert (INJ : inj_dom E_t' mapper').
  { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
    { unfolder. intros x y XINE YINE. rewrite !MAPEQ; ins.
      now apply SIMREL. }
    { basic_solver. }
    rewrite MAPSUB, MAPER_E. apply set_disjointE.
    split; [| basic_solver]. intros x (IN & EQ).
    subst x. now apply ANCODOM. }
  assert (NEWSBSIM : sb G_s' ≡ mapper' ↑ swap_rel sb_t' (eq b_t ∩₁ E_t') (eq a_t ∩₁ E_t')).
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
    arewrite (mapper' ↑₁ eq b_t ≡₁ eq (mapper b_t)).
    { rewrite set_collect_eq. unfold mapper'. rupd; ins.
      symmetry. apply CORR. }
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
    arewrite (mapper' ↑ sb_t ≡ mapper ↑ sb_t).
    { apply collect_rel_eq_dom.
      eapply eq_dom_mori; eauto. unfold flip.
      unfold sb. basic_solver 11. }
    arewrite (mapper' ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘) ≡₁
              mapper ↑₁ dom_rel (sb_t ⨾ ⦗eq b_t⦘)).
    { apply set_collect_eq_dom.
      eapply eq_dom_mori; eauto. unfold flip.
      unfold sb. basic_solver 11. }
    basic_solver 12. }
  assert (SIMREL' : reord_simrel X_s' X_t' a_t b_t mapper').
  { constructor; ins.
    { rewrite NOEXA. basic_solver. }
    { rewrite (WCore.add_event_acts ADD), set_collect_union,
              MAPSUB, MAPER_E, (rsr_codom SIMREL), NOEXA, OLDEXA.
      basic_solver. }
    { rewrite (WCore.add_event_acts ADD). apply eq_dom_union.
      split; unfold compose; unfolder; intros x XINE.
      { rewrite MAPEQ; ins. now apply SIMREL. }
      subst x. unfold mapper'. rupd.
      rewrite (rsr_at_bt_tid CORR).
      symmetry. eapply eba_tid with (X_s := X_s).
      apply (rsr_as SIMREL), extra_a_some; ins. }
    { rewrite (WCore.add_event_acts ADD), (WCore.add_event_lab ADD).
      apply eq_dom_union; split; subst mapper'.
      { unfolder. intros x XIN.
        unfold compose. rupd; try congruence; eauto.
        rewrite <- (rsr_lab SIMREL); ins. }
      unfolder. ins. desf. unfold compose. now rupd. }
    { rewrite (WCore.add_event_acts ADD), NOEXA,
              set_union_empty_r, set_collect_union,
              MAPSUB, MAPER_E, (rsr_acts SIMREL).
      now rewrite OLDEXA. }
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
      arewrite (mapper' ↑ rf_t ≡ mapper ↑ rf_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rfE (rsr_Gt_wf CORR)). }
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
    unfolder. intros x y (XINE & RPO & YINE).
    destruct XINE as (x' & (AEQ & XIN) & XEQ).
    destruct YINE as (y' & (BEQ & YIN) & YEQ).
    subst y. subst y'. subst x. subst x'.
    assert (RPOIMM : rpo_imm G_s' (mapper' a_t) (mapper' b_t)).
    { apply rpo_to_rpo_imm; ins.
      eapply rsr_as_bs_imm with (X_t := X_t'); eauto. }
    unfold rpo_imm in RPOIMM.
    assert (ANF : ~ (F G_s' (mapper' a_t))).
    { unfold is_f.
      arewrite (lab G_s' (mapper' a_t) = lab_t' a_t).
      { rewrite (WCore.add_event_lab ADD). unfold mapper'.
        ins. now rupd. }
      destruct (rsr_a_t_is_r_or_w CORR') with a_t.
      all: unfold is_r, is_w in *; desf. }
    assert (BNF : ~ (F G_s' (mapper' b_t))).
    { unfold is_f.
      arewrite (lab G_s' (mapper' b_t) = lab_t' b_t).
      { rewrite (WCore.add_event_lab ADD). unfold mapper'.
        ins. rupd; try congruence; eauto.
        change (lab_s (mapper b_t)) with ((lab_s ∘ mapper) b_t).
        rewrite (rsr_lab SIMREL); ins. }
      destruct (rsr_b_t_is_r_or_w CORR') with b_t.
      all: unfold is_r, is_w in *; desf. }
    assert (ANACQ : ~ (Acq G_s' (mapper' a_t))).
    { unfold is_acq, mod.
      arewrite (lab G_s' (mapper' a_t) = lab_t' a_t).
      { rewrite (WCore.add_event_lab ADD). unfold mapper'.
        ins. now rupd. }
      intro FALSO. apply (rsr_at_nacq CORR') with a_t.
      all: try split; ins. }
    assert (BNREL : ~ (Rel G_s' (mapper' b_t))).
    { unfold is_rel, mod.
      arewrite (lab G_s' (mapper' b_t) = lab_t' b_t).
      { rewrite (WCore.add_event_lab ADD). unfold mapper'.
        ins. rupd; try congruence; eauto.
        change (lab_s (mapper b_t)) with ((lab_s ∘ mapper) b_t).
        rewrite (rsr_lab SIMREL); ins. }
      intro FALSO. apply (rsr_bt_nrel CORR') with b_t.
      all: try split; ins. }
    unfolder in RPOIMM. desf.
    { arewrite (E_t' \₁ eq a_t \₁ eq b_t ≡₁ E_t \₁ eq a_t \₁ eq b_t).
      { rewrite (WCore.add_event_acts ADD). clear. basic_solver. }
      clear - MAPEQ SIMREL. unfolder. intros x XIN.
      rewrite MAPEQ; [rewrite (rsr_mid SIMREL) |]; desf. }
    { arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t ∩₁ E_t).
      { clear - INB' INB. basic_solver. }
      rewrite set_collect_eq_dom with (g := mapper); [apply SIMREL |].
      eapply eq_dom_mori; eauto. unfold flip. clear. basic_solver. }
    rewrite (WCore.add_event_acts ADD), set_inter_absorb_r by (clear; basic_solver).
    unfold mapper'. now rewrite set_collect_eq, upds. }
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
      arewrite_false (restr_rel dtrmt' (mapper' ↑ (rf_t' ⨾ ⦗eq a_t⦘))).
      { unfold dtrmt', mapper'. unfolder. ins; desf.
        rewrite upds, updo in *.
        all: congruence. }
      now rewrite union_false_r. }
    { rewrite DT, !restr_union, !restr_relE,
              !seqA, <- !id_inter.
      seq_rewrite <- !id_inter.
      rewrite set_interC.
      arewrite ((E_s \₁ eq b_t) ∩₁ dtrmt' ≡₁ dtrmt').
      { unfold dtrmt'. clear. basic_solver. }
      arewrite_false (⦗dtrmt'⦘ ⨾ mapper' ↑ (⦗eq a_t⦘ ⨾ co_t')).
      { unfold dtrmt', mapper'. unfolder. ins; desf.
        rewrite upds in *. congruence. }
      arewrite_false (mapper' ↑ (co_t' ⨾ ⦗eq a_t⦘) ⨾ ⦗dtrmt'⦘).
      { unfold dtrmt', mapper'. unfolder. ins; desf.
        rewrite upds in *. congruence. }
      now rewrite seq_false_l, seq_false_r, !union_false_r. }
    { rewrite DT, (WCore.add_event_rmw ADD),
              collect_rel_union, restr_union,
              !restr_relE, (rsr_rmw SIMREL).
      arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rmwE (rsr_Gt_wf CORR)). }
      arewrite_false (mapper' ↑ WCore.rmw_delta a_t r ⨾ ⦗dtrmt'⦘).
      { unfold dtrmt', mapper'. unfolder. ins; desf.
        rewrite upds in *. congruence. }
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
        unfold mapper'. rupd. congruence. }
      assert (YNA : y' <> a_t).
      { intro FALSO. destruct YD as [YD _].
        apply YD. subst y'.
        unfold mapper'. now rupd. }
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
      unfold mapper' in *. rewrite updo in *; ins.
      unfold dtrmt'. unfolder; splits; ins.
      { symmetry. eauto. }
      intro FALSO. apply (rsr_inj SIMREL) in FALSO.
      all: ins; congruence. }
    { unfolder in ESB.
      destruct ESB as (_ & FALSO).
      apply NOEXA in FALSO. desf. }
    unfolder in ESB.
    destruct ESB as (FALSO & _).
    apply NOEXA in FALSO. desf. }
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
      arewrite_false (mapper' ↑ (rf_t' ⨾ ⦗eq a_t⦘) ⨾ ⦗E_s \₁ eq b_t⦘).
      { unfolder. intros x y HREL. desf.
        unfold mapper' in *.
        now rewrite upds in *. }
      rewrite seq_false_r, codom_empty, set_union_empty_r.
      seq_rewrite seq_eqvK. unfolder.
      intros x ((XINE & NEQ) & ISR).
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
  assert (STAB : WCore.stable_uncmt_reads_gen X_s' dtrmt' thrdle').
  { constructor; ins.
    { unfolder. subst thrdle'. ins.
      splits; try red; eauto. }
    { unfolder. subst thrdle'. ins. desf. }
    { constructor; unfolder; subst thrdle'.
      { ins; desf; eauto. }
      ins; desf. splits; ins; eauto.
      exfalso; eauto. }
    rewrite seq_union_r.
    arewrite (E_s \₁ dtrmt' ≡₁ eq (mapper b_t) ∪₁ eq b_t).
    { subst dtrmt'. rewrite !set_minus_minus_r.
      basic_solver. }
    rewrite id_union, !seq_union_l.
    arewrite_false (⦗eq b_t⦘ ⨾ rf_s ⨾ ⦗E_s \₁ eq b_t⦘).
    { rewrite <- seqA,
              rsr_rf_from_exa with (X_s := X_s) (X_t := X_t).
      all: eauto.
      clear. basic_solver. }
    arewrite (mapper b_t = mapper' b_t).
    assert (INJ_LMB : inj_dom (
      codom_rel ⦗eq b_t⦘ ∪₁
        dom_rel (rf_t' ⨾ ⦗eq a_t⦘)
      ) mapper'
    ).
    { eapply inj_dom_mori; [| reflexivity | apply SIMREL'].
      unfold flip. rewrite (wf_rfE WF').
      clear - INB'. basic_solver. }
    assert (INJ_LMA : inj_dom (
      codom_rel ⦗eq a_t⦘ ∪₁
        dom_rel (rf_t' ⨾ ⦗eq a_t⦘)
      ) mapper'
    ).
    { eapply inj_dom_mori; [| reflexivity | apply SIMREL'].
      unfold flip. rewrite (wf_rfE WF').
      clear - INA. basic_solver. }
    arewrite_false (⦗eq (mapper' b_t)⦘ ⨾ mapper' ↑ (rf_t' ⨾ ⦗eq a_t⦘)).
    { rewrite <- set_collect_eq, <- collect_rel_eqv.
      seq_rewrite <- collect_rel_seq; auto.
      rewrite <- collect_rel_empty; apply collect_rel_mori; auto.
      rewrite (wf_rfl WF').
      enough (RR : ⦗eq a_t⦘ ⨾ same_loc_t' ⨾ ⦗eq b_t⦘ ⊆ ∅₂).
      { forward apply RR. clear. unfold same_loc. basic_solver. }
      rewrite <- (rsr_at_bt_loc INV'), !set_inter_absorb_r.
      all: clear - INB' INA; basic_solver. }
    arewrite_false (⦗eq b_t⦘ ⨾ mapper' ↑ (rf_t' ⨾ ⦗eq a_t⦘)).
    { rewrite <- MAPER_E, <- collect_rel_eqv,
              <- collect_rel_seq.
      all: auto.
      rewrite <- collect_rel_empty; apply collect_rel_mori; auto.
      rewrite <- restr_relE. apply restr_irrefl_eq.
      apply (rf_irr WF'). }
    rewrite !union_false_r.
    arewrite (rf_s ≡ rf_s ∩ same_tid ∪ rf_s \ same_tid).
    { split; [| clear; basic_solver].
      now rewrite <- (split_rel ⊤₁ ⊤₁). }
    rewrite seq_union_l, !seq_union_r.
    apply union_mori.
    { admit. (* TODO: cons of source *) }
    assert (BTID : tid (mapper' b_t) = tid b_t).
    { symmetry. now apply (rsr_tid' b_t SIMREL'). }
    arewrite (rf_s ⊆ rf_s ⨾ ⦗fun x => ~is_init x⦘).
    { rewrite no_rf_to_init at 1.
      all: eauto using G_s_wf with hahn. }
    arewrite (
      rf_s ⨾ ⦗fun x => ~ is_init x⦘ ⊆
        rf_s ⨾ ⦗set_compl (E_s ∩₁ Tid_ tid_init)⦘
    ).
    { rewrite (rsr_ninit_acts_s INV SIMREL).
      clear. basic_solver. }
    arewrite (
      rf_s ⨾ ⦗set_compl (E_s ∩₁ Tid_ tid_init)⦘ ⊆
      rf_s ⨾ ⦗set_compl (Tid_ tid_init)⦘
    ).
    { rewrite (wf_rfE (G_s_wf INV SIMREL)).
      clear. basic_solver. }
    clear - BTID. unfold thrdle', same_tid, NW.
    unfolder. ins. desf. splits; eauto.
    rewrite <- BTID. congruence. }
  (* The proof *)
  exists mapper', X_s', id, dtrmt', cmt'.
  split; red; ins.
  red. exists thrdle'.
  constructor; ins.
  { subst dtrmt' cmt'. basic_solver. }
  { subst cmt'. basic_solver. }
  { unfold dtrmt'. admit. }
  { admit. }
  { constructor; ins.
    { unfold id; ins. rupd. intro FALSO.
      now apply CMT. }
    { rewrite collect_rel_id. unfold rpo.
      arewrite (restr_rel cmt' (rpo_imm G_s')⁺ ⊆ (restr_rel cmt' (rpo_imm G_s'))⁺).
      { apply restr_rel_ct. unfold upward_closed, cmt'.
        intros x y RPOIMM CMT.
        assert (RPNEQ : forall (EQA : x = b_t) (EQB : y = mapper' b_t), False).
        { intros FALSO1 FALSO2; subst x; subst y.
          eapply (rsr_nrpo SIMREL') with b_t (mapper' b_t).
          unfold X_s'. ins.
          unfolder. splits; eauto.
          { exists a_t; splits; ins.
            unfold mapper'. now rupd. }
          unfold rpo. apply t_step, RPOIMM. }
        apply rpo_imm_in_sb in RPOIMM. split.
        { unfold sb in RPOIMM; unfolder in RPOIMM; desf. }
        intro FALSO; subst x.
        apply (rsr_sb SIMREL') in RPOIMM.
        hahn_rewrite NOEXA in RPOIMM.
        hahn_rewrite cross_false_l in RPOIMM.
        hahn_rewrite cross_false_r in RPOIMM.
        do 2 hahn_rewrite union_false_r in RPOIMM.
        destruct RPOIMM as (x' & y' & RPOIMM & XEQ & YEQ).
        unfold swap_rel in RPOIMM.
        destruct RPOIMM as [[SB BAN] | SWP].
        { apply (WCore.add_event_sb ADD) in SB.
          destruct SB as [SB | DELTA].
          { unfold sb in SB. unfolder in SB. desf.
            unfold mapper' in XEQ.
            rewrite updo in XEQ by congruence.
            eapply MAPNEQ with x'; eauto. }
          unfolder in DELTA. destruct DELTA as (_ & HEQA).
          subst y'. unfold mapper' in YEQ.
          rewrite upds in YEQ. subst y.
          now apply CMT. }
        unfolder in SWP; desf. subst y'.
        apply RPNEQ; congruence. }
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
      unfold mapper'. now rupd. }
    { rewrite collect_rel_id, !restr_union.
      repeat apply inclusion_union_l; [basic_solver | |].
      { unfolder. intros x y ((x' & y' & (EQ & CO) & XEQ & YEQ) & CX & CY).
        exfalso. apply CX. rewrite <- XEQ, <- EQ.
        unfold mapper'. now rupd. }
      unfolder. intros x y ((x' & y' & (CO & EQ) & XEQ & YEQ) & CX & CY).
      exfalso. apply CY. rewrite <- YEQ, <- EQ.
      unfold mapper'. now rupd. }
    { rewrite collect_rel_id, (WCore.add_event_rmw ADD), collect_rel_union,
              restr_union.
      apply inclusion_union_l.
      { arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
        { apply collect_rel_eq_dom' with (s := E_t); ins.
          apply (wf_rmwE (rsr_Gt_wf CORR)). }
        rewrite (rsr_rmw SIMREL). basic_solver 11. }
      unfolder. intros x y ((x' & y' & (RO & EQ) & XEQ & YEQ) & CX & CY).
      exfalso. apply CY. rewrite <- YEQ, <- EQ.
      unfold mapper'. now rupd. }
    arewrite (id ↑₁ cmt' ≡₁ cmt').
    { clear. basic_solver. }
    unfold cmt'. clear. basic_solver. }
  { admit. (* TODO: cons *) }
  apply sub_to_full_exec_listless with (thrdle := thrdle'); ins.
  { eapply G_s_rfc with (X_s := X_s'); eauto. }
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