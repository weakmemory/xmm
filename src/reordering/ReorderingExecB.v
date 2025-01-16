Require Import ReordSimrel ReorderingEq.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import PorfPrefix.
Require Import AddEventWf.
Require Import ConsistencyCommon.
Require Import ConsistencyMonotonicity.
Require Import ConsistencyReadExtent.
Require Import ConsistencyWriteExtent.
Require Import ReorderingFakeSrf.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics Lia.

Section ExecB.

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

Lemma simrel_exec_b_step_1 l_a
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (THREADS : threads_set G_t (tid b_t))
    (CONSIST : WCore.is_cons G_t (WCore.sc X_t))
    (TACTS : E_t' ≡₁ E_t ∪₁ eq b_t)
    (TSTEP : sb_t' ≡ sb_t ∪ WCore.sb_delta b_t E_t)
    (BNOTIN : ~E_t b_t) :
  exists l_a' X_s'',
    << LABU2V : same_label_u2v l_a' l_a >> /\
    << ATID : same_tid b_t b_t >> /\
    << STEP1 : WCore.exec_inst X_s  X_s'' b_t l_a' >> /\
    << RF : rf (WCore.G X_s'') ≡
            rf_s ∪ srf (WCore.G X_s'') ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ >> /\
    << CO : co (WCore.G X_s'') ≡
            co_s ∪ (E_s ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) ×
                (eq b_t ∩₁ WCore.lab_is_w l_a) >> /\
    << RMW : rmw (WCore.G X_s'') ≡ rmw_s >>.
Proof using INV INV'.
  (* Generate new actid *)
  assert (NEWE :
  << NINIT : ~is_init b_t >> /\
  << NOTIN : ~E_s b_t >> /\
  << TID : tid b_t = tid b_t >> /\
  << NEWSB : ⦗E_s ∪₁ eq b_t⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq b_t⦘ ≡
          sb_s ∪ WCore.sb_delta b_t E_s >>).
  { unfold NW. splits; auto.
    { apply INV. }
    { intro FALSO. eapply (rsr_actsE INV) in FALSO.
      all: eauto.
      apply set_subset_single_l in FALSO.
      rewrite extra_a_none_r in FALSO by assumption.
      rewrite set_union_empty_r in FALSO.
      now apply -> set_subset_single_l in FALSO. }
    unfold sb.
    erewrite (rsr_actsE INV); eauto.
    rewrite extra_a_none_r by assumption.
    rewrite set_union_empty_r, <- TACTS.
    apply TSTEP. }
  (* unfold hypotheses *)
  assert (WF_S : Wf G_s).
  { eapply G_s_wf with (X_t := X_t); try red; eauto. }
  assert (ALAB : exists l_a',
    << U2V : same_label_u2v l_a' l_a >> /\
    << VAL : dom_rel (fake_srf G_s b_t l_a ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘) ⊆₁ Val_s_ (WCore.lab_val l_a') >>
  ); [| desf].
  { now apply fake_srf_lab_adjustment. }
  set (G_s'' := {|
    acts_set := E_s ∪₁ eq b_t;
    threads_set := threads_set G_s;
    lab := upd lab_s b_t l_a';
    rf := rf_s ∪
          fake_srf G_s b_t l_a ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘;
    co := co_s ∪
          (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) × (eq b_t ∩₁ WCore.lab_is_w l_a);
    rmw := mapper ↑ rmw_t;
    rmw_dep := rmw_dep_s;
    ctrl := ctrl_s;
    data := data_s;
    addr := addr_s;
  |}).
  set (X_s'' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s'';
  |}).
  assert (LOCEQ : WCore.lab_loc l_a = WCore.lab_loc l_a').
  { unfold WCore.lab_loc, same_label_u2v in *. do 2 desf. }
    set (sb_s' := ⦗E_s ∪₁ eq b_t⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq b_t⦘).
  assert (ISREQ : WCore.lab_is_r l_a ≡₁ WCore.lab_is_r l_a').
  { clear - U2V. unfold same_label_u2v, WCore.lab_is_r in *.
    unfolder. split; ins; desf. }
  assert (SRF_W : exists w,
    eq_opt w ≡₁ dom_rel (fake_srf G_s b_t l_a ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘)).
  { now apply fake_srf_exists. }
  destruct SRF_W as (w & SRF_W).
  assert (CO' :
    co (WCore.G X_s'') ⨾ ⦗E_s⦘ ≡ co_s ⨾ ⦗E_s⦘
  ).
  { ins. clear - NOTIN. basic_solver 11. }
  assert (SB' :
    sb (WCore.G X_s'') ⨾ ⦗eq b_t⦘ ≡
    ⦗E_s⦘ ⨾ sb (WCore.G X_s'') ⨾ ⦗eq b_t⦘
  ).
  { unfold sb. ins. rewrite NEWSB.
    rewrite seq_union_l, seq_union_r. apply union_more.
    { unfold sb. clear - NOTIN. basic_solver. }
    unfold WCore.sb_delta.
    arewrite (E_s ≡₁ E_s ∪₁ is_init).
    { symmetry. apply set_union_absorb_r.
      eapply sico_init_acts_s; [| apply INV].
      eapply rsr_common; eauto. }
    clear. basic_solver 11. }
  assert (SRF' :
    fake_srf G_s b_t l_a ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ ≡
    srf (WCore.G X_s'') ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘
  ).
  { rewrite ISREQ, <- fake_srf_u2v; eauto.
    apply fake_srf_is_srf; auto.
    rewrite SB'. ins.
    rewrite <- seqA.
    rewrite porf_pref_vf
       with (G' := G_s'') (G := G_s).
    all: ins; auto with hahn.
    { basic_solver. }
    { unfolder. ins; desf. rupd. congruence. }
    { unfold sb at 1. ins. rewrite NEWSB.
        clear - NOTIN. basic_solver 11. }
    { clear - NOTIN. basic_solver 11. }
    now rewrite (rsr_rmw SIMREL). }
  assert (TOT : forall ol,
    is_total
    ((E_s ∪₁ eq b_t)
    ∩₁ (is_w (upd lab_s b_t l_a'))
    ∩₁ (fun e => loc (upd lab_s b_t l_a') e = ol))
    (co_s ∪
      (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) × (eq b_t ∩₁ WCore.lab_is_w l_a))
  ).
  { ins.
    rewrite !set_inter_union_l.
    unfold is_total. intros x XIN y YIN NEQ.
    destruct XIN as [XIN | XEQA],
            YIN as [YIN | YEQA].
    { destruct (wf_co_total WF_S) with ol x y as [ORF | ORF]; ins.
      all: try now do 2 left.
      all: try now right; left.
      { unfolder in XIN.
        unfolder. desf. splits; ins.
        all: unfold is_w, loc in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      unfolder in YIN.
      unfolder. desf. splits; ins.
      all: unfold is_w, loc in *.
      all: rewrite updo in *; ins.
      all: congruence. }
    { unfolder in YEQA. unfolder in XIN.
      desf.
      unfold loc, is_w in *.
      rewrite upds in *.
      rewrite updo in * by congruence.
      left; right.
      split; [| unfold WCore.lab_is_w; basic_solver].
      unfolder. splits; ins.
      rewrite LOCEQ. unfold WCore.lab_loc. desf. }
    { unfolder in XEQA. unfolder in YIN.
      desf.
      unfold loc, is_w in *.
      rewrite upds in *.
      rewrite updo in * by congruence.
      right; right.
      split; [| unfold WCore.lab_is_w; basic_solver].
      unfolder. splits; ins.
      rewrite LOCEQ. unfold WCore.lab_loc. desf. }
    unfolder in XEQA. unfolder in YEQA. desf. }
  assert (STEP : WCore.add_event X_s X_s'' b_t l_a').
  { red. exists None, ∅, w, ∅,
      (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a) ∩₁ WCore.lab_is_w l_a).
    constructor; ins.
    { rewrite <- (rsr_at_bt_tid INV).
      apply INV. }
    { rewrite SRF_W, fake_srfD_left.
      basic_solver 11. }
    { rewrite SRF_W, fake_srfE_left.
      basic_solver 11. }
    { rewrite SRF_W, fake_srfl.
      rewrite <- LOCEQ.
      basic_solver 11. }
    { rewrite SRF_W; ins. }
    { basic_solver. }
    { basic_solver. }
    { basic_solver. }
    { rewrite <- LOCEQ.
      basic_solver. }
    { apply expand_transitive.
      { eapply G_s_co_trans with (X_t := X_t); eauto. }
      { unfold upward_closed. intros x y REL XIN.
        destruct XIN as ((YINE & ISW) & HLOC).
        unfolder.
        eapply G_s_coE with (X_t := X_t) in REL.
        all: eauto; try now (red; eauto).
        unfolder in REL. destruct REL as (EX & REL & EY).
        eapply G_s_coD with (X_t := X_t) in REL.
        all: eauto; try now (red; eauto).
        unfolder in REL. destruct REL as (DX & REL & DY).
        eapply G_s_co_l with (X_t := X_t) in REL.
        all: eauto; try now (red; eauto).
        unfold same_loc in REL.
        splits; ins. congruence. }
      rewrite G_s_coE with (X_t := X_t).
      all: eauto; try now (red; eauto).
      unfolder. ins. desf. intro FALSO; desf. }
    { rewrite transp_union. apply functional_union.
      { eapply G_s_rff with (X_t := X_t); eauto. }
      { apply functional_mori with (x := (fake_srf G_s b_t l_a)⁻¹).
        { unfold flip; basic_solver. }
        apply fake_srff; auto. }
      unfold transp.
      intros x (y & RF) (y' & SRF).
      apply (wf_rfE WF_S) in RF.
      clear - RF SRF NOTIN.
      unfolder in SRF. unfolder in RF. desf. }
    { eapply sico_init_acts_s; [| apply INV].
      eapply rsr_common; eauto. }
    { now apply (rsr_threads SIMREL). }
    { now rewrite (rsr_ctrl SIMREL), (rsr_nctrl INV). }
    { enough (EMP : eq_opt w ⊆₁ ∅).
      { clear - EMP. unfolder in *. desf.
        exfalso. eauto. }
      rewrite SRF_W.
      clear - NR U2V. unfolder. ins. desf.
      unfold is_r, WCore.lab_is_r, same_label_u2v in *.
      rewrite upds in *. desf. }
    { split; [| basic_solver].
      clear - NW U2V. unfolder. ins. desf.
      unfold is_w, WCore.lab_is_w, same_label_u2v in *.
      rewrite upds in *. desf. }
    { unfold WCore.rf_delta_R. rewrite SRF_W.
      clear. basic_solver 11. }
    { apply union_more; ins.
      unfold WCore.co_delta.
      rewrite cross_false_r, union_false_l.
      destruct classic with (WCore.lab_is_w l_a ≡₁ ∅) as [EMP|NEMP].
      { now rewrite EMP, !set_inter_empty_r, cross_false_l,
                    cross_false_r. }
      unfold WCore.lab_is_w in *. desf.
      now rewrite !set_inter_full_r. }
    rewrite (rsr_rmw SIMREL).
    basic_solver 11. }
  assert (WF_S' : Wf G_s'').
  { red in STEP; desf.
    eapply add_event_wf with (X' := X_s''); eauto. }
  assert (LABEQ : eq_dom E_t (lab G_s'' ∘ mapper) lab_t).
    { unfold G_s''; ins. unfold eq_dom.
      intros x XIN. unfold compose.
      rewrite updo; ins.
      { apply (rsr_lab SIMREL); eauto. }
      intros FALSE.
      destruct (rsr_codom SIMREL) with (x := mapper x).
      { unfold set_collect. exists x; split; vauto. }
      rewrite FALSE in H0. unfold extra_a in H0.
      basic_solver 21. }
  (* The proof *)
  exists l_a', X_s''.
  splits; ins.
  { constructor; ins.
    { assert (RFC_S : rf_complete G_s).
      { eapply G_s_rfc with (X_t := X_t); eauto. }
      unfold rf_complete. unfold G_s''; ins.
      rewrite set_inter_union_l, SRF', codom_union.
      apply set_union_mori.
      { intros x (XINE & ISR).
        apply RFC_S. split; ins.
        unfold is_r in *. rewrite updo in ISR; ins.
        congruence. }
      intros x (XEQ & ISR).
      assert (XLOC : exists ll, loc (upd lab_s b_t l_a') x = Some ll).
      { unfold is_r in ISR. subst x.
        rewrite upds in ISR. desf.
        eexists. unfold loc. now rewrite upds. }
      destruct XLOC as (ll & XLOC).
      subst x.
      destruct srf_exists
          with (G := G_s'') (r := b_t) (l := ll)
            as (w' & SRF).
      all: ins.
      all: try now apply WF_S'.
      { now right. }
      { left. eapply sico_init_acts_s; [| apply INV | easy].
        eapply rsr_common; eauto. }
      { rewrite set_minus_union_l.
        apply set_finite_union. split.
        { eapply (rsr_fin_s INV); eauto. }
        apply set_finite_mori with (x := eq b_t).
        { unfold flip; basic_solver. }
        apply set_finite_eq. }
      exists w'. unfolder; splits; ins.
      unfold is_r, WCore.lab_is_r in *.
      rewrite upds in ISR. desf. }
    assert (RPOCODOM : codom_rel (⦗eq b_t⦘ ⨾ rpo G_s'') ≡₁ ∅).
    { split; [| basic_solver].
      transitivity (codom_rel (⦗eq b_t⦘ ⨾ sb G_s'')).
      { apply codom_rel_mori. hahn_frame.
        apply rpo_in_sb. }
      arewrite (⦗eq b_t⦘ ⨾ sb G_s'' ≡ ∅₂).
      { split; [| basic_solver].
        unfold sb at 1. ins.
        rewrite NEWSB. rewrite (rsr_sb SIMREL). unfold swap_rel.
        arewrite (eq b_t ∩₁ E_t ≡₁ ∅).
        { split; basic_solver. }
        rels. unfold extra_a. desf.
        { destruct a. destruct BNOTIN; eauto. }
        rels. rewrite wf_sbE. destruct SIMREL.
        unfold extra_a in rsr_codom. desf.
        unfold WCore.sb_delta.
        rewrite seq_union_r.
        assert (PROP1 : ⦗eq b_t⦘ ⨾ mapper ↑ (⦗E_t⦘ ⨾ sb_t ⨾ ⦗E_t⦘) ≡ ∅₂).
        { split; [|basic_solver]. rewrite collect_rel_seqi.
          rewrite collect_rel_eqv.
          rewrite rsr_codom. intros x y PATH.
          destruct PATH as (z1 & (C1 & C2) & (z2 & (C3 & C4))).
          rewrite C1 in C2. rewrite <- C2 in C3.
          destruct NOTIN. destruct C3. destruct H0; vauto. }
        assert (PROP2 : ⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a)
              ∪₁ E_s ∩₁ same_tid b_t) × eq b_t ≡ ∅₂).
        { split; [|basic_solver].
          assert (HELP1 : ⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a)
                ∪₁ E_s ∩₁ same_tid b_t) × eq b_t ≡ ∅₂).
          { split; [| basic_solver].
            arewrite (⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a) ∪₁ E_s ∩₁ same_tid b_t) × eq b_t ⊆
                      ⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a) ∪₁ E_s) × eq b_t).
            { basic_solver. }
            basic_solver 12. }
          rewrite HELP1. basic_solver. }
        rewrite PROP1, PROP2. basic_solver. }
      basic_solver. }
    assert (RPOIMMCODOM : codom_rel (⦗eq b_t⦘ ⨾ rpo_imm G_s'') ≡₁ ∅).
    { split; [| basic_solver]. arewrite (rpo_imm G_s'' ⊆ rpo G_s'').
      destruct RPOCODOM; vauto. }
    assert (RPOIMMST : ⦗E_s⦘ ⨾ rpo_imm G_s'' ≡ rpo_imm G_s'').
    { split; [basic_solver |].
      arewrite (rpo_imm G_s'' ⊆ ⦗acts_set G_s''⦘ ⨾ rpo_imm G_s'').
      { rewrite wf_rpo_immE at 1; basic_solver. }
      unfold G_s'' at 1; ins. intros x y COND.
      destruct COND as (z & (C1 & C2) & INE); subst.
      destruct C2 as [C1 | C2].
      { basic_solver 8. }
      destruct RPOIMMCODOM as (IN & OUT).
      destruct IN with y.
      basic_solver 21. }
    destruct l_a'.
    { apply XmmCons.read_extent with (G_t := G_t)
                  (sc_t := WCore.sc X_t) (a := b_t) (m := mapper); eauto.
      { apply SIMREL; vauto. }
      { unfold G_s''; ins.
        rewrite (rsr_acts SIMREL). unfold extra_a. basic_solver 12. }
      { unfold G_s'', is_r. ins.
        rewrite upds. ins. }
      { admit. (*TODO : finish *) }
      { rewrite (rsr_codom SIMREL). basic_solver 21. }
      { unfold G_s'' at 2; ins.
        rewrite set_minus_union_l. rels.
        rewrite set_minusK. rels.
        arewrite (E_s \₁ eq b_t ≡₁ E_s).
        { split; [basic_solver |].
          intros x XIN. unfold set_minus.
          split; eauto. intros FALSO.
          apply NOTIN; vauto. }
        assert (SBSUB : sb G_s'' ⨾ ⦗E_s⦘ ⊆ mapper ↑ sb_t).
        { unfold sb at 1. ins. rewrite NEWSB.
          rewrite seq_union_l.
          unfold WCore.sb_delta. apply inclusion_union_l.
          { rewrite (rsr_sb SIMREL). arewrite_id ⦗E_s⦘; rels.
            apply inclusion_union_l.
            { apply inclusion_union_l.
              { unfold swap_rel. basic_solver 8. }
              unfold extra_a. desf.
              { destruct a. destruct BNOTIN; eauto. }
              basic_solver 4. }
            unfold extra_a. desf.
            { destruct a. destruct BNOTIN; eauto. }
            basic_solver 4. }
          intros x y COND. destruct COND as (z & (C1 & C2) & INE).
          rewrite <- C2 in INE. destruct INE as (EQ & INE).
          destruct NOTIN; eauto. }
        unfold rpo.
        arewrite ((rpo_imm G_s'')⁺ ⨾ ⦗E_s⦘ ⊆ (rpo_imm G_s'' ⨾ ⦗E_s⦘)⁺).
        { induction 1 as (x0 & (P1 & P2)). destruct P2 as (EQ & COND); subst.
        induction P1 as [x y STT | x].
        { apply ct_step. unfold seq. exists y. splits; vauto. }
          apply ct_begin in P1_2. destruct P1_2 as (x0 & P1 & P2).
          eapply RPOIMMST in P1; vauto.
          destruct P1 as (x1 & (EQ' & COND') & P1); subst.
          apply IHP1_1 in COND'. apply IHP1_2 in COND.
          apply ct_ct. unfold seq. exists x1. splits; vauto. }
        assert (IND1 : (rpo_imm G_s'' ⨾ ⦗E_s⦘) ⊆ mapper ↑ (rpo_imm G_t)⁺).
        { unfold rpo_imm. rewrite !seq_union_l. rewrite !seqA.
          arewrite (⦗R G_s'' ∩₁ Rlx G_s''⦘ ⨾ sb G_s'' ⨾ ⦗F G_s'' ∩₁ Acq G_s''⦘ ⨾ ⦗E_s⦘
                    ⊆ ⦗R G_s'' ∩₁ Rlx G_s''⦘ ⨾ mapper ↑ sb_t ⨾ ⦗F G_s'' ∩₁ Acq G_s''⦘).
          { rewrite <- SBSUB. basic_solver 12. }
          arewrite (sb G_s'' ⨾ ⦗Rel G_s''⦘ ⨾ ⦗E_s⦘
                    ⊆ mapper ↑ sb_t ⨾ ⦗Rel G_s''⦘).
          { rewrite <- SBSUB. basic_solver 12. }
          arewrite (⦗F G_s'' ∩₁ Rel G_s''⦘ ⨾ sb G_s'' ⨾ ⦗W G_s'' ∩₁ Rlx G_s''⦘ ⨾ ⦗E_s⦘
                    ⊆ ⦗F G_s'' ∩₁ Rel G_s''⦘ ⨾ mapper ↑ sb_t ⨾ ⦗W G_s'' ∩₁ Rlx G_s''⦘).
          { rewrite <- SBSUB. basic_solver 12. }
          rewrite SBSUB. rewrite <- ct_step.
          rewrite !collect_rel_union.
          repeat apply union_mori; vauto.
          { rewrite wf_sbE. rewrite !seqA.
            rewrite 2! collect_rel_seqi.
            rewrite collect_rel_eqv.
            rewrite !seqA.
            seq_rewrite <- !id_inter.
            arewrite (R G_s'' ∩₁ Rlx G_s'' ∩₁ mapper ↑₁ E_t ⊆₁
                                  mapper ↑₁ (R_t ∩₁ Rlx G_t ∩₁ E_t)).
            { intros x COND.
              destruct COND as ((COND1 & COND2) & INE).
              destruct INE as [x' [INE MAP]].
              unfold set_collect.
              exists x'. splits; vauto.
              split; vauto.
              split.
              { unfold G_s'' in COND1; ins.
                unfold is_r. destruct (rsr_lab SIMREL) with x'; vauto.
                unfold compose. unfold is_r in COND1.
                rewrite updo in COND1; vauto.
                intros FALSE.
                assert (INMAP : (mapper ↑₁ E_t) b_t).
                { rewrite <- FALSE. unfold set_collect.
                  exists x'; vauto. }
                apply (rsr_codom SIMREL) in INMAP.
                clear - INMAP NOTIN.
                unfold set_minus in INMAP. desf. }
              unfold G_s'' in COND2; ins.
              unfold is_rlx. unfold mod. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_rlx in COND2. unfold mod in COND2.
              rewrite updo in COND2; vauto.
              intros FALSE.
              assert (INMAP : (mapper ↑₁ E_t) b_t).
              { rewrite <- FALSE. unfold set_collect.
                exists x'; vauto. }
              apply (rsr_codom SIMREL) in INMAP.
              clear - INMAP NOTIN.
              unfold set_minus in INMAP. desf. }
            arewrite (mapper ↑₁ E_t ∩₁ (F G_s'' ∩₁ Acq G_s'')
                          ⊆₁ mapper ↑₁ (E_t ∩₁ F G_t ∩₁ Acq G_t)).
            { intros x COND.
              destruct COND as (COND1 & COND2).
              destruct COND1 as [x' [INE MAP]].
              unfold set_collect.
              exists x'. splits; vauto.
              split; vauto.
              split.
              { unfold G_s'' in COND2; ins. }
              destruct COND2 as (COND1 & COND2).
              { unfold G_s'' in COND1; ins.
                unfold is_f. destruct (rsr_lab SIMREL) with x'; vauto.
                unfold compose. unfold is_f in COND1.
                rewrite updo in COND1; vauto.
                intros FALSE.
                assert (INMAP : (mapper ↑₁ E_t) b_t).
                { rewrite <- FALSE. unfold set_collect.
                  exists x'; vauto. }
                apply (rsr_codom SIMREL) in INMAP.
                clear - INMAP NOTIN.
                unfold set_minus in INMAP. desf. }
              destruct COND2 as (COND1 & COND2).
              unfold G_s'' in COND2; ins.
              unfold is_acq. unfold mod. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_acq in COND2. unfold mod in COND2.
              rewrite updo in COND2; vauto.
              intros FALSE.
              assert (INMAP : (mapper ↑₁ E_t) b_t).
              { rewrite <- FALSE. unfold set_collect.
                exists x'; vauto. }
              apply (rsr_codom SIMREL) in INMAP.
              clear - INMAP NOTIN.
              unfold set_minus in INMAP. desf. }
            rewrite !collect_rel_seq.
            { rewrite !collect_rel_eqv; basic_solver 8. }
            { assert (IN1 : dom_rel ⦗E_t ∩₁ (F G_t ∩₁ Acq G_t)⦘ ⊆₁ E_t).
              { basic_solver. }
              assert (IN2 : codom_rel sb_t ⊆₁ E_t).
              { rewrite wf_sbE. basic_solver. }
              rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
              eapply (rsr_inj SIMREL). }
            assert (IN1 : codom_rel ⦗R_t ∩₁ Rlx G_t ∩₁ E_t⦘ ⊆₁ E_t).
            { basic_solver 8. }
            assert (IN2 : dom_rel (sb_t ⨾ ⦗E_t ∩₁ (F G_t ∩₁ Acq G_t)⦘) ⊆₁ E_t).
            { rewrite wf_sbE. basic_solver 8. }
            rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
            eapply (rsr_inj SIMREL). }
          { rewrite wf_sbE.
            rewrite 2! collect_rel_seqi.
            rewrite collect_rel_eqv.
            seq_rewrite <- !id_inter.
            arewrite (Acq G_s'' ∩₁ mapper ↑₁ E_t
                          ⊆₁ mapper ↑₁ (Acq G_t ∩₁ E_t)).
            { intros x COND.
              destruct COND as (COND1 & COND2).
              destruct COND2 as [x' [INE MAP]].
              unfold set_collect.
              exists x'. splits; vauto.
              split; vauto.
              unfold G_s'' in COND1; ins.
              unfold is_acq. unfold mod. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_acq in COND1. unfold mod in COND1.
              rewrite updo in COND1; vauto.
              intros FALSE.
              assert (INMAP : (mapper ↑₁ E_t) b_t).
              { rewrite <- FALSE. unfold set_collect.
                exists x'; vauto. }
              apply (rsr_codom SIMREL) in INMAP.
              clear - INMAP NOTIN.
              unfold set_minus in INMAP. desf. }
            rewrite !collect_rel_seq.
            { rewrite !collect_rel_eqv; basic_solver 8. }
            { assert (IN1 : dom_rel ⦗E_t⦘ ⊆₁ E_t).
              { basic_solver. }
              assert (IN2 : codom_rel sb_t ⊆₁ E_t).
              { rewrite wf_sbE. basic_solver. }
              rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
              eapply (rsr_inj SIMREL). }
            assert (IN1 : codom_rel ⦗Acq G_t ∩₁ E_t⦘ ⊆₁ E_t).
            { basic_solver 8. }
            assert (IN2 : dom_rel (sb_t ⨾ ⦗E_t⦘) ⊆₁ E_t).
            { rewrite wf_sbE. basic_solver 8. }
            rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
            eapply (rsr_inj SIMREL). }
          { rewrite wf_sbE.
            rewrite 2! collect_rel_seqi.
            rewrite collect_rel_eqv. rewrite !seqA.
            seq_rewrite <- !id_inter.
            arewrite (mapper ↑₁ E_t ∩₁ Rel G_s''
                          ⊆₁ mapper ↑₁ (E_t ∩₁ Rel G_t)).
            { intros x COND.
              destruct COND as (COND1 & COND2).
              destruct COND1 as [x' [INE MAP]].
              unfold set_collect.
              exists x'. splits; vauto.
              split; vauto.
              unfold G_s'' in COND2; ins.
              unfold is_rel, mod. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_rel, mod in COND2.
              rewrite updo in COND2; vauto.
              intros FALSE.
              assert (INMAP : (mapper ↑₁ E_t) b_t).
              { rewrite <- FALSE. unfold set_collect.
                exists x'; vauto. }
              apply (rsr_codom SIMREL) in INMAP.
              clear - INMAP NOTIN.
              unfold set_minus in INMAP. desf. }
            rewrite !collect_rel_seq.
            { rewrite !collect_rel_eqv; basic_solver 8. }
            { assert (IN1 : dom_rel ⦗E_t ∩₁ Rel G_t⦘ ⊆₁ E_t).
              { basic_solver. }
              assert (IN2 : codom_rel sb_t ⊆₁ E_t).
              { rewrite wf_sbE. basic_solver. }
              rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
              eapply (rsr_inj SIMREL). }
            assert (IN1 : dom_rel (sb_t ⨾ ⦗E_t ∩₁ Rel G_t⦘) ⊆₁ E_t).
            { rewrite wf_sbE. basic_solver 8. }
            assert (IN2 : codom_rel ⦗E_t⦘ ⊆₁ E_t).
            { basic_solver 8. }
            rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
            eapply (rsr_inj SIMREL). }
          rewrite wf_sbE.
          rewrite 2! collect_rel_seqi.
          rewrite collect_rel_eqv. rewrite !seqA.
          seq_rewrite <- !id_inter.
          arewrite (F G_s'' ∩₁ Rel G_s'' ∩₁ mapper ↑₁ E_t
                          ⊆₁ mapper ↑₁ (F G_t ∩₁ Rel G_t ∩₁ E_t)).
          { intros x COND.
            destruct COND as (COND1 & (y & COND2)).
            destruct COND2 as (COND2 & COND3).
            destruct COND1 as [ISF INREL].
            unfold set_collect.
            exists y. splits; vauto.
            split; vauto.
            split.
            { unfold G_s'' in COND2; ins.
              unfold is_f. destruct (rsr_lab SIMREL) with y; vauto.
              unfold compose. unfold is_f in ISF.
              rewrite updo in ISF; vauto.
              intros FALSE.
              assert (INMAP : (mapper ↑₁ E_t) b_t).
              { rewrite <- FALSE. unfold set_collect.
                exists y; vauto. }
              apply (rsr_codom SIMREL) in INMAP.
              clear - INMAP NOTIN.
              unfold set_minus in INMAP. desf. }
            unfold is_rel, mod in INREL.
            unfold is_rel, mod.
            destruct (rsr_lab SIMREL) with y; vauto.
            unfold compose. unfold is_rel, mod in INREL.
            unfold G_s'' in INREL; ins.
            rewrite updo in INREL; vauto.
            intros FALSE.
            assert (INMAP : (mapper ↑₁ E_t) b_t).
            { rewrite <- FALSE. unfold set_collect.
              exists y; vauto. }
            apply (rsr_codom SIMREL) in INMAP.
            clear - INMAP NOTIN.
            unfold set_minus in INMAP. desf. }
          arewrite (mapper ↑₁ E_t ∩₁ (W G_s'' ∩₁ Rlx G_s'')
                        ⊆₁ mapper ↑₁ (E_t ∩₁ W G_t ∩₁ Rlx G_t)).
          { intros x COND.
            destruct COND as (COND1 & COND2).
            destruct COND1 as [x' [INE MAP]].
            destruct COND2 as [ISW INRLX].
            unfold set_collect.
            exists x'. splits; vauto.
            split.
            { split; vauto.
              unfold G_s'' in ISW; ins.
              unfold is_w. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_w in ISW.
              rewrite updo in ISW; vauto.
              intros FALSE.
              assert (INMAP : (mapper ↑₁ E_t) b_t).
              { rewrite <- FALSE. unfold set_collect.
                exists x'; vauto. }
              apply (rsr_codom SIMREL) in INMAP.
              clear - INMAP NOTIN.
              unfold set_minus in INMAP. desf. }
            unfold G_s'' in INRLX; ins.
            unfold is_rlx. unfold mod. destruct (rsr_lab SIMREL) with x'; vauto.
            unfold compose. unfold is_rlx in INRLX. unfold mod in INRLX.
            rewrite updo in INRLX; vauto.
            intros FALSE.
            assert (INMAP : (mapper ↑₁ E_t) b_t).
            { rewrite <- FALSE. unfold set_collect.
              exists x'; vauto. }
            apply (rsr_codom SIMREL) in INMAP.
            clear - INMAP NOTIN.
            unfold set_minus in INMAP. desf. }
          rewrite !collect_rel_seq.
          { rewrite !collect_rel_eqv; basic_solver 8. }
          { assert (IN1 : dom_rel ⦗E_t ∩₁ (W_t ∩₁ Rlx G_t)⦘ ⊆₁ E_t).
            { basic_solver. }
            assert (IN2 : codom_rel sb_t ⊆₁ E_t).
            { rewrite wf_sbE. basic_solver. }
            rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
            eapply (rsr_inj SIMREL). }
          assert (IN1 : codom_rel ⦗F G_t ∩₁ Rel G_t ∩₁ E_t⦘ ⊆₁ E_t).
          { basic_solver 8. }
          assert (IN2 : dom_rel (sb_t ⨾ ⦗E_t ∩₁ (W_t ∩₁ Rlx G_t)⦘) ⊆₁ E_t).
          { rewrite wf_sbE. basic_solver 8. }
          rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
          eapply (rsr_inj SIMREL). }
        assert (IND2 : mapper ↑ (rpo_imm G_t)⁺ ⨾ (rpo_imm G_s'' ⨾ ⦗E_s⦘)
                          ⊆ mapper ↑ (rpo_imm G_t)⁺).
        { assert (TRIN : mapper ↑ (rpo_imm G_t)⁺ ⨾ mapper ↑ (rpo_imm G_t)⁺
                            ⊆ mapper ↑ (rpo_imm G_t)⁺).
          { intros x y PATH. destruct PATH as (x0 & P1 & P2).
            unfold collect_rel in P1, P2. unfold collect_rel.
            destruct P1 as (x' & x0' & (P1 & M1 & M2)).
            destruct P2 as (x0'' & y' & (P2 & M3 & M4)).
            exists x', y'. splits; vauto.
            assert (EQ : x0'' = x0').
            { apply (rsr_inj SIMREL); vauto.
              { apply ct_begin in P2.
                destruct P2 as (x1 & P2 & P3).
                destruct INV.
                apply wf_rpo_immE in P2; vauto.
                destruct P2 as (x2 & INE & REST).
                apply INE. }
              apply ct_end in P1.
              destruct P1 as (x1 & P1 & P1').
              destruct INV.
              apply wf_rpo_immE in P1'; vauto.
              destruct P1' as (x2 & P3 & (x3 & P4 & (EQ & P5))); vauto. }
            subst. apply ct_ct.
            unfold seq. exists x0'. splits; vauto. }
          rewrite <- TRIN at 2. apply seq_mori; vauto. }
        apply inclusion_t_ind_right; vauto. }
      { split; [| basic_solver]. unfold sb at 1.
        ins. rewrite NEWSB. rewrite inter_union_l.
        rewrite seq_union_r. rewrite codom_union.
        rewrite (rsr_sb SIMREL).
        unfold swap_rel.
        arewrite (eq b_t ∩₁ E_t ≡₁ ∅).
        { split; basic_solver. }
        rels. unfold extra_a. desf.
        { destruct a. destruct BNOTIN; eauto. }
        rels. rewrite wf_sbE. destruct SIMREL.
        unfold extra_a in rsr_codom. desf.
        unfold WCore.sb_delta.
        assert (EMP1 : ⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a)
              ∪₁ E_s ∩₁ same_tid b_t) × eq b_t ⊆ ∅₂).
        { arewrite (⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a) ∪₁ E_s ∩₁ same_tid b_t) × eq b_t ⊆
                    ⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a) ∪₁ E_s) × eq b_t).
          { basic_solver. }
          basic_solver 12. }
        assert (EMP2 : ⦗eq b_t⦘ ⨾ mapper ↑ (⦗E_t⦘ ⨾ sb_t ⨾ ⦗E_t⦘)
              ∩ same_loc (upd lab_s b_t (Aload ex0 o0 l0 v)) ⊆ ∅₂).
        { arewrite (⦗eq b_t⦘ ⨾ mapper ↑ (⦗E_t⦘ ⨾ sb_t ⨾ ⦗E_t⦘) ∩ same_loc (upd lab_s b_t (Aload ex0 o0 l0 v)) ⊆
                    ⦗eq b_t⦘ ⨾ mapper ↑ (⦗E_t⦘ ⨾ sb_t ⨾ ⦗E_t⦘)).
          rewrite collect_rel_seqi. rewrite collect_rel_eqv.
          rewrite rsr_codom. basic_solver 12. }
        assert (PROP1 : codom_rel (⦗eq b_t⦘ ⨾ mapper ↑ (⦗E_t⦘ ⨾ sb_t ⨾ ⦗E_t⦘)
                ∩ same_loc (upd lab_s b_t (Aload ex0 o0 l0 v))) ⊆₁ ∅).
        { arewrite (codom_rel (⦗eq b_t⦘ ⨾ mapper ↑ (⦗E_t⦘ ⨾ sb_t ⨾ ⦗E_t⦘)
                ∩ same_loc (upd lab_s b_t (Aload ex0 o0 l0 v))) ⊆₁
                  codom_rel (⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a) ∪₁ E_s) × eq b_t)).
          { apply codom_rel_mori. rewrite EMP2; vauto. }
          rewrite <- codom_empty. apply codom_rel_mori.
          basic_solver 21. }
        assert (PROP2 : codom_rel (⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a) ∪₁ E_s ∩₁ same_tid b_t) × eq b_t
                ∩ same_loc (upd lab_s b_t (Aload ex0 o0 l0 v))) ⊆₁ ∅).
        { rewrite <- codom_empty. apply codom_rel_mori.
          basic_solver 21. }
        rewrite PROP1, PROP2; basic_solver. }
      { unfold sb at 1. ins. rewrite NEWSB.
        rewrite inter_union_l.
        rewrite (rsr_sb SIMREL).
        unfold swap_rel.
        arewrite (eq b_t ∩₁ E_t ≡₁ ∅).
        { split; basic_solver. }
        rels. unfold extra_a. desf.
        { destruct a. destruct BNOTIN; eauto. }
        rels. rewrite wf_sbE. destruct SIMREL.
        unfold extra_a in rsr_codom. desf.
        unfold WCore.sb_delta.
        arewrite (⦗(E_s ∪₁ eq b_t) \₁ eq b_t⦘ ⊆ ⦗E_s⦘).
        { intros x y XIN. unfold set_minus in XIN.
          destruct XIN as (EQ & (COND1 & COND2)). split; eauto.
          destruct COND1; vauto. }
        rewrite seq_union_l. apply inclusion_union_l.
        { intros x y COND. destruct COND as (z & (SB & SL) & INE).
          destruct SB as (x' & z' & SB & M1 & M2).
          destruct INE as (EQ & INE).
          unfold collect_rel. exists x', z'. splits; vauto.
          split; vauto. unfold same_loc in SL.
          unfold loc in SL. do 2 rewrite updo in SL.
          { unfold same_loc. unfold loc.
            arewrite (lab_t x' = lab_s (mapper x')).
            { destruct rsr_lab with x'.
              { destruct SB as (x0 & (C1 & EQ) & C2); vauto. }
              basic_solver. }
            arewrite (lab_t z' = lab_s (mapper z')).
            { destruct rsr_lab with z'.
              { destruct SB as (x0 & C1 & (x2 & C2 & (IN & EQ))); vauto. }
              basic_solver. }
            vauto. }
          { intros FALSO.
            rewrite FALSO in INE; vauto. }
          { intros FALSO.
            destruct SB as (x0 & (C1 & EQ) & C2).
            rewrite <- FALSO in NOTIN.
            destruct NOTIN. destruct rsr_acts.
            apply H0. left. vauto. }
          intros FALSO.
          destruct SB as (x0 & (C1 & EQ) & C2).
          rewrite <- FALSO in NOTIN.
          destruct NOTIN. destruct rsr_acts.
          apply H0. left. vauto. }
        basic_solver 21. }
      { unfold G_s'' at 1; ins. unfold WCore.lab_is_r.
        desf. rewrite set_inter_full_r.
        rewrite (rsr_rf SIMREL).
        unfold extra_a. desf.
        { exfalso. eapply BNOTIN. apply a. }
        rewrite set_inter_empty_l; rels.
        apply union_more; eauto.
        unfold WCore.lab_is_r in SRF'.
        rewrite set_inter_full_r in SRF'.
        rewrite SRF'; vauto. }
      { unfold G_s''; ins. unfold WCore.lab_is_w.
        desf. rewrite set_inter_empty_r. rels.
        rewrite (rsr_co SIMREL).
        unfold add_max. unfold extra_a at 2. desf.
        { exfalso. eapply BNOTIN. apply a. }
        rewrite set_inter_empty_l; rels. }
      destruct INV; eauto. }
    { apply XmmCons.write_extent with (G_t := G_t)
                  (sc_t := WCore.sc X_t) (a := b_t) (m := mapper); eauto.
      { apply SIMREL; vauto. }
      { unfold G_s''; ins.
        rewrite (rsr_acts SIMREL). unfold extra_a. basic_solver 12. }
      { unfold G_s''; ins. unfold upd.
        unfold is_w. basic_solver. }
      { rewrite (rsr_codom SIMREL). basic_solver 21. }
      { unfold G_s'' at 2; ins.
        rewrite set_minus_union_l. rels.
        rewrite set_minusK. rels.
        arewrite (E_s \₁ eq b_t ≡₁ E_s).
        { split; [basic_solver |].
          intros x XIN. unfold set_minus.
          split; eauto. intros FALSO.
          apply NOTIN; vauto. }
        assert (SBSUB : sb G_s'' ⨾ ⦗E_s⦘ ⊆ mapper ↑ sb_t).
        { unfold sb at 1. ins. rewrite NEWSB.
          rewrite seq_union_l.
          unfold WCore.sb_delta. apply inclusion_union_l.
          { rewrite (rsr_sb SIMREL). arewrite_id ⦗E_s⦘; rels.
            apply inclusion_union_l.
            { apply inclusion_union_l.
              { unfold swap_rel. basic_solver 8. }
              unfold extra_a. desf.
              { destruct a. destruct BNOTIN; eauto. }
              basic_solver 4. }
            unfold extra_a. desf.
            { destruct a. destruct BNOTIN; eauto. }
            basic_solver 4. }
          intros x y COND. destruct COND as (z & (C1 & C2) & INE).
          rewrite <- C2 in INE. destruct INE as (EQ & INE).
          destruct NOTIN; eauto. }
        unfold rpo.
        arewrite ((rpo_imm G_s'')⁺ ⨾ ⦗E_s⦘ ⊆ (rpo_imm G_s'' ⨾ ⦗E_s⦘)⁺).
        { induction 1 as (x0 & (P1 & P2)). destruct P2 as (EQ & COND); subst.
          induction P1 as [x y STT | x].
          { apply ct_step. unfold seq. exists y. splits; vauto. }
            apply ct_begin in P1_2. destruct P1_2 as (x0 & P1 & P2).
            eapply RPOIMMST in P1; vauto.
            destruct P1 as (x1 & (EQ' & COND') & P1); subst.
            apply IHP1_1 in COND'. apply IHP1_2 in COND.
            apply ct_ct. unfold seq. exists x1. splits; vauto. }
        assert (IND1 : (rpo_imm G_s'' ⨾ ⦗E_s⦘) ⊆ mapper ↑ (rpo_imm G_t)⁺).
        { unfold rpo_imm. rewrite !seq_union_l. rewrite !seqA.
          arewrite (⦗R G_s'' ∩₁ Rlx G_s''⦘ ⨾ sb G_s'' ⨾ ⦗F G_s'' ∩₁ Acq G_s''⦘ ⨾ ⦗E_s⦘
                    ⊆ ⦗R G_s'' ∩₁ Rlx G_s''⦘ ⨾ mapper ↑ sb_t ⨾ ⦗F G_s'' ∩₁ Acq G_s''⦘).
          { rewrite <- SBSUB. basic_solver 12. }
          arewrite (sb G_s'' ⨾ ⦗Rel G_s''⦘ ⨾ ⦗E_s⦘
                    ⊆ mapper ↑ sb_t ⨾ ⦗Rel G_s''⦘).
          { rewrite <- SBSUB. basic_solver 12. }
          arewrite (⦗F G_s'' ∩₁ Rel G_s''⦘ ⨾ sb G_s'' ⨾ ⦗W G_s'' ∩₁ Rlx G_s''⦘ ⨾ ⦗E_s⦘
                    ⊆ ⦗F G_s'' ∩₁ Rel G_s''⦘ ⨾ mapper ↑ sb_t ⨾ ⦗W G_s'' ∩₁ Rlx G_s''⦘).
          { rewrite <- SBSUB. basic_solver 12. }
          rewrite SBSUB. rewrite <- ct_step.
          rewrite !collect_rel_union.
          repeat apply union_mori; vauto.
          { rewrite wf_sbE. rewrite !seqA.
            rewrite 2! collect_rel_seqi.
            rewrite collect_rel_eqv.
            rewrite !seqA.
            seq_rewrite <- !id_inter.
            arewrite (R G_s'' ∩₁ Rlx G_s'' ∩₁ mapper ↑₁ E_t ⊆₁
                                  mapper ↑₁ (R_t ∩₁ Rlx G_t ∩₁ E_t)).
            { intros x COND.
              destruct COND as ((COND1 & COND2) & INE).
              destruct INE as [x' [INE MAP]].
              unfold set_collect.
              exists x'. splits; vauto.
              split; vauto.
              split.
              { unfold G_s'' in COND1; ins.
                unfold is_r. destruct (rsr_lab SIMREL) with x'; vauto.
                unfold compose. unfold is_r in COND1.
                rewrite updo in COND1; vauto.
                intros FALSE.
                assert (INMAP : (mapper ↑₁ E_t) b_t).
                { rewrite <- FALSE. unfold set_collect.
                  exists x'; vauto. }
                apply (rsr_codom SIMREL) in INMAP.
                clear - INMAP NOTIN.
                unfold set_minus in INMAP. desf. }
              unfold G_s'' in COND2; ins.
              unfold is_rlx. unfold mod. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_rlx in COND2. unfold mod in COND2.
              rewrite updo in COND2; vauto.
              intros FALSE.
              assert (INMAP : (mapper ↑₁ E_t) b_t).
              { rewrite <- FALSE. unfold set_collect.
                exists x'; vauto. }
              apply (rsr_codom SIMREL) in INMAP.
              clear - INMAP NOTIN.
              unfold set_minus in INMAP. desf. }
            arewrite (mapper ↑₁ E_t ∩₁ (F G_s'' ∩₁ Acq G_s'')
                          ⊆₁ mapper ↑₁ (E_t ∩₁ F G_t ∩₁ Acq G_t)).
            { intros x COND.
              destruct COND as (COND1 & COND2).
              destruct COND1 as [x' [INE MAP]].
              unfold set_collect.
              exists x'. splits; vauto.
              split; vauto.
              split.
              { unfold G_s'' in COND2; ins. }
              destruct COND2 as (COND1 & COND2).
              { unfold G_s'' in COND1; ins.
                unfold is_f. destruct (rsr_lab SIMREL) with x'; vauto.
                unfold compose. unfold is_f in COND1.
                rewrite updo in COND1; vauto.
                intros FALSE.
                assert (INMAP : (mapper ↑₁ E_t) b_t).
                { rewrite <- FALSE. unfold set_collect.
                  exists x'; vauto. }
                apply (rsr_codom SIMREL) in INMAP.
                clear - INMAP NOTIN.
                unfold set_minus in INMAP. desf. }
              destruct COND2 as (COND1 & COND2).
              unfold G_s'' in COND2; ins.
              unfold is_acq. unfold mod. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_acq in COND2. unfold mod in COND2.
              rewrite updo in COND2; vauto.
              intros FALSE.
              assert (INMAP : (mapper ↑₁ E_t) b_t).
              { rewrite <- FALSE. unfold set_collect.
                exists x'; vauto. }
              apply (rsr_codom SIMREL) in INMAP.
              clear - INMAP NOTIN.
              unfold set_minus in INMAP. desf. }
            rewrite !collect_rel_seq.
            { rewrite !collect_rel_eqv; basic_solver 8. }
            { assert (IN1 : dom_rel ⦗E_t ∩₁ (F G_t ∩₁ Acq G_t)⦘ ⊆₁ E_t).
              { basic_solver. }
              assert (IN2 : codom_rel sb_t ⊆₁ E_t).
              { rewrite wf_sbE. basic_solver. }
              rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
              eapply (rsr_inj SIMREL). }
            assert (IN1 : codom_rel ⦗R_t ∩₁ Rlx G_t ∩₁ E_t⦘ ⊆₁ E_t).
            { basic_solver 8. }
            assert (IN2 : dom_rel (sb_t ⨾ ⦗E_t ∩₁ (F G_t ∩₁ Acq G_t)⦘) ⊆₁ E_t).
            { rewrite wf_sbE. basic_solver 8. }
            rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
            eapply (rsr_inj SIMREL). }
          { rewrite wf_sbE.
            rewrite 2! collect_rel_seqi.
            rewrite collect_rel_eqv.
            seq_rewrite <- !id_inter.
            arewrite (Acq G_s'' ∩₁ mapper ↑₁ E_t
                          ⊆₁ mapper ↑₁ (Acq G_t ∩₁ E_t)).
            { intros x COND.
              destruct COND as (COND1 & COND2).
              destruct COND2 as [x' [INE MAP]].
              unfold set_collect.
              exists x'. splits; vauto.
              split; vauto.
              unfold G_s'' in COND1; ins.
              unfold is_acq. unfold mod. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_acq in COND1. unfold mod in COND1.
              rewrite updo in COND1; vauto.
              intros FALSE.
              assert (INMAP : (mapper ↑₁ E_t) b_t).
              { rewrite <- FALSE. unfold set_collect.
                exists x'; vauto. }
              apply (rsr_codom SIMREL) in INMAP.
              clear - INMAP NOTIN.
              unfold set_minus in INMAP. desf. }
            rewrite !collect_rel_seq.
            { rewrite !collect_rel_eqv; basic_solver 8. }
            { assert (IN1 : dom_rel ⦗E_t⦘ ⊆₁ E_t).
              { basic_solver. }
              assert (IN2 : codom_rel sb_t ⊆₁ E_t).
              { rewrite wf_sbE. basic_solver. }
              rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
              eapply (rsr_inj SIMREL). }
            assert (IN1 : codom_rel ⦗Acq G_t ∩₁ E_t⦘ ⊆₁ E_t).
            { basic_solver 8. }
            assert (IN2 : dom_rel (sb_t ⨾ ⦗E_t⦘) ⊆₁ E_t).
            { rewrite wf_sbE. basic_solver 8. }
            rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
            eapply (rsr_inj SIMREL). }
          { rewrite wf_sbE.
            rewrite 2! collect_rel_seqi.
            rewrite collect_rel_eqv. rewrite !seqA.
            seq_rewrite <- !id_inter.
            arewrite (mapper ↑₁ E_t ∩₁ Rel G_s''
                          ⊆₁ mapper ↑₁ (E_t ∩₁ Rel G_t)).
            { intros x COND.
              destruct COND as (COND1 & COND2).
              destruct COND1 as [x' [INE MAP]].
              unfold set_collect.
              exists x'. splits; vauto.
              split; vauto.
              unfold G_s'' in COND2; ins.
              unfold is_rel, mod. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_rel, mod in COND2.
              rewrite updo in COND2; vauto.
              intros FALSE.
              assert (INMAP : (mapper ↑₁ E_t) b_t).
              { rewrite <- FALSE. unfold set_collect.
                exists x'; vauto. }
              apply (rsr_codom SIMREL) in INMAP.
              clear - INMAP NOTIN.
              unfold set_minus in INMAP. desf. }
            rewrite !collect_rel_seq.
            { rewrite !collect_rel_eqv; basic_solver 8. }
            { assert (IN1 : dom_rel ⦗E_t ∩₁ Rel G_t⦘ ⊆₁ E_t).
              { basic_solver. }
              assert (IN2 : codom_rel sb_t ⊆₁ E_t).
              { rewrite wf_sbE. basic_solver. }
              rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
              eapply (rsr_inj SIMREL). }
            assert (IN1 : dom_rel (sb_t ⨾ ⦗E_t ∩₁ Rel G_t⦘) ⊆₁ E_t).
            { rewrite wf_sbE. basic_solver 8. }
            assert (IN2 : codom_rel ⦗E_t⦘ ⊆₁ E_t).
            { basic_solver 8. }
            rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
            eapply (rsr_inj SIMREL). }
          rewrite wf_sbE.
          rewrite 2! collect_rel_seqi.
          rewrite collect_rel_eqv. rewrite !seqA.
          seq_rewrite <- !id_inter.
          arewrite (F G_s'' ∩₁ Rel G_s'' ∩₁ mapper ↑₁ E_t
                          ⊆₁ mapper ↑₁ (F G_t ∩₁ Rel G_t ∩₁ E_t)).
          { intros x COND.
            destruct COND as (COND1 & (y & COND2)).
            destruct COND2 as (COND2 & COND3).
            destruct COND1 as [ISF INREL].
            unfold set_collect.
            exists y. splits; vauto.
            split; vauto.
            split.
            { unfold G_s'' in COND2; ins.
              unfold is_f. destruct (rsr_lab SIMREL) with y; vauto.
              unfold compose. unfold is_f in ISF.
              rewrite updo in ISF; vauto.
              intros FALSE.
              assert (INMAP : (mapper ↑₁ E_t) b_t).
              { rewrite <- FALSE. unfold set_collect.
                exists y; vauto. }
              apply (rsr_codom SIMREL) in INMAP.
              clear - INMAP NOTIN.
              unfold set_minus in INMAP. desf. }
            unfold is_rel, mod in INREL.
            unfold is_rel, mod.
            destruct (rsr_lab SIMREL) with y; vauto.
            unfold compose. unfold is_rel, mod in INREL.
            unfold G_s'' in INREL; ins.
            rewrite updo in INREL; vauto.
            intros FALSE.
            assert (INMAP : (mapper ↑₁ E_t) b_t).
            { rewrite <- FALSE. unfold set_collect.
              exists y; vauto. }
            apply (rsr_codom SIMREL) in INMAP.
            clear - INMAP NOTIN.
            unfold set_minus in INMAP. desf. }
          arewrite (mapper ↑₁ E_t ∩₁ (W G_s'' ∩₁ Rlx G_s'')
                        ⊆₁ mapper ↑₁ (E_t ∩₁ W G_t ∩₁ Rlx G_t)).
          { intros x COND.
            destruct COND as (COND1 & COND2).
            destruct COND1 as [x' [INE MAP]].
            destruct COND2 as [ISW INRLX].
            unfold set_collect.
            exists x'. splits; vauto.
            split.
            { split; vauto.
              unfold G_s'' in ISW; ins.
              unfold is_w. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_w in ISW.
              rewrite updo in ISW; vauto.
              intros FALSE.
              assert (INMAP : (mapper ↑₁ E_t) b_t).
              { rewrite <- FALSE. unfold set_collect.
                exists x'; vauto. }
              apply (rsr_codom SIMREL) in INMAP.
              clear - INMAP NOTIN.
              unfold set_minus in INMAP. desf. }
            unfold G_s'' in INRLX; ins.
            unfold is_rlx. unfold mod. destruct (rsr_lab SIMREL) with x'; vauto.
            unfold compose. unfold is_rlx in INRLX. unfold mod in INRLX.
            rewrite updo in INRLX; vauto.
            intros FALSE.
            assert (INMAP : (mapper ↑₁ E_t) b_t).
            { rewrite <- FALSE. unfold set_collect.
              exists x'; vauto. }
            apply (rsr_codom SIMREL) in INMAP.
            clear - INMAP NOTIN.
            unfold set_minus in INMAP. desf. }
          rewrite !collect_rel_seq.
          { rewrite !collect_rel_eqv; basic_solver 8. }
          { assert (IN1 : dom_rel ⦗E_t ∩₁ (W_t ∩₁ Rlx G_t)⦘ ⊆₁ E_t).
            { basic_solver. }
            assert (IN2 : codom_rel sb_t ⊆₁ E_t).
            { rewrite wf_sbE. basic_solver. }
            rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
            eapply (rsr_inj SIMREL). }
          assert (IN1 : codom_rel ⦗F G_t ∩₁ Rel G_t ∩₁ E_t⦘ ⊆₁ E_t).
          { basic_solver 8. }
          assert (IN2 : dom_rel (sb_t ⨾ ⦗E_t ∩₁ (W_t ∩₁ Rlx G_t)⦘) ⊆₁ E_t).
          { rewrite wf_sbE. basic_solver 8. }
          rewrite IN1, IN2. arewrite (E_t ∪₁ E_t ≡₁ E_t); [basic_solver|].
          eapply (rsr_inj SIMREL). }
        assert (IND2 : mapper ↑ (rpo_imm G_t)⁺ ⨾ (rpo_imm G_s'' ⨾ ⦗E_s⦘)
                          ⊆ mapper ↑ (rpo_imm G_t)⁺).
        { assert (TRIN : mapper ↑ (rpo_imm G_t)⁺ ⨾ mapper ↑ (rpo_imm G_t)⁺
                            ⊆ mapper ↑ (rpo_imm G_t)⁺).
          { intros x y PATH. destruct PATH as (x0 & P1 & P2).
            unfold collect_rel in P1, P2. unfold collect_rel.
            destruct P1 as (x' & x0' & (P1 & M1 & M2)).
            destruct P2 as (x0'' & y' & (P2 & M3 & M4)).
            exists x', y'. splits; vauto.
            assert (EQ : x0'' = x0').
            { apply (rsr_inj SIMREL); vauto.
              { apply ct_begin in P2.
                destruct P2 as (x1 & P2 & P3).
                destruct INV.
                apply wf_rpo_immE in P2; vauto.
                destruct P2 as (x2 & INE & REST).
                apply INE. }
              apply ct_end in P1.
              destruct P1 as (x1 & P1 & P1').
              destruct INV.
              apply wf_rpo_immE in P1'; vauto.
              destruct P1' as (x2 & P3 & (x3 & P4 & (EQ & P5))); vauto. }
            subst. apply ct_ct.
            unfold seq. exists x0'. splits; vauto. }
          rewrite <- TRIN at 2. apply seq_mori; vauto. }
        apply inclusion_t_ind_right; vauto. }
      { split; [| basic_solver]. unfold sb at 1.
        ins. rewrite NEWSB. rewrite inter_union_l.
        rewrite seq_union_r. rewrite codom_union.
        rewrite (rsr_sb SIMREL).
        unfold swap_rel.
        arewrite (eq b_t ∩₁ E_t ≡₁ ∅).
        { split; basic_solver. }
        rels. unfold extra_a. desf.
        { destruct a. destruct BNOTIN; eauto. }
        rels. rewrite wf_sbE. destruct SIMREL.
        unfold extra_a in rsr_codom. desf.
        unfold WCore.sb_delta.
        assert (EMP1 : ⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a)
              ∪₁ E_s ∩₁ same_tid b_t) × eq b_t ⊆ ∅₂).
        { arewrite (⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a) ∪₁ E_s ∩₁ same_tid b_t) × eq b_t ⊆
                    ⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a) ∪₁ E_s) × eq b_t).
          { basic_solver. }
          basic_solver 12. }
        assert (EMP2 : ⦗eq b_t⦘ ⨾ mapper ↑ (⦗E_t⦘ ⨾ sb_t ⨾ ⦗E_t⦘)
              ∩ same_loc (upd lab_s b_t (Astore s0 o0 l0 v)) ⊆ ∅₂).
        { arewrite (⦗eq b_t⦘ ⨾ mapper ↑ (⦗E_t⦘ ⨾ sb_t ⨾ ⦗E_t⦘) ∩ same_loc (upd lab_s b_t (Astore s0 o0 l0 v)) ⊆
                    ⦗eq b_t⦘ ⨾ mapper ↑ (⦗E_t⦘ ⨾ sb_t ⨾ ⦗E_t⦘)).
          rewrite collect_rel_seqi. rewrite collect_rel_eqv.
          rewrite rsr_codom. basic_solver 12. }
        assert (PROP1 : codom_rel (⦗eq b_t⦘ ⨾ mapper ↑ (⦗E_t⦘ ⨾ sb_t ⨾ ⦗E_t⦘)
                ∩ same_loc (upd lab_s b_t (Astore s0 o0 l0 v))) ⊆₁ ∅).
        { arewrite (codom_rel (⦗eq b_t⦘ ⨾ mapper ↑ (⦗E_t⦘ ⨾ sb_t ⨾ ⦗E_t⦘)
                ∩ same_loc (upd lab_s b_t (Astore s0 o0 l0 v))) ⊆₁
                  codom_rel (⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a) ∪₁ E_s) × eq b_t)).
          { apply codom_rel_mori. rewrite EMP2; vauto. }
          rewrite <- codom_empty. apply codom_rel_mori.
          basic_solver 21. }
        assert (PROP2 : codom_rel (⦗eq b_t⦘ ⨾ ((fun a : actid => is_init a) ∪₁ E_s ∩₁ same_tid b_t) × eq b_t
                ∩ same_loc (upd lab_s b_t (Astore s0 o0 l0 v))) ⊆₁ ∅).
        { rewrite <- codom_empty. apply codom_rel_mori.
          basic_solver 21. }
        rewrite PROP1, PROP2; basic_solver. }
      { unfold sb at 1. ins. rewrite NEWSB.
        rewrite inter_union_l.
        rewrite (rsr_sb SIMREL).
        unfold swap_rel.
        arewrite (eq b_t ∩₁ E_t ≡₁ ∅).
        { split; basic_solver. }
        rels. unfold extra_a. desf.
        { destruct a. destruct BNOTIN; eauto. }
        rels. rewrite wf_sbE. destruct SIMREL.
        unfold extra_a in rsr_codom. desf.
        unfold WCore.sb_delta.
        arewrite (⦗(E_s ∪₁ eq b_t) \₁ eq b_t⦘ ⊆ ⦗E_s⦘).
        { intros x y XIN. unfold set_minus in XIN.
          destruct XIN as (EQ & (COND1 & COND2)). split; eauto.
          destruct COND1; vauto. }
        rewrite seq_union_l. apply inclusion_union_l.
        { intros x y COND. destruct COND as (z & (SB & SL) & INE).
          destruct SB as (x' & z' & SB & M1 & M2).
          destruct INE as (EQ & INE).
          unfold collect_rel. exists x', z'. splits; vauto.
          split; vauto. unfold same_loc in SL.
          unfold loc in SL. do 2 rewrite updo in SL.
          { unfold same_loc. unfold loc.
            arewrite (lab_t x' = lab_s (mapper x')).
            { destruct rsr_lab with x'.
              { destruct SB as (x0 & (C1 & EQ) & C2); vauto. }
              basic_solver. }
            arewrite (lab_t z' = lab_s (mapper z')).
            { destruct rsr_lab with z'.
              { destruct SB as (x0 & C1 & (x2 & C2 & (IN & EQ))); vauto. }
              basic_solver. }
            vauto. }
          { intros FALSO.
            rewrite FALSO in INE; vauto. }
          { intros FALSO.
            destruct SB as (x0 & (C1 & EQ) & C2).
            rewrite <- FALSO in NOTIN.
            destruct NOTIN. destruct rsr_acts.
            apply H0. left. vauto. }
          intros FALSO.
          destruct SB as (x0 & (C1 & EQ) & C2).
          rewrite <- FALSO in NOTIN.
          destruct NOTIN. destruct rsr_acts.
          apply H0. left. vauto. }
        basic_solver 21. }
      { unfold G_s'' at 1; ins. unfold WCore.lab_is_r.
        desf. rewrite set_inter_empty_r. rels.
        rewrite (rsr_rf SIMREL).
        split; vauto. apply inclusion_union_l; vauto.
        unfold extra_a. desf.
        { exfalso. eapply BNOTIN. apply a. }
        rewrite set_inter_empty_l; rels. }
      { unfold G_s''; ins. rewrite (rsr_co SIMREL).
        rewrite unionA.
        apply union_more; eauto.
        rewrite extra_a_none_r; vauto.
        rewrite set_inter_empty_l.
        rewrite add_max_empty_r.
        unfold WCore.lab_is_w.
        desf. rewrite set_inter_full_r.
        rels. apply cross_more; eauto.
        arewrite ((fun a : actid => is_w (upd lab_s b_t (Astore s o l v)) a)
                      ∩₁ (E_s ∪₁ eq b_t) \₁ eq b_t ≡₁ (fun a : actid => is_w (upd lab_s b_t (Astore s o l v)) a)
                                ∩₁ E_s).
        { split; [basic_solver |].
          intros x XIN. unfold set_minus.
          split.
          { clear - XIN. apply set_inter_union_r.
            left; vauto. }
          clear - XIN NOTIN. intros FALSE.
          apply NOTIN. destruct XIN as (WR & INE); vauto. }
          arewrite ((fun a : actid => is_w (upd lab_s b_t (Astore s o l v)) a)
                        ∩₁ E_s ≡₁ W_s ∩₁ E_s).
          { split.
            { intros x XIN. destruct XIN as (WR & INE).
              unfold is_w in WR. rewrite updo in WR.
              { basic_solver. }
              clear - INE NOTIN. intros FALSO.
              basic_solver. }
            intros x XIN. unfold is_w. split.
            { rewrite updo.
              { clear - XIN. destruct XIN as (WR & INE).
                unfold is_w in WR; vauto. }
              intros FALSO. apply NOTIN.
              destruct XIN as (WR & INE); vauto. }
            destruct XIN as (WR & INE); vauto. }
          rewrite !set_interA.
          arewrite (E_s ∩₁ Loc_s_ (WCore.lab_loc (Astore s0 o0 l0 v0))
                      ≡₁ E_s ∩₁ same_loc (upd lab_s b_t (Astore s o l v)) b_t); vauto.
          split.
          { intros x XIN. destruct XIN as (INE & LOC).
            split; vauto. unfold same_loc.
            destruct classic with (P := x = b_t) as [EQ | NEQ]; vauto.
            unfold loc. rewrite upds; vauto.
            rewrite updo; vauto.
            basic_solver 21. }
          intros x XIN. destruct XIN as (INE & LOC).
          split; vauto. unfold same_loc in LOC.
          destruct classic with (P := x = b_t) as [EQ | NEQ]; vauto.
          unfold loc in *. rewrite upds in LOC; vauto.
          rewrite updo in LOC; vauto.
          basic_solver 21. }
      apply INV. }
    admit. (*TODO : fence*) }
  { apply union_more; ins. }
  { now rewrite set_interC with (s := E_s). }
  subst X_s''. subst G_s''. ins.
  now rewrite (rsr_rmw SIMREL).
Admitted.

Lemma simrel_exec_b l l_a
    (NACQ : ~mode_le Oacq (WCore.lab_mode l_a))
    (NEQLOC : WCore.lab_loc l <> WCore.lab_loc l_a)
    (EQA : a_t = a_t')
    (EQB : b_t = b_t')
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' b_t l)
    (CONSIST : WCore.is_cons G_t (WCore.sc X_t)) :
  exists l_a' a_s X_s'' mapper' X_s',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP1 : WCore.exec_inst X_s  X_s'' a_s l_a' >> /\
    << STEP2 : WCore.exec_inst X_s'' X_s' (mapper' b_t) l >>.
Proof using.
  assert (CORR : reord_step_pred X_t a_t b_t); auto.
  assert (CORR' : reord_step_pred X_t' a_t b_t) by congruence.
  (* unfold hypotheses *)
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  (* Do step 1 *)
  assert (NINB : ~E_t b_t) by apply ADD.
  assert (STEP1 : exists l_a' X_s'',
    << LABU2V : same_label_u2v l_a' l_a >> /\
    << ATID : same_tid b_t b_t >> /\
    << STEPA : WCore.exec_inst X_s  X_s'' b_t l_a' >> /\
    << RF' : rf (WCore.G X_s'') ≡
            rf_s ∪ srf (WCore.G X_s'') ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ >> /\
    << CO' : co (WCore.G X_s'') ≡
            co_s ∪ (E_s ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) ×
                (eq b_t ∩₁ WCore.lab_is_w l_a) >> /\
    << RMW' : rmw (WCore.G X_s'') ≡ rmw_s >>).
  { apply simrel_exec_b_step_1; ins.
    all: apply ADD. }
  subst a_t'. subst b_t'. desf.
  exists l_a', b_t, X_s''.
  destruct STEPA as [ADD' RFC' CONS'].
  destruct ADD' as (r' & R1' & w' & W1' & W2' & ADD').
  assert (ANOTB : b_t <> a_t).
  { intro FALSO. apply (rsr_at_neq_bt INV).
    congruence. }
  assert (ENOTIN : ~E_t b_t) by apply ADD.
  assert (ANOTIN : ~E_t a_t).
  { intro FALSO. now apply ENOTIN, (rsr_at_bt_ord CORR). }
  assert (ANOTIN' : ~E_t' a_t).
  { intro FALSO. apply (WCore.add_event_acts ADD) in FALSO.
    destruct FALSO as [INE|EQ]; eauto. }
  (* Generate new actid *)
  assert (NEWE :
  << NINIT : ~is_init a_t >> /\
  << NOTIN : ~(E_s ∪₁ eq b_t) a_t >> /\
  << TID : tid a_t = tid b_t >> /\
  << NEWSB : ⦗E_s ∪₁ eq b_t ∪₁ eq a_t⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq b_t ∪₁ eq a_t⦘ ≡
          sb (WCore.G X_s'') ∪ WCore.sb_delta a_t (acts_set (WCore.G X_s'')) >>).
  { unfold NW. splits; try now apply CORR.
    { intro FALSO. apply set_subset_single_l in FALSO.
      erewrite (rsr_actsE CORR) in FALSO; eauto.
      rewrite extra_a_none_r in FALSO by apply ADD.
      rewrite set_union_empty_r in FALSO.
      apply -> set_subset_single_l in FALSO.
      destruct FALSO as [INE | EQB].
      { now apply (WCore.add_event_new ADD), (rsr_at_bt_ord INV). }
      apply (rsr_at_neq_bt INV). auto. }
    unfold sb. rewrite (WCore.add_event_acts ADD').
    rewrite (rsr_actsE INV SIMREL), extra_a_none_r; auto.
    rewrite set_union_empty_r, <- (WCore.add_event_acts ADD).
    rewrite id_union, !seq_union_l, !seq_union_r, <- unionA.
    arewrite_false (⦗eq a_t⦘ ⨾ ext_sb ⨾ ⦗eq a_t⦘).
    { clear. unfolder. ins. desf. eapply ext_sb_irr; eauto. }
    arewrite_false (⦗eq a_t⦘ ⨾ ext_sb ⨾ ⦗E_t'⦘).
    { apply INV'. intro FALSO. apply ADD in FALSO.
      destruct FALSO as [IN|EQ].
      { now apply NINB, (rsr_at_bt_ord INV). }
      now apply (rsr_at_neq_bt INV). }
    rewrite !union_false_r. apply union_more; auto.
    unfolder; split; intros x y HREL.
    { clear - HREL. unfold ext_sb in HREL.
      desf; eauto. unfold same_tid. desf; eauto. }
    assert (XIN : E_t' x).
    { clear - HREL INV'. desf.
      now apply (rsr_init_acts INV'). }
    splits; try now (auto; clear - HREL; desf).
    destruct HREL as [[INIT | [INE TID]] EQ]; subst y.
    { clear - INIT INV'. unfold ext_sb; desf.
      now apply (rsr_at_ninit INV'). }
    destruct PeanoNat.Nat.lt_total
        with (n := index a_t) (m := index x)
          as [LT | [EQ | GT]].
    { exfalso. apply (rsr_nat_spot INV') with a_t x; auto.
      unfolder; splits; auto. unfold ext_sb.
      desf; ins; desf; lia. }
    { exfalso. apply ANOTIN'.
      arewrite (a_t = x); auto.
      destruct a_t as [atl | att atn].
      { exfalso. now apply (rsr_at_ninit INV). }
      destruct x as [xl | xt xn].
      { exfalso. apply (rsr_at_tid INV).
        unfold same_tid in TID; desf. }
      unfold same_tid in TID. ins. congruence. }
    unfold ext_sb; desf; ins; lia. }
  desf.
  set (mapper' := upd mapper b_t a_t).
  set (G_s' := {|
    acts_set := E_s ∪₁ eq b_t ∪₁ eq a_t;
    threads_set := threads_set G_s;
    lab := upd (upd lab_s b_t l_a') a_t l;
    rf := rf_s ∪
          mapper' ↑ (rf_t' ⨾ ⦗eq b_t⦘) ∪
          srf (WCore.G X_s'') ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘;
    co := co_s ∪
          mapper' ↑ (⦗eq b_t⦘ ⨾ co_t') ∪
          mapper' ↑ (co_t' ⨾ ⦗eq b_t⦘) ∪
          (W_s ∩₁ E_s ∩₁ Loc_s_ (WCore.lab_loc l_a)) × (eq b_t ∩₁ WCore.lab_is_w l_a);
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
  set (extra_W2 := extra_a X_t' a_t b_t b_t ∩₁ W_s ∩₁ Loc_s_ (WCore.lab_loc l));
  (* Asserts *)
  assert (WF' : Wf G_t').
  { eapply add_event_wf; eauto.
    apply CORR. }
  assert (WF_S'' : Wf (WCore.G X_s'')).
  { apply (add_event_wf ADD').
    eapply G_s_wf with (X_t := X_t); eauto. }
  assert (ENINIT : ~is_init b_t) by apply ADD.
  assert (EQACTS : E_t' ≡₁ E_t ∪₁ eq b_t) by apply ADD.
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    rupd. congruence. }
  assert (ANOTINS : ~E_s b_t).
  { intro FALSO. now apply (WCore.add_event_new ADD'). }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { split; unfolder; intros x (y & YINE & HEQ).
    { exists y; split; ins. rewrite <- MAPEQ; ins. }
    exists y. split; ins. subst mapper'. rupd; ins.
    congruence. }
  assert (LABSUB : eq_dom E_t lab_t' lab_t).
  { rewrite (WCore.add_event_lab ADD). unfolder.
    intros x XINE. rupd. congruence. }
  assert (MAPNEQ : forall x (IN : E_t x), mapper x <> a_t).
  { intros x XINE FALSO. apply NOTIN. left.
    apply (rsr_codom SIMREL). basic_solver. }
  assert (MAPNEQ' : forall x (IN : E_t x), mapper x <> b_t).
  { intros x XINE FALSO. apply ANOTINS.
    apply (rsr_codom SIMREL). basic_solver. }
  assert (FMAP : fixset is_init mapper').
  { unfold mapper'. unfolder. ins. rupd; [| congruence].
    now apply (rsr_init SIMREL). }
  assert (MTID : mapper' ↑₁ (E_t ∩₁ same_tid b_t) ≡₁
                 mapper' ↑₁ E_t ∩₁ same_tid (mapper' b_t)).
  { unfolder. split; intros x HSET.
    { destruct HSET as (y & (INE & HTID) & XEQ). subst x.
      unfold same_tid. split; eauto.
      unfold mapper'; rupd; [| congruence].
      change (tid (mapper y)) with ((tid ∘ mapper) y).
      rewrite (rsr_tid SIMREL), TID; ins. }
    destruct HSET as ((y & INE & XEQ) & HTID).
    exists y; splits; eauto. subst x.
    unfold same_tid. rewrite <- (rsr_tid SIMREL) with y; ins.
    unfold mapper' in HTID. rewrite upds, updo in HTID by congruence.
    unfold compose. now rewrite <- TID, <- HTID. }
  assert (MAPER_E : mapper' ↑₁ eq b_t ≡₁ eq a_t).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (OLDEXA : extra_a X_t a_t b_t b_t ≡₁ ∅).
  { unfold extra_a; do 2 desf; exfalso; eauto. }
  assert (NEWEXA : extra_a X_t' a_t b_t b_t ≡₁ eq b_t).
  { unfold extra_a; do 2 desf; exfalso; eauto.
    apply n; split; ins. apply (WCore.add_event_acts ADD).
    basic_solver. }
  assert (LABEQ : eq_dom E_s (lab (WCore.G X_s'')) lab_s).
  { rewrite (WCore.add_event_lab ADD'). unfolder.
    intros x XINE. rupd; ins. congruence. }
  assert (LABEQ' : eq_dom E_s (upd (upd lab_s b_t l_a') a_t l) lab_s).
  { rewrite (WCore.add_event_lab ADD') in LABEQ. unfolder.
    intros x XINE. rupd; ins; try congruence.
    intro FALSO. eapply NOTIN. left; congruence. }
  assert (MAPE : a_t = mapper' b_t).
  { unfold mapper'. now rewrite upds. }
  assert (NEQLOQ' : WCore.lab_loc l <> WCore.lab_loc l_a').
  { intros FALSO. apply NEQLOC. rewrite FALSO.
    clear - LABU2V. unfold WCore.lab_loc.
    unfold same_label_u2v in LABU2V. desf.
    { basic_solver. }
    basic_solver. }
  assert (SRF'': srf G_s' ⨾ ⦗acts_set (WCore.G X_s'')⦘ ≡
                srf (WCore.G X_s'') ⨾ ⦗acts_set (WCore.G X_s'')⦘).
  { apply (porf_pref_srf (WCore.G X_s'') G_s'); ins.
    { rewrite (WCore.add_event_acts ADD').
      basic_solver. }
    { rewrite (WCore.add_event_acts ADD'),
              (WCore.add_event_lab ADD').
      apply eq_dom_union. split; unfolder.
      all: intros x XIN; rupd; ins; try congruence.
      intro FALSO. apply NOTIN. left; congruence. }
    { unfold sb at 1. ins. rewrite NEWSB.
      rewrite (WCore.add_event_sb ADD').
      unfold WCore.sb_delta.
      rewrite (WCore.add_event_acts ADD').
      rewrite seq_union_l at 1.
      rewrite <- cross_inter_r.
      arewrite (eq a_t ∩₁ (E_s ∪₁ eq b_t) ≡₁ ∅).
      { generalize NOTIN. clear. basic_solver. }
      now rewrite cross_false_r, union_false_r. }
    { rewrite RF', (WCore.add_event_acts ADD'), !seq_union_l.
      rewrite MAPE in NOTIN. clear - NOTIN.
      arewrite_false (mapper' ↑ (rf_t' ⨾ ⦗eq b_t⦘) ⨾ ⦗E_s ∪₁ eq b_t⦘).
      { unfolder in NOTIN. basic_solver. }
      now rewrite union_false_r. }
    { rewrite CO', (WCore.add_event_acts ADD'), !seq_union_l,
              !seq_union_r.
      rewrite MAPE in NOTIN. clear - NOTIN.
      arewrite_false (⦗E_s ∪₁ eq b_t⦘ ⨾ mapper' ↑ (⦗eq b_t⦘ ⨾ co_t')).
      { unfolder in NOTIN. basic_solver. }
      arewrite_false (mapper' ↑ (co_t' ⨾ ⦗eq b_t⦘) ⨾ ⦗E_s ∪₁ eq b_t⦘).
      { unfolder in NOTIN. basic_solver. }
      now rewrite seq_false_l, seq_false_r, !union_false_r,
                  set_interC with (s := E_s). }
    rewrite RMW', (WCore.add_event_acts ADD'), (WCore.add_event_rmw ADD),
            collect_rel_union, seq_union_l.
    arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
    { apply collect_rel_eq_dom' with (s := E_t); ins.
      apply (wf_rmwE (rsr_Gt_wf CORR)). }
    arewrite_false (WCore.rmw_delta b_t r).
    { destruct r as [r|]; [| clear; basic_solver].
      exfalso. eapply (rsr_nrmw CORR') with (x := r) (y := b_t); auto.
      apply ADD. right. clear. basic_solver. }
    now rewrite <- (rsr_rmw SIMREL), collect_rel_empty, seq_false_l,
                union_false_r. }
  assert (NACQ' :
    ~is_acq (upd (upd lab_s b_t l_a') a_t l) b_t
  ).
  { unfold is_acq, mod.
    rewrite updo, upds; [| congruence].
    clear - LABU2V NACQ.
    unfold same_label_u2v in *; desf; ins; desf. }
  assert (NEQLOC' :
    ~same_loc (upd (upd lab_s b_t l_a') a_t l) a_t b_t
  ).
  { unfold same_loc, loc.
    rewrite upds, updo, upds; [| congruence].
    clear - LABU2V NEQLOC.
    unfold same_label_u2v in *; desf; ins; desf. }
  assert (WR' :
    eq b_t ⊆₁ is_r (upd (upd lab_s b_t l_a') a_t l) ∪₁
              is_w (upd (upd lab_s b_t l_a') a_t l)
  ).
  { admit. }
  assert (SIMREL' : reord_simrel X_s' X_t' a_t b_t mapper').
  { constructor; ins.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { unfolder. intros x y XINE YINE. rewrite !MAPEQ; ins.
        now apply SIMREL. }
      { clear. basic_solver. }
      rewrite MAPER_E, MAPSUB, (rsr_codom SIMREL), OLDEXA.
      clear - NOTIN. unfolder in NOTIN. basic_solver. }
    { rewrite NEWEXA. unfolder. intros x XEQ. subst x.
      constructor; ins.
      assert (SUBRF : rf (WCore.G X_s'') ⊆ same_val (upd (upd lab_s b_t l_a') a_t l)).
      { unfolder. unfold same_val. intros x y RF.
        apply (wf_rfE WF_S'') in RF. unfolder in RF.
        destruct RF as (DOM & RF & CODOM).
        apply (WCore.add_event_acts ADD') in DOM, CODOM.
        unfold val. rewrite !updo with (a := a_t).
        all: try congruence.
        apply (wf_rfv WF_S'') in RF.
        now rewrite (WCore.add_event_lab ADD') in RF. }
      rewrite <- SUBRF, RF'. apply inclusion_union_r. right.
      rewrite !id_inter.
      arewrite (⦗eq b_t⦘ ≡ ⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq b_t⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      seq_rewrite SRF''. rewrite seqA.
      arewrite (⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq b_t⦘ ≡ ⦗eq b_t⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      arewrite (⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq b_t⦘ ≡ ⦗eq b_t⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      apply seq_more; ins. rewrite <- !id_inter.
      apply eqv_rel_more.
      arewrite (WCore.lab_is_r l_a ≡₁ WCore.lab_is_r l_a').
      { clear - LABU2V. unfold WCore.lab_is_r, same_label_u2v in *. desf. }
      rewrite <- (lab_is_rE ADD'), (WCore.add_event_lab ADD').
      clear - ANOTB. unfolder. split; ins; desf.
      all: split; ins; unfold is_r in *.
      all: rewrite upds, updo, ?upds in *; ins. }
    { rewrite EQACTS, set_collect_union, MAPER_E, MAPSUB,
              (rsr_codom SIMREL), NEWEXA, set_minus_union_l,
              OLDEXA, set_minus_union_l, set_minusK.
      clear - NOTIN ANOTB ANOTINS.
      rewrite !set_minus_disjoint; basic_solver. }
    { rewrite EQACTS. apply eq_dom_union. split.
      all: unfolder; unfold compose.
      { intros x XIN. rewrite MAPEQ; ins. now apply SIMREL. }
      now subst mapper'; ins; desf; rupd. }
    { rewrite EQACTS, (WCore.add_event_lab ADD).
      apply eq_dom_union; split; subst mapper'.
      { unfolder. intros x XIN.
        unfold compose. rupd; try congruence; eauto.
        now rewrite <- (rsr_lab SIMREL) by basic_solver. }
      clear.
      unfolder. ins. desf. unfold compose. now rupd. }
    { rewrite EQACTS, set_collect_union, MAPER_E, MAPSUB.
      rewrite (rsr_acts SIMREL), NEWEXA, OLDEXA.
      basic_solver 11. }
    { rewrite NEWEXA. unfold sb at 1.
      ins. rewrite NEWSB, (WCore.add_event_sb ADD').
      arewrite (eq a_t ∩₁ E_t' ≡₁ ∅).
      { clear - ANOTIN'. basic_solver. }
      rewrite swap_rel_empty_r.
      rewrite (sb_deltaE ADD), set_collect_dom, (WCore.add_event_sb ADD),
              collect_rel_union, (rsr_sb SIMREL), OLDEXA,
              cross_false_l, cross_false_r, !union_false_r.
      arewrite (eq b_t ∩₁ E_t ≡₁ ∅).
      { clear - ENOTIN. basic_solver. }
      rewrite swap_rel_empty_l.
      arewrite (mapper' ↑ sb_t ≡ mapper ↑ sb_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        unfold sb. basic_solver 11. }
      rewrite mapped_sb_delta, dom_cross; ins.
      all: try now (apply set_nonemptyE; eauto).
      unfold WCore.sb_delta.
      rewrite (WCore.add_event_acts ADD'), (rsr_acts SIMREL).
      rewrite OLDEXA, set_union_empty_r, MAPSUB.
      unfold mapper'. rupd. rewrite set_inter_union_l.
      arewrite (same_tid a_t ≡₁ same_tid b_t).
      { unfold same_tid. now rewrite (rsr_at_bt_tid INV). }
      arewrite (eq b_t ∩₁ same_tid b_t ≡₁ eq b_t).
      { clear. basic_solver. }
      clear. basic_solver 12. }
    { rewrite (rf_delta_RE (rsr_Gt_wf CORR) ADD).
      rewrite NEWEXA.
      arewrite (eq b_t ∩₁ is_r (upd (upd lab_s b_t l_a') a_t l) ≡₁
                eq b_t ∩₁ WCore.lab_is_r l_a').
      { unfolder. split; intros x (EQ & ISR).
        all: split; ins; subst x; unfold is_r in *.
        all: rewrite updo, upds in *; try congruence.
        all: unfold WCore.lab_is_r in *; desf. }
      arewrite (srf G_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a'⦘ ≡
                srf G_s' ⨾ ⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a'⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      seq_rewrite SRF''. rewrite seqA.
      arewrite (⦗acts_set (WCore.G X_s'')⦘ ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a'⦘ ≡
                ⦗eq b_t ∩₁ WCore.lab_is_r l_a'⦘).
      { rewrite (WCore.add_event_acts ADD'). basic_solver 11. }
      rewrite (rsr_rf SIMREL), (WCore.add_event_rf ADD),
              !collect_rel_union.
      arewrite (mapper' ↑ rf_t ≡ mapper ↑ rf_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rfE (rsr_Gt_wf CORR)). }
      rewrite OLDEXA.
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      rewrite collect_rel_empty, !union_false_r.
      arewrite (WCore.lab_is_r l_a ≡₁ WCore.lab_is_r l_a').
      { unfold WCore.lab_is_r, same_label_u2v in *. desf. }
      clear. basic_solver 12. }
    { rewrite (co_deltaE1 (rsr_Gt_wf CORR) ADD),
              (co_deltaE2 (rsr_Gt_wf CORR) ADD).
      rewrite (WCore.add_event_co ADD), !collect_rel_union,
              (rsr_co SIMREL).
      arewrite (mapper' ↑ co_t ≡ mapper ↑ co_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_coE (rsr_Gt_wf CORR)). }
      rewrite OLDEXA, set_inter_empty_l, add_max_empty_r, union_false_r.
      rewrite NEWEXA, !extra_co_D_union, !add_max_union.
      arewrite (extra_co_D (eq a_t) (upd (upd lab_s b_t l_a') a_t l)
                (loc (upd (upd lab_s b_t l_a') a_t l) b_t) ≡₁ ∅).
      { split; [| basic_solver].
        transitivity (same_loc (upd (upd lab_s b_t l_a') a_t l) b_t ∩₁ eq a_t).
        { clear. unfold same_loc. basic_solver. }
        clear - NEQLOC ANOTB LABU2V.
        unfolder. ins. desf.
        unfold same_loc, loc, WCore.lab_loc, same_label_u2v in *.
        rewrite upds, updo, upds in * by assumption.
        do 2 desf. }
      rewrite add_max_empty_l, union_false_r.
      rewrite add_max_sub
         with (A := extra_co_D (eq b_t) _ _)
           by basic_solver 11.
      rewrite union_false_r.
      rewrite extra_co_D_eq_dom with (ll1 := upd (upd lab_s b_t l_a') a_t l).
      all: eauto using same_lab_u2v_dom_inclusion.
      arewrite (eq b_t ∩₁ is_w (upd (upd lab_s b_t l_a') a_t l) ≡₁
                eq b_t ∩₁ WCore.lab_is_w l_a').
      { unfold is_w, WCore.lab_is_w. unfolder.
        split; intros x (EQ & LAB); split; ins; subst x.
        all: rewrite updo, upds in *; ins.
        all: desf. }
      arewrite (loc (upd (upd lab_s b_t l_a') a_t l) b_t = WCore.lab_loc l_a').
      { unfold loc, WCore.lab_loc. now rupd. }
      unfold add_max.
      arewrite (extra_co_D E_s lab_s (WCore.lab_loc l_a') \₁ eq b_t ∩₁ WCore.lab_is_w l_a'
                ≡₁ extra_co_D E_s lab_s (WCore.lab_loc l_a')).
      { rewrite set_minus_disjoint; ins.
        clear - ANOTINS. basic_solver. }
      unfold WCore.co_delta. rewrite collect_rel_union.
      arewrite (WCore.lab_is_w l_a ≡₁ WCore.lab_is_w l_a').
      { clear - LABU2V. unfold WCore.lab_is_w, same_label_u2v in *. desf. }
      arewrite (WCore.lab_loc l_a = (WCore.lab_loc l_a')).
      { clear - LABU2V. unfold WCore.lab_loc, same_label_u2v in *. do 2 desf. }
      clear. basic_solver 11. }
    { rewrite (WCore.add_event_threads ADD). apply SIMREL. }
    { rewrite (WCore.add_event_ctrl ADD). apply SIMREL. }
    { rewrite (WCore.add_event_data ADD). apply SIMREL. }
    { rewrite (WCore.add_event_addr ADD). apply SIMREL. }
    { rewrite (WCore.add_event_rmw_dep ADD). apply SIMREL. }
    { arewrite (eq a_t ∩₁ E_t' ≡₁ ∅).
      { clear - ANOTIN'. basic_solver. }
      rewrite set_collect_empty. clear. basic_solver. }
    { arewrite (E_t' \₁ eq a_t \₁ eq b_t ≡₁ E_t \₁ eq a_t \₁ eq b_t).
      { rewrite (WCore.add_event_acts ADD). clear. basic_solver. }
      clear - MAPEQ SIMREL. unfolder. intros x XIN.
      rewrite MAPEQ; [rewrite (rsr_mid SIMREL)|]; desf. }
    { rewrite EQACTS, set_inter_absorb_r by (clear; basic_solver).
      unfold mapper'. now rewrite set_collect_eq, upds. }
    rewrite EQACTS.
    assert (NEQ : a_t <> b_t) by apply INV.
    arewrite (eq a_t ∩₁ (E_t ∪₁ eq b_t) ≡₁ ∅).
    { rewrite set_inter_union_r. clear - NEQ ANOTIN.
      basic_solver. }
    rewrite set_collect_empty. auto with hahn. }
  (* The proof *)
  exists mapper', X_s'.
  splits; ins.
  { constructor; ins.
    now exists r', R1', w', W1', W2'. }
  constructor; ins.
  { exists (option_map mapper' r), (mapper' ↑₁ R1),
         (option_map mapper' w), (mapper' ↑₁ W1), (mapper' ↑₁ W2).
    apply add_event_to_wf; ins.
    { rewrite (WCore.add_event_acts ADD').
      apply set_subset_union_r. left.
      eapply sico_init_acts_s; [| apply INV].
      eapply rsr_common; eauto. }
    { rewrite <- MAPE.
      intro FALSO. apply (WCore.add_event_acts ADD') in FALSO.
      eauto. }
    { now rewrite <- MAPE. }
    { rewrite <- MAPE, TID, <- (rsr_at_bt_tid CORR). apply CORR. }
    { now rewrite (WCore.add_event_acts ADD'), MAPE. }
    { now rewrite (WCore.add_event_threads ADD'). }
    { now rewrite (WCore.add_event_lab ADD'), MAPE. }
    { rewrite <- mapped_rf_delta_R,
              <- mapped_rf_delta_W.
      rewrite (rf_delta_RE (rsr_Gt_wf CORR) ADD).
      rewrite (add_event_to_rf_complete ADD).
      all: try now apply CORR.
      rewrite collect_rel_empty, union_false_r,
              RF'.
      clear. basic_solver 11. }
    { rewrite (co_deltaE1 (rsr_Gt_wf CORR) ADD),
              (co_deltaE2 (rsr_Gt_wf CORR) ADD).
      rewrite <- mapped_co_delta, CO'.
      clear. basic_solver 11. }
    { rewrite <- mapped_rmw_delta, (WCore.add_event_rmw ADD),
              collect_rel_union.
      arewrite (mapper' ↑ rmw_t ≡ mapper ↑ rmw_t).
      { apply collect_rel_eq_dom' with (s := E_t); ins.
        apply (wf_rmwE (rsr_Gt_wf CORR)). }
      now rewrite RMW', (rsr_rmw SIMREL). }
    { now rewrite (WCore.add_event_data ADD'). }
    { now rewrite (WCore.add_event_addr ADD'). }
    { now rewrite (WCore.add_event_ctrl ADD'). }
    { now rewrite (WCore.add_event_rmw_dep ADD'). }
    { unfold sb at 1. ins. now rewrite NEWSB, MAPE. }
    { now rewrite (rsr_ctrl SIMREL), (rsr_nctrl CORR). }
    eapply G_s_wf with (X_s := X_s') (X_t := X_t'); eauto. }
  { eapply G_s_rfc with (X_s := X_s') (X_t := X_t'); eauto. }
  assert (AINS : (acts_set G_s') a_t).
  { admit. }
  assert (BINS : (acts_set G_s') b_t).
  { admit. }
  assert (AINRW : eq a_t ∩₁ (acts_set G_s') ⊆₁ (R G_s' ∪₁ W G_s')).
  { intros x XIN.
    destruct simrel_a_lab_wr with (X_s := X_s') (X_t := X_t')
        (a_t := a_t) (b_t := b_t) (mapper := mapper') (x := x); vauto. }
  assert (AINNREL : eq a_t ∩₁ (acts_set G_s') ⊆₁ set_compl (Rel G_s')).
  { intros x COND.
    apply rsr_bs_nrel with (X_s := X_s') (X_t := X_t')
        (a_t := a_t) (b_t := b_t) (mapper := mapper') (x := x); vauto. }
  assert (SBFROMA : ⦗eq b_t⦘ ⨾ sb G_s' ⊆ eq b_t × eq a_t).
  { unfold G_s', sb; ins.
    rewrite NEWSB, (WCore.add_event_sb ADD').
    rewrite !seq_union_r.
    arewrite_false (⦗eq b_t⦘ ⨾ sb_s).
    { rewrite wf_sbE. clear - ANOTINS. basic_solver. }
    arewrite_false (⦗eq b_t⦘ ⨾ WCore.sb_delta b_t E_s).
    { clear - ENINIT ANOTINS. basic_solver. }
    rewrite (WCore.add_event_acts ADD').
    clear. basic_solver. }
  assert (RPOIMMEMP : ⦗eq b_t⦘ ⨾ rpo_imm G_s' ⊆ ∅₂).
  { unfold rpo_imm. rewrite !seq_union_r.
    rewrite <- !seqA.
    rewrite !seq_eqvC with (doma := eq b_t).
    rewrite !seqA with (r3 := sb G_s').
    rewrite wf_sbE. rewrite !seqA.
    arewrite !(⦗eq b_t⦘ ⨾ ⦗acts_set G_s'⦘ ≡ ⦗acts_set G_s'⦘ ⨾ ⦗eq b_t⦘).
    { basic_solver 11. }
    rewrite <- !seqA.
    rewrite !seqA with (r3 := ⦗eq b_t⦘).
    rewrite !seqA with (r3 := sb G_s').
    rewrite !SBFROMA.
    rewrite !seqA. rewrite <- !cross_inter_r.
    rewrite <- !cross_inter_l.
    repeat apply inclusion_union_l.
    { clear - AINRW ANOTB.
      arewrite_id (⦗R G_s' ∩₁ Rlx G_s'⦘).
      arewrite_id (⦗acts_set G_s'⦘) at 1.
      rels.
      transitivity (eq b_t × eq a_t ⨾ ⦗acts_set G_s'⦘ ⨾ ⦗F G_s'⦘).
      { clear. basic_solver. }
      intros x y PATH.
      destruct PATH as (x0 & (CROSS1 & CROSS2) & COND); subst.
      apply id_inter in COND.
      clear - AINRW COND.
      destruct COND as (EQ & (COND1 & COND2)); subst.
      destruct AINRW with y; [basic_solver 12 | |].
      { unfold is_f, is_r in *. basic_solver 12. }
      unfold is_f, is_w in *. basic_solver 12. }
    { admit. (*TODO : finish*)}
    { clear - AINNREL.
      arewrite_id (⦗acts_set G_s'⦘) at 1. rels.
      intros x y PATH.
      destruct PATH as (x0 & (CROSS1 & CROSS2) & COND); subst.
      apply id_inter in COND.
      clear - AINNREL COND.
      destruct COND as (EQ & (COND1 & COND2)); subst.
      destruct AINNREL with y; basic_solver 12. }
    arewrite_id (⦗W G_s' ∩₁ Rlx G_s'⦘).
    arewrite_id (⦗acts_set G_s'⦘) at 2.
    seq_rewrite <- !cross_inter_l.
    arewrite ((F G_s' ∩₁ Rel G_s' ∩₁ (acts_set G_s' ∩₁
               eq b_t)) ≡₁ ∅); [|basic_solver].
    split; [|basic_solver].
    transitivity (F G_s' ∩₁ (acts_set G_s' ∩₁ eq b_t)); [basic_solver|].
    rewrite set_interC with (s := acts_set G_s').
    change G_s' with (WCore.G X_s').
    rewrite simrel_b_lab_wr; vauto.
    clear. unfold is_w, is_f, is_r. unfolder; ins; desf. }
  assert (RPOEMP : ⦗eq b_t⦘ ⨾ rpo G_s' ⊆ ∅₂).
  { unfold rpo. rewrite ct_begin.
    rewrite <- seqA.
    rewrite RPOIMMEMP. clear. basic_solver. }
  assert (RPOCODOM : codom_rel (⦗eq b_t⦘ ⨾ rpo G_s') ≡₁ ∅).
  { split; [| basic_solver].
    rewrite RPOEMP. clear; basic_solver. }
  assert (RPOIMMCODOM : codom_rel (⦗eq b_t⦘ ⨾ rpo_imm G_s') ≡₁ ∅).
  { split; [| basic_solver]. arewrite (rpo_imm G_s' ⊆ rpo G_s').
    destruct RPOCODOM; vauto. }
  assert (RPOIMMST : ⦗E_s ∪₁ eq a_t⦘ ⨾ rpo_imm G_s' ≡ rpo_imm G_s').
  { split; [basic_solver |].
    arewrite (rpo_imm G_s' ⊆ ⦗acts_set G_s'⦘ ⨾ rpo_imm G_s').
    { rewrite wf_rpo_immE at 1.
      { basic_solver. }
      apply G_s_wf with (X_s := X_s') (X_t := X_t')
      (a_t := a_t) (b_t := b_t) (mapper := mapper'); vauto. }
    unfold G_s' at 1; ins. intros x y COND.
    destruct COND as (z & (C1 & C2) & C3).
    subst z.
    assert (SWAP : E_s ∪₁ eq b_t ∪₁ eq a_t
                ⊆₁ E_s ∪₁ eq a_t ∪₁ eq b_t) by basic_solver.
    apply SWAP in C2. destruct C2 as [C2 | C2].
    { basic_solver 21. }
    destruct RPOIMMCODOM as (IN & OUT).
    destruct IN with y. basic_solver 21. }
  assert (BINRW : eq b_t ⊆₁ R G_s' ∪₁ W G_s').
  { change G_s' with (WCore.G X_s').
    rewrite <- (simrel_b_lab_wr INV' SIMREL').
    clear - BINS. basic_solver. }
  destruct (BINRW b_t) as [RR | WW]; vauto.
  { apply XmmCons.read_extent with (G_t := G_t')
              (sc_t := WCore.sc X_t') (a := b_t) (m := mapper'); eauto.
    { apply SIMREL'; vauto. }
    { unfold G_s'; ins.
      rewrite (rsr_acts SIMREL). rewrite OLDEXA.
      rewrite EQACTS. rewrite set_collect_union; eauto.
      rewrite MAPER_E. rewrite MAPSUB; basic_solver 12. }
    { apply SIMREL'; vauto. }
    { rewrite EQACTS.
      rewrite set_collect_union, MAPER_E, MAPSUB, (rsr_codom SIMREL).
      rewrite OLDEXA; rels. intros FLS.
      destruct FLS as [FLS | FLS].
      { destruct ANOTINS.
        destruct FLS; vauto. }
      destruct ANOTB; vauto. }
    { arewrite (rpo G_s' ⊆ ⦗acts_set G_s'⦘ ⨾ rpo G_s').
      { rewrite wf_rpoE. basic_solver 8. }
      unfold G_s' at 1; ins.
      arewrite ((E_s ∪₁ eq b_t ∪₁ eq a_t) \₁ eq b_t ≡₁
                E_s ∪₁ eq a_t).
      { clear - ANOTB ANOTINS.
        rewrite !set_minus_union_l.
        arewrite (E_s \₁ eq b_t ≡₁ E_s).
        { split; [basic_solver |].
          unfold set_minus.
          intros x INE. split; vauto.
          intros FALSE; basic_solver. }
        basic_solver. }
      rewrite set_unionA.
      rewrite set_unionC with (s := eq b_t).
      rewrite <- set_unionA.
      rewrite id_union. rewrite seq_union_l.
      apply inclusion_union_l.
      { rewrite id_union at 1. rewrite seq_union_l.
        apply inclusion_union_l.
        { unfold rpo. transitivity ((⦗E_s⦘ ⨾ rpo_imm G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘)⁺).
          { induction 1 as (x0 & (P1 & (x1 & (P2 & P3)))).
            destruct P1 as (EQ & COND1); subst x0.
            destruct P3 as (EQ & COND2); subst x1.
            induction P2 as [x y STT | x].
            { apply ct_step. unfold seq. exists x. splits; vauto. }
            apply ct_begin in P2_2. destruct P2_2 as (x0 & P1 & P2).
            eapply RPOIMMST in P1; vauto.
            destruct P1 as (x1 & (EQ' & COND') & P1); subst x1.
            destruct COND' as [COND' | COND'].
            { assert (COND'' : E_s y) by vauto.
              apply IHP2_1 in COND1; vauto. apply IHP2_2 in COND''; vauto. }
            subst y. exfalso.
            apply rpo_imm_in_sb in P1.
            assert (GEQ : G_s' = WCore.G X_s') by vauto.
            rewrite GEQ in P1.
            apply (rsr_sb SIMREL') in P1.
            destruct P1 as [[P1 | P1] | P1].
            { assert (AEQQ : eq a_t ∩₁ E_t' ≡₁ ∅).
              { clear - ANOTIN'. basic_solver. }
              destruct P1 as (a' & x' & (C1 & C2 & C3)).
              unfold swap_rel in C1.
              destruct C1 as [C1 | C1].
              { assert (C1' : (sb_t') a' x').
                { clear - C1. unfold minus_rel in C1. desf. }
                apply wf_sbE in C1'.
                destruct C1' as (a0 & C1' & C1'').
                destruct C1' as (EQ & C1').
                rewrite MAPE in C2; subst a0.
                apply (rsr_inj SIMREL') in C2; vauto.
                { destruct C1'' as (x1 & PTH & (EQ & INE)).
                  subst x1. subst a'. destruct INV'.
                  assert (C1'' : E_t' b_t) by vauto.
                  apply rsr_bt_max in C1'; vauto.
                  clear - PTH C1' C1''.
                  destruct C1' with b_t x'.
                  basic_solver 21. }
                apply EQACTS. basic_solver. }
              rewrite MAPE in C2.
              apply (rsr_inj SIMREL') in C2; vauto.
              { destruct C1 as (C1 & C1').
                subst a'. clear - C1 ANOTB.
                destruct C1; vauto. }
              { clear - C1. destruct C1 as (C1 & C1').
                destruct C1; vauto. }
              apply EQACTS. basic_solver. }
            { destruct P1 as (P1 & P1').
              destruct P1 as (a0 & (DOM & MAP)).
              destruct DOM as (a1 & (a2 & SBPTH & CD)).
              apply wf_sbE in SBPTH.
              destruct SBPTH as (a3 & (EQ & CND) & CND').
              destruct CND' as (a4 & (EQ' & (EQ2 &CND'))).
              subst a4. subst a3.
              destruct CD as (EQ1 & EQB). subst a2. subst a1.
              rewrite MAPE in MAP.
              apply (rsr_inj SIMREL') in MAP; vauto.
              subst a0. apply sb_irr in EQ'. done. }
            destruct P1 as (P1 & P1').
            apply NEWEXA in P1. clear - P1 ANOTB; vauto. }
          assert (IND1 : (⦗E_s⦘ ⨾ rpo_imm G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘) ⊆ mapper' ↑ (rpo_imm G_t')⁺).
          { unfold rpo_imm. rewrite !seq_union_l. rewrite !seqA.
            rewrite <- ct_step.
            rewrite !seq_union_r.
            arewrite (sb_t' ≡ ⦗E_t'⦘ ⨾ sb_t' ⨾ ⦗E_t'⦘).
            { rewrite wf_sbE. basic_solver 11. }
            rewrite <- seqA. rewrite seq_eqvC.
            rewrite seqA. rewrite seq_eqvC.
            arewrite (⦗E_s⦘ ⨾ ⦗Acq G_s'⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ≡
                      ⦗Acq G_s'⦘ ⨾ ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘).
            { rewrite <- seqA. rewrite seq_eqvC; basic_solver. }
            arewrite (⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗Rel G_s'⦘ ⨾ ⦗E_s ∪₁ eq a_t⦘ ≡
                      ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗Rel G_s'⦘).
            { rewrite <- seqA. rewrite seq_eqvC; basic_solver. }
            arewrite (⦗E_s⦘ ⨾ ⦗F G_s' ∩₁ Rel G_s'⦘ ⨾ sb G_s' ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘ ⨾ ⦗E_s ∪₁ eq a_t⦘ ≡
                      ⦗F G_s' ∩₁ Rel G_s'⦘ ⨾ ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘).
            { rewrite seq_eqvC. rewrite <- seqA. rewrite seq_eqvC. basic_solver. }
            assert (SBSUB : ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⊆ ⦗E_s⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗E_s ∪₁ eq a_t⦘).
            { arewrite (G_s' = WCore.G X_s').
              rewrite (rsr_sb SIMREL'). unfold swap_rel.
              rewrite !NEWEXA.
              arewrite (eq a_t ∩₁ E_t' ≡₁ ∅).
              { clear - ANOTIN'. basic_solver. }
              arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t).
              { split; [basic_solver |].
                rewrite EQACTS. basic_solver 8. }
              arewrite (mapper' b_t = a_t).
              clear - ANOTINS NOTIN ANOTB.
              rewrite !seq_union_l. rewrite !seq_union_r.
              rels. apply inclusion_union_l.
              { apply inclusion_union_l; vauto.
                intros x y PATH. destruct PATH as (z & (C1 & C2) & C3).
                destruct C3 as (x0 & (C4 & C5) & C6). subst x0.
                clear -C6 ANOTINS ANOTB. exfalso.
                destruct C6 as (EQ & COND).
                destruct COND as [COND | COND].
                { apply ANOTINS. rewrite EQ. vauto. }
                apply ANOTB. rewrite EQ. vauto. }
              basic_solver 21. }
            arewrite (⦗R G_s' ∩₁ Rlx G_s'⦘ ⨾ ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗F G_s' ∩₁ Acq G_s'⦘
                      ⊆ ⦗R G_s' ∩₁ Rlx G_s'⦘ ⨾ ⦗E_s⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗F G_s' ∩₁ Acq G_s'⦘).
            { clear - SBSUB. hahn_frame_l. hahn_frame_r; vauto. }
            arewrite (⦗Acq G_s'⦘ ⨾ ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘
                      ⊆ ⦗Acq G_s'⦘ ⨾ ⦗E_s⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗E_s ∪₁ eq a_t⦘).
            arewrite (⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗Rel G_s'⦘
                      ⊆ ⦗E_s⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗Rel G_s'⦘).
            { clear - SBSUB. hahn_frame_r; vauto. }
            arewrite (⦗F G_s' ∩₁ Rel G_s'⦘ ⨾ ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘
                      ⊆ ⦗F G_s' ∩₁ Rel G_s'⦘ ⨾ ⦗E_s⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘).
            { clear - SBSUB. hahn_frame_l. hahn_frame_r; vauto. }
            rewrite <- !id_inter. rewrite <- !seqA.
            rewrite <- !id_inter. rewrite !seqA.
            rewrite <- !set_interA.
            rewrite (rsr_acts SIMREL).
            rewrite OLDEXA. rewrite !set_union_empty_r.
            assert (NOTEQ : forall x , E_t x -> mapper x = x).
            { intros x XINE. apply (rsr_mid SIMREL).
              clear - XINE ENOTIN ANOTIN.
              unfold set_minus. split.
              { split; vauto. intros FALSE. apply ANOTIN.
                rewrite FALSE; vauto. }
              intros FALSE. apply ENOTIN.
              rewrite FALSE; vauto. }
            arewrite (⦗R G_s' ∩₁ Rlx G_s' ∩₁ mapper ↑₁ E_t⦘
                        ⊆ mapper' ↑ ⦗R_t' ∩₁ Rlx G_t' ∩₁ E_t'⦘).
            { intros x y COND. destruct COND as (EQ & COND); subst y.
              destruct COND as ((COND1 & COND2) & INE).
              destruct INE as [x' [INE MAP]].
              unfold set_collect.
              exists x', x'.
              assert (MAP' : mapper' x' = x).
              { rewrite <- MAP.
                unfold mapper'. rupd.
                intros FALSE. apply ENOTIN.
                rewrite FALSE in INE; vauto. }
              splits; vauto. split; vauto.
              split.
              { split.
                { unfold G_s' in COND1; ins.
                  unfold is_r. destruct (rsr_lab SIMREL) with x'; vauto.
                  unfold compose. unfold is_r in COND1.
                  rewrite !updo in COND1; vauto.
                  { arewrite (lab_t' x' = lab_t x').
                    rewrite <- MAP in COND1.
                    destruct (rsr_lab SIMREL) with x'; vauto. }
                  { apply NOTEQ in INE. congruence. }
                  intros FALSE. rewrite FALSE in MAP.
                  assert (INEN : E_t x'); vauto.
                  apply NOTEQ in INE. congruence. }
                unfold G_s' in COND2; ins.
                unfold is_rlx. unfold mod. destruct (rsr_lab SIMREL) with x'; vauto.
                unfold compose. unfold is_rlx in COND2. unfold mod in COND2.
                rewrite !updo in COND2; vauto.
                { arewrite (lab_t' x' = lab_t x').
                  rewrite <- MAP in COND2.
                  destruct (rsr_lab SIMREL) with x'; vauto. }
                { apply NOTEQ in INE. congruence. }
                intros FALSE. rewrite FALSE in MAP.
                assert (INEN : E_t x'); vauto.
                apply NOTEQ in INE. congruence. }
              apply EQACTS; vauto. }
            assert (EQACT : mapper ↑₁ E_t ∪₁ eq a_t ≡₁ mapper' ↑₁ E_t').
            { rewrite EQACTS. rewrite set_collect_union.
              rewrite MAPER_E. rewrite MAPSUB. basic_solver. }
            arewrite (⦗(mapper ↑₁ E_t ∪₁ eq a_t) ∩₁ F G_s' ∩₁ Acq G_s'⦘
                        ⊆ mapper' ↑ ⦗E_t' ∩₁ F G_t' ∩₁ Acq G_t'⦘).
            { intros x y COND. destruct COND as (EQ & COND); subst y.
              destruct COND as ((INE & COND1) & COND2).
              apply EQACT in INE.
              destruct INE as [x' [INE MAP]].
              unfold set_collect.
              exists x', x'.
              split; vauto. split; vauto.
              split.
              { split; vauto.
                unfold is_f. destruct (rsr_lab SIMREL') with x'; vauto.
                unfold compose. rewrite MAP; vauto. }
              unfold is_acq. unfold mod.
              destruct (rsr_lab SIMREL') with x'; vauto.
              unfold compose. unfold is_acq in COND2. unfold mod in COND2.
              rewrite MAP; vauto. }
            arewrite (⦗Acq G_s' ∩₁ mapper ↑₁ E_t⦘
                        ⊆ mapper' ↑ ⦗Acq G_t' ∩₁ E_t'⦘).
            { intros x y COND. destruct COND as (EQ & COND); subst y.
              destruct COND as (COND1 & INE).
              destruct INE as [x' [INE MAP]].
              unfold set_collect.
              exists x', x'.
              assert (MAP' : mapper' x' = x).
              { rewrite <- MAP.
                unfold mapper'. rupd.
                intros FALSE. apply ENOTIN.
                rewrite FALSE in INE; vauto. }
              splits; vauto. split; vauto.
              split.
              { unfold G_s' in COND1; ins.
                unfold is_acq. destruct (rsr_lab SIMREL) with x'; vauto.
                unfold compose. unfold is_acq in COND1.
                unfold mod in COND1. unfold mod.
                rewrite !updo in COND1; vauto.
                { arewrite (lab_t' x' = lab_t x').
                  rewrite <- MAP in COND1.
                  destruct (rsr_lab SIMREL) with x'; vauto. }
                { apply NOTEQ in INE. congruence. }
                intros FALSE. rewrite FALSE in MAP.
                assert (INEN : E_t x'); vauto.
                apply NOTEQ in INE. congruence. }
              apply EQACTS; vauto. }
            arewrite (mapper' ↑ ⦗Acq G_t' ∩₁ E_t'⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗mapper ↑₁ E_t  ∪₁ eq a_t⦘
                  ⊆ mapper' ↑ ⦗Acq G_t' ∩₁ E_t'⦘ ⨾ mapper' ↑ sb_t' ⨾ mapper' ↑ ⦗E_t'⦘).
            { do 2 hahn_frame_l. rewrite collect_rel_eqv.
              rewrite <- MAPSUB. rewrite <- EQACT.
              rewrite MAPSUB. basic_solver. }
            arewrite (⦗(mapper ↑₁ E_t ∪₁ eq a_t) ∩₁ Rel G_s'⦘
                  ⊆ mapper' ↑ ⦗E_t' ∩₁ Rel G_t'⦘).
            { intros x y COND. destruct COND as (EQ & COND); subst y.
              destruct COND as (INE & COND).
              apply EQACT in INE.
              destruct INE as [x' [INE MAP]].
              unfold set_collect.
              exists x', x'.
              splits; vauto. split; vauto.
              split; vauto.
              unfold is_rel. unfold mod. destruct (rsr_lab SIMREL') with x'; vauto.
              unfold compose. unfold is_rel in COND. unfold mod in COND.
              rewrite MAP; vauto. }
            arewrite (⦗mapper ↑₁ E_t⦘ ⨾ mapper' ↑ sb_t' ⨾ mapper' ↑ ⦗E_t' ∩₁ Rel G_t'⦘
                  ⊆ mapper' ↑ ⦗E_t'⦘ ⨾ mapper' ↑ sb_t' ⨾ mapper' ↑ ⦗E_t' ∩₁ Rel G_t'⦘).
            { do 2 hahn_frame_r. rewrite collect_rel_eqv.
              rewrite <- MAPSUB.
              rewrite EQACTS. basic_solver. }
            arewrite (⦗F G_s' ∩₁ Rel G_s' ∩₁ mapper ↑₁ E_t⦘
                    ⊆ mapper' ↑ ⦗F G_t' ∩₁ Rel G_t' ∩₁ E_t'⦘).
            { intros x y COND. destruct COND as (EQ & COND); subst y.
              destruct COND as ((COND1 & COND2) & INE).
              destruct INE as [x' [INE MAP]].
              unfold set_collect.
              exists x', x'.
              assert (MAP' : mapper' x' = x).
              { rewrite <- MAP.
                unfold mapper'. rupd.
                intros FALSE. apply ENOTIN.
                rewrite FALSE in INE; vauto. }
              splits; vauto. split; vauto.
              split.
              { split.
                { unfold G_s' in COND1; ins.
                  unfold is_f. destruct (rsr_lab SIMREL) with x'; vauto.
                  unfold compose. unfold is_f in COND1.
                  rewrite !updo in COND1; vauto.
                  { arewrite (lab_t' x' = lab_t x').
                    rewrite <- MAP in COND1.
                    destruct (rsr_lab SIMREL) with x'; vauto. }
                  { apply NOTEQ in INE. congruence. }
                  intros FALSE. rewrite FALSE in MAP.
                  assert (INEN : E_t x'); vauto.
                  apply NOTEQ in INE. congruence. }
                unfold G_s' in COND2; ins.
                unfold is_rel. unfold mod. destruct (rsr_lab SIMREL) with x'; vauto.
                unfold compose. unfold is_rel in COND2. unfold mod in COND2.
                rewrite !updo in COND2; vauto.
                { arewrite (lab_t' x' = lab_t x').
                  rewrite <- MAP in COND2.
                  destruct (rsr_lab SIMREL) with x'; vauto. }
                { apply NOTEQ in INE. congruence. }
                intros FALSE. rewrite FALSE in MAP.
                assert (INEN : E_t x'); vauto.
                apply NOTEQ in INE. congruence. }
              apply EQACTS; vauto. }
            arewrite (⦗(mapper ↑₁ E_t ∪₁ eq a_t) ∩₁ W G_s' ∩₁ Rlx G_s'⦘
                    ⊆ mapper' ↑ ⦗E_t' ∩₁ W G_t' ∩₁ Rlx G_t'⦘).
            { intros x y COND. destruct COND as (EQ & COND); subst y.
              destruct COND as ((INE & COND1) & COND2).
              apply EQACT in INE.
              destruct INE as [x' [INE MAP]].
              unfold set_collect.
              exists x', x'.
              splits; vauto. split; vauto.
              split.
              { split; vauto.
                unfold is_w. destruct (rsr_lab SIMREL') with x'; vauto.
                unfold compose. unfold is_w in COND1.
                rewrite MAP; vauto. }
              unfold is_rlx. unfold mod. destruct (rsr_lab SIMREL') with x'; vauto.
              unfold compose. unfold is_rlx in COND2. unfold mod in COND2.
              rewrite MAP; vauto. }
            rewrite !collect_rel_union.
            apply union_more.
            { apply union_more.
              { apply union_more.
                { rewrite !collect_rel_seq; vauto.
                  { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
                    { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
                    assert (IN2 : dom_rel ⦗E_t' ∩₁ F G_t' ∩₁ Acq G_t'⦘ ⊆₁ E_t').
                    { clear - ANOTINS. basic_solver. }
                    rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
                    eapply (rsr_inj SIMREL'). }
                  assert (IN1 : codom_rel ⦗R_t' ∩₁ Rlx G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
                  { clear - ANOTINS. basic_solver. }
                  assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t' ∩₁ F G_t' ∩₁ Acq G_t'⦘) ⊆₁ E_t').
                  { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
                  rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
                  eapply (rsr_inj SIMREL'). }
                rewrite !collect_rel_seq; vauto.
                { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
                  { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
                  assert (IN2 : dom_rel ⦗E_t'⦘ ⊆₁ E_t').
                  { clear - ANOTINS. basic_solver. }
                  rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
                  eapply (rsr_inj SIMREL'). }
                assert (IN1 : codom_rel ⦗Acq G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
                { clear - ANOTINS. basic_solver. }
                assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t'⦘) ⊆₁ E_t').
                { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
                rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
                eapply (rsr_inj SIMREL'). }
              rewrite !collect_rel_seq; vauto.
              { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
                { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
                assert (IN2 : dom_rel ⦗E_t' ∩₁ Rel G_t'⦘ ⊆₁ E_t').
                { clear - ANOTINS. basic_solver. }
                rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
                eapply (rsr_inj SIMREL'). }
              assert (IN1 : codom_rel ⦗E_t'⦘ ⊆₁ E_t').
              { clear - ANOTINS. basic_solver. }
              assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t' ∩₁ Rel G_t'⦘) ⊆₁ E_t').
              { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
              rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
              eapply (rsr_inj SIMREL'). }
            rewrite !collect_rel_seq; vauto.
            { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
              { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
              assert (IN2 : dom_rel ⦗E_t' ∩₁ W_t' ∩₁ Rlx G_t'⦘ ⊆₁ E_t').
              { clear - ANOTINS. basic_solver. }
              rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
              eapply (rsr_inj SIMREL'). }
            assert (IN1 : codom_rel ⦗F G_t' ∩₁ Rel G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
            { clear - ANOTINS. basic_solver. }
            assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t' ∩₁ W_t' ∩₁ Rlx G_t'⦘) ⊆₁ E_t').
            { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
            rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
            eapply (rsr_inj SIMREL'). }
          assert (IND2 : mapper' ↑ (rpo_imm G_t')⁺ ⨾ ⦗E_s⦘ ⨾ (rpo_imm G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘)
            ⊆ mapper' ↑ (rpo_imm G_t')⁺).
          { assert (TRIN : mapper' ↑ (rpo_imm G_t')⁺ ⨾ mapper' ↑ (rpo_imm G_t')⁺
                          ⊆ mapper' ↑ (rpo_imm G_t')⁺).
          { intros x y PATH. destruct PATH as (x0 & P1 & P2).
            unfold collect_rel in P1, P2. unfold collect_rel.
            destruct P1 as (x' & x0' & (P1 & M1 & M2)).
            destruct P2 as (x0'' & y' & (P2 & M3 & M4)).
            exists x', y'. splits; vauto.
            assert (EQ : x0'' = x0').
            { apply (rsr_inj SIMREL'); vauto.
              { apply ct_begin in P2.
                destruct P2 as (x1 & P2 & P3).
                apply wf_rpo_immE in P2; vauto.
                destruct P2 as (x2 & INE & REST).
                destruct INE as (EQ & INEN); subst x2; vauto. }
              { apply ct_end in P1.
                destruct P1 as (x1 & P1 & P1').
                apply wf_rpo_immE in P1'; vauto.
                destruct P1' as (x2 & P3 & (x3 & P4 & (EQ & P5))); vauto.
                subst x3; vauto. }
            clear -M2 M3. congruence. }
            subst x0''. apply ct_ct.
            unfold seq. exists x0'. splits; vauto. }
          rewrite <- TRIN at 2. apply seq_mori; vauto. }
          apply inclusion_t_ind_right; vauto. }
        rewrite rpo_in_sb. unfold sb; ins. rewrite NEWSB.
        rewrite (WCore.add_event_sb ADD').
        rewrite (WCore.add_event_acts ADD').
        rewrite !seq_union_l. rewrite !seq_union_r.
        arewrite_false (⦗eq a_t⦘ ⨾ sb_s ⨾ ⦗E_s ∪₁ eq a_t⦘).
        { clear - NOTIN. rewrite wf_sbE.
          rewrite !seqA.
          mode_solver 21. }
        arewrite_false (⦗eq a_t⦘ ⨾ WCore.sb_delta b_t E_s ⨾ ⦗E_s ∪₁ eq a_t⦘).
        { unfold WCore.sb_delta. destruct INV'.
          intros x y PATH.
          destruct PATH as (x0 & (EQ & EQA) & (x1 & PTH & (EQ' & EQQ))).
          subst x0; subst x; subst x1.
          destruct PTH as (PTH & EQB). subst y.
          clear - ANOTINS ANOTB EQQ.
          destruct EQQ as [EQQ | EQQ]; vauto. }
        arewrite_false (⦗eq a_t⦘ ⨾ WCore.sb_delta a_t (E_s ∪₁ eq b_t) ⨾ ⦗E_s ∪₁ eq a_t⦘).
        { unfold WCore.sb_delta. destruct INV'.
          intros x y PATH.
          destruct PATH as (x0 & (EQ & EQA) & (x1 & PTH & (EQ' & EQQ))).
          subst x0; subst x; subst x1.
          destruct PTH as (PTH & EQB). subst y.
          destruct PTH as [PTH | PTH]; vauto.
          destruct PTH as (PTH1 & PTH2).
          clear - NOTIN PTH1.
          basic_solver. }
        basic_solver. }
      arewrite_false (⦗eq b_t⦘ ⨾ rpo G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘); vauto.
      destruct RPOCODOM as [IN OUT].
      arewrite_id ⦗E_s ∪₁ eq a_t⦘. rels. }
    { split; [|basic_solver].
      rewrite <- seq_eqv_inter_ll.
      rewrite SBFROMA. unfolder.
      intros x (y & (XEQ & YEQ) & LOC).
      subst x; subst y.
      unfold same_loc, loc in LOC.
      unfold G_s' in LOC; ins.
      rewrite updo in LOC; auto.
      rewrite !upds in LOC.
      apply NEQLOQ'. unfold WCore.lab_loc.
      congruence. }
    { arewrite (G_s' = WCore.G X_s').
      rewrite (rsr_sb SIMREL'). rewrite !NEWEXA.
      arewrite (eq a_t ∩₁ E_t' ≡₁ ∅).
      { clear - ANOTIN'. basic_solver. }
      arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t).
      { split; [basic_solver |].
        rewrite EQACTS. basic_solver 8. }
      arewrite (mapper' b_t = a_t).
      rewrite !inter_union_l.
      rewrite !seq_union_l.
      repeat apply inclusion_union_l.
      { unfold swap_rel. rels.
        intros x y (z & (COND & INSET)).
        destruct COND as (MAP & SL).
        destruct MAP as (x' & z' & SB & M1 & M2).
        unfold collect_rel.
        exists x'. exists z'. splits; eauto.
        { split; eauto.
          unfold same_loc in SL.
          unfold loc in SL.
          assert (ACTEQ : WCore.G X_s' = G_s') by basic_solver.
          rewrite ACTEQ in SL. unfold same_loc.
          unfold loc.
          arewrite (lab_t' x' = lab G_s' x).
            { destruct (rsr_lab SIMREL') with x'.
              { destruct SB as (x0 & (C1 & EQ) & C2); vauto. }
              unfold compose. clear - M1; basic_solver. }
          arewrite (lab_t' z' = lab G_s' z).
            { destruct (rsr_lab SIMREL') with z'.
              { destruct SB as (x0 & C1 & (x2 & C2 & (IN & EQ))).
                clear - IN EQ. basic_solver. }
              unfold compose. clear - M2; basic_solver. }
            vauto. }
        destruct INSET as (EQ & COND).
        clear - EQ M2; congruence. }
      { basic_solver 21. }
      unfolder. intros x y (((EQ1 & EQ2) & SL) & (ACTS & NEQ)).
      subst x; subst y.
      unfold same_loc, loc in SL.
      unfold G_s' in SL; ins.
      rewrite updo in SL; auto.
      rewrite !upds in SL.
      exfalso.
      apply NEQLOQ'. unfold WCore.lab_loc.
      congruence. }
    { arewrite (G_s' = WCore.G X_s').
      rewrite (rsr_rf SIMREL'). apply union_more; vauto.
      apply seq_more; vauto.
      rewrite NEWEXA. split; [basic_solver|].
      split.
      { destruct H; vauto. }
      split; vauto.
      { destruct H; vauto. }
      destruct H; subst x y; vauto. }
    { arewrite (G_s' = WCore.G X_s').
      rewrite (rsr_co SIMREL'). unfold add_max.
      rewrite NEWEXA.
      arewrite ((extra_co_D (acts_set (WCore.G X_s')) (lab (WCore.G X_s'))
                (loc (lab (WCore.G X_s')) b_t) \₁ eq b_t ∩₁ W (WCore.G X_s'))
                  × (eq b_t ∩₁ W (WCore.G X_s')) ≡ ∅₂); [| basic_solver 8].
      arewrite (eq b_t ∩₁ W (WCore.G X_s') ≡₁ ∅); [| basic_solver 8].
      split; [|basic_solver].
      intros x (EQ & INW); subst x.
      unfold is_r, is_w in *; basic_solver. }
    apply G_s_wf with (X_t := X_t') (X_s := X_s')
          (a_t := a_t) (b_t := b_t) (mapper := mapper'); vauto. }
  apply XmmCons.write_extent with (G_t := G_t')
            (sc_t := WCore.sc X_t') (a := b_t) (m := mapper'); eauto.
  { apply SIMREL'; vauto. }
  { unfold G_s'; ins.
    rewrite (rsr_acts SIMREL). rewrite OLDEXA.
    rewrite EQACTS. rewrite set_collect_union; eauto.
    rewrite MAPER_E. rewrite MAPSUB; basic_solver 12. }
  { apply SIMREL'; vauto. }
  { rewrite EQACTS.
    rewrite set_collect_union, MAPER_E, MAPSUB, (rsr_codom SIMREL).
    rewrite OLDEXA; rels. intros FLS.
    destruct FLS as [FLS | FLS].
    { destruct ANOTINS.
      destruct FLS; vauto. }
    destruct ANOTB; vauto. }
  { arewrite (rpo G_s' ⊆ ⦗acts_set G_s'⦘ ⨾ rpo G_s').
    { rewrite wf_rpoE. basic_solver 8. }
    unfold G_s' at 1; ins.
    arewrite ((E_s ∪₁ eq b_t ∪₁ eq a_t) \₁ eq b_t ≡₁
              E_s ∪₁ eq a_t).
    { clear - ANOTB ANOTINS.
      rewrite !set_minus_union_l.
      arewrite (E_s \₁ eq b_t ≡₁ E_s).
      { split; [basic_solver |].
        unfold set_minus.
        intros x INE. split; vauto.
        intros FALSE; basic_solver. }
      basic_solver. }
    rewrite set_unionA.
    rewrite set_unionC with (s := eq b_t).
    rewrite <- set_unionA.
    rewrite id_union. rewrite seq_union_l.
    apply inclusion_union_l.
    { rewrite id_union at 1. rewrite seq_union_l.
      apply inclusion_union_l.
      { unfold rpo. transitivity ((⦗E_s⦘ ⨾ rpo_imm G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘)⁺).
        { induction 1 as (x0 & (P1 & (x1 & (P2 & P3)))).
          destruct P1 as (EQ & COND1); subst x0.
          destruct P3 as (EQ & COND2); subst x1.
          induction P2 as [x y STT | x].
          { apply ct_step. unfold seq. exists x. splits; vauto. }
          apply ct_begin in P2_2. destruct P2_2 as (x0 & P1 & P2).
          eapply RPOIMMST in P1; vauto.
          destruct P1 as (x1 & (EQ' & COND') & P1); subst x1.
          destruct COND' as [COND' | COND'].
          { assert (COND'' : E_s y) by vauto.
            apply IHP2_1 in COND1; vauto. apply IHP2_2 in COND''; vauto. }
          subst y. exfalso.
          apply rpo_imm_in_sb in P1.
          assert (GEQ : G_s' = WCore.G X_s') by vauto.
          rewrite GEQ in P1.
          apply (rsr_sb SIMREL') in P1.
          destruct P1 as [[P1 | P1] | P1].
          { assert (AEQQ : eq a_t ∩₁ E_t' ≡₁ ∅).
            { clear - ANOTIN'. basic_solver. }
            destruct P1 as (a' & x' & (C1 & C2 & C3)).
            unfold swap_rel in C1.
            destruct C1 as [C1 | C1].
            { assert (C1' : (sb_t') a' x').
              { clear - C1. unfold minus_rel in C1. desf. }
              apply wf_sbE in C1'.
              destruct C1' as (a0 & C1' & C1'').
              destruct C1' as (EQ & C1').
              rewrite MAPE in C2; subst a0.
              apply (rsr_inj SIMREL') in C2; vauto.
              { destruct C1'' as (x1 & PTH & (EQ & INE)).
                subst x1. subst a'. destruct INV'.
                assert (C1'' : E_t' b_t) by vauto.
                apply rsr_bt_max in C1'; vauto.
                clear - PTH C1' C1''.
                destruct C1' with b_t x'.
                basic_solver 21. }
              apply EQACTS. basic_solver. }
            rewrite MAPE in C2.
            apply (rsr_inj SIMREL') in C2; vauto.
            { destruct C1 as (C1 & C1').
              subst a'. clear - C1 ANOTB.
              destruct C1; vauto. }
            { clear - C1. destruct C1 as (C1 & C1').
              destruct C1; vauto. }
            apply EQACTS. basic_solver. }
          { destruct P1 as (P1 & P1').
            destruct P1 as (a0 & (DOM & MAP)).
            destruct DOM as (a1 & (a2 & SBPTH & CD)).
            apply wf_sbE in SBPTH.
            destruct SBPTH as (a3 & (EQ & CND) & CND').
            destruct CND' as (a4 & (EQ' & (EQ2 &CND'))).
            subst a4. subst a3.
            destruct CD as (EQ1 & EQB). subst a2. subst a1.
            rewrite MAPE in MAP.
            apply (rsr_inj SIMREL') in MAP; vauto.
            subst a0. apply sb_irr in EQ'. done. }
          destruct P1 as (P1 & P1').
          apply NEWEXA in P1. clear - P1 ANOTB; vauto. }
        assert (IND1 : (⦗E_s⦘ ⨾ rpo_imm G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘) ⊆ mapper' ↑ (rpo_imm G_t')⁺).
        { unfold rpo_imm. rewrite !seq_union_l. rewrite !seqA.
          rewrite <- ct_step.
          rewrite !seq_union_r.
          arewrite (sb_t' ≡ ⦗E_t'⦘ ⨾ sb_t' ⨾ ⦗E_t'⦘).
          { rewrite wf_sbE. basic_solver 11. }
          rewrite <- seqA. rewrite seq_eqvC.
          rewrite seqA. rewrite seq_eqvC.
          arewrite (⦗E_s⦘ ⨾ ⦗Acq G_s'⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ≡
                    ⦗Acq G_s'⦘ ⨾ ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘).
          { rewrite <- seqA. rewrite seq_eqvC; basic_solver. }
          arewrite (⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗Rel G_s'⦘ ⨾ ⦗E_s ∪₁ eq a_t⦘ ≡
                    ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗Rel G_s'⦘).
          { rewrite <- seqA. rewrite seq_eqvC; basic_solver. }
          arewrite (⦗E_s⦘ ⨾ ⦗F G_s' ∩₁ Rel G_s'⦘ ⨾ sb G_s' ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘ ⨾ ⦗E_s ∪₁ eq a_t⦘ ≡
                    ⦗F G_s' ∩₁ Rel G_s'⦘ ⨾ ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘).
          { rewrite seq_eqvC. rewrite <- seqA. rewrite seq_eqvC. basic_solver. }
          assert (SBSUB : ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⊆ ⦗E_s⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗E_s ∪₁ eq a_t⦘).
          { arewrite (G_s' = WCore.G X_s').
            rewrite (rsr_sb SIMREL'). unfold swap_rel.
            rewrite !NEWEXA.
            arewrite (eq a_t ∩₁ E_t' ≡₁ ∅).
            { clear - ANOTIN'. basic_solver. }
            arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t).
            { split; [basic_solver |].
              rewrite EQACTS. basic_solver 8. }
            arewrite (mapper' b_t = a_t).
            clear - ANOTINS NOTIN ANOTB.
            rewrite !seq_union_l. rewrite !seq_union_r.
            rels. apply inclusion_union_l.
            { apply inclusion_union_l; vauto.
              intros x y PATH. destruct PATH as (z & (C1 & C2) & C3).
              destruct C3 as (x0 & (C4 & C5) & C6). subst x0.
              clear -C6 ANOTINS ANOTB. exfalso.
              destruct C6 as (EQ & COND).
              destruct COND as [COND | COND].
              { apply ANOTINS. rewrite EQ. vauto. }
              apply ANOTB. rewrite EQ. vauto. }
            basic_solver 21. }
          arewrite (⦗R G_s' ∩₁ Rlx G_s'⦘ ⨾ ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗F G_s' ∩₁ Acq G_s'⦘
                    ⊆ ⦗R G_s' ∩₁ Rlx G_s'⦘ ⨾ ⦗E_s⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗F G_s' ∩₁ Acq G_s'⦘).
          { clear - SBSUB. hahn_frame_l. hahn_frame_r; vauto. }
          arewrite (⦗Acq G_s'⦘ ⨾ ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘
                    ⊆ ⦗Acq G_s'⦘ ⨾ ⦗E_s⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗E_s ∪₁ eq a_t⦘).
          arewrite (⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗Rel G_s'⦘
                    ⊆ ⦗E_s⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗Rel G_s'⦘).
          { clear - SBSUB. hahn_frame_r; vauto. }
          arewrite (⦗F G_s' ∩₁ Rel G_s'⦘ ⨾ ⦗E_s⦘ ⨾ sb G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘
                    ⊆ ⦗F G_s' ∩₁ Rel G_s'⦘ ⨾ ⦗E_s⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗E_s ∪₁ eq a_t⦘ ⨾ ⦗W G_s' ∩₁ Rlx G_s'⦘).
          { clear - SBSUB. hahn_frame_l. hahn_frame_r; vauto. }
          rewrite <- !id_inter. rewrite <- !seqA.
          rewrite <- !id_inter. rewrite !seqA.
          rewrite <- !set_interA.
          rewrite (rsr_acts SIMREL).
          rewrite OLDEXA. rewrite !set_union_empty_r.
          assert (NOTEQ : forall x , E_t x -> mapper x = x).
          { intros x XINE. apply (rsr_mid SIMREL).
            clear - XINE ENOTIN ANOTIN.
            unfold set_minus. split.
            { split; vauto. intros FALSE. apply ANOTIN.
              rewrite FALSE; vauto. }
            intros FALSE. apply ENOTIN.
            rewrite FALSE; vauto. }
          arewrite (⦗R G_s' ∩₁ Rlx G_s' ∩₁ mapper ↑₁ E_t⦘
                      ⊆ mapper' ↑ ⦗R_t' ∩₁ Rlx G_t' ∩₁ E_t'⦘).
          { intros x y COND. destruct COND as (EQ & COND); subst y.
            destruct COND as ((COND1 & COND2) & INE).
            destruct INE as [x' [INE MAP]].
            unfold set_collect.
            exists x', x'.
            assert (MAP' : mapper' x' = x).
            { rewrite <- MAP.
              unfold mapper'. rupd.
              intros FALSE. apply ENOTIN.
              rewrite FALSE in INE; vauto. }
            splits; vauto. split; vauto.
            split.
            { split.
              { unfold G_s' in COND1; ins.
                unfold is_r. destruct (rsr_lab SIMREL) with x'; vauto.
                unfold compose. unfold is_r in COND1.
                rewrite !updo in COND1; vauto.
                { arewrite (lab_t' x' = lab_t x').
                  rewrite <- MAP in COND1.
                  destruct (rsr_lab SIMREL) with x'; vauto. }
                { apply NOTEQ in INE. congruence. }
                intros FALSE. rewrite FALSE in MAP.
                assert (INEN : E_t x'); vauto.
                apply NOTEQ in INE. congruence. }
              unfold G_s' in COND2; ins.
              unfold is_rlx. unfold mod. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_rlx in COND2. unfold mod in COND2.
              rewrite !updo in COND2; vauto.
              { arewrite (lab_t' x' = lab_t x').
                rewrite <- MAP in COND2.
                destruct (rsr_lab SIMREL) with x'; vauto. }
              { apply NOTEQ in INE. congruence. }
              intros FALSE. rewrite FALSE in MAP.
              assert (INEN : E_t x'); vauto.
              apply NOTEQ in INE. congruence. }
            apply EQACTS; vauto. }
          assert (EQACT : mapper ↑₁ E_t ∪₁ eq a_t ≡₁ mapper' ↑₁ E_t').
          { rewrite EQACTS. rewrite set_collect_union.
            rewrite MAPER_E. rewrite MAPSUB. basic_solver. }
          arewrite (⦗(mapper ↑₁ E_t ∪₁ eq a_t) ∩₁ F G_s' ∩₁ Acq G_s'⦘
                      ⊆ mapper' ↑ ⦗E_t' ∩₁ F G_t' ∩₁ Acq G_t'⦘).
          { intros x y COND. destruct COND as (EQ & COND); subst y.
            destruct COND as ((INE & COND1) & COND2).
            apply EQACT in INE.
            destruct INE as [x' [INE MAP]].
            unfold set_collect.
            exists x', x'.
            split; vauto. split; vauto.
            split.
            { split; vauto.
              unfold is_f. destruct (rsr_lab SIMREL') with x'; vauto.
              unfold compose. rewrite MAP; vauto. }
            unfold is_acq. unfold mod.
            destruct (rsr_lab SIMREL') with x'; vauto.
            unfold compose. unfold is_acq in COND2. unfold mod in COND2.
            rewrite MAP; vauto. }
          arewrite (⦗Acq G_s' ∩₁ mapper ↑₁ E_t⦘
                      ⊆ mapper' ↑ ⦗Acq G_t' ∩₁ E_t'⦘).
          { intros x y COND. destruct COND as (EQ & COND); subst y.
            destruct COND as (COND1 & INE).
            destruct INE as [x' [INE MAP]].
            unfold set_collect.
            exists x', x'.
            assert (MAP' : mapper' x' = x).
            { rewrite <- MAP.
              unfold mapper'. rupd.
              intros FALSE. apply ENOTIN.
              rewrite FALSE in INE; vauto. }
            splits; vauto. split; vauto.
            split.
            { unfold G_s' in COND1; ins.
              unfold is_acq. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_acq in COND1.
              unfold mod in COND1. unfold mod.
              rewrite !updo in COND1; vauto.
              { arewrite (lab_t' x' = lab_t x').
                rewrite <- MAP in COND1.
                destruct (rsr_lab SIMREL) with x'; vauto. }
              { apply NOTEQ in INE. congruence. }
              intros FALSE. rewrite FALSE in MAP.
              assert (INEN : E_t x'); vauto.
              apply NOTEQ in INE. congruence. }
            apply EQACTS; vauto. }
          arewrite (mapper' ↑ ⦗Acq G_t' ∩₁ E_t'⦘ ⨾ mapper' ↑ sb_t' ⨾ ⦗mapper ↑₁ E_t  ∪₁ eq a_t⦘
                ⊆ mapper' ↑ ⦗Acq G_t' ∩₁ E_t'⦘ ⨾ mapper' ↑ sb_t' ⨾ mapper' ↑ ⦗E_t'⦘).
          { do 2 hahn_frame_l. rewrite collect_rel_eqv.
            rewrite <- MAPSUB. rewrite <- EQACT.
            rewrite MAPSUB. basic_solver. }
          arewrite (⦗(mapper ↑₁ E_t ∪₁ eq a_t) ∩₁ Rel G_s'⦘
                ⊆ mapper' ↑ ⦗E_t' ∩₁ Rel G_t'⦘).
          { intros x y COND. destruct COND as (EQ & COND); subst y.
            destruct COND as (INE & COND).
            apply EQACT in INE.
            destruct INE as [x' [INE MAP]].
            unfold set_collect.
            exists x', x'.
            splits; vauto. split; vauto.
            split; vauto.
            unfold is_rel. unfold mod. destruct (rsr_lab SIMREL') with x'; vauto.
            unfold compose. unfold is_rel in COND. unfold mod in COND.
            rewrite MAP; vauto. }
          arewrite (⦗mapper ↑₁ E_t⦘ ⨾ mapper' ↑ sb_t' ⨾ mapper' ↑ ⦗E_t' ∩₁ Rel G_t'⦘
                ⊆ mapper' ↑ ⦗E_t'⦘ ⨾ mapper' ↑ sb_t' ⨾ mapper' ↑ ⦗E_t' ∩₁ Rel G_t'⦘).
          { do 2 hahn_frame_r. rewrite collect_rel_eqv.
            rewrite <- MAPSUB.
            rewrite EQACTS. basic_solver. }
          arewrite (⦗F G_s' ∩₁ Rel G_s' ∩₁ mapper ↑₁ E_t⦘
                  ⊆ mapper' ↑ ⦗F G_t' ∩₁ Rel G_t' ∩₁ E_t'⦘).
          { intros x y COND. destruct COND as (EQ & COND); subst y.
            destruct COND as ((COND1 & COND2) & INE).
            destruct INE as [x' [INE MAP]].
            unfold set_collect.
            exists x', x'.
            assert (MAP' : mapper' x' = x).
            { rewrite <- MAP.
              unfold mapper'. rupd.
              intros FALSE. apply ENOTIN.
              rewrite FALSE in INE; vauto. }
            splits; vauto. split; vauto.
            split.
            { split.
              { unfold G_s' in COND1; ins.
                unfold is_f. destruct (rsr_lab SIMREL) with x'; vauto.
                unfold compose. unfold is_f in COND1.
                rewrite !updo in COND1; vauto.
                { arewrite (lab_t' x' = lab_t x').
                  rewrite <- MAP in COND1.
                  destruct (rsr_lab SIMREL) with x'; vauto. }
                { apply NOTEQ in INE. congruence. }
                intros FALSE. rewrite FALSE in MAP.
                assert (INEN : E_t x'); vauto.
                apply NOTEQ in INE. congruence. }
              unfold G_s' in COND2; ins.
              unfold is_rel. unfold mod. destruct (rsr_lab SIMREL) with x'; vauto.
              unfold compose. unfold is_rel in COND2. unfold mod in COND2.
              rewrite !updo in COND2; vauto.
              { arewrite (lab_t' x' = lab_t x').
                rewrite <- MAP in COND2.
                destruct (rsr_lab SIMREL) with x'; vauto. }
              { apply NOTEQ in INE. congruence. }
              intros FALSE. rewrite FALSE in MAP.
              assert (INEN : E_t x'); vauto.
              apply NOTEQ in INE. congruence. }
            apply EQACTS; vauto. }
          arewrite (⦗(mapper ↑₁ E_t ∪₁ eq a_t) ∩₁ W G_s' ∩₁ Rlx G_s'⦘
                  ⊆ mapper' ↑ ⦗E_t' ∩₁ W G_t' ∩₁ Rlx G_t'⦘).
          { intros x y COND. destruct COND as (EQ & COND); subst y.
            destruct COND as ((INE & COND1) & COND2).
            apply EQACT in INE.
            destruct INE as [x' [INE MAP]].
            unfold set_collect.
            exists x', x'.
            splits; vauto. split; vauto.
            split.
            { split; vauto.
              unfold is_w. destruct (rsr_lab SIMREL') with x'; vauto.
              unfold compose. unfold is_w in COND1.
              rewrite MAP; vauto. }
            unfold is_rlx. unfold mod. destruct (rsr_lab SIMREL') with x'; vauto.
            unfold compose. unfold is_rlx in COND2. unfold mod in COND2.
            rewrite MAP; vauto. }
          rewrite !collect_rel_union.
          apply union_more.
          { apply union_more.
            { apply union_more.
              { rewrite !collect_rel_seq; vauto.
                { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
                  { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
                  assert (IN2 : dom_rel ⦗E_t' ∩₁ F G_t' ∩₁ Acq G_t'⦘ ⊆₁ E_t').
                  { clear - ANOTINS. basic_solver. }
                  rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
                  eapply (rsr_inj SIMREL'). }
                assert (IN1 : codom_rel ⦗R_t' ∩₁ Rlx G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
                { clear - ANOTINS. basic_solver. }
                assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t' ∩₁ F G_t' ∩₁ Acq G_t'⦘) ⊆₁ E_t').
                { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
                rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
                eapply (rsr_inj SIMREL'). }
              rewrite !collect_rel_seq; vauto.
              { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
                { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
                assert (IN2 : dom_rel ⦗E_t'⦘ ⊆₁ E_t').
                { clear - ANOTINS. basic_solver. }
                rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
                eapply (rsr_inj SIMREL'). }
              assert (IN1 : codom_rel ⦗Acq G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
              { clear - ANOTINS. basic_solver. }
              assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t'⦘) ⊆₁ E_t').
              { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
              rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
              eapply (rsr_inj SIMREL'). }
            rewrite !collect_rel_seq; vauto.
            { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
              { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
              assert (IN2 : dom_rel ⦗E_t' ∩₁ Rel G_t'⦘ ⊆₁ E_t').
              { clear - ANOTINS. basic_solver. }
              rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
              eapply (rsr_inj SIMREL'). }
            assert (IN1 : codom_rel ⦗E_t'⦘ ⊆₁ E_t').
            { clear - ANOTINS. basic_solver. }
            assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t' ∩₁ Rel G_t'⦘) ⊆₁ E_t').
            { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
            rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
            eapply (rsr_inj SIMREL'). }
          rewrite !collect_rel_seq; vauto.
          { assert (IN1 : codom_rel sb_t' ⊆₁ E_t').
            { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
            assert (IN2 : dom_rel ⦗E_t' ∩₁ W_t' ∩₁ Rlx G_t'⦘ ⊆₁ E_t').
            { clear - ANOTINS. basic_solver. }
            rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
            eapply (rsr_inj SIMREL'). }
          assert (IN1 : codom_rel ⦗F G_t' ∩₁ Rel G_t' ∩₁ E_t'⦘ ⊆₁ E_t').
          { clear - ANOTINS. basic_solver. }
          assert (IN2 : dom_rel (sb_t' ⨾ ⦗E_t' ∩₁ W_t' ∩₁ Rlx G_t'⦘) ⊆₁ E_t').
          { clear - ANOTINS. rewrite wf_sbE. basic_solver. }
          rewrite IN1, IN2. arewrite (E_t' ∪₁ E_t' ≡₁ E_t'); [basic_solver|].
          eapply (rsr_inj SIMREL'). }
        assert (IND2 : mapper' ↑ (rpo_imm G_t')⁺ ⨾ ⦗E_s⦘ ⨾ (rpo_imm G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘)
          ⊆ mapper' ↑ (rpo_imm G_t')⁺).
        { assert (TRIN : mapper' ↑ (rpo_imm G_t')⁺ ⨾ mapper' ↑ (rpo_imm G_t')⁺
                        ⊆ mapper' ↑ (rpo_imm G_t')⁺).
        { intros x y PATH. destruct PATH as (x0 & P1 & P2).
          unfold collect_rel in P1, P2. unfold collect_rel.
          destruct P1 as (x' & x0' & (P1 & M1 & M2)).
          destruct P2 as (x0'' & y' & (P2 & M3 & M4)).
          exists x', y'. splits; vauto.
          assert (EQ : x0'' = x0').
          { apply (rsr_inj SIMREL'); vauto.
            { apply ct_begin in P2.
              destruct P2 as (x1 & P2 & P3).
              apply wf_rpo_immE in P2; vauto.
              destruct P2 as (x2 & INE & REST).
              destruct INE as (EQ & INEN); subst x2; vauto. }
            { apply ct_end in P1.
              destruct P1 as (x1 & P1 & P1').
              apply wf_rpo_immE in P1'; vauto.
              destruct P1' as (x2 & P3 & (x3 & P4 & (EQ & P5))); vauto.
              subst x3; vauto. }
          clear -M2 M3. congruence. }
          subst x0''. apply ct_ct.
          unfold seq. exists x0'. splits; vauto. }
        rewrite <- TRIN at 2. apply seq_mori; vauto. }
        apply inclusion_t_ind_right; vauto. }
      rewrite rpo_in_sb. unfold sb; ins. rewrite NEWSB.
      rewrite (WCore.add_event_sb ADD').
      rewrite (WCore.add_event_acts ADD').
      rewrite !seq_union_l. rewrite !seq_union_r.
      arewrite_false (⦗eq a_t⦘ ⨾ sb_s ⨾ ⦗E_s ∪₁ eq a_t⦘).
      { clear - NOTIN. rewrite wf_sbE.
        rewrite !seqA.
        mode_solver 21. }
      arewrite_false (⦗eq a_t⦘ ⨾ WCore.sb_delta b_t E_s ⨾ ⦗E_s ∪₁ eq a_t⦘).
      { unfold WCore.sb_delta. destruct INV'.
        intros x y PATH.
        destruct PATH as (x0 & (EQ & EQA) & (x1 & PTH & (EQ' & EQQ))).
        subst x0; subst x; subst x1.
        destruct PTH as (PTH & EQB). subst y.
        clear - ANOTINS ANOTB EQQ.
        destruct EQQ as [EQQ | EQQ]; vauto. }
      arewrite_false (⦗eq a_t⦘ ⨾ WCore.sb_delta a_t (E_s ∪₁ eq b_t) ⨾ ⦗E_s ∪₁ eq a_t⦘).
      { unfold WCore.sb_delta. destruct INV'.
        intros x y PATH.
        destruct PATH as (x0 & (EQ & EQA) & (x1 & PTH & (EQ' & EQQ))).
        subst x0; subst x; subst x1.
        destruct PTH as (PTH & EQB). subst y.
        destruct PTH as [PTH | PTH]; vauto.
        destruct PTH as (PTH1 & PTH2).
        clear - NOTIN PTH1.
        basic_solver. }
      basic_solver. }
    arewrite_false (⦗eq b_t⦘ ⨾ rpo G_s' ⨾ ⦗E_s ∪₁ eq a_t⦘); vauto.
    destruct RPOCODOM as [IN OUT].
    arewrite_id ⦗E_s ∪₁ eq a_t⦘. rels. }
  { split; [|basic_solver].
    rewrite <- seq_eqv_inter_ll.
    rewrite SBFROMA. unfolder.
    intros x (y & (XEQ & YEQ) & LOC).
    subst x; subst y.
    unfold same_loc, loc in LOC.
    unfold G_s' in LOC; ins.
    rewrite updo in LOC; auto.
    rewrite !upds in LOC.
    apply NEQLOQ'. unfold WCore.lab_loc.
    congruence. }
  { arewrite (G_s' = WCore.G X_s').
    rewrite (rsr_sb SIMREL'). rewrite !NEWEXA.
    arewrite (eq a_t ∩₁ E_t' ≡₁ ∅).
    { clear - ANOTIN'. basic_solver. }
    arewrite (eq b_t ∩₁ E_t' ≡₁ eq b_t).
    { split; [basic_solver |].
      rewrite EQACTS. basic_solver 8. }
    arewrite (mapper' b_t = a_t).
    rewrite !inter_union_l.
    rewrite !seq_union_l.
    repeat apply inclusion_union_l.
    { unfold swap_rel. rels.
      intros x y (z & (COND & INSET)).
      destruct COND as (MAP & SL).
      destruct MAP as (x' & z' & SB & M1 & M2).
      unfold collect_rel.
      exists x'. exists z'. splits; eauto.
      { split; eauto.
        unfold same_loc in SL.
        unfold loc in SL.
        assert (ACTEQ : WCore.G X_s' = G_s') by basic_solver.
        rewrite ACTEQ in SL. unfold same_loc.
        unfold loc.
        arewrite (lab_t' x' = lab G_s' x).
          { destruct (rsr_lab SIMREL') with x'.
            { destruct SB as (x0 & (C1 & EQ) & C2); vauto. }
            unfold compose. clear - M1; basic_solver. }
        arewrite (lab_t' z' = lab G_s' z).
          { destruct (rsr_lab SIMREL') with z'.
            { destruct SB as (x0 & C1 & (x2 & C2 & (IN & EQ))).
              clear - IN EQ. basic_solver. }
            unfold compose. clear - M2; basic_solver. }
          vauto. }
      destruct INSET as (EQ & COND).
      clear - EQ M2; congruence. }
    { basic_solver 21. }
    unfolder. intros x y (((EQ1 & EQ2) & SL) & (ACTS & NEQ)).
    subst x; subst y.
    unfold same_loc, loc in SL.
    unfold G_s' in SL; ins.
    rewrite updo in SL; auto.
    rewrite !upds in SL.
    exfalso.
    apply NEQLOQ'. unfold WCore.lab_loc.
    congruence. }
  { arewrite (G_s' = WCore.G X_s').
    rewrite (rsr_rf SIMREL'). rewrite NEWEXA.
    arewrite (eq b_t ∩₁ R (WCore.G X_s') ≡₁ ∅).
    { split; [| basic_solver].
      intros x (EQ & ISR); subst x.
      unfold is_w, is_r in *; basic_solver. }
    basic_solver 8. }
  { arewrite (G_s' = WCore.G X_s').
    rewrite (rsr_co SIMREL'). unfold add_max.
    rewrite NEWEXA. apply union_more; vauto.
    arewrite (eq b_t ∩₁ W (WCore.G X_s') ≡₁ eq b_t).
    { split; [basic_solver |].
      intros x XIN. split; vauto.
      subst x; vauto. }
    apply cross_more; vauto.
    unfold extra_co_D. unfold same_loc.
    basic_solver 42. }
  apply G_s_wf with (X_t := X_t') (X_s := X_s')
        (a_t := a_t) (b_t := b_t) (mapper := mapper'); vauto.
Admitted.

End ExecB.