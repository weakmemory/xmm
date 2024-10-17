Require Import ReordSimrel.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import PorfPrefix.

From PromisingLib Require Import Language Basic.
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
  set (sb_s' := ⦗E_s ∪₁ eq b_t⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq b_t⦘).
  set (srf_s' := (⦗Loc_s_ (WCore.lab_loc l_a)⦘ ⨾ vf_s ⨾ sb_s') \ (co_s ⨾ vf_s ⨾ sb_s')).
  assert (VFE : vf_s ⊆ ⦗E_s⦘ ⨾ vf_s).
  { rewrite (wf_vfE WF_S) at 1.
    rewrite inclusion_seq_eqv_r. reflexivity. }
  assert (SRFE : srf_s' ⊆ ⦗E_s⦘ ⨾ srf_s').
  { unfold srf_s'. rewrite <- seq_eqv_minus_ll.
    apply minus_rel_mori; [| red; auto with hahn].
    seq_rewrite seq_eqvC. rewrite VFE at 1.
    rewrite 2!seqA. reflexivity. }
  assert (SRFD : srf_s' ⊆ ⦗W_s⦘ ⨾ srf_s').
  { unfold srf_s'. rewrite <- seq_eqv_minus_ll.
    apply minus_rel_mori; [| red; auto with hahn].
    seq_rewrite seq_eqvC. rewrite vf_d_left at 1.
    rewrite 2!seqA. reflexivity. }
  assert (SRFL : srf_s' ⊆ ⦗Loc_s_ (WCore.lab_loc l_a)⦘ ⨾ srf_s').
  { unfold srf_s'. rewrite <- seq_eqv_minus_ll.
    apply minus_rel_mori; [| red; auto with hahn].
    seq_rewrite seq_eqvK. reflexivity. }
  assert (SRFVF : srf_s' ⊆ vf_s ⨾ sb_s').
  { unfold srf_s'. clear.
    rewrite inclusion_minus_rel, inclusion_seq_eqv_l.
    reflexivity. }
  assert (FUN : functional srf_s'⁻¹).
  { rewrite SRFE, SRFD, SRFL. clear - WF_S SRFVF.
    unfolder. intros x y z (((YINE & YW) & YL) & SRF1) (((ZINE & ZW) & ZL) & SRF2).
    destruct (classic (y = z)) as [EQ|NEQ]; ins.
    destruct (wf_co_total WF_S) with (a := y) (b := z)
                        (ol := WCore.lab_loc l_a) as [CO|CO].
    { unfold set_inter; splits; assumption. }
    { unfold set_inter; splits; assumption. }
    { exact NEQ. }
    { exfalso. apply SRF1. apply SRFVF in SRF2.
      clear - CO SRF2. red; eauto. }
    exfalso. apply SRF2. apply SRFVF in SRF1.
    clear - CO SRF1. red; eauto. }
  assert (SRF_W : exists w,
    eq_opt w ≡₁ dom_rel (srf_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘)).
  { clear - FUN.
    destruct classic
        with (dom_rel (srf_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘) ≡₁ ∅)
          as [EMP|NEMP].
    { exists None. rewrite EMP. clear. auto with hahn. }
    apply set_nonemptyE in NEMP. destruct NEMP as (x & DOM).
    exists (Some x). rewrite eq_opt_someE.
    split; red; [congruence|]. intros x' DOM'.
    apply FUN with b_t; red.
    { clear - DOM. unfolder in DOM. desf. }
    clear - DOM'. unfolder in DOM'. desf. }
  destruct SRF_W as (w & SRF_W).
  assert (ALAB : exists l_a',
    << U2V : same_label_u2v l_a' l_a >> /\
    << VAL : dom_rel (srf_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘) ⊆₁ Val_s_ (WCore.lab_val l_a') >>
  ); [| desf].
  { destruct w as [w|].
    { assert (ISR : WCore.lab_is_r l_a b_t).
      { unfolder in SRF_W. destruct SRF_W as [ISR _].
        clear - ISR. destruct ISR with w; desf. }
      assert (ISW : W_s w).
      { unfold srf_s', vf in SRF_W.
        unfolder in SRF_W. destruct SRF_W as [ISW _].
        destruct ISW with w; desf. }
      red in ISR.
      destruct l_a
           as [aex amo al av | axmo amo al av | amo]
           eqn:HEQA; ins.
      unfold is_w in ISW.
      destruct (lab_s w)
           as [wex wmo wl wv | wxmo wmo wl wv | wmo]
           eqn:HEQW; ins.
      exists (Aload aex amo al wv).
      split; red.
      { red. desf. }
      arewrite (dom_rel (srf_s' ⨾ ⦗eq b_t ∩₁ ⊤₁⦘) ⊆₁ Val_s_ (val_s w)).
      { rewrite <- SRF_W. clear. basic_solver. }
      unfold val. rewrite HEQW; ins. }
    exists l_a. split; red.
    { red. desf. }
    rewrite <- SRF_W. clear. basic_solver. }
  set (G_s'' := {|
    acts_set := E_s ∪₁ eq b_t;
    threads_set := threads_set G_s;
    lab := upd lab_s b_t l_a';
    rf := rf_s ∪
          srf_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘;
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
  assert (SRF' :
    srf_s' ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘ ≡
    srf (WCore.G X_s'') ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘
  ).
  { unfold X_s'' at 1. ins. unfold srf.
    seq_rewrite seq_eqv_minus_lr. rewrite !seqA.
    seq_rewrite <- id_inter.
    arewrite (is_r (lab G_s'') ∩₁ (eq b_t ∩₁ WCore.lab_is_r l_a) ≡₁
              eq b_t ∩₁ WCore.lab_is_r l_a).
    { split; [basic_solver |].
      unfold is_r, WCore.lab_is_r. unfolder.
      intros x XIN. destruct XIN; subst; ins.
      rewrite upds. splits; ins; desf. }
    rewrite id_inter.
    rewrite <- !seqA with (r2 := ⦗eq b_t⦘).
    apply seq_more; try easy.
    rewrite minus_inter_l, <- seq_eqv_inter_rr.
    arewrite (same_loc (lab G_s'') ⨾ ⦗eq b_t⦘ ≡
              (fun x y => loc (lab G_s'') x = WCore.lab_loc l_a) ⨾ ⦗eq b_t⦘).
    { rewrite LOCEQ. unfolder; split; ins.
      all: desf; unfold same_loc, loc, WCore.lab_loc in *.
      all: splits; ins.
      all: rewrite upds in *; ins. }
    rewrite seq_eqv_inter_rr.
    arewrite ((vf G_s'' ⨾ sb G_s'' \ co G_s'' ⨾ vf G_s'' ⨾ sb G_s'') ∩ (fun x _ : actid => loc (lab G_s'') x = WCore.lab_loc l_a) ≡
              ⦗fun x => loc (lab G_s'') x = (WCore.lab_loc l_a)⦘ ;; (vf G_s'' ⨾ sb G_s'' \ co G_s'' ⨾ vf G_s'' ⨾ sb G_s'')).
    { basic_solver 11. }
    unfold srf_s'.
    arewrite (sb_s' ≡ sb G_s'').
    rewrite !seq_eqv_minus_r, !seqA.
    arewrite (sb G_s'' ⨾ ⦗eq b_t⦘ ≡ ⦗E_s⦘ ⨾ sb G_s'' ⨾ ⦗eq b_t⦘).
    { unfold sb. ins. rewrite NEWSB.
      rewrite seq_union_l, seq_union_r. apply union_more.
      { unfold sb. clear - NOTIN. basic_solver. }
      unfold WCore.sb_delta.
      arewrite (E_s ≡₁ E_s ∪₁ is_init).
      { symmetry. apply set_union_absorb_r.
        eapply sico_init_acts_s; [| apply INV].
        eapply rsr_common; eauto. }
      clear. basic_solver 11. }
    arewrite (vf G_s'' ⨾ ⦗E_s⦘ ≡ vf_s ⨾ ⦗E_s⦘).
    { apply (porf_pref_vf X_s X_s''); ins.
      { clear. basic_solver. }
      { unfolder. ins; desf. rupd. congruence. }
      { unfold sb at 1. ins. rewrite NEWSB.
        clear - NOTIN. basic_solver 11. }
      { clear - NOTIN. basic_solver 11. }
      now rewrite (rsr_rmw SIMREL). }
    rewrite <- seq_eqv_minus_ll.
    apply minus_rel_more; rewrite <- !seqA.
    all: do 3 (apply seq_more; [| easy]).
    all: rewrite (wf_vfE WF_S), <- !seqA.
    all: do 2 (apply seq_more; [| easy]).
    { rewrite <- !id_inter. apply eqv_rel_more.
      unfold loc. unfolder. split; intros x (HSET & HIN).
      all: split; ins.
      all: rewrite updo in *; ins.
      all: congruence. }
    subst G_s''. ins. clear - NOTIN. basic_solver. }
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
    { rewrite SRF_W, SRF', wf_srfD.
      rewrite !seqA.
      seq_rewrite (seq_eqvC (is_r (lab G_s''))).
      seq_rewrite <- SRF'. rewrite seqA.
      unfold srf_s'.
      transitivity (dom_rel (⦗is_w (lab G_s'')⦘ ⨾ (
          ⦗Loc_s_ (WCore.lab_loc l_a)⦘ ⨾ vf_s ⨾ sb_s'
        ) ⨾ ⦗eq b_t ∩₁ WCore.lab_is_r l_a⦘
          ⨾ ⦗is_r (lab G_s'')⦘
      )); [basic_solver 11|].
      rewrite !seqA.
      seq_rewrite (seq_eqvC (is_w (lab G_s''))).
      rewrite seqA, (wf_vfE WF_S), !seqA.
      arewrite (⦗is_w (lab G_s'')⦘ ⨾ ⦗E_s⦘ ≡ ⦗W_s⦘ ⨾ ⦗E_s⦘).
      { rewrite <- !id_inter. apply eqv_rel_more.
        unfold G_s''; ins. unfolder. split; ins; desf.
        all: splits; ins.
        all: unfold is_w in *.
        all: rewrite updo in *; ins.
        all: congruence. }
      basic_solver 11. }
    { rewrite SRF_W.
      unfold srf_s'.
      rewrite (wf_vfE WF_S), !seqA.
      basic_solver 11. }
    { rewrite SRF_W.
      unfold srf_s'.
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
      { rewrite SRF'. apply functional_mori with (x := (srf G_s'')⁻¹).
        { unfold flip; basic_solver. }
        apply wf_srff'; ins. }
      intros x RF SRF.
      unfolder in RF. destruct RF as (y & RF).
      apply (wf_rfE WF_S) in RF.
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
    eapply WCore.add_event_wf with (X' := X_s''); eauto. }
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
    admit. (* Cons *) }
  { apply union_more; ins. }
  { now rewrite set_interC with (s := E_s). }
  subst X_s''. subst G_s''. ins.
  now rewrite (rsr_rmw SIMREL).
Admitted.

Lemma simrel_exec_b l l_a
    (NEQLOC : WCore.lab_loc l <> WCore.lab_loc l_a)
    (EQA : a_t = a_t')
    (EQB : b_t = b_t')
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (STEP : WCore.exec_inst X_t X_t' b_t l) :
  exists l_a' a_s X_s'' mapper' X_s',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP1 : WCore.exec_inst X_s  X_s'' a_s l_a' >> /\
    << STEP2 : WCore.exec_inst X_s'' X_s' (mapper' b_t) l >>.
Proof using.
  assert (CORR : reord_step_pred X_t a_t b_t); ins.
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
  { eapply WCore.add_event_wf; eauto.
    apply CORR. }
  assert (WF_S'' : Wf (WCore.G X_s'')).
  { apply (WCore.add_event_wf ADD').
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
  assert (SRF'': srf G_s' ⨾ ⦗acts_set (WCore.G X_s'')⦘ ≡
                srf (WCore.G X_s'') ⨾ ⦗acts_set (WCore.G X_s'')⦘).
  { apply (porf_pref_srf X_s'' X_s'); ins.
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
  admit. (* is_cons *)
Admitted.

End ExecB.