Require Import ReordSimrel.
Require Import ReordSimrel.
Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import SubToFullExec.
Require Import ReorderingFakeSrf.
Require Import Thrdle.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
Require Import Setoid Morphisms Program.Basics.
Require Import xmm_s_hb.

Module ReorderingReexecInternal.

Section ReorderingReexecInternal.

Variable X_t X_t' X_s X_s' : WCore.t.
Variable a_t b_t a_t' b_t' : actid.
Variable mapper : actid -> actid.
Variable f : actid -> actid.
Variable dtrmt cmt : actid -> Prop.

Notation "'R' G" := (fun e => is_true (is_r (lab G) e)) (at level 1).
Notation "'F' G" := (fun e => is_true (is_f (lab G) e)) (at level 1).
Notation "'W' G" := (fun e => is_true (is_w (lab G) e)) (at level 1).
Notation "'Acq' G" := (fun e => is_true (is_acq (lab G) e)) (at level 1).
Notation "'Rlx' G" := (fun e => is_true (is_rlx (lab G) e)) (at level 1).
Notation "'Rel' G" := (fun e => is_true (is_rel (lab G) e)) (at level 1).

Notation "'G_t'" := (WCore.G X_t).
Notation "'G_t''" := (WCore.G X_t').
Notation "'G_s'" := (WCore.G X_s).
Notation "'G_s''" := (WCore.G X_s').

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
Notation "'hb_t'" := (hb G_t).
Notation "'rhb_t'" := (rhb G_t).
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
Notation "'hb_t''" := (hb G_t').
Notation "'rhb_t''" := (rhb G_t').
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
Notation "'hb_s'" := (hb G_s).
Notation "'rhb_s'" := (rhb G_s).
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

Notation "'lab_s''" := (lab G_s').
Notation "'val_s''" := (val lab_s').
Notation "'loc_s''" := (loc lab_s').
Notation "'same_loc_s''" := (same_loc lab_s').
Notation "'same_val_s''" := (same_val lab_s').
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
Notation "'hb_s''" := (hb G_s').
Notation "'rhb_s''" := (rhb G_s').
Notation "'eco_s''" := (eco G_s').
Notation "'W_s''" := (fun x => is_true (is_w lab_s' x)).
Notation "'R_s''" := (fun x => is_true (is_r lab_s' x)).
Notation "'F_s''" := (F G_s').
Notation "'vf_s''" := (vf G_s').
Notation "'srf_s''" := (srf G_s').
Notation "'Loc_s_'' l" := (fun e => loc_s' e = l) (at level 1).
Notation "'Val_s_'' l" := (fun e => val_s' e = l) (at level 1).
Notation "'Rlx_s''" := (Rlx G_s').
Notation "'Acq_s''" := (Acq G_s').
Notation "'Rel_s''" := (Rel G_s').

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

(* Id aliases for better readability *)
Definition a_s := b_t.
Definition b_s := a_t.
Definition a_s' := b_t'.
Definition b_s' := a_t'.
Definition A_s' := extra_a X_t' a_t' b_t' a_s'.

Definition mapper' := upd (upd id a_t' a_s') b_t' b_s'.
Definition mapper_inv' := upd (upd id a_s' a_t') b_s' b_t'.

Definition G_s'' : execution := {|
  acts_set := mapper' ↑₁ E_t';
  threads_set := threads_set G_t';
  lab := lab_t' ∘ mapper';
  rf := mapper' ↑ rf_t';
  co := mapper' ↑ co_t';
  rmw := mapper' ↑ rmw_t';
  rmw_dep := rmw_dep_s;
  ctrl := ctrl_s;
  data := data_s;
  addr := addr_s;
|}.

Record reexec_conds : Prop := {
  rc_a_dtrmt : dtrmt a_t <-> dtrmt a_t';
  rc_b_dtrmt : dtrmt b_t <-> dtrmt b_t';
  rc_a_eq : dtrmt a_t -> a_t = a_t';
  rc_b_eq : dtrmt b_t -> b_t = b_t';
  rc_pres : b_t = b_t' -> a_t = a_t';
  rc_simrel : reord_simrel X_s X_t a_t b_t mapper;
  rc_step : WCore.reexec X_t X_t' f dtrmt cmt;
  rc_inv_start : reord_step_pred X_t a_t b_t;
  rc_inv_end : reord_step_pred X_t' a_t' b_t';
  rc_l_a_nacq : Rlx_s' a_s';
  rc_end_cons : WCore.is_cons G_t' ∅₂;
  rc_new_cons : WCore.is_cons G_s' ∅₂;
  rc_vf : forall (IMB : E_t' b_t') (NINA : ~ E_t' a_t'),
            vf_s' ⨾ sb_s' ⨾ ⦗eq a_s'⦘ ≡ vf G_s'' ⨾ sb_s' ⨾ ⦗eq a_s'⦘;
  (**)
  rc_extra_lab : fake_srf G_s'' a_s' (lab_s' a_s') ⨾ ⦗A_s' ∩₁ WCore.lab_is_r (lab_s' a_s')⦘ ⊆ same_val_s';
  rc_lab : eq_dom E_t' (lab_s' ∘ mapper') lab_t';
  rc_acts : E_s' ≡₁ mapper' ↑₁ E_t' ∪₁ extra_a X_t' a_t' b_t' a_s';
  rc_rf : rf_s' ≡ mapper' ↑ rf_t' ∪ fake_srf G_s'' a_s' (lab_s' a_s') ⨾ ⦗A_s' ∩₁ WCore.lab_is_r (lab_s' a_s')⦘;
  rc_co : co_s' ≡ mapper' ↑ co_t' ∪
          add_max
            (extra_co_D (mapper' ↑₁ E_t') lab_s' (WCore.lab_loc (lab_s' a_s')))
            (A_s' ∩₁ WCore.lab_is_w (lab_s' a_s'));
  rc_rmw : rmw_s' ≡ mapper' ↑ rmw_t';
  rc_threads : threads_set G_s' ≡₁ threads_set G_t';
  rc_ctrl : ctrl_s' ≡ ctrl_t';
  rc_data : data_s' ≡ data_t';
  rc_addr : addr_s' ≡ addr_t';
  rc_rmw_dep : rmw_dep_s' ≡ rmw_dep_t';
}.

Lemma mapinj' : inj_dom ⊤₁ mapper'.
Proof using.
  admit.
Admitted.

Lemma mapinj : inj_dom E_t' mapper'.
Proof using.
  admit.
Admitted.

Lemma mapinj_inv' : inj_dom ⊤₁ mapper_inv'.
Proof using.
  admit.
Admitted.

Lemma mapinj_inv : inj_dom E_t' mapper_inv'.
Proof using.
  admit.
Admitted.

Lemma mapper_inv_l_inv
    (NEQ : a_t' <> b_t') :
  mapper' ∘ mapper_inv' = id.
Proof using.
  admit.
Admitted.

Lemma mapper_inv_r_inv
    (NEQ : a_t' <> b_t') :
  mapper_inv' ∘ mapper' = id.
Proof using.
  admit.
Admitted.

Lemma intermediate_graph_wf
    (INB : E_t' b_t')
    (NINA : ~ E_t' a_t')
    (CTX : reexec_conds) :
  Wf G_s''.
Proof using.
  admit. (* This graph is very conveniently mapped by m *)
Admitted.

Lemma reexec_simrel
    (CTX : reexec_conds) :
  reord_simrel X_s' X_t' a_t' b_t' mapper'.
Proof using.
  assert (EXAR : eq b_t' ∩₁ R_s' ≡₁ eq b_t' ∩₁ WCore.lab_is_r (lab_s' a_s')).
  { unfold a_s', is_r, WCore.lab_is_r.
    unfolder; split; ins; desf. }
  assert (MAPINV : forall x (MEQ : mapper' x = b_t'),
    x = a_t'
  ).
  { intros x XEQ.
    replace b_t' with (mapper' a_t') in XEQ.
    { eapply mapinj'; easy. }
    clear - CTX. unfold mapper'.
    rupd; [easy | apply CTX]. }
  assert (SRF :
    fake_srf G_s'' a_s' (lab_s' a_s') ⨾ ⦗A_s' ∩₁ WCore.lab_is_r (lab_s' a_s')⦘ ≡
    srf_s' ⨾ ⦗extra_a X_t' a_t' b_t' b_t' ∩₁ R_s'⦘
  ).
  { unfold A_s', extra_a; desf; [desf | basic_solver 11].
    rewrite EXAR, <- fake_srf_is_srf with (G_s := G_s'').
    all: ins.
    { apply intermediate_graph_wf; auto. }
    { unfold fake_sb, G_s'', sb. ins.
      rewrite (rc_acts CTX), extra_a_some; auto. }
    { unfold G_s''. ins.
      intro FALSO. unfolder in FALSO.
      destruct FALSO as (x & XIN & XEQ).
      rewrite MAPINV in XIN; auto. }
    { unfold G_s''. ins.
      admit. (* TODO: weaken cond*) }
    { apply CTX; auto. }
    rewrite (rc_co CTX), seq_union_l.
    unfold A_s'. rewrite extra_a_some; auto.
    rewrite add_max_seq_r, set_interC, set_interA.
    arewrite (eq a_s' ∩₁ mapper' ↑₁ E_t' ≡₁ ∅).
    { split; [| basic_solver]. unfold a_s'.
      unfolder. intros x (XEQ & y & YIN & YEQ).
      subst x. rewrite MAPINV in YIN; auto. }
    rewrite set_inter_empty_r, add_max_empty_r.
    now rewrite union_false_r. }
  constructor; ins.
  all: try now apply CTX.
  { apply mapinj. }
  { unfolder. unfold extra_a; ins; desf.
    constructor; [red; auto | desf].
    rewrite extra_a_some in SRF; auto.
    rewrite <- SRF. apply CTX. }
  { rewrite (rc_acts CTX), set_minus_union_l.
    unfold a_s'. rewrite set_minusK, set_union_empty_r.
    unfold extra_a; desf; [| clear; basic_solver].
    rewrite set_minus_disjoint; auto with hahn.
    unfolder. intros x (y & YIN & YEQ) XEQ.
    subst x. rewrite MAPINV in YIN; auto. desf. }
  { clear - CTX. unfold mapper'. unfolder.
    ins. rewrite !updo; [done | |].
    all: intro FALSO; desf.
    { now apply (rsr_at_ninit (rc_inv_end CTX)). }
    now apply (rsr_bt_ninit (rc_inv_end CTX)). }
  { clear - CTX. unfold mapper', compose.
    unfolder. ins.
    destruct classic with (x = b_t') as [EQ | XNB].
    { subst. rupd. now rewrite <- (rsr_at_bt_tid (rc_inv_end CTX)). }
    destruct classic with (x = a_t') as [EQ | XNA].
    { subst. rupd. now rewrite (rsr_at_bt_tid (rc_inv_end CTX)). }
    rupd. }
  { admit. }
  { rewrite <- SRF, (rc_rf CTX). auto. }
  { rewrite (rc_co CTX), (rc_acts CTX).
    apply union_more; auto.
    change (extra_a X_t' a_t' b_t' b_t')
      with A_s'.
    change (extra_a X_t' a_t' b_t' a_s')
      with A_s'.
    arewrite (WCore.lab_loc (lab_s' a_s') = loc_s' b_t').
    arewrite (A_s' ∩₁ W_s' ≡₁
              A_s' ∩₁ WCore.lab_is_w (lab_s' a_s')).
    { unfold A_s', extra_a. desf; [| basic_solver].
      clear. unfold is_w, WCore.lab_is_w.
      unfolder. split; ins; desf. }
    destruct classic
        with (WCore.lab_is_w (lab_s' a_s') ≡₁ ∅)
          as [EMP | NEMP].
    { rewrite EMP, set_inter_empty_r.
      now rewrite !add_max_empty_r. }
    arewrite (WCore.lab_is_w (lab_s' a_s') ≡₁ ⊤₁).
    { unfold WCore.lab_is_w in *. desf. }
    rewrite set_inter_full_r,
            add_max_a with (A := extra_co_D (mapper' ↑₁ E_t') lab_s' (loc_s' b_t')),
            add_max_a with (A := extra_co_D (mapper' ↑₁ E_t' ∪₁ A_s') lab_s' (loc_s' b_t')).
    rewrite !extra_co_D_minus, set_minus_union_l.
    now rewrite set_minusK, set_union_empty_r. }
  { admit. (* rpo *) }
  { clear. unfold mapper'. unfolder.
    ins. desf. now rewrite !updo by auto. }
  { clear. unfold mapper'. unfolder.
    ins. desf. now rewrite upds. }
  clear - CTX. unfold mapper'. unfolder.
  ins. desf. rewrite updo, upds; [done |].
  apply CTX.
Admitted.

Definition extra_b :=
  ifP ~E_t' a_t' /\ E_t' b_t' then eq b_t' ∩₁ dtrmt
  else ∅.
Definition cmt' := mapper' ↑₁ cmt.
Definition dtrmt' := mapper' ↑₁ (dtrmt \₁ extra_b).
Definition f' := (mapper ∘ f) ∘ mapper_inv'.

Lemma reexec_step
    (CTX : reexec_conds) :
  WCore.reexec X_s X_s' f' dtrmt' cmt'.
Proof using.
  assert (MAPINV : forall x (MEQ : mapper' x = b_t'),
    x = a_t'
  ).
  { intros x XEQ.
    replace b_t' with (mapper' a_t') in XEQ.
    { eapply mapinj'; easy. }
    clear - CTX. unfold mapper'.
    rupd; [easy | apply CTX]. }
  assert (NEQ : a_t' <> b_t').
  { apply CTX. }
  assert (GREEXEC :
    WCore.reexec X_t X_t' f dtrmt cmt
  ).
  { apply (rc_step CTX). }
  red in GREEXEC. destruct GREEXEC as (thrdle & GREEXEC).
  assert (MEQA : mapper' a_t' = b_t').
  { unfold mapper'.
    rewrite updo, upds; [done |].
    apply CTX. }
  assert (RHBTDLE :
    ⦗E_t' \₁ dtrmt⦘ ⨾ rf_t' ⨾ rhb_t'^? ⊆
      sb_t' ∪ tid ↓ thrdle
  ).
  { apply thrdle_with_rhb; apply GREEXEC. }
  assert (MAPTHRDLE : mapper' ↑ (restr_rel E_t' (tid ↓ thrdle)) ⊆ tid ↓ thrdle).
  { clear - CTX. unfolder. ins. desf.
    rewrite <- !(rsr_tid' _ (reexec_simrel CTX)).
    all: auto. }
  assert (INJHELPER : inj_dom (codom_rel (⦗E_t' \₁ dtrmt⦘ ⨾ rf_t') ∪₁ dom_rel rhb_t'^?) mapper').
  { eapply inj_dom_mori; [| auto | apply mapinj'].
    unfold flip. clear. basic_solver. }
  assert (EXNCMT : extra_a X_t' a_t' b_t' b_t' ∩₁ cmt' ≡₁ ∅).
  { split; vauto.
    unfold cmt'.
    rewrite (WCore.reexec_embd_dom GREEXEC).
    clear - MAPINV.
    unfold extra_a. desf; [| basic_solver].
    unfolder. ins. desf.
    erewrite <- MAPINV in a; eauto. }
  assert (MAPRFRHB :
    mapper' ↑ (⦗E_t' \₁ dtrmt⦘ ⨾ rf_t') ⨾ mapper' ↑ rhb_t'^? ⊆
      sb_s' ∪ tid ↓ thrdle
  ).
  { rewrite <- collect_rel_seq, !seqA; auto.
    rewrite (rsr_no_rfrhb_ba (rc_inv_end CTX) (rc_end_cons CTX)).
    rewrite <- seq_eqv_minus_ll.
    arewrite (
      ⦗E_t' \₁ dtrmt⦘ ⨾ rf_t' ⨾ rhb_t'^? ⊆
      restr_rel E_t' (⦗E_t' \₁ dtrmt⦘ ⨾ rf_t' ⨾ rhb_t'^?)
    ).
    { rewrite (wf_rfE (rsr_Gt_wf (rc_inv_end CTX))) at 1.
      rewrite (wf_rhbE (rsr_Gt_wf (rc_inv_end CTX))) at 1.
      clear. basic_solver 11. }
    rewrite rhb_in_hb, (WCore.surg_ndtrmt (WCore.reexec_sur GREEXEC)).
    rewrite restr_union.
    rewrite minus_union_l, collect_rel_union.
    arewrite (restr_rel E_t' sb_t' ⊆ sb_t').
    rewrite (rsr_sbt_in (rc_inv_end CTX) (reexec_simrel CTX)).
    apply union_mori; auto with hahn.
    transitivity (mapper' ↑ (restr_rel E_t' (tid ↓ thrdle))).
    { clear. apply collect_rel_mori; auto.
      basic_solver. }
    apply MAPTHRDLE. }
  assert (SURG :
    WCore.stable_uncmt_reads_gen X_s' dtrmt' thrdle
  ).
  { admit. }
  assert (WF_START :
    WCore.wf (WCore.X_start X_s dtrmt') X_s' cmt'
  ).
  { admit. (* TODO *) }
  (**)
  red. exists thrdle.
  constructor.
  { unfold dtrmt', f', cmt'.
    arewrite (mapper' ↑₁ (dtrmt \₁ extra_b) ≡₁
              mapper  ↑₁ (dtrmt \₁ extra_b)).
    { admit. }
    rewrite (WCore.dtrmt_cmt GREEXEC).
    rewrite set_collect_compose.
    transitivity ((mapper ∘ f) ↑₁ (mapper_inv' ↑₁ (mapper' ↑₁ cmt)));
      [|basic_solver 11].
    rewrite <- set_collect_compose with (g := mapper_inv').
    rewrite mapper_inv_r_inv, set_collect_id; [| apply CTX].
    rewrite set_collect_compose.
    basic_solver 11. }
  { unfold cmt'.
    rewrite (rc_acts CTX), (WCore.reexec_embd_dom GREEXEC).
    basic_solver. }
  { exact SURG. }
  { admit. (* sb-clos *) }
  { admit. (* rpo edges *) }
  { constructor.
    { intros x' y'; unfold cmt', f'.
      intros [x [Hx]] [y [Hy]]; subst x' y'.
      unfold compose.
      change (mapper_inv' (mapper' x)) with ((mapper_inv' ∘ mapper') x).
      change (mapper_inv' (mapper' y)) with ((mapper_inv' ∘ mapper') y).
      rewrite !mapper_inv_r_inv; auto; unfold id; intro EQf.
      enough (EQxy: x = y); [by rewrite EQxy|].
      apply (WCore.reexec_embd_inj (WCore.reexec_embd_corr GREEXEC)); auto.
      apply (rsr_inj (rc_simrel CTX)).
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver. }
      { apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)); basic_solver. }
      done. }
    { admit. (* TID *) }
    { admit. (* lab *) }
    { admit. }
    { rewrite (rsr_rf (reexec_simrel CTX)),
              restr_union, collect_rel_union.
      arewrite_false (restr_rel cmt'
        (srf_s' ⨾ ⦗extra_a X_t' a_t' b_t' b_t' ∩₁ R_s'⦘)).
      { rewrite restr_relE, !seqA, <- id_inter.
        rewrite set_interA,
                set_interC with (s' := cmt'),
                <- set_interA.
        rewrite EXNCMT. basic_solver. }
      rewrite collect_rel_empty, union_false_r.
      unfold cmt', f'.
      rewrite collect_rel_restr;
        [| eapply inj_dom_mori; eauto using mapinj';
           unfold flip; basic_solver].
      rewrite <- !collect_rel_compose.
      rewrite Combinators.compose_assoc.
      rewrite mapper_inv_r_inv; auto.
      rewrite Combinators.compose_assoc.
      arewrite (f ∘ id = f) by done.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_rf (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_rf (rc_simrel CTX)); auto with hahn. }
    { rewrite (rsr_co (reexec_simrel CTX)),
              restr_union, collect_rel_union.
      arewrite_false (restr_rel cmt'
        (add_max (extra_co_D E_s' lab_s' (loc_s' b_t'))
          (extra_a X_t' a_t' b_t' b_t' ∩₁ W_s'))).
      { rewrite restr_add_max.
        rewrite set_interA,
                set_interC with (s := W_s') (s' := cmt'),
                <- set_interA.
        rewrite EXNCMT. basic_solver. }
      rewrite collect_rel_empty, union_false_r.
      unfold cmt', f'.
      rewrite collect_rel_restr;
        [| eapply inj_dom_mori; eauto using mapinj';
           unfold flip; basic_solver].
      rewrite <- !collect_rel_compose.
      rewrite Combinators.compose_assoc.
      rewrite mapper_inv_r_inv; auto.
      rewrite Combinators.compose_assoc.
      arewrite (f ∘ id = f) by done.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_co (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_co (rc_simrel CTX)); auto with hahn. }
    { rewrite (rsr_rmw (reexec_simrel CTX)).
      unfold cmt', f'.
      rewrite collect_rel_restr;
        [| eapply inj_dom_mori; eauto using mapinj';
           unfold flip; basic_solver].
      rewrite <- !collect_rel_compose.
      rewrite Combinators.compose_assoc.
      rewrite mapper_inv_r_inv; auto.
      rewrite Combinators.compose_assoc.
      arewrite (f ∘ id = f) by done.
      rewrite collect_rel_compose.
      rewrite (WCore.reexec_embd_rmw (WCore.reexec_embd_corr GREEXEC)).
      rewrite (rsr_rmw (rc_simrel CTX)); auto with hahn. }
    unfold cmt', f'.
    rewrite <- !set_collect_compose.
    rewrite Combinators.compose_assoc.
    rewrite mapper_inv_r_inv; auto.
    rewrite Combinators.compose_assoc.
    arewrite (f ∘ id = f) by done.
    rewrite set_collect_compose.
    rewrite (WCore.reexec_embd_acts (WCore.reexec_embd_corr GREEXEC)).
    rewrite (rsr_acts (rc_simrel CTX)); auto with hahn. }
  { exact WF_START. (* wf start *) }
  { admit. (* Consistency *) }
  apply sub_to_full_exec_listless
   with (thrdle := thrdle).
  { exact WF_START. }
  { eapply G_s_rfc with (X_t := X_t').
    { apply CTX. }
    now apply reexec_simrel. }
  { admit. (* difference between acts and dtrmt is fin *) }
  { admit. (* Prefix. Trivial? *) }
  { eapply G_s_wf with (X_t := X_t').
    { apply CTX. }
    now apply reexec_simrel. }
  { admit. (* init acts *) }
  { admit. (* Unprovable SC *) }
  { now rewrite (rc_data CTX), (rsr_ndata (rc_inv_end CTX)). }
  { now rewrite (rc_addr CTX), (rsr_naddr (rc_inv_end CTX)). }
  { now rewrite (rc_ctrl CTX), (rsr_nctrl (rc_inv_end CTX)). }
  { now rewrite (rc_rmw_dep CTX), (rsr_nrmw_dep (rc_inv_end CTX)). }
  ins.
  admit. (* dtrmt' is subset of E_s' *)
Admitted.

End ReorderingReexecInternal.

End ReorderingReexecInternal.

Section ReorderingReexec.

Variable X_t X_t' X_s : WCore.t.
Variable a_t b_t a_t' b_t' : actid.
Variable mapper : actid -> actid.
Variable f : actid -> actid.
Variable dtrmt cmt : actid -> Prop.
Variable l_a' : label. (* The 'desired' label for phantom a_s *)

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

(* Conditions for the re-execution lemma *)
Record reexec_conds : Prop := {
  rc_a_dtrmt : dtrmt a_t <-> dtrmt a_t';
  rc_b_dtrmt : dtrmt b_t <-> dtrmt b_t';
  rc_a_eq : dtrmt a_t -> a_t = a_t';
  rc_b_eq : dtrmt b_t -> b_t = b_t';
  rc_pres : b_t = b_t' -> a_t = a_t';
  rc_simrel : reord_simrel X_s X_t a_t b_t mapper;
  rc_step : WCore.reexec X_t X_t' f dtrmt cmt;
  rc_inv_start : reord_step_pred X_t a_t b_t;
  rc_inv_end : reord_step_pred X_t' a_t' b_t';
  rc_l_a_nacq : mode_le (WCore.lab_mode l_a') Orlx;
}.

Hypothesis CTX : reexec_conds.

(* Id aliases for better readability *)
Definition a_s := b_t.
Definition b_s := a_t.
Definition a_s' := b_t'.
Definition b_s' := a_t'.

Definition mapper' := upd (upd id a_t' a_s') b_t' b_s'.

Lemma mapeq : eq_dom dtrmt mapper mapper'.
Proof using CTX.
  admit.
Admitted.

(* Intermediate graph for locating the srf edge for for a_s *)

Definition A_s' := extra_a X_t' a_t' b_t' a_s'.
Definition E_s' := mapper' ↑₁ E_t' ∪₁ A_s'.

Lemma simrel_reexec :
  exists mapper' X_s' f' dtrmt' cmt',
    << SIMREL : reord_simrel X_s' X_t' a_t' b_t' mapper' >> /\
    << STEP : WCore.reexec X_s X_s' f' dtrmt' cmt' >>.
Proof using CTX.
Admitted.

End ReorderingReexec.

(* DRAFTS FOR FINAL THEOREM *)

(* Lemma simrel_term
    (CONS : WCore.is_cons G_t (WCore.sc X_t))
    (SIM : reord_simrel G_t G_s a_t b_t mapper)
    (TERM : machine_terminated G_t traces) :
  << TERM' : machine_terminated G_s traces' >> /\
  << SIM' : ReordCommon.reord G_s G_t traces traces' a b >>.
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

*)

(* Lemma sim_rel_step : about any step *)

(*
 forall traces P_src, P_trgt. If target is a reordereing of src, then
 <..> (clarify cuz the theorem statement looks weird)
*)
(* Theorem reordering_rw : TODO.
Proof using.
  admit.
Admitted. *)