Require Import AuxDef AuxRel2 Core Lia.
Require Import ReordSimrel ReorderingMapper.
Require Import ReorderingExecA ReorderingExecB.
Require Import ReordExecNaNb ReorderingReexec.
Require Import ThreadTrace TraceSwap.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
Require Import Setoid Morphisms Program.Basics.

Section Behavior.

Variable G : execution.

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'W'" := (fun e => is_true (is_w lab e)).
Notation "'Loc_' l" := (fun e => loc e = l) (at level 1).

Definition event_mem (a : actid) (t : trace label) : Prop :=
  match t, a with
  | _, InitEvent _ => False
  | trace_inf _, _ => True
  | trace_fin l, ThreadEvent _ n => n < length l
  end.

Lemma event_memE e
    (NINIT : tid e <> tid_init)
    (CONT : contigious_actids G) :
  event_mem e (thread_trace G (tid e)) <->
    E e.
Proof using.
  destruct e as [el | et en]; ins.
  red in CONT. destruct (CONT _ NINIT) as [N EQ].
  split; intros HSET.
  { enough (IN' :
      (acts_set G ∩₁ (fun e => et = tid e))
        (ThreadEvent et en)
    ).
    { apply IN'. }
    apply EQ, thread_set_iff.
    unfold thread_trace, thread_actid_trace in HSET.
    ins. rewrite EQ, thread_seq_set_size in HSET.
    ins. now autorewrite with calc_length in HSET. }
  unfold thread_trace, thread_actid_trace.
  ins. rewrite EQ, thread_seq_set_size.
  ins. autorewrite with calc_length.
  eapply thread_set_iff, EQ. basic_solver.
Qed.

Definition behavior := location -> value.

Definition last_val_spec (l : location) (v : value) : Prop :=
  exists (e : actid),
    << INE : E e >> /\
    << WIN : W e >> /\
    << ELOC : loc e = Some l >> /\
    << VAL : val e = Some v >> /\
    << MAX : max_elt co e >>.

Definition behavior_spec (b : behavior) : Prop :=
  forall (l : location), last_val_spec l (b l).

Lemma last_val_exists l
    (WF : Wf G)
    (INIT : is_init ⊆₁ E)
    (FIN : set_finite (acts_set G \₁ is_init)) :
  exists v, last_val_spec l v.
Proof using.
  assert (COEQ : co＊ ≡ co^?).
  { rewrite <- cr_of_ct, ct_of_trans; auto.
    apply WF. }
  assert (ILOC : loc (InitEvent l) = Some l).
  { unfold loc. now rewrite (wf_init_lab WF). }
  assert (IVAL : val (InitEvent l) = Some 0).
  { unfold val. now rewrite (wf_init_lab WF). }
  assert (IISW : W (InitEvent l)).
  { unfold is_w. now rewrite (wf_init_lab WF). }
  assert (FINDOM : exists dom,
    (fun x => In x dom) ≡₁ E ∩₁ W ∩₁ Loc_ (Some l)
  ).
  { apply set_finiteE in FIN.
    destruct FIN as (dom & NODUP & EQ).
    exists ([InitEvent l] ++ filterP (W ∩₁ Loc_ (Some l)) dom).
    rewrite set_union_minus with (s' := is_init) (s := E); auto.
    rewrite set_unionC, !set_inter_union_l.
    arewrite (is_init ∩₁ W ∩₁ Loc_ (Some l) ≡₁ eq (InitEvent l)).
    { split; [| basic_solver ]. unfold is_init. unfolder; ins; desf.
      unfold loc in *. rewrite (wf_init_lab WF _) in *. desf. }
    arewrite (
      (fun x => In x ([InitEvent l] ++ filterP (W ∩₁ Loc_ (Some l)) dom)) ≡₁
        eq (InitEvent l) ∪₁
        (fun x => In x (filterP (W ∩₁ Loc_ (Some l)) dom))
    ).
    apply set_union_more; [reflexivity |].
    arewrite (
      (fun x => In x (filterP (W ∩₁ Loc_ (Some l)) dom)) ≡₁
        (fun x => In x dom) ∩₁ W ∩₁ Loc_ (Some l)
    ); [| now rewrite EQ].
    split; intros x XIN;
      [apply in_filterP_iff in XIN | apply in_filterP_iff].
    all: unfolder; unfolder in XIN; desf. }
  destruct FINDOM as [dom FINDOM].
  destruct last_exists
      with (dom := dom) (s := co) (a := InitEvent l)
        as (a0 & CO & MAX).
  { apply trans_irr_acyclic; apply WF. }
  { intros c CO. apply COEQ, crE in CO.
    apply FINDOM. destruct CO as [EQ | CO].
    { unfolder in EQ. desf.
      unfolder. unfold is_w, loc.
      rewrite (wf_init_lab WF l). splits; auto. }
    apply (wf_coD WF) in CO.
    unfolder in CO. destruct CO as (_ & CO & ISW).
    apply (wf_coE WF) in CO.
    unfolder in CO. destruct CO as (_ & CO & CIN).
    apply (wf_col WF) in CO.
    unfolder. splits; auto.
    unfold same_loc, loc in CO.
    rewrite (wf_init_lab WF l) in CO. desf. }
  apply COEQ, crE in CO.
  assert (ALOC : loc a0 = Some l).
  { unfolder in CO. destruct CO as [[EQ _] | CO]; [desf |].
    apply (wf_col WF) in CO. unfold same_loc, loc in *.
    rewrite (wf_init_lab WF l) in CO. desf. }
  assert (AVAL : exists v, val a0 = Some v).
  { unfolder in CO. destruct CO as [[EQ _] | CO]; [desf; eauto |].
    apply (wf_coD WF) in CO. unfolder in CO.
    unfold is_w, val in *. desf; eauto. }
  destruct AVAL as (v & VEQ).
  exists v. red. exists a0.
  unfold NW. splits; auto.
  { unfolder in CO. destruct CO as [EQ | CO].
    { desf. now apply INIT. }
    apply (wf_coE WF) in CO. unfolder in CO. desf. }
  unfolder in CO. destruct CO as [EQ | CO].
  { desf. }
  apply (wf_coD WF) in CO. unfolder in CO. desf.
Qed.

Lemma last_val_unique l v1 v2
    (WF : Wf G)
    (INIT : is_init ⊆₁ E)
    (FIN : set_finite (acts_set G \₁ is_init))
    (SP1 : last_val_spec l v1)
    (SP2 : last_val_spec l v2) :
  v1 = v2.
Proof using.
  red in SP1, SP2.
  destruct SP1 as (e1 & SP1), SP2 as (e2 & SP2).
  enough (e1 = e2) by desf.
  destruct classic with (e1 = e2) as [EQ | NEQ]; auto.
  exfalso.
  destruct (
    wf_co_total WF
  ) with (ol := Some l) (a := e1) (b := e2)
    as [COL | COR]; auto.
  { unfolder. splits; apply SP1. }
  { unfolder. splits; apply SP2. }
  { eapply SP1; eauto. }
  eapply SP2; eauto.
Qed.

Lemma behavior_exists
    (WF : Wf G)
    (INIT : is_init ⊆₁ E)
    (FIN : set_finite (acts_set G \₁ is_init)) :
  exists (b : behavior), behavior_spec b.
Proof using.
  destruct unique_choice
      with (R := last_val_spec)
        as [b SPEC].
  { intro l.
    destruct last_val_exists
        with (l := l)
          as [v SPEC]; auto.
    exists v. red. split; auto.
    intros v' SPEC'. eapply last_val_unique; eauto. }
  exists b. red. auto.
Qed.

End Behavior.

Section SameBehavior.

Variable G G' : execution.

Notation "'lab''" := (lab G').
Notation "'loc''" := (loc lab').
Notation "'val''" := (val lab').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'W''" := (fun e => is_true (is_w lab' e)).
Notation "'Loc_'' l" := (fun e => loc' e = l) (at level 1).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'W'" := (fun e => is_true (is_w lab e)).
Notation "'Loc_' l" := (fun e => loc e = l) (at level 1).

Lemma same_last_val m l v
    (WF : Wf G)
    (WF' : Wf G')
    (INIT : is_init ⊆₁ E)
    (FIN : set_finite (acts_set G \₁ is_init))
    (MAP : m ↑₁ E ≡₁ E')
    (EQ : eq_dom E (lab' ∘ m) lab)
    (INJ : inj_dom E m)
    (MAPCO : co' ⊆ m ↑ co)
    (LAST : last_val_spec G l v) :
  last_val_spec G' l v.
Proof using.
  unfold last_val_spec in *.
  desf. exists (m e). unfold NW; splits.
  { apply MAP. basic_solver. }
  { unfold is_w in *.
    rewrite <- EQ in WIN; auto. }
  { unfold loc in *.
    rewrite <- EQ in ELOC; auto. }
  { unfold val in *.
    rewrite <- EQ in VAL; auto. }
  unfolder. intros b' CO.
  assert (BEQ : exists b,
      << BEQ : b' = m b >> /\
      << BIN : E b >>
  ); [| desf].
  { apply (wf_coE WF') in CO.
    unfolder in CO. destruct CO as (_ & _ & IN).
    apply MAP in IN. unfolder in IN. desf; eauto. }
  apply MAPCO in CO. unfolder in CO.
  destruct CO as (e' & b' & CO & EQ1 & EQ2).
  apply INJ in EQ1, EQ2; desf.
  { eapply MAX; eauto. }
  all: apply (wf_coE WF) in CO.
  all: unfolder in CO; desf.
Qed.

Lemma same_behavior b m
    (WF : Wf G)
    (WF' : Wf G')
    (INIT : is_init ⊆₁ E)
    (FIN : set_finite (acts_set G \₁ is_init))
    (MAP : m ↑₁ E ≡₁ E')
    (EQ : eq_dom E (lab' ∘ m) lab)
    (INJ : inj_dom E m)
    (MAPCO : co' ⊆ m ↑ co)
    (BEH1 : behavior_spec G b) :
  behavior_spec G' b.
Proof using.
  unfold behavior_spec in *.
  intro l. eapply same_last_val; eauto.
Qed.

End SameBehavior.

Section ReorderingSteps.

Variable X_t X_t' X_s : WCore.t.
Variable rtid : thread_id.
Variable i_b : nat.
Variable traces_t traces_s : trace_storage.

Definition i_a := i_b + 1.

Notation "'G_t'" := (WCore.G X_t).
Notation "'lab_t'" := (lab G_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'val_t'" := (val lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).
Notation "'W_t'" := (fun e => is_true (is_w lab_t e)).
Notation "'R_t'" := (fun e => is_true (is_r lab_t e)).
Notation "'F_t'" := (fun e => is_true (is_f lab_t e)).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).
Notation "'Val_t_' l" := (fun e => val_t e = l) (at level 1).
Notation "'same_loc_t'" := (same_loc lab_t).
Notation "'same_val_t'" := (same_val lab_t).
Notation "'Acq_t'" := (fun e => is_true (is_acq lab_t e)).
Notation "'Rel_t'" := (fun e => is_true (is_rel lab_t e)).
Notation "'Rlx_t'" := (fun e => is_true (is_rlx lab_t e)).
Notation "'Sc_t'" := (fun e => is_true (is_sc lab_t e)).

Notation "'G_s'" := (WCore.G X_s).
Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (fun e => is_true (is_w lab_s e)).
Notation "'R_s'" := (fun e => is_true (is_r lab_s e)).
Notation "'F_s'" := (fun e => is_true (is_f lab_s e)).
Notation "'Loc_s_' l" := (fun e => loc_s e = l) (at level 1).
Notation "'Val_s_' l" := (fun e => val_s e = l) (at level 1).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'same_val_s'" := (same_val lab_s).
Notation "'Acq_s'" := (fun e => is_true (is_acq lab_s e)).
Notation "'Rel_s'" := (fun e => is_true (is_rel lab_s e)).
Notation "'Rlx_s'" := (fun e => is_true (is_rlx lab_s e)).
Notation "'Sc_s'" := (fun e => is_true (is_sc lab_s e)).

Notation "'b_t'" := (ThreadEvent rtid i_b).
Notation "'a_t'" := (ThreadEvent rtid i_a).
Notation "'mapper'" := (mapper a_t b_t).

Definition prefix_closed
    (t : thread_id) :
  Prop :=
    forall tr tr' (IN : traces_t t tr) (PREF : trace_prefix tr' tr),
      traces_t t tr'.

Definition full_coverage : Prop :=
  forall tr (TRIN : traces_t (tid b_t) tr) (IN : event_mem b_t tr),
    exists tr',
      << PREF : trace_prefix tr tr' >> /\
      << AIN : event_mem a_t tr' >>.

Definition correct_loc : Prop :=
  forall (tr : trace label) (TRIN : traces_t (tid b_t) tr)
    (BIN : event_mem b_t tr) (AIN : event_mem a_t tr),
      WCore.lab_loc (trace_nth (index b_t) tr (Afence Opln)) <>
      WCore.lab_loc (trace_nth (index a_t) tr (Afence Opln)).

Definition correct_op_bt : Prop :=
  forall (tr : trace label)
    (TRIN : traces_t (tid b_t) tr) (BIN : event_mem b_t tr),
      (
        WCore.lab_is_r (trace_nth (index b_t) tr (Afence Opln)) ∪₁
        WCore.lab_is_w (trace_nth (index b_t) tr (Afence Opln))
      ) b_t.

Definition correct_op_at : Prop :=
  forall (tr : trace label)
    (TRIN : traces_t (tid a_t) tr) (BIN : event_mem a_t tr),
    (
      WCore.lab_is_r (trace_nth (index a_t) tr (Afence Opln)) ∪₁
      WCore.lab_is_w (trace_nth (index a_t) tr (Afence Opln))
    ) a_t.

Definition correct_mod_bt : Prop :=
  forall (tr : trace label)
    (TRIN : traces_t (tid b_t) tr) (BIN : event_mem b_t tr),
    ~mode_le Orel (WCore.lab_mode (
      trace_nth (index b_t) tr (Afence Opln)
    )).

Definition correct_mod_at : Prop :=
  forall (tr : trace label)
    (TRIN : traces_t (tid a_t) tr) (BIN : event_mem a_t tr),
    ~mode_le Oacq (WCore.lab_mode (
      trace_nth (index a_t) tr (Afence Opln)
    )).

Record correct_traces_t : Prop := {
  prf_at_tid : rtid <> tid_init;
  prf_closed : forall t (NINIT : t <> tid_init), prefix_closed t;
  prf_cov : full_coverage;
  prf_loc : correct_loc;
  prf_op_bt : correct_op_bt;
  prf_op_at : correct_op_at;
  prf_mod_bt : correct_mod_bt;
  prf_mod_at : correct_mod_at;
}.

Lemma simrel_xmm_step
    (INV : reord_step_pred X_t a_t b_t)
    (INV' : reord_step_pred X_t' a_t b_t)
    (STEP : xmm_step X_t X_t')
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper) :
  exists X_s',
    << SIMREL : reord_simrel X_s' X_t' a_t b_t mapper >> /\
    << STEP : xmm_step⁺ X_s X_s' >>.
Proof using.
  admit.
Admitted.

Lemma simrel_behavior b
    (INV : reord_step_pred X_t a_t b_t)
    (SIMREL : reord_simrel X_s X_t a_t b_t mapper)
    (INB : E_t b_t)
    (INA : E_t a_t)
    (BEH : behavior_spec G_t b) :
  behavior_spec G_s b.
Proof using.
  apply same_behavior with (G := G_t) (m := mapper); auto.
  all: try now apply INV.
  all: try now apply SIMREL.
  { eapply G_s_wf; eauto. }
  { rewrite (rsr_acts SIMREL), extra_a_none_l; auto.
    now rewrite set_union_empty_r. }
  rewrite (rsr_co SIMREL), extra_a_none_l; auto.
  now rewrite set_inter_empty_l, add_max_empty_r, union_false_r.
Qed.

Lemma corr_coh_inv
    (WF : Wf G_t)
    (RFC : rf_complete G_t)
    (INIT : is_init ⊆₁ E_t)
    (DEP : rmw_dep_t ≡ ∅₂)
    (DATA : data_t ≡ ∅₂)
    (CTRL : ctrl_t ≡ ∅₂)
    (ADDR : addr_t ≡ ∅₂)
    (CONT : contigious_actids G_t)
    (CORR : correct_traces_t)
    (FIN : set_finite (E_t \₁ is_init))
    (COH : trace_coherent traces_t G_t)
    (INITTID : E_t ∩₁ (fun e => tid e = tid_init) ⊆₁ is_init)
    (RMWD : rmw G_t ⊆ Sc_t × Sc_t) :
  reord_step_pred X_t a_t b_t.
Proof using.
  set (tr := thread_trace G_t rtid).
  assert (NINIT : rtid <> tid_init) by apply CORR.
  assert (EXTSB : ext_sb b_t a_t).
  { unfold ext_sb, i_a. split; auto; lia. }
  assert (NACQ : eq a_t ∩₁ E_t ⊆₁ set_compl Acq_t).
  { unfolder. intros x (EQ & XIN). subst x.
    intro FALSO. apply (prf_mod_at CORR) with tr; auto.
    { apply event_memE; auto. }
    unfold WCore.lab_mode, is_acq in *.
    subst tr. rewrite thread_trace_nth'; auto. }
  assert (NREL : eq b_t ∩₁ E_t ⊆₁ set_compl Rel_t).
  { unfolder. intros x (EQ & XIN). subst x.
    intro FALSO. apply (prf_mod_bt CORR) with tr; auto.
    { apply event_memE; auto. }
    unfold WCore.lab_mode, is_rel in *.
    subst tr. rewrite thread_trace_nth'; auto. }
  constructor; ins.
  { unfolder. intros x (EQ & XIN). subst x.
    destruct (prf_op_at CORR tr) as [ISR|ISW].
    { apply COH, CORR. }
    { apply event_memE; auto. }
    { right. unfold WCore.lab_is_r, is_r in *.
      subst tr.
      rewrite thread_trace_nth' in ISR; auto.
      desf. }
    left. unfold WCore.lab_is_w, is_w in *.
    subst tr.
    rewrite thread_trace_nth' in ISW; auto.
    desf. }
  { unfolder. intros x (EQ & XIN). subst x.
    destruct (prf_op_bt CORR tr) as [ISR|ISW].
    { apply COH, CORR. }
    { apply event_memE; auto. }
    { right. unfold WCore.lab_is_r, is_r in *.
      subst tr.
      rewrite thread_trace_nth' in ISR; auto.
      desf. }
    left. unfold WCore.lab_is_w, is_w in *.
    subst tr.
    rewrite thread_trace_nth' in ISW; auto.
    desf. }
  { unfolder. intros x y ((XEQ & XIN) & SLOC & (YEQ & YIN)).
    subst x y. apply (prf_loc CORR) with tr; auto.
    { apply event_memE; auto. }
    { apply event_memE; auto. }
    unfold same_loc, loc, WCore.lab_loc in *.
    subst tr. rewrite !thread_trace_nth'; auto. }
  { red in CONT. destruct (CONT _ NINIT) as [N EQ].
    assert (INA' : (E_t ∩₁ (fun e => rtid = tid e)) a_t).
    { basic_solver. }
    enough (INB' : (E_t ∩₁ (fun e => rtid = tid e)) b_t).
    { apply INB'. }
    apply EQ, thread_set_iff. apply EQ, thread_set_iff in INA'.
    unfold i_a in INA'. lia. }
  { unfold sb. unfolder. intros x y (((XEQ & XIN) & _) & SB & YIN).
    apply NINA. subst x. destruct y as [yl | yt yn]; ins.
    destruct classic with (yn = i_b + 1) as [EQ|NEQ].
    { desf. }
    apply ext_sb_dense with (e2 := (ThreadEvent yt yn)); auto.
    red. desf; split; ins. unfold i_a. lia. }
  { intros x y RMW. unfolder.
    apply (wf_rmwE WF) in RMW.
    unfolder in RMW. destruct RMW as (XIN & RMW & YIN).
    apply RMWD in RMW. destruct RMW as [XSC YSC].
    splits; auto.
    all: intro FALSO.
    { subst x. apply NACQ with a_t; [basic_solver|].
      unfold is_sc, is_acq in *. desf. }
    { subst x. apply NREL with b_t; [basic_solver|].
      unfold is_sc, is_rel in *. desf. }
    { subst y. apply NACQ with a_t; [basic_solver|].
      unfold is_sc, is_acq in *. desf. }
    subst y. apply NREL with b_t; [basic_solver|].
    unfold is_sc, is_rel in *. desf. }
  { unfold i_a. intro FALSO. desf. lia. }
  { unfold sb. unfolder.
    intros x y ((XEQ & XIN) & YEQ & YIN). subst x y.
    splits; auto. intros c (_ & BC & CIN) (_ & CA & _).
    unfold i_a in *. ins. desf. ins. desf. lia. }
  unfolder. intros x y (XEQ & SB & YIN). subst x.
  apply NINA, ext_sb_dense with (e2 := y); auto.
Qed.

End ReorderingSteps.