Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import xmm_s_hb.
Require Import Lia.
From xmm Require Import Reordering.
From xmm Require Import ThreadTrace.
From xmm Require Import Programs.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
Require Import Setoid Morphisms Program.Basics.

Open Scope program_scope.

Set Implicit Arguments.

Section SimRelSeq.

Variable X_s X_t : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'lab_t'" := (lab G_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'val_t'" := (val lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rhb_t'" := (rhb G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'rpo_t'" := (rpo G_t).
Notation "'rpo_imm_t'" := (rpo_imm G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).

Notation "'G_s'" := (WCore.G X_s).
Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rhb_s'" := (rhb G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'rpo_imm_s'" := (rpo_imm G_s).
Notation "'vf_s'" := (vf G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Definition po_seq := (Tid_ t_1 ∩₁ E_s) × (Tid_ t_2 ∩₁ E_s).

Record seq_simrel : Prop := {
    seq_inj : inj_dom E_t mapper;

    seq_tid_1 : forall e : actid, E_t e -> tid (mapper e) <> t_2 -> tid e = tid (mapper e);
    seq_tid_2 : forall e : actid, E_t e -> tid (mapper e) = t_2 -> tid e = t_1;

    seq_lab : eq_dom E_t (lab_s ∘ mapper) lab_t;
    seq_acts : E_s ≡₁ mapper ↑₁ E_t;
    seq_sb : sb_s ∪ po_seq ≡ mapper ↑ sb_t;
    seq_rf : rf_s ≡ mapper ↑ rf_t;
    seq_co : co_s ≡ mapper ↑ co_t;
    seq_rmw : rmw_s ≡ mapper ↑ rmw_t;
    seq_threads : threads_set G_s ≡₁ threads_set G_t ∪₁ eq t_2;

    seq_ctrl : ctrl_s ≡ ctrl_t;
    seq_data : data_s ≡ data_t;
    seq_addr : addr_s ≡ addr_t;
    seq_rmw_dep : rmw_dep_s ≡ rmw_dep_t;

    seq_init : fixset is_init mapper;
    (* rsr_mid : eq_dom (E_t \₁ eq a_t \₁ eq b_t) mapper id; *)
    seq_codom : mapper ↑₁ E_t ⊆₁ E_s;
}.

End SimRelSeq.

Section SeqSimrelInit.

Variable X_t X_s : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'G_s'" := (WCore.G X_s).

Lemma seq_simrel_init threads
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (THRD1 : threads t_1)
    (THRDNEQ : t_1 <> t_2)
    (INIT : threads tid_init) :
  << SIMREL : seq_simrel
    (WCore.Build_t (WCore.init_exec (threads ∪₁ eq t_2)) ∅₂)
    (WCore.Build_t (WCore.init_exec threads) ∅₂)
    t_1 t_2
    id >>.
Proof using.
    assert (IWF : Wf (WCore.init_exec threads)).
    { now apply WCore.wf_init_exec. }
    split; vauto; ins.
    { assert (FALSE : t_2 = tid_init).
      { rewrite <- H0. unfold tid. desf.
        unfold is_init in H. desf. }
      desf. }
    { clear; basic_solver. }
    { rewrite collect_rel_id; split; vauto.
      unfold po_seq; ins.
      assert (EMP1 : (fun e : actid => tid e = t_1)
                    ∩₁ (fun a : actid => is_init a) ≡₁ ∅).
      { split; [|basic_solver].
        intros x COND. destruct COND as [TID ISINIT].
        unfold is_init in ISINIT. desf. }
      assert (EMP2 : (fun e : actid => tid e = t_2)
                    ∩₁ (fun a : actid => is_init a) ≡₁ ∅).
      { split; [|basic_solver].
        intros x COND. destruct COND as [TID ISINIT].
        unfold is_init in ISINIT. desf. }
      rewrite EMP1, EMP2. clear; basic_solver 8. }
    all : clear; basic_solver.
Qed.

End SeqSimrelInit.

Section SimrelStep.

Variable X_t X_t' X_s : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.
Variable mapper_rev : actid -> actid.

Variable e : actid.
Variable l : label.

Variable dtrmt_t cmt_t : actid -> Prop.
Variable thrdle : relation thread_id.

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

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Hypothesis MAPREV : eq_dom E_t (mapper_rev ∘ mapper) id.

Lemma simrel_step_e_t1 (n : nat)
    (T1 : tid e = t_1) (IND: index e < n)
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (T2NOTIN : ~ threads_set G_t t_2)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper)
    (STEP : WCore.exec_inst X_t X_t' e l)
    (MAPINV : eq_dom E_t (mapper ∘ mapper) id) :
  exists mapper' X_s',
    << MAPINV' : eq_dom E_t' (mapper' ∘ mapper') id >> /\
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' >> /\
    << STEP : WCore.exec_inst X_s X_s' (mapper' e) l >>.
Proof using.
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  set (mapper' := upd mapper e e).
  set (mapper_rev' := upd mapper_rev e e).
  assert (ENOTIN : ~E_t e) by apply ADD.
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    clear - ENOTIN XINE. rewrite updo.
    all: congruence. }
  assert (MAPER_E : mapper' ↑₁ eq e ≡₁ eq e).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { clear - MAPEQ. now apply set_collect_eq_dom. }
  assert (EQACTS : E_t' ≡₁ E_t ∪₁ eq e) by apply ADD.
  assert (NEWE :
  << NINIT : ~is_init e >> /\
  << NOTIN : ~E_s e >> /\
  << TID : tid e = t_1 >>). 
  (* /\
  << NEWSB : ⦗E_s ∪₁ eq e⦘ ⨾ ext_sb ⨾ ⦗E_s ∪₁ eq e⦘ ≡
          sb_s ∪ WCore.sb_delta e E_s >>). *)
  { unfold NW; splits; vauto.
    { intro FALSO. unfold is_init in FALSO. desf. }
    admit. }
  (*  { unfold sb.
      rewrite (rsr_actsE CORR SIMREL).
      unfold extra_a; desf; [exfalso; now apply ETID|].
      rewrite set_union_empty_r.
      rewrite <- EQACTS. apply ADD. }
    unfold sb.
    rewrite rsr_actsE
      with (X_s := X_s) (X_t := X_t)
          (a_t := a_t) (b_t := b_t); eauto.
    unfold extra_a; desf.
    { rewrite <- (rsr_at_bt_tid CORR) in NQT.
      rewrite id_union, !seq_union_l, !seq_union_r.
      arewrite_false (⦗eq e⦘ ⨾ ext_sb ⨾ ⦗eq e⦘).
      { clear. unfolder. ins. desf.
        eapply ext_sb_irr; eauto. }
      arewrite_false (⦗eq e⦘ ⨾ ext_sb ⨾ ⦗E_t ∪₁ eq a_t⦘).
      { admit. }
      rewrite id_union at 3. rewrite seq_union_l.
      arewrite_false (⦗eq a_t⦘ ⨾ ext_sb ⨾ ⦗eq e⦘).
      { clear - NQT CORR. unfolder. unfold ext_sb.
        ins. desf; ins; [| desf].
        apply (rsr_at_ninit CORR). auto. }
      rewrite sb_delta_union.
      assert (SUB : WCore.sb_delta e (eq a_t) ⊆ WCore.sb_delta e E_t).
      { clear - NQT. unfolder. ins. desf. auto. }
      rewrite union_absorb_r with (r := WCore.sb_delta e (eq a_t)); auto.
      rewrite !union_false_r. apply union_more; [reflexivity |].
      arewrite (⦗E_t⦘ ⨾ ext_sb ⨾ ⦗eq e⦘ ≡ ⦗E_t⦘ ⨾ sb_t' ⨾ ⦗eq e⦘).
      { unfold sb. rewrite !seqA. seq_rewrite <- !id_inter.
        rewrite EQACTS. clear - ENOTIN. basic_solver 11. }
      rewrite (WCore.add_event_sb ADD), seq_union_l.
      arewrite_false (sb_t ⨾ ⦗eq e⦘).
      { clear - ENOTIN. rewrite wf_sbE. basic_solver. }
      rewrite union_false_l. unfold WCore.sb_delta.
      seq_rewrite <- cross_inter_l.
      rewrite set_inter_union_r, 2!set_inter_absorb_l.
      all: try now apply CORR.
      all: basic_solver 11. }
    rewrite !set_union_empty_r.
    rewrite <- EQACTS. apply ADD. } *)
  unfold NW in NEWE.
  destruct NEWE as (NINIT & NOTIN & TID).

  set (G_s' := {|
  acts_set := mapper' ↑₁ E_t';
    threads_set := threads_set G_s;
    lab := lab_t' ∘ mapper_rev';
    rf := mapper' ↑ rf_t';
    co := mapper' ↑ co_t';
    rmw := mapper' ↑ rmw_t';
    rmw_dep := rmw_dep_t';
    ctrl := ctrl_t';
    data := data_t';
    addr := addr_t';
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).

  exists mapper', X_s'.
  assert (MAPPINV' : eq_dom E_t' (mapper' ∘ mapper') id).
  { unfold mapper'. unfold eq_dom. intros x XINE. 
    destruct classic with (x = e) as [EQ | NEQ].
    { subst x. unfold compose. rewrite !upds; vauto. }
    unfold compose. rewrite !updo; vauto.
    assert (NINE : E_t x).
    { apply EQACTS in XINE.
      destruct XINE as [XINE | XINE]; vauto. }
    { apply MAPINV; vauto. }
    rewrite updo; vauto.
    intros FALSE.
    assert (INE : E_s (mapper x)).
    { apply SIMREL. unfold set_collect.
      exists x; split.
      { apply EQACTS in XINE. 
        clear - XINE NEQ. destruct XINE; basic_solver. }
      vauto. }
    basic_solver. }
  splits; vauto.
  { constructor; vauto; simpl; try basic_solver 6.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { clear - SIMREL MAPEQ.
        unfolder. ins. apply (seq_inj SIMREL); ins.
        now rewrite <- !MAPEQ. }
      { clear. basic_solver. }
      rewrite MAPER_E, MAPSUB, (seq_codom SIMREL).
      clear - NOTIN. basic_solver. }
    { intros ev INE' TIDCOND.
      destruct classic with (ev = e) as [EQ | NEQ].
      { subst ev. unfold mapper'. rewrite upds; vauto. }
      unfold mapper'. rewrite updo; vauto.
      apply (seq_tid_1 SIMREL); vauto.
      apply EQACTS in INE'. destruct INE' as [C1 | C2]; vauto.
      unfold mapper' in TIDCOND. rewrite updo in TIDCOND; vauto. }
    { intros ev INE' TIDCOND.
      destruct classic with (ev = e) as [EQ | NEQ]; vauto.
      apply (seq_tid_2 SIMREL); vauto.
      { apply EQACTS in INE'. destruct INE' as [C1 | C2]; vauto. }
      unfold mapper'. rewrite updo; vauto. }
    { intros x COND. unfold compose.
      destruct classic with (x = e) as [EQ | NEQ].
      { subst x. unfold mapper', mapper_rev'.
        rewrite !upds; vauto. }
      unfold mapper', mapper_rev'.
      rewrite !updo; vauto.
      { unfold compose in MAPREV. rewrite MAPREV.
        admit. }
      admit. }
    { admit. (*TODO : po-work*) }
    { rewrite (seq_threads SIMREL).
      destruct ADD. rewrite add_event_threads; vauto. }
    unfold mapper'. intros x COND.
    destruct classic with (x = e) as [EQ | NEQ].
    { subst x. rewrite upds; vauto. }
    rewrite updo; vauto.
    apply (seq_init SIMREL); vauto. }
  constructor.
  { unfold WCore.add_event.
    exists (option_map mapper' r), (mapper' ↑₁ R1),
        (option_map mapper' w),
        (mapper' ↑₁ W1),
        (mapper' ↑₁ W2).
    apply add_event_to_wf; simpl; vauto.
    { apply sico_init_acts_s with
            (X_t := X_t) (mapper := mapper).
      { constructor. all : apply SIMREL. }
      destruct ADD. apply add_event_init. }
    { unfold mapper'. rewrite upds. exact NOTIN. }
    { unfold mapper'. rewrite upds; vauto. }
    { unfold mapper'. rewrite upds. basic_solver. }
    { rewrite EQACTS. rewrite set_collect_union.
      rewrite MAPER_E, MAPSUB. rewrite (seq_acts SIMREL).
      unfold mapper'. rewrite upds. basic_solver. }
    { unfold mapper'.
      destruct ADD. rewrite add_event_lab.
      unfold compose. rewrite upds.
      admit. }
    all : admit. }
  all : admit.
Admitted.

Lemma simrel_step_e_t2 (n : nat)
    (T1 : tid e = t_1) (IND: index e >= n)
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (T2NOTIN : ~ threads_set G_t t_2)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper)
    (STEP : WCore.exec_inst X_t X_t' e l)
    (MAPINV : eq_dom E_t (mapper ∘ mapper) id) :
  exists mapper' X_s',
    << MAPINV' : eq_dom E_t' (mapper' ∘ mapper') id >> /\
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' >> /\
    << STEP : WCore.exec_inst X_s X_s' (mapper' e) l >>.
Proof using.
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  set (mapper' := upd mapper e (ThreadEvent t_2 (index e - n))).
  assert (ENOTIN : ~E_t e) by apply ADD.
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    clear - ENOTIN XINE. rewrite updo.
    all: congruence. }
  assert (MAPER_E : mapper' ↑₁ eq e ≡₁ eq (ThreadEvent t_2 (index e - n))).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { clear - MAPEQ. now apply set_collect_eq_dom. }
  assert (EQACTS : E_t' ≡₁ E_t ∪₁ eq e) by apply ADD.
  assert (NEWE :
    << NINIT : ~is_init e >> /\
    << NOTIN : ~E_s e >> /\
    << TID : tid e = t_1 >>). 
  { admit. }
  unfold NW in NEWE. destruct NEWE as (NINIT & NOTIN & TID).

  set (G_s' := {|
    acts_set := E_s ∪₁ eq (ThreadEvent t_2 (index e - n));
    threads_set := threads_set G_s;
    lab := lab_t' ∘ mapper';
    rf := mapper' ↑ rf_t';
    co := mapper' ↑ co_t';
    rmw := mapper' ↑ rmw_t';
    rmw_dep := rmw_dep_t';
    ctrl := ctrl_t';
    data := data_t';
    addr := addr_t';
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).

  exists mapper', X_s'; splits.
  { admit. }
  { constructor; vauto; simpl; try basic_solver 6.
    { rewrite (WCore.add_event_acts ADD). apply inj_dom_union.
      { clear - SIMREL MAPEQ.
        unfolder. ins. apply (seq_inj SIMREL); ins.
        now rewrite <- !MAPEQ. }
      { clear. basic_solver. }
      rewrite MAPER_E, MAPSUB, (seq_codom SIMREL).
      admit. }
    { intros ev INE' TIDCOND.
      destruct classic with (ev = e) as [EQ | NEQ].
      { subst ev. unfold mapper'. rewrite upds; vauto.
        unfold mapper' in TIDCOND. rewrite upds in TIDCOND; vauto. }
      unfold mapper'. rewrite updo; vauto.
      apply (seq_tid_1 SIMREL); vauto.
      apply EQACTS in INE'. destruct INE' as [C1 | C2]; vauto.
      unfold mapper' in TIDCOND. rewrite updo in TIDCOND; vauto. }
    { intros ev INE' TIDCOND.
      destruct classic with (ev = e) as [EQ | NEQ]; vauto.
      { rewrite EQ; vauto. }
      apply (seq_tid_2 SIMREL); vauto.
      { apply EQACTS in INE'. destruct INE' as [C1 | C2]; vauto.
        exfalso; basic_solver. }
      unfold mapper' in TIDCOND.
      rewrite updo in TIDCOND; vauto. }
    { unfold compose.
      admit. }
    { admit. }
    { admit. }
    all : admit. }
  constructor.
  { unfold WCore.add_event.
    exists (option_map mapper' r), (mapper' ↑₁ R1),
        (option_map mapper' w),
        (mapper' ↑₁ W1),
        (mapper' ↑₁ W2).
    apply add_event_to_wf; simpl; vauto.
    { apply sico_init_acts_s with
            (X_t := X_t) (mapper := mapper).
      { constructor. all : admit. }
      destruct ADD. apply add_event_init. }
    { unfold mapper'. rewrite upds. admit. }
    { unfold mapper'. rewrite upds; vauto. }
    { unfold mapper'. rewrite upds. basic_solver. }
    { clear - MAPER_E. admit. }
    { unfold mapper'. rewrite upds.
      destruct ADD; vauto. }
    all : admit. }
  all : admit. 
Admitted.

Lemma simrel_step_e_else
    (T1 : tid e <> t_1)
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (T2NOTIN : ~ threads_set G_t t_2)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper)
    (STEP : WCore.exec_inst X_t X_t' e l)
    (MAPINV : eq_dom E_t (mapper ∘ mapper) id) :
  exists mapper' X_s',
    << MAPINV' : eq_dom E_t' (mapper' ∘ mapper') id >> /\
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' >> /\
    << STEP : WCore.exec_inst X_s X_s' (mapper' e) l >>.
Proof using.
  destruct STEP as [ADD RFC CONS].
  destruct ADD as (r & R1 & w & W1 & W2 & ADD).
  set (mapper' := upd mapper e e).
  assert (ENOTIN : ~E_t e) by apply ADD.
  assert (MAPEQ : eq_dom E_t mapper' mapper).
  { subst mapper'. unfolder. intros x XINE.
    clear - ENOTIN XINE. rewrite updo.
    all: congruence. }
  assert (MAPER_E : mapper' ↑₁ eq e ≡₁ eq e).
  { subst mapper'. rewrite set_collect_eq. now rupd. }
  assert (MAPSUB : mapper' ↑₁ E_t ≡₁ mapper ↑₁ E_t).
  { clear - MAPEQ. now apply set_collect_eq_dom. }
  assert (EQACTS : E_t' ≡₁ E_t ∪₁ eq e) by apply ADD.
  assert (NEWE :
  << NINIT : ~is_init e >> /\
  << NOTIN : ~E_s e >> /\
  << TID : tid e = t_1 >>).
  { admit. }
  unfold NW in NEWE. destruct NEWE as (NINIT & NOTIN & TID).

  set (G_s' := {|
  acts_set := mapper' ↑₁ E_t';
    threads_set := threads_set G_s;
    lab := lab_t' ∘ mapper';
    rf := mapper' ↑ rf_t';
    co := mapper' ↑ co_t';
    rmw := mapper' ↑ rmw_t';
    rmw_dep := rmw_dep_t';
    ctrl := ctrl_t';
    data := data_t';
    addr := addr_t';
  |}).
  set (X_s' := {|
    WCore.sc := WCore.sc X_s;
    WCore.G := G_s';
  |}).

  exists mapper', X_s'; splits.
  { admit. }
  { constructor; vauto; simpl; try basic_solver 6. }
  constructor.
  { unfold WCore.add_event.
    exists (option_map mapper' r), (mapper' ↑₁ R1),
        (option_map mapper' w),
        (mapper' ↑₁ W1),
        (mapper' ↑₁ W2).
    apply add_event_to_wf; simpl; vauto. }
  all : admit. 
Admitted.

Definition seq_graph_rex : execution := {|
  acts_set := id ↑₁ E_t';
  threads_set := threads_set G_s;
  lab := lab_t' ∘ id;
  rf := id ↑ rf_t';
  co := id ↑ co_t';
  rmw := id ↑ rmw_t';
  rmw_dep := rmw_dep_t';
  ctrl := ctrl_t';
  data := data_t';
  addr := addr_t';
|}.

Definition seq_rex := {|
  WCore.sc := WCore.sc X_t;
  WCore.G := seq_graph_rex;
|}.

Notation "'X_s''" := (seq_rex).
Notation "'G_s''" := (WCore.G X_s').
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

Definition cmt' := mapper ↑₁ cmt_t.
Definition dtrmt' := mapper ↑₁ dtrmt_t.

Lemma simrel_step_reex 
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper)
    (STEP : WCore.reexec X_t X_t' mapper dtrmt_t cmt_t) :
  seq_simrel X_s' X_t' t_1 t_2 id.
Proof using.
  constructor; vauto.
  all : admit.
Admitted.

Lemma reex_step_reex
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper)
    (STEP : WCore.reexec X_t X_t' mapper dtrmt_t cmt_t) :
  WCore.reexec X_s X_s' id dtrmt' cmt'.
Proof using.
  admit.
Admitted.

End SimrelStep.

Section SimrelGen.

Variable X_t X_t' X_s : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.

Variable dtrmt_t cmt_t : actid -> Prop.
Variable thrdle : relation thread_id.

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

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Lemma seq_step_gen
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (THRDNEQ : t_1 <> t_2)
    (STEP : xmm_step X_t X_t')
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper) :
  exists X_s' mapper',
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' >> /\
    << STEP : xmm_step⁺ X_s X_s' >>.
Proof using.
  admit.
Admitted.

End SimrelGen.

Section BehaviorGraph.

Variable G_1 G_2 : execution.

Notation "'E_1'" := (acts_set G_1).

Notation "'lab'" := (lab G_1).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).

Definition graph_locations (G : execution) : Set :=
  { l : location | exists e, acts_set G e /\ loc e = Some l }.

Definition same_behaviors (G_1 G_2 : execution) : Prop :=
  behavior_spec G_1 = behavior_spec G_2.

End BehaviorGraph.

Section SimrelMain.

Variable X_t_init X_s_init X_t : WCore.t.
Variable t_1 t_2 : thread_id.

Notation "'G_t_init'" := (WCore.G X_t_init).
Notation "'G_s_init'" := (WCore.G X_s_init).
Notation "'G_t'" := (WCore.G X_t).

Notation "'R' G" := (fun e => is_true (is_r (lab G) e)) (at level 1).
Notation "'F' G" := (fun e => is_true (is_f (lab G) e)) (at level 1).
Notation "'W' G" := (fun e => is_true (is_w (lab G) e)) (at level 1).
Notation "'Acq' G" := (fun e => is_true (is_acq (lab G) e)) (at level 1).
Notation "'Rlx' G" := (fun e => is_true (is_rlx (lab G) e)) (at level 1).
Notation "'Rel' G" := (fun e => is_true (is_rel (lab G) e)) (at level 1).

Notation "'lab_t_init'" := (lab G_t_init).
Notation "'val_t_init'" := (val lab_t_init).
Notation "'loc_t_init'" := (loc lab_t_init).
Notation "'same_loc_t_init'" := (same_loc lab_t_init).
Notation "'E_t_init'" := (acts_set G_t_init).
Notation "'sb_t_init'" := (sb G_t_init).
Notation "'rf_t_init'" := (rf G_t_init).
Notation "'co_t_init'" := (co G_t_init).
Notation "'rmw_t_init'" := (rmw G_t_init).
Notation "'rpo_t_init'" := (rpo G_t_init).
Notation "'rmw_dep_t_init'" := (rmw_dep G_t_init).
Notation "'data_t_init'" := (data G_t_init).
Notation "'ctrl_t_init'" := (ctrl G_t_init).
Notation "'addr_t_init'" := (addr G_t_init).
Notation "'W_t_init'" := (fun x => is_true (is_w lab_t_init x)).
Notation "'R_t_init'" := (fun x => is_true (is_r lab_t_init x)).
Notation "'Loc_t_init_' l" := (fun e => loc_t_init e = l) (at level 1).

Notation "'lab_s_init'" := (lab G_s_init).
Notation "'val_s_init'" := (val lab_s_init).
Notation "'loc_s_init'" := (loc lab_s_init).
Notation "'same_loc_s_init'" := (same_loc lab_s_init).
Notation "'E_s_init'" := (acts_set G_s_init).
Notation "'loc_s_init'" := (loc lab_s_init).
Notation "'sb_s_init'" := (sb G_s_init).
Notation "'rf_s_init'" := (rf G_s_init).
Notation "'co_s_init'" := (co G_s_init).
Notation "'rmw_s_init'" := (rmw G_s_init).
Notation "'rpo_s_init'" := (rpo G_s_init).
Notation "'rmw_dep_s_init'" := (rmw_dep G_s_init).
Notation "'data_s_init'" := (data G_s_init).
Notation "'ctrl_s_init'" := (ctrl G_s_init).
Notation "'addr_s_init'" := (addr G_s_init).
Notation "'W_s_init'" := (fun x => is_true (is_w lab_s_init x)).
Notation "'R_s_init'" := (fun x => is_true (is_r lab_s_init x)).
Notation "'Loc_s_init_' l" := (fun e => loc_s_init e = l) (at level 1).

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

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Lemma simrel_main
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (THRDNEQ : t_1 <> t_2)
    (TARGETPTH : xmm_step＊ X_t_init X_t) :
  exists X_s mapper,
    << SIMREL : seq_simrel X_s X_t t_1 t_2 mapper >> /\
    << STEP : xmm_step＊ X_s_init X_s >> /\
    << BEHRS : same_behaviors (WCore.G X_s) G_t >>.
Proof using.
  admit.
Admitted.

End SimrelMain.

Section ProgMain.

Variable X_t : WCore.t.
Variable t_1 t_2 : thread_id.
Variable threads : thread_id -> Prop.

Variable p1 p2 : program.

Definition X_t_init : WCore.t := WCore.Build_t (WCore.init_exec threads) ∅₂.
Definition X_s_init : WCore.t := WCore.Build_t (WCore.init_exec (threads ∪₁ eq t_2)) ∅₂.

Hypothesis PROGSEQ : program_sequented p1 p2 t_1 t_2.

Lemma prog_supp : 
  exists X_s mapper,
    << SIMREL : seq_simrel X_s X_t t_1 t_2 mapper >> /\
    << STEP   : xmm_step＊ X_s_init X_s >> /\
    << BEHRS  : same_behaviors (WCore.G X_s) (WCore.G X_t) >>.
Proof using.
  admit.
Admitted.

Lemma prog_helper X_s mapper :
  seq_simrel X_s X_t t_1 t_2 mapper ->
  exec_sequent X_s X_t p1 p2 t_1 t_2.
Proof using.
  intros SIMREL.
  constructor; vauto.
  intros tr_1 tr2 TR1 TR2 CR1 CR2.
  constructor. all : admit.
Admitted.

Lemma prog_main :
  exists X_s,
    << SEQUED : exec_sequent X_s X_t p1 p2 t_1 t_2 >> /\
    << STEP   : xmm_step＊ X_s_init X_s >> /\
    << BEHRS  : same_behaviors (WCore.G X_s) (WCore.G X_t) >>.
Proof using.
  destruct prog_supp as (X_s & mapper & SIMREL & STEP & BEHRS).
  exists X_s; splits; auto.
  apply prog_helper with (mapper := mapper).
  vauto.
Qed.

End ProgMain.
