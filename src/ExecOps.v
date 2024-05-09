From imm Require Import Events Execution imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From PromisingLib Require Import Basic.

Require Import AuxDef.
Require Import ThreadTrace.

Require Import Program.Basics.

Open Scope program_scope.

Set Implicit Arguments.

Section ExecOps.

Variable G : execution.

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'is_acq'" := (is_acq lab).
Notation "'is_rel'" := (is_rel lab).
Notation "'is_rlx'" := (is_rlx lab).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'data'" := (data G).
Notation "'ctrl'" := (ctrl G).
Notation "'addr'" := (addr G).
Notation "'rmw'" := (rmw G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'F'" := (is_f lab).
Notation "'R_ex'" := (R_ex lab).

Definition exec_upd_lab e l : execution := {|
  acts_set := E;
  threads_set := threads_set G;
  lab := upd lab e l;
  rmw := rmw;
  data := data;
  addr := addr;
  ctrl := ctrl;
  rmw_dep := rmw_dep;
  rf := rf;
  co := co;
|}.
Definition exec_add_read_event_nctrl e : execution := {|
  acts_set := E ∪₁ eq e;
  threads_set := threads_set G;
  lab := lab;
  rmw := rmw;
  data := data;
  addr := addr;
  ctrl := ctrl;
  rmw_dep := rmw_dep;
  rf := rf;
  co := co;
|}.
Definition exec_add_rf delta_rf : execution := {|
  acts_set := E;
  threads_set := threads_set G;
  lab := lab;
  rmw := rmw;
  data := data;
  addr := addr;
  ctrl := ctrl;
  rmw_dep := rmw_dep;
  rf := rf ∪ delta_rf;
  co := co;
|}.
Definition exec_mapped f lab' : execution := {|
  acts_set := f ↑₁ E;
  threads_set := threads_set G;
  lab := lab';
  rmw := f ↑ rmw;
  data := f ↑ data;
  addr := f ↑ addr;
  ctrl := f ↑ ctrl;
  rmw_dep := f ↑ rmw_dep;
  rf := f ↑ rf;
  co := f ↑ co;
|}.

Lemma exec_add_read_event_nctrl_same_lab e :
  @lab (exec_add_read_event_nctrl e) = lab.
Proof using.
  now unfold exec_add_read_event_nctrl.
Qed.

Lemma exec_add_rf_same_lab delta_rf :
  @lab (exec_add_rf delta_rf) = lab.
Proof using.
  now unfold exec_add_rf.
Qed.

Lemma exec_upd_lab_W e l
    (U2V : same_label_u2v (lab e) l) :
  is_w (upd lab e l) ≡₁ W.
Proof using.
  unfold same_label_u2v in U2V.
  unfold is_w; unfolder; splits.
  all: intro x.
  all: tertium_non_datur (x = e) as [HEQ|HEQ].
  all: subst; rupd; desf.
Qed.

Lemma exec_upd_lab_R e l
    (U2V : same_label_u2v (lab e) l) :
  is_r (upd lab e l) ≡₁ R.
Proof using.
  unfold same_label_u2v in U2V.
  unfold is_r; unfolder; splits.
  all: intro x.
  all: tertium_non_datur (x = e) as [HEQ|HEQ].
  all: subst; rupd; desf.
Qed.

Lemma exec_upd_lab_F e l
    (U2V : same_label_u2v (lab e) l) :
  is_f (upd lab e l) ≡₁ F.
Proof using.
  unfold same_label_u2v in U2V.
  unfold is_f; unfolder; splits.
  all: intro x.
  all: tertium_non_datur (x = e) as [HEQ|HEQ].
  all: subst; rupd; desf.
Qed.

Lemma exec_upd_lab_is_sc e l
    (U2V : same_label_u2v (lab e) l) :
  is_sc (upd lab e l) ≡₁ is_sc lab.
Proof using.
  unfold same_label_u2v in U2V.
  unfold is_sc, mod; unfolder; splits.
  all: intro x.
  all: tertium_non_datur (x = e) as [HEQ|HEQ].
  all: subst; rupd; do 2 desf.
Qed.

Lemma exec_upd_lab_R_ex e l
    (U2V : same_label_u2v (lab e) l) :
  @R_ex _ (upd lab e l) ≡₁ R_ex.
Proof using.
  unfold same_label_u2v in U2V.
  unfold R_ex; unfolder; splits.
  all: intro x.
  all: tertium_non_datur (x = e) as [HEQ|HEQ].
  all: subst; rupd; do 2 desf.
Qed.

Lemma exec_upd_lab_loc e l
    (U2V : same_label_u2v (lab e) l) :
  @loc _ (upd lab e l) = loc.
Proof using.
  apply functional_extensionality. intro x.
  unfold loc. tertium_non_datur (x = e); subst.
  all: rupd.
  unfold same_label_u2v in U2V; do 2 desf.
Qed.

Lemma exec_upd_lab_same_loc e l
    (U2V : same_label_u2v (lab e) l) :
  @same_loc _ (upd lab e l) ≡ same_loc.
Proof using.
  unfold same_loc. rewrite exec_upd_lab_loc; ins.
Qed.

Lemma exec_mapped_W (f : actid -> actid) lab'
    (FSURJ : forall y, exists x, y = f x)
    (HLAB : lab = lab' ∘ f) :
  is_w lab' ≡₁ f ↑₁ W.
Proof using.
  unfold compose in *. rewrite HLAB. unfolder.
  split; intros x HSET; desf; unfold is_w in *.
  destruct (FSURJ x) as [y HEQ]. exists y.
  now rewrite <- HEQ.
Qed.

Lemma exec_mapped_R (f : actid -> actid) lab'
    (FSURJ : forall y, exists x, y = f x)
    (HLAB : lab = lab' ∘ f) :
  is_r lab' ≡₁ f ↑₁ R.
Proof using.
  unfold compose in *. rewrite HLAB. unfolder.
  split; intros x HSET; desf; unfold is_r in *.
  destruct (FSURJ x) as [y HEQ]. exists y.
  now rewrite <- HEQ.
Qed.

Lemma exec_mapped_F (f : actid -> actid) lab'
    (FSURJ : forall y, exists x, y = f x)
    (HLAB : lab = lab' ∘ f) :
  is_f lab' ≡₁ f ↑₁ F.
Proof using.
  unfold compose in *. rewrite HLAB. unfolder.
  split; intros x HSET; desf; unfold is_f in *.
  destruct (FSURJ x) as [y HEQ]. exists y.
  now rewrite <- HEQ.
Qed.

Lemma exec_mapped_R_ex (f : actid -> actid) lab'
    (FSURJ : forall y, exists x, y = f x)
    (HLAB : lab = lab' ∘ f) :
  @R_ex _ lab' ≡₁ f ↑₁ R_ex.
Proof using.
  unfold compose in *. rewrite HLAB. unfolder.
  split; intros x HSET; desf; unfold R_ex in *.
  destruct (FSURJ x) as [y HEQ]. exists y.
  now rewrite <- HEQ.
Qed.

Lemma exec_mapped_is_sc (f : actid -> actid) lab'
    (FSURJ : forall y, exists x, y = f x)
    (HLAB : lab = lab' ∘ f) :
  is_sc lab' ≡₁ f ↑₁ (is_sc lab).
Proof using.
  unfold compose in *. rewrite HLAB. unfolder.
  split; intros x HSET; desf; unfold is_sc, mod in *.
  destruct (FSURJ x) as [y HEQ]. exists y.
  now rewrite <- HEQ.
Qed.

Lemma exec_mapped_loc (f : actid -> actid) :
  @loc _ (lab ∘ f) = loc ∘ f.
Proof using.
  now unfold compose, loc.
Qed.

Lemma exec_mapped_val (f : actid -> actid) :
  @val _ (lab ∘ f) = val ∘ f.
Proof using.
  now unfold compose, val.
Qed.

Lemma exec_mapped_same_loc (f : actid -> actid) lab'
    (FSURJ : forall y, exists x, y = f x)
    (HLAB : lab = lab' ∘ f) :
  @same_loc _ lab' ≡ f ↑ same_loc.
Proof using.
  unfold compose in *. rewrite HLAB. unfolder.
  split; intros x y HREL; desf; unfold same_loc, loc in *.
  destruct (FSURJ x) as [x' HEQX], (FSURJ y) as [y' HEQY].
  exists x', y'. now rewrite <- HEQX, <- HEQY.
Qed.

Lemma exec_upd_lab_wf e l
    (ENINIT : ~is_init e)
    (U2V : same_label_u2v (lab e) l)
    (NRFR : ~codom_rel rf e)
    (NRFL : ~dom_rel rf e)
    (WF : Wf G) :
  Wf (exec_upd_lab e l).
Proof using.
  unfolder in NRFR. unfolder in NRFL.
  assert (SAME_SB : @sb (exec_upd_lab e l) ≡ sb).
  { unfold sb; ins. }
  constructor; unfold exec_upd_lab; ins.
  all: rewrite ?exec_upd_lab_W, ?exec_upd_lab_F,
               ?exec_upd_lab_R, ?SAME_SB,
               ?exec_upd_lab_R_ex,
               ?exec_upd_lab_same_loc by exact U2V.
  all: try now apply WF.
  all: try now rewrite exec_upd_lab_loc in *; ins; apply WF.
  { unfold funeq, val; intros a b RF.
    rewrite !updo; try now apply WF.
    all: intro F; subst; eauto. }
  rewrite updo; [now apply WF | destruct e; ins].
Qed.

Lemma exec_add_event_wf_nctrl e
    (ENINIT : ~is_init e)
    (HIN : ~E e)
    (IS_R : R e)
    (ETID : tid e <> tid_init)
    (ETHR : threads_set G (tid e))
    (HLOC : forall l (LOC : loc e = Some l), E (InitEvent l))
    (NCTRL : ctrl ≡ ∅₂)
    (RMW_SAVED : rmw ⊆ immediate (@sb (exec_add_read_event_nctrl e)))
    (WF : Wf G) :
  Wf (exec_add_read_event_nctrl e).
Proof using.
  assert (SUB_SB : sb ⊆ @sb (exec_add_read_event_nctrl e)).
  { unfold sb, exec_add_read_event_nctrl. ins. basic_solver. }
  constructor; ins.
  all: try now apply WF.
  all: try now transitivity sb; ins; apply WF.
  { unfolder in H. desf; try now apply WF.
    all: destruct a, b; ins.
    all: congruence. }
  { now rewrite NCTRL, seq_false_l. }
  { rewrite WF.(wf_rfE), <- !restr_relE, restr_restr.
    now rewrite set_inter_absorb_r by basic_solver. }
  { rewrite WF.(wf_coE), <- !restr_relE, restr_restr.
    now rewrite set_inter_absorb_r by basic_solver. }
  { assert (N_IS_W : ~W e) by (unfold is_w, is_r in *; desf).
    arewrite ((E ∪₁ eq e) ∩₁ W ≡₁ E ∩₁ W); [basic_solver|].
    now apply WF. }
  { match goal with
    | [EE : exists a, (E ∪₁ _) a /\ loc a = _ |- _]
        => rename EE into AHLOC
    | _ => fail "not found"
    end.
    left. unfolder in AHLOC. desf; [apply WF|]; eauto. }
  unfolder in EE. desf. now apply WF.
Qed.

Lemma exec_add_rf_wf delta_rf
    (NEW_RF : forall x
                  (DOM1 : dom_rel rf⁻¹ x)
                  (DOM2 : dom_rel delta_rf⁻¹ x),
                False)
    (FUNEQ : funeq val delta_rf)
    (FUNC : functional delta_rf⁻¹)
    (DELTA_RF_WFE : delta_rf ≡ ⦗E⦘ ⨾ delta_rf ⨾ ⦗E⦘)
    (DELTA_RF_WFD : delta_rf ≡ ⦗W⦘ ⨾ delta_rf ⨾ ⦗R⦘)
    (DELTA_RF : delta_rf ⊆ same_loc)
    (NCTRL : ctrl ≡ ∅₂)
    (WF : Wf G) :
  Wf (exec_add_rf delta_rf).
Proof using.
  assert (EQ_SB : @sb (exec_add_rf delta_rf) ≡ sb).
  { unfold sb, exec_add_rf. ins. }
  constructor; rewrite ?EQ_SB; ins.
  all: try now apply WF.
  { rewrite seq_union_l, seq_union_r.
    apply union_more; [apply WF | ins]. }
  { rewrite seq_union_l, seq_union_r.
    apply union_more; [apply WF | ins]. }
  { apply inclusion_union_l; [apply WF | ins]. }
  { apply funeq_union; [apply WF | ins]. }
  apply functional_union; ins. apply WF.
Qed.

Lemma exec_mapped_wf f lab'
    (FINJ : inj_dom ⊤₁ f)
    (FSURJ : forall y, exists x, y = f x)
    (HLAB : lab = lab' ∘ f)
    (PRESRVE_RMW : f ↑ rmw ⊆ immediate (@sb (exec_mapped f lab')))
    (PRESEVE_DATA : f ↑ data ⊆ (@sb (exec_mapped f lab')))
    (PRESERVE_ADDR : f ↑ addr ⊆ (@sb (exec_mapped f lab')))
    (PRESERVE_RMW_DEP : f ↑ rmw_dep ⊆ (@sb (exec_mapped f lab')))
    (FMAPINIT : forall l, f (InitEvent l) = InitEvent l)
    (NCTRL : ctrl ≡ ∅₂)
    (MAPIDS : forall a b, (f ↑₁ E) a -> (f ↑₁ E) b ->
              a <> b -> tid a = tid b -> ~is_init a -> index a <> index b)
    (NNEW_TIDS : (tid ∘ f )↑₁ E ⊆₁ threads_set G)
    (WF : Wf G) :
  Wf (exec_mapped f lab').
Proof using.
  constructor; ins.
  all: rewrite ?exec_mapped_W, ?exec_mapped_R,
               ?exec_mapped_F, ?exec_mapped_loc,
               ?exec_mapped_same_loc, ?exec_mapped_R_ex by ins.
  all: rewrite <- ?set_collect_union, <- ?collect_rel_eqv,
               <- ?collect_rel_seq.
  all: try now eapply inj_dom_mori with (x := ⊤₁); ins.
  all: try now apply collect_rel_more, WF.
  all: try now apply collect_rel_mori, WF.
  { desf. eauto. }
  { rewrite NCTRL. basic_solver. }
  { rewrite NCTRL. basic_solver. }
  { unfolder. intros a b RF. desf.
    change (@val _ lab' (f x')) with (@val _ (lab' ∘ f) x').
    change (@val _ lab' (f y')) with (@val _ (lab' ∘ f) y').
    rewrite <- HLAB. now apply WF. }
  { rewrite <- collect_rel_transp.
    arewrite (rf⁻¹ ≡ restr_rel ⊤₁ rf⁻¹) by basic_solver.
    apply functional_collect_rel_inj; auto.
    apply functional_restr, WF. }
  { arewrite (co ≡ restr_rel ⊤₁ co) by basic_solver.
    apply transitive_collect_rel_inj, transitive_restr, WF.
    ins. }
  { eapply is_total_more; [ | eauto |
      apply total_collect_rel, WF with (ol := ol) ].
    rewrite !set_collect_interE by ins.
    repeat apply set_equiv_inter; ins.
    rewrite HLAB. unfolder.
    split; ins; desf; unfold loc, compose.
    destruct (FSURJ x) as [y HEQ].
    exists y; rewrite HEQ; split; ins. }
  { arewrite (co ≡ restr_rel ⊤₁ co) by basic_solver.
    apply collect_rel_irr_inj, irreflexive_restr, WF.
    ins. }
  { unfolder. unfolder in H. desf.
    destruct (FSURJ (InitEvent l)) as [yi HEQ].
    exists yi; split; eauto.
    rewrite <- FMAPINIT in HEQ. apply FINJ in HEQ; ins.
    subst yi. apply WF. eexists; split; eauto.
    rewrite HLAB. now unfold compose. }
  { rewrite <- WF.(wf_init_lab), HLAB.
    unfold compose. now rewrite FMAPINIT. }
  apply NNEW_TIDS. unfolder.
  unfolder in EE. desf. eauto.
Qed.

Lemma exec_upd_lab_cont e l
    (CONT : contigious_actids G) :
  contigious_actids (exec_upd_lab e l).
Proof using.
  ins.
Qed.

Lemma exec_add_event_cont e
    (TID : tid e <> tid_init)
    (CONT : contigious_actids G)
    (MAXSB : (fun x => ext_sb x e) ⊆₁ acts_set G ∩₁ same_tid e ∪₁ is_init)  :
  contigious_actids (exec_add_read_event_nctrl e).
Proof using.
  eapply add_event_to_contigious; eauto.
Qed.

Lemma exec_add_rf_cont delta_rf
    (CONT : contigious_actids G) :
  contigious_actids (exec_add_rf delta_rf).
Proof using.
  ins.
Qed.

End ExecOps.

Section ExecOpsSub.

Variable G G' : execution.

Lemma exec_upd_lab_sub e l
    (SUB : sub_execution G' G ∅₂ ∅₂) :
  sub_execution (exec_upd_lab G' e l)
                (exec_upd_lab G  e l)
                ∅₂ ∅₂.
Proof using.
  constructor; ins.
  all: try now apply SUB.
  now rewrite SUB.(sub_lab).
Qed.

Lemma exec_add_event_nctrl_sub e
    (WF : Wf G')
    (NOTIN : ~acts_set G' e)
    (SUB : sub_execution G' G ∅₂ ∅₂) :
  sub_execution (exec_add_read_event_nctrl G' e)
                (exec_add_read_event_nctrl G  e)
                ∅₂ ∅₂.
Proof using.
  assert (INTER : acts_set G' ∩₁ (acts_set G ∪₁ eq e) ≡₁ acts_set G).
  { rewrite set_inter_union_r, set_inter_absorb_l; try apply SUB.
    rewrite <- set_union_empty_r with (s := acts_set G) at 2.
    apply set_union_more; ins. basic_solver. }
  constructor; ins.
  all: try now apply SUB.
  { apply set_union_mori; [apply SUB | ins]. }
  all: rewrite 1?(wf_rmwE WF), 1?(wf_dataE WF), 1?(wf_addrE WF),
               1?(wf_ctrlE WF), 1?(wf_rmw_depE WF), 1?(wf_rfE WF),
               1?(wf_coE WF).
  all: rewrite ?SUB.(sub_rmw), ?SUB.(sub_data), ?SUB.(sub_addr),
               ?SUB.(sub_ctrl), ?SUB.(sub_rf), ?SUB.(sub_co),
               ?SUB.(sub_frmw).
  all: try now rewrite <- !restr_relE, restr_restr, INTER.
  now rewrite seq_false_l, seq_false_r.
Qed.

Lemma exec_add_rf_sub delta_rf
    (SUB : sub_execution G' G ∅₂ ∅₂)
    (WF_DELTA_RF : delta_rf ≡ ⦗acts_set G⦘ ⨾ delta_rf ⨾ ⦗acts_set G⦘) :
  sub_execution (exec_add_rf G' delta_rf)
                (exec_add_rf G  delta_rf)
                ∅₂ ∅₂.
Proof using.
  constructor; ins.
  all: try now apply SUB.
  rewrite seq_union_l, seq_union_r.
  apply union_more; [apply SUB | ins].
Qed.

Lemma exec_mapped_sub f lab'
    (FINJ : inj_dom ⊤₁ f)
    (SUB : sub_execution G' G ∅₂ ∅₂) :
  sub_execution (exec_mapped G' f lab')
                (exec_mapped G f lab')
                ∅₂ ∅₂.
Proof using.
  constructor; ins.
  { apply set_collect_mori; [ins | apply SUB]. }
  { apply SUB. }
  all: rewrite <- collect_rel_eqv, <- ?collect_rel_seq.
  all: try now apply collect_rel_more, SUB.
  all: try now eapply inj_dom_mori with (x := ⊤₁); eauto; ins.
  now rewrite seq_false_l, seq_false_r.
Qed.

End ExecOpsSub.