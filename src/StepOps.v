From imm Require Import Events Execution SubExecution.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.

Require Import AuxDef AuxRel.
Require Import Core.

Require Import Program.Basics.

Open Scope program_scope.

Set Implicit Arguments.

Section DeltaOps.

Variable X X' : WCore.t.
Variable e : actid.
Variable l : label.
Variable m : actid -> actid.

Notation "'G''" := (WCore.G X').
Notation "'G'" := (WCore.G X).

Notation "'E''" := (acts_set G').
Notation "'threads_set''" := (threads_set G').
Notation "'lab''" := (lab G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'rmw_dep''" := (rmw_dep G').
Notation "'W''" := (is_w lab').
Notation "'R''" := (is_r lab').
Notation "'same_loc''" := (same_loc lab').
Notation "'same_val''" := (same_val lab').

Notation "'E'" := (acts_set G).
Notation "'threads_set'" := (threads_set G).
Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'same_val'" := (same_val lab).
Notation "'Loc_' l" := (fun e => loc e = l) (at level 1).
Notation "'Val_' v" := (fun e => val e = v) (at level 1).

Lemma mapped_sb_delta
    (INIT : fixset is_init m)
    (TID : m ↑₁ (E ∩₁ same_tid e) ≡₁ m ↑₁ E ∩₁ same_tid (m e)) :
  m ↑ WCore.sb_delta e E ≡
    (is_init ∪₁ m ↑₁ E ∩₁ same_tid (m e)) × eq (m e).
Proof using.
  unfold WCore.sb_delta.
  rewrite !collect_rel_cross, set_collect_union,
          set_collect_eq, TID, <- (fixset_set_fixpoint INIT).
  ins.
Qed.

Lemma mapped_rf_delta_R w :
  m ↑ WCore.rf_delta_R e w ≡
    WCore.rf_delta_R (m e) (option_map m w).
Proof using.
  unfold WCore.rf_delta_R.
  rewrite collect_rel_cross, set_collect_eq_opt.
  apply cross_more; ins.
  unfold WCore.lab_is_r. basic_solver.
Qed.

Lemma mapped_rf_delta_W R1 :
  m ↑ WCore.rf_delta_W e R1 ≡
    WCore.rf_delta_W (m e) (m ↑₁ R1).
Proof using.
  unfold WCore.rf_delta_W.
  rewrite collect_rel_cross.
  apply cross_more; ins.
  unfold WCore.lab_is_w. basic_solver.
Qed.

Lemma mapped_co_delta W1 W2 :
  m ↑ WCore.co_delta e W1 W2 ≡
    WCore.co_delta (m e) (m ↑₁ W1) (m ↑₁ W2).
Proof using.
  unfold WCore.co_delta.
  rewrite collect_rel_union, !collect_rel_cross.
  apply union_more; apply cross_more; ins.
  all: unfold WCore.lab_is_w.
  all: basic_solver.
Qed.

Definition mapped_rmw_delta r :
  m ↑ WCore.rmw_delta e r ≡
    WCore.rmw_delta (m e) (option_map m r).
Proof using.
  unfold WCore.rmw_delta.
  rewrite collect_rel_cross, set_collect_eq_opt.
  apply cross_more; ins.
  unfold WCore.lab_is_w. basic_solver.
Qed.

Lemma sb_deltaE r R1 w W1 W2
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  sb' ⨾ ⦗eq e⦘ ≡ WCore.sb_delta e E.
Proof using.
  rewrite (WCore.add_event_sb ADD), seq_union_l.
  arewrite (sb ⨾ ⦗eq e⦘ ≡ ∅₂); [| basic_solver 11].
  unfold sb. enough (~E e) by basic_solver.
  apply ADD.
Qed.

Lemma rf_delta_RE r R1 w W1 W2
    (WF : Wf G)
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  rf' ⨾ ⦗eq e⦘ ≡ WCore.rf_delta_R e w.
Proof using.
  assert (NOTIN : ~E e) by apply ADD.
  rewrite (WCore.add_event_rf ADD), !seq_union_l.
  arewrite (rf ⨾ ⦗eq e⦘ ≡ ∅₂).
  { rewrite (wf_rfE WF). basic_solver. }
  arewrite (WCore.rf_delta_W e R1 ⨾ ⦗eq e⦘ ≡ ∅₂); [| basic_solver 11].
  unfold WCore.rf_delta_W. rewrite <- cross_inter_r.
  enough (~ R1 e) by basic_solver.
  intro FALSO.
  now apply (WCore.add_event_R1E ADD) in FALSO.
Qed.

Lemma rf_delta_WE r R1 w W1 W2
    (WF : Wf G)
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  ⦗eq e⦘ ⨾ rf' ≡ WCore.rf_delta_W e R1.
Proof using.
  assert (NOTIN : ~E e) by apply ADD.
  rewrite (WCore.add_event_rf ADD), !seq_union_r.
  arewrite (⦗eq e⦘ ⨾ rf ≡ ∅₂).
  { rewrite (wf_rfE WF). basic_solver. }
  arewrite (⦗eq e⦘ ⨾ WCore.rf_delta_R e w ≡ ∅₂); [| basic_solver 11].
  unfold WCore.rf_delta_R. rewrite <- cross_inter_l.
  enough (~ eq_opt w e) by basic_solver.
  intro FALSO.
  now apply (WCore.add_event_wE ADD) in FALSO.
Qed.

Lemma co_deltaE1 r R1 w W1 W2
    (WF : Wf G)
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  ⦗eq e⦘ ⨾ co' ≡ eq e × W1.
Proof using.
  assert (NOTIN : ~E e) by apply ADD.
  rewrite (WCore.add_event_co ADD), !seq_union_r.
  arewrite (⦗eq e⦘ ⨾ co ≡ ∅₂).
  { rewrite (wf_coE WF). basic_solver. }
  unfold WCore.co_delta. rewrite seq_union_r.
  arewrite (⦗eq e⦘ ⨾ W2 × eq e ≡ ∅₂); [| clear; basic_solver 11].
  enough (~ W2 e) by basic_solver.
  intro FALSO.
  now apply (WCore.add_event_W2E ADD) in FALSO.
Qed.

Lemma co_deltaE2 r R1 w W1 W2
    (WF : Wf G)
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  co' ⨾ ⦗eq e⦘ ≡ W2 × eq e.
Proof using.
  assert (NOTIN : ~E e) by apply ADD.
  rewrite (WCore.add_event_co ADD), !seq_union_l.
  arewrite (co ⨾ ⦗eq e⦘ ≡ ∅₂).
  { rewrite (wf_coE WF). basic_solver. }
  unfold WCore.co_delta. rewrite seq_union_l.
  arewrite (eq e × W1 ⨾ ⦗eq e⦘  ≡ ∅₂); [| clear; basic_solver 7].
  enough (~ W1 e) by basic_solver.
  intro FALSO.
  now apply (WCore.add_event_W1E ADD) in FALSO.
Qed.

Definition rmw_deltaE r R1 w W1 W2
    (WF : Wf G)
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  rmw' ⨾ ⦗eq e⦘ ≡ WCore.rmw_delta e r.
Proof using.
  assert (NOTIN : ~E e) by apply ADD.
  rewrite (WCore.add_event_rmw ADD), !seq_union_l.
  arewrite (rmw ⨾ ⦗eq e⦘ ≡ ∅₂).
  { rewrite (wf_rmwE WF). basic_solver. }
  clear; basic_solver.
Qed.

Lemma add_event_to_rf_complete r R1 w W1 W2
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2)
    (WF : Wf G)
    (RFC : rf_complete G) :
  WCore.rf_delta_W e R1 ≡ ∅₂.
Proof using.
  split; [| basic_solver]. unfold WCore.rf_delta_W.
  unfolder. intros e' r' (EQ & RF1). subst e'.
  destruct RFC with r' as (w' & RF2).
  { split.
    { now apply (WCore.add_event_R1E ADD). }
    now apply (WCore.add_event_R1D ADD). }
  assert (INE : E w').
  { apply (wf_rfE WF) in RF2. unfolder in RF2.
    desf. }
  assert (FALSEQ : e = w').
  { apply (WCore.add_event_rff ADD) with r'; unfold transp.
    all: hahn_rewrite (WCore.add_event_rf ADD).
    all: basic_solver. }
  apply (WCore.add_event_new ADD). congruence.
Qed.

Lemma lab_is_wE' ll :
  eq e ∩₁ is_w ll ≡₁ eq e ∩₁ WCore.lab_is_w (ll e).
Proof using.
  unfolder. split; intros x (XEQ & XIN); subst x.
  all: split; ins.
  all: unfold is_w, WCore.lab_is_w in *; desf.
Qed.

Lemma lab_loc' ll lc :
  eq e ∩₁ (fun e => @loc _ ll e = lc) ≡₁
    eq e ∩₁ (fun _ => WCore.lab_loc (ll e) = lc).
Proof using.
  unfolder. split; intros x (XEQ & XIN); subst x.
  all: split; ins.
Qed.

Lemma lab_is_wE r R1 w W1 W2
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  eq e ∩₁ W' ≡₁ eq e ∩₁ WCore.lab_is_w l.
Proof using.
  unfold is_w, WCore.lab_is_w.
  rewrite (WCore.add_event_lab ADD).
  unfolder. split.
  all: ins; desf; rewrite upds in *.
  all: congruence.
Qed.

Lemma lab_is_rE r R1 w W1 W2
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  eq e ∩₁ R' ≡₁ eq e ∩₁ WCore.lab_is_r l.
Proof using.
  unfold is_r, WCore.lab_is_r.
  rewrite (WCore.add_event_lab ADD).
  unfolder. split.
  all: ins; desf; rewrite upds in *.
  all: congruence.
Qed.

Lemma co_delta_union_W1 W1 W1' W2 :
  WCore.co_delta e (W1' ∪₁ W1) W2 ≡
    WCore.co_delta e W1 W2 ∪
    eq e × W1'.
Proof using.
  basic_solver 11.
Qed.

Lemma add_event_to_wf r R1 w W1 W2
    (ININ : is_init ⊆₁ E)
    (NEW : ~E e)
    (NINIT : ~is_init e)
    (NTID : tid e <> tid_init)
    (ACTS : E' ≡₁ E ∪₁ eq e)
    (THREADS : threads_set' ≡₁ threads_set)
    (LAB : lab' = upd lab e l)
    (RF : rf' ≡ rf ∪ WCore.rf_delta_R e w ∪ WCore.rf_delta_W e R1)
    (CO : co' ≡ co ∪ WCore.co_delta e W1 W2)
    (RMW : rmw' ≡ rmw ∪ WCore.rmw_delta e r)
    (DATA : data' ≡ data)
    (ADDR : addr' ≡ addr)
    (CTRL : ctrl' ≡ ctrl)
    (RMWDEP : rmw_dep' ≡ rmw_dep)
    (SB : sb' ≡ sb ∪ WCore.sb_delta e E)
    (NCTRL : ctrl' ⊆ ∅₂)
    (WF : Wf G') :
  WCore.add_event_gen X X' e l r R1 w W1 W2.
Proof using.
  assert (WNE : ~ eq_opt w e).
  { destruct w as [w|]; ins.
    intro FALSO; desf.
    apply (rf_irr WF) with e, RF.
    clear. basic_solver. }
  assert (RNE : ~ eq_opt r e).
  { destruct r as [r|]; ins.
    intro FALSO; desf.
    apply (rmw_irr WF) with e, RMW.
    clear. basic_solver. }
  assert (W1NE : ~W1 e).
  { intros FALSO.
    apply (co_irr WF) with e, CO.
    clear - FALSO. basic_solver. }
  assert (W2NE : ~W2 e).
  { intros FALSO.
    apply (co_irr WF) with e, CO.
    clear - FALSO. basic_solver. }
  assert (R1NE : ~R1 e).
  { intros FALSO.
    apply (rf_irr WF) with e, RF.
    clear - FALSO. basic_solver. }
  (**)
  assert (RF1' : eq_opt w ⊆₁ dom_rel (rf' ⨾ ⦗eq e⦘)).
  { rewrite RF. clear. basic_solver 7. }
  assert (RF2' : R1 ⊆₁ codom_rel (⦗eq e⦘ ⨾ rf')).
  { rewrite RF. clear. basic_solver 7. }
  assert (RMW' : eq_opt r ⊆₁ dom_rel (rmw' ⨾ ⦗eq e⦘)).
  { rewrite RMW. clear. basic_solver 7. }
  assert (CO1' : W1 ⊆₁ codom_rel (⦗eq e⦘ ⨾ co')).
  { rewrite CO. clear. basic_solver 7. }
  assert (CO2' : W2 ⊆₁ dom_rel (co' ⨾ ⦗eq e⦘)).
  { rewrite CO. clear. basic_solver 7. }
  (**)
  assert (WE' : eq_opt w ⊆₁ E').
  { rewrite RF1', (wf_rfE WF). clear. basic_solver. }
  assert (R1E' : R1 ⊆₁ E').
  { rewrite RF2', (wf_rfE WF). clear. basic_solver. }
  assert (RE' : eq_opt r ⊆₁ E').
  { rewrite RMW', (wf_rmwE WF). clear. basic_solver. }
  assert (W1E' : W1 ⊆₁ E').
  { rewrite CO1', (wf_coE WF). clear. basic_solver. }
  assert (W2E' : W2 ⊆₁ E').
  { rewrite CO2', (wf_coE WF). clear. basic_solver. }
  (**)
  assert (WE : eq_opt w ⊆₁ E).
  { rewrite ACTS in WE'.
    clear - WNE WE'. unfolder in *.
    intros x XEQ. desf.
    destruct WE' with x; congruence. }
  assert (R1E : R1 ⊆₁ E).
  { rewrite ACTS in R1E'.
    clear - R1NE R1E'. unfolder in *.
    intros x XEQ.
    destruct R1E' with x; congruence. }
  assert (RE : eq_opt r ⊆₁ E).
  { rewrite ACTS in RE'.
    clear - RNE RE'. unfolder in *.
    intros x XEQ. desf.
    destruct RE' with x; congruence. }
  assert (W1E : W1 ⊆₁ E).
  { rewrite ACTS in W1E'.
    clear - W1NE W1E'. unfolder in *.
    intros x XEQ.
    destruct W1E' with x; congruence. }
  assert (W2E : W2 ⊆₁ E).
  { rewrite ACTS in W2E'.
    clear - W2NE W2E'. unfolder in *.
    intros x XEQ.
    destruct W2E' with x; congruence. }
  clear WE' R1E' RE' W1E' W2E'.
  (**)
  assert (SUBW : E ∩₁ W' ⊆₁ W).
  { clear - LAB NEW. unfolder.
    ins. desf. unfold is_w in *.
    rewrite LAB, updo in *; congruence. }
  assert (SUBR : E ∩₁ R' ⊆₁ R).
  { clear - LAB NEW. unfolder.
    ins. desf. unfold is_r in *.
    rewrite LAB, updo in *; congruence. }
  assert (LOCSET' : (fun x => same_loc' x e) ⊆₁ (fun x => same_loc' e x)).
  { clear. unfolder. ins. now apply same_loc_sym. }
  assert (LOCSET : (fun x => same_loc x e) ⊆₁ (fun x => same_loc e x)).
  { clear. unfolder. ins. now apply same_loc_sym. }
  assert (SUBLOC : E ∩₁ (fun x => same_loc' e x) ⊆₁ Loc_ (WCore.lab_loc l)).
  { clear - NEW LAB. unfolder. unfold same_loc, loc, WCore.lab_loc.
    rewrite LAB. intros x (XINE & LOC).
    rewrite upds, updo in LOC; congruence. }
  assert (SUBVAL : E ∩₁ (fun x => same_val' e x) ⊆₁ Val_ (WCore.lab_val l)).
  { clear - NEW LAB. unfolder. unfold same_val, val, WCore.lab_val.
    rewrite LAB. intros x (XINE & VAL).
    rewrite upds, updo in VAL; congruence. }
  assert (VALSET' : (fun x => same_val' x e) ⊆₁ (fun x => same_val' e x)).
  { clear. unfolder. ins. unfold same_val in *. congruence. }
  (**)
  constructor; ins.
  { transitivity (E ∩₁ W'); [| apply SUBW].
    apply set_subset_inter_r. split; [apply WE |].
    rewrite RF1', (wf_rfD WF). clear. basic_solver. }
  { transitivity (E ∩₁ (fun x => same_loc' e x)); [| apply SUBLOC].
    apply set_subset_inter_r. split; [apply WE |].
    rewrite RF1', (wf_rfl WF), <- LOCSET'.
    clear. basic_solver. }
  { transitivity (E ∩₁ (fun x => same_val' e x)); [| apply SUBVAL].
    apply set_subset_inter_r. split; [apply WE |].
    rewrite RF1', <- VALSET'. clear - WF. unfolder.
    ins. desf. now apply (wf_rfv WF). }
  { transitivity (E ∩₁ R'); [| apply SUBR].
    apply set_subset_inter_r. split; [apply RE |].
    rewrite RMW', (wf_rmwD WF). clear. basic_solver. }
  { transitivity (E ∩₁ (fun x => same_loc' e x)); [| apply SUBLOC].
    apply set_subset_inter_r. split; [apply RE |].
    rewrite RMW', (wf_rmwl WF), <- LOCSET'.
    clear. basic_solver. }
  { transitivity rmw'; [| apply WF].
    rewrite RMW. clear. basic_solver. }
  { transitivity (E ∩₁ W'); [| apply SUBW].
    apply set_subset_inter_r. split; [apply W1E |].
    rewrite CO1', (wf_coD WF). clear. basic_solver. }
  { transitivity (E ∩₁ (fun x => same_loc' e x)); [| apply SUBLOC].
    apply set_subset_inter_r. split; [apply W1E |].
    rewrite CO1', (wf_col WF), <- LOCSET'.
    clear. basic_solver. }
  { transitivity (E ∩₁ W'); [| apply SUBW].
    apply set_subset_inter_r. split; [apply W2E |].
    rewrite CO2', (wf_coD WF). clear. basic_solver. }
  { transitivity (E ∩₁ (fun x => same_loc' e x)); [| apply SUBLOC].
    apply set_subset_inter_r. split; [apply W2E |].
    rewrite CO2', (wf_col WF), <- LOCSET'.
    clear. basic_solver. }
  { transitivity (E ∩₁ R'); [| apply SUBR].
    apply set_subset_inter_r. split; [apply R1E |].
    rewrite RF2', (wf_rfD WF). clear. basic_solver. }
  { transitivity (E ∩₁ (fun x => same_loc' e x)); [| apply SUBLOC].
    apply set_subset_inter_r. split; [apply R1E |].
    rewrite RF2', (wf_rfl WF), <- LOCSET'.
    clear. basic_solver. }
  { transitivity (E ∩₁ (fun x => same_val' e x)); [| apply SUBVAL].
    apply set_subset_inter_r. split; [apply R1E |].
    rewrite RF2', <- VALSET'. clear - WF. unfolder.
    ins. desf. symmetry. now apply (wf_rfv WF). }
  all: try now apply WF.
  { apply THREADS, WF, ACTS. now right. }
  { enough (EMP : eq_opt w ≡₁ ∅).
    { clear - EMP. unfolder in *. desf.
      exfalso. eauto. }
    split; [| basic_solver]. rewrite RF1', (wf_rfD WF).
    clear - NR. basic_solver. }
  { split; [| basic_solver]. rewrite RF2', (wf_rfD WF).
    clear - NW. basic_solver. }
  { enough (EMP : eq_opt r ≡₁ ∅).
    { clear - EMP. unfolder in *. desf.
      exfalso. eauto. }
    split; [| basic_solver]. rewrite RMW', (wf_rmwD WF).
    clear - NW. basic_solver. }
  { split; [| basic_solver]. rewrite CO1', (wf_coD WF).
    clear - NW. basic_solver. }
  split; [| basic_solver]. rewrite CO2', (wf_coD WF).
  clear - NW. basic_solver.
Qed.

Lemma dom_sb_delta s :
  dom_rel (WCore.sb_delta e s) ≡₁
    is_init ∪₁ s ∩₁ same_tid e.
Proof using.
  basic_solver 11.
Qed.

Lemma sb_delta_union s1 s2 :
  WCore.sb_delta e (s1 ∪₁ s2) ≡
    WCore.sb_delta e s1 ∪ WCore.sb_delta e s2.
Proof using.
  basic_solver 11.
Qed.

End DeltaOps.