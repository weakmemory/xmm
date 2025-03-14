From imm Require Import Events Execution SubExecution Execution_eco.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.

Require Import AuxDef AuxRel Lia.
Require Import Core Srf AddEventWf.
Require Import xmm_s_hb.

Require Import Program.Basics.

Open Scope program_scope.

Set Implicit Arguments.

Section DeltaOps.

Variable X X' : WCore.t.
Variable e : actid.
Variable l : label.

Notation "'G''" := (WCore.G X').
Notation "'G'" := (WCore.G X).

Notation "'E''" := (acts_set G').
Notation "'threads_set''" := (threads_set G').
Notation "'lab''" := (lab G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'vf''" := (vf G').
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

Lemma mapped_sb_delta m
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

Lemma mapped_rf_delta_R m w :
  m ↑ WCore.rf_delta_R e w ≡
    WCore.rf_delta_R (m e) (option_map m w).
Proof using.
  unfold WCore.rf_delta_R.
  rewrite collect_rel_cross, set_collect_eq_opt.
  apply cross_more; ins.
  unfold WCore.lab_is_r. basic_solver.
Qed.

Lemma mapped_rf_delta_W m R1 :
  m ↑ WCore.rf_delta_W e R1 ≡
    WCore.rf_delta_W (m e) (m ↑₁ R1).
Proof using.
  unfold WCore.rf_delta_W.
  rewrite collect_rel_cross.
  apply cross_more; ins.
  unfold WCore.lab_is_w. basic_solver.
Qed.

Lemma mapped_co_delta m W1 W2 :
  m ↑ WCore.co_delta e W1 W2 ≡
    WCore.co_delta (m e) (m ↑₁ W1) (m ↑₁ W2).
Proof using.
  unfold WCore.co_delta.
  rewrite collect_rel_union, !collect_rel_cross.
  apply union_more; apply cross_more; ins.
  all: unfold WCore.lab_is_w.
  all: basic_solver.
Qed.

Definition mapped_rmw_delta m r :
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

Lemma sb_deltaEE r R1 w W1 W2
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  ⦗E⦘ ⨾ ext_sb ⨾ ⦗eq e⦘ ≡ WCore.sb_delta e E.
Proof using.
  arewrite (⦗E⦘ ⨾ ext_sb ⨾ ⦗eq e⦘ ≡ sb' ⨾ ⦗eq e⦘)
    ; [|eapply sb_deltaE; eauto].
  unfold sb. rewrite !seqA, (WCore.add_event_acts ADD).
  arewrite (⦗E ∪₁ eq e⦘ ⨾ ⦗eq e⦘ ≡ ⦗eq e⦘).
  { enough (NIN : ~E e) by basic_solver.
    apply ADD. }
  rewrite id_union, !seq_union_l.
  arewrite_false (⦗eq e⦘ ⨾ ext_sb ⨾ ⦗eq e⦘).
  { unfolder. ins. desf. eapply ext_sb_irr; eauto. }
  now rewrite union_false_r.
Qed.

Lemma sb_deltaEN r R1 w W1 W2
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  ⦗eq e⦘ ⨾ ext_sb ⨾ ⦗E⦘ ≡ ∅₂.
Proof using.
  arewrite (⦗eq e⦘ ⨾ ext_sb ⨾ ⦗E⦘ ≡ ⦗eq e⦘ ⨾ sb' ⨾ ⦗E⦘).
  { unfold sb. rewrite (WCore.add_event_acts ADD).
    enough (NIN : ~E e) by basic_solver 11.
    apply ADD. }
  rewrite (WCore.add_event_sb ADD). unfold sb.
  enough (NIN : ~E e) by basic_solver 11.
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

Lemma co_deltaE r R1 w W1 W2
    (WF : Wf G)
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  ⦗eq e⦘ ⨾ co' ∪ co' ⨾ ⦗eq e⦘ ≡ WCore.co_delta e W1 W2.
Proof using.
  rewrite (co_deltaE1 WF ADD), (co_deltaE2 WF ADD).
  unfold WCore.co_delta. reflexivity.
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
  { clear. unfold same_loc; basic_solver. }
  assert (LOCSET : (fun x => same_loc x e) ⊆₁ (fun x => same_loc e x)).
  { clear. unfold same_loc; basic_solver. }
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

Lemma rf_uncmt' cmt thrdle
    (WF : Wf G')
    (STAB : WCore.stable_uncmt_reads_gen X' cmt thrdle) :
  rf' ⨾ ⦗E' \₁ cmt⦘ ⊆ tid ↓ thrdle ∪ (rf' ⨾ ⦗E' \₁ cmt⦘) ∩ same_tid.
Proof using.
  arewrite (
    rf' ⨾ ⦗E' \₁ cmt⦘ ⊆
      (rf' ⨾ ⦗E' \₁ cmt⦘) \ same_tid ∪
      (rf' ⨾ ⦗E' \₁ cmt⦘) ∩ same_tid
  ).
  { clear. unfolder. ins. desf. splits; tauto. }
  apply union_mori; auto with hahn.
  rewrite (rf_sub_vf WF).
  arewrite (vf' ⨾ ⦗E' \₁ cmt⦘ ⊆ vf' ⨾ same_tid ⨾ ⦗E' \₁ cmt⦘).
  { unfold same_tid. basic_solver 11. }
  rewrite (WCore.surg_ncmt STAB).
  basic_solver.
Qed.

Lemma rfi_in_sb
    (WF : Wf G')
    (CONS : WCore.is_cons G') :
  rf' ∩ same_tid ⊆ sb'.
Proof using.
  arewrite (
    rf' ⊆ rf' ∩ sb' ∪ rf' \ sb'
  ).
  { apply ri_union_re. }
  rewrite inter_union_l.
  apply inclusion_union_l; [basic_solver |].
  arewrite (rf' \ sb' ⊆ rf' \ ext_sb).
  { rewrite (wf_rfE WF) at 1. unfold sb.
    unfolder. ins. desf. split; tauto. }
  rewrite (no_rf_to_init WF).
  unfolder. intros x y.
  destruct PeanoNat.Nat.lt_total
      with (n := index x) (m := index y)
        as [LT | [EQ | GT]].
  { unfold sb, same_tid, ext_sb.
    unfolder. ins. exfalso. desf.
    ins. desf. eauto. }
  { unfold index in EQ.
    unfold sb, same_tid, ext_sb.
    unfolder. ins. exfalso. desf.
    ins. desf. eapply (rf_irr WF); eauto. }
  ins.
  assert (RFE : (⦗E'⦘ ⨾ rf' ⨾ ⦗E'⦘) x y).
  { apply WF. desf. }
  assert (SB : sb' y x).
  { unfolder in RFE. unfold sb.
    unfolder. splits; desf.
    unfold same_tid, ext_sb in *.
    desf. }
  exfalso.
  apply (WCore.cons_coherence CONS) with y.
  exists x. split; [now apply sb_in_hb |].
  apply r_step, rf_in_eco. desf.
Qed.

Lemma rf_uncmt cmt thrdle
    (WF : Wf G')
    (CONS : WCore.is_cons G')
    (STAB : WCore.stable_uncmt_reads_gen X' cmt thrdle) :
  rf' ⨾ ⦗E' \₁ cmt⦘ ⊆ tid ↓ thrdle ∪ sb'.
Proof using.
  rewrite rf_uncmt' with (thrdle := thrdle); auto.
  rewrite seq_eqv_inter_lr.
  rewrite rfi_in_sb; auto.
  basic_solver.
Qed.

Lemma rexec_dtrmt_sb_dom f dtrmt cmt thrdle
    (REXEC : WCore.reexec_gen X X' f dtrmt cmt thrdle) :
  dom_rel (sb ⨾ ⦗dtrmt⦘) ⊆₁ dtrmt.
Proof using.
  rewrite (WCore.reexec_dtrmt_sb_closed REXEC).
  clear. basic_solver.
Qed.

Lemma acts_steps X'' cmt
    (STEPS : (WCore.guided_step cmt X')＊ X'' X') :
  acts_set (WCore.G X'') ⊆₁ E'.
Proof using.
  apply clos_rt_rtn1 in STEPS.
  induction STEPS as [| X''' X'''' STEP STEPS IHSTEP]; auto.
  rewrite IHSTEP.
  red in STEP. destruct STEP as (e' & l' & STEP).
  set (STEP' := WCore.gsg_add_step STEP).
  red in STEP'. destruct STEP' as (r & R1 & w & W1 & W2 & STEP').
  rewrite (WCore.add_event_acts STEP').
  auto with hahn.
Qed.

Lemma rexec_dtrmt_in_start f dtrmt cmt thrdle
    (REXEC : WCore.reexec_gen X X' f dtrmt cmt thrdle) :
  dtrmt ⊆₁ E.
Proof using.
  arewrite (dtrmt ≡₁ id ↑₁ dtrmt) by basic_solver.
  rewrite set_collect_eq_dom
     with (g := f).
  { rewrite (WCore.dtrmt_cmt REXEC).
    apply (WCore.reexec_embd_acts (WCore.reexec_embd_corr REXEC)). }
  unfolder. unfold id. ins. symmetry.
  now apply (WCore.dtrmt_fixed REXEC).
Qed.

Lemma rexec_dtrmt_in_fin f dtrmt cmt thrdle
    (REXEC : WCore.reexec_gen X X' f dtrmt cmt thrdle) :
  dtrmt ⊆₁ E'.
Proof using.
  rewrite <- (acts_steps (WCore.reexec_steps REXEC)).
  ins. rewrite set_inter_absorb_r; auto with hahn.
  apply (rexec_dtrmt_in_start REXEC).
Qed.

Lemma rexec_dtrmt_sbimm_codom f dtrmt cmt thrdle
    (REXEC : WCore.reexec_gen X X' f dtrmt cmt thrdle) :
  codom_rel (⦗dtrmt⦘ ⨾ immediate (nin_sb G') ⨾ ⦗cmt⦘) ⊆₁ dtrmt.
Proof using.
  rewrite (WCore.dtrmt_sb_max REXEC).
  clear. basic_solver.
Qed.

Record xmm_graph_proper G0 : Prop := {
    xgp_wf : Wf G0;
    xgp_init : is_init ⊆₁ acts_set G0;
    xgp_rmw_dep : @rmw_dep G0 ≡ ∅₂;
    xgp_data : @data G0 ≡ ∅₂;
    xgp_ctrl : @ctrl G0 ≡ ∅₂;
    xgp_addr : @addr G0 ≡ ∅₂;
    xgp_fin : set_finite (acts_set G0 \₁ is_init);
    xgp_init_tid : acts_set G0 ∩₁ (fun e => tid e = tid_init) ⊆₁ is_init;
}.

Definition xmm_graph_correct G0 : Prop :=
  rf_complete G0 /\ xmm_graph_proper G0.

Lemma xmm_add_event_gen_proper r R1 w W1 W2 e' l'
    (STEP : WCore.add_event_gen X X' e' l' r R1 w W1 W2)
    (PROP : xmm_graph_proper G) :
  xmm_graph_proper G'.
Proof using.
  constructor.
  { eapply add_event_wf; eauto using xgp_wf. }
  { rewrite (WCore.add_event_acts STEP), (xgp_init PROP).
    auto with hahn. }
  { rewrite (WCore.add_event_rmw_dep STEP).
    apply PROP. }
  { rewrite (WCore.add_event_data STEP).
    apply PROP. }
  { rewrite (WCore.add_event_ctrl STEP).
    apply PROP. }
  { rewrite (WCore.add_event_addr STEP).
    apply PROP. }
  { rewrite (WCore.add_event_acts STEP),
            set_minus_union_l.
    apply set_finite_union. split; [apply PROP|].
    eapply set_finite_mori; eauto with hahn.
    red. basic_solver. }
  rewrite (WCore.add_event_acts STEP), set_inter_union_l.
  rewrite (xgp_init_tid PROP).
  apply set_subset_union_l. split; [reflexivity |].
  unfolder. ins. desf. exfalso.
  now apply (WCore.add_event_tid_e STEP).
Qed.

Lemma xmm_add_event_proper e' l'
    (STEP : WCore.add_event X X' e' l')
    (PROP : xmm_graph_proper G) :
  xmm_graph_proper G'.
Proof using.
  red in STEP. desf.
  eauto using xmm_add_event_gen_proper.
Qed.

Lemma xmm_guided_step_gen_proper XC cmt e' l'
    (STEP : WCore.guided_step_gen cmt XC X X' e' l')
    (PROP : xmm_graph_proper G) :
  xmm_graph_proper G'.
Proof using.
  eapply xmm_add_event_proper; eauto using WCore.gsg_add_step.
Qed.

Lemma xmm_guided_step_proper XC cmt
    (STEP : WCore.guided_step cmt XC X X')
    (PROP : xmm_graph_proper G) :
  xmm_graph_proper G'.
Proof using.
  red in STEP. desf.
  apply (xmm_guided_step_gen_proper STEP); auto.
Qed.

Lemma sb_closure_preserve s e' l'
    (SIN : s ⊆₁ E)
    (STEP : WCore.add_event X X' e' l')
    (CLOS : sb ⨾ ⦗s⦘ ⊆ ⦗s⦘ ⨾ sb ⨾ ⦗s⦘) :
  sb' ⨾ ⦗s⦘ ⊆ ⦗s⦘ ⨾ sb' ⨾ ⦗s⦘.
Proof using.
  red in STEP. desf.
  rewrite (WCore.add_event_sb STEP).
  rewrite !seq_union_l, seq_union_r.
  apply union_mori; auto.
  unfold WCore.sb_delta.
  rewrite <- cross_inter_r.
  enough (~s e') by basic_solver.
  intro EIN.
  now apply (WCore.add_event_new STEP), SIN.
Qed.

Lemma sb_closure_preserve_guided s XC cmt
    (SIN : s ⊆₁ E)
    (STEP : WCore.guided_step cmt XC X X')
    (CLOS : sb ⨾ ⦗s⦘ ⊆ ⦗s⦘ ⨾ sb ⨾ ⦗s⦘) :
  sb' ⨾ ⦗s⦘ ⊆ ⦗s⦘ ⨾ sb' ⨾ ⦗s⦘.
Proof using.
  red in STEP. destruct STEP as (e' & l' & STEP).
  assert (STEP' : WCore.add_event X X' e' l').
  { apply STEP. }
  eapply sb_closure_preserve; eauto.
Qed.

End DeltaOps.

Section OtherStepInvariants.

Variable X X' : WCore.t.
Variable e : actid.
Variable l : label.

Notation "'G''" := (WCore.G X').
Notation "'G'" := (WCore.G X).

Notation "'E''" := (acts_set G').
Notation "'threads_set''" := (threads_set G').
Notation "'lab''" := (lab G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'vf''" := (vf G').
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

Lemma guided_steps_acts XC cmt X1 X2
    (STEP : (WCore.guided_step cmt XC)＊ X1 X2) :
  acts_set (WCore.G X1) ⊆₁ acts_set (WCore.G X2).
Proof using.
  apply clos_rt_rtn1 in STEP.
  induction STEP as [ | X2 X3 STEP1 STEP2 IH].
  { auto. }
  transitivity (acts_set (WCore.G X2)); auto.
  red in STEP1. destruct STEP1 as (e' & l' & STEP1).
  assert (STEP1' : WCore.add_event X2 X3 e' l').
  { apply STEP1. }
  red in STEP1'. desf.
  rewrite (WCore.add_event_acts STEP1').
  basic_solver.
Qed.

Lemma sb_closure_preserve_guided_trans s XC cmt X1 X2
    (SIN : s ⊆₁ acts_set (WCore.G X1))
    (STEP : (WCore.guided_step cmt XC)＊ X1 X2)
    (CLOS : @sb (WCore.G X1) ⨾ ⦗s⦘ ⊆ ⦗s⦘ ⨾ @sb (WCore.G X1) ⨾ ⦗s⦘) :
  @sb (WCore.G X2) ⨾ ⦗s⦘ ⊆ ⦗s⦘ ⨾ @sb (WCore.G X2) ⨾ ⦗s⦘.
Proof using.
  apply clos_rt_rtn1 in STEP.
  induction STEP as [ | X2 X3 STEP1 STEP2 IH].
  { auto. }
  eapply sb_closure_preserve_guided with (X := X2); eauto.
  transitivity (acts_set (WCore.G X1)); auto.
  eapply guided_steps_acts
    with (cmt := cmt) (XC := XC).
  now apply clos_rt_rtn1_iff in STEP2.
Qed.

Lemma xmm_exec_correct e' l'
    (STEP : WCore.exec_inst X X' e' l')
    (PROP : xmm_graph_correct G) :
  xmm_graph_correct G'.
Proof using.
  destruct PROP as [RFC PROP].
  red. split; [apply STEP |].
  eapply xmm_add_event_proper.
  all: eauto using xmm_add_event_proper.
  all: apply STEP.
Qed.

Lemma xmm_guided_step_proper_trans XC cmt X1 X2
    (STEP : (WCore.guided_step cmt XC)＊ X1 X2)
    (PROP : xmm_graph_proper (WCore.G X1)) :
  xmm_graph_proper (WCore.G X2).
Proof using.
  apply clos_rt_rtn1 in STEP.
  induction STEP as [ | X2 X3 STEP1 STEP2 IH].
  { auto. }
  eapply xmm_guided_step_proper; eauto.
Qed.

Lemma xmm_rexec_gen_correct f dtrmt cmt thrdle
    (STEP : WCore.reexec_gen X X' f dtrmt cmt thrdle)
    (PROP : xmm_graph_correct G) :
  xmm_graph_correct G'.
Proof using.
  red. split; [apply STEP |].
  eapply xmm_guided_step_proper_trans.
  { apply STEP. }
  red in PROP. destruct PROP as (RFC & PROP).
  constructor; ins.
  { apply sub_WF with (G := G) (sc := ∅₂) (sc' := ∅₂).
    { ins. rewrite (WCore.dtrmt_init STEP).
      reflexivity. }
    { apply PROP. }
    apply restrict_sub; [basic_solver |].
    apply (rexec_dtrmt_in_start STEP). }
  { rewrite (WCore.dtrmt_init STEP).
    rewrite <- (rexec_dtrmt_in_start STEP).
    basic_solver. }
  { rewrite (xgp_rmw_dep PROP).
    now rewrite seq_false_l, seq_false_r. }
  { rewrite (xgp_data PROP).
    now rewrite seq_false_l, seq_false_r. }
  { rewrite (xgp_ctrl PROP).
    now rewrite seq_false_l, seq_false_r. }
  { rewrite (xgp_addr PROP).
    now rewrite seq_false_l, seq_false_r. }
  { eapply set_finite_mori; [| apply PROP].
    red. basic_solver. }
  rewrite <- (xgp_init_tid PROP). basic_solver.
Qed.

Lemma xmm_step_correct
    (STEP : xmm_step X X')
    (PROP : xmm_graph_correct G) :
  xmm_graph_correct G'.
Proof using.
  destruct STEP.
  { eapply xmm_exec_correct; eauto. }
  red in STEP. desf.
  eapply xmm_rexec_gen_correct; eauto.
Qed.

End OtherStepInvariants.

Lemma xmm_step_correct_ind X1 X2
    (STEPS : xmm_step⁺ X1 X2)
    (PROP : xmm_graph_correct (WCore.G X1)) :
  xmm_graph_correct (WCore.G X2).
Proof using.
  apply clos_trans_tn1 in STEPS.
  induction STEPS as [X_t STEP | X_t X_t' STEP STEPS SRC].
  { eapply xmm_step_correct; eauto. }
  eapply xmm_step_correct; eauto.
Qed.