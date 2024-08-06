From imm Require Import Events Execution imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From PromisingLib Require Import Basic.

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
Notation "'Loc_' l" := (fun e => loc e = l) (at level 1).
Notation "'Val_' v" := (fun e => val e = v) (at level 1).

Lemma mapped_sb_delta
    (SAME_INIT : m ↑₁ (E ∩₁ is_init) ≡₁ E ∩₁ is_init)
    (SAME_EVENTS : m ↑₁ (E ∩₁ same_tid e) ≡₁ E ∩₁ same_tid (m e)) :
  m ↑ WCore.sb_delta X e ≡
    (E ∩₁ (is_init ∪₁ same_tid (m e))) × eq (m e).
Proof using.
  unfold WCore.sb_delta.
  rewrite !set_inter_union_r, collect_rel_cross,
          set_collect_union, set_collect_eq,
          SAME_INIT, SAME_EVENTS.
  ins.
Qed.

Lemma mapped_rf_delta_R w :
  m ↑ WCore.rf_delta_R e l w ≡
    WCore.rf_delta_R (m e) l (option_map m w).
Proof using.
  unfold WCore.rf_delta_R.
  rewrite collect_rel_cross, set_collect_eq_opt.
  apply cross_more; ins.
  unfold WCore.lab_is_r. basic_solver.
Qed.

Lemma mapped_rf_delta_W R1 :
  m ↑ WCore.rf_delta_W e l R1 ≡
    WCore.rf_delta_W (m e) l (m ↑₁ R1).
Proof using.
  unfold WCore.rf_delta_W.
  rewrite collect_rel_cross.
  apply cross_more; ins.
  unfold WCore.lab_is_w. basic_solver.
Qed.

Lemma mapped_co_delta W1 W2 :
  m ↑ WCore.co_delta e l W1 W2 ≡
    WCore.co_delta (m e) l (m ↑₁ W1) (m ↑₁ W2).
Proof using.
  unfold WCore.co_delta.
  rewrite collect_rel_union, !collect_rel_cross.
  apply union_more; apply cross_more; ins.
  all: unfold WCore.lab_is_w.
  all: basic_solver.
Qed.

Definition mapped_rmw_delta r :
  m ↑ WCore.rmw_delta e l r ≡
    WCore.rmw_delta (m e) l (option_map m r).
Proof using.
  unfold WCore.rmw_delta.
  rewrite collect_rel_cross, set_collect_eq_opt.
  apply cross_more; ins.
  unfold WCore.lab_is_w. basic_solver.
Qed.

Lemma sb_deltaE r R1 w W1 W2
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  sb' ⨾ ⦗eq e⦘ ≡ WCore.sb_delta X e.
Proof using.
  rewrite (WCore.add_event_sb ADD), seq_union_l.
  arewrite (sb ⨾ ⦗eq e⦘ ≡ ∅₂); [| basic_solver 11].
  unfold sb. enough (~E e) by basic_solver.
  apply ADD.
Qed.

Lemma rf_delta_RE r R1 w W1 W2
    (WF : Wf G)
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  rf' ⨾ ⦗eq e⦘ ≡ WCore.rf_delta_R e l w.
Proof using.
  assert (NOTIN : ~E e) by apply ADD.
  rewrite (WCore.add_event_rf ADD), !seq_union_l.
  arewrite (rf ⨾ ⦗eq e⦘ ≡ ∅₂).
  { rewrite (wf_rfE WF). basic_solver. }
  arewrite (WCore.rf_delta_W e l R1 ⨾ ⦗eq e⦘ ≡ ∅₂); [| basic_solver 11].
  unfold WCore.rf_delta_W. rewrite <- cross_inter_r.
  enough (~ R1 e) by basic_solver.
  intro FALSO.
  now apply (WCore.add_event_R1E ADD) in FALSO.
Qed.

Lemma rf_delta_WE r R1 w W1 W2
    (WF : Wf G)
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  ⦗eq e⦘ ⨾ rf' ≡ WCore.rf_delta_W e l R1.
Proof using.
  assert (NOTIN : ~E e) by apply ADD.
  rewrite (WCore.add_event_rf ADD), !seq_union_r.
  arewrite (⦗eq e⦘ ⨾ rf ≡ ∅₂).
  { rewrite (wf_rfE WF). basic_solver. }
  arewrite (⦗eq e⦘ ⨾ WCore.rf_delta_R e l w ≡ ∅₂); [| basic_solver 11].
  unfold WCore.rf_delta_R. rewrite <- cross_inter_l.
  enough (~ eq_opt w e) by basic_solver.
  intro FALSO.
  now apply (WCore.add_event_wE ADD) in FALSO.
Qed.

Lemma co_deltaE1 r R1 w W1 W2
    (WF : Wf G)
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  ⦗eq e⦘ ⨾ co' ≡ (eq e ∩₁ WCore.lab_is_w l) × W1.
Proof using.
  assert (NOTIN : ~E e) by apply ADD.
  rewrite (WCore.add_event_co ADD), !seq_union_r.
  arewrite (⦗eq e⦘ ⨾ co ≡ ∅₂).
  { rewrite (wf_coE WF). basic_solver. }
  unfold WCore.co_delta. rewrite seq_union_r.
  arewrite (⦗eq e⦘ ⨾ W2 × (eq e ∩₁ WCore.lab_is_w l) ≡ ∅₂); [| basic_solver 11].
  enough (~ W2 e) by basic_solver.
  intro FALSO.
  now apply (WCore.add_event_W2E ADD) in FALSO.
Qed.

Lemma co_deltaE2 r R1 w W1 W2
    (WF : Wf G)
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  co' ⨾ ⦗eq e⦘ ≡ W2 × (eq e ∩₁ WCore.lab_is_w l).
Proof using.
  assert (NOTIN : ~E e) by apply ADD.
  rewrite (WCore.add_event_co ADD), !seq_union_l.
  arewrite (co ⨾ ⦗eq e⦘ ≡ ∅₂).
  { rewrite (wf_coE WF). basic_solver. }
  unfold WCore.co_delta. rewrite seq_union_l.
  arewrite ((eq e ∩₁ WCore.lab_is_w l) × W1 ⨾ ⦗eq e⦘  ≡ ∅₂); [| basic_solver 11].
  enough (~ W1 e) by basic_solver.
  intro FALSO.
  now apply (WCore.add_event_W1E ADD) in FALSO.
Qed.

Definition rmw_deltaE r R1 w W1 W2
    (WF : Wf G)
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2) :
  rmw' ⨾ ⦗eq e⦘ ≡ WCore.rmw_delta e l r.
Proof using.
  assert (NOTIN : ~E e) by apply ADD.
  rewrite (WCore.add_event_rmw ADD), !seq_union_l.
  arewrite (rmw ⨾ ⦗eq e⦘ ≡ ∅₂).
  { rewrite (wf_rmwE WF). basic_solver. }
  basic_solver 11.
Qed.

Lemma add_event_to_rf_complete r R1 w W1 W2
    (ADD : WCore.add_event_gen X X' e l r R1 w W1 W2)
    (WF : Wf G)
    (RFC : rf_complete G) :
  WCore.rf_delta_W e l R1 ≡ ∅₂.
Proof using.
  split; [| basic_solver]. unfold WCore.rf_delta_W.
  unfolder. intros e' r' ((EQ & IS_W) & RF1). subst e'.
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
  WCore.co_delta e l (W1' ∪₁ W1) W2 ≡
    WCore.co_delta e l W1 W2 ∪
    (eq e ∩₁ WCore.lab_is_w l) × W1'.
Proof using.
  basic_solver 11.
Qed.

End DeltaOps.