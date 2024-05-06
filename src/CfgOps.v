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
Require Import Core.
Require Import ExecOps.

Require Import Program.Basics.

Open Scope program_scope.

Section CfgOps.

Variable X : WCore.t.
Variable a b : actid.

Notation "'GC'" := (WCore.GC X).
Notation "'G'" := (WCore.G X).
Notation "'cmt'" := (WCore.cmt X).
Notation "'sc'" := (WCore.sc X).

Notation "'labC'" := (lab GC).
Notation "'locC'" := (loc labC).
Notation "'valC'" := (val labC).
Notation "'same_locC'" := (same_loc labC).
Notation "'EC'" := (acts_set GC).
Notation "'sbC'" := (sb GC).
Notation "'rfC'" := (rf GC).
Notation "'coC'" := (co GC).
Notation "'rmwC'" := (rmw GC).
Notation "'dataC'" := (data GC).
Notation "'ctrlC'" := (ctrl GC).
Notation "'addrC'" := (addr GC).
Notation "'rmw_depC'" := (rmw_dep GC).
Notation "'RC'" := (is_r labC).
Notation "'WC'" := (is_w labC).

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'ctrl'" := (ctrl G).
Notation "'addr'" := (addr G).

Definition cfg_upd_lab e l : WCore.t := {|
  WCore.G := exec_upd_lab G e l;
  WCore.GC := exec_upd_lab GC e l;
  WCore.sc := sc;
  WCore.cmt := cmt;
|}.
Definition cfg_add_read_event_nctrl e delta_rf : WCore.t := {|
  WCore.G := exec_add_rf (exec_add_read_event_nctrl G e) delta_rf;
  WCore.GC := exec_add_rf (exec_add_read_event_nctrl GC e) delta_rf;
  WCore.sc := sc;
  WCore.cmt := cmt;
|}.
Definition cfg_mapped f lab' : WCore.t := {|
  WCore.G := exec_mapped G f lab';
  WCore.GC := exec_mapped GC f lab';
  WCore.sc := f ↑ sc;
  WCore.cmt := f ↑₁ cmt;
|}.

Lemma cfg_upd_lab_wf e l
    (ENINIT : ~is_init e)
    (U2V : same_label_u2v (labC e) l)
    (NRFR : ~codom_rel rfC e)
    (NRFL : ~dom_rel rfC e)
    (WF : WCore.wf X) :
  WCore.wf (cfg_upd_lab e l).
Proof using.
  constructor; ins.
  all: try now apply WF.
  { apply exec_upd_lab_wf; ins. apply WF. }
  { constructor; ins; try now apply WF.
    all: rewrite exec_upd_lab_F, exec_upd_lab_is_sc by ins.
    all: apply WF. }
  all: try now rewrite exec_upd_lab_R; [apply WF |
    rewrite WF.(WCore.pfx).(pfx_sub).(sub_lab)].
  constructor; ins.
  all: try now apply exec_upd_lab_cont, WF.
  apply exec_upd_lab_sub, WF.
Qed.

Lemma cfg_add_event_nctrl_wf e delta_rf
    (ENINIT : ~is_init e)
    (NINIT' : tid e <> tid_init)
    (HIN : ~EC e)
    (IS_R : RC e)
    (ETHR : threads_set GC (tid e))
    (SBMAX : (fun x => ext_sb x e) ⊆₁ E ∩₁ same_tid e ∪₁ is_init)
    (HLOC : forall l (LOC : locC e = Some l), EC (InitEvent l))
    (NEW_RF : forall x
                  (DOM1 : dom_rel rfC⁻¹ x)
                  (DOM2 : dom_rel delta_rf⁻¹ x),
                False)
    (FUNEQ : funeq valC delta_rf)
    (FUNC : functional delta_rf⁻¹)
    (DELTA_RF_WFE : delta_rf ≡ ⦗E ∪₁ eq e⦘ ⨾ delta_rf ⨾ ⦗E ∪₁ eq e⦘)
    (DELTA_RF_WFD : delta_rf ≡ ⦗WC⦘ ⨾ delta_rf ⨾ ⦗RC⦘)
    (DELTA_RF : delta_rf ⊆ same_locC)
    (DELTA_RF_CODOM : codom_rel delta_rf e)
    (WF : WCore.wf X) :
  WCore.wf (cfg_add_read_event_nctrl e delta_rf).
Proof using.
  assert (HINE : ~E e).
  { intro F. apply WF.(WCore.pfx) in F. ins. }
  assert (HINC : ~cmt e).
  { intro F. apply WF.(WCore.C_sub_EC) in F. ins. }
  assert (CMTEEQ : cmt ∩₁ eq e ≡₁ ∅) by basic_solver.
  assert (EEEQ : eq e ∩₁ E ≡₁ ∅) by basic_solver.
  constructor; ins.
  all: try now apply WF.
  { apply exec_add_rf_wf, exec_add_event_wf_nctrl; ins.
    all: try now apply WF.
    { rewrite DELTA_RF_WFE, <- !restr_relE, restr_restr.
      rewrite set_inter_absorb_r; ins. apply set_union_mori.
      all: ins; apply WF. }
    unfold sb; ins. unfolder. intros e' SB. desf.
    all: try now eapply ext_sb_irr; eauto.
    apply HIN. apply ext_sb_dense with (e2 := e'); ins.
    apply WF. }
  { constructor; ins.
    all: try now apply WF.
    { rewrite WF.(WCore.wf_scc).(imm_s.wf_scE).
      rewrite <- !restr_relE, restr_restr.
      apply restr_rel_more; ins. basic_solver. }
    rewrite !set_inter_union_l.
    arewrite (eq e ∩₁ (fun e => is_f labC e) ≡₁ ∅).
    { unfold is_r, is_f in *; desf. basic_solver. }
    rewrite set_inter_empty_l, set_union_empty_r. apply WF. }
  { rewrite set_inter_union_l, WF.(WCore.wf_g_init). basic_solver. }
  { rewrite set_inter_union_r, WF.(WCore.wf_gc_acts).
    rewrite <- set_union_empty_r with (s := is_init) at 2.
    apply set_union_mori; ins. unfolder. basic_solver. }
  { rewrite WF.(WCore.C_sub_EC). basic_solver. }
  { rewrite set_inter_union_r, CMTEEQ, set_union_empty_r.
    unfold sb; ins. rewrite <- !restr_relE, restr_restr.
    rewrite set_inter_union_l, <- !set_interA.
    arewrite (eq e ∩₁ cmt ∩₁ E ≡₁ ∅); [basic_solver |].
    arewrite (EC ∩₁ cmt ∩₁ E ≡₁ cmt ∩₁ E).
    { split; [basic_solver |]. unfolder; ins; desf.
      splits; ins. now apply WF. }
    rewrite set_union_empty_r.
    apply restr_rel_mori; [basic_solver | ins]. }
  { rewrite set_inter_union_r, CMTEEQ, set_union_empty_r.
    unfolder; intros x y RFC; desf; try now right.
    left. apply WF. unfolder; eauto. }
  { rewrite set_inter_union_l. intros x [INE | ISE].
    { destruct WF.(WCore.sub_rfD) with (x := x) as [DOM|CMT]; ins.
      all: try now right.
      left. apply codom_union. now left. }
    left. apply codom_union. right. unfolder in ISE; desf. }
  { transitivity (codom_rel (⦗cmt⦘ ⨾ rfC)); [apply WF | basic_solver]. }
  constructor; ins.
  { apply exec_add_rf_sub; ins.
    apply exec_add_event_nctrl_sub; ins.
    all: apply WF. }
  all: apply exec_add_rf_cont, exec_add_event_cont.
  all: ins; try now apply WF.
  intros x SB. apply SBMAX in SB. destruct SB as [INE | INIT].
  { left. split; [apply WF.(WCore.pfx) |]; apply INE. }
  now right.
Qed.

Lemma cfg_mapped_wf f lab'
    (FINJ : inj_dom ⊤₁ f)
    (FSURJ : forall y, exists x, y = f x)
    (HLAB : labC = lab' ∘ f)
    (PRESRVE_RMW : f ↑ rmwC ⊆ immediate (@sb (exec_mapped GC f lab')))
    (PRESERVE_RMW_DEP : f ↑ rmw_depC ⊆ (@sb (exec_mapped GC f lab')))
    (FMAPINIT : forall l, f (InitEvent l) = InitEvent l)
    (MAPIDS : forall a b, (f ↑₁ EC) a -> (f ↑₁ EC) b ->
              a <> b -> tid a = tid b -> ~is_init a -> index a <> index b)
    (NNEW_TIDS : (tid ∘ f) ↑₁ EC ⊆₁ threads_set GC)
    (NINIT_INITIDS : (tid ↓₁ eq tid_init) ∩₁ (f ↑₁ EC) ⊆₁ is_init)
    (NEW_G_CONT : contigious_actids (exec_mapped G f lab'))
    (NEW_GC_CONT : contigious_actids (exec_mapped GC f lab'))
    (WF : WCore.wf X) :
  WCore.wf (cfg_mapped f lab').
Proof using.
  assert (COLINIT : f ↑₁ is_init ≡₁ is_init).
  { unfold is_init. unfolder. split; ins; desf.
    { rewrite ?FMAPINIT in Heq. congruence. }
    eexists. split; eauto. ins. }
  constructor; ins.
  { now rewrite WF.(WCore.cc_ctrl_empty), collect_rel_empty. }
  { now rewrite WF.(WCore.cc_addr_empty), collect_rel_empty. }
  { now rewrite WF.(WCore.cc_data_empty), collect_rel_empty. }
  { apply exec_mapped_wf; ins.
    all: try now apply WF.
    { now rewrite WF.(WCore.cc_data_empty), collect_rel_empty. }
    now rewrite WF.(WCore.cc_addr_empty), collect_rel_empty. }
  all: try apply imm_s.Build_wf_sc; ins.
  all: rewrite 1?exec_mapped_F with (G := GC) (f := f),
               1?exec_mapped_R with (G := GC) (f := f),
               1?exec_mapped_is_sc with (G := GC) (f := f),
               <- 1?COLINIT, ?restr_relE, <- ?set_collect_interE,
               <- ?collect_rel_eqv, <- ?collect_rel_seq,
               <- ?set_collect_codom, <- ?set_collect_union.
  all: eauto.
  all: try now eapply inj_dom_mori with (x := ⊤₁); eauto; ins.
  all: try now (apply collect_rel_more; ins; apply WF).
  all: try now (apply set_collect_mori; ins; apply WF).
  { arewrite (sc ≡ restr_rel ⊤₁ sc) by basic_solver.
    apply transitive_collect_rel_inj, transitive_restr, WF; ins. }
  { apply total_collect_rel, WF. }
  { arewrite (sc ≡ restr_rel ⊤₁ sc) by basic_solver.
    apply collect_rel_irr_inj, irreflexive_restr, WF; ins. }
  { assert (SUBE : E ⊆₁ EC) by apply WF.
    unfold sb. ins. unfolder. intros x y SB. desf.
    splits; ins; eauto. rewrite FINJ with (x := y'0) (y := y1).
    all: try red; eauto. }
  { rewrite <- restr_relE.
    apply collect_rel_mori; ins; apply WF. }
  all: try rewrite <- WF.(WCore.pfx).(pfx_sub).(sub_lab).
  all: try now (apply set_collect_mori; ins; apply WF).
  constructor; ins.
  apply exec_mapped_sub; ins. apply WF.
Qed.

End CfgOps.