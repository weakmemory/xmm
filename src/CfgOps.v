(* From imm Require Import Events Execution imm_s_hb.
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

Lemma cfg_upd_lab_wf_props e l
    (ENINIT : ~is_init e)
    (U2V : same_label_u2v (labC e) l)
    (NRFR : ~codom_rel rfC e)
    (NRFL : ~dom_rel rfC e)
    (WF : WCore.wf_props X) :
  WCore.wf_props (cfg_upd_lab e l).
Proof using.
  constructor; ins.
  all: try now apply WF.
  { apply exec_upd_lab_wf; ins. apply WF. }
  { constructor; ins; try now apply WF.
    all: rewrite exec_upd_lab_F, exec_upd_lab_is_sc; ins.
    all: apply WF. }
  { apply exec_upd_lab_sub, WF. }
  all: rewrite exec_upd_lab_R; [apply WF |].
  all: now rewrite WF.(WCore.wprop_g_sub_gc).(sub_lab).
Qed.

Lemma cfg_upd_lab_wf_struct e l
    (WF : WCore.wf_struct X) :
  WCore.wf_struct (cfg_upd_lab e l).
Proof using.
  constructor; ins.
  all: try now apply WF.
Qed.

Lemma cfg_upd_lab_wf e l
    (ENINIT : ~is_init e)
    (U2V : same_label_u2v (labC e) l)
    (NRFR : ~codom_rel rfC e)
    (NRFL : ~dom_rel rfC e)
    (WF : WCore.wf X) :
  WCore.wf (cfg_upd_lab e l).
Proof using.
  red. red in WF. desf; split.
  { apply cfg_upd_lab_wf_struct; ins. }
  apply cfg_upd_lab_wf_props; ins.
Qed.

Lemma cfg_add_event_nctrl_wf_props e delta_rf
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
    (NCTRL : ctrlC ≡ ∅₂)
    (RMW_SAVED : rmwC ⊆ immediate (@sb (exec_add_read_event_nctrl GC e)))
    (WF : WCore.wf_props X) :
  WCore.wf_props (cfg_add_read_event_nctrl e delta_rf).
Proof using.
  assert (HINC : ~cmt e).
  { intro F. apply WF.(WCore.wprop_C_sub_EC) in F. ins. }
  assert (CMTEEQ : cmt ∩₁ eq e ≡₁ ∅) by basic_solver.
  assert (SUB : E ⊆₁ EC) by apply WF.
  constructor; ins.
  { apply exec_add_rf_wf, exec_add_event_wf_nctrl; ins.
    all: try now apply WF.
    rewrite DELTA_RF_WFE, <- !restr_relE, restr_restr.
    rewrite set_inter_absorb_r; ins. basic_solver. }
  { constructor; ins.
    all: try now apply WF.
    { rewrite WF.(WCore.wprop_wf_scc).(imm_s.wf_scE).
      rewrite <- !restr_relE, restr_restr.
      apply restr_rel_more; ins. basic_solver. }
    rewrite !set_inter_union_l.
    arewrite (eq e ∩₁ (fun e => is_f labC e) ≡₁ ∅).
    { unfold is_r, is_f in *; desf. basic_solver. }
    rewrite set_inter_empty_l, set_union_empty_r. apply WF. }
  { apply exec_add_rf_sub; ins.
    apply exec_add_event_nctrl_sub; ins.
    all: apply WF. }
  { rewrite WF.(WCore.wprop_C_sub_EC). basic_solver. }
  { transitivity sb; [| unfold sb; ins; basic_solver].
    rewrite set_inter_union_r, CMTEEQ, set_union_empty_r.
    eenough (SBEQ : restr_rel _ _ ≡ restr_rel (cmt ∩₁ E) sbC).
    { rewrite SBEQ. apply WF. }
    unfold sb; ins. rewrite <- !restr_relE, !restr_restr.
    rewrite !set_inter_absorb_l with (s := cmt ∩₁ E); ins.
    all: basic_solver. }
  { rewrite set_inter_union_r, CMTEEQ, set_union_empty_r.
    unfolder; intros x y RFC; desf; try now right.
    left. apply WF. unfolder; eauto. }
  { rewrite set_inter_union_l. intros x [INE | ISE].
    { destruct WF.(WCore.wprop_sub_rfD) with (x := x) as [DOM|CMT]; ins.
      all: try now right.
      left. apply codom_union. now left. }
    left. apply codom_union. right. unfolder in ISE; desf. }
  transitivity (codom_rel (⦗cmt⦘ ⨾ rfC)); [apply WF | basic_solver].
Qed.

Lemma cfg_add_event_nctrl_wf_struct e delta_rf
    (SUBE : E ⊆₁ EC)
    (ENINIT : ~is_init e)
    (NINIT' : tid e <> tid_init)
    (GC_INIT : EC ∩₁ is_init ⊆₁ E)
    (GC_TIDS : tid ↓₁ eq tid_init ∩₁ EC ⊆₁ is_init)
    (MAXSB : (fun x => ext_sb x e) ⊆₁ acts_set G ∩₁ same_tid e ∪₁ is_init)
    (WF : WCore.wf_struct X) :
  WCore.wf_struct (cfg_add_read_event_nctrl e delta_rf).
Proof using.
  constructor; ins.
  all: try apply exec_add_rf_cont, exec_add_event_cont; ins.
  all: try now apply WF.
  { transitivity (E ∩₁ same_tid e ∪₁ is_init); ins.
    basic_solver. }
  { rewrite set_inter_union_l, GC_INIT.
    arewrite (eq e ∩₁ is_init ≡₁ ∅); basic_solver. }
  rewrite set_inter_union_r, GC_TIDS.
  arewrite (tid ↓₁ eq tid_init ∩₁ eq e ≡₁ ∅); basic_solver.
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
  red. red in WF. desf; split.
  { apply cfg_add_event_nctrl_wf_struct; ins.
    all: try now apply STRUCT.
    apply PROPS. }
  apply cfg_add_event_nctrl_wf_props; ins.
  { apply STRUCT. }
  transitivity (immediate sbC); try now apply PROPS.
  unfold sb. ins. unfolder. splits; ins; desf.
  all: eauto 11.
  eapply HIN, ext_sb_dense; eauto.
  now apply STRUCT.
Qed.

Lemma cfg_mapped_wf_props f lab'
    (FINJ : inj_dom ⊤₁ f)
    (FSURJ : surj_dom ⊤₁ f)
    (HLAB : labC = lab' ∘ f)
    (FMAPINIT : forall l, f (InitEvent l) = InitEvent l)
    (PRESRVE_RMW : f ↑ rmwC ⊆ immediate (@sb (exec_mapped GC f lab')))
    (PRESERVE_RMW_DEP : f ↑ rmw_depC ⊆ (@sb (exec_mapped GC f lab')))
    (MAPIDS : forall a b, (f ↑₁ EC) a -> (f ↑₁ EC) b ->
              a <> b -> tid a = tid b -> ~is_init a -> index a <> index b)
    (NNEW_TIDS : (tid ∘ f) ↑₁ EC ⊆₁ threads_set GC)
    (NCTRL : ctrlC ≡ ∅₂)
    (NDATA : dataC ≡ ∅₂)
    (NADDR : addrC ≡ ∅₂)
    (WF : WCore.wf_props X) :
  WCore.wf_props (cfg_mapped f lab').
Proof using.
  constructor; ins.
  { apply exec_mapped_wf; ins; try now apply WF.
    all: now rewrite ?NDATA, ?NADDR, collect_rel_empty. }
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
  { apply exec_mapped_sub; ins. apply WF. }
  { assert (SUBE : E ⊆₁ EC) by apply WF.
    unfold sb. ins.
    rewrite collect_rel_eqv, <- !restr_relE.
    rewrite restr_restr, <- set_collect_interE; ins.
    rewrite set_inter_absorb_l; basic_solver. }
  { apply collect_rel_mori. ins.
    rewrite <- restr_relE. apply WF. }
  all: rewrite <- WF.(WCore.wprop_g_sub_gc).(sub_lab).
  all: now (apply set_collect_mori; ins; apply WF).
Qed.

Lemma cfg_mapped_wf_struct f lab'
    (FINJ : inj_dom ⊤₁ f)
    (NEW_G_CONT : contigious_actids (exec_mapped G f lab'))
    (NEW_GC_CONT : contigious_actids (exec_mapped GC f lab'))
    (NINIT_INITIDS : (tid ↓₁ eq tid_init) ∩₁ (f ↑₁ EC) ⊆₁ is_init)
    (FMAPINIT : forall l, f (InitEvent l) = InitEvent l)
    (WF : WCore.wf_struct X) :
  WCore.wf_struct (cfg_mapped f lab').
Proof using.
  constructor; ins.
  all: try now (rewrite <- collect_rel_empty; apply collect_rel_more;
                ins; apply WF).
  { unfold FinThreads.fin_threads. ins.
    apply WF. }
  arewrite (is_init ≡₁ f ↑₁ is_init).
  { unfold is_init. unfolder; splits; ins; desf.
    { eexists; split; eauto; ins. }
    congruence. }
  rewrite <- set_collect_interE; ins.
  apply set_collect_mori; [ins | apply WF].
Qed.

Lemma cfg_mapped_wf f lab'
    (FINJ : inj_dom ⊤₁ f)
    (FSURJ : surj_dom ⊤₁ f)
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
  red. red in WF. desf; split.
  { apply cfg_mapped_wf_struct; ins. }
  apply cfg_mapped_wf_props; ins.
  all: apply STRUCT.
Qed.

End CfgOps. *)