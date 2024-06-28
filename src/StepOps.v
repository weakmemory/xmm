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
Require Import CfgOps.

Require Import Program.Basics.

Open Scope program_scope.

Section StepOps.

Variable X X' : WCore.t.

Notation "'G''" := (WCore.G X').
Notation "'G'" := (WCore.G X).
Notation "'GC'" := (WCore.GC X).
Notation "'cmt'" := (WCore.cmt X).

Notation "'labC'" := (lab GC).

Notation "'lab''" := (lab G').
Notation "'loc''" := (loc lab').
Notation "'val''" := (val lab').
Notation "'same_loc''" := (same_loc lab').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'ctrl''" := (ctrl G').
Notation "'addr''" := (addr G').
Notation "'rmw_dep''" := (rmw_dep G').
Notation "'R''" := (is_r lab').
Notation "'W''" := (is_w lab').

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'ctrl'" := (ctrl G).
Notation "'addr'" := (addr G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'R'" := (is_r lab).
Notation "'W'" := (is_w lab).

Lemma cfg_upd_lab_add_step_props a l e r w W1 W2
    (U2V : same_label_u2v (labC a) l)
    (STEP : WCore.cfg_add_event_props X X' e r w W1 W2) :
  WCore.cfg_add_event_props
    (cfg_upd_lab X  a l)
    (cfg_upd_lab X' a l)
    e r w W1 W2.
Proof using.
  assert (IS_W_SAME : is_w (@lab (exec_upd_lab GC a l)) e = is_w labC e).
  { ins. unfold is_w. red in U2V.
    destruct (classic (e = a)) as [HEQ|NEQ].
    all: subst; rupd; desf. }
  constructor; ins.
  { rewrite (WCore.caep_rf_new STEP); repeat apply union_more; ins.
    { unfold WCore.rf_delta_R. destruct w as [w |]; ins.
      rewrite exec_upd_lab_W, exec_upd_lab_R; ins. }
    unfold WCore.rf_delta_W. ins. rewrite IS_W_SAME. desf. }
  { rewrite (WCore.caep_co_new STEP); repeat apply union_more; ins.
    unfold WCore.co_delta. ins. rewrite IS_W_SAME. desf. }
  rewrite (WCore.caep_rmw_new STEP); apply union_more; ins.
  unfold WCore.rmw_delta. ins.
  rewrite exec_upd_lab_W, exec_upd_lab_R; ins.
Qed.

Lemma cfg_mapped_add_step_props f lab_new e r w W1 W2
    (F_INJ : inj_dom ⊤₁ f)
    (F_SURJ : surj_dom ⊤₁ f)
    (HLAB : labC = lab_new ∘ f)
    (STEP : WCore.cfg_add_event_props X X' e r w W1 W2) :
  WCore.cfg_add_event_props
    (cfg_mapped X  f lab_new)
    (cfg_mapped X' f lab_new)
    (f e)
    (option_map f r)
    (option_map f w)
    (f ↑₁ W1)
    (f ↑₁ W2).
Proof using.
  assert (IS_W_SAME : is_w (@lab (exec_mapped GC f lab_new)) (f e) =
                      is_w labC e).
  { ins. now rewrite HLAB. }
  constructor; ins.
  { rewrite (WCore.caep_rf_new STEP); rewrite !collect_rel_union.
    repeat apply union_more; ins.
    { unfold WCore.rf_delta_R.
      destruct w as [w |]; try now apply collect_rel_empty.
      unfold option_map; ins.
      rewrite collect_rel_interE, collect_rel_cross,
              collect_rel_singl, <- exec_mapped_R,
              <- exec_mapped_W.
      all: eauto. }
    unfold WCore.rf_delta_W. ins. rewrite IS_W_SAME.
    desf; try now apply collect_rel_empty.
    rewrite !collect_rel_seq, !collect_rel_eqv,
            set_collect_eq, set_collect_interE; ins.
    all: now eapply inj_dom_mori; eauto. }
  { rewrite (WCore.caep_co_new STEP); rewrite !collect_rel_union.
    apply union_more; ins.
    unfold WCore.co_delta. ins. rewrite IS_W_SAME.
    desf; try now apply collect_rel_empty.
    now rewrite collect_rel_union, !collect_rel_cross,
            set_collect_eq. }
  rewrite (WCore.caep_rmw_new STEP); rewrite !collect_rel_union.
  apply union_more; ins.
  unfold WCore.rmw_delta.
  rewrite collect_rel_cross, !set_collect_interE,
          set_collect_eq_opt, set_collect_eq,
          <- exec_mapped_R, <- exec_mapped_W; eauto.
Qed.

Lemma cfg_add_event_nctrl_add_step_props a b e r w W1 W2
    (ANCMT : ~cmt a)
    (STEP : WCore.cfg_add_event_props X X' e r w W1 W2) :
  WCore.cfg_add_event_props
    (cfg_add_read_event_nctrl X  a (singl_rel b a))
    (cfg_add_read_event_nctrl X' a (singl_rel b a))
    e r w W1 W2.
Proof using.
  constructor; ins.
  { rewrite !unionC with (r2 := singl_rel b a).
    rewrite (WCore.caep_rf_new STEP), <- !unionA.
    repeat apply union_more; ins.
    unfold WCore.rf_delta_W; ins. desf.
    arewrite (cmt ∩₁ (E ∪₁ eq a) ≡₁ cmt ∩₁ E) by basic_solver.
    arewrite ((@rf GC ∪ singl_rel b a) ⨾ ⦗cmt ∩₁ E⦘ ≡
              @rf GC ⨾ ⦗cmt ∩₁ E⦘) by basic_solver. }
  { rewrite (WCore.caep_co_new STEP); ins. }
  rewrite (WCore.caep_rmw_new STEP); ins.
Qed.

End StepOps.

Lemma cfg_add_event_nctrl_as_add_step sc cmt G GC e w
    (IS_W : is_w (lab GC) w)
    (IS_R : is_r (lab GC) e) :
  WCore.cfg_add_event_props
    {|
      WCore.G := G;
      WCore.GC := exec_add_rf (
        exec_add_read_event_nctrl GC e
      ) (singl_rel w e);
      WCore.cmt := cmt;
      WCore.sc := sc;
    |}
    {|
      WCore.G := exec_add_rf (
        exec_add_read_event_nctrl G e
      ) (singl_rel w e);
      WCore.GC :=  exec_add_rf (
        exec_add_read_event_nctrl GC e
      ) (singl_rel w e);
      WCore.cmt := cmt;
      WCore.sc := sc;
    |}
    e None (Some w) ∅ ∅.
Proof using.
  constructor; ins.
  { arewrite (WCore.rf_delta_W (exec_add_rf
                                  (exec_add_read_event_nctrl GC e)
                                  (singl_rel w e)) e
                                (cmt ∩₁ acts_set G) ≡ ∅₂).
    { unfold WCore.rf_delta_W, is_r, is_w in *; ins. desf. }
    rewrite union_false_r. basic_solver 5. }
  { unfold WCore.co_delta. unfold is_w, is_r in *.
    ins. desf. now rewrite union_false_r. }
  unfold WCore.rmw_delta. basic_solver.
Qed.