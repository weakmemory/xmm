Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import ExecEquiv.
Require Import ThreadTrace.
Require Import Core.
Require Import TraceSwap.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.
From imm Require Import CombRelations.

Set Implicit Arguments.

Module SubToFullExecInternal.

Section Prefix.

Variable X X' : WCore.t.

Notation "'G''" := (WCore.G X').
Notation "'lab''" := (lab G').
Notation "'threads_set''" := (threads_set G').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'rmw_dep''" := (rmw_dep G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'W''" := (is_w lab').
Notation "'R''" := (is_r lab').
Notation "'F''" := (is_f lab').
Notation "'sc''" := (WCore.sc X').

Notation "'G'" := (WCore.G X).
Notation "'lab'" := (lab G).
Notation "'threads_set'" := (threads_set G).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'F'" := (is_f lab).
Notation "'sc'" := (WCore.sc X).

Record prefix : Prop := {
  prf_init : E' ∩₁ is_init ⊆₁ E;
  prf_acts : E ⊆₁ E';
  prf_threads : threads_set ≡₁ threads_set';
  prf_lab : eq_dom (is_init ∪₁ E) lab lab';
  prf_rf : rf ≡ restr_rel E rf';
  prf_co : co ≡ restr_rel E co';
  prf_rmw : rmw ≡ restr_rel E rmw';
  prf_data : data ≡ data';
  prf_ctrl : ctrl ≡ ctrl';
  prf_addr : addr ≡ addr';
  prf_rmw_dep : rmw_dep ≡ rmw_dep';
  prf_sc : sc ≡ restr_rel E sc';
  prf_sb : sb' ⨾ ⦗E⦘ ⊆ sb
}.

End Prefix.

Section DeltaGraph.

Variable X X' : WCore.t.
Variable cmt : actid -> Prop.
Variable e : actid.

Notation "'G''" := (WCore.G X').
Notation "'lab''" := (lab G').
Notation "'threads_set''" := (threads_set G').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'rmw_dep''" := (rmw_dep G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'W''" := (is_w lab').
Notation "'R''" := (is_r lab').
Notation "'F''" := (is_f lab').
Notation "'sc''" := (WCore.sc X').

Notation "'G'" := (WCore.G X).
Notation "'lab'" := (lab G).
Notation "'threads_set'" := (threads_set G).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'F'" := (is_f lab).
Notation "'sc'" := (WCore.sc X).

Definition delta_E := E ∪₁ eq e.
Definition delta_lab := upd lab e (lab' e).

Definition delta_G := {|
  acts_set := delta_E;
  threads_set := threads_set;
  lab := delta_lab;
  rf := restr_rel delta_E rf';
  co := restr_rel delta_E co';
  rmw := restr_rel delta_E rmw';
  addr := addr';
  data := data';
  ctrl := ctrl';
  rmw_dep := rmw_dep';
|}.

Definition delta_sc := restr_rel delta_E sc'.

Definition delta_X := {|
  WCore.G := delta_G;
  WCore.sc := delta_sc;
|}.

Lemma delta_eq_lab
    (PFX : prefix X X')
    (NINIT : ~is_init e)
    (NOTINE : ~ E e) :
  eq_dom (is_init ∪₁ delta_E) delta_lab lab'.
Proof using.
  unfold delta_E, delta_lab.
  rewrite <- set_unionA. apply eq_dom_union.
  split; unfolder; intros x XIN.
  { rewrite updo; [now apply PFX |].
    desf; congruence. }
  subst x. now rewrite upds.
Qed.

Lemma delta_lab_is_r
    (s : actid -> Prop)
    (SUB : s ⊆₁ delta_E)
    (PFX : prefix X X')
    (NINIT : ~is_init e)
    (NOTINE : ~ E e) :
  is_r lab' ∩₁ s ≡₁ is_r delta_lab ∩₁ s.
Proof using.
  unfolder. split; intros x (LAB & IN).
  all: split; ins.
  all: unfold is_r.
  { rewrite delta_eq_lab; ins.
    basic_solver. }
  rewrite <- delta_eq_lab; ins.
  basic_solver.
Qed.

Lemma delta_lab_is_w
    (s : actid -> Prop)
    (SUB : s ⊆₁ delta_E)
    (PFX : prefix X X')
    (NINIT : ~is_init e)
    (NOTINE : ~ E e) :
  is_w lab' ∩₁ s ≡₁ is_w delta_lab ∩₁ s.
Proof using.
  unfolder. split; intros x (LAB & IN).
  all: split; ins.
  all: unfold is_w.
  { rewrite delta_eq_lab; ins.
    basic_solver. }
  rewrite <- delta_eq_lab; ins.
  basic_solver.
Qed.

Lemma delta_lab_is_f
    (s : actid -> Prop)
    (SUB : s ⊆₁ delta_E)
    (PFX : prefix X X')
    (NINIT : ~is_init e)
    (NOTINE : ~ E e) :
  is_f lab' ∩₁ s ≡₁ is_f delta_lab ∩₁ s.
Proof using.
  unfolder. split; intros x (LAB & IN).
  all: split; ins.
  all: unfold is_f.
  { rewrite delta_eq_lab; ins.
    basic_solver. }
  rewrite <- delta_eq_lab; ins.
  basic_solver.
Qed.

Lemma pfx_same_loc x
    (s : actid -> Prop)
    (SUB : s ⊆₁ delta_E)
    (PFX : prefix X X')
    (NINIT : ~is_init e)
    (NOTINE : ~ E e)
    (INE : delta_E x) :
  same_loc lab' x ∩₁ s ≡₁ same_loc delta_lab x ∩₁ s.
Proof using.
  unfolder. split; intros y (LAB & IN).
  all: split; ins.
  all: unfold same_loc, loc.
  { rewrite !delta_eq_lab; ins.
    all: basic_solver. }
  rewrite <- !delta_eq_lab; ins.
  all: basic_solver.
Qed.

Lemma pfx_same_loc'
    (PFX : prefix X X')
    (NINIT : ~is_init e)
    (NOTINE : ~ E e) :
  restr_rel delta_E (same_loc lab') ≡
    restr_rel delta_E (same_loc delta_lab).
Proof using.
  split; intros x y (LAB & DOM & CODOM).
  { apply set_subset_single_l.
    arewrite (restr_rel delta_E (same_loc delta_lab) x ≡₁
              same_loc delta_lab x ∩₁ delta_E).
    { basic_solver 12. }
    rewrite <- pfx_same_loc; ins.
    basic_solver 12. }
  apply set_subset_single_l.
  arewrite (restr_rel delta_E (same_loc lab') x ≡₁
            same_loc lab' x ∩₁ delta_E).
  { basic_solver 12. }
  rewrite pfx_same_loc; ins.
  basic_solver 12.
Qed.

Lemma delta_add_event
    (INE : E' e)
    (NOTINE : ~ E e)
    (NINIT : ~ is_init e)
    (WF : Wf G')
    (PFX : prefix X X')
    (EMAX : ⦗eq e⦘ ⨾ sb' ⨾ ⦗E⦘ ⊆ ∅₂) :
  WCore.add_event X delta_X e (lab' e).
Proof using.
  red.
  assert (RMW : exists r,
    match r with
    | Some r => ⦗E⦘ ⨾ rmw' ⨾ ⦗eq e⦘ ≡ singl_rel r e
    | None => ⦗E⦘ ⨾ rmw' ⨾ ⦗eq e⦘ ≡ ∅₂
    end
  ).
  { destruct (classic (⦗E⦘ ⨾ rmw' ⨾ ⦗eq e⦘ ≡ ∅₂)) as [EMPTY|NEN].
    { now exists None. }
    assert (NEN' : ~dom_rel (⦗E⦘ ⨾ rmw' ⨾ ⦗eq e⦘) ≡₁ ∅).
    { intros EMP. apply NEN. split; [| basic_solver].
      intros x y HREL. eapply EMP with x. basic_solver. }
    apply set_nonemptyE in NEN'. destruct NEN' as (r & HIN).
    exists (Some r). split; [| unfolder in *; ins; desf].
    unfolder. intros x y (HIN' & RMW & HEQ). subst y.
    split; ins. eapply (wf_rmwff WF); eauto.
    unfold transp. unfolder in HIN. desf. }
  assert (RF : exists w,
    match w with
    | Some w => ⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘ ≡ singl_rel w e
    | None => ⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘ ≡ ∅₂
    end
  ).
  { destruct (classic (⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘ ≡ ∅₂)) as [EMPTY|NEN].
    { now exists None. }
    assert (NEN' : ~dom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘) ≡₁ ∅).
    { intros EMP. apply NEN. split; [| basic_solver].
      intros x y HREL. eapply EMP with x. basic_solver. }
    apply set_nonemptyE in NEN'. destruct NEN' as (r & HIN).
    exists (Some r). split; [| unfolder in *; ins; desf].
    unfolder. intros x y (HIN' & RF & HEQ). subst y.
    split; ins. eapply (wf_rff WF); eauto.
    unfold transp. unfolder in HIN. desf. }
  (* The proof *)
  destruct RMW as (r & RMW), RF as (w & RF).
  exists r,
         (codom_rel (⦗eq e⦘ ⨾ rf' ⨾ ⦗E⦘    )),
         w,
         (codom_rel (⦗eq e⦘ ⨾ co' ⨾ ⦗E⦘    )),
         (dom_rel   (   ⦗E⦘ ⨾ co' ⨾ ⦗eq e⦘ )).
  constructor; ins.
  all: try now (symmetry; apply PFX).
  all: unfold delta_E.
  { rewrite restr_set_union, (prf_rf PFX).
    rewrite restr_irrefl_eq by now apply rf_irr.
    rewrite union_false_r.
    repeat apply union_more; ins.
    { unfold WCore.rf_delta_R.
      destruct w as [w |]; ins.
      rewrite <- RF.
      rewrite (wf_rfD WF), !seqA.
      seq_rewrite <- !id_inter.
      rewrite set_interC with (s := E).
      rewrite delta_lab_is_r, delta_lab_is_w.
      all: ins; try (unfold delta_E; basic_solver). }
    unfold WCore.rf_delta_W.
    arewrite (eq e × codom_rel (⦗eq e⦘ ⨾ rf' ⨾ ⦗E⦘) ≡ ⦗eq e⦘ ⨾ rf' ⨾ ⦗E⦘).
    { basic_solver 12. }
    rewrite (wf_rfD WF), !seqA.
    seq_rewrite <- !id_inter.
    rewrite set_interC with (s := eq e).
    rewrite delta_lab_is_r, delta_lab_is_w.
    all: ins; try (unfold delta_E; basic_solver). }
  { rewrite restr_set_union, (prf_co PFX).
    rewrite restr_irrefl_eq by now apply co_irr.
    rewrite union_false_r. rewrite unionA.
    apply union_more; ins. rewrite unionC.
    unfold WCore.co_delta.
    arewrite (eq e × codom_rel (⦗eq e⦘ ⨾ co' ⨾ ⦗E⦘) ≡ ⦗eq e⦘ ⨾ co' ⨾ ⦗E⦘).
    { basic_solver 12. }
    arewrite (dom_rel (⦗E⦘ ⨾ co' ⨾ ⦗eq e⦘) × eq e  ≡ ⦗E⦘ ⨾ co' ⨾ ⦗eq e⦘).
    { basic_solver 12. }
    apply union_more.
    { arewrite (⦗eq e⦘ ⨾ co' ≡ ⦗eq e⦘ ⨾ co' ⨾ ⦗same_loc lab' e⦘).
      { split; [| basic_solver].
        unfolder. intros e' y (EQ & CO); splits; ins.
        subst e'. now apply (wf_col WF). }
      rewrite (wf_coD WF), !seqA.
      seq_rewrite <- !id_inter.
      rewrite set_interC with (s := E),
              set_interC with (s := eq e).
      rewrite 2!delta_lab_is_w, pfx_same_loc.
      all: ins; try (unfold delta_E; basic_solver). }
    arewrite (co' ⨾ ⦗eq e⦘ ≡ ⦗same_loc lab' e⦘ ⨾ co' ⨾ ⦗eq e⦘).
    { split; [| basic_solver].
      unfolder. intros x e' (EQ & CO); splits; ins.
      subst e'. symmetry. now apply (wf_col WF). }
    rewrite (wf_coD WF), !seqA.
    seq_rewrite <- !id_inter.
    rewrite set_interC with (s' := W'),
            set_interC with (s := E).
    rewrite 2!delta_lab_is_w, pfx_same_loc.
    all: ins; try (unfold delta_E; basic_solver). }
  { rewrite restr_set_union, (prf_rmw PFX).
    rewrite restr_irrefl_eq by now apply rmw_irr.
    rewrite union_false_r. rewrite unionA.
    apply union_more; ins.
    arewrite (⦗eq e⦘ ⨾ rmw' ⨾ ⦗E⦘ ≡ ∅₂).
    { split; [| basic_solver].
      now rewrite (wf_rmwi WF), immediate_in. }
    rewrite union_false_r. unfold WCore.rmw_delta.
    destruct r as [r |]; ins.
    rewrite <- RMW.
    rewrite (wf_rmwD WF), !seqA.
    seq_rewrite <- !id_inter.
    rewrite set_interC with (s := E).
    rewrite delta_lab_is_r, delta_lab_is_w.
    all: ins; try (unfold delta_E; basic_solver). }
  unfold delta_G, delta_E, sb at 1. ins.
  rewrite <- restr_relE, restr_set_union, restr_relE.
  change (⦗E⦘ ⨾ ext_sb ⨾ ⦗E⦘) with sb.
  rewrite restr_irrefl_eq by now apply ext_sb_irr.
  arewrite (⦗eq e⦘ ⨾ ext_sb ⨾ ⦗E⦘ ≡ ⦗eq e⦘ ⨾ sb' ⨾ ⦗E⦘).
  { unfold sb. rewrite !seqA. seq_rewrite <- !id_inter.
    rewrite set_inter_absorb_r, set_inter_absorb_l; ins.
    { apply PFX. }
    basic_solver. }
  arewrite (⦗eq e⦘ ⨾ sb' ⨾ ⦗E⦘ ≡ ∅₂).
  { split; [ins | basic_solver]. }
  rewrite !union_false_r. apply union_more; ins.
  unfold WCore.sb_delta. split.
  { unfolder. unfold ext_sb, same_tid. ins.
    do 2 desf; split; ins; eauto. }
  unfolder. intros x y ((HINE & HTID) & HEQ).
  subst y. splits; ins. unfold ext_sb.
  destruct HTID as [INIT | SAME].
  { destruct x, e; ins. }
  destruct e as [el | et en]; ins.
  destruct x as [xl | xt xn]; ins.
  unfold same_tid in SAME. ins. subst xt.
  split; ins.
  assert (TRI : xn < en \/ xn = en \/ en < xn).
  { lia. }
  destruct TRI as [LT | [EQ | GT]]; ins.
  { congruence. }
  exfalso.
  apply EMAX with (ThreadEvent et en) (ThreadEvent et xn).
  unfolder. splits; ins. unfold sb. unfolder.
  splits; ins. now apply PFX.
Qed.

Lemma delta_G_prefix
    (INE : E' e)
    (NOTINE : ~ E e)
    (NINIT : ~ is_init e)
    (EMAX : sb' ⨾ ⦗eq e⦘ ⊆ ⦗E⦘ ⨾ sb' ⨾ ⦗eq e⦘)
    (PFX : prefix X X') :
  prefix delta_X X'.
Proof using.
  assert (SUBE : E ∪₁ eq e ⊆₁ E').
  { apply set_subset_union_l; split; [| basic_solver].
    apply PFX. }
  unfold delta_X, delta_G, delta_sc,
         delta_E, delta_lab.
  constructor; ins.
  { rewrite <- (prf_init PFX). basic_solver. }
  { apply PFX. }
  { rewrite <- set_unionA. apply eq_dom_union.
    unfolder; split; [| now ins; desf; rupd].
    intros x XIN. rupd; [| desf; congruence].
    apply PFX. now unfolder. }
  rewrite id_union, seq_union_r at 1.
  apply inclusion_union_l.
  { rewrite (prf_sb PFX). unfold sb; ins.
    basic_solver. }
  rewrite EMAX.
  unfold sb. ins. rewrite !seqA.
  seq_rewrite <- !id_inter.
  rewrite set_inter_absorb_r, set_inter_absorb_l.
  { basic_solver. }
  { basic_solver. }
  apply set_subset_union_l in SUBE. desf.
Qed.

Lemma delta_G_wf
    (INE : E' e)
    (NOTINE : ~ E e)
    (NINIT : ~ is_init e)
    (EMAX : sb' ⨾ ⦗eq e⦘ ⊆ ⦗E⦘ ⨾ sb' ⨾ ⦗eq e⦘)
    (PFX : prefix X X')
    (NDATA : data' ⊆ ∅₂)
    (NADDR : addr' ⊆ ∅₂)
    (NCTRL : ctrl' ⊆ ∅₂)
    (NRMWDEP : rmw_dep' ⊆ ∅₂)
    (WF : Wf G') :
  Wf delta_G.
Proof using.
  assert (SUBE : delta_E ⊆₁ E').
  { unfold delta_E. apply set_subset_union_l.
    split; [apply PFX | basic_solver]. }
  constructor.
  { intros a b (INA & INB & NEQ & TID & ANINI).
    ins. apply WF. splits; ins.
    all: basic_solver. }
  all: ins.
  { rewrite NDATA. basic_solver. }
  { split; rewrite NDATA at 1; basic_solver. }
  { rewrite NADDR. basic_solver. }
  { split; rewrite NADDR at 1; basic_solver. }
  { rewrite NCTRL. basic_solver. }
  { split; rewrite NCTRL at 1; basic_solver. }
  { rewrite NCTRL at 1. basic_solver. }
  { rewrite (wf_rmwD WF) at 1. rewrite !restr_relE, !seqA.
    seq_rewrite <- !id_inter.
    rewrite !set_interC with (s := delta_E).
    rewrite delta_lab_is_r, delta_lab_is_w; ins. }
  { transitivity (restr_rel delta_E (same_loc delta_lab)); [| basic_solver].
    rewrite <- pfx_same_loc'; ins.
    apply restr_rel_mori; ins. apply WF. }
  { transitivity (restr_rel delta_E (immediate sb')).
    { apply restr_rel_mori; ins. apply WF. }
    admit. }
  { rewrite !restr_relE, !seqA. seq_rewrite <- !id_inter.
    now rewrite !set_interK. }
  { rewrite (wf_rfD WF) at 1. rewrite !restr_relE, !seqA.
    seq_rewrite <- !id_inter.
    rewrite !set_interC with (s := delta_E).
    rewrite delta_lab_is_r, delta_lab_is_w; ins. }
  { transitivity (restr_rel delta_E (same_loc delta_lab)); [| basic_solver].
    rewrite <- pfx_same_loc'; ins.
    apply restr_rel_mori; ins. apply WF. }
  { admit. }
  { rewrite <- restr_transp. apply functional_restr.
    apply WF. }
  { rewrite !restr_relE, !seqA. seq_rewrite <- !id_inter.
    now rewrite !set_interK. }
  { rewrite (wf_coD WF) at 1. rewrite !restr_relE, !seqA.
    seq_rewrite <- !id_inter.
    rewrite !set_interC with (s := delta_E).
    rewrite delta_lab_is_w; ins. }
  { transitivity (restr_rel delta_E (same_loc delta_lab)); [| basic_solver].
    rewrite <- pfx_same_loc'; ins.
    apply restr_rel_mori; ins. apply WF. }
  { apply transitive_restr, WF. }
  { admit. }
  { apply irreflexive_restr, WF. }
  { match goal with
    | [ HEE : exists b, _ /\ loc delta_lab b = Some _  |- _] =>
        rename HEE into EE
    | _ => fail "bruh"
    end.
    left. apply (prf_init PFX). split; ins.
    apply WF. destruct EE as (b & BIN & BLOC).
    exists b. split; [basic_solver |].
    unfold loc. rewrite <- delta_eq_lab; ins. basic_solver. }
  { rewrite (prf_lab (delta_G_prefix INE NOTINE NINIT EMAX PFX)).
    { apply WF. }
    basic_solver. }
  { rewrite NRMWDEP. basic_solver. }
  { split; rewrite NRMWDEP at 1; basic_solver. }
  apply (prf_threads PFX).
  apply WF, SUBE, EE.
Admitted.


Lemma delta_guided_add_step
    (INE : E' e)
    (NOTINE : ~ E e)
    (NINIT : ~ is_init e)
    (WF : Wf G')
    (XWF : WCore.wf X X' cmt)
    (PFX : prefix X X')
    (EMAX1 : ⦗eq e⦘ ⨾ sb' ⨾ ⦗E⦘ ⊆ ∅₂)
    (EMAX2 : sb' ⨾ ⦗eq e⦘ ⊆ ⦗E⦘ ⨾ sb' ⨾ ⦗eq e⦘)
    (NDATA : data' ⊆ ∅₂)
    (NADDR : addr' ⊆ ∅₂)
    (NCTRL : ctrl' ⊆ ∅₂)
    (NRMWDEP : rmw_dep' ⊆ ∅₂)
    (RF : R' ∩₁ eq e ⊆₁ codom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘) ∪₁ cmt) :
  WCore.guided_step_gen cmt X' X delta_X e (lab' e).
Proof using.
  constructor; ins.
  { apply delta_add_event; ins. }
  constructor; ins.
  { apply delta_G_wf; ins. }
  { admit. }
  { apply XWF. }
  { unfold delta_E. rewrite set_inter_union_l.
    apply set_subset_union_l; split.
    { admit. }
    rewrite set_interC with (s := eq e).
    rewrite <- delta_lab_is_r; ins.
    all: try now unfold delta_E; basic_solver.
    rewrite RF, restr_set_union, !codom_union.
    basic_solver 12. }
  admit.
Admitted.

Lemma delta_G_sub
    (NOT_INIT : tid h <> tid_init)
    (WF : WCore.wf X)
    (IN : E' h)
    (NEW : ~E h)
    (SUB : sub_execution G' G ∅₂ ∅₂) :
  sub_execution G' delta_G ∅₂ ∅₂.
Proof using.
  assert (WF' : Wf G').
  { apply WF. }
  assert (SUBE : E ⊆₁ E').
  { apply SUB. }
  constructor; ins.
  all: try apply SUB.
  { unfolder. ins. desf. now apply SUB. }
  { rewrite (sub_rmw SUB), <- !restr_relE, restr_set_union.
    rewrite restr_irrefl_eq; eauto using rmw_irr.
    arewrite (⦗eq h⦘ ⨾ rmw' ⨾ ⦗E⦘ ≡ ∅₂); [| now rewrite !union_false_r].
    split; [|basic_solver]. unfolder; ins; desf.
    change G with (WCore.G X) in NEW.
    eapply NEW, ext_sb_dense; eauto; [apply WF |].
    enough (SB : sb' x y); try now apply wf_rmwi; ins.
    unfold sb in SB; unfolder in SB; desf. }
  { rewrite (WCore.wf_cc_data_empty WF).
    now rewrite seq_false_l, seq_false_r. }
  { rewrite (WCore.wf_cc_addr_empty WF).
    now rewrite seq_false_l, seq_false_r. }
  { rewrite (WCore.wf_cc_ctrl_empty WF).
    now rewrite seq_false_l, seq_false_r. }
  { rewrite (sub_rf SUB), <- !restr_relE, restr_set_union.
    erewrite restr_irrefl_eq, union_false_r; eauto using rf_irr. }
  { rewrite (sub_co SUB), <- !restr_relE, restr_set_union.
    erewrite restr_irrefl_eq, union_false_r; eauto using co_irr. }
    now rewrite seq_false_l, seq_false_r.
Qed.

Lemma delta_G_trace_prefix
    (HIN : E' h)
    (WF : WCore.wf X) :
  exec_trace_prefix G' delta_G.
Proof using.
  assert (SUBE : E ⊆₁ E') by now apply WF.
  unfold exec_trace_prefix; ins.
  destruct (classic (thr = (tid h))) as [HEQ|NEQ]; subst.
  { apply thread_actid_trace_prefix; ins.
    apply set_subset_inter; basic_solver. }
  unfold thread_actid_trace; ins.
  arewrite ((E ∪₁ eq h) ∩₁ (fun e => thr = tid e) ≡₁ E ∩₁ (fun e => thr = tid e)).
  { basic_solver. }
  apply (WCore.wf_trace_prefix WF).
Qed.

Lemma delta_G_cont_ids
    (HIN : E' h)
    (NIN : ~E h)
    (WF : WCore.wf X)
    (NEXT : forall x (IN_D : (E' \₁ E) x), ~ sb' x h) :
  contigious_actids delta_G.
Proof using.
  assert (NINIT : ~is_init h).
  { intro F. apply NIN, (WCore.wf_g_init WF). ins. }
  assert (NINIT' : tid h <> tid_init).
  { intro F. apply NINIT, (WCore.wf_gc_acts WF).
    unfolder. ins. }
  eapply add_event_to_contigious; eauto; ins.
  { apply WF. }
  intros x HSET.
  tertium_non_datur (is_init x) as [XINIT|XNIT]; [now right | left].
  tertium_non_datur (E x) as [XIN|NXIN].
  { split; ins.
    destruct ext_sb_tid_init with (x := x) (y := h); ins. }
  assert (XIN : E' x).
  { apply ext_sb_dense with (e2 := h); ins; try apply WF.
    unfold ext_sb in HSET. destruct x, h; ins; desf. }
  exfalso. apply NEXT with (x := x).
  all: unfold sb; unfolder; ins.
Qed.

Lemma delta_G_prefix
    (HIN : E' h)
    (NIN : ~E h)
    (NINIT : tid h <> tid_init)
    (WF : WCore.wf X)
    (NEXT : forall x (IN_D : (E' \₁ E) x), ~ sb' x h) :
  exec_prefix G' delta_G.
Proof using.
  constructor; try now apply WF.
  all: apply delta_G_sub || apply delta_G_cont_ids.
  all: auto; apply WF.
Qed.

Lemma delta_G_actid_trace_h
    (NOT_INIT : ~is_init h)
    (HIN : E' h)
    (NHIN : ~E h)
    (NEXT : forall x (IN_D : (E' \₁ E) x), ~ sb' x h)
    (WF : WCore.wf X)
    (WF_fin : WCore.wf X_fin) :
  thread_trace delta_G (tid h) =
    trace_app (thread_trace G (tid h)) (trace_fin [lab' h]).
Proof using.
  assert (NOT_INIT' : tid h <> tid_init) by eauto using WCore.wf_actid_tid.
  set (CONT := WCore.wf_g_cont WF NOT_INIT'). desf.
  arewrite (lab' = delta_G.(lab)) by symmetry; apply WF.
  eapply add_event_to_trace; eauto; ins.
  { now rewrite updI. }
  { now rewrite CONT, thread_seq_set_size. }
  { apply WF. }
  apply delta_G_cont_ids; auto; apply WF.
Qed.

Lemma delta_G_sb
    (HIN : E' h)
    (SUB : sub_execution G' G ∅₂ ∅₂) :
  get_sb delta_G ≡ sb ∪ (⦗E⦘ ⨾ sb' ⨾ ⦗eq h⦘) ∪ (⦗eq h⦘ ⨾ sb' ⨾ ⦗E⦘).
Proof using.
  assert (SUBE : E ⊆₁ E') by apply SUB.
  assert (SUBH : eq h ⊆₁ E') by now apply set_subset_eq.
  unfold delta_G, sb; ins.
  rewrite <- restr_relE, restr_set_union.
  rewrite restr_irrefl_eq; [rewrite union_false_r | apply ext_sb_irr].
  rewrite !restr_relE, !seq_absorb; ins.
Qed.

End DeltaGraph.

Section EnumeratedDifference.

Variable G G' : execution.
Variable sc : relation actid.
Variable cmt : actid -> Prop.
Variable traces : thread_id -> trace label -> Prop.

Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'W''" := (fun x => is_w lab' x).
Notation "'R''" := (fun x => is_r lab' x).

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'W'" := (fun x => is_w lab x).
Notation "'R'" := (fun x => is_r lab x).

Record enumd_diff (l : list actid) : Prop := {
  (* Actual enum properties *)
  nodup : NoDup l;
  diff_elems : E' \₁ E ≡₁ fun x => In x l;
  diff_sb : restr_rel (E' \₁ E) sb' ⊆ total_order_from_list l;
  diff_rf : restr_rel (E' \₁ E) (rf' ⨾ ⦗E' \₁ cmt⦘) ⊆ total_order_from_list l;
  diff_rf_d : (E' \₁ E) ∩₁ R ⊆₁ codom_rel rf';
}.

Notation "'X'" := ({|
  WCore.G := G;
  WCore.GC := G';
  WCore.sc := sc;
  WCore.cmt := cmt;
|}).
Notation "'X_fin'" := ({|
  WCore.G := G';
  WCore.GC := G';
  WCore.sc := sc;
  WCore.cmt := cmt;
|}).

Lemma enumd_elems_inter l
    (ENUM : enumd_diff l) :
  (fun x => In x l) ∩₁ E' ≡₁ (fun x => In x l).
Proof using.
  rewrite <- ENUM.(diff_elems l); basic_solver.
Qed.

Lemma enumd_head_most_sb h t
    (ENUM : enumd_diff (h :: t)) :
  forall x (IN_D : (E' \₁ E) x), ~ sb' x h.
Proof using.
  intros x IN_D SB.
  eapply list_min_elt; try now apply ENUM.
  apply ENUM.(diff_sb (h :: t)). unfolder; splits.
  all: try now apply IN_D.
  all: try now (apply ENUM.(diff_elems (h :: t)); desf).
  ins.
Qed.

Lemma diff_no_init l
    (WF : WCore.wf X)
    (ENUM : enumd_diff l) :
  E' \₁ E ⊆₁ set_compl is_init.
Proof.
  unfolder. intros x [INE' NOTINE] INIT.
  apply NOTINE, (WCore.wf_g_init WF); ins.
Qed.

Lemma enumd_deltaG_prefix h t
    (WF : WCore.wf X)
    (ENUM : enumd_diff (h :: t)) :
  exec_prefix G' (delta_G G G' h).
Proof using.
  assert (IN_D : (E' \₁ E) h).
  { by apply ENUM.(diff_elems (h :: t)). }
  eapply delta_G_prefix; eauto using enumd_head_most_sb.
  all: try now apply IN_D.
  intro F. enough (INIT : is_init h).
  { eapply diff_no_init; eauto. }
  apply (WCore.wf_gc_acts WF). unfolder. ins.
  split; auto; apply IN_D.
Qed.

Lemma enumd_deltaG_actid_trace_h h t
    (WF : WCore.wf X)
    (WFfin : WCore.wf X_fin)
    (ENUM : enumd_diff (h :: t)) :
  thread_trace (delta_G G G' h) (tid h) =
    trace_app (thread_trace G (tid h)) (trace_fin [lab' h]).
Proof using.
  assert (IN_D : (E' \₁ E) h).
  { by apply ENUM.(diff_elems (h :: t)). }
  eapply delta_G_actid_trace_h; eauto using enumd_head_most_sb.
  all: try apply IN_D.
  eapply diff_no_init; eauto.
Qed.

Lemma enumd_deltaG_new_event_correct h t
    (WF : WCore.wf X)
    (WF_fin : WCore.wf X_fin)
    (COH : trace_coherent traces G')
    (ENUM : enumd_diff (h :: t)) :
  WCore.new_event_correct traces X
  {|
    WCore.G := delta_G G G' h;
    WCore.GC := G';
    WCore.sc := sc;
    WCore.cmt := cmt;
  |} h.
Proof using.
  set (X' := {|
    WCore.G := delta_G G G' h;
    WCore.GC := G';
    WCore.sc := sc;
    WCore.cmt := cmt;
  |}).
  assert (IN_D : (E' \₁ E) h).
  { by apply ENUM.(diff_elems (h :: t)). }
  assert (NINIT : ~ is_init h).
  { eapply diff_no_init; eauto. }
  assert (NIRID : tid h <> tid_init).
  { intro F.
    eapply diff_no_init with (x := h) (l := h :: t); ins.
    apply (WCore.wf_gc_acts WF). unfolder; split; ins.
    apply IN_D. }
  assert (DCOH : trace_coherent traces (delta_G G G' h)).
  { eapply trace_coherent_sub; eauto.
    { eapply delta_G_trace_prefix; eauto. apply IN_D. }
    eapply delta_G_sub; eauto; try now apply WF.
    all: try now apply IN_D. }
  unfold WCore.new_event_correct. desf.
  { destruct (DCOH (tid h)) as (tr & INT & PREF); auto.
    exists tr; split; auto.
    replace (trace_fin (l ++ [(WCore.G X').(lab) h]))
       with (trace_app (trace_fin l) (trace_fin [lab' h])).
    { erewrite <- Heq, <- delta_G_actid_trace_h.
      all: eauto using enumd_head_most_sb.
      all: try now apply IN_D. }
    ins; do 3 f_equal. erewrite <- sub_lab; auto.
    apply WF. }
  set (FIN := WCore.all_trace_fin WF NIRID).
  ins. rewrite Heq in FIN. red in FIN. desf.
Qed.

Lemma enum_diff_done
    (WF : WCore.wf X)
    (DONE : enumd_diff []) :
  G = G'.
Proof using.
  apply sub_eq; try now apply WF.
  apply DONE.
Qed.

Lemma enum_diff_head_rf h t
    (NOT_INC : ~cmt h)
    (XWF : WCore.wf X)
    (ENUM : enumd_diff (h :: t)) :
  dom_rel (rf' ⨾ ⦗eq h⦘) ⊆₁ E.
Proof using.
  intros e (h' & h'' & RF & EQ & EQ'); subst h'' h'.
  tertium_non_datur (E e) as [INE|INE]; auto.
  exfalso. eapply list_min_elt; [apply ENUM|].
  apply ENUM.(diff_rf (h :: t)).
  unfolder; splits; eauto.
  all: try by apply ENUM.(diff_elems (h :: t)).
  apply wf_rfE in RF; [unfolder in RF; desf | apply XWF].
Qed.

End EnumeratedDifference.

Section SuBToFullExecCases.

Variable G G' : execution.
Variable sc : relation actid.
Variable cmt : actid -> Prop.
Variable traces : thread_id -> trace label -> Prop.
Variable h : actid.
Variable t : list actid.

Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'W''" := (fun x => is_w lab' x).
Notation "'R''" := (fun x => is_r lab' x).
Notation "'F''" := (fun x => is_f lab' x).

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'W'" := (fun x => is_w lab x).
Notation "'R'" := (fun x => is_r lab x).

Notation "'X'" := ({|
  WCore.G := G;
  WCore.GC := G';
  WCore.sc := sc;
  WCore.cmt := cmt;
|}).
Notation "'X''" := ({|
  WCore.G := delta_G G G' h;
  WCore.GC := G';
  WCore.sc := sc;
  WCore.cmt := cmt;
|}).
Notation "'X_fin'" := ({|
  WCore.G := G';
  WCore.GC := G';
  WCore.sc := sc;
  WCore.cmt := cmt;
|}).

(*
  Helper lemma to avoid proving WF-ness of new conf over and over.
  Especially because this part of the proof is independent of h's label
*)
Lemma X_prime_wf_helper
    (NIN : ~ E h)
    (HIN : E' h)
    (ENUM : enumd_diff G G' cmt (h :: t))
    (WF : WCore.wf X)
    (WF_fin : WCore.wf X_fin) :
  WCore.wf X'.
Proof using.
  constructor; ins; constructor; ins.
  all: try now (eapply enumd_deltaG_prefix; eauto).
  all: try rewrite delta_G_sb; auto.
  all: try now apply WF.
  all: try rewrite set_inter_union_r, restr_set_union.
  all: try rewrite restr_irr, union_false_r; auto using sb_irr.
  all: try rewrite !restr_relE.
  all: repeat apply union_mori; try apply seq_restr_helper.
  all: eauto using set_subset_inter_l, set_subset_inter_r.
  { eapply delta_G_cont_ids, enumd_head_most_sb; eauto. }
  { transitivity E; [apply WF | basic_solver]. }
  { erewrite sub_sb with (G := G') (G' := G); try now apply WF.
    apply seq_restr_helper; eauto using set_subset_inter_l,
                                        set_subset_inter_r. }
  { rewrite sub_rf with (G := G') (G' := G); try now apply WF.
    apply seq_restr_helper; eauto using set_subset_inter_l,
                                        set_subset_inter_r. }
  { apply rf_irr, WF. }
  rewrite set_inter_union_l, !codom_union.
  apply set_subset_union_l; split.
  { transitivity (codom_rel rf ∪₁ cmt); [apply WF |].
    apply set_subset_union_l; split.
    all: intros x HSET; unfold set_union; eauto. }
  intros h' (HEQH & IS_R); subst h'.
  tertium_non_datur (cmt h) as [CMT|NCMT].
  { now right. }
  destruct (WCore.wf_sub_rfD WF_fin) with (x := h) as [RF|CMT].
  all: ins; try now right.
  { split; ins; replace lab' with lab; [ins | apply WF]. }
  destruct RF as [w RF]. do 2 left. right.
  exists w. unfolder; splits; ins.
  eapply enum_diff_head_rf with (h := h); eauto.
  exists h. unfolder; eauto.
Qed.

(* Helper lemma to avoid copy-paste of equivalent cases *)
Lemma step_once_read_helper w
    (IN_D : (E' \₁ E) h)
    (NOT_INIT : ~is_init h)
    (H_TID : tid h <> tid_init)
    (IS_R : R' h)
    (WF : WCore.wf X)
    (WF' : WCore.wf X_fin)
    (ENUM : enumd_diff G G' cmt (h :: t))
    (RF : rf' w h)
    (COH : trace_coherent traces G')
    (INE : E w) :
  WCore.cfg_add_event_uninformative traces X X'.
Proof using.
  (* Information about h *)
  assert (IS_W : W' w).
  { apply wf_rfD in RF; [| apply WF].
    unfolder in RF; desf. }
  assert (NOT_W : ~W' h).
  { generalize IS_R; unfold is_w, is_r.
    destruct (lab' h); auto. }
  assert (H_IS_NW : W' h = false).
  { unfold is_w in *. desf. }
  (* Proof of step *)
  exists h, None, (Some w), ∅, ∅.
  splits; [constructor | constructor | |]; ins.
  { apply IN_D. }
  { unfold WCore.rf_delta_W. rewrite H_IS_NW.
    arewrite (singl_rel w h ∩ W' × R' ≡ singl_rel w h).
    { rewrite inter_absorb_r; ins.
      intros x y [EQ1 EQ2]; subst x y. red; eauto. }
    arewrite (⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘ ≡ singl_rel w h).
    { rewrite seq_restr_eq_prod; split; [| basic_solver].
      intros x y (RF' & INE' & HEQH); subst y. red; split; ins.
      eapply wf_rff with (G := G') (x := h); ins. apply WF. }
    repeat apply union_more; auto.
    split; [| basic_solver]. rewrite seq_restr_eq_prod; red.
    intros x y (RF' & INE' & HEQH); subst x.
    apply wf_rfD in RF'; [unfolder in RF'; desf | apply WF]. }
  { unfold WCore.co_delta. rewrite H_IS_NW.
    rewrite wf_coD with (G := G'); [basic_solver | apply WF]. }
  { unfold WCore.rmw_delta, W_ex.
    rewrite wf_rmwD with (G := G'); [basic_solver | apply WF]. }
  { eapply enumd_deltaG_new_event_correct; eauto. }
  apply X_prime_wf_helper; auto; apply IN_D.
Qed.

Lemma step_once_read
    (WF : WCore.wf X)
    (WF' : WCore.wf X_fin)
    (ENUM : enumd_diff G G' cmt (h :: t))
    (COH : trace_coherent traces G')
    (IS_R : R' h) :
  WCore.cfg_add_event_uninformative traces X X'.
Proof using.
  (* Information about h *)
  assert (IN_D : (E' \₁ E) h).
  { apply ENUM; desf. }
  assert (NOT_INIT : ~is_init h).
  { eapply diff_no_init with (G := G); eauto. }
  assert (H_TID : tid h <> tid_init).
  { eapply WCore.wf_actid_tid; eauto. apply IN_D. }
  assert (NOT_W : ~W' h).
  { generalize IS_R; unfold is_w, is_r.
    destruct (lab' h); auto. }
  assert (H_IS_NW : W' h = false).
  { unfold is_w in *. desf. }
  (* Case 1: cmt h *)
  tertium_non_datur (cmt h) as [CMT|NCMT].
  { (* Even if h is cmt -- we still need to add accompanying edges! *)
    tertium_non_datur (codom_rel (⦗E⦘ ⨾ rf') h) as [RF | NRF].
    { destruct RF as (w & w' & (EQ & INE) & RF); subst w'.
      eapply step_once_read_helper; eauto. }
    exists h, None, None, ∅, ∅.
    splits; [constructor | constructor | |]; ins.
    { apply IN_D. }
    { unfold WCore.rf_delta_W. rewrite H_IS_NW.
      arewrite (⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘ ≡ ∅₂).
      { split; [| basic_solver].
        rewrite seq_restr_eq_prod. intros x y (RF & INE' & HISH).
        subst y. apply NRF. unfolder. eauto. }
      repeat apply union_more; auto.
      rewrite wf_rfD; [basic_solver | apply WF]. }
    { unfold WCore.co_delta. rewrite H_IS_NW.
      rewrite wf_coD with (G := G'); [basic_solver | apply WF]. }
    { unfold WCore.rmw_delta, W_ex.
      rewrite wf_rmwD with (G := G'); [basic_solver| apply WF]. }
    { eapply enumd_deltaG_new_event_correct; eauto. }
    apply X_prime_wf_helper; eauto; apply IN_D. }
  (* Case 2: ~cmt h *)
  edestruct (WCore.wf_sub_rfD WF') as [[w RF] | CMT']; ins.
  { ins. split; eauto. apply IN_D. }
  all: ins.
  eapply step_once_read_helper; eauto.
  eapply enum_diff_head_rf; eauto.
  unfolder; exists h, h; now splits.
Qed.

Lemma step_once_write_rmw_helper e
    (WF : WCore.wf X)
    (RMW : rmw' e h)
    (IS_R : R' e)
    (ENUM : enumd_diff G G' cmt (h :: t))
    (HTID : tid h <> tid_init) :
  E e.
Proof using.
  apply wf_rmwi, immediate_in in RMW; [| apply WF].
  assert (E_NINIT : ~is_init e).
  { intro F; destruct e as [l | tide ide]; auto.
    unfold is_r in IS_R; rewrite wf_init_lab in IS_R; auto.
    apply WF. }
  assert (SAME_TID : tid e = tid h).
  { apply sb_tid_init in RMW; desf. }
  unfold sb in RMW. unfolder in RMW; desf.
  assert (IN_D : (E' \₁ E) h).
  { apply ENUM; desf. }
  destruct (WCore.wf_g_cont WF HTID) as [N HEQ].
  erewrite added_event_to_contigious with (G' := delta_G G G' h)
                                          (N := N) (G := G) in RMW0.
  all: ins; try now apply IN_D.
  { destruct e as [el | etid eid]; ins; desf; ins.
    now apply HEQ, thread_set_iff. }
  { now rewrite HEQ, thread_seq_set_size. }
  { apply WF. }
  eapply delta_G_cont_ids; eauto; try now apply IN_D.
  eapply enumd_head_most_sb; eauto.
Qed.

Lemma step_once_write_helper
    (WF : WCore.wf X)
    (NIN : ~E h) :
  ⦗eq h⦘ ⨾ rf' ⨾ ⦗E⦘ ≡ ⦗eq h⦘ ⨾ rf' ⨾ ⦗cmt ∩₁ E⦘.
Proof using.
  split; [| basic_solver].
  unfolder. intros h' r (EQ & RF & INE); subst h'.
  assert (IS_R : R r).
  { replace lab with lab' by (symmetry; apply WF).
    apply wf_rfD in RF; [unfolder in RF; desf | apply WF]. }
  assert (SUBRF : rf ⊆ rf').
  { rewrite sub_rf with (G := G'); [basic_solver | apply WF]. }
  splits; auto.
  edestruct (WCore.wf_sub_rfD WF) as [RF'|CMT]; eauto; ins.
  destruct RF' as [h' RF']. exfalso. apply NIN.
  erewrite wf_rff with (G := G') (x := r)
                       (y := h) (z := h').
  all: try now (red; eauto) || now apply WF.
  apply wf_rfE in RF'; [unfolder in RF'; desf | apply (WCore.wf_g WF)].
Qed.

(* FIXME: this proof contains a lot of copy-paste *)
Lemma step_once_write
    (WF : WCore.wf X)
    (WF' : WCore.wf X_fin)
    (ENUM : enumd_diff G G' cmt (h :: t))
    (COH : trace_coherent traces G')
    (IS_W : W' h) :
  WCore.cfg_add_event_uninformative traces X X'.
Proof using.
  (* Information about h *)
  set (W1 := codom_rel (⦗eq h⦘ ⨾ co' ⨾ ⦗E⦘)).
  set (W2 := dom_rel (⦗E⦘ ⨾ co' ⨾ ⦗eq h⦘)).
  assert (IN_D : (E' \₁ E) h).
  { apply ENUM; desf. }
  assert (NOT_INIT : ~is_init h).
  { eapply diff_no_init with (G := G); eauto. }
  assert (H_TID : tid h <> tid_init).
  { eapply WCore.wf_actid_tid; eauto. apply IN_D. }
  assert (NOT_R : ~R' h).
  { generalize IS_W; unfold is_w, is_r. destruct (lab' h); auto. }
  assert (NRF_TO_H : ⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘ ≡ ∅₂).
  { rewrite wf_rfD; [basic_solver | apply WF]. }
  assert (HIDCO_L : ⦗eq h⦘ ⨾ co' ⨾ ⦗E⦘ ≡ eq h × codom_rel (⦗eq h⦘ ⨾ co' ⨾ ⦗E⦘)).
  { basic_solver 5. }
  assert (HIDCO_R : ⦗E⦘ ⨾ co' ⨾ ⦗eq h⦘ ≡ dom_rel (⦗E⦘ ⨾ co' ⨾ ⦗eq h⦘) × eq h).
  { basic_solver 5. }

  (* Case 1: h is part of an RMW *)
  (* Case 2: no rmw *)
  tertium_non_datur (codom_rel rmw' h) as [[r RMW] | NRMW];
    [exists h, (Some r), None, W1, W2 | exists h, None, None, W1, W2].
  all: subst W1 W2.
  all: splits; [constructor | constructor | |]; ins.
  all: try now apply IN_D.
  all: try now (eapply enumd_deltaG_new_event_correct; eauto).
  all: try now (apply X_prime_wf_helper; eauto; apply IN_D).
  all: try (unfold WCore.rf_delta_W, WCore.co_delta; rewrite IS_W).
  all: try now (rewrite step_once_write_helper, NRF_TO_H; try now apply IN_D).
  all: try now (rewrite unionA, unionC with (r1 := eq h × _);
                now repeat apply union_more).
  { assert (RIS_R : R' r).
    { apply wf_rmwD in RMW; [unfolder in RMW; desf | apply WF]. }
    assert (RIN_E : E r).
    { apply step_once_write_rmw_helper; ins. }
    apply union_more; auto. unfold WCore.rmw_delta, eq_opt, W_ex.
    split; [| basic_solver]. rewrite seq_restr_eq_prod.
    intros x y (RMW' & INE & Y_EQ_H); subst y.
    rewrite wf_rmwff with (G := G') (x := h) (y := x) (z := r).
    all: ins.
    apply WF. }
  apply union_more; auto. unfold WCore.rmw_delta, eq_opt, W_ex.
  split; [| basic_solver]. rewrite seq_restr_eq_prod.
  intros x y (RMW' & INE & Y_EQ_H); subst y. exfalso.
  apply NRMW. red. eauto.
Qed.

Lemma step_once_fence
    (WF : WCore.wf X)
    (WF' : WCore.wf X_fin)
    (ENUM : enumd_diff G G' cmt (h :: t))
    (COH : trace_coherent traces G')
    (IS_F : F' h) :
  WCore.cfg_add_event_uninformative traces X X'.
Proof using.
  (* Information about h *)
  assert (IN_D : (E' \₁ E) h).
  { apply ENUM; desf. }
  assert (NOT_INIT : ~is_init h).
  { eapply diff_no_init with (G := G); eauto. }
  assert (H_TID : tid h <> tid_init).
  { eapply WCore.wf_actid_tid; eauto. apply IN_D. }
  assert (NOT_R : ~R' h).
  { generalize IS_F; unfold is_f, is_r.
    destruct (lab' h); auto. }
  assert (NOT_W : ~W' h).
  { generalize IS_F; unfold is_f, is_w.
    destruct (lab' h); auto. }
  assert (HIS_NW : is_w lab' h = false).
  { unfold is_w in *. desf. }

  exists h, None, None, ∅, ∅.
  splits; [constructor | constructor | |]; ins.
  { apply IN_D. }
  { apply union_more; [apply union_more; auto |].
    { rewrite wf_rfD; [basic_solver | apply WF]. }
    unfold WCore.rf_delta_W. rewrite HIS_NW.
    rewrite wf_rfD; [basic_solver | apply WF]. }
  { unfold WCore.co_delta. rewrite HIS_NW.
    rewrite unionA. apply union_more; ins.
    rewrite wf_coD; try now apply WF.
    basic_solver. }
  { apply union_more; auto. unfold WCore.rmw_delta.
    rewrite wf_rmwD; try now apply WF.
    basic_solver. }
  { eapply enumd_deltaG_new_event_correct; eauto. }
  apply X_prime_wf_helper; eauto; apply IN_D.
Qed.

Lemma step_once
    (WF : WCore.wf X)
    (WF' : WCore.wf X_fin)
    (ENUM : enumd_diff G G' cmt (h :: t))
    (COH : trace_coherent traces G') :
  WCore.cfg_add_event_uninformative traces X X'.
Proof using.
  set (LAB := lab_rwf lab' h); desf.
  { eapply step_once_read; eauto. }
  { eapply step_once_write; eauto. }
  eapply step_once_fence; eauto.
Qed.

End SuBToFullExecCases.

End SubToFullExecInternal.

Section SubToFullExec.

Variable traces : thread_id -> trace label -> Prop.

Lemma sub_to_full_exec_end_wf sc G G' cmt l
    (WF : WCore.wf (WCore.Build_t sc G G' cmt))
    (ENUM : SubToFullExecInternal.enumd_diff G G' cmt l) :
  WCore.wf (WCore.Build_t sc G' G' cmt).
Proof using.
  assert (SUB : sub_execution G' G ∅₂ ∅₂).
  { apply WF. }
  assert (EQLAB : lab G' = lab G).
  { symmetry. apply SUB. }
  assert (WF_G' : Wf G').
  { apply WF. }
  split.
  { constructor; ins.
    all: try now apply WF.
    basic_solver. }
  constructor; ins.
  all: try now apply WF.
  { constructor; ins.
    all: try now apply WF_G'.
    { now apply wf_rmwE. }
    { now apply wf_dataE. }
    { now apply wf_addrE. }
    { now apply wf_ctrlE. }
    { now apply wf_rmw_depE. }
    basic_solver. }
  { basic_solver. }
  { basic_solver. }
  { intros x (INE' & IS_R).
    destruct (classic (acts_set G x)) as [INE|NINE].
    { apply set_subset_single_l.
      transitivity (codom_rel (rf G) ∪₁ cmt).
      { apply set_subset_eq, WF. split; ins.
        now rewrite <- EQLAB. }
      rewrite (sub_rf SUB). basic_solver. }
    destruct (classic (cmt x)) as [CMT|NCMT].
    { now right. }
    left. apply (SubToFullExecInternal.diff_rf_d ENUM).
    unfolder; splits; ins.
    now rewrite <- EQLAB. }
  rewrite EQLAB. apply WF.
Qed.

Lemma sub_to_full_exec sc G G' cmt l
    (WF : WCore.wf (WCore.Build_t sc G G' cmt))
    (ENUM : SubToFullExecInternal.enumd_diff G G' cmt l)
    (COH : trace_coherent traces G') :
  (WCore.cfg_add_event_uninformative traces)＊
    (WCore.Build_t sc G G' cmt)
    (WCore.Build_t sc G' G' cmt).
Proof using.
  assert (WF' : WCore.wf (WCore.Build_t sc G' G' cmt)).
  { eauto using sub_to_full_exec_end_wf. }
  generalize G WF ENUM.
  clear      G WF ENUM.
  induction l as [ | h t IHl]; ins.
  { arewrite (G = G'); [| apply rt_refl].
    eapply SubToFullExecInternal.enum_diff_done; eauto. }
  set (delta_G := SubToFullExecInternal.delta_G G G' h).
  assert (STEP : WCore.cfg_add_event_uninformative traces
    (WCore.Build_t sc       G                G' cmt)
    (WCore.Build_t sc delta_G                G' cmt)).
  { eapply SubToFullExecInternal.step_once; eauto. }
  eapply rt_trans; [apply rt_step; eauto | ].
  red in STEP; desf.
  apply IHl; [eapply WCore.cae_wf; eauto |].
  constructor; ins.
  { eapply nodup_consD, ENUM. }
  { rewrite set_minus_union_r, SubToFullExecInternal.diff_elems,
            set_inter_minus_r, SubToFullExecInternal.enumd_elems_inter.
    all: eauto.
    ins; split; [basic_solver |].
    unfolder; ins; splits; eauto. intro F; subst.
    eapply nodup_cons; [apply ENUM | ins]. }
  { intros x y SB. unfolder in SB; desf.
    assert (LT : total_order_from_list (h :: t) x y).
    { eapply SubToFullExecInternal.diff_sb; unfolder; splits; ins; eauto. }
    apply total_order_from_list_cons in LT; desf.
    exfalso; eauto. }
  { intros x y RF. unfolder in RF; desf.
    assert (LT : total_order_from_list (h :: t) x y).
    { eapply SubToFullExecInternal.diff_rf; unfolder; splits; ins; eauto. }
    apply total_order_from_list_cons in LT; desf.
    exfalso; eauto. }
  rewrite set_minus_union_r.
  rewrite <- (SubToFullExecInternal.diff_rf_d ENUM).
  basic_solver.
Qed.

Lemma enumd_diff_listless  sc G G' cmt thrdle
    (WF : WCore.wf {|
      WCore.sc := sc;
      WCore.G := G;
      WCore.GC := G';
      WCore.cmt := cmt
    |})
    (ACYC : acyclic thrdle)
    (RFCO : acts_set G' ∩₁ is_r (lab G) ⊆₁ codom_rel (rf G'))
    (INITLEAST : least_elt thrdle tid_init)
    (MININIT : wmin_elt thrdle tid_init)
    (ORDRF : (rf G' ⨾ ⦗acts_set G' \₁ cmt⦘) ∩ compl_rel same_tid
            ⊆ tid ↓ thrdle)
    (ORDRFI :
      restr_rel (acts_set G' \₁ acts_set G) (
          (rf G' ⨾ ⦗acts_set G' \₁ cmt⦘)
      ) ∩ same_tid ⊆ sb G') :
  exists l,
    SubToFullExecInternal.enumd_diff G G' cmt l.
Proof using.
  assert (FIN : set_finite (acts_set G' \₁ acts_set G)).
  { arewrite (acts_set G' \₁ acts_set G ⊆₁ acts_set G' \₁ is_init).
    all: try now apply (WCore.wf_gc_fin_exec WF).
    unfolder. intros x (INE' & NINE). split; ins.
    intro INI. apply NINE, (WCore.wf_g_init WF); ins. }
  assert (FULL_SUB : restr_rel (acts_set G' \₁ acts_set G)
                               (rf G' ⨾ ⦗acts_set G' \₁ cmt⦘)
                     ⊆ tid ↓ thrdle⁺ ∪ sb G').
  { arewrite (rf G' ⨾ ⦗acts_set G' \₁ cmt⦘ ≡
              (rf G' ⨾ ⦗acts_set G' \₁ cmt⦘) ∩ ⊤₂).
    { basic_solver. }
    arewrite (⊤₂ ≡ compl_rel same_tid ∪ same_tid).
    { split; [| basic_solver].
      rewrite unionC. unfolder; eauto using classic. }
    rewrite inter_union_r, restr_union, ORDRF,
            !restr_inter, !inter_restr_absorb_r,
            ORDRFI.
    basic_solver. }
  apply set_finiteE in FIN. destruct FIN as (l' & NODUP & EQ).
  destruct partial_order_included_in_total_order
    with actid (tid ↓ thrdle⁺ ∪ sb G')
    as (tord & SUB & TOT).
  { red. split.
    { apply irreflexive_union; split; [| apply sb_irr].
      unfolder. ins. eapply ACYC; eauto. }
    unfolder. intros x y z R1 R2. desf.
    { left. eapply t_trans; eauto. }
    { unfold sb, ext_sb in *. unfolder in R1.
      all: ins; do 2 desf; eauto. }
    { unfold sb, ext_sb in *. unfolder in R2.
      all: ins; do 2 desf; eauto.
      left. apply wmin_elt_t in MININIT.
      ins. apply MININIT in R1. rewrite <- R1.
      basic_solver. }
    right. now apply sb_trans with y. }
  exists (isort tord l'). constructor; ins.
  { apply NoDup_StronglySorted with tord.
    { apply TOT. }
    apply StronglySorted_isort; ins. }
  { rewrite EQ. unfolder; split.
    all: intro; apply in_isort_iff. }
  { rewrite total_order_from_isort, <- EQ, <- SUB; ins.
    basic_solver. }
  { rewrite total_order_from_isort, <- EQ, <- SUB; ins.
    rewrite <- FULL_SUB. basic_solver. }
  rewrite <- RFCO. basic_solver.
Qed.

Lemma sub_to_full_exec_listless sc G G' cmt thrdle
    (WF : WCore.wf (WCore.Build_t sc G G' cmt))
    (COH : trace_coherent traces G')
    (STABLE : WCore.stable_uncmt_reads_gen G' cmt thrdle)
    (RFCO : acts_set G' ∩₁ is_r (lab G) ⊆₁ codom_rel (rf G'))
    (ORDRFI :
      restr_rel (acts_set G' \₁ acts_set G) (
          (rf G' ⨾ ⦗acts_set G' \₁ cmt⦘)
      ) ∩ same_tid ⊆ sb G') :
  (WCore.cfg_add_event_uninformative traces)＊
    (WCore.Build_t sc G G' cmt)
    (WCore.Build_t sc G' G' cmt).
Proof using.
  destruct (enumd_diff_listless) with sc G G' cmt thrdle
                                 as (l & ENUM).
  all: ins; try now apply STABLE.
  apply sub_to_full_exec with l; ins.
Qed.

Lemma sub_to_full_exec_single_uninformative sc G G' cmt e
    (NOTIN : ~acts_set G e)
    (ONE : acts_set G' ≡₁ acts_set G ∪₁ eq e)
    (WF : WCore.wf (WCore.Build_t sc G G' cmt))
    (COH : trace_coherent traces G')
    (RF_EX : eq e ∩₁ is_r (lab G) ⊆₁ codom_rel (rf G')) :
  (WCore.cfg_add_event_uninformative traces)＊
    (WCore.Build_t sc G G' cmt)
    (WCore.Build_t sc G' G' cmt).
Proof using.
  assert (DIFFEQ : acts_set G' \₁ acts_set G ≡₁ eq e).
  { rewrite ONE, set_minus_union_l, set_minusK,
            set_minusE, set_inter_absorb_r.
    all: basic_solver. }
  apply sub_to_full_exec with (l := [e]); ins.
  constructor; ins.
  all: rewrite ?DIFFEQ; ins.
  { basic_solver. }
  { rewrite restr_irrefl_eq; [basic_solver |].
    apply sb_irr. }
  rewrite restr_irrefl_eq; [basic_solver |].
  apply irreflexive_inclusion with (r' := rf G'); [basic_solver |].
  apply rf_irr, WF.
Qed.

Lemma events_after_steps X X'
    (STEP : (WCore.cfg_add_event_uninformative traces)＊ X X') :
  acts_set (WCore.G X) ⊆₁ acts_set (WCore.G X').
Proof using.
  induction STEP as [X X' STEP | X | X X'' X' STEP1 SUB1 STEP2 SUB2].
  { do 2 (red in STEP; desf).
    rewrite (WCore.caes_e_new STRUCT).
    basic_solver. }
  all: basic_solver.
Qed.

Lemma sub_to_full_exec_single sc G G' cmt e
    (NOTIN : ~acts_set G e)
    (ONE : acts_set G' ≡₁ acts_set G ∪₁ eq e)
    (WF : WCore.wf (WCore.Build_t sc G G' cmt))
    (COH : trace_coherent traces G')
    (RF_EX : eq e ∩₁ is_r (lab G) ⊆₁ codom_rel (rf G')) :
  WCore.cfg_add_event traces
    (WCore.Build_t sc G G' cmt)
    (WCore.Build_t sc G' G' cmt)
    e.
Proof using.
  (* Preamble *)
  assert (STEPS : (WCore.cfg_add_event_uninformative traces)＊
                    (WCore.Build_t sc G G' cmt)
                    (WCore.Build_t sc G' G' cmt)).
  { eapply sub_to_full_exec_single_uninformative; eauto. }
  (* Actual proof *)
  apply clos_rt_rt1n in STEPS.
  inversion STEPS as [EQ | X' X'' STEP1 STEP2 EQ]; clear STEPS.
  all: subst.
  { exfalso. apply NOTIN, ONE. basic_solver. }
  destruct STEP1 as [e1 STEP1].
  inversion STEP2 as [EQ | X'' X''' STEP21 STEP22 EQ]; clear STEP2.
  all: subst.
  { arewrite (e = e1); ins.
    assert (NOTIN' : ~acts_set G e1).
    { apply (WCore.cae_e_notin STEP1). }
    rewrite (WCore.cae_e_new STEP1) in ONE. ins.
    unfolder in ONE. destruct ONE as (ONE1 & ONE2).
    destruct ONE1 with e1; eauto. exfalso; eauto. }
  destruct STEP21 as [e2 STEP21].
  (* We are going to infer falsity but first -- some useful props *)
  assert (NEQ : e1 <> e2).
  { intro F; subst.
    apply (WCore.cae_e_notin STEP21).
    apply (WCore.cae_e_new STEP1).
    basic_solver. }
  assert (E1NOTIN : ~acts_set G e1).
  { apply (WCore.cae_e_notin STEP1). }
  assert (E2NOTIN : ~acts_set G e2).
  { intro F. apply (WCore.cae_e_notin STEP21).
    apply (WCore.cae_e_new STEP1). ins.
    unfolder. eauto. }
  assert (ESUB : acts_set (WCore.G X'') ⊆₁ acts_set G').
  { apply clos_rt1n_rt in STEP22.
    now eapply events_after_steps with (X' := {|
      WCore.sc := sc;
      WCore.G := G';
      WCore.GC := G';
      WCore.cmt := cmt
    |}). }
  (* The proof *)
  exfalso.
  rewrite (WCore.cae_e_new STEP21), (WCore.cae_e_new STEP1) in ESUB.
  ins. destruct ONE as [SUBE _]. rewrite <- ESUB in SUBE.
  apply NEQ. unfolder in SUBE.
  destruct SUBE with e1; eauto; [exfalso; eauto |].
  destruct SUBE with e2; eauto; [exfalso; eauto |].
  congruence.
Qed.

End SubToFullExec.