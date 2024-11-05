Require Import Lia Setoid Program.Basics.
Require Import AuxDef HahnTotalListEx AuxRel. (* needs wf_rmwff *)
Require Import ExecEquiv.
Require Import Core AddEventWf.
Require Import Thrdle.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.

Set Implicit Arguments.

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
Notation "'same_loc''" := (same_loc lab').
Notation "'same_val''" := (same_val lab').

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
Notation "'same_loc'" := (same_loc lab).
Notation "'same_val'" := (same_val lab).

Record prefix : Prop := {
  prf_init : is_init ⊆₁ E;
  prf_acts : E ⊆₁ E';
  prf_threads : threads_set ≡₁ threads_set';
  prf_lab : eq_dom (is_init ∪₁ E) lab lab';
  prf_lab_extra : eq_dom (set_compl E') lab lab';
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

Lemma prefix_full_G
    (WF : Wf G')
    (PFX : prefix)
    (FULL : E ≡₁ E') :
  G = G'.
Proof using.
  apply exeeqv_eq. constructor; ins.
  { apply PFX. }
  { apply eq_dom_full_eq. rewrite set_full_split with (S := E').
    apply eq_dom_union. split; [| apply PFX].
    rewrite <- FULL. eapply eq_dom_mori, PFX.
    all: ins.
    unfold flip. basic_solver. }
  { symmetry. rewrite (prf_rmw PFX), FULL, restr_relE.
    apply (wf_rmwE WF). }
  { apply (prf_data PFX). }
  { apply (prf_addr PFX). }
  { apply (prf_ctrl PFX). }
  { apply (prf_rmw_dep PFX). }
  { symmetry. rewrite (prf_rf PFX), FULL, restr_relE.
    apply (wf_rfE WF). }
  symmetry. rewrite (prf_co PFX), FULL, restr_relE.
  apply (wf_coE WF).
Qed.

Lemma prefix_full_sc
    (WF : xmm_s.wf_sc G' sc')
    (PFX : prefix)
    (FULL : E ≡₁ E') :
  sc = sc'.
Proof using.
  apply rel_extensionality.
  rewrite (prf_sc PFX), restr_relE, FULL.
  symmetry. apply WF.
Qed.

Lemma prf_sb'
    (PFX : prefix) :
  sb ≡ restr_rel E sb'.
Proof using.
  unfold sb. rewrite restr_relE, !seqA.
  seq_rewrite <- !id_inter.
  rewrite set_inter_absorb_r, set_inter_absorb_l.
  all: try now apply PFX.
  ins.
Qed.

Lemma prefix_wf
    (NDATA : data ≡ ∅₂)
    (NADDR : addr ≡ ∅₂)
    (NCTRL : ctrl ≡ ∅₂)
    (NRMWDEP : rmw_dep ≡ ∅₂)
    (WF : Wf G')
    (PFX : prefix) :
  Wf G.
Proof using.
  assert (SUBE : E ⊆₁ E') by apply PFX.
  assert (EQR : E ∩₁ R' ≡₁ E ∩₁ R).
  { unfolder. split; ins; desf.
    all: split; ins; unfold is_r in *.
    all: rewrite (prf_lab PFX) in *; ins.
    all: now right. }
  assert (EQW : E ∩₁ W' ≡₁ E ∩₁ W).
  { unfolder. split; ins; desf.
    all: split; ins; unfold is_w in *.
    all: rewrite (prf_lab PFX) in *; ins.
    all: now right. }
  assert (EQL : restr_rel E same_loc' ⊆ same_loc).
  { unfolder. ins; desf.
    unfold same_loc, loc in *.
    rewrite !(prf_lab PFX) in *; ins.
    all: now right. }
  assert (EQV : restr_rel E same_val' ⊆ same_val).
  { unfolder. ins; desf.
    unfold same_val, val in *.
    rewrite !(prf_lab PFX) in *; ins.
    all: now right. }
  constructor.
  { intros a b (INA & INB & NEQ & TID & NINIT).
    apply WF. splits; ins.
    all: now apply (prf_acts PFX). }
  { rewrite NDATA. basic_solver. }
  { rewrite NDATA. basic_solver. }
  { rewrite NADDR. basic_solver. }
  { rewrite NADDR. basic_solver. }
  { rewrite NCTRL. basic_solver. }
  { rewrite NCTRL. basic_solver. }
  { rewrite NCTRL. basic_solver. }
  { rewrite (prf_rmw PFX). rewrite (wf_rmwD WF) at 1.
    rewrite !restr_relE, !seqA. seq_rewrite <- !id_inter.
    rewrite EQR, set_interC with (s' := E), EQW.
    basic_solver. }
  { rewrite <- EQL, (prf_rmw PFX).
    apply restr_rel_mori; ins. apply WF. }
  { rewrite (prf_rmw PFX), (wf_rmwi WF), (prf_sb' PFX).
    unfolder. ins; desf. split; ins. desf; eauto. }
  { rewrite (prf_rf PFX). rewrite (wf_rfE WF) at 1.
    rewrite !restr_relE, !seqA. seq_rewrite <- !id_inter.
    basic_solver 11. }
  { rewrite (prf_rf PFX). rewrite (wf_rfD WF) at 1.
    rewrite !restr_relE, !seqA. seq_rewrite <- !id_inter.
    rewrite EQW, set_interC with (s' := E), EQR.
    basic_solver. }
  { rewrite <- EQL, (prf_rf PFX).
    apply restr_rel_mori; ins. apply WF. }
  { enough (rf ⊆ same_val); ins.
    rewrite <- EQV, (prf_rf PFX).
    apply restr_rel_mori; ins. apply WF. }
  { rewrite (prf_rf PFX), <- restr_transp.
    apply functional_restr, WF. }
  { rewrite (prf_co PFX). rewrite (wf_coE WF) at 1.
    rewrite !restr_relE, !seqA. seq_rewrite <- !id_inter.
    basic_solver 11. }
  { rewrite (prf_co PFX). rewrite (wf_coD WF) at 1.
    rewrite !restr_relE, !seqA. seq_rewrite <- !id_inter.
    rewrite EQW, set_interC with (s' := E), EQW.
    basic_solver. }
  { rewrite <- EQL, (prf_co PFX).
    apply restr_rel_mori; ins. apply WF. }
  { rewrite (prf_co PFX). apply transitive_restr, WF. }
  { intros ol. rewrite (prf_co PFX). unfolder.
    intros x ((XINE & XISW) & XLOC).
    intros y ((YINE & YISW) & YLOC).
    intros NEQ.
    destruct (wf_co_total WF) with ol x y as [CO|CO].
    all: eauto.
    all: unfolder; splits; eauto.
    all: unfold is_w, loc; rewrite <- (prf_lab PFX).
    all: ins.
    all: now right. }
  { rewrite (prf_co PFX). apply irreflexive_restr, WF. }
  { ins; desf. now apply (prf_init PFX). }
  { ins; desf. rewrite (prf_lab PFX); [| now left].
    apply WF. }
  { rewrite NRMWDEP. basic_solver. }
  { rewrite NRMWDEP. basic_solver. }
  ins. apply (prf_acts PFX) in EE.
  now apply (prf_threads PFX), WF.
Qed.

End Prefix.

Module SubToFullExecInternal.

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
Notation "'Loc_'' l" := (fun e => loc lab' e = l) (at level 1).

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

Lemma delta_G_dom
    (NOTINE : ~ E e)
    (PFX : prefix X X') :
  eq_dom (E ∪₁ eq e) lab' delta_lab.
Proof using.
  apply eq_dom_union. split.
  { unfolder. unfold delta_lab. ins.
    rupd; [|congruence]. rewrite (prf_lab PFX); ins.
    basic_solver. }
  unfold delta_lab. unfolder. ins. desf. now rupd.
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
  { unfolder. intros x XIN. rupd; [| congruence].
    now apply (prf_lab_extra PFX). }
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

Lemma delta_add_event
    (NTID : tid e <> tid_init)
    (INE : E' e)
    (NOTINE : ~ E e)
    (NINIT : ~ is_init e)
    (WF : Wf G')
    (PFX : prefix X X')
    (EMAX : ⦗eq e⦘ ⨾ sb' ⨾ ⦗E⦘ ⊆ ∅₂)
    (NCTRL : ctrl' ⊆ ∅₂) :
  WCore.add_event X delta_X e (lab' e).
Proof using.
  red.
  assert (EINDE : eq e ⊆₁ delta_E).
  { unfold delta_E. basic_solver. }
  assert (EINE : E ⊆₁ delta_E).
  { unfold delta_E. basic_solver. }
  assert (DEINE : delta_E ⊆₁ E').
  { unfold delta_E. apply set_subset_union_l.
    split; [apply PFX | basic_solver]. }
  assert (RMW : exists r,
    ⦗E⦘ ⨾ rmw' ⨾ ⦗eq e⦘ ≡ eq_opt r × eq e
  ).
  { destruct (classic (⦗E⦘ ⨾ rmw' ⨾ ⦗eq e⦘ ≡ ∅₂)) as [EMPTY|NEN].
    { exists None. rewrite EMPTY. basic_solver. }
    assert (NEN' : ~dom_rel (⦗E⦘ ⨾ rmw' ⨾ ⦗eq e⦘) ≡₁ ∅).
    { intros EMP. apply NEN. split; [| basic_solver].
      intros x y HREL. eapply EMP with x. basic_solver. }
    apply set_nonemptyE in NEN'. destruct NEN' as (r & HIN).
    exists (Some r). split; [| unfolder in *; ins; desf].
    unfolder. intros x y (HIN' & RMW & HEQ). subst y.
    split; ins. eapply (wf_rmwff WF); eauto.
    unfold transp. unfolder in HIN. desf. }
  assert (RF : exists w,
    ⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘ ≡ eq_opt w × eq e
  ).
  { destruct (classic (⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘ ≡ ∅₂)) as [EMPTY|NEN].
    { exists None. rewrite EMPTY. basic_solver. }
    assert (NEN' : ~dom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘) ≡₁ ∅).
    { intros EMP. apply NEN. split; [| basic_solver].
      intros x y HREL. eapply EMP with x. basic_solver. }
    apply set_nonemptyE in NEN'. destruct NEN' as (r & HIN).
    exists (Some r). split; [| unfolder in *; ins; desf].
    unfolder. intros x y (HIN' & RF & HEQ). subst y.
    split; ins. eapply (wf_rff WF); eauto.
    unfold transp. unfolder in HIN. desf. }
  destruct RMW as (r & RMW), RF as (w & RF).
  assert (EQLAB : eq_dom E lab lab').
  { eapply eq_dom_mori with (x := is_init ∪₁ E); eauto.
    { unfold flip. basic_solver. }
    apply PFX. }
  assert (SWE : eq_opt w ⊆₁ E).
  { arewrite (eq_opt w ⊆₁ dom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘)).
    { rewrite RF. basic_solver. }
    basic_solver. }
  assert (SRE : eq_opt r ⊆₁ E).
  { arewrite (eq_opt r ⊆₁ dom_rel (⦗E⦘ ⨾ rmw' ⨾ ⦗eq e⦘)).
    { rewrite RMW. basic_solver. }
    basic_solver. }
  assert (W1E : codom_rel (⦗eq e⦘ ⨾ co' ⨾ ⦗E⦘) ⊆₁ E).
  { basic_solver. }
  assert (W2E : dom_rel (⦗E⦘ ⨾ co' ⨾ ⦗eq e⦘) ⊆₁ E).
  { basic_solver. }
  assert (R1E : codom_rel (⦗eq e⦘ ⨾ rf' ⨾ ⦗E⦘) ⊆₁ E).
  { basic_solver. }
  (* The proof *)
  exists r,
         (codom_rel (⦗eq e⦘ ⨾ rf' ⨾ ⦗E⦘    )),
         w,
         (codom_rel (⦗eq e⦘ ⨾ co' ⨾ ⦗E⦘    )),
         (dom_rel   (   ⦗E⦘ ⨾ co' ⨾ ⦗eq e⦘ )).
  constructor; ins.
  all: try now (symmetry; apply PFX).
  { apply eq_dom_is_w with (lab := lab').
    { arewrite (eq_opt w ⊆₁ dom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘)).
      { rewrite RF. basic_solver. }
      rewrite (wf_rfD WF). basic_solver. }
    eapply eq_dom_mori with (x := E); eauto. }
  { apply eq_dom_loc with (lab := lab').
    { arewrite (eq_opt w ⊆₁ dom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘)).
      { rewrite RF. basic_solver. }
      rewrite (wf_rfl WF). basic_solver. }
    eapply eq_dom_mori with (x := E); eauto. }
  { apply eq_dom_val with (lab := lab').
    { arewrite (eq_opt w ⊆₁ dom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘)).
      { rewrite RF. basic_solver. }
      rewrite (wf_rfv' WF). basic_solver. }
    eapply eq_dom_mori with (x := E); eauto. }
  { apply eq_dom_is_r with (lab := lab').
    { arewrite (eq_opt r ⊆₁ dom_rel (⦗E⦘ ⨾ rmw' ⨾ ⦗eq e⦘)).
      { rewrite RMW. basic_solver. }
      rewrite (wf_rmwD WF). basic_solver. }
    eapply eq_dom_mori with (x := E); eauto. }
  { apply eq_dom_loc with (lab := lab').
    { arewrite (eq_opt r ⊆₁ dom_rel (⦗E⦘ ⨾ rmw' ⨾ ⦗eq e⦘)).
      { rewrite RMW. basic_solver. }
      rewrite (wf_rmwl WF). basic_solver. }
    eapply eq_dom_mori with (x := E); eauto. }
  { intros x y (SOME & EQE). subst y.
    destruct r as [r| ]; ins. subst x.
    assert (IMM : immediate sb' r e).
    { apply (wf_rmwi WF). unfolder in RMW.
      now apply RMW. }
    split.
    { unfold sb. unfolder. unfold delta_G. ins.
      unfold delta_E. splits.
      { left. destruct RMW as [_ RMW].
        unfolder in RMW. eapply RMW. eauto. }
      { unfold sb in IMM. unfolder in IMM. apply IMM. }
      now right. }
    intros c L R. eapply IMM; unfold sb in *.
    { unfolder in L. unfolder. ins.
      splits; basic_solver. }
    unfolder in R. unfolder. ins.
    splits; basic_solver. }
  { apply eq_dom_is_w with (lab := lab').
    { rewrite (wf_coD WF). basic_solver. }
    eapply eq_dom_mori with (x := E); eauto. }
  { apply eq_dom_loc with (lab := lab').
    { rewrite (wf_col WF). basic_solver. }
    eapply eq_dom_mori with (x := E); eauto. }
  { apply eq_dom_is_w with (lab := lab').
    { rewrite (wf_coD WF). basic_solver. }
    eapply eq_dom_mori with (x := E); eauto. }
  { apply eq_dom_loc with (lab := lab').
    { rewrite (wf_col WF). basic_solver. }
    eapply eq_dom_mori with (x := E); eauto. }
  { apply eq_dom_is_r with (lab := lab').
    { rewrite (wf_rfD WF). basic_solver. }
    eapply eq_dom_mori with (x := E); eauto. }
  { apply eq_dom_loc with (lab := lab').
    { rewrite (wf_rfl WF). basic_solver. }
    eapply eq_dom_mori with (x := E); eauto. }
  { apply eq_dom_val with (lab := lab').
    { rewrite (wf_rfv' WF). basic_solver. }
    eapply eq_dom_mori with (x := E); eauto. }
  { apply transitive_restr, WF. }
  { rewrite <- restr_transp.
    apply functional_restr, WF. }
  all: unfold delta_E.
  { set (dom := (E ∪₁ eq e) ∩₁ W' ∩₁ Loc_' ol).
    set (dom' := E' ∩₁ W' ∩₁ Loc_' ol).
    assert (TOT : is_total dom (restr_rel dom co')).
    { eapply is_total_restr. subst dom.
      eapply is_total_mori with (x := dom').
      all: ins; try now apply (wf_co_total WF).
      unfold flip. subst dom'. basic_solver 11. }
    subst dom. eapply is_total_mori; eauto; [| basic_solver].
    unfold flip. apply set_subset_inter_r.
    split; [apply set_subset_inter_r; split |].
    { basic_solver. }
    { apply eq_dom_is_w with (lab := delta_lab); [basic_solver |].
      eapply eq_dom_mori; eauto; [| now apply delta_G_dom].
      unfold flip. basic_solver. }
    apply eq_dom_loc with (lab := delta_lab); [basic_solver |].
    eapply eq_dom_mori; eauto; [| now apply delta_G_dom].
    unfold flip. basic_solver. }
  { apply (prf_init PFX). }
  { now apply (prf_threads PFX), WF. }
  { destruct w as [w|]; ins. exfalso.
    apply NR. enough (ISR : R' e).
    { unfold delta_lab, is_r in *. now rupd. }
    rewrite (wf_rfD WF), !seqA in RF.
    destruct RF as (_ & RF). unfolder in RF.
    now apply RF with (x := w) (y := e). }
  { split; [| basic_solver].
    unfolder. intros r' (e' & EQ & RF' & RINE).
    subst e'. apply NW. enough (ISR : W' e).
    { unfold delta_lab, is_w in *. now rupd. }
    apply (wf_rfD WF) in RF'. unfolder in RF'.
    apply RF'. }
  { destruct r as [r|]; ins. exfalso.
    apply NW. enough (ISR : W' e).
    { unfold delta_lab, is_w in *. now rupd. }
    rewrite (wf_rmwD WF), !seqA in RMW.
    destruct RMW as (_ & RMW). unfolder in RMW.
    now apply RMW with (x := r) (y := e). }
  { split; [| basic_solver].
    unfolder. intros w' (e' & EQ & CO' & WINE).
    subst e'. apply NW. enough (ISR : W' e).
    { unfold delta_lab, is_w in *. now rupd. }
    apply (wf_coD WF) in CO'. unfolder in CO'.
    apply CO'. }
  { split; [| basic_solver].
    unfolder. intros w' (e' & EQ & CO' & WINE).
    subst e'. apply NW. enough (ISR : W' e).
    { unfold delta_lab, is_w in *. now rupd. }
    apply (wf_coD WF) in CO'. unfolder in CO'.
    apply CO'. }
  { rewrite restr_set_union, (prf_rf PFX).
    rewrite restr_irrefl_eq by now apply rf_irr.
    rewrite union_false_r.
    unfold WCore.rf_delta_R, WCore.rf_delta_W.
    repeat apply union_more; ins.
    clear; basic_solver 12. }
  { rewrite restr_set_union, (prf_co PFX).
    rewrite restr_irrefl_eq by now apply co_irr.
    rewrite union_false_r. unfold WCore.co_delta.
    rewrite unionC with (r1 := eq e × _), <- unionA.
    repeat apply union_more; ins.
    all: clear; basic_solver 12. }
  { rewrite restr_set_union, (prf_rmw PFX).
    rewrite restr_irrefl_eq by now apply rmw_irr.
    rewrite union_false_r. rewrite unionA.
    arewrite (⦗eq e⦘ ⨾ rmw' ⨾ ⦗E⦘ ≡ ∅₂).
    { split; [| basic_solver].
      now rewrite (wf_rmwi WF), immediate_in. }
    rewrite union_false_r. unfold WCore.rmw_delta.
    apply union_more; ins. }
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
  unfolder. intros x y [[INIT | [XIN TID]] HEQ].
  all: subst y; splits; ins.
  { now apply PFX. }
  { unfold ext_sb; desf. }
  destruct e as [el | et en]; ins.
  destruct x as [xl | xt xn]; ins.
  unfold same_tid in TID. ins. subst xt.
  split; ins.
  destruct PeanoNat.Nat.lt_total
        with xn en
        as [LT | [EQ | GT]]; ins.
  { congruence. }
  exfalso.
  apply EMAX with (ThreadEvent et en) (ThreadEvent et xn).
  unfolder. splits; ins. unfold sb. unfolder.
  splits; ins. now apply PFX.
Qed.

Lemma delta_G_wf
    (INE : E' e)
    (NOTINE : ~ E e)
    (NINIT : ~ is_init e)
    (NTID : tid e <> tid_init)
    (EMAX : sb' ⨾ ⦗eq e⦘ ⊆ ⦗E⦘ ⨾ sb' ⨾ ⦗eq e⦘)
    (PFX : prefix X X')
    (NDATA : data' ⊆ ∅₂)
    (NADDR : addr' ⊆ ∅₂)
    (NCTRL : ctrl' ⊆ ∅₂)
    (NRMWDEP : rmw_dep' ⊆ ∅₂)
    (WF : Wf G')
    (EMAX2 : ⦗eq e⦘ ⨾ sb' ⨾ ⦗E⦘ ⊆ ∅₂) :
  Wf delta_G.
Proof using.
  destruct delta_add_event as (r & R1 & w & W1 & W2 & ADD).
  all: eauto.
  eapply add_event_wf
    with (X' := delta_X) (X := X).
  all: eauto.
  eapply prefix_wf; eauto.
  { rewrite (prf_data PFX). basic_solver. }
  { rewrite (prf_addr PFX). basic_solver. }
  { rewrite (prf_ctrl PFX). basic_solver. }
  rewrite (prf_rmw_dep PFX). basic_solver.
Qed.


Lemma delta_guided_add_step
    (INE : E' e)
    (NOTINE : ~ E e)
    (NINIT : ~ is_init e)
    (NTID : tid e <> tid_init)
    (WF : Wf G')
    (XWF : WCore.wf X X' cmt)
    (PFX : prefix X X')
    (EMAX1 : ⦗eq e⦘ ⨾ sb' ⨾ ⦗E⦘ ⊆ ∅₂)
    (EMAX2 : sb' ⨾ ⦗eq e⦘ ⊆ ⦗E⦘ ⨾ sb' ⨾ ⦗eq e⦘)
    (NDATA : data' ⊆ ∅₂)
    (NADDR : addr' ⊆ ∅₂)
    (NCTRL : ctrl' ⊆ ∅₂)
    (NRMWDEP : rmw_dep' ⊆ ∅₂)
    (RF : eq e ∩₁ R' ⊆₁ codom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq e⦘) ∪₁ cmt) :
  WCore.guided_step_gen cmt X' X delta_X e (lab' e).
Proof using.
  assert (SUBE : delta_E ⊆₁ E').
  { unfold delta_E.
    apply set_subset_union_l.
    split; [apply PFX |].
    basic_solver. }
  assert (SUBE' : E ⊆₁ delta_E).
  { unfold delta_E. basic_solver. }
  assert (EQLAB : eq_dom E lab lab').
  { eapply eq_dom_mori with (x := is_init ∪₁ E); eauto.
    { unfold flip. basic_solver. }
    apply PFX. }
  constructor; ins.
  { apply delta_add_event; ins. }
  constructor; ins.
  { apply delta_G_wf; ins. }
  { constructor; ins.
    { basic_solver. }
    { apply PFX. }
    { eapply eq_dom_mori with (x := is_init ∪₁ delta_E).
      all: eauto.
      { unfold flip. basic_solver. }
      apply delta_G_prefix; ins. }
    all: rewrite restr_restr; basic_solver. }
  { apply XWF. }
  { unfold delta_E.
    arewrite ((E ∪₁ eq e) ∩₁ is_r delta_lab ≡₁
              (E ∪₁ eq e) ∩₁ R').
    { apply same_lab_u2v_dom_is_r with (s := E ∪₁ eq e).
      unfold same_lab_u2v_dom, same_label_u2v. intros x XIN.
      rewrite (prf_lab (delta_G_prefix INE NOTINE NINIT EMAX2 PFX)).
      all: basic_solver. }
    rewrite set_inter_union_l.
    apply set_subset_union_l; split.
    { arewrite (E ∩₁ R' ⊆₁ E ∩₁ R).
      { apply set_subset_inter_r; split; [basic_solver |].
        apply eq_dom_is_r with (lab := lab'); [basic_solver |].
        eapply eq_dom_mori; eauto. unfold flip. basic_solver. }
      rewrite (WCore.wf_sub_rfD XWF), (prf_rf PFX).
      basic_solver 7. }
    rewrite RF, restr_set_union, !codom_union.
    basic_solver 12. }
  admit. (* TODO *)
Admitted.

End DeltaGraph.

Section EnumeratedDifference.

Variable X X' : WCore.t.
Variable traces : thread_id -> trace label -> Prop.

Notation "'G''" := (WCore.G X').
Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'W''" := (fun x => is_w lab' x).
Notation "'R''" := (fun x => is_r lab' x).

Notation "'G'" := (WCore.G X).
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
  diff_elemst : E' \₁ E ⊆₁ fun x => tid x <> tid_init;
  diff_sb : restr_rel (E' \₁ E) sb' ⊆ total_order_from_list l;
  diff_rf : restr_rel (E' \₁ E) rf' ⊆ total_order_from_list l;
  diff_rf_d : (E' \₁ E) ∩₁ R' ⊆₁ codom_rel rf';
}.

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
    (PFX : prefix X X')
    (ENUM : enumd_diff l) :
  E' \₁ E ⊆₁ set_compl is_init.
Proof.
  unfolder. intros x [INE' NOTINE] INIT.
  apply NOTINE, (prf_init PFX). basic_solver.
Qed.

End EnumeratedDifference.

End SubToFullExecInternal.

Section SubToFullExec.

Variable X X' : WCore.t.
Variable cmt : actid -> Prop.
Variable thrdle : relation thread_id.
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

Notation "'delta_X'" := (SubToFullExecInternal.delta_X X X').
Notation "'delta_E'" := (SubToFullExecInternal.delta_E X).

Lemma sub_to_full_exec_end_wf l
    (PFX : prefix X X')
    (SCWF : xmm_s.wf_sc G' sc')
    (WF : Wf G')
    (XWF : WCore.wf X X' cmt)
    (ENUM : SubToFullExecInternal.enumd_diff X X' l) :
  WCore.wf X' X' cmt.
Proof using.
  constructor; ins.
  { apply XWF. }
  arewrite (E' ≡₁ E' \₁ E ∪₁ E).
  { apply set_union_minus, PFX. }
  rewrite set_inter_union_l. apply set_subset_union_l.
  split.
  { rewrite (SubToFullExecInternal.diff_rf_d ENUM).
    basic_solver. }
  arewrite (E ∩₁ R' ⊆₁ E ∩₁ R).
  { unfold is_r. unfolder.
    intros x (XIN & XISR). split; ins.
    rewrite (prf_lab PFX); ins.
    basic_solver. }
  rewrite (WCore.wf_sub_rfD XWF), (prf_rf PFX).
  basic_solver.
Qed.

Lemma sub_to_full_exec l
    (WF : Wf (WCore.G X'))
    (XWF : WCore.wf X X' cmt)
    (PFX : prefix X X')
    (SCWF : xmm_s.wf_sc G' sc')
    (NDATA : data' ⊆ ∅₂)
    (NADDR : addr' ⊆ ∅₂)
    (NCTRL : ctrl' ⊆ ∅₂)
    (NRMWDEP : rmw_dep' ⊆ ∅₂)
    (ENUM : SubToFullExecInternal.enumd_diff X X' l) :
  (WCore.guided_step cmt X')＊ X X'.
Proof using.
  assert (WF' : WCore.wf X' X' cmt).
  { apply sub_to_full_exec_end_wf with l; ins. }
  generalize X XWF PFX ENUM.
  clear      X XWF PFX ENUM.
  induction l as [ | h t IHl]; ins.
  { assert (FULL : E ≡₁ E').
    { rewrite set_union_minus with (s := E') (s' := E)
           by apply PFX.
      rewrite (SubToFullExecInternal.diff_elems ENUM).
      basic_solver. }
    arewrite (X = X'); [| apply rt_refl].
    arewrite (X = {| WCore.G := G; WCore.sc := sc; |}); [destruct X; ins |].
    arewrite (X' = {| WCore.G := G'; WCore.sc := sc'; |}); [destruct X'; ins |].
    rewrite prefix_full_G with (X' := X'); ins.
    rewrite prefix_full_sc with (X' := X'); ins. }
  assert (HINE : E' h) by (apply ENUM; ins; eauto).
  assert (NINE : ~E h) by (apply ENUM; ins; eauto).
  assert (HNINIT : ~is_init h).
  { apply (SubToFullExecInternal.diff_no_init PFX ENUM).
    basic_solver. }
  assert (HTID : tid h <> tid_init).
  { apply ENUM. basic_solver. }
  assert (HMAX : sb' ⨾ ⦗eq h⦘ ⊆ ⦗E⦘ ⨾ sb' ⨾ ⦗eq h⦘).
  { arewrite (sb' ⨾ ⦗eq h⦘ ⊆ ⦗E ∪₁ set_compl E⦘ ⨾ sb' ⨾ ⦗eq h⦘) at 1.
    { rewrite set_compl_union_id. basic_solver. }
    rewrite id_union, seq_union_l. apply inclusion_union_l; ins.
    arewrite (⦗set_compl E⦘ ⨾ sb' ⨾ ⦗eq h⦘ ⊆ ∅₂); [| basic_solver].
    intros x y HREL. eapply list_min_elt with (b := x); [apply ENUM |].
    apply (SubToFullExecInternal.diff_sb ENUM).
    unfold sb in *. unfolder. unfolder in HREL. desf. }
  assert (STEP : WCore.guided_step cmt X' X (delta_X h)).
  { exists h, (lab' h).
    apply SubToFullExecInternal.delta_guided_add_step; ins.
    { sin_rewrite (prf_sb PFX). unfold sb. basic_solver. }
    destruct (classic (cmt h)) as [CMT|NCMT]; [basic_solver |].
    intros h' (HIR & EQH). subst h'.
    destruct (SubToFullExecInternal.diff_rf_d ENUM) with (x := h)
          as (w & RF).
    { basic_solver. }
    left. exists w. unfolder; splits; ins.
    destruct (classic (E w)) as [WINE|WNINE]; ins.
    exfalso. eapply list_min_elt with (b := w); [apply ENUM |].
    apply (SubToFullExecInternal.diff_rf ENUM). unfolder; splits; ins.
    apply (wf_rfE WF) in RF. unfolder in RF. desf. }
  assert (NDELTA : forall x (NDELTA : ~delta_E h x), ~E x).
  { unfold SubToFullExecInternal.delta_E. unfolder.
    repeat intros; eauto. }
  eapply rt_trans; [apply rt_step; eauto |].
  apply IHl.
  { red in STEP; desf; apply STEP. }
  { apply SubToFullExecInternal.delta_G_prefix; ins. }
  constructor; ins.
  { eapply nodup_consD, ENUM. }
  { arewrite ((fun x => In x t) ≡₁ (fun x => In x (h :: t)) \₁ eq h).
    { split; [| basic_solver].
      unfolder; ins. split; eauto.
      apply nodup_not_in with (t := t); ins.
      apply ENUM. }
    unfold SubToFullExecInternal.delta_E.
    now rewrite <- (SubToFullExecInternal.diff_elems ENUM),
            set_minus_minus_l. }
  { rewrite <- (SubToFullExecInternal.diff_elemst ENUM).
    basic_solver. }
  { unfold SubToFullExecInternal.delta_E.
    rewrite set_minus_union_r. intros x y SB.
    assert (LT : total_order_from_list (h :: t) x y).
    { eapply SubToFullExecInternal.diff_sb; eauto.
      red. splits; apply SB. }
    apply total_order_from_list_cons in LT; desf.
    unfolder in SB. desf. }
  { unfold SubToFullExecInternal.delta_E.
    rewrite set_minus_union_r. intros x y RF.
    assert (LT : total_order_from_list (h :: t) x y).
    { eapply SubToFullExecInternal.diff_rf; eauto.
      red. splits; apply RF. }
    apply total_order_from_list_cons in LT; desf.
    unfolder in RF. desf. }
  rewrite <- (SubToFullExecInternal.diff_rf_d ENUM).
  basic_solver.
Qed.

Lemma enumd_diff_listless
    (WF : WCore.wf X X' cmt)
    (RFCO : rf_complete G')
    (FIN : set_finite (E' \₁ E))
    (NTID : E' \₁ E ⊆₁ (fun x => tid x <> tid_init))
    (STAB : WCore.stable_uncmt_reads_gen X' E thrdle) :
  exists l,
    SubToFullExecInternal.enumd_diff X X' l.
Proof using.
  apply set_finiteE in FIN. destruct FIN as (l' & NODUP & EQ).
  destruct partial_order_included_in_total_order
    with actid (sb' ∪ tid ↓ thrdle)
    as (tord & SUB & TOT).
  { red. split.
    { apply irreflexive_union; split; [apply sb_irr |].
      unfolder. ins. eapply (WCore.surg_order STAB); eauto. }
    unfolder. intros x y z R1 R2. desf.
    { left. now apply sb_trans with y. }
    all: change (thrdle (tid x) (tid z))
           with ((tid ↓ thrdle) x z).
    { right. apply thrdle_sb_closed with (X := X').
      all: try now apply STAB.
      unfolder. eauto 11. }
    { right. apply thrdle_sb_closed with (X := X').
      all: try now apply STAB.
      unfolder. eauto 11. }
    right. unfolder. eapply STAB; eauto. }
  exists (isort tord l'). constructor; ins.
  { apply NoDup_StronglySorted with tord.
    { apply TOT. }
    apply StronglySorted_isort; ins. }
  { rewrite EQ. unfolder; split.
    all: intro; apply in_isort_iff. }
  { rewrite total_order_from_isort, <- EQ, <- SUB; ins.
    basic_solver. }
  { rewrite total_order_from_isort, <- EQ, <- SUB; ins.
    rewrite <- (WCore.surg_ndtrmt STAB).
    basic_solver 11. }
  transitivity (E' ∩₁ R'); [basic_solver | apply RFCO].
Qed.

Lemma sub_to_full_exec_listless
    (XWF : WCore.wf X X' cmt)
    (RFCO : rf_complete G')
    (FIN : set_finite (E' \₁ E))
    (PFX : prefix X X')
    (WF : Wf G')
    (NTID : E' \₁ E ⊆₁ (fun x => tid x <> tid_init))
    (SCWF : xmm_s.wf_sc G' sc')
    (NDATA : data' ⊆ ∅₂)
    (NADDR : addr' ⊆ ∅₂)
    (NCTRL : ctrl' ⊆ ∅₂)
    (NRMWDEP : rmw_dep' ⊆ ∅₂)
    (STAB : WCore.stable_uncmt_reads_gen X' E thrdle) :
  (WCore.guided_step cmt X')＊ X X'.
Proof using.
  destruct enumd_diff_listless as (l & ENUM); eauto.
  apply sub_to_full_exec with l; ins.
Qed.

End SubToFullExec.