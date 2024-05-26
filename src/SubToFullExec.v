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

Section DeltaGraph.

Variable G G' : execution.
Variable sc :relation actid.
Variable cmt : actid -> Prop.
Variable h : actid.

Notation "'get_sb'" := (fun x => sb x).

Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'rmw_dep''" := (rmw_dep G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'W''" := (fun x => is_w lab' x).
Notation "'R''" := (fun x => is_r lab' x).
Notation "'F''" := (fun x => is_f lab' x).

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'W'" := (fun x => is_w lab x).
Notation "'R'" := (fun x => is_r lab x).
Notation "'F'" := (fun x => is_r lab x).

Definition delta_G := {|
  acts_set := E ∪₁ eq h;
  threads_set := threads_set G;
  lab := lab;
  rmw := rmw ∪ (⦗E⦘ ⨾ rmw' ⨾ ⦗eq h⦘);
  data := ∅₂;
  addr := ∅₂;
  ctrl := ∅₂;
  rmw_dep := ⦗E ∪₁ eq h⦘ ⨾ rmw_dep' ⨾ ⦗E ∪₁ eq h⦘;
  rf := rf ∪ (⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘) ∪ (⦗eq h⦘ ⨾ rf' ⨾ ⦗E⦘);
  co := co ∪ (⦗E⦘ ⨾ co' ⨾ ⦗eq h⦘) ∪ (⦗eq h⦘ ⨾ co' ⨾ ⦗E⦘);
|}.

Notation "'X'" := ({|
  WCore.G := G;
  WCore.GC := G';
  WCore.sc := sc;
  WCore.cmt := cmt;
|}).
Notation "'X''" := ({|
  WCore.G := delta_G;
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

Lemma uncmt_rf_same_tid_sub_sb l
    (WF : WCore.wf X)
    (ENUM : enumd_diff l) :
  restr_rel (E' \₁ E) (rf' ⨾ ⦗E' \₁ cmt⦘) ∩ same_tid ⊆ sb'.
Proof using.
  intros x y (RF & TID).
  assert (XINIT : ~ is_init x).
  { eapply diff_no_init; eauto. apply RF. }
  assert (YINIT : ~ is_init y).
  { eapply diff_no_init; eauto. apply RF. }
  assert (XYNEQ : x <> y).
  { intro F. subst. eapply rf_irr.
    { apply WF. }
    ins. unfolder in RF. desf.
    eauto. }
  unfold sb. unfolder. splits.
  all: try now apply RF.
  destruct x as [xl | xt xn],
           y as [yl | yt yn]; ins.
  split; ins.
  red in TID. ins. subst.
  destruct NPeano.Nat.lt_total with xn yn as [LT | [EQ | GT]].
  all: eauto; try congruence.
  assert (SB : restr_rel (E' \₁ E) sb'
                (ThreadEvent yt yn) (ThreadEvent yt xn)).
  { unfold sb. unfolder. ins; splits; ins.
    all: apply RF. }
  exfalso. eapply total_order_from_list_irreflexive.
  { apply ENUM. }
  eapply total_order_from_list_trans.
  { apply ENUM. }
  { apply ENUM in RF. eauto. }
  now apply ENUM in SB.
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
  { eapply sub_to_full_exec_end_wf; eauto. }
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
  intros x IN.
  destruct IN as ((INX & NINX) & IS_R).
  apply not_or_and in NINX. desf.
  apply (SubToFullExecInternal.diff_rf_d ENUM).
  unfolder; splits; ins.
Qed.

Lemma sub_to_full_exec_sort sc G G' cmt l tord
    (WF : WCore.wf {|
      WCore.sc := sc;
      WCore.G := G;
      WCore.GC := G';
      WCore.cmt := cmt
    |})
    (OTOT : strict_total_order ⊤₁ tord)
    (ORB : min_elt tord tid_init)
    (ORDRF : restr_rel (acts_set G' \₁ acts_set G)
              (rf G' ⨾ ⦗acts_set G' \₁ cmt⦘) ⊆ tid ↓ tord^?)
    (ENUM : SubToFullExecInternal.enumd_diff G G' cmt l) :
  exists l',
    << SORT : StronglySorted (tid ↓ tord ∪ ext_sb) l' >> /\
    << ENUM : SubToFullExecInternal.enumd_diff G G' cmt l' >>.
Proof using.
  destruct partial_order_included_in_total_order
    with actid (tid ↓ tord ∪ ext_sb)
    as (sord & SUB & TOT).
  { unfolder; split.
    { intros x HREL. desf.
      { eapply OTOT. eauto. }
      eapply ext_sb_irr. eauto. }
    unfolder in OTOT.
    intros x y z R1 R2. desf.
    all: eauto using ext_sb_trans.
    all: destruct x as [xl | xt xn],
                  y as [yl | yt yn],
                  z as [zl | zt zn]; ins.
    all: eauto.
    all: try now (exfalso; eapply ORB; eauto).
    all: desf; eauto. }
  assert (DIFF : acts_set G' \₁ acts_set G ≡₁
            fun x => In x (isort sord l)).
  { rewrite (SubToFullExecInternal.diff_elems ENUM).
    unfolder. split; intros x HSET.
    all: eapply in_isort_iff; eauto. }
  assert (SORT : StronglySorted sord (isort sord l)).
  { apply StronglySorted_isort, ENUM; ins. }
  exists (isort sord l). split.
  { apply StronglySorted_sub with sord.
    all: eauto.
    unfolder in OTOT. desf.
    unfolder. splits.
    { intros x HREL; desf; eauto.
      eapply ext_sb_irr; eauto. }
    { intros x y z R1 R2. desf; eauto using ext_sb_trans.
      all: destruct x as [xl | xt xn],
                    y as [yl | yt yn],
                    z as [zl | zt zn]; ins.
      all: eauto.
      all: try now (exfalso; eapply ORB; eauto).
      all: desf; eauto. }
    intros x XIN y YIN NEQ.
    apply DIFF in XIN, YIN.
    assert (XINIT : ~is_init x).
    { eapply SubToFullExecInternal.diff_no_init; eauto. }
    assert (YINIT : ~is_init y).
    { eapply SubToFullExecInternal.diff_no_init; eauto. }
    destruct x as [xl | xt xn],
             y as [yl | yt yn]; ins.
    destruct (classic (xt = yt)) as [TEQ|TNEQ]; subst.
    { destruct NPeano.Nat.lt_total with xn yn as [LT | [EQ | LT]]; eauto.
      congruence. }
    destruct OTOT0 with xt yt; eauto. }
  constructor; ins.
  { apply NoDup_StronglySorted with (r := sord).
    { apply TOT. }
    apply StronglySorted_isort, ENUM; ins. }
  { intros x y (SB & DOM & CODOM).
    apply DIFF in DOM, CODOM.
    apply total_order_from_isort; ins.
    { apply ENUM. }
    unfolder; splits.
    all: try now eapply in_isort_iff; eauto.
    apply SUB. right.
    red in SB. unfolder in SB. desf. }
  { intros x y HREL.
    apply total_order_from_isort; ins.
    { apply ENUM. }
    unfolder; splits.
    { apply SUB.
      destruct (classic (tid x = tid y)) as [TIDEQ|NTEQ].
      { right. enough (SB : sb G' x y).
        { unfold sb in SB. unfolder in SB. apply SB. }
        eapply SubToFullExecInternal.uncmt_rf_same_tid_sub_sb.
        all: eauto.
        split; ins. }
      apply ORDRF in HREL.
      destruct HREL as [EQ|TORD]; ins.
      now left. }
    all: destruct HREL as (_ & DOM & CODOM).
    all: try now eapply in_isort_iff, DIFF; eauto. }
  apply ENUM.
Qed.

Lemma sub_to_full_exec_sort_part sc G G' cmt l tord
    (WF : WCore.wf {|
      WCore.sc := sc;
      WCore.G := G;
      WCore.GC := G';
      WCore.cmt := cmt
    |})
    (OPA : strict_partial_order tord)
    (ORB : min_elt tord tid_init)
    (ORDRF : restr_rel (acts_set G' \₁ acts_set G)
              (rf G' ⨾ ⦗acts_set G' \₁ cmt⦘) ⊆ (tid ↓ tord^?))
    (ENUM : SubToFullExecInternal.enumd_diff G G' cmt l) :
  exists l',
    << SORT : restr_rel (fun x => In x l) (tid ↓ tord ∪ sb G') ⊆ total_order_from_list l' >> /\
    << ENUM : SubToFullExecInternal.enumd_diff G G' cmt l' >>.
Proof using.
  destruct partial_order_included_in_total_order
    with thread_id tord
    as (tord' & SUB & TOT).
  { admit. }
  set (tord'' := restr_rel (fun x => x <> tid_init) tord' ∪
                 (fun x y => x = tid_init /\ y = tid_init)).
  edestruct sub_to_full_exec_sort with (tord := tord'')
                                    as (l' & SORT & ENUM').
  all: eauto.
  { admit. }
  { admit. }
  { admit. }
  exists l'; split; ins. red.
  rewrite total_order_from_sorted with (ord := tid ↓ tord'' ∪ ext_sb).
  all: ins.
  { subst tord''.
    rewrite <- (SubToFullExecInternal.diff_elems ENUM'),
            <- (SubToFullExecInternal.diff_elems ENUM).
    unfolder. intros x y HREL.
    assert (XINIT : ~is_init x).
    { eapply SubToFullExecInternal.diff_no_init; eauto.
      unfolder; desf. }
    assert (YINIT : ~is_init y).
    { eapply SubToFullExecInternal.diff_no_init; eauto.
      unfolder; desf. }
    assert (XINIT' : tid x <> tid_init).
    { intro F. apply XINIT.
      apply WF. ins. unfolder.
      split; ins; desf. }
    assert (YINIT' : tid y <> tid_init).
    { intro F. apply YINIT.
      apply WF. ins. unfolder.
      split; ins; desf. }
    desf; splits; ins; eauto.
    { apply SUB in HREL. eauto. }
    red in HREL. unfolder in HREL. desf.
    eauto. }
  admit.
Admitted.

End SubToFullExec.