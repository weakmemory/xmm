Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
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

Module SubToFullExecInternal.

Section DeltaGraph.

Variable G G' : execution.
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
  WCore.cmt := cmt;
|}).
Notation "'X''" := ({|
  WCore.G := delta_G;
  WCore.GC := G';
  WCore.cmt := cmt;
|}).
Notation "'X_fin'" := ({|
  WCore.G := G';
  WCore.GC := G';
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
  { rewrite !id_union, seq_union_l,
            !seq_union_r, <- (sub_rmw SUB).
    rewrite one_dir_irrefl; eauto using rmw_one_dir.
    destruct (classic (dom_rel (rmw' ⨾ ⦗E⦘) h)) as [HIN1|HIN1].
    { rewrite one_dir_assym_1, !union_false_r;
        eauto using rmw_one_dir, one_dir_dom.
      unfolder in HIN1. desf.
      enough (EINE : E h).
      { arewrite (⦗eq h⦘ ≡ ⦗eq h⦘ ⨾ ⦗E⦘); try basic_solver. }
      apply wf_rmwi, immediate_in in HIN1; eauto.
      change G with (WCore.G X).
      eapply WCore.ext_sb_dense; eauto.
      unfold sb in HIN1. unfolder in HIN1.
      desf. }
    destruct (classic (codom_rel (⦗E⦘ ⨾ rmw') h)) as [HIN2|HIN2].
    { rewrite one_dir_assym_2, !union_false_r;
      eauto using rmw_one_dir, one_dir_dom. }
    rewrite one_dir_assym_helper_1, one_dir_assym_helper_2,
            !union_false_r; eauto. }
  { rewrite (WCore.cc_data_empty WF); basic_solver. }
  { rewrite (WCore.cc_addr_empty WF); basic_solver. }
  { rewrite (WCore.cc_ctrl_empty WF); basic_solver. }
  { rewrite !id_union, seq_union_l, !seq_union_r, <- (sub_rf SUB).
    rewrite one_dir_irrefl; eauto using rf_one_dir.
    now rewrite union_false_r. }
  { rewrite !id_union, seq_union_l, !seq_union_r, <- (sub_co SUB).
    arewrite (⦗eq h⦘ ⨾ co' ⨾ ⦗eq h⦘ ≡ ∅₂); [| now rewrite union_false_r].
    split; [| basic_solver]. unfolder; ins; desf.
    eapply co_irr; eauto. }
  basic_solver.
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
  unfold contigious_actids; ins.
  set (CONT1 := WCore.wf_gc_cont WF NOT_INIT).
  set (CONT2 := WCore.wf_g_cont WF NOT_INIT).
  destruct CONT1 as [N1 CONT1], CONT2 as [N2 CONT2].
  destruct (classic (t = tid h)); subst.
  { exists (1 + N2).
    rewrite thread_set_S, set_inter_union_l, CONT2.
    arewrite (eq h ∩₁ same_tid h ≡₁ eq h) by basic_solver.
    apply set_union_more; auto. apply set_equiv_single_single.
    destruct h as [l | ht hid]; unfold same_tid in *; ins.
    f_equal.
    assert (LT : hid < N1).
    { eapply thread_set_iff, CONT1.
      split; auto. }
    apply PeanoNat.Nat.le_antisymm.
    { apply Compare_dec.not_gt. intro GT.
      apply NEXT with (x := ThreadEvent ht (hid - 1)).
      { apply set_subset_single_l.
        transitivity ((E' ∩₁ (fun e => ht = tid e)) \₁
                      (E ∩₁ (fun e => ht = tid e))); [| basic_solver].
        rewrite CONT1, CONT2, thread_set_diff. apply set_subset_single_l.
        unfolder; ins; desf. exists (hid - 1). split; auto.
        lia. }
      unfold sb, ext_sb; ins. unfolder; splits; auto; try lia.
      apply in_restr_acts, CONT1, thread_set_iff. lia. }
    eapply thread_set_niff. intro F.
    apply CONT2, in_restr_acts in F; auto. }
  exists N2.
  rewrite set_inter_union_l, CONT2.
  arewrite (eq h ∩₁ (fun e => t = tid e) ≡₁ ∅); basic_solver.
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

Lemma delta_G_suffix
    (IN : ~E h)
    (WF : WCore.wf X) :
  sub_execution delta_G G ∅₂ ∅₂.
Proof using.
  constructor; ins.
  { basic_solver. }
  { rewrite wf_rmwE at 1; [basic_solver |].
    change G with (WCore.G X); auto using WCore.wf_g. }
  { arewrite (data ≡ ∅₂); [| basic_solver].
    erewrite sub_data; [| apply WF].
    rewrite WF.(WCore.cc_data_empty); basic_solver. }
  { arewrite (addr ≡ ∅₂); [| basic_solver].
    erewrite sub_addr; [| apply WF].
    rewrite WF.(WCore.cc_addr_empty); basic_solver. }
  { arewrite (ctrl ≡ ∅₂); [| basic_solver].
    erewrite sub_ctrl; [| apply WF].
    rewrite WF.(WCore.cc_ctrl_empty); basic_solver. }
  { rewrite sub_frmw with (G := G') at 1; [basic_solver 7 |].
    apply WF. }
  { rewrite wf_rfE at 1; [basic_solver 7 |].
    change G with (WCore.G X); auto using WCore.wf_g. }
  { rewrite wf_coE at 1; [basic_solver 7 |].
    change G with (WCore.G X); auto using WCore.wf_g. }
  basic_solver.
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
  unfold delta_G, sb; ins. rewrite !id_union.
  rewrite !seq_union_r, !seq_union_l.
  rewrite <- restr_relE with (d := eq h).
  rewrite restr_irrefl_eq; [rewrite union_false_r | apply ext_sb_irr].
  basic_solver 8.
Qed.

End DeltaGraph.

Section EnumeratedDifference.

Variable G G' : execution.
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
  diff_rf : restr_rel (E' \₁ E) rf' ⨾ ⦗E' \₁ cmt⦘ ⊆ total_order_from_list l;
  diff_rf_d : dom_rel (rf' ⨾ ⦗E' \₁ E⦘) ⊆₁ E';
}.

Notation "'X'" := ({|
  WCore.G := G;
  WCore.GC := G';
  WCore.cmt := cmt;
|}).
Notation "'X_fin'" := ({|
  WCore.G := G';
  WCore.GC := G';
  WCore.cmt := cmt;
|}).

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
  rewrite <- set_inter_full_r with (s := E'),
          <- set_inter_full_r with (s := E),
          set_full_split with (S := is_init),
          !set_inter_union_r.
  rewrite WF.(WCore.wf_g_init). basic_solver 5.
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
  apply WF.(WCore.wf_gc_acts). unfolder. ins.
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
    WCore.cmt := cmt;
  |} h.
Proof using.
  set (X' := {|
    WCore.G := delta_G G G' h;
    WCore.GC := G';
    WCore.cmt := cmt;
  |}).
  assert (IN_D : (E' \₁ E) h).
  { by apply ENUM.(diff_elems (h :: t)). }
  assert (NINIT : ~ is_init h).
  { eapply diff_no_init; eauto. }
  assert (NIRID : tid h <> tid_init).
  { intro F. enough (INIT : is_init h).
    { eapply diff_no_init; eauto. }
    apply WF.(WCore.wf_gc_acts). unfolder. ins.
    split; auto; apply IN_D. }
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
  ins. rewrite Heq in FIN.
  unfold trace_finite in FIN. desf.
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
  destruct (classic (E e)) as [INE|INE]; auto.
  exfalso. eapply list_min_elt; [apply ENUM|].
  apply ENUM.(diff_rf (h :: t)).
  unfolder; splits; eauto.
  all: try by apply ENUM.(diff_elems (h :: t)).
  apply wf_rfE in RF; [unfolder in RF; desf | apply XWF].
Qed.

(* Lemma enum_diff_X_fin_WF l
    (ENUM : enumd_diff l)
    (XWF : WCore.wf X) :
  WCore.wf X_fin.
Proof using.
...
Qed. *)

End EnumeratedDifference.

Section SuBToFullExecCases.

Variable G G' : execution.
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
  WCore.cmt := cmt;
|}).
Notation "'X''" := ({|
  WCore.G := delta_G G G' h;
  WCore.GC := G';
  WCore.cmt := cmt;
|}).
Notation "'X_fin'" := ({|
  WCore.G := G';
  WCore.GC := G';
  WCore.cmt := cmt;
|}).

Lemma X_prime_wf_helper
    (NIN : ~ E h)
    (HIN : E' h)
    (ENUM : enumd_diff G G' cmt (h :: t))
    (WF : WCore.wf X)
    (WF_fin : WCore.wf X_fin) :
  WCore.wf X'.
Proof using.
  constructor; ins.
  all: try now apply WF.
  { transitivity E; [apply WF | basic_solver]. }
  { rewrite delta_G_sb; auto; [| apply WF].
    rewrite set_inter_union_r, restr_set_union, !restr_relE.
    arewrite (⦗cmt ∩₁ eq h⦘ ⨾ sb' ⨾ ⦗cmt ∩₁ eq h⦘ ≡ ∅₂).
    { split; [| basic_solver].
      transitivity (⦗eq h⦘ ⨾ sb' ⨾ ⦗eq h⦘); [basic_solver |].
      rewrite <- restr_relE, restr_irrefl_eq; [easy | apply sb_irr]. }
    rewrite union_false_r; repeat apply inclusion_union_mon.
    { rewrite sub_sb with (G := G') (G' := G); [basic_solver | apply WF]. }
    all: basic_solver. }
  { rewrite set_inter_union_r, restr_set_union, !restr_relE.
    arewrite (⦗cmt ∩₁ eq h⦘ ⨾ rf' ⨾ ⦗cmt ∩₁ eq h⦘ ≡ ∅₂).
    { split; [| basic_solver].
      transitivity (⦗eq h⦘ ⨾ rf' ⨾ ⦗eq h⦘); [basic_solver |].
      rewrite <- restr_relE, restr_irrefl_eq; [easy | apply rf_irr].
      apply WF. }
    rewrite union_false_r; repeat apply inclusion_union_mon.
    { rewrite sub_rf with (G := G') (G' := G); [basic_solver | apply WF]. }
    all: basic_solver. }
  { rewrite set_inter_union_l, !codom_union.
    apply set_subset_union_l; split.
    { transitivity (codom_rel rf ∪₁ cmt); [apply WF | basic_solver 5]. }
    destruct (classic (is_r lab' h)) as [ISR|ISR].
    { edestruct (WF_fin.(WCore.sub_rfD)) as [RD|RD],
                (classic (cmt h)) as [CMT|CMT].
      all: try basic_solver.
      ins.
      transitivity (codom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘)); [| basic_solver 7].
      transitivity (eq h); [basic_solver |].
      assert (SUBE : dom_rel (rf' ⨾ ⦗eq h⦘) ⊆₁ E).
      { eapply enum_diff_head_rf; eauto. }
      apply set_subset_single_l.
      unfolder; unfolder in SUBE; unfolder in RD; desf.
      eauto 11. }
    arewrite (eq h ∩₁ (fun a => is_r lab a) ≡₁ ∅).
    { erewrite sub_lab; [| apply WF]; ins. basic_solver. }
    basic_solver. }
  eapply enumd_deltaG_prefix; eauto.
Qed.

Lemma step_once_read_helper w
    (WF : WCore.wf X)
    (WF' : WCore.wf X_fin)
    (ENUM : enumd_diff G G' cmt (h :: t))
    (RF : rf' w h)
    (COH : trace_coherent traces G')
    (INE : E w) :
  WCore.cfg_add_event_uninformative traces X X'.
Proof using.
  (* Information about h *)
  assert (IN_D : (E' \₁ E) h).
  { apply ENUM; desf. }
  assert (NOT_INIT : ~is_init h).
  { eapply diff_no_init with (G := G); eauto. }
  assert (H_TID : tid h <> tid_init).
  { eapply WCore.wf_actid_tid; eauto. apply IN_D. }
  assert (IS_R : R' h).
  { apply wf_rfD in RF; [| apply WF].
    unfolder in RF; desf. }
  assert (IS_W : W' w).
  { apply wf_rfD in RF; [| apply WF].
    unfolder in RF; desf. }
  assert (NOT_W : ~W' h).
  { generalize IS_R; unfold is_w, is_r.
    destruct (lab' h); auto. }

  exists h, None, (Some w), ∅, ∅.
  constructor; ins.
  { apply IN_D. }
  { eapply enumd_deltaG_new_event_correct; eauto. }
  (* TODO: prettify? *)
  { apply union_more; [apply union_more; auto |].
    { split; [| basic_solver].
    intros w' h' (w'' & WINE' & h''' & RF' & WINH).
    destruct WINE', WINH; subst h''' w'' h'.
    erewrite wf_rff with (y := w') (z := w); eauto; try now apply WF.
    basic_solver. }
    unfold WCore.rf_delta_W; ins.
    arewrite (is_w lab' h = false).
    { destruct (is_w lab' h); desf. }
    rewrite wf_rfD; [basic_solver | apply WF]. }
  { unfold WCore.co_delta.
    arewrite (is_w lab' h = false).
    { destruct (is_w lab' h); desf. }
    rewrite wf_coD with (G := G'); [| apply WF].
    basic_solver. }
  { unfold WCore.rmw_delta, W_ex.
    rewrite wf_rmwD with (G := G'); [| apply WF].
    basic_solver. }
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

  destruct (classic (cmt h)) as [CMT|CMT].
  { destruct (classic (codom_rel (⦗E⦘ ⨾ rf') h)) as [RF | NRF].
    { destruct RF as (w & w' & (EQ & INE) & RF); subst w'.
      eapply step_once_read_helper; eauto. }
    exists h, None, None, ∅, ∅.
    constructor; ins.
    { apply IN_D. }
    { eapply enumd_deltaG_new_event_correct; eauto. }
    (* TODO: prettify? *)
    { apply union_more; [apply union_more; auto |].
      { split; [| basic_solver].
        intros w h' RF. apply seqA in RF.
        apply NRF. exists w.
        unfolder; unfolder in RF; desf. }
      unfold WCore.rf_delta_W; ins.
      arewrite (is_w lab' h = false).
      { destruct (is_w lab' h); desf. }
      rewrite wf_rfD; [basic_solver | apply WF]. }
    { unfold WCore.co_delta.
      arewrite (is_w lab' h = false).
      { destruct (is_w lab' h); desf. }
      rewrite wf_coD with (G := G'); [| apply WF].
      basic_solver. }
    { unfold WCore.rmw_delta, W_ex.
      rewrite wf_rmwD with (G := G'); [| apply WF].
      basic_solver. }
    apply X_prime_wf_helper; eauto; apply IN_D. }

  edestruct (WF'.(WCore.sub_rfD)) as [[w RF] | CMT']; ins.
  { ins. split; eauto. apply IN_D. }
  all: ins.
  assert (W_IN_E : E w).
  { eapply enum_diff_head_rf; eauto.
    unfolder; exists h, h; now splits. }
  assert (W_IN_W : W' w).
  { apply wf_rfD in RF; [| apply WF].
    unfolder in RF; desf. }
  exists h, None, (Some w), ∅, ∅.
  constructor; ins.
  { apply IN_D. }
  { eapply enumd_deltaG_new_event_correct; eauto. }
  { apply union_more; [apply union_more; auto |].
    { split; [| basic_solver].
      intros w' h' (w'' & WINE' & h''' & RF' & WINH).
      destruct WINE', WINH; subst h''' w'' h'.
      erewrite wf_rff with (y := w') (z := w); eauto; try now apply WF.
      basic_solver. }
    unfold WCore.rf_delta_W; ins.
    arewrite (is_w lab' h = false).
    { destruct (is_w lab' h); desf. }
    rewrite wf_rfD; [basic_solver | apply WF]. }
  { unfold WCore.co_delta.
    arewrite (is_w lab' h = false).
    { destruct (is_w lab' h); desf. }
    rewrite wf_coD with (G := G'); [basic_solver | apply WF]. }
  { unfold WCore.rmw_delta, W_ex.
    rewrite wf_rmwD with (G := G'); [| apply WF].
    basic_solver. }
  apply X_prime_wf_helper; auto; apply IN_D.
Qed.

Lemma step_once_write_rmw_helper e
    (WF : WCore.wf X)
    (RMW : rmw' e h)
    (IS_R : R' e)
    (ENUM : enumd_diff G G' cmt (h :: t))
    (NOT_INIT2 : tid h <> tid_init) :
  E e.
Proof using.
  assert (IN_D : (E' \₁ E) h).
  { apply ENUM; desf. }
  assert (NOT_INIT1 : ~is_init e).
  { intro F; destruct e as [l | tide ide]; auto.
    unfold is_r in IS_R; rewrite wf_init_lab in IS_R; auto.
    apply WF. }
  set (CONTH := pfx_cont2 (WCore.pfx WF) NOT_INIT2); desf.
  assert (EQH : exists tidh, h = ThreadEvent tidh N).
  { eexists; eapply add_event_to_contigious with (G' := delta_G G G' h).
    all: eauto.
    { rewrite CONTH; apply thread_seq_set_size. }
    { apply WF. }
    { eapply delta_G_cont_ids; eauto; try now apply IN_D.
      eapply enumd_head_most_sb; eauto. }
    { apply IN_D. }
    unfold delta_G; ins. }
  destruct EQH as [tidh EQH]; subst.
  apply wf_rmwi, immediate_in in RMW; [| apply WF].
  assert (TIDEQ : tid e = tidh).
  { apply sb_tid_init in RMW; desf. }
  destruct e as [l | tide ide]; ins; subst.
  apply in_restr_acts, CONTH.
  unfold sb, ext_sb in RMW; unfolder in RMW; desf.
  unfold thread_seq_set, seq_set; unfolder; eauto.
Qed.

Lemma step_once_write_helper
    (WF : WCore.wf X)
    (NIN : ~E h) :
  ⦗eq h⦘ ⨾ rf' ⨾ ⦗E⦘ ≡ ⦗eq h⦘ ⨾ rf' ⨾ ⦗cmt ∩₁ E⦘.
Proof using.
  split; [| basic_solver].
  unfolder. intros h' r (EQ & RF & INE); subst h'.
  splits; auto. edestruct (WCore.sub_rfD) as [RFD | CMT]; eauto.
  { split; auto. apply wf_rfD in RF; [| apply WF].
    ins; unfolder in RF; desf.
    erewrite sub_lab with (G := G'); ins.
    apply WF. }
  exfalso.
  unfolder in RFD; ins; desf.
  eapply sub_rf in RFD; [| apply WF].
  unfolder in RFD; ins; desf.
  apply NIN; erewrite wf_rff with (y := h) (z := x).
  all: eauto.
  apply WF.
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
  assert (IN_D : (E' \₁ E) h).
  { apply ENUM; desf. }
  assert (NOT_INIT : ~is_init h).
  { eapply diff_no_init with (G := G); eauto. }
  assert (H_TID : tid h <> tid_init).
  { eapply WCore.wf_actid_tid; eauto. apply IN_D. }
  assert (NOT_R : ~R' h).
  { generalize IS_W; unfold is_w, is_r. destruct (lab' h); auto. }

  (* Case 1: h is part of an RMW *)
  destruct (classic (codom_rel rmw' h)) as [[r RMW] | NRMW].
  { assert (IS_R : R' r).
    { apply wf_rmwD in RMW; [| apply WF]. unfolder in RMW; desf. }
    assert (IN_E : E r).
    { eapply step_once_write_rmw_helper; eauto. }
    exists h, (Some r), None,
      (codom_rel (⦗eq h⦘ ⨾ co' ⨾ ⦗E⦘)), (dom_rel (⦗E⦘ ⨾ co' ⨾ ⦗eq h⦘)).
    constructor; ins.
    { apply IN_D. }
    { eapply enumd_deltaG_new_event_correct; eauto. }
    { apply union_more; [apply union_more; auto |].
      { rewrite wf_rfD; [basic_solver | apply WF]. }
      unfold WCore.rf_delta_W. rewrite IS_W.
      apply step_once_write_helper; auto; apply IN_D. }
    { unfold WCore.co_delta. rewrite IS_W.
      rewrite unionA; apply union_more; auto.
      rewrite unionC; apply union_more; basic_solver 5. }
    { apply union_more; auto.
      unfold WCore.rmw_delta, eq_opt, W_ex.
      split; [| basic_solver].
      intros x y RMW'; unfolder in RMW'; desf.
      arewrite (x = r); [| basic_solver].
      eapply wf_rmwf2 with (G := G'); eauto; apply WF. }
    apply X_prime_wf_helper; eauto; apply IN_D. }

  (* Case 2: no rmw *)
  exists h, None, None,
    (codom_rel (⦗eq h⦘ ⨾ co' ⨾ ⦗E⦘)), (dom_rel (⦗E⦘ ⨾ co' ⨾ ⦗eq h⦘)).
  constructor; ins.
  { apply IN_D. }
  { eapply enumd_deltaG_new_event_correct; eauto. }
  { apply union_more; [apply union_more; auto |].
    { rewrite wf_rfD; [basic_solver | apply WF]. }
    unfold WCore.rf_delta_W. rewrite IS_W.
    apply step_once_write_helper; auto; apply IN_D. }
  { unfold WCore.co_delta. rewrite IS_W.
    rewrite unionA; apply union_more; auto.
    rewrite unionC; apply union_more; basic_solver 5. }
  { apply union_more; auto.
    unfold WCore.rmw_delta, eq_opt, W_ex.
    split; [| basic_solver].
    intros x y RMW'; unfolder in RMW'; desf.
    exfalso; unfolder in NRMW; eauto. }
  apply X_prime_wf_helper; eauto; apply IN_D.
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

  exists h, None, None, ∅, ∅.
  constructor; ins.
  { apply IN_D. }
  { eapply enumd_deltaG_new_event_correct; eauto. }
  { apply union_more; [apply union_more; auto |].
    { rewrite wf_rfD; [basic_solver | apply WF]. }
    unfold WCore.rf_delta_W.
    arewrite (is_w lab' h = false).
    { destruct (is_w lab' h); desf. }
    rewrite wf_rfD; [basic_solver | apply WF]. }
  { unfold WCore.co_delta.
    arewrite (is_w lab' h = false).
    { destruct (is_w lab' h); desf. }
    arewrite (⦗eq h⦘ ⨾ co' ⨾ ⦗E⦘ ≡ ∅₂).
    { rewrite wf_coD; [basic_solver | apply WF]. }
    arewrite (⦗E⦘ ⨾ co' ⨾ ⦗eq h⦘ ≡ ∅₂).
    { rewrite wf_coD; [basic_solver | apply WF]. }
    basic_solver. }
  { apply union_more; auto.
    arewrite (⦗E⦘ ⨾ rmw' ⨾ ⦗eq h⦘ ≡ ∅₂).
    { rewrite wf_rmwD; [basic_solver | apply WF]. }
    unfold WCore.rmw_delta; basic_solver. }
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

(*



(* NOTE: xmm is doing only prefix restriction *)

End ReorderingSubLemma.

Section ReorderingLemma.

Variable traces : thread_id -> trace label -> Prop.

Definition final_f G f :=
  fun x => ifP acts_set G x then f x else Some x.

Lemma steps C G G' l f f'
    (FFEQ : f' = final_f G f)
    (F_ID : partial_id f')
    (SUB_ID : sub_fun f f')
    (WF : WCore.wf (WCore.Build_t G G' C f))
    (WF' : WCore.wf (WCore.Build_t G' G' C f'))
    (G_PREFIX : restr_exec (acts_set G) G' G)
    (SUB_TRACE : exec_trace_prefix G' G)
    (ENUM : reord_lemma_enum G G' (acts_set G) (acts_set G') C l)
    (COH : trace_coherent traces G')
    (CONT : contigious_actids G') :
  (WCore.cfg_add_event_uninformative traces)＊
    (WCore.Build_t G G' C f)
    (WCore.Build_t G' G' C f').
Proof using.
  generalize f G FFEQ SUB_ID WF G_PREFIX SUB_TRACE ENUM.
  clear      f G FFEQ SUB_ID WF G_PREFIX SUB_TRACE ENUM.
  induction l as [ | h t IHl]; ins.
  { assert (GEQ : G = G').
    { apply sub_eq.
      { apply WF. }
      { apply G_PREFIX. }
      rewrite <- relenum_d; eauto; ins. }
    assert (FEQ : f' = f).
    { rewrite FFEQ. unfold final_f.
      apply functional_extensionality; intro x; desf.
      exfalso; apply n.
      change G' with (WCore.GC (WCore.Build_t G' G' C (final_f G' f))).
      eapply WCore.f_dom; ins.
      unfold is_some, compose; ins.
      unfold final_f. desf. }
    rewrite GEQ, FEQ. apply rt_refl. }
  assert (STEP : WCore.cfg_add_event_uninformative traces
    (WCore.Build_t G                G' C f)
    (WCore.Build_t (delta_G G G' h) G' C (upd f h (Some h)))).
  { eapply step_once; eauto. }
  apply rt_trans with (y := (WCore.Build_t (delta_G G G' h) G' C (upd f h (Some h)))).
  { now apply rt_step. }
  apply IHl.
  { rewrite FFEQ; unfold final_f; apply functional_extensionality.
    intro x; desf; destruct (classic (x = h)); subst; rupd; auto.
    all: exfalso.
    { eapply relenum_d; eauto; desf. }
    all: apply n; ins.
    { now right. }
    { now left. }
    unfolder in a; desf. }
  { arewrite (Some h = f' h); auto using sub_fun_upd.
    symmetry; rewrite FFEQ; unfold final_f.
    desf. exfalso; eapply relenum_d; eauto; desf. }
  { do 2 (red in STEP; desf). apply STEP. }
  { constructor; ins.
    { eapply delta_G_sub; eauto.
      all: try now apply G_PREFIX.
      eapply (WCore.wf_actid_tid WF').
      all: apply ENUM; desf. }
    rewrite set_inter_union_l.
    arewrite (eq h ∩₁ is_init ≡₁ ∅).
    { enough (~is_init h) by basic_solver.
      apply ENUM; desf. }
    rewrite set_union_empty_r.
    apply G_PREFIX. }
  { eapply delta_G_prefix; eauto.
    apply G_PREFIX. }
  constructor; ins.
  { eapply nodup_consD, ENUM. }
  { transitivity (fun x => In x (h :: t)); [ | apply ENUM].
    unfolder; ins; desf; eauto. }
  { arewrite ((fun x => In x t) ≡₁ (fun x => In x (h :: t)) \₁ eq h).
    { ins; split; [| basic_solver].
      intros x IN; unfolder; split; eauto.
      intro F; subst.
      apply nodup_cons with (x := x) (l := t); auto.
      apply ENUM. }
    rewrite relenum_d with (l := h :: t); eauto.
    now rewrite set_minus_minus_l. }
  { intros x y SB. unfolder in SB; desf.
    assert (LT : total_order_from_list (h :: t) x y).
    { eapply relenum_sb; unfolder; splits; ins; eauto. }
    apply total_order_from_list_cons in LT; desf.
    exfalso; eapply nodup_not_in.
    { apply ENUM. }
    { exact SB0. }
    reflexivity. }
  { intros x y RF. unfolder in RF; desf.
    assert (LT : total_order_from_list (h :: t) x y).
    { eapply relenum_rf; unfolder; splits; ins; eauto. }
    apply total_order_from_list_cons in LT; desf.
    exfalso; eapply nodup_not_in.
    { apply ENUM. }
    { exact RF2. }
    reflexivity. }
  intros x IN.
  destruct (classic (h = x)) as [EQ|NEQ]; subst.
  { apply ENUM; desf. }
  eapply relenum_rf_w; eauto.
  eapply dom_rel_mori; eauto; basic_solver.
Qed.
*)