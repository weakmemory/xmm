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
  { rewrite (sub_rmw SUB), <- !restr_relE, restr_set_union.
    rewrite restr_irrefl_eq; eauto using rmw_irr.
    arewrite (⦗eq h⦘ ⨾ rmw' ⨾ ⦗E⦘ ≡ ∅₂); [| now rewrite !union_false_r].
    split; [|basic_solver]. unfolder; ins; desf.
    change G with (WCore.G X) in NEW.
    enough (EXT : ext_sb x y); eauto using WCore.ext_sb_dense.
    enough (SB : sb' x y); try now apply wf_rmwi; ins.
    unfold sb in SB; unfolder in SB; desf. }
  { rewrite (WCore.cc_data_empty WF).
    now rewrite seq_false_l, seq_false_r. }
  { rewrite (WCore.cc_addr_empty WF).
    now rewrite seq_false_l, seq_false_r. }
  { rewrite (WCore.cc_ctrl_empty WF).
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
  unfold contigious_actids; ins.
  set (CONT1 := WCore.wf_gc_cont WF NOT_INIT).
  set (CONT2 := WCore.wf_g_cont WF NOT_INIT).
  destruct CONT1 as [N1 CONT1], CONT2 as [N2 CONT2].
  destruct (classic (t = tid h)); subst.
  { exists (1 + N2). rewrite thread_set_S, set_inter_union_l, CONT2.
    arewrite (eq h ∩₁ same_tid h ≡₁ eq h) by basic_solver.
    apply set_union_more; [auto | apply set_equiv_single_single].
    destruct h as [l | ht hid]; unfold same_tid in *; ins.
    f_equal. assert (LT : hid < N1).
    { eapply thread_set_iff, CONT1; now split. }
    apply PeanoNat.Nat.le_antisymm.
    assert (IN : E' (ThreadEvent ht (hid - 1))).
    { apply in_restr_acts, CONT1, thread_set_iff; lia. }
    { apply Compare_dec.not_gt. intro GT.
      apply NEXT with (x := ThreadEvent ht (hid - 1)).
      { split; auto.
        intro F; apply in_restr_acts, CONT2, thread_set_iff in F; lia. }
      unfold sb, ext_sb; ins. unfolder; splits; auto; try lia. }
    eapply thread_set_niff. intro F.
    apply CONT2, in_restr_acts in F; auto. }
  exists N2. rewrite set_inter_union_l, CONT2.
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

Lemma restr_irr A (x : A) s r
    (IRR : irreflexive r) :
  restr_rel (s ∩₁ eq x) r ≡ ∅₂.
Proof using.
  destruct (classic (s x)) as [HIN|HIN]; [| basic_solver].
  arewrite (s ∩₁ eq x ≡₁ eq x) by basic_solver.
  now apply restr_irrefl_eq.
Qed.

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
  constructor; ins.
  all: try now apply WF.
  { transitivity E; [apply WF | basic_solver]. }
  { rewrite delta_G_sb; auto; [| apply WF].
    rewrite set_inter_union_r, restr_set_union, restr_irr by apply sb_irr.
    rewrite restr_relE, union_false_r; repeat apply inclusion_union_mon.
    { rewrite sub_sb with (G := G') (G' := G); [basic_solver | apply WF]. }
    all: basic_solver. }
  { rewrite set_inter_union_r, restr_set_union, restr_irr by apply rf_irr, WF.
    rewrite restr_relE, union_false_r; repeat apply inclusion_union_mon.
    { rewrite sub_rf with (G := G') (G' := G); [basic_solver | apply WF]. }
    all: basic_solver. }
  { rewrite set_inter_union_l, !codom_union.
    apply set_subset_union_l; split.
    { transitivity (codom_rel rf ∪₁ cmt); [apply WF | basic_solver 5]. }
    destruct (classic (is_r lab' h)) as [ISR|ISR].
    { edestruct (WF_fin.(WCore.sub_rfD)) as [RD|RD],
                (classic (cmt h)) as [CMT|CMT].
      all: try basic_solver 2.
      transitivity (codom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘)); [| basic_solver 7].
      assert (SUBE : dom_rel (rf' ⨾ ⦗eq h⦘) ⊆₁ E).
      { eapply enum_diff_head_rf; eauto. }
      generalize RD SUBE; unfolder; ins; desf; eauto 11. }
    arewrite (eq h ∩₁ (fun a => is_r lab a) ≡₁ ∅); [| basic_solver].
    erewrite sub_lab; [| apply WF]; ins. basic_solver. }
  eapply enumd_deltaG_prefix; eauto.
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
  (* Proof of step *)
  exists h, None, (Some w), ∅, ∅.
  constructor; ins.
  { apply IN_D. }
  { eapply enumd_deltaG_new_event_correct; eauto. }
  { repeat apply union_more; auto.
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
    rewrite wf_rmwD with (G := G'); [basic_solver | apply WF]. }
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
  (* Case 1: cmt h *)
  destruct (classic (cmt h)) as [CMT|CMT].
  { (* Even if h is cmt -- we still need to add accompanying edges! *)
    destruct (classic (codom_rel (⦗E⦘ ⨾ rf') h)) as [RF | NRF].
    { destruct RF as (w & w' & (EQ & INE) & RF); subst w'.
      (* In this situation, this case is actuall like ~cmt h *)
      eapply step_once_read_helper; eauto. }
    exists h, None, None, ∅, ∅.
    constructor; ins.
    { apply IN_D. }
    { eapply enumd_deltaG_new_event_correct; eauto. }
    { repeat apply union_more; auto.
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
      rewrite wf_coD with (G := G'); [basic_solver | apply WF]. }
    { unfold WCore.rmw_delta, W_ex.
      rewrite wf_rmwD with (G := G'); [basic_solver| apply WF]. }
    apply X_prime_wf_helper; eauto; apply IN_D. }
  (* Case 2: ~cmt h *)
  edestruct (WF'.(WCore.sub_rfD)) as [[w RF] | CMT']; ins.
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

Section SubToFullExec.

Variable traces : thread_id -> trace label -> Prop.

Lemma sub_to_full_exec G G' cmt l
    (WF : WCore.wf (WCore.Build_t G G' cmt))
    (WF' : WCore.wf (WCore.Build_t G' G' cmt))
    (ENUM : SubToFullExecInternal.enumd_diff G G' cmt l)
    (COH : trace_coherent traces G') :
  (WCore.cfg_add_event_uninformative traces)＊
    (WCore.Build_t G G' cmt)
    (WCore.Build_t G' G' cmt).
Proof using.
  generalize G WF ENUM.
  clear      G WF ENUM.
  induction l as [ | h t IHl]; ins.
  { arewrite (G = G'); [| apply rt_refl].
    eapply SubToFullExecInternal.enum_diff_done; eauto. }
  set (delta_G := SubToFullExecInternal.delta_G G G' h).
  assert (STEP : WCore.cfg_add_event_uninformative traces
    (WCore.Build_t G                G' cmt)
    (WCore.Build_t delta_G          G' cmt)).
  { eapply SubToFullExecInternal.step_once; eauto. }
  eapply rt_trans; [apply rt_step; eauto | ].
  red in STEP; desf.
  apply IHl; [eapply WCore.new_conf_wf; eauto |].
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
  destruct (classic (h = x)) as [EQ|NEQ]; subst.
  { apply ENUM; desf. }
  eapply SubToFullExecInternal.diff_rf_d; eauto.
  eapply dom_rel_mori; eauto; basic_solver.
Qed.

End SubToFullExec.