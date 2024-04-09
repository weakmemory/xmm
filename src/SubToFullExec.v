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
Variable g2gc : actid -> option actid.
Variable h : actid.

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
Notation "'sb'" := (sb G').
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

Definition g2gc_fin x :=
    ifP E x then g2gc x
    else ifP E' x then Some x
    else None.

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
  WCore.g2gc := g2gc;
  WCore.cmt := cmt;
|}).
Notation "'X''" := ({|
  WCore.G := delta_G;
  WCore.GC := G';
  WCore.g2gc := upd g2gc h (Some h);
  WCore.cmt := cmt;
|}).
Notation "'X_fin'" := ({|
  WCore.G := G';
  WCore.GC := G';
  WCore.g2gc := g2gc_fin;
  WCore.cmt := cmt;
|}).


Lemma over_exec_wf
    (WF : Wf G')
    (F_ID : partial_id g2gc)
    (CTRL : ctrl' ≡ ∅₂)
    (ADDR : addr' ≡ ∅₂)
    (DATA : data' ≡ ∅₂)
    (A_CORRECT : partial_id_dom g2gc ⊆₁ E)
    (C_CORRECT : cmt ⊆₁ E')
    (SUB_INIT : E' ∩₁ is_init ⊆₁ E)
    (G_RF_D : E ∩₁ R ⊆₁ codom_rel rf ∪₁ (Some ↓₁ (g2gc ↑₁ cmt)))
    (G_TIDS : (tid ↓₁ eq tid_init) ∩₁ E' ⊆₁ is_init)
    (G_ACTS : forall thr (NOT_INIT : thr <> tid_init),
      exists N, E ∩₁ (fun x => thr = tid x) ≡₁ thread_seq_set thr N)
    (SUB : sub_execution G' G ∅₂ ∅₂) :
  WCore.wf X.
Proof using.
  unfold partial_id_dom in *.
  assert (ACT_SUB : E ⊆₁ E').
  { apply SUB. }
  constructor; ins.
  { rewrite sub_ctrl, CTRL; eauto; basic_solver. }
  { rewrite sub_addr, ADDR; eauto; basic_solver. }
  { rewrite sub_data, DATA; eauto; basic_solver. }
  { eapply sub_WF; eauto. now rewrite set_interC. }
  { now rewrite ACT_SUB. }
  { transitivity E; auto; apply A_CORRECT. }
  { rewrite partial_id_set; eauto; basic_solver. }
  { now apply partial_id_inj. }
  { rewrite sub_sb with (G' := G), partial_id_rel, !restr_relE; eauto.
    basic_solver. }
  { rewrite sub_rf with (G' := G), partial_id_rel, !restr_relE; eauto.
    basic_solver. }
  { rewrite partial_id_sub_eq; auto; basic_solver. }
  { unfold WCore.unwrap_g2gc, same_lab_u2v_dom,
          is_some, compose.
    unfolder. ins. desf.
    erewrite sub_lab, (F_ID e a); eauto.
    red. desf. }
  unfold compose, is_some in SOME.
  unfold WCore.unwrap_g2gc, val.
  erewrite sub_lab; eauto.
  ins. destruct (g2gc c) eqn:HEQ; ins.
  apply F_ID in HEQ; now subst.
Qed.

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

Lemma delta_G_prefix
    (HIN : E' h)
    (PREFIX : exec_trace_prefix G' G)
    (SUB : sub_execution G' G ∅₂ ∅₂) :
  exec_trace_prefix G' delta_G.
Proof using.
  assert (SUBE : E ⊆₁ E') by now apply SUB.
  unfold exec_trace_prefix; ins.
  destruct (classic (thr = (tid h))) as [HEQ|NEQ]; subst.
  { apply thread_actid_trace_prefix; ins.
    apply set_subset_inter; basic_solver. }
  unfold thread_actid_trace; ins.
  arewrite ((E ∪₁ eq h) ∩₁ (fun e => thr = tid e) ≡₁ E ∩₁ (fun e => thr = tid e)).
  { basic_solver. }
  apply PREFIX.
Qed.

Lemma delta_G_cont_ids
    (HIN : E' h)
    (PREFIX : exec_trace_prefix G' G)
    (CONTFIN : contigious_actids G')
    (CONT : contigious_actids G)
    (NEXT : dom_rel (same_tid ∩ (sb ⨾ ⦗eq h⦘)) ≡₁ same_tid h ∩₁ E)
    (SUB : sub_execution G' G ∅₂ ∅₂) :
  contigious_actids delta_G.
Proof using.
  apply trace_form_sub with (G := G'); auto.
  now apply delta_G_prefix.
Qed.

Lemma delta_G_actid_trace_h
    (NOT_INIT : ~is_init h)
    (HIN : E' h)
    (NHIN : ~E h)
    (PREFIX : exec_trace_prefix G' G)
    (SUB : sub_execution G' G ∅₂ ∅₂)
    (WF : WCore.wf X)
    (WF_fin : WCore.wf X_fin) :
  thread_trace delta_G (tid h) =
    trace_app (thread_trace G (tid h)) (trace_fin [lab' h]).
Proof using.
  assert (NOT_INIT' : tid h <> tid_init) by eauto using WCore.wf_actid_tid.
  set (CONT := WCore.actid_cont WF NOT_INIT'); desf.
  arewrite (lab' = delta_G.(lab)) by symmetry; apply SUB.
  eapply add_event_to_trace; eauto; ins.
  { now rewrite updI. }
  { now rewrite CONT, thread_seq_set_size. }
  { apply WF. }
  apply trace_form_sub with (G := G'), delta_G_prefix; eauto.
  now apply WF_fin.
Qed.

End DeltaGraph.

Section EnumeratedDifference.

Variable G G' : execution.
Variable cmt : actid -> Prop.
Variable g2gc : actid -> option actid.

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
  (* Prefix stuff *)
  g_restr : sub_execution G' G ∅₂ ∅₂;
  g_same_init : acts_set G ∩₁ is_init ≡₁ acts_set G' ∩₁ is_init;
  g_prfx : exec_trace_prefix G' G;
  (* Actual enum properties *)
  nodup : NoDup l;
  diff_elems : E' \₁ E ≡₁ fun x => In x l;
  diff_sb : restr_rel (E' \₁ E) sb' ⊆ total_order_from_list l;
  diff_rf : restr_rel (E' \₁ E) rf' ⨾ ⦗E' \₁ cmt⦘ ⊆ total_order_from_list l;
  diff_rf_d : dom_rel (rf' ⨾ ⦗E' \₁ E⦘) ⊆₁ E';
  (* Helper properties *)
  g2gc_id : partial_id g2gc;
  gc_ctrl_empty : ctrl G' ≡ ∅₂;
  gc_addr_empty : addr G' ≡ ∅₂;
  gc_data_empty : data G' ≡ ∅₂;
}.

Notation "'X'" := ({|
  WCore.G := G;
  WCore.GC := G';
  WCore.g2gc := g2gc;
  WCore.cmt := cmt;
|}).
Notation "'X_fin'" := ({|
  WCore.G := G';
  WCore.GC := G';
  WCore.g2gc := g2gc_fin G G' g2gc;
  WCore.cmt := cmt;
|}).

Lemma enumd_head_most_sb h t
    (ENUM : enumd_diff (h :: t)) :
  dom_rel (same_tid ∩ (sb' ⨾ ⦗eq h⦘)) ≡₁ same_tid h ∩₁ E.
Proof using.
  admit.
Admitted.

Lemma diff_no_init l
    (ENUM : enumd_diff l) :
  E' \₁ E ⊆₁ set_compl is_init.
Proof.
  rewrite <- set_inter_full_r with (s := E'),
          <- set_inter_full_r with (s := E),
          set_full_split with (S := is_init),
          !set_inter_union_r.
  rewrite (g_same_init l ENUM).
  basic_solver 5.
Qed.

Lemma diff_G_wf l
    (WF : Wf G')
    (ENUM : enumd_diff l) :
  Wf G.
Proof using.
  eapply sub_WF with (G := G'); auto; try now apply ENUM.
  rewrite set_interC, <- (g_same_init l ENUM).
  basic_solver.
Qed.

Lemma enum_diff_done
    (WF : Wf G')
    (DONE : enumd_diff []) :
  G = G'.
Proof using.
  apply sub_eq; eauto using g_restr.
  now rewrite (diff_elems [] DONE).
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
  apply (diff_rf _ ENUM).
  unfolder; splits; eauto.
  all: try now apply (diff_elems _ ENUM); desf.
  apply wf_rfE in RF; [unfolder in RF; desf | apply XWF].
Qed.

Lemma enum_diff_sub_fun l
    (XWF : WCore.wf X)
    (ENUM : enumd_diff l) :
  sub_fun g2gc (g2gc_fin G G' g2gc).
Proof using.
  unfold sub_fun, g2gc_fin; intros x y Heq. desf.
  { rewrite <- (g2gc_id l ENUM); eauto. }
  exfalso; apply n0, (WCore.f_dom XWF).
  unfold is_some, compose. ins.
  now rewrite Heq.
Qed.

Lemma enum_diff_part_id l
    (ENUM : enumd_diff l) :
  partial_id (g2gc_fin G G' g2gc).
Proof using.
  unfold partial_id, g2gc_fin; intros x y Heq. desf.
  now apply (g2gc_id l ENUM).
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
Variable g2gc : actid -> option actid.
Variable traces : thread_id -> trace label -> Prop.
Variable h : actid.
Variable t : list actid.

Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'W''" := (fun x => is_w lab' x).
Notation "'R''" := (fun x => is_r lab' x).
Notation "'g2gc''" := (g2gc_fin G G' g2gc).

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'W'" := (fun x => is_w lab x).
Notation "'R'" := (fun x => is_r lab x).

Notation "'X'" := ({|
  WCore.G := G;
  WCore.GC := G';
  WCore.g2gc := g2gc;
  WCore.cmt := cmt;
|}).
Notation "'X''" := ({|
  WCore.G := delta_G G G' h;
  WCore.GC := G';
  WCore.g2gc := upd g2gc h (Some h);
  WCore.cmt := cmt;
|}).
Notation "'X_fin'" := ({|
  WCore.G := G';
  WCore.GC := G';
  WCore.g2gc := g2gc_fin G G' g2gc;
  WCore.cmt := cmt;
|}).

Lemma wf_partial_id_dome
    (G2GC_ID : partial_id g2gc)
    (WF : WCore.wf X) :
  partial_id_dom g2gc ⊆₁ E.
Proof using.
  transitivity (Some ↓₁ (g2gc ↑₁ E')); [ | apply WF].
  rewrite partial_id_set; auto.
  unfolder; ins; split; auto.
  change E' with (acts_set (WCore.GC X)).
  now eapply WCore.f_dom.
Qed.

Lemma step_once_read_helper w
    (WF : WCore.wf X)
    (WF' : WCore.wf X_fin)
    (ENUM : enumd_diff G G' cmt g2gc (h :: t))
    (RF : rf' w h)
    (COH : trace_coherent traces G')
    (INE : E w) :
  WCore.cfg_add_event_uninformative traces X X'.
Proof using.
  (* Information about h *)
  assert (IN_D : (E' \₁ E) h).
  { apply ENUM; desf. }
  assert (NOT_INIT : ~is_init h).
  { eapply diff_no_init; eauto. }
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
  assert (PART : partial_id g2gc).
  { apply ENUM. }
  assert (DELTA_SUB : sub_execution G' (delta_G G G' h) ∅₂ ∅₂).
  { eapply delta_G_sub; eauto; try now apply IN_D. apply ENUM. }
  assert (DELTA_PREF : exec_trace_prefix G' (delta_G G G' h)).
  { eapply delta_G_prefix; try now apply ENUM.
    apply IN_D. }
  assert (DELTA_COH : trace_coherent traces (delta_G G G' h)).
  { eapply trace_coherent_sub; eauto. }
  assert (UPDID : partial_id (upd g2gc h (Some h))).
  { now apply upd_partial_id. }

  exists h, (lab' h), None, (Some w), ∅, ∅, (Some h).
  constructor; ins.
  { apply IN_D. }
  (* TODO: prettify *)
  { set (DCOH := DELTA_COH (tid h) H_TID). ins. desf.
    unfold WCore.new_event_correct. desf.
    { exists tr.
      erewrite sub_lab; eauto.
      erewrite delta_G_actid_trace_h in PREFIX; eauto.
      all: try now apply ENUM.
      all: try now apply IN_D.
      split; ins. now rewrite Heq in PREFIX. }
    set (FIN := WCore.all_trace_fin WF H_TID).
    ins. rewrite Heq in FIN.
    unfold trace_finite in FIN. desf. }
  { erewrite sub_lab; [now rewrite updI | apply ENUM]. }
  (* TODO: prettify? *)
  { apply union_more; [apply union_more; auto |].
    { split; [| basic_solver].
    erewrite sub_lab by apply ENUM.
    intros w' h' (w'' & WINE' & h''' & RF' & WINH).
    destruct WINE', WINH; subst h''' w'' h'.
    erewrite wf_rff with (y := w') (z := w); eauto; try now apply WF.
    basic_solver. }
    unfold WCore.rf_delta_W; ins.
    rewrite partial_id_collect_eq, upds, partial_id_set; eauto.
    rewrite <- seqA with (r2 := rf') (r3 := ⦗E⦘).
    arewrite (⦗eq h⦘ ⨾ rf' ≡ ∅₂); [| basic_solver].
    rewrite wf_rfD; [| apply WF].
    basic_solver. }
  { unfold WCore.co_delta.
    erewrite sub_lab; [| apply ENUM].
    arewrite (is_w lab' h = false).
    { destruct (is_w lab' h); desf. }
    rewrite wf_coD with (G := G'); [| apply WF].
    basic_solver. }
  { unfold WCore.rmw_delta, W_ex.
    rewrite wf_rmwD with (G := G'); [| apply WF].
    rewrite wf_rmwD with (G := G); [| apply WF].
    basic_solver. }
  apply over_exec_wf; ins.
  all: try now apply WF.
  { rewrite partial_id_upd_dom. apply set_subset_union; auto.
    apply wf_partial_id_dome; eauto. }
  { rewrite <- restr_init_sub; eauto.
    { transitivity E; basic_solver. }
    constructor; try now apply ENUM.
    apply set_equiv_refl2. }
  (* TODO prettify? *)
  { arewrite (⦗eq h⦘ ⨾ rf' ⨾ ⦗E⦘ ≡ ∅₂).
    { rewrite wf_rfD; [basic_solver | apply WF]. }
    rewrite union_false_r, codom_union, set_inter_union_l.
    arewrite (codom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘) ≡₁ eq h).
    { basic_solver. }
    transitivity (codom_rel rf ∪₁
      Some ↓₁ (upd g2gc h (Some h) ↑₁ cmt) ∪₁ eq h); [| basic_solver].
    apply set_subset_union; [| basic_solver].
    transitivity (codom_rel rf ∪₁ Some ↓₁ (g2gc ↑₁ cmt)); [apply WF |].
    apply set_subset_union; eauto.
    rewrite !partial_id_set, partial_id_upd_dom; eauto.
    basic_solver. }
  enough (CONT : contigious_actids (delta_G G G' h)).
  { now apply CONT. }
  apply delta_G_cont_ids; eauto.
  all: try now apply ENUM.
  { apply IN_D. }
  { apply WF'. }
  { apply WF. }
  eapply enumd_head_most_sb; eauto.
Qed.

Lemma step_once_read
    (WF : WCore.wf X)
    (WF' : WCore.wf X_fin)
    (ENUM : enumd_diff G G' cmt g2gc (h :: t))
    (COH : trace_coherent traces G')
    (IS_R : R' h) :
  WCore.cfg_add_event_uninformative traces X X'.
Proof using.
  (* Information about h *)
  assert (IN_D : (E' \₁ E) h).
  { apply ENUM; desf. }
  assert (NOT_INIT : ~is_init h).
  { eapply diff_no_init; eauto. }
  assert (H_TID : tid h <> tid_init).
  { eapply WCore.wf_actid_tid; eauto. apply IN_D. }
  assert (NOT_W : ~W' h).
  { generalize IS_R; unfold is_w, is_r.
    destruct (lab' h); auto. }
  assert (PART : partial_id g2gc).
  { apply ENUM. }
  assert (DELTA_SUB : sub_execution G' (delta_G G G' h) ∅₂ ∅₂).
  { eapply delta_G_sub; eauto; try now apply IN_D. apply ENUM. }
  assert (DELTA_PREF : exec_trace_prefix G' (delta_G G G' h)).
  { eapply delta_G_prefix; try now apply ENUM. apply IN_D. }
  assert (DELTA_COH : trace_coherent traces (delta_G G G' h)).
  { eapply trace_coherent_sub; eauto. }
  assert (UPDID : partial_id (upd g2gc h (Some h))).
  { now apply upd_partial_id. }

  destruct (classic (cmt h)) as [CMT|CMT].
  { destruct (classic (codom_rel (⦗E⦘ ⨾ rf') h)) as [RF | NRF].
    { destruct RF as (w & w' & (EQ & INE) & RF); subst w'.
      eapply step_once_read_helper; eauto. }
    exists h, (lab' h), None, None, ∅, ∅, (Some h).
    constructor; ins.
    { apply IN_D. }
    { set (DCOH := DELTA_COH (tid h) H_TID). ins. desf.
      unfold WCore.new_event_correct. desf.
      { exists tr.
        erewrite sub_lab; eauto.
        erewrite delta_G_actid_trace_h in PREFIX; eauto.
        all: try now apply ENUM.
        all: try now apply IN_D.
        split; ins. now rewrite Heq in PREFIX. }
      set (FIN := WCore.all_trace_fin WF H_TID).
      ins. rewrite Heq in FIN.
      unfold trace_finite in FIN. desf. }
    { erewrite sub_lab; [now rewrite updI | apply ENUM]. }
    (* TODO: prettify? *)
    { apply union_more; [apply union_more; auto |].
      { split; [| basic_solver].
        intros w h' RF. apply seqA in RF.
        apply NRF. exists w.
        unfolder; unfolder in RF; desf. }
      unfold WCore.rf_delta_W; ins.
      rewrite partial_id_collect_eq, upds, partial_id_set; eauto.
      rewrite <- seqA with (r2 := rf') (r3 := ⦗E⦘).
      arewrite (⦗eq h⦘ ⨾ rf' ≡ ∅₂); [| basic_solver].
      rewrite wf_rfD; [| apply WF].
      basic_solver. }
    { unfold WCore.co_delta.
      erewrite sub_lab; [| apply ENUM].
      arewrite (is_w lab' h = false).
      { destruct (is_w lab' h); desf. }
      rewrite wf_coD with (G := G'); [| apply WF].
      basic_solver. }
    { unfold WCore.rmw_delta, W_ex.
      rewrite wf_rmwD with (G := G'); [| apply WF].
      rewrite wf_rmwD with (G := G); [| apply WF].
      basic_solver. }
    apply over_exec_wf; ins.
    all: try now apply WF.
    { rewrite partial_id_upd_dom. apply set_subset_union; auto.
      apply wf_partial_id_dome; eauto. }
    { rewrite <- restr_init_sub; eauto.
      { transitivity E; basic_solver. }
      constructor; try now apply ENUM.
      apply set_equiv_refl2. }
    (* TODO prettify? *)
    { arewrite (⦗eq h⦘ ⨾ rf' ⨾ ⦗E⦘ ≡ ∅₂).
      { rewrite wf_rfD; [basic_solver | apply WF]. }
      rewrite union_false_r, codom_union, set_inter_union_l.
      arewrite (codom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘) ≡₁ ∅).
      { split; [| basic_solver].
        intros h' RF. exfalso; apply NRF.
        unfolder; unfolder in RF; desf; eauto. }
      rewrite set_union_empty_r.
      apply set_subset_union_l; split.
      { transitivity (codom_rel rf ∪₁ Some ↓₁ (g2gc ↑₁ cmt)); [apply WF |].
        apply set_subset_union; eauto.
        rewrite !partial_id_set, partial_id_upd_dom; eauto.
        basic_solver. }
      intros h' [EQ IS_R']; subst h'; right.
      apply partial_id_set; auto. split; auto.
      apply partial_id_upd_dom; now right. }
    enough (CONT : contigious_actids (delta_G G G' h)).
    { now apply CONT. }
    apply delta_G_cont_ids; eauto.
    all: try now apply ENUM.
    { apply IN_D. }
    { apply WF'. }
    { apply WF. }
    eapply enumd_head_most_sb; eauto.
  }

  edestruct WCore.f_rfD as [[w RF] | CMT']; ins.
  { apply WF'. }
  { ins. split; eauto. apply IN_D. }
  all: ins.
  (* CASE 1: h is reading *)
  { (* TODO: formula for rf *)
    assert (W_IN_E : E w).
    { eapply enum_diff_head_rf with (g2gc := g2gc); eauto.
      unfolder; exists h, h; now splits. }
    assert (W_IN_W : W' w).
    { apply wf_rfD in RF; [| apply WF].
      unfolder in RF; desf. }
    exists h, (lab' h), None, (Some w), ∅, ∅, (Some h).
    constructor; ins.
    { apply IN_D. }
    (* TODO: prettify *)
    { set (DCOH := DELTA_COH (tid h) H_TID). ins. desf.
      unfold WCore.new_event_correct. desf.
      { exists tr.
        erewrite sub_lab; eauto.
        erewrite delta_G_actid_trace_h in PREFIX; eauto.
        all: try now apply ENUM.
        all: try now apply IN_D.
        split; ins. now rewrite Heq in PREFIX. }
      set (FIN := WCore.all_trace_fin WF H_TID).
      ins. rewrite Heq in FIN.
      unfold trace_finite in FIN. desf. }
    { erewrite sub_lab; [now rewrite updI | apply ENUM]. }
    (* TODO: prettify? *)
    { apply union_more; [apply union_more; auto |].
      { split; [| basic_solver].
        erewrite sub_lab by apply ENUM.
        intros w' h' (w'' & WINE' & h''' & RF' & WINH).
        destruct WINE', WINH; subst h''' w'' h'.
        erewrite wf_rff with (y := w') (z := w); eauto; try now apply WF.
        basic_solver. }
      unfold WCore.rf_delta_W; ins.
      rewrite partial_id_collect_eq, upds, partial_id_set; eauto.
      rewrite <- seqA with (r2 := rf') (r3 := ⦗E⦘).
      arewrite (⦗eq h⦘ ⨾ rf' ≡ ∅₂); [| basic_solver].
      rewrite wf_rfD; [| apply WF].
      basic_solver. }
    { unfold WCore.co_delta.
      erewrite sub_lab; [| apply ENUM].
      arewrite (is_w lab' h = false).
      { destruct (is_w lab' h); desf. }
      rewrite wf_coD with (G := G'); [| apply WF].
      basic_solver. }
    { unfold WCore.rmw_delta, W_ex.
      rewrite wf_rmwD with (G := G'); [| apply WF].
      rewrite wf_rmwD with (G := G); [| apply WF].
      basic_solver. }
    apply over_exec_wf; ins.
    all: try now apply WF.
    { rewrite partial_id_upd_dom. apply set_subset_union; auto.
      apply wf_partial_id_dome; eauto. }
    { rewrite <- restr_init_sub; eauto.
      { transitivity E; basic_solver. }
      constructor; try now apply ENUM.
      apply set_equiv_refl2. }
    (* TODO prettify? *)
    { arewrite (⦗eq h⦘ ⨾ rf' ⨾ ⦗E⦘ ≡ ∅₂).
      { rewrite wf_rfD; [basic_solver | apply WF]. }
      rewrite union_false_r, codom_union, set_inter_union_l.
      arewrite (codom_rel (⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘) ≡₁ eq h).
      { basic_solver. }
      transitivity (codom_rel rf ∪₁
        Some ↓₁ (upd g2gc h (Some h) ↑₁ cmt) ∪₁ eq h); [| basic_solver].
      apply set_subset_union; [| basic_solver].
      transitivity (codom_rel rf ∪₁ Some ↓₁ (g2gc ↑₁ cmt)); [apply WF |].
      apply set_subset_union; eauto.
      rewrite !partial_id_set, partial_id_upd_dom; eauto.
      basic_solver. }
    enough (CONT : contigious_actids (delta_G G G' h)).
    { now apply CONT. }
    apply delta_G_cont_ids; eauto.
    all: try now apply ENUM.
    { apply IN_D. }
    { apply WF'. }
    { apply WF. }
    eapply enumd_head_most_sb; eauto. }
  (* CASE 2: h is commited *)
  exfalso.
  apply partial_id_set in CMT'; eauto.
  apply CMT, CMT'.
  eapply enum_diff_part_id; eauto.
Qed.

End SuBToFullExecCases.

End SubToFullExecInternal.

(*

Lemma step_once_write_rmw_helper e h t f
    (WF : WCore.wf (WCore.Build_t G G' C f))
    (G_PREFIX : restr_exec E G' G)
    (SUB_TRACE : exec_trace_prefix G' G)
    (RMW : rmw' e h)
    (IS_R : R' e)
    (ENUM : reord_lemma_enum E E' C (h :: t))
    (NOT_INIT2 : tid h <> tid_init) :
  E e.
Proof using THREAD_EVENTS.
  assert (IN_D : D h).
  { apply ENUM; desf. }
  assert (CONT : contigious_actids G).
  { eapply trace_form_sub; eauto. }
  assert (NOT_INIT1 : ~is_init e).
  { intro F; destruct e as [l | tide ide]; auto.
    unfold is_r in IS_R; rewrite wf_init_lab in IS_R; auto.
    apply WF. }
  set (CONTH := CONT (tid h) NOT_INIT2); desf.
  assert (EQH : exists tidh, h = ThreadEvent tidh N).
  { eexists; eapply add_event_to_contigious with (G' := delta_G G G' h).
    all: eauto.
    { rewrite CONTH; apply thread_seq_set_size. }
    { eapply trace_form_sub, delta_G_prefix; eauto.
      apply G_PREFIX. }
    apply IN_D. }
  destruct EQH as [tidh EQH]; subst.
  apply wf_rmwi, immediate_in in RMW; [| apply WF].
  assert (TIDEQ : tid e = tidh).
  { apply sb_tid_init in RMW; desf. }
  destruct e as [l | tide ide]; ins; subst.
  apply in_restr_acts, CONTH.
  unfold sb, ext_sb in RMW; unfolder in RMW; desf.
  unfold thread_seq_set, seq_set; unfolder; eauto.
Qed.


(* FIXME: this proof contains a lot of copy-paste *)
Lemma step_once_write h t f f'
    (F_ID : partial_id f')
    (SUB_ID : sub_fun f f')
    (WF : WCore.wf (WCore.Build_t G G' C f))
    (WF' : WCore.wf (WCore.Build_t G' G' C f'))
    (G_PREFIX : restr_exec E G' G)
    (SUB_TRACE : exec_trace_prefix G' G)
    (ENUM : reord_lemma_enum E E' C (h :: t))
    (COH : trace_coherent traces G')
    (IS_W : W' h) :
  WCore.cfg_add_event_uninformative traces
    (WCore.Build_t G                G' C f)
    (WCore.Build_t (delta_G G G' h) G' C (upd f h (Some h))).
Proof using THREAD_EVENTS.
  (* Information about h *)
  assert (IN_D : D h).
  { apply ENUM; desf. }
  assert (NOT_INIT : ~is_init h).
  { apply ENUM; desf. }
  assert (H_TID : tid h <> tid_init).
  { eapply WCore.wf_actid_tid; eauto.
    apply IN_D. }
  assert (NOT_R : ~R' h).
  { generalize IS_W; unfold is_w, is_r.
    destruct (lab' h); auto. }
  assert (PART : partial_id f).
  { eapply partial_id_mori; eauto. }
  assert (DELTA_SUB : sub_execution G' (delta_G G G' h) ∅₂ ∅₂).
  { eapply delta_G_sub; eauto; try now apply IN_D.
    apply G_PREFIX. }
  assert (DELTA_PREF : exec_trace_prefix G' (delta_G G G' h)).
  { eapply delta_G_prefix; eauto; apply G_PREFIX. }
  assert (DELTA_COH : trace_coherent traces (delta_G G G' h)).
  { eapply trace_coherent_sub; eauto. }
  assert (UPDID : partial_id (upd f h (Some h))).
  { apply upd_partial_id. eapply partial_id_mori; eauto. }

  (* Case 1: h is part of an RMW *)
  destruct (classic (codom_rel rmw' h)) as [[r RMW] | NRMW].
  { assert (IS_R : R' r).
    { apply wf_rmwD in RMW; [| apply WF].
      unfolder in RMW; desf. }
    assert (IN_E : E r).
    { eapply step_once_write_rmw_helper; eauto. }
    exists h, (lab' h), (Some r), None,
      (codom_rel (⦗eq h⦘ ⨾ co' ⨾ ⦗E⦘)), (dom_rel (⦗E⦘ ⨾ co' ⨾ ⦗eq h⦘)), (Some h).
    constructor; ins.
    { apply IN_D. }
    { set (DCOH := DELTA_COH (tid h) H_TID). ins. desf.
      unfold WCore.new_event_correct. desf.
      { exists tr.
        erewrite sub_lab; eauto.
        erewrite delta_G_actid_trace_h in PREFIX; eauto; try now apply G_PREFIX.
        split; ins. now rewrite Heq in PREFIX. }
      set (FIN := WCore.all_trace_fin WF H_TID).
      ins. rewrite Heq in FIN.
      unfold trace_finite in FIN. desf. }
    { erewrite sub_lab; [now rewrite updI | apply G_PREFIX]. }
    { apply union_more; [apply union_more; auto |].
      { rewrite wf_rfD; [basic_solver | apply WF]. }
      unfold WCore.rf_delta_W.
      rewrite partial_id_collect_eq, upds, partial_id_set.
      all: eauto using upd_partial_id.
      rewrite partial_id_upd_dom, set_inter_union_r.
      arewrite (codom_rel (⦗eq h⦘ ⨾ rf') ∩₁ eq h ≡₁ ∅).
      { rewrite wf_rfD; [basic_solver | apply WF]. }
      rewrite set_union_empty_r.
      split; intros h' y REL.
      { unfolder in REL; desf; unfolder; splits; eauto.
        enough (IN : (C ∩₁ partial_id_dom f) y).
        { apply IN. }
        apply partial_id_set; auto.
        enough (IN : (codom_rel rf ∪₁ (Some ↓₁ (f ↑₁ C))) y).
        { destruct IN as [IN|IN]; auto.
          exfalso; enough (E h') by now apply IN_D.
          unfolder in IN; desf.
          erewrite wf_rff with (G := G') (y := h') (z := x); eauto; try now apply WF.
          { apply wf_rfE in IN; [|apply WF]. unfolder in IN; desf. }
          eapply sub_rf in IN; [| apply G_PREFIX].
          unfolder in IN; desf. }
        apply WF; ins; split; auto.
        erewrite sub_lab; [| apply G_PREFIX].
        apply wf_rfD in REL0; [| apply WF].
        unfolder in REL0; desf.  }
      unfolder in REL; desf.
      unfolder; splits; auto.
      apply WF; ins. apply partial_id_set; auto.
      split; auto. unfold partial_id_dom in REL1.
      change E' with (acts_set (WCore.GC (WCore.Build_t G' G' C f'))).
      eapply WCore.f_dom; ins.
      eapply partial_id_dom_mori; eauto. }
    { unfold WCore.co_delta. erewrite sub_lab; [| apply G_PREFIX].
      rewrite unionA; apply union_more; auto.
      rewrite unionC, IS_W; apply union_more; basic_solver 5. }
    { apply union_more; auto.
      unfold WCore.rmw_delta, eq_opt, W_ex.
      split; [| basic_solver].
      intros x y RMW'; unfolder in RMW'; desf.
      erewrite sub_lab; [| apply G_PREFIX].
      arewrite (x = r); [| basic_solver].
      assert (IS_R' : R' x).
      { apply wf_rmwD in RMW'0; [| apply WF].
        unfolder in RMW'0; desf. }
      apply wf_rmwi in RMW'0; [| apply WF].
      apply wf_rmwi in RMW; [| apply WF].
      assert (X_NINIT : ~is_init x).
      { unfold is_r in IS_R'; destruct x; auto.
        now rewrite wf_init_lab in IS_R'; [| apply WF]. }
      assert (R_NINIT : ~is_init r). (* TODO: move *)
      (* TODO: shorthand lemma *)
      { unfold is_r in IS_R; destruct r; auto.
        now rewrite wf_init_lab in IS_R; [| apply WF]. }
      eapply total_immediate_unique with
        (P := (E' \₁ is_init) ∩₁ (fun x => tid x = tid y)).
      all: eauto using sb_total.
      all: unfolder; splits; eauto.
      all: try now apply G_PREFIX.
      { apply immediate_in, sb_tid_init in RMW'0; desf. }
      { apply immediate_in, sb_tid_init in RMW; desf. }
      apply IN_D. }
    apply over_exec_wf; ins.
    all: try now apply WF.
    { rewrite partial_id_upd_dom. apply set_subset_union; auto.
      apply wf_partial_id_dome; eauto. }
    { rewrite <- restr_init_sub; eauto.
      transitivity E; basic_solver. }
    (* TODO prettify? *)
    { arewrite (⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘ ≡ ∅₂).
      { rewrite wf_rfD; [basic_solver | apply WF]. }
      rewrite union_false_r, codom_union, set_inter_union_l.
      arewrite (eq h ∩₁ R ≡₁ ∅).
      { erewrite sub_lab; [| apply G_PREFIX]. basic_solver. }
      rewrite set_union_empty_r. intros x IN.
      apply WF in IN; ins.
      destruct IN as [RF|CMT].
      { left; left; auto. }
      right.
      apply partial_id_set in CMT; auto.
      apply partial_id_set; auto.
      split; [apply CMT|].
      apply partial_id_upd_dom.
      destruct (classic (x = h)); subst; rupd.
      { now right. }
      left; apply CMT. }
    enough (CONT : contigious_actids (delta_G G G' h)).
    { now apply CONT. }
    eapply trace_form_sub; eauto. }

  (* Case 2: no rmw *)
  exists h, (lab' h), None, None,
    (codom_rel (⦗eq h⦘ ⨾ co' ⨾ ⦗E⦘)), (dom_rel (⦗E⦘ ⨾ co' ⨾ ⦗eq h⦘)), (Some h).
  constructor; ins.
  { apply IN_D. }
  { set (DCOH := DELTA_COH (tid h) H_TID). ins. desf.
    unfold WCore.new_event_correct. desf.
    { exists tr.
      erewrite sub_lab; eauto.
      erewrite delta_G_actid_trace_h in PREFIX; eauto; try now apply G_PREFIX.
      split; ins. now rewrite Heq in PREFIX. }
    set (FIN := WCore.all_trace_fin WF H_TID).
    ins. rewrite Heq in FIN.
    unfold trace_finite in FIN. desf. }
  { erewrite sub_lab; [now rewrite updI | apply G_PREFIX]. }
  { apply union_more; [apply union_more; auto |].
    { rewrite wf_rfD; [basic_solver | apply WF]. }
    unfold WCore.rf_delta_W.
    rewrite partial_id_collect_eq, upds, partial_id_set.
    all: eauto using upd_partial_id.
    rewrite partial_id_upd_dom, set_inter_union_r.
    arewrite (codom_rel (⦗eq h⦘ ⨾ rf') ∩₁ eq h ≡₁ ∅).
    { rewrite wf_rfD; [basic_solver | apply WF]. }
    rewrite set_union_empty_r.
    split; intros h' y REL.
    { unfolder in REL; desf; unfolder; splits; eauto.
      enough (IN : (C ∩₁ partial_id_dom f) y).
      { apply IN. }
      apply partial_id_set; auto.
      enough (IN : (codom_rel rf ∪₁ (Some ↓₁ (f ↑₁ C))) y).
      { destruct IN as [IN|IN]; auto.
        exfalso; enough (E h') by now apply IN_D.
        unfolder in IN; desf.
        erewrite wf_rff with (G := G') (y := h') (z := x); eauto; try now apply WF.
        { apply wf_rfE in IN; [|apply WF]. unfolder in IN; desf. }
        eapply sub_rf in IN; [| apply G_PREFIX].
        unfolder in IN; desf. }
      apply WF; ins; split; auto.
      erewrite sub_lab; [| apply G_PREFIX].
      apply wf_rfD in REL0; [| apply WF].
      unfolder in REL0; desf.  }
    unfolder in REL; desf.
    unfolder; splits; auto.
    apply WF; ins. apply partial_id_set; auto.
    split; auto. unfold partial_id_dom in REL1.
    change E' with (acts_set (WCore.GC (WCore.Build_t G' G' C f'))).
    eapply WCore.f_dom; ins.
    eapply partial_id_dom_mori; eauto. }
  { unfold WCore.co_delta. erewrite sub_lab; [| apply G_PREFIX].
    rewrite unionA; apply union_more; auto.
    rewrite unionC, IS_W; apply union_more; basic_solver 5. }
  { apply union_more; auto.
    unfold WCore.rmw_delta, eq_opt, W_ex.
    split; [| basic_solver].
    intros x y RMW'; unfolder in RMW'; desf.
    exfalso; unfolder in NRMW; eauto. }
  apply over_exec_wf; ins.
  all: try now apply WF.
  { rewrite partial_id_upd_dom. apply set_subset_union; auto.
    apply wf_partial_id_dome; eauto. }
  { rewrite <- restr_init_sub; eauto.
    transitivity E; basic_solver. }
  (* TODO prettify? *)
  { arewrite (⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘ ≡ ∅₂).
    { rewrite wf_rfD; [basic_solver | apply WF]. }
    rewrite union_false_r, codom_union, set_inter_union_l.
    arewrite (eq h ∩₁ R ≡₁ ∅).
    { erewrite sub_lab; [| apply G_PREFIX]. basic_solver. }
    rewrite set_union_empty_r. intros x IN.
    apply WF in IN; ins.
    destruct IN as [RF|CMT].
    { left; left; auto. }
    right.
    apply partial_id_set in CMT; auto.
    apply partial_id_set; auto.
    split; [apply CMT|].
    apply partial_id_upd_dom.
    destruct (classic (x = h)); subst; rupd.
    { now right. }
    left; apply CMT. }
  enough (CONT : contigious_actids (delta_G G G' h)).
  { now apply CONT. }
  eapply trace_form_sub; eauto.
Qed.

Lemma step_once_fence h t f f'
    (F_ID : partial_id f')
    (SUB_ID : sub_fun f f')
    (WF : WCore.wf (WCore.Build_t G G' C f))
    (WF' : WCore.wf (WCore.Build_t G' G' C f'))
    (G_PREFIX : restr_exec E G' G)
    (SUB_TRACE : exec_trace_prefix G' G)
    (ENUM : reord_lemma_enum E E' C (h :: t))
    (COH : trace_coherent traces G')
    (IS_F : F' h) :
  WCore.cfg_add_event_uninformative traces
    (WCore.Build_t G                G' C f)
    (WCore.Build_t (delta_G G G' h) G' C (upd f h (Some h))).
Proof using THREAD_EVENTS.
  (* Information about h *)
  assert (IN_D : D h).
  { apply ENUM; desf. }
  assert (NOT_INIT : ~is_init h).
  { apply ENUM; desf. }
  assert (H_TID : tid h <> tid_init).
  { eapply WCore.wf_actid_tid; eauto.
    apply IN_D. }
  assert (NOT_R : ~R' h).
  { generalize IS_F; unfold is_f, is_r.
    destruct (lab' h); auto. }
  assert (NOT_W : ~W' h).
  { generalize IS_F; unfold is_f, is_w.
    destruct (lab' h); auto. }
  assert (PART : partial_id f).
  { eapply partial_id_mori; eauto. }
  assert (DELTA_SUB : sub_execution G' (delta_G G G' h) ∅₂ ∅₂).
  { eapply delta_G_sub; eauto; try now apply IN_D.
    apply G_PREFIX. }
  assert (DELTA_PREF : exec_trace_prefix G' (delta_G G G' h)).
  { eapply delta_G_prefix; eauto; apply G_PREFIX. }
  assert (DELTA_COH : trace_coherent traces (delta_G G G' h)).
  { eapply trace_coherent_sub; eauto. }
  assert (UPDID : partial_id (upd f h (Some h))).
  { apply upd_partial_id. eapply partial_id_mori; eauto. }

  exists h, (lab' h), None, None, ∅, ∅, (Some h).
  constructor; ins.
  { apply IN_D. }
  { set (DCOH := DELTA_COH (tid h) H_TID). ins. desf.
    unfold WCore.new_event_correct. desf.
    { exists tr.
      erewrite sub_lab; eauto.
      erewrite delta_G_actid_trace_h in PREFIX; eauto; try now apply G_PREFIX.
      split; ins. now rewrite Heq in PREFIX. }
    set (FIN := WCore.all_trace_fin WF H_TID).
    ins. rewrite Heq in FIN.
    unfold trace_finite in FIN. desf. }
  { erewrite sub_lab; [now rewrite updI | apply G_PREFIX]. }
  { apply union_more; [apply union_more; auto |].
    { rewrite wf_rfD; [basic_solver | apply WF]. }
    unfold WCore.rf_delta_W.
    rewrite partial_id_collect_eq, upds, partial_id_set.
    all: eauto using upd_partial_id.
    arewrite (codom_rel (⦗eq h⦘ ⨾ rf') ≡₁ ∅).
    { rewrite wf_rfD; [basic_solver | apply WF]. }
    arewrite (⦗eq h⦘ ⨾ rf' ⨾ ⦗E⦘ ≡ ∅₂).
    { rewrite wf_rfD; [basic_solver | apply WF]. }
    basic_solver. }
  { unfold WCore.co_delta. erewrite sub_lab; [| apply G_PREFIX].
    arewrite (⦗eq h⦘ ⨾ co' ⨾ ⦗E⦘ ≡ ∅₂).
    { rewrite wf_coD; [basic_solver | apply WF]. }
    arewrite (⦗E⦘ ⨾ co' ⨾ ⦗eq h⦘ ≡ ∅₂).
    { rewrite wf_coD; [basic_solver | apply WF]. }
    desf; basic_solver. }
  { apply union_more; auto.
    arewrite (⦗E⦘ ⨾ rmw' ⨾ ⦗eq h⦘ ≡ ∅₂).
    { rewrite wf_rmwD; [basic_solver | apply WF]. }
    unfold WCore.rmw_delta; basic_solver. }
  apply over_exec_wf; ins.
  all: try now apply WF.
  { rewrite partial_id_upd_dom. apply set_subset_union; auto.
    apply wf_partial_id_dome; eauto. }
  { rewrite <- restr_init_sub; eauto.
    transitivity E; basic_solver. }
  (* TODO prettify? *)
  { arewrite (⦗E⦘ ⨾ rf' ⨾ ⦗eq h⦘ ≡ ∅₂).
    { rewrite wf_rfD; [basic_solver | apply WF]. }
    arewrite (⦗eq h⦘ ⨾ rf' ⨾ ⦗E⦘ ≡ ∅₂).
    { rewrite wf_rfD; [basic_solver | apply WF]. }
    rewrite union_false_r, codom_union, set_inter_union_l,
            codom_empty, set_union_empty_r.
    arewrite (eq h ∩₁ R ≡₁ ∅).
    { erewrite sub_lab; [| apply G_PREFIX]. basic_solver. }
    rewrite set_union_empty_r.
    intros x IN. apply WF in IN; ins.
    destruct IN as [RF|CMT].
    { left; auto. }
    right.
    (* TODO: this repeats. Lemma? *)
    apply partial_id_set in CMT; auto.
    apply partial_id_set; auto.
    split; [apply CMT|].
    apply partial_id_upd_dom.
    destruct (classic (x = h)); subst; rupd.
    { now right. }
    left; apply CMT. }
  enough (CONT : contigious_actids (delta_G G G' h)).
  { now apply CONT. }
  eapply trace_form_sub; eauto.
Qed.

(* NOTE: xmm is doing only prefix restriction *)
Lemma step_once h t f f'
    (F_ID : partial_id f')
    (SUB_ID : sub_fun f f')
    (WF : WCore.wf (WCore.Build_t G G' C f))
    (WF' : WCore.wf (WCore.Build_t G' G' C f'))
    (G_PREFIX : restr_exec E G' G)
    (SUB_TRACE : exec_trace_prefix G' G)
    (ENUM : reord_lemma_enum E E' C (h :: t))
    (COH : trace_coherent traces G') :
  WCore.cfg_add_event_uninformative traces
    (WCore.Build_t G                G' C f)
    (WCore.Build_t (delta_G G G' h) G' C (upd f h (Some h))).
Proof using THREAD_EVENTS.
  set (LAB := lab_rwf lab' h); desf.
  { eapply step_once_read; eauto. }
  { eapply step_once_write; eauto. }
  eapply step_once_fence; eauto.
Qed.

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