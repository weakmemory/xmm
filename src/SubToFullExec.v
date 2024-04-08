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