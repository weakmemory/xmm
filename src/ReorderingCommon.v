Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import ThreadTrace.
Require Import Core.
Require Import TraceSwap.
Require Import SubToFullExec.

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

Section ExtraRel.

Variable G : execution.
Variable traces : thread_id -> trace label -> Prop.

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'loc'" := (loc lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'is_acq'" := (is_acq lab).
Notation "'is_rel'" := (is_rel lab).
Notation "'is_rlx'" := (is_rlx lab).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'ppo'" := (ppo G).
Notation "'hb'" := (hb G).
Notation "'psc'" := (imm.psc G).
Notation "'sw'" := (sw G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'F'" := (is_f lab).

Definition rpo :=
  sb ∩ same_loc ∪
  ⦗is_acq⦘ ⨾ sb ⨾ ⦗is_rel⦘ ∪
  ⦗R ∩₁ is_rlx⦘ ⨾ sb ⨾ ⦗F ∩₁ is_acq⦘ ∪
  ⦗is_acq⦘ ⨾ sb ⨾ ⦗R ∪₁ W⦘ ∪
  ⦗R ∪₁ W⦘ ⨾ sb ⨾ ⦗is_rel⦘ ∪
  ⦗F ∩₁ is_rel⦘ ⨾ sb ⨾ ⦗W ∩₁ is_rlx⦘.
Definition rhb := (rpo ∪ sw)⁺.
Definition vf := ⦗E⦘ ⨾ ⦗W⦘ ⨾ rf^? ⨾ hb^? ⨾ psc^? ⨾ hb^? ⨾ ⦗E⦘.
Definition srf := (vf ∩ same_loc) ⨾ ⦗R⦘ \ (co ⨾ vf).

Definition thread_terminated (t : thread_id) : Prop :=
  traces t (thread_trace G t).
Definition machine_terminated := forall t, thread_terminated t.
(* TODO: fix behavior to be a function from location to
         ordered by co (possibly infinite) set of values written to the location *)
Definition behavior := co.

Lemma wf_rpoE
    (WF : Wf G) :
  rpo ≡ ⦗E⦘ ⨾ rpo ⨾ ⦗E⦘.
Proof using.
  unfold rpo.
  rewrite !seq_union_l, !seq_union_r.
  repeat apply union_more.
  all: rewrite wf_sbE at 1; try rewrite !seq_seq_inter.
  all: basic_solver 7.
Qed.

Lemma wf_vfE
    (WF : Wf G) :
  vf ≡ ⦗E⦘ ⨾ vf ⨾ ⦗E⦘.
Proof using.
  unfold vf. hahn_frame.
  seq_rewrite <- !(id_inter E E).
  now rewrite !set_interK.
Qed.

Lemma vf_dom : dom_rel vf ⊆₁ W.
Proof using.
  unfold vf. basic_solver.
Qed.

Lemma wf_srfE
    (WF : Wf G) :
  srf ≡ ⦗E⦘ ⨾ srf ⨾ ⦗E⦘.
Proof using.
  unfold srf. split; [| basic_solver].
  rewrite wf_vfE at 1 by auto.
  unfolder; ins; splits; desf; eauto.
Qed.

Lemma wf_rhbE
    (WF : Wf G) :
  rhb ≡ ⦗E⦘ ⨾ rhb ⨾ ⦗E⦘.
Proof using.
  unfold rhb. rewrite wf_swE, wf_rpoE; auto.
  rewrite <- seq_union_r, <- seq_union_l.
  seq_rewrite <- ct_seq_eqv_l.
  rewrite <- seqA.
  now seq_rewrite <- ct_seq_eqv_r.
Qed.

Lemma rf_sub_vf (WF : Wf G) : rf ⊆ vf.
Proof using.
  rewrite WF.(wf_rfD), WF.(wf_rfE).
  unfold vf; unfolder; ins; desf.
  splits; eauto.
  do 3 (exists y; splits; eauto).
Qed.

Lemma srf_funcrional (WF : Wf G) : functional srf⁻¹.
Proof using.
  unfolder; unfold srf. intros x y z (VF1 & CO1) (VF2 & CO2).
  tertium_non_datur (y = z) as [EQ|NEQ]; ins; exfalso.
  destruct (WF.(wf_co_total)) with (a := y) (b := z)
                                   (ol := loc x) as [CO|CO].
  all: ins; unfolder in *; desf; splits; eauto.
  all: try now (apply vf_dom; eexists; eauto).
  { apply wf_vfE in VF1; unfolder in VF1; desf. }
  apply wf_vfE in VF2; unfolder in VF2; desf.
Qed.

Lemma srf_exists b
    (HIN : E b)
    (WF : Wf G)
    (IS_R : R b) :
  exists a, srf a b.
Proof using.
  assert (exists l, loc b = Some l) as HLOC; desf.
  { by generalize (is_r_loc lab); unfolder in *; basic_solver 12. }
  assert (HINIT : E (InitEvent l)).
  { by apply WF; eauto. }
  assert (INILAB : lab (InitEvent l) = Astore Xpln Opln l 0).
  { by apply WF. }
  assert (INILOC : loc (InitEvent l) = Some l).
  { by unfold Events.loc; rewrite (wf_init_lab WF). }
  assert (INIW : W (InitEvent l)).
  { by unfolder; unfold is_w, Events.loc; desf; eauto. }
  assert (INISB : sb (InitEvent l) b).
  { by apply init_ninit_sb; eauto; eapply read_or_fence_is_not_init; eauto. }
  assert (INIVF : vf (InitEvent l) b).
  { red. exists (InitEvent l); splits.
    { red. splits; desf. }
    hahn_rewrite <- sb_in_hb.
    basic_solver 21. }
  assert (ACT_LIST : exists El, E ≡₁ (fun x => In x El)); desf.
  { admit. }
  forward (eapply last_exists with (s:=co ⨾ ⦗fun x => vf x b⦘)
                                   (dom:= filterP W El) (a:=(InitEvent l))).
  { eapply acyclic_mon.
    apply trans_irr_acyclic; [apply co_irr| apply co_trans]; eauto.
    basic_solver. }
  { ins.
    assert (A: (co ⨾ ⦗fun x : actid => vf x b⦘)^? (InitEvent l) c).
    { apply rt_of_trans; try done.
      apply transitiveI.
      arewrite_id ⦗fun x : actid => vf x b⦘ at 1.
      rewrite seq_id_l.
      arewrite (co ⨾ co ⊆ co); [|done].
      apply transitiveI.
      eapply co_trans; eauto. }
    unfolder in A; desf.
    { apply in_filterP_iff; split; auto.
      by apply ACT_LIST. }
    apply in_filterP_iff.
    hahn_rewrite WF.(wf_coE) in A.
    hahn_rewrite WF.(wf_coD) in A.
    hahn_rewrite WF.(wf_col) in A.
    unfold same_loc in *; unfolder in *; desf; splits; eauto; congruence. }
  ins; desc.
  assert (A: (co ⨾ ⦗fun x : actid => vf x b⦘)^? (InitEvent l) b0).
  { apply rt_of_trans; [|by subst].
    apply transitiveI.
    arewrite_id ⦗fun x : actid => vf x b⦘ at 1.
    rewrite seq_id_l.
    arewrite (co ⨾ co ⊆ co); [|done].
    apply transitiveI.
    eapply co_trans; eauto. }
  assert (loc b0 = Some l).
  { unfolder in A; desf.
    hahn_rewrite WF.(wf_col) in A.
    unfold same_loc in *; desf; unfolder in *; congruence. }
  exists b0; red; split.
  { unfold urr, same_loc.
    unfolder in A; desf; unfolder; ins; desf; splits; try basic_solver 21; congruence. }
  unfold max_elt in *.
  unfolder in *; ins; desf; intro; desf; basic_solver 11.
Admitted.

End ExtraRel.

Module ReordCommon.

Section ReorderingDefs.

Open Scope program_scope.

Variable G_s G_t : execution.
Variable traces traces' : thread_id -> trace label -> Prop.
Variable a b : actid.

Notation "'lab_t'" := (lab G_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'rpo_t'" := (rpo G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).
Notation "'srf_t'" := (srf G_t).
Notation "'W_t'" := (is_w lab_t).
Notation "'R_t'" := (is_r lab_t).

Notation "'lab_s'" := (lab G_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (is_w lab_s).
Notation "'R_s'" := (is_r lab_s).


Definition mapper := upd (upd id a b) b a.
Definition traces_swapped :=
    forall t' (B_LT_SZ : NOmega.lt (NOnum (index b)) (trace_length t')),
      traces' (tid a) t' <-> exists t,
      << IN : traces (tid a) t >> /\
      << SWAP : trace_swapped label t t' (index a) (index b) >>.
Definition mapped_G_t l : execution := {|
  acts_set := E_t;
  threads_set := threads_set G_t;
  lab := upd (lab_t ∘ mapper) a l;
  rmw := mapper ↑ rmw_t;
  data := mapper ↑ data_t;
  addr := mapper ↑ addr_t;
  ctrl := mapper ↑ ctrl_t;
  rmw_dep := mapper ↑ rmw_dep_t;
  rf := mapper ↑ rf_t;
  co := mapper ↑ co_t;
|}.
Definition mapped_G_t_with_b_srf l : execution := {|
  acts_set := E_t ∪₁ eq b;
  threads_set := threads_set G_t;
  lab := upd (lab_t ∘ mapper) a l;
  rmw := mapper ↑ rmw_t;
  data := mapper ↑ data_t;
  addr := mapper ↑ addr_t;
  ctrl := mapper ↑ ctrl_t;
  rmw_dep := mapper ↑ rmw_dep_t;
  rf := mapper ↑ rf_t ∪ mapper ↑ (srf_t ⨾ ⦗eq b⦘);
  co := mapper ↑ co_t;
|}.

(* TODO computational swap_trace? *)
Record reord : Prop :=
{ a_not_init : ~is_init a;
  events_diff : a <> b;
  events_locs_diff : loc_s a <> loc_s b;
  events_lab : lab_s = lab_t ∘ mapper;
  events_same : E_s ≡₁ E_t;
  events_imm : immediate sb_t a b;
  event_threadset : threads_set G_s ≡₁ threads_set G_t;

  events_no_rpo1 : ~rpo_s a b;

  map_sb : sb_s ≡ sb_t;
  map_rf : rf_s ≡ mapper ↑ rf_t;
  map_co : co_s ≡ mapper ↑ co_t;
  map_rmw : rmw_s ≡ mapper ↑ rmw_t;
  map_rpo : rpo_s ≡ mapper ↑ rpo_t;
  map_rmw_dep : rmw_dep_s ≡ mapper ↑ rmw_dep_t;

  traces_corr : traces_swapped;

  gs_data : data G_s ≡ ∅₂;
  gs_addr : addr G_s ≡ ∅₂;
  gs_ctrl : ctrl G_s ≡ ∅₂;
  gt_data : data G_t ≡ ∅₂;
  gt_addr : addr G_t ≡ ∅₂;
  gt_ctrl : ctrl G_t ≡ ∅₂;
}.

Hypothesis REORD : reord.

Lemma mapper_eq_b : mapper b = a.
Proof using.
  unfold mapper; now rewrite upds.
Qed.

Lemma mapper_eq_a : mapper a = b.
Proof using.
  destruct (classic (a = b)) as [EQ|EQ].
  { unfold mapper. rewrite EQ. now rupd. }
  unfold mapper; rupd; eauto.
Qed.

Lemma mapper_neq x (NEQ_A : x <> a) (NEQ_B : x <> b) : mapper x = x.
Proof using.
  unfold mapper; rupd.
Qed.

Lemma mapper_inj (NEQ : a <> b) : inj_dom ⊤₁ mapper.
Proof using.
  unfold mapper; unfolder. intros x y _ _.
  destruct (classic (x = a)) as [HEQXA|HEQXA],
           (classic (y = b)) as [HEQYB|HEQYB],
           (classic (y = a)) as [HEQYA|HEQYA],
           (classic (x = b)) as [HEQXB|HEQXB].
  all: subst; rupd; ins.
  all: unfold id in *; congruence.
Qed.

Lemma mapper_self_inv (NEQ : a <> b) x : mapper (mapper x) = x.
Proof using.
  unfold mapper.
  tertium_non_datur (x = b) as [HEQA|HEQA]; subst; try now rupd.
  rewrite updo with (c := x); ins.
  tertium_non_datur (x = a) as [HEQB|HEQB]; subst; try now rupd.
Qed.

(* TODO: generalize to injective func *)
Lemma mapper_rel_inter r1 r2
    (NEQ : a <> b) :
  mapper ↑ (r1 ∩ r2) ≡ mapper ↑ r1 ∩ mapper ↑ r2.
Proof.
  split; [apply collect_rel_inter |].
  unfolder; ins; desf.
  apply mapper_inj in H1, H2; ins; desf.
  exists x'0, y'0; splits; ins.
Qed.

(* TODO: generalize to injective func *)
Lemma mapper_inter_set s1 s2
    (NEQ : a <> b) :
  mapper ↑₁ (s1 ∩₁ s2) ≡₁ mapper ↑₁ s1 ∩₁ mapper ↑₁ s2.
Proof using.
  split; [apply set_collect_inter |].
  unfolder; ins; desf.
  apply mapper_inj in H1; ins; desf.
  exists y0; splits; ins.
Qed.

Lemma mapper_lab_same :
  upd (lab_t ∘ mapper) a (lab_t b) = lab_t ∘ mapper.
Proof using.
  apply functional_extensionality. intros x. unfold compose.
  tertium_non_datur (x = a) as [HEQA|NEQA];
  tertium_non_datur (x = b) as [HEQB|NEQB]; subst.
  all: try now rewrite upds, mapper_eq_a.
  all: rewrite updo; eauto.
Qed.

Lemma mapper_R_t
    (NEQ : a <> b) :
  mapper ↑₁ R_t ≡₁ is_r (upd (lab_t ∘ mapper) a (lab_t b)).
Proof using.
  rewrite mapper_lab_same.
  unfolder; split; intros x HSET; desf; unfold compose, is_r in *.
  { rewrite mapper_self_inv; ins. }
  tertium_non_datur (x = a) as [HEQA|NEQA];
  tertium_non_datur (x = b) as [HEQB|NEQB]; subst; ins.
  { rewrite mapper_eq_a in HSET.
    exists b; split; eauto using mapper_eq_b. }
  { rewrite mapper_eq_b in HSET.
    exists a; split; eauto using mapper_eq_a. }
  rewrite mapper_neq in HSET; ins.
  exists x; split; eauto using mapper_neq.
Qed.

Lemma mapper_W_t
    (NEQ : a <> b) :
  mapper ↑₁ W_t ≡₁ is_w (upd (lab_t ∘ mapper) a (lab_t b)).
Proof using.
  rewrite mapper_lab_same.
  unfolder; split; intros x HSET; desf; unfold compose, is_w in *.
  { rewrite mapper_self_inv; ins. }
  tertium_non_datur (x = a) as [HEQA|NEQA];
  tertium_non_datur (x = b) as [HEQB|NEQB]; subst; ins.
  { rewrite mapper_eq_a in HSET.
    exists b; split; eauto using mapper_eq_b. }
  { rewrite mapper_eq_b in HSET.
    exists a; split; eauto using mapper_eq_a. }
  rewrite mapper_neq in HSET; ins.
  exists x; split; eauto using mapper_neq.
Qed.

Lemma mapper_inj_dom s (NEQ : a <> b) : inj_dom s mapper.
Proof using.
  unfold inj_dom; ins.
  apply mapper_inj; ins.
Qed.

Lemma mapper_init
    (ANIT : ~is_init a)
    (BNIT : ~is_init b) :
  mapper ↑₁ (acts_set G_t ∩₁ is_init) ≡₁ acts_set G_t ∩₁ is_init.
Proof using.
  unfold mapper.
  unfolder; split; desf; intros x.
  { intros (y & IN & EQ); generalize EQ; clear EQ.
    destruct (classic (y = a)) as [HA|HA],
             (classic (y = b)) as [HB|HB].
    all: subst; rupd; ins; desf; exfalso; eauto. }
  destruct (classic (x = a)) as [HA|HA],
           (classic (x = b)) as [HB|HB].
  all: subst; ins; desf.
  exists x; rupd.
Qed.

Lemma mapped_G_t_sb l : sb (mapped_G_t l) ≡ sb_t.
Proof using.
  unfold sb; ins.
Qed.

Lemma mapped_G_t_with_b_srf_sb_sub l : sb_t ⊆ sb (mapped_G_t_with_b_srf l).
Proof using.
  unfold sb; ins; basic_solver.
Qed.

Lemma mapped_G_t_with_b_srf_acts_sub l : E_t ⊆₁ acts_set (mapped_G_t_with_b_srf l).
Proof using.
  unfold acts_set, mapped_G_t; ins; basic_solver.
Qed.

Lemma mapped_G_t_with_b_srf_b_max l
    (IN : E_t a)
    (LAST : max_elt sb_t a)
    (NEXT : ext_sb a b) :
  max_elt (sb (mapped_G_t_with_b_srf l)) b.
Proof using.
  unfold max_elt, sb. intros e SB.
  unfolder in SB; desf; ins.
  unfolder in SB1; desf; [| eapply ext_sb_irr; eauto].
  eapply (LAST e); unfold sb; unfolder; splits; eauto.
  eapply ext_sb_trans; eauto.
Qed.

Lemma mapped_G_t_with_b_srf_not_b l x y
    (IN : E_t a)
    (LAST : max_elt sb_t a)
    (NEXT : ext_sb a b)
    (SB : sb (mapped_G_t_with_b_srf l) x y) :
  E_t x.
Proof using.
  enough (XIN : acts_set (mapped_G_t_with_b_srf l) x).
  { ins; unfolder in XIN; desf.
    exfalso; eapply mapped_G_t_with_b_srf_b_max; eauto. }
  unfold sb in SB; unfolder in SB; desf.
Qed.

Lemma mapped_G_t_imm_sb l
    (NINIT : ~is_init a)
    (HINA : E_t a)
    (LAST : max_elt sb_t a)
    (NEXT : ext_sb a b) :
  immediate (sb (mapped_G_t_with_b_srf l)) ≡ immediate sb_t ∪ singl_rel a b.
Proof using.
  split; intros x y HIN.
  { unfold sb in HIN; ins.
    unfolder in HIN; desf.
    all: try now (exfalso; eapply ext_sb_irr; eauto).
    { left; unfold sb; unfolder; splits; ins; eauto.
      apply HIN0 with (c := c); desf; eauto. }
    { exfalso. eapply mapped_G_t_with_b_srf_b_max with (l := l); ins.
      unfold sb; ins; unfolder; splits; eauto. }
    tertium_non_datur (x = a) as [ISA|ISA]; subst.
    { now right. }
    exfalso. tertium_non_datur (is_init x) as [INI|INI].
    { apply HIN0 with (c := a); splits; eauto.
      destruct a, x; ins. }
    assert (TIDEQ : tid a = tid x).
    { unfold ext_sb in NEXT, HIN1. do 2 desf. }
    destruct ext_sb_semi_total_r with (x := b) (y := a) (z := x) as [SB|SB].
    all: eauto.
    { destruct a, x; ins; desf; congruence. }
    { eapply LAST; unfold sb; unfolder; splits; eauto. }
    apply HIN0 with (c := a); splits; eauto. }
  unfolder in HIN; desf.
  { split; [now apply mapped_G_t_with_b_srf_sb_sub|].
    intros c SB1 SB2. assert (INE : E_t c).
    { eapply mapped_G_t_with_b_srf_not_b; eauto. }
    unfold sb in HIN; unfolder in HIN; desf.
    apply HIN0 with (c := c); unfold sb; unfolder; splits.
    all: eauto.
    { unfold sb in SB1; unfolder in SB1; apply SB1. }
    unfold sb in SB2; unfolder in SB2; apply SB2. }
  split; unfold sb; ins.
  { unfolder; splits; eauto. }
  unfolder in R1; desf.
  { eapply LAST; unfold sb; unfolder; splits; eauto. }
  { rewrite R1 in NEXT; eapply ext_sb_irr; eauto. }
  { eapply sb_irr with (G := mapped_G_t_with_b_srf l); eapply R2. }
  rewrite R1 in NEXT; eapply ext_sb_irr; eauto.
Qed.

Lemma mapped_exec_equiv :
    exec_equiv G_s (mapped_G_t (lab_s a)).
Proof using REORD.
  constructor; ins; try apply REORD.
  all: rewrite ?REORD.(gs_data), ?REORD.(gt_data),
               ?REORD.(gs_addr), ?REORD.(gt_addr),
               ?REORD.(gs_ctrl), ?REORD.(gt_ctrl).
  all: try now (symmetry; apply collect_rel_empty).
  apply functional_extensionality. intro x.
  tertium_non_datur (x = a); subst; rupd; ins.
  rewrite REORD.(events_lab); ins.
Qed.

Lemma eq_tid : tid a = tid b.
Proof using REORD.
  enough (OR : tid a = tid b \/ is_init a).
  { desf. exfalso. now apply REORD in OR. }
  eapply sb_tid_init, immediate_in, REORD.
Qed.

Lemma b_not_init : ~is_init b.
Proof using REORD.
  enough (SB : (sb_t ⨾ ⦗set_compl is_init⦘) a b).
  { unfolder in SB; desf. }
  apply no_sb_to_init, immediate_in, REORD.
Qed.

End ReorderingDefs.

Global Hint Unfold mapper : unfolderDB.

End ReordCommon.