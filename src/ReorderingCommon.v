Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import AuxRel.
Require Import ExecEquiv.
Require Import ThreadTrace.
Require Import Core.
Require Import TraceSwap.
Require Import SubToFullExec.
Require Import ExecOps.
Require Import CfgOps.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
From imm Require Import imm_s_ppo.
Require Import xmm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.
Require Import xmm_comb_rel.

(* TODO: restore the lemmas about immediate program order *)

Section Behavior.

Variable G : execution.
Variable traces : thread_id -> trace label -> Prop.

Notation "'lab'" := (lab G).
Notation "'co'" := (co G).

Definition thread_terminated (t : thread_id) : Prop :=
  traces t (thread_trace G t).
Definition machine_terminated := forall t, thread_terminated t.
(* TODO: fix behavior to be a function from location to
         the co-last value. *)
Definition behavior := co.

End Behavior.

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
Notation "'Rex_t'" := (R_ex lab_t).
Notation "'F_t'" := (is_f lab_t).

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

Record reord : Prop :=
{ a_not_init : ~is_init a;
  events_diff : a <> b;
  events_locs_diff : loc_s a <> loc_s b;
  events_lab : lab_s ∘ mapper = lab_t;
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

Lemma mapper_self_inv (NEQ : a <> b) x : mapper (mapper x) = x.
Proof using.
  unfold mapper.
  tertium_non_datur (x = b) as [HEQA|HEQA]; subst; try now rupd.
  rewrite updo with (c := x); ins.
  tertium_non_datur (x = a) as [HEQB|HEQB]; subst; try now rupd.
Qed.

Lemma mapper_mapper_compose (NEQ : a <> b) : mapper ∘ mapper = id.
Proof using.
  apply functional_extensionality; ins.
  apply mapper_self_inv; ins.
Qed.

Lemma mapper_mapper_compose' {A} (f : actid -> A)
    (NEQ : a <> b) :
  f ∘ mapper ∘ mapper = f.
Proof using.
  now rewrite Combinators.compose_assoc,
              mapper_mapper_compose,
              Combinators.compose_id_right.
Qed.

Lemma mapper_surj (NEQ : a <> b) :
  surj_dom ⊤₁ mapper.
Proof using.
  red. intros y.
  exists (mapper y). now rewrite mapper_self_inv.
Qed.

Lemma mapper_inj (NEQ : a <> b) : inj_dom ⊤₁ mapper.
Proof using.
  unfolder. intros x y _ _ HEQ.
  destruct mapper_surj with (y := y) as [y' YHEQ]; ins.
  destruct mapper_surj with (y := x) as [x' XHEQ]; ins.
  rewrite XHEQ, YHEQ, !mapper_self_inv in HEQ; ins.
  now rewrite XHEQ, YHEQ, HEQ.
Qed.

Lemma mapper_acts_iff (s : actid -> Prop)
    (SAME : s a <-> s b) :
  mapper ↑₁ s ≡₁ s.
Proof using.
  unfolder; split; ins; desf.
  { tertium_non_datur (y = a) as [HEQA|NEQA];
    tertium_non_datur (y = b) as [HEQB|NEQB]; subst.
    all: rewrite ?mapper_eq_a, ?mapper_eq_b, ?mapper_neq; eauto. }
  tertium_non_datur (x = a) as [HEQA|NEQA];
  tertium_non_datur (x = b) as [HEQB|NEQB]; subst.
  all: eauto using mapper_eq_a, mapper_eq_b, mapper_neq.
Qed.

Lemma mapper_acts_niff (s : actid -> Prop)
    (INA : s a)
    (NINB : ~s b) :
  mapper ↑₁ s ∪₁ eq a ≡₁ s ∪₁ eq b.
Proof using.
  rewrite <- mapper_eq_b.
  rewrite <- set_collect_eq with (f := mapper) (a := b).
  rewrite <- set_collect_union, mapper_acts_iff; ins.
  unfolder; split; ins; desf; eauto.
Qed.

Lemma mapper_init_actid l
    (ANIT : ~is_init a)
    (BNIT : ~is_init b) :
  mapper (InitEvent l) = InitEvent l.
Proof using.
  unfold mapper; rupd; unfold is_init in *; desf.
Qed.

Lemma mapper_is_init
    (ANIT : ~is_init a)
    (BNIT : ~is_init b) :
  mapper ↑₁ is_init ≡₁ is_init.
Proof using.
  unfolder. split; ins; desf.
  { destruct y; ins. rewrite mapper_init_actid; ins. }
  destruct x; ins. exists (InitEvent l).
  now rewrite mapper_init_actid.
Qed.

Lemma mapper_tid
    (EQ_TID : tid a = tid b) :
  tid ∘ mapper = tid.
Proof using.
  apply functional_extensionality; ins.
  tertium_non_datur (x = a) as [HEQA|NEQA];
  tertium_non_datur (x = b) as [HEQB|NEQB]; subst.
  all : unfold compose; rewrite ?mapper_eq_a, ?mapper_eq_b, ?mapper_neq; ins.
Qed.

Lemma mapper_init
    (ANIT : ~is_init a)
    (BNIT : ~is_init b) :
  mapper ↑₁ (acts_set G_t ∩₁ is_init) ≡₁ acts_set G_t ∩₁ is_init.
Proof using.
  unfolder; split; intros x HSET; desf.
  { destruct y as [l | t i]; ins.
    now rewrite mapper_init_actid. }
  destruct x as [l | t i]; ins.
  exists (InitEvent l).
  now rewrite mapper_init_actid.
Qed.

Lemma mapper_tid' x
    (EQ_TID : tid a = tid b) :
  tid (mapper x) = tid x.
Proof using.
  change (tid (mapper x)) with ((tid ∘ mapper) x).
  now rewrite mapper_tid.
Qed.

Lemma mapper_thrdle r thrdle
    (TIDEQ : tid a = tid b)
    (SUB : r ⊆ tid ↓ thrdle) :
  mapper ↑ r ⊆ tid ↓ thrdle.
Proof using.
  unfolder. ins. desf.
  rewrite !mapper_tid'; ins.
  now apply SUB.
Qed.

Lemma mapped_G_t_sb_helper lab' r
    (SUBORIG : r ⊆ sb_t)
    (ANINIT : ~is_init a)
    (BNINIT : ~is_init b)
    (IMM : immediate ext_sb a b)
    (RNOT : ~r a b) :
  mapper ↑ r ⊆ sb (exec_mapped G_t mapper lab').
Proof using.
  (* Cook hypotheses *)
  unfolder; intros x y HREL; desf.
  unfolder in IMM.
  set (HREL' := HREL).
  apply SUBORIG in HREL'.
  unfold sb in HREL'; unfolder in HREL'.
  desf.
  (* Asserts *)
  assert (NEQ : a <> b).
  { intro F. apply ext_sb_irr with (x := a).
    now rewrite F at 2. }
  assert (NEQXY : x' <> y').
  { intro F. eapply ext_sb_irr with (x := x').
    now rewrite F at 2. }
  (* Preprocessing the goal *)
  unfold sb. unfolder. ins. splits.
  all: try now (unfolder; eauto).
  (* Proof *)
  destruct (classic (x' = a)) as [HEQXA|HEQXA],
           (classic (y' = b)) as [HEQYB|HEQYB],
           (classic (y' = a)) as [HEQYA|HEQYA],
           (classic (x' = b)) as [HEQXB|HEQXB].
  all: subst; try congruence.
  all: rewrite ?mapper_eq_a, ?mapper_eq_b, ?mapper_neq; ins.
  all: try now (eapply ext_sb_trans; eauto).
  (* FIXME: is prettier proof possible? *)
  { destruct ext_sb_semi_total_l with (z := b) (y := y') (x := a).
    all: ins; try now (exfalso; eauto).
    destruct ext_sb_tid_init with (x := a) (y := b); ins.
    destruct ext_sb_tid_init with (x := a) (y := y'); ins.
    destruct y', a, b; ins. congruence. }
  tertium_non_datur (is_init x') as [INIT|NINIT].
  { destruct x', a; ins. }
  destruct ext_sb_semi_total_r with (z := a) (y := x') (x := b).
  all: ins; try now (exfalso; eauto).
  destruct ext_sb_tid_init with (x := a) (y := b); ins.
  destruct ext_sb_tid_init with (x := x') (y := b); ins.
  destruct x', a, b; ins. congruence.
Qed.

Lemma mapped_G_t_immsb_helper lab' r
    (SUBORIG : r ⊆ immediate sb_t)
    (ANINIT : ~is_init a)
    (BNINIT : ~is_init b)
    (IMM : immediate ext_sb a b)
    (RNOT : ~r a b)
    (RNCODOM : ~codom_rel r a)
    (RNDOM : ~dom_rel r b) :
  mapper ↑ r ⊆ immediate (sb (exec_mapped G_t mapper lab')).
Proof using.
  (* Using previous lemma as shortcut *)
  unfolder; intros x y HREL; desf.
  split; [eapply mapped_G_t_sb_helper with (r := r); eauto |].
  { rewrite SUBORIG. now apply immediate_in. }
  { unfolder; exists x', y'; eauto. }
  intros c SB1 SB2.
  (* Cooking *)
  unfolder in IMM. desf.
  (* Asserts *)
  assert (NEQ : a <> b).
  { intro F. apply ext_sb_irr with (x := a).
    now rewrite F at 2. }
  assert (NEQXY : x' <> y').
  { intro F. eapply ext_sb_irr with (x := x').
    apply SUBORIG in HREL. unfold sb in HREL.
    unfolder in HREL. desf. }
  (* Actual proof *)
  destruct (classic (x' = a)) as [HEQXA|HEQXA],
           (classic (y' = b)) as [HEQYB|HEQYB],
           (classic (y' = a)) as [HEQYA|HEQYA],
           (classic (x' = b)) as [HEQXB|HEQXB].
  all: subst; try congruence.
  all: rewrite ?mapper_eq_a, ?mapper_eq_b, ?mapper_neq; ins.
  { apply SUBORIG in HREL. unfolder in HREL. desf.
    rewrite mapper_eq_a in SB1. rewrite mapper_neq in SB2; ins.
    unfold sb in SB1, SB2. unfolder in SB1. unfolder in SB2.
    ins. desf. red in SB5. destruct SB5 as (c' & CINE & HCEQ).
    rewrite mapper_neq in HCEQ.
    { unfold sb in HREL. unfolder in HREL. desf.
      apply HREL0 with c; unfold sb.
      all: unfolder; splits; ins.
      eapply ext_sb_trans with (y := b); ins. }
    all: intro F; subst c'.
    { rewrite mapper_eq_a in HCEQ; subst.
      eapply ext_sb_irr; eauto. }
    rewrite mapper_eq_b in HCEQ; subst.
    apply ext_sb_irr with (x := a), ext_sb_trans with (y := b); ins. }
  { apply SUBORIG in HREL. unfolder in HREL. desf.
    rewrite mapper_eq_b in SB2. rewrite mapper_neq in SB1; ins.
    unfold sb in SB1, SB2. unfolder in SB1. unfolder in SB2.
    ins. desf. red in SB5. destruct SB5 as (c' & CINE & HCEQ).
    rewrite mapper_neq in HCEQ.
    { subst c'.
      apply HREL0 with c; unfold sb; unfolder; splits; ins.
      all: unfold sb in HREL; unfolder in HREL; desf.
      apply ext_sb_trans with (y := a); ins. }
    { intro F; subst c'.
      rewrite mapper_eq_a in HCEQ; subst c.
      apply ext_sb_irr with (x := a).
      eapply ext_sb_trans with (y := b); ins. }
    intro F; subst c'.
    rewrite mapper_eq_b in HCEQ. subst c.
    eapply ext_sb_irr; eauto. }
  { apply SUBORIG in HREL. unfolder in HREL. desf.
    unfold sb in HREL; unfolder in HREL; desf.
    apply ext_sb_irr with (x := a), ext_sb_trans with (y := b); ins. }
  { apply RNCODOM; exists x'; eauto. }
  { apply RNDOM; exists y'; eauto. }
  rewrite mapper_neq in SB1, SB2; ins.
  apply SUBORIG in HREL. unfolder in HREL. desf.
  unfold sb in SB1, SB2. ins.
  apply seq_restr_eq_prod in SB1, SB2.
  destruct SB1 as [SB1 [XINE CINE]], SB2 as [SB2 [_ YINE]].
  destruct XINE as [x'' [XINE XEQ]], YINE as [y'' [YINE YEQ]],
           CINE as [c'' [CINE CEQ]].
  rewrite mapper_neq in XEQ, YEQ; ins.
  all: try intro F; try subst x''; try subst y''.
  all: try rewrite ?mapper_eq_a, ?mapper_eq_b in XEQ.
  all: try rewrite ?mapper_eq_a, ?mapper_eq_b in YEQ.
  all: try now (try subst x'; try subst y').
  rewrite mapper_neq in CEQ.
  { subst. eapply HREL0 with c; unfold sb; unfolder; splits; ins. }
  { intro F. subst c''. rewrite mapper_eq_a in CEQ. subst c.
    enough (EXTA : ext_sb x' a).
    { apply HREL0 with a; unfold sb; unfolder; splits; ins.
      apply ext_sb_trans with (y := b); ins. }
    tertium_non_datur (is_init x') as [XINIT|NINIT].
    { destruct x', a; ins. }
    destruct ext_sb_semi_total_r with b a x' as [FSB|FSB]; ins.
    { intro F. destruct a, x'; ins. do 2 desf. }
    exfalso. apply IMM0 with x'; ins. }
  intro F. subst c''. rewrite mapper_eq_b in CEQ. subst c.
  enough (EXTA : ext_sb b y').
  { apply HREL0 with b; unfold sb; unfolder; splits; ins.
    apply ext_sb_trans with (y := a); ins. }
  tertium_non_datur (is_init y') as [XINIT|NINIT].
  { destruct a, y'; ins. }
  destruct ext_sb_semi_total_l with a b y' as [FSB|FSB]; ins.
  { intro F. destruct a, b, y'; ins. do 2 desf. }
  exfalso. apply IMM0 with y'; ins.
Qed.

End ReorderingDefs.

End ReordCommon.