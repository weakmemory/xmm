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
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.
From imm Require Import CombRelations.

Section Behavior.

Variable G : execution.
Variable traces : thread_id -> trace label -> Prop.

Notation "'lab'" := (lab G).
Notation "'co'" := (co G).

Definition thread_terminated (t : thread_id) : Prop :=
  traces t (thread_trace G t).
Definition machine_terminated := forall t, thread_terminated t.
(* TODO: fix behavior to be a function from location to
         ordered by co (possibly infinite) set of values written to the location *)
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

Lemma mapper_surj (NEQ : a <> b) y :
  exists x, y = mapper x.
Proof using.
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

Lemma mapper_acts
    (SAME : E_t a <-> E_t b) :
  mapper ↑₁ E_t ≡₁ E_t.
Proof using.
  unfolder; split; ins; desf.
  { tertium_non_datur (y = a) as [HEQA|NEQA];
    tertium_non_datur (y = b) as [HEQB|NEQB]; subst.
    all: rewrite ?mapper_eq_a, ?mapper_eq_b, ?mapper_neq; eauto. }
  tertium_non_datur (x = a) as [HEQA|NEQA];
  tertium_non_datur (x = b) as [HEQB|NEQB]; subst.
  all: eauto using mapper_eq_a, mapper_eq_b, mapper_neq.
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

Lemma mapped_G_t_sb_helper lab' r
    (SUBORIG : r ⊆ sb_t)
    (ANINIT : ~is_init a)
    (BNINIT : ~is_init b)
    (IMM : immediate ext_sb a b)
    (RNOT : ~r a b)
    (SAME : E_t a <-> E_t b) :
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
    (RNDOM : ~dom_rel r b)
    (SAME : E_t a <-> E_t b) :
  mapper ↑ r ⊆ immediate (sb (exec_mapped G_t mapper lab')).
Proof using.
  (* Using previous lemma as shortcut *)
  unfolder; intros x y HREL; desf.
  split; [eapply mapped_G_t_sb_helper with (r := r); eauto |].
  { rewrite SUBORIG. now apply immediate_in. }
  { split; ins. }
  { unfolder; exists x', y'; eauto. }
  intros c SB1 SB2.
  (* Actual proof *)
  admit.
Admitted.

Lemma mapped_exec_equiv
    (SAME : E_t a <-> E_t b):
  exec_equiv G_s (exec_mapped G_t mapper (lab_t ∘ mapper)).
Proof using REORD.
  constructor; ins; try apply REORD.
  all: rewrite ?REORD.(gs_data), ?REORD.(gt_data),
               ?REORD.(gs_addr), ?REORD.(gt_addr),
               ?REORD.(gs_ctrl), ?REORD.(gt_ctrl).
  all: try now (symmetry; apply collect_rel_empty).
  { rewrite mapper_acts; [apply REORD | ins]. }
  rewrite <- REORD.(events_lab), Combinators.compose_assoc,
          mapper_mapper_compose, Combinators.compose_id_right; ins.
  apply REORD.
Qed.

Lemma mapped_G_t_wf
    (ANINIT : ~is_init a)
    (BNINIT : ~is_init b)
    (NRMWDEP : ~rmw_dep_t a b)
    (IMM : immediate ext_sb a b)
    (DATA : data_t ≡ ∅₂)
    (ADDR : addr_t ≡ ∅₂)
    (CTRL : ctrl_t ≡ ∅₂)
    (WF : Wf G_t)
    (SAME : E_t a <-> E_t b)
    (NABRMW : ~rmw_t a b)
    (NARMW : ~codom_rel rmw_t a)
    (NBRMW : ~dom_rel rmw_t b)
    (NEQ : a <> b)
    (SAME_TID : tid a = tid b):
  Wf (exec_mapped G_t mapper (lab_t ∘ mapper)).
Proof using.
  apply exec_mapped_wf; auto using mapper_inj.
  { now apply mapper_surj. }
  { now rewrite Combinators.compose_assoc, mapper_mapper_compose,
            Combinators.compose_id_right. }
  { apply mapped_G_t_immsb_helper; ins. apply WF. }
  { rewrite DATA; basic_solver. }
  { rewrite ADDR; basic_solver. }
  { apply mapped_G_t_sb_helper; ins. apply WF. }
  { ins. apply mapper_init_actid; ins. }
  unfolder. intros x y XIN YIN XYEQ TIDEQ XINIT.
  desf. rename y0 into x, y1 into y.
  destruct (classic (x = a)) as [HEQXA|HEQXA],
           (classic (y = b)) as [HEQYB|HEQYB],
           (classic (y = a)) as [HEQYA|HEQYA],
           (classic (x = b)) as [HEQXB|HEQXB].
  all: try congruence.
  all: subst; rewrite ?mapper_eq_a, ?mapper_eq_b in *.
  all: rewrite ?mapper_neq in *; ins.
  all: try now apply WF; eauto 11.
  rewrite mapper_tid; ins.
  unfolder. ins. desf. now apply WF.
Qed.

Lemma mapped_G_t_cont lab'
    (ANINIT : ~is_init a)
    (BNINIT : ~is_init b)
    (SAME : E_t a <-> E_t b)
    (NEQ : a <> b)
    (CONT : contigious_actids G_t) :
  contigious_actids (exec_mapped G_t mapper lab').
Proof using.
  admit.
Admitted.

End ReorderingDefs.

Section MapperCfg.

Variable X : WCore.t.
Variable a b : actid.

Notation "'mapper'" := (mapper a b).
Notation "'GC'" := (WCore.GC X).
Notation "'G'" := (WCore.G X).
Notation "'cmt'" := (WCore.cmt X).
Notation "'sc'" := (WCore.sc X).

Notation "'labC'" := (lab GC).
Notation "'EC'" := (acts_set GC).
Notation "'sbC'" := (sb GC).
Notation "'rfC'" := (rf GC).
Notation "'coC'" := (co GC).
Notation "'rmwC'" := (rmw GC).
Notation "'dataC'" := (data GC).
Notation "'ctrlC'" := (ctrl GC).
Notation "'addrC'" := (addr GC).

Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'ctrl'" := (ctrl G).
Notation "'addr'" := (addr G).

Lemma mapped_G_t_cfg
    (ANINIT : ~is_init a)
    (BNINIT : ~is_init b)
    (SAME_TID : tid a = tid b)
    (NRMWDEP : ~rmw_dep GC a b)
    (IMM : immediate ext_sb a b)
    (NEQ : a <> b)
    (SAME : E a <-> E b)
    (SAMEC : EC a <-> EC b)
    (NABRMW : ~rmwC a b)
    (NARMW : ~codom_rel rmwC a)
    (NBRMW : ~dom_rel rmwC b)
    (WF : WCore.wf X) :
  WCore.wf (cfg_mapped X mapper (labC ∘ mapper)).
Proof using.
  apply cfg_mapped_wf; auto using mapper_inj.
  { apply mapper_surj; ins. }
  { now rewrite Combinators.compose_assoc, mapper_mapper_compose,
                Combinators.compose_id_right. }
  { apply mapped_G_t_immsb_helper; ins. apply WF. }
  { apply mapped_G_t_sb_helper; ins. apply WF. }
  { auto using mapper_init_actid. }
  { unfolder. intros x y XIN YIN XYEQ TIDEQ XINIT.
    desf. rename y0 into x, y1 into y.
    destruct (classic (x = a)) as [HEQXA|HEQXA],
            (classic (y = b)) as [HEQYB|HEQYB],
            (classic (y = a)) as [HEQYA|HEQYA],
            (classic (x = b)) as [HEQXB|HEQXB].
    all: try congruence.
    all: subst; rewrite ?mapper_eq_a, ?mapper_eq_b in *.
    all: rewrite ?mapper_neq in *; ins.
    all: try now apply WF; eauto 11. }
  {rewrite mapper_tid; ins.
    unfolder. ins. desf. now apply WF. }
  { admit. }
  all: apply mapped_G_t_cont; ins; apply WF.
Admitted.

End MapperCfg.

End ReordCommon.