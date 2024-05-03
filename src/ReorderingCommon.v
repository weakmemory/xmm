Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import AuxRel.
Require Import ExecEquiv.
Require Import ThreadTrace.
Require Import Core.
Require Import TraceSwap.
Require Import SubToFullExec.
Require Import ExecOps.

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

Lemma mapper_surj (NEQ : a <> b) y :
  exists x, mapper x = y.
Proof using.
  exists (mapper y). now apply mapper_self_inv.
Qed.

Lemma mapper_inj (NEQ : a <> b) : inj_dom ⊤₁ mapper.
Proof using.
  unfolder. intros x y _ _ HEQ.
  destruct mapper_surj with (y := y) as [y' YHEQ]; ins.
  destruct mapper_surj with (y := x) as [x' XHEQ]; ins.
  rewrite <- XHEQ, <- YHEQ, !mapper_self_inv in HEQ; ins.
  now rewrite <- XHEQ, <- YHEQ, HEQ.
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

Lemma mapper_init
    (ANIT : ~is_init a)
    (BNIT : ~is_init b) :
  mapper ↑₁ (acts_set G_t ∩₁ is_init) ≡₁ acts_set G_t ∩₁ is_init.
Proof using.
  unfolder; split; ins; desf.
  { tertium_non_datur (y = a) as [HEQA|NEQA];
    tertium_non_datur (y = b) as [HEQB|NEQB]; subst.
    all: try now (exfalso; eauto).
    rewrite mapper_neq; eauto. }
  exists x; splits; eauto.
  tertium_non_datur (x = a) as [HEQA|NEQA];
  tertium_non_datur (x = b) as [HEQB|NEQB]; subst.
  all: try now (exfalso; eauto).
  rewrite mapper_neq; eauto.
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

(*
Lemma mapped_G_t_imm_sb
    (NINIT : ~is_init a)
    (HINA : E_t a)
    (LAST : max_elt sb_t a)
    (NEXT : ext_sb a b) :
  immediate (sb mapped_G_t_with_b_srf) ≡ immediate sb_t ∪ singl_rel a b.
Proof using.
  split; intros x y HIN.
  { unfold sb in HIN; ins. unfolder in HIN; desf.
    all: try now (exfalso; eapply ext_sb_irr; eauto).
    { left; unfold sb; unfolder; splits; ins; desf.
      eauto 10. }
    { exfalso. eapply mapped_G_t_with_b_srf_b_max; ins.
      unfold sb; ins; unfolder; splits; eauto. }
    tertium_non_datur (x = a) as [ISA|ISA]; subst.
    { now right. }
    exfalso. tertium_non_datur (is_init x) as [INI|INI].
    { apply HIN0 with (c := a); splits; eauto.
      destruct a, x; ins. }
    assert (TIDEQ : tid a = tid x).
    { unfold ext_sb in NEXT, HIN1; do 2 desf. }
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
  { eapply sb_irr with (G := mapped_G_t_with_b_srf); eapply R2. }
  rewrite R1 in NEXT; eapply ext_sb_irr; eauto.
Qed. *)

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
  { admit. }
  admit.
Admitted.

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
    (NEQ : a <> b) :
  Wf (exec_mapped G_t mapper (lab_t ∘ mapper)).
Proof using.
  apply exec_mapped_wf; auto using mapper_inj.
  { intro y. edestruct mapper_surj; eauto. }
  { admit. }
  { apply mapped_G_t_immsb_helper; ins. apply WF. }
  { rewrite DATA; basic_solver. }
  { rewrite ADDR; basic_solver. }
  { apply mapped_G_t_sb_helper; ins. apply WF. }
  { admit. }
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
Admitted.

End ReorderingDefs.

Section MapperCfg.

Variable X : WCore.t.
Variable a b : actid.

Notation "'mapper'" := (mapper a b).
Notation "'GC'" := (WCore.GC X).
Notation "'G'" := (WCore.G X).
Notation "'cmt'" := (WCore.cmt X).

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

Lemma mapped_G_t_pfx
    (NEQ : a <> b)
    (SAME : E a <-> E b)
    (SAMEC : EC a <-> EC b)
    (PFX : exec_prefix GC G) :
  exec_prefix
    (exec_mapped GC mapper (labC  ∘ mapper))
    (exec_mapped G  mapper (lab ∘ mapper)).
Proof using.
  destruct PFX. constructor; ins.
  constructor; ins.
  { rewrite !mapper_acts; ins. apply pfx_sub. }
  { admit. }
  { now rewrite pfx_sub.(sub_lab). }
  all: try rewrite <- collect_rel_eqv,
                   <- !collect_rel_seq.
  all: try now (apply collect_rel_more, pfx_sub).
  all: try now eapply inj_dom_mori, mapper_inj; eauto; ins.
  { now rewrite seq_false_l, seq_false_r. }
  { admit. }
  admit.
Admitted.

Lemma mapped_G_t_cfg
    (ANINIT : ~is_init a)
    (BNINIT : ~is_init b)
    (NRMWDEP : ~rmw_dep GC a b)
    (IMM : immediate ext_sb a b)
    (NEQ : a <> b)
    (SAME : E a <-> E b)
    (SAMEC : EC a <-> EC b)
    (NABRMW : ~rmwC a b)
    (NARMW : ~codom_rel rmwC a)
    (NBRMW : ~dom_rel rmwC b)
    (WF : WCore.wf X) :
  WCore.wf (WCore.Build_t
    (exec_mapped G  mapper (lab ∘ mapper))
    (exec_mapped GC mapper (labC  ∘ mapper))
    (mapper ↑₁ cmt)
  ).
Proof using.
  destruct WF. constructor; ins.
  { rewrite cc_ctrl_empty. apply collect_rel_empty. }
  { rewrite cc_addr_empty. apply collect_rel_empty. }
  { rewrite cc_data_empty. apply collect_rel_empty. }
  { apply mapped_G_t_wf; ins. }
  { admit. }
  { admit. }
  { apply set_collect_mori; ins. }
  { unfold sb. rewrite restr_relE, seq_seq_inter; ins.
    basic_solver. }
  { rewrite restr_relE,
            <- set_collect_interE, <- collect_rel_eqv; eauto.
    rewrite <- !collect_rel_seq, <- restr_relE.
    all: try now eapply inj_dom_mori, mapper_inj; eauto; ins.
    apply collect_rel_mori; ins. }
  { rewrite <- set_collect_codom, <- set_collect_union,
            exec_mapped_R with (G := G), <- set_collect_interE.
    { apply set_collect_mori; ins. }
    { apply mapper_inj; ins. }
    { intro x. destruct (mapper_surj a b NEQ x); eauto. }
    admit. }
  { rewrite <- collect_rel_eqv, <- collect_rel_seq,
            exec_mapped_R with (G := G), <- set_collect_interE,
            <- set_collect_codom.
    { apply set_collect_mori; ins. }
    { apply mapper_inj; ins. }
    { intro x. destruct (mapper_surj a b NEQ x); eauto. }
    { admit. }
    eapply inj_dom_mori, mapper_inj; eauto; ins. }
  apply mapped_G_t_pfx; ins.
Admitted.

End MapperCfg.

End ReordCommon.