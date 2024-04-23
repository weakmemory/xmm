Require Import Lia Setoid Program.Basics.
Require Import AuxDef.
Require Import ThreadTrace.

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

From RecordUpdate Require Import RecordSet.
(* Import RecordSetNotations. *)
Open Scope program_scope.

Import ListNotations.

Set Implicit Arguments.

#[export] Instance eta_execution : Settable _ :=
  settable! Build_execution
    <acts_set; threads_set; lab; rmw; data; addr; ctrl; rmw_dep; rf; co>
.

(* G' is exec_prefix of G *)
Record exec_prefix G G' : Prop := {
  pfx_sub : sub_execution G G' ∅₂ ∅₂;
  pfx_cont1 : contigious_actids G;
  pfx_cont2 : contigious_actids G';
}.


Section Race.
Variable G : execution.
Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'same_loc'" := (same_loc lab).
Notation "'mod'" := (mod lab).
Notation "'W'" := (is_w lab).
Notation "'hb'" := (hb G).
Notation "'ppo'" := (ppo G).
Notation "'bob'" := (bob G).
Notation "'rf'" := (rf G).
Notation "'sb'" := (sb G).
Notation "'eco'" := (eco G).

Definition one (s : actid -> Prop) : relation actid :=
    fun x y => s x \/ s y.

Definition race := restr_rel E (one W ∩ same_loc \ clos_sym hb).

Definition race_mod (o : mode) := race ∩ one (fun e => mode_le (mod e) o).
End Race.

Module WCore.

Record t := {
  G : execution;
  GC : execution;
  cmt : actid -> Prop;
}.

Definition init_exec G : execution :=
  Build_execution (acts_set G ∩₁ is_init) (threads_set G) (lab G) ∅₂ ∅₂ ∅₂ ∅₂ ∅₂ ∅₂ ∅₂.

#[global]
Hint Unfold init_exec : unfolderDb.

Section Consistency.

Variable G : execution.
Notation "'hb'" := (hb G).
Notation "'fr'" := (fr G).
Notation "'sb'" := (sb G).
Notation "'eco'" := (eco G).
Notation "'psc'" := (imm.psc G).

Record is_cons : Prop := {
  cons_coherence : irreflexive (hb ⨾ eco^?);
  cons_atomicity : irreflexive (fr ⨾ sb);
  cons_sc : acyclic psc;
}.

End Consistency.

Section CoreDefs.

Variable X : t.
Notation "'G'" := (G X).
Notation "'GC'" := (GC X).
Notation "'ctrlc'" := (ctrl GC).
Notation "'datac'" := (data GC).
Notation "'addrc'" := (addr GC).
Notation "'ctrl'" := (ctrl G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'cmt'" := (cmt X).
Notation "'lab'" := (lab G).
Notation "'R'" := (is_r lab).
Notation "'W'" := (is_w lab).
Notation "'sbc'" := (sb GC).
Notation "'rfc'" := (rf GC).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'EC'" := (acts_set GC).
Notation "'E'" := (acts_set G).

Record wf : Prop := {
  cc_ctrl_empty : ctrlc ≡ ∅₂;
  cc_addr_empty : addrc ≡ ∅₂;
  cc_data_empty : datac ≡ ∅₂;

  wf_gc : Wf GC;
  wf_g_init : EC ∩₁ is_init ⊆₁ E;
  wf_gc_acts : (tid ↓₁ eq tid_init) ∩₁ EC ⊆₁ is_init;

  C_sub_EC : cmt ⊆₁ EC;
  sub_sb : restr_rel (cmt ∩₁ E) sbc ⊆ sb;
  sub_rf : restr_rel (cmt ∩₁ E) rfc ⊆ rf;
  sub_rfD : E ∩₁ R ⊆₁ codom_rel rf ∪₁ cmt;
  sub_rfW : cmt ∩₁ R ⊆₁ codom_rel (⦗cmt⦘ ⨾ rfc);

  pfx : exec_prefix GC G;
}.

End CoreDefs.

Global Hint Resolve wf_gc : xmm.

Section DeltaDefs.

Variable GC : execution.
Variable e : actid.

Notation "'W'" := (is_w (lab GC)).
Notation "'R'" := (is_r (lab GC)).
Notation "'rfc'" := (rf GC).
Notation "'W_ex'" := (W_ex GC).

(* We do not need sb_delta as `sb` has an exact formula *)
(* Definition sb_delta : relation actid :=
  (E ∩₁ (fun x => tid x = tid e)) × eq e. *)

Definition rf_delta_R (w : option actid) :=
  match w with
  | Some w => singl_rel w e ∩ W × R
  | _ => ∅₂
  end.

Definition rf_delta_W E : relation actid :=
  if W e then ⦗eq e⦘ ⨾ rfc ⨾ ⦗E⦘
  else ∅₂.

Definition co_delta (W1 W2 : actid -> Prop) : relation actid :=
  if W e then eq e × W1 ∪ W2 × eq e
  else ∅₂.

Definition rmw_delta (r : option actid) : relation actid :=
  (R ∩₁ eq_opt r) × (W ∩₁ eq e). (* FIXME: is_exclusive dropped *)

End DeltaDefs.

#[global]
Hint Unfold rf_delta_R rf_delta_W co_delta rmw_delta : unfolderDb.

Section CfgAddEventStep.

Variable traces : thread_id -> trace label -> Prop.

Variable X X' : t.
Notation "'G''" := (G X').
Notation "'GC''" := (GC X').
Notation "'cmt''" := (cmt X').
Notation "'E''" := (acts_set G').
Notation "'lab''" := (lab G').

Notation "'G'" := (G X).
Notation "'GC'" := (GC X).
Notation "'cmt'" := (cmt X).
Notation "'E'" := (acts_set G).

Definition new_event_correct e : Prop :=
  match thread_trace G (tid e) with
  | trace_inf _ => False
  | trace_fin l =>
    exists tr, traces (tid e) tr /\ trace_prefix (trace_fin (l ++ [lab' e])) tr
  end.

Record cfg_add_event_gen e r w W1 W2 :=
{ e_notin : ~(E e);
  e_notinit : ~ is_init e;
  e_new : E' ≡₁ E ∪₁ (eq e);
  e_correct : new_event_correct e;

  cmt_graph_same : GC' = GC;

  (* Skipping condition for sb *)
  rf_new : rf G' ≡ rf G ∪ rf_delta_R GC e w ∪ rf_delta_W GC e (cmt ∩₁ E);
  co_new : co G' ≡ co G ∪ co_delta GC e W1 W2;
  rmw_new : rmw G' ≡ rmw G ∪ rmw_delta GC e r;

  wf_new_conf : wf X';
}.

Definition cfg_add_event (e : actid) :=
  exists r w W1 W2, cfg_add_event_gen e r w W1 W2.

Definition cfg_add_event_uninformative := exists e, cfg_add_event e.

End CfgAddEventStep.

Global Hint Unfold new_event_correct cfg_add_event
                   cfg_add_event_uninformative : unfolderDb.

Section ExecAdd.

Variables G G' : execution.
Variable traces : thread_id -> trace label -> Prop.

Record exec_inst e := {
  add_event : cfg_add_event traces
    (Build_t G G' ∅)
    (Build_t G' G' ∅)
    e;
  next_cons : is_cons G';
}.

End ExecAdd.

Section ExecRexec.

Variables G G' : execution.
Variable traces : thread_id -> trace label -> Prop.
Variable rfre : relation actid.

Notation "'E''" := (acts_set G').
Notation "'E'" := (acts_set G).
Notation "'W'" := (is_w (lab G)).
Notation "'R'" := (is_r (lab G)).
Notation "'race'" := (race G).
Notation "'lab''" := (lab G').
Notation "'lab'" := (lab G).
Notation "'same_loc'" := (same_loc lab).
Notation "'hb'" := (hb G).
Notation "'hbloc'" := (same_loc ∩ hb).
Notation "'re'" := (⦗W⦘ ⨾ (race ∪ hbloc) ⨾ ⦗R⦘).
Notation "'rf''" := (rf G').
Notation "'sb''" := (sb G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'sb_rf'" := ((sb ∪ rf)⁺).
Notation "'sb_rf''" := ((sb' ∪ rf')⁺).

Notation "'Rre'" := (codom_rel rfre).
Notation "'Wre'" := (dom_rel rfre).

Definition f_cmt (f : actid -> option actid) := is_some ∘ f.
Definition sb_rfre := (sb ∪ rf ⨾ ⦗E \₁ Rre⦘ ∪ rfre ⨾ ⦗Rre⦘)⁺.

Record correct_embeding f : Prop :=
{ reexec_embd_inj : inj_dom (f_cmt f) f;
  reexec_embd_dom : f_cmt f ⊆₁ E';
  reexec_embd_tid : (fun x y => f x = Some y) ⊆ same_tid;
  reexec_embd_lab : forall ec e (MAPPED : f e = Some ec),
                      lab' ec = lab e;
  reexec_embd_sb : Some ↓ (f ↑ restr_rel (f_cmt f) sb') ⊆ sb;
  reexec_embd_rf : Some ↓ (f ↑ restr_rel (f_cmt f) rf') ⊆ rf; }.

Record stable_uncmt_reads_gen f r w : Prop :=
{ surg_is_r : R r;
  surg_is_w : W w;
  surg_ncmt : ~f_cmt f r;
  surg_sb : sb w r;
  surg_sbrf : dom_rel (rf ⨾ ⦗eq r⦘) ∩₁ codom_rel (⦗eq w⦘ ⨾ sb_rf^?) ⊆₁
              dom_rel (sb_rf^? ⨾ sb ⨾ ⦗eq r⦘); }.

Record reexec_gen f dtrmt : Prop :=
{ (* Correct start *)
  rfre_racy : rfre ⊆ re;
  dtrmt_not_reexec : dtrmt ⊆₁ E \₁ codom_rel (⦗Rre⦘ ⨾ (sb ∪ rf)＊);
  dtrmt_cmt : dtrmt ⊆₁ (f_cmt f);
  rfre_writes_cmt : Wre ⊆₁ (f_cmt f);
  rfrre_embd_gc : rfre ⊆ Some ↓ (f ↑ rf');
  reexec_sur : forall r w, stable_uncmt_reads_gen f r w;
  (* Correct embedding *)
  reexec_embd_corr : correct_embeding f;
  reexec_embd_sbrfe : Some ↓ (f ↑ restr_rel (f_cmt f) sb_rf') ⊆
                      restr_rel (Some ↓₁ (f ↑₁ (f_cmt f))) sb_rfre;
  (* Reproducable steps *)
  reexec_start_wf : wf (Build_t G G' (f_cmt f));
  reexec_steps : (cfg_add_event_uninformative traces)＊
    (Build_t (restrict G dtrmt) G' (f_cmt f))
    (Build_t G'                 G' (f_cmt f));
  rexec_final_cons : is_cons G'; }.

Definition reexec : Prop := exists f dtrmt, reexec_gen f dtrmt.

End ExecRexec.

Global Hint Unfold reexec : unfolderDb.

Section WCoreWfProps.

Variable X : t.
Variable WF : wf X.

Notation "'G'" := (G X).
Notation "'ctrl'" := (ctrl G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'GC'" := (GC X).
Notation "'cmt'" := (cmt X).
Notation "'labc'" := (lab GC).
Notation "'lab'" := (lab G).
Notation "'sbc'" := (sb GC).
Notation "'rfc'" := (rf GC).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'EC'" := (acts_set GC).
Notation "'E'" := (acts_set G).

Lemma wf_g : Wf G.
Proof using WF.
  eapply sub_WF; try now apply WF.
  rewrite set_interC; apply WF.
Qed.

Lemma wf_g_cont : contigious_actids G.
Proof using WF.
  apply WF.
Qed.

Lemma wf_gc_cont : contigious_actids GC.
Proof using WF.
  apply WF.
Qed.

Lemma wf_g_acts : (tid ↓₁ eq tid_init) ∩₁ E ⊆₁ is_init.
Proof using WF.
  transitivity (tid ↓₁ eq tid_init ∩₁ EC); try now apply WF.
  apply set_subset_inter; try now apply WF.
  now apply set_map_mori.
Qed.

Lemma wf_actid_tid e
    (IN : E e)
    (NOT_INIT : ~is_init e) :
  tid e <> tid_init.
Proof using WF.
  intro F. enough (is_init e) by auto.
  apply wf_g_acts; basic_solver.
Qed.

Lemma ext_sb_dense x y
    (XNOT_INIT : tid x <> tid_init)
    (IN : E y)
    (SB : ext_sb x y) :
  E x.
Proof using WF.
  assert (YNOT_INIT : ~is_init y).
  { apply ext_sb_to_non_init in SB.
    unfolder in SB; desf. }
  assert (Y_TID : tid y = tid x).
  { destruct (ext_sb_tid_init x y SB); auto.
    destruct x; ins. }
  unfold ext_sb in SB; desf; ins; desf.
  set (ACTS := wf_g_cont XNOT_INIT). desf.
  apply in_restr_acts, ACTS, thread_set_iff in IN.
  apply ACTS, thread_set_iff. lia.
Qed.

Lemma wf_set_sz thr N
    (NOT_INIT : thr <> tid_init)
    (SZ_EQ : set_size (E ∩₁ (fun e => thr = tid e)) = NOnum N) :
  E ∩₁ (fun e => thr = tid e) ≡₁ thread_seq_set thr N.
Proof using WF.
  set (HEQ := wf_g_cont NOT_INIT). desf.
  rewrite HEQ in *.
  now apply thread_seq_N_eq_set_size.
Qed.

Lemma wf_set_sz_helper e N
    (IN : E e)
    (NOT_INIT : ~is_init e)
    (SZ_EQ : set_size (E ∩₁ same_tid e) = NOnum N) :
  E ∩₁ same_tid e ≡₁ thread_seq_set (tid e) N.
Proof using WF.
  apply wf_set_sz with (thr := tid e); auto.
  now apply wf_actid_tid.
Qed.

Lemma all_trace_fin t
    (NOT_INIT : t <> tid_init) :
  trace_finite (thread_trace G t).
Proof using WF.
  set (CONT := wf_g_cont NOT_INIT). desf.
  unfold thread_trace, trace_finite.
  eexists. erewrite thread_actid_trace_form; eauto.
  ins.
Qed.

Lemma wf_trace_prefix : exec_trace_prefix GC G.
Proof using WF.
  unfold exec_trace_prefix; ins.
  apply thread_actid_trace_prefix, set_subset_inter; auto.
  apply WF.
Qed.

End WCoreWfProps.

Global Hint Resolve wf_actid_tid wf_set_sz wf_set_sz_helper :
  xmm.

Section WCoreStepProps.

Variable traces : thread_id -> trace label -> Prop.

Variable X X' : t.
Notation "'G''" := (G X').
Notation "'GC''" := (GC X').
Notation "'cmt''" := (cmt X').
Notation "'E''" := (acts_set G').
Notation "'lab''" := (lab G').

Notation "'G'" := (G X).
Notation "'GC'" := (GC X).
Notation "'cmt'" := (cmt X).
Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).

Lemma add_step_event_set e
    (ADD_STEP : cfg_add_event traces X X' e) :
  (E' ∩₁ set_compl is_init) e.
Proof using.
  red in ADD_STEP. desf.
  split; try apply ADD_STEP.
  now right.
Qed.

Lemma new_conf_wf e
    (ADD_STEP : cfg_add_event traces X X' e) :
  wf X'.
Proof using.
  red in ADD_STEP. desf.
  apply ADD_STEP.
Qed.

Lemma same_lab e
  (WF : wf X)
  (ADD_STEP : cfg_add_event traces X X' e) :
  lab' = lab.
Proof using.
  red in ADD_STEP. desf.
  erewrite sub_lab with (G' := G)  (G := GC),
           sub_lab with (G' := G') (G := GC').
  { f_equal; apply ADD_STEP. }
  { apply ADD_STEP. }
  apply WF.
Qed.

Lemma add_step_trace_eq e N
    (WF : wf X)
    (ADD_STEP : cfg_add_event traces X X' e)
    (SZ_EQ : set_size (E ∩₁ same_tid e) = NOnum N):
  thread_trace G' (tid e) =
    trace_app (thread_trace G (tid e)) (trace_fin [lab' e]).
Proof using.
  assert (SAME : lab' = lab) by (eapply same_lab; eauto).
  red in ADD_STEP. desf.
  eapply add_event_to_trace.
  all: try now apply ADD_STEP.
  { eapply wf_actid_tid; apply ADD_STEP; now right. }
  { now rewrite updI. }
  { apply SZ_EQ. }
  apply WF.
Qed.

Lemma add_step_new_event_correct e
    (ADD_STEP : cfg_add_event traces X X' e) :
  exists tr, traces (tid e) tr /\
    trace_prefix (trace_app (thread_trace G (tid e)) (trace_fin [lab' e])) tr.
Proof using.
  red in ADD_STEP. desf.
  generalize (e_correct ADD_STEP).
  unfold new_event_correct. desf.
Qed.

(* NOTE: might be good as a standalone lemma *)
Lemma add_step_trace_coh e
    (WF : wf X)
    (ADD_STEP : cfg_add_event traces X X' e)
    (G_COH : trace_coherent traces G) :
  trace_coherent traces G'.
Proof using.
  red. ins.
  destruct (classic (thr = (tid e))) as [HEQ_TIDE|HEQ_TIDE].
  { subst. set (EQ := wf_g_cont WF NOT_INIT). desf.
    erewrite add_step_trace_eq; eauto using add_step_new_event_correct.
    erewrite set_size_equiv, thread_seq_set_size; eauto. }
  set (HCORR := G_COH thr NOT_INIT). desf.
  exists tr; split; auto.
  enough (NO_CHANGE : thread_trace G' thr = thread_trace G thr).
  { now rewrite NO_CHANGE. }
  unfold thread_trace. erewrite same_lab; eauto.
  f_equal. red in ADD_STEP; desf.
  unfold thread_actid_trace. rewrite ADD_STEP.(e_new).
  rewrite set_inter_union_l.
  arewrite (eq e ∩₁ (fun x => thr = tid x) ≡₁ ∅); [basic_solver |].
  now rewrite set_union_empty_r.
Qed.

End WCoreStepProps.

Global Hint Resolve new_conf_wf add_step_trace_coh :
  xmm.

End WCore.
