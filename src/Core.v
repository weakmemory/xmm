Require Import Lia Setoid Program.Basics.
Require Import AuxDef AuxRel.
Require Import ThreadTrace.
Require Import ExecRestrEq.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import imm_s.
From imm Require Import SubExecution.
From imm Require Import FinExecution.
From imm Require Import FinThreads.

From RecordUpdate Require Import RecordSet.
(* Import RecordSetNotations. *)
Open Scope program_scope.

Import ListNotations.

Set Implicit Arguments.

#[export] Instance eta_execution : Settable _ :=
  settable! Build_execution
    <acts_set; threads_set; lab; rmw; data; addr; ctrl; rmw_dep; rf; co>
.

Section RfComplete.

Variable G : execution.
Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'R'" := (is_r lab).
Notation "'rf'" := (rf G).

Definition rf_complete : Prop :=
    E ∩₁ R ⊆₁ codom_rel rf.

End RfComplete.

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
  sc : relation actid;
}.

Definition init_exec G : execution :=
  Build_execution (acts_set G ∩₁ is_init) (threads_set G) (lab G) ∅₂ ∅₂ ∅₂ ∅₂ ∅₂ ∅₂ ∅₂.

#[global]
Hint Unfold init_exec : unfolderDb.

Section Consistency.

Variable G : execution.
Variable sc : relation actid.
Notation "'hb'" := (hb G).
Notation "'fr'" := (fr G).
Notation "'sb'" := (sb G).
Notation "'eco'" := (eco G).
Notation "'rmw'" := (rmw G).

Record is_cons : Prop := {
  cons_coherence : irreflexive (hb ⨾ eco^?);
  cons_atomicity : rmw ∩ (fr ⨾ sb) ≡ ∅₂;
  cons_sc : acyclic sc;
}.

End Consistency.

Section Wf.

Variable X XC : t.
Variable cmt : actid -> Prop.

Notation "'GC'" := (G XC).
Notation "'G'" := (G X).
Notation "'ctrlc'" := (ctrl GC).
Notation "'datac'" := (data GC).
Notation "'addrc'" := (addr GC).
Notation "'ctrl'" := (ctrl G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'lab'" := (lab G).
Notation "'R'" := (is_r lab).
Notation "'W'" := (is_w lab).
Notation "'sbc'" := (sb GC).
Notation "'rfc'" := (rf GC).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'EC'" := (acts_set GC).
Notation "'E'" := (acts_set G).
Notation "'sc'" := (sc X).

(*
  Structural properties, that have not much
  to do with the actual model in question.
*)
Record wf_struct : Prop := {
  wstru_fin_threads : fin_threads GC;
  wstru_cc_ctrl_empty : ctrlc ≡ ∅₂;
  wstru_struct_cc_addr_empty : addrc ≡ ∅₂;
  wstru_cc_data_empty : datac ≡ ∅₂;
  wstru_g_cont : contigious_actids G;
  wstru_gc_cont : contigious_actids GC;
  wstru_wf_g_init : EC ∩₁ is_init ⊆₁ E;
  wstru_wf_gc_acts : (tid ↓₁ eq tid_init) ∩₁ EC ⊆₁ is_init;
}.

(*
  Actual propeties that are important for
  the model to function.
*)
Record wf_props := {
  wprop_wf_g : Wf G;
  wprop_wf_ereq : exec_restr_eq G GC cmt;
  wprop_wf_rfc : rf_complete (restrict GC cmt);
  wprop_sub_rfD : E ∩₁ R ⊆₁ codom_rel rf ∪₁ cmt;
  wfprop_wf_sc : wf_sc G sc;
}.

Definition wf : Prop :=
  << STRUCT : wf_struct >> /\
  << PROPS : wf_props >>.

Lemma wf_iff_struct_and_props :
  wf <-> << STRUCT : wf_struct >> /\ << PROPS : wf_props >>.
Proof using.
  split; [intros WF | intros STRUPROPS].
  { split; constructor; ins; apply WF. }
  constructor; ins; try apply STRUPROPS.
Qed.

Lemma wf_cc_ctrl_empty (WF : wf) : ctrlc ≡ ∅₂.
Proof using.
  apply WF.
Qed.

Lemma wf_cc_addr_empty (WF : wf) : addrc ≡ ∅₂.
Proof using.
  apply WF.
Qed.

Lemma wf_cc_data_empty (WF : wf) : datac ≡ ∅₂.
Proof using.
  apply WF.
Qed.

Lemma wf_g_init (WF : wf) : EC ∩₁ is_init ⊆₁ E.
Proof using.
  apply WF.
Qed.

Lemma wf_gc_acts (WF : wf) : (tid ↓₁ eq tid_init) ∩₁ EC ⊆₁ is_init.
Proof using.
  apply WF.
Qed.

Lemma wf_ereq (WF : wf) : exec_restr_eq G GC cmt.
Proof using.
  apply WF.
Qed.

Lemma wf_rfc (WF : wf) : rf_complete (restrict GC cmt).
Proof using.
  apply WF.
Qed.

Lemma wf_sub_rfD (WF : wf) : E ∩₁ R ⊆₁ codom_rel rf ∪₁ cmt.
Proof using.
  apply WF.
Qed.

Lemma wf_fin_threads (WF : wf) : fin_threads GC.
Proof using.
  apply WF.
Qed.

Lemma wf_g_cont (WF : wf) : contigious_actids G.
Proof using.
  apply WF.
Qed.

Lemma wf_gc_cont (WF : wf) : contigious_actids GC.
Proof using.
  apply WF.
Qed.

End Wf.

Section AddEvent.

Variable traces : thread_id -> trace label -> Prop.
Variable sc sc' : relation actid.
Variable X X' : t.
Variable e : actid.
Variable l : label.

Notation "'G''" := (G X').
Notation "'G'" := (G X).

Notation "'E''" := (acts_set G').
Notation "'threads_set''" := (threads_set G').
Notation "'lab''" := (lab G').
Notation "'sb''" := (sb G').
Notation "'rf''" := (rf G').
Notation "'co''" := (co G').
Notation "'rmw''" := (rmw G').
Notation "'data''" := (data G').
Notation "'addr''" := (addr G').
Notation "'ctrl''" := (ctrl G').
Notation "'rmw_dep''" := (rmw_dep G').
Notation "'W''" := (is_w lab').
Notation "'R''" := (is_r lab').
Notation "'same_loc''" := (same_loc lab').

Notation "'E'" := (acts_set G).
Notation "'threads_set'" := (threads_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).
Notation "'W'" := (is_w lab).
Notation "'R'" := (is_r lab).
Notation "'same_loc'" := (same_loc lab).

Definition new_event_correct e : Prop :=
  match thread_trace G (tid e) with
  | trace_inf _ => False
  | trace_fin l =>
    exists tr, traces (tid e) tr /\ trace_prefix (trace_fin (l ++ [lab' e])) tr
  end.

Definition sb_delta : relation actid :=
  (E ∩₁ (is_init ∪₁ same_tid e)) × eq e.

Definition rf_delta_R w : relation actid :=
  match w with
  | Some w => singl_rel w e ∩ (E ∩₁ W) × R
  | _ => ∅₂
  end.

Definition rf_delta_W R1 : relation actid :=
  eq e × R1 ∩ W' × (E' ∩₁ R).

Definition co_delta W1 W2 : relation actid :=
  eq e × (E ∩₁ W1 ∩₁ same_loc e) ∪
  (E ∩₁ W2 ∩₁ same_loc e) × eq e.

Definition rmw_delta r : relation actid :=
  match r with
  | Some r => (R ∩₁ eq r) × (W ∩₁ eq e)
  | _ => ∅₂
  end.

Record add_event_gen r R1 w W1 W2 : Prop := {
  add_event_new : ~E e;
  add_event_ninit : ~is_init e;
  add_event_acts : E' ≡₁ E ∪₁ eq e;
  add_event_threads : threads_set' ≡₁ threads_set;
  add_event_lab : lab' = upd lab e l;
  add_event_rf : rf' ≡ rf ∪ rf_delta_R w ∪ rf_delta_W R1;
  add_event_co : co' ≡ co ∪ co_delta W1 W2;
  add_event_rmw : rmw' ≡ rmw ∪ rmw_delta r;
  add_event_data : data' ≡ data;
  add_event_addr : addr' ≡ addr;
  add_event_ctrl : ctrl' ≡ ctrl;
  add_event_rmw_dep : rmw_dep' ≡ rmw_dep;
  add_event_sb : sb' ≡ sb ∪ sb_delta;
  add_event_trace : new_event_correct e;
}.

Definition add_event :=
  exists r R1 w W1 W2, add_event_gen r R1 w W1 W2.

End AddEvent.

#[global]
Hint Unfold sb_delta rf_delta_R rf_delta_W co_delta rmw_delta : unfolderDb.

Section GuidedStep.

Variable traces : thread_id -> trace label -> Prop.
Variable cmt : actid -> Prop.
Variable XC X1 X2 : t.
Variable e : actid.
Variable l : label.

Record guided_step_gen e : Prop := {
  gsg_add_step : add_event traces X1 X2 e l;
  gsg_wf : wf X2 XC cmt;
}.

Definition guided_step :=
  exists e, guided_step_gen e.

End GuidedStep.

Global Hint Unfold new_event_correct guided_step : unfolderDb.

Section ExecuteStep.

Variable traces : thread_id -> trace label -> Prop.
Variables X X' : t.

Notation "'sc''" := (sc X').
Notation "'G''" := (G X').

Record exec_inst e l := {
  exec_add_event : add_event traces X X' e l;
  exec_rfc : rf_complete G';
  exec_new_cons : is_cons G' sc';
}.

End ExecuteStep.

Section ExecRexec.

Variables G G' : execution.
Variables sc : relation actid.
Variable traces : thread_id -> trace label -> Prop.
Variable dtrmt cmt : actid -> Prop.

Notation "'E''" := (acts_set G').
Notation "'E'" := (acts_set G).
Notation "'W'" := (is_w (lab G)).
Notation "'R'" := (is_r (lab G)).
Notation "'lab''" := (lab G').
Notation "'lab'" := (lab G).
Notation "'hb'" := (hb G).
Notation "'rf''" := (rf G').
Notation "'sb''" := (sb G').
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).

Record stable_uncmt_reads_gen thrdle : Prop :=
  { surg_init_min : wmin_elt thrdle tid_init;
    surg_init_least : least_elt thrdle tid_init;
    surg_order : acyclic thrdle;
    surg_uncmt : (rf' ⨾ ⦗E' \₁ cmt⦘) ∩ compl_rel same_tid ⊆ tid ↓ thrdle; }.

Lemma surg_sb_closed thrdle
    (STABLE_UNCMT : stable_uncmt_reads_gen thrdle) :
  sb^? ⨾ tid ↓ thrdle ⨾ sb^? ⊆ tid ↓ thrdle.
Proof.
  by destruct STABLE_UNCMT; apply thrdle_sb_closed.
Qed.

Record correct_embeding f : Prop :=
{ reexec_embd_inj : inj_dom cmt f;
  reexec_embd_dom : cmt ⊆₁ E';
  reexec_embd_tid : forall e (CMT : cmt e), tid (f e) = tid e;
  reexec_embd_lab : forall e (CMT : cmt e), lab' (f e) = lab e;
  reexec_embd_sb : f ↑ restr_rel cmt sb' ⊆ sb;
  reexec_embd_rf : f ↑ restr_rel cmt rf' ⊆ rf; }.

Definition reexec_start := Build_execution
  (restrict G dtrmt).(acts_set)
	(restrict G dtrmt).(threads_set)
  G'.(lab)
  (restrict G dtrmt).(rmw)
  (restrict G dtrmt).(data)
  (restrict G dtrmt).(addr)
  (restrict G dtrmt).(ctrl)
  (restrict G dtrmt).(rmw_dep)
  (restrict G dtrmt).(rf)
  (restrict G dtrmt).(co).

Record reexec_gen f thrdle : Prop :=
{ (* Correct start *)
  newlab_correct : forall e (DTRMT : dtrmt e), lab' e = lab e;
  dtrmt_cmt : dtrmt ⊆₁ cmt;
  dtrmt_in_G : dtrmt ⊆₁ E;
  reexec_sur : stable_uncmt_reads_gen thrdle;
  (* Correct embedding *)
  reexec_embd_corr : correct_embeding f;
  (* Reproducable steps *)
  reexec_start_wf : wf (Build_t sc reexec_start G' cmt);
  reexec_steps : (cfg_add_event_uninformative traces)＊
    (Build_t sc reexec_start G' cmt)
    (Build_t sc G'           G' cmt);
  rexec_final_cons : is_cons G' sc; }.

Definition reexec : Prop := exists f thrdle, reexec_gen f thrdle.

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

Lemma wf_gc_fin_exec : fin_exec GC.
Proof using WF.
  red.
  set (T := threads_set GC \₁ eq tid_init).
  arewrite (EC \₁ is_init ≡₁ ⋃₁t ∈ T, EC ∩₁ (fun x => t = tid x)).
  { subst T. split; intros x HSET.
    { destruct HSET as [XE XINI]. unfolder. exists (tid x).
      splits; ins; try now apply WF.
      intro F. apply XINI. apply WF.
      unfolder. now split. }
    unfolder in HSET. desf.
    split; ins. intro F. apply HSET2.
    destruct x; ins. }
  apply set_finite_bunion; subst T.
  { eapply set_finite_mori; try now apply WF.
    red. basic_solver. }
  intros t (THR & NINIT).
  assert (NINIT' : t <> tid_init); eauto.
  destruct (wf_gc_cont WF NINIT') as [N EQ].
  rewrite EQ. apply set_size_finite.
  eexists. apply thread_seq_set_size.
Qed.

Lemma wf_g_fin_exec : fin_exec G.
Proof using WF.
  red. eapply set_finite_mori with (x := EC \₁ is_init).
  { red. apply set_minus_mori; [apply WF | basic_solver]. }
  apply wf_gc_fin_exec.
Qed.

Lemma g_acts_fin_enum :
  exists l,
    << NODUP : NoDup l >> /\
    << ELEMS : E \₁ is_init ≡₁ fun x => In x l >>.
Proof using WF.
  set (HFIN := wf_g_fin_exec).
  apply set_finiteE in HFIN.
  desf.
Qed.

Lemma wf_g : Wf G.
Proof using WF.
  eapply sub_WF; try now apply WF.
  rewrite set_interC; apply WF.
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

Lemma wf_set_sz thr N
    (NOT_INIT : thr <> tid_init)
    (SZ_EQ : set_size (E ∩₁ (fun e => thr = tid e)) = NOnum N) :
  E ∩₁ (fun e => thr = tid e) ≡₁ thread_seq_set thr N.
Proof using WF.
  set (HEQ := wf_g_cont WF NOT_INIT). desf.
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
  set (CONT := wf_g_cont WF NOT_INIT). desf.
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
Notation "'sb''" := (sb G').

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
  split; try apply STRUCT.
  now right.
Qed.

(* Lemma new_event_max_sb e
    (WF : wf X)
    (ADD_STEP : cfg_add_event traces X X' e) :
  max_elt sb' e.
Proof using.
  unfolder. intros e' SB.
  red in ADD_STEP. desf.
  unfold sb in SB; unfolder in SB; desf.
  apply ADD_STEP.(e_new) in SB1.
  unfolder in SB1; desf.
  { apply ADD_STEP.(e_notin), ext_sb_dense with (e2 := e'); ins.
    { apply WF. }
    intro F. apply ADD_STEP.(e_notinit).
    eapply wf_g_acts; [apply ADD_STEP.(wf_new_conf) |].
    unfolder; split; ins. }
  eapply ext_sb_irr; eauto.
Qed. *)

Lemma same_lab e
  (WF : wf X)
  (ADD_STEP : cfg_add_event traces X X' e) :
  lab' = lab.
Proof using.
  red in ADD_STEP. desf.
  erewrite (sub_lab (wf_g_sub_gc WF)), (sub_lab (wf_g_sub_gc WF_NEW)).
  f_equal. apply STRUCT.
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
  all: try now apply STRUCT.
  all: eauto using wf_g_cont.
  all: try now rewrite updI.
  eapply (wf_actid_tid WF_NEW); try apply STRUCT.
  now right.
Qed.

Lemma add_step_new_event_correct e
    (ADD_STEP : cfg_add_event traces X X' e) :
  exists tr, traces (tid e) tr /\
    trace_prefix (trace_app (thread_trace G (tid e)) (trace_fin [lab' e])) tr.
Proof using.
  red in ADD_STEP. desf.
  generalize TRACE.
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
  unfold thread_actid_trace.
  rewrite (caes_e_new STRUCT), set_inter_union_l.
  arewrite (eq e ∩₁ (fun x => thr = tid x) ≡₁ ∅); [basic_solver |].
  now rewrite set_union_empty_r.
Qed.

End WCoreStepProps.

End WCore.
