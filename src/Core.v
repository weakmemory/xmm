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

Definition f_restr (D : actid -> Prop) (f : actid -> option actid) : actid -> option actid :=
  (restr_fun (Some ↓₁ (f ↑₁ D)) f (fun x => None)).

Record restr_exec (D : actid -> Prop) (G G'' : execution) : Prop :=
  { restr_sub_G : sub_execution G G'' ∅₂ ∅₂;
    restr_acts_D : acts_set G'' ≡₁ D;
    restr_init_sub : acts_set G'' ∩₁ is_init ≡₁
                     acts_set G ∩₁ is_init;
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
  g2gc : actid -> option actid;
}.

Definition init_exec G : execution :=
  Build_execution (acts_set G ∩₁ (fun x => is_init x)) (threads_set G) (lab G) ∅₂ ∅₂ ∅₂ ∅₂ ∅₂ ∅₂ ∅₂.

Definition empty_cfg G : t :=
  Build_t G (init_exec G) ∅ (fun x => None).

#[global]
Hint Unfold init_exec empty_cfg f_restr : unfolderDb.

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
Notation "'ctrl'" := (ctrl G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'GC'" := (GC X).
Notation "'C'" := (cmt X).
Notation "'f'" := (g2gc X).
Notation "'labc'" := (lab GC).
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
  c_subset : C ⊆₁ acts_set GC;
  c_ctrl_empty : ctrl ≡ ∅₂;
  c_addr_empty : addr ≡ ∅₂;
  c_data_empty : data ≡ ∅₂;

  wf_g : Wf G;
  wf_gc : Wf GC;
  f_dom : is_some ∘ f ⊆₁ EC;
  f_codom : Some ↓₁ (f ↑₁ EC) ⊆₁ E;
  f_inj : inj_dom (EC ∩₁ (is_some ∘ f)) f;

  f_tid : forall c (IN : C c), option_map tid (f c) = Some (tid c);
  f_lab : forall c (IN : C c), option_map lab (f c) = Some (labc c);
  f_sb : Some ↓ (f ↑ (⦗C⦘ ⨾ sbc ⨾ ⦗C⦘)) ⊆ sb;
  f_rf : Some ↓ (f ↑ (⦗C⦘ ⨾ rfc ⨾ ⦗C⦘)) ⊆ rf;
  f_rfD : E ∩₁ R ⊆₁ codom_rel rf ∪₁ (Some ↓₁ (f ↑₁ C));

  f_loc : forall c (IN : EC c), option_map (loc lab) (f c) = Some (loc labc c);
  f_mod : forall c (IN : EC c), option_map (mod lab) (f c) = Some (mod labc c);
  f_read : forall c (IN : EC c), option_map (is_r lab) (f c) = Some (is_r labc c);
  f_write : forall c (IN : EC c), option_map (is_w lab) (f c) = Some (is_w labc c);

  actid_cont : forall thr,
    exists N, E ∩₁ (fun x => thr = tid x) ≡₁ thread_seq_set thr N;
}.

End CoreDefs.

Section DeltaDefs.

Variable (G : execution).
Variable (e : actid).
Notation "'W'" := (is_w (lab G)).
Notation "'R'" := (is_r (lab G)).
Notation "'W_ex'" := (W_ex G).

(* We do not need sb_delta as `sb` has an exact formula *)
(* Definition sb_delta : relation actid :=
  (E ∩₁ (fun x => tid x = tid e)) × eq e. *)

Definition rf_delta_R (w : option actid) : relation actid :=
  match w with
  | Some w => eq w × eq e ∩ W × R
  | _ => ∅₂
  end.

Definition rf_delta_W (GC : execution) (f' : actid -> option actid) : relation actid :=
  let Wc := f' ↓₁ eq (Some e) in
  let Rc := codom_rel (⦗Wc⦘ ⨾ rf GC) in
  eq e × (Some ↓₁ (f' ↑₁ Rc)).

Definition co_delta (W1 W2 : actid -> Prop) : relation actid :=
  if W e then eq e × W1 ∪ eq e × W2
  else ∅₂.

Definition rmw_delta (r : option actid) : relation actid :=
  (R ∩₁ eq_opt r) × (W_ex ∩₁ eq e).

End DeltaDefs.

#[global]
Hint Unfold rf_delta_R rf_delta_W co_delta rmw_delta : unfolderDb.

Section CfgAddEventStep.

Variable traces : thread_id -> trace label -> Prop.

Variable X X' : t.
Notation "'G''" := (G X').
Notation "'GC''" := (GC X').
Notation "'C''" := (cmt X').
Notation "'f''" := (g2gc X').
Notation "'E''" := (acts_set G').
Notation "'lab''" := (lab G').

Notation "'G'" := (G X).
Notation "'GC'" := (GC X).
Notation "'C'" := (cmt X).
Notation "'f'" := (g2gc X).
Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).

Definition new_event_correct e : Prop :=
  match thread_trace G (tid e) with
  | trace_inf _ => False
  | trace_fin l => 
    exists tr, traces (tid e) tr /\ 
      trace_prefix (trace_fin (l ++ [lab e])
    ) tr
  end.

Record cfg_add_event_gen e l r w W1 W2 c :=
{ e_notin : ~(E e);
  e_notinit : ~ is_init e; 
  e_new : E' ≡₁ E ∪₁ (eq e);
  e_correct : new_event_correct e;
  lab_new : lab' = upd lab e l;
  cmt_graph_same : GC' = GC;

  (* Skipping condition for sb *)
  rf_new : rf G' ≡ rf G ∪ rf_delta_R G e w ∪ rf_delta_W e GC f';
  co_new : co G' ≡ co G ∪ co_delta G e W1 W2;
  rmw_new : rmw G' ≡ rmw G ∪ rmw_delta G e r;

  f_new : match c with
          | None => True
          | Some c => f' = upd f e (Some c)
          end;
  wf_new_conf : wf X';
}.

Definition cfg_add_event (e : actid) (l : label) :=
  exists r w W1 W2 c, cfg_add_event_gen e l r w W1 W2 c.

End CfgAddEventStep.

Section ExecAdd.

Variables G G' : execution.
Variable traces : thread_id -> trace label -> Prop.

Record exec_inst e l := {
  cfg_step : cfg_add_event traces (empty_cfg G) (empty_cfg G') e l;
  next_cons : is_cons G';
}.

End ExecAdd.

Section ExecRexec.

Variables G G' : execution.
Variable rfre : relation actid.
Variable traces : thread_id -> trace label -> Prop.

Notation "'E'" := (acts_set G).
Notation "'W'" := (is_w (lab G)).
Notation "'R'" := (is_r (lab G)).
Notation "'race'" := (race G).
Notation "'lab'" := (lab G).
Notation "'same_loc'" := (same_loc lab).
Notation "'hb'" := (hb G).
Notation "'hbloc'" := (same_loc ∩ hb).
Notation "'re'" := (⦗W⦘ ⨾ (race ∪ hbloc) ⨾ ⦗R⦘).
Notation "'rf''" := (rf G').
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).

Notation "'Rre'" := (codom_rel rfre).
Notation "'Wre'" := (dom_rel rfre).
Notation "'D'" := (E \₁ codom_rel (⦗Rre⦘ ⨾ (sb ∪ rf)＊)).

Definition cfg_add_step_uninformative X X' :=
  exists e l, cfg_add_event traces X X' e l.

Record reexec_gen
  (G'' : execution)
  (f f' : actid -> option actid)
  (C : actid -> Prop) : Prop :=
{ rf_sub_re : rfre ⊆ re;
  rf_sub_f : rfre ⊆ Some ↓ (f ↑ rf');
  d_wre_sub_f : D ∪₁ Wre ⊆₁ Some ↓₁ (f ↑₁ C);

  cfg_wf : wf (Build_t G G' C f);
  int_G_D : restr_exec D G G'';
  cfg_steps : cfg_add_step_uninformative＊
    (Build_t G'' G' C (f_restr D f))
    (Build_t G'  G' C f');

  C_correct : forall c (IN_C : C c), is_some (f c);
  new_g_cons : is_cons G';
}.

Definition reexec : Prop := exists G'' f f' C, reexec_gen G'' f f' C.

End ExecRexec.

Section WCoreWfProps.

Variable X : t.
Variable WF : wf X.

Notation "'G'" := (G X).
Notation "'ctrl'" := (ctrl G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'GC'" := (GC X).
Notation "'C'" := (cmt X).
Notation "'g2gc'" := (g2gc X).
Notation "'labc'" := (lab GC).
Notation "'lab'" := (lab G).
Notation "'sbc'" := (sb GC).
Notation "'rfc'" := (rf GC).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'EC'" := (acts_set GC).
Notation "'E'" := (acts_set G).

Lemma wf_iff_read e ec
    (IN : EC ec)
    (MAPPED : g2gc ec = Some e) :
  is_r lab e <-> is_r labc ec.
Proof using WF.
  enough (HEQ : Some (is_r lab e) = Some (is_r labc ec)) by now inversion HEQ.
  change (Some (is_r lab e)) with (option_map (is_r lab) (Some e)).
  rewrite <- MAPPED. now apply WF.
Qed.

Lemma wf_iff_write e ec
    (IN : EC ec)
    (MAPPED : g2gc ec = Some e) :
  is_w lab e <-> is_w labc ec.
Proof using WF.
  enough (HEQ : Some (is_w lab e) = Some (is_w labc ec)) by now inversion HEQ.
  change (Some (is_w lab e)) with (option_map (is_w lab) (Some e)).
  rewrite <- MAPPED. now apply WF.
Qed.

Lemma wf_eq_loc e ec
    (IN : EC ec)
    (MAPPED : g2gc ec = Some e) :
  loc lab e = loc labc ec.
Proof using WF.
  enough (HEQ : Some (loc lab e) = Some (loc labc ec)) by now inversion HEQ.
  change (Some (loc lab e)) with (option_map (loc lab) (Some e)).
  rewrite <- MAPPED. now apply WF.
Qed.

Lemma wf_set_sz e N
    (SZ_EQ : set_size (E ∩₁ same_tid e) = NOnum N) :
  E ∩₁ same_tid e ≡₁ thread_seq_set (tid e) N.
Proof using WF.
  unfold same_tid in *.
  set (HEQ := actid_cont WF (tid e)). desf.
  rewrite HEQ in *.
  now apply thread_seq_N_eq_set_size.
Qed.

End WCoreWfProps.

Section WCoreStepProps.

Variable traces : thread_id -> trace label -> Prop.

Variable X X' : t.
Notation "'G''" := (G X').
Notation "'GC''" := (GC X').
Notation "'C''" := (cmt X').
Notation "'f''" := (g2gc X').
Notation "'E''" := (acts_set G').
Notation "'lab''" := (lab G').

Notation "'G'" := (G X).
Notation "'GC'" := (GC X).
Notation "'C'" := (cmt X).
Notation "'f'" := (g2gc X).
Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).

Lemma add_step_acts_set_sz e l N
    (ADD_STEP : cfg_add_event traces X X' e l)
    (SZ_EQ : set_size (E ∩₁ same_tid e) = NOnum N) :
  set_size (E' ∩₁ same_tid e) = NOnum (N + 1).
Proof using.
  red in ADD_STEP. desf.
  rewrite e_new, set_inter_union_l by eauto.
  arewrite (eq e ∩₁ same_tid e ≡₁ eq e).
  { basic_solver. }
  erewrite set_size_union_disjoint; auto using set_size_single.
  enough (set_disjoint E (eq e)) by basic_solver.
  unfolder; ins; desf.
  now apply ADD_STEP.
Qed.

Lemma add_step_new_acts e l N
    (WF : wf X)
    (ADD_STEP : cfg_add_event traces X X' e l)
    (SZ_EQ : set_size (E ∩₁ same_tid e) = NOnum N):
  E' ∩₁ same_tid e ≡₁ thread_seq_set (tid e) (N + 1).
Proof using.
  rewrite wf_set_sz; eauto using add_step_acts_set_sz.
  red in ADD_STEP; desf. apply ADD_STEP.
Qed.

Lemma add_step_actid e l N
    (WF : wf X)
    (ADD_STEP : cfg_add_event traces X X' e l)
    (SZ_EQ : set_size (E ∩₁ same_tid e) = NOnum N):
  E' ∩₁ same_tid e ≡₁ E ∩₁ same_tid e ∪₁ eq (ThreadEvent (tid e) N).
Proof using.
  erewrite add_step_new_acts, wf_set_sz; eauto.
  now rewrite PeanoNat.Nat.add_1_r, thread_set_S.
Qed.

Lemma add_step_actid_value e l N
    (WF : wf X)
    (ADD_STEP : cfg_add_event traces X X' e l)
    (SZ_EQ : set_size (E ∩₁ same_tid e) = NOnum N):
  e = ThreadEvent (tid e) N.
Proof using.
  admit.
Admitted.

Lemma add_step_trace_eq e l N
    (WF : wf X)
    (ADD_STEP : cfg_add_event traces X X' e l)
    (SZ_EQ : set_size (E ∩₁ same_tid e) = NOnum N):
  thread_trace G' (tid e) =
    trace_app (thread_trace G (tid e)) (trace_fin [lab' e]).
Proof using.
  red in ADD_STEP. desf.
  assert (ADD_STEP' : cfg_add_event traces X X' e l).
  { do 5 econstructor. apply ADD_STEP. }
  unfold thread_trace.
  erewrite !thread_actid_trace_form.
  all: eauto using add_step_new_acts, wf_set_sz.
  erewrite lab_new by eauto.
  rewrite PeanoNat.Nat.add_1_r, seqS; ins.
  f_equal.
  rewrite !map_app; ins.
  erewrite <- add_step_actid_value, upds; eauto.
  f_equal.
  admit.
Admitted.

Lemma add_step_trace_coh e l
    (ADD_STEP : cfg_add_event traces X X' e l)
    (G_COH : trace_coherent traces G) :
  trace_coherent traces G'.
Proof using.
  red in ADD_STEP. desf.
  red. ins.
  set (PREFIX := e_correct ADD_STEP).
  unfold new_event_correct in PREFIX.
  ins.

  { edestruct traceco_wf_acts with (thr:=thr) as [N OLD_ACTS]; eauto.
    destruct (classic (thr = (tid e))); subst; [exists (N + 1) | exists N].
    all: rewrite e_new, set_inter_union_l, OLD_ACTS; eauto.
    { rewrite PeanoNat.Nat.add_1_r, thread_set_S.
      admit. }
    arewrite (eq e ∩₁ (fun x => tid x = thr) ≡₁ ∅); [basic_solver | ].
    now rewrite set_union_empty_r. }
Admitted.

End WCoreStepProps.

End WCore.
