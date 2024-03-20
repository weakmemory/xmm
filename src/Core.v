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
  Build_execution (acts_set G ∩₁ is_init) (threads_set G) (lab G) ∅₂ ∅₂ ∅₂ ∅₂ ∅₂ ∅₂ ∅₂.

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

Definition unwrap_g2gc x :=
  match (f x) with
  | Some y => lab y
  | None => Afence Orlx
  end.

Record wf : Prop := {
  c_ctrl_empty : ctrl ≡ ∅₂;
  c_addr_empty : addr ≡ ∅₂;
  c_data_empty : data ≡ ∅₂;

  wf_g : Wf G;
  wf_g_acts : ~(tid ↑₁ (E ∩₁ set_compl is_init)) tid_init;
  wf_gc : Wf GC;
  wf_gc_acts : ~(tid ↑₁ (EC ∩₁ set_compl is_init)) tid_init;

  f_dom : is_some ∘ f ⊆₁ EC;
  f_codom : Some ↓₁ (f ↑₁ EC) ⊆₁ E;
  f_inj : inj_dom (EC ∩₁ (is_some ∘ f)) f;
  f_c_some : C ⊆₁ is_some ∘ f;

  f_sb : Some ↓ (f ↑ restr_rel C sbc) ⊆ sb;
  f_rf : Some ↓ (f ↑ restr_rel C rfc) ⊆ rf;
  f_rfD : E ∩₁ R ⊆₁ codom_rel rf ∪₁ (Some ↓₁ (f ↑₁ C));

  f_tid : restr_rel EC (fun x y => f x = Some y) ⊆ same_tid;
  f_u2v : same_lab_u2v_dom (EC ∩₁ (is_some ∘ f)) unwrap_g2gc labc;
  f_same_v : forall c (IN : C c), val unwrap_g2gc c = val labc c;

  actid_cont : forall thr (NOT_INIT : thr <> tid_init),
    exists N, E ∩₁ (fun x => thr = tid x) ≡₁ thread_seq_set thr N;
}.

End CoreDefs.

Global Hint Resolve wf_g wf_gc actid_cont : xmm.

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
    exists tr, traces (tid e) tr /\ trace_prefix (trace_fin (l ++ [lab' e])) tr
  end.

Record cfg_add_event_gen e l r w W1 W2 c :=
{ e_notin : ~(E e);
  e_notinit : ~ is_init e;
  e_new : E' ≡₁ E ∪₁ (eq e);
  e_correct : new_event_correct e;
  lab_new : lab' = upd lab e l;
  cmt_graph_same : GC' = GC;
  thread_set_same : threads_set G' ≡₁ threads_set G;

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

Definition cfg_add_step_uninformative := exists e l, cfg_add_event e l.

End CfgAddEventStep.

Global Hint Unfold new_event_correct cfg_add_event
                  cfg_add_step_uninformative : unfolderDb.

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

Record reexec_gen
  (G'' : execution)
  (f f' : actid -> option actid)
  (C : actid -> Prop) : Prop :=
{ rf_sub_re : rfre ⊆ re;
  rf_sub_f : rfre ⊆ Some ↓ (f ↑ rf');
  d_wre_sub_f : D ∪₁ Wre ⊆₁ Some ↓₁ (f ↑₁ C);

  cfg_wf : wf (Build_t G G' C f);
  int_G_D : restr_exec D G G'';
  cfg_steps : (cfg_add_step_uninformative traces)＊
    (Build_t G'' G' C (f_restr D f))
    (Build_t G'  G' C f');

  new_g_cons : is_cons G';
}.

Definition reexec : Prop := exists G'' f f' C, reexec_gen G'' f f' C.

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

Lemma C_sub_EC :
  C ⊆₁ EC.
Proof using WF.
  transitivity (is_some ∘ g2gc); apply WF.
Qed.

Lemma wf_g2gc_unwrap e c
    (MAPPED : g2gc c = Some e) :
  unwrap_g2gc X c = lab e.
Proof using.
  unfold unwrap_g2gc.
  now rewrite MAPPED.
Qed.

Lemma wf_C_eq_lab e
    (INC : C e) :
  unwrap_g2gc X e = labc e.
Proof using WF.
  apply same_label_u2v_val; try now apply WF.
  apply f_u2v; auto.
  split; eauto using C_sub_EC.
  now apply f_c_some.
Qed.

Lemma wf_eq_labs e c
    (INC : C c)
    (MAPPED : g2gc c = Some e) :
  labc c = lab e.
Proof using WF.
  erewrite <- wf_g2gc_unwrap, wf_C_eq_lab; eauto.
Qed.

Lemma wf_iff_read :
  (EC ∩₁ (is_some ∘ g2gc)) ∩₁ is_r (unwrap_g2gc X) ≡₁
  (EC ∩₁ (is_some ∘ g2gc)) ∩₁ is_r labc.
Proof using WF.
  apply same_lab_u2v_dom_is_r, WF.
Qed.

Lemma wf_iff_write :
  (EC ∩₁ (is_some ∘ g2gc)) ∩₁ is_w (unwrap_g2gc X) ≡₁
  (EC ∩₁ (is_some ∘ g2gc)) ∩₁ is_w labc.
Proof using WF.
  apply same_lab_u2v_dom_is_w, WF.
Qed.

Lemma wf_iff_fence :
  (EC ∩₁ (is_some ∘ g2gc)) ∩₁ is_f (unwrap_g2gc X) ≡₁
  (EC ∩₁ (is_some ∘ g2gc)) ∩₁ is_f labc.
Proof using WF.
  apply same_lab_u2v_dom_is_f, WF.
Qed.

Lemma wf_eq_loc :
  restr_rel (EC ∩₁ (is_some ∘ g2gc)) (same_loc (unwrap_g2gc X)) ≡
  restr_rel (EC ∩₁ (is_some ∘ g2gc)) (same_loc labc).
Proof using WF.
  apply same_lab_u2v_dom_same_loc, WF.
Qed.

Lemma wf_actid_tid e
    (NOT_INIT : (E ∩₁ set_compl is_init) e) :
    tid e <> tid_init.
Proof using WF.
  intro F.
  eapply wf_g_acts; eauto.
  unfolder. exists e.
  split; [apply NOT_INIT | exact F].
Qed.

Lemma in_restr_acts e :
  E e <-> (E ∩₁ same_tid e) e.
Proof using.
  unfolder; split; ins; desf.
Qed.

Lemma sb_dense x y
    (XNOT_INIT : tid x <> tid_init)
    (IN : E y)
    (SB : ext_sb x y) :
  E x.
Proof using WF.
  assert (YNOT_INIT : ~is_init y).
  { apply ext_sb_to_non_init in SB.
    unfolder in SB; desf. }
  assert (Y_TID : tid y = tid x).
  { set (COND := ext_sb_tid_init x y SB).
    destruct COND; auto. destruct x; ins. }
  destruct x as [lx | tidx ix], y as [ly | tidy iy]; ins.
  set (ACTS := actid_cont WF XNOT_INIT). desf.
  rewrite in_restr_acts in *. unfold same_tid in *. ins.
  apply ACTS; apply ACTS in IN.
  unfolder; unfolder in IN; desf.
  exists ix; split; auto; lia.
Qed.


Lemma wf_set_sz thr N
    (NOT_INIT : thr <> tid_init)
    (SZ_EQ : set_size (E ∩₁ (fun e => thr = tid e)) = NOnum N) :
  E ∩₁ (fun e => thr = tid e) ≡₁ thread_seq_set thr N.
Proof using WF.
  set (HEQ := actid_cont WF NOT_INIT). desf.
  rewrite HEQ in *.
  now apply thread_seq_N_eq_set_size.
Qed.

Lemma wf_set_sz_helper e N
    (NOT_INIT : (E ∩₁ set_compl is_init) e)
    (SZ_EQ : set_size (E ∩₁ same_tid e) = NOnum N) :
  E ∩₁ same_tid e ≡₁ thread_seq_set (tid e) N.
Proof using WF.
  apply wf_set_sz with (thr := tid e); auto.
  now apply wf_actid_tid.
Qed.

End WCoreWfProps.

Global Hint Resolve wf_actid_tid wf_set_sz wf_set_sz_helper :
  xmm.

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

Lemma add_step_event_set e l
    (ADD_STEP : cfg_add_event traces X X' e l) :
    (E' ∩₁ set_compl is_init) e.
Proof using.
  red in ADD_STEP. desf.
  split; try apply ADD_STEP.
  now right.
Qed.

Lemma new_conf_wf e l
    (ADD_STEP : cfg_add_event traces X X' e l) :
    wf X'.
Proof using.
  red in ADD_STEP. desf.
  apply ADD_STEP.
Qed.

Lemma add_step_event_not_init_tid e l
    (ADD_STEP : cfg_add_event traces X X' e l) :
    tid e <> tid_init.
Proof using.
  eauto using wf_actid_tid, new_conf_wf, add_step_event_set.
Qed.

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
  unfold same_tid. rewrite wf_set_sz with (thr := (tid e)).
  all: eauto using add_step_acts_set_sz, add_step_event_set,
          add_step_event_not_init_tid, new_conf_wf.
Qed.

Lemma add_step_actid e l N
    (WF : wf X)
    (ADD_STEP : cfg_add_event traces X X' e l)
    (SZ_EQ : set_size (E ∩₁ same_tid e) = NOnum N):
  E' ∩₁ same_tid e ≡₁ E ∩₁ same_tid e ∪₁ eq (ThreadEvent (tid e) N).
Proof using.
  erewrite add_step_new_acts, wf_set_sz with (thr := (tid e)).
  all: eauto using add_step_event_set, add_step_event_not_init_tid.
  now rewrite PeanoNat.Nat.add_1_r, thread_set_S.
Qed.

Lemma add_step_actid_value e l N
    (WF : wf X)
    (ADD_STEP : cfg_add_event traces X X' e l)
    (SZ_EQ : set_size (E ∩₁ same_tid e) = NOnum N):
  e = ThreadEvent (tid e) N.
Proof using.
  assert (HIN : (E' ∩₁ same_tid e) e).
  { split; [apply (add_step_event_set ADD_STEP) | easy]. }
  assert (NOTIN : ~E e).
  { red in ADD_STEP; desf. apply ADD_STEP. }
  eapply add_step_actid in HIN; eauto.
  unfolder in HIN; desf.
Qed.

Lemma add_step_trace_eq e l N
    (WF : wf X)
    (ADD_STEP : cfg_add_event traces X X' e l)
    (SZ_EQ : set_size (E ∩₁ same_tid e) = NOnum N):
  thread_trace G' (tid e) =
    trace_app (thread_trace G (tid e)) (trace_fin [lab' e]).
Proof using.
  assert (HEQ_LAB : lab' = upd lab e l).
  { red in ADD_STEP. desf. apply ADD_STEP. }
  unfold thread_trace. erewrite !thread_actid_trace_form.
  all: eauto using add_step_new_acts, wf_set_sz,
        add_step_event_not_init_tid.
  ins. f_equal.
  rewrite PeanoNat.Nat.add_1_r, seqS,
          PeanoNat.Nat.add_0_l, !map_app.
  ins.
  erewrite <- add_step_actid_value with (l := l),
          app_inv_tail_iff, HEQ_LAB, map_upd_irr; eauto.
  rewrite (add_step_actid_value WF ADD_STEP SZ_EQ).
  now apply thread_seq_helper_inv.
Qed.

Lemma set_union_inter_r_notinter:
  forall [A : Type] (s s' s'' : A -> Prop) (HYP : s' ∩₁ s'' ≡₁ ∅),
  (s ∪₁ s') ∩₁ s'' ≡₁ s ∩₁ s''.
Proof using.
  ins. rewrite set_inter_union_l.
  rewrite HYP. basic_solver.
Qed.

(* NOTE: map_upd_irr *)
Lemma map_upd_not_applicable:
  forall (l : list actid) (x : actid) (y : label) (HYP : ~ In x l),
  map (upd lab x y) l = map lab l.
Proof using.
  ins. induction l; ins.
  apply not_or_and in HYP. desf.
  apply IHl in HYP0. rewrite HYP0. f_equal.
  unfold upd. desf.
Qed.

Lemma add_step_new_event_correct e l
    (ADD_STEP : cfg_add_event traces X X' e l) :
  exists tr, traces (tid e) tr /\
    trace_prefix (trace_app (thread_trace G (tid e)) (trace_fin [lab' e])) tr.
Proof using.
  red in ADD_STEP. desf.
  generalize (e_correct ADD_STEP).
  unfold new_event_correct. desf.
Qed.

Lemma add_step_trace_coh e l
    (WF : wf X)
    (ADD_STEP : cfg_add_event traces X X' e l)
    (G_COH : trace_coherent traces G) :
  trace_coherent traces G'.
Proof using.
  red. ins.
  destruct (classic (thr = (tid e))) as [HEQ_TIDE|HEQ_TIDE].
  { subst.
    assert (HEQ : exists N, E ∩₁ same_tid e ≡₁ thread_seq_set (tid e) N).
    { now apply WF. }
    desf.
    erewrite add_step_trace_eq; eauto using add_step_new_event_correct.
    erewrite set_size_equiv, thread_seq_set_size; eauto. }
  set (HCORR := G_COH thr NOT_INIT). desf.
  exists tr; split; auto.
  assert (NO_CHANGE : thread_trace G' thr = thread_trace G thr).
    { unfold thread_trace. unfold cfg_add_event in ADD_STEP. desf.
      destruct ADD_STEP. rewrite lab_new0.
      unfold thread_actid_trace. rewrite e_new0.
      destruct WF. apply actid_cont0 in NOT_INIT.
      destruct NOT_INIT as [N N_EQ].
      rewrite set_union_inter_r_notinter.
      rewrite N_EQ. rewrite thread_seq_set_size.
      { unfold trace_map. assert (HYP: ~ In e (map (ThreadEvent thr) (List.seq 0 N))).
        { intro F. apply in_map_iff in F. desf. }
        rewrite map_upd_not_applicable. all: eauto. }
      basic_solver. }
    now rewrite NO_CHANGE.
Qed.

End WCoreStepProps.

Global Hint Resolve new_conf_wf add_step_event_not_init_tid add_step_trace_coh :
  xmm.

End WCore.
