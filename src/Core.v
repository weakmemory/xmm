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
  Actual propeties that are important for
  the model to function.
*)
Record wf := {
  wf_g : Wf G;
  wf_ereq : exec_restr_eq G GC cmt;
  wf_rfc : rf_complete (restrict GC cmt);
  wf_sub_rfD : E ∩₁ R ⊆₁ codom_rel rf ∪₁ cmt;
  wf_sc : wf_sc G sc;
}.

End Wf.

Section AddEvent.

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
}.

Definition add_event :=
  exists r R1 w W1 W2, add_event_gen r R1 w W1 W2.

End AddEvent.

#[global]
Hint Unfold sb_delta rf_delta_R rf_delta_W co_delta rmw_delta : unfolderDb.

Section GuidedStep.

Variable cmt : actid -> Prop.
Variable XC X1 X2 : t.

Record guided_step_gen e l : Prop := {
  gsg_add_step : add_event X1 X2 e l;
  gsg_wf : wf X2 XC cmt;
}.

Definition guided_step :=
  exists e l, guided_step_gen e l.

End GuidedStep.

Section ExecuteStep.

Variables X X' : t.

Notation "'sc''" := (sc X').
Notation "'G''" := (G X').

Record exec_inst e l := {
  exec_add_event : add_event X X' e l;
  exec_rfc : rf_complete G';
  exec_new_cons : is_cons G' sc';
}.

End ExecuteStep.

Section ReexecStep.

Variables X X' : t.
Variable cmt : actid -> Prop.

Notation "'G''" := (G X').
Notation "'lab''" := (lab G').
Notation "'E''" := (acts_set G').
Notation "'rf''" := (rf G').
Notation "'sb''" := (sb G').
Notation "'rpo''" := (rpo G').
Notation "'rmw''" := (rmw G').
Notation "'co''" := (co G').

Notation "'G'" := (G X).
Notation "'lab'" := (lab G).
Notation "'E'" := (acts_set G).
Notation "'rf'" := (rf G).
Notation "'sb'" := (sb G).
Notation "'rpo'" := (rpo G).
Notation "'rmw'" := (rmw G).
Notation "'co'" := (co G).
Notation "'sc'" := (sc X).

Definition X_start dtrmt :=
  Build_t (restrict G dtrmt) (restr_rel dtrmt sc).

Record stable_uncmt_reads_gen thrdle : Prop :=
  { surg_order : strict_partial_order thrdle;
    surg_uncmt : rf' ⨾ ⦗E' \₁ cmt⦘ ⊆ sb' ∪ tid ↓ thrdle; }.

Record commit_embedded f : Prop :=
{ reexec_embd_inj : inj_dom cmt f;
  reexec_embd_tid : forall e (CMT : cmt e), tid (f e) = tid e;
  reexec_embd_lab : forall e (CMT : cmt e), lab' (f e) = lab e;
  reexec_embd_rpo : f ↑ restr_rel cmt rpo' ⊆ rpo;
  reexec_embd_rf : f ↑ restr_rel cmt rf' ⊆ rf;
  reexec_embd_co : f ↑ restr_rel cmt co' ⊆ co;
  reexec_embd_rmw : f ↑ restr_rel cmt rmw' ⊆ rmw; }.

Record reexec_gen f thrdle dtrmt : Prop :=
{ (* Correct start *)
  dtrmt_cmt : dtrmt ⊆₁ f ↑₁ cmt;
  reexec_embd_dom : cmt ⊆₁ E';
  reexec_sur : stable_uncmt_reads_gen thrdle;
  (* Correct embedding *)
  reexec_embd_corr : commit_embedded f;
  (* Reproducable steps *)
  reexec_start_wf : wf (X_start dtrmt) X' cmt;
  rexec_final_cons : is_cons G' sc;
  reexec_steps : (guided_step cmt X')＊ (X_start dtrmt) X'; }.

Definition reexec : Prop :=
  exists f thrdle dtrmt, reexec_gen f thrdle dtrmt.

End ReexecStep.

End WCore.