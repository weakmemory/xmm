Require Import Lia Setoid Program.Basics.
Require Import AuxDef.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

From RecordUpdate Require Import RecordSet.
(* Import RecordSetNotations. *)

Import ListNotations.

Set Implicit Arguments.

(* TODO: move *)
Definition edges_to {A} (e : A) := (fun _ _ => True) ⨾ ⦗eq e⦘.
Hint Unfold edges_to : unfolderDb.

#[export] Instance eta_execution : Settable _ :=
  settable! Build_execution
    <acts_set; threads_set; lab; rmw; data; addr; ctrl; rmw_dep; rf; co>
.

(* TODO: move *)
Definition rmw_delta e e' : relation actid :=
  eq e × eq_opt e'.
#[global]
Hint Unfold rmw_delta : unfolderDb.

Inductive cont_label :=
| CInit (tid : thread_id)
| CEvent (e : actid)
.

Section Race.
Variable (G : execution).
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

Definition one (s : actid -> Prop) : relation actid :=
    fun x y => s x \/ s y.

Definition race := restr_rel E (one W ∩ same_loc \ clos_sym hb).

Definition race_mod (o : mode) := race ∩ one (fun e => mode_le (mod e) o).

Definition ppo_alt := (sb ∩ same_loc ∪ bob)⁺.
Definition hb_alt := (ppo_alt ∪ rf)⁺.
End Race.

(* Module Commit.
Definition id := nat.

Record graph := {
    commit_ids : id -> Prop;
    sb : relation id;
    rf : relation id;
    lab : id -> label;
}.

End Commit. *)

Module WCore.

(*
  The following relations must be empty for GC
  - data
  - addr
  - ctrl
  - rmw_dep
  - co
*)
Record gc_restr (GC : execution) := {
  gc_wf : Wf GC;
  empty_data : data GC ≡ ∅₂;
  empty_addr : addr GC ≡ ∅₂;
  empty_ctrl : ctrl GC ≡ ∅₂;
  empty_co : co GC ≡ ∅₂;
  empty_rmw_dep : rmw_dep GC ≡ ∅₂;
}.

Record t := {
    G : execution;
    GC : execution;
    GC_COH : gc_restr GC;
    sc : relation actid;
    cont : cont_label ->
            option { lang : Language.t (list label) &
                            (Language.state lang) };
    commit_entries : actid -> option actid;
    non_commit_ids : actid -> Prop;
}.

Section WCoreDefs.
Variable (X : t).
Notation "'G'" := (G X).
Notation "'GC'" := (GC X).
Notation "'sbc'" := (sb GC).
Notation "'sb'" := (sb G).
Notation "'rfc'" := (rf GC).
Notation "'labc'" := (lab GC).
Notation "'E'" := (acts_set G).
Notation "'EC'" := (acts_set GC).
Notation "'lab'" := (lab G).
Notation "'same_loc'" := (same_loc lab).
Notation "'mod'" := (mod lab).
Notation "'hb'"  := (hb G).
Notation "'eco'" := (eco G).
Notation "'rf'"  := (rf G).
Notation "'rmw'" := (rmw G).
Notation "'W'"   := (is_w lab).
Notation "'commit_entries'" := (commit_entries X).
Notation "'non_commit_ids'" := (non_commit_ids X).
Notation "'threads_set'" := (threads_set G).

Definition mapped_cids : actid -> Prop :=
    fun cid => is_some (commit_entries cid).

Definition pmap_rel (r : relation actid) : relation actid :=
    Some ↓ (commit_entries ↑ r).

Definition committed : actid -> Prop :=
    Some ↓₁ (commit_entries ↑₁ E).

Record wf := {
  wf_G : Wf G;
  wf_GC : Wf GC;
  cont_defined : forall e (NINIT : ~ is_init e) (IN : E e) (NRMW : ~ dom_rel rmw e),
    is_some (cont X (CEvent e));
  cont_init : forall tid (IN : threads_set tid), is_some (cont X (CInit tid));

  non_commit_ids_inf : set_size non_commit_ids = NOinfinity;
  non_commit_ids_no_entry : non_commit_ids ⊆₁ (fun cid => commit_entries cid = None);

  commit_sb : pmap_rel sbc ⊆ sb;
  commit_rf : pmap_rel rfc ⊆ rf;

  lab_coh : forall c e (ENTRY : commit_entries c = Some e), lab e = labc c;
}.

Lemma commit_sb_eq : pmap_rel sbc ≡ sb.
Proof using.
  admit.
Admitted.

Lemma entry_commited  : committed ⊆₁ E.
Proof using.
  admit.
Admitted.

(* Record strong_wf := {
  weak_wf : wf;
  entry_commit_ids : mapped_cids ≡₁ EC;
}. *)

Definition correct_cid (e : actid) (c : actid) : Prop :=
  ⟪ CID       : EC c ⟫ /\
  ⟪ LABS      : labc c = lab e ⟫ /\
  ⟪ SB_PRE_G  : dom_rel (pmap_rel (sbc ⨾ ⦗eq c⦘)) ⊆₁ E ⟫ /\
  ⟪ RF_G      : dom_rel (pmap_rel (rfc ⨾ ⦗eq c⦘)) ⊆₁ E ⟫.

(* Definition committed_actid_set :=
    (fun e => exists cid,
                match commit_entries cid with
                | Some (Commit.InExec e') => e = e'
                | _ => False
                end).

Record consistency := {
    hb_eco_irr     : irreflexive (hb ⨾ eco^?);
    weak_atomicity : restr_rel (E_C ∩₁ dom_rel rmw) (rf⁻¹ ⨾ rf) ⊆ ∅₂;
    (* psc_ac : acyclic (psc G); *)
}. *)
End WCoreDefs.

Section WCoreSteps.

(* TODO: check if this satisfies the delta-mo condition (generate lemmas for that and others) *)
Definition add_step_exec
           (lang : Language.t (list label))
           (k k' : cont_label)
           (st st' : Language.state lang)
           (e  : actid)
           (e' : option actid)
           (G G' : execution) : Prop :=
  ⟪ WF_G' : Wf G' ⟫ /\
  ⟪ EIMM : ⦗eq (opt_ext e e')⦘ ⨾ sb G' ≡ ∅₂⟫ /\
  ⟪ EDEF    :
    match e, e' with
    | InitEvent _, _ => False
    | _, Some (InitEvent _) => False
    | ThreadEvent t n, Some (ThreadEvent t' n') =>
      t' = t /\ n' = 1 + n
    | _, _ => True
    end ⟫ /\
  ⟪ THREADS : threads_set G' ≡₁ threads_set G ⟫ /\
  ⟪ EVENTS  : acts_set G' ≡₁ acts_set G ∪₁ (eq e ∪₁ eq_opt e') ⟫ /\
  ⟪ EVENT   : eq e ∪₁ eq_opt e' ⊆₁ set_compl (acts_set G) ⟫ /\
  exists lbl lbl',
    let lbls := (opt_to_list lbl') ++ [lbl] in
    ⟪ KCE     : k' =  CEvent (opt_ext e e') ⟫ /\
    ⟪ STEP    : Language.step lang lbls st st' ⟫ /\
    ⟪ LABEL'  : opt_same_ctor e' lbl' ⟫ /\
    ⟪ LAB'    : lab G' = upd_opt (upd (lab G) e lbl ) e' lbl' ⟫ /\
    ⟪ RF'     : rf G ⊆ rf G' ⟫ /\
    ⟪ CO'     : co G ⊆ co G' ⟫ /\
    ⟪ RMW'    : rmw G' ≡ rmw G ∪ rmw_delta e e' ⟫.


Definition add_step_
           (e  : actid)
           (e' : option actid)
           (X X' : t) : Prop :=
  exists lang k k' st st' c,
    ⟪ COMMIT  : GC X' = GC X ⟫ /\
    ⟪ CONT    : cont X k = Some (existT _ lang st) ⟫ /\
    ⟪ CONT'   : cont X' = upd (cont X) k' (Some (existT _ lang st')) ⟫ /\
    ⟪ NCOMMITIDS : non_commit_ids X' ≡₁ non_commit_ids X ⟫ /\
    ⟪ CORRECT_CID : correct_cid X e c ⟫ /\
    ⟪ COMMIT_ENTRY : commit_entries X' = upd (commit_entries X) c (Some e) ⟫ /\
    add_step_exec lang k k' st st' e e' (G X) (G X').

Definition add_step (X X' : t) : Prop := exists e e', add_step_ e e' X X'.

(* Definition pmap_inv {A B : Type} (s : A -> Prop) (f : A -> option B) : B -> Prop :=
    Some ↓₁ (f ↑₁ s).
Definition add_rc G GC rf_new f :=
  let RC r rc := codom_rel rf_new r /\ lab G r = lab GC rc in
  let po1 x y := in
  ⟪ CMTIDS    : acts_set GC \₁ pmap_inv (dom_rel RC f)  ∪₁ codom_rel RC ⟫ /\
  ⟪ CMTIDS.

Record reexec_step_ rf_new (X X'' X' : t) :=
  { (* The set of reconsidered reads *)
    rf_new_racy : rf_new ⊆ race (G X);
    rf_new_codom : codom_rel rf_new ⊆₁ acts_set (G X);

    (* The intermediate execution *)
    intg_acts : acts_set (G X'') ≡₁ acts_set (G X) \₁ codom_rel (⦗codom_rel rf_new⦘ ⨾ clos_refl_trans (sb (G X) ∪ rf (G X)));
    intg_subexec : sub_execution (G X) (G X'') (sc X) (sc X'');
    intg_cmd_acts : dom_rel (hb_alt (G X) ⨾ ⦗codom_rel rf_new⦘) ⊆₁ acts_set (GC X);
  }.

Record rf_change_step_ G'' sc'' (w r : actid) (X X' : t) :=
  { rfc_r        : is_r (lab (G X)) r;
    rfc_w        : is_w (lab (G X)) w;
    rfc_act_r    : acts_set (G X) r;
    rfc_act_w    : acts_set (G X) w;
    rfc_same_loc : same_loc (lab (G X)) w r;
    rfc_race      : (race (G X) ∪ hb (G X)) w r;

    rfc_ncom  : ~ committed_actid_set X r;
    rfc_hbcom : dom_rel (hb_alt (G X) ⨾ ⦗eq r⦘) ⊆₁ committed_actid_set X;

    rfc_sub      : sub_execution (G X) G'' (sc X) sc'';
    rfc_acts     : acts_set G'' ≡₁ acts_set (G X) \₁ rfc_remove_events r (G X);
    rfc_G        :  G  X' = rfc_endG r w G'';
    rfc_sc       : sc X' = sc'';
  }.
(* TODO: add lemmas on *)

(* TODO: how to update function with a set  *)

Definition removed_commit_ids (r : actid) (X : t) : Commit.id -> Prop :=
  commit_entries X ↓₁
  ((fun e => Some (Commit.InExec e)) ↑₁ rfc_remove_events r (G X)).

Definition rfc_new_commit_entries (r : actid) (X : t) (cid : Commit.id) : option Commit.entry :=
  ifP removed_commit_ids r X cid then None
  else commit_entries X cid.

Definition rfc_new_cont (r : actid) (X : t) (clab : cont_label) : option {lang : Language.t (list label) & Language.state lang} :=
  match clab with
  | CInit tid => cont X clab
  | CEvent e => ifP rfc_remove_events r (G X) e then None else cont X clab
  end.

Definition rf_change_step
           (w    : actid)
           (r    : actid)
           (X X' : t) : Prop :=
  exists G'' sc'',
    ⟪ RFC : rf_change_step_ G'' sc'' w r X X' ⟫ /\
    ⟪ NCOMMITIDS : non_commit_ids X' ≡₁ non_commit_ids X ∪₁ removed_commit_ids r X ⟫ /\
    ⟪ COMMIT_ENTRIES : commit_entries X' = rfc_new_commit_entries r X ⟫ /\
    ⟪ CONTINUATION : cont X' = rfc_new_cont r X ⟫.

Definition reexec_step
           (w    : actid)
           (r    : actid)
           (X X' : t) : Prop :=
  exists X'',
    ⟪ DROP : rf_change_step w r X X'' ⟫ /\
    ⟪ COMMITTED : committed X' ≡₁ committed X ⟫ /\
    ⟪ RESTORE : add_step＊  X'' X' ⟫. *)

End WCoreSteps.

End WCore.

Module Draft.

Record cfg := {
  G : execution;
  GC : execution;
  C : actid -> Prop;
  f : actid -> option actid;
}.

Definition empty_exec : execution :=
  Build_execution ∅ ∅ (fun x => Afence Osc) ∅₂ ∅₂ ∅₂ ∅₂ ∅₂ ∅₂ ∅₂.

Definition empty_cfg (G : execution) : cfg :=
  Build_cfg G empty_exec ∅ (fun x => None).

#[global]
Hint Unfold empty_exec empty_cfg : unfolderDb.

Section Consistency.

Variable (G : execution).

Record IsCons : Prop := {
  (* TODO *)
  dummy: G = G;
}.

End Consistency.

Section CoreDefs.

Variable (X : cfg).
Notation "'G'" := (G X).
Notation "'GC'" := (GC X).
Notation "'C'" := (C X).
Notation "'f'" := (f X).
Notation "'labc'" := (lab GC).
Notation "'lab'" := (lab G).
Notation "'R'" := (is_r lab).
Notation "'W'" := (is_w lab).
Notation "'sbc'" := (sb GC).
Notation "'rfc'" := (rf GC).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).

Record cfg_correct := {
  c_subset : C ⊆₁ acts_set GC;
}.

Record WF : Prop := {
  wf_g : Wf G;
  wf_gc : Wf GC;
  f_inj : inj_dom (fun x => acts_set GC x /\ is_some (f x)) f;
  f_tid : forall c (IN_C : C c), option_map tid (f c) = Some (tid c);
  f_lab : forall c (IN_C : C c), option_map lab (f c) = Some (labc c);
  f_sb : Some ↓ (f ↑ (⦗C⦘ ⨾ sbc ⨾ ⦗C⦘)) ⊆ sb;
  f_rf : Some ↓ (f ↑ (⦗C⦘ ⨾ rfc ⨾ ⦗C⦘)) ⊆ rf;
  f_rmw : forall r (IS_R : R r), dom_rel (rf ⨾ ⦗eq r⦘) ⊆₁ W \/ (f ↑₁ C) (Some r);
}.

End CoreDefs.

Section DeltaDefs.

Variable (G : execution).
Variable (e : actid).
Notation "'is_w'" := (is_w (lab G)).
Notation "'is_r'" := (is_r (lab G)).
Notation "'W'" := is_w.
Notation "'R'" := is_r.
Notation "'W_ex'" := (W_ex G).

(* We do not need sb_delta as `sb` has an exact formula *)
(* Definition sb_delta : relation actid :=
  (E ∩₁ (fun x => tid x = tid e)) × eq e. *)

Definition rf_delta_R (w : option actid) : relation actid :=
  match w with
  | Some w => (eq w) × (eq e) ∩ W × R
  | _ => ∅₂
  end.

Definition rf_delta_W (GC : execution) (f' : actid -> option actid) : relation actid :=
  let Wc := f' ↓₁ (eq (Some e)) in
  let Rc := codom_rel (⦗Wc⦘ ⨾ (rf GC)) in
  (eq e) × (Some ↓₁ (f' ↑₁ Rc)).

Definition mo_delta (W1 W2 : actid -> Prop) : relation actid :=
  if is_w e then ((eq e) × W1) ∪ ((eq e) × W2)
  else ∅₂.

Definition rmw_delta (r : option actid) : relation actid :=
  (R ∩₁ (eq_opt r)) × (W_ex ∩₁ (eq e)).

End DeltaDefs.

Section CfgAddEventStep.

Variable (X X' : cfg).
Notation "'G''" := (G X').
Notation "'GC''" := (GC X').
Notation "'C''" := (C X').
Notation "'f''" := (f X').
Notation "'E''" := (acts_set G').
Notation "'lab''" := (lab G').

Notation "'G'" := (G X).
Notation "'GC'" := (GC X).
Notation "'C'" := (C X).
Notation "'f'" := (f X).
Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).

Record __cfg_add_event
  (e : actid)
  (l : label)
  (r w : option actid)
  (W1 W2 : actid -> Prop)
  (c : option actid) : Prop :=
{ e_notin : ~(E e);
  e_new : E' ≡₁ E ∪₁ (eq e);
  lab_new : lab' = upd lab e l;

  (* Skipping condition for sb *)
  rf_new : rf G' ≡ (rf G) ∪ (rf_delta_R G e w) ∪ (rf_delta_W e GC f');
  mo_new : co G' ≡ (co G) ∪ (mo_delta G e W1 W2);
  rmw_new : rmw G' ≡ (rmw G) ∪ (rmw_delta G e r);

  f_new : match c with
          | None => True
          | Some c => f' = upd f e (Some c)
          end;
  wf_new_conf : WF X';
}.

Definition cfg_add_event (e : actid) (l : label) : Prop :=
  exists r w W1 W2 c, __cfg_add_event e l r w W1 W2 c.

End CfgAddEventStep.

Section ExecAdd.

Variable (G G' : execution).

Record exec_inst (e : actid) (l : label) : Prop := {
  cfg_step : cfg_add_event (empty_cfg G) (empty_cfg G') e l;
  is_cons : IsCons G';
}.

End ExecAdd.

Section ExecRexec.

Variable (G G' : execution).
Variable (rfre : relation actid).

Notation "'E'" := (acts_set G).
Notation "'is_w'" := (is_w (lab G)).
Notation "'is_r'" := (is_r (lab G)).
Notation "'W'" := is_w.
Notation "'R'" := is_r.
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

Definition silent_cfg_add_step (X X' : cfg) : Prop :=
  exists e l, cfg_add_event X X' e l.
Definition f_restr_D (f : actid -> option actid) : (actid -> option actid) :=
  (restr_fun (Some ↓₁ (f ↑₁ D)) f (fun x => None)).

Record G_restr_D (G G'' : execution) : Prop :=
  { sub_G : sub_execution G G'' ∅₂ ∅₂;
    acts_D : acts_set G'' ≡₁ D;
  }.

Record __reexec
  (G'' : execution)
  (f f' : actid -> option actid)
  (C : actid -> Prop) : Prop :=
{ rf_sub_re : rfre ⊆ re;
  rf_sub_f : rfre ⊆ Some ↓ (f ↑ rf');
  d_wre_sub_f : D ∪₁ Wre ⊆₁ Some ↓₁ (f ↑₁ C);

  cfg_wf : WF (Build_cfg G G' C f);
  int_G_D : G_restr_D G G'';
  cfg_steps : silent_cfg_add_step＊
    (Build_cfg G'' G' C (f_restr_D f))
    (Build_cfg G' G' C f');

  c_correct : forall c (IN_C : C c), is_some (f c);
  new_g_cons : IsCons G';
}.

Definition reexec : Prop := exists G'' f f' C, __reexec G'' f f' C.

End ExecRexec.

End Draft.