Require Import Lia Setoid Program.Basics.

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

#[export] Instance eta_execution : Settable _ :=
  settable! Build_execution
    <acts_set; threads_set; lab; rmw; data; addr; ctrl; rmw_dep; rf; co>
.

Definition rmw_delta e e' : relation actid :=
  eq e × eq_opt e'.

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

Module Commit.
Definition id := nat.

Inductive entry :=
| InExec (e : actid)
| ToRestore (l : label)
.
End Commit.

Module WCore.

Record t := {
    G : execution;
    sc : relation actid;
    cont : cont_label ->
            option { lang : Language.t (list label) &
                            (Language.state lang) };

    commit_entries : Commit.id -> option Commit.entry;
    non_commit_ids : Commit.id -> Prop;
}.

Section WCoreDefs.
Variable (X : t).
Notation "'G'" := (G X).
Notation "'E'" := (acts_set G).
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

Definition committed : Commit.id -> Prop :=
    fun cid => is_some (commit_entries cid).

Record wf := {
    wf_G : Wf G;
    cont_defined : forall e (NINIT : ~ is_init e) (IN : E e) (NRMW : ~ dom_rel rmw e),
    is_some (cont X (CEvent e));
    cont_init : forall tid (IN : threads_set tid), is_some (cont X (CInit tid));
    (* TODO: add property stating existence of continuation for some threads *)

    non_commit_ids_inf : set_size non_commit_ids = NOinfinity;
    non_commit_ids_no_entry : forall cid (NCI : non_commit_ids cid),
        commit_entries cid = None;
    no_entry_non_commit_ids : forall cid (CIN : commit_entries cid = None),
        non_commit_ids cid;
}.

Definition committed_actid_set :=
    (fun e => exists cid,
                match commit_entries cid with
                | Some (Commit.InExec e') => e = e'
                | _ => False
                end).
Notation "'E_C'" := (E ∩₁ committed_actid_set).

Record consistency := {
    hb_eco_irr     : irreflexive (hb ⨾ eco^?);
    weak_atomicity : restr_rel (E_C ∩₁ dom_rel rmw) (rf⁻¹ ⨾ rf) ⊆ ∅₂;
    (* psc_ac : acyclic (psc G); *)
}.
End WCoreDefs.

Section WCoreSteps.

Definition add_step_exec
           (lang : Language.t (list label))
           (k k' : cont_label)
           (st st' : Language.state lang)
           (e  : actid)
           (e' : option actid)
           (X X' : t) : Prop :=
  let G' := G X' in
  let G := G X in
  ⟪ WF_G' : Wf G' ⟫ /\
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
    (* TODO: add restrictions on continuations *)
    (* let thrd := ES.cont_thread S k in *)
    ⟪ KCE    : k' =  CEvent (opt_ext e e') ⟫ /\
    ⟪ CONT   : cont X k = Some (existT _ lang st) ⟫ /\
    ⟪ CONT'  : cont X' = upd (cont X) k' (Some (existT _ lang st')) ⟫ /\
    ⟪ STEP   : (Language.step lang) lbls st st' ⟫ /\
    ⟪ LABEL' : opt_same_ctor e' lbl' ⟫ /\
    ⟪ LAB'   : lab G' = upd_opt (upd (lab G) e lbl ) e' lbl' ⟫ /\
    ⟪ RF'     : rf G ⊆ rf G' ⟫ /\
    ⟪ CO'     : co G ⊆ co G' ⟫ /\
    ⟪ RMW'   : rmw G' ≡ rmw G ∪ rmw_delta e e' ⟫.

(* NOTE: merge this definition with add_step_exec? Or move parts of add_step_exec here? *)
(* NOTE: should we add a requirement that `non_commit_ids` remain the same? *)
Definition add_step_
           (e  : actid)
           (e' : option actid)
           (X X' : t) : Prop :=
  exists lang k k' st st',
    ⟪ COMMITTED : committed X' ≡₁ committed X ⟫ /\
    add_step_exec lang k k' st st' e e' X X'.

Definition add_step (X X' : t) : Prop := exists e e', add_step_ e e' X X'.

Lemma add_step_same_uncommitted (X X' : t) (STEP : add_step X X') : non_commit_ids X' ≡₁ non_commit_ids X.
Proof.
Admitted.

Lemma add_step_wf (X X' : t) (WF : wf X) (STEP : add_step X X') : wf X'.
Proof.
  unfold add_step, add_step_, add_step_exec in *.
  desf; constructor; auto; intros.
  { rewrite CONT'.
    (* TODO turn into a lemma like set_subset_eq *)
    apply set_subset_eq with (P := set_compl _) (a := e) in NRMW.
    rewrite RMW', dom_union, set_compl_union in NRMW.
    apply EVENTS in IN; unfolder in IN; desf.
    { rewrite updo. apply WF; auto.
      { apply set_subset_eq with (P := set_compl _) (a := e); auto.
        now apply NRMW. }
      injection as Heq.
      apply EVENT with (x := e); simpl; unfolder; auto. }
    { exfalso.
      apply NRMW with (x := ThreadEvent thread index); auto.
      unfold rmw_delta; unfolder; eauto. }
    now rewrite upds. }
  { rewrite CONT'.
    rewrite updo by congruence.
    apply WF. now apply THREADS. }
  { (*
    committed sets are the same.
    therefore we probably should be able to prove that the
    non_commit_ids set is the same
    *)
    admit. }
  { admit. }
  { admit. }
  { rewrite CONT'.
    (* TODO turn into a lemma like set_subset_eq *)
    apply set_subset_eq with (P := set_compl _) (a := e) in NRMW.
    rewrite RMW', dom_union, set_compl_union in NRMW.
    apply EVENTS in IN; unfolder in IN; desf.
    { rewrite updo. apply WF; auto.
      { apply set_subset_eq with (P := set_compl _) (a := e); auto.
        now apply NRMW. }
      injection as Heq.
      apply EVENT with (x := e); simpl; unfolder; auto. }
    { simpl. now rewrite upds. }
  }
  { rewrite CONT'.
    rewrite updo by congruence.
    apply WF. now apply THREADS. }
  { admit. }
  { admit. }
  { admit. }
Qed.


Record commit_step
           (cid : Commit.id)
           (e  : actid)
           (X X' : t) : Prop :=
  { cmt_G : G X' = G X;
    cmt_K : cont X' = cont X;

    cmt_cid      : non_commit_ids X cid;
    cmt_noncid   : non_commit_ids X' ≡₁ non_commit_ids X \₁ (eq cid);
    cmt_centries : commit_entries X' = upd (commit_entries X) cid (Some (Commit.InExec e));
  }.

Record rf_change_step_ G'' sc'' (w r : actid) (X X' : t) :=
  { rfc_r        : is_r (lab (G X)) r;
    rfc_w        : is_w (lab (G X)) w;
    rfc_same_loc : same_loc (lab (G X)) w r;
    rfc_race      : (race (G X) ∪ hb (G X)) w r;

    rfc_ncom  : ~ committed_actid_set X r;
    rfc_hbcom : dom_rel (hb_alt (G X) ⨾ ⦗eq r⦘) ⊆₁ committed_actid_set X;

    rfc_sub      : sub_execution (G X) G'' (sc X) sc'';
    rfc_acts     : acts_set G'' ≡₁ acts_set (G X) \₁ codom_rel (⦗eq r⦘⨾ (sb (G X) ∪ rf (G X))⁺);
    rfc_G        :  G  X' =
                       set lab (fun lab'' => lab'') (* TODO: fix new lab *)
                       (set rf (fun rf'' => (rf'' \ (edges_to r)) ∪ singl_rel w r) G'');
    rfc_sc       : sc X' = sc'';
  }.
(* TODO: add lemmas on *)

Definition rf_change_step
           (w    : actid)
           (r    : actid)
           (X X' : t) : Prop :=
  exists G'' sc'', rf_change_step_ G'' sc'' w r X X'.

Definition reexec_step
           (w    : actid)
           (r    : actid)
           (X X' : t) : Prop :=
  exists X'',
    ⟪ DROP : rf_change_step w r X X'' ⟫ /\
    ⟪ COMMITTED : committed X' ≡₁ committed X ⟫ /\
    ⟪ RESTORE : add_step＊  X'' X' ⟫.

End WCoreSteps.

End WCore.