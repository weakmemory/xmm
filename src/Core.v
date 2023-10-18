Require Import Lia Setoid Program.Basics.
From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

Import ListNotations.

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

Definition committed : Commit.id -> Prop :=
    fun cid => is_some (commit_entries cid).

Record wf := {
    wf_G : Wf G;
    cont_defined : forall e (NINIT : ~ is_init e) (IN : E e) (NRMW : ~ dom_rel rmw e),
        is_some (cont X (CEvent e));
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
    hb_eco_irr     : irreflexive (hb ;; eco^?);
    weak_atomicity : restr_rel (E_C ∩₁ dom_rel rmw) (rf⁻¹ ;; rf) ⊆ ∅₂;
    (* psc_ac : acyclic (psc G); *)
}.
End WCoreDefs.

Section WCoreSteps.

Definition basic_step_exec_
           (lang : Language.t (list label))
           (k k' : cont_label)
           (st st' : Language.state lang)
           (e  : actid)
           (e' : option actid)
           (G G' : execution) : Prop :=
  ⟪ EDEF    :
    match e, e' with
    | InitEvent _, _ => False
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
    (* let thrd := ES.cont_thread S k in
    ⟪ KCE    : k' =  CEvent (opt_ext e e')⟫ /\
    ⟪ CONT   : K S (k, existT _ lang st) ⟫ /\
    ⟪ CONT'  : ES.cont S' = upd (ES.cont S) k' (Some (existT _ lang st')) ⟫ /\ *)
    ⟪ STEP   : (Language.step lang) lbls st st' ⟫ /\
    ⟪ LABEL' : opt_same_ctor e' lbl' ⟫ /\
    ⟪ LAB'   : lab G' = upd_opt (upd (lab G) e lbl ) e' lbl' ⟫ /\
    ⟪ RF'     : rf G ⊆ rf G' ⟫ /\
    ⟪ CO'     : co G ⊆ co G' ⟫ /\
    ⟪ RMW'   : rmw G' ≡ rmw G ∪ rmw_delta e e' ⟫.

Definition basic_step_
           (lang : Language.t (list label))
           (k k' : cont_label)
           (st st' : (Language.state lang))
           (e  : actid)
           (e' : option actid)
           (X X' : t) : Prop :=
  ⟪ COMMITTED : committed X' ≡₁ committed X ⟫ /\
  basic_step_exec_ lang k k' st st' e e' (G X) (G X').

Definition commit_step_
           (cid : Commit.id)
           (e  : actid)
           (X X' : t) : Prop :=
  << SAMEEXEC : G X' = G X >> /\
  << SAMEcont : cont X' = cont X >> /\

  << NEWCID   : non_commit_ids X cid >> /\
  << NCIDS    : non_commit_ids X' ≡₁ non_commit_ids X \₁ eq cid >> /\
  << ECID     : commit_entries X' = upd (commit_entries X) cid (Some (Commit.InExec e)) >>
  .

Definition reexec_step_
           (X''  : t)

           (w    : actid)
           (r    : actid)
           (X X' : t) : Prop :=
  let E_C := committed_actid_set X in
  << NOTCOM  : ~ E_C r >> /\
  << HBCOM   : dom_rel (hb_alt (G X) ;; <|eq r|>) ⊆₁ E_C >> /\
  << RR      : is_r (lab (G X)) r >> /\
  << WW      : is_w (lab (G X)) w >> /\
  << SAMELOC : same_loc (lab (G X)) w r >> /\
  << RACE : (race (G X) ∪ hb (G X)) w r >> /\

  (* TODO: specify sc relation *)
  << SUBEXEC : sub_execution (G X) (G X'') ∅₂ ∅₂ >> /\
  << EX''    : acts_set (G X'') ≡₁ acts_set (G X) \₁ codom_rel (<|eq r|>;; (sb (G X) ∪ rf (G X))⁺) >> /\

  False.

End WCoreSteps.

End WCore.