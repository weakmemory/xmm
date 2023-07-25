Require Import Lia Setoid Program.Basics.
From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From imm Require Import AuxDef Events Execution Execution_eco imm_s_hb SetSize.

Inductive cont_label :=
| CInit (tid : thread_id)
| CEvent (e : actid)
.

Section Race.
Variable (G : execution).
Variable (hb : relation actid).
Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'same_loc'" := (same_loc lab).
Notation "'mod'" := (mod lab).
Notation "'W'" := (is_w lab).

Definition one (s : actid -> Prop) : relation actid :=
    fun x y => s x \/ s y.

Definition race := restr_rel E (one W ∩ same_loc \ clos_sym hb).

Definition race_mod (o : mode) := race ∩ one (fun e => mode_le (mod e) o).
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
    commit_entries : Commit.id -> option Commit.entry;
    non_commit_ids : Commit.id -> Prop;
    cont : cont_label ->
            option { lang : Language.t (list label) &
                            (Language.state lang) };
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
    non_commit_ids_inf : set_size non_commit_ids = NOinfinity;
    non_commit_ids_no_entry : forall cid (NCI : non_commit_ids cid),
        commit_entries cid = None;
    no_entry_non_commit_ids : forall cid (CIN : commit_entries cid = None),
        non_commit_ids cid;
    cont_defined : forall e (NINIT : ~ is_init e) (IN : E e) (NRMW : ~ dom_rel rmw e),
        is_some (cont X (CEvent e));
    (* TODO: add property stating existence of continuation for some threads *)
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

End WCore.