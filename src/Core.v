Require Import Lia Setoid Program.Basics.
From PromisingLib Require Import Language.
From hahn Require Import Hahn.
From imm Require Import AuxDef Events Execution.

Inductive cont_label :=
| CInit (tid : thread_id)
| CEvent (e : actid)
.

Module CommitId.
Definition t := nat.
End CommitId.

Module WCore.

Record t := {
    G : execution;

    (* We might need a different structure for this,
       i.e., currently on paper, we assign CommitId.t
       to a label. *)
    commit_id : actid -> CommitId.t;
    committed : CommitId.t -> Prop;

    cont : cont_label ->
            option { lang : Language.t (list label) &
                            (Language.state lang) };
}.


(* TODO *)
Record wf (X : t) := {
    wf_G : Wf (G X);
}.

Record consistency (X : t) := {
    hb_eco_irr : False;
}.
    
End WCore.
