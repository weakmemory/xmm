From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import SubExecution.

Section ThreadTrace.

Variable (G : execution).

Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).

Definition thread_trace (t : thread_id) : trace label :=
  let S := (fun e => t = tid e) ∩₁ E in
  match excluded_middle_informative (set_finite S) with
  | left FIN =>
    trace_fin
        (map (fun e => lab e)
          (isort sb
            (undup
              (filterP S
                (proj1_sig
                    (IndefiniteDescription.constructive_indefinite_description
                      (fun findom => forall x, S x -> In x findom)
                      FIN))))))
  | right _ => trace_inf (fun e => lab (ThreadEvent t e))
  end.

End ThreadTrace.