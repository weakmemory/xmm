From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution.
From xmm Require Import Instructions.
From xmm Require Import Core.
Require Import Lia Setoid Program.Basics.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Structures.OrderedType.

Open Scope nat_scope.
Open Scope program_scope.

Section Program.

Definition program_trace := thread_id -> list label.
Definition program := program_trace -> Prop.

Record program_trace_sequented (p_tr1 p_tr2 : program_trace) (t1 t2 : thread_id) : Prop :=
    { p_tr_eq : forall t, t <> t1 /\ t <> t2 -> p_tr1 t = p_tr2 t;
      p_tr_empty : p_tr2 t2 = [];
      p_tr_concat : p_tr2 t1 = p_tr1 t1 ++ p_tr1 t2;
    }. 

Definition corresp_px (exec : WCore.t) (p_tr : program_trace) : Prop :=
    forall t i, (acts_set (WCore.G exec)) (ThreadEvent t i) -> 
            Some (lab (WCore.G exec) (ThreadEvent t i)) = nth_error (p_tr t) i.

Definition program_sequented (p1 p2 : program) (t1 t2 : thread_id) : Prop :=
    forall p_tr : program_trace,
        p2 p_tr -> exists p_tr', p1 p_tr' /\ 
        program_trace_sequented p_tr' p_tr t1 t2.

Record exec_sequent (ex1 ex2 : WCore.t) (p1 p2 : program)
                        (t1 t2 : thread_id) : Prop := {
    exec_sequented : program_sequented p1 p2 t1 t2;
    traces_cond : forall p_tr1 p_tr2 : program_trace,
        p1 p_tr1 -> p2 p_tr2 ->
        corresp_px ex1 p_tr1 ->
        corresp_px ex2 p_tr2 ->
        program_trace_sequented p_tr1 p_tr2 t1 t2;
    }.


End Program.
