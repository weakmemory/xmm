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

(* Definition state : Set := location -> value.
Definition prog_threads : Set := nat.
Definition state_init := prog_threads -> state.

Inductive labels_e : Set :=
  | L : label -> labels_e
  | Epsilon : labels_e.

Definition state_upd (s : state) (l : location) (v : value) : state :=
    upd s l v.

Inductive transition : state -> (intr_info * labels_e) -> state -> Prop :=
    | trans_load :
        forall s t i m l v,
          s l = v ->
          transition s (Build_intr_info i t, L (Aload true m l v)) s
    | trans_store :
        forall s t i xm m l v,
          transition s (Build_intr_info i t, L (Astore xm m l v)) (state_upd s l v)
    | trans_fence :
        forall s t i m,
          transition s (Build_intr_info i t, L (Afence m)) s
    | trans_epsilon :
        forall s t i,
          transition s (Build_intr_info i t, Epsilon) s.

Definition program : Set := list (intr_info * labels_e).

Variable G : execution.
Notation "'sb'" := (sb G).

Definition thread_events t : actid -> Prop :=
    fun x => exists n, ThreadEvent t n = x.

Fixpoint thread_event_list (t : thread_id) (N : nat) : list actid :=
    match N with
    | 0 => []
    | S n' => thread_event_list t n' ++ [ThreadEvent t n']
    end.

(*TODO : N?*)

Definition sb_cmp (x y : actid) : comparison :=
  if excluded_middle_informative (sb x y) then Lt
  else if excluded_middle_informative (sb y x) then Gt
  else Eq.

(*TODO : sort*)

Definition thread_events_labs (lst : list actid) : list label :=
    map (fun x => match x with
                  | ThreadEvent _ _ => (lab G) x
                  | InitEvent _ => Afence Orlx
                end) lst.

Definition extract_labels_from_program (prog : program) : list label :=
    map (fun '(_, lbl) => match lbl with
                  | L l => l
                  | Epsilon => Afence Orlx
                end) prog.

Definition same_label label1 label2 :=
  match label1, label2 with
  | Aload  r1 o1 l1 v1, Aload  r2 o2 l2 v2 => r1 = r2 /\ o1 = o2 /\ l1 = l2 /\ v1 = v2
  | Astore s1 o1 l1 v1, Astore s2 o2 l2 v2 => s1 = s2 /\ o1 = o2 /\ l1 = l2 /\ v1 = v2
  | Afence o1, Afence o2 => o1 = o2
  | _,_ => False
  end.

Lemma same_label_dec : forall l1 l2, {same_label l1 l2} + {~ same_label l1 l2}.
Proof.
    intros l1 l2. admit.
Admitted.

Definition same_label_bool (l1 l2 : label) : bool :=
  if same_label_dec l1 l2 then true else false.

Fixpoint is_subsequence (sub seq : list label) : bool :=
    match sub, seq with
    | [], _ => true
    | _, [] => false
    | x :: xs, y :: ys =>
        if same_label_bool x y
        then is_subsequence xs ys
        else is_subsequence sub ys
    end.

Definition trace_conforming_thread (prog : program) (t : thread_id) (N : nat) : Prop :=
      is_subsequence (thread_events_labs (thread_event_list t N)) (extract_labels_from_program prog).

Definition trace_conforming (prog : program) (N : nat) : Prop :=
    forall t, trace_conforming_thread prog t N. *)

End Program.
