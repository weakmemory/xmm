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

Module Commit.
Definition id := nat. 

Record graph := {
    commit_ids : id -> Prop; 
    sb : relation id; 
    rf : relation id; 
    lab : id -> label;
}.

End Commit.

Module WCore.

Record t := {
    G : execution; 
    GC : Commit.graph;
    sc : relation actid;
    cont : cont_label ->
            option { lang : Language.t (list label) &
                            (Language.state lang) };
    commit_entries : Commit.id -> option actid;
    non_commit_ids : Commit.id -> Prop;
}.

Section WCoreDefs.
Variable (X : t).
Notation "'G'" := (G X). 
Notation "'GC'" := (GC X). 
Notation "'sbc'" := Commit.sb.  
Notation "'rfc'" := Commit.rf.  
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
    entry_commit_ids : forall cid (ENTRY : is_some (commit_entries cid)),
        Commit.commit_ids GC cid;
    
    commit_sb : forall a b ea eb (ENTRY_A : commit_entries a = Some ea)
                                 (ENTRY_B : commit_entries b = Some eb),
        sbc GC a b <-> sb G ea eb;
    commit_rf : forall a b ea eb (ENTRY_A : commit_entries a = Some ea)
                                 (ENTRY_B : commit_entries b = Some eb),
        rf ea eb -> rfc GC a b; 
    (* commit_no_w_r : forall r (NO_WRITE : (E \₁ codom_rel rf) r), 
        is_some (commit_entries r); *)

    lab_coh : forall c e (ENTRY : commit_entries c = Some e),
        lab e = Commit.lab GC c;
}.

(* Definition committed_actid_set :=
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
}. *)
End WCoreDefs.

Section WCoreSteps. 

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

Print set_collect.

Definition correct_cid 
            (G : execution) 
            (GC : Commit.graph) 
            (commit_entries : Commit.id -> option actid)  
            (e : actid) 
            (c : Commit.id) : Prop := 
  ⟪ CID     : (Commit.commit_ids GC) c ⟫ /\ 
  ⟪ LABS    : (Commit.lab GC) c = (lab G) e ⟫ /\ 
  ⟪ SB_PRE_G     : Some ↓₁ (commit_entries ↑₁ dom_rel (Commit.sb GC ⨾ ⦗eq c⦘)) ⊆₁ acts_set G⟫ /\ 
  ⟪ RF_G    : forall c_w e_w (RF : Commit.rf GC c_w c) (EQ : commit_entries c_w = Some e_w) , dom_rel (rf G ⨾ ⦗eq e⦘) e_w ⟫.


(* NOTE: merge this definition with add_step_exec? Or move parts of add_step_exec here? *)
Definition add_step_
           (e  : actid) 
           (e' : option actid)
           (X X' : t) : Prop :=
  exists lang k k' st st' c,
    ⟪ CONT    : cont X k = Some (existT _ lang st) ⟫ /\
    ⟪ CONT'   : cont X' = upd (cont X) k' (Some (existT _ lang st')) ⟫ /\
    ⟪ NCOMMITIDS : non_commit_ids X' ≡₁ non_commit_ids X ⟫ /\
    ⟪ COMMIT_ENTRY : commit_entries X' = upd (commit_entries X) c (Some e) ⟫ /\ 
    ⟪ CORRECT_CID : correct_cid (G X) (GC X) (commit_entries X) e c ⟫ /\
    add_step_exec lang k k' st st' e e' (G X) (G X').

Definition add_step (X X' : t) : Prop := exists e e', add_step_ e e' X X'.

(* TODO make into definition? *)
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

Definition upd_rval (l : label) (new_val : option value) :=
  match l with
  | Aload rmw mode loc old => Aload rmw mode loc (opt_ext old new_val)
  | _ => l
  end.

Definition rfc_endG (r w : actid) (G : execution) :=
    set lab (fun lab'' => upd lab'' r (upd_rval (lab'' r) (val lab'' w)))
    (set rf (fun rf'' => (rf'' \ (edges_to r)) ∪ singl_rel w r) G).

Definition rfc_remove_events (r : actid) (G : execution) : actid -> Prop :=
  codom_rel (⦗eq r⦘⨾ (sb G ∪ rf G)⁺).

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
    ⟪ RESTORE : add_step＊  X'' X' ⟫.

End WCoreSteps.

End WCore.