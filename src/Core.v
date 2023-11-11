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

(* TODO: move to HahnExt/SetSize.v *)
Lemma set_size_inf_minus_finite {A} (s s' : A -> Prop)
    (INF : set_size s = NOinfinity)
    (FIN : set_finite s') :
  set_size (s \₁ s') = NOinfinity.
Proof using.
  unfold set_size in *. desf.
  exfalso.
  destruct s0 as [l HH].
  destruct FIN as [l' AA].
  apply n. exists (l ++ l'). ins.
  destruct (classic (s' x)) as [IN'|NIN].
  { apply in_app_r. now apply AA. }
  apply in_app_l. apply HH.
  red. auto.
Qed.

(* TODO: move to HahnExt/SetSize.v *)
Lemma set_finite_singl {A} (a : A) : set_finite (eq a).
Proof using. exists [a]. ins. auto. Qed.

(* TODO: move to HahnExt/SetSize.v *)
Lemma set_size_inf_minus_singl {A} (s : A -> Prop) (a : A)
    (INF : set_size s = NOinfinity) :
  set_size (s \₁ eq a) = NOinfinity.
Proof using.
  apply set_size_inf_minus_finite; auto.
  apply set_finite_singl.
Qed.


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

(* NOTE: merge this definition with add_step_exec? Or move parts of add_step_exec here? *)
Definition add_step_
           (e  : actid)
           (e' : option actid)
           (X X' : t) : Prop :=
  exists lang k k' st st',
    ⟪ CONT    : cont X k = Some (existT _ lang st) ⟫ /\
    ⟪ CONT'   : cont X' = upd (cont X) k' (Some (existT _ lang st')) ⟫ /\
    ⟪ NCOMMITIDS : non_commit_ids X' ≡₁ non_commit_ids X ⟫ /\
    ⟪ COMMITENTR : commit_entries X' =  commit_entries X ⟫ /\
    add_step_exec lang k k' st st' e e' (G X) (G X').

Definition add_step (X X' : t) : Prop := exists e e', add_step_ e e' X X'.

Lemma add_step_same_committed (X X' : t) (STEP : add_step X X') : committed X' ≡₁ committed X.
Proof using.
  do 2 (red in STEP; desf).
  unfold committed. now rewrite COMMITENTR.
Qed.

Lemma add_step_wf (X X' : t) (WF : wf X) (STEP : add_step X X') : wf X'.
Proof using.
  unfold add_step, add_step_, add_step_exec in *.
  desf; constructor; auto; intros.
  all: rewrite ?CONT', ?COMMITENTR, ?NCOMMITIDS; auto; try apply WF.
  all: try now apply NCOMMITIDS.
  all: try now apply NCOMMITIDS; rewrite COMMITENTR in CIN;
               apply WF.
  all: try now rewrite updo by congruence;
               apply WF; apply THREADS.

  all: apply set_subset_eq with (P := set_compl _) (a := e) in NRMW.
  all: rewrite RMW', dom_union, set_compl_union in NRMW.
  all: apply EVENTS in IN; unfolder in IN; desf; ins.
  all: try now rewrite upds.
  2: { exfalso. eapply NRMW; eauto.
       clear. basic_solver. }
  all: rewrite updo.
  all: try now apply WF; auto; apply NRMW.
  all: injection as Heq; subst.
  all: eapply EVENT; eauto.
  all: clear; basic_solver.
Qed.

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

Lemma commit_step_wf (X X' : t) (WF: wf X)
                (cid : Commit.id) (e : actid)
                (STEP: commit_step cid e X X'): wf X'.
Proof using.
  desf; constructor; intros.
  all: rewrite ?(cmt_K STEP).
  all: try (apply WF; erewrite <- ?cmt_G by eassumption; auto).

  { rewrite (cmt_G STEP).
    now apply WF. }
  { rewrite (cmt_noncid STEP).
    apply set_size_inf_minus_singl.
    apply WF. }
  { apply (cmt_noncid STEP) in NCI.
    rewrite (cmt_centries STEP), updo; [apply WF | symmetry].
    all: apply NCI. }
  assert (AA : cid0 <> cid).
  { intro F. now rewrite F, (cmt_centries STEP), upds in CIN. }
  rewrite (cmt_centries STEP), updo in CIN by auto.
  apply WF in CIN. apply (cmt_noncid STEP). basic_solver.
Qed.

Definition upd_rval (l : label) (new_val : option value) :=
  match l with
  | Aload rmw mode loc old => Aload rmw mode loc (opt_ext old new_val)
  | _ => l
  end.

Definition rfc_endG (r w : actid) (G : execution) :=
    set lab (fun lab'' => upd lab'' r (upd_rval (lab'' r) (val lab'' w)))
    (set rf (fun rf'' => (rf'' \ (edges_to r)) ∪ singl_rel w r) G).

Record rf_change_step_ G'' sc'' (w r : actid) (X X' : t) :=
  { rfc_r        : is_r (lab (G X)) r;
    rfc_w        : is_w (lab (G X)) w;
    rfc_same_loc : same_loc (lab (G X)) w r;
    rfc_race      : (race (G X) ∪ hb (G X)) w r;

    rfc_ncom  : ~ committed_actid_set X r;
    rfc_hbcom : dom_rel (hb_alt (G X) ⨾ ⦗eq r⦘) ⊆₁ committed_actid_set X;

    rfc_sub      : sub_execution (G X) G'' (sc X) sc'';
    rfc_acts     : acts_set G'' ≡₁ acts_set (G X) \₁ codom_rel (⦗eq r⦘⨾ (sb (G X) ∪ rf (G X))⁺);
    rfc_G        :  G  X' = rfc_endG r w G'';
    rfc_sc       : sc X' = sc'';
  }.
(* TODO: add lemmas on *)

(* TODO: how to update function with a set  *)

Lemma rf_change_step_disjoint (G : execution) (r : actid) (WF : Wf G) :
  set_disjoint ((fun a => is_init a) ∩₁ acts_set G) (codom_rel (⦗eq r⦘⨾ (sb G ∪ rf G)⁺)).
Proof using.
  unfolder. intros e (INIT & _) (e' & EQ & REL). subst e'.
  induction REL as [r e REL |]; auto.
  destruct REL as [REL|REL].
  all: apply no_sb_to_init in REL || apply no_rf_to_init in REL.
  all: now unfolder in REL.
Qed.

Lemma rf_change_step_imG_wf (G'' : execution) sc'' (w r : actid) (X X' : t)
  (STEP : rf_change_step_ G'' sc'' w r X X') (WF : Wf (G X)) : Wf G''.
Proof using.
  eapply sub_WF; eauto using rfc_sub.
  rewrite (rfc_acts STEP).
  erewrite <- (set_minus_disjoint (_ ∩₁ _)).
  { apply set_subset_minus; basic_solver. }
  eapply set_disjoint_more.
  all: try apply rf_change_step_disjoint; eauto.
  basic_solver.
Qed.

Lemma rfc_preserve_r (r w : actid) (G : execution) (e : actid)
  : is_r (lab (rfc_endG r w G)) e = is_r (lab G) e.
Proof using.
  unfold rfc_endG, upd_rval, is_r in *; ins.
  destruct (classic (e = r)) as [EQ|NEQ].
  { subst; rewrite upds.
    destruct (lab G r); auto. }
  rewrite updo by assumption.
  destruct (lab G r); auto.
Qed.

Lemma rfc_preserve_w (r w : actid) (G : execution) (e : actid)
  : is_w (lab (rfc_endG r w G)) e = is_w (lab G) e.
Proof using.
  unfold rfc_endG, upd_rval, is_w in *; ins.
  destruct (classic (e = r)) as [EQ|NEQ].
  { subst; rewrite upds.
    destruct (lab G r); auto. }
  rewrite updo by assumption.
  destruct (lab G r); auto.
Qed.

Lemma rfc_preserve_f (r w : actid) (G : execution) (e : actid)
  : is_f (lab (rfc_endG r w G)) e = is_f (lab G) e.
Proof using.
  unfold rfc_endG, upd_rval, is_f in *; ins.
  destruct (classic (e = r)) as [EQ|NEQ].
  { subst; rewrite upds.
    destruct (lab G r); auto. }
  rewrite updo by assumption.
  destruct (lab G r); auto.
Qed.

Lemma rfc_same_r (r w : actid) (G : execution)
  : is_r (lab (rfc_endG r w G)) ≡₁ is_r (lab G).
Proof using.
  unfolder; splits; intros.
  all: now rewrite ?rfc_preserve_r in *.
Qed.

Lemma rfc_same_w (r w : actid) (G : execution)
  : is_w (lab (rfc_endG r w G)) ≡₁ is_w (lab G).
Proof using.
  unfolder; splits; intros.
  all: now rewrite ?rfc_preserve_w in *.
Qed.

Lemma rfc_same_f (r w : actid) (G : execution)
  : is_f (lab (rfc_endG r w G)) ≡₁ is_f (lab G).
Proof using.
  unfolder; splits; intros.
  all: now rewrite ?rfc_preserve_f in *.
Qed.

Lemma rfc_preserve_loc (e : actid) (r w : actid) (G : execution)
  : loc (lab (rfc_endG r w G)) e = loc (lab G) e.
Proof using.
  unfold rfc_endG, upd_rval, loc. simpl.
  destruct (classic (e = r)) as [EQ|NEQ].
  { subst; rewrite upds.
    destruct (lab G r); auto. }
  rewrite updo by assumption.
  destruct (lab G r); auto.
Qed.

Lemma rfc_same_loc_same (r w : actid) (G : execution)
  : same_loc (lab (rfc_endG r w G)) ≡ same_loc (lab G).
Proof using.
  unfold same_loc; unfolder; splits; intros.
  all: now rewrite ?rfc_preserve_loc in *.
Qed.

Lemma rfc_same_actsset (r w : actid) (G : execution)
  : acts_set (rfc_endG r w G) ≡₁ acts_set G.
Proof using.
  unfold acts_set; unfold rfc_endG; simpl.
  easy.
Qed.

Lemma rfc_preserve_rex (e : actid) (r w : actid) (G : execution)
  : R_ex (lab (rfc_endG r w G)) e = R_ex (lab G) e.
Proof using.
  unfold rfc_endG, upd_rval, R_ex. simpl.
  destruct (classic (e = r)) as [EQ|NEQ].
  { subst; rewrite upds.
    destruct (lab G r); auto. }
  rewrite updo by assumption.
  destruct (lab G r); auto.
Qed.

Lemma rfc_same_rex (r w : actid) (G : execution)
  : R_ex (lab (rfc_endG r w G)) ≡₁ R_ex (lab G).
Proof using.
  unfolder; splits; intros.
  all: now rewrite ?rfc_preserve_rex in *.
Qed.

Lemma rel_compress_sub (A : Type) (S1 S2 : A -> Prop) (R1 R2 : relation A)
  (SUB : R1 ⊆ R2) (EQ : R2 ≡ ⦗S1⦘⨾ R2⨾ ⦗ S2⦘):
  R1 ≡ ⦗S1⦘⨾ R1⨾ ⦗S2⦘.
Proof using.
  unfolder; split; try solve[ins; desf; eauto].
  intros x y REL.
  set (REL' := REL).
  apply SUB, EQ in REL'.
  unfolder in REL'; easy.
Qed.

Lemma single_rel_compress (A : Type) (S1 S2 : A -> Prop) (x y : A)
  (MEM_X : S1 x) (MEM_Y : S2 y):
  singl_rel x y ≡ ⦗S1⦘⨾ singl_rel x y⨾ ⦗S2⦘.
Proof using.
  unfolder; split; ins; desf; eauto.
Qed.

Lemma update_rf_ineq_l (r x y : actid) (G : execution)
  (WF : Wf G) (RF : (rf G \ edges_to r) x y) (IS_READ : is_r (lab G) r) :
  x <> r.
Proof using.
  destruct RF as [RF INEQ]. intro F; subst.
  apply (wf_rfD WF) in RF.
  unfolder in RF; desc.
  unfold is_w, is_r in *; destruct (lab G r); auto.
Qed.

Lemma update_rf_ineq_r (r x y : actid) (G : execution)
  (WF : Wf G) (RF : (rf G \ edges_to r) x y) (IS_READ : is_r (lab G) r) :
  y <> r.
Proof using.
  destruct RF as [RF INEQ]. intro F; subst.
  apply INEQ; basic_solver.
Qed.

Lemma rfc_endG_wf (r w : actid) (G : execution) (WF : Wf G)
  (R_MEM : acts_set G w)
  (W_MEM : acts_set G r)
  (R_READ : is_r (lab G) r)
  (W_WRITE : is_w (lab G) w)
  (W_R_SAME_LOC : same_loc (lab G) w r):
  Wf (rfc_endG r w G).
Proof using.
  assert (SUB : rf G \ edges_to r ⊆ rf G) by basic_solver.
  constructor; try now apply WF.
  all: rewrite ?rfc_same_r, ?rfc_same_w, ?rfc_same_f, ?rfc_same_rex.
  all: rewrite ?rfc_same_loc_same, ?rfc_same_actsset.
  all: try solve [unfold rfc_endG; simpl; now apply WF].

  { unfold rfc_endG; simpl.
    rewrite seq_union_l, seq_union_r.
    rewrite <- single_rel_compress by assumption.
    now erewrite <- rel_compress_sub by (apply WF || eauto). }
  { unfold rfc_endG; simpl.
    rewrite seq_union_l, seq_union_r.
    rewrite <- single_rel_compress by assumption.
    now erewrite <- rel_compress_sub by (apply WF || eauto). }
  { unfold rfc_endG; simpl.
    set (HH := wf_rfl WF).
    apply inclusion_union_l; basic_solver. }
  { unfold rfc_endG; simpl. apply funeq_union.
    { intros x y RF.
      unfold val; simpl.
      rewrite updo by (eapply update_rf_ineq_l; eauto).
      rewrite updo by (eapply update_rf_ineq_r; eauto).
      apply wf_rfv; basic_solver. }
    intros x y [EQ EQ']. subst.
    unfold val; simpl.
    rewrite upds. unfold is_r, is_w in *.
    destruct (lab G r) eqn:HEQ1; destruct (lab G w) eqn:HEQ2.
    all: try easy; simpl.
    rewrite updo by (intro F; subst; congruence).
    now rewrite HEQ2. }
  { unfold rfc_endG; simpl.
    rewrite transp_union. apply functional_union.
    { eapply functional_mori; unfold flip; eauto using wf_rff, transp_mori. }
    { basic_solver. }
    unfolder; intros e [y [RF F]] [y' [EQ1 EQ2]]; subst.
    apply F; eauto. }
  { intro ol.
    rewrite rfc_same_w, rfc_same_actsset.
    enough (HEQ :
      (fun x : actid => loc _ x = ol) ≡₁
      (fun x : actid => loc _ x = ol)
    ) by (rewrite HEQ; unfold rfc_endG; simpl; apply WF).
    unfold same_loc; unfolder; splits; intros.
    all: now rewrite ?rfc_preserve_loc in *. }
  { intros l [e [INACT LOC]].
    apply rfc_same_actsset in INACT.
    rewrite rfc_preserve_loc in LOC.
    apply WF; eauto. }
  unfold rfc_endG; simpl. intros l.
  enough (HNEQ: InitEvent l <> r) by (rewrite updo; apply WF || auto).
  intro F; subst. eapply read_or_fence_is_not_init; eauto.
Qed.


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

Lemma reexec_step_wf w r (X X' : t)
  (WF : wf X) (STEP : reexec_step w r X X') : wf X'.
Proof using.
  cdes STEP.
  assert (WF'' : wf X'').
  { (* TODO: make a lemma that rf_change_step preserves wf *)
    admit. }
  (* clos_refl_trans
     clos_refl_trans_1n
     clos_refl_trans_n1 *)
  admit.
Admitted.

End WCoreSteps.

End WCore.