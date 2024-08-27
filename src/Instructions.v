Require Import Lia Setoid Program.Basics.
Require Import AuxDef AuxRel.
Require Import ThreadTrace.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
From imm Require Import imm_s_ppo.
Require Import xmm_s_hb.
From imm Require Import imm_bob.
Require Import xmm_s.
From imm Require Import SubExecution.
From imm Require Import FinExecution.
From imm Require Import FinThreads.

Open Scope nat_scope.

Module I2Exec.

Definition instr_id : Set := nat.

Record intr_info : Set := {
  instr : instr_id;
  tick : nat;
}.

Section MainDefs.

Variable G : execution.
Variable e2instr : actid -> intr_info.
Variable rmw_instr : instr_id -> Prop.

Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'rmw'" := (rmw G).
Notation "'sb'" := (sb G).

Definition rmw_actids := (instr ∘ e2instr) ↓₁ rmw_instr.
Definition instr_actids ins := E ∩₁ set_compl is_init ∩₁
                                (instr ∘ e2instr) ↓₁ eq ins.

Inductive lab_ty : Set :=
| TyLoad : lab_ty
| TyStore : lab_ty
| TyFence : lab_ty.

Definition e_type e :=
  match lab e with
  | Aload _ _ _ _ => TyLoad
  | Astore _ _ _ _ => TyStore
  | Afence _ => TyFence
  end.

Definition same_instr x y : Prop :=
  instr (e2instr x) = instr (e2instr y).

Record E2InstrWf : Prop := {
  wf_rmw_instrs : dom_rel rmw ∪₁ codom_rel rmw ⊆₁ rmw_actids;
  wf_instr_ty : funeq e_type
    (restr_rel (E ∩₁ set_compl rmw_actids) same_instr);
  wf_same_instr_tid : same_instr ⊆ same_tid;
  wf_sb_ticks : forall ins,
    restr_rel (instr_actids ins) (sb \ rmw)
      ⊆ (tick ∘ e2instr) ↓ (fun x y => y = 2 + x)⁺;
  wf_rmw_ticks : forall ins,
    restr_rel (instr_actids ins) rmw
      ⊆ (tick ∘ e2instr) ↓ (fun x y => y = 1 + x);
}.

Lemma rmw_actids_closed x y
    (RMW : rmw_actids x)
    (SAME : same_instr x y) :
  rmw_actids y.
Proof using.
  unfold rmw_actids, same_instr, compose in *.
  unfolder in *. now rewrite <- SAME.
Qed.

Lemma plus_2_t :
  (fun x y => y = 2 + x)⁺ ≡ (fun x y => exists p, y = 2*(1 + p) + x).
Proof using.
  unfolder. split; intros x y HREL.
  { induction HREL as [x y HEQ | x y z HREL1 [p1 IHR1] HREL2 [p2 IHR2]].
    { exists 0; ins. }
    exists (1 + p1 + p2). lia. }
  destruct HREL as [p HEQ]. generalize x y HEQ. clear HEQ x y.
  induction p as [| p IHP].
  { ins. now apply t_step. }
  intros x y HEQ. apply t_trans with (y - 2).
  { apply IHP. lia. }
  apply t_step. lia.
Qed.

Lemma plus_2_irr : irreflexive ((fun x y => y = 2 + x)⁺).
Proof using.
  rewrite plus_2_t. unfolder. ins. desf. lia.
Qed.

Lemma e2instr_inj
    (WF : E2InstrWf) :
  inj_dom (E ∩₁ set_compl is_init) e2instr.
Proof using.
  unfolder. intros x y (XINE & XNINIT) (YINE & YNINIT) EQ.
  assert (INS : same_instr x y) by (red; congruence).
  assert (TID : same_tid x y) by now apply WF.
  set (ins := instr (e2instr x)).
  destruct (classic (rmw x y)) as [XYRMW | NXYRMW].
  { assert (XYRMW' : restr_rel (instr_actids ins) rmw x y).
    { subst ins. unfold instr_actids. unfolder. splits; eauto. }
    apply WF in XYRMW'. unfold compose in XYRMW'.
    unfolder in XYRMW'. rewrite EQ in XYRMW'. lia. }
  destruct (classic (rmw y x)) as [YXRMW | NYXRMW].
  { assert (YXRMW' : restr_rel (instr_actids ins) rmw y x).
    { subst ins. unfold instr_actids. unfolder. splits; eauto. }
    apply WF in YXRMW'. unfold compose in YXRMW'.
    unfolder in YXRMW'. rewrite EQ in YXRMW'. lia. }
  assert (SB : sb x y \/ x = y \/ sb y x).
  { unfold sb, ext_sb, is_init, same_tid in *. unfolder.
    destruct x as [xl | xt xn], y as [yl | yt yn]; ins.
    subst xt. rename yt into t.
    assert (LT_CASES : xn < yn \/ xn = yn \/ yn < xn) by lia.
    desf; eauto.
    { left. do 2 (eexists; splits; eauto). ins. }
    do 2 right. do 2 (eexists; splits; eauto). ins. }
  desf; ins.
  { assert (SB' : restr_rel (instr_actids ins) (sb \ rmw) x y).
    { subst ins. unfold instr_actids. unfolder. splits; eauto. }
    apply WF in SB'. unfold compose in SB'.
    unfolder in SB'. rewrite EQ in SB'.
    now apply plus_2_irr in SB'. }
  assert (SB' : restr_rel (instr_actids ins) (sb \ rmw) y x).
  { subst ins. unfold instr_actids. unfolder. splits; eauto. }
  apply WF in SB'. unfold compose in SB'.
  unfolder in SB'. rewrite EQ in SB'.
  now apply plus_2_irr in SB'.
Qed.

End MainDefs.

Section SameProg.

Variable G G' : execution.
Variable e2instr e2instr' : actid -> intr_info.

Definition same_prog : Prop :=
  forall e e'
    (SAME_INSTR : instr (e2instr e) = instr (e2instr' e')),
      e_type G = e_type G'.

End SameProg.

End I2Exec.