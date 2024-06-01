Require Import Lia Setoid Program.Basics.
Require Import AuxDef AuxRel.
Require Import ThreadTrace.

From PromisingLib Require Import Language Basic.
From hahn Require Import Hahn.
From hahn Require Import HahnTrace.
From hahn Require Import HahnSorted.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco imm_s_hb.
From imm Require Import imm_s_ppo.
From imm Require Import imm_s_hb.
From imm Require Import imm_bob.
From imm Require Import imm_s.
From imm Require Import SubExecution.
From imm Require Import FinExecution.
From imm Require Import FinThreads.

Open Scope nat_scope.

Module I2Exec.

Section MainDefs.

Record instruction_id : Set := {
  instr_id : nat;
  tick : nat;
}.

Variable G : execution.
Variable e2instr : actid -> instruction_id.

Definition rmw_end := codom_rel (rmw G).

Definition nrmw_ord := restr_rel (set_compl is_init) (sb G \ rmw G).

Definition rmw_ord := restr_rel (set_compl is_init) (rmw G).

(* TODO: express via inclusion stuff *)
Record E2InstrWf : Prop := {
  e2instr_inj : inj_dom (acts_set G ∩₁ set_compl is_init) e2instr;
  nrmwend_even_tick : forall instr,
    tick ↑ restr_rel (fun x => instr_id x = instr) (e2instr ↑ nrmw_ord)
      ⊆ (fun x y => y = 2 + x)⁺;
  rmw_ticks : forall instr,
    tick ↑ restr_rel (fun x => instr_id x = instr) (e2instr ↑ rmw_ord)
      ⊆ (fun x y => y = 1 + x)⁺;
}.

End MainDefs.

Section SanityCheck.

Variable G : execution.
Variable e2prog : actid -> nat.

Hypothesis WF : Wf G.
Hypothesis WEAK_INJ : forall x y (EQ : e2prog x = e2prog y), tid x = tid y.

Definition ext_sb_ord := restr_rel (set_compl is_init) ext_sb.

Lemma ninit_ext_sb_before_fin e :
  set_finite (dom_rel (ext_sb_ord ⨾ ⦗eq e⦘)).
Proof using.
  destruct e as [el | et en].
  { arewrite (ext_sb_ord ⨾ ⦗eq (InitEvent el)⦘ ≡ ∅₂).
    { split; [| basic_solver].
      unfold ext_sb_ord. unfolder. ins. desf. }
    rewrite dom_empty. apply set_finite_empty. }
  unfold ext_sb_ord. unfolder.
  exists (map (ThreadEvent et) (List.seq 0 en)).
  intros [xl | xt xn] (y & (SB & DOM & CODOM) & EQ).
  all: subst; ins; desf.
  apply in_map_iff. exists xn; split; eauto.
  now apply in_seq0_iff.
Qed.

Lemma ninit_sb_before_fin e :
  set_finite (dom_rel (nrmw_ord G ⨾ ⦗eq e⦘)).
Proof using WF.
  apply set_finite_mori with (x := dom_rel (ext_sb_ord ⨾ ⦗eq e⦘)).
  all: try now apply ninit_ext_sb_before_fin.
  red. unfold nrmw_ord, ext_sb_ord.
  apply dom_rel_mori, seq_mori; ins.
  apply restr_rel_mori; ins.
  unfold sb. basic_solver.
Qed.

Lemma count_nrmw e :
  { N : nat |
    set_size (
      dom_rel (nrmw_ord G ⨾ ⦗eq e⦘) ∩₁
      fun x => e2prog x = e2prog e
    ) = NOnum N }.
Proof using WF.
  apply ClassicalEpsilon.constructive_indefinite_description.
  eapply set_size_finite, set_finite_mori,
         ninit_sb_before_fin with (e := e).
  red. basic_solver.
Qed.

Lemma count_nrmw_inj instr :
  inj_dom
    (set_compl is_init ∩₁ fun x => e2prog x = instr)
    (fun e => proj1_sig (count_nrmw e)).
Proof using WF WEAK_INJ.
  unfolder. intros x y [XINIT XPROG] [YNINIT YPROG] EQ.
  destruct (count_nrmw x) as [XN XSZ],
           (count_nrmw y) as [YN YSZ]; ins.
  rewrite XPROG in XSZ. rewrite YPROG in YSZ.
  rewrite <- YPROG in XPROG. apply WEAK_INJ in XPROG.
  clear YPROG. rename XPROG into TIDS.
  subst YN. rename XN into N.
  (* Should be true. We will see *)
  admit.
Admitted.

Lemma check_rmw e :
  { o : option actid | forall a,
     << RMW : rmw G a e >> <-> << EQ : o = Some a >> }.
Proof using WF.
  apply ClassicalEpsilon.constructive_indefinite_description.
  destruct (classic (codom_rel (rmw G) e)) as [CDOM|NCDOM].
  { destruct CDOM as (y & RMW). exists (Some y). intros a.
    split; intros HREL; desf.
    { red. f_equal. eapply wf_rmwff; eauto. }
    red in HREL. desf. }
  exists None. intros a. split; intros HREL; desf.
  red in HREL. exfalso. apply NCDOM. red; eauto.
Qed.

Definition nrmw_enum e : instruction_id :=
  {|
    instr_id := e2prog e;
    tick := 2 * proj1_sig (count_nrmw e);
  |}.

Definition all_enum e : instruction_id :=
  match proj1_sig (check_rmw e) with
  | None => nrmw_enum e
  | Some a => {|
      instr_id := instr_id (nrmw_enum a);
      tick := 1 + tick (nrmw_enum a);
    |}
  end.

Lemma e2instr_correct : E2InstrWf G all_enum.
Proof using WF.
  constructor; ins.
  { unfolder. intros x y (INX & XINIT) (INY & YINIY) EQ.
    unfold all_enum in EQ.
    destruct (check_rmw x) as [ox XIFF],
             (check_rmw y) as [oy YIFF]; ins.
    destruct ox as [ax |], oy as [ay |].
    { admit. }
    all: admit. }
Admitted.

End SanityCheck.

End I2Exec.