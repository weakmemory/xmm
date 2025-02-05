Require Import AuxDef.
Require Import Core.
Require Import AuxRel AuxRel2.
Require Import Srf Rhb.
Require Import SimrelCommon.
Require Import StepOps.
Require Import AuxInj.
Require Import xmm_s_hb.
Require Import Lia.

From hahn Require Import Hahn.
From hahnExt Require Import HahnExt.
From imm Require Import Events Execution Execution_eco.
Require Import Setoid Morphisms Program.Basics.

Open Scope program_scope.

Set Implicit Arguments.

Section SimRelSeq.

Variable X_s X_t : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'lab_t'" := (lab G_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'val_t'" := (val lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rhb_t'" := (rhb G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'rpo_t'" := (rpo G_t).
Notation "'rpo_imm_t'" := (rpo_imm G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).

Notation "'G_s'" := (WCore.G X_s).
Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rhb_s'" := (rhb G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'rpo_imm_s'" := (rpo_imm G_s).
Notation "'vf_s'" := (vf G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Definition po_seq := (Tid_ t_1 ∩₁ E_s) × (Tid_ t_2 ∩₁ E_s).

Record seq_simrel : Prop := {
    seq_inj : inj_dom E_t mapper;
    seq_tid_1 : forall tid, tid <> Tid_ t_2 -> eq_dom E_t (tid ∘ mapper) tid; 
    seq_tid_2 : eq_dom E_t (Tid_ t_2 ∘ mapper) Tid_ t_1;
    seq_lab : eq_dom E_t (lab_s ∘ mapper) lab_t;
    seq_acts : E_s ≡₁ mapper ↑₁ E_t;
    seq_sb : sb_s ∪ po_seq ≡ mapper ↑ sb_t;
    seq_rf : rf_s ≡ mapper ↑ rf_t;
    seq_co : co_s ≡ mapper ↑ co_t;
    seq_rmw : rmw_s ≡ mapper ↑ rmw_t;
    seq_threads : threads_set G_s ≡₁ threads_set G_t ∪₁ eq t_2;

    seq_ctrl : ctrl_s ≡ ctrl_t;
    seq_data : data_s ≡ data_t;
    seq_addr : addr_s ≡ addr_t;
    seq_rmw_dep : rmw_dep_s ≡ rmw_dep_t;

    seq_init : fixset is_init mapper;
    (* rsr_mid : eq_dom (E_t \₁ eq a_t \₁ eq b_t) mapper id; *)
}.

End SimRelSeq.

Section SeqSimrelInit.

Variable X_t X_s : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'G_s'" := (WCore.G X_s).

Lemma seq_simrel_init threads
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (THRD1 : threads t_1)
    (THRD2 : threads t_2)
    (THRDNEQ : t_1 <> t_2)
    (INIT : threads tid_init) :
  << SIMREL : seq_simrel
    (WCore.Build_t (WCore.init_exec threads) ∅₂)
    (WCore.Build_t (WCore.init_exec threads) ∅₂)
    t_1 t_2
    id >>.
Proof using.
    assert (IWF : Wf (WCore.init_exec threads)).
    { now apply WCore.wf_init_exec. }
    split; red; vauto; ins.
    { unfold compose. unfold is_init in DX. desf.
      unfold tid. desf. unfold not in *.
      apply PropExtensionality.propositional_extensionality.
      split; ins; desf. }
    { clear; basic_solver. }
    { unfold po_seq; ins.
      assert (EMP1 : (fun e : actid => tid e = t_1)
                    ∩₁ (fun a : actid => is_init a) ≡₁ ∅).
      { split; [|basic_solver].
        intros x COND. destruct COND as [TID ISINIT].
        unfold is_init in ISINIT. desf. }
      assert (EMP2 : (fun e : actid => tid e = t_2)
                    ∩₁ (fun a : actid => is_init a) ≡₁ ∅).
      { split; [|basic_solver].
        intros x COND. destruct COND as [TID ISINIT].
        unfold is_init in ISINIT. desf. }
      rewrite EMP1, EMP2. clear; basic_solver 8. }
    { clear; basic_solver. }
    { clear; basic_solver. }
    { clear; basic_solver. }
    basic_solver.
Qed.

End SeqSimrelInit.

Section SimrelStep.

Variable X_t X_t' X_s : WCore.t.
Variable t_1 t_2 : thread_id.
Variable mapper : actid -> actid.

Notation "'G_t'" := (WCore.G X_t).
Notation "'G_t''" := (WCore.G X_t').
Notation "'G_s'" := (WCore.G X_s).

Notation "'R' G" := (fun e => is_true (is_r (lab G) e)) (at level 1).
Notation "'F' G" := (fun e => is_true (is_f (lab G) e)) (at level 1).
Notation "'W' G" := (fun e => is_true (is_w (lab G) e)) (at level 1).
Notation "'Acq' G" := (fun e => is_true (is_acq (lab G) e)) (at level 1).
Notation "'Rlx' G" := (fun e => is_true (is_rlx (lab G) e)) (at level 1).
Notation "'Rel' G" := (fun e => is_true (is_rel (lab G) e)) (at level 1).

Notation "'lab_t'" := (lab G_t).
Notation "'val_t'" := (val lab_t).
Notation "'loc_t'" := (loc lab_t).
Notation "'same_loc_t'" := (same_loc lab_t).
Notation "'E_t'" := (acts_set G_t).
Notation "'sb_t'" := (sb G_t).
Notation "'rf_t'" := (rf G_t).
Notation "'co_t'" := (co G_t).
Notation "'rmw_t'" := (rmw G_t).
Notation "'rpo_t'" := (rpo G_t).
Notation "'rmw_dep_t'" := (rmw_dep G_t).
Notation "'data_t'" := (data G_t).
Notation "'ctrl_t'" := (ctrl G_t).
Notation "'addr_t'" := (addr G_t).
Notation "'W_t'" := (fun x => is_true (is_w lab_t x)).
Notation "'R_t'" := (fun x => is_true (is_r lab_t x)).
Notation "'Loc_t_' l" := (fun e => loc_t e = l) (at level 1).

Notation "'lab_t''" := (lab G_t').
Notation "'val_t''" := (val lab_t').
Notation "'loc_t''" := (loc lab_t').
Notation "'same_loc_t''" := (same_loc lab_t').
Notation "'E_t''" := (acts_set G_t').
Notation "'sb_t''" := (sb G_t').
Notation "'rf_t''" := (rf G_t').
Notation "'co_t''" := (co G_t').
Notation "'rmw_t''" := (rmw G_t').
Notation "'rpo_t''" := (rpo G_t').
Notation "'rmw_dep_t''" := (rmw_dep G_t').
Notation "'data_t''" := (data G_t').
Notation "'ctrl_t''" := (ctrl G_t').
Notation "'addr_t''" := (addr G_t').
Notation "'W_t''" := (fun x => is_true (is_w lab_t' x)).
Notation "'R_t''" := (fun x => is_true (is_r lab_t' x)).
Notation "'Loc_t_'' l" := (fun e => loc_t' e = l) (at level 1).

Notation "'lab_s'" := (lab G_s).
Notation "'val_s'" := (val lab_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'same_loc_s'" := (same_loc lab_s).
Notation "'E_s'" := (acts_set G_s).
Notation "'loc_s'" := (loc lab_s).
Notation "'sb_s'" := (sb G_s).
Notation "'rf_s'" := (rf G_s).
Notation "'co_s'" := (co G_s).
Notation "'rmw_s'" := (rmw G_s).
Notation "'rpo_s'" := (rpo G_s).
Notation "'rmw_dep_s'" := (rmw_dep G_s).
Notation "'data_s'" := (data G_s).
Notation "'ctrl_s'" := (ctrl G_s).
Notation "'addr_s'" := (addr G_s).
Notation "'W_s'" := (fun x => is_true (is_w lab_s x)).
Notation "'R_s'" := (fun x => is_true (is_r lab_s x)).
Notation "'F_s'" := (F G_s).

Notation "'Tid_' t" := (fun e => tid e = t) (at level 1).

Lemma simrel_step_e e l
    (NINIT1 : t_1 <> tid_init)
    (NINIT2 : t_2 <> tid_init)
    (THRDNEQ : t_1 <> t_2)
    (SIMREL : seq_simrel X_s X_t t_1 t_2 mapper)
    (STEP : WCore.exec_inst X_t X_t' e l) :
  exists mapper' X_s',
    << SIMREL : seq_simrel X_s' X_t' t_1 t_2 mapper' >> /\
    << STEP : WCore.exec_inst X_s X_s' (mapper' e) l >>.
Proof using.
  admit.
Admitted.

End SimrelStep.
