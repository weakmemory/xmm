## Outline

* This document lists planned proofs.
* A checkmark next to an item means that the item is finished and present in the `main` branch
* A **username** next to an item means that it is being actively worked on
* Lack of a **username** next to an item means that it is not being actively worked on

## Features

- [x] [@keba4ok](https://www.github.com/keba4ok) Consistency admit for `src/reordering/ReorderingExecA.v` -- due 30.10
- [x] [@keba4ok](https://www.github.com/keba4ok) Consistency admit for `src/reordering/ReorderingExecB.v` -- due 30.10 (both subcases are done)
- [x] [@keba4ok](https://www.github.com/keba4ok) Consistency admit for `src/reordering/ReorderingExecNaNb.v` -- due 11.11 (largely overdue)
- [x] [@keba4ok](https://www.github.com/keba4ok) po-closure proof for `src/reordering/ReorderingExecA.v` -- due 6.11
- [x] [@keba4ok](https://www.github.com/keba4ok) rpo-dom proof for `src/reordering/ReorderingExecA.v` -- due 11.11 (one admit left)
- [x] [@keba4ok](https://www.github.com/keba4ok) fix monotonicity def — use rhb instead of hb -- due 12.11
- [x] [@keba4ok](https://www.github.com/keba4ok) migrate consistency proofs into copy of main -- due 12.11
- [ ] [@InnocentusLime](https://www.github.com/InnocentusLime) Partial proof for `src/reordering/ReorderingExecReexec.v`
    * [x] vf ; sb equality between `G_s''` and `G_s'` (done with minor admits)
    * [x] Simulation relation for `G_s'` (done with minor admits)
    * [x] Full admitless proof of the simulation relation for `G_s'`
    * [x] Provide a universal rhb nesting for source graph
    * [x] Proof of the step (done with medium admits) -- new estimate N/A (minimum: proof with minor admits)
        - [x] Deploy the fix for the `StableUncommittedReads`, including the fixes of all proofs reasoning about it [commit](weakmemory/xmm/f9742bc1094d4b2bdffec5835afb889f9224afc1)
        - [x] Prove the inclusion of srf into the thrdle relation [commit](weakmemory/xmm/148c9e30a13db554e305380252be3949e712169b)
        - [x] Prove the inclusion of other `rf` edges (merge into `main` past this step)
        - [x] Prove the well-formedness of the starting configuration
        - [x] Prove all other conditions of the `re-execute` step
            - [x] Commit-embeded up-to rpo [commit](https://github.com/weakmemory/xmm/commit/259a1698508bc26ffa74edc193c5dcff92a16d5b)
            - [x] Add the new constraints and patch all lemmas up-to-rexec [commit1](https://github.com/weakmemory/xmm/commit/aaa3968807c1239e1496273ae67e82a1d518d401), [commit2](https://github.com/weakmemory/xmm/commit/e739362f70188d3259b694b08a877ce58a7320f8)
            - [x] Prove the new constraint about act set [commit](https://github.com/weakmemory/xmm/commit/a7c242f8423800ba8c8b31e559ca9a085c6cc8ed)
            - [x] Prove the new constraint about po-maximality of determined events
- [ ] Full Reordering Proof
    - [x] Universal `src/reordering/Reordering.v:simrel_xmm_step` lemma
    - [x] [@InnocentusLime](https://www.github.com/InnocentusLime) Full `Theorem` (this would be the master theorem that uses `simrel_xmm_step` in its proof)
        * The theorem itself should be `Qed`'d with the only `admit`'d fact being the `simrel_xmm_step` lemma.
    - [ ] Proper constraint of the trace family for `G_s'`
    - Constraints of the current result
        * `a` and `b` must have static indices in both source and target graphs
        * `rmw` operations are considered to be in SC mode
        * Both source and target are finite graphs
        * both `a` and `b` are at most relaxed
- [ ] [@InnocentusLime](https://www.github.com/InnocentusLime) Document constraints
    - The main foundational constaints should be converted into `Hypothesis` declarations
    - Each hypothesis should be followed by a comment

## Admits in the re-execution step

The proof for the re-execution step itself has been successfully `Qed`. The only thing left to do is to proof the admitted statements:

- [ ] dtrmt_in_cmt (dtrmt_s ⊆ cmt_s)
- [ ] cmt_in_Es (cmt_s ⊆ E_s')
- [ ] dtrmt_in_Es (dtrmt_s ⊆ E_s)
- [ ] rex_dtrmt_init (is_init ⊆ dtrmt_s)
- [ ] Infer from `forall e : actid,
E_t' e -> tid e = tid b_t -> cmt_t e` that b_t is determined (aka, if all events in a thread are comitted => then all events are determined).
- [ ] `MAP : mapper ↑ vf_rhb_t' ⨾ same_tid ⨾ mapper ↑ ⦗E_t' \₁ cmt_t⦘ ⊆ mapper ↑ (vf_rhb_t' ⨾ same_tid ⨾ ⦗E_t' \₁ cmt_t⦘)` -- some algebraic juggling of mapper
- [ ] The final steps of `rsr_rex_vf` (they are obvious)
- [ ] Cases in `reexec_threads_s`
- [ ] `imm_sb_d_s` -- the lemma about po-max of dtmtr_s
- [ ] po-closure of `dtrmt_s` in `G_s`
- [ ] Its corollary -- the same thing but about `G_s'`
- [ ] Proof that `G_s` restricted by `dtrmt_s` is a prefix of `G_s'`
- [ ] `commit_embedded` predicate
- [x] Various relations hacks in `rsr_rex_crfc_vf`
    - [x] `arewrite` 1
    - [x] `arewrite` 2
    - [x] `arewrite` 3
    - [x] "determined event from target reads from a comitted event"
- [x] In `rsr_rex_crfc_helper` show that if `b_t` is determined in target, but `a_t` is absent from `G_t'` -- then all events before `a_s'` (extra a) are actually determined