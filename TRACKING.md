## Outline

* This document lists planned proofs.
* A checkmark next to an item means that the item is finished and present in the `main` branch
* A **username** next to an item means that it is being actively worked on
* Lack of a **username** next to an item means that it is not being actively worked on

## Features

- [x] [@keba4ok](https://www.github.com/keba4ok) Consistency admit for `src/reordering/ReorderingExecA.v` -- due 30.10 
- [x] [@keba4ok](https://www.github.com/keba4ok) Consistency admit for `src/reordering/ReorderingExecB.v` -- due 30.10 (both subcases are done)
- [ ] [@keba4ok](https://www.github.com/keba4ok) Consistency admit for `src/reordering/ReorderingExecNaNb.v` -- due 11.11 (largely overdue)
- [x] [@keba4ok](https://www.github.com/keba4ok) po-closure proof for `src/reordering/ReorderingExecA.v` -- due 6.11
- [ ] [@keba4ok](https://www.github.com/keba4ok) rpo-dom proof for `src/reordering/ReorderingExecA.v` -- due 11.11 (one admit left)
- [x] [@keba4ok](https://www.github.com/keba4ok) fix monotonicity def — use rhb instead of hb -- due 12.11
- [x] [@keba4ok](https://www.github.com/keba4ok) migrate consistency proofs into copy of main -- due 12.11
- [ ] [@InnocentusLime](https://www.github.com/InnocentusLime) Partial proof for `src/reordering/ReorderingExecReexec.v`
    * [ ] Consistency proof for the intermediate graph
    * [ ] Simulation relation for `G_s'` (done with minor admits)
    * [ ] Proof of the step (done with medium admits) -- new estimate 17.11 (minimum: proof with minor admits)
        - [x] Deploy the fix for the `StableUncommittedReads`, including the fixes of all proofs reasoning about it [commit](weakmemory/xmm/f9742bc1094d4b2bdffec5835afb889f9224afc1)
        - [x] Prove the inclusion of srf into the thrdle relation [commit](weakmemory/xmm/148c9e30a13db554e305380252be3949e712169b)
        - [x] Prove the inclusion of other `rf` edges (merge into `main` past this step)
        - [ ] Prove the well-formedness of the starting configuration
        - [ ] Prove all other conditions of the `re-execute` step
            - [ ] Commit-embeded up-to rpo [commit](https://github.com/weakmemory/xmm/commit/259a1698508bc26ffa74edc193c5dcff92a16d5b)
            - [ ] Add the new constraints and patch all lemmas up-to-rexec [commit1](https://github.com/weakmemory/xmm/commit/aaa3968807c1239e1496273ae67e82a1d518d401), [commit2](https://github.com/weakmemory/xmm/commit/e739362f70188d3259b694b08a877ce58a7320f8)
            - [ ] Prove the new constraint about act set [commit](https://github.com/weakmemory/xmm/commit/a7c242f8423800ba8c8b31e559ca9a085c6cc8ed)
            - [ ] Prove the new constraint about po-maximality of determined events
