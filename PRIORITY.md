# Attribution and priority evidence

This record describes the pre-submission search conducted on 22 November 2026 (Asia/Shanghai). The prize catalogue identifies the entry as JSP-000237. Its mathematical statement corresponds to Erdős problem 278.

| Evidence | What it establishes |
| --- | --- |
| [Pinned prize catalogue](https://github.com/TheJustinSunPrize/awards/blob/7782c2aa02df745da60d53e61718b714f8685a98/problems/catalog-0201-0300.md#JSP-000237) | The entry asks for both extrema. On the audited revision its status is Open, Lean proof is No, and eligibility is No. |
| [Original question as quoted by Cambie, §1](https://arxiv.org/html/2508.18270v2) | The zero-residue minimum is classical. Rogers' result appeared in Halberstam and Roth, *Sequences* (1966), and Simpson's 1986 Lemma 2.3 gives it by inclusion–exclusion. Cambie explains why a useful general description of the other extremum is a substantive question. |
| [Alper Ferudun, 2 September 2026](https://eulersolve.org/papers/ep-278/) | Earlier general characterization of the greatest density using compatibility graphs and an algorithm with parameter the number of moduli. |
| [Yoshiharu Onishi, formal scope at commit 66ff46ad](https://github.com/yoshiyoyoyo44/erdos278/blob/66ff46ad30c302a0fcc19a2fb22d58a87eebf2cb/FORMALIZATION.md) and [main theorem](https://github.com/yoshiyoyoyo44/erdos278/blob/66ff46ad30c302a0fcc19a2fb22d58a87eebf2cb/Erdos278/Main.lean) | The September 2026 release already formalized an attained maximum for arbitrary positive moduli with the natural-density limit. Its main theorem uses a graph/model optimization. Its published theorem map covers the maximum. |
| [Michael Schroeder, 22 September 2026](https://michaelschroeder.ai/research/Erdos278/companion) | Earlier formulas, complexity results and a scoped Lean companion for maximum covered density. |
| [Prize PR 3491](https://github.com/TheJustinSunPrize/awards/pull/3491) | The PR text identifies JSP-000237 with Erdős **237** and points to `Erdos237.lean`. That is a different problem. This closed PR does not supply the congruence-density theorem. |

Before this submission, a GitHub issue and pull-request search in the official repository for the literal identifier `"JSP-000237"` returned PR 3491. The search also covered public repository names matching `erdos278`, `erdos-278`, and `erdos 278 lean`. Different names can escape these searches. Among the materials listed above, the audit found earlier formal work on the maximum. It found no earlier single Lean package establishing both the digit formula for the complete histogram and the Rogers minimum for every finite family.

The user initiated this research, and OpenAI Codex developed the six Lean modules. The proposed contribution is the formalization of both extrema together with a formula in the moduli alone for the complete histogram. The formula follows from weighted inclusion–exclusion. Historical priority for the identity itself is outside the scope of this audit.

The public submission identifies the original Lean commit and links the English manuscript. The committee assesses the adequacy of a $2^L$ formula, the scope of earlier proofs, priority, and eligibility under its rules. [Original Lean commit](https://github.com/jackanderson123456/jsp000237-lean/commit/717bb98f744ba6f17c662dfbfe1134aa5ad5d1de) · [Prize PR #5626](https://github.com/TheJustinSunPrize/awards/pull/5626) · [Award process at the audited revision](https://github.com/TheJustinSunPrize/awards/blob/7782c2aa02df745da60d53e61718b714f8685a98/docs/award-process.md)
