# Independent audit: accepted corrected mathematical results

**PASS**, completed12October2026, for exact commit
`4c16b6a8a6d208795f6e099bc2df534923d22958`, tree
`3dd51cd13c57fcce3b5b5bcd2851fab9299ce941`.

- [Readable report](REPORT.md)
- [Exact-hash machine verdict](verdict.json)
- [Semantic findings and scope](semantic-findings.md)
- [Commands and verification boundaries](COMMANDS.md)
- [Exact terminal CI receipt](terminal-ci-receipt.json)
- [Full compressed evidence](evidence.tar.gz), SHA256
  `66e578a69d0e38db857398153ba506be968e453c59c0b87dbbc3b43919ef1332`
- [Evidence file manifest](artifact-manifest.json)

The accepted corrected results include the Theorem4 terminal range
T<=N^(2/3)exp(-32(log N)^(3/4)). The report explicitly retains finite-weight,
positive-depth and at-least-two-terminal domains, the sufficient alternative
Lemma3 bound, the corrected Lemma5 leaf inclusion and the absence of a runtime
claim. It does not certify the superseded stronger Theorem4 conclusion or
every literal original helper/proof sentence.

Exact CI38189023870 passed00:58:53UTC: all build/index/audit/replay stages,
2,074 paper declarations and150 unique project replays including116 paper
modules. The audit traversed49,287 checked constants, found no unsafe proof
dependencies, checked all1,743 project theorem closures, freshly elaborated19
selected sources, replayed12 selected modules, and replayed the entire45,841-
constant uniform-dimension proof closure into an empty kernel environment.
Three generated partial computational helpers occur in no project theorem
closure. Only propext,Classical.choice,Quot.sound are used as axioms.

This directory publishes the auditor's frozen results without changing them.
The containing documentation successor is not the audited commit; its full CI
is a separate status. All116 mathematical modules remain byte-identical.
F1 is a nonblocking stale-header underclaim; no proof fix was required.
The complete evidence archive contains raw logs, declaration/body inventories,
dependency hashes, source extracts and supplemental checker programs. Extract
it before following paths named in the detailed report or commands.
