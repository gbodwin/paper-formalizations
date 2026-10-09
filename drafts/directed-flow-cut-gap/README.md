# Directed flow-cut gap: unverified source snapshot

This branch preserves work in progress beyond the checked 90-module checkpoint
01804ff8e0b2d07dfbd76b89b62315f3d63a493a. The files here are source snapshots,
not a completed formalization or a verified release. Some have passed individual
checks and others have not compiled yet; this snapshot makes no claim about
any of their verification gates.

The `.lean.txt` extension keeps these drafts outside the built library and its
module index. Any CI result for this branch covers the checked library, not
these draft files. Restoring a draft requires removing the final `.txt`,
resolving its imports, and running fresh compilation, axiom, kernel and semantic
checks before including it in a checked checkpoint.

Only proof source and this concise status/hash manifest are included. The
checked development continues on `directed-flow-cut-checkpoints`.
