# Remaining sourcewise construction: investigation, not a proved result

[Abboud–Bodwin, Section 2.1](https://arxiv.org/html/1710.11250v3#S2.SS1) supplies the relevant argument. 

1. Contract strongly connected components after adding internal in/out trees. Formalize lifting quotient paths using original arcs; charge at most twice the original vertex count. Deduplicate quotient demands and sources .
2. Choose a minimum-cardinality preserver on the quotient DAG. Prove every retained edge is required by some reachable demand, every demand walk must use it.
3. Prove the collision lemma: for a fixed demand and source, at most one pair of distinct required incoming edges can collide. Use acyclicity to justify the avoiding splice; handle a shared collision vertex.
4. Split by indegree at a positive integer d. Bound light edges by n*d. For each demand, inject competing incoming edges at its required heavy edges into sources, obtaining h*d ≤ |S|. Charge each heavy edge to one requiring demand; this yields at most |P|*|S|/d.
5. Optimize d and add the internal-tree budget, with empty cases explicit. Repeat via reversal to discharge both orientations.

These are outstanding proof contracts; no SCC, minimal-DAG, collision, or light-heavy theorem is certified by this checkpoint.
