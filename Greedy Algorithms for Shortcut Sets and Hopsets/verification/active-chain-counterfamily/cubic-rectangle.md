# A direct cubic-saving rectangle in the active repair counterfamily

This is a separate informal lemma for the explicit family in near-maximum-obstruction.md. It is not a general progress theorem. Assume h>=4 and k>=12, and use the same empty-H graph and supplied chain cover.

Let v be the right child of the tree root, and consider its upward stretched edge with singleton vertices z_(v,1),...,z_(v,k). Put p=floor(k/3), q=floor(2k/3), and insert the legal closure edge e=(z_(v,p),z_(v,q)). Let R={z_(v,j):q<=j<=k}.

Let U contain every singleton stretch vertex z_(u,i) whose bottom tree node u lies in the left subtree and has global depth at least3. There are exactly sum_(d=3)^h 2^(d-1)=2^h-4 such upward edges, so |U|=k(2^h-4). Every s in U first reaches x_parent(u). That parent has the left child of the root as a strict ancestor, so its y vertex has a cross edge to y_v. Hence every s reaches every target in R. Each target is a singleton chain entry, so all pairs U x R are important and distinct.

Every original path from such an s to z_(v,j) must traverse y_v,z_(v,1),...,z_(v,j): there are no other incoming edges to these stretch vertices. The source is outside this stretched edge. In particular every minimum s-valid path contains the consecutive singleton block z_(v,p),...,z_(v,q). Replacing this block by e preserves validity, because its new entry target is a singleton chain. It removes exactly q-p-1 distinct chain visits. The source remains s throughout; no source-rebased optimality is asserted or used.

Therefore insertion of e lowers each important-pair distance in U x R by at least q-p-1. All other important distances are nonincreasing under legal insertion. The actual raw-potential drop is at least

    k(2^h-4) (k-q+1) (q-p-1).

For k>=12, k-q+1>=k/3 and q-p-1>=k/3-2>=k/6. For h>=4, 2^h-4>=2^(h-1). Hence the drop is at least 2^h*k^3/36.

The exact maximum important distance is L=h(k+1)+2<=2hk. Also h^3<=4*2^h for every h>=4: equality holds at h=4, and (h+1)^3<=2h^3 for h>=4 because, on writing h=4+a, 2h^3-(h+1)^3=a^3+9a^2+21a+3>=0. Induction proves the bound. Consequently

    L^3 <= 8h^3*k^3 <= 32*2^h*k^3,

and the actual raw-potential drop from this single legal edge is at least L^3/1152.

Thus the near-maximum hereditary repair can fail while a cubic saving comes from many shorter source paths on side branches. Padding by isolated uncovered vertices does not change this rectangle or its raw-potential savings. This identifies a source-multiplicity mechanism worth seeking in the general proof, but proves it only for this counterfamily.

The independent executable check check-active-tree-cubic-rectangle.py recomputes all original selectors and all important distances before and after this one edge. It checks the full raw drop, every charged pair, exact source count and the cubic lower bound for (h,k)=(4,12),(4,16),(5,32). All three satisfy the active inequality after the stated padding. This is diagnostic evidence for the symbolic argument, not a Lean formalization.
