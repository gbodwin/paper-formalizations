import GreedyShortcuts.UniformChainPacking
import GreedyShortcuts.ChainCover

/-! Constructing the finite chain-cover guarantee by maximal packing.
No caller-supplied cover property or fast cover algorithm is assumed. -/
namespace GreedyShortcuts.UniformChainPacking
open Finset SimpleGraph DirectedPaths CanonicalSegments ChainUnion ChainFirst ChainCover ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Any r distinct selected vertices on an original path form an actual
r-vertex reachability chain in their path order. -/
theorem extract_chain {G : V → V → Prop} {s t : V} (p : DWalk s t)
    (hp : Allowed G p) (hsimple : p.IsPath) (S : Finset V) (r : ℕ)
    (hmany : r ≤ (p.support.toFinset ∩ S).card) :
    ∃ c : FixedChain G r,c.chain.support ⊆ S := by
  classical
  let A := (Finset.range (p.length+1)).filter (fun j => p.getVert j∈S)
  have hcard : A.card=(p.support.toFinset ∩ S).card := by
    apply Finset.card_bij (fun j _ => p.getVert j)
    · intro j hj
      exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support j),
        (Finset.mem_filter.mp hj).2⟩
    · intro i hi j hj he
      have hiL : i ≤ p.length := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1;omega
      have hjL : j ≤ p.length := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1;omega
      exact hsimple.getVert_injOn hiL hjL he
    · intro x hx
      obtain ⟨j,hjx,hj⟩ := Walk.mem_support_iff_exists_getVert.mp
        (List.mem_toFinset.mp (Finset.mem_inter.mp hx).1)
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        by simpa only [hjx] using (Finset.mem_inter.mp hx).2⟩,hjx⟩
  obtain ⟨B,hBA,hB⟩ := Finset.exists_subset_card_eq (hmany.trans_eq hcard.symm)
  let e := B.orderEmbOfFin hB
  have heA (i : Fin r) : e i∈A := hBA (B.orderEmbOfFin_mem hB i)
  have heL (i : Fin r) : e i ≤ p.length := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp (heA i)).1;omega
  let f : Fin r → V := fun i => p.getVert (e i)
  have hf : Function.Injective f := by
    intro i j hij
    exact e.injective (hsimple.getVert_injOn (heL i) (heL j) hij)
  have hforward : ∀ i j,i < j → Reachable G (f i) (f j) := by
    intro i j hij
    exact ⟨segment p (e i) (e j) (e.strictMono hij).le,
      allowed_subwalk hp (segment_isSubwalk p _ _ _)⟩
  refine ⟨⟨f,hf,hforward⟩,?_⟩
  intro v hv
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
  exact (Finset.mem_filter.mp (heA i)).2

noncomputable def outside (G : V → V → Prop) (r : ℕ) : Finset V :=
  Finset.univ \ (packing G r).biUnion (fun c => c.chain.support)

theorem outside_path_lt {G : V → V → Prop} (r : ℕ) (hr : 0 < r)
    {s t : V} (p : DWalk s t) (hp : Allowed G p) (hsimple : p.IsPath) :
    (p.support.toFinset ∩ outside G r).card < r := by
  classical
  by_contra h
  obtain ⟨c,hc⟩ := extract_chain p hp hsimple (outside G r) r (by omega)
  have hd : ∀ d∈packing G r,Disjoint c.chain.support d.chain.support := by
    intro d hd
    apply Finset.disjoint_left.mpr
    intro v hvc hvd
    have hv := (Finset.mem_sdiff.mp (hc hvc)).2
    exact hv (Finset.mem_biUnion.mpr ⟨d,hd,hvd⟩)
  have hmem := mem_packing_of_disjoint G r c hd
  have hself := hd c hmem
  have hempty : c.chain.support=∅ := by simpa using hself
  have hz := c.chain.support_card
  rw [hempty,Finset.card_empty] at hz
  change 0=r at hz
  omega

noncomputable def context (G : V → V → Prop) (hG : Acyclic G)
    (r K : ℕ) (W : PathWitness r K) : ChainDistance.Context V {c // c∈packing G r} where
  G := G
  acyclic := hG
  chains := chains G r
  disjoint := chains_disjoint G r
  K := K
  witnesses := fun _ => W

theorem context_cover (G : V → V → Prop) (hG : Acyclic G)
    (r K : ℕ) (hr : 0 < r) (W : PathWitness r K) :
    IsCover (context G hG r K W) (r-1) := by
  classical
  intro s t p hp hsimple
  have hsub : uncovered (context G hG r K W) p ⊆ p.support.toFinset ∩ outside G r := by
    intro v hv
    have hh := Finset.mem_filter.mp hv
    refine Finset.mem_inter.mpr ⟨hh.1,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩⟩
    intro hcov
    obtain ⟨d,hd,hvd⟩ := Finset.mem_biUnion.mp hcov
    have hl := label_of_mem (chains G r) (chains_disjoint G r)
      (c:=⟨d,hd⟩) hvd
    have hnone : label (chains G r) v=none := hh.2
    rw [hl] at hnone
    cases hnone
  have hlt := (Finset.card_le_card hsub).trans_lt (outside_path_lt r hr p hp hsimple)
  omega

end GreedyShortcuts.UniformChainPacking
