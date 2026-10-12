import MinorFreeSpanners.MinimalBranchingCore

/-! Internally selected disjoint branching cores. Every large remaining
connected set has internal degree at most two, so only path-like cases remain. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 def BranchingCore {V : Type*} (G : SimpleGraph V) (d : V → ℝ) (L D : ℝ)
    (S : Finset V) : Prop :=
    ConnectedWithin G S ∧
    (∃ x,∃ N : Finset V,3≤N.card ∧ (∀ y∈N,G.Adj x y) ∧ insert x N⊆S) ∧
    (∃ a b,∃ p : G.Walk a b,p.IsPath ∧ (∀ v∈p.support,v∈S) ∧ L≤pathMass d p) ∧
    (∀ a b,∀ p : G.Walk a b,p.IsPath →
      (∀ v∈p.support,v∈S) → pathMass d p≤L+D)

 theorem exists_branching_core_packing {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) (d : V → ℝ) (L D : ℝ)
    (hD : 0≤D) (hLD : 3*D<L) (hdpos : ∀ v,0<d v) (hd : ∀ v,d v≤D) :
    ∃ P : Finset (Finset V),
      (∀ S∈P,BranchingCore G d L D S) ∧
      (∀ S∈P,∀ T∈P,S≠T → Disjoint S T) ∧
      (∀ W : Finset V,ConnectedWithin G W → Disjoint W (P.biUnion id) →
        (∃ a b,∃ p : G.Walk a b,p.IsPath ∧ (∀ v∈p.support,v∈W) ∧ L≤pathMass d p) →
        ∀ x∈W,((G.neighborFinset x)∩W).card≤2) := by
  classical
  let good (P : Finset (Finset V)) :=
    (∀ S∈P,BranchingCore G d L D S) ∧
    (∀ S∈P,∀ T∈P,S≠T → Disjoint S T)
  let candidates := (Finset.univ : Finset (Finset (Finset V))).filter good
  have h0 : (∅ : Finset (Finset V))∈candidates := by simp [candidates,good]
  obtain ⟨P,hPc,hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨_,h0⟩
  have hP := (Finset.mem_filter.mp hPc).2
  refine ⟨P,hP.1,hP.2,?_⟩
  intro W hW hdis hlarge x hx
  by_contra hn
  let N := G.neighborFinset x∩W
  have hN : ∀ y∈N,G.Adj x y := fun y hy => (G.mem_neighborFinset x y).mp (Finset.mem_inter.mp hy).1
  have hNW : insert x N⊆W := Finset.insert_subset hx Finset.inter_subset_right
  obtain ⟨S,hSW,hNS,hS,hLS,hbound,_⟩ := exists_bounded_branching_core G hG W hW x N hN
    (by dsimp [N];omega) hNW d L D hD hLD (fun v _ => hdpos v) (fun v _ => hd v) hlarge
  have hcore : BranchingCore G d L D S := ⟨hS,⟨x,N,by dsimp [N];omega,hN,hNS⟩,hLS,hbound⟩
  have hne : S.Nonempty := ⟨x,hNS (by simp)⟩
  have hnot : S∉P := by
    intro hs
    exact Finset.disjoint_left.mp hdis (hSW (hne.choose_spec))
      (Finset.mem_biUnion.mpr ⟨S,hs,hne.choose_spec⟩)
  have hdS (T : Finset V) (hT : T∈P) : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro v hv ht
    exact Finset.disjoint_left.mp hdis (hSW hv) (Finset.mem_biUnion.mpr ⟨T,hT,ht⟩)
  have hnew : good (insert S P) := by
    constructor
    · intro T hT
      rcases Finset.mem_insert.mp hT with rfl|hT
      · exact hcore
      · exact hP.1 T hT
    · intro T hT U hU hneTU
      rcases Finset.mem_insert.mp hT with he|hTP
      · subst T
        rcases Finset.mem_insert.mp hU with he|hUP
        · exact (hneTU he.symm).elim
        · exact hdS U hUP
      · rcases Finset.mem_insert.mp hU with he|hUP
        · subst U
          exact (hdS T hTP).symm
        · exact hP.2 T hTP U hUP hneTU
  have hm := hmax (insert S P) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnew⟩)
  rw [Finset.card_insert_of_notMem hnot] at hm
  omega

end MinorFreeSpanners
