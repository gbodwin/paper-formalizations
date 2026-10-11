import MinorFreeSpanners.CleanStarState

/-! Exact original-vertex accounting for full branch partitions. Together
with the actual contraction count, one size-k branch forces every other
branch of a one-star contraction to be a literal singleton. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace MinorModel
variable {I V : Type*} [Fintype I] [Fintype V]
variable {F : SimpleGraph I} {G : SimpleGraph V}

theorem cover_card_eq_sum (M : MinorModel F G) (hM : M.Covers) :
    (∑ i, (M.branch i).toFinset.card)=Fintype.card V := by
  classical
  let f : (Σ i, M.branch i) → V := fun x => x.2.val
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i,x⟩ ⟨j,y⟩ he
      have hxy : x.val=y.val := he
      have hij := M.branch_unique x.property (hxy ▸ y.property)
      subst j
      have h : x=y := Subtype.ext hxy
      subst y
      rfl
    · intro x
      obtain ⟨i,hi⟩ := hM x
      exact ⟨⟨i,⟨x,hi⟩⟩,rfl⟩
  have hh := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa only [Fintype.card_sigma,Set.toFinset_card] using hh

/-- Equality in the complete branch-count budget leaves no room for a
second nonsingleton branch. -/
theorem other_branch_card_one (M : MinorModel F G) (hM : M.Covers)
    (u : I) (r : ℕ) (hr : (M.branch u).toFinset.card=r)
    (hcount : Fintype.card I+r=Fintype.card V+1)
    (j : I) (hju : j ≠ u) : (M.branch j).toFinset.card=1 := by
  classical
  have hpos : ∀ i, 1 ≤ (M.branch i).toFinset.card := fun i =>
    Finset.card_pos.mpr (Set.toFinset_nonempty.mpr (M.nonempty i))
  have hs := Finset.sum_erase_add (Finset.univ : Finset I)
    (fun i => (M.branch i).toFinset.card) (Finset.mem_univ u)
  rw [M.cover_card_eq_sum hM,hr] at hs
  have hI : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨u⟩
  by_contra hn
  have hj2 : 1 < (M.branch j).toFinset.card := by have := hpos j; omega
  have hlt := Finset.sum_lt_sum (s := (Finset.univ : Finset I).erase u)
    (f := fun _ => (1:ℕ)) (g := fun i => (M.branch i).toFinset.card)
    (fun i _ => hpos i) ⟨j,Finset.mem_erase.mpr ⟨hju,Finset.mem_univ _⟩,hj2⟩
  simp only [Finset.sum_const,smul_eq_mul,mul_one,Finset.card_erase_of_mem,
    Finset.mem_univ,Finset.card_univ] at hlt
  omega

theorem other_branch_singleton (M : MinorModel F G) (hM : M.Covers)
    (u : I) (r : ℕ) (hr : (M.branch u).toFinset.card=r)
    (hcount : Fintype.card I+r=Fintype.card V+1)
    (j : I) (hju : j ≠ u) : ∃ x : V, M.branch j={x} := by
  classical
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp (M.other_branch_card_one hM u r hr hcount j hju)
  refine ⟨x,?_⟩
  ext y
  have he := congrArg (fun S : Finset V => y ∈ S) hx
  simpa only [Set.mem_toFinset,Finset.mem_singleton,Set.mem_singleton_iff] using (eq_iff_iff.mp he)

end MinorModel

/-- A state grown from the uncontracted host is exactly one nontrivial
star branch, with every other original vertex a singleton. -/
theorem CleanStarState.other_singleton {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k r E : ℕ} {c : V} {T : Finset V} {q : ℝ}
    (s : CleanStarState G k c T q (Fintype.card V) E r)
    (j : s.Index) (hj : j ≠ s.center) : ∃ x : V, s.model.branch j={x} :=
  s.model.other_branch_singleton s.covers s.center r s.center_card s.vertex_count j hj

/-- Every noncenter vertex in the grown branch is an actual original
neighbor of its center. Extra host edges among leaves are allowed. -/
theorem CleanStarState.center_adj {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k r N E : ℕ} {c : V} {T : Finset V} {q : ℝ}
    (s : CleanStarState G k c T q N E r)
    (hadj : ∀ x ∈ T, G.Adj c x) {x : V}
    (hx : x ∈ s.model.branch s.center) (hxc : x ≠ c) : G.Adj c x := by
  rcases s.center_subset hx with he | hT
  · exact (hxc he).elim
  · exact hadj x hT

/-- The literal leaf set contains exactly r-1 distinct original vertices. -/
theorem CleanStarState.leaf_card {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k r N E : ℕ} {c : V} {T : Finset V} {q : ℝ}
    (s : CleanStarState G k c T q N E r) :
    ((s.model.branch s.center).toFinset.erase c).card+1=r := by
  classical
  rw [Finset.card_erase_of_mem (Set.mem_toFinset.mpr s.center_mem),s.center_card]
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt s.positive)

end MinorFreeSpanners
