import MinorFreeSpanners.MateFreeSets
import Mathlib.Data.Finset.Max

/-! Actual finite selection of a maximum bounded induced-star packing.
The alternating-augmentation and Postle density alternatives remain separate. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Centers lie in B; leaves lie in A. Different centers have disjoint leaf
sets, and each individual leaf set is independent in the actual host. -/
def IsStarPacking (G : SimpleGraph V) (A B : Finset V) (ell : ℕ)
    (L : V → Finset V) : Prop :=
  (∀ b, b ∉ B → L b = ∅) ∧
  (∀ b, L b ⊆ A) ∧
  (∀ b a, a ∈ L b → G.Adj b a) ∧
  (∀ b x, x ∈ L b → ∀ y, y ∈ L b → x ≠ y → ¬ G.Adj x y) ∧
  (∀ b c, b ≠ c → Disjoint (L b) (L c)) ∧
  ∀ b, (L b).card ≤ ell

noncomputable def starPackingSize (B : Finset V) (L : V → Finset V) : ℕ :=
  (B.biUnion L).card

omit [Fintype V] [DecidableEq V] in
/-- The empty assignment is a literal valid packing for every domain. -/
theorem empty_star_packing (G : SimpleGraph V) (A B : Finset V) (ell : ℕ) :
    IsStarPacking G A B ell (fun _ => ∅) := by
  simp [IsStarPacking]

/-- Finiteness constructs the maximum; maximality is not an input oracle. -/
theorem exists_maximum_star_packing (G : SimpleGraph V) (A B : Finset V) (ell : ℕ) :
    ∃ L : V → Finset V, IsStarPacking G A B ell L ∧
      ∀ L', IsStarPacking G A B ell L' → starPackingSize B L' ≤ starPackingSize B L := by
  classical
  let P := (Finset.univ : Finset (V → Finset V)).filter (IsStarPacking G A B ell)
  have hP : P.Nonempty := ⟨fun _ => ∅,by simp [P,empty_star_packing]⟩
  obtain ⟨L,hL,hmax⟩ := Finset.exists_max_image P (starPackingSize B) hP
  refine ⟨L,(Finset.mem_filter.mp hL).2,?_⟩
  intro L' hL'
  exact hmax L' (by simp [P,hL'])

omit [Fintype V] in
/-- The occupied leaf set is an actual subset of A. -/
theorem IsStarPacking.covered_subset {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L) :
    B.biUnion L ⊆ A := by
  intro x hx
  obtain ⟨b,_,hx⟩ := Finset.mem_biUnion.mp hx
  exact h.2.1 b hx

omit [Fintype V] in
/-- The actual selected leaf count is at most ell times the number of centers. -/
theorem IsStarPacking.size_le {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L) :
    starPackingSize B L ≤ ell*B.card := by
  classical
  calc
    _ ≤ ∑ b ∈ B, (L b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ B, ell := Finset.sum_le_sum (fun b _ => h.2.2.2.2.2 b)
    _ = _ := by simp [Nat.mul_comm]

omit [Fintype V] in
/-- Add one genuinely unused compatible leaf at a center with spare capacity. -/
theorem IsStarPacking.insert_leaf {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L)
    {b x : V} (hb : b ∈ B) (hx : x ∈ A) (he : G.Adj b x)
    (hnew : ∀ c, x ∉ L c) (hcompat : ∀ y ∈ L b, ¬ G.Adj x y)
    (hroom : (L b).card < ell) :
    IsStarPacking G A B ell (Function.update L b (insert x (L b))) := by
  classical
  rcases h with ⟨hzero,hsub,hadj,hind,hdisj,hcard⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro c hc
    have hcb : c ≠ b := fun e => hc (e ▸ hb)
    simpa [Function.update_of_ne hcb] using hzero c hc
  · intro c
    by_cases hcb : c=b
    · subst c; simpa using Finset.insert_subset hx (hsub b)
    · simpa [Function.update_of_ne hcb] using hsub c
  · intro c y hy
    by_cases hcb : c=b
    · subst c
      simp only [Function.update_self,Finset.mem_insert] at hy
      rcases hy with rfl|hy
      · exact he
      · exact hadj b y hy
    · exact hadj c y (by simpa [Function.update_of_ne hcb] using hy)
  · intro c y hy z hz hyz
    by_cases hcb : c=b
    · subst c
      simp only [Function.update_self,Finset.mem_insert] at hy hz
      rcases hy with rfl|hy <;> rcases hz with rfl|hz
      · exact (hyz rfl).elim
      · exact hcompat z hz
      · exact fun he => hcompat y hy he.symm
      · exact hind b y hy z hz hyz
    · exact hind c y (by simpa [Function.update_of_ne hcb] using hy)
        z (by simpa [Function.update_of_ne hcb] using hz) hyz
  · intro c d hcd
    apply Finset.disjoint_left.mpr
    intro y hyc hyd
    by_cases hcb : c=b
    · subst c
      have hdb : d ≠ b := Ne.symm hcd
      simp only [Function.update_self,Finset.mem_insert] at hyc
      have hyd' : y ∈ L d := by simpa [Function.update_of_ne hdb] using hyd
      rcases hyc with rfl|hyc
      · exact hnew d hyd'
      · exact Finset.disjoint_left.mp (hdisj b d hcd) hyc hyd'
    · have hyc' : y ∈ L c := by simpa [Function.update_of_ne hcb] using hyc
      by_cases hdb : d=b
      · subst d
        simp only [Function.update_self,Finset.mem_insert] at hyd
        rcases hyd with rfl|hyd
        · exact hnew c hyc'
        · exact Finset.disjoint_left.mp (hdisj c b hcd) hyc' hyd
      · exact Finset.disjoint_left.mp (hdisj c d hcd) hyc'
          (by simpa [Function.update_of_ne hdb] using hyd)
  · intro c
    by_cases hcb : c=b
    · subst c; simpa [Finset.card_insert_of_notMem (hnew b)] using hroom
    · simpa [Function.update_of_ne hcb] using hcard c

omit [Fintype V] in
/-- The selected union changes by precisely the inserted leaf. -/
theorem starPacking_insert_union {B : Finset V} {L : V → Finset V} {b x : V}
    (hb : b ∈ B) :
    B.biUnion (Function.update L b (insert x (L b))) = insert x (B.biUnion L) := by
  classical
  ext y
  simp only [Finset.mem_biUnion,Finset.mem_insert]
  constructor
  · rintro ⟨c,hc,hy⟩
    by_cases hcb : c=b
    · subst c
      simp only [Function.update_self,Finset.mem_insert] at hy
      exact hy.imp_right (fun hy => ⟨b,hb,hy⟩)
    · exact Or.inr ⟨c,hc,by simpa [Function.update_of_ne hcb] using hy⟩
  · rintro (rfl|⟨c,hc,hy⟩)
    · exact ⟨b,hb,by simp⟩
    · refine ⟨c,hc,?_⟩
      by_cases hcb : c=b
      · subst c; simpa using Finset.mem_insert_of_mem hy
      · simpa [Function.update_of_ne hcb] using hy

omit [Fintype V] in
/-- Global maximum size forces every compatible neighbor of an unused leaf
 to be full. This is the one-step augmentation, not the alternating-path lemma. -/
theorem maximum_star_packing_full {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L)
    (hmax : ∀ L', IsStarPacking G A B ell L' → starPackingSize B L' ≤ starPackingSize B L)
    {b x : V} (hb : b ∈ B) (hx : x ∈ A) (he : G.Adj b x)
    (hnew : x ∉ B.biUnion L) (hcompat : ∀ y ∈ L b, ¬ G.Adj x y) :
    (L b).card = ell := by
  classical
  apply Nat.le_antisymm (h.2.2.2.2.2 b)
  by_contra hlt
  have hroom : (L b).card < ell := by omega
  have hn : ∀ c, x ∉ L c := by
    intro c hc
    by_cases hcB : c ∈ B
    · exact hnew (Finset.mem_biUnion.mpr ⟨c,hcB,hc⟩)
    · simp [h.1 c hcB] at hc
  have hi := h.insert_leaf hb hx he hn hcompat hroom
  have hm := hmax _ hi
  rw [starPackingSize,starPacking_insert_union hb,Finset.card_insert_of_notMem hnew] at hm
  unfold starPackingSize at hm
  omega

end MinorFreeSpanners
