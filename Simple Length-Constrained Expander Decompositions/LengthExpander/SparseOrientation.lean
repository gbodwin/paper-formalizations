import LengthExpander.SparseOrder
import Mathlib.Data.List.Basic

/-! The proved elimination order orients each edge from its earlier endpoint
to its later endpoint, with at most K outgoing edges per vertex. Incoming
children can therefore be paired without a rooted-forest oracle. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} {G : SimpleGraph V}

noncomputable def laterNeighbors (G : SimpleGraph V) (L : List V) (u : V) : Finset V := by
  classical
  exact L.toFinset.filter (fun v => G.Adj u v ∧ L.idxOf u < L.idxOf v)

theorem sparseOrder_later_card {K : ℕ} {L : List V}
    (hL : SparseOrder G K L) {u : V} (hu : u ∈ L) :
    (laterNeighbors G L u).card ≤ K := by
  classical
  induction hL with
  | nil => simp at hu
  | cons v L horder hdeg ih =>
    by_cases huv : u = v
    · subst u
      apply (card_le_card (t := L.toFinset.filter (G.Adj v)) ?_).trans hdeg
      intro z hz
      obtain ⟨hz,hvz,hi⟩ := mem_filter.mp hz
      have hzv : z ≠ v := fun he => by subst z; exact Nat.lt_irrefl _ hi
      exact mem_filter.mpr ⟨by simpa [hzv] using hz,hvz⟩
    · have huL : u ∈ L := (List.mem_cons.mp hu).resolve_left huv
      apply (card_le_card (t := laterNeighbors G L u) ?_).trans (ih huL)
      intro z hz
      obtain ⟨hz,huz,hi⟩ := mem_filter.mp hz
      have hzv : z ≠ v := by
        intro he
        subst z
        simpa using hi
      apply mem_filter.mpr
      refine ⟨by simpa [hzv] using hz,huz,?_⟩
      simpa only [List.idxOf_cons_ne L (Ne.symm huv),List.idxOf_cons_ne L (Ne.symm hzv),Nat.succ_lt_succ_iff] using hi

variable [Fintype V]

noncomputable def orientationChildren (G : SimpleGraph V) (L : List V) (p : V) : Finset V := by
  classical
  exact univ.filter (fun u => G.Adj u p ∧ L.idxOf u < L.idxOf p)

@[simp] theorem mem_orientationChildren {L : List V} {p u : V} :
    u ∈ orientationChildren G L p ↔ G.Adj u p ∧ L.idxOf u < L.idxOf p := by
  classical
  simp [orientationChildren]

theorem orientationChildren_no_self (L : List V) (p : V) : p ∉ orientationChildren G L p := by
  simp

theorem orientationChildren_budget {K : ℕ} {L : List V}
    (hL : SparseOrder G K L) (hcover : L.toFinset = univ) (u : V) :
    (univ.filter (fun p => u ∈ orientationChildren G L p)).card ≤ K := by
  classical
  have hset : univ.filter (fun p => u ∈ orientationChildren G L p) = laterNeighbors G L u := by
    ext p
    simp [laterNeighbors,hcover]
  rw [hset]
  apply sparseOrder_later_card hL
  have : u ∈ L.toFinset := hcover.symm ▸ mem_univ u
  exact List.mem_toFinset.mp this

abbrev OrientedUnits (G : SimpleGraph V) (L : List V) := (p : V) × orientationChildren G L p

noncomputable def orientedEdgeEquiv (G : SimpleGraph V) (L : List V)
    (hcover : L.toFinset = univ) : OrientedUnits G L ≃ G.edgeSet := by
  classical
  apply Equiv.ofBijective (fun t => ⟨s((t.2 : V),t.1),(mem_orientationChildren.mp t.2.property).1⟩)
  constructor
  · intro t u he
    have he' := congrArg Subtype.val he
    have ht := (mem_orientationChildren.mp t.2.property).2
    have hu := (mem_orientationChildren.mp u.2.property).2
    rcases Sym2.eq_iff.mp he' with he | he
    · rcases t with ⟨p,t⟩
      rcases u with ⟨q,u⟩
      dsimp at he
      rcases he with ⟨he,hpq⟩
      subst q
      have htu : t = u := Subtype.ext he
      subst u
      rfl
    · have hh : L.idxOf (t.2 : V) = L.idxOf u.1 := congrArg L.idxOf he.1
      have hh' : L.idxOf t.1 = L.idxOf (u.2 : V) := congrArg L.idxOf he.2
      omega
  · intro e
    obtain ⟨⟨x,y⟩,hxy⟩ := e
    have hx : x ∈ L := List.mem_toFinset.mp (hcover.symm ▸ mem_univ x)
    have hy : y ∈ L := List.mem_toFinset.mp (hcover.symm ▸ mem_univ y)
    have hne : L.idxOf x ≠ L.idxOf y := fun he => hxy.ne ((List.idxOf_inj hx).mp he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨⟨y,⟨x,mem_orientationChildren.mpr ⟨hxy,hlt⟩⟩⟩,rfl⟩
    · refine ⟨⟨x,⟨y,mem_orientationChildren.mpr ⟨hxy.symm,hgt⟩⟩⟩,?_⟩
      exact Subtype.ext (Sym2.eq_swap)

theorem orientationChildren_total (G : SimpleGraph V) (L : List V)
    (hcover : L.toFinset = univ) :
    ∑ p, (orientationChildren G L p).card = Fintype.card G.edgeSet := by
  classical
  have hc := Fintype.card_congr (orientedEdgeEquiv G L hcover)
  rw [show Fintype.card (OrientedUnits G L) = ∑ p, Fintype.card (orientationChildren G L p) from Fintype.card_sigma] at hc
  simpa only [Fintype.card_coe] using hc

end LengthExpander
