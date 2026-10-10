import LightSpanners.MonotonePadding
import LightSpanners.PaddingPositions

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- A nonempty extra-safe k-path generates a finite family of safe k-paths
with the same chord word and pairwise distinct actual endpoints. The family
size pays for its first chord. -/
theorem useful_family {eps : ℝ} {k : ℕ} {u v : V} {p : G.Walk u v}
    (heps : 0<eps) (hk : 0<k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k)))
    (hp : C.BucketMonotoneKPath eps k true p) :
    ∃ (e : Sym2 V) (es : List (Sym2 V)) (N : ℕ) (f : Fin N → V × V),
      C.chordEdges p=e::es ∧ Function.Injective f ∧ eps*w e/4≤N ∧
      ∀ a, ∃ q : G.Walk (f a).1 (f a).2,
        C.BucketMonotoneKPath eps k false q ∧ C.chordEdges q=C.chordEdges p := by
  obtain ⟨hcount,J,hp⟩ := hp
  obtain ⟨e,es,hword⟩ := List.exists_cons_of_ne_nil (show C.chordEdges p≠[] by
    intro hh
    rw [hh,List.length_nil] at hcount
    omega)
  obtain ⟨j,hj,hlo,hhi,hmin⟩ := hp.first_bucket C hword
  let t := ⌊eps*k*2^j/2⌋₊
  have ht : (t:ℝ)≤eps*k*2^j/2 := Nat.floor_le (by positivity)
  have hedge : e∈p.edges ∧ e∉C.cycle.edges := by
    have he : e∈C.chordEdges p := by simp [hword]
    simpa [chordEdges] using he
  have htn : t<Fintype.card V := C.bucket_padding_lt_card heps hk hG
    (p.edges_subset_edgeSet hedge.1) hedge.2 hlo ht
  let f : Fin (t+1) → V×V := fun a =>
    ((C.successor.symm : V → V)^[a.val] u,(C.successor.symm : V → V)^[a.val] v)
  refine ⟨e,es,t+1,f,hword,?_,?_,?_⟩
  · intro a b hab
    apply Fin.ext
    exact C.backward_iterate_injective u (by omega) (by omega) (congrArg Prod.fst hab)
  · have hkr : (1:ℝ)≤k := by exact_mod_cast hk
    have hf : eps*k*2^j/2<(t:ℝ)+1 := Nat.lt_floor_add_one _
    have hw : eps*w e/4<eps*2^j/2 := by
      have hm := mul_lt_mul_of_pos_left hhi heps
      rw [pow_succ] at hm
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hkr (by positivity : (0:ℝ)≤eps*2^j/2)
    push_cast
    nlinarith
  · intro a
    have ha : (a.val:ℝ)≤eps*k*2^j/2 :=
      (show (a.val:ℝ)≤t by exact_mod_cast (show a.val≤t by omega)).trans ht
    obtain ⟨q,hq,hqw⟩ := hp.pad_above C heps.le hmin ha
    exact ⟨q,⟨by rwa [hqw],J,hq⟩,hqw⟩

end LightSpanners.UnitSpanningCycle
