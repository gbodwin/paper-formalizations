import LightSpanners.UsefulFamily
import LightSpanners.BucketDispersion

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Endpoint pairs of actual safe k-paths using only selected chords. -/
noncomputable def safeEndpoints (eps : ℝ) (k : ℕ) (S : Finset (Sym2 V)) : Finset (V×V) :=
  Finset.univ.filter fun a => ∃ p : G.Walk a.1 a.2,
    C.BucketMonotoneKPath eps k false p ∧ ∀ e∈C.chordEdges p,e∈S

@[simp] theorem mem_safeEndpoints {eps : ℝ} {k : ℕ} {S : Finset (Sym2 V)} {a : V×V} :
    a∈C.safeEndpoints eps k S ↔ ∃ p : G.Walk a.1 a.2,
      C.BucketMonotoneKPath eps k false p ∧ ∀ e∈C.chordEdges p,e∈S := by
  simp [safeEndpoints]

theorem safeEndpoints_mono {eps : ℝ} {k : ℕ} {S T : Finset (Sym2 V)} (hST : S⊆T) :
    C.safeEndpoints eps k S⊆C.safeEndpoints eps k T := by
  intro a ha
  obtain ⟨p,hp,hs⟩ := C.mem_safeEndpoints.mp ha
  exact C.mem_safeEndpoints.mpr ⟨p,hp,fun e he => hST (hs e he)⟩

/-- A useful family containing the deleted chord occupies new endpoint pairs.
Dispersion supplies the disjointness; no arbitrary path-choice injectivity is assumed. -/
theorem erase_chord_endpoint_gain {eps : ℝ} {k N : ℕ} {S : Finset (Sym2 V)} {e : Sym2 V}
    (heps : 0<eps) (hk : 0<k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k)))
    (f : Fin N → V×V) (hf : Function.Injective f)
    (hpaths : ∀ a, ∃ p : G.Walk (f a).1 (f a).2,
      C.BucketMonotoneKPath eps k false p ∧ e∈C.chordEdges p ∧
      ∀ d∈C.chordEdges p,d∈S) :
    (C.safeEndpoints eps k (S.erase e)).card+N≤(C.safeEndpoints eps k S).card := by
  let F := Finset.univ.image f
  have hFcard : F.card=N := by simp [F,Finset.card_image_of_injective _ hf]
  have hFsub : F⊆C.safeEndpoints eps k S := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨p,hp,_,hS⟩ := hpaths i
    exact C.mem_safeEndpoints.mpr ⟨p,hp,hS⟩
  have hdis : Disjoint (C.safeEndpoints eps k (S.erase e)) F := by
    apply Finset.disjoint_left.mpr
    intro a ha hF
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨p,hp,he,hS⟩ := hpaths i
    obtain ⟨q,hq,hqS⟩ := C.mem_safeEndpoints.mp ha
    have hpq := hp.unique C hq heps hk hG
    have hn := (Finset.mem_erase.mp (hqS e (by rwa [← hpq]))).1
    exact hn rfl
  have hsub : C.safeEndpoints eps k (S.erase e)∪F⊆C.safeEndpoints eps k S :=
    Finset.union_subset (C.safeEndpoints_mono (Finset.erase_subset _ _)) hFsub
  have hh := Finset.card_le_card hsub
  rwa [Finset.card_union_of_disjoint hdis,hFcard] at hh

end LightSpanners.UnitSpanningCycle
