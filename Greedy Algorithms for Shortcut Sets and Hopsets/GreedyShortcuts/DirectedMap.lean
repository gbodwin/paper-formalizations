import GreedyShortcuts.DirectedPaths
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! Injective vertex maps carry genuine directed walks and hop bounds. -/
namespace GreedyShortcuts.DirectedMap

open SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
variable {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

def hom (f : U → V) (hf : Function.Injective f) : (⊤ : SimpleGraph U) →g (⊤ : SimpleGraph V) where
  toFun := f
  map_rel' := by
    intro u v h
    have hu : u ≠ v := by simpa using h
    simpa using (show f u ≠ f v from fun he => hu (hf he))

theorem allowed_map (f : U → V) (hf : Function.Injective f)
    {G : U → U → Prop} {H : V → V → Prop}
    (h : ∀ u v,G u v → H (f u) (f v)) {s t : U} (p : DWalk s t)
    (hp : Allowed G p) : Allowed H (p.map (hom f hf)) := by
  induction p with
  | nil => exact allowed_nil H _
  | @cons s u t ha p ih =>
    have hh := (allowed_cons G ha p).mp hp
    exact (allowed_cons H _ _).mpr ⟨h s u hh.1,ih hh.2⟩

theorem hopDist_map_le (f : U → V) (hf : Function.Injective f)
    {G : U → U → Prop} {H : V → V → Prop}
    (h : ∀ u v,G u v → H (f u) (f v)) {s t : U} (hr : Reachable G s t) :
    hopDist H (f s) (f t) ≤ hopDist G s t := by
  rw [hopDist_eq G hr]
  have hh := hopDist_le_walk H ((canonical G s t hr).map (hom f hf))
    (allowed_map f hf h _ (canonical_optimal G s t hr).1)
  simpa [hom] using hh

def edges (f : U → V) (J : Finset (U × U)) : Finset (V × V) :=
  J.image (fun e => (f e.1,f e.2))

theorem edges_card_le (f : U → V) (J : Finset (U × U)) : (edges f J).card ≤ J.card :=
  Finset.card_image_le

theorem mem_edges (f : U → V) (J : Finset (U × U)) {s t : U} (h : (s,t) ∈ J) :
    (f s,f t) ∈ edges f J := Finset.mem_image.mpr ⟨(s,t),h,rfl⟩

end GreedyShortcuts.DirectedMap
