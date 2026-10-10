import GreedyShortcuts.ChainWindowRoutes
import GreedyShortcuts.ChainGuardWindow

/-! Actual walk-position interfaces for stable end windows. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem stable_window_distance_at_positions {H : Finset (V × V)}
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    (hmin : T.count p=T.distance H s t) {k : ℕ} (hgood : ¬T.BadEndWindow H s t k)
    {i j : ℕ} (hij : i≤j) (hi : T.count (p.take i)≤k)
    (hj : T.distance H s t≤T.distance H s (p.getVert j)+k) :
    4*k≤T.distance H (p.getVert i) (p.getVert j) := by
  by_contra hbad
  apply hgood
  refine ⟨p.getVert i,p.getVert j,p.take i,segment p i j hij,p.drop j,?_,?_,hi,hj,by omega⟩
  · simpa only [take_append_segment p hij,Walk.append_take_drop_eq] using hp
  · simpa only [take_append_segment p hij,Walk.append_take_drop_eq] using hmin

theorem minimum_levels_distinct {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    (hmin : T.count p=T.distance H s t) {i j : ℕ}
    (hij : T.count (p.take i)<T.count (p.take j)) : p.getVert i≠p.getVert j := by
  intro he
  have hi := T.minimum_take hH p hp hmin i
  have hj := T.minimum_take hH p hp hmin j
  have hd := congrArg (T.distance H s) he
  omega

/-- A common middle edge gives a cheap rebased route between any positions
in the two end windows. The proof uses validity inheritance only. -/
theorem window_route_at_positions {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    {i a b j : ℕ} (hia : i≤a) (hab : a≤b) (hbj : b≤j)
    (hca : label T.chains (p.getVert a)≠none)
    (heb : (s,p.getVert b) ∈ T.important) (hne : p.getVert a≠p.getVert b) :
    T.distance (insert (p.getVert a,p.getVert b) H) (p.getVert i) (p.getVert j)≤
      T.count (segment p i a hia)+T.count (segment p b j hbj) := by
  have hp0 := allowed_subwalk hp (segment_isSubwalk p i a hia)
  have hp1 := allowed_subwalk hp (segment_isSubwalk p a b hab)
  have hp2 := allowed_subwalk hp (segment_isSubwalk p b j hbj)
  have hall := (allowed_append _ _ _).mpr ⟨(allowed_append _ _ _).mpr ⟨hp0,hp1⟩,hp2⟩
  have hsi : Reachable T.G s (p.getVert i) :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p.take i,allowed_mono (fun _ _ h => h.1) (allowed_subwalk hp (p.isSubwalk_take i))⟩
  have hib : Reachable T.G (p.getVert i) (p.getVert b) :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      (reachable_segment (allowed_mono (fun _ _ h => h.1) hp) (hia.trans hab))
  exact T.insertion_route_bound hH (segment p i a hia) (segment p a b hab)
    (segment p b j hbj) (T.allowed_rebase hH hsi _ hall) hca (T.important_inherits heb hsi hib) hne

theorem level_positions_strictMono {s t : V} (p : DWalk s t) (M : ℕ)
    (f : Fin M → ℕ) (hf : ∀ i,T.count (p.take (f i))=i.val+1) : StrictMono f := by
  intro i j hij
  by_contra hbad
  have hcount := T.count_take_mono p (show f j≤f i by omega)
  rw [hf i,hf j] at hcount
  omega

end GreedyShortcuts.ChainDistance.Context
