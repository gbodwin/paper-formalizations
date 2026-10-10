import GreedyShortcuts.ChainWindowPositions

/-! Many legal important shortcut choices repair one demand in its unchanged
source filter. This counts shortcut choices, not rebased minimum subpaths. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- An actual demand of distance at least 4k has k² distinct legal important
shortcut choices. Each saves at least 2k on this original demand. -/
theorem many_important_shortcut_choices {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {s t : V} (hst : (s,t) ∈ T.important)
    (k : ℕ) (hk : 0<k) (hL : 4*k ≤ T.distance H s t) :
    ∃ sources targets : Finset V,sources.card=k ∧ targets.card=k ∧
      ∀ u∈sources,∀ v∈targets,(u,v)∈candidates T.G ∧ (u,v)∈T.important ∧
        2*k ≤ T.distance H s t-T.distance (insert (u,v) H) s t := by
  classical
  obtain ⟨p,hp,hmin⟩ := T.distance_spec H (T.important_spec hst).1
  let M := T.count p
  have hMk : 4*k≤M := by dsimp [M];omega
  have hlevels : ∀ i : Fin M, ∃ a,a≤p.length ∧ T.count (p.take a)=i.val+1 ∧
      (s,p.getVert a) ∈ T.important := by
    intro i
    exact T.exists_entry_level hH p hp (i.val+1) (by omega) (by dsimp [M] at i ⊢;omega)
  choose f hf using hlevels
  have hfcount : ∀ i,T.count (p.take (f i))=i.val+1 := fun i => (hf i).2.1
  have hmono := (T.level_positions_strictMono p M f hfcount).monotone
  let vertex : Fin M → V := fun i => p.getVert (f i)
  have hinj : Function.Injective vertex := by
    intro i j he
    have hi := T.minimum_take hH p hp hmin (f i)
    have hj := T.minimum_take hH p hp hmin (f j)
    have he' : p.getVert (f i)=p.getVert (f j) := he
    have hd := congrArg (T.distance H s) he'
    rw [hfcount i] at hi
    rw [hfcount j] at hj
    apply Fin.ext
    omega
  let left : Fin k → Fin M := fun i => ⟨i.val,by omega⟩
  let right : Fin k → Fin M := fun i => ⟨M-k+i.val,by omega⟩
  have hleftinj : Function.Injective (fun i : Fin k => vertex (left i)) := by
    intro i j he
    have hh := congrArg Fin.val (hinj he)
    exact Fin.ext hh
  have hrightinj : Function.Injective (fun i : Fin k => vertex (right i)) := by
    intro i j he
    have hh := congrArg Fin.val (hinj he)
    apply Fin.ext
    change M-k+i.val=M-k+j.val at hh
    omega
  refine ⟨Finset.univ.image (fun i : Fin k => vertex (left i)),
    Finset.univ.image (fun j : Fin k => vertex (right j)),?_,?_,?_⟩
  · simp only [Finset.card_image_of_injective _ hleftinj,Finset.card_univ,Fintype.card_fin]
  · simp only [Finset.card_image_of_injective _ hrightinj,Finset.card_univ,Fintype.card_fin]
  · intro u hu v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    have hij : left i≤right j := by change i.val≤M-k+j.val;omega
    have hpos := hmono hij
    have hne : vertex (left i)≠vertex (right j) := by
      intro he
      have hh := congrArg Fin.val (hinj he)
      change i.val=M-k+j.val at hh
      omega
    have hlegal := T.interior_candidate hH (segment p (f (left i)) (f (right j)) hpos)
      (allowed_subwalk hp (segment_isSubwalk p _ _ hpos)) hne
    have hreach : Reachable T.G (vertex (left i)) (vertex (right j)) :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        (reachable_segment (allowed_mono (fun _ _ h => h.1) hp) hpos)
    have hpair := T.important_inherits (hf (right j)).2.2
      (T.important_spec (hf (left i)).2.2).1 hreach
    refine ⟨hlegal,hpair,?_⟩
    obtain ⟨c,hc⟩ := T.important_covered (hf (left i)).2.2
    have hall : Allowed (T.graph H s)
        (((p.take (f (left i))).append
          (segment p (f (left i)) (f (right j)) hpos)).append (p.drop (f (right j)))) := by
      simpa only [take_append_segment p hpos,Walk.append_take_drop_eq] using hp
    have hnew := T.insertion_route_bound hH (p.take (f (left i)))
      (segment p (f (left i)) (f (right j)) hpos) (p.drop (f (right j))) hall
      (by simp [hc]) (hf (right j)).2.2 hne
    have hsuffix := T.count_append_exact hH (p.take (f (right j))) (p.drop (f (right j)))
      (by simpa only [Walk.append_take_drop_eq] using hp)
    obtain ⟨d,hd⟩ := T.important_covered (hf (right j)).2.2
    rw [Walk.append_take_drop_eq] at hsuffix
    simp only [hd,Option.toFinset_some,Finset.card_singleton] at hsuffix
    rw [hfcount] at hnew
    rw [hfcount] at hsuffix
    change T.distance (insert (vertex (left i),vertex (right j)) H) s t≤
      i.val+1+T.count (p.drop (f (right j))) at hnew
    change T.count p+1=(M-k+j.val+1)+T.count (p.drop (f (right j))) at hsuffix
    dsimp only [M] at hsuffix hMk
    omega

end GreedyShortcuts.ChainDistance.Context
