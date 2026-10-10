import GreedyShortcuts.ChainWindowPositions
import GreedyShortcuts.ChainRectangleCharging

/-! A stable actual minimum path constructs a genuine source-target saving
rectangle. Rebased old distances come from stability, not hereditary minima. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem stable_path_rectangle {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    (hmin : T.count p=T.distance H s t) (k : ℕ) (hk : 0<k)
    (hM : 2*k<T.count p) (hgood : ¬T.BadEndWindow H s t k) :
    ∃ e ∈ candidates T.G,2*k^3≤T.potential H-T.potential (insert e H) := by
  classical
  let M := T.count p
  have hMk : k≤M := by dsimp [M];omega
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
  let left : Fin k → Fin M := fun i => ⟨i.val,by dsimp [M];omega⟩
  let right : Fin k → Fin M := fun i => ⟨M-k+i.val,by omega⟩
  let a : Fin M := ⟨k-1,by dsimp [M];omega⟩
  let b : Fin M := ⟨M-k,by omega⟩
  have hab : a≤b := by change k-1≤M-k;dsimp [M];omega
  have hne : vertex a≠vertex b := by
    intro he
    have hh := congrArg Fin.val (hinj he)
    change k-1=M-k at hh
    dsimp [M] at hh
    omega
  have hca : label T.chains (p.getVert (f a))≠none := by
    obtain ⟨c,hc⟩ := T.important_covered (hf a).2.2
    simp [hc]
  have hlegal : (vertex a,vertex b) ∈ candidates T.G :=
    T.interior_candidate hH (segment p (f a) (f b) (hmono hab))
      (allowed_subwalk hp (segment_isSubwalk p _ _ (hmono hab))) hne
  have hreach : ∀ i j : Fin M,i≤j → Reachable T.G (vertex i) (vertex j) := by
    intro i j hij
    exact (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      (reachable_segment (allowed_mono (fun _ _ h => h.1) hp) (hmono hij))
  have hsource : ∀ i : Fin M,Reachable T.G s (vertex i) := by
    intro i
    exact (T.important_spec (hf i).2.2).1
  have hpairs : ∀ i j : Fin k,(vertex (left i),vertex (right j)) ∈ T.important := by
    intro i j
    apply T.important_inherits (hf (right j)).2.2 (hsource (left i))
    apply hreach
    change i.val≤M-k+j.val
    dsimp [M]
    omega
  have hsaving : ∀ i j : Fin k,2*k≤T.distance H (vertex (left i)) (vertex (right j))-
      T.distance (insert (vertex a,vertex b) H) (vertex (left i)) (vertex (right j)) := by
    intro i j
    have hia : left i≤a := by change i.val≤k-1;omega
    have hbj : b≤right j := by change M-k≤M-k+j.val;omega
    have hij := hia.trans (hab.trans hbj)
    have hold : 4*k≤T.distance H (vertex (left i)) (vertex (right j)) := by
      apply T.stable_window_distance_at_positions p hp hmin hgood (hmono hij)
      · rw [hfcount];change i.val+1≤k;omega
      · have hj := T.minimum_take hH p hp hmin (f (right j))
        rw [hfcount] at hj
        change M-k+j.val+1=T.distance H s (vertex (right j)) at hj
        change T.distance H s t≤T.distance H s (vertex (right j))+k
        have hMdist : M=T.distance H s t := hmin
        omega
    have hnew := T.window_route_at_positions hH p hp (hmono hia) (hmono hab) (hmono hbj)
      hca (hf b).2.2 hne
    have hleftcover : label T.chains (p.getVert (f (left i)))≠none := by
      obtain ⟨c,hc⟩ := T.important_covered (hf (left i)).2.2
      simp [hc]
    have hrightcover : label T.chains (p.getVert (f b))≠none := by
      obtain ⟨c,hc⟩ := T.important_covered (hf b).2.2
      simp [hc]
    have hc1 := T.count_segment_exact hH p hp (hmono hia) hleftcover
    have hc2 := T.count_segment_exact hH p hp (hmono hbj) hrightcover
    rw [hfcount,hfcount] at hc1 hc2
    change T.count (segment p (f (left i)) (f a) (hmono hia))+(i.val+1)=(k-1)+1+1 at hc1
    change T.count (segment p (f b) (f (right j)) (hmono hbj))+(M-k+1)=(M-k+j.val)+1+1 at hc2
    change T.distance (insert (vertex a,vertex b) H) (vertex (left i)) (vertex (right j))≤_ at hnew
    omega
  let sources := Finset.univ.image (fun i : Fin k => vertex (left i))
  let targets := Finset.univ.image (fun i : Fin k => vertex (right i))
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
  have hsc : sources.card=k := by simp only [sources,Finset.card_image_of_injective _ hleftinj,Finset.card_univ,Fintype.card_fin]
  have htc : targets.card=k := by simp only [targets,Finset.card_image_of_injective _ hrightinj,Finset.card_univ,Fintype.card_fin]
  have hdrop := T.rectangle_drop_lower_bound H (vertex a,vertex b) sources targets (2*k)
    (by intro u hu v hv;obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu;obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv;exact hpairs i j)
    (by intro u hu v hv;obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu;obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv;exact hsaving i j)
  rw [hsc,htc] at hdrop
  refine ⟨(vertex a,vertex b),hlegal,?_⟩
  nlinarith

end GreedyShortcuts.ChainDistance.Context
