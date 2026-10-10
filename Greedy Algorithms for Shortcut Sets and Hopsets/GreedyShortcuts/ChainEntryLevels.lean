import GreedyShortcuts.ChainLevels

/-! All positive chain levels, including the first, have actual important
entry vertices on the original fixed-source path. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Initial chain counts cannot exceed one. -/
theorem count_take_zero_le {s t : V} (p : DWalk s t) :
    T.count (p.take 0)≤1 := by
  simpa only [Walk.take_length,Nat.zero_min,Nat.zero_add] using T.count_le_vertices (p.take 0)

theorem count_take_mono {s t : V} (p : DWalk s t) {i j : ℕ} (hij : i≤j) :
    T.count (p.take i)≤T.count (p.take j) :=
  T.count_subwalk (p.take_isSubwalk_take hij)

/-- First attainment gives a real important entry, even when the source
itself lies on the first chain. -/
theorem exists_entry_level {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    (k : ℕ) (hk : 0<k) (hkp : k≤T.count p) :
    ∃ i,i≤p.length ∧ T.count (p.take i)=k ∧ (s,p.getVert i) ∈ T.important := by
  classical
  have hend : T.count (p.take p.length)=T.count p := by
    unfold count
    rw [Walk.take_of_length_le (Nat.le_refl _),T.chainSet_copy]
  have hex : ∃ i,k≤T.count (p.take i) := ⟨p.length,by rw [hend];exact hkp⟩
  let i := Nat.find hex
  have hi : k≤T.count (p.take i) := Nat.find_spec hex
  have hil : i≤p.length := Nat.find_min' hex (by rw [hend];exact hkp)
  by_cases hi0 : i=0
  · have hk1 : k=1 := by
      have hc := T.count_take_zero_le p
      rw [hi0] at hi
      omega
    have hs : label T.chains s ≠ none := by
      intro hn
      have hc : T.count (p.take 0)=0 := by simp [count,chainSet,hn]
      rw [hi0] at hi
      omega
    obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hs
    have hsimp := T.first_important (reachable_refl T.G s) hc
    rw [T.first_self s] at hsimp
    refine ⟨0,Nat.zero_le _,?_,by simpa only [Walk.getVert_zero] using hsimp⟩
    have hc0 := T.count_take_zero_le p
    rw [hi0] at hi
    omega
  · have hprev : T.count (p.take (i-1))<k :=
      Nat.lt_of_not_ge (Nat.find_min hex (by omega : i-1 < i))
    have hstep := T.count_take_succ_le p (i-1)
    have he : i-1+1=i := Nat.sub_add_cancel (by omega)
    rw [he] at hstep
    refine ⟨i,hil,by omega,?_⟩
    have hpair := T.prefix_level_important hH p hp (i-1) (by omega) (by rw [he];omega)
    simpa only [he] using hpair

/-- Original-source minima have minimum prefixes at all actual positions. -/
theorem minimum_take {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    (hmin : T.count p=T.distance H s t) (i : ℕ) :
    T.count (p.take i)=T.distance H s (p.getVert i) := by
  apply T.minimum_prefix hH (p.take i) (p.drop i)
  · simpa only [Walk.append_take_drop_eq] using hp
  · simpa only [Walk.append_take_drop_eq] using hmin

end GreedyShortcuts.ChainDistance.Context
