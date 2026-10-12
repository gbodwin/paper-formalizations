import MinorFreeSpanners.ConnectedLeafDeletion

/-! A sufficiently massive finite tree has a leaf outside any retained star.
The leaf is selected from a genuine maximum-mass path. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem forest_star_path_mass_le {V : Type*} (G : SimpleGraph V) (hG : G.IsAcyclic)
    (x : V) (N : Finset V) (hN : ∀ y∈N,G.Adj x y) (d : V → ℝ) (D : ℝ)
    (hD : 0≤D) (hd : ∀ v∈insert x N,d v≤D) {a b : V}
    (ha : a∈insert x N) (hb : b∈insert x N) (p : G.Walk a b) (hp : p.IsPath) :
    pathMass d p≤3*D := by
  classical
  have root (v : V) (hv : v∈insert x N) :
      ∃ q : G.Walk v x,(∀ u∈q.support,u∈insert x N) ∧ q.length≤1 := by
    rcases Finset.mem_insert.mp hv with rfl|hv
    · exact ⟨.nil,by simp,by simp⟩
    · exact ⟨.cons (hN v hv).symm .nil,by simp [hv],by simp⟩
  obtain ⟨q,hq,hlq⟩ := root a ha
  obtain ⟨r,hr,hlr⟩ := root b hb
  let s := q.append r.reverse
  have hs : ∀ u∈s.support,u∈insert x N := by
    intro u hu
    rcases (Walk.mem_support_append_iff _ _).mp hu with hu|hu
    · exact hq u hu
    · exact hr u (by simpa using hu)
  have hl : s.length≤2 := by simp only [s,Walk.length_append,Walk.length_reverse];omega
  have he := hG.subsingleton_path a b |>.elim ⟨p,hp⟩ s.toPath
  have hpe : p=s.toPath.val := congrArg Subtype.val he
  have hplen : p.length≤2 := by rw [hpe];exact s.length_bypass_le_length.trans hl
  have hps : ∀ u∈p.support,u∈insert x N := by
    rw [hpe]
    exact fun u hu => hs u (s.support_toPath_subset_support hu)
  have hsum : pathMass d p≤p.support.toFinset.card*D := by
    calc
      _ ≤ ∑ _u∈p.support.toFinset,D := Finset.sum_le_sum fun u hu =>
        hd u (hps u (List.mem_toFinset.mp hu))
      _ = _ := by simp
  have hcard : p.support.toFinset.card≤3 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support]
    omega
  exact hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hD)

 theorem exists_leaf_outside_star {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hne : S.Nonempty)
    (x : V) (N : Finset V) (hN : ∀ y∈N,G.Adj x y)
    (hNS : insert x N⊆S) (d : V → ℝ) (L D : ℝ)
    (hdpos : ∀ v∈S,0<d v) (hd : ∀ v∈S,d v≤D) (hD : 0≤D) (hLD : 3*D<L)
    (hlarge : ∃ a b,∃ p : G.Walk a b,p.IsPath ∧
      (∀ v∈p.support,v∈S) ∧ L≤pathMass d p) :
    ∃ a∈S,a∉insert x N ∧ ∃ z,∀ v∈S,G.Adj a v → v=z := by
  classical
  obtain ⟨a,ha,b,hb,p,hp,hs,hmax⟩ := exists_max_mass_path G hG S hne d
  obtain ⟨u,v,q,hq,hqs,hLq⟩ := hlarge
  have hLp : L≤pathMass d p := hLq.trans (hmax u v q hq hqs)
  by_cases hak : a∈insert x N
  · have hbk : b∉insert x N := by
      intro hbK
      have hm := forest_star_path_mass_le G hG x N hN d D hD
        (fun v hv => hd v (hNS hv)) hak hbK p hp
      linarith
    refine ⟨b,hb,hbk,p.reverse.snd,?_⟩
    intro v hv hvadj
    exact max_mass_path_start_neighbor G hG S d hdpos p.reverse hp.reverse
      (by simpa using hs) (by intro i j r hr hrs;simpa only [pathMass_reverse] using hmax i j r hr hrs)
      hv hvadj
  · exact ⟨a,ha,hak,p.snd,fun v hv hvadj => max_mass_path_start_neighbor G hG S d hdpos p hp hs hmax hv hvadj⟩

end MinorFreeSpanners
