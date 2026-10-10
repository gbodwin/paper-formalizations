import GreedyShortcuts.LightReroute
import GreedyShortcuts.PrefixIncidence
import GreedyShortcuts.HeavyCharging

/-! The light-intersection branch: one common prefix source and the first
available base-path suffix intersection give a genuine improving edge. -/
namespace GreedyShortcuts.LightCharging

open Finset SimpleGraph DirectedPaths CanonicalSegments ShortcutWalk SuffixWindowPath
open SuffixIncidence CanonicalSavings
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem common_prefix_progress {G : V → V → Prop} {s t : V} {q : DWalk s t}
    (hq : Allowed G q) (β : ℕ) (hβ : 8 ≤ β) (hshort : q.length+1 ≤ β/8)
    (Q : Finset (CanonicalSuffixPath.active G β)) (hQ : Q.Nonempty) (u : V)
    (hprefix : ∀ d ∈ Q,u ∈ PrefixIncidence.vertices (CanonicalSuffixPath.path G β d))
    (hinter : ∀ d ∈ Q,(q.support.toFinset ∩ vertices (CanonicalSuffixPath.path G β d)).Nonempty) :
    ∃ e ∈ candidates G, β*Q.card ≤ 4*HeavyCharging.totalDrop G β e := by
  classical
  let p := CanonicalSuffixPath.path G β
  let J := (Finset.range (q.length+1)).filter
    (fun j => ∃ d ∈ Q,q.getVert j ∈ vertices (p d))
  have hJ : J.Nonempty := by
    obtain ⟨d,hd⟩ := hQ
    obtain ⟨x,hx⟩ := hinter d hd
    obtain ⟨j,hjx,hj⟩ := Walk.mem_support_iff_exists_getVert.mp
      (List.mem_toFinset.mp (Finset.mem_inter.mp hx).1)
    refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),d,hd,?_⟩⟩
    simpa only [hjx] using (Finset.mem_inter.mp hx).2
  let b := J.min' hJ
  have hb : b ∈ J := J.min'_mem hJ
  have hbl : b ≤ q.length := by
    have hh : b < q.length+1 := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    omega
  obtain ⟨d₀,hd₀,hv₀⟩ := (Finset.mem_filter.mp hb).2
  obtain ⟨a₀,ha₀,hau₀⟩ := PrefixIncidence.mem_vertices.mp (hprefix d₀ hd₀)
  obtain ⟨j₀,hj₀,hjv₀⟩ := Finset.mem_image.mp hv₀
  have hj₀' : j₀ < suffixSize (p d₀) := Finset.mem_range.mp hj₀
  have hactive₀ : β < (p d₀).length := by
    rw [CanonicalSuffixPath.path_length]
    exact (Finset.mem_filter.mp d₀.property).2
  have hlt₀ : a₀ < suffixOffset (p d₀)+j₀ := by
    change a₀ < suffixSize (p d₀) at ha₀
    dsimp [suffixSize,suffixOffset] at *
    omega
  have hneq : u ≠ q.getVert b := by
    intro he
    exact vertices_ne (CanonicalSuffixPath.path_optimal G β d₀).2.1 hlt₀
      (index_bound (p d₀) hj₀') (hau₀.trans (he.trans hjv₀.symm))
  have hreach : Reachable G u (q.getVert b) := by
    have hh : Reachable G ((p d₀).getVert a₀) ((p d₀).getVert (suffixOffset (p d₀)+j₀)) :=
      reachable_segment (CanonicalSuffixPath.path_optimal G β d₀).1 hlt₀.le
    change (p d₀).getVert a₀ = u at hau₀
    simpa only [hau₀,hjv₀] using hh
  let e := (u,q.getVert b)
  have hrow : ∀ d ∈ Q,β ≤ 4*demandDrop G β e d.val := by
    intro d hd
    obtain ⟨x,hx⟩ := hinter d hd
    obtain ⟨j,hjx,hj⟩ := Walk.mem_support_iff_exists_getVert.mp
      (List.mem_toFinset.mp (Finset.mem_inter.mp hx).1)
    obtain ⟨k,hk,hkx⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).2
    have hk' : k < suffixSize (p d) := Finset.mem_range.mp hk
    have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),d,hd,by simpa only [hjx] using (Finset.mem_inter.mp hx).2⟩
    have hbj : b ≤ j := J.min'_le _ hjJ
    obtain ⟨a,ha,hau⟩ := PrefixIncidence.mem_vertices.mp (hprefix d hd)
    have hactive : β < (p d).length := by
      rw [CanonicalSuffixPath.path_length]
      exact (Finset.mem_filter.mp d.property).2
    have hr := allowed_subwalk hq (segment_isSubwalk q b j hbj)
    have hrs : (segment q b j hbj).length+1 ≤ β/8 := by
      rw [segment_length q hbj hj]
      omega
    have hh := LightReroute.reroute_saving (CanonicalSuffixPath.path_optimal G β d)
      hβ hactive ha (show suffixOffset (p d) ≤ suffixOffset (p d)+k by omega)
      (index_bound (p d) hk') hr hrs (hjx.trans hkx.symm)
      (by simpa only [hau] using hneq)
    simpa only [hau] using hh
  refine ⟨e,(mem_candidates G e).mpr ⟨hneq,hreach⟩,?_⟩
  calc
    β*Q.card = ∑ _d ∈ Q,β := by simp [Nat.mul_comm]
    _ ≤ ∑ d ∈ Q,4*demandDrop G β e d.val := Finset.sum_le_sum hrow
    _ = 4*∑ d ∈ Q,demandDrop G β e d.val := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left 4 (HeavyCharging.active_sum_le G β e Q)

noncomputable def light {s t : V} (G : V → V → Prop) (β σ : ℕ) (q : DWalk s t) :
    Finset (CanonicalSuffixPath.active G β) := by
  classical
  exact Finset.univ.filter (fun d =>
    0 < (q.support.toFinset ∩ vertices (CanonicalSuffixPath.path G β d)).card ∧
    (q.support.toFinset ∩ vertices (CanonicalSuffixPath.path G β d)).card < σ)

noncomputable def weight {s t : V} (G : V → V → Prop) (β σ : ℕ) (q : DWalk s t) : ℕ :=
  ∑ d ∈ light G β σ q,(q.support.toFinset ∩ vertices (CanonicalSuffixPath.path G β d)).card

theorem weight_le {s t : V} (G : V → V → Prop) (β σ : ℕ) (q : DWalk s t) :
    weight G β σ q ≤ σ*(light G β σ q).card := by
  classical
  calc
    _ ≤ ∑ _d ∈ light G β σ q,σ := Finset.sum_le_sum (fun d hd =>
      (Finset.mem_filter.mp hd).2.2.le)
    _ = _ := by simp [Nat.mul_comm]

theorem light_progress {G : V → V → Prop} {s t : V} {q : DWalk s t}
    (hq : Allowed G q) (β σ : ℕ) (hβ : 8 ≤ β) (hshort : q.length+1 ≤ β/8)
    (hpos : 0 < weight G β σ q) :
    ∃ e ∈ candidates G, β^2*(light G β σ q).card ≤
      32*Fintype.card V*HeavyCharging.totalDrop G β e := by
  classical
  let Q := light G β σ q
  let p := CanonicalSuffixPath.path G β
  have hQ : Q.Nonempty := by
    by_contra hn
    have hz : light G β σ q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [weight,hz] at hpos
  obtain ⟨u,hu⟩ := PrefixIncidence.exists_vertex Q hQ p
    (fun d _ => (CanonicalSuffixPath.path_optimal G β d).2.1) β hβ
    (by intro d hd; rw [CanonicalSuffixPath.path_length]; exact (Finset.mem_filter.mp d.property).2)
  let R := PrefixIncidence.family Q p u
  have hR : R.Nonempty := Finset.card_pos.mp (by
    have hqc := Finset.card_pos.mpr hQ
    change 0 < (PrefixIncidence.family Q p u).card
    nlinarith)
  obtain ⟨e,he,hdrop⟩ := common_prefix_progress hq β hβ hshort R hR u
    (fun d hd => (Finset.mem_filter.mp hd).2)
    (by
      intro d hd
      have hdQ := (Finset.mem_filter.mp hd).1
      exact Finset.card_pos.mp (Finset.mem_filter.mp hdQ).2.1)
  refine ⟨e,he,?_⟩
  calc
    β^2*Q.card = β*(β*Q.card) := by ring
    _ ≤ β*(8*Fintype.card V*R.card) := Nat.mul_le_mul_left β hu
    _ = 8*Fintype.card V*(β*R.card) := by ring
    _ ≤ 8*Fintype.card V*(4*HeavyCharging.totalDrop G β e) := Nat.mul_le_mul_left _ hdrop
    _ = _ := by ring

/-- Light branch of the high-score dichotomy. -/
theorem light_relative {G : V → V → Prop} {s t : V} {q : DWalk s t}
    (hq : Allowed G q) (β σ : ℕ) (hβ : 8 ≤ β) (hshort : q.length+1 ≤ β/8)
    (hpos : 0 < CanonicalSuffixPath.potential G β)
    (hweight : β*CanonicalSuffixPath.potential G β ≤ 512*Fintype.card V*weight G β σ q) :
    ∃ e ∈ candidates G, β^3*CanonicalSuffixPath.potential G β ≤
      16384*σ*(Fintype.card V)^2*HeavyCharging.totalDrop G β e := by
  have hw : 0 < weight G β σ q := by nlinarith
  obtain ⟨e,he,hh⟩ := light_progress hq β σ hβ hshort hw
  refine ⟨e,he,?_⟩
  calc
    β^3*CanonicalSuffixPath.potential G β = β^2*(β*CanonicalSuffixPath.potential G β) := by ring
    _ ≤ β^2*(512*Fintype.card V*weight G β σ q) := Nat.mul_le_mul_left _ hweight
    _ ≤ β^2*(512*Fintype.card V*(σ*(light G β σ q).card)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (weight_le G β σ q))
    _ = (512*Fintype.card V*σ)*(β^2*(light G β σ q).card) := by ring
    _ ≤ (512*Fintype.card V*σ)*(32*Fintype.card V*HeavyCharging.totalDrop G β e) :=
      Nat.mul_le_mul_left _ hh
    _ = _ := by ring

end GreedyShortcuts.LightCharging
