import OnlineReachabilityPreservers.BalancedRegularization

/-! The density hypotheses of common-order cleaning hold at a positive-budget maximum. -/

namespace OnlineReachabilityPreservers

open Finset

private def singletonPaddedPathFamily (n p : ℕ) (hn : 0<n) (hp : 0<p) :
    Fin p → Finset (Fin n) :=
  fun i => if i = (⟨0,hp⟩ : Fin p) then univ else {⟨0,hn⟩}

private theorem singletonPaddedPathFamily_no_bridge (n p : ℕ) (hn : 0<n) (hp : 0<p)
    (k : ℕ) : IsEmpty (Bridge (PathBefore (singletonPaddedPathFamily n p hn hp)) k) := by
  let root : Fin p := ⟨0,hp⟩
  have only {i : Fin p} {a b : Fin n}
      (step : PathBefore (singletonPaddedPathFamily n p hn hp) i a b) : i = root := by
    by_contra no
    have a0 : a = (⟨0,hn⟩ : Fin n) := by
      simpa [singletonPaddedPathFamily, root, no] using step.1
    have b0 : b = (⟨0,hn⟩ : Fin n) := by
      simpa [singletonPaddedPathFamily, root, no] using step.2.1
    exact step.2.2.ne (a0.trans b0.symm)
  refine ⟨fun b => b.river_ne_arc 0 ((only b.riverStep).trans (only (b.arcStep 0)).symm)⟩

private theorem singletonPaddedPathFamily_dense (n p : ℕ) (hn : 0<n) (hp : 0<p) :
    n ≤ ∑ i, (singletonPaddedPathFamily n p hn hp i).card ∧
      p ≤ ∑ i, (singletonPaddedPathFamily n p hn hp i).card := by
  constructor
  · simpa [singletonPaddedPathFamily] using
      (single_le_sum (f := fun i => (singletonPaddedPathFamily n p hn hp i).card)
        (fun (_ : Fin p) _ => Nat.zero_le _)
        (mem_univ (⟨0,hp⟩ : Fin p)) :
        (singletonPaddedPathFamily n p hn hp ⟨0,hp⟩).card ≤ ∑ i, (singletonPaddedPathFamily n p hn hp i).card)
  · calc
      _ = ∑ _ : Fin p, 1 := by simp
      _ ≤ ∑ i, (singletonPaddedPathFamily n p hn hp i).card := by
        apply sum_le_sum
        intro i _
        unfold singletonPaddedPathFamily
        split
        · simpa using (show 1 ≤ n by omega)
        · simp

/-- The two bridge exclusions on a finite common-order system. -/
def commonOrderAdmissible {V I : Type*} [LinearOrder V] [LinearOrder I]
    (half : Bool) (size : ℕ) (paths : I → Finset V) : Prop :=
  if half then HalfBridgeFree (PathBefore paths) size else BridgeFree (PathBefore paths) size

/-- In either mode take a common-order maximum of the prescribed sizes.
A spanning path and singleton padding show that both density assumptions
of the balanced cleaning theorem hold for this maximizing family. -/
theorem commonOrderExtremal_isDense (n p size : ℕ) (half : Bool) (hn : 0<n) (hp : 0<p) :
    ∃ paths : Fin p → Finset (Fin n), commonOrderAdmissible half size paths ∧
      (∀ other : Fin p → Finset (Fin n), commonOrderAdmissible half size other →
        (∑ i, (other i).card) ≤ ∑ i, (paths i).card) ∧
      n ≤ ∑ i, (paths i).card ∧ p ≤ ∑ i, (paths i).card := by
  classical
  let base := singletonPaddedPathFamily n p hn hp
  have allowed : commonOrderAdmissible half size base := by
    cases half
    · intro k _
      exact singletonPaddedPathFamily_no_bridge n p hn hp k
    · intro k _ bridge _
      exact (singletonPaddedPathFamily_no_bridge n p hn hp k).false bridge
  let admissible := (univ : Finset (Fin p → Finset (Fin n))).filter (commonOrderAdmissible half size)
  have inside : base ∈ admissible := mem_filter.mpr ⟨mem_univ _,allowed⟩
  obtain ⟨paths,member,maximal⟩ := exists_max_image admissible
    (fun paths => ∑ i, (paths i).card) ⟨base,inside⟩
  obtain ⟨ncap,pcap⟩ := singletonPaddedPathFamily_dense n p hn hp
  exact ⟨paths,(mem_filter.mp member).2,
    fun other cond => maximal other (mem_filter.mpr ⟨mem_univ _,cond⟩),
    ncap.trans (maximal base inside),pcap.trans (maximal base inside)⟩

/-- The common-order cleaning conclusion at every positive-budget extremum.
One subdivision and restriction retains a constant fraction of the maximum
within both budgets and the four original-average caps. -/
theorem commonOrderExtremal_balanced (n p size : ℕ) (half : Bool) (hn : 0<n) (hp : 0<p) :
    ∃ paths : Fin p → Finset (Fin n),
      let M := ∑ i, (paths i).card
      let d := (4*M)/Fintype.card (Fin n)
      let l := (4*M)/Fintype.card (Fin p)
      let pieces := splitVertices paths d
      ∃ A : Finset (VertexBlockIndex paths d), ∃ B : Finset (BlockIndex pieces l),
        let clean := rectanglePaths (splitPaths pieces l) A B
        A.card ≤ n ∧ B.card ≤ p ∧ commonOrderAdmissible half size clean ∧
          (∀ other : Fin p → Finset (Fin n), commonOrderAdmissible half size other →
            (∑ i, (other i).card) ≤ 16*(∑ i, (clean i).card)) ∧
          (∀ v : ↥A, (M:ℝ)/(4*(n:ℝ)) ≤ (occurrences clean v).card ∧
            ((occurrences clean v).card:ℝ) ≤ 4*(M:ℝ)/(n:ℝ)) ∧
          (∀ i : ↥B, (M:ℝ)/(4*(p:ℝ)) ≤ (clean i).card ∧
            ((clean i).card:ℝ) ≤ 4*(M:ℝ)/(p:ℝ)) := by
  obtain ⟨paths,eligible,maximal,mn,mp⟩ := commonOrderExtremal_isDense n p size half hn hp
  obtain ⟨A,B,vertices,requests,mass,deg,len,halfFree,fullFree⟩ := regularization_balanced_caps paths
    (by simpa only [Fintype.card_fin] using hn) (by simpa only [Fintype.card_fin] using hp)
    (by simpa only [Fintype.card_fin] using mn) (by simpa only [Fintype.card_fin] using mp)
  refine ⟨paths,A,B,by simpa only [Fintype.card_fin] using vertices,
    by simpa only [Fintype.card_fin] using requests, ?_,
    fun other allowed => (maximal other allowed).trans mass, ?_, ?_⟩
  · cases half
    · exact fullFree size eligible
    · exact halfFree size eligible
  · simpa only [Fintype.card_fin] using deg
  · simpa only [Fintype.card_fin] using len

end OnlineReachabilityPreservers
