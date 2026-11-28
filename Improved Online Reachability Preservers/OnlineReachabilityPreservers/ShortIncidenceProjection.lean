import OnlineReachabilityPreservers.IncidenceComponentCleaning

/-! A finite cutoff only needs short connections at a deleted label. -/

namespace OnlineReachabilityPreservers

open SimpleGraph
local notation "Before" => SourceAudit.BeforeIn

/-- The two portions of a closed walk between any two visited vertices
have combined length equal to the whole walk. At least one portion is
at most half as long. -/
theorem exists_short_walk_of_closed_support {A : Type*} {G : SimpleGraph A}
    {root x y : A} (w : G.Walk root root) (left : x ∈ w.support) (right : y ∈ w.support)
    {k : ℕ} (short : w.length ≤ 2*k) : ∃ route : G.Walk x y, route.length ≤ k := by
  have route (i j : ℕ) (ordered : i ≤ j) (fits : j ≤ w.length) :
      ∃ p : G.Walk (w.getVert i) (w.getVert j), p.length ≤ k := by
    by_cases forwardShort : j-i ≤ k
    · have endpoint : (w.drop i).getVert (j-i) = w.getVert j := by
        rw [Walk.drop_getVert,Nat.add_sub_of_le ordered]
      let p := ((w.drop i).take (j-i)).copy rfl endpoint
      refine ⟨p,?_⟩
      simp only [p,Walk.length_copy,Walk.take_length]
      exact (min_le_left _ _).trans forwardShort
    · let p := ((w.drop j).append (w.take i)).reverse
      refine ⟨p,?_⟩
      simp only [p,Walk.length_reverse,Walk.length_append,Walk.drop_length,Walk.take_length,
        min_eq_left (ordered.trans fits)]
      omega
  obtain ⟨i,leftEq,leftFit⟩ := Walk.mem_support_iff_exists_getVert.mp left
  obtain ⟨j,rightEq,rightFit⟩ := Walk.mem_support_iff_exists_getVert.mp right
  rcases le_total i j with earlier | later
  · obtain ⟨walk,length⟩ := route i j earlier rightFit
    exact ⟨walk.copy leftEq rightEq,by simpa only [Walk.length_copy] using length⟩
  · obtain ⟨walk,length⟩ := route j i later leftFit
    exact ⟨walk.reverse.copy leftEq rightEq,by simpa only [Walk.length_copy,Walk.length_reverse] using length⟩

private theorem bridge_short_incidence_injective {J W A : Type*} [DecidableEq W]
    {pieces : J → List W} {d k : ℕ} (b : Bridge (Before pieces) d) (fit : d+2 ≤ k)
    {G : SimpleGraph A} (f : pathIncidenceGraph pieces →g G)
    (coherent : ∀ a, RespectsShortDeletionLinksAt f a (k-2)) :
    (Function.Injective fun i => f (.inr (b.vertex i))) ∧
      (Function.Injective fun i => f (.inl (b.arc i))) ∧ ∀ i, f (.inl b.river) ≠ f (.inl (b.arc i)) := by
  obtain ⟨walk,length,corners,arcs,river⟩ := b.exists_incidence_closed_walk
  have short : walk.length ≤ 2*k := length.trans_le (Nat.mul_le_mul_left 2 fit)
  have equal {x y : J ⊕ W} (onX : x ∈ walk.support) (onY : y ∈ walk.support) (same : f x = f y) : x = y := by
    obtain ⟨route,near⟩ := exists_short_walk_of_closed_support walk onX onY short
    exact RespectsShortDeletionLinksAt.eq_of_walk (f := f) (coherent (f x)) rfl same.symm route (by omega)
  exact ⟨fun _ _ same => b.distinctVertices (Sum.inr.inj (equal (corners _) (corners _) same)),
    fun _ _ same => b.distinctArcs (Sum.inl.inj (equal (arcs _) (arcs _) same)),
    fun i same => b.river_ne_arc i (Sum.inl.inj (equal river (arcs i) same))⟩

/-- Through cutoff `k`, a split projection only needs to keep neighboring
incidences together when their original labels can connect in at most
`k-2` edges after deleting the common label. -/
theorem localOrderAdmissible_of_short_incidence_links {I J V W : Type*}
    [LinearOrder I] [LinearOrder J] [DecidableEq V] [DecidableEq W]
    {paths : I → List V} {pieces : J → List W} {half : Bool} {k : ℕ}
    (allowed : localOrderAdmissible half k paths)
    (parent : J → I) (project : W → V) (ordered : Monotone parent)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) (project x) (project y))
    (coherent : ∀ a, RespectsShortDeletionLinksAt (pathIncidenceGraph_hom parent project
      (fun {_ _} => members)) a (k-2)) : localOrderAdmissible half k pieces := by
  let f := pathIncidenceGraph_hom parent project (fun {_ _} => members)
  let lift {d : ℕ} (fit : d+2 ≤ k) (b : Bridge (Before pieces) d) : Bridge (Before paths) d := by
    have distinct := bridge_short_incidence_injective b fit f coherent
    refine ⟨project ∘ b.vertex,parent ∘ b.arc,parent b.river,?_,?_,?_,steps b.riverStep,
      fun i => steps (b.arcStep i)⟩
    · intro i j same
      exact distinct.1 (congrArg Sum.inr same)
    · intro i j same
      exact distinct.2.1 (congrArg Sum.inl same)
    · intro i same
      exact distinct.2.2 i (congrArg Sum.inl same)
  cases half
  · intro d fit
    exact ⟨fun b => (allowed fit).false (lift fit b)⟩
  · intro d fit b earlier
    let original := lift fit b
    have strict : original.arc (Fin.last d) < original.river :=
      lt_of_le_of_ne (ordered earlier.le) (original.river_ne_arc _).symm
    exact allowed fit original strict

end OnlineReachabilityPreservers
