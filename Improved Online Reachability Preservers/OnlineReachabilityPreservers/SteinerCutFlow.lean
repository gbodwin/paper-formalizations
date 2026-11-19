import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import OnlineReachabilityPreservers.SimplePaths
import OnlineReachabilityPreservers.SteinerCuts

/-! Integer unit augmentations for the thin phase's directed cut separator. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

abbrev ArcFlow (V : Type*) := V × V → ℤ

def divergence (f : ArcFlow V) (u : V) : ℤ := ∑ v : V, f (u,v)

structure ValidArcFlow (capacity : ArcFlow V) (s t : V) (value : ℕ) (f : ArcFlow V) : Prop where
  skew : ∀ u v, f (u,v) = -f (v,u)
  upper : ∀ e, f e ≤ capacity e
  balance : ∀ u, divergence f u = (if u=s then (value:ℤ) else 0) - (if u=t then (value:ℤ) else 0)

def residualArcs (capacity f : ArcFlow V) : Arcs V :=
  univ.filter fun e => f e < capacity e

private def inPath (P : Arcs V) (e : V × V) : ℤ :=
  if e ∈ P then 1 else 0

def augmentArcFlow (f : ArcFlow V) (P : Arcs V) : ArcFlow V :=
  fun e => f e + inPath P e - inPath P e.swap

private theorem pathDivergence {R : Arcs V} {s t : V} {p : List (V × V)}
    (walk : Walk R s t p) (simple : (p.map Prod.fst ++ [t]).Nodup) (a : V) :
    divergence (augmentArcFlow (fun _ => 0) p.toFinset) a =
      (if a=s then 1 else 0) - (if a=t then 1 else 0) := by
  induction walk with
  | nil => simp [divergence,augmentArcFlow,inPath]
  | @cons u v t p edge walk ih =>
    have hd : u ∉ p.map Prod.fst ++ [t] ∧ (p.map Prod.fst ++ [t]).Nodup := by
      simpa only [List.map_cons,List.cons_append,List.nodup_cons] using simple
    have hnot : (u,v) ∉ p.toFinset := by
      intro hk
      exact hd.1 (List.mem_append_left _ (List.mem_map_of_mem (List.mem_toFinset.mp hk)))
    have bump (e : V × V) :
        inPath ((u,v)::p).toFinset e = inPath p.toFinset e + (if e=(u,v) then 1 else 0) := by
      by_cases eq : e=(u,v)
      · subst e
        simp [inPath,hnot]
      · simp [inPath,List.toFinset_cons,mem_insert,eq]
    have out : (∑ b : V, (if (a,b)=(u,v) then (1:ℤ) else 0)) = if a=u then 1 else 0 := by
      by_cases eq : a=u <;> simp [Prod.mk.injEq,eq]
    have inc : (∑ b : V, (if (b,a)=(u,v) then (1:ℤ) else 0)) = if a=v then 1 else 0 := by
      by_cases eq : a=v <;> simp [Prod.mk.injEq,eq]
    have rest := ih hd.2
    simp only [divergence,augmentArcFlow,zero_add,Prod.swap_prod_mk] at rest ⊢
    simp only [bump,sum_sub_distrib,sum_add_distrib,out,inc]
    rw [sum_sub_distrib] at rest
    omega

theorem ValidArcFlow.augment {c f : ArcFlow V} {s t : V} {value : ℕ}
    (valid : ValidArcFlow c s t value f) {p : List (V × V)}
    (path : SimpleWalk (residualArcs c f) s t p) :
    ValidArcFlow c s t (value+1) (augmentArcFlow f p.toFinset) := by
  constructor
  · intro u v
    have h := valid.skew u v
    simp only [augmentArcFlow,Prod.swap_prod_mk]
    omega
  · intro e
    have base := valid.upper e
    have nonneg : 0 ≤ inPath p.toFinset e.swap := by unfold inPath; split <;> norm_num
    by_cases h : e ∈ p.toFinset
    · have lt := (mem_filter.mp (path.1.mem (List.mem_toFinset.mp h))).2
      have hIn : inPath p.toFinset e = 1 := by simp [inPath,h]
      change f e + inPath p.toFinset e - inPath p.toFinset e.swap ≤ c e
      omega
    · have hIn : inPath p.toFinset e = 0 := by simp [inPath,h]
      change f e + inPath p.toFinset e - inPath p.toFinset e.swap ≤ c e
      omega
  · intro a
    have hd := pathDivergence path.1 path.2 a
    have h := valid.balance a
    simp only [divergence,augmentArcFlow,Prod.swap_prod_mk,sum_add_distrib,sum_sub_distrib,
      zero_add,Int.natCast_add,Int.cast_ofNat_Int] at h hd ⊢
    have expand (b : V) : (if a=b then (value:ℤ)+1 else 0) =
        (if a=b then (value:ℤ) else 0)+(if a=b then (1:ℤ) else 0) := by
      split <;> simp
    rw [expand s,expand t]
    omega

private theorem zeroFlow_valid (c : ArcFlow V) (hc : ∀ e, 0 ≤ c e) (s t : V) :
    ValidArcFlow c s t 0 (fun _ => 0) := by
  constructor
  · simp
  · exact hc
  · intro u
    by_cases hs : u=s <;> by_cases ht : u=t <;> simp [divergence,hs,ht]

def cutArcFlow (f : ArcFlow V) (W : Finset V) : ℤ :=
  ∑ u ∈ W, ∑ v ∈ Wᶜ, f (u,v)

theorem ValidArcFlow.cut_value {c f : ArcFlow V} {s t : V} {value : ℕ}
    (valid : ValidArcFlow c s t value f) {W : Finset V} (hs : s ∈ W) (ht : t ∉ W) :
    cutArcFlow f W = value := by
  let internal := ∑ u ∈ W, ∑ v ∈ W, f (u,v)
  have zero : internal = 0 := by
    have opposite : internal = -internal := by
      calc
        _ = ∑ u ∈ W, ∑ v ∈ W, f (v,u) := sum_comm
        _ = -internal := by
          unfold internal
          simp only [← sum_neg_distrib]
          exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => valid.skew v u
    omega
  have divide : (∑ u ∈ W, divergence f u) = internal+cutArcFlow f W := by
    rw [show internal+cutArcFlow f W = ∑ u ∈ W, ((∑ v ∈ W, f (u,v))+
      ∑ v ∈ Wᶜ, f (u,v)) from sum_add_distrib.symm]
    exact sum_congr rfl (fun u _ => (sum_add_sum_compl W (fun v => f (u,v))).symm)
  have val : (∑ u ∈ W, divergence f u) = value := by
    simp only [valid.balance,sum_sub_distrib,sum_ite_eq',hs,ht,ite_true,ite_false,sub_zero]
  omega

private theorem ValidArcFlow.cut_capacity {c f : ArcFlow V} {s t : V} {value : ℕ}
    (valid : ValidArcFlow c s t value f) {W : Finset V} (hs : s ∈ W) (ht : t ∉ W) :
    (value:ℤ) ≤ cutArcFlow c W := by
  rw [← valid.cut_value hs ht]
  exact sum_le_sum (fun u _ => sum_le_sum (fun v _ => valid.upper (u,v)))

def residualReach (c f : ArcFlow V) (s : V) : Finset V := reaches (reverseArcs (residualArcs c f)) s

theorem mem_residualReach {c f : ArcFlow V} {s v : V} :
    v ∈ residualReach c f s ↔ Reach (residualArcs c f) s v := by
  rw [residualReach,mem_reaches,reach_reverseArcs]

private theorem ValidArcFlow.residualCut_capacity {c f : ArcFlow V} {s t : V} {value : ℕ}
    (valid : ValidArcFlow c s t value f) (stuck : ¬ Reach (residualArcs c f) s t) :
    cutArcFlow c (residualReach c f s) = value := by
  let W := residualReach c f s
  have hs : s ∈ W := mem_residualReach.mpr .refl
  have ht : t ∉ W := fun ht => stuck (mem_residualReach.mp ht)
  calc
    _ = cutArcFlow f W := by
      apply sum_congr rfl
      intro u hu
      apply sum_congr rfl
      intro v hv
      apply le_antisymm _ (valid.upper (u,v))
      by_contra! h
      have edge : Edge (residualArcs c f) u v := mem_filter.mpr ⟨mem_univ _,h⟩
      exact (mem_compl.mp hv) (mem_residualReach.mpr ((mem_residualReach.mp hu).tail edge))
    _ = _ := valid.cut_value hs ht

/-- Augment by one unit until the residual graph has no path or the supply is exhausted. -/
def unitAugmentations (c : ArcFlow V) (s t : V) : ℕ → ArcFlow V → ArcFlow V × ℕ
  | 0, f => (f,0)
  | k+1, f =>
    match routePath (residualArcs c f) s t with
    | none => (f,0)
    | some path =>
      let r := unitAugmentations c s t k (augmentArcFlow f path.toFinset)
      (r.1,r.2+1)

private theorem unitAugmentations_spec {c : ArcFlow V} {s t : V} (fuel : ℕ)
    (f : ArcFlow V) (v : ℕ) (valid : ValidArcFlow c s t v f) :
    let r := unitAugmentations c s t fuel f
    ValidArcFlow c s t (v+r.2) r.1 ∧ r.2 ≤ fuel ∧
      (r.2 < fuel → ¬ Reach (residualArcs c r.1) s t) := by
  induction fuel generalizing v f with
  | zero => simpa [unitAugmentations] using valid
  | succ fuel ih =>
    cases h : routePath (residualArcs c f) s t with
    | none =>
      have stuck : ¬ Reach (residualArcs c f) s t := by
        intro hr
        obtain ⟨path,hp⟩ := routePath_succeeds.mpr hr
        rw [h] at hp
        cases hp
      simp [unitAugmentations,h,valid,stuck]
    | some path =>
      let F := augmentArcFlow f path.toFinset
      let r := unitAugmentations c s t fuel F
      obtain ⟨hv,hb,stuck⟩ := ih F (v+1) (valid.augment (routePath_some h))
      simp only [unitAugmentations,h]
      change ValidArcFlow c s t (v+(r.2+1)) r.1 ∧ r.2+1 ≤ fuel+1 ∧
        (r.2+1 < fuel+1 → ¬ Reach (residualArcs c r.1) s t)
      change r.2 ≤ fuel at hb
      change r.2 < fuel → ¬ Reach (residualArcs c r.1) s t at stuck
      rw [show v+(r.2+1)=v+1+r.2 by omega]
      exact ⟨hv,by omega,fun h => stuck (by omega)⟩

def localArcCapacity (G : Arcs V) (d : V × V) (load : CutLoads V) : ArcFlow V :=
  fun e => if e ∈ intervalArcs G d then (2:ℤ)^(load e) else 0

private theorem localArcCapacity_nonneg (G : Arcs V) (d : V × V) (load : CutLoads V) (e : V × V) :
    0 ≤ localArcCapacity G d load e := by
  unfold localArcCapacity
  split <;> positivity

private theorem localArcCapacity_cut (G : Arcs V) (d : V × V) (load : CutLoads V) (W : Finset V) :
    cutArcFlow (localArcCapacity G d load) W =
      (cutMass (outgoingCut (intervalArcs G d) W) load:ℤ) := by
  unfold cutArcFlow localArcCapacity cutMass
  rw [← Finset.sum_product',← Finset.sum_filter]
  have h : (W ×ˢ Wᶜ).filter (fun e => e ∈ intervalArcs G d) =
      outgoingCut (intervalArcs G d) W := by
    ext e
    simp only [mem_filter,mem_product,mem_compl,outgoingCut]
    tauto
  rw [h,Nat.cast_sum]
  simp

private theorem cut_inter_interval (G : Arcs V) (d : V × V) (W : Finset V) :
    outgoingCut (intervalArcs G d) (W ∩ reachInterval G d) =
      outgoingCut (intervalArcs G d) W := by
  ext e
  by_cases h : e ∈ intervalArcs G d
  · obtain ⟨_,h1,h2⟩ := mem_filter.mp h
    simp [outgoingCut,h,h1,h2]
  · simp [outgoingCut,h]

/-- A violating thin cut found by at most |E(G)| unit augmentations. -/
def fastThinViolation (G : Arcs V) (d : V × V) (load : CutLoads V) : Option (Finset V) :=
  if d.1=d.2 then none
  else
    let c := localArcCapacity G d load
    let r := unitAugmentations c d.1 d.2 G.card (fun _ => 0)
    if r.2=G.card then none else
      some (residualReach c r.1 d.1 ∩ reachInterval G d)

private theorem fastThinViolation_check (G : Arcs V) (d : V × V) (load : CutLoads V)
    (reach : Reach G d.1 d.2) :
    match fastThinViolation G d load with
    | none => CutCovered G d load
    | some W => W ⊆ reachInterval G d ∧ d.1 ∈ W ∧ d.2 ∉ W ∧
        cutMass (outgoingCut (intervalArcs G d) W) load < G.card := by
  by_cases eq : d.1=d.2
  · simp only [fastThinViolation,eq,ite_true]
    intro W hW hs ht
    exact (ht (eq ▸ hs)).elim
  let c := localArcCapacity G d load
  let r := unitAugmentations c d.1 d.2 G.card (fun _ => 0)
  obtain ⟨valid,limit,stuck⟩ := unitAugmentations_spec G.card (fun _ => 0) 0
    (zeroFlow_valid c (localArcCapacity_nonneg G d load) d.1 d.2)
  have flow : ValidArcFlow c d.1 d.2 r.2 r.1 := by
    change ValidArcFlow c d.1 d.2 (0+r.2) r.1 at valid
    simpa only [zero_add] using valid
  change r.2 ≤ G.card at limit
  change r.2 < G.card → ¬ Reach (residualArcs c r.1) d.1 d.2 at stuck
  by_cases enough : r.2=G.card
  · simp only [fastThinViolation,ite_eq_right eq,show
      (unitAugmentations (localArcCapacity G d load) d.1 d.2 G.card fun _ => 0).2=G.card from enough,
      ite_true]
    intro W _ hs ht
    have bound := flow.cut_capacity hs ht
    rw [enough,localArcCapacity_cut] at bound
    exact_mod_cast bound
  · let W := residualReach c r.1 d.1
    have hl : r.2 < G.card := lt_of_le_of_ne limit enough
    have cut := flow.residualCut_capacity (stuck hl)
    change cutArcFlow (localArcCapacity G d load) W = r.2 at cut
    rw [localArcCapacity_cut] at cut
    have hs : d.1 ∈ W := mem_residualReach.mpr .refl
    have ht : d.2 ∉ W := fun h => stuck hl (mem_residualReach.mp h)
    simp only [fastThinViolation,ite_eq_right eq,show
      (unitAugmentations (localArcCapacity G d load) d.1 d.2 G.card fun _ => 0).2≠G.card from enough,
      ite_false]
    change W ∩ reachInterval G d ⊆ reachInterval G d ∧ d.1 ∈ W ∩ reachInterval G d ∧
       d.2 ∉ W ∩ reachInterval G d ∧ cutMass (outgoingCut (intervalArcs G d)
         (W ∩ reachInterval G d)) load < G.card
    refine ⟨inter_subset_right,mem_inter.mpr ⟨hs,mem_reachInterval.mpr ⟨.refl,reach⟩⟩,
      fun h => ht (mem_inter.mp h).1,?_⟩
    rw [cut_inter_interval]
    have e : cutMass (outgoingCut (intervalArcs G d) W) load = r.2 := by exact_mod_cast cut
    rw [e]
    exact hl

theorem fastThinViolation_eq_none {G : Arcs V} {d : V × V} {load : CutLoads V}
    (reach : Reach G d.1 d.2) : fastThinViolation G d load = none ↔ CutCovered G d load := by
  have h := fastThinViolation_check G d load reach
  cases eq : fastThinViolation G d load with
  | none =>
    rw [eq] at h
    exact ⟨fun _ => h,fun _ => rfl⟩
  | some W =>
    rw [eq] at h
    obtain ⟨hW,hs,ht,lt⟩ := h
    constructor
    · intro missing
      cases missing
    · intro coverage
      exact (lt.not_ge (coverage W hW hs ht)).elim

theorem fastThinViolation_some {G : Arcs V} {d : V × V} {load : CutLoads V}
    (reach : Reach G d.1 d.2) {W : Finset V} (h : fastThinViolation G d load = some W) :
    d.1 ∈ W ∧ d.2 ∉ W ∧ cutMass (outgoingCut (intervalArcs G d) W) load < G.card := by
  have check := fastThinViolation_check G d load reach
  rw [h] at check
  exact check.2

/-- The number of successful calls to the path selector is bounded by the supply. -/
theorem unitAugmentations_count {c : ArcFlow V} {s t : V} (fuel : ℕ)
    (hc : ∀ e, 0 ≤ c e) :
    (unitAugmentations c s t fuel (fun _ => 0)).2 ≤ fuel :=
  (unitAugmentations_spec fuel (fun _ => 0) 0 (zeroFlow_valid c hc s t)).2.1

/-- Start at zero and augment to the given supply or a saturated cut. -/
theorem unitAugmentations_zero_spec (c : ArcFlow V) (s t : V) (fuel : ℕ) (hc : ∀ e, 0 ≤ c e) :
    let result := unitAugmentations c s t fuel (fun _ => 0)
    ValidArcFlow c s t result.2 result.1 ∧ result.2 ≤ fuel ∧
      (result.2 < fuel → ¬ Reach (residualArcs c result.1) s t) := by
  simpa only [zero_add] using unitAugmentations_spec fuel (fun _ => 0) 0 (zeroFlow_valid c hc s t)

def findLowCapacityCut (c : ArcFlow V) (s t : V) (supply : ℕ) : Option (Finset V) :=
  let result := unitAugmentations c s t supply (fun _ => 0)
  if result.2 = supply then none else some (residualReach c result.1 s)

/-- A cut below the supplied capacity, or an actual flow proving coverage
of every separating cut. -/
theorem findLowCapacityCut_spec (c : ArcFlow V) (s t : V) (supply : ℕ) (hc : ∀ e, 0 ≤ c e) :
    match findLowCapacityCut c s t supply with
    | none => ValidArcFlow c s t supply (unitAugmentations c s t supply (fun _ => 0)).1
    | some W => s ∈ W ∧ t ∉ W ∧ cutArcFlow c W < (supply : ℤ) := by
  let result := unitAugmentations c s t supply (fun _ => 0)
  obtain ⟨valid, within, stopped⟩ := unitAugmentations_zero_spec c s t supply hc
  change ValidArcFlow c s t result.2 result.1 at valid
  change result.2 ≤ supply at within
  change result.2 < supply → ¬ Reach (residualArcs c result.1) s t at stopped
  by_cases enough : result.2 = supply
  · simp only [findLowCapacityCut, show (unitAugmentations c s t supply (fun _ => 0)).2 = supply from enough, ite_true]
    rw [enough] at valid
    exact valid
  · have small : result.2 < supply := lt_of_le_of_ne within enough
    have unreachable := stopped small
    let W := residualReach c result.1 s
    simp only [findLowCapacityCut, show (unitAugmentations c s t supply (fun _ => 0)).2 ≠ supply from enough,
      ite_false]
    refine ⟨mem_residualReach.mpr .refl, fun member => unreachable (mem_residualReach.mp member), ?_⟩
    change cutArcFlow c W < (supply : ℤ)
    rw [valid.residualCut_capacity unreachable]
    exact_mod_cast small

theorem findLowCapacityCut_eq_none {c : ArcFlow V} {s t : V} {supply : ℕ} (hc : ∀ e, 0 ≤ c e) :
    findLowCapacityCut c s t supply = none ↔
      ∀ W : Finset V, s ∈ W → t ∉ W → (supply : ℤ) ≤ cutArcFlow c W := by
  have checks := findLowCapacityCut_spec c s t supply hc
  cases h : findLowCapacityCut c s t supply with
  | none =>
    rw [h] at checks
    exact ⟨fun _ _ start finish => checks.cut_capacity start finish, fun _ => rfl⟩
  | some W =>
    rw [h] at checks
    obtain ⟨start, finish, capacity⟩ := checks
    constructor
    · intro equal
      cases equal
    · intro all
      exact (capacity.not_ge (all W start finish)).elim

end OnlineReachabilityPreservers
