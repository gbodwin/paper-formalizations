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
    let interval := reachInterval G d
    let edges := G.filter (fun e => e.1 ∈ interval ∧ e.2 ∈ interval)
    let c : ArcFlow V := fun e => if e ∈ edges then (2 : ℤ) ^ load e else 0
    let r := unitAugmentations c d.1 d.2 G.card (fun _ => 0)
    if r.2=G.card then none else
      some (residualReach c r.1 d.1 ∩ interval)

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
  have computation : fastThinViolation G d load =
      if r.2 = G.card then none else some (residualReach c r.1 d.1 ∩ reachInterval G d) := by
    simp only [fastThinViolation, ite_eq_right eq]
    rfl
  rw [computation]
  by_cases enough : r.2=G.card
  · rw [ite_eq_left enough]
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
    rw [ite_eq_right enough]
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

/-- The arcs carrying positive net flow. -/
def positiveFlowArcs (flow : ArcFlow V) : Arcs V :=
  univ.filter fun e => 0 < flow e

private theorem ValidArcFlow.positive_reach {c flow : ArcFlow V} {s t : V} {value : ℕ}
    (valid : ValidArcFlow c s t value flow) (positive : 0 < value) :
    Reach (positiveFlowArcs flow) s t := by
  by_contra stuck
  let W := reaches (reverseArcs (positiveFlowArcs flow)) s
  have follows (u : V) : u ∈ W ↔ Reach (positiveFlowArcs flow) s u := by
    change u ∈ reaches (reverseArcs (positiveFlowArcs flow)) s ↔ Reach (positiveFlowArcs flow) s u
    rw [mem_reaches, reach_reverseArcs]
  have start : s ∈ W := (follows s).mpr .refl
  have finish : t ∉ W := fun h => stuck ((follows t).mp h)
  have total : cutArcFlow flow W ≤ 0 := by
    unfold cutArcFlow
    apply sum_nonpos
    intro u hu
    apply sum_nonpos
    intro v hv
    by_contra! h
    have edge : Edge (positiveFlowArcs flow) u v := mem_filter.mpr ⟨mem_univ _, h⟩
    exact (mem_compl.mp hv) ((follows v).mpr (((follows u).mp hu).tail edge))
  rw [valid.cut_value start finish] at total
  omega

private def consumeArcFlow (flow : ArcFlow V) (path : Arcs V) : ArcFlow V :=
  fun e => flow e - inPath path e + inPath path e.swap

private theorem ValidArcFlow.consume {c flow : ArcFlow V} {s t : V} {value : ℕ}
    (hc : ∀ e, 0 ≤ c e) (valid : ValidArcFlow c s t (value + 1) flow)
    {p : List (V × V)} (path : SimpleWalk (positiveFlowArcs flow) s t p) :
    ValidArcFlow c s t value (consumeArcFlow flow p.toFinset) := by
  constructor
  · intro a b
    have fact := valid.skew a b
    simp only [consumeArcFlow, Prod.swap_prod_mk]
    omega
  · intro e
    have upper := valid.upper e
    have zero := hc e
    have nonnegative : 0 ≤ inPath p.toFinset e := by unfold inPath; split <;> norm_num
    by_cases reverseUsed : e.swap ∈ p.toFinset
    · have pos := (mem_filter.mp (path.1.mem (List.mem_toFinset.mp reverseUsed))).2
      have opposite : flow e = -flow e.swap := valid.skew e.1 e.2
      change flow e - inPath p.toFinset e + inPath p.toFinset e.swap ≤ c e
      have reverseMark : inPath p.toFinset e.swap = 1 := by simp [inPath, reverseUsed]
      omega
    · change flow e - inPath p.toFinset e + inPath p.toFinset e.swap ≤ c e
      have reverseMark : inPath p.toFinset e.swap = 0 := by simp [inPath, reverseUsed]
      omega
  · intro a
    have hs := valid.balance a
    have hd := pathDivergence path.1 path.2 a
    simp only [divergence, consumeArcFlow, augmentArcFlow, Prod.swap_prod_mk,
      sum_add_distrib, sum_sub_distrib, zero_add, Int.natCast_add, Int.cast_ofNat_Int] at hs hd ⊢
    have split (r : V) : (if a = r then (value : ℤ) + 1 else 0) =
        (if a = r then (value : ℤ) else 0) + (if a = r then (1 : ℤ) else 0) := by
      by_cases eq : a = r <;> simp [eq]
    rw [split s, split t] at hs
    omega

private theorem consume_max_add {c flow : ArcFlow V} {s t : V} {value : ℕ}
    (valid : ValidArcFlow c s t value flow) {p : List (V × V)}
    (path : SimpleWalk (positiveFlowArcs flow) s t p) (e : V × V) :
    max 0 (consumeArcFlow flow p.toFinset e) + inPath p.toFinset e = max 0 (flow e) := by
  have skew : flow e = -flow e.swap := valid.skew e.1 e.2
  by_cases forwards : e ∈ p.toFinset
  · have pos := (mem_filter.mp (path.1.mem (List.mem_toFinset.mp forwards))).2
    have noReverse : e.swap ∉ p.toFinset := by
      intro opposite
      have reversePos := (mem_filter.mp (path.1.mem (List.mem_toFinset.mp opposite))).2
      omega
    simp only [consumeArcFlow, inPath, forwards, noReverse, ↓reduceIte, add_zero]
    omega
  · by_cases reverseUsed : e.swap ∈ p.toFinset
    · have reversePos := (mem_filter.mp (path.1.mem (List.mem_toFinset.mp reverseUsed))).2
      simp only [consumeArcFlow, inPath, forwards, reverseUsed, ↓reduceIte, sub_zero, add_zero]
      omega
    · simp [consumeArcFlow, inPath, forwards, reverseUsed]

def arcUsage (paths : List (List (V × V))) (e : V × V) : ℕ :=
  (paths.filter fun p => decide (e ∈ p)).length

omit [Fintype V] in
private theorem arcUsage_cons (p : List (V × V)) (paths : List (List (V × V))) (e : V × V) :
    ((arcUsage (p :: paths) e : ℕ) : ℤ) =
      (arcUsage paths e : ℤ) + inPath p.toFinset e := by
  by_cases h : e ∈ p
  · simp [arcUsage, inPath, h]
  · simp [arcUsage, inPath, h]

/-- An integer flow of value k supplies k unit paths. Their usage of every
arc is at most the positive part of its original net flow. -/
theorem ValidArcFlow.decompose_paths {c flow : ArcFlow V} {s t : V} {value : ℕ}
    (hc : ∀ e, 0 ≤ c e) (valid : ValidArcFlow c s t value flow) :
    ∃ paths : List (List (V × V)), paths.length = value ∧
      (∀ p ∈ paths, SimpleWalk (positiveFlowArcs flow) s t p) ∧
      (∀ e, (arcUsage paths e : ℤ) ≤ max 0 (flow e)) := by
  induction value generalizing flow with
  | zero => exact ⟨[], rfl, by simp, fun _ => by simp [arcUsage]⟩
  | succ value ih =>
    obtain ⟨p, found⟩ := routePath_succeeds.mpr (valid.positive_reach (Nat.succ_pos value))
    have path := routePath_some found
    let next := consumeArcFlow flow p.toFinset
    have nextValid : ValidArcFlow c s t value next := valid.consume hc path
    obtain ⟨rest, length, walks, load⟩ := ih nextValid
    refine ⟨p :: rest, by simp [length], ?_, ?_⟩
    · intro q used
      rcases List.mem_cons.mp used with rfl | member
      · exact path
      · apply (walks q member).mono
        intro e active
        have pos := (mem_filter.mp active).2
        have preserves := consume_max_add valid path e
        have hNonneg : 0 ≤ inPath p.toFinset e := by unfold inPath; split <;> norm_num
        have now : 0 < flow e := by
          change 0 < next e at pos
          change max 0 (next e) + inPath p.toFinset e = max 0 (flow e) at preserves
          omega
        exact mem_filter.mpr ⟨mem_univ _, now⟩
    · intro e
      rw [arcUsage_cons]
      have eq := consume_max_add valid path e
      exact (add_le_add (load e) le_rfl).trans_eq eq

/-- The unit-path usage lies below the original capacity, including on
arcs with zero capacity. -/
theorem ValidArcFlow.decompose_capacity {c flow : ArcFlow V} {s t : V} {value : ℕ}
    (hc : ∀ e, 0 ≤ c e) (valid : ValidArcFlow c s t value flow) :
    ∃ paths : List (List (V × V)), paths.length = value ∧
      (∀ p ∈ paths, SimpleWalk (positiveFlowArcs flow) s t p) ∧
      (∀ e, (arcUsage paths e : ℤ) ≤ c e) := by
  obtain ⟨paths, length, routes, load⟩ := valid.decompose_paths hc
  exact ⟨paths, length, routes, fun e => (load e).trans (max_le (hc e) (valid.upper e))⟩

/-- A separating cut whose capacity equals the flow value contains every
vertex reachable from the source in the residual graph. -/
theorem ValidArcFlow.residualReach_subset_of_tight_cut {c f : ArcFlow V} {s t : V} {value : ℕ}
    (valid : ValidArcFlow c s t value f) {W : Finset V} (start : s ∈ W) (finish : t ∉ W)
    (tight : cutArcFlow c W = value) : residualReach c f s ⊆ W := by
  have closed {u v : V} (inside : u ∈ W) (edge : Edge (residualArcs c f) u v) : v ∈ W := by
    by_contra! outside
    have crossing : (u,v) ∈ W ×ˢ Wᶜ := mem_product.mpr ⟨inside,mem_compl.mpr outside⟩
    have strict : (∑ e ∈ W ×ˢ Wᶜ, f e) < ∑ e ∈ W ×ˢ Wᶜ, c e :=
      sum_lt_sum (fun e _ => valid.upper e) ⟨(u,v),crossing,(mem_filter.mp edge).2⟩
    rw [sum_product W Wᶜ f,sum_product W Wᶜ c] at strict
    change cutArcFlow f W < cutArcFlow c W at strict
    rw [valid.cut_value start finish,tight] at strict
    exact (lt_irrefl _ strict)
  have stays {v : V} (path : Reach (residualArcs c f) s v) : v ∈ W := by
    induction path with
    | refl => exact start
    | tail _ edge ih => exact closed ih edge
  exact fun _ reachable => stays (mem_residualReach.mp reachable)

/-- The source side of a stalled valid flow is the same for every stalled
valid flow with the same capacities and terminals, and their values agree. -/
theorem ValidArcFlow.residualReach_canonical {c f g : ArcFlow V} {s t : V} {sent other : ℕ}
    (first : ValidArcFlow c s t sent f) (second : ValidArcFlow c s t other g)
    (stalledF : ¬ Reach (residualArcs c f) s t) (stalledG : ¬ Reach (residualArcs c g) s t) :
    sent = other ∧ residualReach c f s = residualReach c g s := by
  have startF : s ∈ residualReach c f s := mem_residualReach.mpr .refl
  have startG : s ∈ residualReach c g s := mem_residualReach.mpr .refl
  have finishF : t ∉ residualReach c f s := fun h => stalledF (mem_residualReach.mp h)
  have finishG : t ∉ residualReach c g s := fun h => stalledG (mem_residualReach.mp h)
  have tightF := first.residualCut_capacity stalledF
  have tightG := second.residualCut_capacity stalledG
  have upperF := (first.cut_capacity startG finishG).trans_eq tightG
  have upperG := (second.cut_capacity startF finishF).trans_eq tightF
  have equal : sent = other := by omega
  cases equal
  exact ⟨rfl,Subset.antisymm (first.residualReach_subset_of_tight_cut startG finishG tightG)
    (second.residualReach_subset_of_tight_cut startF finishF tightF)⟩

/-- A valid flow attaining the supply or stalling has the same terminal
value as the reference augmentations, and gives their exact cut when its
value is below the supply. Its choices of augmenting paths may differ. -/
theorem unitAugmentations_terminal_compare {c f : ArcFlow V} {s t : V} {supply sent : ℕ}
    (nonnegative : ∀ e, 0 ≤ c e) (valid : ValidArcFlow c s t sent f)
    (within : sent ≤ supply) (stalled : sent < supply → ¬ Reach (residualArcs c f) s t) :
    let ref := unitAugmentations c s t supply (fun _ => 0)
    sent = ref.2 ∧ (sent < supply → residualReach c f s = residualReach c ref.1 s) := by
  let ref := unitAugmentations c s t supply (fun _ => 0)
  obtain ⟨refValid,refWithin,refStalled⟩ := unitAugmentations_zero_spec c s t supply nonnegative
  change ValidArcFlow c s t ref.2 ref.1 at refValid
  change ref.2 ≤ supply at refWithin
  change ref.2 < supply → ¬ Reach (residualArcs c ref.1) s t at refStalled
  by_cases enough : sent = supply
  · have refEnough : ref.2 = supply := by
      by_contra! lower
      have noRoute := refStalled (lt_of_le_of_ne refWithin lower)
      have source : s ∈ residualReach c ref.1 s := mem_residualReach.mpr .refl
      have target : t ∉ residualReach c ref.1 s := fun h => noRoute (mem_residualReach.mp h)
      have cap := (valid.cut_capacity source target).trans_eq (refValid.residualCut_capacity noRoute)
      omega
    exact ⟨enough.trans refEnough.symm,fun small => (small.ne enough).elim⟩
  · have small := lt_of_le_of_ne within enough
    have noRoute := stalled small
    have source : s ∈ residualReach c f s := mem_residualReach.mpr .refl
    have target : t ∉ residualReach c f s := fun h => noRoute (mem_residualReach.mp h)
    have cap := (refValid.cut_capacity source target).trans_eq (valid.residualCut_capacity noRoute)
    obtain ⟨same,side⟩ := valid.residualReach_canonical refValid noRoute (refStalled (by omega))
    exact ⟨same,fun _ => side⟩

/-- The bounded cut separator depends only on the terminal flow condition. -/
theorem findLowCapacityCut_eq_terminal {c f : ArcFlow V} {s t : V} {supply sent : ℕ}
    (nonnegative : ∀ e, 0 ≤ c e) (valid : ValidArcFlow c s t sent f)
    (within : sent ≤ supply) (stalled : sent < supply → ¬ Reach (residualArcs c f) s t) :
    findLowCapacityCut c s t supply = if sent = supply then none else some (residualReach c f s) := by
  obtain ⟨same,side⟩ := unitAugmentations_terminal_compare nonnegative valid within stalled
  unfold findLowCapacityCut
  dsimp only
  rw [← same]
  by_cases enough : sent = supply
  · simp [enough]
  · simp [enough,side (lt_of_le_of_ne within enough)]

end OnlineReachabilityPreservers
