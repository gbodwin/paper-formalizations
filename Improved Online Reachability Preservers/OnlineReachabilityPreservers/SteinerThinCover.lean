import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sublists
import OnlineReachabilityPreservers.SteinerHubs

/-! An integer implementation of online fractional covering for unweighted thin demands. -/

namespace OnlineReachabilityPreservers

open Finset Relation

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Edges with both endpoints in the reachability interval of the demand. -/
def intervalArcs (G : Arcs V) (d : V × V) : Arcs V :=
  G.filter fun e => e.1 ∈ reachInterval G d ∧ e.2 ∈ reachInterval G d

theorem intervalArcs_subset (G : Arcs V) (d : V × V) : intervalArcs G d ⊆ G :=
  filter_subset _ _

/-- A feasible path in any input subgraph stays within the demand's reachability interval. -/
theorem reach_intervalArcs {G H : Arcs V} (sub : H ⊆ G) {d : V × V}
    (h : Reach H d.1 d.2) : Reach (H ∩ intervalArcs G d) d.1 d.2 := by
  have aux {v : V} (first : Reach H d.1 v) (last : Reach H v d.2) :
      Reach (H ∩ intervalArcs G d) d.1 v := by
    induction first with
    | refl => exact .refl
    | @tail u v first edge ih =>
      have fromU := last.head edge
      have hu := mem_reachInterval.mpr ⟨reach_mono sub first,reach_mono sub fromU⟩
      have hv := mem_reachInterval.mpr ⟨reach_mono sub (first.tail edge),reach_mono sub last⟩
      exact (ih fromU).tail (mem_inter.mpr ⟨edge,mem_filter.mpr ⟨sub edge,hu,hv⟩⟩)
  exact aux h .refl

/-- The arcs leaving a source side. -/
def outgoingCut (G : Arcs V) (W : Finset V) : Arcs V :=
  G.filter fun e => e.1 ∈ W ∧ e.2 ∉ W

omit [Fintype V] in
theorem outgoingCut_subset (G : Arcs V) (W : Finset V) : outgoingCut G W ⊆ G :=
  filter_subset _ _

omit [Fintype V] in
theorem cut_crossing {G : Arcs V} {s t : V} (walk : Reach G s t)
    {W : Finset V} (hs : s ∈ W) (ht : t ∉ W) : (outgoingCut G W).Nonempty := by
  induction walk with
  | refl => exact (ht hs).elim
  | @tail u v _ edge ih =>
    by_cases hu : u ∈ W
    · exact ⟨(u,v),mem_filter.mpr ⟨edge,hu,ht⟩⟩
    · exact ih hu

theorem intervalCut_hits_solution {G Z : Arcs V} (sub : Z ⊆ G) {d : V × V}
    (walk : Reach Z d.1 d.2) {W : Finset V} (hs : d.1 ∈ W) (ht : d.2 ∉ W) :
    (Z ∩ outgoingCut (intervalArcs G d) W).Nonempty := by
  obtain ⟨e,he⟩ := cut_crossing (reach_intervalArcs sub walk) hs ht
  obtain ⟨hh,hW⟩ := mem_filter.mp he
  obtain ⟨hZ,hI⟩ := mem_inter.mp hh
  exact ⟨e,mem_inter.mpr ⟨hZ,mem_filter.mpr ⟨hI,hW⟩⟩⟩

/-- Every source side in the reachable interval, enumerated in a fixed order. -/
def intervalCutSides (G : Arcs V) (d : V × V) : List (Finset V) :=
  (((reachInterval G d).sort (· ≤ ·)).sublists.map List.toFinset).filter
    (fun W => decide (d.1 ∈ W ∧ d.2 ∉ W))

theorem mem_intervalCutSides {G : Arcs V} {d : V × V} {W : Finset V} :
    W ∈ intervalCutSides G d ↔ W ⊆ reachInterval G d ∧ d.1 ∈ W ∧ d.2 ∉ W := by
  let U := reachInterval G d
  simp only [intervalCutSides,List.mem_filter,decide_eq_true_eq,List.mem_map,List.mem_sublists]
  constructor
  · rintro ⟨⟨l,hl,rfl⟩,hW⟩
    refine ⟨fun x hx => (mem_sort (r := (· ≤ ·))).mp (hl.subset (List.mem_toFinset.mp hx)),hW⟩
  · rintro ⟨hW,hs,ht⟩
    refine ⟨⟨W.sort (· ≤ ·),?_,sort_toFinset _ _⟩,hs,ht⟩
    apply List.sublist_of_subperm_of_sortedLE
    · apply List.subperm_of_subset (sort_nodup _ _)
      intro x hx
      simpa only [mem_sort] using hW ((mem_sort (r := (· ≤ ·))).mp hx)
    · exact (pairwise_sort _ _).sortedLE
    · exact (pairwise_sort _ _).sortedLE

/-- Edge loads are exponents. An edge of load x has capacity 2^x / |E(G)|. -/
abbrev CutLoads (V : Type*) := (V × V) → ℕ

def cutMass (E : Arcs V) (load : CutLoads V) : ℕ := ∑ e ∈ E, 2^(load e)

def loadTotal (E : Arcs V) (load : CutLoads V) : ℕ := ∑ e ∈ E, load e

/-- Find the first source side whose integer capacity is below |E(G)|. -/
def thinViolation (G : Arcs V) (d : V × V) (load : CutLoads V) : Option (Finset V) :=
  (intervalCutSides G d).find? fun W =>
    decide (cutMass (outgoingCut (intervalArcs G d) W) load < G.card)

def CutCovered (G : Arcs V) (d : V × V) (load : CutLoads V) : Prop :=
  ∀ W ⊆ reachInterval G d, d.1 ∈ W → d.2 ∉ W →
    G.card ≤ cutMass (outgoingCut (intervalArcs G d) W) load

theorem thinViolation_eq_none {G : Arcs V} {d : V × V} {load : CutLoads V} :
    thinViolation G d load = none ↔ CutCovered G d load := by
  simp only [thinViolation,List.find?_eq_none,decide_eq_true_eq,not_lt,CutCovered,mem_intervalCutSides]
  exact ⟨fun h W hs s t => h W ⟨hs,s,t⟩,fun h W ⟨hs,s,t⟩ => h W hs s t⟩

private theorem thinViolation_some {G : Arcs V} {d : V × V} {load : CutLoads V} {W : Finset V}
    (h : thinViolation G d load = some W) :
    d.1 ∈ W ∧ d.2 ∉ W ∧ cutMass (outgoingCut (intervalArcs G d) W) load < G.card := by
  obtain ⟨_,hs,ht⟩ := mem_intervalCutSides.mp (List.mem_of_find?_eq_some h)
  have hsmall := List.find?_some (p := fun A : Finset V =>
    decide (cutMass (outgoingCut (intervalArcs G d) A) load < G.card)) h
  exact ⟨hs,ht,of_decide_eq_true hsmall⟩

def doubleCut (C : Arcs V) (load : CutLoads V) : CutLoads V :=
  fun e => if e ∈ C then load e + 1 else load e

omit [Fintype V] in
theorem le_doubleCut (C : Arcs V) (load : CutLoads V) : load ≤ doubleCut C load := by
  intro e
  by_cases h : e ∈ C <;> simp [doubleCut,h]

omit [Fintype V] in
private theorem doubleCut_load (C E : Arcs V) (load : CutLoads V) :
    loadTotal E (doubleCut C load) = loadTotal E load + (E ∩ C).card := by
  have changeAt (e : V × V) : doubleCut C load e = load e + if e ∈ C then 1 else 0 := by
    by_cases h : e ∈ C <;> simp [doubleCut,h]
  simp only [loadTotal,changeAt,sum_add_distrib]
  rw [← sum_filter]
  simp
  congr 1

omit [Fintype V] in
private theorem doubleCut_mass (C E : Arcs V) (load : CutLoads V) :
    cutMass E (doubleCut C load) = cutMass E load + cutMass (E ∩ C) load := by
  have changeAt (e : V × V) :
      2^((doubleCut C load) e) = 2^(load e) + if e ∈ C then 2^(load e) else 0 := by
    by_cases h : e ∈ C <;> simp [doubleCut,h,pow_succ,Nat.mul_two]
  simp only [cutMass,changeAt,sum_add_distrib]
  rw [← sum_filter]
  congr 1

theorem CutCovered.mono {G : Arcs V} {d : V × V} {l r : CutLoads V}
    (h : CutCovered G d l) (le : l ≤ r) : CutCovered G d r := by
  intro W hs s t
  apply (h W hs s t).trans
  exact sum_le_sum (fun _ _ => Nat.pow_le_pow_right (by decide) (le _))

omit [Fintype V] in
/-- Every doubling leaves each exponent bounded by floor(log₂ |E|)+1. -/
private theorem doubleCut_bounded {G C : Arcs V} {load : CutLoads V}
    (small : cutMass C load < G.card)
    (bounded : ∀ e ∈ G, load e ≤ G.card.log2+1) :
    ∀ e ∈ G, doubleCut C load e ≤ G.card.log2+1 := by
  intro e he
  by_cases h : e ∈ C
  · simp only [doubleCut,ite_eq_left h, Nat.add_le_add_iff_right]
    have pow : 2^(load e) ≤ cutMass C load := by
      unfold cutMass
      exact single_le_sum (f := fun e => 2^(load e)) (fun _ _ => Nat.zero_le _) h
    exact (Nat.le_log2 (Nat.ne_of_gt (Nat.zero_lt_of_lt small))).mpr (pow.trans small.le)
  · simpa [doubleCut,h] using bounded e he

def thinCoverLoop (G : Arcs V) (d : V × V) : ℕ → CutLoads V → CutLoads V × ℕ
  | 0,load => (load,0)
  | k+1,load =>
    match thinViolation G d load with
    | none => (load,0)
    | some W =>
      let result := thinCoverLoop G d k (doubleCut (outgoingCut (intervalArcs G d) W) load)
      (result.1,result.2+1)

private theorem thinCoverLoop_spec (G Z : Arcs V) (sub : Z ⊆ G) (d : V × V)
    (feasible : Reach Z d.1 d.2) (fuel : ℕ) (load : CutLoads V)
    (bounded : ∀ e ∈ G, load e ≤ G.card.log2+1) :
    let r := thinCoverLoop G d fuel load
    load ≤ r.1 ∧ (∀ e ∈ G, r.1 e ≤ G.card.log2+1) ∧
      loadTotal G load+r.2 ≤ loadTotal G r.1 ∧
      cutMass G r.1 ≤ cutMass G load+G.card*r.2 ∧
      loadTotal Z load+r.2 ≤ loadTotal Z r.1 ∧
      (r.2 < fuel → CutCovered G d r.1) := by
  induction fuel generalizing load with
  | zero =>
    simp [thinCoverLoop]
    exact fun a b h => bounded (a,b) h
  | succ fuel ih =>
    cases h : thinViolation G d load with
    | none =>
      simp [thinCoverLoop,h,thinViolation_eq_none.mp h]
      exact fun a b h => bounded (a,b) h
    | some W =>
      let C := outgoingCut (intervalArcs G d) W
      let r := thinCoverLoop G d fuel (doubleCut C load)
      obtain ⟨hs,ht,small⟩ := thinViolation_some h
      have Csub : C ⊆ G := (outgoingCut_subset _ _).trans (intervalArcs_subset _ _)
      have touch : (Z ∩ C).Nonempty := intervalCut_hits_solution sub feasible hs ht
      have Gtouch : (G ∩ C).Nonempty := touch.mono (inter_subset_inter_right sub)
      obtain ⟨mono,cap,work,cost,charge,covered⟩ :=
        ih (doubleCut C load) (doubleCut_bounded small bounded)
      change loadTotal G (doubleCut C load)+r.2 ≤ loadTotal G r.1 at work
      change cutMass G r.1 ≤ cutMass G (doubleCut C load)+G.card*r.2 at cost
      change loadTotal Z (doubleCut C load)+r.2 ≤ loadTotal Z r.1 at charge
      change r.2 < fuel → CutCovered G d r.1 at covered
      simp only [thinCoverLoop,h]
      change load ≤ r.1 ∧ (∀ e ∈ G, r.1 e ≤ G.card.log2+1) ∧
        loadTotal G load+(r.2+1) ≤ loadTotal G r.1 ∧
        cutMass G r.1 ≤ cutMass G load+G.card*(r.2+1) ∧
        loadTotal Z load+(r.2+1) ≤ loadTotal Z r.1 ∧
        (r.2+1 < fuel+1 → CutCovered G d r.1)
      have workG := doubleCut_load C G load
      have workZ := doubleCut_load C Z load
      have mass := doubleCut_mass C G load
      rw [inter_eq_right.mpr Csub] at mass
      change cutMass C load < G.card at small
      refine ⟨(le_doubleCut C load).trans mono,cap,?_,?_,?_,fun ht => covered (by omega)⟩
      · have := Gtouch.card_pos
        omega
      · rw [Nat.mul_succ]
        omega
      · have := touch.card_pos
        omega

/-- The online fractional update. Fuel is bounded by the sum of load caps. -/
def thinCoverStep (G : Arcs V) (d : V × V) (load : CutLoads V) : CutLoads V :=
  (thinCoverLoop G d (G.card*(G.card.log2+1)+1) load).1

theorem thinCoverStep_spec (G Z : Arcs V) (sub : Z ⊆ G) (d : V × V)
    (feasible : Reach Z d.1 d.2) (load : CutLoads V)
    (bounded : ∀ e ∈ G, load e ≤ G.card.log2+1) :
    let r := thinCoverStep G d load
    load ≤ r ∧ (∀ e ∈ G, r e ≤ G.card.log2+1) ∧ CutCovered G d r ∧
      cutMass G r+G.card*loadTotal Z load ≤ cutMass G load+G.card*loadTotal Z r := by
  let fuel := G.card*(G.card.log2+1)+1
  let out := thinCoverLoop G d fuel load
  obtain ⟨mono,cap,work,cost,charge,covered⟩ := thinCoverLoop_spec G Z sub d feasible fuel load bounded
  have done : out.2 < fuel := by
    have bound : loadTotal G out.1 ≤ G.card*(G.card.log2+1) := by
      unfold loadTotal
      exact (sum_le_sum cap).trans_eq (by simp)
    have steps : out.2 ≤ loadTotal G out.1 := (Nat.le_add_left ..).trans work
    omega
  refine ⟨mono,cap,covered done,?_⟩
  change cutMass G out.1 + G.card*loadTotal Z load ≤ cutMass G load+G.card*loadTotal Z out.1
  change cutMass G out.1 ≤ cutMass G load+G.card*out.2 at cost
  change loadTotal Z load+out.2 ≤ loadTotal Z out.1 at charge
  have h := Nat.mul_le_mul_left G.card charge
  rw [Nat.mul_add] at h
  omega

/-- Apply the fractional update to each revealed demand in succession. -/
def thinCoverRun (G : Arcs V) (D : List (V × V)) : CutLoads V :=
  D.foldl (fun load d => thinCoverStep G d load) (fun _ => 0)

private theorem thinCoverRunFrom_spec (G Z : Arcs V) (sub : Z ⊆ G) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach Z d.1 d.2) (load : CutLoads V)
    (bounded : ∀ e ∈ G, load e ≤ G.card.log2+1) :
    let r := D.foldl (fun l d => thinCoverStep G d l) load
    load ≤ r ∧ (∀ e ∈ G, r e ≤ G.card.log2+1) ∧
      (∀ d ∈ D, CutCovered G d r) ∧
      cutMass G r+G.card*loadTotal Z load ≤ cutMass G load+G.card*loadTotal Z r := by
  induction D generalizing load with
  | nil =>
    simp
    exact fun a b h => bounded (a,b) h
  | cons d ds ih =>
    let first := thinCoverStep G d load
    let last := ds.foldl (fun l d => thinCoverStep G d l) first
    obtain ⟨h1,cap1,covered1,cost1⟩ :=
      thinCoverStep_spec G Z sub d (feasible _ List.mem_cons_self) load bounded
    obtain ⟨h2,cap2,covered2,cost2⟩ :=
      ih (fun e he => feasible _ (List.mem_cons_of_mem _ he)) first cap1
    change load ≤ last ∧ (∀ e ∈ G, last e ≤ G.card.log2+1) ∧
      (∀ e ∈ d::ds, CutCovered G e last) ∧
      cutMass G last+G.card*loadTotal Z load ≤ cutMass G load+G.card*loadTotal Z last
    refine ⟨h1.trans h2,cap2,?_,?_⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | h
      · exact covered1.mono h2
      · exact covered2 _ h
    · change cutMass G first+G.card*loadTotal Z load ≤ cutMass G load+G.card*loadTotal Z first at cost1
      change cutMass G last+G.card*loadTotal Z first ≤ cutMass G first+G.card*loadTotal Z last at cost2
      omega

/-- Integer capacity totaling at most |E(G)| times 1+OPT(1+log₂|E(G)|),
while covering every cut of each revealed request. -/
theorem thinCoverRun_bound (G Z : Arcs V) (sub : Z ⊆ G) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach Z d.1 d.2) :
    let load := thinCoverRun G D
    (∀ d ∈ D, CutCovered G d load) ∧
      cutMass G load ≤ G.card*(1+Z.card*(G.card.log2+1)) := by
  let load := thinCoverRun G D
  obtain ⟨_,caps,covered,cost⟩ := thinCoverRunFrom_spec G Z sub D feasible (fun _ => 0) (by simp)
  change cutMass G load+G.card*loadTotal Z (fun _ => 0) ≤
    cutMass G (fun _ => 0)+G.card*loadTotal Z load at cost
  simp [loadTotal,cutMass] at cost
  have hZ : (∑ e ∈ Z, load e) ≤ Z.card*(G.card.log2+1) :=
    (sum_le_sum (fun e he => caps e (sub he))).trans_eq (by simp)
  refine ⟨covered,cost.trans ?_⟩
  rw [Nat.mul_add,Nat.mul_one]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hZ) _

theorem thinCoverRun_prefix (G : Arcs V) {D E : List (V × V)} (pref : D <+: E)
    (feasible : ∀ d ∈ E, Reach G d.1 d.2) : thinCoverRun G D ≤ thinCoverRun G E := by
  obtain ⟨F,rfl⟩ := pref
  have caps := (thinCoverRunFrom_spec G G Subset.rfl D
    (fun d hd => feasible _ (List.mem_append_left _ hd)) (fun _ => 0) (by simp)).2.1
  have h := (thinCoverRunFrom_spec G G Subset.rfl F
    (fun d hd => feasible _ (List.mem_append_right _ hd)) (thinCoverRun G D) caps).1
  simpa [thinCoverRun,List.foldl_append] using h

end OnlineReachabilityPreservers
