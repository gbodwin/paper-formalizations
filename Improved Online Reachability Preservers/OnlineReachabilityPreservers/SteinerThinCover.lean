import OnlineReachabilityPreservers.SteinerCutFlow

/-! An integer implementation of online fractional covering for unweighted thin demands. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

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
theorem doubleCut_bounded {G C : Arcs V} {load : CutLoads V}
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
    match fastThinViolation G d load with
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
    cases h : fastThinViolation G d load with
    | none =>
      simp [thinCoverLoop,h,(fastThinViolation_eq_none (reach_mono sub feasible)).mp h]
      exact fun a b h => bounded (a,b) h
    | some W =>
      let C := outgoingCut (intervalArcs G d) W
      let r := thinCoverLoop G d fuel (doubleCut C load)
      obtain ⟨hs,ht,small⟩ := fastThinViolation_some (reach_mono sub feasible) h
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

/-- Each successful update consumes at least one unit of the total load budget. -/
theorem thinCoverLoop_load_progress (G Z : Arcs V) (sub : Z ⊆ G) (d : V × V)
    (feasible : Reach Z d.1 d.2) (fuel : ℕ) (load : CutLoads V)
    (bounded : ∀ e ∈ G, load e ≤ G.card.log2+1) :
    let out := thinCoverLoop G d fuel load
    loadTotal G load+out.2 ≤ loadTotal G out.1 :=
  (thinCoverLoop_spec G Z sub d feasible fuel load bounded).2.2.1

/-- The fractional phase makes at most one successful update for each unit
of the remaining total exponent budget. -/
theorem thinCoverLoop_updates (G Z : Arcs V) (sub : Z ⊆ G) (d : V × V)
    (feasible : Reach Z d.1 d.2) (fuel : ℕ) (load : CutLoads V)
    (bounded : ∀ e ∈ G, load e ≤ G.card.log2+1) :
    loadTotal G load+(thinCoverLoop G d fuel load).2 ≤ G.card*(G.card.log2+1) := by
  obtain ⟨_,caps,work,_,_,_⟩ := thinCoverLoop_spec G Z sub d feasible fuel load bounded
  apply work.trans
  unfold loadTotal
  exact (sum_le_sum caps).trans_eq (by simp)

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
