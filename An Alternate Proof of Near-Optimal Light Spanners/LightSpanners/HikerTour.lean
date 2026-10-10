import LightSpanners.HikerDay

namespace LightSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {w : Sym2 V → ℝ} (C : UnitSpanningCycle G w)

namespace WalkSquad

noncomputable def bucketSteps (eps : ℝ) (k i : ℕ) : ℕ := ⌊eps*k*2^i/2⌋₊

noncomputable def bucketTraversals (eps : ℝ) (k i : ℕ) (ds : List G.Dart) : ℕ :=
  2*(bucketSteps eps k i+1)*ds.length

/-- Actual composition of all bucket days preserves the endpoint permutation
and has the exact sum of all layer traversal counts. -/
theorem exists_bucket_tour (ds : ℕ → List G.Dart) (J : ℕ)
    (hds : ∀ i < J, ((ds i).map Dart.edge).Nodup)
    (hd : ∀ i < J, ∀ d ∈ ds i, d.edge ∉ C.cycle.edges)
    (hw : ∀ i < J, ∀ d ∈ ds i, (2:ℝ)^i ≤ w d.edge ∧ w d.edge < 2^(i+1))
    {eps : ℝ} {k : ℕ} (heps : 0 ≤ eps) :
    ∃ A : WalkSquad G, (∀ v, C.BucketMonotoneWalk eps k true J (A.path v)) ∧
      totalChords C A = ∑ i ∈ range J, bucketTraversals eps k i (ds i) := by
  induction J with
  | zero => exact ⟨refl G,fun v => .nil v,by simp⟩
  | succ J ih =>
    obtain ⟨A,hA,hcountA⟩ := ih (fun i hi => hds i (by omega))
      (fun i hi => hd i (by omega)) (fun i hi => hw i (by omega))
    obtain ⟨B,hB,hcountB⟩ := exists_bucket_day C (ds J) J (bucketSteps eps k J)
      (hds J (by omega)) (hd J (by omega)) (hw J (by omega))
      (Nat.floor_le (by positivity : (0:ℝ) ≤ eps*k*2^J/2))
    refine ⟨A.trans B,fun v => .snoc (hA v) (hB (A.position v)),?_⟩
    rw [totalChords_trans,hcountA,hcountB,sum_range_succ]
    rfl

omit [DecidableEq V] [Fintype V] in
theorem bucket_weight_le_traversals (eps : ℝ) (k i : ℕ) (ds : List G.Dart)
    (heps : 0 < eps) (hk : 0 < k)
    (hw : ∀ d ∈ ds, w d.edge < (2:ℝ)^(i+1)) :
    eps*k*(ds.map (fun d => w d.edge)).sum/4 ≤ bucketTraversals eps k i ds := by
  induction ds with
  | nil => simp [bucketTraversals]
  | cons d ds ih =>
    have h := floor_plus_one_layer_bound heps hk (hw d (by simp))
    have ht := ih (fun e he => hw e (by simp [he]))
    simp only [List.map_cons,List.sum_cons]
    simp only [bucketTraversals,List.length_cons,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
      Nat.cast_ofNat] at ⊢ ht
    change eps*k*(w d.edge+(List.map (fun d => w d.edge) ds).sum)/4 ≤ _
    dsimp only [bucketSteps] at ht ⊢
    nlinarith

/-- A weak counting theorem with ambient safety parameter k fixed, even when
the produced walk contains more than k chords. All bucket walks are actual. -/
theorem exists_long_bucket_tour (ds : ℕ → List G.Dart) (J : ℕ)
    (hds : ∀ i < J, ((ds i).map Dart.edge).Nodup)
    (hd : ∀ i < J, ∀ d ∈ ds i, d.edge ∉ C.cycle.edges)
    (hw : ∀ i < J, ∀ d ∈ ds i, (2:ℝ)^i ≤ w d.edge ∧ w d.edge < 2^(i+1))
    {eps : ℝ} {k : ℕ} (heps : 0 < eps) (hk : 0 < k)
    (hweight : 4*(Fintype.card V : ℝ) ≤
      eps*(∑ i ∈ range J, ((ds i).map (fun d => w d.edge)).sum)) :
    ∃ (u v : V) (p : G.Walk u v), C.BucketMonotoneWalk eps k true J p ∧
      k ≤ (C.chordEdges p).length := by
  let : Nonempty V := ⟨C.base⟩
  obtain ⟨A,hA,hcount⟩ := exists_bucket_tour C ds J hds hd hw (k := k) heps.le
  have hsum : eps*k*(∑ i ∈ range J, ((ds i).map (fun d => w d.edge)).sum)/4 ≤
      (∑ i ∈ range J, bucketTraversals eps k i (ds i) : ℕ) := by
    have hs := Finset.sum_le_sum (s := range J) (fun i hi =>
      bucket_weight_le_traversals eps k i (ds i) heps hk
        (fun d hd => (hw i (mem_range.mp hi) d hd).2))
    simpa [div_eq_mul_inv,mul_sum,sum_mul,Nat.cast_sum] using hs
  have hcount' : Fintype.card V*k ≤ totalChords C A := by
    rw [hcount]
    have hnon : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hmul := mul_le_mul_of_nonneg_right hweight hnon
    have hh : ((Fintype.card V*k : ℕ) : ℝ) ≤
      (∑ i ∈ range J, bucketTraversals eps k i (ds i) : ℕ) := by
      simp only [Nat.cast_mul]
      nlinarith
    exact_mod_cast hh
  obtain ⟨u,hu⟩ := exists_long C A k hcount'
  exact ⟨u,A.position u,A.path u,hA u,hu⟩

end WalkSquad
end LightSpanners
