import DirectedFlowCutGap.ChargedCutSelection

/-!
# Amplification with the charges of all executed samples

The input tree is already lowered at the shared rejection limit. Each
sample's own charge is retained. A binary minimum selects the original
winner, and the final charge includes all the samples and the selection.
-/

namespace DirectedFlowCutGap.ChargedAmplification

open FiniteDrawTrees LazyFairBitTrees BinaryFractionalRows BinaryRational
open EncodedVertexSolver (Output)

private theorem map_cons {A B : Type} (f : A → B) (a : A) {k : ℕ} (xs : Fin k → A) :
    (fun i => f (Fin.cons (α := fun _ => A) a xs i)) =
      Fin.cons (α := fun _ => B) (f a) (fun i => f (xs i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem map_samples {A B : Type} (f : A → B) (t : FiniteDrawTrees.Tree A) (k : ℕ) :
    map (fun xs i => f (xs i)) (EncodedAmplification.samples t k) =
      EncodedAmplification.samples (map f t) k := by
  induction k with
  | zero =>
    change FiniteDrawTrees.Tree.pure (fun i => f (Fin.elim0 i)) = .pure Fin.elim0
    exact congrArg FiniteDrawTrees.Tree.pure (funext (fun i => i.elim0))
  | succ k ih =>
    change (fun xs i => f (xs i)) <$> EncodedAmplification.samples t k =
      EncodedAmplification.samples (f <$> t) k at ih
    change (fun xs i => f (xs i)) <$> (t >>= fun a =>
      Fin.cons (α := fun _ => A) a <$> EncodedAmplification.samples t k) =
      (f <$> t) >>= fun a => Fin.cons (α := fun _ => B) a <$> EncodedAmplification.samples (f <$> t) k
    simp only [map_bind, bind_map_left]
    congr 1
    funext a
    rw [← ih]
    simp only [Functor.map_map]
    congr 1
    funext xs
    exact map_cons f a xs

theorem lower_samples {A : Type} (T : ℕ) (t : FiniteDrawTrees.Tree A) (k : ℕ) :
    lower T (EncodedAmplification.samples t k) =
      EncodedAmplification.samples (lower T t) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change lower T (t >>= fun a => Fin.cons (α := fun _ => A) a <$> EncodedAmplification.samples t k) =
      lower T t >>= fun a => Fin.cons (α := fun _ => A) a <$> EncodedAmplification.samples (lower T t) k
    simp only [ChargedCutSelection.lower_bind, ← ChargedUniformRounding.map_lower, ih]

private theorem sample_support {A : Type} (t : FiniteDrawTrees.Tree A) {k : ℕ}
    {xs : Fin k → A} (h : xs ∈ (ideal (EncodedAmplification.samples t k)).support) :
    ∀ i, xs i ∈ (ideal t).support := by
  induction k with
  | zero => exact fun i => i.elim0
  | succ k ih =>
    have hl : ideal (EncodedAmplification.samples t (k + 1)) =
        (ideal t).bind (fun a => (ideal (EncodedAmplification.samples t k)).map
          (Fin.cons (α := fun _ => A) a)) := by
      change law uniformDraw
        (FiniteDrawTrees.bind t (fun a =>
          map (Fin.cons (α := fun _ => A) a) (EncodedAmplification.samples t k))) = _
      simp only [ideal, law_bind, law_map]
    rw [hl] at h
    obtain ⟨a, ha, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
    obtain ⟨tail, ht, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    exact Fin.cases ha (fun i => ih ht i)

private def select {n : ℕ} (costs : Row n) (extra : ℕ)
    (xs : Fin (extra + 1) → Output n × ℕ) : Output n × ℕ :=
  let winner := BinaryCutPriceSelection.minimum (BinaryCutPriceSelection.cutScore costs) extra
    (fun i => (xs i).1)
  let paid := (List.ofFn fun i => (xs i).2).sum
  (winner.value, paid + winner.charge + 20 * (extra + 1)^2 + 5)

def tree {n : ℕ} (costs : Row n) (t : FiniteDrawTrees.Tree (Output n × ℕ)) (extra : ℕ) :
    FiniteDrawTrees.Tree (Output n × ℕ) :=
  map (select costs extra) (EncodedAmplification.samples t (extra + 1))

theorem tree_value {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (t : FiniteDrawTrees.Tree (Output n × ℕ)) (extra : ℕ) :
    map Prod.fst (tree D.costs t extra) =
      EncodedAmplification.selectedTree (EncodedVertexAmplification.codePrice (BinaryFractionalGuesses.decodeInput D))
        (map Prod.fst t) extra := by
  unfold tree EncodedAmplification.selectedTree
  rw [← map_samples _ t]
  let s := EncodedAmplification.samples t (extra + 1)
  change Prod.fst <$> (select D.costs extra <$> s) =
    EncodedAmplification.minimum (EncodedVertexAmplification.codePrice (BinaryFractionalGuesses.decodeInput D)) extra <$>
      ((fun xs i => (xs i).1) <$> s)
  simp only [Functor.map_map]
  congr 1
  funext xs
  exact (BinaryCutPriceSelection.minimum_refines _ _
    (BinaryCutPriceSelection.cutScore_decodes D) extra (fun i => (xs i).1)).1

def budget (extra n B sampleBudget : ℕ) : ℕ :=
  (extra + 1) * sampleBudget + BinaryCutPriceSelection.selectionBound extra n B + 20 * (extra + 1)^2 + 5

theorem tree_charge {n B : ℕ} (costs : Row n) (t : FiniteDrawTrees.Tree (Output n × ℕ)) (extra sampleBudget : ℕ)
    (hB : 1 ≤ B) (hc : ∀ i, StoredBounded (get costs i) B)
    (hround : ∀ a ∈ (ideal t).support, a.2 ≤ sampleBudget)
    {out : Output n × ℕ} (ho : out ∈ (ideal (tree costs t extra)).support) :
    out.2 ≤ budget extra n B sampleBudget := by
  simp only [tree, ideal, law_map] at ho
  obtain ⟨xs, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
  have hs : (List.ofFn fun i => (xs i).2).sum ≤ (extra + 1) * sampleBudget := by
    rw [List.sum_ofFn]
    calc
      (∑ i, (xs i).2) ≤ ∑ _i : Fin (extra + 1), sampleBudget :=
        Finset.sum_le_sum (fun i _ => hround _ (sample_support t hx i))
      _ = _ := by simp
  have hw := (BinaryCutPriceSelection.minimum_charge
    (BinaryCutPriceSelection.cutScore costs) extra (fun i => (xs i).1)
    (n * (B + 1) + 1) (sumBound n B)
    (fun i => BinaryCutPriceSelection.cutScore_charge costs (xs i).1 hB hc)).2
  change (BinaryCutPriceSelection.minimum _ _ _).charge ≤
    BinaryCutPriceSelection.selectionBound extra n B at hw
  dsimp only [select]
  unfold budget
  omega

end DirectedFlowCutGap.ChargedAmplification
