import DirectedFlowCutGap.EncodedIntegerRounding
import DirectedFlowCutGap.RetainedBinarySampler

/-!
# Word charges of the actual integer rounding dispatcher

The hard branch uses the binary sampler with the retained controller,
including its original restart parameters and epoch order. Erasing charges
gives exactly the ordinary bounded fair-bit tree in all three regimes.
The hard branch budget covers the retained controller and sampler. Regime
tests, parameter computation, candidate-dictionary construction and the
initial demand mask have separate preparation costs.
-/

namespace DirectedFlowCutGap.ChargedIntegerRounding

open FiniteDrawTrees RetainedGridState IntegerEpochParameters IntegerAdaptiveExecution
open LazyFairBitTrees

private theorem map_lower {A B : Type} (T : ℕ) (f : A → B) (t : FiniteDrawTrees.Tree A) :
    f <$> lower T t = lower T (f <$> t) := by
  induction t with
  | pure a => rfl
  | draw n hn next ih =>
    change f <$> (rejection n hn T >>= fun r => lower T (next r.value)) =
      rejection n hn T >>= fun r => lower T (f <$> next r.value)
    simp only [map_bind, ih]

private def hard {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    FiniteDrawTrees.Tree (Flags n × ℕ) :=
  let F := CandidateEnumeration.make n L
  let initial := RetainedDemandMask.initial (EncodedIntegerShortestPaths.graph adjacency) F.base.enumeration L hL
  map (fun out => (out.logged.result.cache.state.data.cut, out.operations + 5))
    (RetainedBinarySampler.run adjacency F (CandidateEnumeration.fin_vertices n) hL T
      (restart n) (fuel n + 1) (fuel n + 1) initial)

def bitTree {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    FiniteDrawTrees.Tree (Flags n × ℕ) :=
  if L ≤ n then
    if 64 * cap n ≤ L ∧ n ≤ L ^ 3 then hard T adjacency L hL
    else .pure (Vector.replicate n true, 2 * n + 5)
  else .pure (Vector.replicate n false, 2 * n + 5)

theorem bitTree_value {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    map Prod.fst (bitTree T adjacency L hL) = EncodedIntegerRounding.bitTree T adjacency L hL := by
  unfold bitTree EncodedIntegerRounding.bitTree EncodedIntegerRounding.tree
  split_ifs
  · let F := CandidateEnumeration.make n L
    let horder := CandidateEnumeration.fin_vertices n
    let G := EncodedIntegerShortestPaths.graph adjacency
    let s := RetainedDemandMask.initial G F.base.enumeration L hL
    let Q := RetainedCandidateSolver.optimizer
      (demands := remainingSet (RetainedDemandMask.compute G F.base.enumeration L))
      adjacency F horder hL
    let C := integerCutOracle (G := G) hL F.base.enumeration
    let charged := RetainedBinarySampler.run adjacency F horder hL T
      (restart n) (fuel n + 1) (fuel n + 1) s
    let plain := RetainedDrawTrees.runTree Q hL C (restart n) (fuel n + 1) (fuel n + 1) s
    have h := RetainedBinarySampler.run_projected adjacency F horder hL T
      (restart n) (fuel n + 1) (fuel n + 1) s
    change Prod.fst <$> ((fun out => (out.logged.result.cache.state.data.cut, out.operations + 5)) <$> charged) =
      lower T ((fun out => out.result.cache.state.data.cut) <$> plain)
    rw [← map_lower, ← show EncodedSampledRounding.ChargedResult.logged <$> charged = lower T plain from h]
    change Prod.fst <$> ((fun out => (out.logged.result.cache.state.data.cut, out.operations + 5)) <$> charged) =
      (fun out => out.result.cache.state.data.cut) <$> ((fun out => out.logged) <$> charged)
    simp only [Functor.map_map]
  · rfl
  · rfl

def budget (n T : ℕ) : ℕ := RetainedBinarySampler.wordBudget n T + 2 * n + 5

theorem bitTree_charge {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L)
    {out : Flags n × ℕ} (ho : out ∈ (ideal (bitTree T adjacency L hL)).support) :
    out.2 ≤ budget n T := by
  unfold bitTree at ho
  split_ifs at ho with hLn hhard
  · unfold hard at ho
    rw [show ideal (map _ _) = (ideal _).map _ from law_map _ _ _] at ho
    obtain ⟨tail, ht, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
    have h := RetainedBinarySampler.initial_wordBudget adjacency (CandidateEnumeration.make n L)
      (CandidateEnumeration.fin_vertices n) hL T hLn tail ht
    dsimp only
    unfold budget
    omega
  · have he : out = (Vector.replicate n true, 2 * n + 5) := by simpa [ideal, law] using ho
    rw [he]
    unfold budget
    omega
  · have he : out = (Vector.replicate n false, 2 * n + 5) := by simpa [ideal, law] using ho
    rw [he]
    unfold budget
    omega

end DirectedFlowCutGap.ChargedIntegerRounding
