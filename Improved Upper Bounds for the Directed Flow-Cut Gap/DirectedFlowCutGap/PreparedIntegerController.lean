import DirectedFlowCutGap.ChargedRoundingPreparation
import DirectedFlowCutGap.ChargedIntegerRounding

/-!
# Joining prepared data to the retained integer controller

The hard branch uses the computed dictionary, mask, initial mass and
epoch parameters in the existing charged run. The projected literal
bit tree is identical to the ordinary integer dispatcher. The budget
combines setup and controller word charges.
-/

namespace DirectedFlowCutGap.PreparedIntegerController

open FiniteDrawTrees RetainedGridState IntegerEpochParameters
open EncodedIntegerShortestPaths (graph)
open ChargedRoundingPreparation

private def retained {n L : ℕ} (adjacency : PairFlags n) (hL : 0 < L)
    (F : CandidateEnumeration.Factory n L) (hF : F.base.enumeration.vertices = List.finRange n)
    (T R J : ℕ) {mask : PairFlags n} (start : Code (graph adjacency) (remainingSet mask) L) :
    FiniteDrawTrees.Tree (Flags n × ℕ) :=
  map (fun out => (out.logged.result.cache.state.data.cut, out.operations + 5))
    (RetainedBinarySampler.run adjacency F hF hL T R (J + 1) (J + 1) start)

private theorem retained_eq {n L : ℕ} (adjacency : PairFlags n) (hL : 0 < L)
    (F : CandidateEnumeration.Factory n L) (hF : F.base.enumeration.vertices = List.finRange n)
    (T R J : ℕ) {mask : PairFlags n} (start : Code (graph adjacency) (remainingSet mask) L)
    (hm : mask = RetainedDemandMask.compute (graph adjacency) F.base.enumeration L)
    (hs : start.data = (RetainedDemandMask.initial (graph adjacency) F.base.enumeration L hL).data) :
    retained adjacency hL F hF T R J start =
      retained adjacency hL F hF T R J (RetainedDemandMask.initial (graph adjacency) F.base.enumeration L hL) := by
  subst mask
  have he : start = RetainedDemandMask.initial (graph adjacency) F.base.enumeration L hL := by
    generalize heq : RetainedDemandMask.initial (graph adjacency) F.base.enumeration L hL = base at hs ⊢
    cases start with
    | mk input proof =>
      cases base with
      | mk raw checked =>
        dsimp only at hs
        subst raw
        rfl
  rw [he]

private def runPrepared {n L : ℕ} (T : ℕ) (adjacency : PairFlags n) (hL : 0 < L)
    (ready : Prepared adjacency L) (horder : ready.factory.base.enumeration.vertices = List.finRange n) :
    FiniteDrawTrees.Tree (Flags n × ℕ) :=
  retained adjacency hL ready.factory horder
    T ready.parameters.restart ready.parameters.fuel ready.state

def preparedCore {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    FiniteDrawTrees.Tree (Flags n × ℕ) :=
  runPrepared T adjacency hL (prepare adjacency L hL) (CandidateEnumeration.fin_vertices n)

theorem preparedCore_eq {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    let F := CandidateEnumeration.make n L
    preparedCore T adjacency L hL =
      retained adjacency hL F (CandidateEnumeration.fin_vertices n) T (restart n) (fuel n)
        (RetainedDemandMask.initial (graph adjacency) F.base.enumeration L hL) := by
  let p := prepare adjacency L hL
  let F := CandidateEnumeration.make n L
  let start := RetainedDemandMask.initial (graph adjacency) F.base.enumeration L hL
  obtain ⟨hR, hJ, _, _, hm, hs⟩ := prepare_value adjacency L hL
  unfold preparedCore
  change retained adjacency hL F _ T p.parameters.restart p.parameters.fuel p.state =
    retained adjacency hL F _ T (restart n) (fuel n) start
  rw [hR, hJ]
  exact retained_eq adjacency hL F _ T _ _ p.state hm hs

def bitTree {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    FiniteDrawTrees.Tree (Flags n × ℕ) :=
  let params := EncodedEpochParameters.compute n
  if L ≤ n then
    if 64 * params.cap ≤ L ∧ n ≤ L ^ 3 then
      let prep := prepare adjacency L hL
      map (fun a => (a.1, a.2 + prep.charge + params.work + 10))
        (runPrepared T adjacency hL prep (CandidateEnumeration.fin_vertices n))
    else .pure (Vector.replicate n true, 2 * n + params.work + 10)
  else .pure (Vector.replicate n false, 2 * n + params.work + 10)

theorem bitTree_value {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    map Prod.fst (bitTree T adjacency L hL) = EncodedIntegerRounding.bitTree T adjacency L hL := by
  rw [← ChargedIntegerRounding.bitTree_value]
  unfold bitTree ChargedIntegerRounding.bitTree
  simp only [EncodedEpochParameters.compute_cap]
  split_ifs
  · change map Prod.fst (map _ (preparedCore T adjacency L hL)) = _
    rw [preparedCore_eq]
    let F := CandidateEnumeration.make n L
    let t := retained adjacency hL F (CandidateEnumeration.fin_vertices n) T (restart n) (fuel n)
      (RetainedDemandMask.initial (graph adjacency) F.base.enumeration L hL)
    change Prod.fst <$> ((fun a => (a.1, a.2 + (prepare adjacency L hL).charge +
      (EncodedEpochParameters.compute n).work + 10)) <$> t) = Prod.fst <$> t
    simp only [Functor.map_map]
  · rfl
  · rfl

def budget (n T : ℕ) : ℕ :=
  ChargedIntegerRounding.budget n T + ChargedRoundingPreparation.budget n +
    EncodedEpochParameters.operationBound n + 10

theorem bitTree_charge {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L)
    {out : Flags n × ℕ} (ho : out ∈ (ideal (bitTree T adjacency L hL)).support) :
    out.2 ≤ budget n T := by
  have hp := EncodedEpochParameters.compute_bound n
  unfold bitTree at ho
  simp only [EncodedEpochParameters.compute_cap] at ho
  split_ifs at ho with hLn hh
  · let t := preparedCore T adjacency L hL
    let f (a : Flags n × ℕ) := (a.1, a.2 + (prepare adjacency L hL).charge +
      (EncodedEpochParameters.compute n).work + 10)
    change out ∈ (ideal (map f t)).support at ho
    rw [show ideal (map f t) = (ideal t).map f from law_map _ _ _] at ho
    obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
    have he : t = ChargedIntegerRounding.bitTree T adjacency L hL := by
      unfold ChargedIntegerRounding.bitTree
      simp only [ite_eq_left hLn, ite_eq_left hh]
      exact preparedCore_eq T adjacency L hL
    have hc := ChargedIntegerRounding.bitTree_charge T adjacency L hL (he ▸ ha)
    have hs := prepare_charge adjacency L hL hLn
    dsimp only [f]
    unfold budget
    omega
  · have he : out = (Vector.replicate n true, 2 * n + (EncodedEpochParameters.compute n).work + 10) := by
      simpa [ideal, law] using ho
    rw [he]
    dsimp only
    unfold budget ChargedIntegerRounding.budget
    omega
  · have he : out = (Vector.replicate n false, 2 * n + (EncodedEpochParameters.compute n).work + 10) := by
      simpa [ideal, law] using ho
    rw [he]
    dsimp only
    unfold budget ChargedIntegerRounding.budget
    omega

end DirectedFlowCutGap.PreparedIntegerController
