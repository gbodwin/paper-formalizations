import LightEFTSpanners.StoredVoteEncoding

namespace LightEFTSpanners.StoredVote

def drawCells (ss : Draws) : ℕ := (ss.map List.length).sum

theorem buildSteps_le (Q E T : List StoredEdges.Edge) (W : StoredRecords.Weights) (ss : Draws) :
    buildSteps Q E T W ss ≤
      ss.length*(StoredRecords.cellCount W*(Q.length+E.length+T.length+11)+4*W.length+4)+
      StoredRecords.cellCount W*drawCells ss := by
  induction ss with
  | nil => simp [buildSteps,drawCells]
  | cons S ss ih =>
    have h := StoredRecords.matrixSteps_le (lists Q E T S) W
    change StoredRecords.matrixSteps (lists Q E T S) W ≤
      StoredRecords.cellCount W*(Q.length+E.length+T.length+S.length+11)+4*W.length+2 at h
    simp only [buildSteps,List.map_cons,List.sum_cons,List.length_cons,drawCells] at *
    nlinarith

def bound (n : ℕ) (Q E T : List StoredEdges.Edge) (ss : Draws) : ℕ :=
  ss.length*(n*n*(Q.length+E.length+T.length+11)+4*n+SampleVote.perSample n+5)+n*n*drawCells ss+4

theorem encoded_bound {n : ℕ} (Q E T : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (ss : List (List (Fin n × Fin n))) :
    buildSteps (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T)
      (StoredRecords.encodeWeights w) (encodeDraws ss)+ss.length*(SampleVote.perSample n+1)+4 ≤
      bound n (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T) (encodeDraws ss) := by
  have h := buildSteps_le (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T)
    (StoredRecords.encodeWeights w) (encodeDraws ss)
  have hc : StoredRecords.cellCount (StoredRecords.encodeWeights w)=n*n := by
    simp [StoredRecords.cellCount,StoredRecords.encodeWeights,List.map_ofFn,Function.comp_def]
  have hr : (StoredRecords.encodeWeights w).length=n := by simp [StoredRecords.encodeWeights]
  rw [hc,hr] at h
  simp only [bound,encodeDraws,List.length_map] at *
  nlinarith
end LightEFTSpanners.StoredVote
