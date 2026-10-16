import LightEFTSpanners.StoredPreparedHostExecutable

namespace LightEFTSpanners.StoredPreparedHostVote
open StoredHostPreparation (TypedRecord)

def catalogue {n : ℕ} {J : Type*} (id : J → ℕ)
    (incidence : J → List (Fin n × Fin n)) (input : J → StoredHosts.TypedInput n)
    (js : List J) : List (TypedRecord n) :=
  js.map fun j => ⟨id j,incidence j,input j⟩

def eligibleIndex {n : ℕ} {J : Type*} (u v : Fin n)
    (incidence : J → List (Fin n × Fin n)) (j : J) : Bool :=
  decide (s(u,v)∈StoredSample.edgeSet (incidence j))

theorem chosen_catalogue {n : ℕ} {J : Type*} (u v : Fin n) (id : J → ℕ)
    (incidence : J → List (Fin n × Fin n)) (input : J → StoredHosts.TypedInput n) (js : List J) :
    ((catalogue id incidence input js).filter (StoredHostPreparation.eligible u v)).map TypedRecord.host=
      (js.filter (eligibleIndex u v incidence)).map input := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [catalogue,List.map_cons,List.filter_cons,StoredHostPreparation.eligible,
      eligibleIndex] at *
    by_cases hm : s(u,v)∈StoredSample.edgeSet (incidence j) <;> simp_all

/-- The stored incidence lists construct eligibility. Distinct original labels,
incidence completeness and original draw-bank representations are explicit. -/
theorem execute_original_admission {n : ℕ} {J : Type*} [DecidableEq J]
    (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e)
    (t : ℚ) (u v : Fin n) (h : ℕ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (id : J → ℕ) (incidence : J → List (Fin n × Fin n))
    (input : J → StoredHosts.TypedInput n) (js : List J) (hj : js.Nodup)
    (cover : ∀ j∈eligible s(u,v),j∈js)
    (inc : ∀ j∈js,j∈eligible s(u,v) ↔ s(u,v)∈StoredSample.edgeSet (incidence j))
    (hh : ∀ j∈js,host j=StoredSample.edgeSet (input j).edges)
    (hd : ∀ j∈js,tape (StoredSample.edgeSet E) s(u,v) j=(input j).draws.map StoredSample.edgeSet) :
    execute (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
      n u.val v.val h (t*w s(u,v)) ((catalogue id incidence input js).map StoredHostPreparation.encode)=true ↔
      h≤(ExecutableVoting.votes (StoredSample.edgeSet Q) w hw t eligible host tape
        (StoredSample.edgeSet E) s(u,v)).card := by
  rw [execute_encoded,chosen_catalogue,decide_eq_true_eq]
  have he : (js.filter (eligibleIndex u v incidence)).toFinset=eligible s(u,v) := by
    ext j
    simp only [List.mem_toFinset,List.mem_filter,eligibleIndex,decide_eq_true_eq]
    constructor
    · rintro ⟨hm,hi⟩
      exact (inc j hm).mpr hi
    · intro hi
      exact ⟨cover j hi,(inc j (cover j hi)).mp hi⟩
  rw [StoredHosts.votes_eq_original Q E w hw t u v eligible host tape
    (js.filter (eligibleIndex u v incidence)) input (hj.filter _) he
    (fun j hm => hh j (List.mem_of_mem_filter hm))
    (fun j hm => hd j (List.mem_of_mem_filter hm))]
end LightEFTSpanners.StoredPreparedHostVote
