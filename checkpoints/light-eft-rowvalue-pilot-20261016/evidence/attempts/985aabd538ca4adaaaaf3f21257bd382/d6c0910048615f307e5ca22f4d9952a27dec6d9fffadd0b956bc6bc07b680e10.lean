import LightEFTSpanners.StoredCandidateExecutable

namespace LightEFTSpanners.StoredCandidates
variable {n : ℕ} {J : Type*} [DecidableEq J]

def HostRepresentation (E : List (Fin n × Fin n))
    (eligible : Sym2 (Fin n) → Finset J) (host : J → Finset (Sym2 (Fin n)))
    (tape : SampledGreedy.Tape (Fin n) J) (R : TypedInput n) : Prop :=
  ∃ (js : List J) (input : J → StoredHosts.TypedInput n),
    js.Nodup ∧ js.toFinset=eligible s(R.edge.1,R.edge.2) ∧ R.hosts=js.map input ∧
    (∀ j∈js,host j=StoredSample.edgeSet (input j).edges) ∧
    (∀ j∈js,tape (StoredSample.edgeSet E) s(R.edge.1,R.edge.2) j=
      ((input j).draws.map StoredSample.edgeSet))

def ValidSchedule (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (eligible : Sym2 (Fin n) → Finset J) (host : J → Finset (Sym2 (Fin n)))
    (tape : SampledGreedy.Tape (Fin n) J) (h : ℕ) :
    List (TypedInput n) → List (Fin n × Fin n) → Prop
  | [],_ => True
  | R::rs,E => R.budget=t*w s(R.edge.1,R.edge.2) ∧
      HostRepresentation E eligible host tape R ∧
      ValidSchedule Q w t eligible host tape h rs (updated Q E w h R)

def originalStep (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : Finset (Sym2 (Fin n)) :=
  if h≤(ExecutableVoting.votes Q w hw t eligible host tape E e).card then insert e E else E

theorem updated_eq_original (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) (R : TypedInput n) (hb : R.budget=t*w s(R.edge.1,R.edge.2))
    (hr : HostRepresentation E eligible host tape R) :
    StoredSample.edgeSet (updated Q E w h R)=
      originalStep (StoredSample.edgeSet Q) w hw t eligible host tape h
        (StoredSample.edgeSet E) s(R.edge.1,R.edge.2) := by
  obtain ⟨js,input,hj,he,hh,ht,hd⟩ := hr
  have hv := StoredHosts.votes_eq_original Q E w hw t R.edge.1 R.edge.2
    eligible host tape js input hj he ht hd
  simp only [updated,accept,hb,hh,hv,decide_eq_true_eq,originalStep]
  split <;> simp [StoredSample.edgeSet]

theorem selected_eq_fold (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) (rs : List (TypedInput n))
    (hr : ValidSchedule Q w t eligible host tape h rs E) :
    StoredSample.edgeSet (selected Q w h rs E)=
      (rs.map fun R => s(R.edge.1,R.edge.2)).foldl
        (originalStep (StoredSample.edgeSet Q) w hw t eligible host tape h)
        (StoredSample.edgeSet E) := by
  induction rs generalizing E with
  | nil => rfl
  | cons R rs ih =>
    obtain ⟨hb,hh,ht⟩ := hr
    simp only [selected,List.map_cons,List.foldl_cons]
    rw [ih (updated Q E w h R) ht,updated_eq_original Q E w hw t eligible host tape h R hb hh]

omit [DecidableEq J] in
theorem original_edges_eq_fold (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) (es : List (Sym2 (Fin n))) :
    ExecutableVoting.edges Q w hw t eligible host tape h es=
      es.reverse.foldl (originalStep Q w hw t eligible host tape h) Q := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [ExecutableVoting.edges_cons,ih,List.reverse_cons,List.foldl_append,
      List.foldl_cons,List.foldl_nil,originalStep]
end LightEFTSpanners.StoredCandidates
