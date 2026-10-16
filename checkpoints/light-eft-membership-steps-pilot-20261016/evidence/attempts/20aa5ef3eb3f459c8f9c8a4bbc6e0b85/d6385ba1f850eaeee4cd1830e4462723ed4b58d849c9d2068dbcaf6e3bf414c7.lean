import LightEFTSpanners.RationalDistanceTest
import LightEFTSpanners.EmpiricalVotingGreedy

/-! A computable rational implementation of the literal empirical-voting
recursion, with exact equality to the proved real-weight semantics. Seed,
hosts, eligible host lists, edge order and finite sample tapes are inputs;
this does not claim to compute a minimum seed or a packing in polynomial time. -/
namespace LightEFTSpanners.ExecutableVoting
open SimpleGraph LightSpanners RationalDistance
variable {n : ℕ} {J : Type*} [DecidableEq J]

 def graph (E : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) := edgeGraph E

 instance (E : Finset (Sym2 (Fin n))) : DecidableRel (graph E).Adj :=
  fun u v => inferInstanceAs (Decidable (s(u,v)∈E ∧ u≠v))

 def sampled (Q E T S : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  graph (T∪(S∩(E\Q)))

 instance (Q E T S : Finset (Sym2 (Fin n))) : DecidableRel (sampled Q E T S).Adj :=
  inferInstanceAs (DecidableRel (graph (T∪(S∩(E\Q)))).Adj)

 def estimate (Q E T : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (e : Sym2 (Fin n)) (draws : List (Finset (Sym2 (Fin n)))) : ℚ :=
  ((draws.filter fun S => !(coveredTest (sampled Q E T S) w hw t e)).length:ℚ)/draws.length

 theorem estimate_cast (Q E T : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (e : Sym2 (Fin n)) (draws : List (Finset (Sym2 (Fin n)))) :
    (estimate Q E T w hw t e draws:ℝ)=
      SampledGreedy.estimate Q E T (fun d => (w d:ℝ)) (t:ℝ) e draws := by
  classical
  have heq : (fun S => !(coveredTest (sampled Q E T S) w hw t e))=
      (fun S => decide (¬Covered (testSample Q E T S) (fun d => (w d:ℝ)) (t:ℝ) e)) := by
    funext S
    have hc := @coveredTest_iff n (sampled Q E T S)
      (instDecidableRelFinAdjSampled Q E T S) w hw t e
    by_cases hp : Covered (testSample Q E T S) (fun d => (w d:ℝ)) (t:ℝ) e
    · have hb : coveredTest (sampled Q E T S) w hw t e=true :=
        hc.mpr hp
      simp [hb,hp]
    · have hb : coveredTest (sampled Q E T S) w hw t e=false :=
        Bool.eq_false_iff.mpr (fun h => hp (hc.mp h))
      simp [hb,hp]
  simp only [estimate,SampledGreedy.estimate,heq,Rat.cast_div,Rat.cast_natCast]

 def votes (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : Finset J :=
  (eligible e).filter fun j => (3:ℚ)/8≤estimate Q E (host j) w hw t e (tape E e j)

 omit [DecidableEq J] in
 theorem votes_eq (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    votes Q w hw t eligible host tape E e=
      SampledGreedy.votes Q (fun d => (w d:ℝ)) (t:ℝ) eligible host tape E e := by
  classical
  ext j
  simp only [votes,SampledGreedy.votes,Finset.mem_filter]
  rw [←estimate_cast Q E (host j) w hw t e (tape E e j)]
  have hcast : (((3:ℚ)/8:ℚ):ℝ)=(3:ℝ)/8 := by norm_num
  rw [←hcast,Rat.cast_le]

 def edges (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) : List (Sym2 (Fin n)) → Finset (Sym2 (Fin n)) :=
  List.rec Q (fun e _ E =>
    if h≤(votes Q w hw t eligible host tape E e).card then insert e E else E)

 omit [DecidableEq J] in
 theorem edges_nil (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) :
    edges Q w hw t eligible host tape h [] = Q := rfl

 omit [DecidableEq J] in
 theorem edges_cons (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) (e : Sym2 (Fin n)) (es : List (Sym2 (Fin n))) :
    edges Q w hw t eligible host tape h (e :: es) =
      let E := edges Q w hw t eligible host tape h es
      if h ≤ (votes Q w hw t eligible host tape E e).card then insert e E else E := rfl


 omit [DecidableEq J] in
 theorem edges_eq (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) (l : List (Sym2 (Fin n))) :
    edges Q w hw t eligible host tape h l=
      SampledGreedy.edges Q (fun d => (w d:ℝ)) (t:ℝ) eligible host tape h l := by
  induction l with
  | nil => rfl
  | cons e es ih => simp only [edges_cons,SampledGreedy.edges,ih,votes_eq]
end LightEFTSpanners.ExecutableVoting
