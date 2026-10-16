import LightEFTSpanners.StoredVoteMachine

namespace LightEFTSpanners.StoredVote
open Controller

def buildSteps (Q E T : List StoredEdges.Edge) (W : StoredRecords.Weights) (ss : Draws) : ℕ :=
  (ss.map fun S => StoredRecords.matrixSteps (lists Q E T S) W+2).sum

theorem builds_trace (Q E T : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v : ℕ) (budget : ℚ) (ss : Draws) (acc : List SampleRecords.Records) :
    Trace (transition Q E T W n u v budget) (buildSteps Q E T W ss)
      (.draws ss acc) (.draws [] ((records Q E T W ss).reverse++acc)) := by
  induction ss generalizing acc with
  | nil => simpa [buildSteps,records] using Trace.refl (step:=transition Q E T W n u v budget) (.draws [] acc)
  | cons S ss ih =>
    have h0 := Trace.one (show transition Q E T W n u v budget (.draws (S::ss) acc)=
      some (.build S ss acc (.row 0 W [])) from rfl)
    have h1 := build_lift Q E T S W n u v budget ss acc (StoredRecords.materialize_trace (lists Q E T S) W)
    have h2 := Trace.one (show transition Q E T W n u v budget
      (.build S ss acc (.halt (StoredRecords.values (lists Q E T S) 0 W)))=
      some (.draws ss (StoredRecords.values (lists Q E T S) 0 W::acc)) from rfl)
    have h3 := ih (StoredRecords.values (lists Q E T S) 0 W::acc)
    convert h0.trans (h1.trans (h2.trans h3)) using 1 <;>
      simp [buildSteps,records,List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    all_goals omega

theorem reverse_trace (Q E T : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v : ℕ) (budget : ℚ) (rs acc : List SampleRecords.Records) :
    Trace (transition Q E T W n u v budget) (rs.length+1)
      (.reverse rs acc) (.vote (.samples (rs.reverse++acc) 0 0)) := by
  induction rs generalizing acc with
  | nil => exact Trace.one rfl
  | cons R rs ih =>
    simpa [List.reverse_cons,List.append_assoc] using Trace.cons
      (show transition Q E T W n u v budget (.reverse (R::rs) acc)=some (.reverse rs (R::acc)) from rfl) (ih (R::acc))

theorem construct_trace (Q E T : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v : ℕ) (budget : ℚ) (ss : Draws) :
    Trace (transition Q E T W n u v budget) (buildSteps Q E T W ss+ss.length+2)
      (.draws ss []) (.vote (.samples (records Q E T W ss) 0 0)) := by
  have h1 := builds_trace Q E T W n u v budget ss []
  simp only [List.append_nil] at h1
  have h2 := Trace.one (show transition Q E T W n u v budget
    (.draws [] (records Q E T W ss).reverse)=some (.reverse (records Q E T W ss).reverse []) from rfl)
  have h3 := reverse_trace Q E T W n u v budget (records Q E T W ss).reverse []
  simp only [List.length_reverse,records,List.length_map,List.reverse_reverse,List.append_nil] at h3
  convert h1.trans (h2.trans h3) using 1
  all_goals first | rfl | omega
end LightEFTSpanners.StoredVote
