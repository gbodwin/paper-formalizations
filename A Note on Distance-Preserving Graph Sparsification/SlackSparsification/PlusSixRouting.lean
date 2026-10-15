import SlackSparsification.GraphRouting
import SlackSparsification.Attachments
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The cited Theorem 10 is an explicit premise, not an axiom or a certified
result of this library. The same constant C works for every subset of G.
The routing below reuses the existing ordered-attachment calculation. -/
namespace SlackSparsification
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Quantitative interface to the external subset +2-spanner theorem.
Positivity of C is supplied separately at each construction endpoint. -/
def UniformSubsetPlusTwo (G : SimpleGraph V) (C : ℝ) : Prop :=
  ∀ S : Finset V, ∃ K : SimpleGraph V, K ≤ G ∧
    (K.edgeFinset.card : ℝ) ≤ C * Fintype.card V * Real.sqrt (S.card : ℝ) ∧
    ∀ r ∈ S, ∀ q ∈ S, K.edist r q ≤ G.edist r q + 2

omit [Fintype V] [DecidableEq V] in
/-- A subset connector inside the assembled graph routes ordered attachments.
No distinctness of roots or positivity of the purchased length is required. -/
theorem plus_six_from_subset_connector (G H K : SimpleGraph V)
    (hHG : H ≤ G) (hKH : K ≤ H) (s x y t r q : V)
    (hrx : H.Adj r x) (hyq : H.Adj y q)
    (hconnector : K.edist r q ≤ G.edist r q + 2)
    (hpre : H.edist s x = G.edist s x)
    (hsuf : H.edist y t = G.edist y t)
    (hsplit : G.edist s x + G.edist x y + G.edist y t = G.edist s t) :
    H.edist s t ≤ G.edist s t + 6 := by
  exact route_three_segments G H s x y t 6 hpre hsuf
    (plus_six_between_attachments G H hHG x y r q hrx.symm hyq.symm
      ((edist_anti hKH).trans hconnector)) hsplit

end SlackSparsification
