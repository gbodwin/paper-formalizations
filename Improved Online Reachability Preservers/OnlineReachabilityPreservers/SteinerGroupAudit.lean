import OnlineReachabilityPreservers.Basic

/-! A counterexample to keeping virtual group terminals in an ordinary
undirected Steiner forest instance. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

abbrev GroupExampleVertex := Fin 18

private def symmetric (G : Arcs GroupExampleVertex) : Arcs GroupExampleVertex :=
  G ∪ G.image Prod.swap

/-- Two disjoint trees with roots 12 and 13. Each representative is a leaf. -/
def groupExampleForest : Arcs GroupExampleVertex :=
  symmetric {(0, 14), (4, 14), (14, 10), (10, 12), (12, 11), (11, 15), (15, 1), (15, 5),
    (2, 16), (16, 13), (13, 17), (17, 3)}

def groupExamplePaid : Arcs GroupExampleVertex :=
  symmetric {(0, 14), (4, 14), (10, 12), (12, 11), (11, 15), (15, 1), (15, 5),
    (2, 16), (16, 13), (13, 17), (17, 3)}

def groupExampleFirstSources : Finset GroupExampleVertex := {0, 2}
def groupExampleFirstSinks : Finset GroupExampleVertex := {1, 3}

private def firstAttachments : Arcs GroupExampleVertex :=
  symmetric ((groupExampleFirstSources.image fun u => (6, u)) ∪
    (groupExampleFirstSinks.image fun v => (7, v)))

private def secondAttachments : Arcs GroupExampleVertex := symmetric {(8, 4), (9, 5)}

theorem groupExample_representatives_are_leaves (v : GroupExampleVertex)
    (member : v ∈ ({0, 1, 2, 3, 4, 5} : Finset GroupExampleVertex)) :
    (groupExampleForest.filter fun e => e.1 = v).card = 1 := by
  have finite : ∀ v : GroupExampleVertex, v ∈ ({0, 1, 2, 3, 4, 5} : Finset GroupExampleVertex) →
      (groupExampleForest.filter fun e => e.1 = v).card = 1 := by decide
  exact finite v member

/-- The paid arcs serve the first group request but miss the feasible second
group request from 4 to 5. Keeping the first free attachments lets the
second superterminal pair connect through the other tree. -/
theorem persistentSuperterminals_counterexample :
    groupExamplePaid ⊆ groupExampleForest ∧
    (∃ s ∈ groupExampleFirstSources, ∃ t ∈ groupExampleFirstSinks, Reach groupExamplePaid s t) ∧
    Reach groupExampleForest 4 5 ∧ ¬ Reach groupExamplePaid 4 5 ∧
    Reach (groupExamplePaid ∪ firstAttachments ∪ secondAttachments) 8 9 := by
  refine ⟨by decide, ⟨2, by decide, 3, by decide, ?_⟩, ?_, ?_, ?_⟩
  · rw [← mem_reaches]
    decide
  · rw [← mem_reaches]
    decide
  · rw [← mem_reaches]
    decide
  · rw [← mem_reaches]
    decide

theorem groupExample_requires_unpaid_arc {P : Arcs GroupExampleVertex}
    (sub : P ⊆ groupExampleForest) (served : Reach P 4 5) :
    ((14, 10) : GroupExampleVertex × GroupExampleVertex) ∈ P := by
  by_contra missing
  have incomplete : P ⊆ groupExampleForest.erase (14, 10) :=
    fun e he => mem_erase.mpr ⟨fun eq => missing (eq ▸ he), sub he⟩
  have none : ¬ Reach (groupExampleForest.erase (14, 10)) 4 5 := by
    rw [← mem_reaches]
    decide
  exact none (reach_mono incomplete served)

end OnlineReachabilityPreservers.SourceAudit
