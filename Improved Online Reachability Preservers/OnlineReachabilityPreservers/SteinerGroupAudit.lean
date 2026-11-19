import OnlineReachabilityPreservers.Basic

/-! A counterexample to keeping virtual group terminals in an ordinary
undirected Steiner forest instance. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

abbrev GroupExampleVertex := Fin 10

private def symmetric (G : Arcs GroupExampleVertex) : Arcs GroupExampleVertex :=
  G ∪ G.image Prod.swap

/-- The two original trees are the paths 4–0–1–5 and 2–3. -/
def groupExampleForest : Arcs GroupExampleVertex :=
  symmetric {(4, 0), (0, 1), (1, 5), (2, 3)}

def groupExamplePaid : Arcs GroupExampleVertex :=
  symmetric {(4, 0), (1, 5), (2, 3)}

def groupExampleFirstSources : Finset GroupExampleVertex := {0, 2}
def groupExampleFirstSinks : Finset GroupExampleVertex := {1, 3}

private def firstAttachments : Arcs GroupExampleVertex :=
  symmetric ((groupExampleFirstSources.image fun u => (6, u)) ∪
    (groupExampleFirstSinks.image fun v => (7, v)))

private def secondAttachments : Arcs GroupExampleVertex := symmetric {(8, 4), (9, 5)}

/-- The paid arcs serve the first group request but miss the feasible second
group request from 4 to 5. Keeping the first free attachments lets the
second superterminal pair connect through the other tree. -/
theorem persistentSuperterminals_counterexample :
    groupExamplePaid ⊆ groupExampleForest ∧
    (∃ s ∈ groupExampleFirstSources, ∃ t ∈ groupExampleFirstSinks, Reach groupExamplePaid s t) ∧
    Reach groupExampleForest 4 5 ∧ ¬ Reach groupExamplePaid 4 5 ∧
    Reach (groupExamplePaid ∪ firstAttachments ∪ secondAttachments) 8 9 := by
  refine ⟨by decide, ⟨2, by decide, 3, by decide, ?_⟩, ?_, ?_, ?_⟩
  · exact Relation.ReflTransGen.single (by decide)
  · rw [← mem_reaches]
    decide
  · rw [← mem_reaches]
    decide
  · rw [← mem_reaches]
    decide

end OnlineReachabilityPreservers.SourceAudit
