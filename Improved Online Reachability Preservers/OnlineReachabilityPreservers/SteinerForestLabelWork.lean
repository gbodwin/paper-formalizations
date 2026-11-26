import OnlineReachabilityPreservers.SteinerHeightForest

namespace OnlineReachabilityPreservers

private def lastLabelWithWordWork {V : Type*} (root : V) : List V → V × ℕ
  | [] => (root,3)
  | v :: rest =>
    let found := lastLabelWithWordWork v rest
    (found.1,found.2+5)

private theorem lastLabelWithWordWork_spec {V : Type*} (root : V) (history : List V) :
    let out := lastLabelWithWordWork root history
    out.1 = (root :: history).getLast (List.cons_ne_nil _ _) ∧ out.2 = 5*history.length+3 := by
  induction history generalizing root with
  | nil => simp [lastLabelWithWordWork]
  | cons v rest ih =>
    obtain ⟨label,work⟩ := ih v
    constructor
    · change (lastLabelWithWordWork v rest).1 = _
      rw [List.getLast_cons_cons]
      exact label
    · change (lastLabelWithWordWork v rest).2+5 = _
      rw [work,List.length_cons,Nat.mul_succ]

/-- Read the label of a forest vertex in one traversal of its history. -/
def forestLabelWithWordWork {V : Type*} {h : ℕ} (v : HeightForestVertex V h) : V × ℕ :=
  let found := lastLabelWithWordWork (heightForestRoot v) (heightForestHistory v).val
  (found.1,found.2+6)

theorem forestLabelWithWordWork_spec {V : Type*} {h : ℕ} (v : HeightForestVertex V h) :
    let out := forestLabelWithWordWork v
    out.1 = heightForestLabel v ∧ out.2 ≤ 5*h+9 := by
  obtain ⟨label,work⟩ := lastLabelWithWordWork_spec (heightForestRoot v) (heightForestHistory v).val
  have fit := (heightForestHistory v).property
  refine ⟨label,?_⟩
  dsimp only [forestLabelWithWordWork]
  rw [work]
  omega

end OnlineReachabilityPreservers
