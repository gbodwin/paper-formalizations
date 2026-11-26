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

/-- Read both terminal labels and query the stored metric. The returned
counts track the comparison count and the full query work. -/
def forestDistanceQueryWithWordWork {V : Type*} {h : ℕ} (read : V × V → ℕ × ℕ)
    (e : HeightForestVertex V h × HeightForestVertex V h) : ℕ × ℕ × ℕ :=
  let s := forestLabelWithWordWork e.1
  let t := forestLabelWithWordWork e.2
  let known := read (s.1,t.1)
  (known.1,known.2,s.2+t.2+8*known.2+16)

theorem forestDistanceQueryWithWordWork_spec {V : Type*} {h : ℕ} (read : V × V → ℕ × ℕ)
    (B : ℕ) (budget : ∀ d, (read d).2 ≤ B) (e : HeightForestVertex V h × HeightForestVertex V h) :
    let out := forestDistanceQueryWithWordWork read e
    let old := read (heightForestLabel e.1,heightForestLabel e.2)
    (out.1,out.2.1) = old ∧ out.2.2 ≤ 10*h+8*B+34 := by
  let a := forestLabelWithWordWork e.1
  let b := forestLabelWithWordWork e.2
  obtain ⟨left,costL⟩ := forestLabelWithWordWork_spec e.1
  obtain ⟨right,costR⟩ := forestLabelWithWordWork_spec e.2
  have query := budget (a.1,b.1)
  change a.1 = _ at left
  change b.1 = _ at right
  change a.2 ≤ _ at costL
  change b.2 ≤ _ at costR
  change ((read (a.1,b.1)).1,(read (a.1,b.1)).2) = _ ∧ a.2+b.2+8*(read (a.1,b.1)).2+16 ≤ _
  exact ⟨by rw [left,right],by omega⟩

/-- Return the same metric value with the work of both label reads and
the stored-metric query in one count. -/
def forestDistanceWeightWithWordWork {V : Type*} {h : ℕ} (read : V × V → ℕ × ℕ)
    (e : HeightForestVertex V h × HeightForestVertex V h) : ℕ × ℕ :=
  let out := forestDistanceQueryWithWordWork read e
  (out.1,out.2.2+5)

theorem forestDistanceWeightWithWordWork_spec {V : Type*} {h : ℕ} (read : V × V → ℕ × ℕ)
    (B : ℕ) (budget : ∀ d, (read d).2 ≤ B) (e : HeightForestVertex V h × HeightForestVertex V h) :
    let out := forestDistanceWeightWithWordWork read e
    out.1 = (read (heightForestLabel e.1,heightForestLabel e.2)).1 ∧ out.2 ≤ 10*h+8*B+39 := by
  obtain ⟨value,work⟩ := forestDistanceQueryWithWordWork_spec read B budget e
  have sameValue : (forestDistanceQueryWithWordWork read e).1 =
      (read (heightForestLabel e.1,heightForestLabel e.2)).1 := congrArg Prod.fst value
  exact ⟨sameValue,Nat.add_le_add_right work 5⟩

end OnlineReachabilityPreservers
