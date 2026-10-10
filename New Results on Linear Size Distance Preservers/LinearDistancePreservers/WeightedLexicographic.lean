import LinearDistancePreservers.WeightedProjection

namespace LinearDistancePreservers.ObstacleProduct
open SimpleGraph
open scoped NNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {A B C U J : Type*} {k : ℕ} (D : Data A B C U J k)
open WeightedNativeForcing

def outerThrough (b : B) (j₁ j₂ : J) :
    (outerGraph D).Walk (.inl (D.left b j₁)) (.inr (.inr (D.right b j₂))) :=
  .cons ⟨.inl (b,j₁),Or.inl rfl⟩ (.cons ⟨.inr (b,j₂),Or.inl rfl⟩ .nil)

def realSecondary (wi : U → U → ℝ≥0) : Vertex A B C U → Vertex A B C U → ℝ≥0
  | .inr (.inl (_,u)), .inr (.inl (_,v)) => wi u v
  | _, _ => 0

@[simp] theorem realCost_nil {V : Type*} {G : SimpleGraph V} (w : V → V → ℝ≥0) (u : V) :
    realCost w (.nil : G.Walk u u) = 0 := rfl

@[simp] theorem realCost_cons {V : Type*} {G : SimpleGraph V} (w : V → V → ℝ≥0)
    {s u t : V} (h : G.Adj s u) (p : G.Walk u t) :
    realCost w (.cons h p) = (w s u : ℝ) + realCost w p := rfl

theorem realCost_concat {V : Type*} {G : SimpleGraph V} (w : V → V → ℝ≥0)
    {s u t : V} (p : G.Walk s u) (h : G.Adj u t) :
    realCost w (p.concat h) = realCost w p + w u t := by
  simp [realCost,Walk.darts_concat,List.concat_eq_append]

theorem realPrimary_map (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0) (b : B)
    {u v : U} (w : (innerGraph D).Walk u v) :
    realCost (realPrimary wl wr) (w.map (embed D b)) = 0 := by
  induction w with
  | nil => rfl
  | cons h w ih => simpa [Walk.map_cons,embed,realPrimary,outerWeight,projectVertex] using ih

theorem realSecondary_map (wi : U → U → ℝ≥0) (b : B)
    {u v : U} (w : (innerGraph D).Walk u v) :
    realCost (realSecondary wi) (w.map (embed D b)) = realCost wi w := by
  induction w with
  | nil => rfl
  | cons h w ih => simpa [Walk.map_cons,embed,realSecondary] using ih

theorem realPrimary_through (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0) (b : B) (j₁ j₂ : J)
    (w : (innerGraph D).Walk (D.inner j₁ 0) (D.inner j₂ (Fin.last k))) :
    realCost (realPrimary wl wr) (through D b j₁ j₂ w) =
      wl (D.left b j₁) b + (wr b (D.right b j₂) : ℝ) := by
  rw [through,realCost_cons,realCost_concat,realPrimary_map]
  simp [realPrimary,outerWeight,projectVertex,embed]

theorem realSecondary_through (wi : U → U → ℝ≥0) (b : B) (j₁ j₂ : J)
    (w : (innerGraph D).Walk (D.inner j₁ 0) (D.inner j₂ (Fin.last k))) :
    realCost (realSecondary wi) (through D b j₁ j₂ w) = realCost wi w := by
  rw [through,realCost_cons,realCost_concat,realSecondary_map]
  simp [realSecondary,embed]

@[simp] theorem outerThrough_cost (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0)
    (b : B) (j₁ j₂ : J) :
    realCost (outerWeight wl wr) (outerThrough D b j₁ j₂) =
      wl (D.left b j₁) b + (wr b (D.right b j₂) : ℝ) := by
  simp [outerThrough,outerWeight]

def RealOuterOptimal (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0) : Prop :=
  ∀ b j (q : (outerGraph D).Walk (.inl (D.left b j)) (.inr (.inr (D.right b j)))),
    realCost (outerWeight wl wr) (outerThrough D b j j) ≤ realCost (outerWeight wl wr) q ∧
    (realCost (outerWeight wl wr) q = realCost (outerWeight wl wr) (outerThrough D b j j) →
      q = outerThrough D b j j)

def RealInnerOptimal (wi : U → U → ℝ≥0) : Prop :=
  ∀ j (w : (innerGraph D).Walk (D.inner j 0) (D.inner j (Fin.last k))),
    realCost wi (innerRoute D j) ≤ realCost wi w ∧
    (realCost wi w = realCost wi (innerRoute D j) → w = innerRoute D j)

theorem real_outer_labels (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0)
    (hout : RealOuterOptimal D wl wr) (b : B) (j : J) (b' : B) (j₁ j₂ : J)
    (hl : D.left b' j₁ = D.left b j) (hr : D.right b' j₂ = D.right b j)
    (he : wl (D.left b' j₁) b' + (wr b' (D.right b' j₂) : ℝ) =
      wl (D.left b j) b + (wr b (D.right b j) : ℝ)) :
    b' = b ∧ j₁ = j ∧ j₂ = j := by
  let q := (outerThrough D b' j₁ j₂).copy (congrArg Sum.inl hl)
    (congrArg (fun c => Sum.inr (Sum.inr c)) hr)
  have hq := (hout b j q).2 (by dsimp only [q]; rw [realCost_copy,outerThrough_cost,outerThrough_cost]; exact he)
  have hsup := congrArg Walk.support hq
  have hb : b' = b := by
    simp only [q,Walk.support_copy,outerThrough,Walk.support_cons,Walk.support_nil] at hsup
    have hmid := (List.cons.inj ((List.cons.inj hsup).2)).1
    exact Sum.inl.inj (Sum.inr.inj hmid)
  subst b'
  exact ⟨rfl,D.left_injective b hl,D.right_injective b hr⟩

/-- All actual competing native walks are compared lexicographically by
projecting to the supplied outer graph, then using the supplied inner graph. -/
theorem real_lexicographic (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0) (wi : U → U → ℝ≥0)
    (hout : RealOuterOptimal D wl wr) (hin : RealInnerOptimal D wi)
    (b : B) (j : J)
    (q : (graph D).Walk (.inl (D.left b j)) (.inr (.inr (D.right b j))))
    (hne : q ≠ fullWalk D b j) :
    realCost (realPrimary wl wr) (fullWalk D b j) < realCost (realPrimary wl wr) q ∨
    (realCost (realPrimary wl wr) (fullWalk D b j) = realCost (realPrimary wl wr) q ∧
      realCost (realSecondary wi) (fullWalk D b j) < realCost (realSecondary wi) q) := by
  have hp : realCost (realPrimary wl wr) (fullWalk D b j) =
      realCost (outerWeight wl wr) (outerThrough D b j j) := by
    rw [← through_innerRoute,realPrimary_through,outerThrough_cost]
  have hs : realCost (realSecondary wi) (fullWalk D b j) = realCost wi (innerRoute D j) := by
    rw [← through_innerRoute,realSecondary_through]
  obtain ⟨hmin,huni⟩ := hout b j (projectWalk D q)
  have hmin' := hp.trans_le (hmin.trans_eq (projectWalk_cost D wl wr q))
  rcases lt_or_eq_of_le hmin' with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq,?_⟩
    have hproj : projectWalk D q = outerThrough D b j j := by
      exact huni ((projectWalk_cost D wl wr q).trans (heq.symm.trans hp))
    have hcnt : connectorCount D q ≤ 2 := by
      have hh := congrArg Walk.length hproj
      rw [projectWalk_length] at hh
      change connectorCount D q = 2 at hh
      exact hh.le
    obtain ⟨b',j₁,j₂,hle,hrg,w,hw⟩ := factor_left_right D q hcnt
    have hqt : q = (through D b' j₁ j₂ w).copy
        (congrArg Sum.inl hle) (congrArg (fun c => Sum.inr (Sum.inr c)) hrg) := by
      apply Walk.ext_support
      rw [Walk.support_copy,through_support,hw,hle,hrg]
    have he : wl (D.left b' j₁) b' + (wr b' (D.right b' j₂) : ℝ) =
        wl (D.left b j) b + (wr b (D.right b j) : ℝ) := by
      have h := heq.symm
      rw [hqt,realCost_copy,realPrimary_through,hp,outerThrough_cost] at h
      exact h
    obtain ⟨hb,hj₁,hj₂⟩ := real_outer_labels D wl wr hout b j b' j₁ j₂ hle hrg he
    subst b' j₁ j₂
    have hqthrough : q = through D b j j w := by simpa using hqt
    rw [hs,hqthrough,realSecondary_through]
    obtain ⟨himin,hiunique⟩ := hin j w
    apply lt_of_le_of_ne himin
    intro he
    have hwinner := hiunique he.symm
    apply hne
    rw [hqthrough,hwinner,through_innerRoute]

end LinearDistancePreservers.ObstacleProduct

namespace LinearDistancePreservers.ObstacleProduct
open SimpleGraph WeightedNativeForcing
open scoped NNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {A B C U J : Type*} {k : ℕ} (D : Data A B C U J k)

theorem real_outer_positive (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0)
    (hl : ∀ b j, 0 < wl (D.left b j) b)
    (hr : ∀ b j, 0 < wr b (D.right b j))
    (s t : OuterVertex A B C) (h : (outerGraph D).Adj s t) :
    0 < outerWeight wl wr s t := by
  rcases h with ⟨e,h | h⟩ <;>
    have hs := congrArg Prod.fst h <;> have ht := congrArg Prod.snd h <;>
    dsimp at hs ht
  · rw [← hs,← ht]
    rcases e with ⟨b,j⟩ | ⟨b,j⟩
    · exact hl b j
    · exact hr b j
  · rw [← ht,← hs]
    rcases e with ⟨b,j⟩ | ⟨b,j⟩
    · exact hl b j
    · exact hr b j

/-- The outer premise can be supplied in the ordinary simple-path formulation
of a positive-weight perfect path system. -/
theorem real_outer_optimal_of_paths (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0)
    (hl : ∀ b j, 0 < wl (D.left b j) b)
    (hr : ∀ b j, 0 < wr b (D.right b j))
    (hp : ∀ b j (q : (outerGraph D).Path (.inl (D.left b j)) (.inr (.inr (D.right b j)))),
      realCost (outerWeight wl wr) (outerThrough D b j j) ≤ realCost (outerWeight wl wr) q.val ∧
      (realCost (outerWeight wl wr) q.val = realCost (outerWeight wl wr) (outerThrough D b j j) →
        q.val = outerThrough D b j j)) : RealOuterOptimal D wl wr := by
  classical
  intro b j q
  exact path_optimal_to_walk (outerWeight wl wr) (real_outer_positive D wl wr hl hr)
    (outerThrough D b j j) (fun p => (hp b j p).1) (fun p => (hp b j p).2) q

/-- Likewise, the inner premise requires only unique shortest simple paths;
positive edge costs eliminate all cyclic competitors internally. -/
theorem real_inner_optimal_of_paths (wi : U → U → ℝ≥0)
    (hi : ∀ u v, (innerGraph D).Adj u v → 0 < wi u v)
    (hp : ∀ j (q : (innerGraph D).Path (D.inner j 0) (D.inner j (Fin.last k))),
      realCost wi (innerRoute D j) ≤ realCost wi q.val ∧
      (realCost wi q.val = realCost wi (innerRoute D j) → q.val = innerRoute D j)) :
    RealInnerOptimal D wi := by
  classical
  intro j q
  exact path_optimal_to_walk wi hi (innerRoute D j) (fun p => (hp j p).1) (fun p => (hp j p).2) q

end LinearDistancePreservers.ObstacleProduct
