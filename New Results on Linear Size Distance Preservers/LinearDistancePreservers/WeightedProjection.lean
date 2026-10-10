import LinearDistancePreservers.ObstacleWeights
import LinearDistancePreservers.PathPerturbation

namespace LinearDistancePreservers.ObstacleProduct
open SimpleGraph
open scoped NNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

variable {A B C U J : Type*} {k : ℕ} (D : Data A B C U J k)

abbrev OuterVertex (A B C : Type*) := A ⊕ (B ⊕ C)

def projectVertex : Vertex A B C U → OuterVertex A B C
  | .inl a => .inl a
  | .inr (.inl (b,_)) => .inr (.inl b)
  | .inr (.inr c) => .inr (.inr c)

def outerArc : (B × J) ⊕ (B × J) → OuterVertex A B C × OuterVertex A B C
  | .inl (b,j) => (.inl (D.left b j), .inr (.inl b))
  | .inr (b,j) => (.inr (.inl b), .inr (.inr (D.right b j)))

def outerGraph : SimpleGraph (OuterVertex A B C) where
  Adj u v := ∃ e, outerArc D e = (u,v) ∨ outerArc D e = (v,u)
  symm := ⟨by rintro u v ⟨e,h⟩; exact ⟨e,h.symm⟩⟩
  loopless := ⟨by rintro v ⟨⟨b,j⟩ | ⟨b,j⟩, h | h⟩ <;> simp only [outerArc,Prod.mk.injEq] at h <;>
    have hh := h.1.trans h.2.symm <;> simp at hh⟩

theorem project_adj {s t : Vertex A B C U} (h : (graph D).Adj s t) :
    projectVertex s = projectVertex t ∨
      (outerGraph D).Adj (projectVertex s) (projectVertex t) := by
  rcases h with ⟨e,h | h⟩ <;>
    have hs := congrArg Prod.fst h <;> have ht := congrArg Prod.snd h <;>
    dsimp at hs ht
  · rw [← hs,← ht]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩)
    · exact Or.inr ⟨.inl (b,j),Or.inl rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨.inr (b,j),Or.inl rfl⟩
  · rw [← ht,← hs]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩)
    · exact Or.inr ⟨.inl (b,j),Or.inr rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨.inr (b,j),Or.inr rfl⟩

theorem project_eq_iff_connector_zero {s t : Vertex A B C U}
    (h : (graph D).Adj s t) :
    projectVertex s = projectVertex t ↔ connector s t = 0 := by
  rcases h with ⟨e,h | h⟩ <;>
    have hs := congrArg Prod.fst h <;> have ht := congrArg Prod.snd h <;>
    dsimp at hs ht
  · rw [← hs,← ht]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;> simp [arc,projectVertex,connector]
  · rw [← ht,← hs]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;> simp [arc,projectVertex,connector]

noncomputable def projectWalk {s t : Vertex A B C U} :
    (graph D).Walk s t → (outerGraph D).Walk (projectVertex s) (projectVertex t)
  | .nil => .nil
  | .cons h p => if he : projectVertex _ = projectVertex _ then
      (projectWalk p).copy he.symm rfl
    else .cons ((project_adj D h).resolve_left he) (projectWalk p)

theorem projectWalk_length {s t : Vertex A B C U} (p : (graph D).Walk s t) :
    (projectWalk D p).length = connectorCount D p := by
  induction p with
  | nil => rfl
  | @cons s u t h p ih =>
    simp only [projectWalk,connectorCount_cons]
    split_ifs with he
    · rw [Walk.length_copy,ih,(project_eq_iff_connector_zero D h).mp he,zero_add]
    · rw [Walk.length_cons,ih]
      have hc : connector s u = 1 := by
        cases s with
        | inl => rfl
        | inr s => cases s with
          | inr => rfl
          | inl s => cases u with
            | inl => rfl
            | inr u => cases u with
              | inr => rfl
              | inl u => exact False.elim (he ((project_eq_iff_connector_zero D h).mpr rfl))
      omega

def outerWeight (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0) :
    OuterVertex A B C → OuterVertex A B C → ℝ≥0
  | .inl a, .inr (.inl b) => wl a b
  | .inr (.inl b), .inl a => wl a b
  | .inr (.inl b), .inr (.inr c) => wr b c
  | .inr (.inr c), .inr (.inl b) => wr b c
  | _, _ => 0

def realPrimary (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0)
    (s t : Vertex A B C U) : ℝ≥0 := outerWeight wl wr (projectVertex s) (projectVertex t)

@[simp] theorem outerWeight_self (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0)
    (v : OuterVertex A B C) : outerWeight wl wr v v = 0 := by
  rcases v with a | (b | c) <;> rfl

theorem realCost_copy {V : Type*} {G : SimpleGraph V} (w : V → V → ℝ≥0)
    {s t s' t' : V} (p : G.Walk s t) (hs : s = s') (ht : t = t') :
    WeightedNativeForcing.realCost w (p.copy hs ht) = WeightedNativeForcing.realCost w p := by
  simp [WeightedNativeForcing.realCost,Walk.darts_copy]

theorem projectWalk_cost (wl : A → B → ℝ≥0) (wr : B → C → ℝ≥0)
    {s t : Vertex A B C U} (p : (graph D).Walk s t) :
    WeightedNativeForcing.realCost (outerWeight wl wr) (projectWalk D p) =
      WeightedNativeForcing.realCost (realPrimary wl wr) p := by
  induction p with
  | nil => rfl
  | @cons s u t h p ih =>
    simp only [projectWalk]
    split_ifs with he
    · rw [realCost_copy,ih]
      simp [WeightedNativeForcing.realCost,realPrimary,he]
    · exact congrArg (fun z : ℝ => (outerWeight wl wr (projectVertex s) (projectVertex u) : ℝ) + z) ih

end LinearDistancePreservers.ObstacleProduct

namespace LinearDistancePreservers.WeightedNativeForcing
open SimpleGraph
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {V : Type*}

private theorem positive_sublist_sum {X : Type*} (f : X → ℝ)
    {l r : List X} (h : l.Sublist r) (hp : ∀ x ∈ r, 0 < f x) :
    (l.map f).sum ≤ (r.map f).sum ∧
      ((l.map f).sum = (r.map f).sum → l = r) := by
  induction h with
  | slnil => exact ⟨le_rfl,fun _ => rfl⟩
  | @cons l r a h ih =>
    obtain ⟨hle,_⟩ := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    have ha := hp a (List.mem_cons_self)
    have hs : (l.map f).sum < ((a::r).map f).sum := by
      simp only [List.map_cons,List.sum_cons]
      linarith
    exact ⟨hs.le,fun he => False.elim (hs.ne he)⟩
  | @cons_cons l r a h ih =>
    obtain ⟨hle,heq⟩ := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    refine ⟨by simpa using add_le_add_left hle (f a),?_⟩
    intro he
    have hh : (l.map f).sum = (r.map f).sum := by
      simpa only [List.map_cons,List.sum_cons,add_right_inj] using he
    rw [heq hh]

theorem realCost_bypass [DecidableEq V] {G : SimpleGraph V} (w : V → V → ℝ≥0)
    (hw : ∀ u v, G.Adj u v → 0 < w u v) {s t : V} (p : G.Walk s t) :
    realCost w p.bypass ≤ realCost w p ∧
      (realCost w p.bypass = realCost w p → p.bypass = p) := by
  obtain ⟨hle,heq⟩ := positive_sublist_sum (fun d : G.Dart => (w d.fst d.snd : ℝ))
    p.darts_bypass_sublist_darts (by intro d _; exact_mod_cast hw d.fst d.snd d.adj)
  refine ⟨hle,?_⟩
  intro he
  have hd := heq he
  apply (Walk.length_le_bypass_length_iff p).mp
  have hh := congrArg List.length hd
  simpa using hh.ge

/-- Unique shortest simple paths for positive edge weights are unique shortest
native walks, including all cyclic competitors. -/
theorem path_optimal_to_walk [DecidableEq V] {G : SimpleGraph V} (w : V → V → ℝ≥0)
    (hw : ∀ u v, G.Adj u v → 0 < w u v) {s t : V} (p : G.Walk s t)
    (hmin : ∀ q : G.Path s t, realCost w p ≤ realCost w q.val)
    (hunique : ∀ q : G.Path s t, realCost w q.val = realCost w p → q.val = p)
    (q : G.Walk s t) :
    realCost w p ≤ realCost w q ∧ (realCost w q = realCost w p → q = p) := by
  obtain ⟨hb,hbeq⟩ := realCost_bypass w hw q
  have hm := hmin q.toPath
  change realCost w p ≤ realCost w q.bypass at hm
  refine ⟨hm.trans hb,?_⟩
  intro he
  have he' : realCost w q.bypass = realCost w p := le_antisymm (hb.trans_eq he) hm
  have hq := hunique q.toPath he'
  have hself := hbeq (he'.trans he.symm)
  exact hself.symm.trans hq

end LinearDistancePreservers.WeightedNativeForcing
