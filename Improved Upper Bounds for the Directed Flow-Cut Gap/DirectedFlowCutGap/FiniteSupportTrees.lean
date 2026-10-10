import DirectedFlowCutGap.LazyFairBitTrees

/-! Proof-only support indexing of a finite draw tree. Branches and leaf data
are unchanged; no support test, filtering, or resampling is executed. This
adapter lets dependent validity certificates follow the actual returned leaf. -/
namespace DirectedFlowCutGap.FiniteSupportTrees
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteDrawTrees LazyFairBitTrees

private theorem child_support {A : Type} (n : ℕ) (hn : 0<n)
    (next : Fin n → FiniteDrawTrees.Tree A) (i : Fin n) {a : A}
    (ha : a∈(ideal (next i)).support) :
    a∈(ideal (.draw n hn next)).support := by
  have : NeZero n := ⟨hn.ne'⟩
  exact (PMF.mem_support_bind_iff _ _ a).mpr
    ⟨i,PMF.mem_support_uniformOfFintype i,ha⟩

/-- Only the erased proof argument is added at a reached leaf. -/
def mapSupport {A B : Type} (p : FiniteDrawTrees.Tree A)
    (f : ∀ a∈(ideal p).support,B) : FiniteDrawTrees.Tree B :=
  match p with
  | .pure a => .pure (f a ((PMF.mem_support_pure_iff a a).mpr rfl))
  | .draw n hn next => .draw n hn (fun i =>
      mapSupport (next i) (fun a ha => f a (child_support n hn next i ha)))

theorem within {A B : Type} {p : FiniteDrawTrees.Tree A} {q : ℕ}
    (hp : Within q p) (f : ∀ a∈(ideal p).support,B) :
    Within q (mapSupport p f) := by
  induction hp with
  | pure q a => exact .pure q _
  | draw hc ih => exact .draw (fun i => ih i _)

theorem binary {A B : Type} {p : FiniteDrawTrees.Tree A}
    (hp : Binary p) (f : ∀ a∈(ideal p).support,B) :
    Binary (mapSupport p f) := by
  induction hp with
  | pure a => exact .pure _
  | draw hc ih => exact .draw (fun i => ih i _)

/-- Erasing the proof argument gives the literal ordinary mapped tree. -/
theorem mapSupport_plain {A B : Type} (p : FiniteDrawTrees.Tree A) (f : A → B) :
    mapSupport p (fun a _ => f a)=FiniteDrawTrees.map f p := by
  induction p with
  | pure a => rfl
  | draw n hn next ih =>
      change FiniteDrawTrees.Tree.draw n hn _=FiniteDrawTrees.Tree.draw n hn _
      congr 1
      funext i
      exact ih i

/-- The dependent adapter has exactly the existing support-indexed PMF law. -/
theorem law {A B : Type} (p : FiniteDrawTrees.Tree A)
    (f : ∀ a∈(ideal p).support,B) :
    ideal (mapSupport p f)=
      (ideal p).bindOnSupport (fun a ha => PMF.pure (f a ha)) := by
  classical
  obtain ⟨a₀,ha₀⟩ := (ideal p).support_nonempty
  let g : A → B := fun a => if ha : a∈(ideal p).support then f a ha else f a₀ ha₀
  have hg (a : A) (ha : a∈(ideal p).support) : g a=f a ha := by simp only [g,dite_eq_left ha]
  have he : mapSupport p f=mapSupport p (fun a _ => g a) := by
    congr 1
    funext a ha
    exact (hg a ha).symm
  rw [he,mapSupport_plain]
  change FiniteDrawTrees.law uniformDraw (FiniteDrawTrees.map g p)=_
  rw [FiniteDrawTrees.law_map]
  change (ideal p).bind (fun a => PMF.pure (g a))=_
  rw [← PMF.bindOnSupport_eq_bind]
  congr 1
  funext a ha
  rw [hg a ha]

/-- A structural maximum is a finite sufficient prefix budget. This proof-side
quantity is not an efficient budget-construction or runtime bound. -/
def depth {A : Type} : FiniteDrawTrees.Tree A → ℕ
  | .pure _ => 0
  | .draw _ _ next => (Finset.univ.sup fun i => depth (next i))+1

theorem depth_within {A : Type} (p : FiniteDrawTrees.Tree A) : Within (depth p) p := by
  induction p with
  | pure a => exact .pure 0 a
  | draw n hn next ih =>
      exact .draw (fun i => within_mono (ih i) (Finset.le_sup (f := fun j => depth (next j)) (Finset.mem_univ i)))

end
end DirectedFlowCutGap.FiniteSupportTrees
