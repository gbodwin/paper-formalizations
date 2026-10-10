import DirectedFlowCutGap.BinaryTapePrefix

/-! Full-state interpreter and prefix-budget rules used to compose the actual
binary callbacks through graph controllers. No observable projection is taken. -/
namespace DirectedFlowCutGap.StatefulTreeInterpreter
set_option backward.isDefEq.respectTransparency false
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler
variable {S A B : Type}

section Execute
variable {M : Type → Type} [Monad M] [LawfulMonad M] (b : M (Fin 2))

theorem bind_execute (p : StateT S FiniteDrawTrees.Tree A)
    (f : A → StateT S FiniteDrawTrees.Tree B) (q : StateT S M A)
    (g : A → StateT S M B)
    (hp : ∀ s, execute (liftBit b) (p.run s)=q.run s)
    (hf : ∀ a s, execute (liftBit b) ((f a).run s)=(g a).run s) (s : S) :
    execute (liftBit b) ((p >>= f).run s)=((q >>= g).run s) := by
  change execute (liftBit b) (FiniteDrawTrees.bind (p.run s) (fun x => (f x.1).run x.2)) = _
  rw [execute_bind,hp]
  congr 1
  funext x
  exact hf x.1 x.2

theorem map_execute (p : StateT S FiniteDrawTrees.Tree A) (q : StateT S M A)
    (f : A → B) (hp : ∀ s, execute (liftBit b) (p.run s)=q.run s) (s : S) :
    execute (liftBit b) ((f <$> p).run s)=((f <$> q).run s) := by
  exact bind_execute b p (fun a => pure (f a)) q (fun a => pure (f a)) hp
    (fun _ _ => rfl) s

end Execute

theorem binary_bind (p : StateT S FiniteDrawTrees.Tree A)
    (f : A → StateT S FiniteDrawTrees.Tree B)
    (hp : ∀ s, Binary (p.run s)) (hf : ∀ a s, Binary ((f a).run s)) (s : S) :
    Binary ((p >>= f).run s) :=
  LazyFairBitTrees.binary_bind (hp s) _ (fun x => hf x.1 x.2)

theorem binary_map (p : StateT S FiniteDrawTrees.Tree A) (f : A → B)
    (hp : ∀ s, Binary (p.run s)) (s : S) : Binary ((f <$> p).run s) := by
  exact binary_bind p (fun a => pure (f a)) hp (fun _ _ => .pure _) s

theorem within_bind (p : StateT S FiniteDrawTrees.Tree A)
    (f : A → StateT S FiniteDrawTrees.Tree B) {q r : ℕ}
    (hp : ∀ s, Within q (p.run s)) (hf : ∀ a s, Within r ((f a).run s)) (s : S) :
    Within (q+r) ((p >>= f).run s) :=
  FiniteDrawTrees.within_bind (hp s) _ (fun x => hf x.1 x.2)

theorem within_map (p : StateT S FiniteDrawTrees.Tree A) (f : A → B) {q : ℕ}
    (hp : ∀ s, Within q (p.run s)) (s : S) : Within q ((f <$> p).run s) := by
  exact within_bind p (fun a => pure (f a)) hp (r := 0) (fun _ _ => .pure 0 _) s

end DirectedFlowCutGap.StatefulTreeInterpreter
