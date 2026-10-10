import DirectedFlowCutGap.MonadicBitSampler

/-!
# Exact finite-prefix law for a bounded binary draw tree

A fixed list reader consumes one actual bit at a reached binary draw. Its
returned suffix is the actual state, and a sufficiently long independent
uniform prefix has exactly the tree's fair-bit output law. Empty-source
defaults remain defined but are never used under the proved path bound.
This is a tree-interpreter certificate; applying it to an encoded host program
still requires that program's same-stream refinement, not just a PMF marginal.
-/
namespace DirectedFlowCutGap.FiniteBinaryPrefix
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler

def next : StateM (List (Fin 2)) (Fin 2) := fun xs =>
  match xs with
  | [] => (0,[])
  | b::bs => (b,bs)

def run {A : Type} (p : FiniteDrawTrees.Tree A) : StateM (List (Fin 2)) A :=
  execute (liftBit next) p

theorem run_pure {A : Type} (a : A) (xs : List (Fin 2)) :
    (run (.pure a)).run xs=(a,xs) := rfl

theorem run_cons {A : Type} (p : Fin 2 → FiniteDrawTrees.Tree A) (b : Fin 2) (xs : List (Fin 2)) :
    (run (.draw 2 (by decide) p)).run (b::xs)=(run (p b)).run xs := by
  simp only [run,execute,liftBit_two]
  rfl

/-- The result state is an actual suffix after at most the proved number of
requests. There is no restart, resampling, or second execution. -/
theorem suffix {A : Type} {p : FiniteDrawTrees.Tree A} {q : ℕ}
    (hq : Within q p) (hb : Binary p) (xs : List (Fin 2)) (hlen : q ≤ xs.length) :
    ∃ used ≤ q, ((run p).run xs).2 = xs.drop used := by
  induction hq generalizing xs with
  | pure q a => exact ⟨0,Nat.zero_le _,rfl⟩
  | @draw q n hn p hc ih =>
      cases hb with
      | draw hb =>
          cases xs with
          | nil => simp only [List.length_nil] at hlen;omega
          | cons b bs =>
              obtain ⟨used,hu,hs⟩ := ih b (hb b) bs (by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hlen)
              refine ⟨used+1,Nat.succ_le_succ hu,?_⟩
              rw [run_cons,hs,List.drop_succ_cons]

noncomputable section

def prefixLaw : ℕ → PMF (List (Fin 2))
  | 0 => PMF.pure []
  | q+1 => (PMF.uniformOfFintype (Fin 2)).bind fun b =>
      (prefixLaw q).map (List.cons b)

theorem prefix_length (q : ℕ) {xs : List (Fin 2)} (hxs : xs ∈ (prefixLaw q).support) :
    xs.length=q := by
  induction q generalizing xs with
  | zero =>
      have he := (PMF.mem_support_pure_iff _ _).mp hxs
      subst xs
      rfl
  | succ q ih =>
      obtain ⟨b,hb,hxs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hxs
      obtain ⟨bs,hbs,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hxs
      simpa only [List.length_cons] using congrArg Nat.succ (ih hbs)

/-- Only the output projection is taken here; the suffix theorem above binds
the actual source-state transition independently on every supported prefix. -/
theorem output_law {A : Type} {p : FiniteDrawTrees.Tree A} {q : ℕ}
    (hq : Within q p) (hb : Binary p) :
    (prefixLaw q).map (fun xs => ((run p).run xs).1)=ideal p := by
  induction hq with
  | pure q a =>
      change (prefixLaw q).map (Function.const _ a)=PMF.pure a
      exact PMF.map_const _ _
  | @draw q n hn p hc ih =>
      cases hb with
      | draw hb =>
          simp only [prefixLaw,PMF.map_bind,ideal,law]
          congr 1
          funext b
          rw [PMF.map_comp]
          simpa only [Function.comp_def,run_cons] using ih b (hb b)

/-- The existing whole-monad refinement identifies the same finite-source
execution of the direct monadic decoder, including its actual bit position. -/
theorem direct_output_law {A : Type} {p : FiniteDrawTrees.Tree A} {q w : ℕ}
    (hq : Within q p) (hw : WidthsLE w p) (T : ℕ) :
    (prefixLaw (q*T*w)).map (fun xs =>
      ((execute (MonadicBitSampler.sample next T) p).run xs).1)=actual T p := by
  rw [← execute_lower_refines next T p]
  change (prefixLaw (q*T*w)).map (fun xs => ((run (lower T p)).run xs).1)=_
  rw [output_law (lower_within hq hw T) (lower_binary T p),lower_law]

theorem direct_suffix {A : Type} {p : FiniteDrawTrees.Tree A} {q w : ℕ}
    (hq : Within q p) (hw : WidthsLE w p) (T : ℕ)
    (xs : List (Fin 2)) (hlen : q*T*w ≤ xs.length) :
    ∃ used ≤ q*T*w, ((execute (MonadicBitSampler.sample next T) p).run xs).2=xs.drop used := by
  rw [← execute_lower_refines next T p]
  exact suffix (lower_within hq hw T) (lower_binary T p) xs hlen

/-- Bias from bounded rejection remains explicit for the actual one-stream
finite-prefix execution. The source is never restarted between adaptive draws. -/
theorem direct_event_le {A : Type} [Fintype A] {p : FiniteDrawTrees.Tree A} {q w : ℕ}
    (hq : Within q p) (hw : WidthsLE w p) (T : ℕ) (P : A → Prop) :
    FiniteAmplification.probability
      ((prefixLaw (q*T*w)).map (fun xs =>
        ((execute (MonadicBitSampler.sample next T) p).run xs).1)) P ≤
      FiniteAmplification.probability (ideal p) P+(q : ℝ)*((1 : ℝ)/2)^T := by
  rw [direct_output_law hq hw T]
  exact FiniteDrawTrees.event_le hq T P

end
end DirectedFlowCutGap.FiniteBinaryPrefix
