import DirectedFlowCutGap.BinaryCutPriceSelection
import DirectedFlowCutGap.ChargedUniformRounding

/-!
# Charged selection among the rounded cover rows

Each row is rounded on the same lowered fair-bit tree as the solver.
The selected suffix carries its stored binary price, so comparing a
new mask needs only one new score. Ties preserve the earlier row.
-/

namespace DirectedFlowCutGap.ChargedCutSelection

open FiniteDrawTrees LazyFairBitTrees BinaryFractionalRows BinaryRational
open RetainedGridState (Flags)

theorem lower_bind {A B : Type} (T : ℕ) (t : FiniteDrawTrees.Tree A) (f : A → FiniteDrawTrees.Tree B) :
    lower T (t >>= f) = lower T t >>= fun a => lower T (f a) := by
  induction t with
  | pure a => rfl
  | draw n hn next ih =>
    change (rejection n hn T >>= fun a => lower T (next a.value >>= f)) =
      (rejection n hn T >>= fun a => lower T (next a.value)) >>= fun a => lower T (f a)
    rw [bind_assoc]
    congr 1
    funext a
    exact ih a.value

structure Scored {n : ℕ} (costs : Row n) where
  value : Flags n
  price : Fraction
  correct : decode price = EncodedCutSelection.maskCost (decodeRow costs) value

private def score {n : ℕ} (costs : Row n) (mask : Flags n) : Scored costs × ℕ :=
  let s := BinaryCutPriceSelection.maskScore costs mask
  (⟨mask, s.1, BinaryCutPriceSelection.maskScore_decodes costs mask⟩, s.2)

private def select {n : ℕ} {costs : Row n} (head : Flags n × ℕ)
    (tail : Option (Scored costs) × ℕ) : Option (Scored costs) × ℕ :=
  let a := score costs head.1
  let base := head.2 + tail.2 + a.2 + 10
  match tail.1 with
  | none => (some a.1, base)
  | some b =>
    let cmp := BinaryRational.le a.1.price b.price
    (some (if cmp.1 then a.1 else b), base + cmp.2)

private theorem select_value {n : ℕ} {costs : Row n} (head : Flags n × ℕ)
    (tail : Option (Scored costs) × ℕ) :
    (select head tail).1.map Scored.value = some
      ((tail.1.map Scored.value).elim head.1 (EncodedCutSelection.cheaper (decodeRow costs) head.1)) := by
  rcases tail with ⟨tail, paid⟩
  cases tail with
  | none => rfl
  | some b =>
    simp only [select, le_decode, Scored.correct, score, BinaryCutPriceSelection.maskScore_decodes,
      Option.map_some, Option.elim_some,
      EncodedCutSelection.cheaper]
    split <;> rfl

def best {n : ℕ} (costs : Row n) :
    List (FiniteDrawTrees.Tree (Flags n × ℕ)) → FiniteDrawTrees.Tree (Option (Scored costs) × ℕ)
  | [] => .pure (none, 1)
  | t :: ts => t >>= fun a => select a <$> best costs ts

def result {n : ℕ} {costs : Row n} (a : Option (Scored costs) × ℕ) : Option (Flags n) :=
  a.1.map Scored.value

theorem best_value {n : ℕ} (costs : Row n) (ts : List (FiniteDrawTrees.Tree (Flags n × ℕ))) :
    result <$> best costs ts = EncodedCutSelection.best (decodeRow costs) (ts.map (map Prod.fst)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change result <$> (t >>= fun a => select a <$> best costs ts) =
      (Prod.fst <$> t) >>= fun a =>
        (fun b => some (b.elim a (EncodedCutSelection.cheaper (decodeRow costs) a))) <$>
          EncodedCutSelection.best (decodeRow costs) (ts.map (map Prod.fst))
    simp only [map_bind, bind_map_left, ← ih, Functor.map_map]
    congr 1
    funext a
    congr 1
    funext b
    exact select_value a b

theorem lower_best {n : ℕ} (T : ℕ) (costs : FractionalCoverRawCore.RawRow n)
    (ts : List (FiniteDrawTrees.Tree (Flags n))) :
    lower T (EncodedCutSelection.best costs ts) =
      EncodedCutSelection.best costs (ts.map (lower T)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change lower T (t >>= fun a =>
      (fun b => some (b.elim a (EncodedCutSelection.cheaper costs a))) <$> EncodedCutSelection.best costs ts) = _
    rw [lower_bind]
    simp only [← ChargedUniformRounding.map_lower, ih, List.map_cons, EncodedCutSelection.best]
    rfl

def rowBound (n B roundBudget : ℕ) : ℕ :=
  roundBudget + sumBound n B + 10 + 2048 * (n * (B + 1) + 2)^2

theorem best_charge {n B : ℕ} (costs : Row n) (ts : List (FiniteDrawTrees.Tree (Flags n × ℕ)))
    (roundBudget : ℕ)
    (hB : 1 ≤ B) (hc : ∀ i, StoredBounded (get costs i) B)
    (hround : ∀ t ∈ ts, ∀ a ∈ (ideal t).support, a.2 ≤ roundBudget)
    {out : Option (Scored costs) × ℕ} (ho : out ∈ (ideal (best costs ts)).support) :
    (∀ s ∈ out.1, StoredBounded s.price (n * (B + 1) + 1)) ∧
      out.2 ≤ ts.length * rowBound n B roundBudget + 1 := by
  induction ts generalizing out with
  | nil =>
    have h : out = (none, 1) := by simpa [best, ideal, law] using ho
    subst out
    simp
  | cons t ts ih =>
    have hbind : ideal (best costs (t :: ts)) =
        (ideal t).bind (fun a => (ideal (best costs ts)).map (select a)) := by
      change law uniformDraw (FiniteDrawTrees.bind t (fun a => map (select a) (best costs ts))) = _
      simp only [ideal, law_bind, law_map]
    rw [hbind] at ho
    obtain ⟨a, ha, hh⟩ := (PMF.mem_support_bind_iff _ _ _).mp ho
    obtain ⟨b, hb, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
    obtain ⟨htw, htc⟩ := ih (fun u hu => hround u (List.mem_cons_of_mem _ hu)) hb
    obtain ⟨hw, hpc⟩ := BinaryCutPriceSelection.maskScore_charge costs a.1 hB hc
    have ha' := hround t List.mem_cons_self a ha
    have len : (t :: ts).length * rowBound n B roundBudget =
        ts.length * rowBound n B roundBudget + rowBound n B roundBudget := by
      rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    rw [len]
    cases hbval : b.1 with
    | none =>
      exact ⟨by simpa [select, hbval, score] using hw, by
        simp only [select, hbval, score, rowBound] at *
        omega⟩
    | some s =>
      have hsw : StoredBounded s.price (n * (B + 1) + 1) := htw s (by rw [hbval]; simp)
      have hcmp := le_charge hw hsw
      change (BinaryRational.le (BinaryCutPriceSelection.maskScore costs a.1).1 s.price).2 ≤
        2048 * (n * (B + 1) + 2)^2 at hcmp
      have htotal : a.2 + b.2 + (BinaryCutPriceSelection.maskScore costs a.1).2 + 10 +
          (BinaryRational.le (BinaryCutPriceSelection.maskScore costs a.1).1 s.price).2 ≤
          ts.length * rowBound n B roundBudget + rowBound n B roundBudget + 1 := by
        simp only [rowBound] at htc ⊢
        omega
      simp only [select, hbval, Option.mem_some_iff]
      split
      · exact ⟨fun u hu => hu.symm ▸ hw, htotal⟩
      · exact ⟨fun u hu => hu.symm ▸ hsw, htotal⟩

end DirectedFlowCutGap.ChargedCutSelection
