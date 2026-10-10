import DirectedFlowCutGap.RawNonnegativeRational
import DirectedFlowCutGap.IntegerWeightedChoice

/-!
# Integer masses constructed from retained rational amounts

The constructor multiplies actual stored denominators and rescales earlier
integer masses. It uses no gcd, division, arbitrary denominator witness or
expansion into a list with one entry per ticket. Labels and list length are
preserved. The stored natural fields have linear bit-width bounds in the number
of supplied rational fields and their width.

These are value and representation results. The binary implementation, its
operation charges, fair-bit execution and adaptive probability join remain
separate obligations.
-/
namespace DirectedFlowCutGap.RawWeightedMasses
open scoped BigOperators
open RawNonnegativeRational IntegerWeightedChoice

variable {A : Type*}

def scale (d : ℕ) (xs : List (A × ℕ)) : List (A × ℕ) :=
  xs.map fun x => (x.1, d*x.2)

def encode : List (A × Code) → ℕ × List (A × ℕ)
  | [] => (1, [])
  | (a,q)::xs =>
      let tail := encode xs
      (q.den*tail.1, (a,q.num*tail.1)::scale q.den tail.2)

theorem encode_den_positive (xs : List (A × Code)) : 0 < (encode xs).1 := by
  induction xs with
  | nil => simp [encode]
  | cons x xs ih => exact Nat.mul_pos x.2.positive_den ih

theorem encode_labels (xs : List (A × Code)) :
    (encode xs).2.map Prod.fst = xs.map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [encode,scale,List.map_map,Function.comp_def] using congrArg (List.cons x.1) ih

theorem encode_length (xs : List (A × Code)) : (encode xs).2.length = xs.length := by
  have h := congrArg List.length (encode_labels xs)
  simpa using h

theorem selected_scale (d : ℕ) (xs : List (A × ℕ)) (p : A → Bool) :
    selectedMass (scale d xs) p = d * selectedMass xs p := by
  induction xs with
  | nil => simp [scale,selectedMass]
  | cons x xs ih =>
      change (if p x.1 then d*x.2 else 0) + selectedMass (scale d xs) p =
        d*((if p x.1 then x.2 else 0) + selectedMass xs p)
      rw [ih]
      cases p x.1 <;> simp [mul_add]

/-- Every constructed field has at most the sum of the supplied width bounds,
up to the one-bit endpoint convention in `Code.Bounded`. -/
theorem encode_bounded (xs : List (A × Code)) (B : ℕ)
    (h : ∀ x ∈ xs, x.2.Bounded B) :
    (encode xs).1 ≤ 2^(xs.length*B) ∧
      ∀ x ∈ (encode xs).2, x.2 ≤ 2^(xs.length*B) := by
  induction xs with
  | nil => simp [encode]
  | cons x xs ih =>
      have hx := h x List.mem_cons_self
      obtain ⟨hd,hm⟩ := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      have hp : (2 : ℕ)^B * 2^(xs.length*B) = 2^((xs.length+1)*B) := by
        rw [← pow_add]
        congr 1
        ring
      constructor
      · exact (Nat.mul_le_mul hx.2 hd).trans_eq (by simpa using hp)
      · intro y hy
        change y ∈ (x.1,x.2.num*(encode xs).1)::scale x.2.den (encode xs).2 at hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (Nat.mul_le_mul hx.1 hd).trans_eq (by simpa using hp)
        · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
          exact (Nat.mul_le_mul hx.2 (hm z hz)).trans_eq (by simpa using hp)

/-- The total ticket count is bounded by the actual number of retained entries,
without expanding the mass list into individual tickets. -/
theorem total_le_length_mul (xs : List (A × ℕ)) (B : ℕ)
    (h : ∀ x ∈ xs, x.2 ≤ B) : total xs ≤ xs.length * B := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
      have hx := h x List.mem_cons_self
      have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [total, List.map_cons, List.sum_cons, List.length_cons]
      change x.2 + total xs ≤ (xs.length + 1) * B
      nlinarith

theorem encode_total_bounded (xs : List (A × Code)) (B : ℕ)
    (h : ∀ x ∈ xs, x.2.Bounded B) :
    total (encode xs).2 ≤ xs.length * 2^(xs.length * B) := by
  have hm := total_le_length_mul (encode xs).2 (2^(xs.length * B))
    (encode_bounded xs B h).2
  simpa only [encode_length] using hm

noncomputable section

def selectedValue (xs : List (A × Code)) (p : A → Bool) : ℝ :=
  (xs.map fun x => if p x.1 then (x.2.value : ℝ) else 0).sum

theorem denominator_value (q : Code) : (q.den : ℝ) * (q.value : ℝ) = q.num := by
  have hd : (q.den : ℚ≥0) ≠ 0 := by exact_mod_cast ne_of_gt q.positive_den
  have h : (q.den : ℚ≥0) * q.value = q.num := by
    dsimp [Code.value]
    field_simp [hd]
  exact_mod_cast h

/-- The same positive common denominator scales every predicate's mass. -/
theorem encode_selected (xs : List (A × Code)) (p : A → Bool) :
    (selectedMass (encode xs).2 p : ℝ) = (encode xs).1 * selectedValue xs p := by
  induction xs with
  | nil => simp [encode,selectedMass,selectedValue]
  | cons x xs ih =>
      rcases x with ⟨a,q⟩
      change (((if p a then q.num*(encode xs).1 else 0) +
        selectedMass (scale q.den (encode xs).2) p : ℕ) : ℝ) =
          ((q.den*(encode xs).1 : ℕ) : ℝ) *
            ((if p a then (q.value : ℝ) else 0) + selectedValue xs p)
      rw [selected_scale]
      push_cast
      rw [ih]
      have hq := denominator_value q
      cases p a
      · simp [mul_assoc]
      · simp only [ite_true]
        have he : (q.num : ℝ)*(encode xs).1 =
            (q.den : ℝ)*(encode xs).1*(q.value : ℝ) := by
          rw [← hq]
          ring
        rw [he]
        ring

theorem encode_total (xs : List (A × Code)) :
    (total (encode xs).2 : ℝ) = (encode xs).1 * selectedValue xs (fun _ => true) := by
  simpa [selectedMass,total] using encode_selected xs (fun _ => true)

theorem encode_total_positive (xs : List (A × Code))
    (h : 0 < selectedValue xs (fun _ => true)) : 0 < total (encode xs).2 := by
  have hd : (0 : ℝ) < (encode xs).1 := by exact_mod_cast encode_den_positive xs
  have ht : (0 : ℝ) < total (encode xs).2 := by rw [encode_total]; positivity
  exact_mod_cast ht

theorem encode_ratio (xs : List (A × Code)) (p : A → Bool) :
    (selectedMass (encode xs).2 p : ℝ) / (total (encode xs).2 : ℝ) =
      selectedValue xs p / selectedValue xs (fun _ => true) := by
  rw [encode_selected,encode_total]
  have hd : ((encode xs).1 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (encode_den_positive xs)
  exact mul_div_mul_left _ _ hd

/-- The ideal law of the literal integer selector has exactly the original
retained-rational probability ratio. Sampling that law efficiently is separate. -/
theorem encoded_law_probability [Fintype A] (xs : List (A × Code))
    (h : 0 < selectedValue xs (fun _ => true)) (p : A → Bool) :
    FiniteAmplification.probability
      (IntegerWeightedChoice.law (encode xs).2 (encode_total_positive xs h))
      (fun x => x.any p = true) =
      selectedValue xs p / selectedValue xs (fun _ => true) := by
  rw [law_probability,encode_ratio]

end
end DirectedFlowCutGap.RawWeightedMasses
