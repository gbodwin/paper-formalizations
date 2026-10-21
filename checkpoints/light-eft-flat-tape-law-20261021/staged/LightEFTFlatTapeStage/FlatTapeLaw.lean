import LightEFTPaidJointBridgeStage.SuppliedResponseJointBridge

/-!
Source-only checkpoint: a finite-vector reindexing and its IDEAL product law.
No random-bit generator, physical tape allocation, paid enumeration or cost
bound is asserted. In particular, the supplied-response bridge does not supply
the law used below: idealTapeLaw is defined independently as a literal product.
-/
namespace LightEFTSpanners.FlatTape
open Finset FiniteProbability JointFlagSampling
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Number of cells in the accepted tail-first occurrence/host/repetition/edge order. -/
noncomputable def tapeLength (n m : ℕ) (l : List (OriginalEdge n)) : ℕ :=
  (samplingSchedule (J:=J) n m l).length

abbrev Tape (n m : ℕ) (l : List (OriginalEdge n)) :=
  Fin (tapeLength (J:=J) n m l) → Bool

theorem tapeLength_eq (n m : ℕ) (l : List (OriginalEdge n)) :
    tapeLength (J:=J) n m l =
      l.length * Fintype.card J * m * Fintype.card (OriginalEdge n) := by
  exact samplingSchedule_length (J:=J) n m l

/-- Forward lookup is exactly schedule.get; the inverse is mathematical, not charged. -/
noncomputable def coordinateEquiv (n m : ℕ) (l : List (OriginalEdge n)) :
    Fin (tapeLength (J:=J) n m l) ≃ Coordinate n J m l :=
  Equiv.ofBijective (samplingSchedule (J:=J) n m l).get
    ⟨(samplingSchedule_nodup (J:=J) n m l).injective_get,
      fun c => List.mem_iff_get.mp (mem_samplingSchedule (J:=J) n m l c)⟩

theorem coordinateEquiv_apply (n m : ℕ) (l : List (OriginalEdge n))
    (k : Fin (tapeLength (J:=J) n m l)) :
    coordinateEquiv (J:=J) n m l k = (samplingSchedule (J:=J) n m l).get k := rfl

/-- Flattening retains occurrence POSITIONS even if their candidate keys coincide. -/
theorem distinct_occurrence_indices (n m : ℕ) (l : List (OriginalEdge n))
    (p q : Fin l.length) (hpq : p ≠ q) (j : J) (i : Fin m) (d : OriginalEdge n) :
    (coordinateEquiv (J:=J) n m l).symm (p,j,i,d) ≠
      (coordinateEquiv (J:=J) n m l).symm (q,j,i,d) := by
  intro h
  have hc := (coordinateEquiv (J:=J) n m l).symm.injective h
  exact hpq (congrArg Prod.fst hc)

/-- A bijection of finite data, not an executable response generator. -/
noncomputable def tapeEquiv (n m : ℕ) (l : List (OriginalEdge n)) :
    Tape (J:=J) n m l ≃ JointFlags n J m l where
  toFun tape p j i d := tape ((coordinateEquiv (J:=J) n m l).symm (p,j,i,d))
  invFun bits k :=
    bits (coordinateEquiv (J:=J) n m l k).1
      (coordinateEquiv (J:=J) n m l k).2.1
      (coordinateEquiv (J:=J) n m l k).2.2.1
      (coordinateEquiv (J:=J) n m l k).2.2.2
  left_inv tape := by
    funext k
    change tape ((coordinateEquiv (J:=J) n m l).symm
      (coordinateEquiv (J:=J) n m l k)) = tape k
    rw [Equiv.symm_apply_apply]
  right_inv bits := by
    funext p j i d
    change (fun c : Coordinate n J m l => bits c.1 c.2.1 c.2.2.1 c.2.2.2)
      ((coordinateEquiv (J:=J) n m l)
        ((coordinateEquiv (J:=J) n m l).symm (p,j,i,d))) = bits p j i d
    rw [Equiv.apply_symm_apply]

theorem tapeEquiv_apply (n m : ℕ) (l : List (OriginalEdge n))
    (tape : Tape (J:=J) n m l) (p : Fin l.length) (j : J) (i : Fin m)
    (d : OriginalEdge n) :
    tapeEquiv (J:=J) n m l tape p j i d =
      tape ((coordinateEquiv (J:=J) n m l).symm (p,j,i,d)) := rfl

/-- Each scheduled cell reads exactly its corresponding flat position. -/
theorem tapeEquiv_at_position (n m : ℕ) (l : List (OriginalEdge n))
    (tape : Tape (J:=J) n m l) (k : Fin (tapeLength (J:=J) n m l)) :
    tapeEquiv (J:=J) n m l tape
      (coordinateEquiv (J:=J) n m l k).1
      (coordinateEquiv (J:=J) n m l k).2.1
      (coordinateEquiv (J:=J) n m l k).2.2.1
      (coordinateEquiv (J:=J) n m l k).2.2.2 = tape k := by
  change tape ((coordinateEquiv (J:=J) n m l).symm
    (coordinateEquiv (J:=J) n m l k)) = tape k
  rw [Equiv.symm_apply_apply]

/-- Literal iid finite-vector law. Its realization by a generator is not assumed. -/
noncomputable def idealTapeLaw (n f m : ℕ) (hf : 0 < f)
    (l : List (OriginalEdge n)) : Law (Tape (J:=J) n m l) :=
  BernoulliFlags.law (α:=Fin (tapeLength (J:=J) n m l)) (1/(2*(f:ℝ)))
    (by positivity) (by
      have hf1 : (1:ℝ) ≤ f := by exact_mod_cast hf
      apply (div_le_one (by positivity)).mpr
      linarith)

theorem idealTapeLaw_mass (n f m : ℕ) (hf : 0 < f)
    (l : List (OriginalEdge n)) (tape : Tape (J:=J) n m l) :
    (idealTapeLaw (J:=J) n f m hf l).mass tape =
      ∏ k, if tape k then 1/(2*(f:ℝ)) else 1-1/(2*(f:ℝ)) := rfl

/-- Equality of masses under the bijection; no coordinate independence premise is hidden. -/
theorem tape_mass_eq_joint_mass (n f m : ℕ) (hf : 0 < f)
    (l : List (OriginalEdge n)) (tape : Tape (J:=J) n m l) :
    (idealTapeLaw (J:=J) n f m hf l).mass tape =
      (jointSourceLaw (J:=J) n f m hf l).mass (tapeEquiv (J:=J) n m l tape) := by
  classical
  rw [idealTapeLaw_mass, jointSourceLaw_mass]
  change (∏ k, if tape k then 1/(2*(f:ℝ)) else 1-1/(2*(f:ℝ))) =
    ∏ p, ∏ j, ∏ i, ∏ d,
      if tape ((coordinateEquiv (J:=J) n m l).symm (p,j,i,d))
      then 1/(2*(f:ℝ)) else 1-1/(2*(f:ℝ))
  let factor : Coordinate n J m l → ℝ := fun c =>
    if tape ((coordinateEquiv (J:=J) n m l).symm c)
      then 1/(2*(f:ℝ)) else 1-1/(2*(f:ℝ))
  have he := (coordinateEquiv (J:=J) n m l).prod_comp factor
  simpa only [factor, Equiv.symm_apply_apply, Fintype.prod_prod_type] using he

theorem tape_event_probability (n f m : ℕ) (hf : 0 < f)
    (l : List (OriginalEdge n)) (P : JointFlags n J m l → Prop) :
    (idealTapeLaw (J:=J) n f m hf l).prob
        (fun tape => P (tapeEquiv (J:=J) n m l tape)) =
      (jointSourceLaw (J:=J) n f m hf l).prob P := by
  classical
  unfold Law.prob
  calc
    _ = ∑ tape : Tape (J:=J) n m l,
        if P (tapeEquiv (J:=J) n m l tape)
        then (jointSourceLaw (J:=J) n f m hf l).mass (tapeEquiv (J:=J) n m l tape)
        else 0 := by
      apply Finset.sum_congr rfl
      intro tape _
      rw [tape_mass_eq_joint_mass]
    _ = _ := (tapeEquiv (J:=J) n m l).sum_comp
      (fun bits => if P bits then (jointSourceLaw (J:=J) n f m hf l).mass bits else 0)

/-- Exact pushforward from the explicitly defined ideal flat tape to the accepted source. -/
theorem tape_joint_law (n f m : ℕ) (hf : 0 < f) (l : List (OriginalEdge n)) :
    (idealTapeLaw (J:=J) n f m hf l).map (tapeEquiv (J:=J) n m l) =
      jointSourceLaw (J:=J) n f m hf l := by
  apply JointFlagSampling.Transport.eq_of_prob_eq
  intro P
  rw [Law.prob_map]
  exact tape_event_probability (J:=J) n f m hf l P

/-- Inherit the supplied-response interpretation under this IDEAL tape law only. -/
theorem tape_supplied_assignment_probability (n f m : ℕ) (hf : 0 < f)
    (l : List (OriginalEdge n)) (P : SampledGreedy.Assignment (Fin n) J m → Prop) :
    (idealTapeLaw (J:=J) n f m hf l).prob
        (fun tape => P (PaidJointBridge.storedAssignment l
          (tapeEquiv (J:=J) n m l tape))) =
      (SampledGreedy.executionLaw (V:=Fin n) (J:=J) f hf m l).prob P := by
  calc
    _ = (jointSourceLaw (J:=J) n f m hf l).prob
        (fun bits => P (PaidJointBridge.storedAssignment l bits)) :=
      tape_event_probability (J:=J) n f m hf l _
    _ = _ := PaidJointBridge.supplied_assignment_event_probability (J:=J) n f m hf l P

end LightEFTSpanners.FlatTape
