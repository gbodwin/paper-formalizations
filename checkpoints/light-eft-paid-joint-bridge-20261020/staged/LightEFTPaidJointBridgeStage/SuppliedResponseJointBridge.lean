import LightEFTPaidSamplingStage.PaidFlagSampleComposition
import LightEFTJointFlagSamplingStage.JointAssignmentLaw
import LightEFTSpanners.StoredFlagSampleEncoding

/-!
Source-only, unelaborated bridge over SUPPLIED response functions. The canonical
edge order, response extraction and assignment fold are mathematical data.
Their construction is not charged by the local serialization/filter trace.
The event theorem uses the accepted ideal joint source law; it does not assert
that a finite-bit generator, flattened response tape or paid sampler has that law.
-/
namespace LightEFTSpanners.PaidJointBridge
open Controller Finset
attribute [local instance] Classical.propDecidable

/-- The identical original-edge order used by StoredFlagSample.entries/typed. -/
noncomputable def edgeOrder (n : ℕ) : List (JointFlagSampling.OriginalEdge n) :=
  (univ : Finset (JointFlagSampling.OriginalEdge n)).toList

noncomputable def rawKeys (n : ℕ) : List StoredEdges.Edge :=
  (edgeOrder n).map fun e => (e.out.1.val,e.out.2.val)

noncomputable def responses {n : ℕ}
    (bits : JointFlagSampling.OriginalEdge n → Bool) : List Bool :=
  (edgeOrder n).map bits

theorem response_length {n : ℕ} (bits : JointFlagSampling.OriginalEdge n → Bool) :
    (responses bits).length = (rawKeys n).length := by
  simp only [responses, rawKeys, List.length_map]

theorem rawKeys_length (n : ℕ) :
    (rawKeys n).length = Fintype.card (JointFlagSampling.OriginalEdge n) := by
  simp only [rawKeys, edgeOrder, List.length_map, Finset.length_toList, Finset.card_univ]

/-- Both lists use the same order, without dropping false responses or rows. -/
theorem zip_eq_entries {n : ℕ} (bits : JointFlagSampling.OriginalEdge n → Bool) :
    (rawKeys n).zip (responses bits) = StoredFlagSample.entries bits := by
  unfold rawKeys responses StoredFlagSample.entries edgeOrder
  rw [List.zip_map']

theorem serialize_eq_entries {n : ℕ}
    (bits : JointFlagSampling.OriginalEdge n → Bool) :
    PaidFlagSerialization.execute (rawKeys n) (responses bits) =
      some (StoredFlagSample.entries bits) := by
  rw [PaidFlagSerialization.execute_eq _ _ (response_length bits), zip_eq_entries]

theorem value_eq_encoded {n : ℕ} (bits : JointFlagSampling.OriginalEdge n → Bool) :
    StoredFlagSample.value ((rawKeys n).zip (responses bits)) =
      StoredEdges.encode (StoredFlagSample.typed bits) := by
  rw [zip_eq_entries]
  exact (StoredFlagSample.execute_eq _).symm.trans (StoredFlagSample.execute_encoded bits)

/-- Local supplied-input trace only: no charge for constructing either input list. -/
theorem batch_trace {n : ℕ} (bits : JointFlagSampling.OriginalEdge n → Bool) :
    ∃ k, k ≤ 5*Fintype.card (JointFlagSampling.OriginalEdge n)+5 ∧
      Trace PaidFlagSampleComposition.transition k
        (.serialize (.collect (rawKeys n) (responses bits) []))
        (.filter (.halt (StoredEdges.encode (StoredFlagSample.typed bits)))) := by
  obtain ⟨k,hk,ht⟩ := PaidFlagSampleComposition.full_trace
    (rawKeys n) (responses bits) (response_length bits)
  rw [rawKeys_length] at hk
  rw [value_eq_encoded] at ht
  exact ⟨k,hk,ht⟩

theorem batch_execute {n : ℕ} (bits : JointFlagSampling.OriginalEdge n → Bool) :
    PaidFlagSampleComposition.execute (rawKeys n) (responses bits) =
      some (StoredEdges.encode (StoredFlagSample.typed bits)) := by
  rw [PaidFlagSampleComposition.execute_eq _ _ (response_length bits), value_eq_encoded]

/-- Every occurrence has its own supplied batch, even when candidate keys repeat. -/
theorem execute_occurrence_batch {n m : ℕ} {J : Type*}
    (l : List (JointFlagSampling.OriginalEdge n))
    (bits : JointFlagSampling.JointFlags n J m l) (p : Fin l.length) (j : J) (i : Fin m) :
    ∃ rows : List (Fin n × Fin n),
      PaidFlagSampleComposition.execute (rawKeys n) (responses (bits p j i)) =
        some (StoredEdges.encode rows) ∧
      StoredSample.edgeSet rows = JointFlagSampling.decodeHost (bits p) j i := by
  refine ⟨StoredFlagSample.typed (bits p j i), batch_execute _, ?_⟩
  exact StoredFlagSample.typed_edgeSet _

/-- Mathematical interpretation of the exact typed witnesses returned above. -/
noncomputable def storedHost {n m : ℕ} {J : Type*}
    (bits : JointFlagSampling.HostFlags n J m) :
    J → Fin m → Finset (JointFlagSampling.OriginalEdge n) :=
  fun j i => StoredSample.edgeSet (StoredFlagSample.typed (bits j i))

theorem storedHost_eq_decodeHost {n m : ℕ} {J : Type*}
    (bits : JointFlagSampling.HostFlags n J m) :
    storedHost bits = JointFlagSampling.decodeHost bits := by
  funext j i
  exact StoredFlagSample.typed_edgeSet _

/-- A representation fold, not an operational trace or charged bank constructor. -/
noncomputable def storedAssignment {n m : ℕ} {J : Type*} :
    (l : List (JointFlagSampling.OriginalEdge n)) → JointFlagSampling.JointFlags n J m l →
      SampledGreedy.Assignment (Fin n) J m :=
  List.rec
    (motive := fun l => JointFlagSampling.JointFlags n J m l →
      SampledGreedy.Assignment (Fin n) J m)
    (fun _ => fun _ _ _ => ∅)
    (fun e _es decodeTail bits =>
      Function.update (decodeTail (fun p => bits p.succ)) e (storedHost (bits 0)))

theorem storedAssignment_eq_decoder {n m : ℕ} {J : Type*} :
    ∀ (l : List (JointFlagSampling.OriginalEdge n))
      (bits : JointFlagSampling.JointFlags n J m l),
      storedAssignment l bits = JointFlagSampling.decodeAssignment l bits := by
  intro l
  induction l with
  | nil => intro bits; rfl
  | cons e es ih =>
    intro bits
    change Function.update (storedAssignment es (fun p => bits p.succ)) e
        (storedHost (bits 0)) =
      Function.update (JointFlagSampling.decodeAssignment es (fun p => bits p.succ)) e
        (JointFlagSampling.decodeHost (bits 0))
    rw [ih, storedHost_eq_decodeHost]

/-- Tail first, head last: repeated candidate keys keep the HEAD occurrence. -/
theorem storedAssignment_head {n m : ℕ} {J : Type*}
    (e : JointFlagSampling.OriginalEdge n) (es : List (JointFlagSampling.OriginalEdge n))
    (bits : JointFlagSampling.JointFlags n J m (e::es)) :
    storedAssignment (e::es) bits e = storedHost (bits 0) := by
  change Function.update (storedAssignment es (fun p => bits p.succ)) e
    (storedHost (bits 0)) e = storedHost (bits 0)
  simp only [Function.update_self]

/-- Event transport under the GIVEN ideal product law, with no generator claim.
P may be the accepted canonical actual-output failure event; its caller's
graph/forest/weight hypotheses are retained when that event is instantiated. -/
theorem supplied_assignment_event_probability {J : Type*} [Fintype J] [DecidableEq J]
    (n f m : ℕ) (hf : 0 < f) (l : List (JointFlagSampling.OriginalEdge n))
    (P : SampledGreedy.Assignment (Fin n) J m → Prop) :
    (JointFlagSampling.jointSourceLaw (J:=J) n f m hf l).prob
      (fun bits => P (storedAssignment l bits)) =
      (SampledGreedy.executionLaw (V:=Fin n) (J:=J) f hf m l).prob P := by
  simpa only [storedAssignment_eq_decoder] using
    JointFlagSampling.decoded_assignment_probability (J:=J) n f m hf l P

end LightEFTSpanners.PaidJointBridge
