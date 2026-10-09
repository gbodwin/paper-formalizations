import DirectedFlowCutGap.RawNonnegativeRational
import Mathlib.Data.List.NodupEquivFin

/-!
# Retained enumeration of a Boolean removal mask

The only membership test executed by the filter is one retained Boolean-array
read. Subtype certificates are erased. The list, its random-access label vector
and the exact bijection are kept separate so the latter remains proof-side.
-/

namespace DirectedFlowCutGap.RetainedSurvivorEnumeration

abbrev Survivor {m : ℕ} (removed : Vector Bool m) := {i : Fin m // removed[i.val] = false}

def scan {m : ℕ} (removed : Vector Bool m) : List (Fin m) → List (Survivor removed) × ℕ
  | [] => ([],1)
  | v::vs =>
    let r := scan removed vs
    if h : removed[v.val] = false then (⟨v,h⟩::r.1,r.2+7) else (r.1,r.2+7)

theorem scan_mem {m : ℕ} (removed : Vector Bool m) (vs : List (Fin m))
    (i : Survivor removed) : i∈(scan removed vs).1 ↔ i.val∈vs := by
  induction vs with
  | nil => simp [scan]
  | cons v vs ih =>
    by_cases h : removed[v.val] = false
    · simp [scan,h,ih,Subtype.ext_iff]
    · have hi : i.val≠v := by
        intro he
        exact h (he ▸ i.property)
      simp [scan,h,ih,hi]

theorem scan_nodup {m : ℕ} (removed : Vector Bool m) (vs : List (Fin m))
    (h : vs.Nodup) : (scan removed vs).1.Nodup := by
  induction vs with
  | nil => simp [scan]
  | cons v vs ih =>
    obtain ⟨hv,ht⟩ := List.nodup_cons.mp h
    by_cases hb : removed[v.val] = false
    · simpa [scan,hb,scan_mem] using And.intro hv (ih ht)
    · simpa [scan,hb] using ih ht

theorem scan_length_le {m : ℕ} (removed : Vector Bool m) (vs : List (Fin m)) :
    (scan removed vs).1.length ≤ vs.length := by
  induction vs with
  | nil => simp [scan]
  | cons v vs ih =>
    unfold scan
    split <;> simp only [List.length_cons] <;> omega

theorem scan_work {m : ℕ} (removed : Vector Bool m) (vs : List (Fin m)) :
    (scan removed vs).2 = 7*vs.length+1 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    unfold scan
    split <;> simp only [List.length_cons] <;> omega

def labels {m : ℕ} (removed : Vector Bool m) : List (Survivor removed) :=
  (scan removed (List.finRange m)).1

@[simp] theorem mem_labels {m : ℕ} (removed : Vector Bool m) (i : Survivor removed) :
    i∈labels removed := (scan_mem removed _ i).mpr (List.mem_finRange i.val)

theorem labels_nodup {m : ℕ} (removed : Vector Bool m) : (labels removed).Nodup :=
  scan_nodup removed _ (List.nodup_finRange m)

theorem labels_length_le {m : ℕ} (removed : Vector Bool m) : (labels removed).length ≤ m := by
  simpa [labels] using scan_length_le removed (List.finRange m)

def vector {m : ℕ} (removed : Vector Bool m) : Vector (Survivor removed) (labels removed).length :=
  ⟨(labels removed).toArray,by simp⟩

@[simp] theorem vector_get {m : ℕ} (removed : Vector Bool m) (i : Fin (labels removed).length) :
    (vector removed)[i.val] = (labels removed).get i := by simp [vector]

theorem vector_bijective {m : ℕ} (removed : Vector Bool m) :
    Function.Bijective (fun i : Fin (labels removed).length => (vector removed)[i.val]) := by
  simp only [vector_get]
  exact ⟨List.nodup_iff_injective_get.mp (labels_nodup removed),
    fun a => List.mem_iff_get.mp (mem_labels removed a)⟩

noncomputable def equiv {m : ℕ} (removed : Vector Bool m) :
    Fin (labels removed).length ≃ Survivor removed :=
  Equiv.ofBijective (fun i => (vector removed)[i.val]) (vector_bijective removed)

end DirectedFlowCutGap.RetainedSurvivorEnumeration
