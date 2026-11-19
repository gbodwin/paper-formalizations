import OnlineReachabilityPreservers.BalancedRegularization
import OnlineReachabilityPreservers.LocalRegularization

/-! Induced path lists retain their local orders when vertices and indices are restricted. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V]

local notation "ListBefore" => SourceAudit.BeforeIn

/-- Keep the vertices in `A`, in the original order. -/
def restrictListPath (path : List V) (A : Finset V) : List A :=
  let kept := path.filter fun x => decide (x ∈ A)
  kept.attach.map fun x => ⟨x.val, by
    have inside : x.val ∈ path.filter (fun y => decide (y ∈ A)) := x.property
    exact of_decide_eq_true ((List.mem_filter (p := fun y : V => decide (y ∈ A))).mp inside).2⟩

@[simp]
theorem restrictListPath_map (path : List V) (A : Finset V) :
    (restrictListPath path A).map Subtype.val = path.filter (fun x => decide (x ∈ A)) := by
  unfold restrictListPath
  rw [List.map_map]
  exact List.attach_map_subtype_val _

@[simp]
theorem mem_restrictListPath {path : List V} {A : Finset V} {v : A} :
    v ∈ restrictListPath path A ↔ v.val ∈ path := by
  constructor
  · intro h
    have filtered : v.val ∈ (restrictListPath path A).map Subtype.val := List.mem_map_of_mem h
    rw [restrictListPath_map] at filtered
    exact (List.mem_filter.mp filtered).1
  · intro h
    have filtered : v.val ∈ (restrictListPath path A).map Subtype.val := by
      rw [restrictListPath_map]
      exact List.mem_filter.mpr ⟨h, decide_eq_true v.property⟩
    obtain ⟨u, inside, equal⟩ := List.mem_map.mp filtered
    exact (Subtype.ext equal : u = v) ▸ inside

theorem restrictListPath_nodup {path : List V} (simple : path.Nodup) (A : Finset V) :
    (restrictListPath path A).Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [restrictListPath_map]
  exact List.filter_sublist.nodup simple

theorem restrictListPath_length {path : List V} (simple : path.Nodup) (A : Finset V) :
    (restrictListPath path A).length = (path.toFinset ∩ A).card := by
  let kept := path.filter (fun x => decide (x ∈ A))
  have members : kept.toFinset = path.toFinset ∩ A := by
    ext x
    simp [kept]
  have same : (restrictListPath path A).length = kept.length := by
    rw [← show (restrictListPath path A).map Subtype.val = kept from restrictListPath_map path A]
    simp only [List.length_map]
  have nodup : kept.Nodup := List.filter_sublist.nodup simple
  exact same.trans ((List.toFinset_card_of_nodup nodup).symm.trans (congrArg Finset.card members))

/-- Keep the designated paths and the designated vertices on each path. -/
def restrictListPaths (paths : I → List V) (A : Finset V) (B : Finset I) (j : B) : List A :=
  restrictListPath (paths j.val) A

theorem restrictListPaths_step {paths : I → List V} {A : Finset V} {B : Finset I}
    {i : B} {x y : A} (simple : (paths i.val).Nodup) (step : ListBefore (restrictListPaths paths A B) i x y) :
    ListBefore paths i.val x.val y.val := by
  let inside (j : B) := (paths j.val).filter (fun x => decide (x ∈ A))
  have project : (fun j : B => (restrictListPaths paths A B j).map Subtype.val) = inside :=
    funext (fun j => restrictListPath_map (paths j.val) A)
  have nodup : ((restrictListPaths paths A B i).map Subtype.val).Nodup := by
    rw [show (restrictListPaths paths A B i).map Subtype.val = inside i from congrFun project i]
    exact List.filter_sublist.nodup simple
  have old := listBefore_map Subtype.val nodup step
  rw [project] at old
  exact listBefore_of_sublist (paths := fun j : B => paths j.val) (cut := inside)
    simple List.filter_sublist old

theorem restrictListPaths_fullFree {paths : I → List V} {k : ℕ} (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (ListBefore paths) k) (A : Finset V) (B : Finset I) :
    BridgeFree (ListBefore (restrictListPaths paths A B)) k := by
  intro s hs
  exact ⟨fun b => (free hs).false ((b.mapVertices Subtype.val Subtype.val_injective
    (fun i _ _ h => restrictListPaths_step (simple i.val) h)).mapPaths Subtype.val Subtype.val_injective
      (fun _ _ _ h => h))⟩

theorem restrictListPaths_halfFree [LinearOrder I] {paths : I → List V} {k : ℕ} (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) k) (A : Finset V) (B : Finset I) :
    HalfBridgeFree (ListBefore (restrictListPaths paths A B)) k := by
  intro s hs b earlier
  exact free hs ((b.mapVertices Subtype.val Subtype.val_injective
    (fun i _ _ h => restrictListPaths_step (simple i.val) h)).mapPaths Subtype.val Subtype.val_injective
      (fun _ _ _ h => h)) earlier

theorem restrictListPaths_unique {paths : I → List V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (A : Finset V) (B : Finset I) {i j : B} {x y : A} (different : i ≠ j)
    (xi : x ∈ restrictListPaths paths A B i) (xj : x ∈ restrictListPaths paths A B j)
    (yi : y ∈ restrictListPaths paths A B i) (yj : y ∈ restrictListPaths paths A B j) : x = y :=
  Subtype.ext (unique (fun equal => different (Subtype.ext equal))
    (mem_restrictListPath.mp xi) (mem_restrictListPath.mp xj)
    (mem_restrictListPath.mp yi) (mem_restrictListPath.mp yj))

theorem restrictListPaths_toFinset (paths : I → List V) (A : Finset V) (B : Finset I) (j : B) :
    (restrictListPaths paths A B j).toFinset = rectanglePaths (fun i => (paths i).toFinset) A B j := by
  ext x
  simp [restrictListPaths, rectanglePaths]

end OnlineReachabilityPreservers
