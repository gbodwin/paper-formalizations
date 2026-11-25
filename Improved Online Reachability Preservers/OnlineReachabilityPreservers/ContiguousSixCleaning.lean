import OnlineReachabilityPreservers.LocalFrozenCleaning

/-! Contiguous regularization with unique intersections through bridge size six. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "ListBefore" => SourceAudit.BeforeIn

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]

variable [Fintype V]

/-- With unique intersections, the two regularization splits preserve full
exclusion through size six. They also preserve half exclusion through size
six when the input excludes full bridges through size four. The cleaned
witness meets both budgets and all four frozen caps. -/
theorem regularization_list_frozen_unique_six {half : Bool} (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (free : localOrderAdmissible half 6 paths)
    (fourForHalf : half = true → BridgeFree (ListBefore paths) 4)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (dense : Fintype.card V ≤ ∑ i, (paths i).length) (long : Fintype.card I ≤ ∑ i, (paths i).length) :
    let n := Fintype.card V
    let p := Fintype.card I
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half 6 clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let after := listRegularizedPaths paths D L
  obtain ⟨hD,trimD,_⟩ := four_average_width hn dense
  obtain ⟨hL,trimL,_⟩ := four_average_width hp long
  obtain ⟨rawV,rawI⟩ := regularization_list_counts paths simple hD hL
  have vCap : 3*Fintype.card (ListVertexBlockIndex paths D) ≤ 4*n := by
    change 3*(M/D) ≤ n at trimD
    change Fintype.card (ListVertexBlockIndex paths D) ≤ n+M/D at rawV
    omega
  have iCap : 3*Fintype.card (ListBlockIndex (splitListVertices paths D) L) ≤ 4*p := by
    change 3*(M/L) ≤ p at trimL
    change Fintype.card (ListBlockIndex (splitListVertices paths D) L) ≤ p+M/L at rawI
    omega
  have four : BridgeFree (ListBefore paths) 4 := by
    cases mode : half
    · have full : BridgeFree (ListBefore paths) 6 := by simpa [mode,localOrderAdmissible] using free
      exact fun _ hk => full (hk.trans (by decide))
    · exact fourForHalf mode
  obtain ⟨mass,width,degree⟩ := regularization_list_mass_caps paths simple D L hD hL
  exact regularization_list_frozen_after_caps_with_room after (listRegularizedPaths_simple paths simple D L)
    (regularizedSix_bridge_free simple (fun {_ _ _ _} => unique) four free D L)
    hn hp dense long vCap iCap width degree mass

end OnlineReachabilityPreservers
