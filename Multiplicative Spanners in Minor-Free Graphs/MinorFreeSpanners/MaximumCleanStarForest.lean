import MinorFreeSpanners.GeneralStarForest
import MinorFreeSpanners.MinorHostTransport

/-! Finite selection of an actual maximum clean general-star family.
Admissibility refers to the literal full quotient's edge count. The empty
family is constructed, so no existence or maximality oracle is supplied. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact small-vertex and complete quotient-loss requirements. -/
def SmallCleanStarForest (G : SimpleGraph V) (k : ℕ) (D lossPerVertex : ℝ)
    (C : Finset V) (L : V → Finset V) : Prop :=
  IsGeneralStarForest G k C L ∧
  (∀ x ∈ C.biUnion (fun c => insert c (L c)), (G.degree x:ℝ) ≤ D) ∧
  (G.edgeFinset.card:ℝ) ≤ (fullStarContraction G C L).edgeFinset.card+
    lossPerVertex*(k*C.card:ℕ)

/-- The unchanged host embeds into the literal empty-family quotient. -/
theorem empty_full_star_quotient_edges (G : SimpleGraph V) :
    G.edgeFinset.card ≤ (fullStarContraction G ∅ (fun _ => ∅)).edgeFinset.card := by
  classical
  let f : G →g fullStarContraction G ∅ (fun _ => ∅) := {
    toFun := fun x => .inr ⟨x,by simp [starResidual]⟩
    map_rel' := by
      intro x y hxy
      refine ⟨?_,x,by simp [fullStarBranch],y,by simp [fullStarBranch],hxy⟩
      intro he
      exact hxy.ne (congrArg Subtype.val (Sum.inr.inj he)) }
  exact hom_edge_count_le f (fun _ _ he => congrArg Subtype.val (Sum.inr.inj he))

theorem empty_small_clean_star_forest (G : SimpleGraph V) (k : ℕ) (D q : ℝ) :
    SmallCleanStarForest G k D q ∅ (fun _ => ∅) := by
  refine ⟨empty_general_star_forest G k,by simp,?_⟩
  simpa only [Finset.card_empty,Nat.mul_zero,Nat.cast_zero,mul_zero,add_zero]
    using Nat.cast_le.mpr (empty_full_star_quotient_edges G)

/-- Finiteness constructs the maximum among literal admissible families.
No positive coverage or residual-neighborhood conclusion is inferred here. -/
theorem exists_maximum_small_clean_star_forest (G : SimpleGraph V)
    (k : ℕ) (D q : ℝ) :
    ∃ C : Finset V, ∃ L : V → Finset V, SmallCleanStarForest G k D q C L ∧
      ∀ C' L', SmallCleanStarForest G k D q C' L' → C'.card ≤ C.card := by
  classical
  let candidates := (Finset.univ : Finset (Finset V × (V → Finset V))).filter
    (fun P => SmallCleanStarForest G k D q P.1 P.2)
  have h0 : (∅,fun _ => ∅) ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,empty_small_clean_star_forest G k D q⟩
  obtain ⟨⟨C,L⟩,hCL,hmax⟩ := Finset.exists_max_image candidates
    (fun P : Finset V × (V → Finset V) => P.1.card) ⟨_,h0⟩
  refine ⟨C,L,(Finset.mem_filter.mp hCL).2,?_⟩
  intro C' L' h'
  exact hmax (C',L') (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h'⟩)

end MinorFreeSpanners
