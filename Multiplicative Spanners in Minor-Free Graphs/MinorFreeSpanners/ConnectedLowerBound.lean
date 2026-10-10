import MinorFreeSpanners.CompletionMinor
import MinorFreeSpanners.AllCliqueOrdersLowerBound
import LightSpanners.Weight

namespace MinorFreeSpanners
open SimpleGraph LightSpanners
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With unit weights every spanning tree has the same positive weight
when there are at least two vertices. -/
theorem unit_tree_weight {T : SimpleGraph V} (hT : T.IsTree) :
    totalWeight T (fun _ => 1) = (Fintype.card V : ℝ)-1 := by
  rw [totalWeight_eq_card_mul T _ 1 (by simp),mul_one]
  have hcard : (T.edgeFinset.card:ℝ)+1 = Fintype.card V := by
    exact_mod_cast hT.card_edgeFinset
  linarith

/-- Actual connected finite graphs have an actual unit-weight MST. -/
theorem unit_mst_exists {G : SimpleGraph V} (hG : G.Connected) :
    ∃ T : SimpleGraph V, IsMinimumSpanningTree G T (fun _ => 1) ∧
      totalWeight T (fun _ => 1) = (Fintype.card V : ℝ)-1 := by
  obtain ⟨T,hTG,hT⟩ := hG.exists_isTree_le
  refine ⟨T,⟨hTG,hT,?_⟩,unit_tree_weight hT⟩
  intro S hSG hS
  rw [unit_tree_weight hT,unit_tree_weight hS]

/-- The identity graph is a unit-weight spanner for every k≥1. -/
theorem unit_spanner_self (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k) :
    IsSpanner G G (fun _ => 1) (2*k-1) := by
  refine ⟨le_rfl,?_⟩
  intro u v p
  refine ⟨p,?_⟩
  have hw := walkWeight_nonneg (fun _ : Sym2 V => (1:ℝ)) (by simp) p
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- A connected, exact-size lower-bound graph with a genuine input MST;
both sparsity and lightness apply to every spanner of that graph. -/
def ConnectedLowerWitness (n k h : ℕ) (edgeLower lightLower : ℝ) : Prop := by
  classical
  exact ∃ (X : Type) (inst : Fintype X), letI := inst
    ∃ G T : SimpleGraph X, Fintype.card X = n ∧ G.Connected ∧ CliqueMinorFree G h ∧
      IsMinimumSpanningTree G T (fun _ => 1) ∧
      ∀ J : SimpleGraph X, IsSpanner G J (fun _ => 1) (2*k-1) →
        edgeLower ≤ J.edgeFinset.card ∧ lightLower ≤ lightness J T (fun _ => 1)

/-- Convert the genuine sparse witness on n−1 vertices to a connected
n-vertex graph by adding one hub and one bridge per actual component.
Both lower bounds lose at most a factor two; the MST is constructed. -/
theorem connected_lower_from_sparse (n k h : ℕ) (hk : 1 ≤ k) (hh : 3 ≤ h)
    (hn : 2 ≤ n) (a : ℝ) (ha : 0 ≤ a)
    (hw : SparseLowerWitness (n-1) k h (a*((n-1:ℕ):ℝ))) :
    ConnectedLowerWitness n k h (a/2*(n:ℝ)) (a/2) := by
  classical
  obtain ⟨X,inst,G,hcard,hminor,hgirth,hbound⟩ := hw
  letI := inst
  let F := rootedCompletion G
  have hconn : F.Connected := rootedCompletion.connected G
  have hFminor : CliqueMinorFree F h := rootedCompletion.minorFree G hminor hh
  have hFgirth : GirthAbove F (2*k) := rootedCompletion.girth G hgirth
  have hFcard : Fintype.card (Option X) = n := by simp only [Fintype.card_option,hcard]; omega
  obtain ⟨T,hT,hweight⟩ := unit_mst_exists hconn
  have hwt : totalWeight T (fun _ => 1) = ((n-1:ℕ):ℝ) := by
    rw [hFcard] at hweight
    rw [hweight,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have hmG := hbound G (unit_spanner_self G k hk)
  have hmF : G.edgeFinset.card ≤ F.edgeFinset.card :=
    (MinorModel.ofEmbedding G F ⟨some,Option.some_injective X⟩ (fun _ _ h => h)).edge_count_le
  have hm : a*((n-1:ℕ):ℝ) ≤ F.edgeFinset.card := hmG.trans (by exact_mod_cast hmF)
  refine ⟨Option X,inferInstance,F,T,hFcard,hconn,hFminor,hT,?_⟩
  intro J hJ
  have heq : J = F := high_girth_spanner_eq k hFgirth hJ
  subst J
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hsub : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  constructor
  · rw [hsub] at hm
    nlinarith
  · rw [lightness,hwt,totalWeight_eq_card_mul F _ 1 (by simp),mul_one]
    apply (le_div_iff₀ (by rw [hsub]; linarith : (0:ℝ) < (n-1:ℕ))).mpr
    nlinarith [mul_nonneg ha (Nat.cast_nonneg (n-1))]

/-- The full fixed-k conditional lower bound, simultaneously for sparsity
and genuine connected-graph lightness, with the corrected h≥3 domain. -/
theorem girth_conjecture_connected_lower_bound (k : ℕ) (hk : 1 ≤ k)
    (hconj : ErdosGirthConjecture k) :
    ∃ c : ℝ, 0 < c ∧ ∀ h : ℕ, 3 ≤ h →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ConnectedLowerWitness n k h (c*(n:ℝ)*(h:ℝ)^(2/((k:ℝ)+1)))
          (c*(h:ℝ)^(2/((k:ℝ)+1))) := by
  obtain ⟨c,hc,hfamily⟩ := girth_conjecture_sparse_lower_bound_all_h k hk hconj
  refine ⟨c/2,by positivity,?_⟩
  intro h hh
  obtain ⟨N,hN⟩ := hfamily h hh
  refine ⟨max 2 (N+1),?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hNn : N ≤ n-1 := by have := (le_max_right 2 (N+1)).trans hn; omega
  have hw := hN (n-1) hNn
  let a := c*(h:ℝ)^(2/((k:ℝ)+1))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hw' : SparseLowerWitness (n-1) k h (a*((n-1:ℕ):ℝ)) := by
    simpa only [a,mul_assoc,mul_comm,mul_left_comm] using hw
  have hout := connected_lower_from_sparse n k h hk hh hn2 a ha hw'
  convert hout using 1 <;> dsimp [a] <;> ring

end MinorFreeSpanners
