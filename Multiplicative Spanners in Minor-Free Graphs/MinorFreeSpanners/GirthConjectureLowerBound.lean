import MinorFreeSpanners.CoreExtraction
import MinorFreeSpanners.CoreParameters

/-! The actual sparse-spanner lower-bound family, conditional only on the
paper's explicitly stated Erdos girth conjecture. The target graphs and all
minor/girth/rounding properties are constructed, rather than assumed. -/
namespace MinorFreeSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable

/-- The standard fixed-k girth conjecture, with its asymptotic constant and
threshold made explicit. Only k≥1 is used below. -/
def ErdosGirthConjecture (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ v : ℕ, N ≤ v →
    ∃ G : SimpleGraph (Fin v), GirthAbove G (2*k) ∧
      c*(v:ℝ)^(1+1/(k:ℝ)) ≤ G.edgeFinset.card

/-- A real finite n-vertex graph forcing an explicit edge lower bound for
every spanner. This uses sparsity and makes no disconnected-MST claim. -/
def SparseLowerWitness (n k h : ℕ) (lower : ℝ) : Prop :=
  ∃ (X : Type) (inst : Fintype X),
    letI := inst
    ∃ G : SimpleGraph X, Fintype.card X = n ∧ CliqueMinorFree G h ∧ GirthAbove G (2*k) ∧
      ∀ H : SimpleGraph X, LightSpanners.IsSpanner G H (fun _ => 1) (2*k-1) →
        lower ≤ H.edgeFinset.card

/-- For every positive k, the girth conjecture yields the source's sharp
h-exponent lower bound for every sufficiently large h and every sufficiently
large n. The bounded h≥3 case and connected lightness construction are separate. -/
theorem girth_conjecture_sparse_lower_bound (k : ℕ) (hk : 1 ≤ k)
    (hconj : ErdosGirthConjecture k) :
    ∃ c : ℝ, 0 < c ∧ ∃ H : ℕ, ∀ h : ℕ, H ≤ h →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        SparseLowerWitness n k h (c*(n:ℝ)*(h:ℝ)^(2/((k:ℝ)+1))) := by
  classical
  obtain ⟨c,hc,N,hfamily⟩ := hconj
  let a := min c (1/8)
  have ha : 0 < a := lt_min hc (by norm_num)
  have hac : a ≤ c := min_le_left _ _
  have ha8 : a ≤ 1/8 := min_le_right _ _
  refine ⟨a/8,by positivity,max 3 (max N ⌈2/a⌉₊),?_⟩
  intro h hh
  have hh3 : 3 ≤ h := (le_max_left _ _).trans hh
  have hNh : N ≤ h := (le_max_left _ _).trans ((le_max_right _ _).trans hh)
  have hlarge : 2/a ≤ (h:ℝ) :=
    (Nat.le_ceil (2/a)).trans (by exact_mod_cast
      ((le_max_right N ⌈2/a⌉₊).trans ((le_max_right 3 _).trans hh)))
  let β := 2*(k:ℝ)/(k+1)
  let v := ⌈(h:ℝ)^β⌉₊
  let m := ⌊a*(h:ℝ)^2⌋₊
  obtain ⟨hv,hNv,hvupper,hmlo,hmupper,hmminor⟩ :=
    core_parameter_bounds k h N c a hk hh3 hNh ha hac ha8 hlarge
  change 0 < v at hv
  change N ≤ v at hNv
  change (v:ℝ) ≤ 2*(h:ℝ)^β at hvupper
  change a/2*(h:ℝ)^2 ≤ m at hmlo
  change (m:ℝ) ≤ c*(v:ℝ)^(((k:ℝ)+1)/k) at hmupper
  change m < h.choose 2 at hmminor
  obtain ⟨G,hg,hsize⟩ := hfamily v hNv
  have hexp : 1+1/(k:ℝ) = ((k:ℝ)+1)/k := by
    have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    field_simp
  rw [hexp] at hsize
  have hmG : m ≤ G.edgeFinset.card := by exact_mod_cast hmupper.trans hsize
  obtain ⟨C,hCG,hCm,hCg⟩ := exists_edge_trim G m (2*k) hmG hg
  have hdensity := core_density_bound k h v m a (by omega) hv ha.le hvupper hmlo
  refine ⟨v,?_⟩
  intro n hn
  let X := (Fin (n/Fintype.card (Fin v)) × Fin v) ⊕ Fin (n%Fintype.card (Fin v))
  let F := exactSizeGraph C n
  have hcore := exact_size_core_lower_bound C n k h (by simpa using hv)
    (by simpa using hn) (by omega) (by simpa only [hCm] using hmminor) hCg
  refine ⟨X,inferInstance,F,?_,hcore.1,hcore.2.1,?_⟩
  · simpa only [X,Fintype.card_fin] using (exactSizeGraph_card (V := Fin v) n)
  · intro J hJ
    obtain ⟨_,hj⟩ := hcore.2.2 J hJ
    have hjR : (n:ℝ)*m ≤ 2*(v:ℝ)*J.edgeFinset.card := by
      simpa only [hCm,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using
        (show ((n*C.edgeFinset.card:ℕ):ℝ) ≤ (2*Fintype.card (Fin v)*J.edgeFinset.card:ℕ) by exact_mod_cast hj)
    have hvR : (0:ℝ) < v := by exact_mod_cast hv
    have hmd : (m:ℝ)/(2*v)*(n:ℝ) ≤ J.edgeFinset.card := by
      calc
        _ = ((n:ℝ)*m)/(2*v) := by ring
        _ ≤ _ := (div_le_iff₀ (by positivity : (0:ℝ) < 2*v)).mpr (by nlinarith [hjR])
    have hb := mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg n)
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hb.trans hmd

end MinorFreeSpanners
