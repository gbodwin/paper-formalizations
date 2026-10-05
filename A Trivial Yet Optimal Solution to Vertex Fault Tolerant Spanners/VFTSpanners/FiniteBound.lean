import VFTSpanners.Sampling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 800000

namespace VFTSpanners

/-- The exact ratio between the two- and three-vertex survival counts. -/
theorem choose_three_two (n r : ℕ) (hn : 3 ≤ n) (hr : 3 ≤ r) :
    (n - 2) * Nat.choose (n - 3) (r - 3) =
      Nat.choose (n - 2) (r - 2) * (r - 2) := by
  have h := Nat.add_one_mul_choose_eq (n - 3) (r - 3)
  have en : n - 3 + 1 = n - 2 := by omega
  have er : r - 3 + 1 = r - 2 := by omega
  simpa only [en, er] using h

/-- Division-free edge survival probability. -/
theorem choose_two_ratio (n r : ℕ) (hn : 2 ≤ n) (hr : 2 ≤ r) :
    n * (n - 1) * Nat.choose (n - 2) (r - 2) =
      Nat.choose n r * r * (r - 1) := by
  have h1 := Nat.add_one_mul_choose_eq (n - 1) (r - 1)
  have h2 := Nat.add_one_mul_choose_eq (n - 2) (r - 2)
  have en1 : n - 1 + 1 = n := by omega
  have er1 : r - 1 + 1 = r := by omega
  have en2 : n - 2 + 1 = n - 1 := by omega
  have er2 : r - 2 + 1 = r - 1 := by omega
  rw [en1, er1] at h1
  rw [en2, er2] at h2
  calc
    _ = n * ((n - 1) * Nat.choose (n - 2) (r - 2)) := by ring
    _ = n * (Nat.choose (n - 1) (r - 1) * (r - 1)) := by rw [h2]
    _ = (n * Nat.choose (n - 1) (r - 1)) * (r - 1) := by ring
    _ = _ := by rw [h1]

/-- Explicit finite constant underlying Lemma 4. We use `floor(n/(2f))`,
which removes all asymptotic and rounding qualifications. -/
theorem finite_sampling_arithmetic (n m b f q : ℕ) (hf : 1 ≤ f) (hn : 6*f ≤ n)
    (hb : b ≤ f*m)
    (hcount : m * Nat.choose (n-2) (n/(2*f)-2) ≤
      Nat.choose n (n/(2*f)) * q + b * Nat.choose (n-3) (n/(2*f)-3)) :
    m ≤ 32*f^2*q := by
  let r := n / (2*f)
  have hf0 : 0 < 2*f := by omega
  have hr : 3 ≤ r := (Nat.le_div_iff_mul_le hf0).mpr (by omega)
  have hrn : r ≤ n := Nat.div_le_self _ _
  have hn3 : 3 ≤ n := by omega
  have hn2eq : n = (n-2)+2 := by omega
  have hrmul : r*(2*f) ≤ n := Nat.div_mul_le_self _ _
  have hnlt : n < (r+1)*(2*f) := by simpa [r, Nat.mul_comm] using Nat.lt_mul_div_succ n hf0
  let A := Nat.choose (n-2) (r-2)
  let C := Nat.choose n r
  let D := Nat.choose (n-3) (r-3)
  have hA : 0 < A := Nat.choose_pos (by omega)
  have hC : 0 < C := Nat.choose_pos hrn
  have hratio : (n-2)*D = A*(r-2) := choose_three_two n r hn3 hr
  have h2 : 2*f*(r-2) ≤ n-2 := by
    have : r = (r-2)+2 := by omega
    nlinarith
  have hD : 2*f*D ≤ A := by
    have h := Nat.mul_le_mul_right A h2
    have he := congrArg (fun x => 2*f*x) hratio
    have hn2 : 0 < n-2 := by omega
    nlinarith
  have hc : m*A ≤ C*q+b*D := hcount
  have hbm : b*D ≤ f*m*D := Nat.mul_le_mul_right D hb
  have hmD := Nat.mul_le_mul_left m hD
  have half : m*A ≤ 2*C*q := by nlinarith
  have hprob : n*(n-1)*A = C*r*(r-1) := choose_two_ratio n r (by omega) (by omega)
  have hr1 : r = (r-1)+1 := by omega
  have hnr : n ≤ 4*f*r := by nlinarith
  have hfr : 3*f ≤ r*f := Nat.mul_le_mul_right f hr
  have hn1eq : n = (n-1)+1 := by omega
  have hnr1 : n-1 ≤ 4*f*(r-1) := by nlinarith
  have hnprod := Nat.mul_le_mul hnr hnr1
  have hscaled := Nat.mul_le_mul_left (n*(n-1)) half
  have heq := congrArg (fun x => m*x) hprob
  have hscaled' : m*(r*(r-1)) ≤ 2*n*(n-1)*q := by
    apply Nat.le_of_mul_le_mul_left (c := C) (by nlinarith) hC
  have hfinal := Nat.mul_le_mul_right (2*q) hnprod
  have hrr : 0 < r*(r-1) := Nat.mul_pos (by omega) (by omega)
  apply Nat.le_of_mul_le_mul_right (c := r*(r-1)) (by nlinarith) hrr

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Lemma 4, with explicit constants and an actual sampled graph. -/
theorem exists_high_girth_sample_finite (G : SimpleGraph V)
    (B : Finset (V × Sym2 V)) (k f : ℕ) (hf : 1 ≤ f)
    (hn : 6*f ≤ Fintype.card V) (hB : IsBlockingSet G k (B : Set (V × Sym2 V)))
    (hb : B.card ≤ f*G.edgeFinset.card) :
    ∃ S : Finset V, S.card = Fintype.card V / (2*f) ∧
      G.edgeFinset.card ≤ 32*f^2 *
        (prunedGraph G (S : Set V) (B : Set (V × Sym2 V))).edgeFinset.card ∧
      ∀ a : (S : Set V), ∀ p : (prunedGraph G (S : Set V)
        (B : Set (V × Sym2 V))).Walk a a, p.IsCycle → k < p.length := by
  have hf0 : 0 < 2*f := by omega
  obtain ⟨S, hS, hcount, hgirth⟩ := exists_dense_high_girth_sample G B k
    (Fintype.card V / (2*f)) ((Nat.le_div_iff_mul_le hf0).mpr (by omega))
    (Nat.div_le_self _ _) hB
  exact ⟨S, hS, finite_sampling_arithmetic _ _ _ _ _ hf hn hb hcount, hgirth⟩
end
end VFTSpanners
