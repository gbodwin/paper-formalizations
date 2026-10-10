import GreedyShortcuts.KernelLift

/-! Exact finite balancing of the actual small-kernel algorithm. A kernel
with at most b^3 vertices needs only a near-linear number of selected edges
at inner target b; its external hopbound scales as the expansion factor times b.
The improved kernel certificate itself remains an explicit cited input. -/
namespace GreedyShortcuts.KernelBalance

open DirectedPaths DAGProgress

 theorem blockLength_cube {m b : ℕ} (hb : 0 < b) (hm : m ≤ b^3) :
    blockLength m b 8 ≤ 131072*m+1 := by
  unfold blockLength
  apply max_le
  · have hd := Nat.div_le_self (512*m) 8
    omega
  · have hmul := Nat.mul_le_mul_left (131072*m) hm
    have hnum : 16384*8*m^2 ≤ (131072*m)*b^3 := by nlinarith
    have hd := Nat.div_le_div_right (c:=b^3) hnum
    have he : ((131072*m)*b^3)/(b^3) = 131072*m :=
      Nat.mul_div_cancel _ (by positivity)
    rw [he] at hd
    omega

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The actual SCC reduction plus DAG greedy is near-linear on a kernel of
at most b^3 vertices. No shortcut-size or progress hypothesis is supplied. -/
theorem scc_card {G : W → W → Prop} (b : ℕ) (hb : 8 ≤ b)
    (hW : Fintype.card W ≤ b^3) :
    (SCCGreedy.output G b (by omega)).card ≤
      (Nat.log 2 ((Fintype.card W)^3)+1)*(131074*Fintype.card W+1) := by
  let q := Fintype.card (SCCQuotient.Component G)
  let m := Fintype.card W
  let k := Nat.log 2 (m^3)+1
  have hqm : q ≤ m := SCCQuotient.component_card G
  have hqb : q ≤ b^3 := hqm.trans hW
  have hkq : Nat.log 2 (q^3)+1 ≤ k := Nat.add_le_add_right
    (Nat.log_mono_right (Nat.pow_le_pow_left hqm 3)) 1
  have hdag := DAGProgress.output_card_bound (SCCQuotient.acyclic G) b 8 hb (by omega)
  have hsmall := blockLength_cube (by omega : 0 < b) hqb
  have hblock : blockLength q b 8 ≤ 131072*m+1 := hsmall.trans (by omega)
  have hcard := SCCGreedy.output_card_le G b (by omega)
  change (SCCGreedy.output G b _).card ≤ k*(131074*m+1)
  have hh : (GraphGreedy.output (SCCQuotient.graph G) b (by omega)).card ≤
      k*(131072*m+1) := hdag.trans (Nat.mul_le_mul hkq hblock)
  have hk : 1 ≤ k := by dsimp [k];omega
  have hm' := Nat.mul_le_mul_right (2*m) hk
  change (SCCGreedy.output G b _).card ≤ 2*m+_ at hcard
  nlinarith

variable {G : V → V → Prop} {R L : ℕ} (A : KernelLift.Kernel G W R L)

theorem output_card (b : ℕ) (hb : 8 ≤ b) (hW : Fintype.card W ≤ b^3) :
    (A.output b (by omega)).card ≤
      (Nat.log 2 ((Fintype.card W)^3)+1)*(131074*Fintype.card W+1) :=
  (A.output_card b (by omega)).trans (scc_card b hb hW)

/-- The external hop cost is explicit and includes both access walks and
all SCC expansion costs. -/
theorem output_hop (b : ℕ) (hb : 1 ≤ b) (hL : 1 ≤ L) (hR : R ≤ L)
    {s t : V} (hr : Reachable G s t) :
    hopDist (augment G (A.output b hb)) s t ≤ 7*L*b := by
  have hh := A.output_hop_bound b hb hL hr
  have hm := Nat.mul_le_mul_left (4*L) hb
  nlinarith

/-- A division-free source-shaped tradeoff: for scale Z bounding L*b^3,
the actual output has hopbound times b^2 at most 7Z. -/
theorem output_hop_scaled (b : ℕ) (hb : 1 ≤ b) (hL : 1 ≤ L) (hR : R ≤ L)
    (Z : ℕ) (hscale : L*b^3 ≤ Z) {s t : V} (hr : Reachable G s t) :
    hopDist (augment G (A.output b hb)) s t * b^2 ≤ 7*Z := by
  calc
    _ ≤ (7*L*b)*b^2 := Nat.mul_le_mul_right _ (output_hop A b hb hL hR hr)
    _ = 7*(L*b^3) := by ring
    _ ≤ 7*Z := Nat.mul_le_mul_left _ hscale

end GreedyShortcuts.KernelBalance
