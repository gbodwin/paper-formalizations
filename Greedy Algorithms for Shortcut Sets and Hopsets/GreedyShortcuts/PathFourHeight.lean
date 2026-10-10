import GreedyShortcuts.PathFourConstruction

/-! An exact natural iterated-log height defined by finite power towers.
The uniform ambient-size witness needs no real logarithm or small-n convention. -/
namespace GreedyShortcuts.PathFour
open Finset DirectedPaths ChainUnion

theorem tower_lower (d : ℕ) : d+2 ≤ tower d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hg := Nat.lt_two_pow_self (n:=tower d)
    change d+1+2 ≤ 2^(tower d)
    omega

theorem exists_height (m : ℕ) : ∃ d,m ≤ tower d :=
  ⟨m,(show m ≤ m+2 by omega).trans (tower_lower m)⟩

noncomputable def height (m : ℕ) : ℕ := Nat.find (exists_height m)

theorem height_spec (m : ℕ) : m ≤ tower (height m) := Nat.find_spec (exists_height m)

theorem height_min {m d : ℕ} (hm : m ≤ tower d) : height m ≤ d :=
  Nat.find_min' (exists_height m) hm

theorem height_zero {m : ℕ} (hm : m ≤ 2) : height m=0 := by
  have hh := height_min (show m ≤ tower 0 from hm)
  omega


/-- The tower-defined height obeys the exact ceiling-log iteration, so its
finite coefficient is an iterated logarithm rather than an unnamed oracle. -/
theorem height_clog {m : ℕ} (hm : 2 < m) :
    height m=height (Nat.clog 2 m)+1 := by
  have hupper : height m ≤ height (Nat.clog 2 m)+1 := by
    apply height_min
    change m ≤ 2^(tower (height (Nat.clog 2 m)))
    exact (Nat.clog_le_iff_le_pow (by decide)).mp (height_spec (Nat.clog 2 m))
  have hpos : 0 < height m := by
    by_contra hh
    have he : height m=0 := by omega
    have hs := height_spec m
    rw [he] at hs
    change m ≤ 2 at hs
    omega
  have he : height m=(height m-1)+1 := by omega
  have hspec := height_spec m
  rw [he] at hspec
  have hlog : Nat.clog 2 m ≤ tower (height m-1) :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr hspec
  have hlower := height_min hlog
  omega

/-- One finite tower height for the ambient size supplies every shorter path.
The coefficient is explicit, with empty and singleton domains included. -/
noncomputable def ambientWitness (N m : ℕ) (hm : m ≤ N) : PathWitness m (6*height N+1) :=
  towerWitness (height N) m (hm.trans (height_spec N))

theorem supershortcut_union {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] {G : V → V → Prop} (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support)) :
    ∃ H : Finset (V × V),H ⊆ candidates G ∧
      H.card ≤ (6*height (Fintype.card V)+1)*Fintype.card V ∧
      ∀ c (i j : Fin (C c).length),i ≤ j →
        hopDist (augment G H) ((C c).node i) ((C c).node j) ≤ 4 := by
  apply ChainUnion.supershortcut_union C hdisj (6*height (Fintype.card V)+1)
  intro m hm
  exact ⟨ambientWitness _ m hm⟩

end GreedyShortcuts.PathFour
