import LinearDistancePreservers.ObstacleWalks
import LinearDistancePreservers.WeightedNativeForcing

/-! Integer separation of outer and inner weights in the obstacle product.
This is the small-epsilon construction after multiplying all weights by a
common positive integer. All competitors are native undirected walks. -/
namespace LinearDistancePreservers.ObstacleProduct
open SimpleGraph
open scoped NNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

variable {A B C U J : Type*} {k : ℕ} (D : Data A B C U J k)

def natCost {V : Type*} {G : SimpleGraph V} (w : V → V → ℕ)
    {s t : V} (p : G.Walk s t) : ℕ := (p.darts.map fun d => w d.fst d.snd).sum

@[simp] theorem natCost_nil {V : Type*} {G : SimpleGraph V} (w : V → V → ℕ) (s : V) :
    natCost w (.nil : G.Walk s s) = 0 := rfl

@[simp] theorem natCost_cons {V : Type*} {G : SimpleGraph V} (w : V → V → ℕ)
    {s u t : V} (h : G.Adj s u) (p : G.Walk u t) :
    natCost w (.cons h p) = w s u + natCost w p := rfl

theorem natCost_concat {V : Type*} {G : SimpleGraph V} (w : V → V → ℕ)
    {s u t : V} (p : G.Walk s u) (h : G.Adj u t) :
    natCost w (p.concat h) = natCost w p + w u t := by
  simp [natCost,Walk.darts_concat,List.concat_eq_append]

def primary (wl : A → B → ℕ) (wr : B → C → ℕ) :
    Vertex A B C U → Vertex A B C U → ℕ
  | .inl a, .inr (.inl (b,_)) => wl a b
  | .inr (.inl (b,_)), .inl a => wl a b
  | .inr (.inl (b,_)), .inr (.inr c) => wr b c
  | .inr (.inr c), .inr (.inl (b,_)) => wr b c
  | _, _ => 0

def secondary (wi : U → U → ℕ) : Vertex A B C U → Vertex A B C U → ℕ
  | .inr (.inl (_,u)), .inr (.inl (_,v)) => wi u v
  | _, _ => 0

theorem left_embed_adj (b : B) (j : J) :
    (graph D).Adj (.inl (D.left b j)) ((embed D b) (D.inner j 0)) := left_adj D b j

theorem right_embed_adj (b : B) (j : J) :
    (graph D).Adj ((embed D b) (D.inner j (Fin.last k))) (.inr (.inr (D.right b j))) :=
  right_adj D b j

def through (b : B) (j₁ j₂ : J)
    (w : (innerGraph D).Walk (D.inner j₁ 0) (D.inner j₂ (Fin.last k))) :
    (graph D).Walk (.inl (D.left b j₁)) (.inr (.inr (D.right b j₂))) :=
  .cons (left_embed_adj D b j₁) ((w.map (embed D b)).concat (right_embed_adj D b j₂))

theorem through_support (b : B) (j₁ j₂ : J)
    (w : (innerGraph D).Walk (D.inner j₁ 0) (D.inner j₂ (Fin.last k))) :
    (through D b j₁ j₂ w).support = .inl (D.left b j₁) ::
      ((w.support.map fun u => (.inr (.inl (b,u)) : Vertex A B C U)) ++
        [.inr (.inr (D.right b j₂))]) := by
  simp [through,Walk.support_cons,Walk.support_concat,Walk.support_map,embed]

theorem through_innerRoute (b : B) (j : J) :
    through D b j j (innerRoute D j) = fullWalk D b j := by
  apply Walk.ext_support
  rw [through_support]
  simp only [fullWalk,Walk.support_cons,Walk.support_concat,innerWalk_support]

theorem primary_map (wl : A → B → ℕ) (wr : B → C → ℕ) (b : B)
    {u v : U} (w : (innerGraph D).Walk u v) :
    natCost (primary wl wr) (w.map (embed D b)) = 0 := by
  induction w with
  | nil => rfl
  | cons h w ih => simpa [Walk.map_cons,embed,primary] using ih

theorem secondary_map (wi : U → U → ℕ) (b : B)
    {u v : U} (w : (innerGraph D).Walk u v) :
    natCost (secondary wi) (w.map (embed D b)) = natCost wi w := by
  induction w with
  | nil => rfl
  | cons h w ih => simpa [Walk.map_cons,embed,secondary] using ih

theorem primary_through (wl : A → B → ℕ) (wr : B → C → ℕ) (b : B) (j₁ j₂ : J)
    (w : (innerGraph D).Walk (D.inner j₁ 0) (D.inner j₂ (Fin.last k))) :
    natCost (primary wl wr) (through D b j₁ j₂ w) =
      wl (D.left b j₁) b + wr b (D.right b j₂) := by
  rw [through,natCost_cons,natCost_concat,primary_map]
  simp [primary,embed]

theorem secondary_through (wi : U → U → ℕ) (b : B) (j₁ j₂ : J)
    (w : (innerGraph D).Walk (D.inner j₁ 0) (D.inner j₂ (Fin.last k))) :
    natCost (secondary wi) (through D b j₁ j₂ w) = natCost wi w := by
  rw [through,natCost_cons,natCost_concat,secondary_map]
  simp [secondary,embed]

theorem primary_ge_connectors (wl : A → B → ℕ) (wr : B → C → ℕ) (base : ℕ)
    (hl : ∀ a b, base ≤ wl a b) (hr : ∀ b c, base ≤ wr b c)
    {s t : Vertex A B C U} (p : (graph D).Walk s t) :
    base * connectorCount D p ≤ natCost (primary wl wr) p := by
  have hstep : ∀ s t, (graph D).Adj s t → base * connector s t ≤ primary wl wr s t := by
    rintro s t ⟨e,h | h⟩ <;>
      have hs := congrArg Prod.fst h <;> have ht := congrArg Prod.snd h <;>
      dsimp at hs ht
    · rw [← hs,← ht]
      rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;> simp [arc,connector,primary,hl,hr]
    · rw [← ht,← hs]
      rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;> simp [arc,connector,primary,hl,hr]
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [connectorCount_cons,natCost_cons,Nat.mul_add]
    exact Nat.add_le_add (hstep _ _ h) ih

theorem natCost_separate {V : Type*} {G : SimpleGraph V} (w₀ w₁ : V → V → ℕ)
    (M : ℕ) {s t : V} (p : G.Walk s t) :
    natCost (fun u v => M * w₀ u v + w₁ u v) p = M * natCost w₀ p + natCost w₁ p := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [natCost_cons,ih]; ring

theorem natCost_copy {V : Type*} {G : SimpleGraph V} (w : V → V → ℕ)
    {s t s' t' : V} (p : G.Walk s t) (hs : s = s') (ht : t = t') :
    natCost w (p.copy hs ht) = natCost w p := by
  simp [natCost,Walk.darts_copy]

/-- Quantitative hypotheses about the two input path systems. The outer
condition compares actual sums of the two connector weights, and permits
different input and output port labels for the competitor. -/
def OuterOptimal (wl : A → B → ℕ) (wr : B → C → ℕ) : Prop :=
  ∀ b j b' j₁ j₂, D.left b' j₁ = D.left b j → D.right b' j₂ = D.right b j →
    wl (D.left b j) b + wr b (D.right b j) ≤
      wl (D.left b' j₁) b' + wr b' (D.right b' j₂) ∧
    (wl (D.left b' j₁) b' + wr b' (D.right b' j₂) =
      wl (D.left b j) b + wr b (D.right b j) → b' = b ∧ j₁ = j ∧ j₂ = j)

def InnerOptimal (wi : U → U → ℕ) : Prop :=
  ∀ j (w : (innerGraph D).Walk (D.inner j 0) (D.inner j (Fin.last k))),
    natCost wi (innerRoute D j) ≤ natCost wi w ∧
    (natCost wi w = natCost wi (innerRoute D j) → w = innerRoute D j)

/-- A concrete integer scaling proves weighted product optimality and
uniqueness for every native walk, including non-simple competitors. -/
theorem separated_optimal (wl : A → B → ℕ) (wr : B → C → ℕ) (wi : U → U → ℕ)
    (base M : ℕ) (hl : ∀ a b, base ≤ wl a b) (hr : ∀ b c, base ≤ wr b c)
    (hsmall : ∀ b j, wl (D.left b j) b + wr b (D.right b j) < 3*base)
    (hout : OuterOptimal D wl wr) (hin : InnerOptimal D wi)
    (hM : ∀ j, natCost wi (innerRoute D j) < M)
    (b : B) (j : J)
    (q : (graph D).Walk (.inl (D.left b j)) (.inr (.inr (D.right b j)))) :
    let weight := fun u v => M * primary wl wr u v + secondary wi u v
    natCost weight (fullWalk D b j) ≤ natCost weight q ∧
    (natCost weight q = natCost weight (fullWalk D b j) → q = fullWalk D b j) := by
  dsimp only
  have hp : natCost (primary wl wr) (fullWalk D b j) =
      wl (D.left b j) b + wr b (D.right b j) := by
    rw [← through_innerRoute,primary_through]
  have hs : natCost (secondary wi) (fullWalk D b j) = natCost wi (innerRoute D j) := by
    rw [← through_innerRoute,secondary_through]
  rw [natCost_separate,natCost_separate,hp,hs]
  by_cases hbig : wl (D.left b j) b + wr b (D.right b j) < natCost (primary wl wr) q
  · have hstrict :
        M * (wl (D.left b j) b + wr b (D.right b j)) + natCost wi (innerRoute D j) <
          M * natCost (primary wl wr) q + natCost (secondary wi) q := by
      have hm := hM j
      have hmprod := Nat.mul_le_mul_left M (Nat.succ_le_of_lt hbig)
      nlinarith
    exact ⟨hstrict.le,fun he => False.elim (hstrict.ne he.symm)⟩
  · have hcnt : connectorCount D q ≤ 2 := by
      have hb := primary_ge_connectors D wl wr base hl hr q
      have hsm := hsmall b j
      have hbase : 0 < base := by omega
      by_contra hc
      have hh : 3 ≤ connectorCount D q := by omega
      have hm := Nat.mul_le_mul_left base hh
      nlinarith
    obtain ⟨b',j₁,j₂,hle,hrg,w,hw⟩ := factor_left_right D q hcnt
    have hqt : q = (through D b' j₁ j₂ w).copy
        (congrArg Sum.inl hle) (congrArg (fun c => Sum.inr (Sum.inr c)) hrg) := by
      apply Walk.ext_support
      rw [Walk.support_copy,through_support,hw,hle,hrg]
    have hpc : natCost (primary wl wr) q =
        wl (D.left b' j₁) b' + wr b' (D.right b' j₂) := by
      rw [hqt,natCost_copy,primary_through]
    obtain ⟨hlo,heq⟩ := hout b j b' j₁ j₂ hle hrg
    have he : wl (D.left b' j₁) b' + wr b' (D.right b' j₂) =
        wl (D.left b j) b + wr b (D.right b j) := by omega
    obtain ⟨hb,hj₁,hj₂⟩ := heq he
    subst b' j₁ j₂
    have hqthrough : q = through D b j j w := by simpa using hqt
    have hsc : natCost (secondary wi) q = natCost wi w := by
      rw [hqthrough,secondary_through]
    rw [hpc,hsc]
    obtain ⟨himin,hiunique⟩ := hin j w
    refine ⟨Nat.add_le_add_left himin _,?_⟩
    intro htotal
    have hwinner := hiunique (Nat.add_left_cancel htotal)
    rw [hqthrough,hwinner,through_innerRoute]

theorem realCost_nat {V : Type*} {G : SimpleGraph V} (w : V → V → ℕ)
    {s t : V} (p : G.Walk s t) :
    WeightedNativeForcing.realCost (fun u v => (w u v : ℝ≥0)) p = (natCost w p : ℝ) := by
  unfold WeightedNativeForcing.realCost natCost
  simp only [NNReal.coe_natCast, Nat.cast_list_sum, List.map_map]
  rfl

end LinearDistancePreservers.ObstacleProduct
