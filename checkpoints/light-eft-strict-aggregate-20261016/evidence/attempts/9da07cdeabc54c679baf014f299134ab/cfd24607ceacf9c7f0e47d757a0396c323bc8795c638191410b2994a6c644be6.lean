import LightEFTSpanners.RationalDistanceValues
import LightSpanners.Distance
import Mathlib.Data.Vector.Basic

namespace LightEFTSpanners.RationalDistance
open SimpleGraph
variable {n : ℕ}

def cost (w : Sym2 (Fin n) → ℚ) {G : SimpleGraph (Fin n)} {u v : Fin n}
    (p : G.Walk u v) : ℚ := (p.edges.map w).sum
@[simp] theorem cost_nil (w : Sym2 (Fin n) → ℚ) (G : SimpleGraph (Fin n)) (u : Fin n) :
    cost w (.nil : G.Walk u u)=0 := by simp [cost]
@[simp] theorem cost_cons (w : Sym2 (Fin n) → ℚ) {G : SimpleGraph (Fin n)}
    {u v z : Fin n} (h : G.Adj u v) (p : G.Walk v z) :
    cost w (.cons h p)=w s(u,v)+cost w p := by simp [cost]

def candidate (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) (u v : Fin n) : Option ℚ :=
  if G.Adj u v then (d[v.val]).map (w s(u,v)+·) else none

/-- A materialized vector is produced at each round. The previous vector is
shared by all rows; this is not an exponentially expanding function recursion. -/
def step (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) : Vector (Option ℚ) n :=
  Vector.ofFn fun u => ((List.finRange n).map (candidate G w d u)).foldr best d[u.val]

def table (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (target : Fin n) : ℕ → Vector (Option ℚ) n
  | 0 => Vector.ofFn fun u => if u=target then some 0 else none
  | k+1 => step G w (table G w target k)

 theorem below_candidate (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) (u v : Fin n) (b : ℚ) :
    Below (candidate G w d u v) b ↔
      G.Adj u v ∧ ∃ c, Below d[v.val] c ∧ w s(u,v)+c≤b := by
  by_cases h : G.Adj u v
  · simp only [candidate,h,ite_true,below_map_add,true_and]
    constructor
    · rintro ⟨c,hc,hb⟩;exact ⟨c,⟨c,hc,le_rfl⟩,hb⟩
    · rintro ⟨c,⟨x,hx,hxc⟩,hb⟩;exact ⟨x,hx,by linarith⟩
  · simp [candidate,h]

 theorem below_step (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) (u : Fin n) (b : ℚ) :
    Below (step G w d)[u.val] b ↔ Below d[u.val] b ∨
      ∃ v, G.Adj u v ∧ ∃ c, Below d[v.val] c ∧ w s(u,v)+c≤b := by
  simp only [step,Vector.getElem_ofFn]
  rw [below_fold]
  simp only [List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro (h | ⟨x,⟨v,rfl⟩,hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v,(below_candidate G w d u v b).mp hx⟩
  · rintro (h | ⟨v,hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨candidate G w d u v,⟨v,rfl⟩,(below_candidate G w d u v b).mpr hv⟩

 theorem below_table_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (target : Fin n) (k : ℕ) (u : Fin n) (b : ℚ) :
    Below (table G w target k)[u.val] b ↔
      ∃ p : G.Walk u target, p.length≤k ∧ cost w p≤b := by
  induction k generalizing u b with
  | zero =>
    simp only [table,Vector.getElem_ofFn]
    constructor
    · intro h
      split_ifs at h with he
      · have he : u=target := he
        subst u;exact ⟨.nil,by simp,(below_some 0 b).mp h⟩
      · exact (below_none b h).elim
    · rintro ⟨p,hp,hb⟩
      cases p with
      | nil => simpa using hb
      | cons h p => simp at hp
  | succ k ih =>
    rw [table,below_step]
    constructor
    · rintro (h|⟨v,hv,c,hc,hb⟩)
      · obtain ⟨p,hp,hb⟩ := (ih u b).mp h
        exact ⟨p,by omega,hb⟩
      · obtain ⟨p,hp,hc⟩ := (ih v c).mp hc
        exact ⟨.cons hv p,by simpa using Nat.succ_le_succ hp,
          by simp only [cost_cons]; linarith⟩
    · rintro ⟨p,hp,hb⟩
      cases p with
      | nil => exact Or.inl ((ih target b).mpr ⟨.nil,by simp,hb⟩)
      | @cons u v z hv p =>
        exact Or.inr ⟨v,hv,cost w p,(ih v _).mpr ⟨p,by simpa using hp,le_rfl⟩,
          by simpa using hb⟩
end LightEFTSpanners.RationalDistance
