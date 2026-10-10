import GreedyShortcuts.ChainUnion
import Mathlib.Data.Nat.Log

/-! A concrete median recursion on an ordered path. All edges are strictly
forward, and a depth-d network on m vertices uses at most m*d edges. -/
namespace GreedyShortcuts.PathMedian
open Finset

def shift (a : ℕ) (E : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  E.image (fun e => (a+e.1,a+e.2))

def pivot (m : ℕ) : Finset (ℕ × ℕ) :=
  ((range (m/2)).image (fun i => (i,m/2))) ∪
    ((range (m-(m/2+1))).image (fun j => (m/2,m/2+1+j)))

def edges : ℕ → ℕ → Finset (ℕ × ℕ)
  | 0,_ => ∅
  | d+1,m => (pivot m ∪ edges d (m/2)) ∪
      shift (m/2+1) (edges d (m-(m/2+1)))

theorem shift_card (a : ℕ) (E : Finset (ℕ × ℕ)) : (shift a E).card≤E.card :=
  Finset.card_image_le

theorem pivot_card (m : ℕ) : (pivot m).card≤m := by
  have h := Finset.card_union_le
    ((range (m/2)).image (fun i => (i,m/2)))
    ((range (m-(m/2+1))).image (fun j => (m/2,m/2+1+j)))
  have hl : ((range (m/2)).image (fun i => (i,m/2))).card≤m/2 := by
    simpa only [Finset.card_range] using
      (Finset.card_image_le (s:=range (m/2)) (f:=fun i => (i,m/2)))
  have hr : ((range (m-(m/2+1))).image (fun j => (m/2,m/2+1+j))).card≤m-(m/2+1) := by
    simpa only [Finset.card_range] using
      (Finset.card_image_le (s:=range (m-(m/2+1))) (f:=fun j => (m/2,m/2+1+j)))
  change (pivot m).card≤_ at h
  omega

theorem edges_card (d m : ℕ) : (edges d m).card≤m*d := by
  induction d generalizing m with
  | zero => simp [edges]
  | succ d ih =>
    have h1 := Finset.card_union_le (pivot m) (edges d (m/2))
    have h2 := Finset.card_union_le (pivot m ∪ edges d (m/2))
      (shift (m/2+1) (edges d (m-(m/2+1))))
    have hs := shift_card (m/2+1) (edges d (m-(m/2+1)))
    have hl := ih (m/2)
    have hr := ih (m-(m/2+1))
    have hp := pivot_card m
    have hsum : m/2+(m-(m/2+1))≤m := by omega
    have hm := Nat.mul_le_mul_right d hsum
    change ((pivot m ∪ edges d (m/2)) ∪ shift (m/2+1) (edges d (m-(m/2+1)))).card≤_
    nlinarith

theorem pivot_forward {m : ℕ} {e : ℕ × ℕ} (he : e∈pivot m) :
    e.1<e.2 ∧ e.2<m := by
  rcases Finset.mem_union.mp he with hl | hr
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
    have hi' := Finset.mem_range.mp hi
    dsimp only
    omega
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hr
    have hj' := Finset.mem_range.mp hj
    dsimp only
    omega

theorem edges_forward (d m : ℕ) {e : ℕ × ℕ} (he : e∈edges d m) :
    e.1<e.2 ∧ e.2<m := by
  induction d generalizing m e with
  | zero => simp [edges] at he
  | succ d ih =>
    rcases Finset.mem_union.mp he with hleft | hright
    · rcases Finset.mem_union.mp hleft with hp | hl
      · exact pivot_forward hp
      · have hh := ih (m/2) hl
        exact ⟨hh.1,by omega⟩
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hright
      have hh := ih (m-(m/2+1)) hq
      dsimp only
      omega

/-- Two monotone legs, allowing a zero-length leg at the chosen pivot. -/
theorem two_legs (d m i j : ℕ) (hsize : m≤2^d) (hij : i≤j) (hj : j<m) :
    ∃ z,i≤z ∧ z≤j ∧ (i=z ∨ (i,z)∈edges d m) ∧
      (z=j ∨ (z,j)∈edges d m) := by
  induction d generalizing m i j with
  | zero =>
    have he : i=j := by simp only [pow_zero] at hsize;omega
    exact ⟨i,le_rfl,hij,Or.inl rfl,Or.inl he⟩
  | succ d ih =>
    have hpow : m≤2^d*2 := by simpa only [pow_succ] using hsize
    have hl : m/2≤2^d := by omega
    have hr : m-(m/2+1)≤2^d := by omega
    by_cases hjl : j<m/2
    · obtain ⟨z,hiz,hzj,hizE,hzjE⟩ := ih (m/2) i j hl hij hjl
      refine ⟨z,hiz,hzj,?_,?_⟩
      · exact hizE.imp_right (fun h => Finset.mem_union_left _ (Finset.mem_union_right _ h))
      · exact hzjE.imp_right (fun h => Finset.mem_union_left _ (Finset.mem_union_right _ h))
    · by_cases hir : m/2 < i
      · let a := m/2+1
        obtain ⟨z,hiz,hzj,hizE,hzjE⟩ := ih (m-a) (i-a) (j-a) hr (by omega) (by omega)
        have hi : a+(i-a)=i := by dsimp [a];omega
        have hj' : a+(j-a)=j := by dsimp [a];omega
        have lift : ∀ x y,(x,y)∈edges d (m-a) → (a+x,a+y)∈edges (d+1) m := by
          intro x y hxy
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x,y),hxy,rfl⟩)
        refine ⟨a+z,by omega,by omega,?_,?_⟩
        · rcases hizE with he | he
          · left;omega
          · right;simpa only [hi] using lift (i-a) z he
        · rcases hzjE with he | he
          · left;omega
          · right;simpa only [hj'] using lift z (j-a) he
      · refine ⟨m/2,by omega,by omega,?_,?_⟩
        · by_cases he : i=m/2
          · exact Or.inl he
          · right
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),rfl⟩
        · by_cases he : m/2=j
          · exact Or.inl he
          · right
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            apply Finset.mem_union_right
            refine Finset.mem_image.mpr ⟨j-(m/2+1),Finset.mem_range.mpr (by omega),?_⟩
            apply Prod.ext
            · rfl
            · dsimp only;omega

end GreedyShortcuts.PathMedian
