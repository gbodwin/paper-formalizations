import GreedyShortcuts.ChainCanonicalIncidenceWeights

/-! SOURCE ONLY, UNCOMPILED. Finite suffix-card distribution in an actual
injective natural order. No graph instance or desired rank identity is a
premise. The summatory function retains the exact native midpoint product. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset

def finiteSuffixCard {α : Type*} (s : Finset α) (p : α → ℕ) (v : α) : ℕ :=
  (s.filter (fun w => p v≤p w)).card

/-- For EVERY test weight f, remaining cardinalities of a finite set in
an injective order have the exact distribution 1,...,card(s). Induction
removes the actual least p-element; p-values need not be consecutive. -/
theorem finiteSuffixCard_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℕ)
    (hinj : ∀ v ∈ s,∀ w ∈ s,p v=p w → v=w) (f : ℕ → ℕ) :
    (∑ v ∈ s,f (finiteSuffixCard s p v))=∑ j ∈ Finset.range s.card,f (j+1) := by
  classical
  have main : ∀ n : ℕ,∀ t : Finset α,t.card=n →
      (∀ v ∈ t,∀ w ∈ t,p v=p w → v=w) →
      (∑ v ∈ t,f (finiteSuffixCard t p v))=∑ j ∈ Finset.range t.card,f (j+1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t htn huniq
      by_cases ht : t=∅
      · subst t
        simp
      · have hne : t.Nonempty := by
          by_contra hn
          apply ht
          ext v
          constructor
          · intro hv
            exact False.elim (hn ⟨v,hv⟩)
          · simp
        obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image t p hne
        let b := t \ {v}
        have hvb : v ∉ b := by simp [b]
        have hbt : b ⊆ t := Finset.sdiff_subset
        have hcard : b.card+1=t.card := by
          have hs : ({v} : Finset α) ⊆ t := by
            intro w hw
            simpa only [Finset.mem_singleton.mp hw] using hv
          have hc := Finset.card_sdiff_add_card_inter t {v}
          rw [Finset.inter_eq_right.mpr hs,Finset.card_singleton] at hc
          exact hc
        have hins : insert v b=t := by
          ext w
          simp only [Finset.mem_insert,b,Finset.mem_sdiff,Finset.mem_singleton]
          constructor
          · rintro (rfl|⟨hw,_hne⟩)
            · exact hv
            · exact hw
          · intro hw
            by_cases he : w=v
            · exact Or.inl he
            · exact Or.inr ⟨hw,he⟩
        have hbi : ∀ a ∈ b,∀ c ∈ b,p a=p c → a=c :=
          fun a ha c hc he => huniq a (hbt ha) c (hbt hc) he
        have hind := ih b.card (by omega : b.card<n) b rfl hbi
        have hvRank : finiteSuffixCard t p v=t.card := by
          unfold finiteSuffixCard
          rw [Finset.filter_eq_self.mpr hmin]
        have hother : ∀ w ∈ b,finiteSuffixCard t p w=finiteSuffixCard b p w := by
          intro w hw
          apply congrArg Finset.card
          ext a
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨ha,hwa⟩
            have hav : a≠v := by
              intro he
              have hsmall := hmin w (hbt hw)
              have heq : p w=p v := by rw [he] at hwa;omega
              have hwv := huniq w (hbt hw) v hv heq
              exact hvb (hwv ▸ hw)
            exact ⟨Finset.mem_sdiff.mpr ⟨ha,by simpa only [Finset.mem_singleton] using hav⟩,hwa⟩
          · rintro ⟨ha,hwa⟩
            exact ⟨hbt ha,hwa⟩
        calc
          (∑ w ∈ t,f (finiteSuffixCard t p w))=
              ∑ w ∈ insert v b,f (finiteSuffixCard t p w) := by rw [hins]
          _ =f (finiteSuffixCard t p v)+∑ w ∈ b,f (finiteSuffixCard t p w) :=
            Finset.sum_insert hvb
          _ =f t.card+∑ j ∈ Finset.range b.card,f (j+1) := by
            rw [hvRank]
            congr 1
            calc
              (∑ w ∈ b,f (finiteSuffixCard t p w))=
                  ∑ w ∈ b,f (finiteSuffixCard b p w) :=
                Finset.sum_congr rfl (fun w hw => congrArg f (hother w hw))
              _ =_ := hind
          _ =∑ j ∈ Finset.range t.card,f (j+1) := by
            rw [← hcard,Finset.sum_range_succ]
            omega
  exact main s.card s rfl hinj

/-- Exact natural summatory function; no unproved cubic or floor-square
coefficient is substituted for the accepted midpoint weight. -/
def canonicalMidpointSum (h : ℕ) : ℕ :=
  ∑ j ∈ Finset.range h,canonicalMidpointWeight (j+1)

theorem canonicalMidpointSum_zero : canonicalMidpointSum 0=0 := by
  simp [canonicalMidpointSum]

theorem canonicalMidpointSum_succ (h : ℕ) :
    canonicalMidpointSum (h+1)=canonicalMidpointSum h+canonicalMidpointWeight (h+1) := by
  unfold canonicalMidpointSum
  rw [Finset.sum_range_succ]

theorem canonicalMidpointSum_mono : Monotone canonicalMidpointSum := by
  intro a b hab
  unfold canonicalMidpointSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hab)
  · intro _j _hj _hnot
    exact Nat.zero_le _

end GreedyShortcuts.ChainDistance.Context
