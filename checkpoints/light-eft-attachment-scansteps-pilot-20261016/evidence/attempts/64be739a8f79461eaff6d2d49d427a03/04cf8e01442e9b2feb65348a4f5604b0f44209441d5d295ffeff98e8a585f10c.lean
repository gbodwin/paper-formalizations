import LightEFTSpanners.EvenTightUncrossing

namespace LightEFTSpanners.EvenSplitting
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

/-- Every chosen original incident identity has a different partner for
which every set containing both ends has at least two units of cut slack.
Parity is what turns the obstruction into a tight set; no splitting theorem
or preselected partner is assumed. -/
theorem exists_admissible_partner (ends : I → V) (p : Finset V → ℤ)
    (hcover : ∀ S,p S≤mass ends S) (hsym : ∀ S,p Sᶜ=p S)
    (hskew : SkewSupermodular p) (heven : ∀ S,Even (mass ends S-p S))
    (hcard : 2≤Fintype.card I) (i : I) :
    ∃ j : I,j≠i ∧ ∀ S,ends i∈S → ends j∈S → p S+2≤mass ends S := by
  classical
  have hslack (S : Finset V) (hnt : p S≠mass ends S) : p S+2≤mass ends S := by
    obtain ⟨z,hz⟩ := heven S
    have hc := hcover S
    omega
  by_cases hex : ∃ S,ends i∈S ∧ p S=mass ends S
  · obtain ⟨A,hiA,htA,hmax⟩ := exists_largest_tight ends p hcover hskew i hex
    obtain ⟨j,hjA⟩ := exists_outside_tight ends p hcover hsym htA i hiA
    refine ⟨j,?_,?_⟩
    · intro hji
      subst j
      exact hjA hiA
    · intro S hiS hjS
      apply hslack S
      intro htS
      exact hjA (hmax S hiS htS hjS)
  · have : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨j,hji⟩ := exists_ne i
    refine ⟨j,hji,?_⟩
    intro S hiS _
    apply hslack S
    intro htS
    exact hex ⟨S,hiS,htS⟩
end LightEFTSpanners.EvenSplitting
