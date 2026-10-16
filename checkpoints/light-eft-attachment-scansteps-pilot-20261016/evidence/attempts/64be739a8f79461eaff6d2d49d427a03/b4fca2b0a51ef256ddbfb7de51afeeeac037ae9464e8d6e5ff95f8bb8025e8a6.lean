import LightEFTSpanners.NativeEulerianStep

namespace LightEFTSpanners.EvenSplitting
open Finset MultigraphCuts
universe u v
variable {V : Type u}

/-- A finite trace of literal native splits. The type of edge identities may
change because each step injects old IDs and allocates one fresh ID. -/
inductive CenterSplitTrace : {E F : Type v} → Graph (Option V) E → Graph (Option V) F → Prop
  | refl {E : Type v} (G : Graph (Option V) E) : CenterSplitTrace G G
  | step {E F : Type v} (G : Graph (Option V) E) (i j : CenterInc G) (hij : i≠j)
      {H : Graph (Option V) F} (tail : CenterSplitTrace (centerSplit G i j) H) :
      CenterSplitTrace G H

variable [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The exact output certificate for finite center elimination. The graph
and finite edge type are constructed, while the trace records each legal
original-ID split. No forest packing or path lifting is claimed here. -/
def CenterEliminationResult {E F : Type v} [Fintype E] (G : Graph (Option V) E)
    (P : V → V → Prop) (k : ℕ) (hF : Fintype F) (H : Graph (Option V) F) : Prop :=
  letI := hF
  CenterSplitTrace G H ∧ Fintype.card (CenterInc H)=0 ∧
    RequiredConnectivity H P k ∧ (∀ x,Even (nativeDegree H x)) ∧ H.vertexSet=G.vertexSet

/-- Complete native center elimination by strong induction on the actual
number of nonloop incident identities. Each recursive step is the proved
even-degree split and decreases that number by exactly two. -/
theorem exists_native_center_elimination {E : Type v} [Fintype E]
    (G : Graph (Option V) E) (P : V → V → Prop) (k : ℕ)
    (hdeg : ∀ x,Even (nativeDegree G x)) (hconn : RequiredConnectivity G P k) :
    ∃ (F : Type v) (hF : Fintype F) (H : Graph (Option V) F),
      CenterEliminationResult G P k hF H := by
  classical
  let Q : ℕ → Prop := fun n => ∀ (E : Type v) (hE : Fintype E) (G : Graph (Option V) E),
    letI := hE
    Fintype.card (CenterInc G)=n → (∀ x,Even (nativeDegree G x)) →
      RequiredConnectivity G P k →
      ∃ (F : Type v) (hF : Fintype F) (H : Graph (Option V) F),
        CenterEliminationResult G P k hF H
  have hQ : ∀ n,Q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E hE G hn hd hc
      let := hE
      by_cases hz : Fintype.card (CenterInc G)=0
      · exact ⟨E,hE,G,CenterSplitTrace.refl G,hz,hc,hd,rfl⟩
      · have hpos : 0<Fintype.card (CenterInc G) := Nat.pos_of_ne_zero hz
        obtain ⟨i⟩ := Fintype.card_pos_iff.mp hpos
        obtain ⟨j,hji,hc',hd',hv,hcount⟩ := exists_native_eulerian_step G P k hc hd i
        let H₁ := centerSplit G i j
        have hlt : Fintype.card (CenterInc H₁)<n := by
          change Fintype.card (CenterInc (centerSplit G i j))<n
          omega
        obtain ⟨F,hF,H,hH⟩ := ih _ hlt (Option E) inferInstance H₁ rfl hd' hc'
        let := hF
        obtain ⟨htrace,hzero,hconnH,hdegH,hvertH⟩ := hH
        exact ⟨F,hF,H,CenterSplitTrace.step G i j (Ne.symm hji) htrace,
          hzero,hconnH,hdegH,hvertH.trans hv⟩
  exact hQ _ E inferInstance G rfl hdeg hconn
end LightEFTSpanners.EvenSplitting
