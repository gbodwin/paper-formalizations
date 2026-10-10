import LightEFTSpanners.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic
import Mathlib.Analysis.Real.Sqrt

namespace LightEFTSpanners.GenericBlowupFailure
open SimpleGraph Finset
variable {V I : Type*}

def lift (J : SimpleGraph V) : SimpleGraph (V×I) where
  Adj u v := J.Adj u.1 v.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u => J.loopless.irrefl u.1⟩

/-- A leaf in the base certificate with another original neighbor witnesses
failure whenever the cloud size is within the fault budget. The failed edges
are actual input edges, and their number is proved rather than assumed. -/
theorem leaf_obstruction [Fintype I] [Nonempty I]
    {G T : SimpleGraph V} {a b c : V} {q : ℕ}
    (hTG : T ≤ G) (hab : T.Adj a b) (hleaf : ∀ z,T.Adj a z → z=b)
    (hac : G.Adj a c) (hcb : c≠b) (hq : Fintype.card I≤q) :
    ¬ IsFTConnectivityPreserver (lift (I:=I) G) (lift (I:=I) T) q := by
  classical
  let i : I := Classical.choice inferInstance
  let u : V×I := (a,i)
  let v : V×I := (c,i)
  let F : Finset (Sym2 (V×I)) := univ.image (fun j => s(u,(b,j)))
  have hF : F.card≤q := (card_image_le.trans (by simpa using hq))
  have hinput : ∀ e∈F,e∈(lift (I:=I) G).edgeSet := by
    intro e he
    obtain ⟨j,_,rfl⟩ := mem_image.mp he
    exact (mem_edgeSet _).mpr (hTG hab)
  have hsurvive : (afterFaults (lift (I:=I) G) F).Adj u v := by
    apply deleteEdges_adj.mpr
    refine ⟨hac,?_⟩
    intro he
    obtain ⟨j,_,hej⟩ := mem_image.mp he
    rcases Sym2.eq_iff.mp hej with heq | heq
    · have hh : b=c := congrArg Prod.fst heq.2
      exact hcb hh.symm
    · have hh : a=c := congrArg Prod.fst heq.1
      exact hac.ne hh
  have hiso : (afterFaults (lift (I:=I) T) F).IsIsolated u := by
    intro z hz
    obtain ⟨hzT,hzF⟩ := deleteEdges_adj.mp hz
    have hzb : z.1=b := hleaf z.1 hzT
    apply hzF
    refine mem_image.mpr ⟨z.2,mem_univ _,?_⟩
    congr 1
    exact Prod.ext hzb.symm rfl
  intro h
  obtain ⟨p⟩ := (h.2 F hF u v).mp hsurvive.reachable
  have hn := p.nil_of_isIsolated_of_mem_support hiso p.start_mem_support
  exact hac.ne (congrArg Prod.fst hn.eq)

/-- For complete base graphs on at least three vertices, every spanning tree's
cloud blowup fails once the fault budget reaches the cloud size. This holds
for every MST choice and every positive weighting of that complete base graph. -/
theorem complete_tree_blowup_failure [Fintype I] [Nonempty I]
    (n q : ℕ) (hn : 3≤n) (hq : Fintype.card I≤q)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    ¬ IsFTConnectivityPreserver (lift (I:=I) (⊤ : SimpleGraph (Fin n))) (lift (I:=I) T) q := by
  classical
  letI : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp (by simpa using (show 1<n by omega))
  obtain ⟨a,ha⟩ := hT.exists_vert_degree_one_of_nontrivial
  obtain ⟨b,hab,hunique⟩ := degree_eq_one_iff_existsUnique_adj.mp ha
  have hcard : ({a,b} : Finset (Fin n)).card < (univ : Finset (Fin n)).card := by
    have hp : ({a,b} : Finset (Fin n)).card≤2 := by
      by_cases hab : a=b <;> simp [hab]
    simp only [card_univ,Fintype.card_fin]
    omega
  obtain ⟨c,_,hc⟩ := exists_mem_notMem_of_card_lt_card hcard
  have hc' : c≠a ∧ c≠b := by simpa using hc
  exact leaf_obstruction le_top hab (fun z hz => hunique z hz)
    (by simpa using hc'.1.symm) hc'.2 hq
theorem source_cloud_size_le (q : ℕ) (hq : 2≤q) :
    Nat.ceil (Real.sqrt ((q:ℝ)+1)) ≤ q := by
  apply Nat.ceil_le.mpr
  apply Real.sqrt_le_iff.mpr
  have hqR : (2:ℝ)≤q := by exact_mod_cast hq
  constructor
  · positivity
  · nlinarith [sq_nonneg ((q:ℝ)-2)]

/-- The paper's exact rounded cloud size is within the fault budget for every
integer q≥2, so the failure applies to that proposed certificate without any
rounding approximation. -/
theorem source_parameter_tree_failure (n q : ℕ) (hn : 3≤n) (hq : 2≤q)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    ¬ IsFTConnectivityPreserver
      (lift (I:=Fin (Nat.ceil (Real.sqrt ((q:ℝ)+1)))) (⊤ : SimpleGraph (Fin n)))
      (lift (I:=Fin (Nat.ceil (Real.sqrt ((q:ℝ)+1)))) T) q := by
  have hp : 0 < Nat.ceil (Real.sqrt ((q:ℝ)+1)) := Nat.ceil_pos.mpr (by positivity)
  letI : Nonempty (Fin (Nat.ceil (Real.sqrt ((q:ℝ)+1)))) := ⟨⟨0,hp⟩⟩
  exact complete_tree_blowup_failure n q hn (by simpa using source_cloud_size_le q hq) T hT
end LightEFTSpanners.GenericBlowupFailure
