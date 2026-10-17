import LightEFTSpanners.NativeMaximalCountercase

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Move unused residual edges to a fresh last color while retaining the
selected residual tree as the next genuine earlier class. -/
noncomputable def extendTreeColor {k : ℕ} (color : E → Fin (k+1)) (F : Set E)
    (e : E) : Fin (k+2) :=
  if color e=Fin.last k ∧ e∉F then Fin.last (k+1) else (color e).castSucc

theorem extendTreeColor_old_class {k : ℕ} (color : E → Fin (k+1)) (F : Set E)
    (c : Fin k) :
    {e | extendTreeColor color F e=c.castSucc.castSucc}={e | color e=c.castSucc} := by
  ext e
  by_cases h : color e=Fin.last k ∧ e∉F
  · have hne : color e≠c.castSucc := by rw [h.1]; exact (Fin.castSucc_ne_last c).symm
    simp only [Set.mem_ofPred_eq,extendTreeColor,ite_eq_left h,hne,
      (Fin.castSucc_ne_last c.castSucc).symm]
  · simp only [Set.mem_ofPred_eq,extendTreeColor,ite_eq_right h,Fin.castSucc_inj]

theorem extendTreeColor_new_class {k : ℕ} (color : E → Fin (k+1)) (F : Set E)
    (hF : ∀ e∈F,color e=Fin.last k) :
    {e | extendTreeColor color F e=(Fin.last k).castSucc}=F := by
  ext e
  by_cases he : e∈F
  · have hc := hF e he
    simp only [Set.mem_ofPred_eq,extendTreeColor,hc,he,not_true_eq_false,and_false,ite_false]
  · by_cases hc : color e=Fin.last k
    · simp only [Set.mem_ofPred_eq,extendTreeColor,hc,he,not_false_eq_true,and_self,ite_true,
        (Fin.castSucc_ne_last (Fin.last k)).symm]
    · simp only [Set.mem_ofPred_eq,extendTreeColor,hc,false_and,ite_false,Fin.castSucc_inj,he]

/-- This literal recoloring extends the actual earlier-tree family by one.
The supplied tree is a subset of the old residual color, not an assumed
packing of one more tree. -/
theorem extendTreeColor_earlier_trees (G : Graph V E) {k : ℕ}
    (color : E → Fin (k+1)) (ht : earlierColorTrees G color) (F : Set E)
    (hF : ∀ e∈F,color e=Fin.last k)
    (hbridge : ∀ e∈(G.restrict F).edgeSet,(G.restrict F).IsBridge e)
    (hconn : (G.restrict F).toSimpleGraph.Connected) :
    earlierColorTrees G (extendTreeColor color F) := by
  intro c
  obtain ⟨c,rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last c
  · have hEq := congrArg G.restrict (extendTreeColor_old_class color F c)
    exact (congrArg (fun K : Graph V E =>
      (∀ e∈K.edgeSet,K.IsBridge e) ∧ K.toSimpleGraph.Connected) hEq).mpr (ht c)
  · have hEq := congrArg G.restrict (extendTreeColor_new_class color F hF)
    exact (congrArg (fun K : Graph V E =>
      (∀ e∈K.edgeSet,K.IsBridge e) ∧ K.toSimpleGraph.Connected) hEq).mpr ⟨hbridge,hconn⟩
end LightEFTSpanners.MultigraphCuts
