import LightEFTSpanners.NativeGreedyTrace

namespace LightEFTSpanners.NativeWeighted.Walk
open Finset
open scoped NNReal
variable {V E : Type*} {G : Graph V E} {H F : Finset E}

@[simp] theorem edgeList_append {u v z : G.vertexSet} (p : Walk G H F u v)
    (q : Walk G H F v z) : (p.append q).edgeList = p.edgeList ++ q.edgeList := by
  induction p with
  | nil => rfl
  | cons e hl he hf p ih => simp [append,edgeList,ih]

theorem edgeList_selected {u v : G.vertexSet} (p : Walk G H F u v) :
    ∀ e ∈ p.edgeList, e ∈ H := by
  induction p with
  | nil => simp [edgeList]
  | cons d hl hd hf p ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hd
    · exact ih e he

/-- Change the selected set using actual traversed IDs, preserving all edge
occurrences and the exact weight. No global/path-restricted distance equality. -/
theorem transfer_selected {u v : G.vertexSet} (w : E → ℝ≥0)
    (p : Walk G H F u v) (J : Finset E) (h : ∀ e ∈ p.edgeList, e ∈ J) :
    ∃ r : Walk G J F u v, r.edgeList = p.edgeList ∧ r.weight w = p.weight w := by
  induction p with
  | nil u => exact ⟨.nil u,rfl,rfl⟩
  | cons e hl he hf p ih =>
    obtain ⟨r,hr,hw⟩ := ih (fun d hd => h d (List.mem_cons_of_mem e hd))
    refine ⟨.cons e hl (h e (by simp [edgeList])) hf r,?_,?_⟩
    · simp [edgeList,hr]
    · simp [weight,hw]

/-- Split at an occurrence of an original edge identity. -/
theorem split_edge {u v : G.vertexSet} (w : E → ℝ≥0) (p : Walk G H F u v)
    (e : E) (he : e ∈ p.edgeList) :
    ∃ x y : G.vertexSet, ∃ a : Walk G H F u x, ∃ b : Walk G H F y v,
      G.IsLink e x.val y.val ∧ p.edgeList = a.edgeList ++ e :: b.edgeList ∧
      p.weight w = a.weight w + w e + b.weight w := by
  induction p with
  | nil => simp [edgeList] at he
  | @cons u z v d hl hd hf p ih =>
    by_cases hde : d = e
    · subst d
      exact ⟨u,z,.nil u,p,hl,rfl,by simp [weight]⟩
    · have ht : e ∈ p.edgeList := (List.mem_cons.mp he).resolve_left (Ne.symm hde)
      obtain ⟨x,y,a,b,hab,heq,hw⟩ := ih ht
      refine ⟨x,y,.cons d hl hd hf a,b,hab,?_,?_⟩
      · simp [edgeList,heq]
      · simp [weight,hw,add_assoc]

/-- Rotate an edge-simple closed walk at e and remove that edge. This includes
a single loop (empty complement) and distinct parallel IDs (one-edge complement).
The endpoint order of the complementary walk is reversed, as it must be. -/
theorem cycle_complement [DecidableEq E] {u : G.vertexSet} (w : E → ℝ≥0)
    (p : Walk G H F u u) (hn : p.edgeList.Nodup) (e : E) (he : e ∈ p.edgeList) :
    ∃ x y : G.vertexSet, G.IsLink e x.val y.val ∧
      ∃ q : Walk G H F y x, q.edgeList.Nodup ∧
        (∀ d, d ∈ q.edgeList ↔ d ∈ p.edgeList ∧ d ≠ e) ∧
        q.weight w + w e = p.weight w := by
  obtain ⟨x,y,a,b,hl,hlist,hw⟩ := p.split_edge w e he
  have hn' : (a.edgeList ++ e :: b.edgeList).Nodup := hlist ▸ hn
  have hneA : e ∉ a.edgeList := by
    intro hea
    exact (List.nodup_append.mp hn').2.2 e hea e (by simp) rfl
  have hneB : e ∉ b.edgeList := (List.nodup_cons.mp hn'.of_append_right).1
  have hBA : (b.edgeList ++ a.edgeList).Nodup := by
    apply List.Nodup.append (List.nodup_cons.mp hn'.of_append_right).2 hn'.of_append_left
    intro d hdB hdA
    exact (List.nodup_append.mp hn').2.2 d hdA d (List.mem_cons_of_mem e hdB) rfl
  refine ⟨x,y,hl,b.append a,by simpa using hBA,?_,?_⟩
  · intro d
    rw [edgeList_append,hlist]
    simp only [List.mem_append,List.mem_cons]
    constructor
    · rintro (hdB | hdA)
      · exact ⟨Or.inr (Or.inr hdB),fun h => hneB (h ▸ hdB)⟩
      · exact ⟨Or.inl hdA,fun h => hneA (h ▸ hdA)⟩
    · rintro ⟨hd,hdne⟩
      rcases hd with hdA | rfl | hdB
      · exact Or.inr hdA
      · exact False.elim (hdne rfl)
      · exact Or.inl hdB
  · rw [weight_append,hw]
    ac_rfl

end LightEFTSpanners.NativeWeighted.Walk
