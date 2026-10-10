import MinorFreeSpanners.ClusterGraph

namespace MinorFreeSpanners
open SimpleGraph LightSpanners
variable {I V : Type*} {A G B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

namespace MinorModel
lemma branchLabel_eq_some_iff {F : SimpleGraph I} (M : MinorModel F G) (x : V) (i : I) :
    M.branchLabel x = some i ↔ x ∈ M.branch i := by
  classical
  constructor
  · intro hx
    unfold branchLabel at hx
    split_ifs at hx with h
    · have he := Option.some.inj hx
      exact he ▸ h.choose_spec
  · exact M.branchLabel_eq
end MinorModel

namespace ClusterFamily
variable (C : ClusterFamily (I := I) A w D) (hA : A ≤ G) (hB : B ≤ G)

/-- Every coarse edge has an actual host edge with the corresponding unordered
pair of branch labels. -/
lemma exists_crossing_edge (e : Sym2 I) (he : e ∈ (C.graph B).edgeSet) :
    ∃ d ∈ B.edgeSet, Sym2.map (C.minorModel hA hB).branchLabel d = Sym2.map some e := by
  induction e using Sym2.inductionOn with
  | hf i j =>
    obtain ⟨_,x,hx,y,hy,hxy⟩ := (mem_edgeSet (C.graph B)).mp he
    refine ⟨s(x,y),(mem_edgeSet B).mpr hxy,?_⟩
    simp only [Sym2.map_mk,(C.minorModel hA hB).branchLabel_eq hx,(C.minorModel hA hB).branchLabel_eq hy]

/-- One real weight per unordered coarse edge, chosen from a genuine bridge.
This is symmetric by construction, without any total order on vertices. -/
noncomputable def edgeWeight (e : Sym2 I) : ℝ := by
  classical
  exact if he : e ∈ (C.graph B).edgeSet then
    w (C.exists_crossing_edge hA hB e he).choose else 0

/-- Recover either requested orientation of a host edge from its branch labels. -/
lemma orient_crossing (i j : I) (d : Sym2 V) (hdmem : d ∈ B.edgeSet)
    (hdlabel : Sym2.map (C.minorModel hA hB).branchLabel d = s(some i,some j)) :
    ∃ x ∈ C.branch i, ∃ y ∈ C.branch j, B.Adj x y ∧ d = s(x,y) := by
  induction d using Sym2.inductionOn with
  | hf x y =>
    have hadj := (mem_edgeSet B).mp hdmem
    simp only [Sym2.map_mk,Sym2.eq_iff] at hdlabel
    rcases hdlabel with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact ⟨x,((C.minorModel hA hB).branchLabel_eq_some_iff _ _).mp hx,
        y,((C.minorModel hA hB).branchLabel_eq_some_iff _ _).mp hy,hadj,rfl⟩
    · exact ⟨y,((C.minorModel hA hB).branchLabel_eq_some_iff _ _).mp hy,
        x,((C.minorModel hA hB).branchLabel_eq_some_iff _ _).mp hx,hadj.symm,Sym2.eq_swap⟩

/-- The chosen coarse weight is realized by a bridge in either requested
orientation. Disjoint branch sets provide the orientation recovery. -/
lemma exists_bridge_with_weight (i j : I) (hij : (C.graph B).Adj i j) :
    ∃ x ∈ C.branch i, ∃ y ∈ C.branch j, B.Adj x y ∧
      w s(x,y) = C.edgeWeight hA hB s(i,j) := by
  classical
  have he : s(i,j) ∈ (C.graph B).edgeSet := (mem_edgeSet _).mpr hij
  let d := (C.exists_crossing_edge hA hB s(i,j) he).choose
  have hd := (C.exists_crossing_edge hA hB s(i,j) he).choose_spec
  have hdmem : d ∈ B.edgeSet := hd.1
  have hdlabel : Sym2.map (C.minorModel hA hB).branchLabel d = s(some i,some j) := hd.2
  have hdw : w d = C.edgeWeight hA hB s(i,j) := by simp [edgeWeight,he,d]
  obtain ⟨x,hx,y,hy,hxy,hde⟩ := C.orient_crossing hA hB i j d hdmem hdlabel
  exact ⟨x,hx,y,hy,hxy,by rw [← hde]; exact hdw⟩

end ClusterFamily
end MinorFreeSpanners
