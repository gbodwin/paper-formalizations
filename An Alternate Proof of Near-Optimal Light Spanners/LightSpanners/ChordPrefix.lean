import LightSpanners.BucketPrefix

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Split an actual walk immediately after its kth chord. -/
theorem exists_kth_chord_prefix {u v : V} (p : G.Walk u v) {k : ℕ}
    (hk : 0 < k) (hlen : k ≤ (C.chordEdges p).length) :
    ∃ (x y : V) (a : G.Walk u x) (h : G.Adj x y) (b : G.Walk y v),
      p=(a.concat h).append b ∧ s(x,y) ∉ C.cycle.edges ∧
      (C.chordEdges (a.concat h)).length=k := by
  induction p generalizing k with
  | nil => simp at hlen; omega
  | @cons u z v h p ih =>
    by_cases hc : s(u,z) ∈ C.cycle.edges
    · have ht : k ≤ (C.chordEdges p).length := by
        simpa [chordEdges,Walk.edges_cons,hc] using hlen
      obtain ⟨x,y,a,hxy,b,hp,hch,hcount⟩ := ih hk ht
      refine ⟨x,y,.cons h a,hxy,b,?_,hch,?_⟩
      · simp [hp]
      · simpa [chordEdges,Walk.edges_cons,hc] using hcount
    · by_cases hk1 : k=1
      · subst k
        exact ⟨u,z,.nil,h,p,rfl,hc,by simp [chordEdges,hc]⟩
      · have ht : k-1 ≤ (C.chordEdges p).length := by
          have heq : C.chordEdges (.cons h p) = s(u,z)::C.chordEdges p := by
            simp [chordEdges,hc]
          rw [heq,List.length_cons] at hlen
          omega
        obtain ⟨x,y,a,hxy,b,hp,hch,hcount⟩ := ih (by omega : 0<k-1) ht
        refine ⟨x,y,.cons h a,hxy,b,?_,hch,?_⟩
        · simp [hp]
        · have heq : C.chordEdges ((Walk.cons h a).concat hxy) =
              s(u,z)::C.chordEdges (a.concat hxy) := by
            simp [chordEdges,hc]
          rw [heq,List.length_cons,hcount]
          omega

/-- Every sufficiently long bucket block has an extra-safe truncation with
exactly the requested positive number of chords. -/
theorem BucketExtraSafe.truncate {u v : V} {eps : ℝ} {k i r : ℕ} {p : G.Walk u v}
    (hp : C.BucketExtraSafe eps k i p) (hr : 0<r)
    (hlen : r≤(C.chordEdges p).length) :
    ∃ (z : V) (q : G.Walk u z), C.BucketExtraSafe eps k i q ∧
      (C.chordEdges q).length=r ∧ List.IsPrefix (C.chordEdges q) (C.chordEdges p) := by
  obtain ⟨s,hp,hs⟩ := hp
  obtain ⟨x,y,a,h,b,he,hch,hcount⟩ := C.exists_kth_chord_prefix p hr hlen
  rw [he] at hp
  obtain ⟨s',z,q,hbound,hq,hword⟩ := hp.complete_chord_prefix C a h b hch
  refine ⟨z,q,⟨s',hq,?_⟩,?_,?_⟩
  · exact (by exact_mod_cast hbound : (s':ℝ)≤s).trans hs
  · rw [hword,hcount]
  · rw [hword,he,C.chordEdges_append]
    exact List.prefix_append _ _

end LightSpanners.UnitSpanningCycle

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Truncation of an actual bucket-monotone extra-safe walk, with its original
ambient budget retained and no new chord inserted. -/
theorem BucketMonotoneWalk.truncate {u v : V} {eps : ℝ} {k J r : ℕ} {p : G.Walk u v}
    (hp : C.BucketMonotoneWalk eps k true J p) (hr : 0<r)
    (hlen : r≤(C.chordEdges p).length) :
    ∃ (z : V) (q : G.Walk u z) (J' : ℕ), J'≤J ∧
      C.BucketMonotoneWalk eps k true J' q ∧ (C.chordEdges q).length=r ∧
      List.IsPrefix (C.chordEdges q) (C.chordEdges p) := by
  induction hp with
  | nil u => simp at hlen; omega
  | @snoc J u v z p q hp hq ih =>
    by_cases hshort : r≤(C.chordEdges p).length
    · obtain ⟨z',p',J',hJ,hp',hc,hprefix⟩ := ih hshort
      refine ⟨z',p',J',by omega,hp',hc,?_⟩
      rw [C.chordEdges_append]
      exact hprefix.trans (List.prefix_append _ _)
    · have hqcount : r-(C.chordEdges p).length≤(C.chordEdges q).length := by
        rw [C.chordEdges_append,List.length_append] at hlen
        omega
      obtain ⟨z',q',hq',hc,hprefix⟩ := BucketExtraSafe.truncate C hq (by omega) hqcount
      refine ⟨z',p.append q',J+1,le_rfl,.snoc hp hq',?_,?_⟩
      · rw [C.chordEdges_append,List.length_append,hc]
        omega
      · rw [C.chordEdges_append,C.chordEdges_append]
        obtain ⟨t,ht⟩ := hprefix
        exact ⟨t,by simp [List.append_assoc,ht]⟩

/-- The weak-counting output yields an actual exactly-k extra-safe walk. -/
theorem exact_extra_safe_of_long {u v : V} {eps : ℝ} {k J : ℕ} {p : G.Walk u v}
    (hp : C.BucketMonotoneWalk eps k true J p) (hk : 0<k)
    (hlen : k≤(C.chordEdges p).length) :
    ∃ (z : V) (q : G.Walk u z), C.BucketMonotoneKPath eps k true q := by
  obtain ⟨z,q,J',_,hq,hcount,_⟩ := hp.truncate C hk hlen
  exact ⟨z,q,hcount,J',hq⟩

end LightSpanners.UnitSpanningCycle
