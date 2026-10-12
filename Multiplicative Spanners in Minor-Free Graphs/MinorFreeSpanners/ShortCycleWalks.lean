import MinorFreeSpanners.PathRootedWalk

/-! The short-cycle cluster has an actual supported diameter certificate.
Split its light middle path in half, attach the two outer arms, and cross the
original heavy edge at most once. No shortest-path projection is assumed. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem short_cycle_walks (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (H : SimpleGraph I) (d : I → ℝ) (L : ℝ) {x y u v : I}
    (l : H.Walk x u) (m : H.Walk x y) (r : H.Walk y v)
    (hl : l.IsPath) (hm : m.IsPath) (hr : r.IsPath)
    (hD : 0≤D) (hd1 : ∀ i,1≤d i) (hdD : ∀ i,d i≤D)
    (hlmass : pathMass (fun i => d i+1) l≤L+D+1)
    (hrmass : pathMass (fun i => d i+1) r≤L+D+1)
    (hmmass : pathMass (fun i => d i+1) m≤2*(L+D+1))
    (hdiam : ∀ i a,a∈C.branch i → ∀ b,b∈C.branch i →
      ∃ p : A.Walk a b,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (hbridge : ∀ i j,H.Adj i j → ∃ a∈C.branch i,∃ b∈C.branch j,
      ∃ _hab : G.Adj a b,w s(a,b)≤1)
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) (hab : G.Adj a b)
    (hw : 0≤w s(a,b)) :
    ∀ z,(∃ i∈l.support.toFinset∪m.support.toFinset∪r.support.toFinset,z∈C.branch i) →
      ∀ t,(∃ i∈l.support.toFinset∪m.support.toFinset∪r.support.toFinset,t∈C.branch i) →
      ∃ p : G.Walk z t,
        (∀ s∈p.support,∃ i∈l.support.toFinset∪m.support.toFinset∪r.support.toFinset,s∈C.branch i) ∧
        walkWeight w p≤2*(L+2*D+1)+w s(a,b) := by
  classical
  have hpos : 0<pathMass (fun i => d i+1) m := by
    apply Finset.sum_pos
    · intro i _
      have hi := hd1 i
      linarith
    · exact ⟨x,List.mem_toFinset.mpr m.start_mem_support⟩
  obtain ⟨z,p,q,he,hp,hq,hpm,hqm⟩ := exists_balanced_path_split (fun i => d i+1) (D+1) m hm
    (fun i _ => by have hi:=hdD i;linarith) hpos
  have hpb : pathMass (fun i => d i+1) p-1≤L+2*D+1 := by linarith
  have hqb : pathMass (fun i => d i+1) q.reverse-1≤L+2*D+1 := by
    rw [pathMass_reverse]
    linarith
  let S : Set V := {s | ∃ i,(i∈l.support ∨ i∈p.support) ∧ s∈C.branch i}
  let T : Set V := {s | ∃ i,(i∈r.support ∨ i∈q.reverse.support) ∧ s∈C.branch i}
  have hnon : ∀ i,0≤d i+1 := fun i => by have hi:=hd1 i;linarith
  have hS : ∀ s∈S,∃ t : G.Walk s a,(∀ z∈t.support,z∈S) ∧ walkWeight w t≤L+2*D+1 := by
    rintro s ⟨i,hi,hsi⟩
    rcases hi with hi|hi
    · obtain ⟨t,ht,htw⟩ := C.path_to_start hA H d l hl (fun i _ => hnon i) hdiam hbridge hi hsi ha
      refine ⟨t,?_,by linarith⟩
      intro z hz
      obtain ⟨j,hj,hzj⟩ := ht z hz
      exact ⟨j,Or.inl hj,hzj⟩
    · obtain ⟨t,ht,htw⟩ := C.path_to_start hA H d p hp (fun i _ => hnon i) hdiam hbridge hi hsi ha
      refine ⟨t,?_,htw.trans hpb⟩
      intro z hz
      obtain ⟨j,hj,hzj⟩ := ht z hz
      exact ⟨j,Or.inr hj,hzj⟩
  have hT : ∀ s∈T,∃ t : G.Walk s b,(∀ z∈t.support,z∈T) ∧ walkWeight w t≤L+2*D+1 := by
    rintro s ⟨i,hi,hsi⟩
    rcases hi with hi|hi
    · obtain ⟨t,ht,htw⟩ := C.path_to_start hA H d r hr (fun i _ => hnon i) hdiam hbridge hi hsi hb
      refine ⟨t,?_,by linarith⟩
      intro z hz
      obtain ⟨j,hj,hzj⟩ := ht z hz
      exact ⟨j,Or.inl hj,hzj⟩
    · obtain ⟨t,ht,htw⟩ := C.path_to_start hA H d q.reverse hq.reverse (fun i _ => hnon i)
        hdiam hbridge hi hsi hb
      refine ⟨t,?_,htw.trans hqb⟩
      intro z hz
      obtain ⟨j,hj,hzj⟩ := ht z hz
      exact ⟨j,Or.inr hj,hzj⟩
  have hU : S∪T={s | ∃ i∈l.support.toFinset∪m.support.toFinset∪r.support.toFinset,s∈C.branch i} := by
    ext s
    constructor
    · rintro (⟨i,hi,hsi⟩|⟨i,hi,hsi⟩)
      · rcases hi with hi|hi
        · exact ⟨i,Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr hi)),hsi⟩
        · have him : i∈m.support := by rw [he,Walk.mem_support_append_iff];exact Or.inl hi
          exact ⟨i,Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr him)),hsi⟩
      · rcases hi with hi|hi
        · exact ⟨i,Finset.mem_union_right _ (List.mem_toFinset.mpr hi),hsi⟩
        · have him : i∈m.support := by
            rw [he,Walk.mem_support_append_iff]
            exact Or.inr (by simpa using hi)
          exact ⟨i,Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr him)),hsi⟩
    · rintro ⟨i,hi,hsi⟩
      rcases Finset.mem_union.mp hi with hi|hi
      · rcases Finset.mem_union.mp hi with hi|hi
        · exact Or.inl ⟨i,Or.inl (List.mem_toFinset.mp hi),hsi⟩
        · have him := List.mem_toFinset.mp hi
          rw [he,Walk.mem_support_append_iff] at him
          rcases him with him|him
          · exact Or.inl ⟨i,Or.inr him,hsi⟩
          · exact Or.inr ⟨i,Or.inr (by simpa using him),hsi⟩
      · exact Or.inr ⟨i,Or.inl (List.mem_toFinset.mp hi),hsi⟩
  have h := rooted_sets_bridge w S T hab ⟨x,Or.inl l.start_mem_support,ha⟩
    (L+2*D+1) (w s(a,b)) hw le_rfl hS hT
  simpa only [hU,Set.mem_ofPred_eq] using h

end ClusterFamily
end MinorFreeSpanners
