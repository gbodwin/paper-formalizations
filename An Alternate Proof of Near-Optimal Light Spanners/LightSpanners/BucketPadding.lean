import LightSpanners.HikerCompletion

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

theorem BucketWalk.first_cycle_forward {u v z : V} {i s : ℕ}
    (h : G.Adj u v) (p : G.Walk v z) (hp : C.BucketWalk i s (.cons h p))
    (hc : s(u,v) ∈ C.cycle.edges) :
    (⟨(u,v),h⟩ : G.Dart) ∈ C.cycle.darts := by
  obtain ⟨_,_,f,b,he,hf,hb,hfor,_⟩ := hp
  have he' : (⟨(u,v),h⟩ : G.Dart)::C.cycleDarts p=f++b := by
    simpa [cycleDarts,hc] using he
  cases f with
  | nil =>
    have hs : s=0 := hf.symm
    have hb' : b=[] := List.length_eq_zero_iff.mp (hb.trans hs)
    simp [hb'] at he'
  | cons d ds =>
    have hd := (List.cons.inj he').1
    rw [hd]
    exact hfor d (by simp)

theorem BucketWalk.last_cycle_backward {u v z : V} {i s : ℕ}
    (p : G.Walk u v) (h : G.Adj v z) (hp : C.BucketWalk i s (p.concat h))
    (hc : s(v,z) ∈ C.cycle.edges) :
    (⟨(v,z),h⟩ : G.Dart).symm ∈ C.cycle.darts := by
  obtain ⟨_,_,f,b,he,hf,hb,_,hback⟩ := hp
  have he' : C.cycleDarts p++[(⟨(v,z),h⟩ : G.Dart)]=f++b := by
    simpa [cycleDarts,Walk.darts_concat,List.concat_eq_append,hc] using he
  rcases List.eq_nil_or_concat b with rfl | ⟨b',d,rfl⟩
  · have hs : s=0 := hb.symm
    have hf' : f=[] := List.length_eq_zero_iff.mp (hf.trans hs)
    simp [hf'] at he'
  · have hd := congrArg List.getLast? he'
    simp only [List.concat_eq_append,← List.append_assoc,List.getLast?_concat,
      Option.some.injEq] at hd
    rw [hd]
    exact hback d (by simp)

theorem predecessor_forward_dart (v : V) :
    (⟨(C.successor.symm v,v),(C.predecessor_adj v).symm⟩ : G.Dart) ∈ C.cycle.darts := by
  apply (C.dart_mem_iff_successor _).mpr
  exact C.successor.apply_symm_apply v

theorem BucketWalk.prepend_forward_nonbacktracking {u v : V} {i s : ℕ}
    (p : G.Walk u v) (hp : C.BucketWalk i s p) :
    (Walk.cons (C.predecessor_adj u).symm p).edges.IsChain (· ≠ ·) := by
  cases p with
  | nil => simp
  | @cons u z v h p =>
    rw [Walk.edges_cons]
    apply List.IsChain.cons hp.1
    intro e he
    have heq : e=s(u,z) := by simpa [eq_comm] using he
    subst e
    intro hedge
    have hc : s(u,z) ∈ C.cycle.edges := by
      rw [← hedge]
      exact List.mem_map.mpr ⟨_,C.predecessor_forward_dart u,rfl⟩
    exact WalkSquad.forward_darts_ne C (C.predecessor_forward_dart u)
      (hp.first_cycle_forward C h p hc) (by rfl) hedge

/-- One simultaneous forward prefix and backward suffix preserves bucket
structure and adds exactly one to its balanced budget, provided a chord is present. -/
theorem BucketWalk.wrap_one {u v : V} {i s : ℕ} (p : G.Walk u v)
    (hp : C.BucketWalk i s p) (hne : C.chordEdges p ≠ []) :
    C.BucketWalk i (s+1)
      ((Walk.cons (C.predecessor_adj u).symm p).concat (C.predecessor_adj v)) := by
  have hpre := hp.prepend_forward_nonbacktracking C p
  have hnb : ((Walk.cons (C.predecessor_adj u).symm p).concat (C.predecessor_adj v)).edges.IsChain (· ≠ ·) := by
    cases p with
    | nil => simp at hne
    | @cons u z v h p =>
      obtain ⟨x,a,hx,heq⟩ := p.exists_cons_eq_concat h
      have hpc : C.BucketWalk i s (a.concat hx) := by rwa [← heq]
      rw [Walk.edges_concat,List.concat_eq_append]
      apply List.IsChain.append hpre (by simp)
      intro e he f hf hedge
      have he' : e=s(x,v) := by
        rw [heq] at he
        simp only [Walk.edges_cons,Walk.edges_concat,List.concat_eq_append,← List.cons_append,
          List.getLast?_concat] at he
        simpa only [Option.mem_def,Option.some.injEq,eq_comm] using he
      have hf' : f=s(v,C.successor.symm v) := by simpa [eq_comm] using hf
      have hc : s(x,v) ∈ C.cycle.edges := by
        rw [← he',hedge,hf']
        have hm : s(C.successor.symm v,v) ∈ C.cycle.edges :=
          List.mem_map.mpr ⟨_,C.predecessor_forward_dart v,rfl⟩
        simpa [Sym2.eq_swap] using hm
      have hn := WalkSquad.forward_darts_ne C (C.predecessor_forward_dart v)
        (hpc.last_cycle_backward C a hx hc) (by rfl)
      apply hn
      simpa [he',hf',Sym2.eq_swap] using hedge.symm
  obtain ⟨_,hw,f,b,he,hf,hb,hfor,hback⟩ := hp
  have hfront : s(C.successor.symm u,u) ∈ C.cycle.edges :=
    List.mem_map.mpr ⟨_,C.predecessor_forward_dart u,rfl⟩
  have hlast : s(v,C.successor.symm v) ∈ C.cycle.edges := by
    have hm : s(C.successor.symm v,v) ∈ C.cycle.edges :=
      List.mem_map.mpr ⟨_,C.predecessor_forward_dart v,rfl⟩
    simpa [Sym2.eq_swap] using hm
  refine ⟨hnb,?_,⟨(C.successor.symm u,u),(C.predecessor_adj u).symm⟩::f,
    b++[⟨(v,C.successor.symm v),C.predecessor_adj v⟩],?_,?_,?_,?_,?_⟩
  · simpa [chordEdges,Walk.edges_concat,List.concat_eq_append,hfront,hlast] using hw
  · simp [cycleDarts,Walk.darts_concat,List.concat_eq_append,hfront,hlast] at ⊢
    change C.cycleDarts p++[⟨(v,C.successor.symm v),C.predecessor_adj v⟩] =
      f++(b++[⟨(v,C.successor.symm v),C.predecessor_adj v⟩])
    rw [he,List.append_assoc]
  · simp [hf]
  · simp [hb]
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact C.predecessor_forward_dart u
    · exact hfor d hd
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hback d hd
    · have heq : d=⟨(v,C.successor.symm v),C.predecessor_adj v⟩ := List.mem_singleton.mp hd
      subst d
      exact C.predecessor_forward_dart v

end LightSpanners.UnitSpanningCycle

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Wrapping adds only cycle edges and preserves the complete chord word. -/
theorem chordEdges_wrap_one {u v : V} (p : G.Walk u v) :
    C.chordEdges ((Walk.cons (C.predecessor_adj u).symm p).concat (C.predecessor_adj v)) =
      C.chordEdges p := by
  have hf : s(C.successor.symm u,u) ∈ C.cycle.edges :=
    List.mem_map.mpr ⟨_,C.predecessor_forward_dart u,rfl⟩
  have hb : s(v,C.successor.symm v) ∈ C.cycle.edges := by
    have hm : s(C.successor.symm v,v) ∈ C.cycle.edges :=
      List.mem_map.mpr ⟨_,C.predecessor_forward_dart v,rfl⟩
    simpa [Sym2.eq_swap] using hm
  simp [chordEdges,Walk.edges_concat,List.concat_eq_append,hf,hb]

theorem chordEdges_copy {u v u' v' : V} (p : G.Walk u v)
    (hu : u=u') (hv : v=v') : C.chordEdges (p.copy hu hv)=C.chordEdges p := by
  subst_vars
  rfl

/-- Simultaneous padding at both ends gives actual shifted endpoints and
preserves every chord. No girth or numerical budget is required for this step. -/
theorem BucketWalk.pad {u v : V} {i s : ℕ} (p : G.Walk u v)
    (hp : C.BucketWalk i s p) (hne : C.chordEdges p ≠ []) (t : ℕ) :
    ∃ q : G.Walk ((C.successor.symm : V → V)^[t] u) ((C.successor.symm : V → V)^[t] v),
      C.BucketWalk i (s+t) q ∧ C.chordEdges q=C.chordEdges p := by
  induction t with
  | zero => exact ⟨p,by simpa using hp,rfl⟩
  | succ t ih =>
    obtain ⟨q,hq,hword⟩ := ih
    let r := (Walk.cons (C.predecessor_adj _).symm q).concat (C.predecessor_adj _)
    have hu : C.successor.symm ((C.successor.symm : V → V)^[t] u) =
      (C.successor.symm : V → V)^[t+1] u := (Function.iterate_succ_apply' _ _ _).symm
    have hv : C.successor.symm ((C.successor.symm : V → V)^[t] v) =
      (C.successor.symm : V → V)^[t+1] v := (Function.iterate_succ_apply' _ _ _).symm
    refine ⟨r.copy hu hv,?_,?_⟩
    · have hh := hq.wrap_one C q (by rwa [hword])
      have hh' : C.BucketWalk i (s+(t+1)) r := by simpa [r,Nat.add_assoc] using hh
      exact C.bucketWalk_copy r hu hv hh'
    · exact (C.chordEdges_copy r hu hv).trans ((C.chordEdges_wrap_one q).trans hword)

theorem BucketExtraSafe.pad_safe {u v : V} {eps : ℝ} {k i t : ℕ} {p : G.Walk u v}
    (hp : C.BucketExtraSafe eps k i p) (hne : C.chordEdges p ≠ [])
    (ht : (t:ℝ)≤eps*k*2^i/2) :
    ∃ q : G.Walk ((C.successor.symm : V → V)^[t] u) ((C.successor.symm : V → V)^[t] v),
      C.BucketSafe eps k i q ∧ C.chordEdges q=C.chordEdges p := by
  obtain ⟨s,hp,hs⟩ := hp
  obtain ⟨q,hq,hword⟩ := hp.pad C p hne t
  refine ⟨q,⟨s+t,hq,?_⟩,hword⟩
  push_cast
  linarith

end LightSpanners.UnitSpanningCycle
