import Mathlib.Data.Finset.Sort
import OnlineReachabilityPreservers.SplitPreservation

/-! The exact lower construction for the consecutive-edge overlay in a common vertex order. -/

namespace OnlineReachabilityPreservers

open Finset Relation

variable {V I : Type*} [LinearOrder V] [LinearOrder I]

private inductive ColouredDetour (paths : I → Finset V) (river : I) :
    V → V → List I → Prop
  | nil (u : V) : ColouredDetour paths river u u []
  | cons {u v w : V} {c : I} {C : List I} (fresh : river ≠ c)
      (edge : PathBefore paths c u v) (tail : ColouredDetour paths river v w C) :
      ColouredDetour paths river u w (c::C)

namespace ColouredDetour

variable {paths : I → Finset V} {river : I} {u v w : V} {C : List I}

omit [LinearOrder I] in
private theorem le (r : ColouredDetour paths river u v C) : u ≤ v := by
  induction r with
  | nil => exact le_rfl
  | cons _ edge _ ih => exact edge.2.2.le.trans ih

omit [LinearOrder I] in
private theorem append_step (r : ColouredDetour paths river u v C) {c : I}
    (fresh : river ≠ c) (edge : PathBefore paths c v w) :
    ColouredDetour paths river u w (C++[c]) := by
  induction r with
  | nil => exact .cons fresh edge (.nil _)
  | cons diff e _ ih => exact .cons diff e (ih edge)

omit [LinearOrder I] in
private theorem used_fresh (r : ColouredDetour paths river u v C) {c : I} (mem : c ∈ C) :
    river ≠ c := by
  induction r with
  | nil => simp at mem
  | cons diff _ _ ih =>
    rcases List.mem_cons.mp mem with rfl | h
    · exact diff
    · exact ih h

omit [LinearOrder I] in
private theorem suffix_after (r : ColouredDetour paths river u v C) (nodup : C.Nodup)
    {c : I} (present : c ∈ C) :
    ∃ a b D, u ≤ a ∧ PathBefore paths c a b ∧ ColouredDetour paths river b v D ∧
      D.Nodup ∧ c ∉ D := by
  induction r with
  | nil => simp at present
  | @cons x y z d D fresh edge tail ih =>
    obtain ⟨none,nd⟩ := List.nodup_cons.mp nodup
    rcases List.mem_cons.mp present with rfl | mem
    · exact ⟨x,y,D,le_rfl,edge,tail,nd,none⟩
    · obtain ⟨a,b,E,le,other,rest,ndE,noE⟩ := ih nd mem
      exact ⟨a,b,E,edge.2.2.le.trans le,other,rest,ndE,noE⟩

/-- A repeated colour can be shortcut when every path uses the same vertex order. -/
private theorem remove_duplicates (r : ColouredDetour paths river u v C) :
    ∃ D : List I, ColouredDetour paths river u v D ∧ D.Nodup := by
  induction r with
  | nil => exact ⟨[],.nil _,by simp⟩
  | @cons s t v c C fresh edge tail ih =>
    obtain ⟨D,shortened,nd⟩ := ih
    by_cases used : c ∈ D
    · obtain ⟨a,b,E,ha,other,rest,ndE,noE⟩ := suffix_after shortened nd used
      have step : PathBefore paths c s b :=
        ⟨edge.1,other.2.1,(edge.2.2.trans_le ha).trans other.2.2⟩
      exact ⟨c::E,.cons fresh step rest,List.nodup_cons.mpr ⟨noE,ndE⟩⟩
    · exact ⟨c::D,.cons fresh edge shortened,List.nodup_cons.mpr ⟨used,nd⟩⟩

omit [LinearOrder I] in
private theorem coordinates (r : ColouredDetour paths river u v C) :
    ∃ x : Fin (C.length+1) → V, x 0 = u ∧ x (Fin.last C.length) = v ∧
      ∀ i : Fin C.length, PathBefore paths (C.get i) (x i.castSucc) (x i.succ) := by
  induction r with
  | nil =>
    exact ⟨fun _ => _,rfl,rfl,fun i => i.elim0⟩
  | @cons s t v c D _ edge tail ih =>
    obtain ⟨x,x0,xlast,steps⟩ := ih
    let vertices : Fin ((c::D).length+1) → V := Fin.cases s x
    refine ⟨vertices,rfl,?_,?_⟩
    · change x (Fin.last D.length) = v
      exact xlast
    · intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j,rfl⟩
      · change PathBefore paths c s (x 0)
        rwa [x0]
      · change PathBefore paths (D.get j) (x j.castSucc) (x j.succ)
        exact steps j

private theorem yields_bridge (r : ColouredDetour paths river u v C)
    (riverEdge : PathBefore paths river u v) : ∃ k, Nonempty (Bridge (PathBefore paths) k) := by
  obtain ⟨D,short,nd⟩ := remove_duplicates r
  obtain ⟨x,x0,xlast,steps⟩ := short.coordinates
  cases D with
  | nil =>
    have uv : u=v := x0.symm.trans xlast
    exact (riverEdge.2.2.ne uv).elim
  | cons c rest =>
    refine ⟨rest.length,⟨orderedBridge x (fun i => (c::rest).get i) river
      (List.nodup_iff_injective_get.mp nd) ?_ ?_ steps⟩⟩
    · intro i
      exact short.used_fresh ((c::rest).get_mem i)
    · change PathBefore paths river (x 0) (x (Fin.last (c::rest).length))
      rwa [x0,xlast]

end ColouredDetour

variable [Fintype V] [Fintype I]

/-- All forward steps on a path other than the designated river. -/
noncomputable def otherPathArcs (paths : I → Finset V) (river : I) : Arcs V := by
  classical
  exact univ.filter fun e => ∃ c, river ≠ c ∧ PathBefore paths c e.1 e.2

private theorem mem_otherPathArcs {paths : I → Finset V} {river : I} {e : V × V} :
    e ∈ otherPathArcs paths river ↔ ∃ c, river ≠ c ∧ PathBefore paths c e.1 e.2 := by
  classical
  simp [otherPathArcs]

/-- A route between two vertices of the river using only other paths creates a bridge. -/
theorem bridge_of_acyclic_detour {paths : I → Finset V} {river : I} {u v : V}
    (along : PathBefore paths river u v) (detour : Reach (otherPathArcs paths river) u v) :
    ∃ k, Nonempty (Bridge (PathBefore paths) k) := by
  have lift {a b : V} (r : Reach (otherPathArcs paths river) a b) :
      ∃ C, ColouredDetour paths river a b C := by
    induction r with
    | refl => exact ⟨[],.nil _⟩
    | tail _ edge ih =>
      obtain ⟨D,steps⟩ := ih
      obtain ⟨c,fresh,step⟩ := mem_otherPathArcs.mp edge
      exact ⟨D++[c],steps.append_step fresh step⟩
  obtain ⟨C,steps⟩ := lift detour
  exact steps.yields_bridge along

/-- Adjacent vertices of one path in the common vertex order. -/
noncomputable def consecutiveArcs (S : Finset V) : Arcs V := by
  classical
  exact univ.filter fun e => e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 < e.2 ∧
    ∀ w ∈ S, ¬ (e.1 < w ∧ w < e.2)

theorem mem_consecutiveArcs {S : Finset V} {u v : V} :
    (u,v) ∈ consecutiveArcs S ↔ u ∈ S ∧ v ∈ S ∧ u < v ∧
      ∀ w ∈ S, ¬ (u < w ∧ w < v) := by
  classical
  simp [consecutiveArcs]

omit [LinearOrder I] [Fintype I] in
private theorem consecutiveArcs_before {paths : I → Finset V} {i : I} {u v : V}
    (h : (u,v) ∈ consecutiveArcs (paths i)) : PathBefore paths i u v :=
  let p := mem_consecutiveArcs.mp h
  ⟨p.1,p.2.1,p.2.2.1⟩

/-- Vertices of one path are connected by its consecutive arcs. -/
theorem consecutiveArcs_reach {S : Finset V} {s t : V} (hs : s ∈ S) (ht : t ∈ S)
    (st : s ≤ t) : Reach (consecutiveArcs S) s t := by
  have aux (k : ℕ) (u : V) (hu : u ∈ S) (hut : u ≤ t)
      (hk : (S.filter fun v => u<v).card = k) : Reach (consecutiveArcs S) u t := by
    induction k using Nat.strong_induction_on generalizing u with
    | _ k ih =>
      by_cases same : u=t
      · rw [same]
      · have lt : u<t := lt_of_le_of_ne hut same
        let above (u : V) := S.filter (u<·)
        have tAbove : t ∈ above u := mem_filter.mpr ⟨ht,lt⟩
        obtain ⟨v,hv⟩ := least?_some ⟨t,tAbove⟩
        obtain ⟨vIn,uv⟩ := mem_filter.mp (least?_mem hv)
        have vt : v≤t := least?_le hv tAbove
        have e : (u,v) ∈ consecutiveArcs S := by
          apply mem_consecutiveArcs.mpr
          refine ⟨hu,vIn,uv,fun w hw h => ?_⟩
          exact h.2.not_ge (least?_le hv (mem_filter.mpr ⟨hw,h.1⟩))
        have sub : above v ⊂ above u := by
          apply ssubset_iff_subset_ne.mpr
          refine ⟨?_,?_⟩
          · intro a ha
            obtain ⟨inside,lt⟩ := mem_filter.mp ha
            exact mem_filter.mpr ⟨inside,uv.trans lt⟩
          · intro eq
            have yes : v ∈ above u := least?_mem hv
            have no : v ∉ above v := by simp [above]
            exact no (eq.symm ▸ yes)
        have ltCount := card_lt_card sub
        change (above u).card = k at hk
        rw [hk] at ltCount
        exact (ih _ ltCount v vIn vt rfl).head e
  exact aux _ s hs st rfl

private theorem consecutiveArcs_unique_next {S : Finset V} {u a b : V}
    (ha : (u,a) ∈ consecutiveArcs S) (hb : (u,b) ∈ consecutiveArcs S) : a=b := by
  obtain ⟨_,ai,ua,noA⟩ := mem_consecutiveArcs.mp ha
  obtain ⟨_,bi,ub,noB⟩ := mem_consecutiveArcs.mp hb
  rcases lt_trichotomy a b with l | e | r
  · exact (noB a ai ⟨ua,l⟩).elim
  · exact e
  · exact (noA b bi ⟨ub,r⟩).elim

/-- The directed overlay that includes only consecutive arcs of each path. -/
noncomputable def acyclicOverlay (paths : I → Finset V) : Arcs V :=
  univ.biUnion fun i => consecutiveArcs (paths i)

private theorem overlay_step_other {paths : I → Finset V} {river : I} {u v : V}
    (he : (u,v) ∈ acyclicOverlay paths) (notRiver : (u,v) ∉ consecutiveArcs (paths river)) :
    (u,v) ∈ otherPathArcs paths river := by
  obtain ⟨c,_,hc⟩ := mem_biUnion.mp he
  exact mem_otherPathArcs.mpr ⟨c,fun eq => notRiver (eq.symm ▸ hc),consecutiveArcs_before hc⟩

omit [LinearOrder I] in
private theorem overlay_step_lt {paths : I → Finset V} {u v : V}
    (h : (u,v) ∈ acyclicOverlay paths) : u<v := by
  obtain ⟨c,_,he⟩ := mem_biUnion.mp h
  exact (mem_consecutiveArcs.mp he).2.2.1

/-- In a common vertex order with no bridges, any route between vertices of
one path can be confined to its own consecutive arcs. -/
theorem acyclicOverlay_confine {paths : I → Finset V} (free : ∀ k, IsEmpty (Bridge (PathBefore paths) k))
    {H : Arcs V} (sub : H ⊆ acyclicOverlay paths) {river : I} {u v : V}
    (hu : u ∈ paths river) (hv : v ∈ paths river) (r : Reach H u v) :
    Reach (H ∩ consecutiveArcs (paths river)) u v := by
  let R := consecutiveArcs (paths river)
  let Q := otherPathArcs paths river
  have forbidden {a b : V} (ha : a ∈ paths river) (hb : b ∈ paths river) (lt : a<b)
      (rr : Reach Q a b) : False := by
    obtain ⟨k,⟨w⟩⟩ := bridge_of_acyclic_detour ⟨ha,hb,lt⟩ rr
    exact (free k).false w
  have inv {w : V} (walk : Reach H u w) :
      (w ∈ paths river ∧ Reach (H ∩ R) u w) ∨
        (w ∉ paths river ∧ ∃ a ∈ paths river, a<w ∧ Reach Q a w) := by
    induction walk with
    | refl => exact Or.inl ⟨hu,.refl⟩
    | @tail x y _ edge ih =>
      have xy := overlay_step_lt (sub edge)
      rcases ih with ⟨hx,old⟩ | ⟨hx,a,ha,ax,detour⟩
      · by_cases correct : (x,y) ∈ R
        · exact Or.inl ⟨(mem_consecutiveArcs.mp correct).2.1,old.tail (mem_inter.mpr ⟨edge,correct⟩)⟩
        · have rival : (x,y) ∈ Q := overlay_step_other (sub edge) correct
          by_cases hy : y ∈ paths river
          · exact (forbidden hx hy xy (.single rival)).elim
          · exact Or.inr ⟨hy,x,hx,xy,.single rival⟩
      · have other : (x,y) ∈ Q :=
          overlay_step_other (sub edge) (fun correct => hx (mem_consecutiveArcs.mp correct).1)
        by_cases hy : y ∈ paths river
        · exact (forbidden ha hy (ax.trans xy) (detour.tail other)).elim
        · exact Or.inr ⟨hy,a,ha,ax.trans xy,detour.tail other⟩
  rcases inv r with h | h
  · exact h.2
  · exact (h.1 hv).elim

private theorem consecutiveArc_required {S : Finset V} {H : Arcs V} (sub : H ⊆ consecutiveArcs S)
    {s t x y : V} (r : Reach H s t) (edge : (x,y) ∈ consecutiveArcs S) (sx : s≤x) (yt : y≤t) :
    (x,y) ∈ H := by
  obtain ⟨hx,_,xy,_⟩ := mem_consecutiveArcs.mp edge
  have crossing {a b : V} (walk : Reach H a b) (low : a≤x) (high : x<b) :
      ∃ u v, (u,v) ∈ H ∧ u≤x ∧ x<v := by
    induction walk with
    | refl => exact (high.not_ge low).elim
    | @tail u v _ ev ih =>
      by_cases hu : x<u
      · exact ih hu
      · exact ⟨u,v,ev,le_of_not_gt hu,high⟩
  obtain ⟨a,b,ab,ax,xb⟩ := crossing r sx (xy.trans_le yt)
  have step := sub ab
  have eq : a=x := by
    by_contra ne
    exact (mem_consecutiveArcs.mp step).2.2.2 x hx ⟨lt_of_le_of_ne ax ne,xb⟩
  subst a
  have bEq := consecutiveArcs_unique_next step edge
  exact bEq ▸ ab

/-- The acyclic overlay requires every arc when all designated endpoint pairs
are kept reachable. Each endpoint is the first or last vertex of its path. -/
theorem theorem14_acyclic_overlay_required {paths : I → Finset V}
    (free : ∀ k, IsEmpty (Bridge (PathBefore paths) k))
    (first last : I → V)
    (head : ∀ i, first i ∈ paths i ∧ ∀ w ∈ paths i, first i≤w)
    (tail : ∀ i, last i ∈ paths i ∧ ∀ w ∈ paths i, w≤last i)
    {H : Arcs V} (sub : H ⊆ acyclicOverlay paths) (preserved : ∀ i, Reach H (first i) (last i)) :
    H = acyclicOverlay paths := by
  apply le_antisymm sub
  intro e he
  obtain ⟨i,_,step⟩ := mem_biUnion.mp he
  have r := acyclicOverlay_confine free sub (head i).1 (tail i).1 (preserved i)
  have h := mem_consecutiveArcs.mp step
  exact (mem_inter.mp (consecutiveArc_required inter_subset_right r step
    ((head i).2 e.1 h.1) ((tail i).2 e.2 h.2.1))).1

omit [LinearOrder I] in
theorem acyclicOverlay_routes {paths : I → Finset V} {i : I} {s t : V}
    (hs : s ∈ paths i) (ht : t ∈ paths i) (st : s≤t) :
    Reach (acyclicOverlay paths) s t :=
  reach_mono (fun _ he => mem_biUnion.mpr ⟨i,mem_univ _,he⟩) (consecutiveArcs_reach hs ht st)

/-- Each nonfinal vertex contributes exactly one consecutive arc. -/
theorem consecutiveArcs_card (S : Finset V) : (consecutiveArcs S).card = S.card-1 := by
  classical
  by_cases nonempty : S.Nonempty
  · let z := S.max' nonempty
    have zmem : z ∈ S := max'_mem _ _
    have largest : ∀ a ∈ S, a≤z := fun a ha => le_max' S a ha
    let E := consecutiveArcs S
    have origins : E.image Prod.fst = S.erase z := by
      ext u
      constructor
      · intro h
        obtain ⟨e,he,rfl⟩ := mem_image.mp h
        have t := mem_consecutiveArcs.mp he
        have lt := t.2.2.1.trans_le (largest _ t.2.1)
        exact mem_erase.mpr ⟨lt.ne,t.1⟩
      · intro h
        obtain ⟨ne,hu⟩ := mem_erase.mp h
        let above := S.filter (u<·)
        have hz : z ∈ above := mem_filter.mpr ⟨zmem,lt_of_le_of_ne (largest u hu) ne⟩
        obtain ⟨v,hv⟩ := least?_some ⟨z,hz⟩
        obtain ⟨hvS,uv⟩ := mem_filter.mp (least?_mem hv)
        have e : (u,v) ∈ E := by
          apply mem_consecutiveArcs.mpr
          refine ⟨hu,hvS,uv,fun a ha hlt => ?_⟩
          exact hlt.2.not_ge (least?_le hv (mem_filter.mpr ⟨ha,hlt.1⟩))
        exact mem_image.mpr ⟨(u,v),e,rfl⟩
    have inj : Set.InjOn (Prod.fst : V × V → V) E := by
      rintro ⟨u,v⟩ uv ⟨a,b⟩ ab e
      change u=a at e
      subst a
      exact Prod.ext rfl (consecutiveArcs_unique_next uv ab)
    change E.card = S.card-1
    rw [← card_image_of_injOn inj,origins,card_erase_of_mem zmem]
  · have e := not_nonempty_iff_eq_empty.mp nonempty
    subst S
    simp [consecutiveArcs]

theorem acyclicOverlay_card {paths : I → Finset V} (free : ∀ k, IsEmpty (Bridge (PathBefore paths) k)) :
    (acyclicOverlay paths).card = ∑ i : I, ((paths i).card-1) := by
  classical
  have separate : (↑(univ : Finset I) : Set I).PairwiseDisjoint (fun i => consecutiveArcs (paths i)) := by
    intro a _ b _ unequal
    apply disjoint_left.mpr
    intro e ha hb
    have rival : e ∈ otherPathArcs paths a :=
      mem_otherPathArcs.mpr ⟨b,unequal,consecutiveArcs_before hb⟩
    obtain ⟨k,⟨bridge⟩⟩ := bridge_of_acyclic_detour (consecutiveArcs_before ha) (.single rival)
    exact (free k).false bridge
  simp only [acyclicOverlay,card_biUnion separate,consecutiveArcs_card]

omit [LinearOrder I] in
theorem acyclicOverlay_dag (paths : I → Finset V) : IsDAG (acyclicOverlay paths) := by
  have le {u v : V} (r : Reach (acyclicOverlay paths) u v) : u≤v := by
    induction r with
    | refl => exact le_rfl
    | tail _ he ih => exact ih.trans (overlay_step_lt he).le
  intro u v e back
  exact (overlay_step_lt e).not_ge (le back)

/-- Each acyclic bridge-free path family has an overlay instance with one
demand per path and exactly mass minus path count necessary edges. -/
theorem theorem14_acyclic_overlay_lower {paths : I → Finset V}
    (nonempty : ∀ i, (paths i).Nonempty)
    (free : ∀ k, IsEmpty (Bridge (PathBefore paths) k)) :
    ∃ G : Arcs V, ∃ D : List (V × V), IsDAG G ∧ D.length = Fintype.card I ∧
      (∀ d ∈ D, Reach G d.1 d.2) ∧
      ∀ H ⊆ G, Preserves G H D → H.card+D.length = ∑ i : I, (paths i).card := by
  classical
  let first (i : I) := (paths i).min' (nonempty i)
  let last (i : I) := (paths i).max' (nonempty i)
  let d (i : I) := (first i,last i)
  let D := (univ : Finset I).toList.map d
  let G := acyclicOverlay paths
  have dLen : D.length = Fintype.card I := by simp [D]
  have lo (i : I) : first i ∈ paths i ∧ ∀ v ∈ paths i, first i≤v :=
    ⟨min'_mem _ _,fun v hv => min'_le (paths i) v hv⟩
  have hi (i : I) : last i ∈ paths i ∧ ∀ v ∈ paths i, v≤last i :=
    ⟨max'_mem _ _,fun v hv => le_max' (paths i) v hv⟩
  have serve (i : I) : Reach G (first i) (last i) :=
    acyclicOverlay_routes (lo i).1 (hi i).1 ((lo i).2 _ (hi i).1)
  refine ⟨G,D,acyclicOverlay_dag paths,dLen,?_,?_⟩
  · intro e he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    exact serve i
  · intro H sub preserves
    have all (i : I) : Reach H (first i) (last i) := by
      have mem : d i ∈ D := List.mem_map_of_mem (by simp)
      exact (preserves (d i) mem).mpr (serve i)
    have eq : H=G := theorem14_acyclic_overlay_required free first last lo hi sub all
    rw [eq,dLen,acyclicOverlay_card free]
    have one : (∑ _i : I, 1) = Fintype.card I := by simp
    rw [← one,← sum_add_distrib]
    exact sum_congr rfl (fun i _ => Nat.sub_add_cancel (card_pos.mpr (nonempty i)))

end OnlineReachabilityPreservers
