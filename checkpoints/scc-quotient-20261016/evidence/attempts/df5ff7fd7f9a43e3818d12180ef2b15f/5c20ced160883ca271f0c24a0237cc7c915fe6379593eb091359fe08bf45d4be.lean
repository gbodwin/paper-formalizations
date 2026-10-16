import SlackSparsification.SourcewiseCollision
import Mathlib.Data.Fintype.Quotient

namespace SlackSparsification.Directed
open SimpleGraph Finset
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The SCC equivalence uses actual allowed walks in the original graph. -/
def componentSetoid (K : SimpleGraph V) (A : V → V → Prop) : Setoid V where
  r x y := Reachable K A x y ∧ Reachable K A y x
  iseqv := ⟨fun x => ⟨⟨Walk.nil,by simp [Allowed]⟩,⟨Walk.nil,by simp [Allowed]⟩⟩,
    fun h => ⟨h.2,h.1⟩,
    fun h h' => ⟨reachable_trans h.1 h'.1,reachable_trans h'.2 h.2⟩⟩

abbrev Component (K : SimpleGraph V) (A : V → V → Prop) := Quotient (componentSetoid K A)

noncomputable instance componentFintype (K : SimpleGraph V) (A : V → V → Prop) :
    Fintype (Component K A) := Fintype.ofFinite _
noncomputable instance componentDecidableEq (K : SimpleGraph V) (A : V → V → Prop) :
    DecidableEq (Component K A) := Classical.decEq _

def component (K : SimpleGraph V) (A : V → V → Prop) (v : V) : Component K A := Quotient.mk _ v

def componentGraph (K : SimpleGraph V) (A : V → V → Prop) : SimpleGraph (Component K A) := ⊤

/-- Quotient arcs have distinct endpoints and an original crossing-arc witness. -/
def componentArc (K : SimpleGraph V) (A : V → V → Prop) (c d : Component K A) : Prop :=
  c ≠ d ∧ ∃ u v, component K A u = c ∧ component K A v = d ∧ K.Adj u v ∧ A u v

theorem component_eq_iff (K : SimpleGraph V) (A : V → V → Prop) (u v : V) :
    component K A u = component K A v ↔ Reachable K A u v ∧ Reachable K A v u :=
  Quotient.eq

theorem component_card_le (K : SimpleGraph V) (A : V → V → Prop) :
    Fintype.card (Component K A) ≤ Fintype.card V :=
  Fintype.card_le_of_surjective (component K A) (fun c => ⟨c.out,Quotient.out_eq c⟩)

/-- Project a walk, dropping steps whose endpoints lie in the same SCC. -/
theorem project_reachable (K : SimpleGraph V) (A : V → V → Prop) {s t : V}
    (hr : Reachable K A s t) :
    Reachable (componentGraph K A) (componentArc K A) (component K A s) (component K A t) := by
  obtain ⟨p,hp⟩ := hr
  induction p with
  | nil => exact ⟨Walk.nil,by simp [Allowed]⟩
  | @cons u v t huv p ih =>
    have ha : A u v := hp ⟨(u,v),huv⟩ (by simp)
    have ht : Allowed A p := fun d hd => hp d (by simp [hd])
    obtain ⟨q,hq⟩ := ih ht
    by_cases heq : component K A u = component K A v
    · rw [heq]
      exact ⟨q,hq⟩
    · have hadj : (componentGraph K A).Adj (component K A u) (component K A v) := by
        simpa [componentGraph] using heq
      refine ⟨Walk.cons hadj q,?_⟩
      intro d hd
      simp only [Walk.darts_cons,List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact ⟨heq,u,v,rfl,rfl,huv,ha⟩
      · exact hq d hd

/-- One quotient step can be traversed between any original representatives.
The connectors use the original graph; sparse connectors are constructed later. -/
theorem component_arc_lift (K : SimpleGraph V) (A : V → V → Prop)
    {c d : Component K A} (h : componentArc K A c d) (x y : V)
    (hx : component K A x = c) (hy : component K A y = d) : Reachable K A x y := by
  obtain ⟨_,u,v,hu,hv,huv,ha⟩ := h
  have hxu := ((component_eq_iff K A x u).mp (hx.trans hu.symm)).1
  have hvy := ((component_eq_iff K A v y).mp (hv.trans hy.symm)).1
  have huv' : Reachable K A u v := ⟨Walk.cons huv Walk.nil,by simpa [Allowed] using ha⟩
  exact reachable_trans (reachable_trans hxu huv') hvy

/-- Lift a quotient walk through original SCC connectors, including nil walks. -/
theorem lift_component_walk (K : SimpleGraph V) (A : V → V → Prop)
    {c d : Component K A} (p : (componentGraph K A).Walk c d)
    (hp : Allowed (componentArc K A) p) (x y : V)
    (hx : component K A x = c) (hy : component K A y = d) : Reachable K A x y := by
  induction p generalizing x with
  | nil => exact ((component_eq_iff K A x y).mp (hx.trans hy.symm)).1
  | @cons c z d hcz p ih =>
    have ha := hp ⟨(c,z),hcz⟩ (by simp)
    have ht : Allowed (componentArc K A) p := fun e he => hp e (by simp [he])
    have hz : component K A z.out = z := Quotient.out_eq z
    exact reachable_trans (component_arc_lift K A ha x z.out hx hz) (ih ht z.out hz hy)

/-- Original and quotient reachability agree even for endpoints in one class. -/
theorem component_reachable_iff (K : SimpleGraph V) (A : V → V → Prop) (x y : V) :
    Reachable (componentGraph K A) (componentArc K A) (component K A x) (component K A y) ↔
      Reachable K A x y := by
  constructor
  · rintro ⟨p,hp⟩
    exact lift_component_walk K A p hp x y rfl rfl
  · exact project_reachable K A

/-- Reachability on components is antisymmetric. -/
theorem component_reachable_antisymm (K : SimpleGraph V) (A : V → V → Prop)
    (c d : Component K A)
    (h : Reachable (componentGraph K A) (componentArc K A) c d)
    (h' : Reachable (componentGraph K A) (componentArc K A) d c) : c = d := by
  have hc : component K A c.out = c := Quotient.out_eq c
  have hd : component K A d.out = d := Quotient.out_eq d
  have hxy : Reachable K A c.out d.out := by
    obtain ⟨p,hp⟩ := h
    exact lift_component_walk K A p hp _ _ hc hd
  have hyx : Reachable K A d.out c.out := by
    obtain ⟨p,hp⟩ := h'
    exact lift_component_walk K A p hp _ _ hd hc
  exact hc.symm.trans (((component_eq_iff K A _ _).mpr ⟨hxy,hyx⟩).trans hd)

/-- Quotient acyclicity is proved on actual quotient input arcs. -/
theorem component_acyclic (K : SimpleGraph V) (A : V → V → Prop) :
    SelectedAcyclic (componentGraph K A) (inputArcs (componentGraph K A) (componentArc K A)) := by
  intro c p hp
  have ha : Allowed (componentArc K A) p := fun e he => (mem_filter.mp (hp e he)).2.2
  cases p with
  | nil => simp
  | @cons c z c hcz p =>
    have hfirst := ha ⟨(c,z),hcz⟩ (by simp)
    have htail : Reachable (componentGraph K A) (componentArc K A) z c :=
      ⟨p,fun e he => ha e (by simp [he])⟩
    have hstep : Reachable (componentGraph K A) (componentArc K A) c z :=
      ⟨Walk.cons hcz Walk.nil,by simpa [Allowed] using hfirst⟩
    exact (hfirst.1 (component_reachable_antisymm K A c z hstep htail)).elim

/-- Every vertex of an allowed path between SCC-equivalent endpoints stays
in that SCC. No restricted-path/global-distance identification is used. -/
theorem support_same_component (K : SimpleGraph V) (A : V → V → Prop)
    {x y : V} (p : K.Walk x y) (hp : Allowed A p)
    (hxy : component K A x = component K A y) {z : V} (hz : z ∈ p.support) :
    component K A z = component K A x := by
  have hparts := (allowed_append A _ _).mp (show Allowed A
    ((p.takeUntil z hz).append (p.dropUntil z hz)) by rw [Walk.take_spec]; exact hp)
  have hxz : Reachable K A x z := ⟨_,hparts.1⟩
  have hzy : Reachable K A z y := ⟨_,hparts.2⟩
  have hyx := ((component_eq_iff K A x y).mp hxy).2
  exact (component_eq_iff K A z x).mpr ⟨reachable_trans hzy hyx,hxz⟩

/-- Source and demand images are deduplicated, with no cardinality increase. -/
theorem component_demand_images (K : SimpleGraph V) (A : V → V → Prop)
    (S : Finset V) (P : Finset (V × V)) (hs : ∀ st ∈ P, st.1 ∈ S) :
    (S.image (component K A)).card ≤ S.card ∧
    (P.image (fun st => (component K A st.1,component K A st.2))).card ≤ P.card ∧
    ∀ cd ∈ P.image (fun st => (component K A st.1,component K A st.2)),
      cd.1 ∈ S.image (component K A) := by
  refine ⟨card_image_le,card_image_le,?_⟩
  intro cd hcd
  obtain ⟨st,hst,rfl⟩ := mem_image.mp hcd
  exact mem_image.mpr ⟨st.1,hs st hst,rfl⟩

end SlackSparsification.Directed
