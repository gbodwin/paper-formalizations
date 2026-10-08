import LinearDistancePreservers.DirectionPerfect
import LinearDistancePreservers.ConvexRigidity
import LinearDistancePreservers.ObstacleWalks

/-! Concrete unweighted obstacle products from two vector families.
The outer directions are indexed by the inner canonical paths, making
port capacity explicit. Both path-uniqueness hypotheses are proved from
bounded convex-position directions; no graph uniqueness is assumed.
Sharp direction-set existence and global parameter selection remain
separate from this exact finite construction. -/
namespace LinearDistancePreservers.DirectionObstacle
open SimpleGraph Finset DirectionGraph
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {D Q J : Type*} {n M k r R : ℕ}

abbrev Port (D J : Type*) (n : ℕ) := (D → ZMod n) × J

def castVector (v : J → D → ℕ) (a : J) : D → ZMod n := fun d => (v a d : ZMod n)

theorem castVector_injective (v : J → D → ℕ) (hv : ∀ a d, v a d < n)
    (hinj : Function.Injective v) : Function.Injective (castVector (n := n) v) := by
  intro a b h
  apply hinj
  funext d
  have hh := congrArg ZMod.val (congrFun h d)
  simpa only [castVector,ZMod.val_natCast_of_lt (hv a d),ZMod.val_natCast_of_lt (hv b d)] using hh

def data (v : J → D → ℕ) (z : Port D J n → Q → ℕ)
    (hv : ∀ a d, v a d < n) (hinj : Function.Injective v)
    (hz : ∀ a d, z a d < M) (hzinj : Function.Injective z) :
    ObstacleProduct.Data (Q → ZMod M) (Q → ZMod M) (Q → ZMod M)
      (DirectionGraph.Vertex D n k) (Port D J n) k where
  left b p := b - castVector z p
  right b p := b + castVector z p
  inner p := point v p.1 p.2
  layer u := u.1.val
  inner_layer _ _ := rfl
  left_injective b := fun _ _ h => castVector_injective z hz hzinj (sub_right_inj.mp h)
  right_injective b := fun _ _ h => castVector_injective z hz hzinj (add_left_cancel h)
  inner_arc_injective := DirectionGraph.arc_injective v hv hinj

variable (v : J → D → ℕ) (z : Port D J n → Q → ℕ)
  (hv : ∀ a d, v a d < n) (hinj : Function.Injective v)
  (hz : ∀ a d, z a d < M) (hzinj : Function.Injective z)

/-- Average rigidity of the outer vectors forces the same copy and port
on any competing two-connector route. -/
theorem outer_unique (hzR : ∀ a d, z a d < R) (hM : 3*R ≤ M) (hc : AverageRigid z) :
    ObstacleProduct.OuterUnique (data (k := k) v z hv hinj hz hzinj) := by
  intro b j b' j₁ j₂ hl hr
  let f : Fin 2 → Port D J n := ![j₁,j₂]
  have he (d : Q) : ∑ i, (z (f i) d : ZMod M) = (2 : ZMod M)*(z j d : ZMod M) := by
    have hl' := congrFun hl d
    have hr' := congrFun hr d
    change b' d - (z j₁ d : ZMod M) = b d - (z j d : ZMod M) at hl'
    change b' d + (z j₂ d : ZMod M) = b d + (z j d : ZMod M) at hr'
    simp only [f,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
    linear_combination hr' - hl'
  have hc' := hc 2 j f (ConvexDirections.no_wrap_sum (fun i => z (f i)) (z j)
    (fun i => hzR (f i)) (hzR j) hM he)
  have h1 : j₁ = j := hzinj (by simpa [f] using hc' 0)
  have h2 : j₂ = j := hzinj (by simpa [f] using hc' 1)
  subst j₁ j₂
  exact ⟨sub_left_inj.mp hl,rfl,rfl⟩

def innerHom : ObstacleProduct.innerGraph (data (k := k) v z hv hinj hz hzinj) →g
    DirectionGraph.graph v n k where
  toFun := id
  map_rel' := by
    rintro u w ⟨i,j,h⟩
    apply (DirectionGraph.adj_iff_arc v u w).mpr
    exact ⟨(i,j),by simpa only [DirectionGraph.arc,Prod.mk.injEq,data] using h⟩

/-- Inner native-walk uniqueness, discharged by the vector construction. -/
theorem inner_unique (hvr : ∀ a d, v a d < r) (hn : (k+1)*r ≤ n) (hc : AverageRigid v) :
    ObstacleProduct.InnerUnique (data (k := k) v z hv hinj hz hzinj) := by
  intro j w hw
  have hw' : (w.map (innerHom v z hv hinj hz hzinj)).length ≤ k :=
    (Walk.length_map (innerHom v z hv hinj hz hzinj) w).le.trans hw
  have hu := DirectionGraph.canonical_unique v hvr hn hc j.1 j.2
    (w.map (innerHom v z hv hinj hz hzinj)) hw'
  have he : (w.map (innerHom v z hv hinj hz hzinj)).support = List.ofFn (point v j.1 j.2) :=
    (congrArg (fun q : (DirectionGraph.graph v n k).Walk (point v j.1 j.2 0)
      (point v j.1 j.2 (Fin.last k)) => q.support) hu).trans (canonical_support v j.1 j.2)
  apply Walk.ext_support
  simpa [Walk.support_map,innerHom,ObstacleProduct.innerRoute_support,data] using he

variable [Fintype D] [Fintype Q] [Fintype J] [NeZero n] [NeZero M]

/-- Exact size of the graph resulting from substitution. -/
theorem vertex_count :
    Fintype.card (ObstacleProduct.Vertex (Q → ZMod M) (Q → ZMod M) (Q → ZMod M)
      (DirectionGraph.Vertex D n k)) =
      2*M^(Fintype.card Q) + M^(Fintype.card Q)*(k+1)*n^(Fintype.card D) := by
  simp [ObstacleProduct.Vertex,DirectionGraph.Vertex,ZMod.card]
  ring

/-- Finite Theorem 4 construction from convex-position direction sets.
Every preserving subgraph keeps all edges. The outer directions must be
indexed injectively by the n^d |J| inner paths; their existence is explicit
input, not replaced by an assumed cardinality or a uniqueness axiom. -/
theorem preserver_edge_count
    (hvr : ∀ a d, v a d < r) (hn : (k+1)*r ≤ n) (hcv : ConvexPosition v)
    (hzR : ∀ a d, z a d < R) (hM : 3*R ≤ M) (hcz : ConvexPosition z)
    (H : SimpleGraph (ObstacleProduct.Vertex (Q → ZMod M) (Q → ZMod M) (Q → ZMod M)
      (DirectionGraph.Vertex D n k)))
    (hH : H ≤ ObstacleProduct.graph (data (k := k) v z hv hinj hz hzinj))
    (hp : ∀ b j,
      H.edist (.inl ((data (k := k) v z hv hinj hz hzinj).left b j))
        (.inr (.inr ((data (k := k) v z hv hinj hz hzinj).right b j))) =
      (ObstacleProduct.graph (data (k := k) v z hv hinj hz hzinj)).edist
        (.inl ((data (k := k) v z hv hinj hz hzinj).left b j))
        (.inr (.inr ((data (k := k) v z hv hinj hz hzinj).right b j)))) :
    H.edgeFinset.card = M^(Fintype.card Q)*n^(Fintype.card D)*Fintype.card J*(k+2) := by
  have h := ObstacleProduct.preserver_edge_count (data (k := k) v z hv hinj hz hzinj)
    (outer_unique v z hv hinj hz hzinj hzR hM (convexPosition_rigid z hcz))
    (inner_unique v z hv hinj hz hzinj hvr hn (convexPosition_rigid v hcv)) H hH hp
  simpa [Port,ZMod.card,mul_assoc] using h

abbrev ProductVertex (D Q : Type*) (n M k : ℕ) :=
  ObstacleProduct.Vertex (Q → ZMod M) (Q → ZMod M) (Q → ZMod M) (DirectionGraph.Vertex D n k)

def boundary : (Q → ZMod M) ⊕ (Q → ZMod M) → ProductVertex D Q n M k
  | .inl a => .inl a
  | .inr c => .inr (.inr c)

theorem boundary_injective : Function.Injective (boundary (D := D) (Q := Q) (n := n) (M := M) (k := k)) := by
  rintro (a | c) (a' | c') h <;> simp_all [boundary]

noncomputable def terminals : Finset (ProductVertex D Q n M k) := univ.image boundary

theorem terminals_card : (terminals (D := D) (Q := Q) (n := n) (M := M) (k := k)).card =
    2*M^(Fintype.card Q) := by
  rw [terminals,card_image_of_injective _ boundary_injective,card_univ]
  simp [ZMod.card,two_mul]

theorem left_mem_terminals (a : Q → ZMod M) :
    (.inl a : ProductVertex D Q n M k) ∈ terminals := mem_image.mpr ⟨.inl a,mem_univ _,rfl⟩

theorem right_mem_terminals (c : Q → ZMod M) :
    (.inr (.inr c) : ProductVertex D Q n M k) ∈ terminals := mem_image.mpr ⟨.inr c,mem_univ _,rfl⟩

/-- The actual S×S subset-distance-preserver consequence, with exactly
2 M^|Q| terminals. The direction families, bounds, and convexity are still
explicit geometric inputs; this is not the final asymptotic Theorem 4. -/
theorem subset_preserver_edge_count
    (hvr : ∀ a d, v a d < r) (hn : (k+1)*r ≤ n) (hcv : ConvexPosition v)
    (hzR : ∀ a d, z a d < R) (hM : 3*R ≤ M) (hcz : ConvexPosition z)
    (H : SimpleGraph (ProductVertex D Q n M k))
    (hH : H ≤ ObstacleProduct.graph (data (k := k) v z hv hinj hz hzinj))
    (hp : ∀ s ∈ terminals (D := D) (Q := Q) (n := n) (M := M) (k := k), ∀ t ∈ terminals,
      H.edist s t = (ObstacleProduct.graph (data (k := k) v z hv hinj hz hzinj)).edist s t) :
    H.edgeFinset.card = M^(Fintype.card Q)*n^(Fintype.card D)*Fintype.card J*(k+2) := by
  apply preserver_edge_count v z hv hinj hz hzinj hvr hn hcv hzR hM hcz H hH
  intro b j
  exact hp _ (left_mem_terminals _) _ (right_mem_terminals _)

end LinearDistancePreservers.DirectionObstacle
