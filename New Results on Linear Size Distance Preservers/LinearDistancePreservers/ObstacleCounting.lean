import LinearDistancePreservers.LayeredWalks
import LinearDistancePreservers.PreserverForcing
import Mathlib.Data.Sym.Sym2

/-! The finite graph and exact counts for the obstacle product of Section
4.1. A middle vertex b is replaced by a disjoint copy of the inner graph;
path j determines both ports. The assumptions express edge-disjointness
of the outer and inner path systems, not a distance-preserver bound.
The metric uniqueness of the substituted paths is a separate obligation. -/
namespace LinearDistancePreservers.ObstacleProduct
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

structure Data (A B C U J : Type*) (k : ℕ) where
  left : B → J → A
  right : B → J → C
  inner : J → Fin (k+1) → U
  layer : U → ℕ
  inner_layer : ∀ j i, layer (inner j i) = i.val
  left_injective : ∀ b, Function.Injective (left b)
  right_injective : ∀ b, Function.Injective (right b)
  inner_arc_injective : Function.Injective
    (fun e : Fin k × J => (inner e.2 e.1.castSucc, inner e.2 e.1.succ))

abbrev Vertex (A B C U : Type*) := A ⊕ ((B × U) ⊕ C)
abbrev EdgeIndex (B J : Type*) (k : ℕ) := (B × J) ⊕ ((B × (Fin k × J)) ⊕ (B × J))

variable {A B C U J : Type*} {k : ℕ} (D : Data A B C U J k)

def arc : EdgeIndex B J k → Vertex A B C U × Vertex A B C U
  | .inl (b,j) => (.inl (D.left b j), .inr (.inl (b,D.inner j 0)))
  | .inr (.inl (b,i,j)) =>
      (.inr (.inl (b,D.inner j i.castSucc)), .inr (.inl (b,D.inner j i.succ)))
  | .inr (.inr (b,j)) => (.inr (.inl (b,D.inner j (Fin.last k))), .inr (.inr (D.right b j)))

def layer : Vertex A B C U → ℕ
  | .inl _ => 0
  | .inr (.inl (_,u)) => D.layer u + 1
  | .inr (.inr _) => k + 2

theorem arc_layer (e : EdgeIndex B J k) :
    layer D (arc D e).2 = layer D (arc D e).1 + 1 := by
  rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;> simp [arc, layer, D.inner_layer]

theorem arc_injective : Function.Injective (arc D) := by
  intro e f h
  rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;>
    rcases f with ⟨b',j'⟩ | (⟨b',i',j'⟩ | ⟨b',j'⟩) <;>
    simp only [arc, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, and_false] at h
  · obtain ⟨hl, hb, hi⟩ := h
    subst b'
    have := D.left_injective b hl
    subst j'
    rfl
  · obtain ⟨⟨hb, hi⟩, hb', hi'⟩ := h
    subst b'
    have hp : (i,j) = (i',j') := D.inner_arc_injective (Prod.ext hi hi')
    have hiq := congrArg Prod.fst hp
    have hjq := congrArg Prod.snd hp
    dsimp at hiq hjq
    subst i'
    subst j'
    rfl
  · obtain ⟨⟨hb, hi⟩, hr⟩ := h
    subst b'
    have := D.right_injective b hr
    subst j'
    rfl

theorem arc_ne_swap (e f : EdgeIndex B J k) : arc D e ≠ (arc D f).swap := by
  intro h
  have h1 := congrArg (fun a => layer D a.1) h
  have h2 := congrArg (fun a => layer D a.2) h
  have he := arc_layer D e
  have hf := arc_layer D f
  simp only [Prod.fst_swap, Prod.snd_swap] at h1 h2
  omega

def edge (e : EdgeIndex B J k) : Sym2 (Vertex A B C U) :=
  s((arc D e).1, (arc D e).2)

theorem edge_injective : Function.Injective (edge D) := by
  intro e f h
  rcases Sym2.mk_eq_mk_iff.mp h with h | h
  · exact arc_injective D h
  · exact False.elim (arc_ne_swap D e f h)

def graph : SimpleGraph (Vertex A B C U) where
  Adj u v := ∃ e : EdgeIndex B J k, arc D e = (u,v) ∨ arc D e = (v,u)
  symm := ⟨by rintro u v ⟨e,h⟩; exact ⟨e,h.symm⟩⟩
  loopless := ⟨by
    rintro v ⟨e,h | h⟩ <;> have he := arc_layer D e <;> simp [h] at he⟩

theorem graph_layered : LayeredWalks.Layered (graph D) (fun v => (layer D v : ℤ)) := by
  rintro u v ⟨e,h | h⟩
  · have he := arc_layer D e
    rw [h] at he
    exact Or.inl (by dsimp at he ⊢; omega)
  · have he := arc_layer D e
    rw [h] at he
    exact Or.inr (by dsimp at he ⊢; omega)

theorem arc_adj (e : EdgeIndex B J k) : (graph D).Adj (arc D e).1 (arc D e).2 :=
  ⟨e, Or.inl rfl⟩

theorem left_adj (b : B) (j : J) :
    (graph D).Adj (.inl (D.left b j)) (.inr (.inl (b,D.inner j 0))) :=
  arc_adj D (.inl (b,j))

theorem right_adj (b : B) (j : J) :
    (graph D).Adj (.inr (.inl (b,D.inner j (Fin.last k)))) (.inr (.inr (D.right b j))) :=
  arc_adj D (.inr (.inr (b,j)))

/-- The entire designated inner path inside copy b. -/
def innerWalk (b : B) (j : J) :
    (graph D).Walk (.inr (.inl (b,D.inner j 0)))
      (.inr (.inl (b,D.inner j (Fin.last k)))) :=
  walkOfSequence (G := graph D) (fun i => (.inr (.inl (b,D.inner j i)) : Vertex A B C U))
    (fun i => arc_adj D (.inr (.inl (b,i,j))))

/-- Actual substituted native path: left connector, inner route, right
connector. No route existence is supplied as a hypothesis. -/
def fullWalk (b : B) (j : J) :
    (graph D).Walk (.inl (D.left b j)) (.inr (.inr (D.right b j))) :=
  .cons (left_adj D b j) ((innerWalk D b j).concat (right_adj D b j))

@[simp] theorem innerWalk_length (b : B) (j : J) : (innerWalk D b j).length = k :=
  length_walkOfSequence _ _

@[simp] theorem fullWalk_length (b : B) (j : J) : (fullWalk D b j).length = k+2 := by
  have hc := SimpleGraph.Walk.length_concat (innerWalk D b j)
    (right_adj D b j)
  change ((innerWalk D b j).concat (right_adj D b j)).length + 1 = k+2
  rw [hc, innerWalk_length]

theorem fullWalk_tight (b : B) (j : J) :
    (layer D (.inr (.inr (D.right b j))) : ℤ) - layer D (.inl (D.left b j)) =
      ((fullWalk D b j).length : ℤ) := by
  simp [layer]

/-- Every designated substituted route is shortest in the unweighted graph.
Uniqueness is deliberately not asserted here: it still requires the perfect
path hypotheses on the outer and inner input graphs. -/
theorem fullWalk_shortest (b : B) (j : J)
    (q : (graph D).Walk (.inl (D.left b j)) (.inr (.inr (D.right b j)))) :
    (fullWalk D b j).length ≤ q.length := by
  have h := LayeredWalks.layer_le_length (fun v => (layer D v : ℤ)) (graph_layered D) q
  rw [fullWalk_tight D b j] at h
  exact_mod_cast h

theorem innerWalk_getVert (b : B) (j : J) (i : Fin (k+1)) :
    (innerWalk D b j).getVert i.val = .inr (.inl (b,D.inner j i)) := by
  have hsup : (innerWalk D b j).support =
      List.ofFn (fun i => (.inr (.inl (b,D.inner j i)) : Vertex A B C U)) :=
    support_walkOfSequence _ _
  simpa only [hsup, List.getElem_ofFn] using
    (innerWalk D b j).getVert_eq_support_getElem (show i.val ≤ (innerWalk D b j).length by simp; omega)

theorem inner_edge_mem (b : B) (j : J) (i : Fin k) :
    edge D (.inr (.inl (b,i,j))) ∈ (innerWalk D b j).edges := by
  apply (innerWalk D b j).mk_mem_edges_iff_exists.mpr
  refine ⟨i.val, by simpa using i.isLt, ?_⟩
  dsimp [edge, arc]
  rw [show (innerWalk D b j).getVert i.val = .inr (.inl (b,D.inner j i.castSucc)) from
    innerWalk_getVert D b j i.castSucc,
    show (innerWalk D b j).getVert (i.val+1) = .inr (.inl (b,D.inner j i.succ)) from
    innerWalk_getVert D b j i.succ]

theorem indexed_edge_covered (e : EdgeIndex B J k) :
    ∃ b j, edge D e ∈ (fullWalk D b j).edges := by
  rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩)
  · exact ⟨b,j, by simp [fullWalk, SimpleGraph.Walk.edges_cons, edge, arc]⟩
  · refine ⟨b,j, ?_⟩
    have hi := inner_edge_mem D b j i
    have hc := SimpleGraph.Walk.edges_concat (innerWalk D b j)
      (right_adj D b j)
    simp only [fullWalk, SimpleGraph.Walk.edges_cons, List.mem_cons]
    apply Or.inr
    rw [hc]
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton]
    exact Or.inl hi
  · exact ⟨b,j, by simp [fullWalk, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.concat, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_nil, edge, arc]⟩

variable [Fintype A] [Fintype B] [Fintype C] [Fintype U] [Fintype J]

theorem vertex_count : Fintype.card (Vertex A B C U) =
    Fintype.card A + Fintype.card B * Fintype.card U + Fintype.card C := by
  simp [Vertex, add_assoc]

theorem graph_edgeFinset : (graph D).edgeFinset = univ.image (edge D) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf u v =>
    simp only [mem_edgeFinset, mem_edgeSet, graph, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, Sym2.mk_eq_mk_iff.mpr hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Sym2.mk_eq_mk_iff.mp hi⟩

/-- Two connector edges per outer path, and k inner edges per path, with
no duplicate undirected edges. Every copy of the inner graph is counted. -/
theorem edge_count : (graph D).edgeFinset.card =
    Fintype.card B * Fintype.card J * (k+2) := by
  classical
  rw [graph_edgeFinset, card_image_of_injective _ (edge_injective D), card_univ]
  simp [EdgeIndex]
  ring

/-- Exact remaining metric input exposed as a hypothesis. Once uniqueness
of the substituted routes is established, every preserver of their endpoint
distances has the counted number of edges. This is not Lemma 7 itself. -/
theorem preserver_edge_count_of_unique
    (hunique : ∀ b j (q : (graph D).Walk (.inl (D.left b j)) (.inr (.inr (D.right b j)))),
      q.length ≤ k+2 → q = fullWalk D b j)
    (H : SimpleGraph (Vertex A B C U)) (hsub : H ≤ graph D)
    (hpres : ∀ b j, H.edist (.inl (D.left b j)) (.inr (.inr (D.right b j))) =
      (graph D).edist (.inl (D.left b j)) (.inr (.inr (D.right b j)))) :
    H.edgeFinset.card = Fintype.card B * Fintype.card J * (k+2) := by
  classical
  have hcover : ∀ e ∈ (graph D).edgeSet,
      ∃ p : B × J, e ∈ (fullWalk D p.1 p.2).edges := by
    intro e he
    have hf : e ∈ (graph D).edgeFinset := by simpa using he
    rw [graph_edgeFinset] at hf
    obtain ⟨i, _, rfl⟩ := mem_image.mp hf
    obtain ⟨b,j,hbj⟩ := indexed_edge_covered D i
    exact ⟨(b,j), hbj⟩
  have heq := UnweightedForcing.eq_of_covers
    (fun p : B × J => (.inl (D.left p.1 p.2) : Vertex A B C U))
    (fun p : B × J => (.inr (.inr (D.right p.1 p.2)) : Vertex A B C U))
    (fun p => fullWalk D p.1 p.2)
    (fun p q hq => hunique p.1 p.2 q (by simpa using hq))
    hcover hsub (fun p => hpres p.1 p.2)
  rw [heq]
  exact edge_count D

end LinearDistancePreservers.ObstacleProduct
