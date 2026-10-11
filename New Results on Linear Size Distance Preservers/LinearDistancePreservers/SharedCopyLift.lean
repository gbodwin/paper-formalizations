import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! A positive shared-copy lifting construction. Outer edges may belong to
many terminal routes, and the input need not have unique shortest paths. -/
namespace LinearDistancePreservers.SharedCopyLift
open SimpleGraph
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

variable {V A B C D : Type*}

abbrev Vertex (V A B C D : Type*) := (A × B) ⊕ ((B × C) × V) ⊕ (C × D)

@[reducible] def adj (F : SimpleGraph V) (left : A → V) (right : D → V) :
    Vertex V A B C D → Vertex V A B C D → Prop
  | .inl (a,b), .inr (.inl ((b',_),v)) => b=b' ∧ v=left a
  | .inr (.inl ((b',_),v)), .inl (a,b) => b=b' ∧ v=left a
  | .inr (.inl (bc,u)), .inr (.inl (bc',v)) => bc=bc' ∧ F.Adj u v
  | .inr (.inl ((_,c),v)), .inr (.inr (c',d)) => c=c' ∧ v=right d
  | .inr (.inr (c',d)), .inr (.inl ((_,c),v)) => c=c' ∧ v=right d
  | _, _ => False

@[reducible] def graph (F : SimpleGraph V) (left : A → V) (right : D → V) :
    SimpleGraph (Vertex V A B C D) where
  Adj := adj F left right
  symm := ⟨by
    intro u v h
    rcases u with ⟨a,b⟩ | (⟨⟨b,c⟩,u⟩ | ⟨c,d⟩) <;>
      rcases v with ⟨a',b'⟩ | (⟨⟨b',c'⟩,v⟩ | ⟨c',d'⟩) <;>
      simp only [adj] at h ⊢
    all_goals first | exact h | exact ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by
    intro u
    rcases u with ⟨a,b⟩ | (⟨bc,u⟩ | ⟨c,d⟩) <;> simp [adj]⟩

variable (F : SimpleGraph V) (left : A → V) (right : D → V)

def project : Vertex V A B C D → V
  | .inl (a,_) => left a
  | .inr (.inl (_,v)) => v
  | .inr (.inr (_,d)) => right d

def connector : Vertex V A B C D → Vertex V A B C D → ℕ
  | .inr (.inl _), .inr (.inl _) => 0
  | _, _ => 1

def coarse : Vertex V A B C D → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def connectors {H : SimpleGraph (Vertex V A B C D)} {s t} : H.Walk s t → ℕ
  | .nil => 0
  | .cons (v := u) _ p => connector s u + connectors p

@[simp] lemma connectors_cons {H : SimpleGraph (Vertex V A B C D)} {s u t}
    (h : H.Adj s u) (p : H.Walk u t) :
    connectors (.cons h p) = connector s u + connectors p := rfl

lemma coarse_step {s t : Vertex V A B C D}
    (h : (graph F left right).Adj s t) :
    (coarse t : ℤ)-coarse s ≤ connector s t := by
  rcases s with ⟨a,b⟩ | (⟨bc,u⟩ | ⟨c,d⟩) <;>
    rcases t with ⟨a',b'⟩ | (⟨bc',v⟩ | ⟨c',d'⟩) <;>
    simp_all [adj,coarse,connector]

lemma coarse_le_connectors {H : SimpleGraph (Vertex V A B C D)}
    (hH : H ≤ graph F left right) {s t} (p : H.Walk s t) :
    (coarse t : ℤ)-coarse s ≤ connectors p := by
  induction p with
  | nil => simp [connectors]
  | cons h p ih =>
    have hs := coarse_step F left right (hH h)
    rw [connectors_cons,Nat.cast_add]
    omega

lemma step_cases {s t : Vertex V A B C D}
    (h : (graph F left right).Adj s t) :
    (connector s t=1 ∧ project left right s=project left right t) ∨
      (connector s t=0 ∧ F.Adj (project left right s) (project left right t)) := by
  rcases s with ⟨a,b⟩ | (⟨⟨b,c⟩,u⟩ | ⟨c,d⟩) <;>
    rcases t with ⟨a',b'⟩ | (⟨⟨b',c'⟩,v⟩ | ⟨c',d'⟩) <;>
    simp only [adj] at h
  all_goals first
    | contradiction
    | (left; simp only [project,connector,true_and]; exact h.2)
    | (left; simp only [project,connector,true_and]; exact h.2.symm)
    | (right; exact ⟨rfl,h.2⟩)

/-- Contracting every connector projects an arbitrary walk to a genuine
input walk. Its exact length counts only the within-copy steps. -/
lemma project_walk {H : SimpleGraph (Vertex V A B C D)}
    (hH : H ≤ graph F left right) {s t} (p : H.Walk s t) :
    ∃ w : F.Walk (project left right s) (project left right t),
      w.length+connectors p=p.length := by
  induction p with
  | nil => exact ⟨.nil,rfl⟩
  | cons h p ih =>
    obtain ⟨w,hw⟩ := ih
    rcases step_cases F left right (hH h) with ⟨hc,he⟩ | ⟨hc,he⟩
    · refine ⟨w.copy he.symm rfl,?_⟩
      simp only [Walk.length_copy,connectors_cons,hc,Walk.length_cons]
      omega
    · refine ⟨.cons he w,?_⟩
      simp only [connectors_cons,hc,zero_add,Walk.length_cons]
      omega

/-- Projection charges only inner edges. This holds for arbitrary walks,
including excursions, and also for disconnected input graphs. -/
lemma walk_budget {H : SimpleGraph (Vertex V A B C D)}
    (hH : H ≤ graph F left right) {s t} (p : H.Walk s t) :
    F.dist (project left right s) (project left right t) + connectors p ≤ p.length := by
  obtain ⟨w,hw⟩ := project_walk F left right hH p
  have hd := F.dist_le w
  omega

/-- Every copy embeds as an actual subgraph. -/
@[reducible] def embed (bc : B × C) : F →g graph F left right (B := B) (C := C) where
  toFun v := .inr (.inl (bc,v))
  map_rel' h := ⟨rfl,h⟩

/-- Lift any input walk through its designated copy with exactly two connectors. -/
def liftWalk (a : A) (b : B) (c : C) (d : D)
    (p : F.Walk (left a) (right d)) :
    (graph F left right).Walk (.inl (a,b)) (.inr (.inr (c,d))) :=
by
  have h1 : (graph F left right).Adj (.inl (a,b))
      (.inr (.inl ((b,c),left a))) := ⟨rfl,rfl⟩
  have h2 : (graph F left right).Adj (.inr (.inl ((b,c),right d)))
      (.inr (.inr (c,d))) := ⟨rfl,rfl⟩
  exact .cons h1 ((p.map (embed F left right (b,c))).append h2.toWalk)

@[simp] lemma liftWalk_length (a : A) (b : B) (c : C) (d : D)
    (p : F.Walk (left a) (right d)) :
    (liftWalk F left right a b c d p).length = p.length+2 := by
  unfold liftWalk
  rw [Walk.length_cons,Walk.length_append,Walk.length_map,Adj.length_toWalk]

/-- Exact native cross-terminal distances. Arbitrarily many critical paths
may share outer edges; no outer or inner uniqueness premise is needed. -/
theorem cross_edist_of_reachable (a : A) (b : B) (c : C) (d : D)
    (hF : F.Reachable (left a) (right d)) :
    (graph F left right (B := B) (C := C)).edist (.inl (a,b)) (.inr (.inr (c,d))) =
      (F.dist (left a) (right d)+2 : ℕ) := by
  obtain ⟨p,hp⟩ := hF.exists_walk_length_eq_dist
  have hr := (liftWalk F left right a b c d p).reachable
  obtain ⟨q,hq⟩ := hr.exists_walk_length_eq_edist
  have hlo := walk_budget F left right le_rfl q
  have hc := coarse_le_connectors F left right le_rfl q
  simp only [project] at hlo
  simp only [coarse,Nat.cast_ofNat,Nat.cast_zero,sub_zero] at hc
  have htwo : 2 ≤ connectors q := by omega
  have hl : F.dist (left a) (right d)+2 ≤ q.length := by omega
  have hu := (graph F left right).edist_le (liftWalk F left right a b c d p)
  rw [liftWalk_length,hp] at hu
  exact le_antisymm hu (by rw [← hq]; exact_mod_cast hl)

/-- The actual subgraph retained inside one designated copy. -/
def copyGraph (H : SimpleGraph (Vertex V A B C D)) (bc : B × C) : SimpleGraph V where
  Adj u v := H.Adj (.inr (.inl (bc,u))) (.inr (.inl (bc,v)))
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => H.irrefl h⟩

lemma copyGraph_le {H : SimpleGraph (Vertex V A B C D)}
    (hH : H ≤ graph F left right) (bc : B × C) : copyGraph H bc ≤ F := by
  intro u v h
  exact (hH h).2

lemma factor_middle_right {H : SimpleGraph (Vertex V A B C D)}
    (hH : H ≤ graph F left right) {b : B} {c c' : C} {u : V} {d : D}
    (q : H.Walk (.inr (.inl ((b,c),u))) (.inr (.inr (c',d))))
    (hq : connectors q ≤ 1) :
    c=c' ∧ ∃ w : (copyGraph H (b,c)).Walk u (right d), q.length=w.length+1 := by
  generalize hm : q.length = m
  induction m using Nat.strong_induction_on generalizing b c u with
  | h m ih =>
    cases q with
    | cons hadj p =>
      rename_i v
      rcases v with ⟨a',b'⟩ | (⟨⟨b',c''⟩,v⟩ | ⟨c'',d'⟩)
      · have hlo := coarse_le_connectors F left right hH p
        simp only [connectors_cons,connector] at hq
        simp only [coarse,Nat.cast_ofNat,Nat.cast_zero,sub_zero] at hlo
        omega
      · have hbc := (hH hadj).1
        change (b,c)=(b',c'') at hbc
        rcases Prod.mk.inj hbc with ⟨rfl,rfl⟩
        have hp : connectors p ≤ 1 := by simpa [connectors,connector] using hq
        obtain ⟨hc,w,hw⟩ := ih p.length (by simp only [Walk.length_cons] at hm; omega)
          p hp rfl
        refine ⟨hc,.cons hadj w,?_⟩
        simp only [Walk.length_cons] at hm ⊢
        omega
      · have hp : connectors p=0 := by
          simp only [connectors_cons,connector] at hq
          omega
        cases p with
        | cons h p => simp [connectors,connector] at hp
        | nil =>
          have hh := hH hadj
          change c=c' ∧ u=right d at hh
          refine ⟨hh.1,?_⟩
          rcases hh.2 with rfl
          exact ⟨.nil,by simpa using hm.symm⟩

/-- Two connectors determine the entire copy from the two outer terminal
indices, without any restriction on the inner shortest-path multiplicity. -/
lemma factor_cross {H : SimpleGraph (Vertex V A B C D)}
    (hH : H ≤ graph F left right) {a : A} {b : B} {c : C} {d : D}
    (q : H.Walk (.inl (a,b)) (.inr (.inr (c,d)))) (hq : connectors q ≤ 2) :
    ∃ w : (copyGraph H (b,c)).Walk (left a) (right d), q.length=w.length+2 := by
  cases q with
  | cons hadj p =>
    rename_i v
    rcases v with ⟨a',b'⟩ | (⟨⟨b',c'⟩,v⟩ | ⟨c',d'⟩)
    · exact False.elim (hH hadj)
    · have hh := hH hadj
      change b=b' ∧ v=left a at hh
      rcases hh with ⟨rfl,rfl⟩
      have hp : connectors p ≤ 1 := by
        simp only [connectors_cons,connector] at hq
        omega
      obtain ⟨rfl,w,hw⟩ := factor_middle_right F left right hH p hp
      exact ⟨w,by simp only [Walk.length_cons]; omega⟩
    · exact False.elim (hH hadj)

/-- Preserving cross-terminal distances in the constructed graph forces
an actual cross-terminal preserver in every inner copy. -/
theorem copy_preserves
    {H : SimpleGraph (Vertex V A B C D)} (hH : H ≤ graph F left right)
    (hp : ∀ a b c d, H.edist (.inl (a,b)) (.inr (.inr (c,d))) =
      (graph F left right).edist (.inl (a,b)) (.inr (.inr (c,d))))
    (a : A) (b : B) (c : C) (d : D) :
    (copyGraph H (b,c)).edist (left a) (right d)=F.edist (left a) (right d) := by
  by_cases hr : F.Reachable (left a) (right d)
  swap
  · have ht := F.edist_eq_top_of_not_reachable hr
    have hle := (copyGraph H (b,c)).edist_anti (u := left a) (v := right d) (copyGraph_le F left right hH (b,c))
    rw [ht] at hle ⊢
    exact top_le_iff.mp hle
  have he : H.edist (.inl (a,b)) (.inr (.inr (c,d))) =
      (F.dist (left a) (right d)+2 : ℕ) := (hp a b c d).trans (cross_edist_of_reachable F left right a b c d hr)
  obtain ⟨q,hq⟩ := H.exists_walk_of_edist_eq_coe he
  have hb := walk_budget F left right hH q
  simp only [project] at hb
  have hc : connectors q ≤ 2 := by omega
  obtain ⟨w,hw⟩ := factor_cross F left right hH q hc
  have hl : w.length=F.dist (left a) (right d) := by omega
  apply le_antisymm
  · have hh := (copyGraph H (b,c)).edist_le w
    rw [hl,hr.coe_dist_eq_edist] at hh
    exact hh
  · exact (copyGraph H (b,c)).edist_anti (copyGraph_le F left right hH (b,c))

/-- Exact extended distances, including disconnected input terminal pairs. -/
theorem cross_edist (a : A) (b : B) (c : C) (d : D) :
    (graph F left right (B := B) (C := C)).edist (.inl (a,b)) (.inr (.inr (c,d))) =
      F.edist (left a) (right d)+2 := by
  by_cases hr : F.Reachable (left a) (right d)
  · rw [cross_edist_of_reachable F left right a b c d hr,
      Nat.cast_add,hr.coe_dist_eq_edist]
    rfl
  · have hn : ¬(graph F left right (B := B) (C := C)).Reachable
        (.inl (a,b)) (.inr (.inr (c,d))) := by
      rintro ⟨p⟩
      obtain ⟨w,_⟩ := project_walk F left right le_rfl p
      exact hr w.reachable
    rw [(graph F left right).edist_eq_top_of_not_reachable hn,
      F.edist_eq_top_of_not_reachable hr]
    simp

/-- The tagged outer vertices are all distinct terminals even when input
port maps repeat vertices. -/
def terminalEmbedding : ((A × B) ⊕ (C × D)) ↪ Vertex V A B C D where
  toFun
    | .inl ab => .inl ab
    | .inr cd => .inr (.inr cd)
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

noncomputable def terminals : Finset (Vertex V A B C D) :=
  Finset.univ.map terminalEmbedding

lemma terminals_card : (terminals (V := V) (A := A) (B := B) (C := C) (D := D)).card =
    Fintype.card A*Fintype.card B + Fintype.card C*Fintype.card D := by
  simp [terminals]

lemma left_mem_terminals (a : A) (b : B) :
    (.inl (a,b) : Vertex V A B C D) ∈ terminals :=
  Finset.mem_map.mpr ⟨.inl (a,b),Finset.mem_univ _,rfl⟩

lemma right_mem_terminals (c : C) (d : D) :
    (.inr (.inr (c,d)) : Vertex V A B C D) ∈ terminals :=
  Finset.mem_map.mpr ⟨.inr (c,d),Finset.mem_univ _,rfl⟩

variable [Fintype V]

lemma vertex_card : Fintype.card (Vertex V A B C D) =
    Fintype.card A*Fintype.card B + Fintype.card B*Fintype.card C*Fintype.card V +
      Fintype.card C*Fintype.card D := by
  simp [Vertex,Nat.add_assoc]

/-- Copy edges are genuinely disjoint edges of the output graph, even
though the outer connector edges are shared by many critical routes. -/
lemma sum_copy_edges_le (H : SimpleGraph (Vertex V A B C D)) :
    ∑ bc : B × C, (copyGraph H bc).edgeFinset.card ≤ H.edgeFinset.card := by
  classical
  let emb : (Σ bc : B × C, (copyGraph H bc).Dart) → H.Dart :=
    fun x => ⟨(.inr (.inl (x.1,x.2.fst)),.inr (.inl (x.1,x.2.snd))),x.2.adj⟩
  have hinj : Function.Injective emb := by
    rintro ⟨bc,⟨⟨u,v⟩,h⟩⟩ ⟨bc',⟨⟨u',v'⟩,h'⟩⟩ he
    have hf := congrArg (fun e : H.Dart => e.fst) he
    have hs := congrArg (fun e : H.Dart => e.snd) he
    change (.inr (.inl (bc,u)) : Vertex V A B C D)=.inr (.inl (bc',u')) at hf
    change (.inr (.inl (bc,v)) : Vertex V A B C D)=.inr (.inl (bc',v')) at hs
    simp only [Sum.inr.injEq,Sum.inl.injEq,Prod.mk.injEq] at hf hs
    rcases hf with ⟨rfl,rfl⟩
    rcases hs.2 with rfl
    rfl
  have hh := Fintype.card_le_of_injective emb hinj
  simp only [Fintype.card_sigma,dart_card_eq_twice_card_edges,← Finset.mul_sum] at hh
  omega

/-- Positive finite lifting theorem for arbitrary input cross-terminal
preserver lower bounds. No layeredness, unique shortest paths, edge ownership,
connectedness, or supplied output graph is assumed. -/
theorem preserver_lower_bound {m : ℕ}
    (hbound : ∀ K : SimpleGraph V, K ≤ F →
      (∀ a d, K.edist (left a) (right d)=F.edist (left a) (right d)) →
      m ≤ K.edgeFinset.card)
    (H : SimpleGraph (Vertex V A B C D)) (hH : H ≤ graph F left right)
    (hp : ∀ s∈terminals, ∀ t∈terminals, H.edist s t=(graph F left right).edist s t) :
    Fintype.card B*Fintype.card C*m ≤ H.edgeFinset.card := by
  classical
  have hc (bc : B × C) : m ≤ (copyGraph H bc).edgeFinset.card := by
    apply hbound _ (copyGraph_le F left right hH bc)
    intro a d
    exact copy_preserves F left right hH
      (fun a b c d => hp _ (left_mem_terminals a b) _ (right_mem_terminals c d)) a bc.1 bc.2 d
  have hs := Finset.sum_le_sum (fun bc (_ : bc ∈ (Finset.univ : Finset (B × C))) => hc bc)
  have hh := hs.trans (sum_copy_edges_le H)
  simpa using hh

/-- A concrete subset-preserver transformation with r² copies. For an
n-vertex input and s terminals, the new graph has r²n+2rs vertices and
2rs terminals, and forces at least r²m edges whenever the input forces m.
This preserves a normalized lower bound; it does not claim amplification. -/
theorem subset_lift (F : SimpleGraph V) (S : Finset V) (r m : ℕ)
    (hbound : ∀ K : SimpleGraph V, K ≤ F →
      (∀ s∈S, ∀ t∈S, K.edist s t=F.edist s t) → m ≤ K.edgeFinset.card) :
    let W := Vertex V S (Fin r) (Fin r) S
    Fintype.card W = r^2*Fintype.card V+2*r*S.card ∧
      ∃ (G : SimpleGraph W) (T : Finset W), T.card=2*r*S.card ∧
        ∀ H : SimpleGraph W, H ≤ G →
          (∀ s∈T, ∀ t∈T, H.edist s t=G.edist s t) →
          r^2*m ≤ H.edgeFinset.card := by
  classical
  dsimp only
  have hcard : Fintype.card S=S.card := Fintype.card_coe _
  constructor
  · rw [vertex_card]
    simp only [Fintype.card_fin,hcard]
    ring
  · refine ⟨graph F (fun s : S => s.val) (fun s : S => s.val),terminals,?_,?_⟩
    · rw [terminals_card]
      simp only [Fintype.card_fin,hcard]
      ring
    · intro H hH hp
      have hinput : ∀ K : SimpleGraph V, K ≤ F →
          (∀ a d : S, K.edist a.val d.val=F.edist a.val d.val) → m ≤ K.edgeFinset.card := by
        intro K hK hpres
        exact hbound K hK (fun s hs t ht => hpres ⟨s,hs⟩ ⟨t,ht⟩)
      have hh := preserver_lower_bound F (fun s : S => s.val) (fun s : S => s.val)
        hinput H hH hp
      simpa [pow_two] using hh

end LinearDistancePreservers.SharedCopyLift
