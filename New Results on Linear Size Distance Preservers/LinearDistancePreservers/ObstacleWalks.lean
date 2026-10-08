import LinearDistancePreservers.ObstacleCounting

/-! Walk decomposition in the actual undirected obstacle product. Counting
the connector edges excludes excursions into other copies, independently
of the length or cost of the route within a copy. -/
namespace LinearDistancePreservers.ObstacleProduct
open SimpleGraph
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

variable {A B C U J : Type*} {k : ℕ} (D : Data A B C U J k)

def innerGraph : SimpleGraph U where
  Adj u v := ∃ i : Fin k, ∃ j : J,
    (D.inner j i.castSucc = u ∧ D.inner j i.succ = v) ∨
    (D.inner j i.castSucc = v ∧ D.inner j i.succ = u)
  symm := ⟨by rintro u v ⟨i,j,h⟩; exact ⟨i,j,h.symm⟩⟩
  loopless := ⟨by
    rintro u ⟨i,j,h | h⟩ <;>
      have h1 := congrArg D.layer h.1 <;>
      have h2 := congrArg D.layer h.2 <;>
      simp only [D.inner_layer, Fin.val_castSucc, Fin.val_succ] at h1 h2 <;> omega⟩

theorem left_neighbor {a : A} {v : Vertex A B C U}
    (h : (graph D).Adj (.inl a) v) :
    ∃ b j, a = D.left b j ∧ v = .inr (.inl (b,D.inner j 0)) := by
  rcases h with ⟨e,h | h⟩ <;>
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;>
    simp only [arc, Prod.mk.injEq, Sum.inl.injEq, Sum.inr_ne_inl,
      false_and, and_false] at h
  exact ⟨b,j,h.1.symm,h.2.symm⟩

theorem right_neighbor {c : C} {v : Vertex A B C U}
    (h : (graph D).Adj (.inr (.inr c)) v) :
    ∃ b j, c = D.right b j ∧ v = .inr (.inl (b,D.inner j (Fin.last k))) := by
  rcases h with ⟨e,h | h⟩ <;>
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;>
    simp only [arc, Prod.mk.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
      false_and, and_false] at h
  exact ⟨b,j,h.2.symm,h.1.symm⟩

theorem middle_adj {b b' : B} {u v : U} :
    (graph D).Adj (.inr (.inl (b,u))) (.inr (.inl (b',v))) ↔
      b = b' ∧ (innerGraph D).Adj u v := by
  constructor
  · rintro ⟨e,h | h⟩ <;>
      rcases e with ⟨a,j⟩ | (⟨a,i,j⟩ | ⟨a,j⟩) <;>
      simp only [arc, Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, and_false] at h
    · exact ⟨h.1.1.symm.trans h.2.1, i,j, Or.inl ⟨h.1.2,h.2.2⟩⟩
    · exact ⟨h.2.1.symm.trans h.1.1, i,j, Or.inr ⟨h.1.2,h.2.2⟩⟩
  · rintro ⟨rfl,i,j,h | h⟩
    · exact ⟨.inr (.inl (b,i,j)), Or.inl (by simp [arc,h.1,h.2])⟩
    · exact ⟨.inr (.inl (b,i,j)), Or.inr (by simp [arc,h.1,h.2])⟩

def embed (b : B) : innerGraph D →g graph D where
  toFun u := .inr (.inl (b,u))
  map_rel' h := (middle_adj D).mpr ⟨rfl,h⟩

def innerRoute (j : J) :
    (innerGraph D).Walk (D.inner j 0) (D.inner j (Fin.last k)) :=
  walkOfSequence (D.inner j) (fun i => ⟨i,j,Or.inl ⟨rfl,rfl⟩⟩)

@[simp] theorem innerRoute_length (j : J) : (innerRoute D j).length = k :=
  length_walkOfSequence _ _

theorem innerRoute_support (j : J) : (innerRoute D j).support = List.ofFn (D.inner j) :=
  support_walkOfSequence _ _

theorem innerWalk_support (b : B) (j : J) :
    (innerWalk D b j).support =
      ((innerRoute D j).support.map fun u => (.inr (.inl (b,u)) : Vertex A B C U)) := by
  simp only [innerWalk, support_walkOfSequence, innerRoute_support, List.map_ofFn]
  rfl

def coarseLayer : Vertex A B C U → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def connector : Vertex A B C U → Vertex A B C U → ℕ
  | .inr (.inl _), .inr (.inl _) => 0
  | _, _ => 1

def connectorCount {s t : Vertex A B C U} (p : (graph D).Walk s t) : ℕ :=
  (p.darts.map fun d => connector d.fst d.snd).sum

@[simp] theorem connectorCount_nil (v : Vertex A B C U) :
    connectorCount D (.nil : (graph D).Walk v v) = 0 := rfl

@[simp] theorem connectorCount_cons {s u t : Vertex A B C U}
    (h : (graph D).Adj s u) (p : (graph D).Walk u t) :
    connectorCount D (.cons h p) = connector s u + connectorCount D p := rfl

theorem coarse_step {s t : Vertex A B C U} (h : (graph D).Adj s t) :
    (coarseLayer t : ℤ) - coarseLayer s ≤ connector s t := by
  rcases h with ⟨e,h | h⟩
  · have hs := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    dsimp at hs ht
    rw [← hs, ← ht]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;>
      simp [arc,coarseLayer,connector]
  · have hs := congrArg Prod.snd h
    have ht := congrArg Prod.fst h
    dsimp at hs ht
    rw [← hs, ← ht]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;>
      simp [arc,coarseLayer,connector]

theorem coarse_le_connectorCount {s t : Vertex A B C U}
    (p : (graph D).Walk s t) :
    (coarseLayer t : ℤ) - coarseLayer s ≤ connectorCount D p := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have hs := coarse_step D h
    rw [connectorCount_cons, Nat.cast_add]
    omega

theorem right_zero {c : C} {t : Vertex A B C U}
    (p : (graph D).Walk (.inr (.inr c)) t) (hp : connectorCount D p = 0) :
    p.support = [.inr (.inr c)] := by
  cases p with
  | nil => rfl
  | cons h p => simp [connector] at hp

/-- A route from a gadget to the right boundary with at most one
connector cannot leave the gadget before its final step. -/
theorem factor_middle_right {b : B} {u : U} {c : C}
    (q : (graph D).Walk (.inr (.inl (b,u))) (.inr (.inr c)))
    (hq : connectorCount D q ≤ 1) :
    ∃ j, D.right b j = c ∧
      ∃ w : (innerGraph D).Walk u (D.inner j (Fin.last k)),
        q.support = (w.support.map fun v => (.inr (.inl (b,v)) : Vertex A B C U)) ++
          [.inr (.inr c)] := by
  generalize hm : q.length = m
  induction m using Nat.strong_induction_on generalizing b u c with
  | h m ih =>
    cases q with
    | cons hadj p =>
      rename_i v
      rcases v with a | (⟨b',v⟩ | c')
      · have hlo := coarse_le_connectorCount D p
        simp only [connectorCount_cons, connector] at hq
        simp only [coarseLayer, Nat.cast_ofNat, Nat.cast_zero, sub_zero] at hlo
        omega
      · obtain ⟨hb,huv⟩ := (middle_adj D).mp hadj
        subst b'
        have hp : connectorCount D p ≤ 1 := by simpa [connector] using hq
        obtain ⟨j,hj,w,hw⟩ := ih p.length (by simp only [Walk.length_cons] at hm; omega) p hp rfl
        refine ⟨j,hj,.cons huv w,?_⟩
        simpa only [Walk.support_cons, List.map_cons, List.cons_append] using
          congrArg (List.cons (.inr (.inl (b,u)))) hw
      · have hp : connectorCount D p = 0 := by
          simp only [connectorCount_cons, connector] at hq
          omega
        cases p with
        | cons h p => simp [connector] at hp
        | nil =>
          obtain ⟨b',j,hc,hu⟩ := right_neighbor D hadj.symm
          simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at hu
          obtain ⟨rfl,rfl⟩ := hu
          exact ⟨j,hc.symm,.nil,rfl⟩

/-- Two connectors force a route to use exactly one copy of the inner
 graph. The two port labels are not assumed to agree. -/
theorem factor_left_right {a : A} {c : C}
    (q : (graph D).Walk (.inl a) (.inr (.inr c)))
    (hq : connectorCount D q ≤ 2) :
    ∃ b j₁ j₂, D.left b j₁ = a ∧ D.right b j₂ = c ∧
      ∃ w : (innerGraph D).Walk (D.inner j₁ 0) (D.inner j₂ (Fin.last k)),
        q.support = .inl a ::
          ((w.support.map fun v => (.inr (.inl (b,v)) : Vertex A B C U)) ++
            [.inr (.inr c)]) := by
  cases q with
  | cons h p =>
    obtain ⟨b,j₁,ha,rfl⟩ := left_neighbor D h
    have hp : connectorCount D p ≤ 1 := by
      simp only [connectorCount_cons, connector] at hq
      omega
    obtain ⟨j₂,hc,w,hw⟩ := factor_middle_right D p hp
    refine ⟨b,j₁,j₂,ha.symm,hc,w,?_⟩
    simpa only [Walk.support_cons] using congrArg (List.cons (.inl a)) hw

theorem coarse_step_eq {s t : Vertex A B C U} (h : (graph D).Adj s t)
    (hrise : layer D t = layer D s + 1) :
    (connector s t : ℤ) = (coarseLayer t : ℤ) - coarseLayer s := by
  rcases h with ⟨e,h | h⟩
  · have hs := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    dsimp at hs ht
    rw [← hs, ← ht]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;>
      simp [arc,coarseLayer,connector]
  · have he := arc_layer D e
    rw [h] at he
    dsimp at he
    omega

theorem connectorCount_of_rising {s t : Vertex A B C U}
    (p : (graph D).Walk s t)
    (hrise : ∀ d ∈ p.darts, (layer D d.snd : ℤ) = layer D d.fst + 1) :
    (connectorCount D p : ℤ) = (coarseLayer t : ℤ) - coarseLayer s := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have hfirst := hrise ⟨(_, _),h⟩ (by simp)
    have hs := coarse_step_eq D h (by dsimp at hfirst; omega)
    have ht := ih (by intro d hd; exact hrise d (by simp [hd]))
    rw [connectorCount_cons, Nat.cast_add]
    omega

/-- The two-edge outer path is uniquely determined even when its two
port labels are initially allowed to differ. -/
def OuterUnique : Prop :=
  ∀ b j b' j₁ j₂, D.left b' j₁ = D.left b j → D.right b' j₂ = D.right b j →
    b' = b ∧ j₁ = j ∧ j₂ = j

/-- Unique shortest designated paths in the actual inner graph. -/
def InnerUnique : Prop :=
  ∀ j (w : (innerGraph D).Walk (D.inner j 0) (D.inner j (Fin.last k))),
    w.length ≤ k → w = innerRoute D j

/-- Unweighted Lemma 7: input path uniqueness implies uniqueness of the
substituted routes among all walks in the undirected product. -/
theorem fullWalk_unique (hout : OuterUnique D) (hin : InnerUnique D)
    (b : B) (j : J)
    (q : (graph D).Walk (.inl (D.left b j)) (.inr (.inr (D.right b j))))
    (hq : q.length ≤ k+2) : q = fullWalk D b j := by
  have hlo := fullWalk_shortest D b j q
  have hlen : q.length = k+2 := by rw [fullWalk_length] at hlo; omega
  have hrise := LayeredWalks.tight_walk_rises (fun v => (layer D v : ℤ))
    (graph_layered D) q (by simp [layer,hlen])
  have hcnt : connectorCount D q ≤ 2 := by
    have hc := connectorCount_of_rising D q hrise
    simp only [coarseLayer, Nat.cast_ofNat, Nat.cast_zero, sub_zero] at hc
    omega
  obtain ⟨b',j₁,j₂,hl,hr,w,hw⟩ := factor_left_right D q hcnt
  obtain ⟨hb,hj₁,hj₂⟩ := hout b j b' j₁ j₂ hl hr
  subst b' j₁ j₂
  have hwl : w.length ≤ k := by
    have hh := congrArg List.length hw
    simp only [List.length_cons, List.length_append, List.length_map,
      Walk.length_support] at hh
    omega
  have hwq := hin j w hwl
  apply Walk.ext_support
  rw [hw, hwq]
  simp only [fullWalk, Walk.support_cons, Walk.support_concat,
    innerWalk_support]

/-- The preserver conclusion of unweighted Lemma 7 has no separate
product-uniqueness premise: it follows from the two input path systems. -/
theorem preserver_edge_count [Fintype A] [Fintype B] [Fintype C] [Fintype U] [Fintype J]
    (hout : OuterUnique D) (hin : InnerUnique D)
    (H : SimpleGraph (Vertex A B C U)) (hH : H ≤ graph D)
    (hpres : ∀ b j, H.edist (.inl (D.left b j)) (.inr (.inr (D.right b j))) =
      (graph D).edist (.inl (D.left b j)) (.inr (.inr (D.right b j)))) :
    H.edgeFinset.card = Fintype.card B * Fintype.card J * (k+2) := by
  exact preserver_edge_count_of_unique D (fullWalk_unique D hout hin) H hH hpres

end LinearDistancePreservers.ObstacleProduct
