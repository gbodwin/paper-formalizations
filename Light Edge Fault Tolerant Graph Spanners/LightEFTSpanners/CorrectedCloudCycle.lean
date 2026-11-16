import LightEFTSpanners.CorrectedCloudConstruction
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Tactic

namespace LightEFTSpanners.CorrectedCloud
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- The union of identity and cyclic-shift matchings, on two labelled clouds. -/
def matchingCycle (p : ℕ) : SimpleGraph (Fin p ⊕ Fin p) where
  Adj a b := match a,b with
    | Sum.inl i, Sum.inr j => i=j ∨ finRotate p i=j
    | Sum.inr j, Sum.inl i => i=j ∨ finRotate p i=j
    | _,_ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

@[simp] theorem matchingCycle_cross (p : ℕ) (i j : Fin p) :
    (matchingCycle p).Adj (Sum.inl i) (Sum.inr j) ↔
      i=j ∨ finRotate p i=j := Iff.rfl

theorem rotate_ne {p : ℕ} (hp : 2≤p) (i : Fin p) : finRotate p i≠i := by
  let : NeZero p := ⟨by omega⟩
  rw [finRotate_apply]
  intro h
  have h1 : (1 : Fin p)=0 := add_left_cancel (by simpa using h : i+1=i+0)
  have hval := congrArg Fin.val h1
  rw [Fin.val_one',Fin.val_zero,Nat.mod_eq_of_lt (by omega)] at hval
  omega

theorem matchingCycle_neighbors_left (p : ℕ) (i : Fin p) :
    (matchingCycle p).neighborSet (Sum.inl i) =
      {Sum.inr i,Sum.inr (finRotate p i)} := by
  ext a
  cases a <;> simp [matchingCycle,eq_comm]

theorem matchingCycle_neighbors_right (p : ℕ) (i : Fin p) :
    (matchingCycle p).neighborSet (Sum.inr i) =
      {Sum.inl i,Sum.inl ((finRotate p).symm i)} := by
  ext a
  cases a with
  | inl j =>
    simp only [mem_neighborSet,matchingCycle,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sum.inl.injEq]
    rw [← Equiv.eq_symm_apply]
  | inr j => simp [matchingCycle]

theorem matchingCycle_isCycles {p : ℕ} (hp : 2≤p) : (matchingCycle p).IsCycles := by
  intro a _
  cases a with
  | inl i =>
    rw [matchingCycle_neighbors_left]
    exact Set.ncard_pair (by simpa using (rotate_ne hp i).symm)
  | inr i =>
    rw [matchingCycle_neighbors_right]
    apply Set.ncard_pair
    intro h
    have heq : i=(finRotate p).symm i := Sum.inl.inj h
    have hr : finRotate p i=i := by
      calc
        finRotate p i=finRotate p ((finRotate p).symm i) := congrArg _ heq
        _=i := Equiv.apply_symm_apply _ _
    exact rotate_ne hp i hr

theorem matchingCycle_connected {p : ℕ} (hp : 0<p) : (matchingCycle p).Connected := by
  let : NeZero p := ⟨hp.ne'⟩
  have hstep (i : Fin p) :
      (matchingCycle p).Reachable (Sum.inl i) (Sum.inl (finRotate p i)) := by
    apply Reachable.trans
      (show (matchingCycle p).Adj (Sum.inl i) (Sum.inr (finRotate p i)) from Or.inr rfl).reachable
    exact (show (matchingCycle p).Adj (Sum.inr (finRotate p i))
      (Sum.inl (finRotate p i)) from Or.inl rfl).reachable
  have hleftNat (i : ℕ) : ∀ hi : i<p,
      (matchingCycle p).Reachable (Sum.inl (0 : Fin p)) (Sum.inl ⟨i,hi⟩) := by
    induction i with
    | zero => intro hi; exact Reachable.refl _
    | succ i ih =>
      intro hi
      have hip : i<p := by omega
      have heq : finRotate p (⟨i,hip⟩ : Fin p)=⟨i+1,hi⟩ := by
        apply Fin.ext
        rw [finRotate_apply,Fin.val_add_one_of_lt' (by omega)]
      simpa only [heq] using (ih hip).trans (hstep ⟨i,hip⟩)
  have hall (a : Fin p ⊕ Fin p) :
      (matchingCycle p).Reachable (Sum.inl (0 : Fin p)) a := by
    cases a with
    | inl i => exact hleftNat i.val i.is_lt
    | inr i =>
      exact (hleftNat i.val i.is_lt).trans
        ((show (matchingCycle p).Adj (Sum.inl i) (Sum.inr i) from Or.inl rfl).reachable)
  exact { preconnected := fun a b => (hall a).symm.trans (hall b) }

/-- The alternating matching cycle remains connected after one edge failure. -/
theorem matchingCycle_two {p : ℕ} (hp : 2≤p) : (matchingCycle p).IsEdgeConnected 2 := by
  intro a b
  rw [isEdgeReachable_two]
  intro e
  have hcon := matchingCycle_connected (by omega : 0<p)
  have hbridge : ¬(matchingCycle p).IsBridge e := by
    obtain ⟨u,v⟩ := e
    rw [isBridge_iff]
    by_cases hadj : (matchingCycle p).Adj u v
    · exact not_not.mpr (IsCycles.reachable_deleteEdges hadj (matchingCycle_isCycles hp))
    · have hdel : (matchingCycle p).deleteEdges {s(u,v)}=matchingCycle p := by
        apply le_antisymm (deleteEdges_le _)
        intro x y hxy
        apply deleteEdges_adj.mpr ⟨hxy,?_⟩
        intro he
        have heq : s(x,y)=s(u,v) := Set.mem_singleton_iff.mp he
        have hm : s(u,v)∈(matchingCycle p).edgeSet := heq ▸ (mem_edgeSet _).mpr hxy
        exact hadj ((mem_edgeSet _).mp hm)
      rw [hdel]
      exact not_not.mpr (hcon.preconnected u v)
  exact (hcon.preconnected.connected_deleteEdges_of_not_isBridge hbridge).preconnected a b

theorem matchingCycle_cross_injective {p : ℕ} : Function.Injective
    (fun ij : Fin p × Fin p => (s(Sum.inl ij.1,Sum.inr ij.2) : Sym2 (Fin p ⊕ Fin p))) := by
  intro a b he
  rcases Sym2.eq_iff.mp he with he | he
  · exact Prod.ext (Sum.inl.inj he.1) (Sum.inr.inj he.2)
  · simp at he

theorem matchingCycle_edges (p : ℕ) :
    (matchingCycle p).edgeFinset =
      (univ.image (fun i : Fin p => s(Sum.inl i,Sum.inr i))) ∪
      (univ.image (fun i : Fin p => s(Sum.inl i,Sum.inr (finRotate p i)))) := by
  ext e
  constructor
  · intro he
    obtain ⟨a,b⟩ := e
    have hab := mem_edgeFinset.mp he
    cases a with
    | inl i =>
      cases b with
      | inl j => exact False.elim hab
      | inr j =>
        rcases hab with h | h
        · subst j; exact mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
        · subst j; exact mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
    | inr i =>
      cases b with
      | inl j =>
        rcases hab with h | h
        · subst i
          exact mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,Sym2.eq_swap⟩)
        · subst i
          exact mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,Sym2.eq_swap⟩)
      | inr j => exact False.elim hab
  · intro he
    rcases mem_union.mp he with he | he
    · obtain ⟨i,_,rfl⟩ := mem_image.mp he
      exact mem_edgeFinset.mpr (Or.inl rfl)
    · obtain ⟨i,_,rfl⟩ := mem_image.mp he
      exact mem_edgeFinset.mpr (Or.inr rfl)

theorem matchingCycle_edge_card {p : ℕ} (hp : 2≤p) :
    (matchingCycle p).edgeFinset.card=2*p := by
  have hinj1 : Function.Injective
      (fun i : Fin p => (s(Sum.inl i,Sum.inr i) : Sym2 (Fin p ⊕ Fin p))) := by
    intro a b he
    exact congrArg Prod.fst (@matchingCycle_cross_injective p (a,a) (b,b) he)
  have hinj2 : Function.Injective
      (fun i : Fin p => (s(Sum.inl i,Sum.inr (finRotate p i)) : Sym2 (Fin p ⊕ Fin p))) := by
    intro a b he
    exact congrArg Prod.fst (@matchingCycle_cross_injective p
      (a,finRotate p a) (b,finRotate p b) he)
  have hd : Disjoint
      (univ.image (fun i : Fin p => (s(Sum.inl i,Sum.inr i) : Sym2 (Fin p ⊕ Fin p))))
      (univ.image (fun i : Fin p => (s(Sum.inl i,Sum.inr (finRotate p i)) : Sym2 (Fin p ⊕ Fin p)))) := by
    rw [Finset.disjoint_left]
    intro e he hf
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    obtain ⟨j,_,heq⟩ := mem_image.mp hf
    have hij := @matchingCycle_cross_injective p (j,finRotate p j) (i,i) heq
    have hji : j=i := congrArg Prod.fst hij
    have hr : finRotate p j=i := congrArg Prod.snd hij
    exact rotate_ne hp j (hr.trans hji.symm)
  rw [matchingCycle_edges,card_union_of_disjoint hd,
    card_image_of_injective _ hinj1,card_image_of_injective _ hinj2]
  simp [two_mul]

/-- Place the two labelled cycle clouds at specified core vertices. -/
def cycleEmbedding {m p : ℕ} (u v : Fin m) : (Fin p ⊕ Fin p) → Fin m × Fin p
  | Sum.inl i => (u,i)
  | Sum.inr i => (v,i)

theorem cycleEmbedding_injective {m p : ℕ} {u v : Fin m} (huv : u≠v) :
    Function.Injective (cycleEmbedding (p:=p) u v) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [cycleEmbedding,Prod.mk.injEq]

def cycleHom {m p : ℕ} {T : SimpleGraph (Fin m)} {u v : Fin m}
    (huv : T.Adj u v) (horder : u<v) :
    matchingCycle p →g certificate T p where
  toFun := cycleEmbedding u v
  map_rel' := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact False.elim hab
      | inr j =>
        rcases hab with h | h
        · exact Or.inr ⟨huv,Or.inl h⟩
        · exact Or.inr ⟨huv,Or.inr (Or.inl ⟨horder,h⟩)⟩
    | inr i =>
      cases b with
      | inl j =>
        rcases hab with h | h
        · exact Or.inr ⟨huv.symm,Or.inl h.symm⟩
        · exact Or.inr ⟨huv.symm,Or.inr (Or.inr ⟨horder,h⟩)⟩
      | inr j => exact False.elim hab

end LightEFTSpanners.CorrectedCloud
