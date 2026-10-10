import MinorFreeSpanners.FiniteStarPacking

/-! Actual simple alternating-route augmentation for induced-star packings.
Every internal step deletes one old matching edge and inserts one compatible
new edge. The final step uses a center with spare capacity. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Deleting leaves preserves every packing condition. -/
theorem IsStarPacking.leaf_subset {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L M : V → Finset V} (h : IsStarPacking G A B ell L)
    (hML : ∀ b, M b ⊆ L b) : IsStarPacking G A B ell M := by
  rcases h with ⟨hz,hs,ha,hi,hd,hc⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b hb
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := hML b hx
    simp [hz b hb] at hx'
  · intro b x hx; exact hs b (hML b hx)
  · intro b x hx; exact ha b x (hML b hx)
  · intro b x hx y hy hxy; exact hi b x (hML b hx) y (hML b hy) hxy
  · intro b c hbc
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact Finset.disjoint_left.mp (hd b c hbc) (hML b hz) (hML c hz')
  · intro b; exact (Finset.card_le_card (hML b)).trans (hc b)

/-- One old leaf is removed at its actual owner. -/
theorem IsStarPacking.erase_leaf {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L)
    (b y : V) : IsStarPacking G A B ell (Function.update L b ((L b).erase y)) := by
  classical
  apply h.leaf_subset
  intro c
  by_cases hcb : c = b
  · subst c; simpa using Finset.erase_subset y (L b)
  · simp [Function.update_of_ne hcb]

/-- Uncovered leaves occur at no center, including centers outside B. -/
theorem IsStarPacking.unused_of_uncovered {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L)
    {x : V} (hx : x ∉ B.biUnion L) : ∀ c, x ∉ L c := by
  intro c hc
  by_cases hcB : c ∈ B
  · exact hx (Finset.mem_biUnion.mpr ⟨c,hcB,hc⟩)
  · simp [h.1 c hcB] at hc

/-- Disjointness makes local deletion equal global deletion of that leaf. -/
theorem IsStarPacking.erase_union {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L)
    {b y : V} (hy : y ∈ L b) :
    B.biUnion (Function.update L b ((L b).erase y)) = (B.biUnion L).erase y := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨c,hc,hz⟩ := Finset.mem_biUnion.mp hz
    by_cases hcb : c = b
    · subst c
      have hz' : z ≠ y ∧ z ∈ L b := by simpa using hz
      exact Finset.mem_erase.mpr ⟨hz'.1,Finset.mem_biUnion.mpr ⟨b,hc,hz'.2⟩⟩
    · have hz' : z ∈ L c := by simpa [Function.update_of_ne hcb] using hz
      refine Finset.mem_erase.mpr ⟨?_,Finset.mem_biUnion.mpr ⟨c,hc,hz'⟩⟩
      intro hzy
      subst z
      exact Finset.disjoint_left.mp (h.2.2.2.2.1 c b hcb) hz' hy
  · intro hz
    obtain ⟨hzy,hz⟩ := Finset.mem_erase.mp hz
    obtain ⟨c,hc,hz⟩ := Finset.mem_biUnion.mp hz
    refine Finset.mem_biUnion.mpr ⟨c,hc,?_⟩
    by_cases hcb : c = b
    · subst c; simpa using Finset.mem_erase.mpr ⟨hzy,hz⟩
    · simpa [Function.update_of_ne hcb] using hz

/-- One internal alternating step: x replaces the old matched leaf y at b.
No augmentation or validity certificate is assumed for the new assignment. -/
theorem IsStarPacking.exchange_leaf {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L)
    {b x y : V} (hb : b ∈ B) (hx : x ∈ A) (he : G.Adj b x)
    (hnew : ∀ c, x ∉ L c) (hcompat : ∀ z ∈ L b, ¬ G.Adj x z)
    (hy : y ∈ L b) :
    let M := Function.update L b (insert x ((L b).erase y))
    IsStarPacking G A B ell M ∧ (∀ c, y ∉ M c) ∧
      B.biUnion M = insert x ((B.biUnion L).erase y) := by
  classical
  dsimp only
  let D := Function.update L b ((L b).erase y)
  have hD : IsStarPacking G A B ell D := h.erase_leaf b y
  have hDsub : ∀ c, D c ⊆ L c := by
    intro c
    by_cases hcb : c = b
    · subst c; simpa [D] using Finset.erase_subset y (L b)
    · simp [D,Function.update_of_ne hcb]
  have hroom : (D b).card < ell := by
    have hbound := h.2.2.2.2.2 b
    have hpos : 0 < (L b).card := Finset.card_pos.mpr ⟨y,hy⟩
    simp only [D,Function.update_self,Finset.card_erase_of_mem hy]
    omega
  have hM := hD.insert_leaf hb hx he (fun c hc => hnew c (hDsub c hc))
    (fun z hz => hcompat z (hDsub b hz)) hroom
  have hupdate : Function.update D b (insert x (D b)) =
      Function.update L b (insert x ((L b).erase y)) := by
    funext c
    by_cases hcb : c = b <;> simp [D,hcb]
  rw [hupdate] at hM
  have hu : B.biUnion (Function.update L b (insert x ((L b).erase y))) =
      insert x ((B.biUnion L).erase y) := by
    rw [← hupdate,starPacking_insert_union hb]
    congr 1
    exact h.erase_union hy
  refine ⟨hM,?_,hu⟩
  apply hM.unused_of_uncovered
  rw [hu]
  simp only [Finset.mem_insert,Finset.notMem_erase,or_false]
  intro hyx
  exact hnew b (hyx ▸ hy)

/-- A finite simple alternating route, expressed as the literal sequence of
edge exchanges. Each old-edge premise is membership in the current matching;
new-edge premises are actual host adjacency and compatibility with its star.
The center and incoming-leaf lists explicitly prohibit repeated vertices.
No constructor assumes validity, augmentation, or a size increase. -/
inductive StarAlternatingRoute (G : SimpleGraph V) (A B : Finset V) (ell : ℕ) :
    (V → Finset V) → V → List V → List V → Prop
  | finish {L : V → Finset V} {x b : V}
      (hb : b ∈ B) (he : G.Adj b x)
      (hc : ∀ z ∈ L b, ¬ G.Adj x z) (hr : (L b).card < ell) :
      StarAlternatingRoute G A B ell L x [b] [x]
  | step {L : V → Finset V} {x b y : V} {bs xs : List V}
      (hb : b ∈ B) (he : G.Adj b x)
      (hc : ∀ z ∈ L b, ¬ G.Adj x z) (hy : y ∈ L b)
      (hbnew : b ∉ bs) (hxnew : x ∉ xs)
      (tail : StarAlternatingRoute G A B ell
        (Function.update L b (insert x ((L b).erase y))) y bs xs) :
      StarAlternatingRoute G A B ell L x (b :: bs) (x :: xs)

/-- Simplicity is an actual consequence of the route representation. -/
theorem StarAlternatingRoute.nodup {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} {x : V} {bs xs : List V}
    (r : StarAlternatingRoute G A B ell L x bs xs) : bs.Nodup ∧ xs.Nodup := by
  induction r with
  | finish => simp
  | step hb he hc hy hbnew hxnew tail ih =>
    exact ⟨List.nodup_cons.mpr ⟨hbnew,ih.1⟩,List.nodup_cons.mpr ⟨hxnew,ih.2⟩⟩

/-- Construct the actual reassigned packing for an arbitrary finite simple
alternating route, and prove its occupied set gains exactly the initial leaf. -/
theorem StarAlternatingRoute.augment_union {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} {x : V} {bs xs : List V}
    (r : StarAlternatingRoute G A B ell L x bs xs) :
    IsStarPacking G A B ell L → x ∈ A → (∀ c, x ∉ L c) →
    ∃ M : V → Finset V, IsStarPacking G A B ell M ∧
      B.biUnion M = insert x (B.biUnion L) := by
  classical
  induction r with
  | finish hb he hc hr =>
    intro h hx hn
    exact ⟨_,h.insert_leaf hb hx he hn hc hr,starPacking_insert_union hb⟩
  | @step L x b y bs xs hb he hc hy hbnew hxnew tail ih =>
    intro h hx hn
    obtain ⟨hM,hynew,hu⟩ := h.exchange_leaf hb hx he hn hc hy
    obtain ⟨N,hN,hNu⟩ := ih hM (h.2.1 b hy) hynew
    refine ⟨N,hN,?_⟩
    rw [hNu,hu,Finset.insert_comm]
    have hyU : y ∈ B.biUnion L := Finset.mem_biUnion.mpr ⟨b,hb,hy⟩
    rw [Finset.insert_erase hyU]

/-- The genuine augmentation increases the number of selected leaves by one. -/
theorem StarAlternatingRoute.augment {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} {x : V} {bs xs : List V}
    (r : StarAlternatingRoute G A B ell L x bs xs)
    (h : IsStarPacking G A B ell L) (hx : x ∈ A) (hn : x ∉ B.biUnion L) :
    ∃ M : V → Finset V, IsStarPacking G A B ell M ∧
      starPackingSize B M = starPackingSize B L + 1 := by
  obtain ⟨M,hM,hu⟩ := r.augment_union h hx (h.unused_of_uncovered hn)
  refine ⟨M,hM,?_⟩
  rw [starPackingSize,hu,Finset.card_insert_of_notMem hn]
  rfl

/-- A maximum packing admits no such route ending at spare capacity. -/
theorem maximum_star_packing_no_augmenting_route {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L)
    (hm : ∀ M, IsStarPacking G A B ell M → starPackingSize B M ≤ starPackingSize B L)
    {x : V} (hx : x ∈ A) (hn : x ∉ B.biUnion L) {bs xs : List V} :
    ¬ StarAlternatingRoute G A B ell L x bs xs := by
  intro r
  obtain ⟨M,hM,hsize⟩ := r.augment h hx hn
  have := hm M hM
  omega

/-- A static simple alternating route in the ORIGINAL packing. The terminal
center has spare capacity in that packing. Old and new edges are explicit;
the recursive tail contains no reassigned packing and no existence oracle. -/
inductive StaticStarAlternatingRoute (G : SimpleGraph V) (A B : Finset V)
    (ell : ℕ) (L : V → Finset V) : V → List V → List V → Prop
  | finish {x b : V}
      (hb : b ∈ B) (he : G.Adj b x)
      (hc : ∀ z ∈ L b, ¬ G.Adj x z) (hr : (L b).card < ell) :
      StaticStarAlternatingRoute G A B ell L x [b] [x]
  | step {x b y : V} {bs xs : List V}
      (hb : b ∈ B) (he : G.Adj b x)
      (hc : ∀ z ∈ L b, ¬ G.Adj x z) (hy : y ∈ L b)
      (hbnew : b ∉ bs) (hxnew : x ∉ xs)
      (tail : StaticStarAlternatingRoute G A B ell L y bs xs) :
      StaticStarAlternatingRoute G A B ell L x (b :: bs) (x :: xs)

/-- Distinct centers ensure prior exchanges do not affect any future edge or
compatibility premise. This derives the dynamic route from static data. -/
theorem StaticStarAlternatingRoute.to_dynamic {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} {x : V} {bs xs : List V}
    (r : StaticStarAlternatingRoute G A B ell L x bs xs) :
    ∀ M : V → Finset V, (∀ b ∈ bs, M b = L b) →
      StarAlternatingRoute G A B ell M x bs xs := by
  classical
  induction r with
  | @finish x b hb he hc hr =>
    intro M hML
    have hMb := hML b (by simp)
    apply StarAlternatingRoute.finish hb he
    · simpa [hMb] using hc
    · simpa [hMb] using hr
  | @step x b y bs xs hb he hc hy hbnew hxnew tail ih =>
    intro M hML
    have hMb := hML b (by simp)
    apply StarAlternatingRoute.step hb he
      (by simpa [hMb] using hc) (by simpa [hMb] using hy) hbnew hxnew
    apply ih
    intro c hcbs
    have hcb : c ≠ b := by
      intro hcb
      exact hbnew (hcb ▸ hcbs)
    rw [Function.update_of_ne hcb]
    exact hML c (by simp [hcbs])

/-- An arbitrary static alternating route really augments the original
packing by one leaf. All reassignment and cardinality reasoning is internal. -/
theorem StaticStarAlternatingRoute.augment {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} {x : V} {bs xs : List V}
    (r : StaticStarAlternatingRoute G A B ell L x bs xs)
    (h : IsStarPacking G A B ell L) (hx : x ∈ A) (hn : x ∉ B.biUnion L) :
    ∃ M : V → Finset V, IsStarPacking G A B ell M ∧
      starPackingSize B M = starPackingSize B L + 1 := by
  exact (r.to_dynamic L (fun _ _ => rfl)).augment h hx hn

/-- Static path simplicity, independently of the construction. -/
theorem StaticStarAlternatingRoute.nodup {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} {x : V} {bs xs : List V}
    (r : StaticStarAlternatingRoute G A B ell L x bs xs) : bs.Nodup ∧ xs.Nodup := by
  exact (r.to_dynamic L (fun _ _ => rfl)).nodup


omit [DecidableEq V] in
/-- The route's center and leaf vertices lie in the actual two domains. -/
theorem StaticStarAlternatingRoute.vertices_mem {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} {x : V} {bs xs : List V}
    (r : StaticStarAlternatingRoute G A B ell L x bs xs)
    (h : IsStarPacking G A B ell L) :
    x ∈ A → (∀ b ∈ bs, b ∈ B) ∧ (∀ a ∈ xs, a ∈ A) := by
  induction r with
  | finish hb he hc hr =>
    intro hx
    exact ⟨by simpa using hb,by simpa using hx⟩
  | @step x b y bs xs hb he hc hy hbnew hxnew tail ih =>
    intro hx
    obtain ⟨hbs,hxs⟩ := ih (h.2.1 b hy)
    constructor
    · intro c hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hb
      · exact hbs c hc'
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hx
      · exact hxs a ha

/-- Under the source's disjoint domains, ALL route vertices are distinct,
including centers versus leaves, rather than merely distinct on each side. -/
theorem StaticStarAlternatingRoute.vertices_nodup {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} {x : V} {bs xs : List V}
    (r : StaticStarAlternatingRoute G A B ell L x bs xs)
    (h : IsStarPacking G A B ell L) (hx : x ∈ A) (hAB : Disjoint A B) :
    (bs ++ xs).Nodup := by
  obtain ⟨hbs,hxs⟩ := r.vertices_mem h hx
  apply List.nodup_append'.mpr
  refine ⟨r.nodup.1,r.nodup.2,?_⟩
  intro z hzb hzx
  exact Finset.disjoint_left.mp hAB (hxs z hzx) (hbs z hzb)

/-- Maximality rules out the concrete static route, with no dynamic oracle. -/
theorem maximum_star_packing_no_static_route {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L)
    (hm : ∀ M, IsStarPacking G A B ell M → starPackingSize B M ≤ starPackingSize B L)
    {x : V} (hx : x ∈ A) (hn : x ∉ B.biUnion L) {bs xs : List V} :
    ¬ StaticStarAlternatingRoute G A B ell L x bs xs := by
  intro r
  obtain ⟨M,hM,hsize⟩ := r.augment h hx hn
  have := hm M hM
  omega

end MinorFreeSpanners
