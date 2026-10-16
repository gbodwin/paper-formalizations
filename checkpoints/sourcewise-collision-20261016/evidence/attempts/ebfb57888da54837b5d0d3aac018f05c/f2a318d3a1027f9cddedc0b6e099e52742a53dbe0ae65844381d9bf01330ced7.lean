import SlackSparsification.SourcewiseMinimal

namespace SlackSparsification.Directed
open SimpleGraph Finset
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Explicit directed acyclicity: every allowed closed walk is nil. -/
def SelectedAcyclic (K : SimpleGraph V) (F : Finset (V × V)) : Prop :=
  ∀ v (p : K.Walk v v), Allowed (edgeRel F) p → p.Nil

omit [Fintype V] [DecidableEq V] in
theorem selected_acyclic_path {K : SimpleGraph V} {F : Finset (V × V)}
    (h : SelectedAcyclic K F) {s t : V} (p : K.Walk s t) (hp : Allowed (edgeRel F) p) :
    p.IsPath := by
  apply Walk.isPath_iff_isSubwalk_imp_nil.mpr
  intro v q hq
  exact h v q (fun d hd => hp d (hq.darts_subset hd))

omit [Fintype V] in
theorem arc_head_mem_support {K : SimpleGraph V} {s t : V} (p : K.Walk s t)
    {e : V × V} (he : e ∈ arcs p) : e.2 ∈ p.support := by
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  have hm : d.snd ∈ p.darts.map (fun d => d.snd) := List.mem_map.mpr ⟨d,hd,rfl⟩
  rw [Walk.map_snd_darts] at hm
  exact List.mem_of_mem_tail hm

omit [Fintype V] in
theorem arcs_append_mem {K : SimpleGraph V} {s v t : V} (p : K.Walk s v)
    (q : K.Walk v t) (e : V × V) : e ∈ arcs (p.append q) ↔ e ∈ arcs p ∨ e ∈ arcs q := by
  simp [arcs,arcList,Walk.darts_append,List.map_append]

omit [Fintype V] [DecidableEq V] in
/-- Two support vertices can be ordered by splitting the actual walk. -/
theorem ordered_walk_split {K : SimpleGraph V} {s t v w : V} (p : K.Walk s t)
    (hv : v ∈ p.support) (hw : w ∈ p.support) :
    (∃ (a : K.Walk s v) (m : K.Walk v w) (b : K.Walk w t), p = a.append (m.append b)) ∨
    (∃ (a : K.Walk s w) (m : K.Walk w v) (b : K.Walk v t), p = a.append (m.append b)) := by
  obtain ⟨a,b,hab⟩ := Walk.mem_support_iff_exists_append.mp hv
  have hwb : w ∈ a.support ∨ w ∈ b.support := by
    rw [hab,Walk.mem_support_append_iff] at hw
    exact hw
  rcases hwb with hwa | hwb
  · obtain ⟨x,m,hxm⟩ := Walk.mem_support_iff_exists_append.mp hwa
    exact Or.inr ⟨x,m,b,by rw [hab,hxm,Walk.append_assoc]⟩
  · obtain ⟨m,z,hmz⟩ := Walk.mem_support_iff_exists_append.mp hwb
    exact Or.inl ⟨a,m,z,by rw [hab,hmz]⟩

omit [Fintype V] in
/-- An arc entering the second split vertex lies in the middle segment.
Simplicity excludes it from both the prefix and the suffix. -/
theorem incoming_in_middle {K : SimpleGraph V} {s t v w : V}
    (a : K.Walk s v) (m : K.Walk v w) (b : K.Walk w t)
    (hp : (a.append (m.append b)).IsPath) (hvw : w ≠ v)
    {e : V × V} (he : e ∈ arcs (a.append (m.append b))) (hh : e.2 = w) : e ∈ arcs m := by
  rcases (arcs_append_mem _ _ _).mp he with ha | hmb
  · have hw : w ∈ a.support := hh ▸ arc_head_mem_support a ha
    have hw' : w ∈ (m.append b).support := by simp only [Walk.mem_support_append_iff]; exact Or.inl m.end_mem_support
    exact (hp.ne_of_mem_support_of_append hvw hw hw' rfl).elim
  · rcases (arcs_append_mem _ _ _).mp hmb with hm | hb
    · exact hm
    · exact (path_no_incoming_start b hp.of_append_right.of_append_right hb hh).elim

/-- The distinct-vertex splice contradiction. Its three segments each avoid
f, the competing required edge entering the later collision vertex. -/
theorem collision_ordered_impossible {K : SimpleGraph V} {F : Finset (V × V)}
    (hacy : SelectedAcyclic K F) {a b s t u v w : V}
    (pre : K.Walk a v) (mid : K.Walk v w) (post : K.Walk w b)
    (hallow : Allowed (edgeRel F) (pre.append (mid.append post)))
    (hvw : w ≠ v) {e f g : V × V}
    (he : Requires K F a b e) (hh : e.2 = w)
    (hg : Requires K F s t g) (hgv : g.2 = v)
    (hf : Requires K F s u f) (hfw : f.2 = w) (hne : e ≠ f) : False := by
  have hpath := selected_acyclic_path hacy _ hallow
  have hem : e ∈ arcs mid := incoming_in_middle pre mid post hpath hvw (he.2 _ hallow) hh
  have ham : Allowed (edgeRel F) mid := ((allowed_append _ _ _).mp
    ((allowed_append _ _ _).mp hallow).2).1
  obtain ⟨q,hq⟩ := hg.1
  obtain ⟨r,hr⟩ := hf.1
  have hvq : v ∈ q.support := hgv ▸ arc_head_mem_support q (hg.2 q hq)
  have hwr : w ∈ r.support := hfw ▸ arc_head_mem_support r (hf.2 r hr)
  let left := q.takeUntil v hvq
  let right := r.dropUntil w hwr
  have hal : Allowed (edgeRel F) left := fun d hd => hq d (q.darts_takeUntil_subset_darts hvq hd)
  have har : Allowed (edgeRel F) right := fun d hd => hr d (r.darts_dropUntil_subset_darts hwr hd)
  have hfm : f ∉ arcs mid := by
    intro h
    exact hne (path_incoming_unique mid (selected_acyclic_path hacy _ ham) hem h (hh.trans hfw.symm))
  have hfl : f ∉ arcs left := by
    intro h
    have hlm := selected_acyclic_path hacy (left.append mid) ((allowed_append _ _ _).mpr ⟨hal,ham⟩)
    exact hne (path_incoming_unique _ hlm
      ((arcs_append_mem _ _ _).mpr (Or.inr hem)) ((arcs_append_mem _ _ _).mpr (Or.inl h))
      (hh.trans hfw.symm))
  have hfr : f ∉ arcs right := by
    intro h
    exact path_no_incoming_start right (selected_acyclic_path hacy _ har) h hfw
  have hsplice : Allowed (edgeRel F) (left.append (mid.append right)) :=
    (allowed_append _ _ _).mpr ⟨hal,(allowed_append _ _ _).mpr ⟨ham,har⟩⟩
  have h := hf.2 _ hsplice
  rcases (arcs_append_mem _ _ _).mp h with h | h
  · exact hfl h
  · rcases (arcs_append_mem _ _ _).mp h with h | h
    · exact hfm h
    · exact hfr h

/-- At most one ordered pair of competing incoming arcs per fixed demand and
other source. The same-vertex case is separate from the acyclic splice. -/
theorem required_collision_unique {K : SimpleGraph V} {F : Finset (V × V)}
    (hacy : SelectedAcyclic K F) {a b s t u : V} {e e' f f' : V × V}
    (he : Requires K F a b e) (he' : Requires K F a b e')
    (hf : Requires K F s t f) (hf' : Requires K F s u f')
    (h1 : e.2 = f.2) (h2 : e'.2 = f'.2) (hne : e ≠ f) (hne' : e' ≠ f') :
    e = e' ∧ f = f' := by
  by_cases hv : e.2 = e'.2
  · exact collision_same_vertex he he' hf hf' h1 h2 hv
  obtain ⟨p,hp⟩ := he.1
  have hvp := arc_head_mem_support p (he.2 p hp)
  have hwp := arc_head_mem_support p (he'.2 p hp)
  rcases ordered_walk_split p hvp hwp with ⟨pre,mid,post,hp'⟩ | ⟨pre,mid,post,hp'⟩
  · have hallow : Allowed (edgeRel F) (pre.append (mid.append post)) := hp' ▸ hp
    exact (collision_ordered_impossible hacy pre mid post hallow (Ne.symm hv)
      he' rfl hf h1.symm hf' h2.symm hne').elim
  · have hallow : Allowed (edgeRel F) (pre.append (mid.append post)) := hp' ▸ hp
    exact (collision_ordered_impossible hacy pre mid post hallow hv
      he rfl hf' h2.symm hf h1.symm hne).elim


noncomputable def competingArcs (K : SimpleGraph V) (F : Finset (V × V)) (a b : V) : Finset (V × V) :=
  F.filter fun f => ∃ e ∈ F, Requires K F a b e ∧ e.2 = f.2 ∧ e ≠ f

/-- Label each competing arc by a requiring demand's source. Collision
uniqueness makes these source labels injective. Minimality supplies hreq. -/
theorem competing_arcs_card {K : SimpleGraph V} {F P : Finset (V × V)} {S : Finset V}
    (hacy : SelectedAcyclic K F) (hsrc : ∀ st ∈ P, st.1 ∈ S)
    (hreq : ∀ f ∈ F, ∃ st ∈ P, Requires K F st.1 st.2 f) (a b : V) :
    (competingArcs K F a b).card ≤ S.card := by
  classical
  let T := competingArcs K F a b
  choose lab hlP hlreq using fun f : {f // f ∈ T} => hreq f.val (mem_filter.mp f.property).1
  let label : {f // f ∈ T} → {s // s ∈ S} := fun f => ⟨(lab f).1,hsrc _ (hlP f)⟩
  apply card_le_card_of_injective (f := label)
  intro i j hij
  apply Subtype.ext
  have hsource : (lab i).1 = (lab j).1 := congrArg Subtype.val hij
  obtain ⟨e,_,he,hhead,hne⟩ := (mem_filter.mp i.property).2
  obtain ⟨e',_,he',hhead',hne'⟩ := (mem_filter.mp j.property).2
  have hj := hlreq j
  rw [← hsource] at hj
  exact (required_collision_unique hacy he he' (hlreq i) hj hhead hhead' hne hne').2

noncomputable def requiredHeavyArcs (K : SimpleGraph V) (F : Finset (V × V))
    (a b : V) (d : ℕ) : Finset (V × V) :=
  F.filter fun e => Requires K F a b e ∧ d < (F.filter fun f => f.2 = e.2).card

/-- Each heavy required incoming arc has at least d competing arcs. Distinct
required heads give disjoint fibers, so no competing arc is counted twice. -/
theorem required_heavy_mul_le {K : SimpleGraph V} {F P : Finset (V × V)} {S : Finset V}
    (hacy : SelectedAcyclic K F) (hsrc : ∀ st ∈ P, st.1 ∈ S)
    (hreq : ∀ f ∈ F, ∃ st ∈ P, Requires K F st.1 st.2 f) (a b : V) (d : ℕ) :
    (requiredHeavyArcs K F a b d).card * d ≤ S.card := by
  classical
  let H := requiredHeavyArcs K F a b d
  let I := fun e : V × V => (F.filter fun f => f.2 = e.2).erase e
  have hI : ∀ e ∈ H, d ≤ (I e).card := by
    intro e he
    obtain ⟨he,_,hc⟩ := mem_filter.mp he
    have hc' := card_erase_add_one (mem_filter.mpr ⟨he,rfl⟩ : e ∈ F.filter fun f => f.2 = e.2)
    dsimp [I]
    omega
  have hdis : (H : Set (V × V)).PairwiseDisjoint I := by
    intro e he e' he' hne
    apply Finset.disjoint_left.mpr
    intro f hf hf'
    have h1 := (mem_filter.mp (mem_erase.mp hf).2).2
    have h2 := (mem_filter.mp (mem_erase.mp hf').2).2
    have heq := required_same_demand_same_vertex (mem_filter.mp he).2.1
      (mem_filter.mp he').2.1 (h1.symm.trans h2)
    exact hne heq
  have hsub : H.biUnion I ⊆ competingArcs K F a b := by
    intro f hf
    obtain ⟨e,he,hfe⟩ := mem_biUnion.mp hf
    obtain ⟨hne,hfe⟩ := mem_erase.mp hfe
    obtain ⟨hf,hhead⟩ := mem_filter.mp hfe
    exact mem_filter.mpr ⟨hf,e,(mem_filter.mp he).1,(mem_filter.mp he).2.1,hhead.symm,Ne.symm hne⟩
  calc
    H.card * d = ∑ _ ∈ H, d := by simp
    _ ≤ ∑ e ∈ H, (I e).card := sum_le_sum hI
    _ = (H.biUnion I).card := (card_biUnion hdis).symm
    _ ≤ (competingArcs K F a b).card := card_le_card hsub
    _ ≤ S.card := competing_arcs_card hacy hsrc hreq a b

/-- Positive cutoffs permit the real-valued heavy bound without floor loss. -/
theorem required_heavy_card_le {K : SimpleGraph V} {F P : Finset (V × V)} {S : Finset V}
    (hacy : SelectedAcyclic K F) (hsrc : ∀ st ∈ P, st.1 ∈ S)
    (hreq : ∀ f ∈ F, ∃ st ∈ P, Requires K F st.1 st.2 f)
    (a b : V) (d : ℕ) (hd : 1 ≤ d) :
    ((requiredHeavyArcs K F a b d).card : ℝ) ≤ (S.card : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  apply (le_div_iff₀ hd').mpr
  exact_mod_cast required_heavy_mul_le hacy hsrc hreq a b d


/-- Required-edge charging covers all heavy arcs and finite unions avoid
multiple counting of arcs required by several demands. -/
theorem acyclic_required_total_bound {K : SimpleGraph V} {F P : Finset (V × V)} {S : Finset V}
    (hacy : SelectedAcyclic K F) (hsrc : ∀ st ∈ P, st.1 ∈ S)
    (hreq : ∀ f ∈ F, ∃ st ∈ P, Requires K F st.1 st.2 f)
    (d : ℕ) (hd : 1 ≤ d) :
    (F.card : ℝ) ≤ (Fintype.card V : ℝ) * d + (P.card : ℝ) * S.card / d := by
  classical
  let H := F.filter fun e => d < (F.filter fun f => f.2 = e.2).card
  let L := F.filter fun e => (F.filter fun f => f.2 = e.2).card ≤ d
  let J := fun st : V × V => requiredHeavyArcs K F st.1 st.2 d
  have hsub : H ⊆ P.biUnion J := by
    intro f hf
    obtain ⟨hf,hdeg⟩ := mem_filter.mp hf
    obtain ⟨st,hst,hstf⟩ := hreq f hf
    exact mem_biUnion.mpr ⟨st,hst,mem_filter.mpr ⟨hf,hstf,hdeg⟩⟩
  have hsum : H.card * d ≤ P.card * S.card := calc
    _ ≤ (∑ st ∈ P, (J st).card) * d := Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ st ∈ P, (J st).card * d := by rw [sum_mul]
    _ ≤ ∑ _ ∈ P, S.card := sum_le_sum (fun st _ => required_heavy_mul_le hacy hsrc hreq st.1 st.2 d)
    _ = P.card * S.card := by simp
  have hH : (H.card : ℝ) ≤ (P.card : ℝ) * S.card / d := by
    apply (le_div_iff₀ (show (0 : ℝ) < d by exact_mod_cast (show 0 < d by omega))).mpr
    exact_mod_cast hsum
  have hcover : F ⊆ L ∪ H := by
    intro e he
    by_cases h : (F.filter fun f => f.2 = e.2).card ≤ d
    · exact mem_union_left _ (mem_filter.mpr ⟨he,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨he,by omega⟩)
  have hF : (F.card : ℝ) ≤ L.card + H.card := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le L H)
  have hL : (L.card : ℝ) ≤ (Fintype.card V : ℝ) * d := by exact_mod_cast light_arcs_card F d
  linarith

/-- Construct the DAG preserver internally, with a uniform integer parameter.
The only graph restriction is acyclicity of the actual input arcs. -/
theorem exists_sourcewise_dag_integer (K : SimpleGraph V) (A : V → V → Prop)
    (hacy : SelectedAcyclic K (inputArcs K A)) (S : Finset V) (P : Finset (V × V))
    (hsrc : ∀ st ∈ P, st.1 ∈ S) (d : ℕ) (hd : 1 ≤ d) :
    ∃ F : Finset (V × V), F ⊆ inputArcs K A ∧ PreservesReachability K A P F ∧
      (F.card : ℝ) ≤ (Fintype.card V : ℝ) * d + (P.card : ℝ) * S.card / d := by
  obtain ⟨F,hF,hs,hmin⟩ := exists_minimal_reachability K A P
  have hfacy : SelectedAcyclic K F := by
    intro v p hp
    exact hacy v p (fun e he => hF (hp e he))
  have hreq : ∀ f ∈ F, ∃ st ∈ P, Requires K F st.1 st.2 f := by
    intro f hf
    obtain ⟨st,hst,_,hr⟩ := minimal_arc_required hF hs hmin hf
    exact ⟨st,hst,hr⟩
  exact ⟨F,hF,hs,acyclic_required_total_bound hfacy hsrc hreq d hd⟩

end SlackSparsification.Directed
