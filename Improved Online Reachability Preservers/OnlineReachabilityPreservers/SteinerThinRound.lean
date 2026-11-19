import Mathlib.Algebra.BigOperators.Field
import OnlineReachabilityPreservers.SteinerThinCover

/-! Fixed edge thresholds and finite product probabilities for the thin phase. -/

namespace OnlineReachabilityPreservers

open Finset

private noncomputable def constrainedSamples {I : Type*} [Fintype I] (m : ℕ) (allowed : I → Finset (Fin m)) :
    Finset (I → Fin m) := by
  classical
  exact univ.filter fun sample => ∀ i, sample i ∈ allowed i

private theorem constrainedSamples_card {I : Type*} [Fintype I] (m : ℕ) (allowed : I → Finset (Fin m)) :
    (constrainedSamples m allowed).card = ∏ i, (allowed i).card := by
  classical
  let e : {s // s ∈ constrainedSamples m allowed} ≃ ∀ i, {u // u ∈ allowed i} :=
    { toFun := fun s i => ⟨s.1 i, (mem_filter.mp s.2).2 i⟩
      invFun := fun f => ⟨fun i => (f i).1,mem_filter.mpr ⟨mem_univ _,fun i => (f i).2⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => funext fun _ => Subtype.ext rfl }
  rw [← Fintype.card_coe,Fintype.card_congr e,Fintype.card_pi]
  simp

private def lowThreshold (m u : ℕ) : Finset (Fin m) := univ.filter fun i => (i:ℕ) < u

private theorem lowThreshold_card (m u : ℕ) : (lowThreshold m u).card = min m u := by
  let eqv : {i // i ∈ lowThreshold m u} ≃ Fin (min m u) :=
    { toFun := fun i => ⟨i.1.1, lt_min i.1.isLt (mem_filter.mp i.2).2⟩
      invFun := fun i => ⟨⟨i.1, i.isLt.trans_le (min_le_left _ _)⟩,
        mem_filter.mpr ⟨mem_univ _,i.isLt.trans_le (min_le_right _ _)⟩⟩
      left_inv := fun _ => Subtype.ext (Fin.ext rfl)
      right_inv := fun _ => Fin.ext rfl }
  rw [← Fintype.card_coe,Fintype.card_congr eqv,Fintype.card_fin]

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- One independent threshold per arc, uniform among |E| choices. -/
abbrev ThinSample (G : Arcs V) := G → Fin G.card

/-- Round a deterministic fractional state using a single fixed threshold vector. -/
def roundedThinArcs (G : Arcs V) (factor : ℕ) (load : CutLoads V) (sample : ThinSample G) : Arcs V :=
  (G.attach.filter fun e => (sample e:ℕ) < factor*2^(load e.1)).image Subtype.val

omit [Fintype V] in
theorem mem_roundedThinArcs {G : Arcs V} {factor : ℕ} {load : CutLoads V} {sample : ThinSample G}
    {e : V × V} :
    e ∈ roundedThinArcs G factor load sample ↔
      ∃ h : e ∈ G, (sample ⟨e,h⟩:ℕ) < factor*2^(load e) := by
  constructor
  · intro h
    obtain ⟨⟨a,ha⟩,hp,eq⟩ := mem_image.mp h
    change a=e at eq
    subst e
    exact ⟨ha,(mem_filter.mp hp).2⟩
  · rintro ⟨ha,hs⟩
    exact mem_image.mpr ⟨⟨e,ha⟩,mem_filter.mpr ⟨mem_attach _ _,hs⟩,rfl⟩

omit [Fintype V] in
theorem roundedThinArcs_subset (G : Arcs V) (factor : ℕ) (load : CutLoads V)
    (sample : ThinSample G) : roundedThinArcs G factor load sample ⊆ G :=
  fun _ he => (mem_roundedThinArcs.mp he).choose

omit [Fintype V] in
theorem roundedThinArcs_mono (G : Arcs V) (factor : ℕ) (sample : ThinSample G)
    {l r : CutLoads V} (le : l ≤ r) : roundedThinArcs G factor l sample ⊆ roundedThinArcs G factor r sample := by
  intro e he
  obtain ⟨h,hs⟩ := mem_roundedThinArcs.mp he
  apply mem_roundedThinArcs.mpr
  exact ⟨h,hs.trans_le (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (le e)))⟩

/-- The uniform probability of a set of threshold vectors. -/
noncomputable def thinProbability (G : Arcs V) (event : Finset (ThinSample G)) : ℝ :=
  (event.card:ℝ)/(G.card:ℝ)^G.card

private def missCutChoices (G C : Arcs V) (factor : ℕ) (load : CutLoads V) (e : G) : Finset (Fin G.card) :=
  if e.1 ∈ C then (lowThreshold G.card (factor*2^(load e.1)))ᶜ else univ

private noncomputable def missedCutSamples (G C : Arcs V) (factor : ℕ) (load : CutLoads V) :
    Finset (ThinSample G) := constrainedSamples G.card (missCutChoices G C factor load)

omit [Fintype V] in
private theorem mem_missedCutSamples {G C : Arcs V} {factor : ℕ} {load : CutLoads V} {s : ThinSample G} :
    s ∈ missedCutSamples G C factor load ↔
      ∀ e ∈ C, e ∉ roundedThinArcs G factor load s := by
  classical
  simp only [missedCutSamples,constrainedSamples,mem_filter,mem_univ,true_and]
  constructor
  · intro good e he hround
    obtain ⟨hG,lt⟩ := mem_roundedThinArcs.mp hround
    have hm := good ⟨e,hG⟩
    have nl : ¬ (s ⟨e,hG⟩:ℕ) < factor*2^(load e) := by
      simpa [missCutChoices,he,lowThreshold] using hm
    exact nl lt
  · intro hm e
    by_cases h : e.1 ∈ C
    · have hr := hm e.1 h
      simp only [missCutChoices,ite_eq_left h,mem_compl,lowThreshold,mem_filter,mem_univ,true_and]
      exact fun hh => hr (mem_roundedThinArcs.mpr ⟨e.2,hh⟩)
    · simp [missCutChoices,h]

omit [LinearOrder V] [Fintype V] in
private theorem thinProbability_product (G : Arcs V) (allowed : G → Finset (Fin G.card)) :
    thinProbability G (constrainedSamples G.card allowed) =
      ∏ e : G, ((allowed e).card:ℝ)/(G.card:ℝ) := by
  unfold thinProbability
  rw [constrainedSamples_card,Nat.cast_prod, prod_div_distrib,prod_const,card_univ,Fintype.card_coe]

omit [Fintype V] in
private theorem missCutChoices_le_exp (G C : Arcs V) {factor : ℕ} {load : CutLoads V}
    (hm : 0 < G.card) (e : G) :
    ((missCutChoices G C factor load e).card:ℝ)/(G.card:ℝ) ≤
      Real.exp (-(if e.1 ∈ C then (factor:ℝ)*2^(load e.1)/(G.card:ℝ) else 0)) := by
  have hm0 : (0:ℝ) < G.card := Nat.cast_pos.mpr hm
  by_cases hc : e.1 ∈ C
  · let w := factor*2^(load e.1)
    have card : (missCutChoices G C factor load e).card = G.card - min G.card w := by
      simp [missCutChoices,hc,Finset.card_compl,lowThreshold_card,w]
    simp only [hc,ite_true]
    rw [card]
    by_cases all : G.card ≤ w
    · rw [min_eq_left all,Nat.sub_self,Nat.cast_zero,zero_div]
      exact (Real.exp_pos _).le
    · have le : w ≤ G.card := (le_of_not_ge all)
      rw [min_eq_right le,Nat.cast_sub le,sub_div,div_self hm0.ne']
      have eq : (w:ℝ) = (factor:ℝ)*2^(load e.1) := by simp [w]
      rw [eq]
      simpa only [sub_eq_add_neg,add_comm] using
        (Real.add_one_le_exp (-((factor:ℝ)*2^(load e.1)/(G.card:ℝ))))
  · simp [missCutChoices,hc,div_self hm0.ne']

omit [Fintype V] in
private theorem cut_rate_sum (G C : Arcs V) (sub : C ⊆ G) (factor : ℕ) (load : CutLoads V) :
    (∑ e : G, if e.1 ∈ C then (factor:ℝ)*2^(load e.1)/(G.card:ℝ) else 0) =
      (factor:ℝ)*(cutMass C load:ℝ)/(G.card:ℝ) := by
  let term (e : V × V) := if e ∈ C then (factor:ℝ)*2^(load e)/(G.card:ℝ) else 0
  change (∑ e : G, term e.1) = _
  rw [← Finset.sum_subtype G (fun _ => Iff.rfl) term]
  unfold term
  rw [← sum_filter]
  have fc : G.filter (fun e => e ∈ C) = C := by
    ext e
    exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨sub h,h⟩⟩
  rw [fc]
  unfold cutMass
  rw [Nat.cast_sum,mul_sum, sum_div]
  simp

omit [Fintype V] in
/-- A covered directed cut is absent from the rounded output with probability at most exp(-factor). -/
theorem roundedThin_cut_probability (G C : Arcs V) (sub : C ⊆ G) (factor : ℕ) (load : CutLoads V)
    (hm : 0 < G.card) (cover : G.card ≤ cutMass C load) :
    thinProbability G (missedCutSamples G C factor load) ≤ Real.exp (-(factor:ℝ)) := by
  have hm0 : (0:ℝ) < G.card := Nat.cast_pos.mpr hm
  rw [missedCutSamples,thinProbability_product]
  let r (e : G) := if e.1 ∈ C then (factor:ℝ)*2^(load e.1)/(G.card:ℝ) else 0
  have lower : (factor:ℝ) ≤ (factor:ℝ)*(cutMass C load:ℝ)/(G.card:ℝ) :=
    (le_div_iff₀ hm0).mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr cover) (by positivity))
  calc
    _ ≤ ∏ e : G, Real.exp (-r e) :=
      prod_le_prod₀ (fun _ _ => by positivity) (fun e _ => missCutChoices_le_exp G C hm e)
    _ = Real.exp (-((factor:ℝ)*(cutMass C load:ℝ)/(G.card:ℝ))) := by
      rw [← Real.exp_sum,sum_neg_distrib]
      congr 2
      exact cut_rate_sum G C sub factor load
    _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg lower)

private noncomputable def pairCutFailures (G : Arcs V) (d : V × V) (factor : ℕ) (load : CutLoads V) :
    Finset (ThinSample G) :=
  (intervalCutSides G d).toFinset.biUnion fun W =>
    missedCutSamples G (outgoingCut (intervalArcs G d) W) factor load

theorem pairCutFailures_contains {G : Arcs V} {d : V × V} {factor : ℕ} {load : CutLoads V}
    {sample : ThinSample G}
    (feasible : Reach G d.1 d.2) (fail : ¬ Reach (roundedThinArcs G factor load sample) d.1 d.2) :
    sample ∈ pairCutFailures G d factor load := by
  classical
  let H := roundedThinArcs G factor load sample
  let W := reaches (reverseArcs H) d.1 ∩ reachInterval G d
  have Hreach : ∀ v, v ∈ reaches (reverseArcs H) d.1 ↔ Reach H d.1 v := by
    intro v
    rw [mem_reaches,reach_reverseArcs]
  have hs : d.1 ∈ W :=
    mem_inter.mpr ⟨(Hreach _).mpr .refl,mem_reachInterval.mpr ⟨.refl,feasible⟩⟩
  have ht : d.2 ∉ W := fun h => fail ((Hreach _).mp (mem_inter.mp h).1)
  apply mem_biUnion.mpr
  refine ⟨W,List.mem_toFinset.mpr (mem_intervalCutSides.mpr ⟨inter_subset_right,hs,ht⟩),?_⟩
  apply mem_missedCutSamples.mpr
  intro e ec eh
  obtain ⟨ei, eleft, eright⟩ := mem_filter.mp ec
  obtain ⟨_, _, vinterval⟩ := mem_filter.mp ei
  apply eright
  exact mem_inter.mpr ⟨(Hreach _).mpr (((Hreach _).mp (mem_inter.mp eleft).1).tail eh),vinterval⟩

private theorem intervalCutSides_length_le (G : Arcs V) (d : V × V) :
    (intervalCutSides G d).length ≤ 2^(reachInterval G d).card := by
  unfold intervalCutSides
  refine (List.length_filter_le ..).trans_eq ?_
  rw [List.length_map,List.length_sublists,length_sort]

/-- Each thin pair has at most 2^τ cuts. Their failure probabilities can be summed
using the same threshold vector for all requests. -/
theorem roundedThin_pair_probability (G : Arcs V) (d : V × V) (factor τ : ℕ) (load : CutLoads V)
    (hm : 0 < G.card) (thin : (reachInterval G d).card ≤ τ) (covered : CutCovered G d load) :
    thinProbability G (pairCutFailures G d factor load) ≤ (2:ℝ)^τ * Real.exp (-(factor:ℝ)) := by
  unfold thinProbability
  let q := (G.card:ℝ)^G.card
  let S := (intervalCutSides G d).toFinset
  let miss (W : Finset V) := missedCutSamples G (outgoingCut (intervalArcs G d) W) factor load
  change ((S.biUnion miss).card:ℝ)/q ≤ _
  have cards : (S.biUnion miss).card ≤ ∑ W ∈ S, (miss W).card := card_biUnion_le
  calc
    _ ≤ (∑ W ∈ S, ((miss W).card:ℝ))/q := div_le_div_of_nonneg_right (by exact_mod_cast cards)
      (by dsimp [q]; positivity)
    _ = ∑ W ∈ S, ((miss W).card:ℝ)/q := sum_div ..
    _ ≤ ∑ _W ∈ S, Real.exp (-(factor:ℝ)) := by
      apply sum_le_sum
      intro W hW
      obtain ⟨ws,s,t⟩ := mem_intervalCutSides.mp (List.mem_toFinset.mp hW)
      exact roundedThin_cut_probability G _ ((outgoingCut_subset _ _).trans (intervalArcs_subset _ _))
        factor load hm (covered W ws s t)
    _ = (S.card:ℝ)*Real.exp (-(factor:ℝ)) := by simp
    _ ≤ _ := by
      have count := ((List.toFinset_card_le (intervalCutSides G d)).trans
        (intervalCutSides_length_le G d)).trans (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) thin)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast count) (Real.exp_pos _).le

omit [Fintype V] in
private theorem roundedThin_coordinate_probability (G : Arcs V) (factor : ℕ)
    (load : CutLoads V) (hm : 0 < G.card) (e : G) :
    thinProbability G ((univ : Finset (ThinSample G)).filter fun s =>
      (s e:ℕ) < factor*2^(load e.1)) =
      (min G.card (factor*2^(load e.1)):ℝ)/(G.card:ℝ) := by
  classical
  let choices (f : G) : Finset (Fin G.card) :=
    if f=e then lowThreshold G.card (factor*2^(load e.1)) else univ
  have events : (univ : Finset (ThinSample G)).filter (fun s => (s e:ℕ) < factor*2^(load e.1)) =
      constrainedSamples G.card choices := by
    ext sample
    simp only [constrainedSamples,mem_filter,mem_univ,true_and]
    constructor
    · intro hs f
      by_cases eq : f = e
      · subst f
        simpa [choices,lowThreshold] using hs
      · simp [choices,eq]
    · intro all
      simpa [choices,lowThreshold] using all e
  rw [events,thinProbability_product, Finset.prod_eq_single e]
  · simp [choices,lowThreshold_card]
  · intro f _ ne
    have m0 : (G.card:ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
    simpa [choices,ne] using div_self m0
  · simp

/-- Mean size over the uniform product of thresholds. -/
noncomputable def thinMean (G : Arcs V) (output : ThinSample G → Arcs V) : ℝ := by
  classical
  exact (∑ s : ThinSample G, ((output s).card:ℝ))/(G.card:ℝ)^G.card

omit [Fintype V] in
/-- Each arc is bought with probability min(1, factor × capacity). -/
theorem roundedThin_expected_bound (G : Arcs V) (factor : ℕ) (load : CutLoads V)
    (hm : 0 < G.card) :
    thinMean G (roundedThinArcs G factor load) ≤ (factor:ℝ)*(cutMass G load:ℝ)/(G.card:ℝ) := by
  classical
  let m := G.card
  let included (s : ThinSample G) (e : G) : ℝ := if (s e:ℕ) < factor*2^(load e.1) then 1 else 0
  let event (e : G) := (univ : Finset (ThinSample G)).filter fun s => (s e:ℕ) < factor*2^(load e.1)
  have count (s : ThinSample G) : ((roundedThinArcs G factor load s).card:ℝ) = ∑ e : G, included s e := by
    rw [roundedThinArcs,card_image_of_injective _ Subtype.val_injective]
    dsimp [included]
    rw [← sum_filter]
    rw [attach_eq_univ]
    simp only [sum_const,nsmul_eq_mul,mul_one]
  have count' (e : G) : (∑ s : ThinSample G, included s e) = ((event e).card:ℝ) := by
    dsimp [included,event]
    rw [← sum_filter]
    simp
  calc
    _ = ∑ e : G, thinProbability G (event e) := by
      unfold thinMean thinProbability
      rw [← sum_div]
      congr 1
      simp only [count, ← count']
      exact sum_comm
    _ ≤ ∑ e : G, (factor:ℝ)*2^(load e.1)/(m:ℝ) := by
      apply sum_le_sum
      intro e _
      have h := roundedThin_coordinate_probability G factor load hm e
      change thinProbability G (event e) = _ at h
      rw [h]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast min_le_right m (factor*2^(load e.1))
    _ = _ := by
      let term (e : V × V) := (factor:ℝ)*2^(load e)/(m:ℝ)
      change (∑ e : G, term e.1) = _
      rw [← Finset.sum_subtype G (fun _ => Iff.rfl) term]
      unfold term cutMass
      rw [Nat.cast_sum,mul_sum,sum_div]
      simp [m]

/-- A failure at any revealed prefix. It is tested by finite graph reachability. -/
def ThinRoundFailure (G : Arcs V) (factor : ℕ) (sample : ThinSample G) (D : List (V × V)) : Prop :=
  ∃ i : Fin D.length, (D.get i).1 ∉ reaches
    (roundedThinArcs G factor (thinCoverRun G (D.take (i.1+1))) sample) (D.get i).2

instance (G : Arcs V) (factor : ℕ) (s : ThinSample G) (D : List (V × V)) :
    Decidable (ThinRoundFailure G factor s D) := by
  unfold ThinRoundFailure
  infer_instance

/-- Round at each prefix with fixed thresholds. If an arriving request is still
unserved, retain the full input graph from that prefix onwards. -/
def thinRoundRun (G : Arcs V) (factor : ℕ) (sample : ThinSample G) (D : List (V × V)) : Arcs V :=
  if D.isEmpty then ∅ else
    if ThinRoundFailure G factor sample D then G
    else roundedThinArcs G factor (thinCoverRun G D) sample

theorem thinRoundRun_correct (G : Arcs V) (factor : ℕ) (sample : ThinSample G)
    (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    thinRoundRun G factor sample D ⊆ G ∧ Preserves G (thinRoundRun G factor sample D) D := by
  cases D with
  | nil => simp [thinRoundRun,Preserves]
  | cons first rest =>
    let D := first :: rest
    by_cases failure : ThinRoundFailure G factor sample D
    · simp [thinRoundRun,show ThinRoundFailure G factor sample (first::rest) from failure,Preserves]
    · have heq : thinRoundRun G factor sample D = roundedThinArcs G factor (thinCoverRun G D) sample := by
        simp [thinRoundRun,D,show ¬ ThinRoundFailure G factor sample (first::rest) from failure]
      rw [show first::rest = D from rfl, heq]
      let out := roundedThinArcs G factor (thinCoverRun G D) sample
      have sub : out ⊆ G := roundedThinArcs_subset G factor _ sample
      refine ⟨sub,fun d hd => ⟨reach_mono sub,fun _ => ?_⟩⟩
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hd
      have h := not_exists.mp failure i
      have hreach := mem_reaches.mp (not_not.mp h)
      have pref : D.take (i.1+1) <+: D := List.take_prefix _ _
      have mono := roundedThinArcs_mono G factor sample (thinCoverRun_prefix G pref feasible)
      exact reach_mono mono hreach

private theorem ThinRoundFailure.prefix {G : Arcs V} {factor : ℕ} {sample : ThinSample G}
    {D E : List (V × V)} (pref : D <+: E) (fail : ThinRoundFailure G factor sample D) :
    ThinRoundFailure G factor sample E := by
  obtain ⟨F,rfl⟩ := pref
  obtain ⟨i,hi⟩ := fail
  let j : Fin (D++F).length := ⟨i.1,by have := i.isLt; simp; omega⟩
  have de : (D++F).get j = D.get i := List.getElem_append_left i.isLt
  have pe : (D++F).take (j.1+1) = D.take (i.1+1) :=
    List.take_append_of_le_length (Nat.succ_le_of_lt i.isLt)
  exact ⟨j,by simpa only [de,pe] using hi⟩

theorem thinRoundRun_prefix (G : Arcs V) (factor : ℕ) (sample : ThinSample G) {D E : List (V × V)}
    (pref : D <+: E) (feasible : ∀ d ∈ E, Reach G d.1 d.2) :
    thinRoundRun G factor sample D ⊆ thinRoundRun G factor sample E := by
  cases D with
  | nil => simp [thinRoundRun]
  | cons d ds =>
    cases E with
    | nil => simp at pref
    | cons e es =>
      by_cases fail : ThinRoundFailure G factor sample (e::es)
      · simpa [thinRoundRun,fail] using (thinRoundRun_correct G factor sample (d::ds)
          (fun d hd => feasible d (pref.sublist.subset hd))).1
      · have early : ¬ ThinRoundFailure G factor sample (d::ds) := fun h => fail (h.prefix pref)
        simp only [thinRoundRun,List.isEmpty_cons, Bool.false_eq_true, ite_false,ite_eq_right fail,ite_eq_right early]
        exact roundedThinArcs_mono G factor sample (thinCoverRun_prefix G pref feasible)

private noncomputable def thinRoundBad (G : Arcs V) (factor : ℕ) (D : List (V × V)) :
    Finset (ThinSample G) := by
  classical
  exact univ.filter fun s => ThinRoundFailure G factor s D

private theorem thinRoundBad_probability (G : Arcs V) (factor τ : ℕ) (D : List (V × V))
    (hm : 0 < G.card) (thin : ∀ d ∈ D, (reachInterval G d).card ≤ τ)
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    thinProbability G (thinRoundBad G factor D) ≤ D.length*(2:ℝ)^τ*Real.exp (-(factor:ℝ)) := by
  classical
  let bad (i : Fin D.length) := pairCutFailures G (D.get i) factor (thinCoverRun G (D.take (i.1+1)))
  have sub : thinRoundBad G factor D ⊆ univ.biUnion bad := by
    intro s hs
    obtain ⟨i,hi⟩ := (mem_filter.mp hs).2
    exact mem_biUnion.mpr ⟨i,mem_univ _,pairCutFailures_contains (feasible _ (D.get_mem i))
      (fun h => hi (mem_reaches.mpr h))⟩
  have union : (thinRoundBad G factor D).card ≤ ∑ i : Fin D.length, (bad i).card :=
    (card_le_card sub).trans card_biUnion_le
  unfold thinProbability
  calc
    _ ≤ (∑ i : Fin D.length, ((bad i).card:ℝ))/(G.card:ℝ)^G.card :=
      div_le_div_of_nonneg_right (by exact_mod_cast union) (by positivity)
    _ = ∑ i : Fin D.length, ((bad i).card:ℝ)/(G.card:ℝ)^G.card := sum_div ..
    _ ≤ ∑ _i : Fin D.length, (2:ℝ)^τ*Real.exp (-(factor:ℝ)) := by
      apply sum_le_sum
      intro i _
      let T := D.take (i.1+1)
      have mem : D.get i ∈ T := List.mem_take_iff_getElem.mpr
        ⟨i.1,lt_min (Nat.lt_succ_self _) i.isLt,rfl⟩
      have cover := (thinCoverRun_bound G G Subset.rfl T
        (fun _ hd => feasible _ (List.mem_of_mem_take hd))).1 _ mem
      exact roundedThin_pair_probability G _ factor τ _ hm (thin _ (D.get_mem i)) cover
    _ = _ := by simp; ring

/-- Expected size with the fallback purchase charged on the bad event. -/
theorem thinRoundRun_expected_bound (G Z : Arcs V) (sub : Z ⊆ G) (factor τ : ℕ)
    (D : List (V × V)) (hm : 0 < G.card) (thin : ∀ d ∈ D, (reachInterval G d).card ≤ τ)
    (feasible : ∀ d ∈ D, Reach Z d.1 d.2) :
    thinMean G (fun s => thinRoundRun G factor s D) ≤
      (factor:ℝ)*(1+Z.card*(G.card.log2+1))+
        G.card*D.length*(2:ℝ)^τ*Real.exp (-(factor:ℝ)) := by
  classical
  let m := G.card
  let load := thinCoverRun G D
  let H := roundedThinArcs G factor load
  let bad := thinRoundBad G factor D
  let pred (s : ThinSample G) := if s ∈ bad then (m:ℝ) else 0
  have m0 : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have point (s : ThinSample G) : ((thinRoundRun G factor s D).card:ℝ) ≤ (H s).card+pred s := by
    cases D with
    | nil => simp [thinRoundRun,pred]; positivity
    | cons d ds =>
      by_cases fail : ThinRoundFailure G factor s (d::ds)
      · have h : s ∈ bad := mem_filter.mpr ⟨mem_univ _,fail⟩
        simp [thinRoundRun,fail,pred,h,m]
      · have h : s ∉ bad := fun hs => fail ((mem_filter.mp hs).2)
        simp [thinRoundRun,fail,pred,h,H,load]
  have mulBad : (∑ s : ThinSample G, pred s) = (m:ℝ)*(bad.card:ℝ) := by
    dsimp only [pred]
    rw [← sum_filter,filter_mem_eq_inter,univ_inter]
    simp [mul_comm]
  have split : thinMean G (fun s => thinRoundRun G factor s D) ≤
      thinMean G H+(m:ℝ)*thinProbability G bad := by
    unfold thinMean thinProbability
    apply (div_le_div_of_nonneg_right (sum_le_sum (fun s _ => point s)) (by positivity)).trans
    rw [sum_add_distrib,mulBad,add_div,mul_div_assoc]
  have cover := (thinCoverRun_bound G Z sub D feasible).2
  have rating : thinMean G H ≤ (factor:ℝ)*(1+Z.card*(G.card.log2+1)) := by
    apply (roundedThin_expected_bound G factor load hm).trans
    apply (div_le_iff₀ m0).mpr
    have realCover : (cutMass G load:ℝ) ≤ (m:ℝ)*(1+(Z.card:ℝ)*((G.card.log2:ℝ)+1)) := by
      exact_mod_cast cover
    calc
      _ ≤ (factor:ℝ)*((m:ℝ)*(1+(Z.card:ℝ)*((G.card.log2:ℝ)+1))) :=
        mul_le_mul_of_nonneg_left realCover (by positivity)
      _ = _ := by ring
  have chance := thinRoundBad_probability G factor τ D hm thin
    (fun d hd => reach_mono sub (feasible d hd))
  have expected := add_le_add rating (mul_le_mul_of_nonneg_left chance m0.le)
  apply split.trans
  convert expected using 1
  ring

/-- Integer oversampling factor for all thin cuts and all distinct demands. -/
def thinRoundingFactor (n τ : ℕ) : ℕ := τ+4*(n.log2+1)

private theorem log_le_log2_succ {n : ℕ} (hn : 0 < n) :
    Real.log (n:ℝ) ≤ (n.log2:ℝ)+1 := by
  have n0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have two : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hpow : (n:ℝ) ≤ (2:ℝ)^(n.log2+1) := by
    exact_mod_cast ((Nat.log2_lt hn.ne').mp (Nat.lt_succ_self _)).le
  calc
    _ ≤ Real.log ((2:ℝ)^(n.log2+1)) := Real.log_le_log n0 hpow
    _ = ((n.log2:ℝ)+1)*Real.log 2 := by rw [Real.log_pow]; push_cast; rfl
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left two (by positivity : 0 ≤ (n.log2:ℝ)+1)

private theorem thinRoundingFactor_failure {n τ : ℕ} (hn : 0 < n) :
    (2:ℝ)^τ*Real.exp (-(thinRoundingFactor n τ:ℝ)) ≤ 1/(n:ℝ)^4 := by
  have n0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have l2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have cut : (τ:ℝ)*Real.log 2 ≤ τ := by
    simpa using mul_le_mul_of_nonneg_left l2 (show (0:ℝ) ≤ τ by positivity)
  have log := log_le_log2_succ hn
  have f : (τ:ℝ)*Real.log 2-(thinRoundingFactor n τ:ℝ) ≤ -4*Real.log (n:ℝ) := by
    push_cast [thinRoundingFactor]
    linarith only [cut,log]
  calc
    _ = Real.exp ((τ:ℝ)*Real.log 2-(thinRoundingFactor n τ:ℝ)) := by
      have h : (2:ℝ)^τ = Real.exp ((τ:ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
      rw [h,← Real.exp_add,sub_eq_add_neg]
    _ ≤ Real.exp (-4*Real.log (n:ℝ)) := Real.exp_le_exp.mpr f
    _ = _ := by
      rw [neg_mul,Real.exp_neg,show (4:ℝ) = ((4:ℕ):ℝ) by norm_num,
        Real.exp_nat_mul,Real.exp_log n0,one_div]

/-- The expected thin-demand cost for distinct non-self requests. The only
escape cost is at most one in expectation over the fixed threshold vector. -/
theorem thinRoundRun_competitive (G Z : Arcs V) (sub : Z ⊆ G) (τ : ℕ)
    (D : List (V × V)) (distinct : D.Nodup)
    (thin : ∀ d ∈ D, (reachInterval G d).card ≤ τ)
    (nonself : ∀ d ∈ D, d.1 ≠ d.2)
    (feasible : ∀ d ∈ D, Reach Z d.1 d.2) :
    let factor := thinRoundingFactor (Fintype.card V) τ
    thinMean G (fun s => thinRoundRun G factor s D) ≤
      ((factor:ℝ)*((G.card.log2:ℝ)+2)+1)*Z.card := by
  cases D with
  | nil =>
    simp [thinMean,thinRoundRun]
    positivity
  | cons d ds =>
    let D := d :: ds
    let n := Fintype.card V
    let factor := thinRoundingFactor n τ
    have npos : 0 < n := Fintype.card_pos_iff.mpr ⟨d.1⟩
    have n0 : (0:ℝ) < n := Nat.cast_pos.mpr npos
    have count := lemma20_opt_squared D.toFinset Z
      (fun a ha => nonself _ (List.mem_toFinset.mp ha))
      (fun a ha => feasible _ (List.mem_toFinset.mp ha))
    rw [List.toFinset_card_of_nodup distinct] at count
    have zpos : 0 < Z.card := by
      by_contra! hc
      have e : Z.card = 0 := by omega
      have h : 0 < D.length := by simp [D]
      have zero : D.length ≤ 0 := by simpa only [e,zero_pow (by decide : 2 ≠ 0)] using count
      exact (not_lt_of_ge zero) h
    have mpos : 0 < G.card := zpos.trans_le (card_le_card sub)
    have z1 : (1:ℝ) ≤ Z.card := by exact_mod_cast zpos
    have gcap : (G.card:ℝ) ≤ (n:ℝ)^2 := by
      exact_mod_cast (show G.card ≤ n^2 by simpa [n,Fintype.card_prod,pow_two] using card_le_univ G)
    have listCap : (D.length:ℝ) ≤ (n:ℝ)^2 := by
      have c : D.toFinset.card ≤ n^2 := by
        simpa [n,Fintype.card_prod,pow_two] using card_le_univ D.toFinset
      rw [List.toFinset_card_of_nodup distinct] at c
      exact_mod_cast c
    have small := thinRoundingFactor_failure (τ := τ) npos
    have fallback : (G.card:ℝ)*D.length*(2:ℝ)^τ*Real.exp (-(factor:ℝ)) ≤ 1 := by
      calc
        _ = ((G.card:ℝ)*D.length)*((2:ℝ)^τ*Real.exp (-(factor:ℝ))) := by ring
        _ ≤ ((n:ℝ)^2*(n:ℝ)^2)*(1/(n:ℝ)^4) :=
          mul_le_mul (mul_le_mul gcap listCap (by positivity) (by positivity)) small
            (by positivity) (by positivity)
        _ = 1 := by field_simp
    have fraction : (factor:ℝ)*(1+Z.card*(G.card.log2+1)) ≤
        (factor:ℝ)*((G.card.log2:ℝ)+2)*Z.card := by
      calc
        _ ≤ (factor:ℝ)*((Z.card:ℝ)+Z.card*(G.card.log2+1)) :=
          mul_le_mul_of_nonneg_left (add_le_add z1 le_rfl) (by positivity)
        _ = _ := by ring
    have raw := thinRoundRun_expected_bound G Z sub factor τ D mpos thin feasible
    change thinMean G (fun s => thinRoundRun G factor s D) ≤ _
    apply raw.trans
    linarith only [fallback,fraction,z1]

end OnlineReachabilityPreservers
