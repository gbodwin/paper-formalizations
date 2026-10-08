import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.Order.Monoid.Lex
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Basic.NNReal.Basic
import Mathlib.Tactic

/-! Deterministic shortest-path tiebreaking (Lemma 2).
An ambient simple graph supplies the walk datatype; `Allowed` independently
restricts the direction of each step, so no symmetry of the directed input is
assumed. The primary score is the original nonnegative real cost. The
secondary score assigns a distinct power of two to each undirected edge.
Simple paths with fixed endpoints have different secondary scores.
Lexicographic minimization therefore selects consistent shortest paths without
random perturbations, finite precision, or a uniqueness assumption. -/
namespace LinearDistancePreservers.ConsistentTiebreaking
open SimpleGraph Finset
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {K : SimpleGraph V}

def Allowed (G : V → V → Prop) {u v : V} (p : K.Walk u v) : Prop :=
  ∀ d ∈ p.darts, G d.fst d.snd

theorem allowed_append (G : V → V → Prop) {u v z : V}
    (p : K.Walk u v) (q : K.Walk v z) :
    Allowed G (p.append q) ↔ Allowed G p ∧ Allowed G q := by
  simp [Allowed, Walk.darts_append, List.mem_append, or_imp, forall_and]

theorem allowed_bypass {G : V → V → Prop} {u v : V} {p : K.Walk u v}
    (h : Allowed G p) : Allowed G p.bypass :=
  fun d hd => h d (p.darts_bypass_subset_darts hd)

/-- A simple path is determined by its endpoints and its edge multiset. -/
theorem path_eq_of_edges_perm {u v : V} (p q : K.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath) (he : p.edges.Perm q.edges) : p = q := by
  induction p with
  | nil =>
    have : q = .nil := by simpa using (Walk.isPath_iff_nil.mp hq)
    exact this.symm
  | @cons u z v ha p ih =>
    cases q with
    | nil => simp at he
    | @cons u z' v hb q =>
      have hmem : s(u,z) ∈ (Walk.cons hb q).edges := he.mem_iff.mp (by simp)
      have hz : z = z' := by simpa using hq.eq_snd_of_mem_edges hmem
      subst z'
      have htail : p.edges.Perm q.edges := List.Perm.cons_inv he
      have heq := ih q hp.of_cons hq.of_cons htail
      subst q
      rfl

noncomputable def edgeIndex : Sym2 V ↪ ℕ :=
  (Fintype.equivFin (Sym2 V)).toEmbedding.trans ⟨Fin.val, Fin.val_injective⟩

noncomputable def edgeCode (e : Sym2 V) : ℕ := 2 ^ edgeIndex e

theorem edgeCode_injective_on_finsets :
    Function.Injective (fun E : Finset (Sym2 V) => ∑ e ∈ E, edgeCode e) := by
  classical
  intro E F h
  have himg : E.image edgeIndex = F.image edgeIndex := by
    apply geomSum_injective (n := 2) (by decide)
    simpa [sum_image, edgeIndex.injective.injOn, edgeCode] using h
  exact (Finset.image_injective edgeIndex.injective) himg

abbrev Score := ℝ ×ₗ ℕ

noncomputable def stepScore (w : V → V → ℝ≥0) (d : K.Dart) : Score :=
  toLex ((w d.fst d.snd : ℝ), edgeCode d.edge)

noncomputable def score (w : V → V → ℝ≥0) {u v : V} (p : K.Walk u v) : Score :=
  (p.darts.map (stepScore w)).sum

theorem score_append (w : V → V → ℝ≥0) {u v z : V}
    (p : K.Walk u v) (q : K.Walk v z) :
    score w (p.append q) = score w p + score w q := by
  simp [score, Walk.darts_append]

theorem score_secondary (w : V → V → ℝ≥0) {u v : V} (p : K.Walk u v) :
    (ofLex (score w p)).2 = (p.edges.map edgeCode).sum := by
  induction p with
  | nil => simp [score]
  | cons h p ih => simpa [score, stepScore] using ih

theorem score_primary (w : V → V → ℝ≥0) {u v : V} (p : K.Walk u v) :
    (ofLex (score w p)).1 = (p.darts.map fun d => (w d.fst d.snd : ℝ)).sum := by
  induction p with
  | nil => simp [score]
  | cons h p ih => simpa [score, stepScore] using ih

theorem stepScore_nonneg (w : V → V → ℝ≥0) (d : K.Dart) : 0 ≤ stepScore w d := by
  change toLex (0,0) ≤ toLex ((w d.fst d.snd : ℝ), edgeCode d.edge)
  rw [Prod.Lex.toLex_le_toLex]
  rcases lt_or_eq_of_le (w d.fst d.snd).coe_nonneg with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, Nat.zero_le _⟩

theorem score_bypass_le (w : V → V → ℝ≥0) {u v : V} (p : K.Walk u v) :
    score w p.bypass ≤ score w p := by
  have aux {l r : List K.Dart} (h : l.Sublist r) :
      (l.map (stepScore w)).sum ≤ (r.map (stepScore w)).sum := by
    induction h with
    | slnil => rfl
    | cons d h ih =>
      simpa only [List.map_cons, List.sum_cons] using
        ih.trans (le_add_of_nonneg_left (stepScore_nonneg w d))
    | cons_cons d h ih =>
      simpa only [List.map_cons, List.sum_cons] using add_le_add (le_refl (stepScore w d)) ih
  exact aux p.darts_bypass_sublist_darts

theorem score_injective_on_paths (w : V → V → ℝ≥0) {u v : V}
    (p q : K.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (he : score w p = score w q) : p = q := by
  classical
  have hs := congrArg (fun c : Score => (ofLex c).2) he
  rw [score_secondary, score_secondary] at hs
  have hsets : p.edges.toFinset = q.edges.toFinset := by
    apply edgeCode_injective_on_finsets
    simpa only [List.sum_toFinset _ hp.isTrail.edges_nodup,
      List.sum_toFinset _ hq.isTrail.edges_nodup] using hs
  apply path_eq_of_edges_perm p q hp hq
  exact (List.perm_ext_iff_of_nodup hp.isTrail.edges_nodup hq.isTrail.edges_nodup).mpr
    (fun e => by simpa using congrArg (fun E : Finset (Sym2 V) => e ∈ E) hsets)

def Optimal (G : V → V → Prop) (w : V → V → ℝ≥0)
    {u v : V} (p : K.Walk u v) : Prop :=
  Allowed G p ∧ p.IsPath ∧ ∀ q : K.Walk u v, Allowed G q → score w p ≤ score w q

theorem exists_optimal (G : V → V → Prop) (w : V → V → ℝ≥0) (u v : V)
    (hex : ∃ p : K.Walk u v, Allowed G p) : ∃ p : K.Walk u v, Optimal G w p := by
  classical
  let A : Finset (K.Path u v) := univ.filter fun p => Allowed G p.val
  have hA : A.Nonempty := by
    obtain ⟨p, hp⟩ := hex
    exact ⟨p.toPath, mem_filter.mpr ⟨mem_univ _, allowed_bypass hp⟩⟩
  obtain ⟨p, hp, hmin⟩ := exists_min_image A (fun p => score w p.val) hA
  refine ⟨p.val, (mem_filter.mp hp).2, p.property, ?_⟩
  intro q hq
  exact (hmin q.toPath (mem_filter.mpr ⟨mem_univ _, allowed_bypass hq⟩)).trans
    (score_bypass_le w q)

theorem Optimal.unique {G : V → V → Prop} {w : V → V → ℝ≥0}
    {u v : V} {p q : K.Walk u v} (hp : Optimal G w p) (hq : Optimal G w q) : p = q :=
  score_injective_on_paths w p q hp.2.1 hq.2.1 (le_antisymm (hp.2.2 q hq.1) (hq.2.2 p hp.1))

/-- Original weights remain primary: the selected path is truly shortest. -/
theorem Optimal.shortest {G : V → V → Prop} {w : V → V → ℝ≥0}
    {u v : V} {p : K.Walk u v} (hp : Optimal G w p)
    (q : K.Walk u v) (hq : Allowed G q) :
    (p.darts.map fun d => (w d.fst d.snd : ℝ)).sum ≤
      (q.darts.map fun d => (w d.fst d.snd : ℝ)).sum := by
  rw [← score_primary, ← score_primary]
  exact Prod.Lex.monotone_fst_ofLex (hp.2.2 q hq)

/-- Every contiguous subwalk of the selected path is itself optimal. -/
theorem Optimal.subwalk {G : V → V → Prop} {w : V → V → ℝ≥0}
    {u v a b : V} {p : K.Walk u v} (hp : Optimal G w p)
    {q : K.Walk a b} (hsub : q.IsSubwalk p) : Optimal G w q := by
  obtain ⟨l, r, heq⟩ := hsub
  subst p
  have hall := (allowed_append G _ _).mp hp.1
  have hleft := (allowed_append G _ _).mp hall.1
  refine ⟨hleft.2, hp.2.1.of_append_left.of_append_right, ?_⟩
  intro z hz
  have hvalid := (allowed_append G (l.append z) r).mpr
    ⟨(allowed_append G l z).mpr ⟨hleft.1, hz⟩, hall.2⟩
  have hm := hp.2.2 ((l.append z).append r) hvalid
  simpa only [score_append, add_le_add_iff_right, add_le_add_iff_left] using hm

/-- Consistency: optimal paths with the same subpath endpoints use exactly
the same subpath, even when their overall demand endpoints differ. -/
theorem optimal_subpaths_eq {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t s' t' a b : V} {p : K.Walk s t} {p' : K.Walk s' t'}
    (hp : Optimal G w p) (hp' : Optimal G w p')
    {q q' : K.Walk a b} (hq : q.IsSubwalk p) (hq' : q'.IsSubwalk p') : q = q' :=
  (hp.subwalk hq).unique (hp'.subwalk hq')

end LinearDistancePreservers.ConsistentTiebreaking
