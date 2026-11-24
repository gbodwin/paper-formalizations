import DirectedFlowCutGap.ConcurrentEdgeOracle
import DirectedFlowCutGap.FractionalCoverGraphOracle

/-! A joint vertex column records one endpoint-excluding shortest path for
each demand, with multiplicity on the original internal vertices. -/
namespace DirectedFlowCutGap.ConcurrentVertexOracle

open scoped BigOperators
open BinaryFractionalWalkOracle (Adjacency Candidate graph)
open ConcurrentEdgeOracle (Edge Resource edge resource encoded Profile)
open FractionalCover (Row value value_ofFn)
open MultiplicityCover (Column Oracle coeff length)
open FractionalCoverGraphOracle (outgoing internalColumn)
open IntegralNetworkFlow.Tabulated

variable {m n : ℕ}

def lifted (s : Fin n) (y : Row n) : Row (n*n) :=
  Vector.ofFn fun i => outgoing y s (edge i)

theorem lifted_read (s : Fin n) (y : Row n) (e : Edge n) :
    value (lifted s y) (resource e) = outgoing y s e := by
  simp only [lifted,value_ofFn,ConcurrentEdgeOracle.edge_resource]

def path (A : Adjacency n) (y : Row n) (d : Edge n) : Option (Candidate n) :=
  ConcurrentEdgeOracle.path A (encoded (lifted d.1 y)) d

theorem path_minimum (A : Adjacency n) (y : Row n) (nonnegative : ∀ i, 0 ≤ value y i)
    (d : Edge n) (reach : Nonempty (SimplePath (graph A) d.1 d.2)) :
    ∃ q : Candidate n, ∃ p : SimplePath (graph A) d.1 d.2,
      path A y d = some q ∧ q.edges = FlowTable.edgeList p ∧
      ∀ other : SimplePath (graph A) d.1 d.2,
        FractionalCover.length y p.internalVertices ≤ FractionalCover.length y other.internalVertices := by
  have liftNonneg (i : Resource n) : 0 ≤ value (lifted d.1 y) i := by
    simp only [lifted,value_ofFn]
    exact FractionalCoverGraphOracle.outgoing_nonneg y d.1 nonnegative (edge i)
  obtain ⟨q,p,read,retained,least⟩ :=
    ConcurrentEdgeOracle.path_minimum A (lifted d.1 y) liftNonneg d reach
  refine ⟨q,p,read,retained,?_⟩
  intro other
  have compare := least other
  simp only [lifted_read,FractionalCoverGraphOracle.outgoing_pathCost] at compare
  exact compare

def cells (A : Adjacency n) (P : Vector (Edge n) m) (y : Row n) : Vector (Option (Candidate n)) m :=
  Vector.ofFn fun j => path A y (P.get j)

def column (P : Vector (Edge n) m) (ps : Vector (Option (Candidate n)) m) : Column n :=
  Vector.ofFn fun v =>
    ∑ j : Fin m,
      if ((ps.get j).map fun q => decide (v ∈ internalColumn (P.get j).1 (P.get j).2 q.edges)).getD false
      then 1 else 0

noncomputable def profileCoeff (A : Adjacency n) (P : Vector (Edge n) m)
    (paths : Profile A P) (i : Fin n) : ℕ :=
  ∑ j : Fin m, if i ∈ (paths j).internalVertices then 1 else 0

def columns (A : Adjacency n) (P : Vector (Edge n) m) : Set (Column n) :=
  {q | ∃ paths : Profile A P, ∀ i, coeff q i = profileCoeff A P paths i}

def active (q : Column n) : List (Fin n) :=
  (List.finRange n).filter fun i => decide (0 < coeff q i)

def rate (c : Row n) (q : Column n) (i : Fin n) : ℚ :=
  value c i/(coeff q i : ℚ)

def pivot (hn : 0 < n) (c : Row n) (q : Column n) : Fin n :=
  ((active q).argmin (rate c q)).getD ⟨0,hn⟩

theorem pivot_spec (hn : 0 < n) (c : Row n) (q : Column n) (present : ∃ i, 0 < coeff q i) :
    0 < coeff q (pivot hn c q) ∧ ∀ i, 0 < coeff q i → rate c q (pivot hn c q) ≤ rate c q i := by
  have member (i : Fin n) : i ∈ active q ↔ 0 < coeff q i := by simp [active]
  cases found : (active q).argmin (rate c q) with
  | none =>
    obtain ⟨i,nonzero⟩ := present
    have ok := (member i).mpr nonzero
    rw [List.argmin_eq_none.mp found] at ok
    exact (List.not_mem_nil ok).elim
  | some i =>
    have sample : i ∈ (active q).argmin (rate c q) := by simp [found]
    simp only [pivot,found,Option.getD_some]
    exact ⟨(member i).mp (List.argmin_mem sample),
      fun j hj => List.le_of_mem_argmin ((member j).mpr hj) sample⟩

def oracle (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m) (c : Row n) : Oracle n := fun y =>
  let q := column P (cells A P y)
  ⟨q,pivot hn c q⟩

private theorem cell (A : Adjacency n) (P : Vector (Edge n) m) (y : Row n) (j : Fin m) :
    (cells A P y).get j = path A y (P.get j) := by
  cases j
  exact Vector.getElem_ofFn _

private theorem column_eq (A : Adjacency n) (P : Vector (Edge n) m) (y : Row n)
    (paths : Profile A P) (candidates : Fin m → Candidate n)
    (taken : ∀ j, path A y (P.get j) = some (candidates j))
    (recorded : ∀ j, (candidates j).edges = FlowTable.edgeList (paths j)) (v : Fin n) :
    coeff (column P (cells A P y)) v = profileCoeff A P paths v := by
  classical
  simp only [coeff,column,Vector.getElem_ofFn,profileCoeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [cell,taken,Option.map_some,Option.getD_some,recorded,FractionalCoverGraphOracle.internalColumn_eq]
  simp

theorem profile_eval {K : Type*} [Semiring K] (A : Adjacency n) (P : Vector (Edge n) m)
    (q : Column n) (paths : Profile A P) (equal : ∀ i, coeff q i = profileCoeff A P paths i)
    (w : Fin n → K) :
    (∑ i, (coeff q i : K)*w i) = ∑ j : Fin m, ∑ v ∈ (paths j).internalVertices, w v := by
  classical
  simp only [equal,profileCoeff,Nat.cast_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have same : (Finset.univ : Finset (Fin n)).filter (· ∈ (paths j).internalVertices) =
      (paths j).internalVertices := by ext i; simp
  simp only [apply_ite,Nat.cast_one,Nat.cast_zero,ite_mul,one_mul,zero_mul]
  rw [← Finset.sum_filter,same]

theorem oracle_correct (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m) (c : Row n)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) (noArc : ¬ (graph A).Adj (P.get d).1 (P.get d).2) :
    MultiplicityCover.OracleCorrect c (columns A P) (oracle hn A P c) := by
  classical
  have retained (y : Row n) (pos : ∀ i, 0 < value y i) : ∃ paths : Profile A P,
      (∀ i, coeff (oracle hn A P c y).column i = profileCoeff A P paths i) ∧
      ∀ other : Profile A P, ∀ j,
        FractionalCover.length y (paths j).internalVertices ≤ FractionalCover.length y (other j).internalVertices := by
    have found (j : Fin m) := path_minimum A y (fun i => (pos i).le) (P.get j) (reach j)
    choose q paths taken recorded comparison using found
    exact ⟨paths,column_eq A P y paths q taken recorded,fun other j => comparison j (other j)⟩
  have pivotGood (y : Row n) (pos : ∀ i, 0 < value y i) :
      let q := (oracle hn A P c y).column
      0 < coeff q (pivot hn c q) ∧ ∀ i, 0 < coeff q i → rate c q (pivot hn c q) ≤ rate c q i := by
    obtain ⟨paths,shape,_⟩ := retained y pos
    obtain ⟨v,inside⟩ := FractionalCoverGraphOracle.internal_nonempty_of_nonadjacent (paths d) different noArc
    apply pivot_spec
    refine ⟨v,?_⟩
    rw [shape,profileCoeff]
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨d,Finset.mem_univ _,by simp [inside]⟩
  refine ⟨?_,fun y pos => (pivotGood y pos).1,fun y pos => (pivotGood y pos).2,?_⟩
  · intro y pos
    obtain ⟨paths,shape,_⟩ := retained y pos
    exact ⟨paths,shape⟩
  · intro y pos q ways
    obtain ⟨paths,shape,least⟩ := retained y pos
    obtain ⟨other,written⟩ := ways
    unfold length
    rw [profile_eval A P _ paths shape,profile_eval A P _ other written]
    exact Finset.sum_le_sum (fun j _ => least other j)

end DirectedFlowCutGap.ConcurrentVertexOracle
