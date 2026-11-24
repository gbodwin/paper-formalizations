import DirectedFlowCutGap.MultiplicityCoverAnalysis
import DirectedFlowCutGap.RationalSparsestEdgeDistances
import DirectedFlowCutGap.BinaryRawRational
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.MinMax

/-! A concurrent-flow column contains one shortest path for every demand.
Resource coefficients count how many of those paths traverse each arc. -/
namespace DirectedFlowCutGap.ConcurrentEdgeOracle

open scoped BigOperators NNRat
open BinaryFractionalWalkOracle (Adjacency Candidate graph shortest decodeCost)
open RationalEdgeThresholds (Weights cost)
open FractionalCover (Row value)
open MultiplicityCover (Column coeff length Choice Oracle)
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

variable {m n : ℕ}

abbrev Resource (n : ℕ) := Fin (n*n)
abbrev Edge (n : ℕ) := Fin n × Fin n

def resource (e : Edge n) : Resource n := finProdFinEquiv e
def edge (i : Resource n) : Edge n := finProdFinEquiv.symm i

@[simp] theorem resource_edge (i : Resource n) : resource (edge i) = i :=
  finProdFinEquiv.apply_symm_apply i

@[simp] theorem edge_resource (e : Edge n) : edge (resource e) = e :=
  finProdFinEquiv.symm_apply_apply e

private def nonnegativeRat (a : ℚ) : ℚ≥0 := ⟨max a 0, le_max_right _ _⟩

def encoded (y : Row (n*n)) : Weights n :=
  Vector.ofFn fun u => Vector.ofFn fun v =>
    let a := value y (resource (u,v))
    (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat (nonnegativeRat a))).1

theorem read_length (y : Row (n*n)) (nonnegative : ∀ i, 0 ≤ value y i) (e : Edge n) :
    FractionalCoverRawCore.rational (decodeCost (cost (encoded y)) e) = value y (resource e) := by
  rcases e with ⟨u,v⟩
  simp only [cost, encoded, decodeCost, Vector.getElem_ofFn, BinaryRawRational.encode_value,
    FractionalCoverRawCore.rational, RawNonnegativeRational.Code.value_ofNNRat]
  change max (value y (resource (u,v))) 0 = value y (resource (u,v))
  exact max_eq_left (nonnegative _)

def path (A : Adjacency n) (y : Weights n) (e : Edge n) : Option (Candidate n) :=
  (shortest (ResidualSearch.Enumeration.fin n) A (cost y) e.1 e.2).1

theorem path_minimum (A : Adjacency n) (y : Row (n*n)) (nonnegative : ∀ i, 0 ≤ value y i)
    (e : Edge n) (reachable : Nonempty (SimplePath (graph A) e.1 e.2)) :
    ∃ q : Candidate n, ∃ p : SimplePath (graph A) e.1 e.2,
      path A (encoded y) e = some q ∧ q.edges = FlowTable.edgeList p ∧
        ∀ alternative : SimplePath (graph A) e.1 e.2,
          FractionalCoverWalkOracle.pathCost (fun f => value y (resource f)) p ≤
            FractionalCoverWalkOracle.pathCost (fun f => value y (resource f)) alternative := by
  let E := ResidualSearch.Enumeration.fin n
  let c := cost (encoded y)
  let C := fun f => FractionalCoverRawCore.rational (decodeCost c f)
  have read : C = fun f => value y (resource f) := funext (read_length y nonnegative)
  have cpos (f : Edge n) : 0 ≤ C f := by rw [read]; exact nonnegative _
  have binary := BinaryFractionalWalkOracle.shortest_decode E A c e.1 e.2
  have rational := congrArg Prod.fst (FractionalCoverRawOracle.shortest_refines E
    (graph A) (decodeCost c) e.1 e.2)
  change ((FractionalCoverRawOracle.shortest E (graph A) (decodeCost c) e.1 e.2).1.map
    FractionalCoverRawOracle.decode) = (FractionalCoverPathOracle.shortest E (graph A) C e.1 e.2).1
    at rational
  rw [← binary, Option.map_map] at rational
  change (path A (encoded y) e).map _ = _ at rational
  cases found : path A (encoded y) e with
  | none =>
    rw [found, Option.map_none] at rational
    exact (((FractionalCoverPathOracle.shortest_none_iff E (graph A) C cpos e.1 e.2).mp
      rational.symm) reachable).elim
  | some q =>
    rw [found, Option.map_some] at rational
    obtain ⟨p, edges, objective⟩ := FractionalCoverPathOracle.shortest_valid E (graph A) C
      e.1 e.2 rational.symm
    refine ⟨q,p,rfl,edges,?_⟩
    intro alternative
    obtain ⟨r, accepted, minimal⟩ := FractionalCoverPathOracle.shortest_minimum E (graph A) C cpos
      e.1 e.2 alternative
    have equal := Option.some.inj (rational.trans accepted)
    rw [← equal, objective, read] at minimal
    exact minimal

abbrev Profile (A : Adjacency n) (P : Vector (Edge n) m) :=
  ∀ j : Fin m, SimplePath (graph A) (P.get j).1 (P.get j).2

noncomputable def profileCoeff (A : Adjacency n) (P : Vector (Edge n) m)
    (p : Profile A P) (i : Resource n) : ℕ :=
  ∑ d : Fin m, if edge i ∈ (p d).edges then 1 else 0

def cells (A : Adjacency n) (P : Vector (Edge n) m) (y : Row (n*n)) :
    Vector (Option (Candidate n)) m :=
  let stored := encoded y
  Vector.ofFn fun j => path A stored (P.get j)

def column (paths : Vector (Option (Candidate n)) m) : Column (n*n) :=
  Vector.ofFn fun i => ∑ d : Fin m,
    if (Option.map (fun q : Candidate n => q.edges.contains (edge i)) (paths.get d)).getD false
      then 1 else 0

def columns (A : Adjacency n) (P : Vector (Edge n) m) : Set (Column (n*n)) :=
  {q | ∃ p : Profile A P, ∀ i, coeff q i = profileCoeff A P p i}

def active (q : Column (n*n)) : List (Resource n) :=
  (List.finRange (n*n)).filter fun i => decide (0 < coeff q i)

def rate (c : Row (n*n)) (q : Column (n*n)) (i : Resource n) : ℚ :=
  value c i / (coeff q i : ℚ)

def pivot (hn : 0 < n) (c : Row (n*n)) (q : Column (n*n)) : Resource n :=
  ((active q).argmin (rate c q)).getD ⟨0, Nat.mul_pos hn hn⟩

theorem pivot_spec (hn : 0 < n) (c : Row (n*n)) (q : Column (n*n))
    (present : ∃ i, 0 < coeff q i) : 0 < coeff q (pivot hn c q) ∧
      ∀ i, 0 < coeff q i → rate c q (pivot hn c q) ≤ rate c q i := by
  have member (i : Resource n) : i ∈ active q ↔ 0 < coeff q i := by
    simp [active]
  cases found : (active q).argmin (rate c q) with
  | none =>
    obtain ⟨i, nonzero⟩ := present
    have impossible := (member i).mpr nonzero
    rw [List.argmin_eq_none.mp found] at impossible
    exact (List.not_mem_nil impossible).elim
  | some i =>
    have selected : i ∈ (active q).argmin (rate c q) := by simp [found]
    simp only [pivot, found, Option.getD_some]
    exact ⟨(member i).mp (List.argmin_mem selected),
      fun j hj => List.le_of_mem_argmin (member j |>.mpr hj) selected⟩

def oracle (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c : Row (n*n)) : Oracle (n*n) := fun y =>
  let q := column (n := n) (cells A P y)
  ⟨q, pivot hn c q⟩

private theorem cell (A : Adjacency n) (P : Vector (Edge n) m) (y : Row (n*n)) (d : Fin m) :
    (cells A P y).get d = path A (encoded y) (P.get d) := by
  cases d
  exact Vector.getElem_ofFn _

private theorem column_eq (A : Adjacency n) (P : Vector (Edge n) m) (y : Row (n*n))
    (paths : Profile A P) (Q : Fin m → Candidate n)
    (reached : ∀ d, path A (encoded y) (P.get d) = some (Q d))
    (edges : ∀ d, (Q d).edges = FlowTable.edgeList (paths d)) (i : Resource n) :
    coeff (column (n := n) (cells A P y)) i = profileCoeff A P paths i := by
  classical
  simp only [coeff, column, Vector.getElem_ofFn, profileCoeff]
  apply Finset.sum_congr rfl
  intro d _
  rw [cell, reached d, Option.map_some, Option.getD_some, edges d]
  congr 1
  simp [FlowTable.edgeList, SimplePath.mem_edges, eq_comm]

theorem profile_eval {K : Type*} [Semiring K] (A : Adjacency n) (P : Vector (Edge n) m)
    (q : Column (n*n)) (paths : Profile A P)
    (encodedColumn : ∀ i, coeff q i = profileCoeff A P paths i) (w : Resource n → K) :
    (∑ i, (coeff q i : K) * w i) = ∑ d : Fin m, ∑ e ∈ (paths d).edges, w (resource e) := by
  classical
  simp only [encodedColumn, profileCoeff, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  let p := paths d
  let f (i : Resource n) : K := (if edge i ∈ p.edges then (1 : ℕ) else 0 : ℕ) * w i
  change (∑ i, f i) = ∑ e ∈ p.edges, w (resource e)
  rw [← (finProdFinEquiv : Edge n ≃ Resource n).sum_comp f]
  change (∑ e : Edge n, f (resource e)) = ∑ e ∈ p.edges, w (resource e)
  simp only [f, edge_resource, apply_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
  have filter : (Finset.univ : Finset (Edge n)).filter (· ∈ p.edges) = p.edges := by
    ext e
    simp
  rw [← Finset.sum_filter, filter]

theorem profile_length (A : Adjacency n) (P : Vector (Edge n) m) (q : Column (n*n))
    (paths : Profile A P) (encodedColumn : ∀ i, coeff q i = profileCoeff A P paths i)
    (y : Row (n*n)) :
    length y q = ∑ d : Fin m, FractionalCoverWalkOracle.pathCost
      (fun f => value y (resource f)) (paths d) := by
  exact profile_eval A P q paths encodedColumn (value y)

private theorem positive_coefficient (A : Adjacency n) (P : Vector (Edge n) m)
    (paths : Profile A P) (q : Column (n*n))
    (encodedColumn : ∀ i, coeff q i = profileCoeff A P paths i)
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) :
    ∃ i, 0 < coeff q i := by
  classical
  let p := paths d
  have long : 0 < p.edgeLength := by
    by_contra! short
    have zero : p.edgeLength = 0 := Nat.eq_zero_of_le_zero short
    have same : (0 : Fin (p.edgeLength+1)) = Fin.last p.edgeLength := Fin.ext (by simp [zero])
    exact different (p.source_eq.symm.trans ((congrArg p.vertex same).trans p.target_eq))
  let e := p.edgeAt ⟨0,long⟩
  let i := resource e
  have inPath : edge i ∈ (paths d).edges := by
    rw [show edge i = e from edge_resource e]
    exact p.edgeAt_mem_edges ⟨0,long⟩
  refine ⟨i, ?_⟩
  rw [encodedColumn, profileCoeff]
  apply Finset.sum_pos'
  · exact fun _ _ => Nat.zero_le _
  · exact ⟨d, Finset.mem_univ _, by simp [inPath]⟩

theorem oracle_correct (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m) (c : Row (n*n))
    (reachable : ∀ d : Fin m, Nonempty (SimplePath (graph A) (P.get d).1 (P.get d).2))
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2) :
    MultiplicityCover.OracleCorrect c (columns A P) (oracle hn A P c) := by
  classical
  have output (y : Row (n*n)) (positive : ∀ i, 0 < value y i) :
      ∃ pathSet : Profile A P,
        (∀ i, coeff (oracle hn A P c y).column i = profileCoeff A P pathSet i) ∧
        (∀ alt : Profile A P, ∀ j,
          FractionalCoverWalkOracle.pathCost (fun e => value y (resource e)) (pathSet j) ≤
            FractionalCoverWalkOracle.pathCost (fun e => value y (resource e)) (alt j)) := by
    have each (j : Fin m) := path_minimum A y (fun i => (positive i).le) (P.get j) (reachable j)
    choose Q p reached edges minimal using each
    exact ⟨p, column_eq A P y p Q reached edges, fun alt j => minimal j (alt j)⟩
  have pivotValid (y : Row (n*n)) (positive : ∀ i, 0 < value y i) :
      let q := (oracle hn A P c y).column
      0 < coeff q (pivot hn c q) ∧
        ∀ i, 0 < coeff q i → rate c q (pivot hn c q) ≤ rate c q i := by
    obtain ⟨p, q, _⟩ := output y positive
    exact pivot_spec hn c (oracle hn A P c y).column
      (positive_coefficient A P p _ q d different)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y positive
    obtain ⟨p, q, _⟩ := output y positive
    exact ⟨p,q⟩
  · intro y positive
    exact (pivotValid y positive).1
  · intro y positive i present
    exact (pivotValid y positive).2 i present
  · intro y positive q member
    obtain ⟨p, actual, minimal⟩ := output y positive
    obtain ⟨alt, written⟩ := member
    rw [profile_length A P _ p actual y, profile_length A P q alt written y]
    exact Finset.sum_le_sum (fun j _ => minimal alt j)

end DirectedFlowCutGap.ConcurrentEdgeOracle
