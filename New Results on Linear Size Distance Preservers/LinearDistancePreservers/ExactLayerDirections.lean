import LinearDistancePreservers.ExactLayerEncoding
import LinearDistancePreservers.LatticeVertices
import LinearDistancePreservers.PrimitiveDirections

namespace LinearDistancePreservers.DirectionEncoding
open SimpleGraph Finset DirectionGraph
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000

/-- A carry-free encoding realizes every sufficiently large prescribed layer
cardinality, rather than only perfect powers. The vector premise will be
discharged by the already proved lattice-hull count. -/
theorem exact_layer_directions {d k r N x : ℕ} (hr : 0<r) (hk : 0<k)
    (v : Fin x → Fin (d+1) → ℕ) (hinj : Function.Injective v)
    (hv : ∀ a i, v a i<r) (hrigid : AverageRigid v)
    (hN : ((k+1)*r)^(d+1)≤N) :
    ∃ w : Fin x → Unit → ℕ,
      Function.Injective w ∧ (∀ a i, w a i<N) ∧
      (∀ (s : Unit → ZMod N) (a : Fin x)
        (q : (graph w N k).Walk (point w s a 0) (point w s a (Fin.last k))),
        q.length≤k → q=canonicalWalk w s a) := by
  let B := (k+1)*r
  have hB : 0<B := Nat.mul_pos (by omega) hr
  have hrB : r≤B := by dsimp [B]; nlinarith
  have hkr : k*r<B := by dsimp [B]; nlinarith
  let w : Fin x → Unit → ℕ := fun a _ => encode B (v a)
  have hw (a : Fin x) (i : Unit) : w a i<r*B^d := encode_lt hrB (v a) (hv a)
  have hn : (k+1)*(r*B^d)≤N := by
    calc
      _ = B^(d+1) := by dsimp [B]; rw [pow_succ]; ring
      _ ≤ N := hN
  have hs : r*B^d≤N := (Nat.le_mul_of_pos_left _ (by omega)).trans hn
  refine ⟨w,?_,fun a i => (hw a i).trans_le hs,?_⟩
  · intro a b he
    apply hinj
    exact encode_injective hB (fun i => (hv a i).trans_le hrB)
      (fun i => (hv b i).trans_le hrB) (congrFun he ())
  · intro s a q hq
    apply canonical_unique_fixed_length w hw hn _ s a q hq
    intro a f hsum j
    funext i
    exact fixed_length_rigid hB hkr v hv hrigid a f (hsum ()) j


end LinearDistancePreservers.DirectionEncoding

namespace LinearDistancePreservers.DirectionEncoding
open SimpleGraph Finset DirectionGraph
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000

/-- All combinatorial conditions of the perfect family, with exact cardinality
N in every layer, follow for the encoded directions. -/
theorem exact_layer_perfect {d k r N x : ℕ} [NeZero N] (hr : 0<r) (hk : 0<k)
    (v : Fin x → Fin (d+1) → ℕ) (hinj : Function.Injective v)
    (hv : ∀ a i, v a i<r) (hrigid : AverageRigid v)
    (hN : ((k+1)*r)^(d+1)≤N) :
    ∃ w : Fin x → Unit → ℕ,
      Fintype.card (Unit → ZMod N)=N ∧
      (graph w N k).edgeFinset.card=k*N*x ∧
      Function.Injective (fun p : (Unit → ZMod N) × Fin x =>
        (canonicalWalk (k := k) w p.1 p.2).support) ∧
      (∀ u : Vertex Unit N k,
        Fintype.card {p : (Unit → ZMod N) × Fin x // u∈(canonicalWalk w p.1 p.2).support}=x) ∧
      (∀ e : Sym2 (Vertex Unit N k), e∈(graph w N k).edgeSet →
        ∃! p : (Unit → ZMod N) × Fin x, e∈(canonicalWalk w p.1 p.2).edges) ∧
      (∀ (s : Unit → ZMod N) (a : Fin x)
        (q : (graph w N k).Walk (point w s a 0) (point w s a (Fin.last k))),
        q.length≤k → q=canonicalWalk w s a) := by
  obtain ⟨w,hwi,hwb,hwu⟩ := exact_layer_directions hr hk v hinj hv hrigid hN
  refine ⟨w,?_,?_,canonical_support_injective w hwb hwi hk,?_,?_,hwu⟩
  · simp [ZMod.card]
  · have hE := graph_edge_count (n := N) (k := k) w hwb hwi
    simp only [Fintype.card_unit,pow_one,Fintype.card_fin] at hE
    simp only [edgeFinset,Set.toFinset_card,Fintype.card_eq_nat_card] at hE ⊢
    exact hE
  · intro u
    have hh := canonical_incidence w u
    simp only [Fintype.card_fin] at hh
    simp only [Fintype.card_eq_nat_card] at hh ⊢
    exact hh
  · exact canonical_edge_owner_unique w hwb hwi




/-- An empty family has exact incidence zero for every layer cardinality. -/
theorem zero_layer_family {N k : ℕ} [NeZero N] :
    ∃ w : Fin 0 → Unit → ℕ,
      Fintype.card (Unit → ZMod N)=N ∧
      (graph w N k).edgeFinset.card=k*N*0 ∧
      Function.Injective (fun p : (Unit → ZMod N) × Fin 0 =>
        (canonicalWalk (k := k) w p.1 p.2).support) ∧
      (∀ u : Vertex Unit N k,
        Fintype.card {p : (Unit → ZMod N) × Fin 0 // u∈(canonicalWalk w p.1 p.2).support}=0) ∧
      (∀ e : Sym2 (Vertex Unit N k), e∈(graph w N k).edgeSet →
        ∃! p : (Unit → ZMod N) × Fin 0, e∈(canonicalWalk w p.1 p.2).edges) ∧
      (∀ (s : Unit → ZMod N) (a : Fin 0)
        (q : (graph w N k).Walk (point w s a 0) (point w s a (Fin.last k))),
        q.length≤k → q=canonicalWalk w s a) := by
  let w : Fin 0 → Unit → ℕ := fun a => a.elim0
  have hw : ∀ a i, w a i<N := fun a => a.elim0
  have hi : Function.Injective w := by intro a; exact a.elim0
  refine ⟨w,by simp [ZMod.card],?_,?_,?_,?_,?_⟩
  · have hE := graph_edge_count (n := N) (k := k) w hw hi
    simp only [Fintype.card_unit,pow_one,Fintype.card_fin] at hE
    simp only [edgeFinset,Set.toFinset_card,Fintype.card_eq_nat_card] at hE ⊢
    exact hE
  · intro p; exact p.2.elim0
  · intro u
    have hh := canonical_incidence w u
    simp only [Fintype.card_fin] at hh
    simp only [Fintype.card_eq_nat_card] at hh ⊢
    exact hh
  · exact canonical_edge_owner_unique w hw hi
  · intro s a; exact a.elim0

end LinearDistancePreservers.DirectionEncoding

namespace LinearDistancePreservers.DirectionEncoding
open Finset DirectionGraph

/-- One radius factor for each dimension, including the elementary planar
case, valid for every positive integer scale and every smaller family size. -/
theorem uniform_bounded_directions (d : ℕ) (hd : 2≤d) :
    ∃ C : ℕ, 0<C ∧ ∀ b x : ℕ, 0<b → x≤b^(d*(d-1)) →
      ∃ v : Fin x → Fin d → ℕ, Function.Injective v ∧
        (∀ a i, v a i<C*b^(d+1)) ∧ AverageRigid v := by
  by_cases hd2 : d=2
  · subst d
    refine ⟨9,by omega,?_⟩
    intro b x hb hx
    have hx' : 4*x≤(2*b)^2 := by norm_num at hx; nlinarith
    obtain ⟨v,hi,hv,hr⟩ := PrimitiveDirections.exists_planar_directions_of_card hx'
    let w : Fin x → Fin 2 → ℕ := fun a i => v a (finTwoEquiv i)
    have hb3 : 0<b^3 := by positivity
    refine ⟨w,?_,?_,?_⟩
    · intro a c he
      apply hi
      funext q
      simpa [w] using congrFun he (finTwoEquiv.symm q)
    · intro a i
      have hh := hv a (finTwoEquiv i)
      dsimp [w]
      nlinarith only [hh,hb3]
    · intro m a f hsum j
      have hh := hr m a f (fun q => by simpa [w] using hsum (finTwoEquiv.symm q)) j
      funext i
      exact congrFun hh (finTwoEquiv i)
  · obtain ⟨n,rfl⟩ : ∃ n : ℕ, d=n+3 := ⟨d-3,by omega⟩
    obtain ⟨C,hC,hcount⟩ := LatticeHull.uniform_vertices n
    refine ⟨2*C+1,by omega,?_⟩
    intro b x hb hx
    have hx' : x≤(LatticeHull.vertices (LatticeHull.ball (n+3) (C*b^(n+4)))).card := by
      apply le_trans _ (hcount b hb)
      simpa only [show n+3-1=n+2 by omega] using hx
    obtain ⟨v,hi,hv,hr⟩ := LatticeHull.exists_directions hx'
    refine ⟨v,hi,?_,hr⟩
    intro a i
    have hh := hv a i
    have hbpow : 0<b^(n+4) := by positivity
    simpa only [show n+3+1=n+4 by omega] using
      hh.trans_le (show 2*(C*b^(n+4))+1≤(2*C+1)*b^(n+4) by nlinarith)

end LinearDistancePreservers.DirectionEncoding
