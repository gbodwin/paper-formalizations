import LinearDistancePreservers.SphereDirections
import LinearDistancePreservers.UnweightedPadding

/-! Unweighted subset-preserver witnesses with the outer direction set
constructed using mathlib's quantitative Behrend theorem. The final
theorem also constructs the inner directions, using a common sphere.
Only explicit numerical capacity conditions remain in its statement.
The sphere count is weaker than the sharp fixed-dimension count in
Theorem 6, so this is not a claim of the full asymptotic Theorem 4. -/
namespace LinearDistancePreservers.BehrendProduct
open SimpleGraph Finset DirectionGraph DirectionObstacle
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

variable {D J : Type*} [Fintype D] [Fintype J]
  {n M k r R : ℕ} [NeZero n] [NeZero M]

/-- An actual graph with exactly `2*M` terminals, with its entire edge
set forced. No outer direction family or path-uniqueness hypothesis is
assumed: the required slopes are selected from a progression-free set. -/
theorem exists_product (v : J → D → ℕ)
    (hinj : Function.Injective v) (hvr : ∀ a d, v a d < r)
    (hn : (k+1)*r ≤ n) (hc : AverageRigid v) (hM : 3*R ≤ M)
    (hcap : n^(Fintype.card D)*Fintype.card J ≤ rothNumberNat R) :
    ∃ (G : SimpleGraph (ProductVertex D Unit n M k))
      (S : Finset (ProductVertex D Unit n M k)),
      S.card = 2*M ∧ UnweightedPadding.Rigid G S ∧
      G.edgeFinset.card = M*n^(Fintype.card D)*Fintype.card J*(k+2) := by
  classical
  have hv : ∀ a d, v a d < n := by
    intro a d
    exact (hvr a d).trans_le ((Nat.le_mul_of_pos_left r (by omega)).trans hn)
  obtain ⟨a,ha,haR,hfree⟩ := BehrendPorts.exists_ports
    (J := Port D J n) (R := R) (by simpa [Port,ZMod.card] using hcap)
  let z := BehrendPorts.direction a
  have hz : ∀ a d, z a d < M := fun j _ => (haR j).trans_le (by omega)
  have hzinj : Function.Injective z := BehrendPorts.direction_injective ha
  let data := DirectionObstacle.data (k := k) v z hv hinj hz hzinj
  let G := ObstacleProduct.graph data
  let S := terminals (D := D) (Q := Unit) (n := n) (M := M) (k := k)
  have hout : ObstacleProduct.OuterUnique data :=
    BehrendPorts.outer_unique v a hv hinj ha haR hM hfree
  have hin : ObstacleProduct.InnerUnique data :=
    DirectionObstacle.inner_unique v z hv hinj hz hzinj hvr hn hc
  have hcount (H : SimpleGraph (ProductVertex D Unit n M k)) (hH : H ≤ G)
      (hp : ∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) :
      H.edgeFinset.card = M*n^(Fintype.card D)*Fintype.card J*(k+2) := by
    have he := ObstacleProduct.preserver_edge_count data hout hin H hH
      (fun b j => hp _ (left_mem_terminals _) _ (right_mem_terminals _))
    simpa [Port,ZMod.card,mul_assoc] using he
  have hG := hcount G le_rfl (by intros; rfl)
  refine ⟨G,S,by simpa [S] using (terminals_card (D := D) (Q := Unit)
    (n := n) (M := M) (k := k)),?_,hG⟩
  intro H hH hp
  apply edgeFinset_inj.mp
  exact eq_of_subset_of_card_le (edgeFinset_mono hH) ((hG.trans (hcount H hH hp).symm).le)

/-- Explicit Behrend-capacity version of the graph construction. -/
theorem exists_product_of_exp (v : J → D → ℕ)
    (hinj : Function.Injective v) (hvr : ∀ a d, v a d < r)
    (hn : (k+1)*r ≤ n) (hc : AverageRigid v) (hM : 3*R ≤ M)
    (hcap : ((n^(Fintype.card D)*Fintype.card J : ℕ) : ℝ) ≤
      (R : ℝ)*Real.exp (-4*Real.sqrt (Real.log R))) :
    ∃ (G : SimpleGraph (ProductVertex D Unit n M k))
      (S : Finset (ProductVertex D Unit n M k)),
      S.card = 2*M ∧ UnweightedPadding.Rigid G S ∧
      G.edgeFinset.card = M*n^(Fintype.card D)*Fintype.card J*(k+2) := by
  apply exists_product v hinj hvr hn hc hM
  exact_mod_cast hcap.trans Behrend.roth_lower_bound

/-- Exact-size unweighted lower bound. Both direction families and the
entire graph are constructed. The hypotheses are solely numerical.
Every S×S-preserving subgraph keeps the stated number of distinct edges. -/
theorem sphere_lower_bound_of_roth {d x N T : ℕ}
    (hsphere : x*(d*(r-1)^2+1) ≤ r^d)
    (hn : (k+1)*r ≤ n) (hM : 3*R ≤ M)
    (hcap : n^d*x ≤ rothNumberNat R)
    (hN : 2*M+M*(k+1)*n^d ≤ N) (hT : 2*M ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        H.edgeFinset.card = M*n^d*x*(k+2) := by
  classical
  obtain ⟨v,hinj,hvr,hc⟩ := SphereDirections.exists_directions hsphere
  obtain ⟨G,S,hS,hG,hE⟩ := exists_product (n := n) (M := M) (k := k)
    v hinj hvr hn hc hM (by simpa using hcap)
  have hv : Fintype.card (ProductVertex (Fin d) Unit n M k) ≤ N := by
    simpa [ProductVertex,ObstacleProduct.Vertex,DirectionGraph.Vertex,ZMod.card,
      mul_assoc,two_mul,add_assoc,add_left_comm,add_comm] using hN
  have hST : S.card ≤ T := hS.le.trans hT
  obtain ⟨K,S',hS',hK,hE'⟩ := UnweightedPadding.pad G S hG hv hST hTN
  refine ⟨K,S',hS',?_⟩
  intro H hH hp
  have heq : H = K := hK H hH hp
  subst H
  simp only [Fintype.card_fin] at hE
  simp only [edgeFinset,Set.toFinset_card,Fintype.card_eq_nat_card] at hE hE' ⊢
  exact hE'.trans hE

/-- Explicit exponential capacity, from the imported quantitative
Behrend theorem, gives the exact-size graph lower bound. -/
theorem sphere_lower_bound {d x N T : ℕ}
    (hsphere : x*(d*(r-1)^2+1) ≤ r^d)
    (hn : (k+1)*r ≤ n) (hM : 3*R ≤ M)
    (hcap : ((n^d*x : ℕ) : ℝ) ≤ (R : ℝ)*Real.exp (-4*Real.sqrt (Real.log R)))
    (hN : 2*M+M*(k+1)*n^d ≤ N) (hT : 2*M ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        H.edgeFinset.card = M*n^d*x*(k+2) := by
  apply sphere_lower_bound_of_roth hsphere hn hM _ hN hT hTN
  exact_mod_cast hcap.trans Behrend.roth_lower_bound

/-- The same lower bound with only natural-number inequalities as
inputs. The inner and outer dimensions may be selected independently. -/
theorem integer_lower_bound {d x N T q b : ℕ}
    (hsphere : x*(d*(r-1)^2+1) ≤ r^d)
    (hn : (k+1)*r ≤ n) (hM : 3*((2*b-1)^q) ≤ M)
    (hcap : (n^d*x)*(q*(b-1)^2+1) ≤ b^q)
    (hN : 2*M+M*(k+1)*n^d ≤ N) (hT : 2*M ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        H.edgeFinset.card = M*n^d*x*(k+2) := by
  exact sphere_lower_bound_of_roth hsphere hn hM
    (BehrendPorts.roth_capacity hcap) hN hT hTN

end LinearDistancePreservers.BehrendProduct
