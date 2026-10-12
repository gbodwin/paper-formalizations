import MinorFreeSpanners.BranchingPhaseConservation

/-! Turn the actual residual degree bound into a concrete spanning simple
path of every nonempty connected residual component. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem interior_path_boundary_degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) {a b x y : V} (p : G.Walk a b)
    (hp : p.IsPath) (hs : ∀ v∈p.support,v∈S)
    (hx : x∈p.support) (hxa : x≠a) (hxb : x≠b)
    (hy : y∈S) (hyp : y∉p.support) (hxy : G.Adj x y) :
    3≤((G.neighborFinset x)∩S).card := by
  classical
  obtain ⟨q,r,hq,hr,hqr⟩ := hp.mem_support_iff_exists_append.mp hx
  have hqn : ¬q.Nil := Walk.not_nil_of_ne hxa.symm
  have hrn : ¬r.Nil := Walk.not_nil_of_ne hxb
  have hqm : q.penultimate∈q.support := q.getVert_mem_support _
  have hrm : r.snd∈r.support := r.getVert_mem_support _
  have hqa : G.Adj x q.penultimate := (q.adj_penultimate hqn).symm
  have hra : G.Adj x r.snd := r.adj_snd hrn
  have hqp : q.penultimate∈p.support := by rw [hqr,Walk.mem_support_append_iff];exact Or.inl hqm
  have hrp : r.snd∈p.support := by rw [hqr,Walk.mem_support_append_iff];exact Or.inr hrm
  have hne : q.penultimate≠r.snd := (hqr ▸ hp).ne_of_mem_support_of_append hra.ne' hqm hrm
  have hqy : q.penultimate≠y := fun h => hyp (h ▸ hqp)
  have hry : r.snd≠y := fun h => hyp (h ▸ hrp)
  have hsub : {q.penultimate,r.snd,y}⊆G.neighborFinset x∩S := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl|rfl
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hqa,hs _ hqp⟩
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hra,hs _ hrp⟩
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxy,hy⟩
  have hcard := Finset.card_le_card hsub
  simpa [hne,hqy,hry] using hcard

 theorem connected_forest_degree_two_path {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (hS : ConnectedWithin G S) (hne : S.Nonempty)
    (hdeg : ∀ x∈S,((G.neighborFinset x)∩S).card≤2) :
    ∃ a∈S,∃ b∈S,∃ p : G.Walk a b,p.IsPath ∧ p.support.toFinset=S := by
  classical
  obtain ⟨a,ha,b,hb,p,hp,hps,hmax⟩ := exists_max_mass_path G hG S hne (fun _ => 1)
  have hsub : p.support.toFinset⊆S := fun v hv => hps v (List.mem_toFinset.mp hv)
  refine ⟨a,ha,b,hb,p,hp,?_⟩
  by_contra hneq
  have hlt : p.support.toFinset.card<S.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hneq⟩)
  obtain ⟨x,hxp,y,hy,hyp,hxy⟩ := hS.boundary hsub
    ⟨a,List.mem_toFinset.mpr p.start_mem_support⟩ hlt
  have hyout : y∉p.support := by simpa using hyp
  have hxa : x≠a := by
    intro he;subst x
    have h := max_mass_path_start_neighbor G hG S (fun _ => 1) (by intros;norm_num)
      p hp hps hmax hy hxy
    exact hyout (h.symm ▸ p.getVert_mem_support 1)
  have hxb : x≠b := by
    intro he;subst x
    have h := max_mass_path_start_neighbor G hG S (fun _ => 1) (by intros;norm_num)
      p.reverse hp.reverse (by simpa using hps)
      (by intro i j q hq hqs;simpa only [pathMass_reverse] using hmax i j q hq hqs) hy hxy
    have hh : y∈p.reverse.support := h.symm ▸ p.reverse.getVert_mem_support 1
    exact hyout (by simpa using hh)
  have hd := interior_path_boundary_degree G S p hp hps (List.mem_toFinset.mp hxp) hxa hxb hy hyout hxy
  have hh := hdeg x (hsub hxp)
  omega

end MinorFreeSpanners
