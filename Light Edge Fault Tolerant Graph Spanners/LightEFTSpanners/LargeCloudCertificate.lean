import LightEFTSpanners.GenericBlowupFailure

/-! A genuine replacement connectivity certificate at a larger cloud size.
This changes the vertex scaling and weight loss and does not recover the
paper's square-root-cloud lower bound. -/
namespace LightEFTSpanners.GenericBlowupFailure
open SimpleGraph Finset
variable {V I : Type*} [Fintype I]

theorem exists_clean_cloud {u v : V} (huv : u≠v)
    (F : Finset (Sym2 (V×I))) (hcard : F.card < Fintype.card I) :
    ∃ i : I, ∀ j : I, s((u,i),(v,j)) ∉ F := by
  classical
  by_contra! hh
  choose j hj using hh
  have hinj : Function.Injective (fun i : I => (s((u,i),(v,j i)) : Sym2 (V×I))) := by
    intro a b he
    rcases Sym2.eq_iff.mp he with he | he
    · exact congrArg Prod.snd he.1
    · exact (huv (congrArg Prod.fst he.1)).elim
  have hsub : univ.image (fun i : I => (s((u,i),(v,j i)) : Sym2 (V×I))) ⊆ F := by
    intro e he
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    exact hj i
  have hc := card_le_card hsub
  rw [card_image_of_injective _ hinj,card_univ] at hc
  omega

/-- Each blown-up base edge is connected after fewer faults than cloud vertices. -/
theorem cross_reachable_afterFaults {T : SimpleGraph V} {u v : V}
    (huv : T.Adj u v) (F : Finset (Sym2 (V×I)))
    (hcard : F.card < Fintype.card I) (i j : I) :
    (afterFaults (lift (I:=I) T) F).Reachable (u,i) (v,j) := by
  obtain ⟨a,ha⟩ := exists_clean_cloud huv.ne F hcard
  obtain ⟨b,hb⟩ := exists_clean_cloud huv.ne.symm F hcard
  have left (x : I) : (afterFaults (lift (I:=I) T) F).Adj (u,x) (v,b) := by
    refine deleteEdges_adj.mpr ⟨huv,?_⟩
    simpa only [Sym2.eq_swap,Finset.mem_coe] using hb x
  have right (y : I) : (afterFaults (lift (I:=I) T) F).Adj (u,a) (v,y) :=
    deleteEdges_adj.mpr ⟨huv,ha y⟩
  exact (left i).reachable.trans ((right b).reachable.symm.trans (right j).reachable)

theorem same_cloud_reachable_afterFaults {T : SimpleGraph V} {u v : V}
    (huv : T.Adj u v) (F : Finset (Sym2 (V×I)))
    (hcard : F.card < Fintype.card I) (i j : I) :
    (afterFaults (lift (I:=I) T) F).Reachable (u,i) (u,j) :=
  (cross_reachable_afterFaults huv F hcard i i).trans
    (cross_reachable_afterFaults huv F hcard j i).symm

/-- Connected base graphs without isolated singleton vertices lift to graphs
that remain connected under every fault set smaller than a cloud. -/
theorem lift_afterFaults_connected [Nontrivial V] [Nonempty I]
    {T : SimpleGraph V} (hT : T.Connected) (F : Finset (Sym2 (V×I)))
    (hcard : F.card < Fintype.card I) : (afterFaults (lift (I:=I) T) F).Connected := by
  classical
  have base (u v : V) (p : T.Walk u v) : ∀ i j : I,
      (afterFaults (lift (I:=I) T) F).Reachable (u,i) (v,j) := by
    induction p with
    | @nil u =>
      intro i j
      obtain ⟨v,huv⟩ := hT.preconnected.exists_adj_of_nontrivial u
      exact same_cloud_reachable_afterFaults huv F hcard i j
    | @cons u v z huv p ih =>
      intro i j
      exact (cross_reachable_afterFaults huv F hcard i i).trans (ih i j)
  exact ⟨fun u v => by
    obtain ⟨p⟩ := hT.preconnected u.1 v.1
    exact base u.1 v.1 p u.2 v.2⟩

/-- A spanning connected subgraph's blowup is a valid q-fault certificate when
cloud size exceeds q. This is an actual all-fault preserver theorem, not the
invalid square-root-cloud claim. -/
theorem large_cloud_isFTPreserver [Nontrivial V] [Nonempty I]
    {G T : SimpleGraph V} (hTG : T≤G) (hT : T.Connected)
    (q : ℕ) (hq : q<Fintype.card I) :
    IsFTConnectivityPreserver (lift (I:=I) G) (lift (I:=I) T) q := by
  have hlift : lift (I:=I) T ≤ lift (I:=I) G := fun _ _ h => hTG h
  refine ⟨hlift,?_⟩
  intro F hF u v
  constructor
  · intro _
    exact (lift_afterFaults_connected hT F (hF.trans_lt hq)).preconnected u v
  · exact Reachable.mono (afterFaults_mono hlift F)
end LightEFTSpanners.GenericBlowupFailure
