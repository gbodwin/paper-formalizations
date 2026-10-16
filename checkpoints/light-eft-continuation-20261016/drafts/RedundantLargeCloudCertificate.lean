import LightEFTSpanners.GenericBlowupFailure

/-! A bounded positive repair of the cloud certificate, with an explicit larger
cloud requirement. This does not prove the original square-root-cloud scaling. -/
namespace LightEFTSpanners.GenericBlowupFailure
open SimpleGraph Finset
variable {V I : Type*}

/-- At most twice as many copy labels as failed edges occur at their endpoints. -/
theorem exists_untouched_copy [Fintype I] (F : Finset (Sym2 (V × I)))
    (hF : 2 * F.card < Fintype.card I) :
    ∃ i : I, ∀ (u : V × I) (a : V), s(u,(a,i)) ∉ F := by
  classical
  let B : Finset I := F.biUnion fun e => e.toFinset.image Prod.snd
  have hB : B.card ≤ 2 * F.card := by
    calc
      B.card ≤ ∑ e ∈ F, (e.toFinset.image Prod.snd).card := card_biUnion_le
      _ ≤ ∑ _e ∈ F, 2 := by
        apply sum_le_sum
        intro e _
        apply card_image_le.trans
        rw [Sym2.card_toFinset]
        split_ifs <;> omega
      _ = 2 * F.card := by simp [mul_comm]
  obtain ⟨i,_,hi⟩ := exists_mem_notMem_of_card_lt_card
    (show B.card < (univ : Finset I).card by simpa using hB.trans_lt hF)
  refine ⟨i,fun u a hf => hi ?_⟩
  exact mem_biUnion.mpr ⟨s(u,(a,i)),hf,
    mem_image.mpr ⟨(a,i),Sym2.mem_toFinset.mpr (Sym2.mem_mk_right u (a,i)),rfl⟩⟩

/-- A connected nontrivial base has a preconnected blowup after these failures.
Faults need not be input edges: the endpoint-label count handles arbitrary F. -/
theorem large_cloud_preconnected [Fintype I] [Nontrivial V]
    (T : SimpleGraph V) (hT : T.Preconnected) (F : Finset (Sym2 (V × I)))
    (hF : 2 * F.card < Fintype.card I) :
    (afterFaults (lift (I:=I) T) F).Preconnected := by
  classical
  obtain ⟨i,hi⟩ := exists_untouched_copy F hF
  let φ : T →g afterFaults (lift (I:=I) T) F :=
    { toFun := fun a => (a,i)
      map_rel' := fun h => deleteEdges_adj.mpr ⟨h,hi _ _⟩ }
  intro u v
  obtain ⟨a,ha⟩ := hT.exists_adj_of_nontrivial u.1
  obtain ⟨b,hb⟩ := hT.exists_adj_of_nontrivial v.1
  have hu : (afterFaults (lift (I:=I) T) F).Adj u (a,i) :=
    deleteEdges_adj.mpr ⟨ha,hi u a⟩
  have hv : (afterFaults (lift (I:=I) T) F).Adj v (b,i) :=
    deleteEdges_adj.mpr ⟨hb,hi v b⟩
  exact hu.reachable.trans (((hT a b).map φ).trans hv.reachable.symm)

/-- The larger-cloud certificate is genuine for every fault set of size at most q.
It does not assert the lightness scaling of the paper's smaller-cloud certificate. -/
theorem large_cloud_preserver [Fintype I] [Nontrivial V]
    {G T : SimpleGraph V} (hTG : T ≤ G) (hT : T.Preconnected)
    (q : ℕ) (hq : 2 * q < Fintype.card I) :
    IsFTConnectivityPreserver (lift (I:=I) G) (lift (I:=I) T) q := by
  have hsub : lift (I:=I) T ≤ lift (I:=I) G := fun _ _ h => hTG h
  refine ⟨hsub,fun F hF u v => ⟨fun _ => ?_,fun h => h.mono (afterFaults_mono hsub F)⟩⟩
  exact large_cloud_preconnected T hT F ((Nat.mul_le_mul_left 2 hF).trans_lt hq) u v

/-- In particular, 2q+1 copies per vertex repair connectivity of an actual
spanning-tree blowup, at a different cloud size from the original argument. -/
theorem enlarged_tree_certificate [Nontrivial V]
    {G T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree) (q : ℕ) :
    IsFTConnectivityPreserver (lift (I:=Fin (2*q+1)) G) (lift (I:=Fin (2*q+1)) T) q := by
  exact large_cloud_preserver hTG hT.connected.preconnected q (by simp)

end LightEFTSpanners.GenericBlowupFailure
