import LightEFTSpanners.CorrectedCloudLowerBound
import LightEFTSpanners.HostWeightTransport

/-! Adding isolated vertices transports the actual all-fault spanner and
minimum-preserver problems without changing any edge weight or ratio. -/
namespace LightEFTSpanners.CorrectedCloud.Padding
open SimpleGraph Finset LightSpanners
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

noncomputable def weight (r : W → V) (w : Sym2 V → ℝ) (e : Sym2 W) : ℝ :=
  w (Sym2.map r e)

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem weight_map (j : V ↪ W) (r : W → V) (hj : Function.LeftInverse r j)
    (w : Sym2 V → ℝ) (e : Sym2 V) : weight r w (j.sym2Map e)=w e := by
  obtain ⟨a,b⟩ := e
  simp [weight,Function.Embedding.sym2Map_apply,Sym2.map_mk,hj a,hj b]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem endpoints_restore (j : V ↪ W) (r : W → V) (hj : Function.LeftInverse r j)
    {G : SimpleGraph V} {H : SimpleGraph W} (hHG : H≤G.map j)
    {a b : W} (hab : H.Adj a b) : j (r a)=a ∧ j (r b)=b := by
  obtain ⟨u,v,_,rfl,rfl⟩ := (map_adj j G a b).mp (hHG hab)
  exact ⟨by rw [hj u],by rw [hj v]⟩

abbrev embedFaultHom (j : V ↪ W) (G : SimpleGraph V) (F : Finset (Sym2 V)) :
    afterFaults G F →g afterFaults (G.map j) (F.map j.sym2Map) where
  toFun := j
  map_rel' := by
    intro a b hab
    obtain ⟨hadj,hnot⟩ := deleteEdges_adj.mp hab
    apply deleteEdges_adj.mpr ⟨map_adj_apply.mpr hadj,?_⟩
    change j.sym2Map s(a,b)∉F.map j.sym2Map
    exact fun h => hnot ((Finset.mem_map' j.sym2Map).mp h)

abbrev restrictFaultHom (j : V ↪ W) (r : W → V) (hj : Function.LeftInverse r j)
    {G : SimpleGraph V} {H : SimpleGraph W} (hHG : H≤G.map j)
    (F : Finset (Sym2 V)) :
    afterFaults H (F.map j.sym2Map) →g afterFaults (H.comap j) F where
  toFun := r
  map_rel' := by
    intro a b hab
    obtain ⟨hadj,hnot⟩ := deleteEdges_adj.mp hab
    obtain ⟨ha,hb⟩ := endpoints_restore j r hj hHG hadj
    apply deleteEdges_adj.mpr
    constructor
    · change H.Adj (j (r a)) (j (r b))
      rwa [ha,hb]
    · intro he
      apply hnot
      apply mem_map.mpr ⟨s(r a,r b),he,?_⟩
      simp only [Function.Embedding.sym2Map_apply,Sym2.map_mk,ha,hb]

abbrev pullFaultHom (j : V ↪ W) (r : W → V) (hj : Function.LeftInverse r j)
    (G : SimpleGraph V) (F : Finset (Sym2 W)) :
    afterFaults (G.map j) F →g afterFaults G (pullEdges j F) where
  toFun := r
  map_rel' := by
    intro a b hab
    obtain ⟨hadj,hnot⟩ := deleteEdges_adj.mp hab
    obtain ⟨u,v,huv,rfl,rfl⟩ := (map_adj j G a b).mp hadj
    rw [hj u,hj v]
    apply deleteEdges_adj.mpr ⟨huv,?_⟩
    change j.sym2Map s(u,v)∉F at hnot
    intro he
    exact hnot ((mem_pullEdges j F s(u,v)).mp he)

abbrev mapFaultHom (j : V ↪ W) (G : SimpleGraph V) (F : Finset (Sym2 W)) :
    afterFaults G (pullEdges j F) →g afterFaults (G.map j) F where
  toFun := j
  map_rel' := by
    intro a b hab
    obtain ⟨hadj,hnot⟩ := deleteEdges_adj.mp hab
    apply deleteEdges_adj.mpr ⟨map_adj_apply.mpr hadj,?_⟩
    change j.sym2Map s(a,b)∉F
    intro he
    exact hnot ((mem_pullEdges j F s(a,b)).mpr he)

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem map_comap_eq (j : V ↪ W) {G : SimpleGraph V} {H : SimpleGraph W}
    (hHG : H≤G.map j) : (H.comap j).map j=H := by
  apply le_antisymm (map_comap_le j H)
  intro a b hab
  obtain ⟨u,v,_,rfl,rfl⟩ := (map_adj j G a b).mp (hHG hab)
  exact map_adj_apply.mpr hab

omit [DecidableEq V] [DecidableEq W] in
theorem totalWeight_map (j : V ↪ W) (r : W → V) (hj : Function.LeftInverse r j)
    (G : SimpleGraph V) (w : Sym2 V → ℝ) : totalWeight (G.map j) (weight r w)=totalWeight G w := by
  rw [totalWeight_map_embedding]
  apply sum_congr rfl
  intro e _
  exact weight_map j r hj w e

omit [DecidableEq V] [DecidableEq W] in
theorem totalWeight_restrict (j : V ↪ W) (r : W → V) (hj : Function.LeftInverse r j)
    {G : SimpleGraph V} {H : SimpleGraph W} (hHG : H≤G.map j) (w : Sym2 V → ℝ) :
    totalWeight H (weight r w)=totalWeight (H.comap j) w := by
  calc
    _ = totalWeight ((H.comap j).map j) (weight r w) :=
      congrArg (fun K => totalWeight K (weight r w)) (map_comap_eq j hHG).symm
    _ = _ := totalWeight_map j r hj (H.comap j) w

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem eft_restrict (j : V ↪ W) (r : W → V) (hj : Function.LeftInverse r j)
    {G : SimpleGraph V} {H : SimpleGraph W} {w : Sym2 V → ℝ} {t : ℝ} {f : ℕ}
    (hsp : IsEFTSpanner (G.map j) H (weight r w) t f) :
    IsEFTSpanner G (H.comap j) w t f := by
  have hsub : H.comap j≤G := by
    intro a b hab
    exact map_adj_apply.mp (hsp.1 hab)
  refine ⟨hsub,fun F hF => ⟨afterFaults_mono hsub F,?_⟩⟩
  intro a b p
  obtain ⟨q,hq⟩ := (hsp.2 (F.map j.sym2Map) (by simpa using hF)).2
    (j a) (j b) (p.map (embedFaultHom j G F))
  let s := (q.map (restrictFaultHom j r hj hsp.1 F)).copy (hj a) (hj b)
  refine ⟨s,?_⟩
  have hs : walkWeight w s=walkWeight (weight r w) q := by
    calc
      _ = walkWeight w (q.map (restrictFaultHom j r hj hsp.1 F)) := by simp [s,walkWeight]
      _ = walkWeight (fun e => w (Sym2.map (restrictFaultHom j r hj hsp.1 F) e)) q :=
        walkWeight_map (restrictFaultHom j r hj hsp.1 F) w q
      _ = _ := rfl
  have hp : walkWeight (weight r w) (p.map (embedFaultHom j G F))=walkWeight w p := by
    rw [walkWeight_map]
    apply congrArg (fun z => walkWeight z p)
    funext e
    exact weight_map j r hj w e
  rw [hp] at hq
  rw [hs]
  exact hq

omit [Fintype W] [DecidableEq V] in
theorem preserver_map (j : V ↪ W) (r : W → V) (hj : Function.LeftInverse r j)
    {G S : SimpleGraph V} {f : ℕ} (hS : IsFTConnectivityPreserver G S f) :
    IsFTConnectivityPreserver (G.map j) (S.map j) f := by
  have hsub : S.map j≤G.map j := map_monotone j hS.1
  refine ⟨hsub,fun F hF a b => ⟨?_,fun h => h.mono (afterFaults_mono hsub F)⟩⟩
  intro hr
  by_cases hab : a=b
  · subst b
    exact Reachable.refl _
  obtain ⟨p⟩ := hr
  have hafter : afterFaults (G.map j) F≤G.map j := deleteEdges_le _
  have ha := (endpoints_restore j r hj hafter
    (p.adj_snd (p.not_nil_of_ne hab))).1
  have hb := (endpoints_restore j r hj hafter
    (p.reverse.adj_snd (p.reverse.not_nil_of_ne (Ne.symm hab)))).1
  have hbase : (afterFaults G (pullEdges j F)).Reachable (r a) (r b) :=
    ⟨p.map (pullFaultHom j r hj G F)⟩
  have hSbase := (hS.2 (pullEdges j F) ((pullEdges_card_le j F).trans hF) (r a) (r b)).mp hbase
  have hback := hSbase.map (mapFaultHom j S F)
  change (afterFaults (S.map j) F).Reachable (j (r a)) (j (r b)) at hback
  rwa [ha,hb] at hback

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem preserver_restrict (j : V ↪ W) (r : W → V) (hj : Function.LeftInverse r j)
    {G : SimpleGraph V} {Q : SimpleGraph W} {f : ℕ}
    (hQ : IsFTConnectivityPreserver (G.map j) Q f) :
    IsFTConnectivityPreserver G (Q.comap j) f := by
  have hsub : Q.comap j≤G := by
    intro a b hab
    exact map_adj_apply.mp (hQ.1 hab)
  refine ⟨hsub,fun F hF a b => ⟨?_,fun h => h.mono (afterFaults_mono hsub F)⟩⟩
  intro hr
  have himage := hr.map (embedFaultHom j G F)
  have hQimage := (hQ.2 (F.map j.sym2Map) (by simpa using hF) (j a) (j b)).mp himage
  have hback := hQimage.map (restrictFaultHom j r hj hQ.1 F)
  change (afterFaults (Q.comap j) F).Reachable (r (j a)) (r (j b)) at hback
  rwa [hj a,hj b] at hback

omit [DecidableEq V] in
theorem minimum_preserver_restrict (j : V ↪ W) (r : W → V)
    (hj : Function.LeftInverse r j) {G : SimpleGraph V} {Q : SimpleGraph W}
    {w : Sym2 V → ℝ} {f : ℕ}
    (hQ : IsMinimumFTPreserver (G.map j) Q (weight r w) f) :
    IsMinimumFTPreserver G (Q.comap j) w f := by
  refine ⟨preserver_restrict j r hj hQ.1,?_⟩
  intro S hS
  have h := hQ.2 (S.map j) (preserver_map j r hj hS)
  rwa [totalWeight_restrict j r hj hQ.1.1 w,totalWeight_map j r hj] at h

omit [DecidableEq V] [DecidableEq W] in
theorem competitiveLightness_restrict (j : V ↪ W) (r : W → V)
    (hj : Function.LeftInverse r j) {G : SimpleGraph V} {H Q : SimpleGraph W}
    (hHG : H≤G.map j) (hQG : Q≤G.map j) (w : Sym2 V → ℝ) :
    competitiveLightness H Q (weight r w)=
      competitiveLightness (H.comap j) (Q.comap j) w := by
  unfold competitiveLightness
  rw [totalWeight_restrict j r hj hHG,totalWeight_restrict j r hj hQG]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem positive_map (j : V ↪ W) (r : W → V) (hj : Function.LeftInverse r j)
    {G : SimpleGraph V} {w : Sym2 V → ℝ} (hw : ∀e∈G.edgeSet,0<w e) :
    ∀e∈(G.map j).edgeSet,0<weight r w e := by
  intro e he
  rw [G.edgeSet_map j] at he
  obtain ⟨d,hd,rfl⟩ := he
  rw [weight_map j r hj]
  exact hw d hd

end LightEFTSpanners.CorrectedCloud.Padding
