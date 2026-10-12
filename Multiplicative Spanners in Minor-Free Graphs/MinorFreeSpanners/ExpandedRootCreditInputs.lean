import MinorFreeSpanners.ReindexedLongPhaseInputs
import MinorFreeSpanners.ConstructedRetainedCreditFamily

/-! Retain the actual post-short-absorption radius and credit when constructing
long-phase inputs. The future credit is the very same amount carried by the
short-phase bill; the original residual credit is neither replaced nor reset. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
variable {I : Type*}

 theorem expanded_radius_bounds (P U : Finset (Finset I))
    (e : {r // r∈selectedRoots P} ≃ {g // g∈U})
    (d : I → ℝ) (oldRadius : {S // S∈P} → ℝ)
    (radius : {r // r∈selectedRoots P} → ℝ) (E L c baseline : ℝ) (future : {r // r∈selectedRoots P} → ℝ)
    (hc : 0≤c) (hold : ∀ S,0≤oldRadius S ∧ oldRadius S≤E)
    (hbase : ∀ r,c*baseline≤c*(mixedEffectiveDiameter d oldRadius r.val-1)+future r)
    (hrad : ∀ r,mixedEffectiveDiameter d oldRadius r.val-1≤radius r ∧
      radius r≤mixedEffectiveDiameter d oldRadius r.val-1+2*L) :
    (∀ g,0≤radius (e.symm g) ∧ radius (e.symm g)≤E+2*L) ∧
    (∀ g,c*baseline≤c*radius (e.symm g)+future (e.symm g)) := by
  have hr (r : {r // r∈selectedRoots P}) :
      0≤radius r ∧ radius r≤E+2*L ∧ c*baseline≤c*radius r+future r := by
    obtain ⟨r,hr⟩ := r
    cases r with
    | inl S =>
      have hh := hrad ⟨Sum.inl S,hr⟩
      simp only [mixedEffectiveDiameter,Sum.elim_inl,add_sub_cancel_right] at hh
      have ho := hold S
      have hb := hbase ⟨Sum.inl S,hr⟩
      simp only [mixedEffectiveDiameter,Sum.elim_inl,add_sub_cancel_right] at hb
      constructor
      · exact ho.1.trans hh.1
      constructor
      · linarith
      · nlinarith
    | inr i => simp [selectedRoots] at hr
  exact ⟨fun g => ⟨(hr (e.symm g)).1,(hr (e.symm g)).2.1⟩,
    fun g => (hr (e.symm g)).2.2⟩

attribute [-instance] instDecidableEqSum in
 theorem expanded_mixed_credit_inputs (U : Finset (Finset I))
    (d credit : I → ℝ) (radius : {g // g∈U} → ℝ)
    (D rootBound c b baseline : ℝ) (spare future : {g // g∈U} → ℝ)
    (hc : 0≤c) (hspare : ∀ g,0≤spare g)
    (hd : ∀ i,1≤d i ∧ d i≤D)
    (hcredit : ∀ i,c*d i≤credit i) (hbase : ∀ i,c*b≤credit i)
    (hrad : ∀ g,0≤radius g ∧ radius g≤rootBound)
    (hrootbase : ∀ g,c*baseline≤c*radius g+future g) :
    let mixed := fun i => mixedEffectiveDiameter d radius i-1
    let keep := selectedResidualCredit U (fun g => c*radius g+spare g) credit
    (∀ r∈selectedRoots U,0≤mixed r) ∧
    (∀ r : {r // r∈selectedRoots U},mixed r.val≤rootBound) ∧
    (∀ i∉selectedRoots U,1≤mixed i ∧ mixed i+1≤D+1 ∧
      c*mixed i≤keep i ∧ c*b≤keep i) ∧
    (∀ i,0≤keep i) ∧
    (∀ r : {r // r∈selectedRoots U},c*mixed r.val+Sum.elim spare (fun _ => 0) r.val≤keep r.val) ∧
    (∀ r : {r // r∈selectedRoots U},c*baseline≤c*mixed r.val+Sum.elim future (fun _ => 0) r.val) := by
  intro mixed keep
  have hm (i) : mixed i=Sum.elim radius (fun i => d i.val) i := by
    cases i <;> simp [mixed,mixedEffectiveDiameter]
  have hk (i) : keep i=Sum.elim (fun g => c*radius g+spare g) (fun i => credit i.val) i := rfl
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro r hr
    cases r with
    | inl g => simpa [hm] using (hrad g).1
    | inr i => simp [selectedRoots] at hr
  · rintro ⟨r,hr⟩
    cases r with
    | inl g => simpa [hm] using (hrad g).2
    | inr i => simp [selectedRoots] at hr
  · intro i hi
    cases i with
    | inl g => exact (hi (by simp [selectedRoots])).elim
    | inr i => simpa [hm,hk] using ⟨(hd i.val).1,(hd i.val).2,hcredit i.val,hbase i.val⟩
  · intro i
    cases i with
    | inl g => simpa [hk] using add_nonneg (mul_nonneg hc (hrad g).1) (hspare g)
    | inr i => simpa [hk] using (mul_nonneg hc (le_trans (by norm_num) (hd i.val).1)).trans (hcredit i.val)
  · rintro ⟨r,hr⟩
    cases r with
    | inl g => simp [hm,hk]
    | inr i => simp [selectedRoots] at hr
  · rintro ⟨r,hr⟩
    cases r with
    | inl g => simpa [hm] using hrootbase g
    | inr i => simp [selectedRoots] at hr


def reindexedRootValue (P U : Finset (Finset I))
    (e : {r // r∈selectedRoots P} ≃ {g // g∈U})
    (f : {r // r∈selectedRoots P} → ℝ) (r : {r // r∈selectedRoots U}) : ℝ :=
  Sum.elim (fun g => f (e.symm g)) (fun _ => 0) r.val

attribute [-instance] instDecidableEqSum in
 theorem reindexed_root_budgets (P U : Finset (Finset I))
    (e : {r // r∈selectedRoots P} ≃ {g // g∈U})
    (high : Finset {r // r∈selectedRoots P})
    (spare reserve future : {r // r∈selectedRoots P} → ℝ) (c edgeMax a : ℝ) (N : ℕ)
    (hf : ∀ r,future r≤reserve r)
    (hb : ∀ r,r∈high → 2*c*edgeMax+2*(N:ℝ)*a+future r≤reserve r)
    (hr : ∀ r,5*(N:ℝ)*a+reserve r≤spare r) :
    (∀ r,reindexedRootValue P U e future r≤reindexedRootValue P U e reserve r) ∧
    (∀ r,r.val∈highRootEligible U (high.image e) →
      2*c*edgeMax+2*(N:ℝ)*a+reindexedRootValue P U e future r≤reindexedRootValue P U e reserve r) ∧
    (∀ r,5*(N:ℝ)*a+reindexedRootValue P U e reserve r≤reindexedRootValue P U e spare r) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨r,hr⟩
    cases r with
    | inl g => exact hf (e.symm g)
    | inr i => simp [selectedRoots] at hr
  · rintro ⟨r,hr⟩ he
    cases r with
    | inl g =>
      have hg : g∈high.image e := by simpa [highRootEligible] using he
      obtain ⟨ro,hro,heq⟩ := Finset.mem_image.mp hg
      have he : e.symm g=ro := by rw [←heq];simp
      simpa [reindexedRootValue,he] using hb ro hro
    | inr i => simp [selectedRoots] at hr
  · rintro ⟨r,hr'⟩
    cases r with
    | inl g => exact hr (e.symm g)
    | inr i => simp [selectedRoots] at hr'

end MinorFreeSpanners
