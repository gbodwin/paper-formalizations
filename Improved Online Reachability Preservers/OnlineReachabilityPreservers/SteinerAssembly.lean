import Mathlib.Data.List.Induction
import OnlineReachabilityPreservers.SteinerThinRound

/-! Composition of the Section 5 phases with an interface for the cited early routine. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- The feasibility interface needed from the early-demand routine. Its
competitive guarantee is a separate proof obligation. -/
structure EarlySteinerRule (G : Arcs V) where
  run : List (V × V) → Arcs V
  empty : run [] = ∅
  subset : ∀ D, run D ⊆ G
  online : ∀ {D E}, D <+: E → run D ⊆ run E
  preserves : ∀ D, (∀ d ∈ D, Reach G d.1 d.2) → Preserves G (run D) D

structure SteinerPhaseTraces (V : Type*) where
  early : List (V × V)
  hits : List (V × V)
  thin : List (V × V)

private def SteinerPhaseTraces.empty : SteinerPhaseTraces V := ⟨[],[],[]⟩

/-- During the early phase, skip requests already served by that phase.
Afterwards, skip hits already served by the hub phase. The thin trace uses
only the hub test and duplicate detection, independently of its thresholds. -/
def steinerPhaseStep {G : Arcs V} (early : EarlySteinerRule G) (T : ℕ) (S : Finset V)
    (traces : SteinerPhaseTraces V) (d : V × V) : SteinerPhaseTraces V :=
  if d.1=d.2 then traces
  else if traces.early.length < T then
    if d.1 ∈ reaches (early.run traces.early) d.2 then traces
    else {traces with early := traces.early++[d]}
  else
    match hitHub G S d with
    | some _ =>
      if d.1 ∈ reaches (hubPreserver G S traces.hits) d.2 then traces
      else {traces with hits := traces.hits++[d]}
    | none =>
      if d ∈ traces.thin then traces
      else {traces with thin := traces.thin++[d]}

def steinerPhaseTraces {G : Arcs V} (early : EarlySteinerRule G) (T : ℕ) (S : Finset V)
    (D : List (V × V)) : SteinerPhaseTraces V :=
  D.foldl (steinerPhaseStep early T S) SteinerPhaseTraces.empty

private def NontrivialTrace (run : List (V × V) → Arcs V) (D : List (V × V)) : Prop :=
  ∀ i : Fin D.length, ¬ Reach (run (D.take i.1)) (D.get i).1 (D.get i).2

omit [LinearOrder V] [Fintype V] in
private theorem nontrivialTrace_snoc {run : List (V × V) → Arcs V} {D : List (V × V)}
    (hD : NontrivialTrace run D) {d : V × V} (hd : ¬ Reach (run D) d.1 d.2) :
    NontrivialTrace run (D++[d]) := by
  intro i
  have il : i.1 < D.length+1 := by simpa using i.isLt
  by_cases before : i.1 < D.length
  · let j : Fin D.length := ⟨i.1,before⟩
    have take : (D++[d]).take i.1 = D.take j.1 := List.take_append_of_le_length before.le
    change ¬ Reach (run ((D++[d]).take i.1)) ((D++[d]).get i).1 ((D++[d]).get i).2
    rw [take,show (D++[d]).get i = D.get j from List.getElem_append_left before]
    exact hD j
  · have last : i.1 = D.length := by omega
    have take : (D++[d]).take i.1 = D := by simp [last]
    have get : (D++[d]).get i = d := by
      change (D++[d])[i.1] = d
      rw [List.getElem_append_right (show D.length ≤ i.1 by omega)]
      simp [last]
    change ¬ Reach (run ((D++[d]).take i.1)) ((D++[d]).get i).1 ((D++[d]).get i).2
    rw [take,get]
    exact hd

private structure PhaseTraceFacts {G : Arcs V} (early : EarlySteinerRule G) (T : ℕ) (S : Finset V)
    (D : List (V × V)) (traces : SteinerPhaseTraces V) : Prop where
  early_in : ∀ d ∈ traces.early, d ∈ D
  hits_in : ∀ d ∈ traces.hits, d ∈ D
  thin_in : ∀ d ∈ traces.thin, d ∈ D
  early_cap : traces.early.length ≤ T
  before_cutoff : traces.early.length < T → traces.hits=[] ∧ traces.thin=[]
  early_nontrivial : NontrivialTrace early.run traces.early
  hits_nontrivial : NontrivialTrace (hubPreserver G S) traces.hits
  hits_found : ∀ d ∈ traces.hits, ∃ v, hitHub G S d = some v
  thin_missed : ∀ d ∈ traces.thin, hitHub G S d = none
  thin_nonself : ∀ d ∈ traces.thin, d.1 ≠ d.2
  thin_distinct : traces.thin.Nodup

private theorem steinerPhaseStep_cases {G : Arcs V} (early : EarlySteinerRule G) (T : ℕ) (S : Finset V)
    (st : SteinerPhaseTraces V) (d : V × V) :
    let r := steinerPhaseStep early T S st d
    r = st ∨
      (r = {st with early := st.early++[d]} ∧ st.early.length < T ∧
        ¬ Reach (early.run st.early) d.1 d.2) ∨
      (r = {st with hits := st.hits++[d]} ∧ T ≤ st.early.length ∧
        (∃ v, hitHub G S d = some v) ∧ ¬ Reach (hubPreserver G S st.hits) d.1 d.2) ∨
      (r = {st with thin := st.thin++[d]} ∧ T ≤ st.early.length ∧
        hitHub G S d = none ∧ d ∉ st.thin ∧ d.1 ≠ d.2) := by
  by_cases self : d.1=d.2
  · exact Or.inl (by simp [steinerPhaseStep,self])
  by_cases cut : st.early.length<T
  · by_cases served : d.1 ∈ reaches (early.run st.early) d.2
    · exact Or.inl (by simp [steinerPhaseStep,self,cut,served])
    · exact Or.inr (Or.inl ⟨by simp [steinerPhaseStep,self,cut,served],cut,
        fun h => served (mem_reaches.mpr h)⟩)
  cases hit : hitHub G S d with
  | some v =>
    by_cases served : d.1 ∈ reaches (hubPreserver G S st.hits) d.2
    · exact Or.inl (by simp [steinerPhaseStep,self,cut,hit,served])
    · exact Or.inr (Or.inr (Or.inl ⟨by simp [steinerPhaseStep,self,cut,hit,served],
        Nat.le_of_not_gt cut,⟨v,rfl⟩,fun h => served (mem_reaches.mpr h)⟩))
  | none =>
    by_cases seen : d ∈ st.thin
    · exact Or.inl (by simp [steinerPhaseStep,self,cut,hit,seen])
    · exact Or.inr (Or.inr (Or.inr ⟨by simp [steinerPhaseStep,self,cut,hit,seen],
        Nat.le_of_not_gt cut,rfl,seen,self⟩))

private theorem steinerPhaseTraces_snoc {G : Arcs V} (early : EarlySteinerRule G) (T : ℕ) (S : Finset V)
    (D : List (V × V)) (d : V × V) :
    steinerPhaseTraces early T S (D++[d]) =
      steinerPhaseStep early T S (steinerPhaseTraces early T S D) d := by simp [steinerPhaseTraces]

private theorem steinerPhaseTraces_facts {G : Arcs V} (early : EarlySteinerRule G) (T : ℕ) (S : Finset V)
    (D : List (V × V)) :
    PhaseTraceFacts early T S D (steinerPhaseTraces early T S D) := by
  induction D using List.reverseRecOn with
  | nil =>
    constructor <;> simp [steinerPhaseTraces,SteinerPhaseTraces.empty,NontrivialTrace]
  | append_singleton D d ih =>
    rw [steinerPhaseTraces_snoc]
    let st := steinerPhaseTraces early T S D
    have old : PhaseTraceFacts early T S D st := ih
    have early_in (a : V × V) (ha : a ∈ st.early) : a ∈ D++[d] :=
      List.mem_append_left _ (old.early_in a ha)
    have hits_in (a : V × V) (ha : a ∈ st.hits) : a ∈ D++[d] :=
      List.mem_append_left _ (old.hits_in a ha)
    have thin_in (a : V × V) (ha : a ∈ st.thin) : a ∈ D++[d] :=
      List.mem_append_left _ (old.thin_in a ha)
    have push {L : List (V × V)} (incl : ∀ a ∈ L, a ∈ D++[d]) :
        ∀ a ∈ L++[d], a ∈ D++[d] := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact incl a h
      · exact List.mem_append_right _ h
    rcases steinerPhaseStep_cases early T S st d with keep | ⟨added,cut,hr⟩ |
      ⟨added,cut,hit,hr⟩ | ⟨added,cut,miss,new,hn⟩
    · rw [keep]
      exact ⟨early_in,hits_in,thin_in,old.early_cap,old.before_cutoff,
        old.early_nontrivial,old.hits_nontrivial,old.hits_found,
        old.thin_missed,old.thin_nonself,old.thin_distinct⟩
    · rw [added]
      refine ⟨push early_in,hits_in,thin_in,?_,fun _ => old.before_cutoff cut,
        nontrivialTrace_snoc old.early_nontrivial hr,old.hits_nontrivial,old.hits_found,
        old.thin_missed,old.thin_nonself,old.thin_distinct⟩
      simpa using Nat.succ_le_of_lt cut
    · rw [added]
      refine ⟨early_in,push hits_in,thin_in,old.early_cap,fun h => (cut.not_gt h).elim,
        old.early_nontrivial,nontrivialTrace_snoc old.hits_nontrivial hr,?_,
        old.thin_missed,old.thin_nonself,old.thin_distinct⟩
      intro a ha
      rcases List.mem_append.mp ha with hm | hm
      · exact old.hits_found a hm
      · simpa using (List.mem_singleton.mp hm).symm ▸ hit
    · rw [added]
      refine ⟨early_in,hits_in,push thin_in,old.early_cap,fun h => (cut.not_gt h).elim,
        old.early_nontrivial,old.hits_nontrivial,old.hits_found,?_,?_,?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with hm | hm
        · exact old.thin_missed a hm
        · simpa only [List.mem_singleton.mp hm] using miss
      · intro a ha
        rcases List.mem_append.mp ha with hm | hm
        · exact old.thin_nonself a hm
        · simpa only [List.mem_singleton.mp hm] using hn
      · refine List.nodup_append.mpr ⟨old.thin_distinct,by simp,?_⟩
        intro a ha b hb eq
        exact new ((eq.trans (List.mem_singleton.mp hb)) ▸ ha)

private theorem steinerPhaseTraces_prefix {G : Arcs V} (early : EarlySteinerRule G) (T : ℕ) (S : Finset V)
    {D E : List (V × V)} (p : D <+: E) :
    let x := steinerPhaseTraces early T S D
    let y := steinerPhaseTraces early T S E
    x.early <+: y.early ∧ x.hits <+: y.hits ∧ x.thin <+: y.thin := by
  obtain ⟨F,rfl⟩ := p
  induction F using List.reverseRecOn with
  | nil => simp
  | append_singleton F d ih =>
    rw [← List.append_assoc,steinerPhaseTraces_snoc]
    let st := steinerPhaseTraces early T S (D++F)
    rcases steinerPhaseStep_cases early T S st d with keep | ⟨add,_,_⟩ |
      ⟨add,_,_,_⟩ | ⟨add,_,_,_,_⟩
    · rw [keep]
      exact ih
    · rw [add]
      exact ⟨ih.1.trans ⟨[d],rfl⟩,ih.2⟩
    · rw [add]
      exact ⟨ih.1,ih.2.1.trans ⟨[d],rfl⟩,ih.2.2⟩
    · rw [add]
      exact ⟨ih.1,ih.2.1,ih.2.2.trans ⟨[d],rfl⟩⟩

private def phaseUnion {G : Arcs V} (early : EarlySteinerRule G) (S : Finset V) (factor : ℕ)
    (sample : ThinSample G) (st : SteinerPhaseTraces V) : Arcs V :=
  early.run st.early ∪ hubPreserver G S st.hits ∪ thinRoundRun G factor sample st.thin

private theorem phaseUnion_subset {G : Arcs V} (early : EarlySteinerRule G) (S : Finset V)
    (factor : ℕ) (sample : ThinSample G) (st : SteinerPhaseTraces V)
    (feasible : ∀ d ∈ st.thin, Reach G d.1 d.2) :
    phaseUnion early S factor sample st ⊆ G :=
  union_subset (union_subset (early.subset _) (hubPreserver_bound G S _).1)
    (thinRoundRun_correct G factor sample _ feasible).1

/-- For fixed hub and edge-threshold samples, combine the early, hub, and thin
purchases. An unhit thick request causes an immediate full-graph purchase. -/
def assembledSteiner {G : Arcs V} (early : EarlySteinerRule G) (T τ : ℕ) (S : Finset V)
    (sample : ThinSample G) (D : List (V × V)) : Arcs V :=
  let st := steinerPhaseTraces early T S D
  if st.thin.any (fun d => decide (τ < (reachInterval G d).card)) then G
  else phaseUnion early S (thinRoundingFactor (Fintype.card V) τ) sample st


theorem assembledSteiner_empty {G : Arcs V} (early : EarlySteinerRule G) (T τ : ℕ) (S : Finset V)
    (sample : ThinSample G) : assembledSteiner early T τ S sample [] = ∅ := by
  simp [assembledSteiner,steinerPhaseTraces,SteinerPhaseTraces.empty,phaseUnion,early.empty,
    hubPreserver,hitRequests,sinkPreserver,sourcePreserver,liftedRun,thinRoundRun,reverseArcs]

private theorem phaseUnion_prefix {G : Arcs V} (early : EarlySteinerRule G) (T : ℕ) (S : Finset V)
    (factor : ℕ) (sample : ThinSample G) {D E : List (V × V)} (pref : D <+: E)
    (feasible : ∀ d ∈ E, Reach G d.1 d.2) :
    phaseUnion early S factor sample (steinerPhaseTraces early T S D) ⊆
      phaseUnion early S factor sample (steinerPhaseTraces early T S E) := by
  obtain ⟨pe,ph,pt⟩ := steinerPhaseTraces_prefix early T S pref
  have facts := steinerPhaseTraces_facts early T S E
  exact union_subset_union (union_subset_union (early.online pe) (hubPreserver_prefix G S ph))
    (thinRoundRun_prefix G factor sample pt (fun d hd => feasible d (facts.thin_in d hd)))

theorem assembledSteiner_prefix {G : Arcs V} (early : EarlySteinerRule G) (T τ : ℕ) (S : Finset V)
    (sample : ThinSample G) {D E : List (V × V)} (pref : D <+: E)
    (feasible : ∀ d ∈ E, Reach G d.1 d.2) :
    assembledSteiner early T τ S sample D ⊆ assembledSteiner early T τ S sample E := by
  let x := steinerPhaseTraces early T S D
  let y := steinerPhaseTraces early T S E
  let pred (d : V × V) := decide (τ < (reachInterval G d).card)
  have facts := steinerPhaseTraces_facts early T S D
  have earlyThin : ∀ d ∈ x.thin, Reach G d.1 d.2 :=
    fun d hd => feasible d (pref.sublist.subset (facts.thin_in d hd))
  change (if x.thin.any pred then G else phaseUnion early S _ sample x) ⊆
    (if y.thin.any pred then G else phaseUnion early S _ sample y)
  by_cases bad : y.thin.any pred
  · rw [ite_eq_left bad]
    split
    · exact Subset.rfl
    · exact phaseUnion_subset early S _ sample x earlyThin
  · have earlyGood : ¬ x.thin.any pred := by
      intro h
      obtain ⟨d,hd,hbad⟩ := List.any_eq_true.mp h
      have p := (steinerPhaseTraces_prefix early T S pref).2.2
      exact bad (List.any_eq_true.mpr ⟨d,p.sublist.subset hd,hbad⟩)
    rw [ite_eq_right earlyGood,ite_eq_right bad]
    exact phaseUnion_prefix early T S _ sample pref feasible

private theorem phaseStep_serves {G : Arcs V} (early : EarlySteinerRule G) (T : ℕ) (S : Finset V)
    (factor : ℕ) (sample : ThinSample G) (st : SteinerPhaseTraces V) (d : V × V)
    (feasibleEarly : ∀ e ∈ st.early, Reach G e.1 e.2)
    (feasibleThin : ∀ e ∈ st.thin, Reach G e.1 e.2) (feasible : Reach G d.1 d.2) :
    Reach (phaseUnion early S factor sample (steinerPhaseStep early T S st d)) d.1 d.2 := by
  have earlyReach (s : SteinerPhaseTraces V) {a b : V} (h : Reach (early.run s.early) a b) :
      Reach (phaseUnion early S factor sample s) a b :=
    reach_mono (subset_union_left.trans subset_union_left) h
  have hubReach (s : SteinerPhaseTraces V) {a b : V} (h : Reach (hubPreserver G S s.hits) a b) :
      Reach (phaseUnion early S factor sample s) a b :=
    reach_mono (subset_union_right.trans subset_union_left) h
  have thinReach (s : SteinerPhaseTraces V) {a b : V}
      (h : Reach (thinRoundRun G factor sample s.thin) a b) :
      Reach (phaseUnion early S factor sample s) a b := reach_mono subset_union_right h
  by_cases self : d.1=d.2
  · rw [← self]
  by_cases cut : st.early.length<T
  · by_cases served : d.1 ∈ reaches (early.run st.early) d.2
    · simpa [steinerPhaseStep,self,cut,served] using earlyReach st (mem_reaches.mp served)
    · let s := {st with early := st.early++[d]}
      have f : ∀ e ∈ s.early, Reach G e.1 e.2 := by
        intro e he
        rcases List.mem_append.mp he with h | h
        · exact feasibleEarly _ h
        · simpa only [List.mem_singleton.mp h] using feasible
      have m : d ∈ s.early := by simp [s]
      have r := ((early.preserves s.early f) d m).mpr feasible
      simpa [steinerPhaseStep,self,cut,served,s] using earlyReach s r
  cases hit : hitHub G S d with
  | some h =>
    by_cases served : d.1 ∈ reaches (hubPreserver G S st.hits) d.2
    · simpa [steinerPhaseStep,self,cut,hit,served] using hubReach st (mem_reaches.mp served)
    · let s := {st with hits := st.hits++[d]}
      have m : d ∈ s.hits := by simp [s]
      obtain ⟨pre,post⟩ := hubPreserver_serves G S s.hits m hit
      simpa [steinerPhaseStep,self,cut,hit,served,s] using hubReach s (pre.trans post)
  | none =>
    by_cases seen : d ∈ st.thin
    · have r := ((thinRoundRun_correct G factor sample st.thin feasibleThin).2 d seen).mpr feasible
      simpa [steinerPhaseStep,self,cut,hit,seen] using thinReach st r
    · let s := {st with thin := st.thin++[d]}
      have f : ∀ e ∈ s.thin, Reach G e.1 e.2 := by
        intro e he
        rcases List.mem_append.mp he with h | h
        · exact feasibleThin _ h
        · simpa only [List.mem_singleton.mp h] using feasible
      have m : d ∈ s.thin := by simp [s]
      have r := ((thinRoundRun_correct G factor sample s.thin f).2 d m).mpr feasible
      simpa [steinerPhaseStep,self,cut,hit,seen,s] using thinReach s r

/-- Every realized choice of hubs and edge thresholds serves each revealed request. -/
theorem assembledSteiner_correct {G : Arcs V} (early : EarlySteinerRule G) (T τ : ℕ) (S : Finset V)
    (sample : ThinSample G) (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    assembledSteiner early T τ S sample D ⊆ G ∧ Preserves G (assembledSteiner early T τ S sample D) D := by
  have sub {E : List (V × V)} (f : ∀ e ∈ E, Reach G e.1 e.2) :
      assembledSteiner early T τ S sample E ⊆ G := by
    dsimp only [assembledSteiner]
    split
    · exact Subset.rfl
    · exact phaseUnion_subset early S _ sample _
        (fun e he => f e ((steinerPhaseTraces_facts early T S E).thin_in e he))
  refine ⟨sub feasible,fun d hd => ⟨reach_mono (sub feasible),fun _ => ?_⟩⟩
  suffices result : ∀ E : List (V × V), (∀ e ∈ E, Reach G e.1 e.2) →
      ∀ e ∈ E, Reach (assembledSteiner early T τ S sample E) e.1 e.2 by
    exact result D feasible d hd
  intro E
  induction E using List.reverseRecOn with
  | nil => simp
  | append_singleton E e ih =>
    intro f v hv
    have earlier (w : V × V) (hw : w ∈ E) : Reach G w.1 w.2 :=
      f w (List.mem_append_left _ hw)
    rcases List.mem_append.mp hv with hm | hm
    · exact reach_mono (assembledSteiner_prefix early T τ S sample ⟨[e],rfl⟩ f) (ih earlier v hm)
    · have same : v=e := List.mem_singleton.mp hm
      subst v
      have reach := f e (List.mem_append_right _ (List.mem_singleton_self _))
      dsimp only [assembledSteiner]
      rw [steinerPhaseTraces_snoc]
      split
      · exact reach
      · let st := steinerPhaseTraces early T S E
        have h := steinerPhaseTraces_facts early T S E
        exact phaseStep_serves early T S _ sample st e
          (fun d hd => earlier _ (h.early_in _ hd)) (fun d hd => earlier _ (h.thin_in _ hd)) reach

omit [Fintype V] in
theorem thinMean_union_const (G A : Arcs V) (output : ThinSample G → Arcs V) :
    thinMean G (fun sample => A ∪ output sample) ≤ (A.card:ℝ)+thinMean G output := by
  classical
  let q := (G.card:ℝ)^G.card
  have pos : 0 < q := by
    cases h : G.card with
    | zero => simpa only [q,h,Nat.cast_zero,pow_zero] using (zero_lt_one : (0:ℝ)<1)
    | succ m => dsimp only [q]; rw [h]; positivity
  have count : (Fintype.card (ThinSample G):ℝ) = q := by
    rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow]
  have point (sample : ThinSample G) : (((A ∪ output sample).card:ℕ):ℝ) ≤ (A.card:ℝ)+(output sample).card := by
    exact_mod_cast card_union_le A (output sample)
  change (∑ sample : ThinSample G, ((A ∪ output sample).card:ℝ))/q ≤
    (A.card:ℝ)+(∑ sample : ThinSample G, ((output sample).card:ℝ))/q
  calc
    _ ≤ (∑ sample : ThinSample G, ((A.card:ℝ)+(output sample).card))/q :=
      div_le_div_of_nonneg_right (sum_le_sum (fun s _ => point s)) pos.le
    _ = _ := by
      rw [sum_add_distrib,add_div,sum_const,nsmul_eq_mul,card_univ,count]
      have h : q*(A.card:ℝ)/q = (A.card:ℝ) := by
        rw [mul_comm q (A.card:ℝ),mul_div_assoc,div_self pos.ne',mul_one]
      rw [h]

private theorem phaseEarly_opt_lower {G Z : Arcs V} (early : EarlySteinerRule G)
    (T : ℕ) (S : Finset V) (D : List (V × V)) (sub : Z ⊆ G)
    (feasible : ∀ d ∈ D, Reach Z d.1 d.2) :
    (steinerPhaseTraces early T S D).early.length ≤ Z.card^2 := by
  let st := steinerPhaseTraces early T S D
  have facts := steinerPhaseTraces_facts early T S D
  let H (i : ℕ) := early.run (st.early.take i)
  have mono : Monotone H := fun _ _ hi => early.online (List.take_prefix_take_left hi)
  have reach (d : V × V) (hd : d ∈ st.early) : Reach Z d.1 d.2 :=
    feasible d (facts.early_in d hd)
  apply lemma20_nontrivial_trace st.early H mono facts.early_nontrivial _ Z
    (fun i => reach _ (st.early.get_mem i))
  intro i
  let E := st.early.take (i.1+1)
  have hmem : st.early.get i ∈ E :=
    List.mem_take_iff_getElem.mpr ⟨i.1,lt_min (Nat.lt_succ_self _) i.isLt,rfl⟩
  exact ((early.preserves E (fun d hd => reach_mono sub (reach d (List.mem_of_mem_take hd))))
    _ hmem).mpr (reach_mono sub (reach _ (st.early.get_mem i)))

/-- The initial request count is an offline lower bound whenever a
later hub request occurs. -/
theorem phaseCutoff_le_opt_of_hits {G Z : Arcs V} (early : EarlySteinerRule G)
    (T : ℕ) (S : Finset V) (D : List (V × V)) (sub : Z ⊆ G)
    (feasible : ∀ d ∈ D, Reach Z d.1 d.2)
    (later : (steinerPhaseTraces early T S D).hits ≠ []) : T ≤ Z.card ^ 2 := by
  have facts := steinerPhaseTraces_facts early T S D
  have eq : T = (steinerPhaseTraces early T S D).early.length := by
    apply le_antisymm _ facts.early_cap
    exact le_of_not_gt fun lt => later (facts.before_cutoff lt).1
  exact eq ▸ phaseEarly_opt_lower early T S D sub feasible

theorem steinerPhaseTraces_early_empty_at_zero {G : Arcs V} (early : EarlySteinerRule G)
    (S : Finset V) (D : List (V × V)) :
    (steinerPhaseTraces early 0 S D).early = [] := by
  apply List.length_eq_zero_iff.mp
  exact Nat.eq_zero_of_le_zero (steinerPhaseTraces_facts early 0 S D).early_cap

/-- The verified conditional mean of the assembled phases on a good hub draw.
The early routine enters only by the number of edges it actually bought. -/
theorem assembledSteiner_good_sample_bound_of_size {G Z : Arcs V} (early : EarlySteinerRule G)
    {T τ cutoff k : ℕ} {C : ℝ} (hc : 0 ≤ C) (hn : 0 < Fintype.card V)
    (ht : (Fintype.card V:ℝ)^(6/5:ℝ) ≤ cutoff)
    (draw : Fin k → V) (sampleSize : (k : ℝ) ≤ C * (Fintype.card V : ℝ) ^ (2/5 : ℝ))
    (good : draw ∉ thickFailures G τ _) (D : List (V × V))
    (sub : Z ⊆ G) (feasible : ∀ d ∈ D, Reach Z d.1 d.2)
    (optLower : (steinerPhaseTraces early T (sampledVertices draw) D).hits ≠ [] → cutoff ≤ Z.card ^ 2) :
    let S := sampledVertices draw
    let st := steinerPhaseTraces early T S D
    let L := thinRoundingFactor (Fintype.card V) τ
    let n : ℝ := Fintype.card V
    thinMean G (fun sample => assembledSteiner early T τ S sample D) ≤
      ((early.run st.early).card:ℝ)+
        ((6+4*C)*n^(3/5:ℝ)+((L:ℝ)*((G.card.log2:ℝ)+2)+1))*Z.card := by
  let S := sampledVertices draw
  let st := steinerPhaseTraces early T S D
  let L := thinRoundingFactor (Fintype.card V) τ
  let n : ℝ := Fintype.card V
  have facts := steinerPhaseTraces_facts early T S D
  have localThin (d : V × V) (hd : d ∈ st.thin) : (reachInterval G d).card ≤ τ := by
    by_contra! ht
    have thick : d ∈ thickPairs G τ := mem_filter.mpr ⟨mem_univ _,ht⟩
    obtain ⟨a,ha⟩ := hitHub_from_thick good thick
    rw [facts.thin_missed d hd] at ha
    cases ha
  have noFallback : ¬ st.thin.any (fun d => decide (τ < (reachInterval G d).card)) := by
    intro h
    obtain ⟨d,hd,lt⟩ := List.any_eq_true.mp h
    exact (not_lt_of_ge (localThin d hd)) (of_decide_eq_true lt)
  have output (sample : ThinSample G) : assembledSteiner early T τ S sample D =
      (early.run st.early ∪ hubPreserver G S st.hits) ∪ thinRoundRun G L sample st.thin := by
    change (if st.thin.any _ then G else phaseUnion early S L sample st) = _
    rw [ite_eq_right noFallback]
    rfl
  have hThin := thinRoundRun_competitive G Z sub τ st.thin facts.thin_distinct
    localThin facts.thin_nonself (fun d hd => feasible d (facts.thin_in d hd))
  have hHub : ((hubPreserver G S st.hits).card:ℝ) ≤
      (6+4*C)*n^(3/5:ℝ)*Z.card := by
    by_cases empty : st.hits=[]
    · simp [empty,hubPreserver,hitRequests,sinkPreserver,sourcePreserver,liftedRun]
      positivity
    · have hOpt := optLower empty
      let H (i : ℕ) := hubPreserver G S (st.hits.take i)
      have mono : Monotone H := fun _ _ hi => hubPreserver_prefix G S (List.take_prefix_take_left hi)
      exact hubPreserver_balanced_bound_of_size G S st.hits H mono hn ht
        ((Nat.cast_le.mpr (sampledVertices_card draw)).trans sampleSize) facts.hits_found
        facts.hits_nontrivial (fun _ => Subset.rfl) Z
        (fun i => feasible _ (facts.hits_in _ (st.hits.get_mem i))) hOpt
  have hUnion : (((early.run st.early ∪ hubPreserver G S st.hits).card:ℕ):ℝ) ≤
      ((early.run st.early).card:ℝ)+(hubPreserver G S st.hits).card := by
    exact_mod_cast card_union_le (early.run st.early) (hubPreserver G S st.hits)
  change thinMean G (fun sample => assembledSteiner early T τ S sample D) ≤ _
  simp only [output]
  apply (thinMean_union_const G _ _).trans
  change (((early.run st.early ∪ hubPreserver G S st.hits).card:ℕ):ℝ)+
    thinMean G (fun sample => thinRoundRun G L sample st.thin) ≤ _
  linarith only [hThin,hHub,hUnion]

theorem assembledSteiner_good_sample_bound_of_opt {G Z : Arcs V} (early : EarlySteinerRule G)
    {T τ cutoff : ℕ} {power : ℝ} (hp : 0 ≤ power) (hn : 0 < Fintype.card V)
    (ht : (Fintype.card V:ℝ)^(6/5:ℝ) ≤ cutoff) (hτ : (Fintype.card V:ℝ)^(3/5:ℝ) ≤ (τ:ℝ)+1)
    (draw : Fin (thickSampleCount (Fintype.card V) τ power) → V)
    (good : draw ∉ thickFailures G τ _) (D : List (V × V))
    (sub : Z ⊆ G) (feasible : ∀ d ∈ D, Reach Z d.1 d.2)
    (optLower : (steinerPhaseTraces early T (sampledVertices draw) D).hits ≠ [] → cutoff ≤ Z.card ^ 2) :
    let S := sampledVertices draw
    let st := steinerPhaseTraces early T S D
    let L := thinRoundingFactor (Fintype.card V) τ
    let n : ℝ := Fintype.card V
    thinMean G (fun sample => assembledSteiner early T τ S sample D) ≤
      ((early.run st.early).card:ℝ)+
        ((6+4*((2+power)*Real.log n+1))*n^(3/5:ℝ)+((L:ℝ)*((G.card.log2:ℝ)+2)+1))*Z.card := by
  have n1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have log0 := Real.log_nonneg n1
  exact assembledSteiner_good_sample_bound_of_size early (by positivity) hn ht draw
    (thickSampleCount_balanced hn hp hτ) good D sub feasible optLower

theorem assembledSteiner_good_sample_bound {G Z : Arcs V} (early : EarlySteinerRule G)
    {T τ : ℕ} {power : ℝ} (hp : 0 ≤ power) (hn : 0 < Fintype.card V)
    (ht : (Fintype.card V:ℝ)^(6/5:ℝ) ≤ T) (hτ : (Fintype.card V:ℝ)^(3/5:ℝ) ≤ (τ:ℝ)+1)
    (draw : Fin (thickSampleCount (Fintype.card V) τ power) → V)
    (good : draw ∉ thickFailures G τ _) (D : List (V × V))
    (sub : Z ⊆ G) (feasible : ∀ d ∈ D, Reach Z d.1 d.2) :
    let S := sampledVertices draw
    let st := steinerPhaseTraces early T S D
    let L := thinRoundingFactor (Fintype.card V) τ
    let n : ℝ := Fintype.card V
    thinMean G (fun sample => assembledSteiner early T τ S sample D) ≤
      ((early.run st.early).card:ℝ)+
        ((6+4*((2+power)*Real.log n+1))*n^(3/5:ℝ)+((L:ℝ)*((G.card.log2:ℝ)+2)+1))*Z.card :=
  assembledSteiner_good_sample_bound_of_opt early hp hn ht hτ draw good D sub feasible
    (phaseCutoff_le_opt_of_hits early T (sampledVertices draw) D sub feasible)

omit [Fintype V] in
private theorem thinMean_le_graph {G : Arcs V} (output : ThinSample G → Arcs V)
    (sub : ∀ sample, output sample ⊆ G) : thinMean G output ≤ G.card := by
  classical
  let q := (G.card:ℝ)^G.card
  have pos : 0 < q := by
    cases h : G.card with
    | zero => simpa only [q,h,Nat.cast_zero,pow_zero] using (zero_lt_one : (0:ℝ)<1)
    | succ m => dsimp only [q]; rw [h]; positivity
  have count : (Fintype.card (ThinSample G):ℝ) = q := by
    rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow]
  change (∑ sample : ThinSample G, ((output sample).card:ℝ))/q ≤ _
  apply (div_le_iff₀ pos).mpr
  calc
    _ ≤ ∑ _sample : ThinSample G, (G.card:ℝ) :=
      sum_le_sum (fun s _ => Nat.cast_le.mpr (card_le_card (sub s)))
    _ = (G.card:ℝ)*q := by rw [sum_const,nsmul_eq_mul,card_univ,count,mul_comm]

/-- Average over independent hub draws and edge thresholds. -/
noncomputable def assembledSteinerMeanOfDrawCount {G : Arcs V} (early : EarlySteinerRule G)
    (T τ k : ℕ) (D : List (V × V)) : ℝ :=
  (∑ draw : Fin k → V, thinMean G (fun s =>
    assembledSteiner early T τ (sampledVertices draw) s D))/(Fintype.card V:ℝ)^k

noncomputable def assembledSteinerMean {G : Arcs V} (early : EarlySteinerRule G)
    (T τ : ℕ) (power : ℝ) (D : List (V × V)) : ℝ :=
  assembledSteinerMeanOfDrawCount early T τ (thickSampleCount (Fintype.card V) τ power) D

private theorem thickFailureBound_all {G : Arcs V} {τ : ℕ} {power : ℝ} (hn : 0 < Fintype.card V) :
    let n := Fintype.card V
    let k := thickSampleCount n τ power
    ((thickFailures G τ k).card:ℝ)/(n:ℝ)^k ≤ (n:ℝ)^(-power) := by
  by_cases hτ : τ < Fintype.card V
  · exact thickSampleCount_probability G hn hτ
  · have empty : thickPairs G τ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro d hd
      have h := (mem_filter.mp hd).2
      exact hτ (h.trans_le (card_le_univ (reachInterval G d)))
    simp [thickFailures,empty]
    exact Real.rpow_nonneg (by positivity) _

/-- The combined mean bound with the actual early purchase bounded separately.
The stochastic estimate averages over both independent finite choices. -/
theorem assembledSteiner_mean_transfer_of_draw_count {G Z : Arcs V} (early : EarlySteinerRule G)
    {T τ cutoff k : ℕ} {C δ earlyCost : ℝ} (hc : 0 ≤ C) (hE : 0 ≤ earlyCost)
    (hn : 0 < Fintype.card V) (ht : (Fintype.card V:ℝ)^(6/5:ℝ) ≤ cutoff)
    (sampleSize : (k : ℝ) ≤ C * (Fintype.card V : ℝ) ^ (2/5 : ℝ))
    (failure : ((thickFailures G τ k).card : ℝ) / (Fintype.card V : ℝ) ^ k ≤ δ)
    (D : List (V × V)) (sub : Z ⊆ G) (feasible : ∀ d ∈ D, Reach Z d.1 d.2)
    (optLower : ∀ S : Finset V, (steinerPhaseTraces early T S D).hits ≠ [] → cutoff ≤ Z.card ^ 2)
    (earlyBound : ∀ S : Finset V,
      ((early.run (steinerPhaseTraces early T S D).early).card:ℝ) ≤ earlyCost) :
    let n : ℝ := Fintype.card V
    let L := thinRoundingFactor (Fintype.card V) τ
    assembledSteinerMeanOfDrawCount early T τ k D ≤ earlyCost+
      ((6+4*C)*n^(3/5:ℝ)+((L:ℝ)*((G.card.log2:ℝ)+2)+1))*Z.card+
      G.card*δ := by
  classical
  let n := Fintype.card V
  let L := thinRoundingFactor n τ
  let F := earlyCost+((6+4*C)*(n:ℝ)^(3/5:ℝ)+
    ((L:ℝ)*((G.card.log2:ℝ)+2)+1))*Z.card
  let bad := thickFailures G τ k
  let out (sample : Fin k → V) :=
    thinMean G (fun s => assembledSteiner early T τ (sampledVertices sample) s D)
  let charge (sample : Fin k → V) := if sample ∈ bad then (G.card:ℝ) else 0
  have n0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have F0 : 0 ≤ F := by dsimp [F]; positivity
  have point (sample : Fin k → V) : out sample ≤ F+charge sample := by
    by_cases badDraw : sample ∈ bad
    · have h := thinMean_le_graph
        (fun s => assembledSteiner early T τ (sampledVertices sample) s D)
        (fun s => (assembledSteiner_correct early T τ (sampledVertices sample) s D
          (fun d hd => reach_mono sub (feasible d hd))).1)
      change out sample ≤ (G.card:ℝ) at h
      simp only [charge,ite_eq_left badDraw]
      linarith only [h,F0]
    · have h := assembledSteiner_good_sample_bound_of_size early hc hn ht sample sampleSize badDraw D sub feasible
        (optLower (sampledVertices sample))
      have hEarc := earlyBound (sampledVertices sample)
      simp only [charge,ite_eq_right badDraw,add_zero]
      exact h.trans (add_le_add hEarc le_rfl)
  let q := (n:ℝ)^k
  have qpos : 0 < q := pow_pos n0 _
  have count : (Fintype.card (Fin k → V):ℝ) = q := by
    rw [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  have chargeSum : (∑ sample : Fin k → V, charge sample) = (G.card:ℝ)*(bad.card:ℝ) := by
    unfold charge
    rw [← sum_filter,filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul,mul_comm]
  have chance : (bad.card:ℝ)/q ≤ δ := failure
  change (∑ sample : Fin k → V, out sample)/q ≤ F+(G.card:ℝ)*δ
  calc
    _ ≤ (∑ sample : Fin k → V, (F+charge sample))/q :=
      div_le_div_of_nonneg_right (sum_le_sum (fun s _ => point s)) qpos.le
    _ = F+(G.card:ℝ)*((bad.card:ℝ)/q) := by
      rw [sum_add_distrib,add_div,chargeSum,sum_const,nsmul_eq_mul,card_univ,count]
      have h : q*F/q = F := by rw [mul_comm q F,mul_div_assoc,div_self qpos.ne',mul_one]
      rw [h,mul_div_assoc]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left chance (by positivity))

theorem assembledSteiner_mean_transfer_of_opt {G Z : Arcs V} (early : EarlySteinerRule G)
    {T τ cutoff : ℕ} {power earlyCost : ℝ} (hp : 0 ≤ power) (hE : 0 ≤ earlyCost)
    (hn : 0 < Fintype.card V) (ht : (Fintype.card V:ℝ)^(6/5:ℝ) ≤ cutoff)
    (hτ : (Fintype.card V:ℝ)^(3/5:ℝ) ≤ (τ:ℝ)+1)
    (D : List (V × V)) (sub : Z ⊆ G) (feasible : ∀ d ∈ D, Reach Z d.1 d.2)
    (optLower : ∀ S : Finset V, (steinerPhaseTraces early T S D).hits ≠ [] → cutoff ≤ Z.card ^ 2)
    (earlyBound : ∀ S : Finset V,
      ((early.run (steinerPhaseTraces early T S D).early).card:ℝ) ≤ earlyCost) :
    let n : ℝ := Fintype.card V
    let L := thinRoundingFactor (Fintype.card V) τ
    assembledSteinerMean early T τ power D ≤ earlyCost+
      ((6+4*((2+power)*Real.log n+1))*n^(3/5:ℝ)+((L:ℝ)*((G.card.log2:ℝ)+2)+1))*Z.card+
      G.card*n^(-power) := by
  have n1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have log0 := Real.log_nonneg n1
  exact assembledSteiner_mean_transfer_of_draw_count early (by positivity) hE hn ht
    (thickSampleCount_balanced hn hp hτ) (thickFailureBound_all hn) D sub feasible optLower earlyBound

theorem assembledSteiner_mean_transfer {G Z : Arcs V} (early : EarlySteinerRule G)
    {T τ : ℕ} {power earlyCost : ℝ} (hp : 0 ≤ power) (hE : 0 ≤ earlyCost)
    (hn : 0 < Fintype.card V) (ht : (Fintype.card V:ℝ)^(6/5:ℝ) ≤ T)
    (hτ : (Fintype.card V:ℝ)^(3/5:ℝ) ≤ (τ:ℝ)+1)
    (D : List (V × V)) (sub : Z ⊆ G) (feasible : ∀ d ∈ D, Reach Z d.1 d.2)
    (earlyBound : ∀ S : Finset V,
      ((early.run (steinerPhaseTraces early T S D).early).card:ℝ) ≤ earlyCost) :
    let n : ℝ := Fintype.card V
    let L := thinRoundingFactor (Fintype.card V) τ
    assembledSteinerMean early T τ power D ≤ earlyCost+
      ((6+4*((2+power)*Real.log n+1))*n^(3/5:ℝ)+((L:ℝ)*((G.card.log2:ℝ)+2)+1))*Z.card+
      G.card*n^(-power) :=
  assembledSteiner_mean_transfer_of_opt early hp hE hn ht hτ D sub feasible
    (fun S => phaseCutoff_le_opt_of_hits early T S D sub feasible) earlyBound

end OnlineReachabilityPreservers
