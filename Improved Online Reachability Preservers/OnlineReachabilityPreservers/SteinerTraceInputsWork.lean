import OnlineReachabilityPreservers.DeterministicEnumerationWork
import OnlineReachabilityPreservers.SteinerSeedDecoderWork

/-! Meter phase splitting and the distinct sampled hub list. -/

namespace OnlineReachabilityPreservers

/-- Split the demand list in one traversal of its early segment. -/
def splitSteinerTraceWithWordWork {A : Type*} :
    ℕ → List A → (List A × List A) × ℕ
  | 0, rows => (([],rows),4)
  | _+1, [] => (([],[]),5)
  | k+1, first::rows =>
    let rest := splitSteinerTraceWithWordWork k rows
    ((first::rest.1.1,rest.1.2),rest.2+11)

theorem splitSteinerTraceWithWordWork_spec {A : Type*} (k : ℕ) (rows : List A) :
    let out := splitSteinerTraceWithWordWork k rows
    out.1 = (rows.take k,rows.drop k) ∧ out.2 ≤ 11*rows.length+5 := by
  induction k generalizing rows with
  | zero => simp [splitSteinerTraceWithWordWork]
  | succ k ih =>
    cases rows with
    | nil => simp [splitSteinerTraceWithWordWork]
    | cons first rows =>
      obtain ⟨same,charge⟩ := ih rows
      rw [splitSteinerTraceWithWordWork]
      dsimp only
      constructor
      · rw [same, List.take_succ_cons, List.drop_succ_cons]
      · rw [List.length_cons,Nat.mul_succ 11 rows.length]
        omega

private def collectSampledVerticesWithWordWork {V : Type*} [DecidableEq V] {k : ℕ}
    (read : Fin k → V × ℕ) : List (Fin k) → List V × ℕ
  | [] => ([],3)
  | i::rest =>
    let tail := collectSampledVerticesWithWordWork read rest
    let draw := read i
    let seen := memScanWithWordWork draw.1 tail.1
    ((if seen.1 then tail.1 else draw.1::tail.1),tail.2+draw.2+seen.2+14)

private theorem collectSampledVerticesWithWordWork_spec {V : Type*} [DecidableEq V] {k : ℕ}
    (read : Fin k → V × ℕ) (draw : Fin k → V) (exactDraw : ∀ i, (read i).1 = draw i)
    (C : ℕ) (charge : ∀ i, (read i).2 ≤ C) (B : ℕ) (slots : List (Fin k)) (room : slots.length ≤ B) :
    let out := collectSampledVerticesWithWordWork read slots
    out.1.toFinset = slots.toFinset.image draw ∧ out.1.Nodup ∧ out.1.length ≤ slots.length ∧
      out.2 ≤ slots.length*(C+2*B+15)+3 := by
  induction slots with
  | nil => simp [collectSampledVerticesWithWordWork]
  | cons i rest ih =>
    let tail := collectSampledVerticesWithWordWork read rest
    let found := memScanWithWordWork (read i).1 tail.1
    have inputLen : rest.length+1 ≤ B := room
    obtain ⟨same,unique,len,work⟩ := ih (Nat.le_of_succ_le inputLen)
    obtain ⟨decideMember,lookup⟩ := memScanWithWordWork_spec (read i).1 tail.1
    have cap := charge i
    have reads : found.2 ≤ 2*B+1 := lookup.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (len.trans (Nat.le_of_succ_le inputLen))) 1)
    change (if found.1 then tail.1 else (read i).1::tail.1).toFinset = (i::rest).toFinset.image draw ∧
      (if found.1 then tail.1 else (read i).1::tail.1).Nodup ∧
      (if found.1 then tail.1 else (read i).1::tail.1).length ≤ (i::rest).length ∧
      tail.2+(read i).2+found.2+14 ≤ (i::rest).length*(C+2*B+15)+3
    change tail.2 ≤ _ at work
    have workBound : tail.2+(read i).2+found.2+14 ≤ (i::rest).length*(C+2*B+15)+3 := by
      rw [List.length_cons,Nat.succ_mul]
      omega
    by_cases seen : (read i).1 ∈ tail.1
    · have yes : found.1 = true := by rw [decideMember]; simp [seen]
      have belongs : draw i ∈ rest.toFinset.image draw := by
        rw [← same, ← exactDraw]
        exact List.mem_toFinset.mpr seen
      simp only [yes, ite_true,List.toFinset_cons,Finset.image_insert,Finset.insert_eq_of_mem belongs]
      exact ⟨same,unique,len.trans (Nat.le_succ _),workBound⟩
    · have no : found.1 = false := by rw [decideMember]; simp [seen]
      simp only [no,Bool.false_eq_true,ite_false,List.toFinset_cons,Finset.image_insert]
      exact ⟨by rw [same,exactDraw],List.nodup_cons.mpr ⟨seen,unique⟩,Nat.succ_le_succ len,workBound⟩

/-- Enumerate sample positions once and avoid duplicate hub records.
Each read is charged at the supplied sample lookup cost. -/
def sampledVertexListWithWordWork {V : Type*} [DecidableEq V] {k : ℕ}
    (read : Fin k → V × ℕ) : List V × ℕ :=
  let slots := finVerticesWithWordWork k
  let out := collectSampledVerticesWithWordWork read slots.1
  (out.1,slots.2+out.2+4)

theorem sampledVertexListWithWordWork_spec {V : Type*} [DecidableEq V] {k : ℕ}
    (read : Fin k → V × ℕ) (draw : Fin k → V) (exactDraw : ∀ i, (read i).1 = draw i)
    (C : ℕ) (charge : ∀ i, (read i).2 ≤ C) :
    let out := sampledVertexListWithWordWork read
    out.1.toFinset = sampledVertices draw ∧ out.1.Nodup ∧
      out.2 ≤ k*(C+2*k+23)+8 := by
  let slots := finVerticesWithWordWork k
  let out := collectSampledVerticesWithWordWork read slots.1
  have card : slots.1.length = k := by
    rw [finVerticesWithWordWork_eq_sort]
    simp
  obtain ⟨_,all,enum⟩ := finVerticesWithWordWork_spec k
  have full : slots.1.toFinset = Finset.univ := Finset.eq_univ_of_forall (fun x => List.mem_toFinset.mpr (all x))
  obtain ⟨same,unique,_,work⟩ := collectSampledVerticesWithWordWork_spec read draw exactDraw C charge k slots.1 card.le
  rw [full] at same
  rw [card] at work
  change out.2 ≤ _ at work
  refine ⟨same,unique,?_⟩
  change slots.2+out.2+4 ≤ _
  change slots.2 = _ at enum
  rw [enum]
  calc
    _ ≤ (8*k+1)+(k*(C+2*k+15)+3)+4 := by omega
    _ = _ := by ring

/-- Integer cutoffs and the number of hub draws for one scale of input graph. -/
structure SteinerTraceParameters (n : ℕ) where
  earlyCutoff : ℕ
  thinThreshold : ℕ
  hubCount : ℕ
  earlyCutoff_eq : earlyCutoff = steinerEarlyCutoff n
  thinThreshold_eq : thinThreshold = steinerThinThreshold n
  hubCount_eq : hubCount = steinerHubDraws n (steinerThinThreshold n)

/-- Compute both phase cutoffs and the hub array length once. -/
def steinerTraceParametersWithWordWork (n : ℕ) : SteinerTraceParameters n × ℕ :=
  let square := n*n
  let cube := square*n
  let early := fifthRootWithWork (cube*cube) square
  let thin := fifthRootWithWork cube n
  let bits := bitLengthWithWork n
  let draws := if n = 0 then 0 else (4 * max 1 bits.1 * n)/(thin.1+1)+1
  have earlyEq : early.1+1 = steinerEarlyCutoff n := by
    dsimp only [early,cube,square]
    rw [show (n*n*n)*(n*n*n) = n^6 by ring, show n*n = n^2 by ring]
    rw [(fifthRootWithWork_spec _ _).1]
    rfl
  have thinEq : thin.1 = steinerThinThreshold n := by
    dsimp only [thin,cube,square]
    rw [show n*n*n = n^3 by ring, (fifthRootWithWork_spec _ _).1]
    rfl
  have drawEq : draws = steinerHubDraws n (steinerThinThreshold n) := by
    dsimp only [draws,bits]
    rw [(bitLengthWithWork_spec n).1,max_size_eq_log2_add_one,thinEq]
    rfl
  (⟨early.1+1,thin.1,draws,earlyEq,thinEq,drawEq⟩,early.2+thin.2+bits.2+26)

theorem steinerTraceParametersWithWordWork_bound (n : ℕ) :
    (steinerTraceParametersWithWordWork n).2 ≤ 16*n^2+23*n+33 := by
  have early := (fifthRootWithWork_spec ((n*n*n)*(n*n*n)) (n*n)).2
  have thin := (fifthRootWithWork_spec (n*n*n) n).2
  have bits := bitLengthWork_le n
  dsimp only [steinerTraceParametersWithWordWork]
  rw [pow_two]
  omega

/-- Read each original draw once and prepare a duplicate-free hub set.
The caller supplies the already computed sample count. -/
def collectSteinerHubsWithWordWork {V : Type*} [DecidableEq V] {k K : ℕ} (sameCount : k = K)
    (draw : Fin K → V) : Finset V × ℕ :=
  let read := fun i : Fin k => (draw ⟨i.val,sameCount ▸ i.isLt⟩,3)
  let out := sampledVertexListWithWordWork read
  have noDuplicates := (sampledVertexListWithWordWork_spec read
    (fun i => (read i).1) (fun _ => rfl) 3 (fun _ => le_rfl)).2.1
  (⟨(out.1 : Multiset V),Multiset.coe_nodup.mpr noDuplicates⟩,out.2+5)

theorem collectSteinerHubsWithWordWork_spec {V : Type*} [DecidableEq V] {k K : ℕ}
    (sameCount : k = K) (draw : Fin K → V) :
    let out := collectSteinerHubsWithWordWork sameCount draw
    out.1 = sampledVertices draw ∧ out.2 ≤ k*(2*k+26)+13 := by
  subst K
  let read := fun i : Fin k => (draw i,3)
  obtain ⟨equal,_,work⟩ := sampledVertexListWithWordWork_spec read draw (fun _ => rfl) 3 (fun _ => le_rfl)
  have bound : (sampledVertexListWithWordWork read).2+5 ≤ k*(2*k+26)+13 := by
    exact (Nat.add_le_add_right work 5).trans_eq (by ring)
  refine ⟨?_,bound⟩
  ext v
  have normal : v ∈ (sampledVertexListWithWordWork read).1.toFinset ↔ v ∈ sampledVertices draw :=
    equal ▸ Iff.rfl
  exact List.mem_toFinset.symm.trans normal

end OnlineReachabilityPreservers
