import DirectedFlowCutGap.CacheStabilizeProgram
import DirectedFlowCutGap.ControllerEpochParameters

/-! The literal tape interpreter composes epoch samples with their actual read counts. -/

namespace DirectedFlowCutGap.ControllerTapeModel

open BinaryArithmetic RetainedGridState IntegralNetworkFlow FiniteDrawTrees
open CandidateEnumeration (Node Network)
open EpochScanData (Graph cacheOf optimizer)
open CacheStabilizeProgram (stableCode stable_exact)
open PhysicalBoundedDrawExecution (draw sample solver_run)

private theorem draw_shift_word (fuel n : ℕ) (positive : 0<n) (tape : Bits) (start : ℕ)
    (word : Bits) (val : value word=n) (width : word.length=FairBitWords.width n) :
    (draw fuel n positive).run (tape,start) =
      ((draw fuel n positive).run (tape,0)).map (fun (x,(rest,reads)) => (x,(rest,start+reads))) := by
  subst n
  rw [PhysicalBoundedDrawExecution.draw_run word fuel positive width tape start,
    PhysicalBoundedDrawExecution.draw_run word fuel positive width tape 0]
  dsimp only [PhysicalBoundedDrawExecution.checkedFrom]
  by_cases fits : (PhysicalBoundedDrawProgram.outcome word fuel tape).requests.length≤tape.length <;> simp [fits]

private theorem draw_shift (fuel n : ℕ) (positive : 0<n) (tape : Bits) (start : ℕ) :
    (draw fuel n positive).run (tape,start) =
      ((draw fuel n positive).run (tape,0)).map (fun (x,(rest,reads)) => (x,(rest,start+reads))) :=
  draw_shift_word fuel n positive tape start n.bits (value_bits n)
    ((Nat.size_eq_bits_len n).trans (BinaryBoundedSampler.size_eq_width positive))

private theorem sample_shift (fuel n : ℕ) (positive : 0<n) (tape : Bits) (start : ℕ) :
    (sample fuel n positive).run (tape,start) =
      ((sample fuel n positive).run (tape,0)).map (fun (x,(rest,reads)) => (x,(rest,start+reads))) := by
  simp only [PhysicalBoundedDrawExecution.sample,StateT.run_map,draw_shift fuel n positive tape start]
  cases (draw fuel n positive).run (tape,0) with
  | none => rfl
  | some value => rcases value with ⟨_,_,_⟩; rfl

private theorem execute_shift {α : Type} (T : ℕ) (tree : FiniteDrawTrees.Tree α) (tape : Bits) (start : ℕ) :
    (execute (sample T) tree).run (tape,start) =
      ((execute (sample T) tree).run (tape,0)).map (fun (x,(rest,reads)) => (x,(rest,start+reads))) := by
  induction tree generalizing tape start with
  | pure x => simp [execute,StateT.run_pure]
  | draw n positive next ih =>
    simp only [execute,StateT.run_bind,sample_shift T n positive tape start]
    cases step : (sample T n positive).run (tape,0) with
    | none => rfl
    | some value =>
      rcases value with ⟨i,rest,reads⟩
      change (execute (sample T) (next i)).run (rest,start+reads) =
        ((execute (sample T) (next i)).run (rest,reads)).map
          (fun (x,(tail,count)) => (x,(tail,start+count)))
      rw [ih i rest (start+reads),ih i rest reads]
      cases (execute (sample T) (next i)).run (rest,0) with
      | none => rfl
      | some value =>
        rcases value with ⟨y,tail,count⟩
        simp [Nat.add_assoc]

theorem run_bind {α β : Type} (T : ℕ) (t : FiniteDrawTrees.Tree α) (next : α→FiniteDrawTrees.Tree β) (tape : Bits) :
    EncodedSolverBits.run (LazyFairBitTrees.lower T (t >>= next)) tape =
      ((EncodedSolverBits.run (LazyFairBitTrees.lower T t) tape).bind fun (x,(rest,reads)) =>
        (EncodedSolverBits.run (LazyFairBitTrees.lower T (next x)) rest).map fun (y,(suffix,count)) =>
          (y,(suffix,reads+count))) := by
  rw [solver_run]
  change (execute (sample T) (FiniteDrawTrees.bind t next)).run (tape,0) = _
  rw [MonadicBitSampler.execute_bind,StateT.run_bind,solver_run]
  cases first : (execute (sample T) t).run (tape,0) with
  | none => rfl
  | some value =>
    rcases value with ⟨x,rest,reads⟩
    simp only [Option.bind_some,solver_run]
    exact execute_shift T (next x) rest reads

variable {n L : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)}

noncomputable def tree (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (R : Bits)
    (restarts : ℕ) : ℕ → Code (Graph adj) demands L → FiniteDrawTrees.Tree (Code (Graph adj) demands L)
  | 0, s => .pure (stableCode positive E R restarts s)
  | epochs+1, s =>
    let c := stableCode positive E R restarts s
    if (cacheOf positive E c).optimal==0 then .pure c else
      RetainedDrawTrees.sampleTape positive c.data.remaining >>= fun t =>
        let input := RetainedTapeInput.materialize positive c.data.remaining t
        let next := EpochScanData.scan positive E R c.data.current.bits input.cell input.order c
        tree positive E R restarts epochs next

theorem scan_threshold (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (R M N : Bits)
    (h : value M=value N) (cells : Pair n→Fin L) (order : List (Pair n)) (s : Code (Graph adj) demands L) :
    EpochScanData.scan positive E R M cells order s=EpochScanData.scan positive E R N cells order s := by
  have first := EpochScanData.scan_exact positive E R M cells order s
  have second := EpochScanData.scan_exact positive E R N cells order s
  rw [h,second] at first
  exact congrArg (fun c => c.state) first.symm

private theorem map_bind {A B C : Type} (t : FiniteDrawTrees.Tree A) (g : A→FiniteDrawTrees.Tree B) (f : B→C) :
    map f (t >>= g) = t >>= fun a => map f (g a) := by
  induction t with
  | pure a => rfl
  | draw n positive next ih =>
    exact congrArg (FiniteDrawTrees.Tree.draw n positive) (funext ih)

private theorem reference_succ (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (R : Bits)
    (epochs restarts : ℕ) (s : Code (Graph adj) demands L) :
    let c := stableCode positive E R restarts s
    let Q := optimizer (adj:=adj) (demands:=demands) positive E
    let C := EpochScanData.cutOracle adj positive
    map (fun out => out.result.cache.state) (RetainedDrawTrees.executeTree Q positive C (value R) restarts (epochs+1)
      (cacheOf positive E s)) =
      if (cacheOf positive E c).optimal==0 then .pure c else
        RetainedDrawTrees.sampleTape positive c.data.remaining >>= fun t =>
          let input := RetainedTapeInput.materialize positive c.data.remaining t
          let next := EpochScanData.scan positive E R c.data.current.bits input.cell input.order c
          map (fun out => out.result.cache.state) (RetainedDrawTrees.executeTree Q positive C (value R) restarts epochs
            (cacheOf positive E next)) := by
  dsimp only
  unfold RetainedDrawTrees.executeTree
  rw [RetainedSampledExecution.executeSampled,stable_exact]
  split
  · rfl
  · simp only [map_bind]
    congr 1
    funext t
    let c := stableCode positive E R restarts s
    let input := RetainedTapeInput.materialize positive c.data.remaining t
    let Q := optimizer (adj:=adj) (demands:=demands) positive E
    let C := EpochScanData.cutOracle adj positive
    let b := IntegerAdaptiveExecution.scan Q positive C (value R) c.data.current input.cell input.order (cacheOf positive E c)
    let next := EpochScanData.scan positive E R c.data.current.bits input.cell input.order c
    let resumeTree (cursor : _) := RetainedSampledExecution.executeSampled (RetainedDrawTrees.sampleTape positive)
      Q positive C (value R) restarts epochs cursor
    change map (fun out => out.result.cache.state) (resumeTree b.cache) =
      map (fun out => out.result.cache.state) (resumeTree (cacheOf positive E next))
    have eq : b.cache=cacheOf positive E next := by
      simpa only [b,next,value_bits] using EpochScanData.scan_exact positive E R c.data.current.bits input.cell input.order c
    rw [eq]

theorem tree_exact (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (R : Bits)
    (epochs restarts : ℕ) (s : Code (Graph adj) demands L) :
    tree positive E R restarts epochs s =
      map (fun out => out.result.cache.state)
        (RetainedDrawTrees.executeTree (optimizer (adj:=adj) (demands:=demands) positive E) positive
          (EpochScanData.cutOracle adj positive) (value R) restarts epochs (cacheOf positive E s)) := by
  induction epochs generalizing s with
  | zero => rfl
  | succ epochs ih =>
    rw [tree,reference_succ]
    split
    · rfl
    · congr 1
      funext t
      exact ih _

noncomputable abbrev run (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (R : Bits)
    (trials restarts epochs : ℕ) (s : Code (Graph adj) demands L) (tape : Bits) :=
  EncodedSolverBits.run (LazyFairBitTrees.lower trials (tree positive E R restarts epochs s)) tape

theorem run_step (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (R : Bits)
    (trials restarts epochs : ℕ) (s : Code (Graph adj) demands L) (tape : Bits) :
    let c := stableCode positive E R restarts s
    run positive E R trials restarts (epochs+1) s tape =
      if (cacheOf positive E c).optimal==0 then some (c,(tape,0)) else
        (EncodedSolverBits.run (LazyFairBitTrees.lower trials (RetainedDrawTrees.sampleTape positive c.data.remaining)) tape).bind
          (fun (t,(rest,reads)) =>
            let input := RetainedTapeInput.materialize positive c.data.remaining t
            let next := EpochScanData.scan positive E R c.data.current.bits input.cell input.order c
            (run positive E R trials restarts epochs next rest).map fun (last,(suffix,count)) =>
              (last,(suffix,reads+count))) := by
  dsimp only [run]
  rw [tree]
  split
  · rfl
  · exact run_bind _ _ _ _

theorem row_widths {B : ℕ} (d : Data n) (words : List (List Bits))
    (data : RetainedMassTableProgram.DataRows d.weights words) (widths : ∀ ws∈words,∀ w∈ws,w.length≤B) :
    ∀ p (v : Fin n),(row d.weights p)[v.val].bits.length≤B := by
  intro p v
  let selected := RoundWeightRowProgram.selected p words
  have seen : selected∈words := RoundWeightRowProgram.selected_mem data p
  have values : selected.map value=(row d.weights p).toList := RoundWeightRowProgram.selected_values data p
  have count : selected.length=n := by simpa only [List.length_map,Vector.length_toList] using congrArg List.length values
  have range : v.val<selected.length := count.symm ▸ v.isLt
  have eq : value selected[v.val]=(row d.weights p)[v.val] := by
    have indexMap : v.val<(selected.map value).length := by simpa only [List.length_map] using range
    have indexRow : v.val<(row d.weights p).toList.length := by simpa only [Vector.length_toList] using v.isLt
    have get := congrArg (fun xs : List ℕ => xs[v.val]?) values
    rw [List.getElem?_eq_getElem indexMap,List.getElem?_eq_getElem indexRow,List.getElem_map,Vector.getElem_toList] at get
    exact Option.some.inj get
  rw [← eq,Nat.size_eq_bits_len]
  exact Nat.size_le.mpr ((value_lt selected[v.val]).trans_le (Nat.pow_le_pow_right (by decide) (widths _ seen _ (List.getElem_mem range))))

end DirectedFlowCutGap.ControllerTapeModel
