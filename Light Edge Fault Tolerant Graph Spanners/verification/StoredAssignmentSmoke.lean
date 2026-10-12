import LightEFTSpanners.StoredAssignmentExecutable
open LightEFTSpanners

def require (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

def main : IO Unit := do
  let w : Sym2 (Fin 2) → ℚ := fun _ => 5
  let es : List (Fin 2 × Fin 2) := [(0,1)]
  let go := fun (js : Sym2 (Fin 2) → List Unit)
      (input : Sym2 (Fin 2) → Unit → StoredHosts.TypedInput 2) =>
    StoredCandidates.execute [] [] (StoredRecords.encodeWeights w) 2 1
      ((StoredCandidates.assignmentRecords w 1 js input es).map StoredCandidates.encode)
  require "fixed assignment accepting record" (go (fun _ => [()]) (fun _ _ => ⟨[],[[]]⟩)==[(0,1)])
  require "fixed assignment host path rejects" (go (fun _ => [()]) (fun _ _ => ⟨[(1,0)],[[]]⟩)==[])
  require "fixed assignment zero draws rejects" (go (fun _ => [()]) (fun _ _ => ⟨[],[]⟩)==[])
  require "fixed assignment empty eligible list rejects" (go (fun _ => []) (fun _ _ => ⟨[],[[]]⟩)==[])
