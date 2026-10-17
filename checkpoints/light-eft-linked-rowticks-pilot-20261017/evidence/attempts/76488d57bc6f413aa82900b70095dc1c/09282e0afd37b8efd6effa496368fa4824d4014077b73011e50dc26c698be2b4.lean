import LightEFTSpanners.LinkedDistanceTrace
namespace LightEFTSpanners.LinkedDistance
open RationalDistance
variable (size : ℕ) (M : Matrix) (source target : ℕ) (budget : ℚ)
local notation "go" => transition size M source target budget

 theorem initial_trace (k i : ℕ) (acc : List Cell) :
    Executes go (k+1) (.init k i acc)
      (.revInit (((List.range' i k).map (fun j => if j=target then some (0:ℚ) else none)).reverse++acc) []) := by
  induction k generalizing i acc with
  | zero => exact Executes.one rfl
  | succ k ih =>
    have h := Executes.cons (step:=go)
      (show go (.init (k+1) i acc)=some (.init k (i+1) ((if i=target then some 0 else none)::acc)) from rfl)
      (ih (i+1) ((if i=target then some 0 else none)::acc))
    simpa [List.range'_succ,List.reverse_cons,List.append_assoc] using h

 theorem reverse_initial_trace (xs out : List Cell) :
    Executes go (xs.length+1) (.revInit xs out) (.round size (xs.reverse++out)) := by
  induction xs generalizing out with
  | nil => exact Executes.one rfl
  | cons x xs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using
      Executes.cons (step:=go) rfl (ih (x::out))

 theorem initial_setup_trace :
    Executes go (2*size+2) (.init size 0 []) (.round size (initial size target)) := by
  have h := (initial_trace size M source target budget size 0 []).trans
    (reverse_initial_trace size M source target budget
      (((List.range' 0 size).map (fun j => if j=target then some (0:ℚ) else none)).reverse++[]) [])
  have hr : List.range' 0 size=List.range size := by
    apply List.ext_getElem <;> simp
  convert h using 1 <;> simp [hr,initial]
  omega

 theorem lookup_trace (i : ℕ) (d : List Cell) :
    ∃ t, t ≤ i + 1 ∧ Executes go t (.lookup i d)
      (.halt (test ((d[i]?).getD none) budget)) := by
  induction i generalizing d with
  | zero => cases d <;> exact ⟨1,by omega,Executes.one rfl⟩
  | succ i ih =>
    cases d with
    | nil => exact ⟨1,by omega,Executes.one rfl⟩
    | cons x xs =>
      obtain ⟨t,ht,he⟩ := ih xs
      exact ⟨t+1,by omega,Executes.cons rfl he⟩

 theorem machine_terminates (hM : M.length=size) (hs : source<size) :
    ∃ t,t≤size^3+3*size^2+6*size+4 ∧
      Executes go t (.init size 0 [])
        (.halt (test (((rounds M size (initial size target))[source]?).getD none) budget)) := by
  obtain ⟨t,ht,he⟩ := round_trace size M source target budget size (initial size target)
  obtain ⟨q,hq,hqe⟩ := lookup_trace size M source target budget source (rounds M size (initial size target))
  have hstart := initial_setup_trace size M source target budget
  have hlast := (Executes.one (step:=go)
    (show go (.round 0 (rounds M size (initial size target)))=
      some (.lookup source (rounds M size (initial size target))) from rfl)).trans hqe
  refine ⟨(2*size+2)+t+(1+q),?_,(hstart.trans he).trans hlast⟩
  simp only [initial,List.length_map,List.length_range,hM] at ht
  nlinarith

end LightEFTSpanners.LinkedDistance
