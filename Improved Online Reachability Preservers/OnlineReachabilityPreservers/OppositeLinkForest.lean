import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import OnlineReachabilityPreservers.OppositeIntersectionPruning
import OnlineReachabilityPreservers.OppositePathChains

/-! Cycles of consecutive opposite intersections force full bridges. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped List

local notation "Before" => SourceAudit.BeforeIn

variable {V I : Type*} [DecidableEq V] [LinearOrder I]

/-- A link joins consecutive common vertices of two oppositely ordered paths. -/
def oppositeLinkGraphOfHalfTwo (paths : I → List V) (two : HalfBridgeFree (Before paths) 2) : SimpleGraph V where
  Adj x y := ∃ a b, OppositeNeighbors paths a b x y
  symm := ⟨by
    rintro _ _ ⟨a,b,h⟩
    exact ⟨b,a,oppositeNeighbors_swap_of_halfTwo two h⟩⟩
  loopless := ⟨by
    rintro _ ⟨_,_,h⟩
    exact listBefore_ne h.2.1 rfl⟩

def oppositeLinkGraph (paths : I → List V) (three : BridgeFree (Before paths) 3) : SimpleGraph V :=
  oppositeLinkGraphOfHalfTwo paths (fun _ size => three.halfFree (size.trans (by decide)))

omit [LinearOrder I] in
private theorem listBefore_transitive {paths : I → List V} {a : I} {x y z : V}
    (xy : Before paths a x y) (yz : Before paths a y z) : Before paths a x z :=
  ⟨xy.1,yz.2.1,xy.2.2.trans yz.2.2⟩

private theorem opposite_forward_unique {paths : I → List V} (two : HalfBridgeFree (Before paths) 2)
    {x y : V} {a b c d : I} (ab : OppositeNeighbors paths a b x y) (cd : OppositeNeighbors paths c d x y) :
    a = c ∧ b = d := by
  constructor <;> by_contra different
  · exact no_parallel_list_steps two (by decide) different ab.2.1 cd.2.1
  · exact no_parallel_list_steps two (by decide) different ab.2.2.1 cd.2.2.1

private theorem opposite_adjacent_forward {paths : I → List V} (three : BridgeFree (Before paths) 3)
    {x y z : V} {a b c d : I} (xy : OppositeNeighbors paths a b x y) (yz : OppositeNeighbors paths c d y z)
    (apart : x ≠ z) (carries : a = c ∨ a = d) : a = c := by
  rcases carries with h | h
  · exact h
  · subst d
    exact (apart (oppositeNeighbors_in_unique three xy (oppositeNeighbors_swap three yz))).elim

/-- An internal gap starts after a last present index and ends before the next present index. -/
private theorem exists_between_gap (P : ℕ → Prop) {i j k : ℕ} (ij : i < j) (jk : j < k)
    (hi : P i) (hj : ¬ P j) (hk : P k) :
    ∃ a b, i ≤ a ∧ a < j ∧ j < b ∧ b ≤ k ∧ P a ∧ P b ∧ ∀ t, a < t → t < b → ¬ P t := by
  classical
  have before : ∃ d, d ≤ j-i ∧ P (j-d) := ⟨j-i,le_rfl,by rwa [Nat.sub_sub_self ij.le]⟩
  have after : ∃ b, j ≤ b ∧ b ≤ k ∧ P b := ⟨k,jk.le,le_rfl,hk⟩
  let d := Nat.find before
  let b := Nat.find after
  let a := j-d
  have left : d ≤ j-i ∧ P a := Nat.find_spec before
  have right : j ≤ b ∧ b ≤ k ∧ P b := Nat.find_spec after
  have dl : d ≤ j := left.1.trans (Nat.sub_le _ _)
  have ia : i ≤ a := by unfold a; omega
  have aj : a < j := (Nat.sub_le _ _).lt_of_ne (fun eq => hj (eq ▸ left.2))
  have jb : j < b := right.1.lt_of_ne (fun eq => hj (eq.symm ▸ right.2.2))
  refine ⟨a,b,ia,aj,jb,right.2.1,left.2,right.2.2,?_⟩
  intro t atb tb ht
  by_cases jt : j ≤ t
  · exact (Nat.find_min after tb) ⟨jt,tb.le.trans right.2.1,ht⟩
  · have dlt : j-t < Nat.find before := by change j-t < d; unfold a at atb; omega
    exact (Nat.find_min before dlt) ⟨by omega,by rwa [Nat.sub_sub_self (by omega : t ≤ j)]⟩

/-- A simple reversible route joining two vertices of a river that owns none of its links. -/
private structure OppositeDetour (paths : I → List V) (length : ℕ) where
  vertex : ℕ → V
  distinct : ∀ i ≤ length, ∀ j ≤ length, vertex i = vertex j → i = j
  river : I
  ordered : Before paths river (vertex 0) (vertex length)
  links : ∀ i < length, ∃ a b, OppositeNeighbors paths a b (vertex i) (vertex (i+1)) ∧ river ≠ a ∧ river ≠ b

private theorem makeOppositeDetour {paths : I → List V} (three : BridgeFree (Before paths) 3)
    {n : ℕ} (positive : 0 < n) (vertex : ℕ → V) (river : I)
    (distinct : ∀ i ≤ n, ∀ j ≤ n, vertex i = vertex j → i = j)
    (first : vertex 0 ∈ paths river) (last : vertex n ∈ paths river)
    (links : ∀ i < n, ∃ a b, OppositeNeighbors paths a b (vertex i) (vertex (i+1)) ∧ river ≠ a ∧ river ≠ b) :
    Nonempty (OppositeDetour paths n) := by
  have apart : vertex 0 ≠ vertex n := fun eq => positive.ne (distinct 0 (Nat.zero_le _) n le_rfl eq)
  rcases listBefore_total first last apart with increasing | decreasing
  · exact ⟨⟨vertex,distinct,river,increasing,links⟩⟩
  refine ⟨⟨fun i => vertex (n-i),?_,river,?_,?_⟩⟩
  · intro i hi j hj equal
    have equal' := distinct (n-i) (Nat.sub_le _ _) (n-j) (Nat.sub_le _ _) equal
    omega
  · simpa using decreasing
  · intro i hi
    obtain ⟨a,b,step,ra,rb⟩ := links (n-(i+1)) (by omega)
    refine ⟨b,a,?_,rb,ra⟩
    rw [show n-i=n-(i+1)+1 by omega]
    exact oppositeNeighbors_swap three step

private def ContiguousLabels (labels : List I) : Prop :=
  ∀ front a middle suffix, labels = front ++ a :: (middle ++ a :: suffix) →
    ∀ b ∈ middle, b = a

omit [LinearOrder I] in
private theorem ContiguousLabels.tail {a : I} {labels : List I} (h : ContiguousLabels (a::labels)) :
    ContiguousLabels labels := by
  intro front b middle suffix eq c hc
  exact h (a::front) b middle suffix (congrArg (a::·) eq) c hc

omit [LinearOrder I] in
private theorem ContiguousLabels.head_of_mem {a : I} {labels : List I}
    (h : ContiguousLabels (a::labels)) (mem : a ∈ labels) : labels.head? = some a := by
  obtain ⟨front,suffix,shape⟩ := List.append_of_mem mem
  cases front with
  | nil => simp [shape]
  | cons b rest =>
    have head := h [] a (b::rest) suffix (by simp [shape]) b (by simp)
    simp [shape,head]

omit [LinearOrder I] in
private theorem contiguousLabels_of_indices {n : ℕ} (label : ℕ → I)
    (runs : ∀ i j k, i ≤ j → j ≤ k → k < n → label i = label k → label j = label i) :
    ContiguousLabels (List.ofFn fun i : Fin n => label i) := by
  intro front a middle suffix shape b present
  obtain ⟨j,hj,hb⟩ := List.mem_iff_getElem.mp present
  let left := front.length
  let mid := left+1+j
  let right := left+1+middle.length
  have full : n = left+1+middle.length+1+suffix.length := by
    simpa [left, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg List.length shape
  have hleft : left < n := by omega
  have hmid : mid < n := by unfold mid; omega
  have hright : right < n := by unfold right; omega
  have l : label left = a := by
    have eq := congrArg (fun l : List I => l[left]?) shape
    simpa [List.getElem?_append, left, hleft] using eq
  have r : label right = a := by
    have eq := congrArg (fun l : List I => l[right]?) shape
    have shift : right-front.length-1 = middle.length := by unfold right left; omega
    simpa [right, left, List.getElem?_append, List.getElem?_cons, show ¬ right < front.length by dsimp [right,left]; omega,
      show right-front.length ≠ 0 by dsimp [right,left]; omega, shift, List.getElem?_ofFn, hright] using eq
  have m : label mid = b := by
    have eq := congrArg (fun l : List I => l[mid]?) shape
    have shift : mid-front.length-1 = j := by unfold mid left; omega
    simpa [mid, left, List.getElem?_append, List.getElem?_cons, show ¬ mid < front.length by dsimp [mid,left]; omega,
      show mid-front.length ≠ 0 by dsimp [mid,left]; omega, shift, List.getElem?_ofFn, hmid,hj,hb] using eq
  rw [← m,← l]
  exact runs left mid right (by unfold mid; omega) (by unfold mid right; omega) hright (l.trans r.symm)

private inductive DirectedListRoute (paths : I → List V) : V → V → List I → List V → Prop
  | nil (u : V) : DirectedListRoute paths u u [] [u]
  | cons {u v w : V} {a : I} {labels : List I} {vertices : List V}
      (step : Before paths a u v) (tail : DirectedListRoute paths v w labels vertices) :
      DirectedListRoute paths u w (a::labels) (u::vertices)

namespace DirectedListRoute

omit [LinearOrder I] in
private theorem of_indices {paths : I → List V} {n : ℕ} (v : ℕ → V) (label : ℕ → I)
    (steps : ∀ i < n, Before paths (label i) (v i) (v (i+1))) :
    DirectedListRoute paths (v 0) (v n) (List.ofFn fun i : Fin n => label i)
      (List.ofFn fun i : Fin (n+1) => v i) := by
  induction n generalizing v label with
  | zero => simpa only [List.ofFn_zero,List.ofFn_succ,Fin.val_zero] using nil (paths := paths) (v 0)
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    exact .cons (steps 0 (by omega)) (ih (fun i => v (i+1)) (fun i => label (i+1))
      (fun i hi => steps (i+1) (by omega)))

omit [LinearOrder I] in
private theorem compress {paths : I → List V} {u w : V} {labels : List I} {vertices : List V}
    (p : DirectedListRoute paths u w labels vertices) (blocks : ContiguousLabels labels) :
    ∃ labels' vertices', DirectedListRoute paths u w labels' vertices' ∧ labels'.Nodup ∧
      labels' <+ labels ∧ labels'.head? = labels.head? ∧ vertices' <+ vertices := by
  induction p with
  | nil => exact ⟨[],[_],.nil _,by simp,List.Sublist.slnil,rfl,List.Sublist.refl _⟩
  | @cons u v w a labels vertices step tail ih =>
    obtain ⟨ls,vs,reduced,nd,sub,head,support⟩ := ih blocks.tail
    cases reduced with
    | nil =>
      exact ⟨[a],[u,v],.cons step (.nil v),by simp,sub.cons_cons _,rfl,support.cons_cons _⟩
    | @cons v x w b bs xs next rest =>
      by_cases same : a = b
      · subst b
        exact ⟨a::bs,u::xs,.cons (listBefore_transitive step next) rest,nd,sub.cons _,rfl,
          ((List.Sublist.refl xs).cons v).trans support |>.cons_cons u⟩
      · have fresh : a ∉ b::bs := by
          intro mem
          have wanted := blocks.head_of_mem (sub.subset mem)
          exact same (Option.some.inj (wanted.symm.trans head.symm))
        exact ⟨a::b::bs,u::v::xs,.cons step (.cons next rest),List.nodup_cons.mpr ⟨fresh,nd⟩,
          sub.cons_cons _,rfl,support.cons_cons _⟩

omit [LinearOrder I] in
private theorem coordinates {paths : I → List V} {u w : V} {labels : List I} {vertices : List V}
    (p : DirectedListRoute paths u w labels vertices) :
    ∃ v : Fin (labels.length+1) → V, List.ofFn v = vertices ∧ v 0 = u ∧ v (Fin.last labels.length) = w ∧
      ∀ i, Before paths (labels.get i) (v i.castSucc) (v i.succ) := by
  induction p with
  | nil => exact ⟨fun _ => _,by simp,rfl,rfl,fun i => i.elim0⟩
  | @cons u v w a labels vertices step tail ih =>
    obtain ⟨x,shape,first,last,steps⟩ := ih
    let all : Fin ((a::labels).length+1) → V := Fin.cases u x
    refine ⟨all,?_,rfl,?_,?_⟩
    · rw [List.ofFn_succ]
      change u :: List.ofFn x = u :: vertices
      rw [shape]
    · exact last
    · intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j,rfl⟩
      · change Before paths a u (x 0)
        rwa [first]
      · exact steps j

end DirectedListRoute

/-- In a shortest detour over all rivers, repeated labels occur in consecutive blocks. -/
private theorem minimum_detour_yields_bridge {paths : I → List V}
    (three : BridgeFree (Before paths) 3) {n : ℕ} (d : OppositeDetour paths n)
    (minimal : ∀ m < n, ¬ Nonempty (OppositeDetour paths m)) :
    ∃ k, k+1 ≤ n ∧ Nonempty (Bridge (Before paths) k) := by
  classical
  let v := d.vertex
  let step (i : Fin n) := Classical.choose_spec (d.links i.val i.isLt)
  let front (i : ℕ) : I := if h : i < n then Classical.choose (d.links i h) else d.river
  let rear (i : ℕ) : I := if h : i < n then Classical.choose (step ⟨i,h⟩) else d.river
  have link (i : ℕ) (hi : i < n) : OppositeNeighbors paths (front i) (rear i) (v i) (v (i+1)) ∧
      d.river ≠ front i ∧ d.river ≠ rear i := by
    simp only [front,rear,dite_eq_left hi]
    exact Classical.choose_spec (step ⟨i,hi⟩)
  let carries (a : I) (i : ℕ) := a = front i ∨ a = rear i
  have onPath (a : I) {i : ℕ} (hi : i < n) (h : carries a i) :
      v i ∈ paths a ∧ v (i+1) ∈ paths a := by
    rcases h with eq | eq
    · rw [eq]
      exact ⟨(link i hi).1.2.1.1,(link i hi).1.2.1.2.1⟩
    · rw [eq]
      exact ⟨(link i hi).1.2.2.1.2.1,(link i hi).1.2.2.1.1⟩
  have contiguous (a : I) (i j k : ℕ) (ij : i ≤ j) (jk : j ≤ k) (kn : k < n)
      (first : carries a i) (last : carries a k) : carries a j := by
    by_contra gap
    have ij' : i < j := ij.lt_of_ne (fun eq => gap (eq ▸ first))
    have jk' : j < k := jk.lt_of_ne (fun eq => gap (eq.symm ▸ last))
    obtain ⟨x,y,_,xj,jy,yk,start,finish,missing⟩ := exists_between_gap (carries a) ij' jk' first gap last
    let m := y-(x+1)
    have xn : x < n := by omega
    have yn : y < n := yk.trans_lt kn
    refine minimal m (by unfold m; omega) (makeOppositeDetour three (by unfold m; omega)
      (fun t => v (x+1+t)) a ?_ ?_ ?_ ?_)
    · intro s hs t ht same
      have eq := d.distinct (x+1+s) (by unfold m at hs; omega) (x+1+t) (by unfold m at ht; omega) same
      omega
    · simpa using (onPath a xn start).2
    · rw [show x+1+m = y by unfold m; omega]
      exact (onPath a yn finish).1
    · intro t ht
      let b := x+1+t
      have bn : b < n := by unfold b m at *; omega
      have avoid := missing b (by unfold b; omega) (by unfold b m at *; omega)
      exact ⟨front b,rear b,by simpa [b,Nat.add_assoc] using (link b bn).1,
        fun eq => avoid (.inl eq),fun eq => avoid (.inr eq)⟩
  have blocks (i j k : ℕ) (ij : i ≤ j) (jk : j ≤ k) (kn : k < n) (agree : front i = front k) :
      front j = front i := by
    have inside (b : ℕ) (ib : i ≤ b) (bk : b ≤ k) : carries (front i) b :=
      contiguous _ i b k ib bk kn (.inl rfl) (.inl agree)
    induction j, ij using Nat.le_induction with
    | base => rfl
    | succ b ib ih =>
      have sbk : b+1 ≤ k := jk
      have bn : b+1 < n := sbk.trans_lt kn
      have diff : v b ≠ v (b+2) := fun eq => by
        have e := d.distinct b (by omega) (b+2) (by omega) eq
        omega
      have mark : carries (front b) (b+1) := by
        rw [ih (by omega)]
        exact inside (b+1) (by omega) sbk
      exact (opposite_adjacent_forward three (link b (by omega)).1 (link (b+1) bn).1 diff mark).symm.trans (ih (by omega))
  let labels := List.ofFn fun i : Fin n => front i
  let vertices := List.ofFn fun i : Fin (n+1) => v i
  have path := DirectedListRoute.of_indices v front (fun i hi => (link i hi).1.2.1)
  obtain ⟨colors,corners,compressed,unique,used,_,kept⟩ := path.compress (contiguousLabels_of_indices front blocks)
  have cornersSimple : corners.Nodup := kept.nodup (by
    change vertices.Nodup
    rw [List.nodup_ofFn]
    intro i j same
    apply Fin.ext
    exact d.distinct i.val (by omega) j.val (by omega) same)
  have different (a : I) (mem : a ∈ colors) : d.river ≠ a := by
    have present : a ∈ labels := used.subset mem
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp present
    rw [← eq]
    exact (link i.val i.isLt).2.1
  have count := used.length_le
  rw [List.length_ofFn] at count
  obtain ⟨corner,shape,first,last,arcs⟩ := compressed.coordinates
  cases colors with
  | nil =>
    have eq : v 0 = v n := first.symm.trans ((congrArg corner (Subsingleton.elim (0 : Fin 1) (Fin.last 0))).trans last)
    exact (listBefore_ne d.ordered eq).elim
  | cons a tail =>
    refine ⟨tail.length,count,⟨?_⟩⟩
    refine {
      vertex := corner
      arc := (a::tail).get
      river := d.river
      distinctVertices := ?_
      distinctArcs := List.nodup_iff_injective_get.mp unique
      river_ne_arc := fun i => different _ (List.get_mem (a::tail) i)
      riverStep := ?_
      arcStep := arcs }
    · rw [← shape,List.nodup_ofFn] at cornersSimple
      exact cornersSimple
    · change Before paths d.river (corner 0) (corner (Fin.last (a::tail).length))
      rw [first,last]
      exact d.ordered

private theorem detour_yields_bridge {paths : I → List V} (three : BridgeFree (Before paths) 3)
    {n : ℕ} (detour : Nonempty (OppositeDetour paths n)) :
    ∃ k, k+1 ≤ n ∧ Nonempty (Bridge (Before paths) k) := by
  classical
  have existsDetour : ∃ m, Nonempty (OppositeDetour paths m) := ⟨n,detour⟩
  obtain ⟨short⟩ := Nat.find_spec existsDetour
  obtain ⟨k,length,bridge⟩ := minimum_detour_yields_bridge three short (fun m h => Nat.find_min existsDetour h)
  exact ⟨k,length.trans (Nat.find_min' existsDetour detour), bridge⟩

/-- A cycle of opposite links yields a full bridge no larger than the cycle. -/
theorem oppositeLinkGraph_cycle_forces_bridge {paths : I → List V} (three : BridgeFree (Before paths) 3)
    {u : V} (cycle : (oppositeLinkGraph paths three).Walk u u) (isCycle : cycle.IsCycle) :
    ∃ k, k+2 ≤ cycle.length ∧ Nonempty (Bridge (Before paths) k) := by
  classical
  let length := cycle.length
  let v := cycle.getVert
  have large : 3 ≤ length := isCycle.three_le_length
  have edge (i : ℕ) (hi : i < length) : ∃ a b, OppositeNeighbors paths a b (v i) (v (i+1)) :=
    cycle.adj_getVert_succ hi
  obtain ⟨river,opposite,firstLink⟩ := edge 0 (by omega)
  let onLink (i : ℕ) := ∃ a, OppositeNeighbors paths river a (v i) (v (i+1)) ∨
    OppositeNeighbors paths river a (v (i+1)) (v i)
  have atStart : onLink 0 := ⟨opposite,.inl firstLink⟩
  have closes : v length = v 0 := by simp [length,v,SimpleGraph.Walk.getVert_length]
  have noTurn (i : ℕ) (hi : i+2 ≤ length) : v i ≠ v (i+2) := by
    intro eq
    by_cases inside : i+2 < length
    · have bad := isCycle.getVert_injOn' (by change i ≤ cycle.length-1; omega)
        (by change i+2 ≤ cycle.length-1; omega) eq
      omega
    · have bad := isCycle.getVert_injOn (by change 1 ≤ i ∧ i ≤ cycle.length; constructor <;> omega)
        (by change 1 ≤ i+2 ∧ i+2 ≤ cycle.length; constructor <;> omega) eq
      omega
  have missing : ∃ i < length, ¬ onLink i := by
    by_contra! all
    have forward (i : ℕ) (hi : i < length) : ∃ b, OppositeNeighbors paths river b (v i) (v (i+1)) := by
      induction i with
      | zero => exact ⟨opposite,firstLink⟩
      | succ i ih =>
        obtain ⟨a,previous⟩ := ih (by omega)
        obtain ⟨b,relation | relation⟩ := all (i+1) hi
        · exact ⟨b,relation⟩
        · exact (noTurn i (by omega) (oppositeNeighbors_in_unique three previous relation)).elim
    have across (i : ℕ) (positive : 0 < i) (hi : i ≤ length) : Before paths river (v 0) (v i) := by
      induction i with
      | zero => omega
      | succ i ih =>
        obtain ⟨_,step⟩ := forward i (by omega)
        by_cases zero : i = 0
        · simpa [zero] using step.2.1
        · exact listBefore_transitive (ih (by omega) (by omega)) step.2.1
    exact listBefore_ne (across length (by omega) le_rfl) closes.symm
  obtain ⟨i,ir,absent⟩ := missing
  let on (j : ℕ) := j = length ∨ onLink j
  have no : ¬ on i := fun h => h.elim ir.ne absent
  have pos : 0 < i := Nat.pos_of_ne_zero (fun e => absent (e ▸ atStart))
  obtain ⟨a,b,_,ai,ib,br,ma,mb,inside⟩ := exists_between_gap on pos ir (.inr atStart) no (.inl rfl)
  have ar : a < length := ai.trans ir
  let m := b-(a+1)
  have before : v (a+1) ∈ paths river := by
    obtain ⟨_,ab | ab⟩ := ma.resolve_left ar.ne
    · exact ab.2.1.2.1
    · exact ab.2.1.1
  have after : v b ∈ paths river := by
    rcases mb with eq | onMember
    · simpa [eq,closes] using firstLink.2.1.1
    · obtain ⟨_,ab | ab⟩ := onMember
      · exact ab.2.1.1
      · exact ab.2.1.2.1
  have detour : Nonempty (OppositeDetour paths m) := by
    refine makeOppositeDetour three (by unfold m; omega) (fun t => v (a+1+t)) river ?_ (by simpa using before) ?_ ?_
    · intro s hs t ht eq
      have same := isCycle.getVert_injOn (x₁ := a+1+s) (x₂ := a+1+t)
        (by change 1 ≤ a+1+s ∧ a+1+s ≤ cycle.length; unfold m at hs; constructor <;> omega)
        (by change 1 ≤ a+1+t ∧ a+1+t ≤ cycle.length; unfold m at ht; constructor <;> omega) eq
      omega
    · simpa only [show a+1+m = b by unfold m; omega] using after
    · intro t ht
      let j := a+1+t
      have jb : j < b := by unfold m at ht; unfold j; omega
      obtain ⟨f,r,h⟩ := edge j (jb.trans_le br)
      have skipped : ¬ onLink j := fun mem => inside j (by unfold j; omega) jb (.inr mem)
      exact ⟨f,r,by simpa [j,Nat.add_assoc] using h,
        fun eq => skipped ⟨r,.inl (eq.symm ▸ h)⟩,
        fun eq => skipped ⟨f,.inr (eq.symm ▸ oppositeNeighbors_swap three h)⟩⟩
  obtain ⟨k,bound,bridge⟩ := detour_yields_bridge three detour
  exact ⟨k,by unfold m at bound; change k+2 ≤ length; omega, bridge⟩

/-- At a finite full-bridge cutoff, a cycle of opposite links must be longer than the cutoff. -/
theorem oppositeLinkGraph_cycle_length_gt_cutoff {paths : I → List V} {cutoff : ℕ}
    (free : BridgeFree (Before paths) cutoff) (three : 3 ≤ cutoff) {u : V}
    (cycle : (oppositeLinkGraph paths (fun _ h => free (h.trans three))).Walk u u)
    (isCycle : cycle.IsCycle) : cutoff < cycle.length := by
  by_contra! short
  obtain ⟨_,size,⟨bridge⟩⟩ := oppositeLinkGraph_cycle_forces_bridge _ cycle isCycle
  exact (free (size.trans short)).false bridge

/-- With full bridge exclusion at every size, the opposite-neighbor graph is a forest. -/
theorem oppositeLinkGraph_acyclic {paths : I → List V} (three : BridgeFree (Before paths) 3)
    (full : ∀ k, IsEmpty (Bridge (Before paths) k)) : (oppositeLinkGraph paths three).IsAcyclic := by
  intro u cycle isCycle
  obtain ⟨k,_,⟨bridge⟩⟩ := oppositeLinkGraph_cycle_forces_bridge three cycle isCycle
  exact (full k).false bridge

theorem oppositeLinkGraph_card_edgeSet [Fintype V] {paths : I → List V} (three : BridgeFree (Before paths) 3)
    (full : ∀ k, IsEmpty (Bridge (Before paths) k)) :
    Nat.card (oppositeLinkGraph paths three).edgeSet ≤ Fintype.card V - 1 := by
  classical
  let G := oppositeLinkGraph paths three
  by_cases empty : IsEmpty V
  · let _ := empty
    change Nat.card G.edgeSet ≤ Fintype.card V - 1
    simp
  · let _ : Nonempty V := not_isEmpty_iff.mp empty
    obtain ⟨T,inside,_,tree⟩ := SimpleGraph.connected_top.exists_isTree_le_of_le_of_isAcyclic
      (H := G) le_top (oppositeLinkGraph_acyclic three full)
    have size := tree.card_edgeFinset
    change Nat.card G.edgeSet ≤ Fintype.card V - 1
    rw [Nat.card_eq_fintype_card, ← G.edgeFinset_card]
    exact (card_le_card (SimpleGraph.edgeFinset_mono inside)).trans (by omega)

variable [Fintype V]

private structure OppositePruneCharge {p : ℕ} (paths : Fin p → List V) (i : Fin p) (v : V) where
  earlier : Fin p
  precedes : earlier < i
  next : V
  link : OppositeNeighbors paths i earlier v next

omit [Fintype V] in
private theorem oppositePruneCharge_exists {p : ℕ} {paths : Fin p → List V}
    (two : HalfBridgeFree (Before paths) 2) (simple : ∀ i, (paths i).Nodup) {i : Fin p} {v : V}
    (present : v ∈ paths i) (missing : v ∉ removeOppositeIntersections paths i) :
    Nonempty (OppositePruneCharge paths i v) := by
  rw [removeOppositeIntersections_mem] at missing
  push Not at missing
  obtain ⟨j,ji,u,forward,backward⟩ := missing present
  have connected := oppositeNeighbors_connect_of_halfTwo two ji.ne' forward (removeOppositeIntersections_before simple backward)
  have initial {x y : V} (h : Relation.TransGen (OppositeNeighbors paths i j) x y) :
      ∃ z, OppositeNeighbors paths i j x z := by
    induction h with
    | single h => exact ⟨_,h⟩
    | tail _ _ ih => exact ih
  obtain ⟨w,adjacent⟩ := initial connected
  exact ⟨⟨j,ji,w,adjacent⟩⟩

/-- Each removed incidence charges a distinct opposite link in the original family. -/
theorem removeOppositeIntersections_mass_with_half_two_link_count {p : ℕ} {paths : Fin p → List V}
    (two : HalfBridgeFree (Before paths) 2) (simple : ∀ i, (paths i).Nodup) :
    (∑ i, (paths i).length) ≤ (∑ i, (removeOppositeIntersections paths i).length) +
      Nat.card (oppositeLinkGraphOfHalfTwo paths two).edgeSet := by
  classical
  let retained := removeOppositeIntersections paths
  let omitted := (univ : Finset (Fin p × V)).filter fun x => x.2 ∈ paths x.1 ∧ x.2 ∉ retained x.1
  let G := oppositeLinkGraphOfHalfTwo paths two
  let witness (x : omitted) := Classical.choice (oppositePruneCharge_exists two simple
    (mem_filter.mp x.property).2.1 (mem_filter.mp x.property).2.2)
  let charge (x : omitted) : G.edgeSet :=
    ⟨s(x.val.2,(witness x).next),G.mem_edgeSet.mpr ⟨x.val.1,(witness x).earlier,(witness x).link⟩⟩
  have injective : Function.Injective charge := by
    intro x y same
    have endpoints := Sym2.eq_iff.mp (congrArg Subtype.val same)
    rcases endpoints with ⟨sameStart,sameEnd⟩ | ⟨swappedStart,swappedEnd⟩
    · have aligned : OppositeNeighbors paths y.val.1 (witness y).earlier x.val.2 (witness x).next :=
        (congrArg₂ (OppositeNeighbors paths y.val.1 (witness y).earlier) sameStart sameEnd).mpr (witness y).link
      exact Subtype.ext (Prod.ext (opposite_forward_unique two (witness x).link aligned).1 sameStart)
    · have reversed : OppositeNeighbors paths (witness y).earlier y.val.1 x.val.2 (witness x).next :=
        (congrArg₂ (OppositeNeighbors paths (witness y).earlier y.val.1) swappedStart swappedEnd).mpr
          (oppositeNeighbors_swap_of_halfTwo two (witness y).link)
      have owners := opposite_forward_unique two (witness x).link reversed
      have backwards : y.val.1 < (witness y).earlier :=
        (congrArg₂ (fun a b : Fin p => a < b) owners.2 owners.1).mp (witness x).precedes
      exact (lt_asymm backwards (witness y).precedes).elim
  have loss : omitted.card ≤ Nat.card G.edgeSet := by
    rw [Nat.card_eq_fintype_card,← Fintype.card_coe]
    exact Fintype.card_le_of_injective charge injective
  have omittedSize : omitted.card = ∑ i, ((paths i).toFinset \ (retained i).toFinset).card := by
    unfold omitted
    rw [card_filter,← univ_product_univ,Finset.sum_product]
    apply sum_congr rfl
    intro i _
    rw [← card_filter]
    congr 1
    ext v
    simp
  have simpleKept (i : Fin p) : (retained i).Nodup :=
    (removeOppositeIntersections_sublist paths i).nodup (simple i)
  have subset (i : Fin p) : (retained i).toFinset ⊆ (paths i).toFinset := fun v hv =>
    List.mem_toFinset.mpr ((removeOppositeIntersections_sublist paths i).subset (List.mem_toFinset.mp hv))
  have exactMass : omitted.card + (∑ i, (retained i).length) = ∑ i, (paths i).length := by
    rw [omittedSize,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [← List.toFinset_card_of_nodup (simpleKept i),← List.toFinset_card_of_nodup (simple i),
      card_sdiff_add_card_eq_card (subset i)]
  change (∑ i, (paths i).length) ≤ (∑ i, (retained i).length) + Nat.card G.edgeSet
  omega

theorem removeOppositeIntersections_mass_with_link_count {p : ℕ} {paths : Fin p → List V}
    (three : BridgeFree (Before paths) 3) (simple : ∀ i, (paths i).Nodup) :
    (∑ i, (paths i).length) ≤ (∑ i, (removeOppositeIntersections paths i).length) +
      Nat.card (oppositeLinkGraph paths three).edgeSet :=
  removeOppositeIntersections_mass_with_half_two_link_count
    (fun _ size => three.halfFree (size.trans (by decide))) simple

/-- For full bridge exclusion at every size, pruning to unique intersections
discards at most one less than the number of vertices. -/
theorem removeOppositeIntersections_mass_of_fullFree {p : ℕ} {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) (full : ∀ k, IsEmpty (Bridge (Before paths) k)) :
    (∑ i, (paths i).length) ≤ (∑ i, (removeOppositeIntersections paths i).length) + (Fintype.card V - 1) := by
  have three : BridgeFree (Before paths) 3 := fun {k} _ => full k
  exact (removeOppositeIntersections_mass_with_link_count three simple).trans
    (Nat.add_le_add_left (oppositeLinkGraph_card_edgeSet three full) _)

omit [Fintype V] in
private theorem halfThree_river_before_final {paths : I → List V} (free : HalfBridgeFree (Before paths) 3)
    {a b r : I} (ab : a ≠ b) (ra : r ≠ a) (rb : r ≠ b)
    {x y z : V} (xy : Before paths a x y) (yz : Before paths b y z) (xz : Before paths r x z) : r < b := by
  have permitted : ¬ b < r := free (k := 1) (by decide) (threeListBridge ab ra rb xy yz xz)
  exact (le_of_not_gt permitted).lt_of_ne rb

omit [Fintype V] in
private theorem halfThree_no_opposite_triangle_on_path {paths : I → List V} (free : HalfBridgeFree (Before paths) 3)
    {x y z : V} {line : I} (xy : Before paths line x y) (yz : Before paths line y z)
    (linkXY : ∃ a b, OppositeNeighbors paths a b x y)
    (linkYZ : ∃ a b, OppositeNeighbors paths a b y z)
    (linkXZ : ∃ a b, OppositeNeighbors paths a b x z) : False := by
  obtain ⟨_,backXY,opXY⟩ := linkXY
  obtain ⟨_,backYZ,opYZ⟩ := linkYZ
  obtain ⟨frontXZ,backXZ,opXZ⟩ := linkXZ
  have legYX : Before paths backXY y x := opXY.2.2.1
  have legZY : Before paths backYZ z y := opYZ.2.2.1
  have legZX : Before paths backXZ z x := opXZ.2.2.1
  have same : frontXZ = line := by
    by_contra different
    exact no_parallel_list_steps free (by decide) different opXZ.2.1 (listBefore_transitive xy yz)
  subst frontXZ
  have missing : y ∉ paths backXZ := fun mem => opXZ.2.2.2 ⟨y,xy,yz,mem⟩
  have outsideXY : backXZ ≠ backXY := fun same => missing (same.symm ▸ legYX.1)
  have outsideYZ : backXZ ≠ backYZ := fun same => missing (same.symm ▸ legZY.2.1)
  have two : backYZ ≠ backXY := by
    intro same
    have step := listBefore_transitive legZY (same.symm ▸ legYX)
    exact no_parallel_list_steps free (by decide) outsideYZ legZX step
  have differentLine : backXY ≠ line := by
    intro same
    exact (lt_asymm xy.2.2 (same ▸ legYX).2.2)
  have forward := halfThree_river_before_final free two outsideYZ outsideXY legZY legYX legZX
  have backward := halfThree_river_before_final free opXZ.1 differentLine outsideXY.symm yz legZX legYX
  exact (not_lt_of_ge backward.le) forward

omit [Fintype V] in
/-- Three opposite links cannot form a triangle in a half-3-bridge-free
system. The ordering of the two competing last arcs would have to run
in both directions. -/
theorem halfThree_oppositeLinkGraph_no_triangle {paths : I → List V} (free : HalfBridgeFree (Before paths) 3)
    {x y z : V}
    (xy : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj x y)
    (yz : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj y z)
    (zx : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj z x) : False := by
  let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
  have xy' : G.Adj y x := xy.symm
  have yz' : G.Adj z y := yz.symm
  have zx' : G.Adj x z := zx.symm
  have apartXY : x ≠ y := G.ne_of_adj xy
  have apartYZ : y ≠ z := G.ne_of_adj yz
  have apartZX : z ≠ x := G.ne_of_adj zx
  have noCommon (owner : I) (atX : x ∈ paths owner) (atY : y ∈ paths owner) (atZ : z ∈ paths owner) : False := by
    rcases listBefore_total atX atY apartXY with orderedXY | orderedYX
    · rcases listBefore_total atY atZ apartYZ with orderedYZ | orderedZY
      · exact halfThree_no_opposite_triangle_on_path free orderedXY orderedYZ xy yz zx'
      · rcases listBefore_total atX atZ apartZX.symm with orderedXZ | orderedZX
        · exact halfThree_no_opposite_triangle_on_path free orderedXZ orderedZY zx' yz' xy
        · exact halfThree_no_opposite_triangle_on_path free orderedZX orderedXY zx xy yz'
    · rcases listBefore_total atX atZ apartZX.symm with orderedXZ | orderedZX
      · exact halfThree_no_opposite_triangle_on_path free orderedYX orderedXZ xy' zx' yz
      · rcases listBefore_total atY atZ apartYZ with orderedYZ | orderedZY
        · exact halfThree_no_opposite_triangle_on_path free orderedYZ orderedZX yz zx xy'
        · exact halfThree_no_opposite_triangle_on_path free orderedZY orderedYX yz' xy' zx
  obtain ⟨a,ar,sideXY⟩ := xy
  obtain ⟨b,_,sideYZ⟩ := yz
  obtain ⟨c,_,sideXZ⟩ := zx'
  have stepXY := sideXY.2.1
  have stepYX := sideXY.2.2.1
  have stepYZ := sideYZ.2.1
  have stepXZ := sideXZ.2.1
  have ab : a ≠ b := fun same => noCommon a stepXY.1 stepXY.2.1 (same.symm ▸ stepYZ.2.1)
  have ca : c ≠ a := fun same => noCommon c stepXZ.1 (same.symm ▸ stepXY.2.1) stepXZ.2.1
  have cb : c ≠ b := fun same => noCommon c stepXZ.1 (same.symm ▸ stepYZ.1) stepXZ.2.1
  have arc : ar ≠ c := fun same => noCommon ar stepYX.2.1 stepYX.1 (same.symm ▸ stepXZ.2.1)
  have bar : b ≠ ar := fun same => noCommon b (same.symm ▸ stepYX.2.1) stepYZ.1 stepYZ.2.1
  have forward := halfThree_river_before_final free ab ca cb stepXY stepYZ stepXZ
  have backward := halfThree_river_before_final free arc bar cb.symm stepYX stepXZ stepYZ
  exact (not_lt_of_ge backward.le) forward


omit [Fintype V] in
/-- If two vertices of a path are joined by two opposite links, the
intermediate vertex lies on the same path. -/
theorem halfThree_mem_of_two_opposite_links {paths : I → List V} (free : HalfBridgeFree (Before paths) 3)
    {x w z : V} {line : I} (xz : Before paths line x z)
    (left : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj x w)
    (right : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj w z) :
    w ∈ paths line := by
  obtain ⟨c,e,left⟩ := left
  obtain ⟨d,f,right⟩ := right
  by_contra missing
  have lineC : line ≠ c := fun same => missing (same.symm ▸ left.2.1.2.1)
  have lineE : line ≠ e := fun same => missing (same.symm ▸ left.2.2.1.1)
  have lineD : line ≠ d := fun same => missing (same.symm ▸ right.2.1.1)
  have lineF : line ≠ f := fun same => missing (same.symm ▸ right.2.2.1.2.1)
  have cd : c ≠ d := by
    intro same
    exact no_parallel_list_steps free (by decide) lineC xz
      (listBefore_transitive left.2.1 (same.symm ▸ right.2.1))
  have before := halfThree_river_before_final free cd lineC lineD left.2.1 right.2.1 xz
  have ed : e = d := by
    by_contra different
    have after := halfThree_river_before_final free lineE.symm (fun same => different same.symm) lineD.symm
      left.2.2.1 xz right.2.1
    exact (not_lt_of_ge after.le) before
  subst e
  have zd : z ∈ paths d := right.2.1.2.1
  have xd : x ∈ paths d := left.2.2.1.2.1
  have zxD : Before paths d z x := by
    rcases listBefore_total zd xd (listBefore_ne xz).symm with zx | xz'
    · exact zx
    · exact (no_parallel_list_steps free (by decide) lineD xz xz').elim
  have cf : c ≠ f := by
    intro same
    have zc : z ∈ paths c := same.symm ▸ right.2.2.1.1
    have zxC : Before paths c z x := by
      rcases listBefore_total zc left.2.1.1 (listBefore_ne xz).symm with zx | xz'
      · exact zx
      · exact (no_parallel_list_steps free (by decide) lineC xz xz').elim
    have flipped := oppositeNeighbors_swap_of_halfTwo (fun _ h => free (h.trans (by decide))) right
    exact flipped.2.2.2 ⟨x,same ▸ zxC,same ▸ left.2.1,xd⟩
  have earlier := halfThree_river_before_final free lineF lineC.symm cf xz right.2.2.1 left.2.1
  have later := halfThree_river_before_final free cd.symm right.1.symm cf.symm zxD left.2.1 right.2.2.1
  exact (not_lt_of_ge later.le) earlier


omit [Fintype V] in
private theorem halfFour_river_before_final {paths : I → List V} (free : HalfBridgeFree (Before paths) 4)
    {a b c r : I} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (ra : r ≠ a) (rb : r ≠ b) (rc : r ≠ c)
    {x y z t : V} (xz : x ≠ z) (yt : y ≠ t)
    (first : Before paths a x y) (second : Before paths b y z) (last : Before paths c z t)
    (direct : Before paths r x t) : r < c := by
  let bridge : Bridge (Before paths) 2 := {
    vertex := ![x,y,z,t]
    arc := ![a,b,c]
    river := r
    distinctVertices := by
      intro i j eq
      have xy := listBefore_ne first
      have yz := listBefore_ne second
      have zt := listBefore_ne last
      have xt := listBefore_ne direct
      fin_cases i <;> fin_cases j <;> simp_all
    distinctArcs := by
      intro i j eq
      fin_cases i <;> fin_cases j <;> simp_all
    river_ne_arc := by intro i; fin_cases i <;> first | exact ra | exact rb | exact rc
    riverStep := direct
    arcStep := by intro i; fin_cases i <;> first | exact first | exact second | exact last }
  exact (le_of_not_gt (free (k := 2) (by decide) bridge)).lt_of_ne rc

private abbrev LinkedOpposite {paths : I → List V} (free : HalfBridgeFree (Before paths) 3) (x y : V) : Prop :=
  (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj x y

omit [Fintype V] in
private theorem halfThree_middle_on_line {paths : I → List V} (free : HalfBridgeFree (Before paths) 3)
    {i : I} {x w z : V} (xmem : x ∈ paths i) (zmem : z ∈ paths i) (xz : x ≠ z)
    (left : LinkedOpposite free x w) (right : LinkedOpposite free w z) : w ∈ paths i := by
  rcases listBefore_total xmem zmem xz with straight | reversed
  · exact halfThree_mem_of_two_opposite_links free straight left right
  · exact halfThree_mem_of_two_opposite_links free reversed right.symm left.symm

omit [Fintype V] in
private theorem halfFour_square_return_order {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 4) {u x w z : V}
    (oppUW : u ≠ w) (oppXZ : x ≠ z)
    (ux : LinkedOpposite (fun _ h => free (h.trans (by decide))) u x)
    (xw : LinkedOpposite (fun _ h => free (h.trans (by decide))) x w)
    (wz : LinkedOpposite (fun _ h => free (h.trans (by decide))) w z)
    (zu : LinkedOpposite (fun _ h => free (h.trans (by decide))) z u)
    (noFull : ∀ i, u ∈ paths i → x ∈ paths i → w ∈ paths i → z ∈ paths i → False) :
    ∃ a b, Before paths a x u ∧ Before paths b z u ∧ b < a := by
  let three : HalfBridgeFree (Before paths) 3 := fun _ h => free (h.trans (by decide))
  have noUW {i : I} (umem : u ∈ paths i) (wmem : w ∈ paths i) : False :=
    noFull i umem (halfThree_middle_on_line three umem wmem oppUW ux xw)
      wmem (halfThree_middle_on_line three umem wmem oppUW zu.symm wz.symm)
  have noXZ {i : I} (xmem : x ∈ paths i) (zmem : z ∈ paths i) : False :=
    noFull i (halfThree_middle_on_line three xmem zmem oppXZ ux.symm zu.symm) xmem
      (halfThree_middle_on_line three xmem zmem oppXZ xw wz) zmem
  obtain ⟨_,a,oppUX⟩ := ux
  obtain ⟨_,c,oppXW⟩ := xw
  obtain ⟨_,d,oppWZ⟩ := wz
  obtain ⟨b,_,oppZU⟩ := zu
  have xu := oppUX.2.2.1
  have wx := oppXW.2.2.1
  have zw := oppWZ.2.2.1
  have stepZU := oppZU.2.1
  have dc : d ≠ c := fun same => noXZ (same.symm ▸ wx.2.1) zw.1
  have da : d ≠ a := fun same => noUW (same.symm ▸ xu.2.1) zw.2.1
  have ca : c ≠ a := fun same => noUW (same.symm ▸ xu.2.1) wx.1
  have bd : b ≠ d := fun same => noUW stepZU.2.1 (same.symm ▸ zw.2.1)
  have bc : b ≠ c := fun same => noUW stepZU.2.1 (same.symm ▸ wx.1)
  have ba : b ≠ a := fun same => noXZ (same.symm ▸ xu.1) stepZU.1
  exact ⟨a,b,xu,stepZU,halfFour_river_before_final free dc da ca bd bc ba oppXZ.symm oppUW.symm zw wx xu stepZU⟩

omit [Fintype V] in
private theorem halfFour_no_square_with_row_min {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 4) {u x w z : V} {p : I}
    (oppUW : u ≠ w) (oppXZ : x ≠ z)
    (ux : LinkedOpposite (fun _ h => free (h.trans (by decide))) u x)
    (xw : LinkedOpposite (fun _ h => free (h.trans (by decide))) x w)
    (wz : LinkedOpposite (fun _ h => free (h.trans (by decide))) w z)
    (zu : LinkedOpposite (fun _ h => free (h.trans (by decide))) z u)
    (orderUX : Before paths p u x) (orderXZ : Before paths p x z) : False := by
  let three : HalfBridgeFree (Before paths) 3 := fun _ h => free (h.trans (by decide))
  have orderUZ := listBefore_transitive orderUX orderXZ
  have uniqueUZ : ∀ q, Before paths q u z → q = p := by
    intro q step
    by_contra distinct
    exact no_parallel_list_steps free (by decide) distinct step orderUZ
  obtain ⟨frontUZ,backZU,opUZ⟩ := zu.symm
  have exactUZ := uniqueUZ frontUZ opUZ.2.1
  subst frontUZ
  have awayX : x ∉ paths backZU := fun member => opUZ.2.2.2 ⟨x,orderUX,orderXZ,member⟩
  have only {i : I} (uMem : u ∈ paths i) (xMem : x ∈ paths i) (zMem : z ∈ paths i) : i = p := by
    rcases listBefore_total uMem zMem (listBefore_ne orderUZ) with ordered | backwards
    · exact uniqueUZ i ordered
    · have eq : i = backZU := by
        by_contra different
        exact no_parallel_list_steps free (by decide) different backwards opUZ.2.2.1
      exact (awayX (eq ▸ xMem)).elim
  have onlyUW {i : I} (uMem : u ∈ paths i) (wMem : w ∈ paths i) : i = p :=
    only uMem (halfThree_middle_on_line three uMem wMem oppUW ux xw)
      (halfThree_middle_on_line three uMem wMem oppUW zu.symm wz.symm)
  have onlyXZ {i : I} (xMem : x ∈ paths i) (zMem : z ∈ paths i) : i = p :=
    only (halfThree_middle_on_line three xMem zMem oppXZ ux.symm zu.symm) xMem zMem
  obtain ⟨_,a,opUX⟩ := ux
  obtain ⟨_,c,opXW⟩ := xw
  obtain ⟨_,d,opWZ⟩ := wz
  let b := backZU
  have xu := opUX.2.2.1
  have wx := opXW.2.2.1
  have zw := opWZ.2.2.1
  have stepZU : Before paths b z u := opUZ.2.2.1
  have aNot : a ≠ p := by
    intro same
    exact lt_asymm orderUX.2.2 (same ▸ xu).2.2
  have bNot : b ≠ p := opUZ.1.symm
  have ab : a ≠ b := fun same => awayX (show x ∈ paths b from same ▸ xu.1)
  have priority := halfThree_river_before_final three bNot.symm aNot ab orderXZ stepZU xu
  have dc : d ≠ c := by
    intro same
    have both := onlyXZ (same.symm ▸ wx.2.1) zw.1
    have reversed := listBefore_transitive zw (same.symm ▸ wx)
    exact lt_asymm orderXZ.2.2 (both ▸ reversed).2.2
  have da : d ≠ a := fun same => aNot (onlyUW xu.2.1 (same ▸ zw.2.1))
  have ca : c ≠ a := fun same => aNot (onlyUW xu.2.1 (same ▸ wx.1))
  have bd : b ≠ d := fun same => bNot (onlyUW stepZU.2.1 (same.symm ▸ zw.2.1))
  have bc : b ≠ c := fun same => bNot (onlyUW stepZU.2.1 (same.symm ▸ wx.1))
  have impossible := halfFour_river_before_final free dc da ca bd bc ab.symm oppXZ.symm oppUW.symm zw wx xu stepZU
  exact (not_lt_of_ge impossible.le) priority


omit [Fintype V] in
/-- Four distinct vertices with successive opposite links would force a
half-bridge of size at most four. -/
theorem halfFour_oppositeLinkGraph_no_square {paths : I → List V} (free : HalfBridgeFree (Before paths) 4)
    {u x w z : V} (oppUW : u ≠ w) (oppXZ : x ≠ z)
    (ux : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj u x)
    (xw : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj x w)
    (wz : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj w z)
    (zu : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj z u) : False := by
  let three : HalfBridgeFree (Before paths) 3 := fun _ h => free (h.trans (by decide))
  by_cases supported : ∃ i, u ∈ paths i ∧ x ∈ paths i ∧ w ∈ paths i ∧ z ∈ paths i
  · obtain ⟨p,atU,atX,atW,atZ⟩ := supported
    let corners : Finset V := {u,x,w,z}
    obtain ⟨first,onCorners,least⟩ := Finset.exists_min_image corners (paths p).idxOf ⟨u,by simp [corners]⟩
    have contains (v : V) (on : v ∈ corners) : v ∈ paths p := by
      simp only [corners,Finset.mem_insert,Finset.mem_singleton] at on
      rcases on with rfl | rfl | rfl | rfl <;> assumption
    have starts {v : V} (on : v ∈ corners) (apart : first ≠ v) : Before paths p first v := by
      refine ⟨contains first onCorners,contains v on,(least v on).lt_of_ne ?_⟩
      exact fun same => apart ((List.idxOf_inj (contains first onCorners)).mp same)
    have fromMinimum {a b c d : V} (ac : a ≠ c) (bd : b ≠ d)
        (ab : LinkedOpposite three a b) (bc : LinkedOpposite three b c)
        (cd : LinkedOpposite three c d) (da : LinkedOpposite three d a)
        (firstB : Before paths p a b) (firstD : Before paths p a d) : False := by
      rcases listBefore_total firstB.2.1 firstD.2.1 bd with ordered | reversed
      · exact halfFour_no_square_with_row_min free ac bd ab bc cd da firstB ordered
      · exact halfFour_no_square_with_row_min free ac bd.symm da.symm cd.symm bc.symm ab.symm firstD reversed
    simp only [corners,Finset.mem_insert,Finset.mem_singleton] at onCorners
    rcases onCorners with rfl | rfl | rfl | rfl
    · exact fromMinimum oppUW oppXZ ux xw wz zu (starts (by simp [corners]) ux.ne)
        (starts (by simp [corners]) zu.ne.symm)
    · exact fromMinimum oppXZ oppUW.symm xw wz zu ux (starts (by simp [corners]) xw.ne)
        (starts (by simp [corners]) ux.ne.symm)
    · exact fromMinimum oppUW.symm oppXZ.symm wz zu ux xw (starts (by simp [corners]) wz.ne)
        (starts (by simp [corners]) xw.ne.symm)
    · exact fromMinimum oppXZ.symm oppUW zu ux xw wz (starts (by simp [corners]) zu.ne)
        (starts (by simp [corners]) wz.ne.symm)
  · have noFull (p : I) (atU : u ∈ paths p) (atX : x ∈ paths p) (atW : w ∈ paths p) (atZ : z ∈ paths p) : False :=
      supported ⟨p,atU,atX,atW,atZ⟩
    obtain ⟨a,b,xu,stepZU,forward⟩ := halfFour_square_return_order free oppUW oppXZ ux xw wz zu noFull
    obtain ⟨b',a',stepZU',xu',backward⟩ :=
      halfFour_square_return_order free oppUW oppXZ.symm zu.symm wz.symm xw.symm ux.symm
        (fun p atU atZ atW atX => noFull p atU atX atW atZ)
    have first : a' = a := by
      by_contra different
      exact no_parallel_list_steps free (by decide) different xu' xu
    have second : b' = b := by
      by_contra different
      exact no_parallel_list_steps free (by decide) different stepZU' stepZU
    rw [first,second] at backward
    exact (not_lt_of_ge backward.le) forward


omit [Fintype V] in
/-- Opposite-link cycles have length at least five under half-bridge
exclusion through size four. -/
theorem halfFour_oppositeLinkGraph_cycle_length_gt_four {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 4) {u : V}
    (cycle : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Walk u u)
    (simple : cycle.IsCycle) : 4 < cycle.length := by
  let length := cycle.length
  let v := cycle.getVert
  have large : 3 ≤ length := simple.three_le_length
  by_contra! short
  change length ≤ 4 at short
  have separate (i j : ℕ) (before : i < j) (inside : j < length) : v i ≠ v j := by
    intro equal
    have same := simple.getVert_injOn'
      (show i ≤ cycle.length-1 by change i ≤ length-1; omega)
      (show j ≤ cycle.length-1 by change j ≤ length-1; omega) equal
    exact before.ne same
  have closes : v length = v 0 := by simp [length,v,SimpleGraph.Walk.getVert_length]
  have edge (i : ℕ) (inside : i < length) :
      (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj (v i) (v (i+1)) :=
    cycle.adj_getVert_succ inside
  rcases (show length = 3 ∨ length = 4 by omega) with three | four
  · have last : v 3 = v 0 := three ▸ closes
    exact halfThree_oppositeLinkGraph_no_triangle (fun _ h => free (h.trans (by decide)))
      (edge 0 (by omega)) (edge 1 (by omega)) (last ▸ edge 2 (by omega))
  · have last : v 4 = v 0 := four ▸ closes
    exact halfFour_oppositeLinkGraph_no_square free (separate 0 2 (by decide) (by omega))
      (separate 1 3 (by decide) (by omega))
      (edge 0 (by omega)) (edge 1 (by omega)) (edge 2 (by omega)) (last ▸ edge 3 (by omega))


/-- Each ordered pair of distinct vertices accounts for at most one
ordered two-step walk, with equal endpoints counted by the incident edge. -/
theorem halfFour_oppositeLinkGraph_card_edgeSet_sq {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 4) :
    let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
    4*(Nat.card G.edgeSet)^2 ≤ (Fintype.card V)^2*(Fintype.card V-1) := by
  classical
  let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
  let n := Fintype.card V
  let walks : Finset (Σ _ : V, V × V) :=
    Finset.univ.sigma fun v => (G.neighborFinset v).product (G.neighborFinset v)
  let encode (entry : Σ _ : V, V × V) : V × V :=
    if entry.2.1 = entry.2.2 then (entry.1,entry.2.1) else entry.2
  have neighbor (v x y : V) (on : (⟨v,(x,y)⟩ : Σ _ : V, V × V) ∈ walks) : G.Adj v x ∧ G.Adj v y := by
    have both := (Finset.mem_sigma.mp on).2
    change (x,y) ∈ (G.neighborFinset v).product (G.neighborFinset v) at both
    obtain ⟨first,second⟩ := Finset.mem_product.mp both
    exact ⟨(G.mem_neighborFinset v x).mp first,(G.mem_neighborFinset v y).mp second⟩
  have into : Set.MapsTo encode walks (Finset.univ : Finset V).offDiag := by
    rintro ⟨v,x,y⟩ on
    obtain ⟨vx,vy⟩ := neighbor v x y on
    by_cases same : x = y
    · exact Finset.mem_offDiag.mpr ⟨by simp [encode,same],by simp [encode,same],by simpa [encode,same] using vx.ne⟩
    · exact Finset.mem_offDiag.mpr ⟨by simp [encode,same],by simp [encode,same],by simp [encode,same]⟩
  have noTriangle {v x y : V} (vx : G.Adj v x) (xy : G.Adj x y) (vy : G.Adj v y) : False :=
    halfThree_oppositeLinkGraph_no_triangle (fun _ h => free (h.trans (by decide))) vx xy vy.symm
  have unique : Set.InjOn encode walks := by
    rintro ⟨v,x,y⟩ onA ⟨w,a,b⟩ onB same
    obtain ⟨vx,vy⟩ := neighbor v x y onA
    obtain ⟨wa,wb⟩ := neighbor w a b onB
    by_cases first : x = y
    · subst y
      by_cases second : a = b
      · subst b
        obtain ⟨centers,ends⟩ := Prod.mk.inj (show (v,x) = (w,a) by simpa [encode] using same)
        subst w
        subst a
        rfl
      · obtain ⟨start,finish⟩ := Prod.mk.inj (show (v,x) = (a,b) by simpa [encode,second] using same)
        subst a
        subst b
        exact (noTriangle wa vx wb).elim
    · by_cases second : a = b
      · subst b
        obtain ⟨start,finish⟩ := Prod.mk.inj (show (x,y) = (w,a) by simpa [encode,first] using same)
        subst w
        subst a
        exact (noTriangle vx wa vy).elim
      · obtain ⟨starts,ends⟩ := Prod.mk.inj (show (x,y) = (a,b) by simpa [encode,first,second] using same)
        subst a
        subst b
        have centers : v = w := by
          by_contra different
          exact halfFour_oppositeLinkGraph_no_square free first different vx.symm vy wb.symm wa
        subst w
        rfl
  have size := Finset.card_le_card_of_injOn encode into unique
  have walkSize : walks.card = ∑ v, G.degree v^2 := by
    simp [walks,Finset.card_sigma,Finset.card_product,pow_two]
  have nonloopSize : ((Finset.univ : Finset V).offDiag).card = n*(n-1) := by
    rw [Finset.offDiag_card,Finset.card_univ,Nat.mul_sub_left_distrib,Nat.mul_one]
  have squares : (∑ v, G.degree v^2) ≤ n*(n-1) := walkSize.symm.trans_le (size.trans_eq nonloopSize)
  have cauchy : (∑ v, G.degree v)^2 ≤ n * ∑ v, G.degree v^2 := by
    have realBound : (∑ v, (G.degree v : ℝ))^2 ≤ (n:ℝ) * ∑ v, (G.degree v : ℝ)^2 := by
      simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,n] using
        Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V) (fun _ => (1:ℝ)) (fun v => (G.degree v : ℝ))
    exact_mod_cast realBound
  rw [G.sum_degrees_eq_twice_card_edges] at cauchy
  change 4*(Nat.card G.edgeSet)^2 ≤ n^2*(n-1)
  calc
    _ = (2*G.edgeFinset.card)^2 := by rw [Nat.card_eq_fintype_card,G.card_edgeSet]; ring
    _ ≤ n * ∑ v, G.degree v^2 := cauchy
    _ ≤ n*(n*(n-1)) := Nat.mul_le_mul_left n squares
    _ = _ := by ring


end OnlineReachabilityPreservers
