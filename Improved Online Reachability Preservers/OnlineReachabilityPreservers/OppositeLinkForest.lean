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
def oppositeLinkGraph (paths : I → List V) (three : BridgeFree (Before paths) 3) : SimpleGraph V where
  Adj x y := ∃ a b, OppositeNeighbors paths a b x y
  symm := ⟨by
    rintro _ _ ⟨a,b,h⟩
    exact ⟨b,a,oppositeNeighbors_swap three h⟩⟩
  loopless := ⟨by
    rintro _ ⟨_,_,h⟩
    exact listBefore_ne h.2.1 rfl⟩

omit [LinearOrder I] in
private theorem listBefore_transitive {paths : I → List V} {a : I} {x y z : V}
    (xy : Before paths a x y) (yz : Before paths a y z) : Before paths a x z :=
  ⟨xy.1,yz.2.1,xy.2.2.trans yz.2.2⟩

private theorem opposite_forward_unique {paths : I → List V} (three : BridgeFree (Before paths) 3)
    {x y : V} {a b c d : I} (ab : OppositeNeighbors paths a b x y) (cd : OppositeNeighbors paths c d x y) :
    a = c ∧ b = d := by
  constructor <;> by_contra different
  · exact no_parallel_list_steps three.halfFree (by decide) different ab.2.1 cd.2.1
  · exact no_parallel_list_steps three.halfFree (by decide) different ab.2.2.1 cd.2.2.1

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
    (three : BridgeFree (Before paths) 3) (simple : ∀ i, (paths i).Nodup) {i : Fin p} {v : V}
    (present : v ∈ paths i) (missing : v ∉ removeOppositeIntersections paths i) :
    Nonempty (OppositePruneCharge paths i v) := by
  rw [removeOppositeIntersections_mem] at missing
  push Not at missing
  obtain ⟨j,ji,u,forward,backward⟩ := missing present
  have connected := oppositeNeighbors_connect three ji.ne' forward (removeOppositeIntersections_before simple backward)
  have initial {x y : V} (h : Relation.TransGen (OppositeNeighbors paths i j) x y) :
      ∃ z, OppositeNeighbors paths i j x z := by
    induction h with
    | single h => exact ⟨_,h⟩
    | tail _ _ ih => exact ih
  obtain ⟨w,adjacent⟩ := initial connected
  exact ⟨⟨j,ji,w,adjacent⟩⟩

/-- Each removed incidence charges a distinct opposite link in the original family. -/
theorem removeOppositeIntersections_mass_with_link_count {p : ℕ} {paths : Fin p → List V}
    (three : BridgeFree (Before paths) 3) (simple : ∀ i, (paths i).Nodup) :
    (∑ i, (paths i).length) ≤ (∑ i, (removeOppositeIntersections paths i).length) +
      Nat.card (oppositeLinkGraph paths three).edgeSet := by
  classical
  let retained := removeOppositeIntersections paths
  let omitted := (univ : Finset (Fin p × V)).filter fun x => x.2 ∈ paths x.1 ∧ x.2 ∉ retained x.1
  let G := oppositeLinkGraph paths three
  let witness (x : omitted) := Classical.choice (oppositePruneCharge_exists three simple
    (mem_filter.mp x.property).2.1 (mem_filter.mp x.property).2.2)
  let charge (x : omitted) : G.edgeSet :=
    ⟨s(x.val.2,(witness x).next),G.mem_edgeSet.mpr ⟨x.val.1,(witness x).earlier,(witness x).link⟩⟩
  have injective : Function.Injective charge := by
    intro x y same
    have endpoints := Sym2.eq_iff.mp (congrArg Subtype.val same)
    rcases endpoints with ⟨sameStart,sameEnd⟩ | ⟨swappedStart,swappedEnd⟩
    · have aligned : OppositeNeighbors paths y.val.1 (witness y).earlier x.val.2 (witness x).next :=
        (congrArg₂ (OppositeNeighbors paths y.val.1 (witness y).earlier) sameStart sameEnd).mpr (witness y).link
      exact Subtype.ext (Prod.ext (opposite_forward_unique three (witness x).link aligned).1 sameStart)
    · have reversed : OppositeNeighbors paths (witness y).earlier y.val.1 x.val.2 (witness x).next :=
        (congrArg₂ (OppositeNeighbors paths (witness y).earlier y.val.1) swappedStart swappedEnd).mpr
          (oppositeNeighbors_swap three (witness y).link)
      have owners := opposite_forward_unique three (witness x).link reversed
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

/-- For full bridge exclusion at every size, pruning to unique intersections
discards at most one less than the number of vertices. -/
theorem removeOppositeIntersections_mass_of_fullFree {p : ℕ} {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) (full : ∀ k, IsEmpty (Bridge (Before paths) k)) :
    (∑ i, (paths i).length) ≤ (∑ i, (removeOppositeIntersections paths i).length) + (Fintype.card V - 1) := by
  have three : BridgeFree (Before paths) 3 := fun {k} _ => full k
  exact (removeOppositeIntersections_mass_with_link_count three simple).trans
    (Nat.add_le_add_left (oppositeLinkGraph_card_edgeSet three full) _)

end OnlineReachabilityPreservers
