import GreedyShortcuts.FiniteDistanceDP

/-! Materialized longest-path witness rows on a finite enabled graph.
The rows are actual vertex lists; an empty row is the no-start sentinel.
This component will support a constructive residual-path chain packing. -/
namespace GreedyShortcuts.FiniteLongestPathDP
open SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking

variable {α : Type*}

def longest : List (List α) → List α
  | [] => []
  | p::ps => let q := longest ps; if q.length≤p.length then p else q

theorem longest_mem_or_empty (ps : List (List α)) : longest ps=[] ∨ longest ps∈ps := by
  induction ps with
  | nil => exact Or.inl rfl
  | cons p ps ih =>
    simp only [longest]
    split_ifs with h
    · exact Or.inr (List.mem_cons_self ..)
    · exact ih.elim Or.inl (fun hm => Or.inr (List.mem_cons_of_mem _ hm))

theorem le_longest {ps : List (List α)} {p : List α} (hp : p∈ps) : p.length≤(longest ps).length := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [longest]
    have hc := List.mem_cons.mp hp
    split_ifs with h
    · rcases hc with rfl | hc
      · exact le_rfl
      · exact (ih hc).trans h
    · rcases hc with rfl | hc
      · omega
      · exact ih hc

variable {n : ℕ}

def rows (edge : Fin n → Fin n → Bool) (enabled : Fin n → Bool) :
    ℕ → Vector (List (Fin n)) n
  | 0 => Vector.ofFn (fun u => if enabled u then [u] else [])
  | k+1 =>
    let previous := rows edge enabled k
    Vector.ofFn (fun u => if enabled u then longest
      (previous[u] :: List.ofFn (fun v : Fin n =>
        if u≠v ∧ edge u v=true ∧ previous[v]≠[] then u::previous[v] else [])) else [])

def path (edge : Fin n → Fin n → Bool) (enabled : Fin n → Bool) (k : ℕ) (u : Fin n) :=
  (rows edge enabled k)[u]

@[simp] theorem path_zero (edge : Fin n → Fin n → Bool) (enabled : Fin n → Bool) (u : Fin n) :
    path edge enabled 0 u=if enabled u then [u] else [] := by simp [path,rows]

theorem path_succ (edge : Fin n → Fin n → Bool) (enabled : Fin n → Bool) (k : ℕ) (u : Fin n) :
    path edge enabled (k+1) u=if enabled u then longest
      (path edge enabled k u :: List.ofFn (fun v : Fin n =>
        if u≠v ∧ edge u v=true ∧ path edge enabled k v≠[] then u::path edge enabled k v else [])) else [] := by
  simp [path,rows]
  rfl

theorem path_sound (edge : Fin n → Fin n → Bool) (enabled : Fin n → Bool)
    (k : ℕ) (u : Fin n) (hp : path edge enabled k u≠[]) :
    ∃t,∃p : DWalk u t,Allowed (fun a b => edge a b=true) p ∧
      (∀v∈p.support,enabled v=true) ∧ p.support=path edge enabled k u ∧ p.length≤k := by
  induction k generalizing u with
  | zero =>
    have hu : enabled u=true := by
      by_contra hn
      simp only [path_zero,ite_eq_right hn] at hp
      exact hp rfl
    refine ⟨u,.nil,allowed_nil _ _,?_,?_,by simp⟩
    · simpa using hu
    · simp [hu]
  | succ k ih =>
    have hu : enabled u=true := by
      by_contra hn
      simp only [path_succ,ite_eq_right hn] at hp
      exact hp rfl
    rw [path_succ,ite_eq_left hu] at hp ⊢
    let ps := path edge enabled k u :: List.ofFn (fun v : Fin n =>
      if u≠v ∧ edge u v=true ∧ path edge enabled k v≠[] then u::path edge enabled k v else [])
    have hm : longest ps∈ps := (longest_mem_or_empty ps).resolve_left hp
    rcases List.mem_cons.mp hm with hold | hnew
    · obtain ⟨t,p,hp,hena,he,hlen⟩ := ih u (by intro hz;exact hp (hold.trans hz))
      exact ⟨t,p,hp,hena,he.trans hold.symm,by omega⟩
    · obtain ⟨v,hv⟩ := List.mem_ofFn.mp hnew
      by_cases hedge : u≠v ∧ edge u v=true ∧ path edge enabled k v≠[]
      · simp only [ite_eq_left hedge] at hv
        obtain ⟨t,p,hp,hena,he,hlen⟩ := ih v hedge.2.2
        let ha : (⊤ : SimpleGraph (Fin n)).Adj u v := by simpa using hedge.1
        refine ⟨t,.cons ha p,(allowed_cons _ ha p).mpr ⟨hedge.2.1,hp⟩,?_,?_,by simp;omega⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hu
          · exact hena z hz
        · simpa only [Walk.support_cons,he] using hv
      · simp only [ite_eq_right hedge] at hv
        exact (hp hv.symm).elim

theorem path_longest (edge : Fin n → Fin n → Bool) (enabled : Fin n → Bool)
    (k : ℕ) {u t : Fin n} (p : DWalk u t) (hp : Allowed (fun a b => edge a b=true) p)
    (hen : ∀v∈p.support,enabled v=true) (hlen : p.length≤k) :
    p.length+1≤(path edge enabled k u).length := by
  induction k generalizing u with
  | zero =>
    cases p with
    | nil =>
      have hu := hen t (by simp)
      simp [hu]
    | cons ha p => simp at hlen
  | succ k ih =>
    have hu := hen u p.start_mem_support
    rw [path_succ,ite_eq_left hu]
    cases p with
    | nil =>
      exact (ih .nil (allowed_nil _ _) hen (by simp)).trans (le_longest (List.mem_cons_self ..))
    | @cons u v t ha p =>
      have ht := (allowed_cons _ ha p).mp hp
      have hena : ∀z∈p.support,enabled z=true := fun z hz => hen z (List.mem_cons_of_mem _ hz)
      have hi := ih p ht.2 hena (by simpa using Nat.le_of_succ_le_succ hlen)
      have hn : path edge enabled k v≠[] := by
        intro hz
        rw [hz] at hi
        simp only [List.length_nil] at hi
        omega
      have hmem : u::path edge enabled k v∈path edge enabled k u :: List.ofFn
          (fun z : Fin n => if u≠z ∧ edge u z=true ∧ path edge enabled k z≠[]
            then u::path edge enabled k z else []) :=
        List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨v,by simp [ha.ne,ht.1,hn]⟩)
      have hc := le_longest hmem
      simp only [Walk.length_cons,List.length_cons] at *
      omega

end GreedyShortcuts.FiniteLongestPathDP
