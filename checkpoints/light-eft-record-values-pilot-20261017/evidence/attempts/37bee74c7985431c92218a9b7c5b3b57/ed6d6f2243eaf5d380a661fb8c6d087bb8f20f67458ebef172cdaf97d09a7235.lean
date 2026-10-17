import LightEFTSpanners.StoredHostExecutable

namespace LightEFTSpanners.StoredHosts

theorem votes_eq_filter_length {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (u v : Fin n) (budget : ℚ) (rs : List (TypedInput n)) :
    votes Q E w u v budget rs=(rs.filter (decision Q E w u v budget)).length := by
  induction rs with
  | nil => rfl
  | cons R rs ih =>
    cases hd : decision Q E w u v budget R <;>
      simp [votes,hd] at * <;> omega

theorem votes_indexed {n : ℕ} {J : Type*} [DecidableEq J]
    (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (u v : Fin n) (budget : ℚ) (js : List J) (input : J → TypedInput n) (hj : js.Nodup) :
    votes Q E w u v budget (js.map input)=
      (js.toFinset.filter fun j => decision Q E w u v budget (input j)=true).card := by
  rw [votes_eq_filter_length]
  have hn := List.toFinset_card_of_nodup (hj.filter (fun j => decision Q E w u v budget (input j)))
  rw [List.toFinset_filter] at hn
  rw [hn]
  simp only [List.filter_map,Function.comp_def,List.length_map]
end LightEFTSpanners.StoredHosts
