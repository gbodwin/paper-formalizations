import DirectedFlowCutGap.StatefulRoundingCertificate

/-! The actual selected list and flag array denote the same cut. This is a
support-level statement for arbitrary stateful tape callbacks, including
correlated records and ledgers. -/
namespace DirectedFlowCutGap.StatefulOutputShape
noncomputable section
open RetainedGridState EncodedRoundingEntry EncodedRoundingRepetition
set_option backward.isDefEq.respectTransparency false
variable {n L : ℕ} {S : Type}

def Shape (o : Output n) : Prop :=
  o.vertices.Nodup ∧ o.vertices.toFinset = cutSet o.flags

theorem entry_shape
    (sample : (a : PairFlags n) → StateT S PMF (RetainedTapeInput.Tape L a × ℕ))
    (adjacency : PairFlags n) (hL : 0<L) (state : S)
    {out : Output n × S}
    (hout : out ∈ ((EncodedRoundingEntry.run sample adjacency hL).run state).support) :
    Shape out.1 := by
  change out ∈ (PMF.bind _ _).support at hout
  obtain ⟨d,hd,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  exact ⟨EncodedRoundingBounds.output_nodup _,EncodedRoundingBounds.output_set _⟩

theorem allRegime_shape
    (sample : (a : PairFlags n) → StateT S PMF (RetainedTapeInput.Tape L a × ℕ))
    (adjacency : PairFlags n) (hL : 0<L) (state : S)
    {out : Output n × S}
    (hout : out ∈ ((EncodedAllRegimeRounding.run sample adjacency hL).run state).support) :
    Shape out.1 := by
  simp only [EncodedAllRegimeRounding.run] at hout
  split_ifs at hout with hn hLn hHard
  · have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    constructor
    · exact List.nodup_nil
    · ext v; simp [EncodedAllRegimeRounding.emptyOutput,cutSet]
  · change out ∈ (PMF.bind _ _).support at hout
    obtain ⟨r,hr,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    exact entry_shape sample adjacency hL state (out := r)
      (by simpa only [StateT.run] using hr)
  · have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    constructor
    · exact List.nodup_finRange n
    · ext v; simp [EncodedAllRegimeRounding.universalOutput,cutSet]
  · have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    constructor
    · exact List.nodup_nil
    · ext v; simp [EncodedAllRegimeRounding.emptyOutput,cutSet]

theorem selected_shape
    (sample : (a : PairFlags n) → StateT S PMF (RetainedTapeInput.Tape L a × ℕ))
    (adjacency : PairFlags n) (hL : 0<L) (extra : ℕ) (state : S)
    {out : Result n × S}
    (hout : out ∈ ((EncodedRoundingRepetition.run sample adjacency hL extra).run state).support) :
    Shape out.1.selected :=
  StatefulRoundingCertificate.repeat_valid
    (EncodedAllRegimeRounding.run sample adjacency hL) extra Shape
    (fun s o ho => allRegime_shape sample adjacency hL s ho) state hout

end
end DirectedFlowCutGap.StatefulOutputShape
