import Analysis.MeasureTheory.Section_1_2_1

/-!
# Introduction to Measure Theory, Section 1.2.2: Lebesgue measurability

A companion to (the introduction to) Section 1.2.2 of the book "An introduction to Measure Theory".

-/

/-- Lemma 1.2.13(i) (Every open set is Lebesgue measurable). -/
theorem IsOpen.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsOpen E) : LebesgueMeasurable E := by
  -- Strategy: For any ε > 0, choose U = E itself
  -- Since E is already open, U \ E = E \ E = ∅, and m*(∅) = 0 ≤ ε
  intro ε hε
  -- Witness: U = E
  use E
  constructor
  · -- E is open (given)
    exact hE
  constructor
  · -- E ⊆ E (reflexivity)
    rfl
  · -- Show m*(E \ E) ≤ ε
    have h_empty : E \ E = ∅ := Set.diff_self
    rw [h_empty]
    have h_zero : Lebesgue_outer_measure (∅ : Set (EuclideanSpace' d)) = 0 :=
      Lebesgue_outer_measure.of_empty d
    rw [h_zero]
    exact le_of_lt hε

/-- Helper: For a finset of pairwise almost disjoint dyadic boxes, the outer measure of their
    union equals the sum of their volumes. -/
private lemma Lebesgue_outer_measure.sum_of_almost_disjoint_finset {d : ℕ} (_hd_pos : 0 < d)
    {t : Finset ℕ} {Q : ℕ → Box d} (_hQ_dyadic : ∀ i, (Q i).IsDyadic)
    (hQ : Pairwise (Function.onFun AlmostDisjoint Q)) :
    Lebesgue_outer_measure (⋃ i ∈ t, (Q i).toSet) = ∑ i ∈ t, ((Q i).volume : EReal) := by
  -- Direct proof using elementary set theory (avoids flawed union_of_separated approach)
  -- Convert to Fin (t.card) indexed boxes via Finset.equivFin
  let equiv := t.equivFin
  let B' : Fin t.card → Box d := fun i => Q (equiv.symm i).val
  -- Show the biUnion equals the iUnion over Fin t.card
  have h_eq : (⋃ i ∈ t, (Q i).toSet) = ⋃ (i : Fin t.card), (B' i).toSet := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_iUnion, B']
    constructor
    · intro ⟨i, hi, hx⟩
      exact ⟨equiv ⟨i, hi⟩, by simp [hx]⟩
    · intro ⟨i, hx⟩
      exact ⟨(equiv.symm i).val, (equiv.symm i).property, hx⟩
  rw [h_eq]
  -- The finite union is elementary
  have hElem : IsElementary (⋃ (i : Fin t.card), (B' i).toSet) :=
    IsElementary.iUnion_boxes B'
  -- Almost-disjointness for Fin-indexed boxes
  have hB'_disj : Pairwise (Function.onFun AlmostDisjoint B') := by
    intro i j h_ne
    simp only [Function.onFun, B']
    apply hQ
    intro h_eq
    have heq : equiv.symm i = equiv.symm j := Subtype.ext h_eq
    exact h_ne (equiv.symm.injective heq)
  -- Apply IsElementary.almost_disjoint: measure = ∑ volumes
  have h_measure := IsElementary.almost_disjoint hElem B' rfl hB'_disj
  -- Convert measure to outer measure
  have h_outer := Lebesgue_outer_measure.elementary _ hElem
  -- Sum conversion: ∑ i : Fin t.card, (B' i).volume = ∑ i ∈ t, (Q i).volume
  have h_sum_eq : ∑ i : Fin t.card, (B' i).volume = ∑ i ∈ t, (Q i).volume := by
    conv_rhs => rw [← Finset.sum_attach]
    refine Finset.sum_equiv equiv.symm ?_ ?_
    · intro i; simp [Finset.mem_univ, Finset.mem_attach]
    · intro i _; simp only [B']
  rw [h_outer, h_measure, h_sum_eq]
  -- Now need: ↑(∑ i ∈ t, (Q i).volume) = ∑ i ∈ t, ↑(Q i).volume
  exact EReal.coe_finset_sum (fun i _ => Box.volume_nonneg _)


/-- Helper: Bounded closed sets are measurable (Lemma 1.2.13(ii) for bounded case).
    For bounded closed E (compact by Heine-Borel), show that for any ε > 0,
    there exists open U ⊇ E with m*(U \ E) ≤ ε. -/
private lemma IsClosed.measurable_of_bounded {d:ℕ} {E: Set (EuclideanSpace' d)}
    (hE: IsClosed E) (hE_bounded : Bornology.IsBounded E) : LebesgueMeasurable E := by
  intro ε hε
  -- Empty case
  by_cases hE_empty : E = ∅
  · use ∅
    refine ⟨isOpen_empty, ?_, ?_⟩
    · rw [hE_empty]
    · simp [Lebesgue_outer_measure.of_empty]; exact le_of_lt hε
  -- Non-empty bounded closed E is compact
  have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
  -- Get open U with m*(U) ≤ m*(E) + ε/2
  have hε_half_pos : (0 : EReal) < ε / 2 := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top =>
      show (0 : EReal) < ⊤ / 2
      -- ⊤ / 2 = ⊤ in EReal since 2 > 0 and 2 ≠ ⊤
      have : (⊤ : EReal) / 2 = ⊤ := by
        have h2_pos : (0 : EReal) < 2 := by norm_num
        have h2_ne_top : (2 : EReal) ≠ ⊤ := by
          intro h
          have : (2 : EReal) = (2 : ℝ) := rfl
          rw [this] at h
          exact EReal.coe_ne_top 2 h
        exact EReal.top_div_of_pos_ne_top h2_pos h2_ne_top
      rw [this]
      exact EReal.zero_lt_top
    | coe r =>
      have hr_pos : 0 < r := EReal.coe_pos.mp hε
      rw [show (2 : EReal) = (2 : ℝ) from rfl, ← EReal.coe_div r 2]
      exact EReal.coe_pos.mpr (half_pos hr_pos)
  obtain ⟨U, hU_open, hE_sub_U, hU_meas⟩ := Lebesgue_outer_measure.exists_open_superset_measure_le E (ε/2) hε_half_pos
  use U
  refine ⟨hU_open, hE_sub_U, ?_⟩
  -- Key: show m*(U \ E) ≤ ε
  -- U \ E is open
  have h_diff_open : IsOpen (U \ E) := hU_open.sdiff hE
  -- Handle d = 0 separately
  by_cases hd : d = 0
  · -- In dimension 0, EuclideanSpace' 0 = Fin 0 → ℝ is a subsingleton
    -- Since E is nonempty and E ⊆ U, and U is nonempty (contains E), we have E = U
    -- Therefore U \ E = ∅, so m*(U \ E) = 0 ≤ ε
    subst hd
    have : Subsingleton (EuclideanSpace' 0) := by
      unfold EuclideanSpace'
      infer_instance
    have hU_nonempty : U.Nonempty := hE_nonempty.mono hE_sub_U
    have hEU_eq : E = U := by
      apply Set.Subset.antisymm hE_sub_U
      intro x hx
      obtain ⟨y, hy⟩ := hE_nonempty
      have hxy : x = y := Subsingleton.elim x y
      rw [hxy]
      exact hy
    rw [hEU_eq, Set.diff_self, Lebesgue_outer_measure.of_empty]
    exact le_of_lt hε
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- If U \ E is empty, trivial
  by_cases h_diff_empty : U \ E = ∅
  · rw [h_diff_empty, Lebesgue_outer_measure.of_empty]; exact le_of_lt hε
  -- Main argument: U \ E is nonempty open, decompose into cubes
  have h_diff_nonempty : (U \ E).Nonempty := Set.nonempty_iff_ne_empty.mpr h_diff_empty
  obtain ⟨Q, hQ_union, hQ_dyadic, hQ_pairwise⟩ := h_diff_open.eq_union_boxes hd_pos (U \ E) h_diff_nonempty
  rw [hQ_union]
  -- m*(⋃ Q_n) = ∑ |Q_n|
  have h_measure_eq : Lebesgue_outer_measure (⋃ n, (Q n).toSet) = ∑' n, (Q n).volume.toEReal := by
    have h1 := Lebesgue_outer_measure.union_of_almost_disjoint hQ_pairwise
    simp_rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _),
             IsElementary.measure_of_box] at h1
    exact h1
  rw [h_measure_eq]
  -- Use compactness: E is compact (closed + bounded)
  -- EuclideanSpace ℝ (Fin d) is finite-dimensional, hence ProperSpace
  -- By Heine-Borel: closed + bounded = compact in proper spaces
  have hE_compact : IsCompact E := Metric.isCompact_of_isClosed_isBounded hE hE_bounded
  calc ∑' n, (Q n).volume.toEReal
      = Lebesgue_outer_measure (⋃ n, (Q n).toSet) := h_measure_eq.symm
    _ = Lebesgue_outer_measure (U \ E) := by rw [← hQ_union]
    _ ≤ ε / 2 := by
        -- Key: E is compact, so m*(E) is finite (not ⊥ or ⊤)
        have hE_finite : Lebesgue_outer_measure E ≠ ⊤ :=
          Lebesgue_outer_measure.finite_of_compact hE_compact
        have hE_ne_bot : Lebesgue_outer_measure E ≠ ⊥ := by
          have h_nonneg : 0 ≤ Lebesgue_outer_measure E := Lebesgue_outer_measure.nonneg E
          intro h_eq
          rw [h_eq] at h_nonneg
          -- 0 ≤ ⊥ is false in EReal
          exact not_le.mpr EReal.bot_lt_zero h_nonneg

        -- For each finite N, show ∑_{i < N} vol(Q_i) ≤ ε/2
        have h_finite_sum_bound : ∀ (t : Finset ℕ),
            ∑ i ∈ t, ((Q i).volume : EReal) ≤ ε / 2 := by
          intro t
          -- Handle empty finset case
          by_cases ht_empty : t = ∅
          · rw [ht_empty]
            simp
            exact le_of_lt hε_half_pos
          -- Now t is nonempty
          -- Let F_t = ⋃_{i ∈ t} Q_i
          let F_t := ⋃ i ∈ t, (Q i).toSet
          -- F_t is compact (finite union of compact boxes)
          have hF_compact : IsCompact F_t := by
            -- Each box is compact (product of compact intervals)
            have hQ_compact : ∀ i ∈ t, IsCompact ((Q i).toSet) := by
              intro i _
              exact Box.isCompact (Q i) (Box.IsDyadic.all_sides_Icc (hQ_dyadic i))
            -- Finite union of compact sets is compact
            exact Finset.isCompact_biUnion t hQ_compact
          -- E ∩ F_t = ∅ (since F_t ⊆ U\E)
          have hE_F_disj : E ∩ F_t = ∅ := by
            ext x
            simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, F_t]
            intro hxE
            simp only [Set.mem_iUnion, not_exists]
            intro i hi
            -- x ∈ E and x ∈ Q_i, but Q_i ⊆ U\E
            have hQ_sub : (Q i).toSet ⊆ U \ E := by
              have : (Q i).toSet ⊆ ⋃ n, (Q n).toSet := by
                intro y hy
                exact Set.mem_iUnion_of_mem i hy
              rw [← hQ_union] at this
              exact this
            intro hxi
            exact (hQ_sub hxi).2 hxE
          -- By compactness: set_dist E F_t > 0 (t is nonempty, so F_t is nonempty)
          have h_sep : set_dist E F_t > 0 :=
            dist_of_disj_compact_pos E F_t hE_compact hF_compact hE_F_disj
          -- By separation: m*(E ∪ F_t) = m*(E) + m*(F_t)
          have h_add : Lebesgue_outer_measure (E ∪ F_t) =
                       Lebesgue_outer_measure E + Lebesgue_outer_measure F_t :=
            Lebesgue_outer_measure.union_of_separated hd_pos h_sep
          -- E ∪ F_t ⊆ U
          have h_sub : E ∪ F_t ⊆ U := by
            intro x hx
            cases hx with
            | inl hxE => exact hE_sub_U hxE
            | inr hxF =>
              -- F_t ⊆ ⋃ n, Q_n = U\E ⊆ U
              have : F_t ⊆ ⋃ n, (Q n).toSet := by
                intro y hy
                simp [F_t] at hy
                obtain ⟨i, hi, hyi⟩ := hy
                exact Set.mem_iUnion_of_mem i hyi
              have hF_sub : (⋃ n, (Q n).toSet) ⊆ U := by
                rw [← hQ_union]
                exact Set.diff_subset
              exact hF_sub (this hxF)
          -- So m*(E ∪ F_t) ≤ m*(U) ≤ m*(E) + ε/2
          have h_bound : Lebesgue_outer_measure (E ∪ F_t) ≤ Lebesgue_outer_measure E + ε / 2 := by
            calc Lebesgue_outer_measure (E ∪ F_t)
                ≤ Lebesgue_outer_measure U := Lebesgue_outer_measure.mono h_sub
              _ ≤ Lebesgue_outer_measure E + ε / 2 := hU_meas
          -- Therefore m*(E) + m*(F_t) ≤ m*(E) + ε/2, so m*(F_t) ≤ ε/2
          rw [h_add] at h_bound
          -- Cancellation: m*(E) + m*(F_t) ≤ m*(E) + ε/2 implies m*(F_t) ≤ ε/2
          have h_F_bound : Lebesgue_outer_measure F_t ≤ ε / 2 := by
            -- Use EReal.sub_le_of_le_add': if a ≤ b + c then a - b ≤ c
            have h1 : Lebesgue_outer_measure E + Lebesgue_outer_measure F_t - Lebesgue_outer_measure E ≤ ε / 2 :=
              EReal.sub_le_of_le_add' h_bound
            -- Since m*(E) is finite (not ⊥ or ⊤), we have (m*(E) + m*(F_t)) - m*(E) = m*(F_t)
            -- Case analysis on m*(E) being a real number
            have h_cancel : Lebesgue_outer_measure E + Lebesgue_outer_measure F_t - Lebesgue_outer_measure E = Lebesgue_outer_measure F_t := by
              cases h : Lebesgue_outer_measure E with
              | bot => exact absurd h hE_ne_bot
              | top => exact absurd h hE_finite
              | coe r =>
                -- m*(E) = r (a real number), so the goal is already r + m*(F_t) - r = m*(F_t)
                exact EReal.add_sub_cancel_left
            rw [h_cancel] at h1
            exact h1
          -- Finally: m*(F_t) = ∑_{i ∈ t} vol(Q_i) by almost disjoint union
          calc ∑ i ∈ t, ((Q i).volume : EReal)
              = Lebesgue_outer_measure F_t := by
                symm
                exact Lebesgue_outer_measure.sum_of_almost_disjoint_finset hd_pos hQ_dyadic hQ_pairwise
            _ ≤ ε / 2 := h_F_bound

        -- Now: ∑' n, vol(Q_n) ≤ ε/2 by supremum of finite sums
        have hvol_nonneg : ∀ n, 0 ≤ (Q n).volume := fun n => Box.volume_nonneg _
        have h_range_bound : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((Q i).volume : EReal) ≤ ε / 2 :=
          fun N => h_finite_sum_bound (Finset.range N)
        have h_tsum_bound : ∑' n, ((Q n).volume : EReal) ≤ ε / 2 :=
          EReal.tsum_le_of_sum_range_le hvol_nonneg h_range_bound
        -- Convert back using h_measure_eq
        calc Lebesgue_outer_measure (U \ E)
            = Lebesgue_outer_measure (⋃ n, (Q n).toSet) := by rw [hQ_union]
          _ = ∑' n, ((Q n).volume : EReal) := h_measure_eq
          _ ≤ ε / 2 := h_tsum_bound
    _ ≤ ε := by
        cases ε with
        | bot => exact absurd hε (not_lt.mpr bot_le)
        | top => simp
        | coe r =>
          have hr_pos : 0 < r := EReal.coe_pos.mp hε
          rw [show (2 : EReal) = (2 : ℝ) from rfl, ← EReal.coe_div r 2]
          exact EReal.coe_le_coe_iff.mpr (half_le_self (le_of_lt hr_pos))

/-- Lemma 1.2.13(ii) (Every closed set is Lebesgue measurable). -/
theorem IsClosed.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsClosed E) : LebesgueMeasurable E := by
  -- Write E = ⋃_{n=0}^∞ (E ∩ closedBall 0 n)
  have h_union : E = ⋃ n : ℕ, E ∩ Metric.closedBall 0 n := (Metric.iUnion_inter_closedBall_nat E 0).symm
  rw [h_union]
  -- Each E ∩ closedBall 0 n is closed (intersection of closed sets) and bounded
  have h_closed : ∀ n : ℕ, IsClosed (E ∩ Metric.closedBall 0 n) :=
    fun n => hE.inter Metric.isClosed_closedBall
  have h_bounded : ∀ n : ℕ, Bornology.IsBounded (E ∩ Metric.closedBall 0 n) :=
    fun n => Metric.isBounded_closedBall.subset Set.inter_subset_right
  -- Apply IsClosed.measurable_of_bounded to each piece
  have h_meas : ∀ n : ℕ, LebesgueMeasurable (E ∩ Metric.closedBall 0 n) :=
    fun n => IsClosed.measurable_of_bounded (h_closed n) (h_bounded n)
  -- Inline countable union proof (Lemma 1.2.13(vi) is defined later in this file)
  intro ε hε
  -- Convert EReal ε to a real number ε' with 0 < ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- For each n, get U_n open with (E ∩ closedBall 0 n) ⊆ U_n and m*(U_n \ (E ∩ closedBall 0 n)) ≤ ε'/2^(n+1)
  have hδ_pos : ∀ n, (0:EReal) < ε' / 2^(n+1) := fun n => by
    apply EReal.div_pos (EReal.coe_pos.mpr hε'_pos)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_pos.mpr (by positivity)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_ne_top ((2:ℝ)^(n+1))
  choose U hU_open hE_sub hU_diff using fun n => h_meas n (ε' / 2^(n+1)) (hδ_pos n)
  -- The open set is ⋃ n, U n
  use ⋃ n, U n
  constructor
  · exact isOpen_iUnion hU_open
  constructor
  · apply Set.iUnion_mono; intro n; exact hE_sub n
  · -- m*((⋃ n, U n) \ (⋃ n, E ∩ closedBall 0 n)) ≤ ε
    have h_diff_subset : (⋃ (n : ℕ), U n) \ (⋃ (n : ℕ), E ∩ Metric.closedBall 0 ↑n) ⊆ ⋃ (n : ℕ), (U n \ (E ∩ Metric.closedBall 0 ↑n)) := by
      intro x ⟨hx_in_U, hx_not_in_E⟩
      simp only [Set.mem_iUnion] at hx_in_U hx_not_in_E ⊢
      obtain ⟨k, hxk⟩ := hx_in_U
      use k
      constructor
      · exact hxk
      · intro hx_Ek; exact hx_not_in_E ⟨k, hx_Ek⟩
    calc Lebesgue_outer_measure ((⋃ (n : ℕ), U n) \ (⋃ (n : ℕ), E ∩ Metric.closedBall 0 ↑n))
        ≤ Lebesgue_outer_measure (⋃ (n : ℕ), (U n \ (E ∩ Metric.closedBall 0 ↑n))) :=
          Lebesgue_outer_measure.mono h_diff_subset
      _ ≤ ∑' (n : ℕ), Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n)) :=
          Lebesgue_outer_measure.union_le _
      _ ≤ ∑' (n : ℕ), ((ε' / 2^(n+1) : ℝ) : EReal) := by
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_f_nonneg : ∀ n, 0 ≤ Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n)) :=
            fun n => Lebesgue_outer_measure.nonneg _
          have h_le_coe : ∀ n, Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n)) ≤ ((ε' / 2^(n+1) : ℝ) : EReal) := by
            intro n
            calc Lebesgue_outer_measure (U n \ (E ∩ Metric.closedBall 0 ↑n))
                ≤ (↑ε' : EReal) / 2^(n+1) := hU_diff n
              _ = ↑(ε' / 2^(n+1)) := by
                  rw [EReal.coe_div]
                  congr 1
                  exact Eq.symm (EReal.coe_pow 2 (n + 1))
          exact EReal.tsum_le_coe_tsum_of_forall_le h_f_nonneg h_nonneg h_summable h_le_coe
      _ = ε' := by
          have h_sum : ∑' n : ℕ, (ε' : ℝ) / 2^(n+1) = ε' := tsum_geometric_eps ε' hε'_pos
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          rw [← EReal.coe_tsum_of_nonneg h_nonneg h_summable, h_sum]
      _ ≤ ε := hε'_le

abbrev IsNull {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := Lebesgue_outer_measure E = 0

/-- Lemma 1.2.13(iii) (Every null set is Lebesgue measurable).-/
theorem IsNull.measurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsNull E) : LebesgueMeasurable E := by
  -- Strategy: For any ε > 0, since m*(E) = 0, get a box cover with total volume < ε,
  -- then inflate boxes to open sets. The union is open and contains E.
  intro ε hε
  -- Handle dimension 0 separately
  by_cases hd : d = 0
  · -- In dimension 0, EuclideanSpace' 0 is a single point.
    -- Since m*(E) = 0 and m*(univ) = 1 for nonempty sets in d=0, E must be empty.
    -- Use U = E = ∅, which is open, E ⊆ U, and U \ E = ∅ has measure 0.
    subst hd
    -- In d=0: m*(E) = if E.Nonempty then 1 else 0
    -- hE : IsNull E is an abbrev for Lebesgue_outer_measure E = 0
    have hE' : Lebesgue_outer_measure E = 0 := hE
    rw [Lebesgue_outer_measure_of_dim_zero] at hE'
    simp only [ite_eq_right_iff, one_ne_zero] at hE'
    -- hE' : E.Nonempty → False, i.e., E = ∅
    have hE_empty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE'
    use ∅
    refine ⟨isOpen_empty, ?_, ?_⟩
    · rw [hE_empty]
    · simp only [Set.empty_diff]
      rw [Lebesgue_outer_measure.of_empty]
      exact le_of_lt hε
  -- Now d > 0
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- m*(E) = 0 implies m*(E) ≠ ⊤
  have h_finite : Lebesgue_outer_measure E ≠ ⊤ := by rw [hE]; exact EReal.zero_ne_top
  -- Convert EReal ε to a real number
  -- Since ε > 0, get a real ε' with 0 < ε' and ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- Get an ε'/2-close box cover
  have hε2_pos : 0 < ε' / 2 := by linarith
  obtain ⟨S, hS_cover, hS_vol⟩ := Lebesgue_outer_measure.exists_cover_close hd_pos E (ε' / 2) hε2_pos h_finite
  -- hS_vol : ∑' n, (S n).volume.toEReal ≤ m*(E) + ε'/2 = 0 + ε'/2 = ε'/2
  rw [hE] at hS_vol
  simp only [zero_add] at hS_vol
  -- Inflate each box to get an open set containing it
  -- Use δₙ = ε' / 2^(n+2) so that ∑ δₙ = ε'/2
  let δ : ℕ → ℝ := fun n => ε' / 2 / 2 ^ (n + 1)
  have hδ_pos : ∀ n, 0 < δ n := fun n => by simp only [δ]; positivity
  -- Get inflated boxes using Box.inflate
  have h_inflate := fun n => Box.inflate (S n) (δ n) (hδ_pos n)
  choose U' hU'_subset hU'_open hU'_vol using h_inflate
  -- Define U as union of interiors of inflated boxes
  let U := ⋃ n, interior (U' n).toSet
  use U
  constructor
  · -- U is open (union of open sets)
    exact isOpen_iUnion (fun n => isOpen_interior)
  constructor
  · -- E ⊆ U
    calc E ⊆ ⋃ n, (S n).toSet := hS_cover
         _ ⊆ ⋃ n, interior (U' n).toSet := Set.iUnion_mono (fun n => hU'_subset n)
  · -- m*(U \ E) ≤ ε
    -- Key bounds: m*(U \ E) ≤ m*(U) ≤ ∑ |U' n|ᵥ ≤ ∑ (|S n|ᵥ + δ n) ≤ ε'/2 + ε'/2 = ε' ≤ ε
    have h1 : Lebesgue_outer_measure (U \ E) ≤ Lebesgue_outer_measure U :=
      Lebesgue_outer_measure.mono Set.diff_subset
    have h2 : Lebesgue_outer_measure U ≤ ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) := by
      have : U = ⋃ n, interior (U' n).toSet := rfl
      rw [this]
      exact Lebesgue_outer_measure.union_le _
    -- Each interior has measure ≤ box volume
    have h3 : ∀ n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ (U' n).volume.toEReal := by
      intro n
      calc Lebesgue_outer_measure (interior (U' n).toSet)
          ≤ Lebesgue_outer_measure (U' n).toSet := Lebesgue_outer_measure.mono interior_subset
        _ = (IsElementary.box (U' n)).measure.toEReal := by
            rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _)]
        _ = (U' n).volume.toEReal := by rw [IsElementary.measure_of_box]
    -- Each inflated box volume ≤ original + δ
    have h4 : ∀ n, (U' n).volume.toEReal ≤ ((S n).volume + δ n).toEReal := by
      intro n
      exact EReal.coe_le_coe_iff.mpr (hU'_vol n)
    -- The sum splits: ∑ (|S n|ᵥ + δ n) = ∑ |S n|ᵥ + ∑ δ n ≤ ε'/2 + ε'/2 = ε' ≤ ε
    have hδ_sum : ∑' n, (δ n : ℝ) = ε' / 2 := by
      simp only [δ, div_div]
      have h := tsum_geometric_two' (ε' / 2)
      convert h using 1
      congr 1
      ext n
      ring_nf
    -- Combine the bounds to show m*(U \ E) ≤ ε' ≤ ε
    -- Strategy:
    -- m*(U\E) ≤ m*(U) ≤ ∑ m*(interior U'_n) ≤ ∑ vol(U'_n) ≤ ∑ (vol(S_n) + δ_n)
    --         ≤ ∑ vol(S_n) + ∑ δ_n ≤ ε'/2 + ε'/2 = ε' ≤ ε
    -- The key steps use h1, h2, h3, h4, hS_vol, hδ_sum, hε'_le
    have h_sum_le : ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ε' := by
      -- Each interior measure ≤ vol(U' n) ≤ vol(S n) + δ n
      -- Sum: ∑ vol(S n) ≤ ε'/2, ∑ δ n = ε'/2, so total ≤ ε'
      -- First show δ is summable (geometric series)
      have hδ_summable : Summable δ := by
        simp only [δ, div_div]
        exact (summable_geometric_two' (ε' / 2)).congr (fun n => by ring_nf)
      -- Show volumes are summable (from the bound hS_vol)
      have hvol_nonneg : ∀ n, 0 ≤ (S n).volume := fun n => Box.volume_nonneg _
      have hvol_sum : Summable (fun n => (S n).volume) := by
        -- Key: use that the partial sums in EReal are bounded
        have h_partial_bound : ∀ t : Finset ℕ, (∑ n ∈ t, (S n).volume : EReal) ≤ ε' / 2 := by
          intro t
          calc (∑ n ∈ t, (S n).volume : EReal)
              ≤ ∑' n, ((S n).volume : EReal) := EReal.finset_sum_le_tsum hvol_nonneg t
            _ ≤ ε' / 2 := hS_vol
        -- In ℝ: partial sums bounded implies summable for nonneg sequences
        have h_partial_real : ∀ t : Finset ℕ, ∑ n ∈ t, (S n).volume ≤ ε' / 2 := by
          intro t
          have h := h_partial_bound t
          have h_coe : (∑ n ∈ t, (S n).volume : EReal) = ↑(∑ n ∈ t, (S n).volume) :=
            (EReal.coe_finset_sum (fun n _ => hvol_nonneg n)).symm
          rw [h_coe] at h; exact EReal.coe_le_coe_iff.mp h
        exact summable_of_sum_le hvol_nonneg h_partial_real
      have hsum_combined : Summable (fun n => (S n).volume + δ n) := hvol_sum.add hδ_summable
      -- Use transitivity through ε' bound:
      -- ∑ m*(interior U'_n) ≤ ∑ vol(U'_n) ≤ ∑ (vol S_n + δ_n) = ∑ vol S_n + ∑ δ_n ≤ ε'/2 + ε'/2 = ε'
      have h_interior_bound : ∀ n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ((S n).volume + δ n : EReal) := by
        intro n
        calc Lebesgue_outer_measure (interior (U' n).toSet)
            ≤ (U' n).volume.toEReal := h3 n
          _ ≤ ((S n).volume + δ n).toEReal := h4 n
          _ = ((S n).volume + δ n : EReal) := rfl
      -- Sum bound: use EReal.tsum_le_coe_tsum_of_forall_le
      have hg_nonneg : ∀ n, 0 ≤ (S n).volume + δ n := fun n => by linarith [hvol_nonneg n, hδ_pos n]
      have h_tsum_bound : ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) ≤ ∑' n, ((S n).volume + δ n : EReal) :=
        EReal.tsum_le_coe_tsum_of_forall_le (fun n => Lebesgue_outer_measure.nonneg _)
          hg_nonneg hsum_combined h_interior_bound
      -- Key equality: tsums in EReal with coercion can be rewritten
      have h_tsum_eq : ∑' n, (↑(S n).volume + ↑(δ n) : EReal) = ↑(∑' n, ((S n).volume + δ n)) := by
        have h1 : ∑' n, (↑(S n).volume + ↑(δ n) : EReal) = ∑' n, ↑((S n).volume + δ n) := by
          apply tsum_congr
          intro n; exact (EReal.coe_add _ _).symm
        have h2 : ∑' n, (↑((S n).volume + δ n) : EReal) = ↑(∑' n, ((S n).volume + δ n)) :=
          (EReal.coe_tsum_of_nonneg hg_nonneg hsum_combined).symm
        rw [h1, h2]
      calc ∑' n, Lebesgue_outer_measure (interior (U' n).toSet)
          ≤ ∑' n, (↑(S n).volume + ↑(δ n) : EReal) := h_tsum_bound
        _ = ↑(∑' n, ((S n).volume + δ n)) := h_tsum_eq
        _ = ↑(∑' n, (S n).volume + ∑' n, δ n) := by rw [hvol_sum.tsum_add hδ_summable]
        _ = ↑(∑' n, (S n).volume) + ↑(∑' n, δ n) := by rw [EReal.coe_add]
        _ ≤ ↑(ε' / 2) + ↑(ε' / 2) := by
            apply add_le_add
            · have := EReal.coe_tsum_of_nonneg hvol_nonneg hvol_sum
              rw [this]; exact hS_vol
            · rw [hδ_sum]
        _ = ε' := by rw [← EReal.coe_add]; norm_cast; ring
    calc Lebesgue_outer_measure (U \ E)
        ≤ Lebesgue_outer_measure U := h1
      _ ≤ ∑' n, Lebesgue_outer_measure (interior (U' n).toSet) := h2
      _ ≤ ε' := h_sum_le
      _ ≤ ε := hε'_le

/-- Lemma 1.2.13(iv) (Empty set is measurable).-/
theorem LebesgueMeasurable.empty {d:ℕ} : LebesgueMeasurable (∅: Set (EuclideanSpace' d)) :=
-- use (i) directly
  IsOpen.measurable isOpen_empty

theorem LebesgueMeasurable.empty' {d:ℕ} : LebesgueMeasurable (∅: Set (EuclideanSpace' d)) := by
-- use definition of Lebesgue measurability
  intro ε hε
  use ∅
  constructor
  · exact isOpen_empty
  constructor
  · exact Set.empty_subset ∅
  · have h_empty : ∅ \ ∅ = (∅ : Set (EuclideanSpace' d)) := Set.diff_self
    rw [h_empty]
    rw [Lebesgue_outer_measure.of_empty d]
    exact le_of_lt hε

/-- Lemma 1.2.13(vi) (Countable union of measurable sets is measurable).-/
theorem LebesgueMeasurable.countable_union {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) : LebesgueMeasurable (⋃ n, E n) := by
  -- Use the ε/2^n trick: let ε > 0 be arbitrary
  intro ε hε
  -- Convert EReal ε to a real number ε' with 0 < ε' ≤ ε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ (ε' : EReal) ≤ ε := by
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact ⟨1, one_pos, le_top⟩
    | coe r =>
      have hr : 0 < r := EReal.coe_pos.mp hε
      exact ⟨r, hr, le_refl _⟩
  -- For each n, get U_n open with E_n ⊆ U_n and m*(U_n \ E_n) ≤ ε'/2^(n+1)
  have hδ_pos : ∀ n, (0:EReal) < ε' / 2^(n+1) := fun n => by
    apply EReal.div_pos (EReal.coe_pos.mpr hε'_pos)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_pos.mpr (by positivity)
    · exact EReal.coe_pow 2 (n+1) ▸ EReal.coe_ne_top ((2:ℝ)^(n+1))
  -- Apply measurability of each E_n with ε'/2^(n+1)
  choose U hU_open hE_sub hU_diff using fun n => hE n (ε' / 2^(n+1)) (hδ_pos n)
  -- The open set is ⋃ n, U n
  use ⋃ n, U n
  constructor
  · -- ⋃ n, U n is open (union of open sets)
    exact isOpen_iUnion hU_open
  constructor
  · -- ⋃ n, E n ⊆ ⋃ n, U n
    apply Set.iUnion_mono
    intro n; exact hE_sub n
  · -- m*((⋃ n, U n) \ (⋃ n, E n)) ≤ ε
    -- Key: (⋃ U_n) \ (⋃ E_n) ⊆ ⋃ (U_n \ E_n)
    have h_diff_subset : (⋃ n, U n) \ (⋃ n, E n) ⊆ ⋃ n, (U n \ E n) := by
      intro x ⟨hx_in_U, hx_not_in_E⟩
      simp only [Set.mem_iUnion] at hx_in_U hx_not_in_E ⊢
      obtain ⟨k, hxk⟩ := hx_in_U
      use k
      constructor
      · exact hxk
      · intro hx_Ek
        exact hx_not_in_E ⟨k, hx_Ek⟩
    calc Lebesgue_outer_measure ((⋃ n, U n) \ (⋃ n, E n))
        ≤ Lebesgue_outer_measure (⋃ n, (U n \ E n)) :=
          Lebesgue_outer_measure.mono h_diff_subset
      _ ≤ ∑' n, Lebesgue_outer_measure (U n \ E n) :=
          Lebesgue_outer_measure.union_le _
      _ ≤ ∑' n, ((ε' / 2^(n+1) : ℝ) : EReal) := by
          -- Use EReal.tsum_le_coe_tsum_of_forall_le
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_f_nonneg : ∀ n, 0 ≤ Lebesgue_outer_measure (U n \ E n) :=
            fun n => Lebesgue_outer_measure.nonneg _
          have h_le_coe : ∀ n, Lebesgue_outer_measure (U n \ E n) ≤ ((ε' / 2^(n+1) : ℝ) : EReal) := by
            intro n
            calc Lebesgue_outer_measure (U n \ E n)
                ≤ (↑ε' : EReal) / 2^(n+1) := hU_diff n
              _ = ↑(ε' / 2^(n+1)) := by
                  rw [EReal.coe_div]
                  congr 1
                  exact Eq.symm (EReal.coe_pow 2 (n + 1))
          exact EReal.tsum_le_coe_tsum_of_forall_le h_f_nonneg h_nonneg h_summable h_le_coe
      _ = ε' := by
          -- ∑ n, ε'/2^(n+1) = ε' (geometric series)
          have h_sum : ∑' n : ℕ, (ε' : ℝ) / 2^(n+1) = ε' := tsum_geometric_eps ε' hε'_pos
          have h_summable : Summable (fun n => ε' / 2^(n+1)) :=
            (summable_geometric_two' ε').congr (fun n => by ring)
          have h_nonneg : ∀ n, 0 ≤ ε' / 2^(n+1) := fun n => by positivity
          rw [← EReal.coe_tsum_of_nonneg h_nonneg h_summable, h_sum]
      _ ≤ ε := hε'_le

/-- Lemma 1.2.13(v) (Complement of a measurable set is measurable). -/
theorem LebesgueMeasurable.complement {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) : LebesgueMeasurable (Eᶜ) := by
  -- Strategy: For each n, find open Uₙ ⊇ E with m*(Uₙ \ E) ≤ 1/(n+1).
  -- Let Fₙ = Uₙᶜ (closed). Then Eᶜ ⊇ Fₙ and m*(Eᶜ \ Fₙ) = m*(Uₙ \ E) ≤ 1/(n+1).
  -- Let F = ⋃ Fₙ. Then m*(Eᶜ \ F) = 0 and Eᶜ = F ∪ (Eᶜ \ F).
  -- F is measurable (countable union of closed sets), Eᶜ \ F is null (hence measurable).

  -- Step 1: For each n, get open Uₙ with E ⊆ Uₙ and m*(Uₙ \ E) ≤ 1/(n+1)
  have h_eps_pos : ∀ n : ℕ, (0 : EReal) < 1 / (n + 1 : ℕ) := fun n => by
    have h1 : (0 : EReal) < 1 := EReal.coe_pos.mpr (by norm_num : (0 : ℝ) < 1)
    have h2 : (0 : EReal) < (n + 1 : ℕ) := by
      simp only [Nat.cast_add, Nat.cast_one]
      exact EReal.coe_pos.mpr (by linarith : (0 : ℝ) < n + 1)
    exact EReal.div_pos h1 h2 (EReal.coe_ne_top _)
  choose U hU_open hE_sub_U hU_diff using fun n => hE (1 / (n + 1 : ℕ)) (h_eps_pos n)

  -- Step 2: Define Fₙ = Uₙᶜ (closed sets)
  let F_n : ℕ → Set (EuclideanSpace' d) := fun n => (U n)ᶜ
  have hF_closed : ∀ n, IsClosed (F_n n) := fun n => (hU_open n).isClosed_compl

  -- Key set-theoretic fact: Eᶜ \ Fₙ = Uₙ \ E
  have h_diff_eq : ∀ n, Eᶜ \ F_n n = U n \ E := fun n => by
    simp only [F_n, Set.diff_compl]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]
    tauto

  -- Step 3: Define F = ⋃ Fₙ (F-sigma set)
  let F := ⋃ n, F_n n

  -- Step 4: Show m*(Eᶜ \ F) = 0
  have h_diff_F : ∀ n, Eᶜ \ F ⊆ U n \ E := fun n => by
    have h1 : Eᶜ \ F ⊆ Eᶜ \ F_n n := Set.diff_subset_diff_right (Set.subset_iUnion F_n n)
    rw [h_diff_eq n] at h1
    exact h1

  have h_measure_bound : ∀ n, Lebesgue_outer_measure (Eᶜ \ F) ≤ 1 / (n + 1 : ℕ) := fun n =>
    calc Lebesgue_outer_measure (Eᶜ \ F)
        ≤ Lebesgue_outer_measure (U n \ E) := Lebesgue_outer_measure.mono (h_diff_F n)
      _ ≤ 1 / (n + 1 : ℕ) := hU_diff n

  have h_null : IsNull (Eᶜ \ F) := by
    apply le_antisymm
    · -- Show m*(Eᶜ \ F) ≤ 0 by showing it's ≤ 1/(n+1) for all n
      by_contra h_ne
      push_neg at h_ne
      have h_pos : 0 < Lebesgue_outer_measure (Eᶜ \ F) := h_ne
      -- Get a real ε with 0 < ε ≤ m*(Eᶜ \ F)
      obtain ⟨ε, hε_pos, hε_le⟩ : ∃ ε : ℝ, 0 < ε ∧ (ε : EReal) ≤ Lebesgue_outer_measure (Eᶜ \ F) := by
        cases hm : Lebesgue_outer_measure (Eᶜ \ F) with
        | bot => rw [hm] at h_pos; exact absurd h_pos (not_lt.mpr bot_le)
        | top => exact ⟨1, one_pos, le_top⟩
        | coe r =>
          rw [hm] at h_pos
          have hr : 0 < r := EReal.coe_pos.mp h_pos
          exact ⟨r, hr, le_refl _⟩
      -- Find N with 1/(N+1) < ε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      have hNp1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hN1 : 1 / ((N : ℝ) + 1) < ε := by
        have h1 : 1 / ε < (N : ℝ) + 1 := lt_of_lt_of_le hN (by norm_cast; exact Nat.le_succ N)
        rw [one_div_lt hNp1_pos hε_pos]; exact h1
      -- h_measure_bound N says m*(Eᶜ \ F) ≤ 1/(N+1)
      have h_bound : Lebesgue_outer_measure (Eᶜ \ F) ≤ 1 / (N + 1 : ℕ) := h_measure_bound N
      have h_eq : (1 : EReal) / (N + 1 : ℕ) = ↑(1 / ((N : ℝ) + 1)) := by
        rw [EReal.coe_div, EReal.coe_one]; norm_cast
      rw [h_eq] at h_bound
      -- ε ≤ m*(Eᶜ \ F) ≤ 1/(N+1) < ε, contradiction
      have h_final : (ε : EReal) < (ε : EReal) := calc
        (ε : EReal) ≤ Lebesgue_outer_measure (Eᶜ \ F) := hε_le
        _ ≤ ↑(1 / ((N : ℝ) + 1)) := h_bound
        _ < ε := EReal.coe_lt_coe_iff.mpr hN1
      exact lt_irrefl (ε : EReal) h_final
    · exact Lebesgue_outer_measure.nonneg _

  -- Step 5: Show Eᶜ = F ∪ (Eᶜ \ F)
  have h_decomp : Eᶜ = F ∪ (Eᶜ \ F) := by
    ext x
    simp only [Set.mem_union, Set.mem_diff]
    constructor
    · intro hx
      by_cases hxF : x ∈ F
      · left; exact hxF
      · right; exact ⟨hx, hxF⟩
    · intro h
      cases h with
      | inl hxF =>
        simp only [F, Set.mem_iUnion] at hxF
        obtain ⟨n, hxFn⟩ := hxF
        simp only [F_n, Set.mem_compl_iff] at hxFn
        have hxE : x ∉ E := fun h => hxFn (hE_sub_U n h)
        exact hxE
      | inr hxEcF => exact hxEcF.1

  -- Step 6: Apply measurability results
  rw [h_decomp]
  have hF_meas : LebesgueMeasurable F := by
    have : F = ⋃ n, F_n n := rfl
    rw [this]
    exact LebesgueMeasurable.countable_union (fun n => (hF_closed n).measurable)
  have hN_meas : LebesgueMeasurable (Eᶜ \ F) := h_null.measurable
  -- Union of two measurable sets
  let S : ℕ → Set (EuclideanSpace' d) := fun n => if n = 0 then F else if n = 1 then Eᶜ \ F else ∅
  have hS_meas : ∀ n, LebesgueMeasurable (S n) := fun n => by
    simp only [S]
    split_ifs with h0 h1
    · exact hF_meas
    · exact hN_meas
    · exact LebesgueMeasurable.empty
  have h_eq : F ∪ (Eᶜ \ F) = ⋃ n, S n := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, S]
    constructor
    · intro h
      cases h with
      | inl hF => exact ⟨0, by simp [hF]⟩
      | inr hN => exact ⟨1, by simp [hN]⟩
    · intro ⟨n, hn⟩
      split_ifs at hn with h0 h1
      · left; exact hn
      · right; exact hn
      · exact absurd hn (Set.notMem_empty x)
  rw [h_eq]
  exact LebesgueMeasurable.countable_union hS_meas

theorem LebesgueMeasurable.finite_union {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hE: ∀ i, LebesgueMeasurable (E i)) : LebesgueMeasurable (⋃ i, E i) := by
  -- Extend E to ℕ-indexed family by padding with empty sets
  let E' : ℕ → Set (EuclideanSpace' d) := fun k => if h : k < n then E ⟨k, h⟩ else ∅
  have hE'_meas : ∀ k, LebesgueMeasurable (E' k) := fun k => by
    simp only [E']
    split_ifs with hk
    · exact hE ⟨k, hk⟩
    · exact LebesgueMeasurable.empty
  -- Show ⋃ i : Fin n, E i = ⋃ k : ℕ, E' k
  have h_eq : (⋃ i : Fin n, E i) = ⋃ k : ℕ, E' k := by
    ext x
    simp only [Set.mem_iUnion, E']
    constructor
    · intro ⟨i, hx⟩
      use i.val
      simp only [i.isLt, ↓reduceDIte, hx]
    · intro ⟨k, hx⟩
      split_ifs at hx with hk
      · exact ⟨⟨k, hk⟩, hx⟩
      · exact absurd hx (Set.notMem_empty x)
  rw [h_eq]
  exact LebesgueMeasurable.countable_union hE'_meas

theorem LebesgueMeasurable.union {d :ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : LebesgueMeasurable (E ∪ F) := by
  -- Express E ∪ F as union over Fin 2
  let S : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
  have hS : ∀ i, LebesgueMeasurable (S i) := fun i => by fin_cases i <;> simp [S, hE, hF]
  have h_eq : E ∪ F = ⋃ i : Fin 2, S i := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, S]
    constructor
    · rintro (hx | hx)
      · exact ⟨0, by simp [hx]⟩
      · exact ⟨1, by simp [hx]⟩
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
  rw [h_eq]
  exact LebesgueMeasurable.finite_union hS

/-- Lemma 1.2.13(vii) (Countable intersection of measurable sets is measurable). -/
theorem LebesgueMeasurable.countable_inter {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) : LebesgueMeasurable (⋂ n, E n) := by
  -- By de Morgan: ⋂ Eₙ = (⋃ Eₙᶜ)ᶜ
  have h_eq : (⋂ n, E n) = (⋃ n, (E n)ᶜ)ᶜ := by
    rw [Set.compl_iUnion]
    simp only [compl_compl]
  rw [h_eq]
  -- Each Eₙᶜ is measurable by (v)
  have hE_compl : ∀ n, LebesgueMeasurable ((E n)ᶜ) := fun n => (hE n).complement
  -- ⋃ Eₙᶜ is measurable by (vi)
  have h_union : LebesgueMeasurable (⋃ n, (E n)ᶜ) := LebesgueMeasurable.countable_union hE_compl
  -- (⋃ Eₙᶜ)ᶜ is measurable by (v) again
  exact h_union.complement

theorem LebesgueMeasurable.finite_inter {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hE: ∀ i, LebesgueMeasurable (E i)) : LebesgueMeasurable (⋂ i, E i) := by
  -- Extend Fin n indexed family to ℕ indexed family with univ for k ≥ n
  let E' : ℕ → Set (EuclideanSpace' d) := fun k => if h : k < n then E ⟨k, h⟩ else Set.univ
  have hE'_meas : ∀ k, LebesgueMeasurable (E' k) := fun k => by
    simp only [E']
    split_ifs with hk
    · exact hE ⟨k, hk⟩
    · -- univ = ∅ᶜ, so measurable by complement of empty
      rw [← Set.compl_empty]
      exact LebesgueMeasurable.empty.complement
  have h_eq : (⋂ i : Fin n, E i) = ⋂ k : ℕ, E' k := by
    ext x
    simp only [Set.mem_iInter, E']
    constructor
    · intro hx k
      split_ifs with hk
      · exact hx ⟨k, hk⟩
      · exact Set.mem_univ x
    · intro hx ⟨i, hi⟩
      have := hx i
      simp only [hi, dite_true] at this
      exact this
  rw [h_eq]
  exact LebesgueMeasurable.countable_inter hE'_meas

theorem LebesgueMeasurable.inter {d :ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : LebesgueMeasurable (E ∩ F) := by
  -- Express E ∩ F as intersection over Fin 2
  let S : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
  have hS : ∀ i, LebesgueMeasurable (S i) := fun i => by fin_cases i <;> simp [S, hE, hF]
  have h_eq : E ∩ F = ⋂ i : Fin 2, S i := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, S]
    constructor
    · intro ⟨hxE, hxF⟩ i
      fin_cases i <;> simp_all
    · intro hx
      exact ⟨hx 0, hx 1⟩
  rw [h_eq]
  exact LebesgueMeasurable.finite_inter hS

/-- Exercise 1.2.7 (Criteria for measurability)-/
theorem LebesgueMeasurable.TFAE {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E,
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure (U \ E) ≤ ε),
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsClosed F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsClosed F ∧ Lebesgue_outer_measure (symmDiff F E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε)
    ].TFAE
  := by sorry

  /-- Exercise 1.2.8 -/
theorem Jordan_measurable.lebesgue {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : LebesgueMeasurable E := by
  sorry

open BoundedInterval

abbrev CantorInterval (n:ℕ) : Set ℝ := ⋃ a : Fin n → ({0, 2}:Set ℕ), (Icc (∑ i, (a i)/(3:ℝ)^(i.val+1)) (∑ i, a i/(3:ℝ)^(i.val+1) + 1/(3:ℝ)^(n+1))).toSet

abbrev CantorSet : Set ℝ := ⋂ n : ℕ, CantorInterval n

/-- Exercise 1.2.9 (Middle thirds Cantor set ) -/
theorem CantorSet.compact : IsCompact CantorSet := by
  sorry

theorem CantorSet.uncountable : Uncountable CantorSet := by
  sorry

theorem CantorSet.null : IsNull (Real.equiv_EuclideanSpace' '' CantorSet) := by sorry

/-- Exercise 1.2.10 ([0,1) is not the countable union of pairwise disjoint closed intervals)-/
example : ¬ ∃ (I: ℕ → BoundedInterval), (∀ n, IsClosed (I n).toSet) ∧ (Set.univ.PairwiseDisjoint (fun n ↦ (I n).toSet) ) ∧ (⋃ n, (I n).toSet = Set.Ico 0 1) := by
  sorry

/-- Exercise 1.2.10, challenge version -/
example : ¬ ∃ (E: ℕ → Set ℝ), (∀ n, IsClosed (E n)) ∧ (Set.univ.PairwiseDisjoint (fun n ↦ (E n)) ) ∧ (⋃ n, (E n) = Set.Ico 0 1) := by
  sorry

theorem Jordan_measurable.Lebesgue_measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : Lebesgue_measure E = hE.measure := by
  sorry

/-- Lemma 1.2.15(a) (Empty set has zero Lebesgue measure). The proof is missing. -/
@[simp]
theorem Lebesgue_measure.empty {d:ℕ} : Lebesgue_measure (∅: Set (EuclideanSpace' d)) = 0 := by
  sorry

/-- Lemma 1.2.15(b) (Countable additivity). The proof is missing. -/
theorem Lebesgue_measure.countable_union {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hmes: ∀ n, LebesgueMeasurable (E n)) (hdisj: Set.univ.PairwiseDisjoint E) : Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  sorry

theorem Lebesgue_measure.finite_union {d n:ℕ} {E: Fin n → Set (EuclideanSpace' d)} (hmes: ∀ n, LebesgueMeasurable (E n)) (hdisj: Set.univ.PairwiseDisjoint E) : Lebesgue_measure (⋃ n, E n) = ∑' n, Lebesgue_measure (E n) := by
  sorry

theorem Lebesgue_measure.union {d:ℕ} {E F: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) (hdisj: E ∩ F = ∅) : Lebesgue_measure (E ∪ F) = Lebesgue_measure E + Lebesgue_measure F := by
  sorry

/-- Exercise 1.2.11(a) (Upward monotone convergence)-/
theorem Lebesgue_measure.upward_monotone_convergence {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) (hmono: ∀ n, E n ⊆ E (n + 1)) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋃ n, E n))) := by
  sorry

/-- Exercise 1.2.11(b) (Downward monotone convergence)-/
theorem Lebesgue_measure.downward_monotone_convergence {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) (hmono: ∀ n, E (n+1) ⊆ E n) (hfin: ∃ n, Lebesgue_measure (E n) < ⊤) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋂ n, E n))) := by
  sorry

/-- Exercise 1.2.11 (c) (counterexample)-/
example : ∃ (d:ℕ) (E: ℕ → Set (EuclideanSpace' d)) (hE: ∀ n, LebesgueMeasurable (E n)) (hmono: ∀ n, E (n+1) ⊆ E n), ¬ Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure (⋂ n, E n))) := by sorry

/-- Exercise 1.2.12 -/
example {d:ℕ} (m: Set (EuclideanSpace' d) → EReal) (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E) (hadd: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n)) {E F: Set (EuclideanSpace' d)}
(hsub: E ⊆ F) (hE: LebesgueMeasurable E) (hF: LebesgueMeasurable F) : m E ≤ m F := by
  sorry

/-- Exercise 1.2.12 -/
example {d:ℕ} (m: Set (EuclideanSpace' d) → EReal) (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E) (hadd: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n)) {E: ℕ → Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)):  m (⋃ n, E n) ≤ ∑' n, m (E n) := by
  sorry

/-- Exercise 1.2.13(i) -/
example {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} {E₀: Set (EuclideanSpace' d)} (hE: ∀ n, LebesgueMeasurable (E n)) (hpoint: ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x))) : LebesgueMeasurable E₀ := by sorry

/-- Exercise 1.2.13(ii) -/
example {d:ℕ} {E: ℕ → Set (EuclideanSpace' d)} {E₀ F: Set (EuclideanSpace' d)}
  (hE: ∀ n, LebesgueMeasurable (E n))
  (hpoint: ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x)))
  (hsub: ∀ n, E n ⊆ F) (hFmes: LebesgueMeasurable F) (hfin: Lebesgue_measure F < ⊤) : Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure E₀)) := by sorry

/-- Exercise 1.2.13(iii) -/
example : ∃ (d:ℕ) (E: ℕ → Set (EuclideanSpace' d)) (E₀ F: Set (EuclideanSpace' d))
  (hE: ∀ n, LebesgueMeasurable (E n))
  (hpoint: ∀ x, Filter.atTop.Tendsto (fun n ↦ (E n).indicator' x) (nhds (E₀.indicator' x)))
  (hsub: ∀ n, E n ⊆ F) (hFmes: LebesgueMeasurable F), ¬ Filter.atTop.Tendsto (fun n ↦ Lebesgue_measure (E n)) (nhds (Lebesgue_measure E₀)) := by sorry

/-- Exercise 1.2.14 -/
example {d:ℕ} (E: Set (EuclideanSpace' d)) : ∃ (F: Set (EuclideanSpace' d)), E ⊆ F ∧ LebesgueMeasurable F ∧ Lebesgue_measure F = Lebesgue_outer_measure E := by sorry

/-- Exercise 1.2.15 (Inner regularity)-/
theorem Lebesgue_measure.eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): Lebesgue_measure E = sSup { M | ∃ K, K ⊆ E ∧ IsCompact K ∧ M = Lebesgue_measure K} := by
  sorry

/-- Exercise 1.2.16 (Criteria for measurability)-/
theorem LebesgueMeasurable.finite_TFAE {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E ∧ Lebesgue_measure E < ⊤,
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_measure U < ⊤ ∧ Lebesgue_outer_measure (U \ E) ≤ ε),
      (∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ Bornology.IsBounded U ∧ Lebesgue_outer_measure (symmDiff U E) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsCompact F ∧ F ⊆ E ∧ Lebesgue_outer_measure (E \ F) ≤ ε),
      (∀ ε > 0, ∃ F: Set (EuclideanSpace' d), IsCompact F ∧ Lebesgue_outer_measure (symmDiff F E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Lebesgue_measure E' < ⊤ ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), LebesgueMeasurable E' ∧ Bornology.IsBounded E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ E': Set (EuclideanSpace' d), IsElementary E' ∧ Lebesgue_outer_measure (symmDiff E' E) ≤ ε),
      (∀ ε > 0, ∃ (n:ℤ) (F: Finset (Box d)), (∀ B ∈ F, B.IsDyadicAtScale n) ∧ Lebesgue_outer_measure (symmDiff (⋃ B ∈ F, B.toSet) E) ≤ ε)
    ].TFAE
  := by sorry

/-- Exercise 1.2.17 (Caratheodory criterion one direction)-/
theorem LebesgueMeasurable.caratheodory {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E,
      (∀ A: Set (EuclideanSpace' d), IsElementary A → Lebesgue_outer_measure A = Lebesgue_outer_measure (A ∩ E) + Lebesgue_outer_measure (A \ E)),
      (∀ (B:Box d),  Lebesgue_outer_measure B.toSet = Lebesgue_outer_measure (B.toSet ∩ E) + Lebesgue_outer_measure (B.toSet \ E))
    ].TFAE
  := by sorry

theorem Bornology.IsBounded.inElementary {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ∃ (A: Set (EuclideanSpace' d)), IsElementary A ∧ E ⊆ A := by sorry

noncomputable def inner_measure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ℝ := (Lebesgue_measure hE.inElementary.choose).toReal - (Lebesgue_measure (hE.inElementary.choose \ E)).toReal

/-- Exercise 1.2.18(i) (Inner measure)-/
theorem inner_measure.eq {d:ℕ} {E A: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E)
  (hA: IsElementary A) (hsub: E ⊆ A) : inner_measure hE = Lebesgue_measure A - Lebesgue_outer_measure (A \ E) := by
  sorry

/-- Exercise 1.2.18(ii) (Inner measure)-/
theorem inner_measure.le {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E)
  : inner_measure hE ≤ Lebesgue_outer_measure E := by
  sorry

/-- Exercise 1.2.18(ii) (Inner measure)-/
theorem inner_measure.eq_iff {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E)
  : inner_measure hE = Lebesgue_outer_measure E ↔ LebesgueMeasurable E := by
  sorry

def IsFσ  {X:Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsClosed t) ∧ T.Countable ∧ s = ⋃₀ T

/-- Exercise 1.2.19 -/
theorem LebesgueMeasurable.TFAE' {d:ℕ} (E: Set (EuclideanSpace' d)) :
    [
      LebesgueMeasurable E,
      (∃ F, ∃ N, IsGδ F ∧ IsNull N ∧ E = F \ N),
      (∃ F, ∃ N, IsFσ F ∧ IsNull N ∧ E = F ∪ N)
    ].TFAE
  := by sorry

open Pointwise

/-- Exercise 1.2.20 (Translation invariance) -/
theorem LebesgueMeasurable.translate {d:ℕ} (E: Set (EuclideanSpace' d)) (x: EuclideanSpace' d) :
    LebesgueMeasurable E ↔ LebesgueMeasurable (E + {x}) := by
  sorry

theorem Lebesgue_measure.translate {d:ℕ} {E: Set (EuclideanSpace' d)} (x: EuclideanSpace' d)
   (hE: LebesgueMeasurable E): Lebesgue_measure (E + {x}) = Lebesgue_measure E := by
  sorry

/-- Exercise 1.2.21 (Change of variables) -/
lemma LebesgueMeasurable.linear {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
{E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): LebesgueMeasurable (T '' E) := by
  sorry

/-- Exercise 1.2.21 (Change of variables) -/
lemma Lebesgue_measure.linear {d:ℕ} (A: Matrix (Fin d) (Fin d) ℝ) [Invertible A]
 {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E): Lebesgue_measure (A.linear_equiv '' E) = |A.det| * Lebesgue_measure E := by
  sorry

/-- Exercise 1.2.22 -/
theorem Lebesgue_outer_measure.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  : Lebesgue_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ Lebesgue_outer_measure E₁ * Lebesgue_outer_measure E₂ := by sorry

/-- Exercise 1.2.22 -/
theorem LebesgueMeasurable.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: LebesgueMeasurable E₁) (hE₂: LebesgueMeasurable E₂) : LebesgueMeasurable (EuclideanSpace'.prod E₁ E₂) := by sorry

/-- Exercise 1.2.22 -/
theorem Lebesgue_measure.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: LebesgueMeasurable E₁) (hE₂: LebesgueMeasurable E₂)
  : Lebesgue_measure (EuclideanSpace'.prod E₁ E₂) = Lebesgue_measure E₁ * Lebesgue_measure E₂ := by sorry

/-- Exercise 1.2.23 (Uniqueness of Lebesgue measure) -/
theorem Lebesgue_measure.unique {d:ℕ} (m: Set (EuclideanSpace' d) → EReal)
  (h_empty: m ∅ = 0) (h_pos: ∀ E, 0 ≤ m E)
  (h_add: ∀ E: ℕ → Set (EuclideanSpace' d), (Set.univ.PairwiseDisjoint E) → (∀ n, LebesgueMeasurable (E n)) → m (⋃ n, E n) = ∑' n, m (E n))
  (hnorm: m (Box.unit_cube d) = 1)
  : ∀ E, LebesgueMeasurable E → m E = Lebesgue_measure E := by sorry

/-- Exercise 1.2.24(i) (Lebesgue measure as the completion of elementary measure)-/
instance IsElementary.ae_equiv {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A):
Setoid (Set A) := {
   r E F := IsNull (Subtype.val '' (_root_.symmDiff E F))
   iseqv := by sorry
}

def IsElementary.ae_subsets {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) := Quotient hA.ae_equiv

def IsElementary.ae_quot {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: Set A): hA.ae_subsets := Quotient.mk' (s := hA.ae_equiv) E

/-- Exercise 1.2.24(ii) (Lebesgue measure as the completion of elementary measure)-/
noncomputable def IsElementary.dist {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : hA.ae_subsets → hA.ae_subsets → ℝ := Quotient.lift₂ (fun E F ↦ (Lebesgue_outer_measure (Subtype.val '' (_root_.symmDiff E F))).toReal) (by sorry)

/-- Exercise 1.2.24(ii) (Lebesgue measure as the completion of elementary measure)-/
noncomputable instance IsElementary.metric {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : MetricSpace hA.ae_subsets := {
    dist := hA.dist
    dist_self := by sorry
    eq_of_dist_eq_zero := by sorry
    dist_comm := by sorry
    dist_triangle := by sorry
  }

/-- Exercise 1.2.24(ii) (Lebesgue measure as the completion of elementary measure)-/
instance IsElementary.complete {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : CompleteSpace hA.ae_subsets := by
  sorry

noncomputable def IsElementary.ae_elem {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : Set hA.ae_subsets := { E | ∃ F: Set A, IsElementary (Subtype.val '' F) ∧ hA.ae_quot F = E }

noncomputable def IsElementary.ae_measurable {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : Set hA.ae_subsets := { E | ∃ F: Set A, LebesgueMeasurable (Subtype.val '' F) ∧ hA.ae_quot F = E }

/-- Exercise 1.2.24(iii) (Lebesgue measure as the completion of elementary measure)-/
theorem IsElementary.measurable_eq_closure_elem {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : closure hA.ae_elem = hA.ae_measurable := by
  sorry

/-- Exercise 1.2.24(c) (Lebesgue measure as the completion of elementary measure)-/
theorem IsElementary.measurable_complete {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) : closure hA.ae_elem = hA.ae_measurable := by
  sorry

noncomputable def IsElementary.ae_measure {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: hA.ae_measurable) : ℝ := (Lebesgue_measure (Subtype.val '' E.property.choose)).toReal

noncomputable def IsElementary.ae_elem_measure {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (E: hA.ae_elem) : ℝ := E.property.choose_spec.1.measure

/-- Exercise 1.2.24(iv) (Lebesgue measure as the completion of elementary measure)-/
theorem IsElementary.ae_measure_eq_completion {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A) (m: hA.ae_subsets → ℝ) :
ContinuousOn m hA.ae_measurable ∧ (∀ (E:hA.ae_elem), m E.val = hA.ae_elem_measure E)
↔ (∀ (E:hA.ae_measurable), m E.val = hA.ae_measure E) := by sorry

noncomputable abbrev IsCurve {d:ℕ} (C: Set (EuclideanSpace' d)) : Prop := ∃ (a b:ℝ) (γ: ℝ → EuclideanSpace' d), C = γ '' (Set.Icc a b) ∧ ContDiffOn ℝ 1 γ (Set.Icc a b)

/-- Exercise 1.2.25(i) -/
theorem IsCurve.null {d:ℕ} (hd: d ≥ 2) {C: Set (EuclideanSpace' d)} (hC: IsCurve C) : IsNull C := by sorry

example : ∃ (d:ℕ) (C: Set (EuclideanSpace' d)) (hC: IsCurve C), ¬ IsNull Cx := by
  sorry

/-- Exercise 1.2.25 -/
example {d:ℕ} (hd: d ≥ 2) : ¬ ∃ C: ℕ → Set (EuclideanSpace' d), (∀ n, IsCurve (C n)) ∧ (⋃ n, C n = (Box.unit_cube d).toSet) := by
  sorry
