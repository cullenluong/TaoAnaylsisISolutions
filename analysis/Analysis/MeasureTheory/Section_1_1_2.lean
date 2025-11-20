import Analysis.MeasureTheory.Section_1_1_1
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Introduction to Measure Theory, Section 1.1.2: Jordan measure

A companion to Section 1.1.2 of the book "An introduction to Measure Theory".

-/

/-- Definition 1.1.4.  We intend these concepts to only be applied for bounded sets `E`, but
it is convenient to permit `E` to be unbounded for the purposes of making the definitions.
-/
noncomputable abbrev Jordan_inner_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : ℝ :=
  sSup { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, A ⊆ E ∧ m = hA.measure }

noncomputable abbrev Jordan_outer_measure {d:ℕ} (E: Set (EuclideanSpace' d)) : ℝ :=
  sInf { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, E ⊆ A ∧ m = hA.measure }

noncomputable abbrev JordanMeasurable {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop :=
  Bornology.IsBounded E ∧ Jordan_inner_measure E = Jordan_outer_measure E

noncomputable abbrev JordanMeasurable.measure {d:ℕ} {E: Set (EuclideanSpace' d)} (_: JordanMeasurable E) : ℝ :=
  Jordan_inner_measure E

theorem JordanMeasurable.eq_inner {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : hE.measure = Jordan_inner_measure E := rfl

theorem JordanMeasurable.eq_outer {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) : hE.measure = Jordan_outer_measure E := by grind


/-- Various preparatory lemmas for the exercises. -/
theorem IsElementary.contains_bounded {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : ∃ A: Set (EuclideanSpace' d), IsElementary A ∧ E ⊆ A := by
  -- Strategy:
  -- 1. Get bound M from boundedness: E ⊆ Metric.closedBall 0 M
  -- 2. Construct box B with Icc (-M') M' in each coordinate, where M' = max M 0 + 1
  -- 3. Show E ⊆ B.toSet: for x ∈ E, we have ‖x‖ ≤ M < M', so |x i| ≤ ‖x‖ < M' for each coordinate i
  -- 4. Use IsElementary.box to show B.toSet is elementary
  -- Step 1: Get bound M from boundedness
  rw [Metric.isBounded_iff_subset_closedBall 0] at hE
  obtain ⟨M, hE_ball⟩ := hE
  -- Step 2: Construct box B with Icc (-M') M' in each coordinate
  set M' := max M 0 + 1
  let B : Box d := {
    side := fun _ => BoundedInterval.Icc (-M') M'
  }
  -- Step 3: Show E ⊆ B.toSet
  have hE_subset : E ⊆ B.toSet := by
    intro x hx
    simp [Box.toSet]
    intro i _
    simp
    have h_mem : x ∈ Metric.closedBall 0 M := hE_ball hx
    rw [Metric.mem_closedBall, dist_zero_right] at h_mem
    have h_M_bound : M ≤ max M 0 := le_max_left _ _
    have h_M'_bound : max M 0 < M' := by
      dsimp [M']
      exact lt_add_one (max M 0)
    have h_norm_bound : ‖x‖ < M' := lt_of_le_of_lt h_mem (lt_of_le_of_lt h_M_bound h_M'_bound)
    have h_coord_sq : (x i)^2 ≤ ∑ j, (x j)^2 := by
      exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    have h_coord : |x i| ≤ ‖x‖ := by
      rw [EuclideanSpace'.norm_eq]
      calc |x i| = Real.sqrt ((x i)^2) := by rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt (∑ j, (x j)^2) := Real.sqrt_le_sqrt h_coord_sq
    have h_abs_bound : |x i| < M' := lt_of_le_of_lt h_coord h_norm_bound
    constructor
    · have : -M' < x i := by
        rw [abs_lt] at h_abs_bound
        exact h_abs_bound.1
      linarith
    · have : x i < M' := by
        rw [abs_lt] at h_abs_bound
        exact h_abs_bound.2
      linarith
  -- Step 4: Show B.toSet is elementary
  have hB_elem : IsElementary B.toSet := IsElementary.box B
  exact ⟨B.toSet, hB_elem, hE_subset⟩

theorem Jordan_inner_measure_nonneg {d:ℕ} (E: Set (EuclideanSpace' d)) : 0 ≤ Jordan_inner_measure E := by
  -- Strategy:
  -- 1. Unfold the definition: Jordan_inner_measure E = sSup { m | ∃ A, IsElementary A, A ⊆ E ∧ m = hA.measure }
  -- 2. Apply Real.sSup_nonneg: this requires showing ∀ m in the set, 0 ≤ m
  -- 3. For any m in the set, extract the elementary set A and use IsElementary.measure_nonneg
  -- Note: Real.sSup_nonneg handles both empty and nonempty sets, so we don't need to show nonemptiness
  unfold Jordan_inner_measure
  apply Real.sSup_nonneg
  -- For any m in the set, there exists an elementary set A ⊆ E with m = hA.measure
  intro m hm
  -- Extract the elementary set and its measure
  obtain ⟨A, hA, hA_subset, rfl⟩ := hm
  -- Apply IsElementary.measure_nonneg to show 0 ≤ hA.measure
  exact IsElementary.measure_nonneg hA

theorem Jordan_outer_measure_nonneg {d:ℕ} (E: Set (EuclideanSpace' d)) : 0 ≤ Jordan_outer_measure E := by
  -- Strategy:
  -- 1. Unfold the definition: Jordan_outer_measure E = sInf { m | ∃ A, IsElementary A, E ⊆ A ∧ m = hA.measure }
  -- 2. Apply Real.sInf_nonneg: this requires showing ∀ m in the set, 0 ≤ m
  -- 3. For any m in the set, extract the elementary set A and use IsElementary.measure_nonneg
  -- Note: Real.sInf_nonneg handles both empty and nonempty sets, so we don't need to show nonemptiness
  unfold Jordan_outer_measure
  apply Real.sInf_nonneg
  -- For any m in the set, there exists an elementary set A ⊇ E with m = hA.measure
  intro m hm
  -- Extract the elementary set and its measure
  obtain ⟨A, hA, hE_subset, rfl⟩ := hm
  -- Apply IsElementary.measure_nonneg to show 0 ≤ hA.measure
  exact IsElementary.measure_nonneg hA

theorem Jordan_inner_le_outer {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) : Jordan_inner_measure E ≤ Jordan_outer_measure E := by
  -- Strategy:
  -- 1. Unfold both definitions to work with sSup and sInf directly
  -- 2. Use csSup_le to show that outer measure is an upper bound for inner measure set
  --    csSup_le requires two goals:
  --    a. Show inner measure set {A.measure | A ⊆ E, elementary} is nonempty (it contains at least 0)
  --    b. Show outer measure is an upper bound: for any m in inner measure set, m ≤ outer measure
  unfold Jordan_inner_measure Jordan_outer_measure
  apply csSup_le
  · -- Show the set is nonempty (it contains at least 0)
    use 0
    use ∅
    use IsElementary.empty d
    simp [IsElementary.measure_of_empty]
  · -- Show that sInf {B.measure | B ⊇ E, elementary} is an upper bound
    intro m hm
    obtain ⟨A, hA, hA_subset_E, rfl⟩ := hm
    -- For any elementary B ⊇ E, we have A ⊆ B, so A.measure ≤ B.measure
    -- Taking infimum over all such B gives A.measure ≤ sInf {B.measure | B ⊇ E, elementary}
    apply le_csInf
    · -- Show the outer measure set is nonempty (use IsElementary.contains_bounded)
      obtain ⟨B, hB, hE_subset_B⟩ := IsElementary.contains_bounded hE
      exact ⟨hB.measure, B, hB, hE_subset_B, rfl⟩
    · -- Show A.measure is a lower bound for the outer measure set
      intro b hb
      obtain ⟨B, hB, hE_subset_B, rfl⟩ := hb
      -- Since A ⊆ E ⊆ B, we have A ⊆ B, so A.measure ≤ B.measure
      exact IsElementary.measure_mono hA hB (Set.Subset.trans hA_subset_E hE_subset_B)

theorem le_Jordan_inner {d:ℕ} {E A: Set (EuclideanSpace' d)}
  (hA: IsElementary A) (hAE: A ⊆ E) : hA.measure ≤ Jordan_inner_measure A := by
  -- Strategy:
  -- 1. Unfold definition: Jordan_inner_measure A = sSup { m | ∃ B, IsElementary B, B ⊆ A ∧ m = hB.measure }
  -- 2. Show hA.measure is in this set: use A itself (A ⊆ A, and hA.measure = hA.measure)
  -- 3. Show the set is bounded above by hA.measure: for any B ⊆ A elementary, B.measure ≤ A.measure by monotonicity
  -- 4. Apply le_csSup: any element of a set is ≤ its supremum
  unfold Jordan_inner_measure
  -- Step 2: Show hA.measure is in the set
  have h_mem : hA.measure ∈ { m:ℝ | ∃ (B: Set (EuclideanSpace' d)), ∃ hB: IsElementary B, B ⊆ A ∧ m = hB.measure } := by
    use A, hA, Set.Subset.refl A
  -- Step 3: Show the set is bounded above by hA.measure
  have h_bdd : BddAbove { m:ℝ | ∃ (B: Set (EuclideanSpace' d)), ∃ hB: IsElementary B, B ⊆ A ∧ m = hB.measure } := by
    use hA.measure
    intro m hm
    obtain ⟨B, hB, hB_subset_A, rfl⟩ := hm
    -- Since B ⊆ A and both are elementary, B.measure ≤ A.measure by monotonicity
    exact IsElementary.measure_mono hB hA hB_subset_A
  -- Step 4: Apply le_csSup
  exact le_csSup h_bdd h_mem

theorem Jordan_outer_le {d:ℕ} {E A: Set (EuclideanSpace' d)}
  (hA: IsElementary A) (hAE: E ⊆ A) : Jordan_outer_measure A ≤ hA.measure := by
  -- Strategy:
  -- 1. Unfold definition: Jordan_outer_measure A = sInf { m | ∃ B, IsElementary B, A ⊆ B ∧ m = hB.measure }
  -- 2. Show hA.measure is in this set: use A itself (A ⊆ A, and hA.measure = hA.measure)
  -- 3. Show the set is bounded below by 0: for any B ⊇ A elementary, 0 ≤ B.measure by nonnegativity
  -- 4. Apply csInf_le: infimum of a set is ≤ any element in the set
  unfold Jordan_outer_measure
  -- Step 2: Show hA.measure is in the set
  have h_mem : hA.measure ∈ { m:ℝ | ∃ (B: Set (EuclideanSpace' d)), ∃ hB: IsElementary B, A ⊆ B ∧ m = hB.measure } := by
    use A, hA, Set.Subset.refl A
  -- Step 3: Show the set is bounded below by 0
  have h_bdd : BddBelow { m:ℝ | ∃ (B: Set (EuclideanSpace' d)), ∃ hB: IsElementary B, A ⊆ B ∧ m = hB.measure } := by
    use 0
    intro m hm
    obtain ⟨B, hB, _, rfl⟩ := hm
    -- Since B is elementary, 0 ≤ B.measure by nonnegativity
    exact IsElementary.measure_nonneg hB
  -- Step 4: Apply csInf_le
  exact csInf_le h_bdd h_mem

theorem Jordan_inner_le {d:ℕ} {E: Set (EuclideanSpace' d)} {m:ℝ}
  (hm: m < Jordan_inner_measure E) : ∃ A: Set (EuclideanSpace' d), ∃ hA: IsElementary A, A ⊆ E ∧ m < hA.measure := by
  -- Strategy:
  -- 1. Unfold definition: Jordan_inner_measure E = sSup { m' | ∃ A, IsElementary A, A ⊆ E ∧ m' = hA.measure }
  -- 2. Show the set is nonempty (empty set is elementary with measure 0)
  -- 3. Apply exists_lt_of_lt_csSup to get existence of element greater than m
  -- 4. Extract the elementary set A from the witness
  unfold Jordan_inner_measure at hm
  set S := { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, A ⊆ E ∧ m = hA.measure }
  -- Step 2: Show the set is nonempty
  have h_nonempty : S.Nonempty := by
    use 0
    use ∅
    use IsElementary.empty d
    constructor
    · exact Set.empty_subset E
    · exact Eq.symm (IsElementary.measure_of_empty d)
  -- Step 3: Apply exists_lt_of_lt_csSup to get existence of element greater than m
  obtain ⟨m', hm', hm_lt⟩ := exists_lt_of_lt_csSup h_nonempty hm
  -- Step 4: Extract the elementary set A from the witness
  obtain ⟨A, hA, hA_subset, rfl⟩ := hm'
  exact ⟨A, hA, hA_subset, hm_lt⟩

theorem le_Jordan_outer {d:ℕ} {E: Set (EuclideanSpace' d)} {m:ℝ}
  (hm: Jordan_outer_measure E < m) (hbound: Bornology.IsBounded E) :
  ∃ A: Set (EuclideanSpace' d), ∃ hA: IsElementary A, E ⊆ A ∧ hA.measure < m := by
  -- Strategy:
  -- 1. Unfold definition: Jordan_outer_measure E = sInf { m' | ∃ A, IsElementary A, E ⊆ A ∧ m' = hA.measure }
  -- 2. Since sInf S < m, by properties of infimum, there exists x ∈ S with x < m
  -- 3. Use IsElementary.contains_bounded to show the set is nonempty (since E is bounded)
  -- 4. Apply exists_lt_of_csInf_lt to get existence of element less than m
  -- 5. Extract the elementary set A from the witness
  unfold Jordan_outer_measure at hm
  set S := { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A, E ⊆ A ∧ m = hA.measure }
  -- Step 3: Show the set is nonempty
  have h_nonempty : S.Nonempty := by
    obtain ⟨A, hA, hE_subset⟩ := IsElementary.contains_bounded hbound
    exact ⟨hA.measure, A, hA, hE_subset, rfl⟩
  -- Step 4: Apply exists_lt_of_csInf_lt to get existence of element less than m
  obtain ⟨m', hm', hm'_lt⟩ := exists_lt_of_csInf_lt h_nonempty hm
  -- Step 5: Extract the elementary set A from the witness
  obtain ⟨A, hA, hE_subset, rfl⟩ := hm'
  exact ⟨A, hA, hE_subset, hm'_lt⟩

/-- Exercise 1.1.5 -/
theorem JordanMeasurable.equiv {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
 [JordanMeasurable E,
  ∀ ε>0, ∃ A, ∃ B, ∃ hA: IsElementary A, ∃ hB: IsElementary B,
    A ⊆ E ∧ E ⊆ B ∧ (hB.sdiff hA).measure ≤ ε,
  ∀ ε>0, ∃ A, ∃ hA: IsElementary A, Jordan_outer_measure (symmDiff E A) ≤ ε].TFAE := by
  sorry

theorem IsElementary.jordanMeasurable {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : JordanMeasurable E := by
  sorry

theorem JordanMeasurable.mes_of_elementary {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: IsElementary E) : hE.jordanMeasurable.measure = hE.measure := by
  sorry

theorem JordanMeasurable.empty (d:ℕ) : JordanMeasurable (∅: Set (EuclideanSpace' d)) := by
  sorry

@[simp]
theorem JordanMeasurable.mes_of_empty (d:ℕ) : (JordanMeasurable.empty d).measure = 0 := by
  sorry


/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.union {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (E ∪ F) := by
  sorry

lemma JordanMeasurable.union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, JordanMeasurable E) : JordanMeasurable (⋃ E ∈ S, E) := by sorry

/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.inter {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (E ∩ F) := by
  sorry

/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.sdiff {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (E \ F) := by
  sorry

/-- Exercise 1.1.6 (i) (Boolean closure) -/
theorem JordanMeasurable.symmDiff {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) : JordanMeasurable (symmDiff E F) := by
  sorry

/-- Exercise 1.1.6 (ii) (non-negativity) -/
theorem JordanMeasurable.nonneg {d:ℕ} {E : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) : 0 ≤ hE.measure := by
  sorry

/-- Exercise 1.1.6 (iii) (finite additivity) -/
theorem JordanMeasurable.mes_of_disjUnion {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) (hEF: Disjoint E F)
  : (hE.union hF).measure = hE.measure + hF.measure := by
  sorry

/-- Exercise 1.1.6 (iii) (finite additivity) -/
lemma JordanMeasurable.measure_of_disjUnion' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, JordanMeasurable E) (hdisj: S.toSet.PairwiseDisjoint id):
  (JordanMeasurable.union' hE).measure = ∑ E:S, (hE E.val E.property).measure := by
  sorry

/-- Exercise 1.1.6 (iv) (monotonicity) -/
theorem JordanMeasurable.mono {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F) (hEF: E ⊆ F)
  : hE.measure ≤ hF.measure := by
  sorry

/-- Exercise 1.1.6 (v) (finite subadditivity) -/
theorem JordanMeasurable.mes_of_union {d:ℕ} {E F : Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F)
  : (hE.union hF).measure ≤ hE.measure + hF.measure := by
  sorry

/-- Exercise 1.1.6 (v) (finite subadditivity) -/
lemma JordanMeasurable.measure_of_union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, JordanMeasurable E) :
  (JordanMeasurable.union' hE).measure ≤ ∑ E:S, (hE E.val E.property).measure := by
  sorry

open Pointwise

/-- Exercise 1.1.6 (vi) (translation invariance) -/
theorem JordanMeasurable.translate {d:ℕ} {E: Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (x: EuclideanSpace' d) : JordanMeasurable (E + {x}) := by
  sorry

/-- Exercise 1.1.6 (vi) (translation invariance) -/
lemma JordanMeasurable.measure_of_translate {d:ℕ} {E: Set (EuclideanSpace' d)}
(hE: JordanMeasurable E) (x: EuclideanSpace' d):
  (hE.translate x).measure ≤ hE.measure := by
  sorry

/-- Exercise 1.1.7 (i) (Regions under graphs are Jordan measurable) -/
lemma JordanMeasurable.graph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ} (hf: ContinuousOn f B.toSet) : JordanMeasurable { p | ∃ x ∈ B.toSet, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, f x ⟩ } := by
  sorry

/-- Exercise 1.1.7 (i) (Regions under graphs are Jordan measurable) -/
lemma JordanMeasurable.measure_of_graph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ} (hf: ContinuousOn f B.toSet) : (JordanMeasurable.graph hf).measure = 0 := by
  sorry

/-- Exercise 1.1.7 (i) (Regions under graphs are Jordan measurable) -/
lemma JordanMeasurable.undergraph {d:ℕ} {B:Box d} {f: EuclideanSpace' d → ℝ} (hf: ContinuousOn f B.toSet) : JordanMeasurable { p | ∃ x ∈ B.toSet, ∃ t:ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } := by
  sorry

/-- Exercise 1.1.8 -/
lemma JordanMeasurable.triangle (T: Affine.Triangle ℝ (EuclideanSpace' 2)) : JordanMeasurable T.closedInterior := by
  sorry

abbrev EuclideanSpace'.plane_wedge (x y: EuclideanSpace' 2) := x 1 * y 0 - x 0 * y 1

/-- Exercise 1.1.8 -/
lemma JordanMeasurable.measure_triangle (T: Affine.Triangle ℝ (EuclideanSpace' 2)) : (JordanMeasurable.triangle T).measure = |(T.points 1 - T.points 0).plane_wedge (T.points 2 - T.points 0)| / 2 := by
  sorry

/-- Exercise 1.1.9 -/

abbrev IsPolytope {d:ℕ} (P: Set (EuclideanSpace' d)) : Prop :=
  ∃ (V: Finset (EuclideanSpace' d)), P = convexHull ℝ (V.toSet)

lemma JordanMeasurable.polytope {d:ℕ} {P: Set (EuclideanSpace' d)} (hP: IsPolytope P) : JordanMeasurable P := by
  sorry

/-- Exercise 1.1.10 (1) -/
lemma JordanMeasurable.ball {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r) : JordanMeasurable (Metric.ball x₀ r) := by
  sorry

/-- Exercise 1.1.10 (1) -/
lemma JordanMeasurable.closedBall {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r) : JordanMeasurable (Metric.closedBall x₀ r) := by
  sorry


/-- Exercise 1.1.10 (1) -/
lemma JordanMeasurable.measure_ball (d:ℕ) : ∃ c, ∀ (x₀: EuclideanSpace' d) (r: ℝ) (hr: 0 < r), (ball x₀ hr).measure = c * r^d := by sorry

lemma JordanMeasurable.measure_closedBall {d:ℕ} (x₀: EuclideanSpace' d) {r: ℝ} (hr: 0 < r): (closedBall x₀ hr).measure = (ball x₀ hr).measure := by sorry

/-- Exercise 1.1.10 (2) -/
lemma JordanMeasurable.measure_ball_le (d:ℕ) : (measure_ball d).choose ≤ 2^d := by sorry

/-- Exercise 1.1.10 (2) -/
lemma JordanMeasurable.le_measure_ball (d:ℕ) : 2^d/d.factorial ≤ (measure_ball d).choose := by sorry

/-- Exercise 1.1.11 (1) -/
lemma JordanMeasurable.linear_of_elem {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
{E: Set (EuclideanSpace' d)} (hE: IsElementary E): JordanMeasurable (T '' E) := by
  sorry

/-- Exercise 1.1.11 (1) -/
lemma JordanMeasurable.measure_linear_of_elem {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d) : ∃ D > 0, ∀ (E: Set (EuclideanSpace' d)) (hE: IsElementary E), (linear_of_elem T hE).measure = D * hE.measure := by sorry

/-- Exercise 1.1.11 (2) -/
lemma JordanMeasurable.linear {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d)
{E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E): JordanMeasurable (T '' E) := by
  sorry

/-- Exercise 1.1.11 (2) -/
lemma JordanMeasurable.measure_linear {d:ℕ} (T: EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d) :
∃ D > 0, ∀ (E: Set (EuclideanSpace' d)) (hE: JordanMeasurable E), (linear T hE).measure = hE.measure := by sorry

noncomputable def Matrix.linear_equiv {d:ℕ} (A: Matrix (Fin d) (Fin d) ℝ) [Invertible A] :
EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d where
  toFun x := toLin' A x
  map_add' := LinearMap.map_add (toLin' A)
  map_smul' := LinearMap.CompatibleSMul.map_smul (toLin' A)
  invFun x := toLin' A⁻¹ x
  left_inv x := by simp
  right_inv x := by simp

/-- Exercise 1.1.11 (3) -/
lemma JordanMeasurable.measure_linear_det {d:ℕ} (A: Matrix (Fin d) (Fin d) ℝ) [Invertible A] :
(measure_linear A.linear_equiv).choose = |A.det| := by sorry

abbrev JordanMeasurable.null {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := ∃ hE: JordanMeasurable E, hE.measure = 0

lemma JordanMeasurable.null_iff {d:ℕ} {E: Set (EuclideanSpace' d)} : null E ↔ Bornology.IsBounded E ∧ Jordan_outer_measure E = 0 := by
  sorry

/-- Exercise 1.1.12 -/
lemma JordanMeasurable.null_mono {d:ℕ} {E F: Set (EuclideanSpace' d)} (h: null E) (hEF: F ⊆ E) : null F := by
  sorry

/-- Exercise 1.1.13 -/
theorem JordanMeasure.measure_eq {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E):
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥(E ∩ (Set.range (fun (n:Fin d → ℤ) i ↦ (N:ℝ)⁻¹*(n i)))))
  (nhds hE.measure) := by sorry

noncomputable abbrev Box.dyadic {d:ℕ} (n:ℤ) (i:Fin d → ℤ) : Box d where
  side j := BoundedInterval.Ico ((i j)/2^n) ((i j + 1)/2^n)

noncomputable abbrev metric_entropy_lower {d:ℕ} (E: Set (EuclideanSpace' d)) (n:ℤ) : ℕ := Nat.card { i:Fin d → ℤ | (Box.dyadic n i).toSet ⊆ E }

noncomputable abbrev metric_entropy_upper {d:ℕ} (E: Set (EuclideanSpace' d)) (n:ℤ) : ℕ := Nat.card { i:Fin d → ℤ | (Box.dyadic n i).toSet ∩ E ≠ ∅ }

/-- Exercise 1.1.14 -/
theorem JordanMeasure.iff {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  JordanMeasurable E ↔ Filter.atTop.Tendsto (fun n ↦ (2:ℝ)^(-(d*n:ℤ)) * ((metric_entropy_upper E n - metric_entropy_lower E n))) (nhds 0) := by sorry

theorem JordanMeasure.eq_lim_lower {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) :
   Filter.atTop.Tendsto (fun n ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_lower E n)) (nhds hE.measure) := by sorry

theorem JordanMeasure.eq_lim_upper {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: JordanMeasurable E) :
   Filter.atTop.Tendsto (fun n ↦ (2:ℝ)^(-(d*n:ℤ)) * (metric_entropy_upper E n)) (nhds hE.measure) := by sorry

/-- Exercise 1.1.15 (Uniqueness of Jordan measure) -/
theorem JordanMeasure.measure_uniq {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (JordanMeasurable E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (hF: JordanMeasurable F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE) : ∃ c, c ≥ 0 ∧ ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE = c * hE.measure := by
    sorry

theorem JordanMeasure.measure_uniq' {d:ℕ} {m': (E: Set (EuclideanSpace' d)) → (JordanMeasurable E) → ℝ}
  (hnonneg: ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE ≥ 0)
  (hadd: ∀ E F: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (hF: JordanMeasurable F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans: ∀ E: Set (EuclideanSpace' d), ∀ (hE: JordanMeasurable E) (x: EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE)
  (hcube : m' (Box.unit_cube d) (IsElementary.box _).jordanMeasurable = 1) :
  ∀ E: Set (EuclideanSpace' d), ∀ hE: JordanMeasurable E, m' E hE = hE.measure := by
    sorry


/-- Exercise 1.1.16 -/
theorem JordanMeasurable.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: JordanMeasurable E₁) (hE₂: JordanMeasurable E₂) : JordanMeasurable (EuclideanSpace'.prod E₁ E₂) := by sorry

theorem JordanMeasurable.measure_of_prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: JordanMeasurable E₁) (hE₂: JordanMeasurable E₂)
  : (hE₁.prod hE₂).measure = hE₁.measure * hE₂.measure := by sorry

abbrev Isometric {d:ℕ} (E F: Set (EuclideanSpace' d)) : Prop :=
 ∃ A ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∃ x₀, F = ((Matrix.toLin' A) '' E: Set (EuclideanSpace' d)) + {x₀}

/-- Exercise 1.1.17 -/
theorem JordanMeasurable.measure_of_equidecomposable {d n:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: JordanMeasurable E) (hF: JordanMeasurable F)
  {P Q: Fin n → Set (EuclideanSpace' d)} (hPQ: ∀ i, Isometric (P i) (Q i))
  (hPE: E = ⋃ i, P i) (hQF: F = ⋃ i, Q i) (hPdisj: Set.PairwiseDisjoint .univ P)
  (hQdisj: Set.PairwiseDisjoint .univ (fun i ↦ (interior (Q i)))) : hE.measure = hF.measure := by
  sorry

/-- Exercise 1.1.18 (1) -/
theorem JordanMeasurable.outer_measure_of_closure {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  Jordan_outer_measure (closure E) = Jordan_outer_measure E := by sorry

/-- Exercise 1.1.18 (2) -/
theorem JordanMeasurable.inner_measure_of_interior {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  Jordan_inner_measure (interior E) = Jordan_inner_measure E := by sorry

/-- Exercise 1.1.18 (3) -/
theorem JordanMeasurable.iff_boundary_null {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) :
  JordanMeasurable E ↔ JordanMeasurable.null (frontier E) := by sorry

abbrev bullet_riddled_square : Set (EuclideanSpace' 2) := { x | ∀ i, x i ∈ Set.Icc 0 1 ∧ x i ∉ (fun (q:ℚ) ↦ (q:ℝ)) '' .univ}

abbrev bullets : Set (EuclideanSpace' 2) := { x | ∀ i, x i ∈ Set.Icc 0 1 ∧ x i ∈ (fun (q:ℚ) ↦ (q:ℝ)) '' .univ}

theorem bullet_riddled_square.inner : Jordan_inner_measure bullet_riddled_square = 0 := by sorry

theorem bullet_riddled_square.outer : Jordan_outer_measure bullet_riddled_square = 1 := by sorry

theorem bullets.inner : Jordan_inner_measure bullets = 0 := by sorry

theorem bullets.outer : Jordan_outer_measure bullets = 1 := by sorry

theorem bullet_riddled_square.not_jordanMeasurable : ¬ JordanMeasurable bullet_riddled_square := by sorry

theorem bullets.not_jordanMeasurable : ¬ JordanMeasurable bullets := by sorry

/-- Exercise 1.1.19 (Caratheodory property) -/
theorem JordanMeasurable.caratheodory {d:ℕ} {E F: Set (EuclideanSpace' d)} (hE: Bornology.IsBounded E) (hF: IsElementary F) :
  Jordan_outer_measure E = Jordan_outer_measure (E ∩ F) + Jordan_outer_measure (E \ F) := by
  sorry
