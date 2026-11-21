import QuantitativeStochasticHomogenization.Ch04.Sec04.TestPairClosure

/-!
# The energy projection onto the test pair closure and the harmonic extension

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, p. 155: approximation of the admissible class by `a`-harmonic extensions.

For a pair `v`, the energy `B_a(v - t, v - t)` has a minimizer `P_a v` over the closed space `T₀`
of limits of mean-zero test pairs (the energy controls the gradient, and the Poincaré inequality
the mean-zero potential). The minimizer is characterized by the orthogonality of `v - P_a v` to
`T₀`, so it is unique, and `v - P_a v` is a harmonic pair whenever `v` is a gradient pair: the
`a`-harmonic extension of `v`. For a harmonic pair `F`, `‖P_a v‖² ≤ C ‖v - F‖²`, so the harmonic
extensions of pairs close to `F` are close to `F`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ} {z : Vec d} {T : ℝ}

theorem pairGradEnergy_sub_le (x y : PairSpace d z T) :
    pairGradEnergy (x - y) ≤ 2 * pairGradEnergy x + 2 * pairGradEnergy y := by
  unfold pairGradEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Prod.snd_sub, Pi.sub_apply]
  have h1 := norm_sub_le (x.2 k) (y.2 k)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖x.2 k‖ - ‖y.2 k‖)]

/-- The Poincaré constant `(2^d · 2T)²` of the ball `B_T(z)`. -/
def ballPoincareConstant (d : ℕ) (T : ℝ) : ℝ := (2 ^ d * (2 * T)) ^ 2

theorem ballPoincareConstant_nonneg (d : ℕ) (T : ℝ) : 0 ≤ ballPoincareConstant d T :=
  sq_nonneg _

theorem pairGauge_le_of_mem_testPairClosure (hT : 0 < T) {t : PairSpace d z T}
    (ht : t ∈ testPairClosure d z T) :
    pairGauge t ≤ (ballPoincareConstant d T + 1) * pairGradEnergy t := by
  have h := norm_fst_sq_le_of_isGradientPair t (IsGradientPair.of_mem_testPairClosure ht) hT
    (pairMean_eq_zero_of_mem hT ht)
  unfold pairGauge ballPoincareConstant
  nlinarith [pairGradEnergy_nonneg t]

theorem bddAbove_pairGauge_energy_sublevel (a : CoefficientField d Λ) (hT : 0 < T)
    (v : PairSpace d z T) (s : ℝ) :
    BddAbove (pairGauge '' {t | t ∈ (testPairClosure d z T : Set (PairSpace d z T)) ∧
      energyForm a (v - t) (v - t) ≤ s}) := by
  refine ⟨(ballPoincareConstant d T + 1) * (2 * pairGradEnergy v + 2 * s), ?_⟩
  rintro _ ⟨t, ⟨ht, hts⟩, rfl⟩
  have h1 : pairGradEnergy (v - t) ≤ s := (pairGradEnergy_le_energyForm a _).trans hts
  have h2 : pairGradEnergy t ≤ 2 * pairGradEnergy v + 2 * pairGradEnergy (v - t) := by
    have := pairGradEnergy_sub_le v (v - t)
    rwa [sub_sub_cancel] at this
  calc pairGauge t ≤ (ballPoincareConstant d T + 1) * pairGradEnergy t :=
        pairGauge_le_of_mem_testPairClosure hT ht
    _ ≤ (ballPoincareConstant d T + 1) * (2 * pairGradEnergy v + 2 * s) :=
        mul_le_mul_of_nonneg_left (by linarith)
          (by linarith [ballPoincareConstant_nonneg d T])

theorem continuous_energyForm_sub (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (v : PairSpace d z T) :
    Continuous fun t : PairSpace d z T => energyForm a (v - t) (v - t) := by
  exact Continuous.energyForm a hΛ (continuous_const.sub continuous_id)
    (continuous_const.sub continuous_id)

theorem energyForm_sub_smul_self (a : CoefficientField d Λ) (w u : PairSpace d z T) (s : ℝ) :
    energyForm a (w - s • u) (w - s • u) =
      energyForm a w w - 2 * s * energyForm a w u + s ^ 2 * energyForm a u u := by
  simp only [energyForm_sub_left, energyForm_sub_right, energyForm_smul_left,
    energyForm_smul_right]
  rw [energyForm_symm a u w]
  ring

theorem energyForm_sub_sub_self (a : CoefficientField d Λ) (x y : PairSpace d z T) :
    energyForm a (x - y) (x - y) = energyForm a x x - 2 * energyForm a x y + energyForm a y y := by
  have h := energyForm_sub_smul_self a x y 1
  rw [one_smul] at h
  rw [h]
  ring

/-- The energy of `v - t` is minimal at some `t ∈ T₀`. -/
theorem exists_energyProjection (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (hT : 0 < T)
    (v : PairSpace d z T) :
    ∃ t ∈ (testPairClosure d z T : Set (PairSpace d z T)),
      ∀ t' ∈ (testPairClosure d z T : Set (PairSpace d z T)),
        energyForm a (v - t) (v - t) ≤ energyForm a (v - t') (v - t') := by
  obtain ⟨t, ht, hmin, -⟩ := exists_lexicographic_minimizer isQuadraticGauge_pairGauge
    isClosed_testPairClosure ⟨0, (testPairClosure d z T).zero_mem⟩
    (continuous_energyForm_sub a hΛ v)
    ((convexOn_energyForm_sub a v).subset (Set.subset_univ _) (testPairClosure d z T).convex)
    (fun t _ => energyForm_self_nonneg a _) (g := fun _ => (0 : ℝ)) continuous_const
    (convexOn_const 0 (testPairClosure d z T).convex) (fun _ _ => le_rfl)
    (fun s => bddAbove_pairGauge_energy_sublevel a hT v s)
  exact ⟨t, ht, hmin⟩

/-- **First variation**: at a minimizer `t`, `v - t` is energy-orthogonal to `T₀`. -/
theorem energyForm_eq_zero_of_isEnergyMinimizer (a : CoefficientField d Λ) {v t : PairSpace d z T}
    (ht : t ∈ testPairClosure d z T)
    (hmin : ∀ t' ∈ (testPairClosure d z T : Set (PairSpace d z T)),
      energyForm a (v - t) (v - t) ≤ energyForm a (v - t') (v - t'))
    {u : PairSpace d z T} (hu : u ∈ testPairClosure d z T) : energyForm a (v - t) u = 0 := by
  set w := v - t
  set b := energyForm a w u
  set c := energyForm a u u
  have hc : 0 ≤ c := energyForm_self_nonneg a u
  have key : ∀ s : ℝ, 0 ≤ -2 * s * b + s ^ 2 * c := by
    intro s
    have hm := hmin (t + s • u) ((testPairClosure d z T).add_mem ht
      ((testPairClosure d z T).smul_mem s hu))
    have he : v - (t + s • u) = w - s • u := by rw [sub_add_eq_sub_sub]
    rw [he] at hm
    have hexp := energyForm_sub_smul_self a w u s
    linarith
  have hc1 : 0 < c + 1 := by linarith
  have h := key (b / (c + 1))
  have h' : 0 ≤ (-2 * (b / (c + 1)) * b + (b / (c + 1)) ^ 2 * c) * (c + 1) ^ 2 :=
    mul_nonneg h (sq_nonneg _)
  have e : (-2 * (b / (c + 1)) * b + (b / (c + 1)) ^ 2 * c) * (c + 1) ^ 2 = -(b ^ 2 * (c + 2)) := by
    field_simp
    ring
  rw [e] at h'
  have hb : b ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg b)
  exact pow_eq_zero_iff two_ne_zero |>.1 hb

/-- Uniqueness of the energy minimizer on `T₀`. -/
theorem eq_of_isEnergyMinimizer (a : CoefficientField d Λ) (hT : 0 < T) {v t₁ t₂ : PairSpace d z T}
    (ht₁ : t₁ ∈ testPairClosure d z T) (ht₂ : t₂ ∈ testPairClosure d z T)
    (h₁ : ∀ t' ∈ (testPairClosure d z T : Set (PairSpace d z T)),
      energyForm a (v - t₁) (v - t₁) ≤ energyForm a (v - t') (v - t'))
    (h₂ : ∀ t' ∈ (testPairClosure d z T : Set (PairSpace d z T)),
      energyForm a (v - t₂) (v - t₂) ≤ energyForm a (v - t') (v - t')) : t₁ = t₂ := by
  have hu : t₂ - t₁ ∈ testPairClosure d z T := (testPairClosure d z T).sub_mem ht₂ ht₁
  have o₁ := energyForm_eq_zero_of_isEnergyMinimizer a ht₁ h₁ hu
  have o₂ := energyForm_eq_zero_of_isEnergyMinimizer a ht₂ h₂ hu
  have hdiff : t₂ - t₁ = (v - t₁) - (v - t₂) := by abel
  have hE : energyForm a (t₂ - t₁) (t₂ - t₁) = 0 := by
    have : energyForm a (t₂ - t₁) (t₂ - t₁) =
        energyForm a ((v - t₁) - (v - t₂)) (t₂ - t₁) := by rw [← hdiff]
    rw [this, energyForm_sub_left, o₁, o₂, sub_zero]
  have hg : pairGradEnergy (t₂ - t₁) ≤ 0 := hE ▸ pairGradEnergy_le_energyForm a _
  have hQ := pairGauge_le_of_mem_testPairClosure hT hu
  have hQ0 : pairGauge (t₂ - t₁) ≤ 0 := by
    nlinarith [ballPoincareConstant_nonneg d T, pairGradEnergy_nonneg (t₂ - t₁)]
  have hn := isQuadraticGauge_pairGauge.norm_sq_le (t₂ - t₁)
  have : ‖t₂ - t₁‖ = 0 := by nlinarith [norm_nonneg (t₂ - t₁)]
  exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm

/-- The harmonic extension `v - P_a v` of a gradient pair is a harmonic pair. -/
theorem isHarmonicPair_sub_of_isEnergyMinimizer (a : CoefficientField d Λ)
    {v t : PairSpace d z T} (hv : IsGradientPair v) (ht : t ∈ testPairClosure d z T)
    (hmin : ∀ t' ∈ (testPairClosure d z T : Set (PairSpace d z T)),
      energyForm a (v - t) (v - t) ≤ energyForm a (v - t') (v - t')) :
    IsHarmonicPair a (v - t) :=
  ⟨hv.sub (IsGradientPair.of_mem_testPairClosure ht), fun φ hφ => by
    rw [harmConstraint_eq_energyForm]
    exact energyForm_eq_zero_of_isEnergyMinimizer a ht hmin (testPair_mem_testPairClosure hφ)⟩

/-- The energy minimizer is small when `v` is close to a harmonic pair. -/
theorem pairGauge_le_of_isEnergyMinimizer (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (hT : 0 < T)
    {v t F : PairSpace d z T} (ht : t ∈ testPairClosure d z T)
    (hmin : ∀ t' ∈ (testPairClosure d z T : Set (PairSpace d z T)),
      energyForm a (v - t) (v - t) ≤ energyForm a (v - t') (v - t'))
    (hF : IsHarmonicPair a F) :
    pairGauge t ≤ (ballPoincareConstant d T + 1) * ((d : ℝ) ^ 2 * Λ * ‖v - F‖ ^ 2) := by
  have o := energyForm_eq_zero_of_isEnergyMinimizer a ht hmin ht
  have hFt : energyForm a F t = 0 := energyForm_eq_zero_of_isHarmonicPair a hΛ hF ht
  have hvt : energyForm a (v - t) t = energyForm a v t - energyForm a t t :=
    energyForm_sub_left a v t t
  have h1 : energyForm a (v - F) t = energyForm a t t := by
    rw [energyForm_sub_left, hFt, sub_zero]
    linarith
  have h2 : 0 ≤ energyForm a ((v - F) - t) ((v - F) - t) := energyForm_self_nonneg a _
  rw [energyForm_sub_sub_self, h1] at h2
  have h3 : energyForm a t t ≤ energyForm a (v - F) (v - F) := by linarith
  have h4 : energyForm a (v - F) (v - F) ≤ (d : ℝ) ^ 2 * Λ * ‖v - F‖ ^ 2 := by
    have := (le_abs_self _).trans (abs_energyForm_le a hΛ (v - F) (v - F))
    nlinarith
  calc pairGauge t ≤ (ballPoincareConstant d T + 1) * pairGradEnergy t :=
        pairGauge_le_of_mem_testPairClosure hT ht
    _ ≤ (ballPoincareConstant d T + 1) * ((d : ℝ) ^ 2 * Λ * ‖v - F‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ((pairGradEnergy_le_energyForm a t).trans (h3.trans h4))
          (by linarith [ballPoincareConstant_nonneg d T])

end QSH
