import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximation
import QuantitativeStochasticHomogenization.Ch03.Sec03.ScalarRmsCalculus

/-!
# One step of the quadratic excess decay from (2) and the harmonic expansion

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.3, the derivation of (3) in the first-order proof of Theorem 3.8 for `k = 1`. Let `v`
be an element of `A₁` minus a corrected affine function, with `‖v‖_{L̲²(E_R)} = X`, and let `h`
be the `B`-harmonic approximation of (2) on `E_b`, `b = (1 - 3η)R`, `η = R^{-ν₂}`. With the
first-order part `ℓ₁ = c₁ + p₁ · x` of `h` and `t = R/2`,
`‖h - ℓ₁‖_{L̲²(E_t)} ≤ (t/b)² ‖h‖_{L̲²(E_b)} ≤ ¼ (R/b)^{d+2} X + O(η) X`, and replacing `ℓ₁` by
its corrected version `c₁ - ∑ p₁ᵢ mᵢ + p₁ · x + ∑ p₁ᵢ φᵢ` costs `O(R^{-μ}) X` by the sublinearity
of the correctors on the ball `B_{Lt} ⊇ E_t`. Since `R/b ≤ 1 + 6η`, the factor is
`¼ (1 + C R^{-ν})` with `ν = min ν₂ μ`.
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The radius factor `L = (∑ M_{ij}²)^{1/2} + 1` with `M B_R ⊆ B_{LR}`. -/
def ellipsoidRadius (M : Mat d) : ℝ := Real.sqrt (∑ i, ∑ j, M i j ^ 2) + 1

theorem one_le_ellipsoidRadius (M : Mat d) : 1 ≤ ellipsoidRadius M := by
  unfold ellipsoidRadius
  linarith [Real.sqrt_nonneg (∑ i, ∑ j, M i j ^ 2)]

theorem matrixEllipsoid_subset_ball (M : Mat d) (R : ℝ) :
    matrixEllipsoid M R ⊆ ball 0 (ellipsoidRadius M * R) := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : euclideanNorm (y - 0) < R := hy
  rw [sub_zero] at hy'
  change euclideanNorm (Matrix.toLin' M y - 0) < ellipsoidRadius M * R
  rw [sub_zero, Matrix.toLin'_apply]
  have h1 := euclideanNorm_mulVec_le M y
  have h2 : 0 ≤ euclideanNorm y := Real.sqrt_nonneg _
  have h3 : 0 ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) := Real.sqrt_nonneg _
  unfold ellipsoidRadius
  nlinarith

theorem volume_real_ball_le_matrixEllipsoid {M : Mat d} (hdet : M.det ≠ 0) (R : ℝ) :
    volume.real (ball (0 : Vec d) (ellipsoidRadius M * R)) ≤
      ellipsoidRadius M ^ d / |M.det| * volume.real (matrixEllipsoid M R) := by
  have hL : 0 < ellipsoidRadius M := lt_of_lt_of_le one_pos (one_le_ellipsoidRadius M)
  have hdet0 : 0 < |M.det| := abs_pos.2 hdet
  apply le_of_eq
  simp only [measureReal_def, volume_matrixEllipsoid, volume_ball_zero_mul hL,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ellipsoidRadius M ^ d)]
  field_simp

theorem memLp_dot_ball (p : Vec d) (R : ℝ) :
    MemLp (fun x => dot p x) 2 (volume.restrict (ball (0 : Vec d) R)) := by
  have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.2 (volume_ball_zero_lt_top R).ne
  have hcont : Continuous fun x : Vec d => dot p x := by unfold dot; fun_prop
  refine MemLp.of_bound hcont.aestronglyMeasurable ((∑ i, |p i|) * |R|) ?_
  filter_upwards [ae_restrict_mem (isOpen_ball_zero R).measurableSet] with x hx
  have hx' : euclideanNorm (x - 0) < R := hx
  rw [sub_zero] at hx'
  rw [Real.norm_eq_abs]
  unfold dot
  calc |∑ i, p i * x i| ≤ ∑ i, |p i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |p i| * |R| := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          ((coordinate_abs_le_euclideanNorm x i).trans (hx'.le.trans (le_abs_self R)))
          (abs_nonneg _)
    _ = (∑ i, |p i|) * |R| := by rw [Finset.sum_mul]

theorem memLp_correctedAffineOf_ball {Λ μ C₁ R₀ : ℝ} {a : CoefficientField d Λ} {D : Mat d}
    (F : SublinearCorrectorFamily a D μ C₁ R₀) (c : ℝ) (p : Vec d) {R : ℝ} (hR : 0 < R) :
    MemLp (correctedAffineOf F.φ c p) 2 (volume.restrict (ball (0 : Vec d) R)) := by
  have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.2 (volume_ball_zero_lt_top R).ne
  show MemLp (fun x => c + dot p x + ∑ i, p i * F.φ i x) 2 _
  exact ((memLp_const c).add (memLp_dot_ball p R)).add
    (memLp_finsetSum _ fun i _ => (F.memLp i R hR).1.const_mul (p i))

/-- The triangle inequality in the form `‖g‖ ≤ ‖f‖ + ‖f - g‖`. -/
theorem scalarRms_le_add_sub {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hfg : MemLp (fun x => f x - g x) 2 (volume.restrict U)) :
    scalarRms volume U g ≤ scalarRms volume U f + scalarRms volume U (fun x => f x - g x) := by
  have h := scalarRms_sub_le hf hfg
  have e : (fun x => f x - (f x - g x)) = g := by
    funext x
    ring
  rw [e] at h
  exact h

/-- The arithmetic of the quarter step. -/
theorem quarter_step_arith {X H T1 T2 T3 η ρ r s C₂ K₃ : ℝ} (n : ℕ)
    (hX : 0 ≤ X) (hC₂ : 0 ≤ C₂) (hK₃ : 0 ≤ K₃) (hη0 : 0 ≤ η) (hη6 : η ≤ 1 / 6) (hρ1 : 1 ≤ ρ)
    (hρη : ρ ≤ 1 + 6 * η) (hr : 0 ≤ r) (hηs : η ≤ s) (hrs : r ≤ s)
    (hT1 : T1 ≤ 2 ^ n * C₂ * (η * X)) (hH : H ≤ ρ ^ n * X + C₂ * (η * X))
    (hT2 : T2 ≤ (ρ / 2) ^ 2 * H) (hT3 : T3 ≤ K₃ * r * H) :
    T1 + T2 + T3 ≤ 1 / 4 * (1 + 4 * (6 * ((2 : ℝ) ^ (n + 2) - 1) / 4 + C₂ + 2 ^ n * C₂ +
      K₃ * (2 ^ n + C₂)) * s) * X := by
  have hρ2 : ρ ≤ 2 := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hρn : ρ ^ n ≤ 2 ^ n := pow_le_pow_left₀ hρ0 hρ2 n
  have hρn2 : ρ ^ (n + 2) ≤ 1 + ((2 : ℝ) ^ (n + 2) - 1) * (6 * η) :=
    (pow_le_pow_left₀ hρ0 hρη (n + 2)).trans (one_add_pow_le (by positivity) (by linarith) (n + 2))
  have hρsq : ρ ^ 2 ≤ 4 := by nlinarith
  have hηX : 0 ≤ η * X := mul_nonneg hη0 hX
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h2n2 : (1 : ℝ) ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
  have hH0' : H ≤ (2 ^ n + C₂) * X := by
    have : C₂ * (η * X) ≤ C₂ * X := mul_le_mul_of_nonneg_left (by nlinarith) hC₂
    nlinarith [mul_le_mul_of_nonneg_right hρn hX]
  have hT2' : T2 ≤ 1 / 4 * X + (6 * ((2 : ℝ) ^ (n + 2) - 1) / 4 + C₂) * (η * X) := by
    have hq : 0 ≤ (ρ / 2) ^ 2 := by positivity
    calc T2 ≤ (ρ / 2) ^ 2 * H := hT2
      _ ≤ (ρ / 2) ^ 2 * (ρ ^ n * X + C₂ * (η * X)) := mul_le_mul_of_nonneg_left hH hq
      _ = 1 / 4 * (ρ ^ (n + 2) * X) + 1 / 4 * ρ ^ 2 * (C₂ * (η * X)) := by ring
      _ ≤ 1 / 4 * ((1 + ((2 : ℝ) ^ (n + 2) - 1) * (6 * η)) * X) + 1 / 4 * 4 * (C₂ * (η * X)) := by
          have e1 := mul_le_mul_of_nonneg_right hρn2 hX
          have e2 := mul_le_mul_of_nonneg_right hρsq (mul_nonneg hC₂ hηX)
          nlinarith
      _ = 1 / 4 * X + (6 * ((2 : ℝ) ^ (n + 2) - 1) / 4 + C₂) * (η * X) := by ring
  have hT3' : T3 ≤ K₃ * (2 ^ n + C₂) * (r * X) := by
    calc T3 ≤ K₃ * r * H := hT3
      _ ≤ K₃ * r * ((2 ^ n + C₂) * X) := mul_le_mul_of_nonneg_left hH0' (mul_nonneg hK₃ hr)
      _ = K₃ * (2 ^ n + C₂) * (r * X) := by ring
  have hc1 : 0 ≤ 2 ^ n * C₂ := by positivity
  have hc2 : 0 ≤ 6 * ((2 : ℝ) ^ (n + 2) - 1) / 4 + C₂ := by
    have : 0 ≤ 6 * ((2 : ℝ) ^ (n + 2) - 1) / 4 := by
      apply div_nonneg _ (by norm_num)
      nlinarith
    linarith
  have hc3 : 0 ≤ K₃ * (2 ^ n + C₂) := by positivity
  have hηsX : η * X ≤ s * X := mul_le_mul_of_nonneg_right hηs hX
  have hrsX : r * X ≤ s * X := mul_le_mul_of_nonneg_right hrs hX
  have e1 := mul_le_mul_of_nonneg_left hηsX hc1
  have e2 := mul_le_mul_of_nonneg_left hηsX hc2
  have e3 := mul_le_mul_of_nonneg_left hrsX hc3
  nlinarith

/-- **(3) from (2) and the harmonic expansion.** -/
theorem quarterExcessStep_of_harmonicApproximation (h2 : harmonicApproximationStatement)
    (hH : harmonicExpansionStatement) : quarterExcessStepStatement := by
  intro d hd Λ μ C₁ hΛ hμ hμ' hC₁ D hD
  obtain ⟨M, hdet, hMM, CH, hCH, hexp⟩ := hH d hd D hD
  obtain ⟨C₂', ν₂, hν₂, happ⟩ := h2 d hd Λ μ C₁ hΛ hμ hμ' hC₁ D M hD hdet hMM
  obtain ⟨C₂, hC₂def⟩ : ∃ C₂ : ℝ, C₂ = max C₂' 0 := ⟨_, rfl⟩
  have hC₂ : 0 ≤ C₂ := hC₂def ▸ le_max_right _ _
  have hC₂' : C₂' ≤ C₂ := hC₂def ▸ le_max_left _ _
  obtain ⟨ν, hνdef⟩ : ∃ ν : ℝ, ν = min ν₂ μ := ⟨_, rfl⟩
  have hν : 0 < ν := hνdef ▸ lt_min hν₂ hμ
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = ellipsoidRadius M := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := hLdef ▸ one_le_ellipsoidRadius M
  have hL : 0 < L := by linarith
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = L ^ d / |M.det| := ⟨_, rfl⟩
  have hκ : 0 ≤ κ := by rw [hκdef]; exact div_nonneg (pow_nonneg hL.le d) (abs_nonneg _)
  obtain ⟨K₃, hK₃def⟩ : ∃ K₃ : ℝ, K₃ = 2 * Real.sqrt κ * d * C₁ * L * CH := ⟨_, rfl⟩
  have hK₃ : 0 ≤ K₃ := by
    rw [hK₃def]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two
      (Real.sqrt_nonneg _)) (Nat.cast_nonneg d)) hC₁) hL.le) hCH
  refine ⟨M, 4 * (6 * ((2 : ℝ) ^ (d + 2) - 1) / 4 + C₂ + 2 ^ d * C₂ + K₃ * (2 ^ d + C₂)), ν,
    hdet, hMM, hν, fun R₀ hR₀ => ?_⟩
  obtain ⟨R₂, hR₀₂, happR⟩ := happ R₀ hR₀
  refine ⟨max R₂ (max ((7 : ℝ) ^ (1 / ν₂)) (2 * R₀)), le_trans hR₀₂ (le_max_left _ _),
    fun a F w R hR c p => ?_⟩
  have hR2 : R₂ ≤ R := le_trans (le_max_left _ _) hR
  have hR6 : (7 : ℝ) ^ (1 / ν₂) ≤ R :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hRR₀ : 2 * R₀ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  obtain ⟨h, hhar, hvh⟩ := happR a F w R hR2 c p
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = (1 - 3 * R ^ (-ν₂)) * R := ⟨_, rfl⟩
  rw [← hbdef] at hhar hvh
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = R ^ (-ν₂) := ⟨_, rfl⟩
  rw [← hηdef] at hvh hbdef
  have hη0 : 0 < η := hηdef ▸ Real.rpow_pos_of_pos hR0 _
  have hη7 : η ≤ 1 / 7 := by
    have h1 : (7 : ℝ) ≤ R ^ ν₂ := by
      have h := Real.rpow_le_rpow (by positivity) hR6 hν₂.le
      rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hν₂.ne', Real.rpow_one] at h
    rw [hηdef, Real.rpow_neg hR0.le, one_div]
    exact inv_anti₀ (by norm_num) h1
  have hη6 : η ≤ 1 / 6 := by linarith
  have hb2 : R / 2 ≤ b := by
    have : 0 ≤ (1 / 2 - 3 * η) * R := mul_nonneg (by linarith) hR0.le
    rw [hbdef]
    linarith
  have hbR : b ≤ R := by
    have : 0 ≤ η * R := mul_nonneg hη0.le hR0.le
    rw [hbdef]
    linarith
  have hb2' : R / 2 < b := by
    have : 0 < (1 / 2 - 3 * η) * R := mul_pos (by linarith) hR0
    rw [hbdef]
    linarith
  have hb0 : 0 < b := by linarith
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = R / 2 := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; linarith
  have htb : t ≤ b := htdef ▸ hb2
  have htb' : t < b := htdef ▸ hb2'
  have htR : t ≤ R := by rw [htdef]; linarith
  have hLt : R₀ ≤ L * t := by
    have h1 : t ≤ L * t := le_mul_of_one_le_left ht0.le hL1
    have h2 : R₀ ≤ t := by rw [htdef]; linarith
    linarith
  obtain ⟨v, hvdef⟩ : ∃ v : Vec d → ℝ, v = fun x => w.potential x - correctedAffineOf F.φ c p x :=
    ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = scalarRms volume (matrixEllipsoid M R) v := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := hXdef ▸ scalarRms_nonneg _ _
  have hvh' : scalarRms volume (matrixEllipsoid M b) (fun x => v x - h x) ≤ C₂ * (η * X) := by
    have e : (fun x => v x - h x) =
        fun x => w.potential x - correctedAffineOf F.φ c p x - h x := by
      rw [hvdef]
    rw [e, hXdef, hvdef]
    refine hvh.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hC₂' (mul_nonneg hη0.le (hvdef ▸ hXdef ▸ hX0))
  have hhL2 : MemLp h 2 (volume.restrict (matrixEllipsoid M b)) := hhar.1
  obtain ⟨c₁, p₁, hdec, hp₁⟩ := hexp b hb0 h hhar
  obtain ⟨m, hmdef⟩ : ∃ m : Fin d → ℝ, m = fun i => ⨍ y in ball 0 (L * t), F.φ i y := ⟨_, rfl⟩
  refine ⟨c₁ - ∑ i, p₁ i * m i, p₁, ?_⟩
  rw [← htdef, show (scalarRms volume (matrixEllipsoid M R) fun x =>
    w.potential x - correctedAffineOf F.φ c p x) = X by rw [hXdef, hvdef]]
  -- square integrability
  have hsubR : matrixEllipsoid M R ⊆ ball 0 (L * R) := hLdef ▸ matrixEllipsoid_subset_ball M R
  have hvR : MemLp v 2 (volume.restrict (matrixEllipsoid M R)) := by
    rw [hvdef]
    exact ((w.local_energy (L * R) (mul_pos hL hR0)).1.sub
      (memLp_correctedAffineOf_ball F c p (mul_pos hL hR0))).mono_measure
      (Measure.restrict_mono hsubR le_rfl)
  have hbsub : matrixEllipsoid M b ⊆ matrixEllipsoid M R := matrixEllipsoid_mono M hbR
  have htsub : matrixEllipsoid M t ⊆ matrixEllipsoid M b := matrixEllipsoid_mono M htb
  have htball : matrixEllipsoid M t ⊆ ball 0 (L * t) := hLdef ▸ matrixEllipsoid_subset_ball M t
  have hvb : MemLp v 2 (volume.restrict (matrixEllipsoid M b)) :=
    hvR.mono_measure (Measure.restrict_mono hbsub le_rfl)
  have hvhb : MemLp (fun x => v x - h x) 2 (volume.restrict (matrixEllipsoid M b)) := hvb.sub hhL2
  have hfinLt : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) (L * t))) :=
    isFiniteMeasure_restrict.2 (volume_ball_zero_lt_top _).ne
  have hℓ₁ : MemLp (fun x => c₁ + dot p₁ x) 2 (volume.restrict (matrixEllipsoid M t)) :=
    ((memLp_const c₁).add (memLp_dot_ball p₁ (L * t))).mono_measure
      (Measure.restrict_mono htball le_rfl)
  have hht : MemLp (fun x => h x - (c₁ + dot p₁ x)) 2 (volume.restrict (matrixEllipsoid M t)) :=
    (hhL2.mono_measure (Measure.restrict_mono htsub le_rfl)).sub hℓ₁
  have hvht : MemLp (fun x => v x - h x) 2 (volume.restrict (matrixEllipsoid M t)) :=
    hvhb.mono_measure (Measure.restrict_mono htsub le_rfl)
  have hφball : ∀ i, MemLp (fun x => F.φ i x - m i) 2
      (volume.restrict (ball (0 : Vec d) (L * t))) := fun i =>
    (F.memLp i (L * t) (mul_pos hL ht0)).1.sub (memLp_const _)
  have hsumt : MemLp (fun x => ∑ i, p₁ i * (F.φ i x - m i)) 2
      (volume.restrict (matrixEllipsoid M t)) :=
    (memLp_finsetSum _ fun i _ => (hφball i).const_mul (p₁ i)).mono_measure
      (Measure.restrict_mono htball le_rfl)
  have hsum2 : MemLp (fun x => (v x - h x) + (h x - (c₁ + dot p₁ x))) 2
      (volume.restrict (matrixEllipsoid M t)) := hvht.add hht
  -- the decomposition
  have hdecomp : (fun x => w.potential x -
      correctedAffineOf F.φ (c + (c₁ - ∑ i, p₁ i * m i)) (p + p₁) x) =
      fun x => ((v x - h x) + (h x - (c₁ + dot p₁ x))) - ∑ i, p₁ i * (F.φ i x - m i) := by
    funext x
    rw [hvdef]
    simp only [correctedAffineOf, dot, Pi.add_apply, add_mul, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hdecomp]
  have hT : scalarRms volume (matrixEllipsoid M t)
      (fun x => ((v x - h x) + (h x - (c₁ + dot p₁ x))) - ∑ i, p₁ i * (F.φ i x - m i)) ≤
      scalarRms volume (matrixEllipsoid M t) (fun x => v x - h x) +
        scalarRms volume (matrixEllipsoid M t) (fun x => h x - (c₁ + dot p₁ x)) +
        scalarRms volume (matrixEllipsoid M t) (fun x => ∑ i, p₁ i * (F.φ i x - m i)) := by
    have h1 := scalarRms_sub_le hsum2 hsumt
    have h2 := scalarRms_add_le hvht hht
    linarith
  -- first term
  have hT1 : scalarRms volume (matrixEllipsoid M t) (fun x => v x - h x) ≤
      2 ^ d * C₂ * (η * X) := by
    have h1 := scalarRms_matrixEllipsoid_le hdet ht0 htb hvhb
    have hbt : b / t ≤ 2 := by rw [div_le_iff₀ ht0, htdef]; linarith
    have h2 : (b / t) ^ d ≤ 2 ^ d := pow_le_pow_left₀ (div_nonneg hb0.le ht0.le) hbt d
    calc _ ≤ (b / t) ^ d * scalarRms volume (matrixEllipsoid M b) (fun x => v x - h x) := h1
      _ ≤ 2 ^ d * (C₂ * (η * X)) :=
          mul_le_mul h2 hvh' (scalarRms_nonneg _ _) (by positivity)
      _ = 2 ^ d * C₂ * (η * X) := by ring
  -- the ratio `R / b`
  have hρ1 : 1 ≤ R / b := by rw [le_div_iff₀ hb0]; linarith
  have hρη : R / b ≤ 1 + 6 * η := by
    have h1 : 0 ≤ 3 * η * (1 - 6 * η) * R :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hR0.le
    rw [div_le_iff₀ hb0, hbdef]
    linarith
  have hHb : scalarRms volume (matrixEllipsoid M b) h ≤ (R / b) ^ d * X + C₂ * (η * X) := by
    have h1 := scalarRms_le_add_sub hvb hvhb
    have h3 := scalarRms_matrixEllipsoid_le hdet hb0 hbR hvR
    rw [← hXdef] at h3
    linarith
  have hT2 : scalarRms volume (matrixEllipsoid M t) (fun x => h x - (c₁ + dot p₁ x)) ≤
      (R / b / 2) ^ 2 * scalarRms volume (matrixEllipsoid M b) h := by
    have h1 := hdec t ht0 htb'
    have e : t / b = R / b / 2 := by rw [htdef]; ring
    rwa [e] at h1
  -- third term
  have hT3 : scalarRms volume (matrixEllipsoid M t) (fun x => ∑ i, p₁ i * (F.φ i x - m i)) ≤
      K₃ * R ^ (-μ) * scalarRms volume (matrixEllipsoid M b) h := by
    have hballt : MemLp (fun x => ∑ i, p₁ i * (F.φ i x - m i)) 2
        (volume.restrict (ball (0 : Vec d) (L * t))) :=
      memLp_finsetSum _ fun i _ => (hφball i).const_mul (p₁ i)
    have hvolt : volume.real (ball (0 : Vec d) (L * t)) ≤ κ * volume.real (matrixEllipsoid M t) := by
      rw [hκdef, hLdef]
      exact volume_real_ball_le_matrixEllipsoid hdet t
    have h1 := scalarRms_le_sqrt_mul_of_subset htball (volume_matrixEllipsoid_ne_zero hdet ht0)
      (volume_ball_zero_lt_top _).ne hvolt hκ hballt.integrable_sq
    have h2 := scalarRms_finset_sum_le Finset.univ hφball p₁
    have hosc : ∀ i, scalarRms volume (ball 0 (L * t)) (fun x => F.φ i x - m i) ≤
        C₁ * (L * t) ^ (1 - μ) := by
      intro i
      have h := F.oscillation i (L * t) hLt
      have hnn : 0 ≤ ∑ j, ∑ k, scalarRms volume (ball 0 (L * t))
          (fun x => F.σ i x j k - ⨍ y in ball 0 (L * t), F.σ i y j k) :=
        Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => scalarRms_nonneg _ _
      have e : scalarRms volume (ball 0 (L * t)) (fun x => F.φ i x - m i) =
          scalarRms volume (ball 0 (L * t)) (fun x => F.φ i x - ⨍ y in ball 0 (L * t), F.φ i y) := by
        rw [hmdef]
      rw [e]
      linarith
    have hpow : (L * t) ^ (1 - μ) ≤ L * R ^ (1 - μ) := by
      have hLR : (L * t) ^ (1 - μ) ≤ (L * R) ^ (1 - μ) :=
        Real.rpow_le_rpow (mul_pos hL ht0).le (mul_le_mul_of_nonneg_left htR hL.le) (by linarith)
      rw [Real.mul_rpow hL.le hR0.le] at hLR
      have hL' : L ^ (1 - μ) ≤ L := by
        have := Real.rpow_le_rpow_of_exponent_le hL1 (show 1 - μ ≤ 1 by linarith)
        rwa [Real.rpow_one] at this
      exact hLR.trans (mul_le_mul_of_nonneg_right hL' (Real.rpow_nonneg hR0.le _))
    have hsum : ∑ i, |p₁ i| * scalarRms volume (ball 0 (L * t)) (fun x => F.φ i x - m i) ≤
        d * euclideanNorm p₁ * (C₁ * (L * R ^ (1 - μ))) := by
      calc _ ≤ ∑ _i : Fin d, euclideanNorm p₁ * (C₁ * (L * R ^ (1 - μ))) :=
            Finset.sum_le_sum fun i _ => mul_le_mul (coordinate_abs_le_euclideanNorm p₁ i)
              ((hosc i).trans (mul_le_mul_of_nonneg_left hpow hC₁)) (scalarRms_nonneg _ _)
              (Real.sqrt_nonneg _)
        _ = d * euclideanNorm p₁ * (C₁ * (L * R ^ (1 - μ))) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have hH0 : 0 ≤ scalarRms volume (matrixEllipsoid M b) h := scalarRms_nonneg _ _
    have hp₁' : euclideanNorm p₁ ≤ 2 * CH / R * scalarRms volume (matrixEllipsoid M b) h := by
      refine hp₁.trans (mul_le_mul_of_nonneg_right ?_ hH0)
      rw [div_le_div_iff₀ hb0 hR0]
      have h1 : R ≤ 2 * b := by linarith
      calc CH * R ≤ CH * (2 * b) := mul_le_mul_of_nonneg_left h1 hCH
        _ = 2 * CH * b := by ring
    have hRμ : R ^ (1 - μ) = R * R ^ (-μ) := by
      rw [Real.rpow_sub hR0, Real.rpow_one, Real.rpow_neg hR0.le]
      field_simp
    have hsq : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg _
    have hA : 0 ≤ C₁ * (L * R ^ (1 - μ)) :=
      mul_nonneg hC₁ (mul_nonneg hL.le (Real.rpow_nonneg hR0.le _))
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc _ ≤ Real.sqrt κ * scalarRms volume (ball 0 (L * t))
            (fun x => ∑ i, p₁ i * (F.φ i x - m i)) := h1
      _ ≤ Real.sqrt κ * (d * euclideanNorm p₁ * (C₁ * (L * R ^ (1 - μ)))) :=
          mul_le_mul_of_nonneg_left (h2.trans hsum) hsq
      _ ≤ Real.sqrt κ * (d * (2 * CH / R * scalarRms volume (matrixEllipsoid M b) h) *
            (C₁ * (L * R ^ (1 - μ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hsq
          refine mul_le_mul_of_nonneg_right ?_ hA
          exact mul_le_mul_of_nonneg_left hp₁' hd0
      _ = K₃ * R ^ (-μ) * scalarRms volume (matrixEllipsoid M b) h := by
          rw [hRμ, hK₃def]
          field_simp
  have hηs : η ≤ R ^ (-ν) := by
    rw [hηdef]
    exact Real.rpow_le_rpow_of_exponent_le hR1
      (by rw [hνdef, neg_le_neg_iff]; exact min_le_left _ _)
  have hrs : R ^ (-μ) ≤ R ^ (-ν) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by rw [hνdef, neg_le_neg_iff]; exact min_le_right _ _)
  exact hT.trans (quarter_step_arith d hX0 hC₂ hK₃ hη0.le hη6 hρ1 hρη
    (Real.rpow_nonneg hR0.le _) hηs hrs hT1 hHb hT2 hT3)

end QSH
