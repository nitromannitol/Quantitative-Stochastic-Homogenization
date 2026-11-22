import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicApproximationCore
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicExpansionBallProof

/-!
# Proof of the harmonic approximation (2) and the first-order Liouville theorem

`harmonicApproximation` proves `harmonicApproximationStatement` with `ν = μ/(d + 2)`: at the scale
`R`, with `η = R^{-ν} ≤ 1/8`, the one-scale harmonic approximation is applied to
`v = w - ℓ_{c,p}` and to the correctors recentred at their means on the ball `B_{LR} ⊇ E_R`, whose
`L²` norms are at most `|B_{LR}|^{1/2} C₁ (LR)^{1-μ}`. The error is
`ε = K₁ η ‖v‖_{L²(E_R)} + K₂ R^{-μ} η^{-d-1} ‖v‖_{L²(E_R)}`, and `R^{-μ} η^{-d-1} = η`. Dividing by
`|E_b|^{1/2}` with `|E_R| ≤ 2^d |E_b|` gives the normalized estimate. With the harmonic expansion,
`firstOrderLiouville` proves Theorem 3.8 for `k = 1` without hypotheses.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ}

theorem HasWeakGradient.sub_const {f : Vec d → ℝ} {g : Vec d → Vec d}
    (h : HasWeakGradient Set.univ f g) (c : ℝ) :
    HasWeakGradient Set.univ (fun x => f x - c) g := by
  have h2 := hasWeakGradient_add h (hasWeakGradient_const (-c))
  have e1 : (fun x => f x + -c) = fun x => f x - c := by funext x; ring
  have e2 : (fun x => g x + (0 : Vec d)) = g := by funext x; simp
  rw [e1, e2] at h2
  exact h2

theorem HasWeakDivergence.sub_const_field {F : Vec d → Vec d} {f : Vec d → ℝ}
    (h : HasWeakDivergence Set.univ F f) (c : Vec d) :
    HasWeakDivergence Set.univ (fun x => F x - c) f := by
  have h2 := hasWeakDivergence_add h (hasWeakDivergence_const_field (-c))
  have e1 : (fun x => F x + -c) = fun x => F x - c := by funext x; abel
  have e2 : (fun x => f x + (0 : ℝ)) = f := by funext x; simp
  rw [e1, e2] at h2
  exact h2

theorem memLp_component {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemLp g 2 (volume.restrict U)) (l : Fin d) :
    MemLp (fun x => g x l) 2 (volume.restrict U) :=
  hg.of_le ((continuous_apply l).comp_aestronglyMeasurable hg.aestronglyMeasurable)
    (Eventually.of_forall fun x => norm_le_pi_norm (g x) l)

theorem memLp_coordinate_ball (R : ℝ) (i : Fin d) :
    MemLp (fun x : Vec d => x i) 2 (volume.restrict (ball (0 : Vec d) R)) := by
  refine (memLp_dot_ball (unitVector i) R).ae_eq (Eventually.of_forall fun x => ?_)
  exact dot_unitVector_left i x

theorem integral_sq_le_of_scalarRms_le {B : Set (Vec d)} {f : Vec d → ℝ} {T : ℝ}
    (hB : 0 < volume.real B) (h : scalarRms volume B f ≤ T) :
    ∫ x in B, f x ^ 2 ≤ volume.real B * T ^ 2 := by
  have hA : 0 ≤ ⨍ x in B, f x ^ 2 := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 measureReal_nonneg) (integral_nonneg fun x => sq_nonneg _)
  have h2 : ⨍ x in B, f x ^ 2 ≤ T ^ 2 := by
    have h' := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rwa [Real.sq_sqrt hA] at h'
  rw [setAverage_eq, smul_eq_mul] at h2
  calc ∫ x in B, f x ^ 2 = volume.real B * ((volume.real B)⁻¹ * ∫ x in B, f x ^ 2) := by
        rw [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
    _ ≤ volume.real B * T ^ 2 := mul_le_mul_of_nonneg_left h2 hB.le

theorem sqrt_pow_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg x) n), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt hx]

/-- `R^{1-μ} / (R η^{d+1}) = η` for `η = R^{-ν}`, `ν (d + 2) = μ`. -/
theorem rpow_div_mul_pow_eq {R μ : ℝ} (hR : 0 < R) :
    R ^ (1 - μ) / (R * (R ^ (-(μ / (d + 2)))) ^ (d + 1)) = R ^ (-(μ / (d + 2))) := by
  have hd2 : (d : ℝ) + 2 ≠ 0 := by positivity
  set η := R ^ (-(μ / (d + 2))) with hηdef
  have hη : 0 < η := Real.rpow_pos_of_pos hR _
  have h1 : η ^ (d + 2) = R ^ (-μ) := by
    rw [hηdef, ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 1
    push_cast
    field_simp
  have h2 : R ^ (1 - μ) = R * η ^ (d + 2) := by
    rw [h1, sub_eq_add_neg, Real.rpow_add hR, Real.rpow_one]
  rw [h2, pow_succ]
  field_simp

/-- The error of the one-scale approximation in closed form. -/
theorem harmonicApproximation_error_eq {η R L μ V CK Kc N2 C₁ fM det nM Q : ℝ} (n : ℕ)
    (hη : 0 < η) (hR : 0 < R) (hL : 0 < L) (hV : 0 ≤ V) (hKc : 0 ≤ Kc) (hdet : 0 < det) :
    n * (η ^ 2 * R) * (Real.sqrt (fM / det) * (Real.sqrt (Kc * N2) / (η * R))) +
        det⁻¹ * nM ^ 2 * (Q * (Real.sqrt (V * (L * R) ^ n) * (C₁ * (L * R) ^ (1 - μ))) *
          (Real.sqrt (Kc * N2) / (η * R))) * Real.sqrt ((η ^ 2 * R)⁻¹ ^ n * CK) =
      (n * Real.sqrt (fM / det) * Real.sqrt Kc * η +
        det⁻¹ * nM ^ 2 * Q * Real.sqrt V * Real.sqrt (L ^ n) * C₁ * L ^ (1 - μ) *
          Real.sqrt Kc * Real.sqrt CK * (R ^ (1 - μ) / (R * η ^ (n + 1)))) * Real.sqrt N2 := by
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have e1 : Real.sqrt (Kc * N2) = Real.sqrt Kc * Real.sqrt N2 := Real.sqrt_mul hKc _
  have e2 : Real.sqrt (V * (L * R) ^ n) = Real.sqrt V * Real.sqrt (L ^ n) * Real.sqrt R ^ n := by
    rw [Real.sqrt_mul hV, mul_pow, Real.sqrt_mul (pow_nonneg hL.le n), sqrt_pow_eq hR.le]
    ring
  have e3 : (L * R) ^ (1 - μ) = L ^ (1 - μ) * R ^ (1 - μ) := Real.mul_rpow hL.le hR.le
  have e4 : Real.sqrt ((η ^ 2 * R)⁻¹ ^ n * CK) = (η ^ n * Real.sqrt R ^ n)⁻¹ * Real.sqrt CK := by
    rw [Real.sqrt_mul (pow_nonneg (inv_nonneg.2 (by positivity)) n), inv_pow, Real.sqrt_inv,
      sqrt_pow_eq (by positivity), Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη.le, mul_pow]
  rw [e1, e2, e3, e4]
  field_simp
  ring

theorem volume_real_ball_le_two_pow {R b : ℝ} (hb : 0 < b) (hbR : R ≤ 2 * b) (hR : 0 < R) :
    volume.real (ball (0 : Vec d) R) ≤ 2 ^ d * volume.real (ball (0 : Vec d) b) := by
  have hq : 0 < R / b := div_pos hR hb
  have h := volume_ball_zero_mul (d := d) hq b
  rw [div_mul_cancel₀ R hb.ne'] at h
  rw [measureReal_def, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← measureReal_def]
  refine mul_le_mul_of_nonneg_right ?_ measureReal_nonneg
  exact pow_le_pow_left₀ hq.le ((div_le_iff₀ hb).2 (by linarith)) d

/-- **The harmonic approximation (2)** of the first-order proof of Theorem 3.8, `k = 1`. -/
theorem harmonicApproximation : harmonicApproximationStatement := by
  intro d hd Λ μ C₁ hΛ hμ hμ' hC₁ D M hD hdet hMM
  have hd0 : 0 < d := by omega
  obtain ⟨CK, hCK0, hCK⟩ := exists_harmonicKernelScaled_le (d := d)
  have hν : 0 < μ / (d + 2) := by positivity
  set L := ellipsoidRadius M with hLdef
  have hL1 : 1 ≤ L := one_le_ellipsoidRadius M
  have hL0 : 0 < L := by linarith
  set det := |M.det| with hdetdef
  have hdet0 : 0 < det := abs_pos.2 hdet
  set V := volume.real (ball (0 : Vec d) 1) with hVdef
  have hV : 0 ≤ V := measureReal_nonneg
  set fM := entrySqSum M with hfMdef
  set Kc := ellipsoidCaccioppoliConst Λ M with hKcdef
  have hKc : 0 ≤ Kc := by
    rw [hKcdef, ellipsoidCaccioppoliConst]
    have : (0 : ℝ) ≤ Λ := by linarith
    positivity
  set nM := inverseEntrySum M with hnMdef
  set Q : ℝ := (d : ℝ) ^ 3 + (d : ℝ) ^ 2 * Real.sqrt d * Λ with hQdef
  set K1 := (d : ℝ) * Real.sqrt (fM / det) * Real.sqrt Kc with hK1def
  set K2 := det⁻¹ * nM ^ 2 * Q * Real.sqrt V * Real.sqrt (L ^ d) * C₁ * L ^ (1 - μ) *
    Real.sqrt Kc * Real.sqrt CK with hK2def
  refine ⟨(K1 + K2) * Real.sqrt (det * 2 ^ d), μ / (d + 2), hν, fun R₀ hR₀ => ?_⟩
  refine ⟨max R₀ ((8 : ℝ) ^ (1 / (μ / (d + 2)))), le_max_left _ _, fun a F w R hR c p => ?_⟩
  have hR0 : 0 < R := by linarith [le_max_left R₀ ((8 : ℝ) ^ (1 / (μ / (d + 2))))]
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = R ^ (-(μ / (d + 2))) := ⟨_, rfl⟩
  rw [← hηdef]
  have hη : 0 < η := by rw [hηdef]; exact Real.rpow_pos_of_pos hR0 _
  have hη8 : η ≤ 1 / 8 := by
    have h8 : (8 : ℝ) ^ (1 / (μ / (d + 2))) ≤ R := le_trans (le_max_right _ _) hR
    have h8' : (8 : ℝ) ≤ R ^ (μ / (d + 2)) := by
      calc (8 : ℝ) = ((8 : ℝ) ^ (1 / (μ / (d + 2)))) ^ (μ / (d + 2)) := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hν.ne', Real.rpow_one]
        _ ≤ R ^ (μ / (d + 2)) := Real.rpow_le_rpow (by positivity) h8 hν.le
    rw [hηdef, Real.rpow_neg hR0.le, one_div]
    exact inv_anti₀ (by norm_num) h8'
  have hLR0 : 0 < L * R := by positivity
  have hLR : R₀ ≤ L * R :=
    (le_trans (le_max_left _ _) hR).trans (le_mul_of_one_le_left hR0.le hL1)
  -- the residual
  set v : Vec d → ℝ := fun x => w.potential x - correctedAffineOf F.φ c p x with hvdef
  set gv := residualGrad F w p with hgvdef
  have hER : matrixEllipsoid M R ⊆ ball 0 (L * R) := matrixEllipsoid_subset_ball M R
  have hv : MemLp v 2 (volume.restrict (matrixEllipsoid M R)) :=
    memLp_mono_set (memLp_residual_ball F w c p hLR0) hER
  have hgφB : ∀ k l, MemLp (fun x => F.gφ k x l) 2 (volume.restrict (ball (0 : Vec d) (L * R))) :=
    fun k l => memLp_component (F.memLp k (L * R) hLR0).2.1 l
  have hgv : ∀ i, MemLp (fun x => gv x i) 2 (volume.restrict (matrixEllipsoid M R)) := by
    intro i
    have hw : MemLp (fun x => w.grad x i) 2 (volume.restrict (ball (0 : Vec d) (L * R))) := by
      refine memLp_grad_component_of_norm (w.local_energy (L * R) hLR0).2 ?_
      have h := (w.weak_gradient i).2.1.aestronglyMeasurable
      rw [Measure.restrict_univ] at h
      exact h.restrict
    have hs := memLp_finsetSum (Finset.univ : Finset (Fin d)) fun k _ => (hgφB k i).const_mul (p k)
    have hall := hw.add (((memLp_const (p i)).add hs).const_mul (-1))
    refine memLp_mono_set (hall.ae_eq (Eventually.of_forall fun x => ?_)) hER
    simp [hgvdef, residualGrad, Finset.sum_apply]
    ring
  -- centred correctors
  set B := ball (0 : Vec d) (L * R) with hBdef
  set m : Fin d → ℝ := fun i => ⨍ y in B, F.φ i y with hmdef
  set mσ : Fin d → Mat d := fun i j k => ⨍ y in B, F.σ i y j k with hmσdef
  set φ' : Fin d → Vec d → ℝ := fun i x => F.φ i x - m i with hφ'def
  set σ' : Fin d → Vec d → Mat d := fun i x j k => F.σ i x j k - mσ i j k with hσ'def
  have hr'R : (1 - η) * R ≤ R := by
    have := mul_pos hη hR0
    linarith
  have hE' : matrixEllipsoid M ((1 - η) * R) ⊆ B := (matrixEllipsoid_mono M hr'R).trans hER
  have hφB : ∀ i, MemLp (φ' i) 2 (volume.restrict B) := fun i =>
    (F.memLp i (L * R) hLR0).1.sub (memLp_const (m i))
  have hσB : ∀ i j k, MemLp (fun x => σ' i x j k) 2 (volume.restrict B) := fun i j k =>
    ((F.memLp i (L * R) hLR0).2.2 j k).1.sub (memLp_const (mσ i j k))
  have hwφ' : ∀ i, HasWeakGradient Set.univ (φ' i) (F.gφ i) := fun i =>
    (F.weak_gradient_φ i).sub_const (m i)
  have hwc' : ∀ i, HasWeakGradient Set.univ (fun x => x i + φ' i x)
      (fun x => unitVector i + F.gφ i x) := by
    intro i
    have h := hasWeakGradient_add (hasWeakGradient_dot (unitVector i)) (hwφ' i)
    have e : (fun x => dot (unitVector i) x + φ' i x) = fun x => x i + φ' i x := by
      funext x
      rw [dot_unitVector_left]
    rw [e] at h
    exact h
  have hmskew : ∀ i j k, mσ i j k = -mσ i k j := by
    intro i j k
    simp only [hmσdef, setAverage_eq, smul_eq_mul]
    rw [← mul_neg, ← integral_neg]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun y => F.skew i y j k)
  have hskew' : ∀ i x j k, σ' i x j k = -σ' i x k j := by
    intro i x j k
    simp only [hσ'def]
    rw [F.skew i x j k, hmskew i j k]
    ring
  have hflux' : ∀ i j, HasWeakDivergence Set.univ (fun x k => σ' i x j k)
      (fun x => (a x).mulVec (unitVector i + F.gφ i x) j - D.mulVec (unitVector i) j) := by
    intro i j
    exact (F.flux i j).sub_const_field (fun k => mσ i j k)
  -- the oscillation bounds
  set O := Real.sqrt (V * (L * R) ^ d) * (C₁ * (L * R) ^ (1 - μ)) with hOdef
  have hO0 : 0 ≤ O := by positivity
  have hvolB : volume.real B = V * (L * R) ^ d := by
    have h := volume_ball_zero_mul (d := d) hLR0 1
    rw [mul_one] at h
    rw [hBdef, measureReal_def, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      hVdef, measureReal_def]
    ring
  have hvolB0 : 0 < volume.real B := by
    rw [hBdef, measureReal_def]
    exact ENNReal.toReal_pos (volume_ball_zero_pos hLR0).ne' (volume_ball_zero_lt_top _).ne
  have hOsq : volume.real B * (C₁ * (L * R) ^ (1 - μ)) ^ 2 = O ^ 2 := by
    rw [hOdef, mul_pow (Real.sqrt (V * (L * R) ^ d)), Real.sq_sqrt (mul_nonneg hV (by positivity)),
      hvolB]
  have hrmsnn : ∀ f : Vec d → ℝ, 0 ≤ scalarRms volume B f := fun f => Real.sqrt_nonneg _
  have hOφ : ∀ i, ∫ x in matrixEllipsoid M ((1 - η) * R), φ' i x ^ 2 ≤ O ^ 2 := by
    intro i
    have hosc := F.oscillation i (L * R) hLR
    have hsum : 0 ≤ ∑ j, ∑ k, scalarRms volume (ball 0 (L * R))
        (fun x => F.σ i x j k - ⨍ y in ball 0 (L * R), F.σ i y j k) :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hrmsnn _
    have hrms : scalarRms volume B (φ' i) ≤ C₁ * (L * R) ^ (1 - μ) := by
      change scalarRms volume (ball 0 (L * R)) (fun x => F.φ i x - ⨍ y in ball 0 (L * R), F.φ i y) ≤ _
      linarith
    calc ∫ x in matrixEllipsoid M ((1 - η) * R), φ' i x ^ 2 ≤ ∫ x in B, φ' i x ^ 2 :=
          setIntegral_mono_set (hφB i).integrable_sq (Eventually.of_forall fun x => sq_nonneg _)
            (Eventually.of_forall hE')
      _ ≤ volume.real B * (C₁ * (L * R) ^ (1 - μ)) ^ 2 := integral_sq_le_of_scalarRms_le hvolB0 hrms
      _ = O ^ 2 := hOsq
  have hOσ : ∀ i j k, ∫ x in matrixEllipsoid M ((1 - η) * R), σ' i x j k ^ 2 ≤ O ^ 2 := by
    intro i j k
    have hosc := F.oscillation i (L * R) hLR
    have h1 : scalarRms volume (ball 0 (L * R))
        (fun x => F.σ i x j k - ⨍ y in ball 0 (L * R), F.σ i y j k) ≤
        ∑ j, ∑ k, scalarRms volume (ball 0 (L * R))
          (fun x => F.σ i x j k - ⨍ y in ball 0 (L * R), F.σ i y j k) := by
      refine (Finset.single_le_sum (f := fun k => scalarRms volume (ball 0 (L * R))
        (fun x => F.σ i x j k - ⨍ y in ball 0 (L * R), F.σ i y j k))
        (fun k _ => hrmsnn _) (Finset.mem_univ k)).trans ?_
      exact Finset.single_le_sum (f := fun j => ∑ k, scalarRms volume (ball 0 (L * R))
        (fun x => F.σ i x j k - ⨍ y in ball 0 (L * R), F.σ i y j k))
        (fun j _ => Finset.sum_nonneg fun k _ => hrmsnn _) (Finset.mem_univ j)
    have hrms : scalarRms volume B (fun x => σ' i x j k) ≤ C₁ * (L * R) ^ (1 - μ) := by
      change scalarRms volume (ball 0 (L * R))
        (fun x => F.σ i x j k - ⨍ y in ball 0 (L * R), F.σ i y j k) ≤ _
      linarith [hrmsnn (fun x => F.φ i x - ⨍ y in ball 0 (L * R), F.φ i y)]
    calc ∫ x in matrixEllipsoid M ((1 - η) * R), σ' i x j k ^ 2 ≤ ∫ x in B, σ' i x j k ^ 2 :=
          setIntegral_mono_set (hσB i j k).integrable_sq (Eventually.of_forall fun x => sq_nonneg _)
            (Eventually.of_forall hE')
      _ ≤ volume.real B * (C₁ * (L * R) ^ (1 - μ)) ^ 2 := integral_sq_le_of_scalarRms_le hvolB0 hrms
      _ = O ^ 2 := hOsq
  -- the one-scale approximation
  obtain ⟨h, hharm, hsq⟩ := exists_harmonic_ball_sq_le hd0 hΛ a hdet hMM hCK0 hCK hR0 hη hη8 hv hgv
    (hasWeakGradient_residual F w c p) (hasWeakDivergence_residual F w p) (φ := φ') (gφ := F.gφ)
    (fun i => memLp_mono_set (hφB i) hE') (fun i l => memLp_mono_set (hgφB i l) hE') hwφ'
    (fun i => memLp_mono_set ((memLp_coordinate_ball (L * R) i).add (hφB i)) hE')
    (fun i l => memLp_mono_set ((memLp_const (unitVector i l)).add (hgφB i l)) hE') hwc'
    F.harmonic (σ := σ') (gσ := F.gσ) (fun i j k => memLp_mono_set (hσB i j k) hE')
    (fun i j k l => memLp_mono_set (memLp_component ((F.memLp i (L * R) hLR0).2.2 j k).2 l) hE')
    (fun i j k => (F.weak_gradient_σ i j k).sub_const (mσ i j k)) hskew' hflux' hO0 hOφ hOσ
  refine ⟨h, hharm, ?_⟩
  -- the error in closed form
  have hN2 : 0 ≤ ∫ x in matrixEllipsoid M R, v x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hε : ∫ y in ball 0 ((1 - 3 * η) * R), (v (M.mulVec y) - h (M.mulVec y)) ^ 2 ≤
      ((K1 + K2) * η) ^ 2 * ∫ x in matrixEllipsoid M R, v x ^ 2 := by
    refine hsq.trans (le_of_eq ?_)
    have e := harmonicApproximation_error_eq (η := η) (R := R) (L := L) (μ := μ) (V := V)
      (CK := CK) (Kc := Kc) (N2 := ∫ x in matrixEllipsoid M R, v x ^ 2) (C₁ := C₁) (fM := fM)
      (det := det) (nM := nM) (Q := Q) d hη hR0 hL0 hV hKc hdet0
    have e2 := rpow_div_mul_pow_eq (d := d) (μ := μ) hR0
    rw [← hηdef] at e2
    rw [e2] at e
    show (↑d * (η ^ 2 * R) * (Real.sqrt (fM / det) *
        (Real.sqrt (Kc * ∫ x in matrixEllipsoid M R, v x ^ 2) / (η * R))) +
      det⁻¹ * nM ^ 2 * (Q * (Real.sqrt (V * (L * R) ^ d) * (C₁ * (L * R) ^ (1 - μ))) *
        (Real.sqrt (Kc * ∫ x in matrixEllipsoid M R, v x ^ 2) / (η * R))) *
          Real.sqrt ((η ^ 2 * R)⁻¹ ^ d * CK)) ^ 2 = _
    rw [e, ← hK1def, ← hK2def, mul_pow, Real.sq_sqrt hN2]
    ring
  -- normalization
  set b := (1 - 3 * η) * R with hbdef
  have hb0 : 0 < b := by rw [hbdef]; exact mul_pos (by linarith) hR0
  have hbR : R ≤ 2 * b := by
    have : (0 : ℝ) ≤ (1 - 6 * η) * R := mul_nonneg (by linarith) hR0.le
    rw [hbdef]
    linarith
  set A := ∫ y in ball 0 b, (v (M.mulVec y) - h (M.mulVec y)) ^ 2 with hAdef
  set I := ∫ y in ball 0 R, v (M.mulVec y) ^ 2 with hIdef
  have hI : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  have hcv : ∫ x in matrixEllipsoid M R, v x ^ 2 = det * I :=
    setIntegral_matrixEllipsoid hdet R (fun x => v x ^ 2)
  rw [hcv] at hε
  set Vb := volume.real (ball (0 : Vec d) b) with hVbdef
  set VR := volume.real (ball (0 : Vec d) R) with hVRdef
  have hVb : 0 < Vb := by
    rw [hVbdef, measureReal_def]
    exact ENNReal.toReal_pos (volume_ball_zero_pos hb0).ne' (volume_ball_zero_lt_top _).ne
  have hVR : 0 < VR := by
    rw [hVRdef, measureReal_def]
    exact ENNReal.toReal_pos (volume_ball_zero_pos hR0).ne' (volume_ball_zero_lt_top _).ne
  have hVRb : VR ≤ 2 ^ d * Vb := volume_real_ball_le_two_pow hb0 hbR hR0
  have hlhs : scalarRms volume (matrixEllipsoid M b) (fun x => v x - h x) =
      Real.sqrt (Vb⁻¹ * A) := by
    rw [scalarRms_matrixEllipsoid_eq hdet b, scalarRms, setAverage_eq, smul_eq_mul]
  have hrhs : scalarRms volume (matrixEllipsoid M R) v = Real.sqrt (VR⁻¹ * I) := by
    rw [scalarRms_matrixEllipsoid_eq hdet R, scalarRms, setAverage_eq, smul_eq_mul]
  change scalarRms volume (matrixEllipsoid M b) (fun x => v x - h x) ≤
    (K1 + K2) * Real.sqrt (det * 2 ^ d) * η * scalarRms volume (matrixEllipsoid M R) v
  rw [hlhs, hrhs]
  have hK1 : 0 ≤ K1 := by rw [hK1def]; positivity
  have hQ : 0 ≤ Q := by rw [hQdef]; have : (0 : ℝ) ≤ Λ := by linarith
                        positivity
  have hnM : 0 ≤ nM ^ 2 := sq_nonneg _
  have hK2 : 0 ≤ K2 := by
    rw [hK2def]
    have : 0 ≤ L ^ (1 - μ) := Real.rpow_nonneg hL0.le _
    positivity
  have hK : 0 ≤ K1 + K2 := add_nonneg hK1 hK2
  have hineq : Vb⁻¹ * A ≤
      ((K1 + K2) * Real.sqrt (det * 2 ^ d) * η * Real.sqrt (VR⁻¹ * I)) ^ 2 := by
    have hsq2 : ((K1 + K2) * Real.sqrt (det * 2 ^ d) * η * Real.sqrt (VR⁻¹ * I)) ^ 2 =
        ((K1 + K2) * η) ^ 2 * det * 2 ^ d * (VR⁻¹ * I) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      ring
    rw [hsq2]
    have hinv : Vb⁻¹ ≤ 2 ^ d * VR⁻¹ := by
      have h1 : (2 ^ d * Vb)⁻¹ ≤ VR⁻¹ := inv_anti₀ hVR hVRb
      have h2 : Vb⁻¹ = 2 ^ d * (2 ^ d * Vb)⁻¹ := by
        field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    calc Vb⁻¹ * A ≤ Vb⁻¹ * (((K1 + K2) * η) ^ 2 * (det * I)) :=
          mul_le_mul_of_nonneg_left hε (inv_nonneg.2 hVb.le)
      _ ≤ 2 ^ d * VR⁻¹ * (((K1 + K2) * η) ^ 2 * (det * I)) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = ((K1 + K2) * η) ^ 2 * det * 2 ^ d * (VR⁻¹ * I) := by ring
  calc Real.sqrt (Vb⁻¹ * A)
      ≤ Real.sqrt (((K1 + K2) * Real.sqrt (det * 2 ^ d) * η * Real.sqrt (VR⁻¹ * I)) ^ 2) :=
        Real.sqrt_le_sqrt hineq
    _ = (K1 + K2) * Real.sqrt (det * 2 ^ d) * η * Real.sqrt (VR⁻¹ * I) :=
        Real.sqrt_sq (by positivity)

/-- **Theorem 3.8 for `k = 1`**: every element of `A₁` is a corrected affine function. -/
theorem firstOrderLiouville : firstOrderLiouvilleStatement :=
  firstOrderLiouville_of_harmonicApproximation_only harmonicApproximation

end QSH
