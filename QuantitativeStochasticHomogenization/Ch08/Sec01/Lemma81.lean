import QuantitativeStochasticHomogenization.Ch08.Sec01.CaccioppoliEnergy

/-!
# Lemma 8.1: the parabolic Caccioppoli inequality

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 8.1, Lemma 8.1. For `u ∈ H¹_par(Q_{2r})` and `u* ∈ L²(I_{2r}; H⁻¹(B_{2r}))` with
`∂ₜu - ∇·(a∇u) = u*` in `Q_{2r}`,

* (8.8) `‖∇u‖_{L̲²(Q_r)} ≤ C r⁻¹ ‖u‖_{L̲²(Q_{2r})} + C ‖u*‖_{L̲²(I_{2r}; H̲⁻¹(B_{2r}))}`;
* for every `s ∈ I_r`, `‖u(s, ·)‖_{L̲²(B_r)} ≤ C ‖u‖_{L̲²(Q_{2r})} + C r ‖u*‖_{L̲²(I_{2r}; H̲⁻¹(B_{2r}))}`.

The second bound is (8.9) in the form given by the book's proof: the printed (8.9) has
`C ‖∇u‖_{L̲²(Q_{2r})}` in place of `C ‖u‖_{L̲²(Q_{2r})}` and no factor `r`, which fails for `u = 1`,
`u* = 0`. Here `u*` is written `∇·F` (every element of `L²(I; H⁻¹(B_{2r}))` has this form) and
`u(s, ·)` is the time slice of the representative of `u` which is weakly continuous in time, for
which the supremum over `s` of the book is a supremum over every `s ∈ I_r`.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

theorem volume_real_parabolicCylinder {r : ℝ} :
    volume.real (parabolicCylinder d r) = volume.real (ball (0 : Vec d) r) * r ^ 2 := by
  rw [parabolicCylinder, measureReal_def, Measure.volume_eq_prod, Measure.prod_prod,
    ENNReal.toReal_mul, Real.volume_Ioc, sub_neg_eq_add, zero_add,
    ENNReal.toReal_ofReal (sq_nonneg r)]
  rfl

theorem sqrt_mul_add_sq_le {K x y : ℝ} (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (K * (x ^ 2 + y ^ 2)) ≤ Real.sqrt K * (x + y) := by
  rw [Real.sqrt_mul hK]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  calc Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt ((x + y) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hx hy])
    _ = x + y := Real.sqrt_sq (by linarith)

/-- **Lemma 8.1 (parabolic Caccioppoli inequality).** There is `C(d, Λ)` such that for every
`r > 0`, `u ∈ H¹_par(Q_{2r})` and `u* = ∇·F ∈ L²(I_{2r}; H⁻¹(B_{2r}))` with
`∂ₜu - ∇·(a∇u) = u*` in `Q_{2r}`:
(8.8) `‖∇u‖_{L̲²(Q_r)} ≤ C r⁻¹ ‖u‖_{L̲²(Q_{2r})} + C ‖u*‖_{L̲²(I_{2r}; H̲⁻¹(B_{2r}))}`, and for
every `s ∈ I_r`, `‖u(s, ·)‖_{L̲²(B_r)} ≤ C ‖u‖_{L̲²(Q_{2r})} + C r ‖u*‖_{L̲²(I_{2r}; H̲⁻¹(B_{2r}))}`
((8.9) as given by the book's proof). -/
theorem lemma_8_1 {Λ : ℝ} (hΛ : 1 ≤ Λ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoefficientField d Λ) (r : ℝ), 0 < r →
      ∀ (u : PDE.ParH1Function (ball (0 : Vec d) (2 * r)) (Ioc (-(2 * r) ^ 2) 0))
        (F : Vec d × ℝ → Vec d),
      (∀ i, MemLp (fun z => F z i) 2 (volume.restrict (parabolicCylinder d (2 * r)))) →
      IsParabolicSolution a (ball 0 (2 * r)) (Ioc (-(2 * r) ^ 2) 0) u F →
      ENNReal.ofReal (vectorRms volume (parabolicCylinder d r) u.grad) ≤
          ENNReal.ofReal (C * r⁻¹ * scalarRms volume (parabolicCylinder d (2 * r)) u.toFun) +
            ENNReal.ofReal C *
              timeNegativeSobolevNorm (Ioc (-(2 * r) ^ 2) 0) (ball 0 (2 * r)) F ∧
        ∀ s ∈ Ioc (-r ^ 2) (0 : ℝ),
          ENNReal.ofReal (scalarRms volume (ball (0 : Vec d) r) fun x => u.toFun (x, s)) ≤
            ENNReal.ofReal (C * scalarRms volume (parabolicCylinder d (2 * r)) u.toFun) +
              ENNReal.ofReal (C * r) *
                timeNegativeSobolevNorm (Ioc (-(2 * r) ^ 2) 0) (ball 0 (2 * r)) F := by
  obtain ⟨CE, hCE, hE⟩ := parabolicCaccioppoli_energy (d := d) hΛ hd
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 2 ^ (d + 2) * CE := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKdef]; positivity
  refine ⟨Real.sqrt K, Real.sqrt_pos.2 hK, ?_⟩
  intro a r hr u F hF hu
  have h2r : 0 < 2 * r := by linarith
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  -- volumes
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal := ⟨_, rfl⟩
  have hω : 0 < ω := hωdef ▸ PDE.volume_euclideanBall_toReal_pos 0 one_pos
  have hVr : volume.real (ball (0 : Vec d) r) = r ^ d * ω := by
    rw [measureReal_def, ball_eq_euclideanBall 0 hr, hωdef]
    exact PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos 0 hr
  have hV2 : volume.real (ball (0 : Vec d) (2 * r)) = (2 * r) ^ d * ω := by
    rw [measureReal_def, ball_eq_euclideanBall 0 h2r, hωdef]
    exact PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos 0 h2r
  have hQr : volume.real (parabolicCylinder d r) = r ^ d * ω * r ^ 2 := by
    rw [volume_real_parabolicCylinder, hVr]
  have hQ2 : volume.real (parabolicCylinder d (2 * r)) = (2 * r) ^ d * ω * (2 * r) ^ 2 := by
    rw [volume_real_parabolicCylinder, hV2]
  -- the norm of the right-hand side
  obtain ⟨L, hL⟩ : ∃ L, L = ∫⁻ τ in Ioc (-(2 * r) ^ 2) 0,
      negativeSobolevOneNorm 2 (ball (0 : Vec d) (2 * r)) (fun _ => 0) (fun x => F (x, τ)) ^ 2 :=
    ⟨_, rfl⟩
  have hN : timeNegativeSobolevNorm (Ioc (-(2 * r) ^ 2) 0) (ball (0 : Vec d) (2 * r)) F =
      ((volume (Ioc (-(2 * r) ^ 2) (0 : ℝ)))⁻¹ * L) ^ (1 / 2 : ℝ) := by
    rw [hL]
    rfl
  have hI : volume (Ioc (-(2 * r) ^ 2) (0 : ℝ)) = ENNReal.ofReal ((2 * r) ^ 2) := by
    rw [Real.volume_Ioc, sub_neg_eq_add, zero_add]
  by_cases hLtop : L = ⊤
  · have hNtop : timeNegativeSobolevNorm (Ioc (-(2 * r) ^ 2) 0) (ball (0 : Vec d) (2 * r)) F =
        ⊤ := by
      rw [hN, hLtop, hI, ENNReal.mul_top (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top),
        ENNReal.top_rpow_of_pos (by norm_num)]
    rw [hNtop]
    refine ⟨?_, fun s _ => ?_⟩
    · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hK)).ne', add_top]
      exact le_top
    · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 (mul_pos (Real.sqrt_pos.2 hK) hr)).ne', add_top]
      exact le_top
  obtain ⟨Lr, hLr⟩ : ∃ Lr, Lr = L.toReal := ⟨_, rfl⟩
  have hLeq : L = ENNReal.ofReal Lr := by rw [hLr, ENNReal.ofReal_toReal hLtop]
  have hLr0 : 0 ≤ Lr := hLr ▸ ENNReal.toReal_nonneg
  obtain ⟨ν, hν⟩ : ∃ ν, ν = Real.sqrt (Lr / (2 * r) ^ 2) := ⟨_, rfl⟩
  have hν0 : 0 ≤ ν := hν ▸ Real.sqrt_nonneg _
  have hν2 : ν ^ 2 = Lr / (2 * r) ^ 2 := by rw [hν, Real.sq_sqrt (by positivity)]
  have hNν : timeNegativeSobolevNorm (Ioc (-(2 * r) ^ 2) 0) (ball (0 : Vec d) (2 * r)) F =
      ENNReal.ofReal ν := by
    rw [hN, hI, hLeq, ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul
      (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), hν,
      Real.sqrt_eq_rpow, inv_mul_eq_div]
  -- the energy inequality in real form
  obtain ⟨S₂, hS₂⟩ : ∃ S₂, S₂ = ∫ z in parabolicCylinder d (2 * r), u.toFun z ^ 2 := ⟨_, rfl⟩
  have hS₂0 : 0 ≤ S₂ := hS₂ ▸ integral_nonneg fun z => sq_nonneg _
  have hreal : ∀ t ∈ Ioc (-r ^ 2) (0 : ℝ),
      (∫ x in ball (0 : Vec d) r, u.toFun (x, t) ^ 2) +
          (∫ z in ball (0 : Vec d) r ×ˢ Ioc (-r ^ 2) t, euclideanSq (u.grad z)) ≤
        CE * (r ^ 2)⁻¹ * S₂ + CE * volume.real (ball (0 : Vec d) (2 * r)) * Lr := by
    intro t ht
    have h := hE a r hr u F hF hu t ht
    rw [← hL, ← hS₂, hLeq, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  -- normalized quantities
  obtain ⟨m, hm⟩ : ∃ m, m = (volume.real (parabolicCylinder d (2 * r)))⁻¹ * S₂ := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := hm ▸ mul_nonneg (inv_nonneg.2 measureReal_nonneg) hS₂0
  have hsm : scalarRms volume (parabolicCylinder d (2 * r)) u.toFun = Real.sqrt m := by
    rw [scalarRms, setAverage_eq, smul_eq_mul, hm, hS₂]
  refine ⟨?_, fun s hs => ?_⟩
  · -- (8.8)
    obtain ⟨B, hB⟩ : ∃ B, B = ∫ z in parabolicCylinder d r, euclideanSq (u.grad z) := ⟨_, rfl⟩
    have hA0 : 0 ≤ ∫ x in ball (0 : Vec d) r, u.toFun (x, 0) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    have h0 := hreal 0 ⟨by linarith, le_rfl⟩
    have hB' : B ≤ CE * (r ^ 2)⁻¹ * S₂ + CE * volume.real (ball (0 : Vec d) (2 * r)) * Lr := by
      rw [hB]
      exact (le_add_of_nonneg_left hA0).trans h0
    have hvr : vectorRms volume (parabolicCylinder d r) u.grad =
        Real.sqrt ((volume.real (parabolicCylinder d r))⁻¹ * B) := by
      rw [vectorRms, setAverage_eq, smul_eq_mul, hB]
    have hclaim : (volume.real (parabolicCylinder d r))⁻¹ * B ≤
        K * ((r⁻¹ * Real.sqrt m) ^ 2 + ν ^ 2) := by
      have hQr0 : 0 < volume.real (parabolicCylinder d r) := by rw [hQr]; positivity
      have h1 := mul_le_mul_of_nonneg_left hB' (inv_nonneg.2 hQr0.le)
      refine h1.trans (le_of_eq ?_)
      rw [mul_pow, Real.sq_sqrt hm0, hν2, hm, hQr, hQ2, hV2, hKdef]
      field_simp
      ring
    rw [hvr, hNν, hsm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.sqrt ((volume.real (parabolicCylinder d r))⁻¹ * B)
        ≤ Real.sqrt (K * ((r⁻¹ * Real.sqrt m) ^ 2 + ν ^ 2)) := Real.sqrt_le_sqrt hclaim
      _ ≤ Real.sqrt K * (r⁻¹ * Real.sqrt m + ν) :=
          sqrt_mul_add_sq_le hK.le (by positivity) hν0
      _ = Real.sqrt K * r⁻¹ * Real.sqrt m + Real.sqrt K * ν := by ring
  · -- (8.9), in the form given by the proof
    obtain ⟨A, hA⟩ : ∃ A, A = ∫ x in ball (0 : Vec d) r, u.toFun (x, s) ^ 2 := ⟨_, rfl⟩
    have hB0 : 0 ≤ ∫ z in ball (0 : Vec d) r ×ˢ Ioc (-r ^ 2) s, euclideanSq (u.grad z) :=
      integral_nonneg fun z => by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hA' : A ≤ CE * (r ^ 2)⁻¹ * S₂ + CE * volume.real (ball (0 : Vec d) (2 * r)) * Lr := by
      rw [hA]
      exact (le_add_of_nonneg_right hB0).trans (hreal s hs)
    have hsr : scalarRms volume (ball (0 : Vec d) r) (fun x => u.toFun (x, s)) =
        Real.sqrt ((volume.real (ball (0 : Vec d) r))⁻¹ * A) := by
      rw [scalarRms, setAverage_eq, smul_eq_mul, hA]
    have hclaim : (volume.real (ball (0 : Vec d) r))⁻¹ * A ≤
        K * (Real.sqrt m ^ 2 + (r * ν) ^ 2) := by
      have hVr0 : 0 < volume.real (ball (0 : Vec d) r) := by rw [hVr]; positivity
      have h1 := mul_le_mul_of_nonneg_left hA' (inv_nonneg.2 hVr0.le)
      refine h1.trans (le_of_eq ?_)
      rw [mul_pow, Real.sq_sqrt hm0, hν2, hm, hVr, hQ2, hV2, hKdef]
      field_simp
      ring
    rw [hsr, hNν, hsm, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.sqrt ((volume.real (ball (0 : Vec d) r))⁻¹ * A)
        ≤ Real.sqrt (K * (Real.sqrt m ^ 2 + (r * ν) ^ 2)) := Real.sqrt_le_sqrt hclaim
      _ ≤ Real.sqrt K * (Real.sqrt m + r * ν) :=
          sqrt_mul_add_sq_le hK.le (Real.sqrt_nonneg _) (by positivity)
      _ = Real.sqrt K * Real.sqrt m + Real.sqrt K * r * ν := by ring

end QSH
