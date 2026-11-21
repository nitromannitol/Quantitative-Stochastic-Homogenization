import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizedEnergyMeasurability

/-!
# The energy form of a coefficient field on the pair space

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, p. 155. The bilinear form `B_a(F, F') = ∫_{B_T(z)} F'_g · a F_g` on the gradient
components of pairs, as a sum of weighted pairings: bilinear, symmetric, bounded, bounded below by
the gradient energy, continuous, and measurable in `a` for the local σ-algebra. The weak
harmonicity constraint of a pair is its energy pairing with the test pairs.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace QSH

variable {d : ℕ} {μ : Measure (Vec d)}

/-! ## Bilinearity of the weighted pairings -/

section Pairing

variable {ρ : Vec d → ℝ} {M : ℝ}

theorem weightedPairing_add_left (hρ : AEStronglyMeasurable ρ μ) (hM : ∀ᵐ x ∂μ, |ρ x| ≤ M)
    (u u' v : Lp ℝ 2 μ) :
    weightedPairing μ ρ (u + u') v = weightedPairing μ ρ u v + weightedPairing μ ρ u' v := by
  unfold weightedPairing
  rw [← integral_add (integrable_weighted hρ hM u v) (integrable_weighted hρ hM u' v)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add u u'] with x hx
  rw [hx, Pi.add_apply]; ring

theorem weightedPairing_add_right (hρ : AEStronglyMeasurable ρ μ) (hM : ∀ᵐ x ∂μ, |ρ x| ≤ M)
    (u v v' : Lp ℝ 2 μ) :
    weightedPairing μ ρ u (v + v') = weightedPairing μ ρ u v + weightedPairing μ ρ u v' := by
  unfold weightedPairing
  rw [← integral_add (integrable_weighted hρ hM u v) (integrable_weighted hρ hM u v')]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add v v'] with x hx
  rw [hx, Pi.add_apply]; ring

theorem weightedPairing_smul_left (c : ℝ) (u v : Lp ℝ 2 μ) :
    weightedPairing μ ρ (c • u) v = c * weightedPairing μ ρ u v := by
  unfold weightedPairing
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c u] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul]; ring

theorem weightedPairing_smul_right (c : ℝ) (u v : Lp ℝ 2 μ) :
    weightedPairing μ ρ u (c • v) = c * weightedPairing μ ρ u v := by
  unfold weightedPairing
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c v] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul]; ring

theorem weightedPairing_zero_left (v : Lp ℝ 2 μ) : weightedPairing μ ρ 0 v = 0 := by
  have h := weightedPairing_smul_left (ρ := ρ) (0 : ℝ) (0 : Lp ℝ 2 μ) v
  simpa using h

theorem abs_weightedPairing_le (hρ : AEStronglyMeasurable ρ μ) (hM0 : 0 ≤ M)
    (hM : ∀ᵐ x ∂μ, |ρ x| ≤ M) (u v : Lp ℝ 2 μ) :
    |weightedPairing μ ρ u v| ≤ M * (‖u‖ * ‖v‖) := by
  have h := abs_weightedPairing_sub_le hρ hM0 hM u v 0 0
  rw [weightedPairing_zero_left, sub_zero, sub_zero, sub_zero, norm_zero, zero_mul,
    add_zero] at h
  exact h

end Pairing

/-! ## The energy form -/

variable {Λ : ℝ} {z : Vec d} {T : ℝ}

/-- The energy form `B_a(F, F') = ∑_{k,l} ∫_{B_T(z)} a_{kl} F_{g,l} F'_{g,k}`. -/
def energyForm (a : CoefficientField d Λ) (F F' : PairSpace d z T) : ℝ :=
  ∑ k, ∑ l, weightedPairing (ballMeasure z T) (fun x => a x k l) (F.2 l) (F'.2 k)

theorem aestronglyMeasurable_coefficient_ball (a : CoefficientField d Λ) (k l : Fin d) :
    AEStronglyMeasurable (fun x => a x k l) (ballMeasure z T) :=
  a.aestronglyMeasurable_apply k l _ Measure.restrict_le_self.absolutelyContinuous

theorem coefficient_bound (a : CoefficientField d Λ) (k l : Fin d) :
    ∀ᵐ x ∂ballMeasure z T, |a x k l| ≤ Λ :=
  Eventually.of_forall fun x => a.abs_apply_le x k l

theorem energyForm_add_left (a : CoefficientField d Λ) (F F' H : PairSpace d z T) :
    energyForm a (F + F') H = energyForm a F H + energyForm a F' H := by
  simp only [energyForm, Prod.snd_add, Pi.add_apply,
    weightedPairing_add_left (aestronglyMeasurable_coefficient_ball a _ _)
      (coefficient_bound a _ _), Finset.sum_add_distrib]

theorem energyForm_add_right (a : CoefficientField d Λ) (F H H' : PairSpace d z T) :
    energyForm a F (H + H') = energyForm a F H + energyForm a F H' := by
  simp only [energyForm, Prod.snd_add, Pi.add_apply,
    weightedPairing_add_right (aestronglyMeasurable_coefficient_ball a _ _)
      (coefficient_bound a _ _), Finset.sum_add_distrib]

theorem energyForm_smul_left (a : CoefficientField d Λ) (c : ℝ) (F H : PairSpace d z T) :
    energyForm a (c • F) H = c * energyForm a F H := by
  simp only [energyForm, Prod.smul_snd, Pi.smul_apply, weightedPairing_smul_left, Finset.mul_sum]

theorem energyForm_smul_right (a : CoefficientField d Λ) (c : ℝ) (F H : PairSpace d z T) :
    energyForm a F (c • H) = c * energyForm a F H := by
  simp only [energyForm, Prod.smul_snd, Pi.smul_apply, weightedPairing_smul_right, Finset.mul_sum]

theorem energyForm_sub_left (a : CoefficientField d Λ) (F F' H : PairSpace d z T) :
    energyForm a (F - F') H = energyForm a F H - energyForm a F' H := by
  rw [sub_eq_add_neg, energyForm_add_left, ← neg_one_smul ℝ F', energyForm_smul_left]; ring

theorem energyForm_sub_right (a : CoefficientField d Λ) (F H H' : PairSpace d z T) :
    energyForm a F (H - H') = energyForm a F H - energyForm a F H' := by
  rw [sub_eq_add_neg, energyForm_add_right, ← neg_one_smul ℝ H', energyForm_smul_right]; ring

theorem energyForm_symm (a : CoefficientField d Λ) (F H : PairSpace d z T) :
    energyForm a F H = energyForm a H F := by
  unfold energyForm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  unfold weightedPairing
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hs : a x l k = a x k l := by
    have h := congrFun (congrFun (a.symmetric x) k) l
    simpa [Matrix.transpose_apply] using h
  simp only [hs]
  ring

theorem abs_energyForm_le (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) (F H : PairSpace d z T) :
    |energyForm a F H| ≤ (d : ℝ) ^ 2 * Λ * (‖F‖ * ‖H‖) := by
  unfold energyForm
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k l : Fin d, |weightedPairing (ballMeasure z T) (fun x => a x k l) (F.2 l) (H.2 k)|
      ≤ Λ * (‖F‖ * ‖H‖) := by
    intro k l
    refine (abs_weightedPairing_le (aestronglyMeasurable_coefficient_ball a k l) hΛ
      (coefficient_bound a k l) _ _).trans (mul_le_mul_of_nonneg_left ?_ hΛ)
    have h1 : ‖F.2 l‖ ≤ ‖F‖ := (norm_le_pi_norm F.2 l).trans (norm_snd_le F)
    have h2 : ‖H.2 k‖ ≤ ‖H‖ := (norm_le_pi_norm H.2 k).trans (norm_snd_le H)
    exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
  calc ∑ k, |∑ l, weightedPairing (ballMeasure z T) (fun x => a x k l) (F.2 l) (H.2 k)|
      ≤ ∑ k : Fin d, ∑ l : Fin d, Λ * (‖F‖ * ‖H‖) :=
        Finset.sum_le_sum fun k _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun l _ => hterm k l)
    _ = (d : ℝ) ^ 2 * Λ * (‖F‖ * ‖H‖) := by simp; ring

theorem dot_mulVec_eq_sum (A : Mat d) (g h : Vec d) :
    dot h (A.mulVec g) = ∑ k, ∑ l, A k l * g l * h k := by
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem integrable_energy_integrand (a : CoefficientField d Λ) (F H : PairSpace d z T) :
    Integrable (fun x => dot (fun k => H.2 k x) ((a x).mulVec fun k => F.2 k x))
      (ballMeasure z T) := by
  simp_rw [dot_mulVec_eq_sum]
  exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    integrable_weighted (aestronglyMeasurable_coefficient_ball a k l) (coefficient_bound a k l) _ _

theorem energyForm_eq_integral (a : CoefficientField d Λ) (F H : PairSpace d z T) :
    energyForm a F H =
      ∫ x in ball z T, dot (fun k => H.2 k x) ((a x).mulVec fun k => F.2 k x) := by
  have hint : ∀ k l, Integrable (fun x => a x k l * F.2 l x * H.2 k x) (ballMeasure z T) :=
    fun k l => integrable_weighted (aestronglyMeasurable_coefficient_ball a k l)
      (coefficient_bound a k l) _ _
  simp_rw [dot_mulVec_eq_sum]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  exact Finset.sum_congr rfl fun k _ => (integral_finsetSum _ fun l _ => hint k l).symm

theorem pairGradEnergy_eq_integral (F : PairSpace d z T) :
    pairGradEnergy F = ∫ x in ball z T, euclideanSq (fun k => F.2 k x) := by
  simp only [pairGradEnergy, norm_sq_eq_integral]
  rw [← integral_finsetSum _ fun k _ => (Lp.memLp (F.2 k)).integrable_sq]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp [euclideanSq, dot, sq])

/-- The energy form is bounded below by the gradient energy. -/
theorem pairGradEnergy_le_energyForm (a : CoefficientField d Λ) (F : PairSpace d z T) :
    pairGradEnergy F ≤ energyForm a F F := by
  rw [energyForm_eq_integral, pairGradEnergy_eq_integral]
  have hsq : Integrable (fun x => euclideanSq (fun k => F.2 k x)) (ballMeasure z T) := by
    have := integrable_finsetSum Finset.univ fun k _ => (Lp.memLp (F.2 k)).integrable_sq
    exact this.congr (Eventually.of_forall fun x => by simp [euclideanSq, dot, sq])
  exact integral_mono_ae hsq (integrable_energy_integrand a F F)
    (Eventually.of_forall fun x => (a.elliptic x _).1)

theorem energyForm_self_nonneg (a : CoefficientField d Λ) (F : PairSpace d z T) :
    0 ≤ energyForm a F F :=
  (pairGradEnergy_nonneg F).trans (pairGradEnergy_le_energyForm a F)

theorem continuous_energyForm (a : CoefficientField d Λ) (hΛ : 0 ≤ Λ) :
    Continuous fun FH : PairSpace d z T × PairSpace d z T => energyForm a FH.1 FH.2 := by
  unfold energyForm
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
  have hW := continuous_weightedPairing (μ := ballMeasure z T)
    (aestronglyMeasurable_coefficient_ball a k l) hΛ (coefficient_bound a k l)
  have h1 : Continuous fun FH : PairSpace d z T × PairSpace d z T => (FH.1.2 l, FH.2.2 k) := by
    fun_prop
  exact hW.comp h1

/-- The energy form is measurable in the coefficients for the local σ-algebra. -/
theorem measurable_energyForm (F H : PairSpace d z T) :
    @Measurable (CoefficientField d Λ) ℝ (localSigma (ball z T)) _
      fun a => energyForm a F H := by
  unfold energyForm
  let _ : MeasurableSpace (CoefficientField d Λ) := localSigma (ball z T)
  refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
  have hg : Integrable (fun x => F.2 l x * H.2 k x) (ballMeasure z T) :=
    (Lp.memLp (F.2 l)).integrable_mul (Lp.memLp (H.2 k))
  have heq : (fun a : CoefficientField d Λ => weightedPairing (ballMeasure z T)
      (fun x => a x k l) (F.2 l) (H.2 k)) =
      fun a => ∫ x in ball z T, (F.2 l x * H.2 k x) * a x k l := by
    funext a
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [heq]
  exact measurable_setIntegral_mul_coefficient z T hg k l

/-- The convexity of the energy of the differences `v - t`. -/
theorem convexOn_energyForm_sub (a : CoefficientField d Λ) (v : PairSpace d z T) :
    ConvexOn ℝ Set.univ fun t : PairSpace d z T => energyForm a (v - t) (v - t) := by
  refine ⟨convex_univ, fun F _ G _ s t hs ht hst => ?_⟩
  show energyForm a (v - (s • F + t • G)) (v - (s • F + t • G)) ≤
    s • energyForm a (v - F) (v - F) + t • energyForm a (v - G) (v - G)
  have hv : v - (s • F + t • G) = s • (v - F) + t • (v - G) := by
    rw [smul_sub, smul_sub, show v = s • v + t • v by rw [← add_smul, hst, one_smul]]
    abel_nf
    rw [← add_smul, hst, one_smul]
    abel
  rw [hv]
  generalize v - F = X
  generalize v - G = Y
  have hXY := energyForm_self_nonneg a (X - Y)
  simp only [energyForm_sub_left, energyForm_sub_right, energyForm_add_left, energyForm_add_right,
    energyForm_smul_left, energyForm_smul_right, smul_eq_mul] at hXY ⊢
  rw [energyForm_symm a Y X] at hXY ⊢
  have ht' : t = 1 - s := by linarith
  subst ht'
  nlinarith [mul_nonneg hs ht]

end QSH
