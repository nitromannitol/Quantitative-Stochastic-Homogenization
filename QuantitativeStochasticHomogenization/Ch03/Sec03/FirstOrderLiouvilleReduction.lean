import QuantitativeStochasticHomogenization.Ch03.Sec03.QuarterExcessStepReduction
import QuantitativeStochasticHomogenization.Ch03.Sec03.FirstOrderLiouville
import QuantitativeStochasticHomogenization.Ch03.Sec03.CorrectedAffine
import QuantitativeStochasticHomogenization.Ch06.Sec01.FluxCorrectorSkewDivergence
import QuantitativeStochasticHomogenization.Ch06.Sec01.CorrectorSublinear
import QuantitativeStochasticHomogenization.Ch03.Sec04.FrobeniusNorm
import QuantitativeStochasticHomogenization.Ch03.Sec04.SpatialWeakProduct
import QuantitativeStochasticHomogenization.Ch04.Sec01.QuadraticEntryBounds

/-!
# The first-order Liouville theorem from one step of the quadratic excess decay

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Theorem 3.8 for `k = 1`, first-order route: `firstOrderLiouvilleStatement` follows from
`quarterExcessStepStatement`. Almost surely the coordinate correctors `φ_{eᵢ}` and the skew
parts of flux correctors form a `SublinearCorrectorFamily` with the homogenized matrix `ā` of
the high-contrast theorem: (6.5)–(6.6) give the flux identity, and Lemma 3.17 with Lemma 6.1
and Proposition 6.2 give the oscillation bound `C r^{1 - β(d - s)}` above the largest of the
`d` random scales, with `s` chosen so that `β(d - s) ≤ ½`. Each entry of the skew part has
centered normalized `L²` norm at most that of the flux corrector in the Frobenius norm. The
gradients agree because weak gradients are unique. With the derivation of the quarter step from
the harmonic approximation (2) and the harmonic expansion, the first-order Liouville theorem
follows from these two deterministic estimates.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The integral of a partial derivative of a smooth compactly supported test vanishes. -/
theorem integral_coordinateDerivative_eq_zero {ψ : Vec d → ℝ}
    (hψ : IsSpatialTest Set.univ ψ) (k : Fin d) : ∫ x, coordinateDerivative k ψ x = 0 := by
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
  have hdint : Integrable (coordinateDerivative k ψ) :=
    (isSpatialTest_coordinateDerivative hψ k).1.continuous.integrable_of_hasCompactSupport
      (isSpatialTest_coordinateDerivative hψ k).2.1
  have hψint : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Vec d))) (f := fun _ : Vec d => (1 : ℝ)) (g := ψ)
    (v := unitVector k) (by simp) (by simp only [one_mul]; exact hdint)
    (by simp only [one_mul]; exact hψint) (fun x _ => differentiableAt_const _)
    (fun x _ => hψd x)
  simpa [coordinateDerivative] using h

/-- A constant has zero weak gradient. -/
theorem hasWeakGradient_const (c : ℝ) :
    HasWeakGradient Set.univ (fun _ : Vec d => c) (fun _ => 0) := by
  intro i
  refine ⟨locallyIntegrableOn_const _, locallyIntegrableOn_zero, fun ψ hψ => ?_⟩
  simp only [Measure.restrict_univ, Pi.zero_apply, zero_mul, integral_zero, neg_zero]
  rw [integral_const_mul, integral_coordinateDerivative_eq_zero hψ i, mul_zero]

/-- **Uniqueness of weak gradients.** -/
theorem hasWeakGradient_ae_eq {f f' : Vec d → ℝ} {g g' : Vec d → Vec d}
    (hg : HasWeakGradient Set.univ f g) (hg' : HasWeakGradient Set.univ f' g')
    (hff : f =ᵐ[volume] f') : g =ᵐ[volume] g' := by
  have hcomp : ∀ i, ∀ᵐ x ∂(volume : Measure (Vec d)), g x i - g' x i = 0 := by
    intro i
    have h1 := (hg i).2.1
    have h2 := (hg' i).2.1
    rw [locallyIntegrableOn_univ] at h1 h2
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (h1.sub h2) fun ψ hψ hψc => ?_
    have htest : IsSpatialTest Set.univ ψ := ⟨hψ, hψc, Set.subset_univ _⟩
    have e1 := (hg i).2.2 ψ htest
    have e2 := (hg' i).2.2 ψ htest
    simp only [Measure.restrict_univ] at e1 e2
    have e3 : ∫ x, f x * coordinateDerivative i ψ x = ∫ x, f' x * coordinateDerivative i ψ x :=
      integral_congr_ae (by filter_upwards [hff] with x hx; rw [hx])
    have hint1 : Integrable fun x => g x i * ψ x := by
      have h := integrableOn_mul_spatialTest (hg i).2.1 htest
      rwa [integrableOn_univ] at h
    have hint2 : Integrable fun x => g' x i * ψ x := by
      have h := integrableOn_mul_spatialTest (hg' i).2.1 htest
      rwa [integrableOn_univ] at h
    have hsplit : ∫ x, ψ x • (fun x => g x i - g' x i) x =
        (∫ x, g x i * ψ x) - ∫ x, g' x i * ψ x := by
      rw [← integral_sub hint1 hint2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      ring
    rw [hsplit]
    linarith
  filter_upwards [ae_all_iff.2 hcomp] with x hx
  funext i
  linarith [hx i]

/-- The symmetric part of a matrix in the quadratic form. -/
theorem dot_mulVec_eq_vecDot_symmPart (A : Mat d) (ξ : Vec d) :
    dot ξ (A.mulVec ξ) = _root_.Homogenization.vecDot ξ
      (_root_.Homogenization.matVecMul (_root_.Homogenization.symmPart A) ξ) := by
  simp only [dot, _root_.Homogenization.vecDot, _root_.Homogenization.matVecMul,
    _root_.Homogenization.symmPart, Matrix.mulVec, dotProduct, Finset.mul_sum]
  have h2 : ∑ i, ∑ j, ξ i * (A j i * ξ j) = ∑ i, ∑ j, ξ i * (A i j * ξ j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h3 : ∑ i, ∑ j, ξ i * ((A i j + A j i) / 2 * ξ j) =
      (∑ i, ∑ j, ξ i * (A i j * ξ j)) / 2 + (∑ i, ∑ j, ξ i * (A j i * ξ j)) / 2 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h3, h2]
  ring

theorem sq_entry_le_frobeniusSq (A : Mat d) (j k : Fin d) : A j k ^ 2 ≤ frobeniusSq A := by
  unfold frobeniusSq
  calc A j k ^ 2 = A j k * A j k := sq _
    _ ≤ ∑ k', A j k' * A j k' :=
        Finset.single_le_sum (f := fun k' => A j k' * A j k') (fun k' _ => mul_self_nonneg _)
          (Finset.mem_univ k)
    _ ≤ ∑ j', ∑ k', A j' k' * A j' k' :=
        Finset.single_le_sum (f := fun j' => ∑ k', A j' k' * A j' k')
          (fun j' _ => Finset.sum_nonneg fun k' _ => mul_self_nonneg _) (Finset.mem_univ j)

private theorem setAverage_le_setAverage {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : Integrable g (volume.restrict U)) (hfg : ∀ x, f x ≤ g x) :
    ⨍ x in U, f x ≤ ⨍ x in U, g x := by
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (integral_mono_of_nonneg (Eventually.of_forall hf) hg (Eventually.of_forall hfg))
    (inv_nonneg.2 measureReal_nonneg)

private theorem memLp_half_sub {μ : Measure (Vec d)} {f g : Vec d → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : MemLp (fun x => (f x - g x) / 2) 2 μ :=
  ((hf.sub hg).const_mul (1 / 2 : ℝ)).ae_eq
    (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)

/-- The centered normalized `L²` norm of an entry of the skew part is at most that of the matrix
field in the Frobenius norm. -/
theorem scalarRms_skew_entry_le {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    {σ : Vec d → Mat d} (hσ : ∀ j k, MemLp (fun x => σ x j k) 2 (volume.restrict U))
    (j k : Fin d) :
    scalarRms volume U (fun x => (σ x j k - σ x k j) / 2 - ⨍ y in U, (σ y j k - σ y k j) / 2) ≤
      Real.sqrt (⨍ x in U, frobeniusNorm (σ x -
        (Matrix.of fun i l => ⨍ y in U, σ y i l)) ^ 2) := by
  have hint : ∀ j k, Integrable (fun x => σ x j k) (volume.restrict U) := fun j k =>
    (hσ j k).integrable one_le_two
  have hmean : ⨍ y in U, (σ y j k - σ y k j) / 2 =
      ((⨍ y in U, σ y j k) - ⨍ y in U, σ y k j) / 2 := by
    rw [setAverage_eq, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      integral_div, integral_sub (hint j k) (hint k j)]
    ring
  unfold scalarRms
  apply Real.sqrt_le_sqrt
  have hsqint : ∀ j k, Integrable (fun x => (σ x j k - ⨍ y in U, σ y j k) ^ 2)
      (volume.restrict U) := fun j k => ((hσ j k).sub (memLp_const _)).integrable_sq
  have hfrob : Integrable (fun x => frobeniusNorm (σ x -
      (Matrix.of fun i l => ⨍ y in U, σ y i l)) ^ 2) (volume.restrict U) := by
    have hsum : Integrable (fun x => ∑ i, ∑ l, (σ x i l - ⨍ y in U, σ y i l) ^ 2)
        (volume.restrict U) :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => hsqint i l
    refine hsum.congr (Eventually.of_forall fun x => ?_)
    simp only [frobeniusNorm]
    rw [Real.sq_sqrt (frobeniusSq_nonneg _)]
    unfold frobeniusSq
    simp only [Matrix.sub_apply, Matrix.of_apply, sq]
  refine setAverage_le_setAverage (fun x => sq_nonneg _) hfrob (fun x => ?_)
  rw [hmean, frobeniusNorm, Real.sq_sqrt (frobeniusSq_nonneg _)]
  have h1 := sq_entry_le_frobeniusSq (σ x - Matrix.of fun i l => ⨍ y in U, σ y i l) j k
  have h2 := sq_entry_le_frobeniusSq (σ x - Matrix.of fun i l => ⨍ y in U, σ y i l) k j
  simp only [Matrix.sub_apply, Matrix.of_apply] at h1 h2
  nlinarith [sq_nonneg ((σ x j k - ⨍ y in U, σ y j k) + (σ x k j - ⨍ y in U, σ y k j))]

/-- **Theorem 3.8, `k = 1`, from one step of the quadratic excess decay.** -/
theorem firstOrderLiouville_of_quarterExcessStep (hstep : quarterExcessStepStatement) :
    firstOrderLiouvilleStatement := by
  intro d hd Λ hΛ P hP S
  obtain ⟨β, C, hβ, hC, hE8⟩ := sublinearCorrectors d hd Λ hΛ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set δ : ℝ := min ((d : ℝ) / 2) (1 / (2 * β)) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδd : δ < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set s : ℝ := d - δ with hs
  have hs0 : 0 < s := by linarith
  have hsd : s < d := by linarith
  obtain ⟨Cs, -, hE8s⟩ := hE8 s hs0 hsd
  set μ : ℝ := β * ((d : ℝ) - s) with hμ
  have hμδ : μ = β * δ := by rw [hμ, hs]; ring
  have hμ0 : 0 < μ := by rw [hμδ]; positivity
  have hμ' : μ ≤ 1 / 2 := by
    rw [hμδ]
    calc β * δ ≤ β * (1 / (2 * β)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hβ.le
      _ = 1 / 2 := by field_simp
  have hunit : ∀ i : Fin d, euclideanNorm (unitVector i) = 1 := euclideanNorm_unitVector_eq_one
  have hFl : ∀ i : Fin d, Nonempty (FluxCorrector (S.corrector (unitVector i))) := fun i =>
    (hE8s P hP _ (hunit i) _).1
  set Fl : ∀ i : Fin d, FluxCorrector (S.corrector (unitVector i)) := fun i =>
    Classical.choice (hFl i) with hFldef
  have hX := fun i : Fin d => (hE8s P hP _ (hunit i) _).2 (Fl i)
  choose X _hXm _hXos hXae using hX
  obtain ⟨κ, C₀, hκ, hC₀, hpk⟩ := exists_highContrastCorrectorPackage d hd
  obtain ⟨pk⟩ := hpk Λ hΛ.le P hP
  set D : Mat d := pk.abar with hDdef
  have hD : ∀ ξ : Vec d, ξ ≠ 0 → 0 < dot ξ (D.mulVec ξ) := fun ξ hξ => by
    rw [dot_mulVec_eq_vecDot_symmPart]
    exact pk.posDef ξ hξ
  have hskew := fun i : Fin d =>
    (Fl i).ae_skew_divergence_of_package hd hΛ hP hκ hC₀.le pk (hunit i)
  have hC₁ : 0 ≤ (1 + (d : ℝ) ^ 2) * C := by positivity
  filter_upwards [ae_all_iff.2 hXae, ae_all_iff.2 hskew,
    ae_all_iff.2 fun i => (S.corrector (unitVector i)).weak_gradient,
    ae_all_iff.2 fun i => (S.corrector (unitVector i)).locally_square_integrable,
    ae_all_iff.2 fun i => (S.corrector (unitVector i)).harmonic,
    ae_all_iff.2 fun i => (Fl i).locally_square_integrable] with a hXa hska hwg hlsi hharm hFlsi
  intro w
  set R₀ : ℝ := 1 + ∑ i, X i a with hR₀def
  have hXnn : ∀ i, 0 ≤ X i a := fun i => le_trans zero_le_one (hXa i).1
  have hXle : ∀ i, X i a ≤ R₀ := by
    intro i
    have h : X i a ≤ ∑ i, X i a :=
      Finset.single_le_sum (f := fun i => X i a) (fun i _ => hXnn i) (Finset.mem_univ i)
    linarith
  have hR₀ : 1 ≤ R₀ := by
    have : 0 ≤ ∑ i, X i a := Finset.sum_nonneg fun i _ => hXnn i
    linarith
  let F : SublinearCorrectorFamily a D μ ((1 + (d : ℝ) ^ 2) * C) R₀ :=
    { φ := fun i => (S.corrector (unitVector i)).potential a
      gφ := fun i => (S.corrector (unitVector i)).grad a
      σ := fun i x j k => ((Fl i).potential a x j k - (Fl i).potential a x k j) / 2
      gσ := fun i j k x => (1 / 2 : ℝ) • ((Fl i).grad a j k x - (Fl i).grad a k j x)
      weak_gradient_φ := hwg
      weak_gradient_σ := fun i j k => ((hska i) j).2 k
      memLp := fun i R hR => ⟨(hlsi i R hR).1, (hlsi i R hR).2, fun j k =>
        ⟨memLp_half_sub (hFlsi i R hR j k).1 (hFlsi i R hR k j).1,
          ((hFlsi i R hR j k).2.sub (hFlsi i R hR k j).2).const_smul (1 / 2 : ℝ)⟩⟩
      harmonic := hharm
      flux := fun i j => ((hska i) j).1
      skew := fun i x j k => by ring
      oscillation := by
        intro i R hR
        have hR0 : 0 < R := by linarith
        have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
          isFiniteMeasure_restrict.2 (volume_ball_zero_lt_top R).ne
        obtain ⟨hbd, -⟩ := (hXa i).2 R ((hXle i).trans hR)
        set A := Real.sqrt (⨍ x in ball 0 R, |(S.corrector (unitVector i)).potential a x -
          (⨍ y in ball 0 R, (S.corrector (unitVector i)).potential a y)| ^ 2) with hA
        set B := Real.sqrt (⨍ x in ball 0 R, frobeniusNorm ((Fl i).potential a x -
          (Matrix.of fun i' j' => ⨍ y in ball 0 R, (Fl i).potential a y i' j')) ^ 2) with hB
        have hA0 : 0 ≤ A := Real.sqrt_nonneg _
        have hB0 : 0 ≤ B := Real.sqrt_nonneg _
        have hφ : scalarRms volume (ball 0 R) (fun x => (S.corrector (unitVector i)).potential a x -
            ⨍ y in ball 0 R, (S.corrector (unitVector i)).potential a y) = A := by
          rw [hA]
          unfold scalarRms
          simp only [sq_abs]
        have hentry : ∀ j k, scalarRms volume (ball 0 R)
            (fun x => ((Fl i).potential a x j k - (Fl i).potential a x k j) / 2 -
              ⨍ y in ball 0 R, ((Fl i).potential a y j k - (Fl i).potential a y k j) / 2) ≤ B :=
          fun j k => scalarRms_skew_entry_le (fun j k => (hFlsi i R hR0 j k).1) j k
        have hsum : ∑ j : Fin d, ∑ k : Fin d, scalarRms volume (ball 0 R)
            (fun x => ((Fl i).potential a x j k - (Fl i).potential a x k j) / 2 -
              ⨍ y in ball 0 R, ((Fl i).potential a y j k - (Fl i).potential a y k j) / 2) ≤
            (d : ℝ) ^ 2 * B := by
          calc _ ≤ ∑ _j : Fin d, ∑ _k : Fin d, B :=
                Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
            _ = (d : ℝ) ^ 2 * B := by simp [Finset.sum_const, sq]; ring
        change scalarRms volume (ball 0 R) (fun x => (S.corrector (unitVector i)).potential a x -
            ⨍ y in ball 0 R, (S.corrector (unitVector i)).potential a y) +
          ∑ j : Fin d, ∑ k : Fin d, scalarRms volume (ball 0 R)
            (fun x => ((Fl i).potential a x j k - (Fl i).potential a x k j) / 2 -
              ⨍ y in ball 0 R, ((Fl i).potential a y j k - (Fl i).potential a y k j) / 2) ≤
          (1 + (d : ℝ) ^ 2) * C * R ^ (1 - μ)
        rw [hφ]
        have hd2 : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg _
        have hRμ : 0 ≤ R ^ (1 - μ) := Real.rpow_nonneg hR0.le _
        have hbd' : A + B ≤ C * R ^ (1 - μ) := hbd
        nlinarith [mul_le_mul_of_nonneg_left hbd' hd2] }
  obtain ⟨c, p, hcp⟩ := exists_ae_eq_correctedAffineOf hstep hd hΛ.le hμ0 hμ' hC₁ hR₀ hD F w
  have hpot : ∀ᵐ x ∂(volume : Measure (Vec d)), w.potential x = c + correctedAffine S a p x := by
    filter_upwards [hcp] with x hx
    rw [hx]
    simp only [correctedAffineOf, correctedAffine, F]
    ring
  refine ⟨c, p, hpot, ?_⟩
  have hG : HasWeakGradient Set.univ (fun x => c + correctedAffine S a p x)
      (fun x => 0 + correctedAffineGrad S a p x) :=
    hasWeakGradient_add (hasWeakGradient_const c)
      (hasWeakGradient_add (hasWeakGradient_dot p)
        (hasWeakGradient_finset_sum_const_mul Finset.univ p
          (f := fun i => (S.corrector (unitVector i)).potential a)
          (g := fun i => (S.corrector (unitVector i)).grad a) fun i _ => hwg i))
  have h := hasWeakGradient_ae_eq w.weak_gradient hG hpot
  filter_upwards [h] with x hx
  rw [hx, zero_add]

/-- **Theorem 3.8, `k = 1`, from the harmonic approximation (2) and the harmonic expansion.** -/
theorem firstOrderLiouville_of_harmonicApproximation (h2 : harmonicApproximationStatement)
    (hH : harmonicExpansionStatement) : firstOrderLiouvilleStatement :=
  firstOrderLiouville_of_quarterExcessStep (quarterExcessStep_of_harmonicApproximation h2 hH)

end QSH
