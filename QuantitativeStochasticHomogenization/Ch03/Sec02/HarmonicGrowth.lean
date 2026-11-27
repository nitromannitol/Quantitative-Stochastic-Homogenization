import QuantitativeStochasticHomogenization.Ch03.Sec02.Lemma36
import PDEFoundation.Monotonicity.Core.HarmonicLiouvilleDeriv

/-!
# The space (3.23) and Lemma 3.6 with the book's `Ā_k`

Armstrong–Kuusi–Mourrat define, in (3.23), `Ā_k` as the space of `ā`-harmonic functions in
`H¹_loc(ℝ^d)` with `r^{-(k+1)} ‖u‖_{L̲²(B_r)} → 0`, and identify it with the `ā`-harmonic
polynomials of degree at most `k` by (3.7). Here `growthHarmonicSpace A k` is (3.23) for a symmetric
`A` with `1 ≤ A ≤ Λ`; it contains `harmonicPolys A k` (`harmonicPolys_subset_growthHarmonicSpace`),
and each of its elements agrees almost everywhere with an element of `harmonicPolys A k`
(`exists_harmonicPoly_ae_of_growth`). For the Laplacian the proof takes the smooth representative of
Weyl's lemma on every ball and bounds `D^{k+1}` at every point by the pointwise derivative bounds on
balls of radius `b → ∞` (`(C (k+1)/b)^{k+1} ‖u‖_{L̲²(B_b)} → 0`), so the representative is its
Taylor polynomial of degree `k`; the passage to `A` is the change of variables `x = M y`. Hence the
distance to (3.23) is `harmonicFlatness` (`growthFlatness_eq`), and Lemma 3.6 holds as printed with
the book's `Ā_k` (`lemma_3_6_growth`).
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- The space (3.23): the weakly `A`-harmonic functions on `ℝ^d` (in `H¹(B_R)` for every `R`) with
`r^{-(k+1)} ‖u‖_{L̲²(B_r)} → 0`. -/
def growthHarmonicSpace (A : Mat d) (k : ℕ) : Set (Vec d → ℝ) :=
  {u | (∀ R : ℝ, 0 < R → IsL2HarmonicOn A (ball 0 R) u) ∧
    Tendsto (fun r : ℝ => (r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) u) atTop (𝓝 0)}

theorem scalarRms_congr_ae {U : Set (Vec d)} {f g : Vec d → ℝ}
    (h : ∀ᵐ x ∂(volume.restrict U), f x = g x) : scalarRms volume U f = scalarRms volume U g := by
  unfold scalarRms
  congr 1
  exact average_congr (by filter_upwards [h] with x hx; rw [hx])

theorem eq_eval_taylorPoly_of_iteratedFDeriv_eq_zero {b : ℝ} {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (PDE.euclideanBall 0 b)) {k : ℕ}
    (hzero : ∀ x ∈ PDE.euclideanBall (0 : Vec d) b, iteratedFDeriv ℝ (k + 1) f x = 0) :
    ∀ x ∈ PDE.euclideanBall (0 : Vec d) b, f x = MvPolynomial.eval x (PDE.taylorPoly f k) := by
  intro x hx
  obtain ⟨ξ, hξ, h⟩ := PDE.taylor_line (PDE.isOpen_euclideanBall 0 b)
    (fun _ hy _ hτ => PDE.euclideanBall_smul_mem hy hτ) hf hx k
  rw [hzero _ (PDE.euclideanBall_smul_mem hx (Ioo_subset_Icc_self hξ))] at h
  rw [PDE.eval_taylorPoly, h]
  simp

/-- **Liouville for (3.23), Laplacian**: a weakly harmonic function on `ℝ^d` with
`r^{-(k+1)} ‖u‖_{L̲²(B_r)} → 0` agrees almost everywhere with a harmonic polynomial of degree at most
`k`. -/
theorem exists_poly_of_harmonic_growth (hd : 0 < d) (k : ℕ) {h : Vec d → ℝ}
    (hh : ∀ b : ℝ, 0 < b → IsL2HarmonicOn 1 (ball (0 : Vec d) b) h)
    (hgrow : Tendsto (fun r : ℝ => (r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) h) atTop (𝓝 0)) :
    ∃ P : MvPolynomial (Fin d) ℝ, P.totalDegree ≤ k ∧
      (∀ x, PDE.euclideanCoordLaplacian (fun y => MvPolynomial.eval y P) x = 0) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), h x = MvPolynomial.eval x P := by
  have hrep : ∀ b : ℝ, 0 < b → ∃ v : Vec d → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v (PDE.euclideanBall 0 b) ∧
      (∀ y ∈ PDE.euclideanBall (0 : Vec d) b, PDE.euclideanCoordLaplacian v y = 0) ∧
      ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) b)), v x = h x := by
    intro b hb
    obtain ⟨huL2, g, hgL2, hgrad, hdiv⟩ := hh b hb
    obtain ⟨v, hvs, hvh, hvae, -⟩ := PDE.exists_harmonicWeylRepresentative hd hb
      (toH1Function hb huL2 hgL2 hgrad) (isWeakDivergenceFormSolutionOn_toH1Function hb huL2 hgL2
        hgrad hdiv)
    refine ⟨v, hvs, hvh, ?_⟩
    rw [ball_zero_eq_pdeEuclideanBall hb]
    exact hvae
  choose V hVs hVh hVae using hrep
  have hagree : ∀ (b b' : ℝ) (hb : 0 < b) (hb' : 0 < b'), b ≤ b' →
      EqOn (V b hb) (V b' hb') (PDE.euclideanBall 0 b) := by
    intro b b' hb hb' hbb'
    have hsub : PDE.euclideanBall (0 : Vec d) b ⊆ PDE.euclideanBall 0 b' :=
      PDE.euclideanBall_mono hb.le hbb'
    refine Measure.eqOn_open_of_ae_eq (μ := (volume : Measure (Vec d))) ?_
      (PDE.isOpen_euclideanBall 0 b) (hVs b hb).continuousOn
      ((hVs b' hb').continuousOn.mono hsub)
    have h1 := hVae b hb
    have h2 := ae_restrict_of_ae_restrict_of_subset (ball_zero_subset_ball_zero hbb') (hVae b' hb')
    rw [ball_zero_eq_pdeEuclideanBall hb] at h1 h2
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
  have hCW := PDE.harmonicPointwiseConst_pos hd
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 * PDE.harmonicPointwiseConst d * ((k : ℝ) + 1)) ^ (k + 1) *
      Real.sqrt (2 ^ d) := ⟨_, rfl⟩
  have hzero : ∀ (b : ℝ) (hb : 0 < b), ∀ z ∈ PDE.euclideanBall (0 : Vec d) b,
      iteratedFDeriv ℝ (k + 1) (V b hb) z = 0 := by
    intro b hb z hz
    have hlim : Tendsto (fun r : ℝ => K * ((r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) h)) atTop
        (𝓝 0) := by simpa using hgrow.const_mul K
    have hF : Real.sqrt (∑ ι : Fin (k + 1) → Fin d,
        (iteratedFDeriv ℝ (k + 1) (V b hb) z (fun l => Pi.single (ι l) 1)) ^ 2) ≤ 0 := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop (max b (2 * euclideanNorm z + 1))] with b' hb'
      have hbb' : b ≤ b' := le_trans (le_max_left _ _) hb'
      have hb'0 : 0 < b' := lt_of_lt_of_le hb hbb'
      have hzb' : euclideanNorm z ≤ b' / 2 := by
        have := le_trans (le_max_right _ _) hb'
        linarith
      have hev : V b hb =ᶠ[𝓝 z] V b' hb'0 := Filter.eventuallyEq_of_mem
        ((PDE.isOpen_euclideanBall 0 b).mem_nhds hz) (hagree b b' hb hb'0 hbb')
      rw [(hev.iteratedFDeriv ℝ (k + 1)).eq_of_nhds]
      have hfrob := TaylorHarmonic.frob_iteratedFDeriv_le hb'0 hd (hh b' hb'0) (hVs b' hb'0)
        (hVh b' hb'0) (hVae b' hb'0) hzb' (k + 1) (by omega)
      refine hfrob.trans ?_
      have hosc : scalarRms volume (ball 0 b') (fun x => h x - ⨍ y in ball 0 b', h y) ≤
          scalarRms volume (ball 0 b') h := by
        refine (scalarRms_sub_setAverage_le_sub_const (volume_ball_ne_top' 0 b')
          (hh b' hb'0).1 0).trans ?_
        simp only [sub_zero, le_refl]
      have e1 : PDE.harmonicPointwiseConst d * ((k + 1 : ℕ) : ℝ) / (b' / 2) =
          (2 * PDE.harmonicPointwiseConst d * ((k : ℝ) + 1)) * b'⁻¹ := by
        push_cast; field_simp
      calc (PDE.harmonicPointwiseConst d * ((k + 1 : ℕ) : ℝ) / (b' / 2)) ^ (k + 1) *
            (Real.sqrt (2 ^ d) * scalarRms volume (ball 0 b') (fun x => h x - ⨍ y in ball 0 b', h y))
          ≤ (PDE.harmonicPointwiseConst d * ((k + 1 : ℕ) : ℝ) / (b' / 2)) ^ (k + 1) *
            (Real.sqrt (2 ^ d) * scalarRms volume (ball 0 b') h) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hosc (Real.sqrt_nonneg _))
              (by positivity)
        _ = K * ((b' ^ (k + 1))⁻¹ * scalarRms volume (ball 0 b') h) := by
            rw [e1, hK, mul_pow, inv_pow]
            ring
    have hsum : ∑ ι : Fin (k + 1) → Fin d,
        (iteratedFDeriv ℝ (k + 1) (V b hb) z (fun l => Pi.single (ι l) 1)) ^ 2 = 0 := by
      have h0 := le_antisymm hF (Real.sqrt_nonneg _)
      rwa [Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h0
    refine PDE.continuousMultilinearMap_eq_zero_of_basisVec _ fun ι => ?_
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 hsum ι
      (Finset.mem_univ _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
  have hE : ∀ {s : ℝ}, 0 < s → (0 : Vec d) ∈ PDE.euclideanBall 0 s := fun hs => by
    rw [← ball_zero_eq_pdeEuclideanBall hs, mem_ball_zero_iff']
    simpa [euclideanNorm, euclideanSq, dot] using hs
  obtain ⟨P, hPdef⟩ : ∃ P, P = PDE.taylorPoly (V 1 one_pos) k := ⟨_, rfl⟩
  have hPn : ∀ (b : ℝ) (hb : 0 < b), 1 ≤ b →
      ∀ x ∈ PDE.euclideanBall (0 : Vec d) b, V b hb x = MvPolynomial.eval x P := by
    intro b hb h1 x hx
    have hev : V b hb =ᶠ[𝓝 (0 : Vec d)] V 1 one_pos := (Filter.eventuallyEq_of_mem
      ((PDE.isOpen_euclideanBall 0 1).mem_nhds (hE one_pos)) (hagree 1 b one_pos hb h1)).symm
    have hit : ∀ n, iteratedFDeriv ℝ n (V b hb) 0 = iteratedFDeriv ℝ n (V 1 one_pos) 0 :=
      fun n => (hev.iteratedFDeriv ℝ n).eq_of_nhds
    have htay : PDE.taylorPoly (V b hb) k = P := by
      rw [hPdef]; unfold PDE.taylorPoly; simp only [hit]
    rw [← htay]
    exact eq_eval_taylorPoly_of_iteratedFDeriv_eq_zero (hVs b hb) (hzero b hb) x hx
  refine ⟨P, by rw [hPdef]; exact PDE.taylorPoly_totalDegree_le _ k, fun x => ?_, ?_⟩
  · have hb : 0 < euclideanNorm x + 1 := by linarith [euclideanNorm_nonneg x]
    have hx : x ∈ PDE.euclideanBall (0 : Vec d) (euclideanNorm x + 1) := by
      rw [← ball_zero_eq_pdeEuclideanBall hb, mem_ball_zero_iff']; linarith
    rw [TaylorHarmonic.laplacian_congr_of_eqOn (PDE.isOpen_euclideanBall 0 _)
      (fun y hy => (hPn _ hb (by linarith [euclideanNorm_nonneg x]) y hy).symm) hx]
    exact hVh _ hb x hx
  · have hcover : (⋃ n : ℕ, ball (0 : Vec d) ((n : ℝ) + 1)) = univ := by
      ext x
      simp only [mem_iUnion, mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_gt (euclideanNorm x)
      exact ⟨n, mem_ball_zero_iff'.2 (by linarith)⟩
    suffices hs : ∀ᵐ x ∂(volume.restrict (⋃ n : ℕ, ball (0 : Vec d) ((n : ℝ) + 1))),
        h x = MvPolynomial.eval x P by
      rwa [hcover, Measure.restrict_univ] at hs
    rw [ae_restrict_iUnion_iff]
    intro n
    have hb : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    filter_upwards [hVae _ hb, ae_restrict_mem (measurableSet_ball' 0 _)] with x hx hxm
    rw [← hx]
    exact hPn _ hb (by linarith [n.cast_nonneg (α := ℝ)]) x
      (by rw [← ball_zero_eq_pdeEuclideanBall hb]; exact hxm)

/-- A symmetric `A` with `1 ≤ A ≤ Λ` is `M Mᵀ` for an invertible `M`. -/
theorem exists_mul_transpose_eq {A : Mat d} (hsym : A.transpose = A)
    (hA : HomogenizedMatrixBounds A Λ) : ∃ M : Mat d, M.det ≠ 0 ∧ M * M.transpose = A := by
  have hpos : ∀ ξ : Vec d, ξ ≠ 0 → 0 < dot ξ (A.mulVec ξ) := by
    intro ξ hξ
    have h1 := (hA ξ).1
    have h2 : 0 < euclideanSq ξ := by
      rcases (BaseExponent.euclideanSq_nonneg ξ).eq_or_lt with h0 | h0
      · exfalso
        apply hξ
        funext i
        have hsum : ∑ j, ξ j * ξ j = 0 := h0.symm
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (ξ j))).mp hsum i
          (Finset.mem_univ i)
        simpa using this
      · exact h0
    linarith
  obtain ⟨M, hdet, hMM⟩ := exists_mul_transpose_eq_symmPart hpos
  refine ⟨M, hdet, ?_⟩
  rw [hMM, hsym, ← two_smul ℝ A, smul_smul]
  norm_num

/-- **The elements of (3.23) are the `A`-harmonic polynomials of degree at most `k`**, up to
almost everywhere equality. -/
theorem exists_harmonicPoly_ae_of_growth (hd : 2 ≤ d) (hΛ : 1 ≤ Λ) (k : ℕ) {A : Mat d}
    (hsym : A.transpose = A) (hA : HomogenizedMatrixBounds A Λ) {u : Vec d → ℝ}
    (hu : u ∈ growthHarmonicSpace A k) :
    ∃ p ∈ harmonicPolys A k, ∀ᵐ x ∂(volume : Measure (Vec d)), u x = p x := by
  obtain ⟨M, hdet, hMA⟩ := exists_mul_transpose_eq hsym hA
  have hΛ0 : 0 < Λ := by linarith
  have hsΛ : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ0
  have hA' : HomogenizedMatrixBounds (M * M.transpose) Λ := by rw [hMA]; exact hA
  have hsym' : (M * M.transpose).transpose = M * M.transpose := by rw [hMA]; exact hsym
  have hdet1 := one_le_abs_det hdet hA'
  have hdet0 : 0 < |M.det| := by linarith
  have hEB : ∀ b : ℝ, matrixEllipsoid M b ⊆ ball 0 (Real.sqrt Λ * b) := fun b =>
    matrixEllipsoid_subset_ball_sqrt hdet hΛ0 hA' hsym' b
  have huA : ∀ R : ℝ, 0 < R → IsL2HarmonicOn (M * M.transpose) (ball 0 R) u := fun R hR => by
    rw [hMA]; exact hu.1 R hR
  have hhar : ∀ b : ℝ, 0 < b → IsL2HarmonicOn 1 (ball (0 : Vec d) b) (fun y => u (M.mulVec y)) :=
    fun b hb => ((huA _ (mul_pos hsΛ hb)).mono (hEB b)).comp_matrixEllipsoid hdet
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.sqrt (Real.sqrt Λ ^ d / |M.det|) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; exact Real.sqrt_nonneg _
  have hle : ∀ r : ℝ, 0 < r → (r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) (fun y => u (M.mulVec y))
      ≤ Real.sqrt Λ ^ (k + 1) * c * (((Real.sqrt Λ * r) ^ (k + 1))⁻¹ *
        scalarRms volume (ball 0 (Real.sqrt Λ * r)) u) := by
    intro r hr
    have hvol : volume.real (ball (0 : Vec d) (Real.sqrt Λ * r)) ≤
        (Real.sqrt Λ ^ d / |M.det|) * volume.real (matrixEllipsoid M r) := by
      rw [volume_real_matrixEllipsoid, volume_real_ball_mul hsΛ r]
      apply le_of_eq
      field_simp
    have h1 : scalarRms volume (matrixEllipsoid M r) u ≤
        c * scalarRms volume (ball 0 (Real.sqrt Λ * r)) u := by
      rw [hc]
      exact scalarRms_le_sqrt_mul_of_subset (hEB r) (volume_matrixEllipsoid_ne_zero hdet hr)
        (volume_ball_ne_top' 0 _) hvol (by positivity)
        (huA _ (mul_pos hsΛ hr)).1.integrable_sq
    rw [← scalarRms_matrixEllipsoid_eq hdet r]
    have hr' : 0 < (r ^ (k + 1))⁻¹ := by positivity
    calc (r ^ (k + 1))⁻¹ * scalarRms volume (matrixEllipsoid M r) u
        ≤ (r ^ (k + 1))⁻¹ * (c * scalarRms volume (ball 0 (Real.sqrt Λ * r)) u) :=
          mul_le_mul_of_nonneg_left h1 hr'.le
      _ = _ := by
          rw [mul_pow]
          field_simp
  have hgrow : Tendsto (fun r : ℝ => (r ^ (k + 1))⁻¹ *
      scalarRms volume (ball 0 r) (fun y => u (M.mulVec y))) atTop (𝓝 0) := by
    have hcomp := hu.2.comp (tendsto_id.const_mul_atTop hsΛ)
    have hup : Tendsto (fun r : ℝ => Real.sqrt Λ ^ (k + 1) * c * (((Real.sqrt Λ * r) ^ (k + 1))⁻¹ *
        scalarRms volume (ball 0 (Real.sqrt Λ * r)) u)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using hcomp.const_mul (Real.sqrt Λ ^ (k + 1) * c)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with r hr
      exact mul_nonneg (by positivity) (scalarRms_nonneg _ _)
    · filter_upwards [eventually_gt_atTop 0] with r hr
      exact hle r hr
  obtain ⟨P, hPdeg, hPharm, hae⟩ := exists_poly_of_harmonic_growth (by omega) k hhar hgrow
  obtain ⟨Q, hQdeg, hQe⟩ := exists_poly_comp_mulVec M⁻¹ P
  refine ⟨fun x => MvPolynomial.eval (M⁻¹.mulVec x) P,
    ⟨⟨Q, hQdeg.trans hPdeg, fun x => (hQe x).symm⟩, fun ρ hρ => ?_⟩, ?_⟩
  · have hE := isL2HarmonicOn_comp_inv hdet hρ (PDE.contDiff_eval_mvPolynomial P)
      (fun y _ => hPharm y)
    rw [hMA] at hE
    exact hE.mono (ball_subset_matrixEllipsoid hdet hA' ρ)
  · have hdetinv : (Matrix.toLin' M⁻¹).det ≠ 0 := by
      rw [LinearMap.det_toLin', Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact inv_ne_zero hdet
    have h := (Measure.LinearMap.quasiMeasurePreserving (μ := (volume : Measure (Vec d)))
      (Matrix.toLin' M⁻¹) hdetinv).ae hae
    filter_upwards [h] with x hx
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec] at hx
    exact hx

theorem abs_eval_mvPolynomial_le {P : MvPolynomial (Fin d) ℝ} {k : ℕ} (hP : P.totalDegree ≤ k) {r : ℝ}
    (hr : 1 ≤ r) {x : Vec d} (hx : euclideanNorm x ≤ r) :
    |MvPolynomial.eval x P| ≤ (∑ s ∈ P.support, |P.coeff s|) * r ^ k := by
  have hxi : ∀ i, |x i| ≤ r := fun i => by
    have h : x i ^ 2 ≤ euclideanSq x := by
      rw [euclideanSq, dot, sq]
      exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    exact (Real.abs_le_sqrt h).trans hx
  conv_lhs => rw [P.as_sum, map_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [MvPolynomial.eval_monomial, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [Finsupp.prod, Finset.abs_prod]
  calc ∏ i ∈ s.support, |x i ^ s i| ≤ ∏ i ∈ s.support, r ^ s i :=
        by
          gcongr with i hi
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hxi i) _
    _ = r ^ (s.sum fun _ e => e) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ r ^ k := pow_le_pow_right₀ hr ((MvPolynomial.le_totalDegree hs).trans hP)

/-- The `A`-harmonic polynomials of degree at most `k` belong to (3.23). -/
theorem harmonicPolys_subset_growthHarmonicSpace (A : Mat d) (k : ℕ) :
    harmonicPolys A k ⊆ growthHarmonicSpace A k := by
  rintro p ⟨⟨P, hP, hPe⟩, hph⟩
  refine ⟨hph, ?_⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ s ∈ P.support, |P.coeff s| := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hle : ∀ r : ℝ, 1 ≤ r → (r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) p ≤ S * r⁻¹ := by
    intro r hr
    have hr0 : 0 < r := by linarith
    have hpt : ∀ x ∈ ball (0 : Vec d) r, |p x| ≤ S * r ^ k := fun x hx => by
      rw [hPe x, hS]
      exact abs_eval_mvPolynomial_le hP hr (mem_ball_zero_iff'.1 hx).le
    have hvol : 0 < volume.real (ball (0 : Vec d) r) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (volume_ball_ne_zero' 0 hr0) (volume_ball_ne_top' 0 r)
    have hrms : scalarRms volume (ball 0 r) p ≤ S * r ^ k := by
      refine scalarRms_le_of_integral_sq_le hvol (by positivity) ?_
      calc ∫ x in ball 0 r, p x ^ 2 ≤ ∫ x in ball 0 r, (S * r ^ k) ^ 2 :=
            setIntegral_mono_on (hph r hr0).1.integrable_sq
              (integrableOn_const (volume_ball_ne_top' 0 r)) (measurableSet_ball' 0 r)
              (fun x hx => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hpt x hx) 2)
        _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
    calc (r ^ (k + 1))⁻¹ * scalarRms volume (ball 0 r) p ≤ (r ^ (k + 1))⁻¹ * (S * r ^ k) :=
          mul_le_mul_of_nonneg_left hrms (by positivity)
      _ = S * r⁻¹ := by field_simp; ring
  have hup : Tendsto (fun r : ℝ => S * r⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul S
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with r hr
    exact mul_nonneg (by positivity) (scalarRms_nonneg _ _)
  · filter_upwards [eventually_ge_atTop 1] with r hr
    exact hle r hr

/-- `inf_{p ∈ Ā_k} ‖u - p‖_{L̲²(B_r)}` with `Ā_k` the space (3.23). -/
def growthFlatness (A : Mat d) (k : ℕ) (u : Vec d → ℝ) (r : ℝ) : ℝ :=
  ⨅ p : growthHarmonicSpace A k, scalarRms volume (ball 0 r) (fun x => u x - (p : Vec d → ℝ) x)

/-- The distance to (3.23) is the distance to the `A`-harmonic polynomials of degree at most `k`. -/
theorem growthFlatness_eq (hd : 2 ≤ d) (hΛ : 1 ≤ Λ) (k : ℕ) {A : Mat d} (hsym : A.transpose = A)
    (hA : HomogenizedMatrixBounds A Λ) (u : Vec d → ℝ) (r : ℝ) :
    growthFlatness A k u r = harmonicFlatness A k u r := by
  have : Nonempty (harmonicPolys A k) := ⟨⟨_, zero_mem_harmonicPolys A k⟩⟩
  have : Nonempty (growthHarmonicSpace A k) :=
    ⟨⟨_, harmonicPolys_subset_growthHarmonicSpace A k (zero_mem_harmonicPolys A k)⟩⟩
  have hbdd : BddBelow (range fun p : growthHarmonicSpace A k =>
      scalarRms volume (ball 0 r) (fun x => u x - (p : Vec d → ℝ) x)) :=
    ⟨0, by rintro _ ⟨p, rfl⟩; exact scalarRms_nonneg _ _⟩
  unfold growthFlatness harmonicFlatness
  apply le_antisymm
  · exact le_ciInf fun p => ciInf_le hbdd ⟨p.1, harmonicPolys_subset_growthHarmonicSpace A k p.2⟩
  · refine le_ciInf fun p => ?_
    obtain ⟨q, hq, hpq⟩ := exists_harmonicPoly_ae_of_growth hd hΛ k hsym hA p.2
    rw [scalarRms_congr_ae (g := fun x => u x - q x)
      (ae_restrict_of_ae (by filter_upwards [hpq] with x hx; rw [hx]))]
    exact ciInf_le (bddBelow_harmonicFlatness A k u r) ⟨q, hq⟩

/-- **Lemma 3.6 as printed**, with `Ā_k` the space (3.23) of the book. -/
theorem lemma_3_6_growth (hd : 2 ≤ d) (hΛ : 1 ≤ Λ) {α : ℝ} (hα : 0 < α) (k : ℕ) :
    ∃ θ C : ℝ, 0 < θ ∧ θ < 1 / 2 ∧ 0 ≤ C ∧
      ∀ A : Mat d, A.transpose = A → HomogenizedMatrixBounds A Λ →
      ∀ K X R : ℝ, 1 ≤ X → ∀ u : Vec d → ℝ, MemLp u 2 (volume.restrict (ball 0 R)) →
      (∀ r : ℝ, X ≤ r → r ≤ R → ∃ w : Vec d → ℝ, IsL2HarmonicOn A (ball 0 (r / 2)) w ∧
        scalarRms volume (ball 0 (r / 2)) (fun x => u x - w x) ≤
          K * r ^ (-α) * scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y)) →
      ∀ r : ℝ, X ≤ r → r ≤ R →
        growthFlatness A k u (θ * r) ≤
          1 / 4 * θ ^ ((k : ℝ) + 1 - α / 2) * growthFlatness A k u r +
            C * K * r ^ (-α) * scalarRms volume (ball 0 r) (fun x => u x - ⨍ y in ball 0 r, u y) := by
  obtain ⟨θ, C, hθ0, hθ1, hC, h⟩ := lemma_3_6 hd hΛ hα k
  refine ⟨θ, C, hθ0, hθ1, hC, fun A hsym hA K X R hX u hu hyp r hXr hrR => ?_⟩
  rw [growthFlatness_eq hd hΛ k hsym hA, growthFlatness_eq hd hΛ k hsym hA]
  exact h A hsym hA K X R hX u hu hyp r hXr hrR

end QSH
