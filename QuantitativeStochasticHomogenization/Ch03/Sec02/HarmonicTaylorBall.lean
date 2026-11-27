import QuantitativeStochasticHomogenization.Ch03.Sec02.TaylorHarmonic
import QuantitativeStochasticHomogenization.Ch03.Sec02.Theorem33
import QuantitativeStochasticHomogenization.Ch01.Sec05.ConvexBoundaryDensity
import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestCorrectorTranslation
import QuantitativeStochasticHomogenization.Ch03.Sec04.CoefficientSigma
import QuantitativeStochasticHomogenization.Ch04.Sec04.CompactTestFiniteBallCore
import PDEFoundation.Monotonicity.Core.BridgeLocalize
import PDEFoundation.PDE.HarmonicPointwiseAssembly
import PDEFoundation.PDE.HarmonicWeylRepresentative

/-!
# The Taylor approximation of harmonic functions on balls, (3.24) for every `k`

For `u` weakly harmonic in `B_b` and `k ∈ ℕ`, the Taylor polynomial `P` of degree `k` at `0` of the
smooth representative of `u` is a harmonic polynomial and, for `t ≤ b/4`,
`‖u - P‖_{L̲²(B_t)} ≤ C (t/b)^{k+1} ‖u - (u)_{B_b}‖_{L̲²(B_b)}` with `C(k, d)`
(`harmonicTaylorBall`). The proof is Taylor's formula with Lagrange remainder along segments and the
pointwise derivative bounds for harmonic functions of the elliptic regularity library (the
`C^{k,1}` estimate (3.7) for the Laplacian), applied at the points of `B_{b/4}` after a
translation.
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace QSH

variable {d : ℕ}

namespace TaylorHarmonic

/-- A function smooth on `B_R` agrees on a larger ball than `B_ρ` with a smooth function on `ℝ^d`
(the localization of the elliptic regularity library, for smooth functions). -/
theorem exists_contDiff_top_localization {u : Vec d → ℝ} {R ρ : ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (PDE.euclideanBall 0 R)) (hρ : 0 < ρ) (hρR : ρ < R) :
    ∃ (ρ' : ℝ) (v : Vec d → ℝ), ρ < ρ' ∧ ρ' < R ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
      EqOn v u (PDE.euclideanBall 0 ρ') := by
  set ρ' : ℝ := (ρ + R) / 2 with hρ'
  have h1 : ρ < ρ' := by rw [hρ']; linarith
  have h2 : ρ' < R := by rw [hρ']; linarith
  have hρ'0 : 0 ≤ ρ' := by linarith
  set χ := PDE.canonicalBallCutoff (0 : Vec d) ρ' R with hχ
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ := PDE.canonicalBallCutoff_smooth (0 : Vec d) hρ'0 h2
  have hts : tsupport χ ⊆ PDE.euclideanBall 0 R :=
    PDE.canonicalBallCutoff_tsupport_subset_outer hρ'0 h2
  have hopen : IsOpen (PDE.euclideanBall (0 : Vec d) R) := PDE.isOpen_euclideanBall 0 R
  refine ⟨ρ', (PDE.euclideanBall 0 R).indicator (fun x => χ x * u x), h1, h2, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ PDE.euclideanBall (0 : Vec d) R
    · have hat : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => χ x * u x) x :=
        hχs.contDiffAt.mul (hu.contDiffAt (hopen.mem_nhds hx))
      refine hat.congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact indicator_of_mem hy _
    · have hxt : x ∉ tsupport χ := fun h => hx (hts h)
      have hn : (tsupport χ)ᶜ ∈ 𝓝 x := (isClosed_tsupport χ).isOpen_compl.mem_nhds hxt
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hn] with y hy
      by_cases hyb : y ∈ PDE.euclideanBall (0 : Vec d) R
      · rw [indicator_of_mem hyb, image_eq_zero_of_notMem_tsupport hy, zero_mul]
      · rw [indicator_of_notMem hyb]
  · intro x hx
    have hxR : x ∈ PDE.euclideanBall (0 : Vec d) R := PDE.euclideanBall_mono hρ'0 h2.le hx
    simp only [indicator_of_mem hxR]
    have h1x : χ x = 1 := PDE.canonicalBallCutoff_eq_one_on_inner hρ'0 h2 hx
    rw [h1x, one_mul]

theorem euclideanCoordDeriv_comp_add (f : Vec d → ℝ) (z : Vec d) (i : Fin d) :
    PDE.euclideanCoordDeriv i (fun x => f (x + z)) =
      fun x => PDE.euclideanCoordDeriv i f (x + z) := by
  funext x
  simp only [PDE.euclideanCoordDeriv]
  rw [fderiv_comp_add_right]

theorem laplacian_comp_add (f : Vec d → ℝ) (z x : Vec d) :
    PDE.euclideanCoordLaplacian (fun y => f (y + z)) x = PDE.euclideanCoordLaplacian f (x + z) := by
  simp only [PDE.euclideanCoordLaplacian, PDE.euclideanCoordSecondDeriv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [euclideanCoordDeriv_comp_add, fderiv_comp_add_right]

theorem laplacian_congr_of_eqOn {f g : Vec d → ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    (h : EqOn f g U) {x : Vec d} (hx : x ∈ U) :
    PDE.euclideanCoordLaplacian f x = PDE.euclideanCoordLaplacian g x := by
  have h1 : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h
  have h2 : ∀ i, PDE.euclideanCoordDeriv i f =ᶠ[𝓝 x] PDE.euclideanCoordDeriv i g := fun i => by
    filter_upwards [h1.fderiv (𝕜 := ℝ)] with y hy
    simp only [PDE.euclideanCoordDeriv, hy]
  simp only [PDE.euclideanCoordLaplacian, PDE.euclideanCoordSecondDeriv]
  exact Finset.sum_congr rfl fun i _ => by rw [(h2 i).fderiv_eq]

/-- `|B (x, …, x)| ≤ (∑_ι B(e_ι)²)^{1/2} |x|^m`. -/
theorem abs_diag_le {m : ℕ} (B : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec d) ℝ)
    (x : Vec d) :
    |B fun _ => x| ≤ Real.sqrt (∑ ι : Fin m → Fin d, (B fun l => Pi.single (ι l) 1) ^ 2) *
      euclideanNorm x ^ m := by
  have hexp : (B fun _ => x) =
      ∑ ι : Fin m → Fin d, (B fun l => Pi.single (ι l) 1) * ∏ l, x (ι l) := by
    rw [← PDE.eval_multilinearPoly B x]
    simp [PDE.multilinearPoly, PDE.basisVec]
  have hprod : ∑ ι : Fin m → Fin d, (∏ l, x (ι l)) ^ 2 = euclideanSq x ^ m := by
    have h := Finset.prod_univ_sum (t := fun (_ : Fin m) => (Finset.univ : Finset (Fin d)))
      (fun (_ : Fin m) (i : Fin d) => x i * x i)
    simp only [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    rw [euclideanSq, dot, h]
    exact Finset.sum_congr rfl fun ι _ => by rw [sq, ← Finset.prod_mul_distrib]
  have hsq : 0 ≤ euclideanSq x := by rw [euclideanSq, dot]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [hexp]
  refine (Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)).trans_eq ?_
  rw [Real.sqrt_mul (Finset.sum_nonneg fun ι _ => sq_nonneg _), hprod, euclideanNorm,
    show euclideanSq x ^ m = (Real.sqrt (euclideanSq x) ^ m) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hsq],
    Real.sqrt_sq (by positivity)]

/-- Translation of a weakly harmonic function: `x ↦ u(x + z)` is weakly harmonic in `B_s` when
`|z| + s ≤ b`. -/
theorem isL2HarmonicOn_comp_add {b s : ℝ} {u : Vec d → ℝ}
    (hu : IsL2HarmonicOn 1 (ball (0 : Vec d) b) u) {z : Vec d} (hz : euclideanNorm z + s ≤ b) :
    IsL2HarmonicOn 1 (ball (0 : Vec d) s) (fun x => u (x + z)) := by
  obtain ⟨hL2, g, hg, hgrad, hdiv⟩ := hu
  have hV : ∀ x ∈ ball (0 : Vec d) s, (1 : ℝ) • x + z ∈ ball (0 : Vec d) b := fun x hx => by
    rw [one_smul]
    rw [mem_ball_zero_iff'] at hx ⊢
    linarith [euclideanNorm_add_le' x z]
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) s)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 s)
  have h1 := MemLp.comp_smul_add_restrict (measurableSet_ball' 0 b) (measurableSet_ball' 0 s)
    one_ne_zero z hV hL2
  have h2 : ∀ i, MemLp (fun x => g ((1 : ℝ) • x + z) i) 2 (volume.restrict (ball 0 s)) := fun i =>
    MemLp.comp_smul_add_restrict (f := fun x => g x i) (measurableSet_ball' 0 b)
      (measurableSet_ball' 0 s) one_ne_zero z hV (hg i)
  have hw := hasWeakGradientOn_comp_smul_add one_pos z hV hgrad
  have hw' : HasWeakGradient (ball 0 s) (fun x => (1 : ℝ)⁻¹ * u ((1 : ℝ) • x + z))
      (fun x => g ((1 : ℝ) • x + z)) :=
    hasWeakGradient_of_hasWeakGradientOn' hw
      (IntegrableOn.locallyIntegrableOn ((h1.const_mul (1 : ℝ)⁻¹).integrable one_le_two))
      (fun i => IntegrableOn.locallyIntegrableOn ((h2 i).integrable one_le_two))
  have hd := TwoScale.hasWeakDivergence_comp_smul_add one_pos z hV hdiv
    (fun i => by
      simpa only [Matrix.one_mulVec] using
        IntegrableOn.locallyIntegrableOn ((h2 i).integrable one_le_two))
  simp only [one_smul, inv_one, one_mul] at h1 h2 hw' hd
  exact ⟨h1, fun x => g (x + z), h2, hw', hd⟩

theorem setAverage_ball_eq_integralAverage {s : ℝ} (hs : 0 < s) (f : Vec d → ℝ) :
    ⨍ x in ball (0 : Vec d) s, f x = PDE.integralAverage (PDE.euclideanBall (0 : Vec d) s) f := by
  unfold PDE.integralAverage
  rw [ball_zero_eq_pdeEuclideanBall hs, setAverage_eq, smul_eq_mul, measureReal_def]

/-- The derivative bound at the points of `B_{b/2}`: for `u` weakly harmonic in `B_b` with smooth
representative `v` and `|z| ≤ b/2`,
`(∑_ι Dᵐ v(z)(e_ι)²)^{1/2} ≤ (C m/(b/2))ᵐ 2^{d/2} ‖u - (u)_{B_b}‖_{L̲²(B_b)}`. -/
theorem frob_iteratedFDeriv_le {b : ℝ} (hb : 0 < b) (hd : 0 < d) {u v : Vec d → ℝ}
    (hu : IsL2HarmonicOn 1 (ball (0 : Vec d) b) u)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (PDE.euclideanBall 0 b))
    (hΔ : ∀ y ∈ PDE.euclideanBall (0 : Vec d) b, PDE.euclideanCoordLaplacian v y = 0)
    (hae : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) b)), v x = u x)
    {z : Vec d} (hz : euclideanNorm z ≤ b / 2) (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt (∑ ι : Fin m → Fin d, (iteratedFDeriv ℝ m v z (fun l => Pi.single (ι l) 1)) ^ 2) ≤
      (PDE.harmonicPointwiseConst d * m / (b / 2)) ^ m *
        (Real.sqrt (2 ^ d) * scalarRms volume (ball 0 b) (fun x => u x - ⨍ y in ball 0 b, u y)) := by
  have hs : 0 < b / 2 := half_pos hb
  have huz := isL2HarmonicOn_comp_add hu (s := b / 2) (z := z) (by linarith)
  obtain ⟨hL2, g, hgL2, hgrad, hdiv⟩ := huz
  have hsol := isWeakDivergenceFormSolutionOn_toH1Function hs hL2 hgL2 hgrad hdiv
  have hmaps : ∀ x ∈ PDE.euclideanBall (0 : Vec d) (b / 2), x + z ∈ PDE.euclideanBall 0 b := by
    intro x hx
    rw [← ball_zero_eq_pdeEuclideanBall hs] at hx
    rw [← ball_zero_eq_pdeEuclideanBall hb, mem_ball_zero_iff']
    rw [mem_ball_zero_iff'] at hx
    linarith [euclideanNorm_add_le' x z]
  have hvz : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => v (x + z)) (PDE.euclideanBall 0 (b / 2)) :=
    hv.comp (contDiff_id.add contDiff_const).contDiffOn hmaps
  have hΔz : ∀ y ∈ PDE.euclideanBall (0 : Vec d) (b / 2),
      PDE.euclideanCoordLaplacian (fun x => v (x + z)) y = 0 := fun y hy => by
    rw [laplacian_comp_add]; exact hΔ _ (hmaps y hy)
  have haez : ∀ᵐ x ∂(volume.restrict (PDE.euclideanBall (0 : Vec d) (b / 2))),
      v (x + z) = u (x + z) := by
    rw [← ball_zero_eq_pdeEuclideanBall hs, ae_restrict_iff' (measurableSet_ball' 0 _)]
    have h := (measurePreserving_add_right (volume : Measure (Vec d)) z).quasiMeasurePreserving.ae
      ((ae_restrict_iff' (measurableSet_ball' 0 b)).1 hae)
    filter_upwards [h] with x hx hxs
    refine hx ?_
    rw [← ball_zero_eq_pdeEuclideanBall hb] at hmaps
    rw [← ball_zero_eq_pdeEuclideanBall hs] at hmaps
    exact hmaps x hxs
  have hbound := (PDE.harmonicPointwise_of_representative hd hs
    (toH1Function hs hL2 hgL2 hgrad) hvz hΔz haez).2 m hm
  have hit : iteratedFDeriv ℝ m (fun x => v (x + z)) 0 = iteratedFDeriv ℝ m v z := by
    rw [iteratedFDeriv_comp_add_right, zero_add]
  rw [hit] at hbound
  refine hbound.trans (mul_le_mul_of_nonneg_left ?_ (by
    have := PDE.harmonicPointwiseConst_pos hd
    positivity))
  have hosc : Real.sqrt (PDE.integralAverage (PDE.euclideanBall (0 : Vec d) (b / 2))
      (fun x => (u (x + z) - PDE.integralAverage (PDE.euclideanBall (0 : Vec d) (b / 2))
        (fun y => u (y + z))) ^ 2)) =
      scalarRms volume (ball 0 (b / 2)) (fun x => u (z + x) - ⨍ y in ball 0 (b / 2), u (z + y)) := by
    rw [scalarRms_ball_eq_sqrt_integralAverage hs, setAverage_ball_eq_integralAverage hs]
    simp only [add_comm z]
  change Real.sqrt (PDE.integralAverage (PDE.euclideanBall (0 : Vec d) (b / 2))
      (fun x => (u (x + z) - PDE.integralAverage (PDE.euclideanBall (0 : Vec d) (b / 2))
        (fun y => u (y + z))) ^ 2)) ≤ _
  rw [hosc]
  have h2 := scalarRms_translate_le (f := u) (w := z) hs hz (by
    rw [show 2 * (b / 2) = b by ring]; exact hu.1)
  rwa [show 2 * (b / 2) = b by ring] at h2

/-- **(3.24) for harmonic functions on balls, every order**: for `u` weakly harmonic in `B_b`
there is a harmonic polynomial `P` of degree at most `k` (the Taylor polynomial at `0` of the smooth
representative of `u`) with `‖u - P‖_{L̲²(B_t)} ≤ C (t/b)^{k+1} ‖u - (u)_{B_b}‖_{L̲²(B_b)}` for
`t ≤ b/4`, with `C` depending only on `k` and `d`. -/
theorem harmonicTaylorBall (hd : 0 < d) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 0 < b → ∀ u : Vec d → ℝ, IsL2HarmonicOn 1 (ball (0 : Vec d) b) u →
      ∃ P : MvPolynomial (Fin d) ℝ, P.totalDegree ≤ k ∧
        (∀ x, PDE.euclideanCoordLaplacian (fun y => MvPolynomial.eval y P) x = 0) ∧
        ∀ t : ℝ, 0 < t → t ≤ b / 4 →
          scalarRms volume (ball 0 t) (fun x => u x - MvPolynomial.eval x P) ≤
            C * (t / b) ^ (k + 1) *
              scalarRms volume (ball 0 b) (fun x => u x - ⨍ y in ball 0 b, u y) := by
  have hCW := PDE.harmonicPointwiseConst_pos hd
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (2 * PDE.harmonicPointwiseConst d * ((k : ℝ) + 1)) ^ (k + 1) *
      Real.sqrt (2 ^ d) / ((k + 1).factorial : ℝ) := ⟨_, rfl⟩
  have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C, hC0, fun b hb u hu => ?_⟩
  obtain ⟨huL2, g, hgL2, hgrad, hdiv⟩ := hu
  have hsol := isWeakDivergenceFormSolutionOn_toH1Function hb huL2 hgL2 hgrad hdiv
  obtain ⟨v, hvs, hvh, hvae, -⟩ :=
    PDE.exists_harmonicWeylRepresentative hd hb (toH1Function hb huL2 hgL2 hgrad) hsol
  obtain ⟨hvan, -⟩ :=
    PDE.harmonicPointwise_of_representative hd hb (toH1Function hb huL2 hgL2 hgrad) hvs hvh hvae
  have hvae' : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) b)), v x = u x := by
    rw [ball_zero_eq_pdeEuclideanBall hb]; exact hvae
  have hE : ∀ {s : ℝ}, 0 < s → (0 : Vec d) ∈ PDE.euclideanBall 0 s := fun hs => by
    rw [← ball_zero_eq_pdeEuclideanBall hs, mem_ball_zero_iff']
    simpa [euclideanNorm, euclideanSq, dot] using hs
  have hsym : ∀ n, IsSymm (iteratedFDeriv ℝ n v 0) :=
    isSymm_iteratedFDeriv_of_analyticAt (hvan 0 (hE hb))
  obtain ⟨ρ', v', hρ1, hρ2, hv', heq⟩ :=
    exists_contDiff_top_localization hvs (half_pos hb) (half_lt_self hb)
  have hρ'0 : 0 < ρ' := lt_trans (half_pos hb) hρ1
  have hev : v' =ᶠ[𝓝 (0 : Vec d)] v :=
    Filter.eventuallyEq_of_mem ((PDE.isOpen_euclideanBall 0 ρ').mem_nhds (hE hρ'0)) heq
  have hiter : ∀ n, iteratedFDeriv ℝ n v' 0 = iteratedFDeriv ℝ n v 0 := fun n =>
    (hev.iteratedFDeriv ℝ n).eq_of_nhds
  have hP : PDE.taylorPoly v' k = PDE.taylorPoly v k := by
    unfold PDE.taylorPoly; simp only [hiter]
  have hΔ' : ∀ᶠ y in 𝓝 (0 : Vec d), PDE.euclideanCoordLaplacian v' y = 0 := by
    filter_upwards [(PDE.isOpen_euclideanBall 0 ρ').mem_nhds (hE hρ'0)] with y hy
    rw [laplacian_congr_of_eqOn (PDE.isOpen_euclideanBall 0 ρ') heq hy]
    exact hvh y (PDE.euclideanBall_mono hρ'0.le hρ2.le hy)
  refine ⟨PDE.taylorPoly v k, PDE.taylorPoly_totalDegree_le v k, fun x => ?_, fun t ht htb => ?_⟩
  · rw [← hP]
    exact laplacian_eval_taylorPoly hv' hΔ' (fun n => by rw [hiter]; exact hsym n) k x
  obtain ⟨osc, hosc⟩ : ∃ o : ℝ,
      o = scalarRms volume (ball 0 b) (fun x => u x - ⨍ y in ball 0 b, u y) := ⟨_, rfl⟩
  rw [← hosc]
  have hosc0 : 0 ≤ osc := by rw [hosc]; exact scalarRms_nonneg _ _
  have hM : 0 ≤ C * (t / b) ^ (k + 1) * osc := by positivity
  have hpt : ∀ x ∈ ball (0 : Vec d) t,
      |v x - MvPolynomial.eval x (PDE.taylorPoly v k)| ≤ C * (t / b) ^ (k + 1) * osc := by
    intro x hx
    have hxn : euclideanNorm x < t := mem_ball_zero_iff'.1 hx
    have hxE : x ∈ PDE.euclideanBall (0 : Vec d) b := by
      rw [← ball_zero_eq_pdeEuclideanBall hb, mem_ball_zero_iff']; linarith
    obtain ⟨ξ, hξ, htay⟩ := PDE.taylor_line (PDE.isOpen_euclideanBall 0 b)
      (fun _ hy _ hτ => PDE.euclideanBall_smul_mem hy hτ) hvs hxE k
    rw [PDE.eval_taylorPoly, htay, add_sub_cancel_left, abs_div, abs_of_pos hfac]
    have hξx : euclideanNorm (ξ • x) ≤ b / 2 := by
      rw [euclideanNorm_smul_of_zero_le ξ hξ.1.le]
      have := euclideanNorm_nonneg x
      nlinarith [hξ.2]
    have hF := frob_iteratedFDeriv_le hb hd ⟨huL2, g, hgL2, hgrad, hdiv⟩ hvs hvh hvae' hξx (k + 1)
      (by omega)
    rw [← hosc] at hF
    push_cast at hF
    have hdiag := abs_diag_le (iteratedFDeriv ℝ (k + 1) v (ξ • x)) x
    have hxt : euclideanNorm x ^ (k + 1) ≤ t ^ (k + 1) :=
      pow_le_pow_left₀ (euclideanNorm_nonneg x) hxn.le _
    have hb2 : 0 < b / 2 := half_pos hb
    calc |iteratedFDeriv ℝ (k + 1) v (ξ • x) (fun _ => x)| / ((k + 1).factorial : ℝ)
        ≤ ((PDE.harmonicPointwiseConst d * ((k : ℝ) + 1) / (b / 2)) ^ (k + 1) *
            (Real.sqrt (2 ^ d) * osc)) * t ^ (k + 1) / ((k + 1).factorial : ℝ) :=
          div_le_div_of_nonneg_right (hdiag.trans (mul_le_mul hF hxt
            (pow_nonneg (euclideanNorm_nonneg x) _)
            (mul_nonneg (pow_nonneg (by positivity) _) (mul_nonneg (Real.sqrt_nonneg _) hosc0))))
            hfac.le
      _ = C * (t / b) ^ (k + 1) * osc := by
          have e1 : PDE.harmonicPointwiseConst d * ((k : ℝ) + 1) / (b / 2) =
              (2 * PDE.harmonicPointwiseConst d * ((k : ℝ) + 1)) * b⁻¹ := by
            field_simp
          rw [e1, hC, mul_pow, div_pow, inv_pow]
          ring
  have hsub : ball (0 : Vec d) t ⊆ PDE.euclideanBall 0 b := fun x hx => by
    rw [← ball_zero_eq_pdeEuclideanBall hb, mem_ball_zero_iff']
    have := mem_ball_zero_iff'.1 hx; linarith
  have hcont : ContinuousOn (fun x => v x - MvPolynomial.eval x (PDE.taylorPoly v k))
      (ball 0 t) := (hvs.continuousOn.mono hsub).sub (MvPolynomial.continuous_eval _).continuousOn
  have hcongr : scalarRms volume (ball 0 t) (fun x => u x - MvPolynomial.eval x (PDE.taylorPoly v k)) =
      scalarRms volume (ball 0 t) (fun x => v x - MvPolynomial.eval x (PDE.taylorPoly v k)) := by
    unfold scalarRms
    congr 1
    refine average_congr ?_
    have h := ae_restrict_of_ae_restrict_of_subset
      (ball_zero_subset_ball_zero (by linarith : t ≤ b)) hvae'
    filter_upwards [h] with x hx
    rw [hx]
  rw [hcongr]
  have hvol : 0 < volume.real (ball (0 : Vec d) t) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (volume_ball_ne_zero' 0 ht) (volume_ball_ne_top' 0 t)
  refine scalarRms_le_of_integral_sq_le hvol hM ?_
  have : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) t)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_ne_top' 0 t)
  have hcont2 : ContinuousOn (fun x => (v x - MvPolynomial.eval x (PDE.taylorPoly v k)) ^ 2)
      (ball 0 t) := fun x hx => (hcont x hx).pow 2
  have hint : IntegrableOn (fun x => (v x - MvPolynomial.eval x (PDE.taylorPoly v k)) ^ 2)
      (ball 0 t) :=
    Integrable.of_bound (hcont2.aestronglyMeasurable (measurableSet_ball' 0 t))
      ((C * (t / b) ^ (k + 1) * osc) ^ 2)
      ((ae_restrict_iff' (measurableSet_ball' 0 t)).2 (Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hpt x hx) 2))
  calc ∫ x in ball 0 t, (v x - MvPolynomial.eval x (PDE.taylorPoly v k)) ^ 2
      ≤ ∫ x in ball 0 t, (C * (t / b) ^ (k + 1) * osc) ^ 2 :=
        setIntegral_mono_on hint (integrableOn_const (volume_ball_ne_top' 0 t))
          (measurableSet_ball' 0 t) (fun x hx => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hpt x hx) 2)
    _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_comm]

end TaylorHarmonic

end QSH
