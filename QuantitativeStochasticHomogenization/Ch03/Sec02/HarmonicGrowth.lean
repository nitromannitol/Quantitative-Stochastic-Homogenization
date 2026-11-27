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

end QSH
