import QuantitativeStochasticHomogenization.Ch01.Sec05.HarmonicInterior

/-!
# The interior estimates (1.61) for constant coefficients

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 1.5, Step 0 of the proof of Theorem 1.17: for a constant symmetric matrix `A` with
`Id ≤ A ≤ Λ Id`, a weak solution `u ∈ H¹(U)` of `-∇·(A∇u) = 0` has a smooth function `ũ` with
`∇ũ = ∇u` almost everywhere near every point `x₀` with `B_ρ(x₀) ⊆ U`, and
`|∇^k ũ(x₀)| ≤ C ρ^{1-k-d/2} ‖∇u‖_{L²(U)}` for `k = 1, 2, 3`
(`exists_smooth_interior_bound_of_constant`), with `C(d, Λ)`.

The proof is the change of variables `x = M y` with `M = A^{1/2}`: `u(M ·)` is weakly harmonic on
`M⁻¹ U` (`HasWeakDivergence.comp_linearImage`), its mollification `v` satisfies the bounds of
`exists_smooth_harmonic_interior_bound`, and `ũ = v(M⁻¹ ·)`; since `|M⁻¹ w| ≤ |w|`, the entries
of `M⁻¹` are at most `1` and `|det M⁻¹| ≤ d!`.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

namespace TwoScale

variable {d : ℕ}

/-- **Uniqueness of weak gradients on open sets** against a smooth representative: if `φ` is
smooth, `φ = f` almost everywhere on the open set `V` and `G` is a weak gradient of `f` on `V`,
then `∇φ = G` almost everywhere on `V`. -/
theorem ae_gradient_eq_of_ae_eq {V : Set (Vec d)} (hV : IsOpen V) {f : Vec d → ℝ}
    {G : Vec d → Vec d} (hG : HasWeakGradient V f G) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hfφ : ∀ᵐ x ∂(volume.restrict V), φ x = f x) :
    ∀ᵐ x ∂(volume.restrict V), gradient φ x = G x := by
  have hcomp : ∀ i, ∀ᵐ x ∂(volume.restrict V), G x i - coordinateDerivative i φ x = 0 := by
    intro i
    have hcont : Continuous (coordinateDerivative i φ) :=
      continuous_coordinateDerivative (hφ.of_le (by simp)) i
    have hloc : LocallyIntegrableOn (fun x => G x i - coordinateDerivative i φ x) V volume :=
      (hG i).2.1.sub (hcont.locallyIntegrable.locallyIntegrableOn V)
    have h := hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun ψ hψ hψc hψV => by
      have htest : IsSpatialTest V ψ := ⟨hψ, hψc, hψV⟩
      have hzero : ∀ x, x ∉ V → ψ x • (G x i - coordinateDerivative i φ x) = 0 := fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψV h)), zero_smul]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
      have i1 : IntegrableOn (fun x => G x i * ψ x) V := integrableOn_mul_spatialTest (hG i).2.1 htest
      have i2 : IntegrableOn (fun x => coordinateDerivative i φ x * ψ x) V :=
        integrableOn_mul_spatialTest (hcont.locallyIntegrable.locallyIntegrableOn V) htest
      have e1 := (hG i).2.2 ψ htest
      have e2 := setIntegral_mul_coordinateDerivative_of_contDiff hφ htest i
      have e3 : ∫ x in V, φ x * coordinateDerivative i ψ x =
          ∫ x in V, f x * coordinateDerivative i ψ x :=
        integral_congr_ae (by filter_upwards [hfφ] with x hx; rw [hx])
      have e4 : ∫ x in V, ψ x • (G x i - coordinateDerivative i φ x) =
          (∫ x in V, G x i * ψ x) - ∫ x in V, coordinateDerivative i φ x * ψ x := by
        rw [← integral_sub i1 i2]
        exact integral_congr_ae (Eventually.of_forall fun x => by
          simp only [smul_eq_mul]; ring)
      rw [e4]
      linarith
    rw [ae_restrict_iff' hV.measurableSet]
    exact h
  have hall := ae_all_iff.2 hcomp
  filter_upwards [hall] with x hx
  funext i
  have := hx i
  show coordinateDerivative i φ x = G x i
  linarith

theorem euclideanSq_pos_of_ne_zero {x : Vec d} (hx : x ≠ 0) : 0 < euclideanSq x := by
  unfold euclideanSq dot
  have h0 : ∀ i ∈ Finset.univ, 0 ≤ x i * x i := fun i _ => mul_self_nonneg _
  rcases (Finset.sum_nonneg h0).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg h0).1 h.symm i (Finset.mem_univ i)
    simpa using this

/-- **The square root of a constant elliptic matrix.** For `A` symmetric with `|ξ|² ≤ ξ·Aξ` there
is an invertible symmetric `M` with `M M = A`. -/
theorem exists_sqrt_of_elliptic {A : Mat d} (hAt : A.transpose = A)
    (hA0 : ∀ ξ, euclideanSq ξ ≤ dot ξ (A.mulVec ξ)) :
    ∃ M : Mat d, M.det ≠ 0 ∧ M.transpose = M ∧ M * M = A := by
  have hApd : A.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hAt
    · rw [star_trivial]
      exact (euclideanSq_pos_of_ne_zero hx).trans_le (hA0 x)
  obtain ⟨hMpsd, hMM⟩ := _root_.Homogenization.HighContrast.matSqrt_spec hApd.posSemidef
  have hMt : (_root_.Homogenization.HighContrast.matSqrt A).transpose =
      _root_.Homogenization.HighContrast.matSqrt A := by
    have h := hMpsd.isHermitian
    unfold Matrix.IsHermitian at h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact ⟨_, ((Matrix.isUnit_iff_isUnit_det _).1
    (_root_.Homogenization.HighContrast.isUnit_matSqrt hApd)).ne_zero, hMt, hMM⟩

theorem euclideanSq_mulVec_eq {M A : Mat d} (hMt : M.transpose = M) (hMM : M * M = A)
    (w : Vec d) : euclideanSq (M.mulVec w) = dot w (A.mulVec w) := by
  unfold euclideanSq
  change dotProduct (M.mulVec w) (M.mulVec w) = dotProduct w (A.mulVec w)
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hMt, Matrix.mulVec_mulVec, hMM,
    dotProduct_comm]

theorem abs_apply_le_sqrt_euclideanSq (x : Vec d) (i : Fin d) :
    |x i| ≤ Real.sqrt (euclideanSq x) := by
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  unfold euclideanSq dot
  rw [sq]
  exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

theorem sq_apply_le_euclideanSq (x : Vec d) (i : Fin d) : x i ^ 2 ≤ euclideanSq x := by
  unfold euclideanSq dot
  rw [sq]
  exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

theorem abs_sum_mul_le_of_abs_le_one {c a : Fin d → ℝ} (hc : ∀ l, |c l| ≤ 1) {B : ℝ}
    (ha : ∀ l, |a l| ≤ B) : |∑ l, c l * a l| ≤ d * B := by
  calc |∑ l, c l * a l| ≤ ∑ l, |c l * a l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin d, B := Finset.sum_le_sum fun l _ => by
        rw [abs_mul]
        exact (mul_le_mul (hc l) (ha l) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = d * B := by simp

/-- **The interior estimates (1.61)** for a constant matrix `Id ≤ A ≤ Λ Id`, `d ≥ 1`: there is
`C(d, Λ)` such that for every open `U`, every weak solution `u ∈ H¹(U)` of `-∇·(A∇u) = 0` with
gradient `g` and every `ρ > 0` there is a smooth `ũ` such that, at every `x₀` with `B_ρ(x₀) ⊆ U`,
`∇ũ = g` almost everywhere on a neighbourhood of `x₀` and
`|∂_i ũ(x₀)| ≤ C (ρ^{-d})^{1/2} ‖g‖_{L²(U)}`, `|∂_j ∂_i ũ(x₀)| ≤ C ρ⁻¹ (ρ^{-d})^{1/2} ‖g‖_{L²(U)}`,
`|∂_k ∂_j ∂_i ũ(x₀)| ≤ C ρ⁻² (ρ^{-d})^{1/2} ‖g‖_{L²(U)}`. -/
theorem exists_smooth_interior_bound_of_constant (hd : 0 < d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : Mat d), A.transpose = A →
      (∀ ξ, euclideanSq ξ ≤ dot ξ (A.mulVec ξ)) →
      (∀ ξ, dot ξ (A.mulVec ξ) ≤ Λ * euclideanSq ξ) →
      ∀ (U : Set (Vec d)), IsOpen U → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      MemLp u 2 (volume.restrict U) → MemLp g 2 (volume.restrict U) →
      HasWeakGradient U u g → HasWeakDivergence U (fun x => A.mulVec (g x)) (fun _ => 0) →
      ∀ ρ : ℝ, 0 < ρ → ∃ ũ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ũ ∧
        ∀ x₀ : Vec d, (∀ z, euclideanNorm (z - x₀) < ρ → z ∈ U) →
          (∃ V : Set (Vec d), IsOpen V ∧ x₀ ∈ V ∧
            ∀ᵐ x ∂(volume.restrict V), gradient ũ x = g x) ∧
          (∀ i, |coordinateDerivative i ũ x₀| ≤
            C * Real.sqrt (ρ⁻¹ ^ d) * Real.sqrt (∫ x in U, euclideanSq (g x))) ∧
          (∀ i j, |coordinateDerivative j (coordinateDerivative i ũ) x₀| ≤
            C * ρ⁻¹ * Real.sqrt (ρ⁻¹ ^ d) * Real.sqrt (∫ x in U, euclideanSq (g x))) ∧
          (∀ i j k, |coordinateDerivative k (coordinateDerivative j (coordinateDerivative i ũ)) x₀|
            ≤ C * ρ⁻¹ ^ 2 * Real.sqrt (ρ⁻¹ ^ d) *
              Real.sqrt (∫ x in U, euclideanSq (g x))) := by
  obtain ⟨Ch, hCh, hharm⟩ := exists_smooth_harmonic_interior_bound (d := d) hd
  set q : ℝ := 4 * Real.sqrt Λ with hq
  have hsΛ : 1 ≤ Real.sqrt Λ := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hΛ
  have hq1 : 1 ≤ q := by rw [hq]; linarith
  have hq0 : 0 < q := by linarith
  have hsΛ0 : 0 < Real.sqrt Λ := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  set C : ℝ := (d : ℝ) ^ 3 * Ch * q ^ 2 * Real.sqrt (q ^ d) *
    Real.sqrt (Λ * (Nat.factorial d : ℝ)) with hC
  refine ⟨C, by positivity, fun A hAt hA0 hA1 U hUo u g hu hg hw hdiv ρ hρ => ?_⟩
  obtain ⟨M, hdet, hMt, hMM⟩ := exists_sqrt_of_elliptic hAt hA0
  have hMsq := euclideanSq_mulVec_eq hMt hMM
  set N : Mat d := M⁻¹ with hN
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hdet)
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.2 hdet)
  have hNdet : N.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det M (isUnit_iff_ne_zero.2 hdet)).ne_zero
  have hMNw : ∀ w, M.mulVec (N.mulVec w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]
  have hNMw : ∀ w, N.mulVec (M.mulVec w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
  -- `|N w| ≤ |w|`, entries of `N` bounded by `1`, `|det N| ≤ d!`
  have hNsq : ∀ w, euclideanSq (N.mulVec w) ≤ euclideanSq w := fun w => by
    have h := hA0 (N.mulVec w)
    rwa [← hMsq, hMNw] at h
  have hNentry : ∀ a b, |N a b| ≤ 1 := fun a b => by
    have h1 := abs_apply_le_sqrt_euclideanSq (N.mulVec (unitVector b)) a
    have h2 : N.mulVec (unitVector b) a = N a b := by
      simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
    have h3 : euclideanSq (unitVector (d := d) b) = 1 := by
      simp [euclideanSq, dot, unitVector, Pi.single_apply]
    rw [h2] at h1
    refine h1.trans ?_
    rw [← Real.sqrt_one, ← h3]
    exact Real.sqrt_le_sqrt (hNsq _)
  have hNdetle : |N.det| ≤ (Nat.factorial d : ℝ) := by
    have h := Matrix.det_le (abv := AbsoluteValue.abs) (x := (1 : ℝ)) (A := N) hNentry
    simpa using h
  have hMdetinv : |M.det|⁻¹ ≤ (Nat.factorial d : ℝ) := by
    have : N.det = (M.det)⁻¹ := by
      rw [hN, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    rw [← abs_inv, ← this]
    exact hNdetle
  -- the transformed problem on `S = M⁻¹ U`
  set S : Set (Vec d) := Matrix.toLin' M ⁻¹' U with hS
  have hSo : IsOpen S := hUo.preimage (Matrix.toLin' M).continuous_of_finiteDimensional
  have himage : Matrix.toLin' M '' S = U := by
    refine Set.image_preimage_eq U fun x => ⟨N.mulVec x, ?_⟩
    rw [Matrix.toLin'_apply, hMNw]
  have hgi : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U) := fun i => hg.eval i
  have hu' : MemLp (fun y => u (M.mulVec y)) 2 (volume.restrict S) :=
    MemLp.comp_matrixEllipsoid hdet (h := u) (by rw [← linearImage_eq_image, himage]; exact hu)
  have hg' : ∀ i, MemLp (fun y => (M.transpose.mulVec (g (M.mulVec y))) i) 2
      (volume.restrict S) := by
    intro i
    have h : MemLp (fun y => ∑ k, M k i * g (M.mulVec y) k) 2 (volume.restrict S) :=
      memLp_finsetSum _ fun k _ => (MemLp.comp_matrixEllipsoid hdet (h := fun x => g x k)
        (by rw [← linearImage_eq_image, himage]; exact hgi k)).const_mul (M k i)
    refine h.ae_eq (Eventually.of_forall fun y => ?_)
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have hw' := HasWeakGradient.comp_linearImage hdet hSo (h := u) (g := g)
    (by rw [himage]; exact hw)
  have hdiv' := HasWeakDivergence.comp_linearImage hdet hSo (g := g)
    (by rw [himage]; exact fun k => (hw k).2.1)
    (by rw [himage, hMt, hMM]; exact hdiv)
  set δ : ℝ := ρ / q with hδ
  have hδ0 : 0 < δ := div_pos hρ hq0
  obtain ⟨v, hvs, hv⟩ := hharm S hSo (fun y => u (M.mulVec y))
    (fun y => M.transpose.mulVec (g (M.mulVec y))) hu' hg' hw' hdiv' δ hδ0
  -- the bound of the transformed gradient
  set Gn := Real.sqrt (∫ x in U, euclideanSq (g x)) with hGn
  have hG' : ∀ a, Real.sqrt (∫ y in S, (M.transpose.mulVec (g (M.mulVec y))) a ^ 2) ≤
      Real.sqrt (Λ * (Nat.factorial d : ℝ)) * Gn := by
    intro a
    rw [hGn, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have hint : IntegrableOn (fun x => euclideanSq (g x)) U := by
      have h : Integrable (fun x => ∑ k, g x k ^ 2) (volume.restrict U) :=
        integrable_finsetSum _ fun k _ => (hgi k).integrable_sq
      refine h.congr (Eventually.of_forall fun x => ?_)
      simp [euclideanSq, dot, sq]
    have hintS : IntegrableOn (fun y => euclideanSq (g (M.mulVec y))) S :=
      IntegrableOn.comp_matrixEllipsoid hdet (h := fun x => euclideanSq (g x))
        (by rw [← linearImage_eq_image, himage]; exact hint)
    have hcv : ∫ y in S, euclideanSq (g (M.mulVec y)) = |M.det|⁻¹ * ∫ x in U, euclideanSq (g x) := by
      rw [← himage, setIntegral_linearImage hdet S, ← mul_assoc,
        inv_mul_cancel₀ (abs_ne_zero.2 hdet), one_mul]
    have hI0 : 0 ≤ ∫ x in U, euclideanSq (g x) :=
      setIntegral_nonneg hUo.measurableSet fun x _ => by
        unfold euclideanSq dot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    calc ∫ y in S, (M.transpose.mulVec (g (M.mulVec y))) a ^ 2
        ≤ ∫ y in S, Λ * euclideanSq (g (M.mulVec y)) := by
          refine setIntegral_mono (hg' a).integrable_sq (hintS.const_mul Λ) fun y => ?_
          refine (sq_apply_le_euclideanSq _ a).trans ?_
          rw [hMt, hMsq]
          exact hA1 _
      _ = Λ * (|M.det|⁻¹ * ∫ x in U, euclideanSq (g x)) := by rw [integral_const_mul, hcv]
      _ ≤ Λ * ((Nat.factorial d : ℝ) * ∫ x in U, euclideanSq (g x)) := by
          gcongr
      _ = Λ * (Nat.factorial d : ℝ) * ∫ x in U, euclideanSq (g x) := by ring
  refine ⟨fun x => v (N.mulVec x), hvs.comp (matrixCLE N hNdet).contDiff, fun x₀ hx₀ => ?_⟩
  set y₀ := N.mulVec x₀ with hy₀
  have hball : PDE.euclideanBall y₀ (4 * δ) ⊆ S := by
    intro y hy
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)] at hy
    change Matrix.toLin' M y ∈ U
    rw [Matrix.toLin'_apply]
    refine hx₀ _ ?_
    have e : M.mulVec y - x₀ = M.mulVec (y - y₀) := by
      rw [Matrix.mulVec_sub, hy₀, hMNw]
    rw [e]
    have h1 : euclideanSq (M.mulVec (y - y₀)) ≤ Λ * euclideanSq (y - y₀) := by
      rw [hMsq]; exact hA1 _
    have h2 : euclideanNorm (M.mulVec (y - y₀)) ≤ Real.sqrt Λ * euclideanNorm (y - y₀) := by
      unfold euclideanNorm
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt h1
    have h3 : euclideanNorm (y - y₀) < 4 * δ := hy
    have h4 : Real.sqrt Λ * (4 * δ) = ρ := by
      rw [hδ, hq]; field_simp
    calc euclideanNorm (M.mulVec (y - y₀)) ≤ Real.sqrt Λ * euclideanNorm (y - y₀) := h2
      _ < Real.sqrt Λ * (4 * δ) := mul_lt_mul_of_pos_left h3 (by linarith)
      _ = ρ := h4
  obtain ⟨hae, hder⟩ := hv y₀ hball
  -- powers of `δ⁻¹ = q ρ⁻¹`
  have hδinv : δ⁻¹ = q * ρ⁻¹ := by rw [hδ, inv_div, div_eq_mul_inv]
  have hsq : Real.sqrt (δ⁻¹ ^ d) = Real.sqrt (q ^ d) * Real.sqrt (ρ⁻¹ ^ d) := by
    rw [hδinv, mul_pow, Real.sqrt_mul (by positivity)]
  have hρi : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
  have hbound : ∀ (n : ℕ), n ≤ 2 → ∀ (a : Fin d) (ι : Fin n → Fin d),
      |PDE.iteratedCoordDeriv n ι (PDE.euclideanCoordDeriv a v) y₀| ≤
        Ch * q ^ 2 * Real.sqrt (q ^ d) * Real.sqrt (Λ * (Nat.factorial d : ℝ)) *
          ρ⁻¹ ^ n * Real.sqrt (ρ⁻¹ ^ d) * Gn := by
    intro n hn a ι
    refine (hder a n hn ι).trans ?_
    rw [hsq, hδinv, mul_pow]
    have hqn : q ^ n ≤ q ^ 2 := pow_le_pow_right₀ hq1 hn
    have hG := hG' a
    have h0 : 0 ≤ Real.sqrt (∫ y in S, (M.transpose.mulVec (g (M.mulVec y))) a ^ 2) :=
      Real.sqrt_nonneg _
    calc Ch * (q ^ n * ρ⁻¹ ^ n) * (Real.sqrt (q ^ d) * Real.sqrt (ρ⁻¹ ^ d)) *
          Real.sqrt (∫ y in S, (M.transpose.mulVec (g (M.mulVec y))) a ^ 2)
        ≤ Ch * (q ^ 2 * ρ⁻¹ ^ n) * (Real.sqrt (q ^ d) * Real.sqrt (ρ⁻¹ ^ d)) *
          (Real.sqrt (Λ * (Nat.factorial d : ℝ)) * Gn) := by
          gcongr
      _ = _ := by ring
  set B : ℕ → ℝ := fun n => Ch * q ^ 2 * Real.sqrt (q ^ d) *
    Real.sqrt (Λ * (Nat.factorial d : ℝ)) * ρ⁻¹ ^ n * Real.sqrt (ρ⁻¹ ^ d) * Gn with hB
  have hB0 : ∀ n, 0 ≤ B n := fun n => by rw [hB]; positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨?_, fun i => ?_, fun i j => ?_, fun i j k => ?_⟩
  · -- the gradient equals `g` near `x₀`
    set e := matrixMeasurableEquiv M hdet
    refine ⟨Matrix.toLin' M '' PDE.euclideanBall y₀ δ,
      (matrixCLE M hdet).toHomeomorph.isOpenMap _ (PDE.isOpen_euclideanBall _ _),
      ⟨y₀, PDE.center_mem_euclideanBall y₀ hδ0, by rw [Matrix.toLin'_apply, hy₀, hMNw]⟩, ?_⟩
    have hVo : IsOpen (Matrix.toLin' M '' PDE.euclideanBall y₀ δ) :=
      (matrixCLE M hdet).toHomeomorph.isOpenMap _ (PDE.isOpen_euclideanBall _ _)
    have hVU : Matrix.toLin' M '' PDE.euclideanBall y₀ δ ⊆ U := by
      rw [← himage]
      exact Set.image_mono ((PDE.euclideanBall_mono hδ0.le (by linarith)).trans hball)
    have hmap : ∀ᵐ x ∂(Measure.map e (volume.restrict (PDE.euclideanBall y₀ δ))),
        v (N.mulVec x) = u x := by
      rw [e.measurableEmbedding.ae_map_iff]
      filter_upwards [hae] with y hy
      rw [matrixMeasurableEquiv_apply, hNMw]
      exact hy
    rw [map_restrict_matrixMeasurableEquiv hdet,
      Measure.ae_ennreal_smul_measure_iff (by simpa using hdet)] at hmap
    exact ae_gradient_eq_of_ae_eq hVo (HasWeakGradient.mono hVU hw)
      (hvs.comp (matrixCLE N hNdet).contDiff) hmap
  · -- first derivatives
    rw [coordinateDerivative_comp_mulVec hNdet v i x₀]
    have h := abs_sum_mul_le_of_abs_le_one (c := fun l => N l i) (fun l => hNentry l i)
      (a := fun l => coordinateDerivative l v (N.mulVec x₀)) (B := B 0)
      (fun l => hbound 0 (by norm_num) l Fin.elim0)
    refine h.trans ?_
    have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by
      calc (d : ℝ) = (d : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (d : ℝ) ^ 3 := pow_le_pow_right₀ hd1 (by norm_num)
    calc (d : ℝ) * B 0 ≤ (d : ℝ) ^ 3 * B 0 := mul_le_mul_of_nonneg_right hd3 (hB0 0)
      _ = C * Real.sqrt (ρ⁻¹ ^ d) * Gn := by rw [hB, hC]; ring
  · -- second derivatives
    rw [coordinateDerivative_coordinateDerivative_comp_mulVec hNdet hvs i j x₀]
    have hin : ∀ l, |∑ k, N l i * N k j *
        coordinateDerivative k (coordinateDerivative l v) (N.mulVec x₀)| ≤ d * B 1 := by
      intro l
      have e : ∀ k, N l i * N k j * coordinateDerivative k (coordinateDerivative l v)
          (N.mulVec x₀) = N k j * (N l i * coordinateDerivative k (coordinateDerivative l v)
          (N.mulVec x₀)) := fun k => by ring
      simp_rw [e]
      refine abs_sum_mul_le_of_abs_le_one (fun k => hNentry k j) fun k => ?_
      rw [abs_mul]
      have hb := hbound 1 (by norm_num) l ![k]
      have hb' : |coordinateDerivative k (coordinateDerivative l v) (N.mulVec x₀)| ≤ B 1 := hb
      exact (mul_le_mul (hNentry l i) hb' (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    calc |∑ l, ∑ k, N l i * N k j *
          coordinateDerivative k (coordinateDerivative l v) (N.mulVec x₀)|
        ≤ ∑ l, |∑ k, N l i * N k j *
          coordinateDerivative k (coordinateDerivative l v) (N.mulVec x₀)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin d, (d : ℝ) * B 1 := Finset.sum_le_sum fun l _ => hin l
      _ = (d : ℝ) ^ 2 * B 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ (d : ℝ) ^ 3 * B 1 := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hd1 (by norm_num)) (hB0 1)
      _ = C * ρ⁻¹ * Real.sqrt (ρ⁻¹ ^ d) * Gn := by rw [hB, hC]; ring
  · -- third derivatives
    have h2 : coordinateDerivative j (coordinateDerivative i (fun x => v (N.mulVec x))) =
        fun x => ∑ p : Fin d × Fin d, (N p.1 i * N p.2 j) *
          coordinateDerivative p.2 (coordinateDerivative p.1 v) (N.mulVec x) := by
      funext x
      rw [coordinateDerivative_coordinateDerivative_comp_mulVec hNdet hvs i j x,
        ← Finset.univ_product_univ, Finset.sum_product]
    have hdiff : ∀ p : Fin d × Fin d, Differentiable ℝ
        (fun x => coordinateDerivative p.2 (coordinateDerivative p.1 v) (N.mulVec x)) :=
      fun p => ((contDiff_coordinateDerivative_top (contDiff_coordinateDerivative_top hvs p.1)
        p.2).differentiable (by simp)).comp (matrixCLE N hNdet).differentiable
    rw [h2, coordinateDerivative_sum_const_mul _ _ hdiff]
    have hin : ∀ p : Fin d × Fin d, |(N p.1 i * N p.2 j) *
        coordinateDerivative k (fun x => coordinateDerivative p.2 (coordinateDerivative p.1 v)
          (N.mulVec x)) x₀| ≤ d * B 2 := by
      intro p
      rw [coordinateDerivative_comp_mulVec hNdet _ k x₀, abs_mul]
      have hc : |N p.1 i * N p.2 j| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul (hNentry _ _) (hNentry _ _) (abs_nonneg _) zero_le_one).trans_eq
          (one_mul _)
      have hs := abs_sum_mul_le_of_abs_le_one (c := fun q' => N q' k) (fun q' => hNentry q' k)
        (a := fun q' => coordinateDerivative q' (coordinateDerivative p.2
          (coordinateDerivative p.1 v)) (N.mulVec x₀)) (B := B 2)
        (fun q' => hbound 2 le_rfl p.1 ![q', p.2])
      exact (mul_le_mul hc hs (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    calc |∑ p : Fin d × Fin d, (N p.1 i * N p.2 j) *
          coordinateDerivative k (fun x => coordinateDerivative p.2
            (coordinateDerivative p.1 v) (N.mulVec x)) x₀|
        ≤ ∑ p : Fin d × Fin d, |(N p.1 i * N p.2 j) *
          coordinateDerivative k (fun x => coordinateDerivative p.2
            (coordinateDerivative p.1 v) (N.mulVec x)) x₀| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : Fin d × Fin d, (d : ℝ) * B 2 := Finset.sum_le_sum fun p _ => hin p
      _ = (d : ℝ) ^ 3 * B 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul]; push_cast; ring
      _ = C * ρ⁻¹ ^ 2 * Real.sqrt (ρ⁻¹ ^ d) * Gn := by rw [hB, hC]; ring

end TwoScale

end QSH
