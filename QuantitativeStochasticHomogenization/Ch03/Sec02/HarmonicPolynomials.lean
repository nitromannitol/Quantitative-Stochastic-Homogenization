import QuantitativeStochasticHomogenization.Ch03.Sec02.HarmonicTaylorBall
import QuantitativeStochasticHomogenization.Ch03.Sec03.EllipsoidSmoothTransfer
import PDEFoundation.Monotonicity.Core.Homogeneous

/-!
# The `A`-harmonic polynomials and (3.24) for `A`-harmonic functions, every order

`harmonicPolys A k` is the space `Ā_k` of the `A`-harmonic polynomials of degree at most `k`
(the polynomials of total degree at most `k` that are weakly `A`-harmonic on every ball). For a
symmetric `A` with `1 ≤ A ≤ Λ`, an `A`-harmonic `h` in `B_ρ` is approximated by an element `q` of
`Ā_k` with `‖h - q‖_{L̲²(B_t)} ≤ C (t/ρ)^{k+1} ‖h‖_{L̲²(B_ρ)}` for `t ≤ ρ/(4√Λ)`
(`exists_harmonicPoly_scalarRms_ball_le`), from the case of the Laplacian (`harmonicTaylorBall`)
and the change of variables `x = M y`, `M Mᵀ = A`, as for `k = 1` (`exists_affine_scalarRms_ball_le`).
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-- The `A`-harmonic polynomials of degree at most `k`, `Ā_k`. -/
def harmonicPolys (A : Mat d) (k : ℕ) : Set (Vec d → ℝ) :=
  {p | (∃ P : MvPolynomial (Fin d) ℝ, P.totalDegree ≤ k ∧ ∀ x, p x = MvPolynomial.eval x P) ∧
    ∀ ρ : ℝ, 0 < ρ → IsL2HarmonicOn A (ball 0 ρ) p}

theorem IsL2HarmonicOn.add' {A : Mat d} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IsL2HarmonicOn A U f) (hg : IsL2HarmonicOn A U g) :
    IsL2HarmonicOn A U (fun x => f x + g x) := by
  obtain ⟨hf1, gf, hgf, hf2, hf3⟩ := hf
  obtain ⟨hg1, gg, hgg, hg2, hg3⟩ := hg
  refine ⟨hf1.add hg1, fun x => gf x + gg x, fun i => (hgf i).add (hgg i),
    hasWeakGradient_add hf2 hg2, ?_⟩
  have h := hasWeakDivergence_add hf3 hg3
  convert h using 1
  · funext x; rw [Matrix.mulVec_add]
  · funext x; simp

theorem IsL2HarmonicOn.const_mul'' {A : Mat d} {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : IsL2HarmonicOn A U f) (c : ℝ) : IsL2HarmonicOn A U (fun x => c * f x) := by
  obtain ⟨hf1, gf, hgf, hf2, hf3⟩ := hf
  refine ⟨hf1.const_mul c, fun x => c • gf x, fun i => ?_, hf2.const_mul' c, ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using (hgf i).const_mul c
  · convert hf3.const_smul' c using 2 with x
    rw [Matrix.mulVec_smul]

theorem IsL2HarmonicOn.sub' {A : Mat d} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IsL2HarmonicOn A U f) (hg : IsL2HarmonicOn A U g) :
    IsL2HarmonicOn A U (fun x => f x - g x) := by
  have h := hf.add' (hg.const_mul'' (-1))
  convert h using 2 with x
  ring

theorem zero_mem_harmonicPolys (A : Mat d) (k : ℕ) : (fun _ => (0 : ℝ)) ∈ harmonicPolys A k := by
  refine ⟨⟨0, by simp, fun x => by simp⟩, fun ρ _ => ⟨MemLp.zero, fun _ => 0,
    fun _ => MemLp.zero, hasWeakGradient_mono (subset_univ _) (hasWeakGradient_const 0), ?_⟩⟩
  simpa only [Matrix.mulVec_zero] using
    (hasWeakDivergence_const_field (0 : Vec d)).mono' (subset_univ (ball (0 : Vec d) ρ))

theorem add_mem_harmonicPolys {A : Mat d} {k : ℕ} {p q : Vec d → ℝ} (hp : p ∈ harmonicPolys A k)
    (hq : q ∈ harmonicPolys A k) : (fun x => p x + q x) ∈ harmonicPolys A k := by
  obtain ⟨⟨P, hP, hPe⟩, hph⟩ := hp
  obtain ⟨⟨Q, hQ, hQe⟩, hqh⟩ := hq
  refine ⟨⟨P + Q, (MvPolynomial.totalDegree_add P Q).trans (max_le hP hQ), fun x => ?_⟩,
    fun ρ hρ => (hph ρ hρ).add' (hqh ρ hρ)⟩
  show p x + q x = _
  rw [hPe x, hQe x, map_add]

theorem eval_bind₁' (f : Fin d → MvPolynomial (Fin d) ℝ) (P : MvPolynomial (Fin d) ℝ)
    (x : Vec d) :
    MvPolynomial.eval x (MvPolynomial.bind₁ f P) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (f i)) P := by
  induction P using MvPolynomial.induction_on <;> simp_all

theorem totalDegree_bind₁_le (f : Fin d → MvPolynomial (Fin d) ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (P : MvPolynomial (Fin d) ℝ) :
    (MvPolynomial.bind₁ f P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  calc ∑ i ∈ s.support, ((f i) ^ (s i)).totalDegree ≤ ∑ i ∈ s.support, s i :=
        Finset.sum_le_sum fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
          (by simpa using Nat.mul_le_mul_left (s i) (hf i))
    _ = s.sum fun _ e => e := rfl
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hs

/-- A polynomial composed with a linear map is a polynomial of at most the same degree. -/
theorem exists_poly_comp_mulVec (N : Mat d) (P : MvPolynomial (Fin d) ℝ) :
    ∃ Q : MvPolynomial (Fin d) ℝ, Q.totalDegree ≤ P.totalDegree ∧
      ∀ x, MvPolynomial.eval x Q = MvPolynomial.eval (N.mulVec x) P := by
  refine ⟨MvPolynomial.bind₁ (fun i => ∑ j, MvPolynomial.C (N i j) * MvPolynomial.X j) P,
    totalDegree_bind₁_le _ (fun i => ?_) P, fun x => ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · have e : (fun i => MvPolynomial.eval x (∑ j, MvPolynomial.C (N i j) * MvPolynomial.X j)) =
        N.mulVec x := by
      funext i
      simp [Matrix.mulVec, dotProduct]
    rw [eval_bind₁', e]

/-- **(3.24) for `A`-harmonic functions on balls, every order**: for a symmetric `A` with
`1 ≤ A ≤ Λ` and `h` `A`-harmonic in `B_ρ`, there is `q ∈ Ā_k` with
`‖h - q‖_{L̲²(B_t)} ≤ C (t/ρ)^{k+1} ‖h‖_{L̲²(B_ρ)}` for `t ≤ ρ/(4√Λ)`, with `C(k, d, Λ)`. -/
theorem exists_harmonicPoly_scalarRms_ball_le (hd : 2 ≤ d) (hΛ : 1 ≤ Λ) (k : ℕ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ A : Mat d, A.transpose = A → HomogenizedMatrixBounds A Λ →
      ∀ ρ : ℝ, 0 < ρ → ∀ h : Vec d → ℝ, IsL2HarmonicOn A (ball 0 ρ) h →
      ∃ q ∈ harmonicPolys A k, ∀ t : ℝ, 0 < t → t ≤ ρ / (4 * Real.sqrt Λ) →
        scalarRms volume (ball 0 t) (fun x => h x - q x) ≤
          C₁ * (t / ρ) ^ (k + 1) * scalarRms volume (ball 0 ρ) h := by
  obtain ⟨C, hC, hball⟩ := TaylorHarmonic.harmonicTaylorBall (d := d) (by omega) k
  have hΛ0 : 0 < Λ := by linarith
  have hsΛ : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ0
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = Real.sqrt (Real.sqrt Λ ^ d) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact Real.sqrt_nonneg _
  refine ⟨C * Real.sqrt Λ ^ (k + 1) * κ, by positivity, ?_⟩
  intro A hsym hA ρ hρ h hh
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
  have hMA : M * M.transpose = A := by
    rw [hMM, hsym, ← two_smul ℝ A, smul_smul]
    norm_num
  have hA' : HomogenizedMatrixBounds (M * M.transpose) Λ := by rw [hMA]; exact hA
  have hsym' : (M * M.transpose).transpose = M * M.transpose := by rw [hMA]; exact hsym
  have hdet1 := one_le_abs_det hdet hA'
  have hdet0 : 0 < |M.det| := by linarith
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = ρ / Real.sqrt Λ := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbdef]; exact div_pos hρ hsΛ
  have hρb : Real.sqrt Λ * b = ρ := by rw [hbdef]; field_simp
  have hEB : matrixEllipsoid M b ⊆ ball 0 ρ := by
    have := matrixEllipsoid_subset_ball_sqrt hdet hΛ0 hA' hsym' b
    rwa [hρb] at this
  have hhA : IsL2HarmonicOn (M * M.transpose) (ball 0 ρ) h := by rw [hMA]; exact hh
  have hhE : IsL2HarmonicOn (M * M.transpose) (matrixEllipsoid M b) h := hhA.mono hEB
  have hL2 : MemLp h 2 (volume.restrict (ball 0 ρ)) := hh.1
  have hhM := hhE.comp_matrixEllipsoid hdet
  obtain ⟨P, hPdeg, hPharm, hdec⟩ := hball b hb _ hhM
  obtain ⟨Q, hQdeg, hQe⟩ := exists_poly_comp_mulVec M⁻¹ P
  have hq : (fun x => MvPolynomial.eval (M⁻¹.mulVec x) P) ∈ harmonicPolys A k := by
    refine ⟨⟨Q, hQdeg.trans hPdeg, fun x => (hQe x).symm⟩, fun ρ' hρ' => ?_⟩
    have hE := isL2HarmonicOn_comp_inv hdet hρ' (PDE.contDiff_eval_mvPolynomial P)
      (fun y _ => hPharm y)
    rw [hMA] at hE
    exact hE.mono (ball_subset_matrixEllipsoid hdet hA' ρ')
  refine ⟨_, hq, fun t ht htb => ?_⟩
  have hvolEB : volume.real (ball (0 : Vec d) ρ) ≤
      (Real.sqrt Λ ^ d / |M.det|) * volume.real (matrixEllipsoid M b) := by
    rw [volume_real_matrixEllipsoid, ← hρb, volume_real_ball_mul hsΛ b]
    apply le_of_eq
    field_simp
  have hEb : scalarRms volume (matrixEllipsoid M b) h ≤
      Real.sqrt (Real.sqrt Λ ^ d / |M.det|) * scalarRms volume (ball 0 ρ) h :=
    scalarRms_le_sqrt_mul_of_subset hEB (volume_matrixEllipsoid_ne_zero hdet hb)
      (volume_ball_ne_top' 0 ρ) hvolEB (by positivity) hL2.integrable_sq
  have hrms0 := scalarRms_nonneg (d := d) (ball 0 ρ) h
  have htb' : t ≤ b / 4 := by
    rw [hbdef, div_div, mul_comm (Real.sqrt Λ) 4]; exact htb
  have htb1 : t ≤ b := by linarith
  have hEtB : matrixEllipsoid M t ⊆ ball 0 ρ := (matrixEllipsoid_mono M htb1).trans hEB
  have hqL2 : MemLp (fun x => MvPolynomial.eval (M⁻¹.mulVec x) P) 2 (volume.restrict (ball 0 ρ)) :=
    (hq.2 ρ hρ).1
  have hmem : MemLp (fun x => h x - MvPolynomial.eval (M⁻¹.mulVec x) P) 2
      (volume.restrict (matrixEllipsoid M t)) :=
    (hL2.sub hqL2).mono_measure (Measure.restrict_mono hEtB le_rfl)
  have h1 : scalarRms volume (ball 0 t) (fun x => h x - MvPolynomial.eval (M⁻¹.mulVec x) P) ≤
      Real.sqrt |M.det| * scalarRms volume (matrixEllipsoid M t)
        (fun x => h x - MvPolynomial.eval (M⁻¹.mulVec x) P) :=
    scalarRms_le_sqrt_mul_of_subset (ball_subset_matrixEllipsoid hdet hA' t)
      (volume_ball_ne_zero' 0 ht) (volume_matrixEllipsoid_lt_top M t).ne
      (volume_real_matrixEllipsoid M t).le (abs_nonneg _) hmem.integrable_sq
  have hosc : scalarRms volume (ball 0 b) (fun y => h (M.mulVec y) -
      ⨍ z in ball 0 b, h (M.mulVec z)) ≤ scalarRms volume (matrixEllipsoid M b) h := by
    rw [scalarRms_matrixEllipsoid_eq hdet b]
    refine (scalarRms_sub_setAverage_le_sub_const (volume_ball_ne_top' 0 b) hhM.1 0).trans ?_
    simp only [sub_zero, le_refl]
  have h2 : scalarRms volume (matrixEllipsoid M t)
      (fun x => h x - MvPolynomial.eval (M⁻¹.mulVec x) P) ≤
      C * (t / b) ^ (k + 1) * scalarRms volume (matrixEllipsoid M b) h := by
    rw [scalarRms_matrixEllipsoid_eq hdet t]
    have e : (fun y => h (M.mulVec y) - MvPolynomial.eval (M⁻¹.mulVec (M.mulVec y)) P) =
        fun y => h (M.mulVec y) - MvPolynomial.eval y P := by
      funext y
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.2 hdet),
        Matrix.one_mulVec]
    rw [e]
    exact (hdec t ht htb').trans (mul_le_mul_of_nonneg_left hosc (by positivity))
  have htb2 : (t / b) ^ (k + 1) = Real.sqrt Λ ^ (k + 1) * (t / ρ) ^ (k + 1) := by
    rw [← mul_pow]
    congr 1
    rw [hbdef]
    field_simp
  have hdetk : Real.sqrt |M.det| * Real.sqrt (Real.sqrt Λ ^ d / |M.det|) = κ := by
    rw [← Real.sqrt_mul (abs_nonneg _), hκ, mul_div_cancel₀ _ hdet0.ne']
  calc scalarRms volume (ball 0 t) (fun x => h x - MvPolynomial.eval (M⁻¹.mulVec x) P)
      ≤ Real.sqrt |M.det| * (C * (t / b) ^ (k + 1) * scalarRms volume (matrixEllipsoid M b) h) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
    _ ≤ Real.sqrt |M.det| * (C * (t / b) ^ (k + 1) *
          (Real.sqrt (Real.sqrt Λ ^ d / |M.det|) * scalarRms volume (ball 0 ρ) h)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEb (by positivity))
          (Real.sqrt_nonneg _)
    _ = C * Real.sqrt Λ ^ (k + 1) * κ * (t / ρ) ^ (k + 1) * scalarRms volume (ball 0 ρ) h := by
        rw [htb2, ← hdetk]
        ring

end QSH
