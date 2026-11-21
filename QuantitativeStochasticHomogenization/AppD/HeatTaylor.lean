import QuantitativeStochasticHomogenization.AppD.HeatEquation

/-!
# Appendix D: the Taylor formula of the heat semigroup

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D (Sobolev norms and heat flow): for a smooth compactly supported `χ` and `m ≥ 1`,
`χ = ∑_{k<m} (-1)^k/k! Φ(1) ∗ Δ^k χ - 1/(m-1)! ∫₀¹ (-s)^{m-1} Φ(s) ∗ Δ^m χ ds`
(`heatTaylor`), obtained by integrating the derivative of `s ↦ ∑_{k<m} (-s)^k/k! Φ(s) ∗ Δ^k χ`,
which telescopes to `(-s)^{m-1}/(m-1)! Φ(s) ∗ Δ^m χ`.
-/

open MeasureTheory Filter Set
open scoped ContDiff Topology Nat

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The iterated Laplacian `Δ^k χ`. -/
def iterLaplacian (k : ℕ) (χ : Vec d → ℝ) : Vec d → ℝ := coordLaplacian^[k] χ

theorem contDiff_coordLaplacian {χ : Vec d → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (coordLaplacian χ) := by
  show ContDiff ℝ ∞ (fun x => ∑ j, coordinateDerivative j (coordinateDerivative j χ) x)
  exact ContDiff.sum fun j _ => contDiff_coordinateDerivative (contDiff_coordinateDerivative hχ j) j

theorem hasCompactSupport_coordLaplacian {χ : Vec d → ℝ} (hcχ : HasCompactSupport χ) :
    HasCompactSupport (coordLaplacian χ) := by
  have hj : ∀ j, HasCompactSupport (coordinateDerivative j (coordinateDerivative j χ)) := fun j =>
    hasCompactSupport_coordinateDerivative (hasCompactSupport_coordinateDerivative hcχ j) j
  refine (isCompact_iUnion fun j => hj j).of_isClosed_subset (isClosed_tsupport _) ?_
  refine closure_minimal (fun x hx => ?_) (isClosed_iUnion_of_finite fun j => isClosed_tsupport _)
  by_contra hnot
  simp only [mem_iUnion, not_exists] at hnot
  apply hx
  show ∑ j, coordinateDerivative j (coordinateDerivative j χ) x = 0
  exact Finset.sum_eq_zero fun j _ => image_eq_zero_of_notMem_tsupport (hnot j)

theorem iterLaplacian_smooth {χ : Vec d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (k : ℕ) : ContDiff ℝ ∞ (iterLaplacian k χ) ∧ HasCompactSupport (iterLaplacian k χ) := by
  induction k with
  | zero => exact ⟨hχ, hcχ⟩
  | succ k ih =>
    rw [iterLaplacian, Function.iterate_succ_apply']
    exact ⟨contDiff_coordLaplacian ih.1, hasCompactSupport_coordLaplacian ih.2⟩

theorem iterLaplacian_succ (k : ℕ) (χ : Vec d → ℝ) :
    iterLaplacian (k + 1) χ = coordLaplacian (iterLaplacian k χ) := by
  rw [iterLaplacian, iterLaplacian, Function.iterate_succ_apply']

/-- `s ↦ Φ(s) ∗ f (x)` for `s > 0`, extended by `f(x)` at `s ≤ 0`. -/
def heatPath (f : Vec d → ℝ) (x : Vec d) (s : ℝ) : ℝ :=
  if s ≤ 0 then f x else heatSmooth s f x

theorem heatPath_of_pos {f : Vec d → ℝ} {x : Vec d} {s : ℝ} (hs : 0 < s) :
    heatPath f x s = heatSmooth s f x := by
  simp [heatPath, not_le.mpr hs]

theorem continuousOn_heatPath {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (x : Vec d) : ContinuousOn (heatPath f x) (Ici 0) := by
  intro s hs
  rcases (mem_Ici.mp hs).eq_or_lt with h0 | hpos
  · subst h0
    have hlim := tendsto_heatSmooth_zero hf.continuous hcf x
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have : heatPath f x 0 = f x := by simp [heatPath]
    rw [ContinuousWithinAt, this]
    exact hlim.congr' (eventually_nhdsWithin_of_forall fun t ht => (heatPath_of_pos ht).symm)
  · have hd := (hasDerivAt_heatSmooth hpos hf hcf x).continuousAt
    have hev : heatPath f x =ᶠ[𝓝 s] fun t => heatSmooth t f x := by
      filter_upwards [lt_mem_nhds hpos] with t ht
      exact heatPath_of_pos ht
    exact (hd.congr hev.symm).continuousWithinAt

/-- The function `Q(s) = ∑_{k<m} (-s)^k/k! Φ(s) ∗ Δ^k χ (x)`. -/
def heatTaylorSum (m : ℕ) (χ : Vec d → ℝ) (x : Vec d) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, (-s) ^ k / (k ! : ℝ) * heatPath (iterLaplacian k χ) x s

theorem hasDerivAt_heatTaylorSum {χ : Vec d → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (x : Vec d) {s : ℝ} (hs : 0 < s) (m : ℕ) :
    HasDerivAt (heatTaylorSum (m + 1) χ x)
      ((-s) ^ m / (m ! : ℝ) * heatPath (iterLaplacian (m + 1) χ) x s) s := by
  have hev : ∀ k, heatPath (iterLaplacian k χ) x =ᶠ[𝓝 s]
      fun t => heatSmooth t (iterLaplacian k χ) x := fun k => by
    filter_upwards [lt_mem_nhds hs] with t ht
    exact heatPath_of_pos ht
  have hpath : ∀ k, HasDerivAt (heatPath (iterLaplacian k χ) x)
      (heatPath (iterLaplacian (k + 1) χ) x s) s := fun k => by
    have h := (iterLaplacian_smooth hχ hcχ k)
    have hd := hasDerivAt_heatSmooth hs h.1 h.2 x
    rw [heatPath_of_pos hs, iterLaplacian_succ]
    exact hd.congr_of_eventuallyEq (hev k)
  induction m with
  | zero =>
    have h0 : heatTaylorSum 1 χ x = heatPath (iterLaplacian 0 χ) x := by
      funext t
      simp [heatTaylorSum]
    rw [h0]
    simpa using hpath 0
  | succ m ih =>
    have hsum : heatTaylorSum (m + 1 + 1) χ x = fun t => heatTaylorSum (m + 1) χ x t +
        (-t) ^ (m + 1) / ((m + 1) ! : ℝ) * heatPath (iterLaplacian (m + 1) χ) x t := by
      funext t
      simp only [heatTaylorSum]
      rw [Finset.sum_range_succ]
    rw [hsum]
    have hpow : HasDerivAt (fun t : ℝ => (-t) ^ (m + 1) / ((m + 1) ! : ℝ))
        (-((-s) ^ m / (m ! : ℝ))) s := by
      have h1 := ((hasDerivAt_neg' s).pow (m + 1)).div_const ((m + 1) ! : ℝ)
      convert h1 using 1
      rw [Nat.factorial_succ, Nat.cast_mul]
      have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hf : (m ! : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    have := ih.add (hpow.mul (hpath (m + 1)))
    convert this using 1
    ring

/-- **The Taylor formula of the heat semigroup**:
`χ(x) = ∑_{k≤m} (-1)^k/k! Φ(1) ∗ Δ^k χ (x) - ∫₀¹ (-s)^m/m! Φ(s) ∗ Δ^{m+1} χ (x) ds`. -/
theorem heatTaylor {χ : Vec d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (x : Vec d) (m : ℕ) :
    χ x = heatTaylorSum (m + 1) χ x 1 -
      ∫ s in (0 : ℝ)..1, (-s) ^ m / (m ! : ℝ) * heatPath (iterLaplacian (m + 1) χ) x s := by
  have hcont : ∀ k, ContinuousOn (heatPath (iterLaplacian k χ) x) (Icc 0 1) := fun k =>
    (continuousOn_heatPath (iterLaplacian_smooth hχ hcχ k).1 (iterLaplacian_smooth hχ hcχ k).2
      x).mono Icc_subset_Ici_self
  have hQ : ContinuousOn (heatTaylorSum (m + 1) χ x) (Icc 0 1) := by
    unfold heatTaylorSum
    exact continuousOn_finsetSum _ fun k _ =>
      ((continuous_neg.pow k).div_const _).continuousOn.mul (hcont k)
  have hQ' : IntervalIntegrable (fun s : ℝ => (-s) ^ m / (m ! : ℝ) *
      heatPath (iterLaplacian (m + 1) χ) x s) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact ((continuous_neg.pow m).div_const _).continuousOn.mul (hcont (m + 1))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hQ
    (fun s hs => hasDerivAt_heatTaylorSum hχ hcχ x hs.1 m) hQ'
  have h0 : heatTaylorSum (m + 1) χ x 0 = χ x := by
    unfold heatTaylorSum
    rw [Finset.sum_eq_single 0]
    · simp [heatPath, iterLaplacian]
    · intro k _ hk
      simp [zero_pow hk]
    · simp
  rw [hftc, h0]
  ring

end QSH
