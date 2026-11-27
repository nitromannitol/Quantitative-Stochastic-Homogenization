import PDEFoundation.Monotonicity.Core.TaylorPoly
import PDEFoundation.Sobolev.ClassicalLaplacian
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Taylor polynomials of harmonic functions are harmonic

For a symmetric continuous `n`-linear form `B` on `Vec d`, the diagonal `x ↦ B (x, …, x)` has
derivative `v ↦ n B (x, …, x, v)`, so its Laplacian is
`n (n - 1) ∑ᵢ B (x, …, x, eᵢ, eᵢ)`. For a smooth function `f` with `Δf = 0` near `0` and symmetric
derivatives at `0` (an analytic function), `∑ᵢ Dⁿ⁺² f(0) (x, …, x, eᵢ, eᵢ) = Dⁿ (Δf)(0) (x, …, x) = 0`,
hence the Taylor polynomial of `f` at `0` of every degree is harmonic. This is the statement of
Exercise 3.5 of Armstrong–Kuusi–Mourrat that the Taylor expansion of a harmonic function is harmonic.
-/

open Set Filter Topology

noncomputable section

namespace QSH

namespace TaylorHarmonic

variable {d : ℕ}

/-- A continuous multilinear form invariant under the permutations of its arguments. -/
def IsSymm {n : ℕ} (B : ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec d) ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (m : Fin n → Vec d), B (m ∘ σ) = B m

theorem snoc_const_apply {m : ℕ} (x v : Vec d) (k : Fin (m + 1)) :
    (Fin.snoc (fun _ : Fin m => x) v : Fin (m + 1) → Vec d) k =
      if k = Fin.last m then v else x := by
  induction k using Fin.lastCases with
  | last => simp
  | cast j => simp [Fin.snoc_castSucc, (Fin.castSucc_lt_last j).ne]

theorem update_const_eq_snoc_comp_swap {m : ℕ} (x v : Vec d) (i : Fin (m + 1)) :
    Function.update (fun _ : Fin (m + 1) => x) i v =
      (Fin.snoc (fun _ : Fin m => x) v : Fin (m + 1) → Vec d) ∘ Equiv.swap (Fin.last m) i := by
  funext j
  rw [Function.comp_apply, snoc_const_apply, Function.update_apply, Equiv.swap_apply_def]
  by_cases hji : j = i
  · subst hji
    by_cases hjl : j = Fin.last m
    · simp [hjl]
    · simp [hjl]
  · by_cases hjl : j = Fin.last m
    · subst hjl
      simp [hji, Ne.symm hji]
    · simp [hji, hjl]

/-- The derivative of the diagonal of a symmetric multilinear form. -/
theorem hasFDerivAt_diag {m : ℕ} (B : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => Vec d) ℝ)
    (hB : IsSymm B) (x : Vec d) :
    HasFDerivAt (fun y : Vec d => B fun _ => y)
      (((m : ℝ) + 1) • ContinuousMultilinearMap.curryRight B (fun _ : Fin m => x)) x := by
  have hδ : HasFDerivAt (fun y : Vec d => fun _ : Fin (m + 1) => y)
      (ContinuousLinearMap.pi fun _ : Fin (m + 1) => ContinuousLinearMap.id ℝ (Vec d)) x :=
    (ContinuousLinearMap.pi fun _ : Fin (m + 1) => ContinuousLinearMap.id ℝ (Vec d)).hasFDerivAt
  have h := (B.hasFDerivAt (fun _ => x)).comp x hδ
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  have e : ∀ i : Fin (m + 1), B (Function.update (fun _ => x) i v) =
      B (Fin.snoc (fun _ : Fin m => x) v) := fun i => by
    rw [update_const_eq_snoc_comp_swap, hB]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_pi',
    ContinuousLinearMap.coe_id', id_eq, ContinuousMultilinearMap.linearDeriv_apply,
    smul_apply, ContinuousMultilinearMap.curryRight_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

theorem fderiv_diag_apply {m : ℕ} (B : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => Vec d) ℝ)
    (hB : IsSymm B) (x v : Vec d) :
    fderiv ℝ (fun y : Vec d => B fun _ => y) x v =
      ((m : ℝ) + 1) * B (Fin.snoc (fun _ : Fin m => x) v) := by
  rw [(hasFDerivAt_diag B hB x).fderiv]
  simp

/-- Fixing the last argument of a multilinear form. -/
def fixLast {m : ℕ} (B : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => Vec d) ℝ) (v : Vec d) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec d) ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ v).compContinuousMultilinearMap
    (ContinuousMultilinearMap.curryRight B)

theorem fixLast_apply {m : ℕ} (B : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => Vec d) ℝ)
    (v : Vec d) (w : Fin m → Vec d) : fixLast B v w = B (Fin.snoc w v) := by
  simp [fixLast]

theorem isSymm_fixLast {m : ℕ} (B : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => Vec d) ℝ)
    (hB : IsSymm B) (v : Vec d) : IsSymm (fixLast B v) := by
  intro σ w
  rw [fixLast_apply, fixLast_apply]
  have e : (Fin.snoc (w ∘ σ) v : Fin (m + 1) → Vec d) =
      (Fin.snoc w v : Fin (m + 1) → Vec d) ∘
        (finSuccEquivLast.symm.permCongr (Equiv.optionCongr σ)) := by
    funext k
    induction k using Fin.lastCases with
    | last => simp [Equiv.permCongr_apply]
    | cast j => simp [Equiv.permCongr_apply]
  rw [e, hB]

/-- The pure second derivatives of the diagonal of a symmetric multilinear form. -/
theorem secondDeriv_diag {m : ℕ} (B : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 2) => Vec d) ℝ)
    (hB : IsSymm B) (x : Vec d) (i : Fin d) :
    PDE.euclideanCoordSecondDeriv i i (fun y : Vec d => B fun _ => y) x =
      ((m : ℝ) + 2) * (((m : ℝ) + 1) *
        B (Fin.snoc (Fin.snoc (fun _ : Fin m => x) (PDE.basisVec i)) (PDE.basisVec i))) := by
  have e : PDE.euclideanCoordDeriv i (fun y : Vec d => B fun _ => y) =
      fun y => ((m : ℝ) + 2) * fixLast B (PDE.basisVec i) (fun _ => y) := by
    funext y
    rw [PDE.euclideanCoordDeriv, fderiv_diag_apply B hB, fixLast_apply]
    push_cast
    ring_nf
  have hdiff : DifferentiableAt ℝ (fun y : Vec d => fixLast B (PDE.basisVec i) fun _ => y) x :=
    (hasFDerivAt_diag _ (isSymm_fixLast B hB _) x).differentiableAt
  rw [PDE.euclideanCoordSecondDeriv, e, fderiv_const_mul hdiff, smul_apply,
    smul_eq_mul, fderiv_diag_apply _ (isSymm_fixLast B hB _), fixLast_apply]

/-- The iterated derivatives of an analytic function are symmetric. -/
theorem isSymm_iteratedFDeriv_of_analyticAt {f : Vec d → ℝ} {x : Vec d} (hf : AnalyticAt ℝ f x)
    (n : ℕ) : IsSymm (iteratedFDeriv ℝ n f x) := by
  intro σ m
  have h : ContDiffWithinAt ℝ (⊤ : WithTop ℕ∞) f univ x := by
    rw [contDiffWithinAt_univ]; exact hf.contDiffAt
  have h2 := h.iteratedFDerivWithin_comp_perm uniqueDiffOn_univ (mem_univ x) m σ
  simpa only [iteratedFDerivWithin_univ] using h2

theorem secondDeriv_eq_fderiv_fderiv {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d)
    (y : Vec d) :
    PDE.euclideanCoordSecondDeriv i i f y =
      fderiv ℝ (fderiv ℝ f) y (PDE.basisVec i) (PDE.basisVec i) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)) y
  show fderiv ℝ (fun z => fderiv ℝ f z (PDE.basisVec i)) y (PDE.basisVec i) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- `∑ᵢ Dᵐ⁺² f(0) (x, …, x, eᵢ, eᵢ) = Dᵐ (Δf)(0) (x, …, x) = 0` for a smooth `f` harmonic near `0`. -/
theorem sum_iteratedFDeriv_snoc_snoc_eq_zero {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hΔ : ∀ᶠ y in 𝓝 (0 : Vec d), PDE.euclideanCoordLaplacian f y = 0) (m : ℕ) (x : Vec d) :
    ∑ i : Fin d, iteratedFDeriv ℝ (m + 2) f 0
      (Fin.snoc (Fin.snoc (fun _ : Fin m => x) (PDE.basisVec i)) (PDE.basisVec i)) = 0 := by
  obtain ⟨L, hL⟩ : ∃ L : (Vec d →L[ℝ] Vec d →L[ℝ] ℝ) →L[ℝ] ℝ,
      L = ∑ i : Fin d, (ContinuousLinearMap.apply ℝ ℝ (PDE.basisVec i)).comp
        (ContinuousLinearMap.apply ℝ (Vec d →L[ℝ] ℝ) (PDE.basisVec i)) := ⟨_, rfl⟩
  have hLapp : ∀ T : Vec d →L[ℝ] Vec d →L[ℝ] ℝ,
      L T = ∑ i : Fin d, T (PDE.basisVec i) (PDE.basisVec i) := fun T => by
    rw [hL]; simp
  have hf1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hf2 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ f)) :=
    hf1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hstep : ∀ i : Fin d, iteratedFDeriv ℝ (m + 2) f 0
      (Fin.snoc (Fin.snoc (fun _ : Fin m => x) (PDE.basisVec i)) (PDE.basisVec i)) =
      iteratedFDeriv ℝ m (fderiv ℝ (fderiv ℝ f)) 0 (fun _ => x) (PDE.basisVec i)
        (PDE.basisVec i) := fun i => by
    rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last,
      iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  have hcomp : iteratedFDeriv ℝ m (⇑L ∘ fderiv ℝ (fderiv ℝ f)) 0 =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ m (fderiv ℝ (fderiv ℝ f)) 0) :=
    L.iteratedFDeriv_comp_left hf2.contDiffAt (i := m) (by exact_mod_cast le_top)
  have hLf : (⇑L ∘ fderiv ℝ (fderiv ℝ f)) = PDE.euclideanCoordLaplacian f := by
    funext y
    rw [Function.comp_apply, hLapp, PDE.euclideanCoordLaplacian]
    exact Finset.sum_congr rfl fun i _ => (secondDeriv_eq_fderiv_fderiv hf i y).symm
  have hzero : iteratedFDeriv ℝ m (PDE.euclideanCoordLaplacian f) 0 = 0 := by
    have hΔ' : PDE.euclideanCoordLaplacian f =ᶠ[𝓝 (0 : Vec d)] fun _ => (0 : ℝ) := hΔ
    have h := (hΔ'.iteratedFDeriv ℝ m).eq_of_nhds
    rw [h, iteratedFDeriv_fun_zero]
    rfl
  rw [hLf, hzero] at hcomp
  have h := congrArg (fun T => T (fun _ : Fin m => x)) hcomp
  simp only [zero_apply, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, hLapp] at h
  rw [Finset.sum_congr rfl fun i _ => hstep i]
  exact h.symm

theorem contDiff_diag {n : ℕ} (B : ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec d) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => B fun _ => y) :=
  B.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)

/-- The Laplacian is linear on smooth functions. -/
theorem laplacian_sum_const_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ) {g : ι → Vec d → ℝ}
    (hg : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n)) (x : Vec d) :
    PDE.euclideanCoordLaplacian (fun y => ∑ n ∈ s, c n * g n y) x =
      ∑ n ∈ s, c n * PDE.euclideanCoordLaplacian (g n) x := by
  have hD : ∀ (h : ι → Vec d → ℝ), (∀ n, ContDiff ℝ (⊤ : ℕ∞) (h n)) → ∀ i : Fin d,
      PDE.euclideanCoordDeriv i (fun y => ∑ n ∈ s, c n * h n y) =
        fun y => ∑ n ∈ s, c n * PDE.euclideanCoordDeriv i (h n) y := by
    intro h hh i
    funext y
    have hdy : ∀ n, DifferentiableAt ℝ (h n) y := fun n => ((hh n).differentiable (by simp)) y
    rw [PDE.euclideanCoordDeriv, fderiv_fun_sum fun n _ => (hdy n).const_mul (c n)]
    simp only [FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [fderiv_const_mul (hdy n), smul_apply, smul_eq_mul, PDE.euclideanCoordDeriv]
  rw [PDE.euclideanCoordLaplacian]
  simp only [PDE.euclideanCoordSecondDeriv]
  have hD2 : ∀ i : Fin d, PDE.euclideanCoordDeriv i
      (PDE.euclideanCoordDeriv i (fun y => ∑ n ∈ s, c n * g n y)) =
      fun y => ∑ n ∈ s, c n * PDE.euclideanCoordDeriv i (PDE.euclideanCoordDeriv i (g n)) y := by
    intro i
    rw [hD g hg i]
    exact hD (fun n => PDE.euclideanCoordDeriv i (g n))
      (fun n => PDE.contDiff_euclideanCoordDeriv (hg n) i) i
  have e : ∀ i : Fin d, fderiv ℝ (PDE.euclideanCoordDeriv i (fun y => ∑ n ∈ s, c n * g n y)) x
      (PDE.basisVec i) = ∑ n ∈ s, c n * PDE.euclideanCoordSecondDeriv i i (g n) x := fun i => by
    have h := congrFun (hD2 i) x
    simpa only [PDE.euclideanCoordDeriv, PDE.euclideanCoordSecondDeriv] using h
  rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [PDE.euclideanCoordLaplacian, Finset.mul_sum]

theorem laplacian_const (c : ℝ) (x : Vec d) :
    PDE.euclideanCoordLaplacian (fun _ : Vec d => c) x = 0 := by
  have h : ∀ i : Fin d, PDE.euclideanCoordDeriv i (fun _ : Vec d => c) = fun _ => 0 := fun i => by
    funext y
    show fderiv ℝ (fun _ : Vec d => c) y (PDE.basisVec i) = 0
    simp
  simp [PDE.euclideanCoordLaplacian, PDE.euclideanCoordSecondDeriv, h]

/-- The Laplacian of the diagonal of `Dⁿ f(0)` vanishes for a smooth `f` harmonic near `0` with
symmetric derivatives at `0`. -/
theorem laplacian_diag_iteratedFDeriv {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hΔ : ∀ᶠ y in 𝓝 (0 : Vec d), PDE.euclideanCoordLaplacian f y = 0)
    (hsymm : ∀ n, IsSymm (iteratedFDeriv ℝ n f 0)) (n : ℕ) (x : Vec d) :
    PDE.euclideanCoordLaplacian (fun y : Vec d => iteratedFDeriv ℝ n f 0 fun _ => y) x = 0 := by
  match n with
  | 0 =>
    have e : (fun y : Vec d => iteratedFDeriv ℝ 0 f 0 fun _ => y) =
        fun _ => iteratedFDeriv ℝ 0 f 0 fun _ => 0 := by
      funext y; congr 1; exact Subsingleton.elim _ _
    rw [e, laplacian_const]
  | 1 =>
    have e : ∀ i : Fin d, PDE.euclideanCoordDeriv i
        (fun y : Vec d => iteratedFDeriv ℝ 1 f 0 fun _ => y) =
        fun _ => iteratedFDeriv ℝ 1 f 0 (Fin.snoc (fun _ : Fin 0 => (0 : Vec d)) (PDE.basisVec i)) :=
      fun i => by
        funext y
        rw [PDE.euclideanCoordDeriv, fderiv_diag_apply _ (hsymm 1)]
        have hs : (fun _ : Fin 0 => y) = fun _ => (0 : Vec d) := Subsingleton.elim _ _
        rw [hs]
        simp only [CharP.cast_eq_zero, zero_add, one_mul]
    rw [PDE.euclideanCoordLaplacian]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [PDE.euclideanCoordSecondDeriv, e i]
    simp
  | m + 2 =>
    rw [PDE.euclideanCoordLaplacian,
      Finset.sum_congr rfl fun i _ => secondDeriv_diag _ (hsymm (m + 2)) x i, ← Finset.mul_sum,
      ← Finset.mul_sum, sum_iteratedFDeriv_snoc_snoc_eq_zero hf hΔ m x, mul_zero, mul_zero]

/-- **The Taylor polynomials of a harmonic function are harmonic**: for a smooth `f` harmonic near
`0` with symmetric derivatives at `0` (for instance analytic at `0`), every Taylor polynomial of
`f` at `0` is harmonic on `ℝ^d`. -/
theorem laplacian_eval_taylorPoly {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hΔ : ∀ᶠ y in 𝓝 (0 : Vec d), PDE.euclideanCoordLaplacian f y = 0)
    (hsymm : ∀ n, IsSymm (iteratedFDeriv ℝ n f 0)) (k : ℕ) (x : Vec d) :
    PDE.euclideanCoordLaplacian (fun y => MvPolynomial.eval y (PDE.taylorPoly f k)) x = 0 := by
  have e : (fun y => MvPolynomial.eval y (PDE.taylorPoly f k)) =
      fun y => ∑ n ∈ Finset.range (k + 1),
        ((n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n f 0 (fun _ => y)) := by
    funext y; exact PDE.eval_taylorPoly f k y
  rw [e, laplacian_sum_const_mul _ _ (fun n => contDiff_diag (iteratedFDeriv ℝ n f 0)) x]
  exact Finset.sum_eq_zero fun n _ => by
    rw [laplacian_diag_iteratedFDeriv hf hΔ hsymm n x, mul_zero]

end TaylorHarmonic

end QSH
