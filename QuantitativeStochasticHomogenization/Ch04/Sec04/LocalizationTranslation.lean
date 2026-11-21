import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizedFamilyMeasurability

/-!
# Translation covariance of the localization of Section 4.4

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.4, pp. 155-156, and (0.9). Shifting the variable by `c` maps the `a`-harmonic functions
on `B_T(z)` to the `b`-harmonic functions on `B_T(z')`, where `b(y) = a(c + y)` and
`c + z' = z`. The shift preserves the admissible class, the objective `I` of the coordinate
minimization, the `L²` norm and the localized energy, so it maps least-norm coordinate minimizers
to least-norm coordinate minimizers, and `J₁^{(δ)}(a, z, r, p, q) = J₁^{(δ)}(T_z a, 0, r, p, q)`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ} {Λ : ℝ}

/-! ## Change of variables on balls -/

theorem preimage_add_ball {c z z' : Vec d} (hz : c + z' = z) (R : ℝ) :
    (fun y => c + y) ⁻¹' ball z R = ball z' R := by
  ext y
  simp only [Set.mem_preimage, ball, Set.mem_ofPred_eq]
  rw [← hz, add_sub_add_left_eq_sub]

theorem setIntegral_ball_add {c z z' : Vec d} (hz : c + z' = z) (R : ℝ) (f : Vec d → ℝ) :
    ∫ y in ball z' R, f (c + y) = ∫ y in ball z R, f y := by
  rw [← preimage_add_ball hz R]
  exact (measurePreserving_add_left volume c).setIntegral_preimage_emb
    (measurableEmbedding_addLeft c) f (ball z R)

theorem volume_ball_add {c z z' : Vec d} (hz : c + z' = z) (R : ℝ) :
    volume (ball z' R) = volume (ball z R) := by
  rw [← preimage_add_ball hz R]
  exact (measurePreserving_add_left volume c).measure_preimage
    (measurableSet_ball z R).nullMeasurableSet

theorem setAverage_ball_add {c z z' : Vec d} (hz : c + z' = z) (R : ℝ) (f : Vec d → ℝ) :
    ⨍ y in ball z' R, f (c + y) = ⨍ y in ball z R, f y := by
  rw [setAverage_eq, setAverage_eq, setIntegral_ball_add hz, Measure.real, Measure.real,
    volume_ball_add hz]

theorem measurePreserving_add_ball {c z z' : Vec d} (hz : c + z' = z) (R : ℝ) :
    MeasurePreserving (fun y => c + y) (ballMeasure z' R) (ballMeasure z R) := by
  have h := (measurePreserving_add_left volume c).restrict_preimage (measurableSet_ball z R)
  rwa [preimage_add_ball hz R] at h

theorem MemLp.ball_add {E : Type*} [NormedAddCommGroup E] {c z z' : Vec d} (hz : c + z' = z)
    {R : ℝ} {g : Vec d → E} (hg : MemLp g 2 (ballMeasure z R)) :
    MemLp (fun y => g (c + y)) 2 (ballMeasure z' R) :=
  hg.comp_measurePreserving (measurePreserving_add_ball hz R)

/-! ## Shifted tests -/

theorem IsSpatialTest.shift {c z z' : Vec d} (hz : c + z' = z) {R : ℝ} {φ : Vec d → ℝ}
    (hφ : IsSpatialTest (ball z' R) φ) : IsSpatialTest (ball z R) fun y => φ (y + -c) := by
  refine ⟨hφ.1.comp (contDiff_id.add contDiff_const), ?_, ?_⟩
  · exact hφ.2.1.comp_homeomorph (Homeomorph.addRight (-c))
  · have h := tsupport_comp_eq_preimage φ (Homeomorph.addRight (-c))
    change tsupport (φ ∘ (Homeomorph.addRight (-c))) ⊆ _
    rw [h]
    intro y hy
    have hy' : y + -c ∈ ball z' R := hφ.2.2 hy
    show euclideanNorm (y - z) < R
    have e : y - z = (y + -c) - z' := by rw [← hz]; abel
    rw [e]
    exact hy'

theorem coordinateDerivative_shift (c : Vec d) (φ : Vec d → ℝ) (i : Fin d) (y : Vec d) :
    coordinateDerivative i (fun y => φ (y + -c)) y = coordinateDerivative i φ (y + -c) := by
  unfold coordinateDerivative
  rw [fderiv_comp_add_right]

theorem gradient_shift (c : Vec d) (φ : Vec d → ℝ) (y : Vec d) :
    gradient (fun y => φ (y + -c)) y = gradient φ (y + -c) := by
  funext i
  exact coordinateDerivative_shift c φ i y

/-! ## Shifted local harmonic functions -/

variable {a b : CoefficientField d Λ} {c z z' : Vec d} {T : ℝ}

/-- **The shift** of a local `a`-harmonic function on `B_T(z)` to a local `b`-harmonic function
on `B_T(z')`, where `b(y) = a(c + y)` and `c + z' = z`. -/
def LocalHarmonic.shift (w : LocalHarmonic a z T) (hb : ∀ y, b.field y = a.field (c + y))
    (hz : c + z' = z) : LocalHarmonic b z' T where
  potential := fun y => w.potential (c + y)
  grad := fun y => w.grad (c + y)
  square_integrable := MemLp.ball_add hz w.square_integrable
  gradient_square_integrable := MemLp.ball_add hz w.gradient_square_integrable
  weak_gradient := fun i => by
    refine ⟨IntegrableOn.locallyIntegrableOn
        ((MemLp.ball_add hz w.square_integrable).integrable one_le_two),
      IntegrableOn.locallyIntegrableOn
        ((MemLp.ball_add hz (w.memLp_grad i)).integrable one_le_two),
      fun φ hφ => ?_⟩
    have hψ := hφ.shift hz
    have h := (w.weak_gradient i).2.2 _ hψ
    have e1 := setIntegral_ball_add hz T
      (fun y => w.potential y * coordinateDerivative i (fun y => φ (y + -c)) y)
    have e2 := setIntegral_ball_add hz T (fun y => w.grad y i * φ (y + -c))
    simp only [coordinateDerivative_shift, add_neg_cancel_comm] at e1 e2
    rw [e1, e2]
    simp only [coordinateDerivative_shift] at h
    exact h
  harmonic := by
    refine ⟨fun k => ?_, locallyIntegrableOn_const 0, fun φ hφ => ?_⟩
    · refine IntegrableOn.locallyIntegrableOn ?_
      have : (fun y => ((b y).mulVec (w.grad (c + y))) k) =
          fun y => ∑ l, b y k l * w.grad (c + y) l := by
        funext y; simp [Matrix.mulVec, dotProduct]
      rw [this]
      refine integrable_finsetSum _ fun l _ => ?_
      refine Integrable.bdd_mul (c := Λ) ((MemLp.ball_add hz (w.memLp_grad l)).integrable one_le_two)
        (b.aestronglyMeasurable_apply k l _ Measure.restrict_le_self.absolutelyContinuous)
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs]
      exact b.abs_apply_le y k l
    · have hψ := hφ.shift hz
      have h := w.harmonic.2.2 _ hψ
      have e1 := setIntegral_ball_add hz T
        (fun y => dot ((a y).mulVec (w.grad y)) (gradient (fun y => φ (y + -c)) y))
      simp only [gradient_shift, add_neg_cancel_comm] at e1
      have hb' : ∀ y, b y = a (c + y) := hb
      simp only [hb']
      simp only [gradient_shift] at h
      rw [e1, h]
      simp

@[simp] theorem LocalHarmonic.shift_potential (w : LocalHarmonic a z T)
    (hb : ∀ y, b.field y = a.field (c + y)) (hz : c + z' = z) (y : Vec d) :
    (w.shift hb hz).potential y = w.potential (c + y) := rfl

@[simp] theorem LocalHarmonic.shift_grad (w : LocalHarmonic a z T)
    (hb : ∀ y, b.field y = a.field (c + y)) (hz : c + z' = z) (y : Vec d) :
    (w.shift hb hz).grad y = w.grad (c + y) := rfl

end QSH
