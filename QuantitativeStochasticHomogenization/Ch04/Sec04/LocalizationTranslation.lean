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

/-! ## Invariance of the objective, the norm, the admissible class and the energy -/

theorem heatKernel_add_add (c y : Vec d) (t : ℝ) (y' : Vec d) :
    heatKernel (c + y) t (c + y') = heatKernel y t y' := by
  unfold heatKernel
  rw [add_sub_add_left_eq_sub]

theorem localizationObjective_shift (hz : c + z' = z) (S σ θ : ℝ) (i : Fin d)
    (f : Vec d → ℝ) :
    localizationObjective z' T S σ θ (fun y => f (c + y) - (y - z') i) =
      localizationObjective z T S σ θ (fun y => f y - (y - z) i) := by
  unfold localizationObjective
  have hinner : ∀ y, (∫ y' in ball z' T, heatKernel y (σ * S) y' * (f (c + y') - (y' - z') i)) =
      ∫ x in ball z T, heatKernel (c + y) (σ * S) x * (f x - (x - z) i) := by
    intro y
    rw [← setIntegral_ball_add hz T]
    refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
    have e : (c + y' - z) i = (y' - z') i := by rw [← hz, add_sub_add_left_eq_sub]
    simp only [heatKernel_add_add, e]
  simp_rw [hinner]
  exact setAverage_ball_add hz (S / θ)
    (fun u => (∫ x in ball z T, heatKernel u (σ * S) x * (f x - (x - z) i)) ^ 2)

theorem integral_sq_shift (hz : c + z' = z) (f : Vec d → ℝ) :
    ∫ y in ball z' T, f (c + y) ^ 2 = ∫ y in ball z T, f y ^ 2 :=
  setIntegral_ball_add hz T (fun y => f y ^ 2)

theorem vectorRms_shift (hz : c + z' = z) (g : Vec d → Vec d) :
    vectorRms volume (ball z' T) (fun y => g (c + y)) = vectorRms volume (ball z T) g := by
  unfold vectorRms
  rw [setAverage_ball_add hz T (fun y => euclideanSq (g y))]

theorem LocalHarmonic.isLocalizationAdmissible_shift_iff (w : LocalHarmonic a z T)
    (hb : ∀ y, b.field y = a.field (c + y)) (hz : c + z' = z) (C : ℝ) :
    IsLocalizationAdmissible C (w.shift hb hz) ↔ IsLocalizationAdmissible C w := by
  unfold IsLocalizationAdmissible
  rw [show (w.shift hb hz).grad = fun y => w.grad (c + y) from rfl, vectorRms_shift hz]

theorem neg_add_shift_eq (hz : c + z' = z) : -c + z = z' := by
  rw [← hz, neg_add_cancel_left]

theorem field_unshift (hb : ∀ y, b.field y = a.field (c + y)) (y : Vec d) :
    a.field y = b.field (-c + y) := by
  rw [hb, add_neg_cancel_left]

/-- The shift maps least-norm coordinate minimizers to least-norm coordinate minimizers. -/
theorem IsLeastNormCoordinateMinimizer.shift {S σ θ C : ℝ} {i : Fin d} {w : LocalHarmonic a z T}
    (hw : IsLeastNormCoordinateMinimizer S σ θ C i w) (hb : ∀ y, b.field y = a.field (c + y))
    (hz : c + z' = z) : IsLeastNormCoordinateMinimizer S σ θ C i (w.shift hb hz) := by
  have hb' := field_unshift hb
  have hz' := neg_add_shift_eq hz
  have hobj : ∀ v : LocalHarmonic b z' T,
      localizationObjective z T S σ θ (fun y => (v.shift hb' hz').potential y - (y - z) i) =
        localizationObjective z' T S σ θ (fun y => v.potential y - (y - z') i) := by
    intro v
    have h := localizationObjective_shift (T := T) hz S σ θ i (v.shift hb' hz').potential
    rw [← h]
    congr 1
    funext y
    simp
  have hnorm : ∀ v : LocalHarmonic b z' T,
      ∫ y in ball z T, (v.shift hb' hz').potential y ^ 2 = ∫ y in ball z' T, v.potential y ^ 2 := by
    intro v
    have h := integral_sq_shift (T := T) hz (v.shift hb' hz').potential
    rw [← h]
    congr 1
    funext y
    simp
  have hadm : ∀ v : LocalHarmonic b z' T,
      IsLocalizationAdmissible C (v.shift hb' hz') ↔ IsLocalizationAdmissible C v :=
    fun v => v.isLocalizationAdmissible_shift_iff hb' hz' C
  have hobj_w : localizationObjective z' T S σ θ
      (fun y => (w.shift hb hz).potential y - (y - z') i) =
        localizationObjective z T S σ θ (fun y => w.potential y - (y - z) i) :=
    localizationObjective_shift hz S σ θ i w.potential
  have hmin : IsCoordinateMinimizer S σ θ C i (w.shift hb hz) := by
    refine ⟨(w.isLocalizationAdmissible_shift_iff hb hz C).2 hw.1.1, fun v hv => ?_⟩
    rw [hobj_w, ← hobj v]
    exact hw.1.2 _ ((hadm v).2 hv)
  refine ⟨hmin, fun v hv => ?_⟩
  have hvm : IsCoordinateMinimizer S σ θ C i (v.shift hb' hz') := by
    refine ⟨(hadm v).2 hv.1, fun u hu => ?_⟩
    rw [hobj v]
    have h1 := hv.2 (u.shift hb hz) ((u.isLocalizationAdmissible_shift_iff hb hz C).2 hu)
    rw [show (fun x => (u.shift hb hz).potential x - (x - z') i) =
      fun y => u.potential (c + y) - (y - z') i from rfl,
      localizationObjective_shift hz S σ θ i u.potential] at h1
    exact h1
  have h2 := hw.2 _ hvm
  rw [hnorm v] at h2
  rw [show (w.shift hb hz).potential = fun y => w.potential (c + y) from rfl,
    integral_sq_shift hz]
  exact h2

/-- The shift of a localized basis. -/
def LocalizedBasis.shift {S σ θ C : ℝ} (W : LocalizedBasis a z T S σ θ C)
    (hb : ∀ y, b.field y = a.field (c + y)) (hz : c + z' = z) : LocalizedBasis b z' T S σ θ C where
  coordinate i := (W.coordinate i).shift hb hz
  selected i := (W.selected i).shift hb hz

/-- **The localized energy is invariant under the shift.** -/
theorem localizedJ1_shift {S σ θ C : ℝ} (W : LocalizedBasis a z T S σ θ C)
    (hb : ∀ y, b.field y = a.field (c + y)) (hz : c + z' = z) (r : ℝ) (p q : Vec d) :
    localizedJ1 (W.shift hb hz) r p q = localizedJ1 W r p q := by
  unfold localizedJ1
  congr 1
  ext e
  refine exists_congr fun cc => ?_
  have hint : (∫ x in ball z' T, heatKernel z' r x *
      (-(1 / 2 : ℝ) * dot (localizedGradient (W.shift hb hz) cc x)
        ((b x).mulVec (localizedGradient (W.shift hb hz) cc x)) -
        dot p ((b x).mulVec (localizedGradient (W.shift hb hz) cc x)) +
        dot q (localizedGradient (W.shift hb hz) cc x))) =
      ∫ x in ball z T, heatKernel z r x *
        (-(1 / 2 : ℝ) * dot (localizedGradient W cc x) ((a x).mulVec (localizedGradient W cc x)) -
          dot p ((a x).mulVec (localizedGradient W cc x)) + dot q (localizedGradient W cc x)) := by
    rw [← setIntegral_ball_add hz T]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hk : heatKernel z' r x = heatKernel z r (c + x) := by
      unfold heatKernel
      rw [← hz, add_sub_add_left_eq_sub]
    have hg : localizedGradient (W.shift hb hz) cc x = localizedGradient W cc (c + x) := rfl
    have hbx : b x = a (c + x) := hb x
    simp only [hk, hg, hbx]
  rw [hint]

end QSH
