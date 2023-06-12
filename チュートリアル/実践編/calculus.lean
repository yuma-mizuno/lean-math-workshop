import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul

open Topology Filter Asymptotics

example (a : ℝ) : (fun x => x ^ 2 : ℝ → ℝ) =O[𝓝 a] (fun x => x ^ 2 : ℝ → ℝ) := by
  rw [isBigO_iff]
  existsi 1
  apply eventually_of_forall 
  intro x
  linarith

example : (fun x => x : ℝ → ℝ) =O[atTop] (fun x => x ^ 2 : ℝ → ℝ) := by
  apply IsBigO.of_bound 1
  rw [eventually_atTop]
  exists 1
  intro b hb
  simp only [Real.norm_eq_abs, norm_pow, sq_abs, one_mul]
  rw [abs_of_pos (by linarith)]
  nlinarith

example : (fun x => x ^ 2 : ℝ → ℝ) =O[𝓝 0] (fun x => x : ℝ → ℝ) := by
  rw [isBigO_iff]
  existsi 1
  rw [Metric.eventually_nhds_iff]
  exists 1
  split_ands
  simp
  intro y hy
  simp [dist] at hy
  simp
  by_cases 0 < abs y
  calc y ^ 2 = abs y * abs y := by simp; ring
    _ ≤ abs y  := by
      refine Iff.mpr (mul_le_iff_le_one_right h) ?_
      exact le_of_lt hy
  simp at h
  rw [h]
  simp
  

example (x : ℝ) {f : ℝ → ℝ} {f' : ℝ →L[ℝ] ℝ} :
    HasFDerivAt f f' x ↔ 
      (fun x' => f x' - f x - f' (x' - x)) =o[𝓝 x] fun x' => x' - x := 
  by rfl

example (x : ℝ) {f : ℝ → ℝ} {f' : ℝ →L[ℝ] ℝ} (hf : HasFDerivAt f f' x) {g : ℝ → ℝ} {g' : ℝ →L[ℝ] ℝ} (hg : HasFDerivAt g g' (f x))
     : HasFDerivAt (g ∘ f) (g'.comp f') x := by
  have := 
    calc 
      (fun x' ↦ g (f x') - g (f x) - g' (f x' - f x)) 
        =o[𝓝 x] fun x' ↦ f x' - f x         := hg.comp_tendsto (hf.continuousAt)
      _ =O[𝓝 x] fun x' ↦ x' - x            := hf.isBigO_sub
  refine this.triangle ?_
  have hg' : (fun x' ↦ g' (f x' - f x - f' (x' - x))) =O[𝓝 x] fun x' ↦ f x' - f x - f' (x' - x) := g'.isBigO_comp _ _ 
  calc (fun x' ↦ g' (f x' - f x) - g'.comp f' (x' - x)) 
      = fun x' ↦ g' (f x' - f x - f' (x' - x))           := by simp
    _ =O[𝓝 x] fun x' ↦ f x' - f x - f' (x' - x)         := (g'.isBigO_comp _ _)
    _ =o[𝓝 x] fun x' ↦ x' - x                           := hf

example (x : ℝ) : HasDerivAt (fun x ↦ x^2 : ℝ → ℝ) (2 * x) x := by
  dsimp [HasDerivAt, HasFDerivAtFilter, HasDerivAtFilter ]

  calc (fun x' => x' ^ 2 - x ^ 2 - (x' - x) * (2 * x))
      =o[𝓝 x] (fun x' => x' ^ 2 - x ^ 2 - (x' * (2 * x) - x * (2 * x))) := sorry
    _ = (fun x' => (x' - x) ^ 2 - x ^ 2 - (x' * (2 * x) - x * (2 * x))) := sorry
    _ = fun x' => x' - x := sorry
  -- rw [hasDerivAt_iff_tendsto]


  

open Polynomial Asymptotics

example (x : ℝ) :
    HasFDerivAt (fun x => x.fst * x.snd)
      (IsBoundedBilinearMap.deriv (ContinuousLinearMap.mul ℝ ℝ).isBoundedBilinearMap
        (x, x)) (x, x) := by
  -- simp
  simp only [hasFDerivAt_iff_isLittleO_nhds_zero]
  -- dsimp only [HasFDerivAt, HasFDerivAtFilter ]
  -- simp only [← map_add_left_nhds_zero (f x, g x), isLittleO_map]
  simp only [ContinuousLinearMap.mul_apply']
  simp only [Prod.fst_add, Prod.snd_add, IsBoundedBilinearMap.deriv_apply]
  -- simp only
  calc (fun h => (x + h.fst) * (x + h.snd) - x * x - (x * h.snd + h.fst * x) : ℝ × ℝ → ℝ)
      = fun h => h.1 * h.2 := by ext; ring
    _ =o[𝓝 0] fun h => h := by
      rw [isLittleO_iff]
      intro c hc
      rw [Metric.eventually_nhds_iff]
      existsi c
      constructor
      exact hc
      intro a ha
      simp at ha ⊢
      simp only [norm] at ha ⊢
      refine Iff.mp (mul_inv_le_iff hc) ?_
      simp at ha ⊢
      right
      cases Classical.em (0 < abs a.snd)
      calc abs a.fst * abs a.snd * c⁻¹ 
          ≤ c * abs a.2 * c⁻¹ := by 
            rw [mul_le_mul_right]
            rw [mul_le_mul_right]
            apply le_of_lt ha.1
            assumption
            exact Iff.mpr inv_pos hc
        _ = abs a.2 := by 
          calc c * abs a.snd * c⁻¹ 
              = c * c⁻¹ * abs a.snd := by ring
            _ = 1 * abs a.snd := by congr 1; refine mul_inv_cancel (ne_of_gt hc)
            _ = abs a.snd := by simp
      case inr h => 
        simp at h
        simp [h]
  -- calc
  --   _ = fun x ↦ h.deriv (x.1 - x.2) (x.2.1, x.1.2) := by
  --     ext ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
  --     rcases p with ⟨x, y⟩
  --     simp [h.add_left, h.add_right, h.deriv_apply, h.map_sub_left, h.map_sub_right]
  --     abel
  --   -- _ =O[𝓝 (0 : T)] fun x ↦ ‖x.1 - x.2‖ * ‖(x.2.1, x.1.2)‖ :=
  --   --     h.toContinuousLinearMap.deriv₂.isBoundedBilinearMap.isBigO_comp
  --   -- _ = o[𝓝 0] fun x ↦ ‖x.1 - x.2‖ * 1 := _
  --   _ =o[𝓝 (0 : T)] fun x ↦ x.1 - x.2 := by
  --     -- TODO : add 2 `calc` steps instead of the next 3 lines
  --     refine h.toContinuousLinearMap.deriv₂.isBoundedBilinearMap.isBigO_comp.trans_isLittleO ?_
  --     suffices : (fun x : T ↦ ‖x.1 - x.2‖ * ‖(x.2.1, x.1.2)‖) =o[𝓝 0] fun x ↦ ‖x.1 - x.2‖ * 1
  --     · simpa only [mul_one, isLittleO_norm_right] using this
  --     refine (isBigO_refl _ _).mul_isLittleO ((isLittleO_one_iff _).2 ?_)
  --     -- TODO: `continuity` fails
  --     exact (continuous_snd.fst.prod_mk continuous_fst.snd).norm.tendsto' _ _ (by simp)
  --   _ = _ := by simp [(· ∘ ·)]

example (x : ℝ) {f : ℝ → ℝ} {c' : ℝ} (hf : HasDerivAt f c' x) {g : ℝ → ℝ} {d' : ℝ} (hg : HasDerivAt g d' x) :
    HasDerivAt (fun y => f y * g y) (f x * d' + c' * g x) x := by
  have := ((ContinuousLinearMap.mul ℝ ℝ).isBoundedBilinearMap.hasFDerivAt (f x, g x)).comp x (hf.prod hg)
  simp only [hasDerivAt_iff_isLittleO_nhds_zero, hasFDerivAt_iff_isLittleO_nhds_zero] at this ⊢
  dsimp at this
  calc (fun h => f (x + h) * g (x + h) - f x * g x - h * (f x * d' + c' * g x) : ℝ → ℝ)
     = (fun h => f (x + h) * g (x + h) - f x * g x - (f x * (h * d') + h * c' * g x) : ℝ → ℝ) := by ext; ring
   _ =o[𝓝 0] (fun h => h : ℝ → ℝ) := this
    
open ContinuousLinearMap

example : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := by
  apply LinearMap.mkContinuous₂ (LinearMap.mk₂ ℝ (· * ·) _ _ _ _) 1 (fun x y => (?_ : ‖x * y‖ ≤ 1 * ‖x‖ * ‖y‖)) <;> 
    intros <;> simp <;> ring

noncomputable
example : ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ := by
  set f : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := by apply LinearMap.mkContinuous₂ (LinearMap.mk₂ ℝ (· * ·) _ _ _ _) 1 (fun x y => (?_ : ‖x * y‖ ≤ 1 * ‖x‖ * ‖y‖)) <;> 
    intros <;> simp <;> ring
  exact f.bilinearComp (fst _ _ _) (snd _ _ _) + f.flip.bilinearComp (snd _ _ _) (fst _ _ _)


example (x : ℝ × ℝ) : HasFDerivAt (fun x ↦ x.1 * x.2 : ℝ × ℝ → ℝ) ((ContinuousLinearMap.mul ℝ ℝ).isBoundedBilinearMap.deriv x) x := by
  simp [hasFDerivAt_iff_isLittleO_nhds_zero]
  calc (fun h => (x.1 + h.1) * (x.2 + h.2) - x.1 * x.2 - (x.1 * h.2 + h.1 * x.2) : ℝ × ℝ → ℝ) 
      =(fun h => h.1 * h.2) := by ext; ring
    _ =o[𝓝 0] fun h => h := by sorry



example (x : ℝ) {f : ℝ → ℝ} {c : ℝ} (hf : HasDerivAt f c x) {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d x) :
    HasDerivAt (fun y => f y * g y) (f x * d + c * g x) x := by
  have h : (fun y => f y * g y) = (fun y => y.1 * y.2 : ℝ × ℝ → ℝ) ∘ fun y => (f y, g y) := by 
    ext
    simp
  rw [h]
  set P := (ContinuousLinearMap.mul ℝ ℝ).isBoundedBilinearMap.deriv (f x, g x)
  have hP : P (c, d) = f x * d + c * g x := rfl
  set fg := (ContinuousLinearMap.prod (smulRight (1 : ℝ →L[ℝ] ℝ) (deriv f x)) (smulRight (1 : ℝ →L[ℝ] ℝ) (deriv g x)))
  dsimp at fg
  have hfg : fg x = (x * c, x * d) := by
    simp [hf.deriv, hg.deriv]


  -- change HasDerivAt (fun y => y.1 * y.2 ∘ fun y => (y, y)) (f x * d' + c' * g x) x
  apply HasFDerivAt.comp
  have h0 := ((ContinuousLinearMap.mul ℝ ℝ).isBoundedBilinearMap.hasFDerivAt (f x, g x))

  dsimp at h0
  have := ((ContinuousLinearMap.mul ℝ ℝ).isBoundedBilinearMap.hasFDerivAt (f x, g x)).comp x (hf.prod hg)
  dsimp [HasDerivAt, HasFDerivAt, HasDerivAtFilter] at this ⊢
  convert this using 1
  ext
  rw [ContinuousLinearMap.comp_apply]
  simp

example (x : ℝ) {f : ℝ → ℝ} {c : ℝ} (hf : HasDerivAt f c x) {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d x) :
    HasDerivAt (fun y => f y * g y) (f x * d + c * g x) x := by
  rw [hasDerivAt_iff_isLittleO]
  calc (fun x' => f x' * g x' - f x * g x - (x' - x) * (f x * d + c * g x))
    _ = fun x' => f x * (g x' - g x - (x' - x) * d) + 
          (g x * (f x' - f x - (x' - x) * c) + (f x' - f x) * (g x' - g x)) := by ext; ring
    _ =o[𝓝 x] fun x' => x' - x                                             := ?eq1
  case eq1 =>
    apply (hg.const_mul_left (f x)).add <| (hf.const_mul_left (g x)).add _
    calc (fun x' => (f x' - f x) * (g x' - g x))
      _ =o[𝓝 x] fun x' => (x' - x) * 1      := ?eq2
      _ = fun x' => x' - x                   := by ext; ring
    case eq2 =>
      apply IsBigO.mul_isLittleO
      · apply (hf.isBigO_sub : (fun x' => f x' - f x) =O[𝓝 x] fun x' => x' - x)
      · rw [isLittleO_one_iff]
        rw [tendsto_sub_nhds_zero_iff]
        apply hg.continuousAt.tendsto

example (x : ℝ) {f : ℝ → ℝ} {c : ℝ} (hf : HasDerivAt f c x) {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d x) :
    HasDerivAt (fun y => f y * g y) (f x * d + c * g x) x := by
  rw [hasDerivAt_iff_isLittleO]
  calc (fun x' => f x' * g x' - f x * g x - (x' - x) * (f x * d + c * g x)) 
    _ = fun x' => f x * (g x' - g x - (x' - x) * d) + 
          (g x * (f x' - f x - (x' - x) * c) + (f x' - f x) * (g x' - g x)) := by ext; ring
    _ =o[𝓝 x] fun x' => x' - x                                              := ?eq1
  case eq1 =>
    have hf' := IsLittleO.const_mul_left hf (g x)
    have hg' : (fun x' => f x * (g x' - g x - (x' - x) * d)) =o[𝓝 x] fun x' => x' - x := 
      hg.const_mul_left (f x)
    apply IsLittleO.add hg'
    apply IsLittleO.add hf'
    calc (fun x' => (f x' - f x) * (g x' - g x))
      _ =o[𝓝 x] fun x' => (x' - x) * 1      := ?eq2
      _ = fun x' => x' - x                   := by ext; ring
    case eq2 =>
      apply IsBigO.mul_isLittleO
      · apply (hf.isBigO_sub : (fun x' => f x' - f x) =O[𝓝 x] fun x' => x' - x)
      · rw [isLittleO_one_iff]
        rw [tendsto_sub_nhds_zero_iff]
        apply hg.continuousAt.tendsto

example (x : ℝ) {f : ℝ → ℝ} {c' : ℝ} (hf : HasDerivAt f c' x) {g : ℝ → ℝ} {d' : ℝ} (hg : HasDerivAt g d' x) :
    HasDerivAt (fun y => f y * g y) (f x * d' + c' * g x) x := by
  rw [hasDerivAt_iff_isLittleO]
  calc (fun x' => f x' * g x' - f x * g x - (x' - x) * (f x * d' + c' * g x)) 
    _ = fun x' => f x * (g x' - g x - (x' - x) * d') + 
          (g x * (f x' - f x - (x' - x) * c') + (f x' - f x) * (g x' - g x)) := by ext; ring
    _ =o[𝓝 x] fun x' => x' - x                                              := ?eq1
  case eq1 =>
    have hf' := IsLittleO.const_mul_left hf (g x)
    have hg' := IsLittleO.const_mul_left hg (f x)
    apply IsLittleO.add hg'
    apply IsLittleO.add hf'
    calc (fun x_1 => (f x_1 - f x) * (g x_1 - g x))
      _ =o[𝓝 x] fun x' => (x' - x) * 1      := ?eq2
      _ = fun x' => x' - x                   := by ext; ring
    case eq2 =>
      apply IsBigO.mul_isLittleO
      · exact HasDerivAtFilter.isBigO_sub hf
      · rw [isLittleO_const_iff one_ne_zero]
        rw [tendsto_sub_nhds_zero_iff]
        apply hg.continuousAt.tendsto
  

example (n : ℕ) (x : ℝ) : HasDerivAt (fun x ↦ x ^ n : ℝ → ℝ) (n * x ^ (n - 1)) x := by
  induction n
  case zero => simp [hasDerivAt_iff_isLittleO_nhds_zero]
  case succ n ih => 
    cases n
    case zero => simp [hasDerivAt_iff_isLittleO_nhds_zero, Nat.succ_eq_add_one]
    case succ n =>
      dsimp only [Nat.succ_eq_add_one] at ih ⊢
      suffices HasDerivAt (fun x => x ^ (n + 1) * x : ℝ → ℝ) ((↑(n + 1) * x ^ n) * x + x ^ (n + 1) * 1) x by
        simp [hasDerivAt_iff_isLittleO_nhds_zero] at this ⊢
        convert this using 1
        ext
        ring
      apply HasDerivAt.mul
      apply ih
      apply hasDerivAt_id
    

example (a : ℝ) : HasDerivAt (fun x ↦ x ^ 2) (2 * a) a := by
  calc (fun x => x ^ 2 - a ^ 2 - (x - a) * (2 * a)) 
    _ = fun x => (x - a) ^ 2 := ?eq2
    _ =o[𝓝 a] fun x => x - a := ?eq3
  case eq2 => ext x; ring
  case eq3 =>
    apply isLittleO_iff.mpr (fun ε hε => Metric.eventually_nhds_iff.mpr ?_)
    existsi ε / 2
    split_ands
    exact half_pos hε
    intro x (hx : abs (x - a) < ε / 2)
    cases Classical.em (0 < abs (x - a))
    case inl h =>
      have := calc (x - a) ^ 2 = abs (x - a) * abs (x - a) := by simp; ring
        _ ≤ ε * abs (x - a) := by 
          rw [mul_le_mul_right h]
          linarith
      simp only [norm_pow, Real.norm_eq_abs, sq_abs, ge_iff_le]
      linarith
    case inr h =>
      replace h : x - a = 0 := by simpa using h
      simp [h] 

example (a : ℝ) : HasDerivAt (X ^ 2).eval ((2 * X).eval a) a := by
  calc (fun x => eval x (X ^ 2) - eval a (X ^ 2) - (x - a) * eval a (2 * X))
    _ = fun x => x ^ 2 - a ^ 2 - (x - a) * (2 * a) := ?eq1
    _ = fun x => (x - a) ^ 2 := ?eq2
    _ =o[𝓝 a] fun x => x - a := ?eq3
  case eq1 =>
    ext x
    simp only [eval_pow, eval_X, eval_mul, sub_right_inj]
    congr 2
    apply eval_nat_cast
  case eq2 => 
    ext x
    ring
  case eq3 =>
    rw [isLittleO_iff]
    intro c hc
    rw [Metric.eventually_nhds_iff]
    existsi c
    constructor
    apply hc
    intro x hx
    
    -- intro x hx
    by_cases (0 < abs (x - a))
    have := calc (x - a) ^ 2 ≤ (abs (x - a))^2  := by simp
      _ = (abs (x - a)) * (abs (x - a)) := by ring
      _ < c * abs (x - a) := by 
        replace hx : abs (x - a) < c := by simpa [dist] using hx
        apply mul_lt_mul_of_nonneg_of_pos <;> linarith
    simp only [norm_pow, Real.norm_eq_abs, sq_abs, ge_iff_le]
    linarith
    replace h : x - a = 0 := by simpa using h
    simp [h] 

example (a : ℝ) : HasDerivAt (X ^ 2).eval ((2 * X).eval a) a := by
  calc (fun x => eval x (X ^ 2) - eval a (X ^ 2) - (x - a) * eval a (2 * X))
    _ = fun x => x ^ 2 - a ^ 2 - (x - a) * (2 * a) := ?eq1
    _ = fun x => (x - a) ^ 2 := ?eq2
    _ =o[𝓝 a] fun x => x - a := ?eq3
  case eq1 =>
    ext x
    simp only [eval_pow, eval_X, eval_mul, sub_right_inj]
    congr 2
    apply eval_nat_cast
  case eq2 => 
    ext x
    ring
  case eq3 =>
    rw [isLittleO_iff]
    intro c hc
    refine Iff.mpr Metric.eventually_nhds_iff ?_
    -- rw [eventually_iff]
    -- simp only [Real.norm_eq_abs]
    -- rw [mem_nhds_iff]
    -- existsi Ioo a b
    -- existsi Metric.ball a c
    -- existsi {x | abs (x - a) < c }
    existsi c
    constructor
    
    -- intro x hx
    by_cases (0 < abs (x - a))
    have := calc (x - a) ^ 2 ≤ (abs (x - a))^2  := by simp
      _ = (abs (x - a)) * (abs (x - a)) := by ring
      _ < c * abs (x - a) := by 
        replace hx : abs (x - a) < c := by simpa [dist] using hx
        apply mul_lt_mul_of_nonneg_of_pos <;> linarith
    simp only [Set.mem_setOf_eq]
    linarith
    replace h : x - a = 0 := by simpa using h
    simp [h] 
    exact ⟨Metric.isOpen_ball, Metric.mem_ball_self hc⟩


  -- rw [hasDerivAt_iff_tendsto]

example (x : ℝ) : HasFDerivAt (X ^ 2 : ℝ[X]).eval (LinearMap.toContinuousLinearMap (LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (2 : ℝ))) x := by
  simp [HasFDerivAt, HasFDerivAtFilter]
  rw [hasFDerivAt_iff_tendsto]
  simp
  simp only [Tendsto, Real.norm_eq_abs, Pi.pow_apply, map_sub, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, smul_eq_mul]
  linarith
  continuity

noncomputable
instance : Coe ((Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ((Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) := ⟨LinearMap.toContinuousLinearMap⟩

-- set_option trace.Meta.synthInstance true in
example (m n l : ℕ) (x : Fin m → ℝ) {f : (Fin m → ℝ) → (Fin n → ℝ)} {f' : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)} 
  (hf : HasFDerivAt f (LinearMap.toContinuousLinearMap f') x) {g : (Fin n → ℝ) → (Fin l → ℝ)} {g' : (Fin n → ℝ) →ₗ[ℝ] (Fin l → ℝ)} 
    (hg : HasFDerivAt g (LinearMap.toContinuousLinearMap g') (f x))
     : HasFDerivAt (g ∘ f) (LinearMap.toContinuousLinearMap (g'.comp f')) x := by
  unfold HasFDerivAt HasFDerivAtFilter at hg
  have :=
    calc
      (fun x' ↦ g (f x') - g (f x) - g' (f x' - f x)) =o[𝓝 x] fun x' ↦ f x' - f x :=
        hg.comp_tendsto (hf.continuousAt)

      _ =O[𝓝 x] fun x' => x' - x := hf.isBigO_sub
  refine' this.triangle _
  calc
    (fun x' => g' (f x' - f x) - g'.comp f' (x' - x)) =ᶠ[𝓝 x] fun x' =>
        g' (f x' - f x - f' (x' - x)) :=
      eventually_of_forall fun x' => by simp
    _ =O[𝓝 x] fun x' => f x' - f x - f' (x' - x) := (g'.toContinuousLinearMap.isBigO_comp _ _)
    _ =o[𝓝 x] fun x' => x' - x := hf

example (σ : Type) (m n l : ℕ) (x : σ → ℝ) {f : (σ → ℝ) → (Fin n → ℝ)} {f' : (σ → ℝ) →L[ℝ] (Fin n → ℝ)} 
  (hf : HasFDerivAt f f' x) {g : (Fin n → ℝ) → (Fin l → ℝ)} {g' : (Fin n → ℝ) →L[ℝ] (Fin l → ℝ)} 
    (hg : HasFDerivAt g g' (f x))
     : HasFDerivAt (g ∘ f) (g'.comp f') x := by
  unfold HasFDerivAt HasFDerivAtFilter at hg
  have :=
    calc
      (fun x' ↦ g (f x') - g (f x) - g' (f x' - f x)) =o[𝓝 x] fun x' ↦ f x' - f x :=
        hg.comp_tendsto (hf.continuousAt)

      _ =O[𝓝 x] fun x' => x' - x := hf.isBigO_sub
  refine' this.triangle _
  calc
    (fun x' => g' (f x' - f x) - g'.comp f' (x' - x)) =ᶠ[𝓝 x] fun x' =>
        g' (f x' - f x - f' (x' - x)) :=
      eventually_of_forall fun x' => by simp
    _ =O[𝓝 x] fun x' => f x' - f x - f' (x' - x) := (g'.toContinuousLinearMap.isBigO_comp _ _)
    _ =o[𝓝 x] fun x' => x' - x := hf