import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Asymptotics.Asymptotics

open Topology Filter Asymptotics

/- # ランダウ記号

-/

theorem aaaa : (fun x => x⁻¹ * x : ℝ → ℝ) =ᶠ[𝓝[{0}ᶜ] 0] (fun x => 1) := by
  apply eventually_nhdsWithin_of_forall (fun (x : ℝ) hx => (?_ : x⁻¹ * x = 1))
  rw [inv_mul_cancel]
  simpa using hx

example : Tendsto (fun x => x⁻¹ * x : ℝ → ℝ) (𝓝[{0}ᶜ] 0) (𝓝 1) := by
  rw [tendsto_congr' aaaa]
  exact tendsto_const_nhds

def HasDerivAt (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) := 
  (fun x' => f x' - f x - (x' - x) * f') =o[𝓝 x] fun x' => x' - x 

example : (fun x => x ^ 2 : ℝ → ℝ) =O[𝓝 0] (fun x => x ^ 2 : ℝ → ℝ) := by
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

variable {f : ℝ → ℝ} {f' : ℝ} {x : ℝ}

/- # 微分
関数`f : ℝ → ℝ`の`x : ℝ`における微分係数が`c : ℝ`であることを`HasDerivAt f c x`と書く。
以下、いくつかの同値な特徴づけを与える。
-/

variable {f : ℝ → ℝ} {f' : ℝ} {x : ℝ}

/-- `x'`が`x`に近づくとき`f x' = f x + (x' - x) • f' + o(x' - x)`である -/
theorem hasDerivAt_iff_isLittleO : 
    HasDerivAt f f' x ↔ (fun x' => f x' - f x - (x' - x) * f') =o[𝓝 x] fun x' => x' - x :=
  Iff.rfl

/-- `h`が`0`に近づくとき`f (x + h) = f x + h • f' + o(h)`である -/
theorem hasDerivAt_iff_isLittleO_nhds_zero : 
    HasDerivAt f f' x ↔ (fun h => f (x + h) - f x - h * f') =o[𝓝 0] fun h => h := by
  rw [HasDerivAt, ← map_add_left_nhds_zero x, isLittleO_map]
  simp [(· ∘ ·)]

/-- `x'`が`x`に近づくとき`‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖`は`0`に近づく -/
theorem hasDerivAt_iff_tendsto : 
    HasDerivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) * f'‖) (𝓝 x) (𝓝 0) := by
  rw [HasDerivAt, ← isLittleO_norm_left, ← isLittleO_norm_right, 
    isLittleO_iff_tendsto (by intro _ h; simp [sub_eq_zero.1 (norm_eq_zero.1 h)])]
  apply tendsto_congr (by intros; field_simp) 

/-- `x'`が`x`に近づくとき`(x' - x)⁻¹ * (f x' - f x)`は`f'`に近づく -/
theorem hasDerivAt_iff_tendsto_slope : 
    HasDerivAt f f' x ↔ Tendsto (fun x' => (x' - x)⁻¹ * (f x' - f x)) (𝓝[≠] x) (𝓝 f') := by
  -- _root_.hasDerivAt_iff_tendsto_slope
  calc HasDerivAt f f' x
    _ ↔ Tendsto (fun x' ↦ (x' - x)⁻¹ * (f x' - f x) - (x' - x)⁻¹ * (x' - x) * f') (𝓝 x) (𝓝 0)    := ?iff1
    _ ↔ Tendsto (fun x' ↦ (x' - x)⁻¹ * (f x' - f x) - (x' - x)⁻¹ * (x' - x) * f') (𝓝[≠] x) (𝓝 0) := ?iff2
    _ ↔ Tendsto (fun x' ↦ (x' - x)⁻¹ * (f x' - f x) - f') (𝓝[≠] x) (𝓝 0)                         := ?iff3
    _ ↔ Tendsto (fun x' ↦ (x' - x)⁻¹ * (f x' - f x)) (𝓝[≠] x) (𝓝 f')                             := ?iff4
  case iff1 => simp only [hasDerivAt_iff_tendsto, ← norm_inv, mul_sub, ← norm_smul, smul_eq_mul, mul_assoc, sub_mul, ← tendsto_zero_iff_norm_tendsto_zero]
  case iff2 => exact .symm <| tendsto_inf_principal_nhds_iff_of_forall_eq <| by simp
  case iff3 => exact tendsto_congr' <| (Set.EqOn.eventuallyEq fun y hy ↦ (by field_simp [sub_ne_zero.2 hy])).filter_mono inf_le_right
  case iff4 => rw [← nhds_translation_sub f', tendsto_comap_iff]; rfl

theorem HasDerivAt.isBigO_sub (h : HasDerivAt f f' x) : (fun x' => f x' - f x) =O[𝓝 x] fun x' => x' - x := by
  rewrite [hasDerivAt_iff_isLittleO] at h
  rewrite [h.isBigO.congr_of_sub]
  calc (fun x' => (x' - x) * f') 
    _ = fun x' => f' * (x' - x)  := ?eq1
    _ =O[𝓝 x] fun x' => x' - x  := ?eq2
  case eq1 =>
    { funext x'
      ring }
  case eq2 =>
    { apply isBigO_const_mul_self }

theorem HasDerivAt.continuousAt (h : HasDerivAt f f' x) : ContinuousAt f x := by
  have : Tendsto (fun x' => f x' - f x) (𝓝 x) (𝓝 0) := by
    apply h.isBigO_sub.trans_tendsto
    rw [← sub_self x]
    exact tendsto_id.sub tendsto_const_nhds
  have := this.add (@tendsto_const_nhds _ _ _ (f x) _)
  rw [zero_add (f x)] at this
  exact this.congr (by simp)

/- 合成関数の微分 -/
theorem HasDerivAt.comp (x : ℝ) {f : ℝ → ℝ} {c : ℝ} (hf : HasDerivAt f c x) {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d (f x)) : 
    HasDerivAt (g ∘ f) (d * c) x := by
  rw [hasDerivAt_iff_isLittleO]
  have := 
    calc 
      (fun x' ↦ g (f x') - g (f x) - (f x' - f x) * d) 
        =o[𝓝 x] fun x' ↦ f x' - f x         := ?eq1
      _ =O[𝓝 x] fun x' ↦ x' - x            := hf.isBigO_sub
  case eq1 =>
    apply hg.comp_tendsto
    apply hf.continuousAt
  refine this.triangle ?_
  dsimp
  calc (fun x' => (f x' - f x) * d - (x' - x) * (d * c)) 
    _ = fun x' => d * (f x' - f x - (x' - x) * c) := by ext; ring
    _ =O[𝓝 x] fun x' ↦ f x' - f x - (x' - x) * c := by 
      apply isBigO_const_mul_self
    _ =o[𝓝 x] fun x' => x' - x := by
      apply hf

theorem HasDerivAt.mul' (x : ℝ) {f : ℝ → ℝ} {c : ℝ} (hf : HasDerivAt f c x) {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d x) :
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

theorem hasDerivAt_const : HasDerivAt (fun _ => c) 0 x :=
  sorry

theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x + g x) (f' + g') x :=
  sorry


theorem HasDerivAt.mul (x : ℝ) {f : ℝ → ℝ} {c : ℝ} (hf : HasDerivAt f c x) {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d x) :
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

theorem HasDerivAt.const_mul (c : ℝ) (hd : HasDerivAt f f' x) :
    HasDerivAt (fun y => c * f y) (c * f') x := by
  sorry

theorem HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (fun x => -f x) (-f') x := by
  have : HasDerivAt (fun y => -1 * f y) ((-1) * f' + 0 * f x) x := by
    apply HasDerivAt.mul
    apply hasDerivAt_const
    apply h
  simp at this
  apply this
  

theorem HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x - g x) (f' - g') x :=
  sorry



theorem hasDerivAt_id (x : ℝ) : HasDerivAt id 1 x := sorry


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
      · exact hf.isBigO_sub
      · rw [isLittleO_const_iff one_ne_zero]
        rw [tendsto_sub_nhds_zero_iff]
        apply hg.continuousAt.tendsto
  
/- 単項式の微分 -/
example (n : ℕ) (x : ℝ) : HasDerivAt (fun x ↦ x ^ n : ℝ → ℝ) (n * x ^ (n - 1)) x := by
  induction n
  case zero => simp [hasDerivAt_iff_isLittleO_nhds_zero]
  case succ n ih => 
    cases n
    case zero => simp [hasDerivAt_iff_isLittleO_nhds_zero, Nat.succ_eq_add_one]
    case succ n =>
      dsimp only [Nat.succ_eq_add_one] at ih ⊢
      suffices HasDerivAt (fun x => x ^ (n + 1) * x : ℝ → ℝ) (x ^ (n + 1) * 1 + (↑(n + 1) * x ^ n) * x) x by
        simp [hasDerivAt_iff_isLittleO_nhds_zero] at this ⊢
        convert this using 1
        ext
        ring
      apply HasDerivAt.mul
      apply ih
      simp [HasDerivAt]
    
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

open Set

variable (f f' : ℝ → ℝ) {a b : ℝ}

theorem exists_Ioo_extr_on_Icc (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsExtrOn f (Icc a b) c := by
  have ne : (Icc a b).Nonempty := nonempty_Icc.2 (le_of_lt hab)
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : ∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f c ≤ f x :=
    isCompact_Icc.exists_forall_le ne hfc
  obtain ⟨C, Cmem, Cge⟩ : ∃ C ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f C :=
    isCompact_Icc.exists_forall_ge ne hfc
  by_cases hc : f c = f a
  · by_cases hC : f C = f a
    · have : ∀ x ∈ Icc a b, f x = f a := fun x hx => le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx)
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases nonempty_Ioo.2 hab with ⟨c', hc'⟩
      refine ⟨c', hc', Or.inl fun x hx ↦ ?_⟩
      simp only [mem_setOf_eq, this x hx, this c' (Ioo_subset_Icc_self hc'), le_rfl]
    · refine' ⟨C, ⟨lt_of_le_of_ne Cmem.1 <| mt _ hC, lt_of_le_of_ne Cmem.2 <| mt _ hC⟩, Or.inr Cge⟩
      exacts [fun h => by rw [h], fun h => by rw [h, hfI]]
  · refine' ⟨c, ⟨lt_of_le_of_ne cmem.1 <| mt _ hc, lt_of_le_of_ne cmem.2 <| mt _ hc⟩, Or.inl cle⟩
    exacts [fun h => by rw [h], fun h => by rw [h, hfI]]

/-- A continuous function on a closed interval with `f a = f b` has a local extremum at some
point of the corresponding open interval. -/
theorem exists_local_extr_Ioo (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_Ioo_extr_on_Icc f hab hfc hfI
  ⟨c, cmem, hc.isLocalExtr <| Icc_mem_nhds cmem.1 cmem.2⟩

variable {f : ℝ → ℝ} {f' : ℝ} {x a b : ℝ}

/-- If `f` has a local max on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMax.hasDerivAt_nonpos (h : IsLocalMax f a)
    (hf : HasDerivAt f f' a) (y) : y * f' ≤ 0 := by

  have cdlim : (fun x => (x - a)⁻¹ * ((x - a) * y) : ℝ → ℝ) =ᶠ[𝓝[>] a] (fun _ => y) := by
    apply eventually_nhdsWithin_of_forall (fun x hx => (?_ : (x - a)⁻¹ * ((x - a) * y) = y))
    simp [←mul_assoc, inv_mul_cancel (ne_of_gt (sub_pos.mpr <| mem_Ioi.mp hx))]

  have cdlim : Tendsto (fun x => (x - a)⁻¹ * ((x - a) * y)) (𝓝[>] a) (𝓝 y) := by
    rw [tendsto_congr' cdlim]
    exact tendsto_const_nhds

  have tendsto_arg : Tendsto (fun x => a + (x - a) * y) (𝓝[>] a) (𝓝 a) := by 
    convert Tendsto.add tendsto_const_nhds (?_ : Tendsto (fun x => (x - a) * y) (𝓝[Ioi a] a) (𝓝 0))
    · simp
    · convert Tendsto.mul (?_ : Tendsto (fun x => (x - a)) (𝓝[>] a) (𝓝 0)) (tendsto_const_nhds_iff.mpr rfl)
      · simp
      · apply Tendsto.mono_left _ nhdsWithin_le_nhds
        rw [tendsto_sub_nhds_zero_iff]
        apply tendsto_id

  have : (fun x => f (a + (x - a) * y) - f a - (a + (x - a) * y - a) * f') =o[𝓝[>] a] fun x => a + (x - a) * y - a := by
    apply (hasDerivAt_iff_isLittleO.1 hf).comp_tendsto tendsto_arg
  have : (fun x => f (a + (x - a) * y) - f a - (x - a) * y * f') =o[𝓝[>] a] fun x => (x - a) * y := by simpa only [add_sub_cancel']
  have : (fun x => (x - a)⁻¹ * (f (a + (x - a) * y) - f a - (x - a) * y * f')) =o[𝓝[>] a] fun x => (x - a)⁻¹ * ((x - a) * y) := by
    apply (isBigO_refl _ _).mul_isLittleO this
  have : (fun x => (x - a)⁻¹ * (f (a + (x - a) * y) - f a - (x - a) * y * f')) =o[𝓝[>] a] fun _ => (1 : ℝ) := by
    apply this.trans_isBigO
    apply Tendsto.isBigO_one
    apply cdlim
  have L1 : Tendsto (fun x => (x - a)⁻¹ * (f (a + (x - a) * y) - f a - (x - a) * y * f')) (𝓝[>] a) (𝓝 0) :=
    (isLittleO_one_iff ℝ).1 this
  have L2 : Tendsto (fun x => ((x - a)⁻¹ * ((x - a) * y) * f')) (𝓝[>] a) (𝓝 (y * f')) :=
    Tendsto.mul_const f' cdlim
  have L3 :
    Tendsto (fun x => (x - a)⁻¹ * (f (a + (x - a) * y) - f a - (x - a) * y * f') + (x - a)⁻¹ * ((x - a) * y) * f') (𝓝[>] a) (𝓝 (0 + y * f')) :=
    L1.add L2
  have : (fun x => (x - a)⁻¹ * (f (a + (x - a) * y) - f a - (x - a) * y * f') + (x - a)⁻¹ * ((x - a) * y) * f') =ᶠ[𝓝[>] a]
    (fun x => (x - a)⁻¹ * (f (a + (x - a) * y) - f a)) := by
    apply eventually_nhdsWithin_of_forall (fun x hx => ?_)
    field_simp [inv_mul_cancel (ne_of_gt (sub_pos.mpr <| mem_Ioi.mp hx))]
  have L4 : Tendsto (fun x => (x - a)⁻¹ * (f (a + (x - a) * y) - f a)) (𝓝[>] a) (𝓝 (y * f')) := by
    rw [tendsto_congr' this.symm]
    rw [zero_add] at L3
    apply L3
  suffices : ∀ᶠ x in 𝓝[>] a, ((x - a)⁻¹ * (f (a + (x - a) * y) - f a)) ≤ 0
  · apply le_of_tendsto _ this
    apply L4
  have hd : Tendsto (fun x => a + (x - a) * y) (𝓝[>] a) (𝓝 a) := tendsto_arg
  have hc : ∀ᶠ (x : ℝ) in 𝓝[Ioi a] a, 0 < (x - a)⁻¹ := by
    apply eventually_nhdsWithin_of_forall
    intro x hx
    simp only [inv_pos]
    exact Iff.mpr sub_pos hx
  filter_upwards [hd.eventually h, hc] with x hx hnc
  -- have hx' : f (a + (x - a) * y) - f a ≤ 0 := by simpa using hx
  nlinarith only [hnc, hx]

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMax.hasDerivAt_eq_zero_aux (h : IsLocalMax f a)
    (hf : HasDerivAt f f' a) (y) : y * f' = 0 := by
  apply le_antisymm (IsLocalMax.hasDerivAt_nonpos h hf y)
  simpa using IsLocalMax.hasDerivAt_nonpos h hf (-y)

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMax.hasDerivAt_eq_zero (h : IsLocalMax f a) (hf : HasDerivAt f f' a) : f' = 0 := by
  simpa using IsLocalMax.hasDerivAt_eq_zero_aux h hf 1

theorem IsLocalMin.hasDerivAt_eq_zero_aux (h : IsLocalMin f a)
    (hf : HasDerivAt f f' a) (y) : y * f' = 0 := by
  have h' : IsLocalMax (fun x => - f x) a := by exact neg h
  convert le_antisymm (IsLocalMax.hasDerivAt_nonpos h' hf.neg (-y)) ?_ using 1
  simp only [mul_neg, neg_mul, neg_neg]
  simpa using IsLocalMax.hasDerivAt_nonpos h' hf.neg y

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.hasDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasDerivAt f f' a) : f' = 0 := by
  simpa using IsLocalMin.hasDerivAt_eq_zero_aux h hf 1

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.hasDerivAt_eq_zero (h : IsLocalExtr f a) : HasDerivAt f f' a → f' = 0 := by
  apply h.elim
  · apply IsLocalMin.hasDerivAt_eq_zero
  · apply IsLocalMax.hasDerivAt_eq_zero

variable (f f' : ℝ → ℝ) {a b : ℝ}

/-- **Rolle's Theorem** `HasDerivAt` version -/
theorem exists_hasDerivAt_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) : ∃ c ∈ Ioo a b, f' c = 0 :=
  have ⟨c, cmem, hc⟩ := exists_local_extr_Ioo f hab hfc hfI
  ⟨c, cmem, hc.hasDerivAt_eq_zero <| hff' c cmem⟩
  
variable 
  (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
  (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
  (g g' : ℝ → ℝ) (hgc : ContinuousOn g (Icc a b)) 
  (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)

/-- Cauchy's **Mean Value Theorem**, `HasDerivAt` version. -/
theorem exists_ratio_hasDerivAt_eq_ratio_slope :
    ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c := by
  let h x := (g b - g a) * f x - (f b - f a) * g x
  have hI : h a = h b := by simp only; ring
  let h' x := (g b - g a) * f' x - (f b - f a) * g' x
  have hhh' : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x := by
    intro x hx
    apply HasDerivAt.sub ((hff' x hx).const_mul (g b - g a)) ((hgg' x hx).const_mul (f b - f a))
  have hhc : ContinuousOn h (Icc a b) :=
    (continuousOn_const.mul hfc).sub (continuousOn_const.mul hgc)
  rcases exists_hasDerivAt_eq_zero h h' hab hhc hI hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩

/-- Lagrange's Mean Value Theorem, `HasDerivAt` version -/
theorem exists_hasDerivAt_eq_slope : 
    ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  have hc : ∃ c ∈ Ioo a b, (b - a) * f' c = (f b - f a) * 1 :=
    exists_ratio_hasDerivAt_eq_ratio_slope f f' hab hfc hff' id 1 continuousOn_id
      fun x _ => hasDerivAt_id x
  rcases hc with ⟨c, c_mem, hc⟩
  have : f' c = (f b - f a) / (b - a) := by
    rw [mul_one, mul_comm, ← eq_div_iff (sub_ne_zero.2 hab.ne')] at hc
    apply hc
  exists c
