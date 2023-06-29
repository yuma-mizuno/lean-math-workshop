import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Asymptotics.Asymptotics

open Topology Filter Asymptotics

/- # ランダウ記号
mathlibではランダウ記号を次のように記述する。
- `f =O[𝓝 a] g`: （よくある記法ではf(x) = O(g(x)) as x → a）
- `f =o[𝓝 a] g`: （よくある記法ではf(x) = o(g(x)) as x → a）
すなわち、関数`f, g : ℝ → ℝ`に対して、`f = O[𝓝 a] g`は`x`が十分`a`に近いときに`|f x|`が`|g x|`の
定数倍で抑えられることを表す。また、`f = o[𝓝 a] g`は`x`が十分`a`に近いときに`|f x|`が`|g x|`の
任意に小さい定数倍で抑えられることを表す。
-/

-- 定数倍は自身のBig O
example : (fun x ↦ 2 * x : ℝ → ℝ) =O[𝓝 0] (fun x ↦ x : ℝ → ℝ) := by
  apply isBigO_const_mul_self 

-- `x ^ 2`は`x`よりも速くゼロに近づく
example : (fun x ↦ x ^ 2 : ℝ → ℝ) =o[𝓝 0] (fun x ↦ x : ℝ → ℝ) := by
  apply isLittleO_pow_id (by linarith)

-- ランダウ記号の計算は、あたかも等式の変形のように扱えて便利
example : (fun x ↦ 11 * x ^ 5 + 4 * x ^ 3 : ℝ → ℝ) =o[𝓝 0] (fun x ↦ 23 * x ^ 2 : ℝ → ℝ) := by
  have h₁ := 
    calc (fun x ↦  11 * x ^ 5 : ℝ → ℝ) 
      _ =O[𝓝 0] fun x ↦ x ^ 5        := by apply isBigO_const_mul_self
      _ =o[𝓝 0] fun x ↦ x ^ 2        := by apply isLittleO_pow_pow (by linarith)
      _ =O[𝓝 0] fun x ↦ 23 * x ^ 2   := by apply isBigO_self_const_mul _ (by linarith)
  have h₂ := 
    calc (fun x ↦ 4 * x ^ 3 : ℝ → ℝ) 
      _ =O[𝓝 0] fun x ↦ x ^ 3        := by apply isBigO_const_mul_self
      _ =o[𝓝 0] fun x ↦ x ^ 2        := by apply isLittleO_pow_pow (by linarith)
      _ =O[𝓝 0] fun x ↦ 23 * x ^ 2   := by apply isBigO_self_const_mul _ (by linarith)
  apply h₁.add h₂

example : (fun x ↦ 4 * x ^ 5 - 2 * x ^ 4 : ℝ → ℝ) =o[𝓝 0] (fun x ↦ 5 * x ^ 3 : ℝ → ℝ) := by
  sorry

/- # 微分 -/

/-- 関数`f : ℝ → ℝ`の`a : ℝ`における微分係数が`f' : ℝ`である -/
def HasDerivAt (f : ℝ → ℝ) (f' : ℝ) (a : ℝ) := 
  (fun x ↦ f x - f a - (x - a) * f') =o[𝓝 a] fun x ↦ x - a 

/-
以下、4つの同値な特徴づけを与える。
-/

variable {f : ℝ → ℝ} {f' : ℝ} {a : ℝ}

/-- 1. `x`が`a`に近づくとき`f x = f a + (x - a) * f' + o(x - a)`である -/
theorem hasDerivAt_iff_isLittleO : 
    HasDerivAt f f' a ↔ (fun x ↦ f x - f a - (x - a) * f') =o[𝓝 a] fun x ↦ x - a := by
  rfl

/-- 2. `h`が`0`に近づくとき`f (x + h) = f a + h * f' + o(h)`である -/
theorem hasDerivAt_iff_isLittleO_nhds_zero : 
    HasDerivAt f f' a ↔ (fun h ↦ f (a + h) - f a - h * f') =o[𝓝 0] fun h => h := by
  rw [hasDerivAt_iff_isLittleO, ← map_add_left_nhds_zero a, isLittleO_map]
  simp [(· ∘ ·)]

/-- 3. `x`が`a`に近づくとき`(x - a)⁻¹ * (f x - f a - (x - a) * f')`は`0`に近づく -/
theorem hasDerivAt_iff_tendsto : 
    HasDerivAt f f' a ↔ Tendsto (fun x ↦ (x - a)⁻¹ * (f x - f a - (x - a) * f')) (𝓝[≠] a) (𝓝 0) := by
  calc HasDerivAt f f' a
    _ ↔ Tendsto (fun x ↦ (f x - f a - (x - a) * f') / (x - a)) (𝓝 a) (𝓝 0)      := ?iff1
    _ ↔ Tendsto (fun x ↦ (f x - f a - (x - a) * f') / (x - a)) (𝓝[≠] a) (𝓝 0)   := ?iff2
    _ ↔ Tendsto (fun x ↦ (x - a)⁻¹ * (f x - f a - (x - a) * f')) (𝓝[≠] a) (𝓝 0) := ?iff3   
  case iff1 => rw [hasDerivAt_iff_isLittleO, isLittleO_iff_tendsto (by intro _ h; simp [sub_eq_zero.1 h])]
  case iff2 => exact .symm <| tendsto_inf_principal_nhds_iff_of_forall_eq <| by simp
  case iff3 => exact tendsto_congr (by intros; field_simp)

/-- 4. `x`が`a`に近づくとき`(x - a)⁻¹ * (f x - f a)`は`f'`に近づく -/
theorem hasDerivAt_iff_tendsto_slope : 
    HasDerivAt f f' a ↔ Tendsto (fun x ↦ (x - a)⁻¹ * (f x - f a)) (𝓝[≠] a) (𝓝 f') := by
  calc HasDerivAt f f' a
    _ ↔ Tendsto (fun x ↦ (x - a)⁻¹ * (f x - f a) - (x - a)⁻¹ * (x - a) * f') (𝓝[≠] a) (𝓝 0) := ?iff1
    _ ↔ Tendsto (fun x ↦ (x - a)⁻¹ * (f x - f a) - f') (𝓝[≠] a) (𝓝 0)                       := ?iff2
    _ ↔ Tendsto (fun x ↦ (x - a)⁻¹ * (f x - f a)) (𝓝[≠] a) (𝓝 f')                           := ?iff3
  case iff1 => simp only [hasDerivAt_iff_tendsto, mul_sub, mul_assoc, sub_mul]
  case iff2 => exact tendsto_congr' <| (Set.EqOn.eventuallyEq fun _ h ↦ (by field_simp [sub_ne_zero.2 h])).filter_mono inf_le_right
  case iff3 => rw [← nhds_translation_sub f', tendsto_comap_iff]; rfl

-- 具体例として、`x ↦ x ^ 2`の微分係数を求める。まずは2つめの定義を使う。
example (x : ℝ) : HasDerivAt (fun x ↦ x ^ 2 : ℝ → ℝ) (2 * x) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  calc (fun h ↦ (x + h) ^ 2 - x ^ 2 - h * (2 * x)) 
    _ = fun h ↦ h ^ 2                        := ?eq1
    _ =o[𝓝 0] fun h ↦ h                     := ?eq2
  case eq1 =>
  -- ヒント: 関数の間の等号を示したいときは`funext`を使おう
    sorry
  case eq2 =>
  -- ヒント: `apply?`を使って必要な命題を探そう
    sorry

-- 次の問題で使うかも？
#check inv_mul_cancel

-- 次は4つめの定義を使って同じ事実を証明する。
example (x : ℝ) : HasDerivAt (fun x ↦ x ^ 2 : ℝ → ℝ) (2 * x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  -- 条件をε-δで書き換える
  suffices ∀ (ε : ℝ), ε > 0 → ∃ δ, δ > 0 ∧ 
      ∀ {y : ℝ}, y ≠ x → |y - x| < δ → 
        |(y - x)⁻¹ * (y ^ 2 - x ^ 2) - 2 * x| < ε from
    Metric.tendsto_nhdsWithin_nhds.mpr this
  sorry

/-
以下では微分に関する基本的な性質を示していく。
-/

theorem HasDerivAt.isBigO_sub (h : HasDerivAt f f' a) : 
    (fun x ↦ f x - f a) =O[𝓝 a] fun x ↦ x - a := by
  rw [hasDerivAt_iff_isLittleO] at h
  rw [h.isBigO.congr_of_sub]
  calc (fun x ↦ (x - a) * f') 
    _ = fun x ↦ f' * (x - a)  := ?eq1
    _ =O[𝓝 a] fun x ↦ x - a  := ?eq2
  case eq1 =>
    -- ヒント: 関数の間の等号を示したいときは`funext`を使おう
    sorry
  case eq2 =>
    -- ヒント: `apply?`を使って必要な命題を探そう
    sorry

/-- 微分可能ならば連続 -/
theorem HasDerivAt.continuousAt (h : HasDerivAt f f' a) : Tendsto f (𝓝 a) (𝓝 (f a)) := by
  have : Tendsto (fun x ↦ f x - f a + f a) (𝓝 a) (𝓝 (0 + f a)) := by
    apply Tendsto.add _ tendsto_const_nhds
    apply h.isBigO_sub.trans_tendsto
    rw [← sub_self a]
    apply tendsto_id.sub tendsto_const_nhds
  rw [zero_add] at this
  exact this.congr (by simp)

-- 次の問題で使うかも？
#check isBigO_const_mul_self
#check IsLittleO.comp_tendsto

variable {g : ℝ → ℝ} {g' : ℝ}

/-- 合成関数の微分 -/
theorem HasDerivAt.comp (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' (f a)) : 
    HasDerivAt (g ∘ f) (g' * f') a := by
  rw [hasDerivAt_iff_isLittleO]
  have h₁ := 
    calc (fun x ↦ g (f x) - g (f a) - (f x - f a) * g') 
        =o[𝓝 a] fun x ↦ f x - f a                := ?eq1
      _ =O[𝓝 a] fun x ↦ x - a                    := ?eq2
  have h₂ := 
    calc (fun x ↦ (f x - f a) * g' - (x - a) * (g' * f'))
      _ = fun x ↦ g' * (f x - f a - (x - a) * f') := ?eq3
      _ =O[𝓝 a] fun x ↦ f x - f a - (x - a) * f' := ?eq4 
      _ =o[𝓝 a] fun x ↦ x - a                    := ?eq5
  apply h₁.triangle h₂
  case eq1 =>
    sorry
  case eq2 => 
    sorry
  case eq3 =>
    sorry
  case eq4 =>
    sorry
  case eq5 =>
    sorry

theorem hasDerivAt_const (c : ℝ) : HasDerivAt (fun _ => c) 0 a := by
  sorry

-- 次の問題で使うかも？
#check IsLittleO.add

theorem HasDerivAt.add (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a) :
    HasDerivAt (fun x ↦ f x + g x) (f' + g') a := by
  rw [hasDerivAt_iff_isLittleO]
  calc (fun x ↦ f x + g x - (f a + g a) - (x - a) * (f' + g')) 
    _ = fun x ↦ (f x - f a - (x - a) * f') + (g x - g a - (x - a) * g') := ?eq1 
    _ =o[𝓝 a] fun x ↦ x - a                                            := ?eq2
  case eq1 =>
    sorry
  case eq2 =>
    sorry

-- 次の問題で使うかも？
#check IsLittleO.const_mul_left
#check IsBigO.mul_isLittleO

theorem HasDerivAt.mul {f : ℝ → ℝ} (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a) :
    HasDerivAt (fun x ↦ f x * g x) (f a * g' + f' * g a) a := by
  rw [hasDerivAt_iff_isLittleO]
  calc (fun x ↦ f x * g x - f a * g a - (x - a) * (f a * g' + f' * g a))
    _ = fun x ↦ f a * (g x - g a - (x - a) * g') + 
          (g a * (f x - f a - (x - a) * f') + (f x - f a) * (g x - g a)) := ?eq1
    _ =o[𝓝 a] fun x ↦ x - a                                             := ?eq2
  case eq1 =>
    sorry
  case eq2 =>
    have hg' : (fun x => f a * (g x - g a - (x - a) * g')) =o[𝓝 a] fun x => x - a := 
      sorry
    have hf' : (fun x => g a * (f x - f a - (x - a) * f')) =o[𝓝 a] fun x => x - a := 
      sorry
    have hfg := calc (fun x => (f x - f a) * (g x - g a))
      _ =o[𝓝 a] fun x => (x - a) * 1      := ?eq3
      _ = fun x => x - a                   := ?eq4
    sorry
    case eq3 =>
      have hg'' : (fun x => g x - g a) =o[𝓝 a] fun _ => (1 : ℝ) := by
        rw [isLittleO_one_iff, tendsto_sub_nhds_zero_iff]
        sorry
      sorry
    case eq4 =>
      sorry

theorem HasDerivAt.const_mul (c : ℝ) (hf : HasDerivAt f f' a) :
    HasDerivAt (fun x ↦ c * f x) (c * f') a := by
  sorry

theorem HasDerivAt.neg (hf : HasDerivAt f f' a) : HasDerivAt (fun x ↦ -f x) (-f') a := by
  suffices HasDerivAt (fun x ↦ -1 * f x) ((-1) * f') a by simpa using this  
  sorry
  
theorem HasDerivAt.sub (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a) :
    HasDerivAt (fun x ↦ f x - g x) (f' - g') a := by
  sorry

theorem hasDerivAt_id (a : ℝ) : HasDerivAt id 1 a := by
  sorry
  
-- 次の問題で使うかも？
#check Nat.succ_eq_add_one

/-- 単項式の微分 -/
theorem hasDerivAt_pow (n : ℕ) (x : ℝ) : HasDerivAt (fun x ↦ x ^ n : ℝ → ℝ) (n * x ^ (n - 1)) x := by
  -- ヒント: `induction n`で帰納法が使える。`induction`の使い方は`cases`と大体同じ。
  sorry

-- 再び`x ↦ x ^ 2`の微分。すぐ上で示した`hasDerivAt_pow`を使ってみよう。
example (x : ℝ) : HasDerivAt (fun x ↦ x ^ 2 : ℝ → ℝ) (2 * x) x := by
  suffices HasDerivAt (fun x ↦ x ^ 2) (2 * x ^ (2 - 1)) x by simpa using this
  sorry

