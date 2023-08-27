import Mathlib.Analysis.Asymptotics.Asymptotics

namespace Tutorial

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
  apply Asymptotics.isBigO_const_mul_self 

-- `x ^ 2`は`x`よりも速くゼロに近づく
example : (fun x ↦ x ^ 2 : ℝ → ℝ) =o[𝓝 0] (fun x ↦ x : ℝ → ℝ) := by
  apply Asymptotics.isLittleO_pow_id (by linarith)

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

/-- 2. `h`が`0`に近づくとき`f (a + h) = f a + h * f' + o(h)`である -/
theorem hasDerivAt_iff_isLittleO_nhds_zero : 
    HasDerivAt f f' a ↔ (fun h ↦ f (a + h) - f a - h * f') =o[𝓝 0] fun h ↦ h := by
  rw [hasDerivAt_iff_isLittleO, ← map_add_left_nhds_zero a, Asymptotics.isLittleO_map]
  simp [(· ∘ ·)]

/-- 3. `x`が`a`に近づくとき`(f x - f a - (x - a) * f') / (x - a)`は`0`に近づく -/
theorem hasDerivAt_iff_tendsto : 
    HasDerivAt f f' a ↔ Tendsto (fun x ↦ (f x - f a - (x - a) * f') / (x - a)) (𝓝[≠] a) (𝓝 0) := by
  calc HasDerivAt f f' a
    _ ↔ Tendsto (fun x ↦ (f x - f a - (x - a) * f') / (x - a)) (𝓝 a) (𝓝 0)      := ?iff1
    _ ↔ Tendsto (fun x ↦ (f x - f a - (x - a) * f') / (x - a)) (𝓝[≠] a) (𝓝 0)   := ?iff2
  case iff1 => rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff_tendsto (by intro _ h; simp [sub_eq_zero.1 h])]
  case iff2 => exact .symm <| tendsto_inf_principal_nhds_iff_of_forall_eq <| by simp

/-- 4. `x`が`a`に近づくとき`(f x - f a) / (x - a)`は`f'`に近づく -/
theorem hasDerivAt_iff_tendsto_slope : 
    HasDerivAt f f' a ↔ Tendsto (fun x ↦ (f x - f a) / (x - a)) (𝓝[≠] a) (𝓝 f') := by
  calc HasDerivAt f f' a
    _ ↔ Tendsto (fun x ↦ (f x - f a) / (x - a) - (x - a) / (x - a) * f') (𝓝[≠] a) (𝓝 0) := ?iff1
    _ ↔ Tendsto (fun x ↦ (f x - f a) / (x - a) - f') (𝓝[≠] a) (𝓝 0)                     := ?iff2
    _ ↔ Tendsto (fun x ↦ (f x - f a) / (x - a)) (𝓝[≠] a) (𝓝 f')                         := ?iff3
  case iff1 => simp only [hasDerivAt_iff_tendsto, sub_div, mul_div_right_comm]
  case iff2 => exact tendsto_congr' <| (Set.EqOn.eventuallyEq fun _ h ↦ (by field_simp [sub_ne_zero.2 h])).filter_mono inf_le_right
  case iff3 => rw [← nhds_translation_sub f', tendsto_comap_iff]; rfl

-- 具体例として、`x ↦ x ^ 2`の微分係数を求める。ここでは2つめの定義を使う。
example (a : ℝ) : HasDerivAt (fun x ↦ x ^ 2) (2 * a) a := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  calc (fun h ↦ (a + h) ^ 2 - a ^ 2 - h * (2 * a)) 
    _ = fun h ↦ h ^ 2                        := ?eq1
    _ =o[𝓝 0] fun h ↦ h                     := ?eq2
  case eq1 =>
    -- ヒント: 関数の間の等号を示したいときは`funext`を使おう
    sorry
  case eq2 =>
    -- ヒント: `apply?`を使って必要な命題を探せる。2行以内で証明できるはず。
    sorry

-- 4つめの定義を使っても示すことができるが、ゼロ除算の扱いに注意する必要がある。
example (a : ℝ) : HasDerivAt (fun x ↦ x ^ 2) (2 * a) a := by
  rw [hasDerivAt_iff_tendsto_slope]
  rw [show 𝓝 (2 * a) = 𝓝 (a + a) by congr; ring]
  apply (tendsto_nhdsWithin_of_tendsto_nhds ((continuous_id.tendsto a).add tendsto_const_nhds)).congr'
  apply eventually_nhdsWithin_of_forall
  intro x hx
  suffices x + a = (x ^ 2 - a ^ 2) / (x - a) by assumption
  have hxa : x - a ≠ 0 := by rw [sub_ne_zero]; simpa using hx
  field_simp [hxa]
  ring

/-
以下では微分に関する基本的な性質を示していく。
-/

-- 必要になるかもしれないランダウ記号の性質
section Landau

variable {f g h f₁ g₁ f₂ g₂ : ℝ → ℝ} {a b : ℝ}

theorem IsLittleO.add (h₁ : f₁ =o[𝓝 a] g) (h₂ : f₂ =o[𝓝 a] g) :
    (fun x ↦ f₁ x + f₂ x) =o[𝓝 a] g := 
  Asymptotics.IsLittleO.add h₁ h₂

theorem IsLittleO.const_mul_left (h : f =o[𝓝 a] g) (c : ℝ) : 
    (fun x ↦ c * f x) =o[𝓝 a] g :=
  Asymptotics.IsLittleO.const_mul_left h c

theorem isBigO_const_mul_self (c : ℝ) (f : ℝ → ℝ) : 
    (fun x ↦ c * f x) =O[𝓝 a] f :=
  Asymptotics.isBigO_const_mul_self c f (𝓝 a)

theorem IsLittleO.comp_tendsto (hfg : f =o[𝓝 b] g) (hh : Tendsto h (𝓝 a) (𝓝 b)) : 
    (f ∘ h) =o[𝓝 a] (g ∘ h) :=
  Asymptotics.IsLittleO.comp_tendsto hfg hh

theorem IsBigO.mul_isLittleO (h₁ : f₁ =O[𝓝 a] g₁) (h₂ : f₂ =o[𝓝 a] g₂) :
    (fun x ↦ f₁ x * f₂ x) =o[𝓝 a] fun x ↦ g₁ x * g₂ x :=
  Asymptotics.IsBigO.mul_isLittleO h₁ h₂

end Landau

theorem hasDerivAt_const (c : ℝ) : HasDerivAt (fun _ ↦ c) 0 a := by
  rw [hasDerivAt_iff_isLittleO]
  -- ヒント: `simp`を使おう
  sorry 

theorem hasDerivAt_id (a : ℝ) : HasDerivAt id 1 a := by
  rw [hasDerivAt_iff_isLittleO]
  sorry

theorem HasDerivAt.add (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a) :
    HasDerivAt (fun x ↦ f x + g x) (f' + g') a := by
  rw [hasDerivAt_iff_isLittleO] at *
  calc (fun x ↦ f x + g x - (f a + g a) - (x - a) * (f' + g')) 
    _ = fun x ↦ (f x - f a - (x - a) * f') + (g x - g a - (x - a) * g') := ?eq1 
    _ =o[𝓝 a] fun x ↦ x - a                                            := ?eq2
  case eq1 =>
    -- ヒント: 関数の間の等号を示したいときは`funext`を使おう
    sorry
  case eq2 =>
    -- ヒント: `apply?`を使って必要な命題を探せる
    sorry

theorem HasDerivAt.const_mul (c : ℝ) (hf : HasDerivAt f f' a) :
    HasDerivAt (fun x ↦ c * f x) (c * f') a := by
  rw [hasDerivAt_iff_isLittleO] at *
  -- ヒント: `HasDerivAt.add`のときと同様に`calc`で計算できる
  sorry

-- Lecture 2で用いる
theorem HasDerivAt.neg (hf : HasDerivAt f f' a) : 
    HasDerivAt (fun x ↦ -f x) (-f') a :=
  suffices HasDerivAt (fun x ↦ -1 * f x) (-1 * f') a by simpa using this
  hf.const_mul (-1)

-- Lecture 2で用いる
theorem HasDerivAt.sub (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a) :
    HasDerivAt (fun x ↦ f x - g x) (f' - g') a :=
  suffices HasDerivAt (fun x ↦ f x + -g x) (f' + -g') a by simpa [sub_eq_add_neg] using this
  hf.add (hg.neg)

/-
合成関数の微分と積の微分についての命題を示す。これらの命題の証明には、微分可能なら連続であることを
用いるので、まずはそれに関連する命題を示しておく。
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
    -- ヒント: `apply?`を使って必要な命題を探せる
    sorry

/-- 微分可能ならば連続 -/
theorem HasDerivAt.continuousAt (h : HasDerivAt f f' a) : 
    Tendsto f (𝓝 a) (𝓝 (f a)) := by
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
  rw [hasDerivAt_iff_isLittleO] at *
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
    -- `IsLittleO.comp_tendsto`が使える
    sorry
  case eq2 => 
    sorry
  case eq3 =>
    sorry
  case eq4 =>
    sorry
  case eq5 =>
    sorry

-- 次の問題で使うかも？
#check IsLittleO.const_mul_left
#check IsBigO.mul_isLittleO

theorem HasDerivAt.mul {f : ℝ → ℝ} (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a) :
    HasDerivAt (fun x ↦ f x * g x) (f' * g a + f a * g') a := by
  rw [hasDerivAt_iff_isLittleO]
  calc (fun x ↦ f x * g x - f a * g a - (x - a) * (f' * g a + f a * g'))
    _ = fun x ↦ g a * (f x - f a - (x - a) * f') + 
          (f a * (g x - g a - (x - a) * g') + (f x - f a) * (g x - g a)) := ?eq1
    _ =o[𝓝 a] fun x ↦ x - a                                             := ?eq2
  case eq1 =>
    sorry
  case eq2 =>
    have hf' : (fun x ↦ g a * (f x - f a - (x - a) * f')) =o[𝓝 a] fun x ↦ x - a := 
      sorry
    have hg' : (fun x ↦ f a * (g x - g a - (x - a) * g')) =o[𝓝 a] fun x ↦ x - a := 
      sorry
    have hfg := 
      calc (fun x ↦ (f x - f a) * (g x - g a))
        _ =o[𝓝 a] fun x ↦ (x - a) * 1      := ?eq3
        _ = fun x ↦ x - a                   := ?eq4
    sorry
    case eq3 =>
      have hg'' : (fun x ↦ g x - g a) =o[𝓝 a] fun _ ↦ (1 : ℝ) := by
        rw [Asymptotics.isLittleO_one_iff, tendsto_sub_nhds_zero_iff]
        sorry
      -- `IsBigO.mul_isLittleO`が使える
      sorry
    case eq4 =>
      sorry
  
-- 次の問題で使うかも？
#check Nat.succ_eq_add_one

/-- 単項式の微分 -/
theorem hasDerivAt_pow (n : ℕ) (a : ℝ) : 
    HasDerivAt (fun x ↦ x ^ (n + 1)) ((n + 1) * a ^ n) a := by
  -- ヒント: `induction n`で帰納法が使える。`induction`の使い方は`cases`と大体同じ。
  sorry

/- 
TIPS: 右画面の表示に現れる`↑n`はcoercionといって、自然数を実数と思いたいときに現れる。
つまり、`n : ℕ`に対して`↑n : ℝ`となる。
-/

-- 再び`x ↦ x ^ 2`の微分。すぐ上で示した`hasDerivAt_pow`を使ってみよう。
example (a : ℝ) : HasDerivAt (fun x ↦ x ^ 2) (2 * a) a := by
  suffices HasDerivAt (fun x ↦ x ^ 2) (((1 : ℕ) + 1) * a ^ 1) a by simpa [one_add_one_eq_two]
  sorry

end Tutorial
