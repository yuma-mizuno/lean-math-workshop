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

/-- 関数`f : ℝ → ℝ`の`a : ℝ`における微分係数は`f' : ℝ`である -/
def HasDerivAt (f : ℝ → ℝ) (f' : ℝ) (a : ℝ) :=
  (fun x ↦ f x - f a - (x - a) * f') =o[𝓝 a] fun x ↦ x - a

/- 以下、4つの同値な特徴づけを与える（同値性の証明については読み飛ばしても構わない） -/

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
    funext h
    ring
  case eq2 =>
    -- ヒント: `apply?`を使って必要な命題を探せる。2行以内で証明できるはず。
    apply isLittleO_pow_id (by linarith)

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
  simp

theorem hasDerivAt_id (a : ℝ) : HasDerivAt id 1 a := by
  rw [hasDerivAt_iff_isLittleO]
  simp

theorem HasDerivAt.add (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a) :
    HasDerivAt (fun x ↦ f x + g x) (f' + g') a := by
  rw [hasDerivAt_iff_isLittleO] at *
  calc (fun x ↦ f x + g x - (f a + g a) - (x - a) * (f' + g'))
    _ = fun x ↦ (f x - f a - (x - a) * f') + (g x - g a - (x - a) * g') := ?eq1
    _ =o[𝓝 a] fun x ↦ x - a                                            := ?eq2
  case eq1 =>
    -- ヒント: 関数の間の等号を示したいときは`funext`を使おう
    funext x
    ring
  case eq2 =>
    -- ヒント: `apply?`を使って必要な命題を探せる
    apply IsLittleO.add hf hg

theorem HasDerivAt.const_mul (c : ℝ) (hf : HasDerivAt f f' a) :
    HasDerivAt (fun x ↦ c * f x) (c * f') a := by
  rw [hasDerivAt_iff_isLittleO] at *
  -- ヒント: `HasDerivAt.add`のときと同様に`calc`で計算できる
  calc (fun x ↦  c * f x - c * f a - (x - a) * (c * f'))
    _ = fun x ↦ c * (f x - f a - (x - a) * f') := ?eq1
    _ =o[𝓝 a] fun x ↦ x - a                   := ?eq2
  case eq1 =>
    funext x
    ring
  case eq2 =>
    apply IsLittleO.const_mul_left hf c

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
    funext x
    ring
  case eq2 =>
    -- ヒント: `apply?`を使って必要な命題を探せる
    apply isBigO_const_mul_self

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
    apply hg.comp_tendsto
    apply hf.continuousAt
  case eq2 =>
    apply hf.isBigO_sub
  case eq3 =>
    funext
    ring
  case eq4 =>
    apply isBigO_const_mul_self
  case eq5 =>
    apply hf

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
    funext
    ring
  case eq2 =>
    have hf' : (fun x ↦ g a * (f x - f a - (x - a) * f')) =o[𝓝 a] fun x ↦ x - a := by
      apply IsLittleO.const_mul_left hf
    have hg' : (fun x ↦ f a * (g x - g a - (x - a) * g')) =o[𝓝 a] fun x ↦ x - a := by
      apply IsLittleO.const_mul_left hg
    have hfg :=
      calc (fun x ↦ (f x - f a) * (g x - g a))
        _ =o[𝓝 a] fun x ↦ (x - a) * 1      := ?eq3
        _ = fun x ↦ x - a                   := ?eq4
    apply IsLittleO.add hf'
    apply IsLittleO.add hg'
    apply hfg
    case eq3 =>
      have hg'' : (fun x ↦ g x - g a) =o[𝓝 a] fun _ ↦ (1 : ℝ) := by
        rw [Asymptotics.isLittleO_one_iff, tendsto_sub_nhds_zero_iff]
        apply hg.continuousAt
      -- `IsBigO.mul_isLittleO`が使える
      apply IsBigO.mul_isLittleO
      · apply isBigO_sub hf
      · apply hg''
    case eq4 =>
      funext
      ring

-- 次の問題で使うかも？
#check Nat.succ_eq_add_one

/-- 単項式の微分 -/
theorem hasDerivAt_pow (n : ℕ) (a : ℝ) :
    HasDerivAt (fun x ↦ x ^ (n + 1)) ((n + 1) * a ^ n) a := by
  -- ヒント: `induction n`で帰納法が使える。`induction`の使い方は`cases`と大体同じ。
  induction n
  case zero => simp [hasDerivAt_iff_isLittleO_nhds_zero]
  case succ n ih =>
    rw [Nat.succ_eq_add_one]
    suffices HasDerivAt (fun x => x ^ (n + 1) * x) (((n + 1) * a ^ n) * a + a ^ (n + 1) * 1) a by
      apply IsLittleO.congr_left this
      intro x
      simp
      ring
    apply ih.mul (hasDerivAt_id a)

/-
TIPS: 右画面の表示に現れる`↑n`はcoercionといって、ここでは自然数を実数と思いたいときに現れる。
つまり、`n : ℕ`に対して`↑n : ℝ`となる。
-/

-- 再び`x ↦ x ^ 2`の微分。すぐ上で示した`hasDerivAt_pow`を使ってみよう。
example (a : ℝ) : HasDerivAt (fun x ↦ x ^ 2) (2 * a) a := by
  suffices HasDerivAt (fun x ↦ x ^ 2) (((1 : ℕ) + 1) * a ^ 1) a by simpa [one_add_one_eq_two]
  apply hasDerivAt_pow

/- # Leanでの部分関数の扱いについて
少し発展的な話題となります。読み飛ばしても問題ありません。

`HasDerivAt`による微分の定義は一般性が足りず不十分と思う人がいるかもしれない。というのも、
`HasDerivAt`は微分係数を関数`f : ℝ → ℝ`に対して定義しているが、実際には定義域が全体でない関数を扱い
たい場合があるからである（例えば`x⁻¹`や`tan x`など）。しかし実は`HasDerivAt`の定義で十分である。
全体が定義域とは限らない関数`f : U → ℝ`に対してはその拡張`f⁺ : ℝ → ℝ`を考えることができ（例えば
`U`の外側では`f x := 0`とすればよい）、`f`について論じる代わりに`f⁺`について論じればよいからである。

一般に、部分関数を扱う方法として以下の3つがある。
1. 定義域を制限する
2. 値域に「未定義」という元を付加する
3. 定義域の外側の値を何でもよいので決めてしまう

数学では多くの場合1.の方法がとられる。プログラミングの世界では2.の方法がとられることも多い（値域を
拡張する方法としてOption型が知られている）。一方でLeanでは3.の方法が便利な場合ことが多い。実数関数の
扱いもその一例である。

1.の方法に慣れている数学者からすると3.の方法は受け入れがたいかもしれない。確かに一見「ad-hoc」で
「不自然」なようにも思える。しかしLeanで数学をやる際にはこの方法がもっとも便利だと考えられている。
この話題についてより詳しく知りたい場合はブログ記事
https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/
を参照せよ。

例として`HasDerivAt`が`x⁻¹`の微分を問題なく扱えることを確認しておく。
-/

example (a : ℝ) (ha : a ≠ 0) : HasDerivAt (fun x ↦ x⁻¹) (-(a ^ 2)⁻¹) a := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hne : ∀ᶠ x in 𝓝[≠] a, x ≠ 0 := eventually_ne_nhdsWithin ha
  have hne' : ∀ᶠ x in 𝓝[≠] a, x ≠ a := eventually_mem_nhdsWithin
  have : (fun x ↦ (x⁻¹ - a⁻¹) / (x - a)) =ᶠ[𝓝[≠] a] fun x ↦ - (x⁻¹ * a⁻¹) := by
    filter_upwards [hne, hne'] with x hx hx'
    rw [← sub_ne_zero] at hx'
    field_simp
    ring
  apply (tendsto_nhdsWithin_of_tendsto_nhds _).neg.congr' this.symm
  rw [show (a ^ 2)⁻¹ = a⁻¹ * a⁻¹ by ring]
  apply (tendsto_inv₀ ha).mul_const a⁻¹

/-
この例における`fun x ↦ x⁻¹`の型は`ℝ → ℝ`であり、全域関数として扱われている。つまり`0⁻¹`にも何らか
の値を割り当てている。その値が気になるかもしれないが...実は気にする必要はない。上の証明は`0⁻¹`の値
がなんであろうと成立する。また、仮定に`a ≠ 0`があるので、上記の主張では`x⁻¹`の`0`における微分係数に
ついては何も言っていない。ここではやらないが、`x⁻¹`の`0`における微分係数は存在しないことが証明でき
るだろう。`x⁻¹`の定義域を制限しない代わりに、`x⁻¹`に関する定理の主張に制限が付くと考えるとよいかも
しれない。
-/

/- `0⁻¹`の値が気になる人へ: Leanでは`0⁻¹`は`0`と定義されている -/
example : (0 : ℚ)⁻¹ = 0 := by rfl
example : (0 : ℝ)⁻¹ = 0 := by ring

end Tutorial
