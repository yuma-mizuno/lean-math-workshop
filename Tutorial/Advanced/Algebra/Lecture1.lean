/-
このファイルでは群・部分群・準同型の定義と基本性質を見る。
目標の一つは「群準同型が単射なことと核が自明なことが同値」を示すこと。

# 目次
- Section 1. 群の定義と基本性質
- Section 2. 部分群の定義と基本性質
- Section 3. 群準同型の定義と基本性質
- Section 4. 群準同型に付随する部分群
- Appendix(おまけ、飛ばしてOK): 群は自己全単射のなす群に埋め込める
-/
import Mathlib.Tactic
import Mathlib.Data.SetLike.Basic
namespace Tutorial

section Section1_Definition_and_Basic_Properties
/-
# 1.1 群の定義
数学的には、群とは以下のような情報をまとめたものと思える。
1. 台集合`G`
2. `G`上の二項演算`- * - : G × G → G`
3. 単位元`1 ∈ G`
4. 各元`a ∈ G`に`a⁻¹ ∈ G`を対応させる操作`(-)⁻¹ : G → G`
5. これらが、結合則や単位元や逆元についての条件を満たす
このチュートリアルでは*乗法的記法*のみを用いる。

これをLeanでは以下のように表す。
-/
class Group (G : Type _) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_inv_left : ∀ a : G, mul (inv a) a = one

/-
1. `G : Type _`は`G`が集合であることを表すと思ってよい。
2. `mul : G → G → G`は二項演算（mul = multiplication）。
Leanで`→`は右結合的、つまり`mul : G → (G → G)`、つまり`mul`とは「`G`の元を与えたら「`G`から`G`への関数」を返すような関数」である。
人によっては`Hom(G, Hom(G, G))`と書くと分かりやすいかもしれない。
よって`mul`は二項演算と思える（`a`と`b`の結果は`mul a b`）。
このようにLeanでは`X × Y → Z`の代わりに`X → Y → Z`を使うことが多い。
3. `one : G`とは`G`の単位元のこと。
`G`の元を表すときは `∈`でなく `a : G`のように表すことに注意。
4. `inv : G → G`は`a`に対してその逆元（となるべきもの）を返す関数

ここまでが構造であって、普通の数学ではその後は公理であるが、Leanでは公理（が成り立つという事実）も一緒に群という一つの構造だと思う。
5. `mul_assoc`, `one_mul`, `mul_inv_left`が何を表すかはみれば分かるだろう。

見て分かる通り、今回は*左単位元と左逆元のみ*を要請としているが、群の公理はこれで十分である。
実際、後で*これが右単位元・右逆元であることを示して*いく。
-/

/-
例えばℤは足し算について群であることは次のように表現、証明できる。
（このチュートリアルで群は乗法的にかかれているので注意）
-/
example : Group ℤ where
  mul := fun x y ↦ x + y
  one := 0
  inv := fun x ↦ - x
  mul_assoc := by
    sorry -- ヒント: `apply?`で必要なものを見つけよう
  one_mul := by
    sorry
  mul_inv_left := by
    sorry

-- 環`A`の可逆元全体`Aˣ`は積について群になる
variable [Ring A]

example : Group Aˣ where
  mul := fun a b ↦ a * b
  one := 1
  inv := fun a ↦ a⁻¹
  mul_assoc := by
    sorry
  one_mul := by
    sorry
  mul_inv_left := by
    sorry

/-
# 1.2 群の基本性質
以下この節では`G`を群とする。
-/
variable [Group G]
/-
いちいち`G`の演算を`mul a b`等と書いていたのでは大変なので、
`*`と`1`と`⁻¹` (\inv または \- または \-1) が使えるようにする。
-/
instance : Mul G := ⟨Group.mul⟩
instance : One G := ⟨Group.one⟩
instance : Inv G := ⟨Group.inv⟩

-- 定義から出てくるものを、使えるよう名付けておく

/-- 群の積は結合的である。 -/
theorem mul_assoc (a b c : G) : a * b * c = a * (b * c) := Group.mul_assoc a b c
-- `a * b * c`はLeanでは`(a * b) * c`のこと。
-- `(a * b) * c`と書いてもよい。

/-- `1`は左単位元。 -/
@[simp]
theorem one_mul (a : G) : 1 * a = a := Group.one_mul a

/-- `a⁻¹`は`a`の左逆元。 -/
@[simp]
theorem inv_mul_self (a : G) : a⁻¹ * a = 1 := Group.mul_inv_left a

/-
上に出てきた`@[simp]`について。
これは「左辺を簡単にすると右辺になる」形の定理につけておく。
すると次のように`simp` tacticがこれらを使えるようになる。
-/
example (a b : G) : (a * b)⁻¹ * (a * b) = 1 := by
  -- `simp`を使ってみよう。すると
  -- 自動的に`inv_mul_self`が使われて証明が終わる。
  -- `simp?`にすると使われた定理が分かる。
  sorry

-- 後々のためにもう1つ`simp`を追加。証明中でも`simp`を積極的に使おう。
@[simp]
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  calc
    a⁻¹ * (a * b) = (a⁻¹ * a) * b := by
      sorry
    _ = 1 * b := by
      sorry
    _ = b := by
      sorry

/-
まずは`1`が右単位元でもあることを見ていきたい。
そのため次の補題を使う。
-/
/-- 等しいかどうかは左から元をかけてチェックできる。 -/
theorem mul_left_cancel {a x y : G} : a * x = a * y → x = y := by
  -- ヒント: `intro h`してから上のように`calc`で変形しよう
  -- （`calc`を使わず`rw`のみの縛りプレイでも可能）
  sorry

/-- `1`は右単位元でもある。 -/
@[simp]
theorem mul_one (a : G) : a * 1 = a := by
  /-
  ヒント: `mul_left_cancel`の`a`として`foo`を使いたいときは、
  `apply mul_left_cancel (a := foo)`とする。
  `foo`として何を使えばいいだろうか？
  その後は積極的に`simp`を使おう。
  -/
  sorry

-- `a⁻¹`が`a`の右逆元でもあること
@[simp]
theorem mul_inv_self (a : G) : a * a⁻¹ = 1 := by
  sorry

-- いろいろ便利なので練習も兼ねて`simp`を追加。
@[simp]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc]
  sorry

@[simp]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  sorry

@[simp]
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  sorry

/-- 等しいかどうかは右から元をかけてチェックできる。 -/
theorem mul_right_cancel {a x y : G} : x * a = y * a → x = y := by
  sorry

/-- 左逆元の一意性 -/
theorem inv_eq_of_mul_eq_one_left {a x : G} : x * a = 1 → a⁻¹ = x := by
  sorry

-- その変種。後で便利かも。
theorem eq_inv_of_mul_eq_one_left {a x : G} : x * a = 1 → x = a⁻¹ := fun h ↦ (inv_eq_of_mul_eq_one_left h).symm

@[simp]
theorem inv_one : (1 : G)⁻¹ = 1 := by
  apply inv_eq_of_mul_eq_one_left
  sorry

@[simp]
theorem inv_inv {a : G} : a⁻¹⁻¹ = a := by
  sorry

/-- 積の逆元は逆元をひっくり返した積。 -/
@[simp]
theorem mul_inv_rev {a b : G} : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

theorem mul_inv_eq_iff_eq_mul {a b c : G} : a * b⁻¹ = c ↔ a = c * b := by
  -- ヒント: `constructor`でゴールを分けよう
  sorry

theorem mul_inv_eq_one {a b : G} : a = b ↔ a * b⁻¹ = 1 := by
  sorry

end Section1_Definition_and_Basic_Properties


section Section2_Subgroup
/-
# 2. 部分群
群`G`の部分群とは、単位元を含み積と逆元で閉じた`G`の部分集合である。
これは以下のように定式化できる。
-/
structure Subgroup (G) [Group G] where
  carrier : Set G
  one_mem' : 1 ∈ carrier
  mul_mem' : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  inv_mem' : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier
/-
- 群`G`に対して、`Set G`とは`G`の部分集合の集合と思ってよい。
- `carrier`とは部分群の台集合
- その他は部分群の公理

*Leanでの部分集合の扱いについて*
全体集合`X`の部分集合`A : Set X`については、
`x : X`が`A`に属することは、`x : A`でなく`x ∈ A`と書く。
上で`1 ∈ carrier`等書いているのはそのため。

*上級者向け、飛ばしてください*
集合`X`について`Set X`とは実は`X → Prop`のことで、
`A : Set X`とは「`X`の元が与えられたら、それが`A`に属するかどうかの命題を返す関数`A : G → Prop`のこと」
ようするに`{x : X | xについての条件 }`という部分集合の作り方の、
`xについての条件`のところを取り出したのが`A`である。
`x : X`がこの条件`A`を満たす、つまり`A x`のことを、
数学の慣習と合うように`x ∈ A`と書いている。
（`x ∈ A`の定義は実は`A x`なので、上で`carrier 1`とか書いてもエラーは出ない。）
このような実装をしているのは、`X`の元`x`の型は唯一つのみであって、
同時に`x : X`かつ`x : A`であることはありえない、という型理論の要請からきている。
-/

-- 以下この節では`G`を群、`H`をその部分群とする
variable [Group G] {H : Subgroup G}

/-
部分群とは「台集合と、ある公理たちが成り立つという事実との組」なので、
本来は`a ∈ H`とは書けず`a ∈ H.carrier`と書かなければならない。
それは面倒なので以下のおまじないにより`a ∈ H`と書ける。
-/
instance : SetLike (Subgroup G) G where
  coe H := H.carrier
  coe_injective' H₁ H₂ _ := by cases H₁; cases H₂; congr

namespace Subgroup

-- 定義からすぐ分かること

@[simp]
theorem one_mem : 1 ∈ H := H.one_mem'

theorem mul_mem {a b : G} : a ∈ H → b ∈ H → a * b ∈ H := H.mul_mem'

theorem inv_mem {a : G} : a ∈ H → a⁻¹ ∈ H := H.inv_mem'

theorem inv_mem_iff {a : G} : a⁻¹ ∈ H ↔ a ∈ H := by
  sorry

/-
部分群が等しいとは`∈`が同値なとき。
このような補題を`ext`マークつけておくと、
部分群が等しいことを示すとき`ext` tacticで使えるようになる。
-/
@[ext]
theorem ext {H K : Subgroup G} : (∀ x : G, x ∈ H ↔ x ∈ K) → H = K := SetLike.ext

end Subgroup

end Section2_Subgroup


section Section3_GroupHom
/-
# 3. 群の準同型
群`G₁`と`G₂`に対して、その準同型とは、写像であって積を保つものをいう。
今までと同じように、underlying mapと、それが写像を保つこと、を束ねてこれを実装する。
-/
structure GroupHom (G₁ : Type _) (G₂ : Type _) [Group G₁] [Group G₂] where
  toFun : G₁ → G₂
  map_mul' : ∀ a b : G₁, toFun (a * b) = toFun a * toFun b
  -- 単位元を保つことはここから従う、後で示す

-- `f : G₁ →* G₂`で群準同型を表せるようにする。
infixr:25 " →* " => GroupHom

-- 以下この節では`G₁`と`G₂`を群、`f`をその間の準同型とする。
variable [Group G₁] [Group G₂] {f : G₁ →* G₂}

-- `f`と`a : G₁`に対して`f a`などと書くためのおまじない
-- （`f`そのものは、関数と「積を保つという事実」を束ねたもので本来は関数でない）
instance : FunLike (G₁ →* G₂) G₁ (fun _ ↦ G₂) where
  coe := fun f ↦ f.toFun
  coe_injective' f₁ f₂ _ := by cases f₁; cases f₂; congr

-- 定義から分かること
@[simp]
theorem map_mul {a b : G₁} : f (a * b) = f a * f b := f.map_mul' a b

/-- 群準同型は単位元を保つ。 -/
@[simp]
theorem map_one : f 1 = 1 := by
  have h : f 1 * f 1 = f 1 := by
    sorry
  sorry

/-- 群準同型は逆元を保つ。 -/
@[simp]
theorem map_inv {a : G₁} : f (a⁻¹) = (f a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  sorry

/--
2つの郡準同型`f₁ : G₁ →* G₂`と`f₂ : G₂ →* G₃`の合成`f₂ ∘ f₁`も準同型。
`f₂.comp f₁`でアクセスできる。 -/
def GroupHom.comp [Group G₁] [Group G₂] [Group G₃]
  (f₂ : G₂ →* G₃) (f₁ : G₁ →* G₂) : G₁ →* G₃ where
  toFun := f₂ ∘ f₁
  map_mul' := by
    sorry -- ヒント: まずは`simp`を試そう

-- 恒等写像は準同型
def GroupHom.id (G) [Group G] : G →* G where
  toFun := fun a ↦ a
  map_mul' := by
    sorry

-- 全てを`1`に飛ばす写像は準同型
def GroupHom.one : G₁ →* G₂ where
  toFun := fun _ ↦ 1
  map_mul' := by
    sorry

end Section3_GroupHom


section Section4_Hom_and_Subgroups
/-
# 4. 群準同型に付随する部分群
群準同型`f : G₁ →* G₂`に対して、その像と核を定義し、
基本性質や、「単射なことと核が自明が同値」等を示そう。
この節では`G₁`と`G₂`を群とする。
-/
variable [Group G₁] [Group G₂]

namespace GroupHom

/-- 群準同型`f : G₁ →* G₂`の像（`G₂`の部分群）。
慣習に合わせて`range`とする。`f.range`でアクセス可能。
-/
def range (f : G₁ →* G₂) : Subgroup G₂ where
  carrier := Set.range f -- `f`の写像としての像
  -- これが部分群の公理を満たすことを示す必要がある。
  one_mem' := by
    -- ヒント: とりあえず`simp`して考えよう
    -- `∃ a : A, P a`を示したかったら、
    -- 条件を満たす`a`を探して`exists a`しよう
    sorry
  mul_mem' := by
    sorry
  inv_mem' := by
    sorry

/-- 群準同型`f : G₁ →* G₂`の核（`G₁`の部分群）。`f.ker`でアクセス可能。 -/
def ker (f : G₁ →* G₂) : Subgroup G₁ where
  carrier := { a : G₁ | f a = 1 } -- このような直感的な記法が使える
  -- 部分群の公理を満たすことを示そう。
  one_mem' := by
    sorry
  mul_mem' := by
    sorry
  inv_mem' := by
    sorry

/-- 核に入ることと飛ばして`1`に行くことは同値。 -/
@[simp]
theorem mem_ker {f : G₁ →* G₂} {a : G₁} : a ∈ f.ker ↔ f a = 1 := Iff.rfl 

end GroupHom

/-
以下は*準同型写像が単射なことと核が自明なことは同値*を示してく。
これを正確に述べるために、まだ自明な部分群を定義していなかった。
「全体」と「単位元のみ」という2つの部分群を定義する。
以下この節では`G`を群とする。
-/
variable [Group G]
-- 群`G`は`G`の部分群でもある
instance : Top (Subgroup G) where
  top := {
    carrier := Set.univ -- これは`G`を`G`の部分集合とみなしたもの
    one_mem' := by
      sorry
    mul_mem' := by
      sorry
    inv_mem' := by
      sorry
  }

-- これは以下のように使える。`⊤`は\topで入力し、これはこの部分群が
-- 部分群全体のなす順序集合の最大元なことからくる慣習的記法。
#check (⊤ : Subgroup G)

-- 双対的に、`⊥`(\bot)も定義しよう。
instance : Bot (Subgroup G) where
  bot := {
    carrier := { 1 } -- `1`のみからなる一元集合
    one_mem' := by
      sorry
    mul_mem' := by
      sorry
    inv_mem' := by
      sorry
  }

/-- 自明部分群`⊥`に属することと`1`なことは同値。 -/
@[simp]
theorem mem_bot {a : G} : a ∈ (⊥ : Subgroup G) ↔ a = 1 := Iff.rfl

/-- 全ての元は部分群`⊤`に属する。 -/
@[simp]
theorem mem_top {a : G} : a ∈ (⊤ : Subgroup G) := trivial

namespace GroupHom
-- 以下`f`を群準同型`f : G₁ →* G₂`とする。
variable {f : G₁ →* G₂}

-- 「単射と核が自明が同値」の証明で本質的なのは下の主張。
#check mul_inv_eq_one -- これが役立つかも
theorem injective_iff_map_eq_one : Function.Injective f ↔ (∀ a, f a = 1 → a = 1) := by
  sorry

/-- 群準同型の核が自明なことと単射なことは同値。 -/
theorem ker_eq_bot_iff : f.ker = ⊥ ↔ Function.Injective f := by
  -- 上の`injective_iff_map_eq_one`で`rw`してから`constructor`がよい。
  -- （上を使わず直接示すこともできる）
  sorry

/-- 群準同型の像が全体なことと全射なことは同値。 -/
theorem range_eq_top_iff : f.range = ⊤ ↔ Function.Surjective f := by
  constructor
  · intro hrange y
    have hy : y ∈ (⊤ : Subgroup G₂) := by
      sorry
    sorry
  · intro hsurj
    ext a
    sorry

end GroupHom

end Section4_Hom_and_Subgroups


section Appendix
/-
# Appendix: 群の対称群への埋め込み
群`G`は`G`上の全単射のなす群に単射で埋め込めることがよく知られている。
とくに有限群は対称群の部分群として実現できる。
このAppendiexではそれを見ていく。
このことは今後に関係ないので、気になる人だけ見ればよい。
-/
open Equiv
/--
`X`上の全単射のなす集合は`Perm X`である。
正確には、`Perm X`の元は写像`toFun`、その逆写像`invFun`、
それが左・右逆写像であることの証明、という組。
`Perm X`に群構造を与えよう。
-/
instance (X : Type _) : Group (Perm X) where
  mul f g := Equiv.trans g f
  -- この積`f * g`は、先に`g`、次に`f`という、関数の合成の向き。
  one := Equiv.refl X
  inv := Equiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_inv_left := Equiv.self_trans_symm

/-- `Perm X`上の積の定義の確認。 -/
@[simp]
theorem mul_apply {f g : Perm X} {x : X} : (f * g) x = f (g x) := rfl

/-
群`G`があったとき、単射準同型`G →* Perm G`が、
`a ↦ (G → G, x ↦ a * x)`で定義されるはずである。
まず準同型の構成をする。
-/
variable (G) [Group G]
def homToPerm : G →* Perm G where
  toFun := fun a ↦ {
    -- `G → G, x ↦ a * x`に対応する`Perm G`の元を構成する
    toFun := fun x ↦ a * x
    -- この写像の逆写像は何であろうか。
    invFun := sorry
    -- これらが互いに逆写像なことを示していく。
    left_inv := by
      rw [Function.LeftInverse]
      sorry
    right_inv := by
      sorry
  }
  map_mul' := by
    -- 上の写像が積を保つことの証明
    -- ヒント: ゴールが`f g : Perm G`について`f = g`なら、
    -- `ext x`とすると、`f x = g x`を示すことの帰着される。
    sorry

#check homToPerm G -- `homToPerm G`で群準同型`G →* Perm G`を表す

/-- 上で定義した`homToPerm`は単射である。 -/
theorem homToPerm_injective : Function.Injective (homToPerm G) := by
  intro a b h
  calc
    a = a * 1 := by simp
    _ = (homToPerm G a) 1 := by
      -- 冷静に考えるとこれは`homToPerm`の定義なので、`trivial`である
      sorry
    -- 必要ならば途中計算をいくつか入れよう。
    _ = b := by
      sorry

-- 以上により任意の群`G`に対して、単射準同型`G →* Perm G`が構成できた！

end Appendix

end Tutorial
