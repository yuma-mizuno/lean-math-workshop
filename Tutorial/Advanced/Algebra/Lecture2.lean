/-
このファイルでは群準同型と性質や、群準同型の核や像等を扱う。
一つの目標は「準同型が単射なことと核が自明なことは同値」である。
*Lecture1で示したことは自由に使える*ので、必要なら使える定理を探しに行こう。

# 目次
- Section 1. 群準同型の定義と基本性質
- Section 2. 群準同型に付随する部分群
- Appendix. Cayleyの定理（群は自己全単射のなす群に埋め込める）
-/
import Tutorial.Advanced.Algebra.Lecture1
namespace Tutorial

section Section1
/-
# 1. 群の準同型
群`G₁`と`G₂`に対して、その準同型とは、写像であって積を保つものをいう。
今までと同じように、underlying mapと、それが写像を保つこと、を束ねてこれを実装する。
-/
structure GroupHom (G₁ G₂ : Type) [Group G₁] [Group G₂] where
  toFun : G₁ → G₂
  map_mul' : ∀ a b : G₁, toFun (a * b) = toFun a * toFun b
  -- 単位元を保つことはここから従う、後で示す

-- `f : G₁ →* G₂`で群準同型を表せるようにする。
infixr:25 " →* " => GroupHom

-- 以下この節では`G₁`と`G₂`を群、`f`をその間の準同型とする。
variable [Group G₁] [Group G₂] {f : G₁ →* G₂}

-- `f`と`a : G₁`に対して、いちいち`f.toFun a`と書く代わりに、`f a`と書くためのおまじない
-- （`f`そのものは、写像`f.toFun`と、それが積を保つという事実`f.map_mul'`を束ねたもので、本来は写像でない）
-- 右側のInfoviewには、`f a`の代わりに`↑f a`と表示されることもあるが、同じなので気にしないでください。
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

#check eq_inv_of_mul_eq_one_left -- これが使えるかも
/-- 群準同型は逆元を保つ。 -/
@[simp]
theorem map_inv {a : G₁} : f (a⁻¹) = (f a)⁻¹ := by
  sorry

/--
2つの群準同型`f₁ : G₁ →* G₂`と`f₂ : G₂ →* G₃`の合成`f₂ ∘ f₁`も準同型。
`f₂.comp f₁`でアクセスできる。 -/
def GroupHom.comp [Group G₁] [Group G₂] [Group G₃]
  (f₂ : G₂ →* G₃) (f₁ : G₁ →* G₂) : G₁ →* G₃ where
  toFun := f₂ ∘ f₁
  map_mul' := by
    -- ヒント: まずは`simp`を試そう
    sorry

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

end Section1


section Section2
/-
# 2. 群準同型に付随する部分群
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

/-- 像に入ることの定義の確認。 -/
@[simp]
theorem mem_range {f : G₁ →* G₂} : b ∈ f.range ↔ ∃ a, f a = b := Iff.rfl

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

-- これは以下のように使える。`⊤`は`\top`で入力し、これはこの部分群が
-- 部分群全体のなす順序集合の最大元なことからくる慣習的記法。
#check (⊤ : Subgroup G)

-- 双対的に、`⊥`(`\bot`)も定義しよう。
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

-- 以下`f`を群準同型`f : G₁ →* G₂`とする。
variable {f : G₁ →* G₂}

-- 「単射と核が自明が同値」の証明で本質的なのは下の主張。
#check mul_inv_eq_one -- これが役立つかも
theorem injective_iff_map_eq_one : Function.Injective f ↔ (∀ a, f a = 1 → a = 1) := by
  constructor
  · sorry
  · sorry 

namespace GroupHom

/-- 群準同型の核が自明なことと単射なことは同値。 -/
theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  -- 上の`injective_iff_map_eq_one`で`rw`してから`constructor`がよい。
  -- （上を使わず直接示すこともできる）
  sorry

/-- 群準同型の像が全体なことと全射なことは同値。 -/
theorem range_eq_top : f.range = ⊤ ↔ Function.Surjective f := by
  constructor
  · intro hrange y
    have hy : y ∈ (⊤ : Subgroup G₂) := by
      sorry
    sorry
  · intro hsurj
    -- ヒント: 2つの部分群が等しいことを示したいので、
    -- `ext a`を使うと、元を取って比較できる。
    sorry

end GroupHom

end Section2


section Appendix
/-
# Appendix: Cayleyの定理
群`G`は`G`上の全単射のなす群に単射で埋め込めることがよく知られている。
とくに有限群は対称群の部分群として実現できる。
これはCayleyの定理と呼ばれる（らしい）。
このAppendiexではそれを見ていく。
このことは今後に関係ないので、*最初は飛ばす*とよい。
-/
open Equiv
/--
`X`上の全単射のなす集合は`Perm X`である。
正確には、`Perm X`の元は写像`toFun`、その逆写像`invFun`、
それが左・右逆写像であることの証明、という組。
`Perm X`に群構造を与えよう。
-/
instance (X : Type) : Group (Perm X) where
  mul f g := Equiv.trans g f
  -- この積`f * g`は、先に`g`、次に`f`という、写像の合成の向き。
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
  -- せっかくなので先程示した単射性の判定法を使おう。
  rw [injective_iff_map_eq_one]
  intro a h
  calc
    a = a * 1 := by simp
    _ = (homToPerm G a) 1 := by
      -- 冷静に考えるとこれは`homToPerm`の定義。
      -- 定義から両辺が等しいときは`rfl` tacticが使える。
      sorry
    _ = 1 := by
      sorry

-- 以上により任意の群`G`に対して、単射準同型`G →* Perm G`が構成できた！

end Appendix

end Tutorial