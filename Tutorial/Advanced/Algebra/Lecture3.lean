/-
このファイルでは群の集合への作用やその間の同変写像についてみる。
一つの目標は、群`G`と`G`集合`X`に対して、
`G →[G] X`（`G`自身を`G`集合と見たときの`G`から`X`への同変写像の集合）と
`X`との間に自然な全単射があることを示すことである。

# 目次
- Section 1. `G`集合の定義・基本性質
- Section 2. `G`集合の同変写像
- Appendix. `G`集合の軌道についての練習問題
-/
import Solution.Advanced.Algebra.Lecture1
namespace Tutorial
attribute [-instance] Mul.toSMul

section Section1
/-
# G集合の定義・基本性質
集合`X`に対する群`G`の左作用とは、作用写像
`G × X → X, (a, x) ↦ a • x`が与えられており、次の公理が満たされるとき。
1. `∀ x : X, 1 • x = x`
2. `∀ a b : G, x : X, (a * b) • x = a • (b • x)`
簡単のため、このとき`X`を**左`G`集合**と呼ぶことにする。

左`G`集合は次のように定式化できる。
Leanでは`G × X → X`という形よりも、`G → X → X`によって、
「`G`の元が与えられたら「`X`から`X`への写像」を返す写像」で
作用写像を表すことに注意。
-/
class GroupAction (G : Type) [Group G] (X : Type) where
  smul : G → X → X
  one_smul' : ∀ x, smul 1 x = x
  mul_smul' : ∀ a b x, smul (a * b) x = smul a (smul b x)

-- 作用を`a • x`で書くためのおまじない。`•`は`\smul`で入力。
infixr:73 " • " => GroupAction.smul

-- 以下この節では、`G`を群、`X`を左`G`集合とする。
variable [Group G] [GroupAction G X]

-- 定義からすぐ従うことをいくつか
@[simp]
theorem one_smul (x : X) : (1 : G) • x = x := GroupAction.one_smul' x
-- 注意: 単純に`1 • x`と書いてしまうと、`1`は自然数だと解釈されエラーが出る。
-- そのため、`G`の`1`なことを表すために、はっきりと`1 : G`と書いている。

theorem mul_smul (a b : G) (x : X) : (a * b) • x = a • b • x := GroupAction.mul_smul' a b x

theorem smul_smul (a b : G) (x : X) : a • b • x = (a * b) • x := (mul_smul a b x).symm

-- いくつかの`simp`を追加
@[simp]
theorem inv_smul_smul {a : G} {x : X} : a⁻¹ • a • x = x := by
  sorry

@[simp]
theorem smul_inv_smul {a : G} {x : X} : a • a⁻¹ • x = x := by
  sorry

/-- `G`集合に対して左から`a : G`を当てる写像は単射。 -/
theorem GroupAction.injective (a : G) : Function.Injective fun (x : X) ↦ a • x := by
  intro x y (h : a • x = a • y)
  -- `calc`を使うとよいかも？
  sorry

-- 上の言い換え、きっといつか使うときに便利。
/-- `G`集合に対して、`a : G`を当てて等しいならもともと等しい。 -/
theorem smul_cancel (a : G) {x y : X} (h : a • x = a • y) : x = y :=
  GroupAction.injective a h

/-- 左から`a : G`を当てる写像は全射。 -/
theorem GroupAction.surjective (a : G) : Function.Surjective fun (x : X) ↦ a • x := by
  sorry

-- もっと強く、`a • (-)`という写像は自然な逆写像を持つ`X`から`X`への全単射である。
-- `X`から`X`への全単射とその逆写像の組の集合は`X ≃ X`と表す。
def GroupAction.toPerm : G → (X ≃ X) := fun (a : G) ↦ {
  toFun := fun x ↦ a • x
  -- この写像の逆写像は何であろうか？
  invFun := sorry
  -- これらが互いに逆写像なことを示す必要がある。
  left_inv := by
    sorry
  right_inv := by
    sorry
}

-- 群`G`自体も左から元を当てることで、自然に左`G`集合になる。
instance : GroupAction G G where
  smul := fun a x ↦ a * x
  one_smul' := by
    sorry
  mul_smul' := by
    sorry

/-- `G`集合`G`での`•`の定義の確認。 -/
@[simp]
theorem smul_eq_mul (a x : G) : a • x = a * x := rfl

end Section1


section Section2
/-
# G集合の同変写像
群`G`に対して、二つの`G`集合`X`と`Y`があったとき、
`G`同変な写像`f : X →[G] Y`とは、写像であって、
`G`作用と可換、つまり`f (a • x) = a • f x`が成り立つときをいう。
これを定式化して、性質を示していこう。
-/

/-- `G`集合の間の同変写像。 -/
structure GroupActionHom
    (G) [Group G] (X) [GroupAction G X] (Y) [GroupAction G Y] where
  toFun : X → Y -- underlying function
  map_smul' : ∀ (a : G) (x : X), toFun (a • x) = a • toFun x

-- `X →[G] Y`と書くためのおまじない。
notation:25 X " →[" G:25 "] " Y:0 => GroupActionHom G X Y

-- この節では以下`G`を群、`X Y Z`を左`G`集合とする。
variable [Group G] [GroupAction G X] [GroupAction G Y] [GroupAction G Z]

-- `f : X →[G] Y`に対して`f x`のように書くためのおまじない。
instance : DFunLike (GroupActionHom G X Y) X (fun _ ↦ Y) where
  coe f := f.toFun
  coe_injective' f₁ f₂ _ := by cases f₁; cases f₂; congr

/-- underlying functionが`f`の同変写像を単なる写像とみなしたものは`f`と等しい。 -/
-- 当たり前の事実だがsimpで使えるようにしておくと便利なのでそうしておく。
@[simp]
theorem GroupActionHom.coe_coe (f : X → Y) (h) : ((⟨f, h⟩ : X →[G] Y) : X → Y) = f :=
  rfl

-- 定義からすぐ分かること
@[ext]
theorem GroupActionHom.ext {f₁ f₂ : X →[G] Y} : (∀ x, f₁ x = f₂ x) → f₁ = f₂ :=
  DFunLike.ext f₁ f₂

theorem map_smul (f : X →[G] Y) : ∀ (a : G) (x : X), f (a • x) = a • f x := f.map_smul'

/-- 2つの同変写像の合成はまた同変写像。 -/
def GroupActionHom.comp (f₁ : X →[G] Y) (f₂ : Y →[G] Z) : X →[G] Z where
  toFun := f₂ ∘ f₁
  map_smul' := by
    sorry

-- ついでに`G`集合の同型も定義しよう。

/-- `G`集合`X`と`Y`の間の`G`集合としての同型、
つまり単射かつ全射な同変写像。 -/
structure GroupActionIso (G X Y) [Group G] [GroupAction G X] [GroupAction G Y]
    extends X →[G] Y where
  injective : toFun.Injective
  surjective : toFun.Surjective

notation:25 X " ≅[" G:25 "] " Y:0 => GroupActionIso G X Y

-- 以下の定理により、逆写像が同変なことは自動的である。
/-- 同変写像`f`に逆写像`g`があったら、`g`も同変写像。 -/
def GroupActionHom.inverse (f : X →[G] Y)
    (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : Y →[G] X where
  toFun := g
  map_smul' := by
    /- ヒント
    `f`の単射性が`h₁.injective`で取り出せるので、それを使うと分かりやすいか。
    もしくは、`rw [Function.LeftInverse] at h₁`で定義を確認して、
    それを利用して直接`calc`で等式を示すこともできる。
    -/
    sorry

/-
最後に、`G`集合`X`について、`G`自身から`X`への同変写像の集合は、
`X`と自然に全単射がある、つまりいわゆる`Hom_G (G, X) ≃ X`を示そう。
（環`R`上の加群`M`についての`Hom_R (R, M) ≃ M`の`G`集合バージョン。）
対応は、`f : G →[G] X`について`f 1 : X`を対応させ、
`x : X`に対しては`G → X, a ↦ a • x`を対応させる。
-/
def yoneda : (G →[G] X) ≃ X where
  -- `(G →[G] X) → X`
  toFun := fun f ↦ f 1
  -- `X → (G →[G] X)`
  invFun := fun x ↦ {
    toFun := fun a ↦ a • x
    map_smul' := by -- `G`同変なことを示す必要がある。
      sorry
  }
  -- これらが互いに逆写像なこと。
  left_inv := by
    /- ヒント
    ごちゃついているが、写像が等しいことを示すには、
    元を代入して等しいかをみればいい、つまり`ext a`を使おう。
    またゴールが定義上「`c = d`」に等しいときは、
    `change c = d`でゴールをその形に変えられる。
    -/
    sorry
  right_inv := by
    sorry

end Section2


section Appendix
/-
# Appendix: 群の作用による軌道
群`G`上の`G`集合`X`について、`G`の元の作用で移り合うという関係は同値関係となる。
この同値類を軌道と呼ぶ。
以下では、この軌道についての基本的な性質を示す。
このことは今後に関係ないので、*最初は飛ばす*とよい。

`X`上の同値関係やその商を表すのに、Leanでは`Setoid X`を使う。
-/
/-- `G`集合`X`上の、`G`の元で移り合うという同値関係。 -/
def orbitRel (G) [Group G] (X) [GroupAction G X] : Setoid X where
  -- `r : X → X → Prop`という`X`上の二項関係を次で定める。
  r x y := ∃ a : G, a • x = y
  iseqv := { -- この`r`が同値関係なこと。
    refl := by -- 反射律
      sorry
    symm := by -- 対称律
      sorry
    trans := by -- 推移律
      sorry
  }

-- 一方で`x : X`の軌道というものも考えられる。
def orbit (G) {X} [Group G] [GroupAction G X] (x : X) :=
  { y : X | ∃ a : G, a • x = y }

variable [Group G] [GroupAction G X]

/-- 軌道が等しいことと、片方が軌道に含まれることは同値。 -/
theorem orbit_eq_orbit_iff_mem_orbit {x y : X} : orbit G x = orbit G y ↔ y ∈ orbit G x := by
  sorry

end Appendix

end Tutorial
