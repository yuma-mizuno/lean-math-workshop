/-
このファイルでは、群`G`の部分群`H`について、
左剰余類`a H`の集合`G ⧸ H`を定義する。
またこれが左`G`集合であることや、任意の空でない推移的`G`集合は、
安定化群を考えることにより`G ⧸ H`という形の`G`集合と同型なことを示す。
（いわゆる*orbit-stabilizer theorem*。）

# 目次
- Section 1: 部分群による左剰余類の集合
- Section 2: 推移的G集合の構造定理
-/
import Tutorial.Advanced.Algebra.Lecture3
namespace Tutorial

section Section1
/-
# 部分群による左剰余類の集合
この節では群`G`とその部分群`H`について、左剰余類のなす集合を`G ⧸ H`として定義する。
また`a : G`の左剰余類を`a ⋆ H : G ⧸ H`で表す（通常での`a H`に対応するもの）。

まず群`G`とその部分群`H`について、同値関係`r`を、`r a b := a⁻¹ * b ∈ H`により定義する。
（これはいわゆる`a H = b H`と同値。）
Leanでは集合`X`上の同値関係や商集合を扱うには`Setoid X`というものを使う。
これは、`r : X → X → Prop`という`X`上の二項関係と、
それが同値関係である、という証明を束ねたものである。
-/
namespace LeftQuotient

/-- 群`G`の部分群`H`について、`a⁻¹ * b ∈ H`であるとき
`a`と`b`が同値であるとした同値関係。 -/
def leftRel {G} [Group G] (H : Subgroup G) : Setoid G where
  r a b := a⁻¹ * b ∈ H
  iseqv := { -- `r`が同値関係なことを示す。
    refl := by -- 反射律
      sorry
    symm := by -- 対称律
      -- ヒント: `H.inv_mem_iff`が使えるかも。
      sorry
    trans := by -- 推移律
      -- ヒント: `H.mul_mem`が使えるかも。
      sorry
  }

/-- 群`G`とその部分群`H`について、左剰余類のなす集合、
つまり`leftRel H`による商集合。 -/
def leftQuotient (G) [Group G] (H : Subgroup G) :=
  Quotient (leftRel H)

-- `G ⧸ H`と書くおまじない。`⧸`は`\quot`か`\/`で入力。
infixl:35 " ⧸ " => leftQuotient 

-- 以下この節では`G`を群、`H`をその部分群とする。
variable [Group G] {H : Subgroup G}

/-- `G`から`G ⧸ H`への自然な全射。 -/
def mk (a : G) : G ⧸ H :=
  Quotient.mk'' a

-- `a : G`に対して、`a ⋆ H`で対応する`G ⧸ H`の元を表そう。
-- `⋆`は`\star`か`\*`で入力。
notation:80 a:80 " ⋆ " H:81 => (mk a : _ ⧸ H)

-- `G ⧸ H`についての、定義から従うことたちをいくつか準備。

@[simp]
theorem leftRel_apply {a b : G} : (leftRel H).r a b ↔ a⁻¹ * b ∈ H := Iff.rfl

theorem eq' {a b : G} : a ⋆ H = b ⋆ H ↔ (leftRel H).r a b :=
  ⟨Quotient.exact, Quotient.sound'⟩

/-- 同値類が等しいことの言い換え。 -/
@[simp]
theorem eq {a b : G} : a ⋆ H = b ⋆ H ↔ a⁻¹ * b ∈ H := 
  eq'.trans leftRel_apply

@[simp]
theorem mk_eq : (Quot.mk _ a : G ⧸ H) = a ⋆ H := rfl

/-- `G`上の写像`f : G → Y`から`G ⧸ H → Y`を作るためのもの。
具体的に写像を作るには、`f`に加えて、
`f`が同値なものを等しいものに送る（well-defined性）
という事実`h`を与える必要がある。
-/
def lift {Y} (f : G → Y)
    (h : ∀ a b : G, a⁻¹ * b ∈ H → f a = f b) : G ⧸ H → Y :=
  Quotient.lift f h

/-- `lift`についての自然な可換性。
誘導される写像の定義より、`lift f h : G ⧸ H → Y`について、
`(lift f h) (a ⋆ H) = f (a)`となる。
-/
@[simp]
theorem lift_mk (f : G → Y) (h) (a : G) : (lift f h) (a ⋆ H) = f a := rfl

/-
`G ⧸ H`には、左`G`集合の構造が、
`a • (x ⋆ H) := (a * x) ⋆ H`で定まる。
これがwell-definedなことと、左作用の公理を満たすことを示そう。
-/
instance : GroupAction G (G ⧸ H) where
  /-`a : G`が与えられたときに、写像`a • (-) : G ⧸ H → G ⧸ H`
  を対応させたい。
  このため、`lift`に、関数`G → G ⧸ H, x ↦ (a * x) ⋆ H`と、
  それが`G ⧸ H`上でwell-definedなことの証明を与える。
  -/
  smul := fun a ↦ lift (fun x ↦ (a * x) ⋆ H) (by
    sorry
  )
  one_smul' := by
    /- これは「任意の`G ⧸ H`の元について◯◯」という形をしている。
    普通に`intro`すると`G ⧸ H`の元を取ることになり面倒だが、
    `rintro ⟨a⟩`とすると、`G`の元`a : G`についての主張に書き換わる。
    -/
    sorry
  mul_smul' := by
    /- ヒント: 上のように`rintro`を適切に使うとよい。
    また、ゴールが定義上`? ⋆ H = ? ⋆ H`という形と同じときは、
    `change _ ⋆ H = _ ⋆ H`とすればゴールが変わる。
    （他にもいろんなやり方があるだろう。）
    -/
    sorry

-- `G ⧸ H`上での`G`作用の定義の確認
@[simp]
theorem smul_mk {a b : G} : a • (b ⋆ H) = (a * b) ⋆ H := rfl

end LeftQuotient

end Section1

section Section2
/-
# 推移的G集合の構造定理
群`G`上の`G`集合`X`が*推移的 (transtiive)* であるとは、
`∀ x y : X, ∃ a : G, a • x = y`となることである。
また、`X`の元`x : X`について、その*安定化群 (stabilizer)*は、
`{ a : G | a • x = x }`という`G`の部分集合で、これは部分群でもある。

`G`集合についての有名な主張に、
「空でない推移的な`G`集合`X`は、その元`x₀ : X`をとると、
`G ⧸ stabilizer x₀`と`G`集合として同型」
というものがある
（推移的`G`集合の構造定理、*orbit-stabilizer theorem*というらしい）。
この節ではこれを示すことを目的とする。
-/

namespace GroupAction
/-- `G`集合`X`が推移的であることを`IsTransitive G X`で表す。 -/
class IsTransitive (G : Type _) (X : Type _) [Group G] [GroupAction G X] : Prop where
  exists_smul_eq : ∀ x y : X, ∃ a : G, a • x = y

-- 以下この節では群`G`を固定する。
variable [Group G]

-- `G ⧸ H`は`G`集合とみて推移的である。
instance {H : Subgroup G} : IsTransitive G (G ⧸ H) where
  exists_smul_eq := by
    -- 任意の`G ⧸ H`の元2つについて◯◯、という主張なので、
    -- `rintro ⟨a⟩ ⟨b⟩`により2つ`G`の元をとってこれる。
    sorry

-- 逆に全ての空でない推移的`G`集合はこの形なことを見ていこう。

/-- `G`集合`X`と`x : X`について、`stabilizer G x`により、
`x`での安定化群を表す。
これは`x`に作用させても変わらない`G`の元からなる`G`の部分群である。
-/
def stabilizer (G) [Group G] {X} [GroupAction G X] (x : X) : Subgroup G where
  carrier := { a : G | a • x = x }
  -- 部分群の公理を満たすことを示そう。
  one_mem' := by
    sorry
  mul_mem' := by
    sorry
  inv_mem' := by
    sorry

-- 以下`X`を`G`集合とする。
variable [GroupAction G X]

/-- `stabilizer`に入ることの定義。 -/
@[simp]
theorem mem_stabilizer_iff {a : G} {x : X} : a ∈ stabilizer G x ↔ a • x = x := Iff.rfl

/-- 推移的`G`集合`X`の元`x₀`が与えられたとき、
`G ⧸ stabilizer G x₀`は`X`と`G`集合として同型で、
その写像は`a`の剰余類を`a • x₀`に対応させることで与えられる。 -/
def leftQuotientStabilizerIsoSelfOfIsTransitive
    [IsTransitive G X] (x₀ : X) : (G ⧸ stabilizer G x₀) ≅[G] X where
  -- `G → X, a ↦ a • x₀`を`G ⧸ stabilizer G x₀`上の写像にリフトさせよう。
  toFun := LeftQuotient.lift (fun a ↦ a • x₀) (by
    -- 写像がwell-definedなことを示す必要がある。
    sorry
  )
  map_smul' := by -- 上の写像が`G`同変なこと。
    -- 「`G ⧸ H`の元について◯◯」がゴールなら、
    -- `rintro ⟨a⟩`とすれば`a : G`についての主張に書き換わる。
    sorry
  injective := by -- 単射性
    sorry
  surjective := by -- 全射性
    -- 今`X`は推移的という仮定があるので、`x y : X`がに対して、
    -- `∃ a : G, a • x = y`という形の主張は、
    -- `apply IsTransitive.exists_smul_eq`で示すことができる。
    sorry

end GroupAction

end Section2

end Tutorial
