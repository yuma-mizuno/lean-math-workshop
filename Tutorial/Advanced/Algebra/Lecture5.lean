/-
このファイルでは、群の*正規部分群*やそれによる*商群*、また*準同型定理*について見ていく。
後半では、準同型定理を述べる前にそもそも、部分群を群だとみなす際の困難や、それを解消する*部分型*についても説明する。
が初見では難しい概念なので上級者向きである。

# 目次
- Section 1: 正規部分群と、それによる商群
- Section 2: 群の準同型定理
-/
import Tutorial.Advanced.Algebra.Lecture2
import Tutorial.Advanced.Algebra.Lecture4

namespace Tutorial

section Section1
-- この節では`G`を群とする。
variable [Group G]

namespace Subgroup

/-- 群`G`の正規部分群。`N : Subgroup G`に対し、`[N.Normal]`により`N`が正規部分群なことを表す。-/
class Normal (N : Subgroup G) : Prop where
  /-- 任意の元での共役を取る操作で閉じている。-/
  conj_mem : ∀ a : G, ∀ n ∈ N, a * n * a⁻¹ ∈ N

variable {N : Subgroup G} [N.Normal]

#check Normal.conj_mem -- この名前で使える。
/-- 積`a * b`が正規部分群に属するなら、`b * a`も属する。
あまり有名でなさそうだが有用な補題。-/
theorem mem_comm {a b} : a * b ∈ N → b * a ∈ N := by
  intro hab
  -- 一度紙で計算してみて、下のように`calc`するとよいかも。
  calc
    b * a = sorry := by sorry
    _ = sorry := by sorry
    _ ∈ N := by
      sorry

theorem mem_comm_iff (a b : G) : a * b ∈ N ↔ b * a ∈ N := ⟨mem_comm, mem_comm⟩

end Subgroup

variable {N : Subgroup G} [N.Normal]

/- 正規部分群`N`について、左剰余類の集合`G ⧸ N`に群の構造を入れよう。-/
-- `Quotient.map₂'`は、商集合の上の二項演算を定義するときに使えるもの。
instance : Group (G ⧸ N) where
  mul := Quotient.map₂' (fun a b ↦ a * b) <| by
    -- 積が剰余類上でwell-definedか？
    -- `mem_comm`や`mem_comm_iff`が役立つかも。
    sorry
  one := 1 ⋆ N
  -- 逆元を取る操作は、`a ↦ a⁻¹ ⋆ N`をliftしよう。
  inv := LeftQuotient.lift (fun a ↦ a⁻¹ ⋆ N) <| by
    -- well-defined性
    sorry
  mul_assoc := by
    -- 結合性。まず代表元を取る。
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    -- 次のように`change`でゴールを見やすくするとよい
    change (a * b * c) ⋆ N = (a * (b * c)) ⋆ N
    -- もしくは`change`のかわりに、`simp`や`dsimp`を使ってもよい
    sorry
  one_mul := by
    rintro ⟨a⟩
    sorry
  mul_inv_left := by
    sorry

@[simp]
theorem QuotientGroup.mul_eq (a b : G) : (a ⋆ N) * (b ⋆ N) = (a * b) ⋆ N := rfl

@[simp]
theorem one : (1 : G ⧸ N) = 1 ⋆ N := rfl

@[simp]
theorem mem_of_eq_one {a : G} : a ⋆ N = (1 : G ⧸ N) ↔ a ∈ N := by
  sorry

variable [Group G] {N : Subgroup G} [N.Normal] [Group H] 

/-- `N`の元を全て潰す群準同型`f : G →* H`があると、それは商群`G ⧸ N`からの準同型 `G ⧸ N →* H`を誘導する。
いわゆる商群の普遍性。 -/
def GroupHom.kerLift (f : G →* H) (h : ∀ a ∈ N, f a = 1) : (G ⧸ N) →* H where
  toFun := LeftQuotient.lift f <| by
    sorry
  map_mul' := by
    -- `rintro ⟨a⟩`等で代表元をとると良い。
    sorry

end Section1


section Section2
-- 以下群`G`と`H`とその間の群準同型`f`を固定。
variable [Group G] [Group H] (f : G →* H)

-- 準同型定理を示すにあたって、まだ群の同型を定義していなかったので定義しよう。
/-- 群の同型。ここでは単射かつ全射な群準同型として定義する。 -/
structure GroupIso (G) [Group G] (H) [Group H] extends G →* H where
  injective : toFun.Injective
  surjective : toFun.Surjective

-- `f : G ≅* H`で群同型が表せるようになるおまじない。
infixr:25 " ≅* " => GroupIso

/-- 群準同型の核は正規部分群である。 -/
instance : f.ker.Normal where
  conj_mem := by
    sorry

/-
さて、以下では`f : G →* H`について、`G ⧸ f.ker ≅* f.range`を示したい。
しかし`f.range`の型は`Subgroup H`であり、（意図的に避けていた）ある問題が生じる。

群`G`の部分群`K : Subgroup G`は、あくまで型が`Subgroup G`であり、そのままでは集合でない（つまり型が`Type`でない）、
よって`f.range`を群だと思うことはできないはずである（群は`Type`上に乗った構造であるので）。
同じ状況は、一般に集合`X : Type`の部分集合`A : Set X`についても成り立つ。なぜなら`A`の型は`Set X`であり、`Type`でないからである。
この状況を解決するため、Leanでは*subtype*という概念が用いられる。

簡単のため`A : Set X`（≒ `A`は`X`の部分集合）の場合を考える。
この場合、実は`A.Elem := { x : X // x ∈ A } : Type`が使用でき、これは`x ∈ A`が成り立つ元からなる集合と思える。
`A.Elem`は、`a : A`と`ha : a ∈ A`によるペアリング`⟨a, ha⟩`という形の項からなる型であり、
逆に`x : A.Elem`について、`x.1 : A`と`x.2 : a ∈ A`が取り出せる。
このような構成`{ x : X // P x }`は型`X`の*部分型 (subtype)*と呼ばれる。
単に`a : A`と書いたときは、`A`が`A.Elem`だと自動的にLeanが判断する。
同じく、単に`A : Type`と書けば自動的にLeanがそれを`A.Elem`だと解釈してくれるので、`A.Elem`等を入力する必要はない。

右側の状況欄には、`↑A : Type`等の`↑`が書かれる場合がある。
この`↑`は*coercion (型強制)*という、ある型を持つ項を自然な同一視により別の型のものだとみなす場合に表れる。
今までに出てきた、群準同型`f : G →* H`を写像だと思う`↑f : G → H`や、`a : ℕ`について`a : ℤ`と書けるのはcoercionの例である。
-/
#check Subtype
#check Set.Elem
example (X : Type) (A : Set X) : (A : Type) = { x : X // x ∈ A } := rfl

/-
さて、この`K : Subgroup G`に対して自動的に`K : Set G`が使えるので、`K : Type`も自動的に使える。
なので、`Group K`という記法が通り、このインスタンスを作ることにより、`K : Subgroup G`について`Group K`、
つまり「`G`の部分群はそれ自身が群となる」という主張が定式化できる。
ただしこの`Group K`の`K`は実際には`K.Elem`のことなので、それに注意して書く必要がある。
-/
namespace Subgroup
variable {K : Subgroup G} -- `K`を`G`の部分群とする
instance : Group K where
  /-
  例えば積を定義するときは、`a : K.Elem`と`b : K.Elem`から`K.Elem`の項を構成する必要がある。
  これには、`a.1 : G`と`b.1 : G`の積をペアの第一成分、
  そしてその積が`K`に属していることの証明を第二成分に与えれば良く、次のように書ける。
  ここで`a.2 : a.1 ∈ K`だった。
  -/
  mul := fun a b ↦ ⟨a.1 * b.1, K.mul_mem a.2 b.2⟩
  -- おそらく慣れないと難しいので全て与える。
  one := ⟨1, by simp⟩
  inv := fun a ↦ ⟨a.1⁻¹, K.inv_mem a.2⟩
  mul_assoc := by simp [mul_assoc]
  one_mul := by simp
  mul_inv_left := by simp

-- 以下で便利ないくつかの`simp`を書いておく。どれも定義から自明。
@[simp]
theorem coe_mul {a b : K} : a * b = ⟨a.1 * b.1, K.mul_mem a.2 b.2⟩ := rfl

@[simp]
theorem coe_one : (1 : K) = ⟨1, by simp⟩ := rfl

@[simp]
theorem ext_iff {a b : K} : a = b ↔ a.1 = b.1 := Subtype.ext_iff

-- よって`f : G →* H`の像`f.range : Subgroup H`も群だと思え、準同型定理を示す準備が整った。
end Subgroup

namespace GroupHom

/-- `f : G →* H`からcodomainを制限して得られる群準同型`f : G →* f.range`のこと。 -/
def rangeRestrict : G →* f.range where
  toFun := fun a ↦ ⟨f a, by simp⟩
  map_mul' := by
    sorry

/-- `rangeRestrict`の定義の確認。 -/
@[simp]
theorem rangeRestrict_apply {a : G} : f.rangeRestrict a = f a := rfl

/-- `f : G →* H`から誘導される`G ⧸ f.ker →* f.range`。つまり準同型定理で同型であることが主張される準同型。 -/
def rangeKerLift : G ⧸ f.ker →* f.range :=
  f.rangeRestrict.kerLift <| by
    sorry

/-- `rangeKerLift`の定義の確認。 -/
@[simp]
theorem rangeKerLift_apply {a : G} : f.rangeKerLift (a ⋆ f.ker) = f a := rfl

#check injective_iff_map_eq_one -- これが便利かも
/-- `f.rangeKerLift`は単射である。 -/
theorem rangeKerLift_injective : Function.Injective f.rangeKerLift := by
  sorry

/-- `f.rangeKerLift`は全射である。 -/
theorem rangeKerLift_surjective : Function.Surjective f.rangeKerLift := by
  -- `f.range.Elem`から元を取るとき、下のようにすると`y : H`が取れ、わかりやすい
  intro ⟨y, hy⟩
  sorry

/-- 群の準同型定理。`G ⧸ f.ker`と`f.range`の間に自然な群同型が誘導される。 -/
-- 全て必要なことは示したので、やることはない。
def quotientKerIsoRange : G ⧸ f.ker ≅* f.range where
  toFun := f.rangeKerLift
  map_mul' := f.rangeKerLift.map_mul'
  injective := f.rangeKerLift_injective
  surjective := f.rangeKerLift_surjective

end GroupHom

end Section2

end Tutorial