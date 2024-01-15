import Mathlib.Algebra.Algebra.Hom

namespace Tutorial

/- 圏論では、いわゆる宇宙の扱いが必要である。なのでLeanにおける宇宙の取り扱いに
最初に説明をする。このような基礎付けに興味がないひとは圏の定義まで読み飛ばしても
問題ない。-/

/- # 型の階層
Leanにおいて「`X`が集合である」といいたいときは`X : Type`と書く。これは
「`X`は`Type`の項である」もしくは「`X`の型は`Type`である」という意味である。
集合論的にいえば、`Type`はすべての集合からなる集合であるといえる。しかし、
よく知られているようにすべての集合からなる集合は素朴には存在しないのであった。
では、`Type`の型はなんであろうか？ -/

#check Type

/- 見てわかるように、`Type`の型は`Type 1`である。Leanは可算無限階層の型の列
`Type 0`, `Type 1`, `Type 2`,...を持っていて、`Type`とは実は`Type 0`のことである。
Leanではこのような階層を用意することでパラドックスを回避している。-/

/- 実用上は、型の階層を具体的な自然数を使っていじることをはほとんどない。代わりに
宇宙変数というものを用いる。これは`universe`というキーワードで宣言することができる。
Leanは状況に応じて宇宙変数への割り当てを自動的に行ってくれるため、ユーザーは型の階層
について注意を払う必要がないことが多い。-/

universe u v

/- # 圏 -/

/- 圏の定義は驚くほど単純に記述できる。-/

class Category (C : Type u) where
  Hom : C → C → Type v
  comp : ∀ {a b c : C}, Hom a b → Hom b c → Hom a c
  id : ∀ (a : C), Hom a a
  id_comp : ∀ {a b : C} (f : Hom a b), comp (id a) f = f := by aesop
  comp_id : ∀ {a b : C} (f : Hom a b), comp f (id b) = f := by aesop
  assoc : ∀ {a b c d : C} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp (comp f g) h = comp f (comp g h) := by aesop

/- 以降、`[Category C]`と書くことで集合`C`に圏構造を載せることができる。

定義に関していくつか補足をする。
* 2つの宇宙変数`u, v`を用いている。`Type u`は対象全体の集合の属する階層、`Type v`はHom集合の属する
  階層である。例えばよく現れる「局所小」の設定は`u > v`（典型的には`u = v + 1`）の場合におおよそ対応する。
* `Hom`は`a b : C`に対してHom集合`Hom a b`を定義している。`Hom`の型の`C → C → Type v`は`C → (C → Type v)`
  のことであり、したがって`Hom`の項は「`C`の項に対して`C`から`Type v`への関数を対応させる」関数である。
  `C → C → Type v`は`C × C → Type v`と数学的には等価である。しかしLeanは多くの場合で前者の形を好む。
* 3つの公理の後ろについている`by aesop`はデフォルト引数である。これは、圏を構成する際にユーザーが
  公理の証明を書かなかった場合は`aesop` tacticが実行されることを意味する。圏論では`aesop`が成功する
  ような「自明な証明」が多く、このようなデフォルト引数を用いた自動化が非常に有用である。tacicが失敗した
  場合にはエラーが生じる。このような場合にはユーザーは手動で証明を埋める必要がある。`aseop` tacticに
  関する詳細は https://github.com/JLimperg/aesop を参照せよ。
-/

open Category

/-- `f : Hom a b`と`g : Hom b c`の合成を`f ≫ g`と書く。
このように左から右という順で合成を書くことにする。-/
infixr:80 " ≫ " => Category.comp

/-- `a`における恒等射を`𝟙 a`と書く。 -/
notation "𝟙" => Category.id

/- TIPS: `≫`や`𝟙`などの記号の上にマウスカーソルを記号の上に乗せると、入力方法がわかる。-/

/- TIPS: この時点で上記の圏の定義に現れる公理を確認すると、いま定義した記号を使って表示される。 -/
#check id_comp
#check comp_id
#check assoc

/- 公理の等式をsimp補題に設定しておく -/
attribute [simp] id_comp comp_id assoc

variable {C : Type u} [Category.{u, v} C] {a b c d e : C}

example (f : Hom a b) (g : Hom b c) (h : Hom c d) (i : Hom d e) :
    (f ≫ (𝟙 b ≫ g)) ≫ (h ≫ i) = f ≫ (g ≫ ((𝟙 c ≫ h) ≫ i)) := by
  -- ヒント: `simp`を使えば圏の公理を使って式が簡略化される
  simp

example (f : Hom a b) (g : Hom b a) (h₁ h₂ : Hom b c) (Hgf : g ≫ f = 𝟙 b) (Hfh : f ≫ h₁ = f ≫ h₂) :
    h₁ = h₂ := by
  calc h₁ = 𝟙 b ≫ h₁ := by simp
    _ = (g ≫ f) ≫ h₁ := by rw [Hgf]
    _ = g ≫ (f ≫ h₁) := by simp
    _ = g ≫ (f ≫ h₂) := by rw [Hfh]
    _ = (g ≫ f) ≫ h₂ := by simp
    _ = 𝟙 b ≫ h₂ := by rw [Hgf]
    _ = h₂ := by simp

/- # 圏の例 -/

/-- 型の圏。Leanにおける「集合の圏」である。-/
instance : Category Type where
  Hom X Y := X → Y
  -- 合成の順序が逆であることに注意する
  comp f g := g ∘ f
  id X := id
  /- 公理の証明を書いていないにもかかわらずエラーが出ていないのはデフォルト引数の`aesop`が成功して
  いることを意味する -/

/- TIPS: `pp.universes`オプションによって、宇宙を明示させることができる。-/
set_option pp.universes true in
#check inferInstanceAs (Category Type)
/- 先ほど型の圏を定義した際には圏の宇宙を明示していなかったにも関わらず、Leanが
`u = 1`, `v = 0`という宇宙変数の割り当てを行っていることがわかる。このように、
具体的な数学的対象を扱う際にはユーザーは宇宙の大きさを気にしなくてもよいことが多い。 -/

@[simp]
theorem comp_app {X Y Z : Type} (f : Hom X Y) (g : Hom Y Z) (x : X) : (f ≫ g) x = g (f x) := by
  rfl

@[simp]
theorem id_app (X : Type) (x : X) : 𝟙 X x = x := by
  rfl

/-- 可換環の圏 -/
structure CommRingCat where
  /- 環は、底集合とその上の環構造から成る。-/
  base : Type
  /- mathlibでは型`R`上の環構造の型を`CommRing R`で表す（なので圏そのものを`CommRing`と書けない...）-/
  str : CommRing base

/- おまじない。`R : CommRingCat`に対して`a : R`と書けるようになる。 -/
instance : CoeSort CommRingCat Type := ⟨fun R ↦ R.base⟩
/- おまじない。`R : CommRingCat`に対しては`R.base`上の環構造として`R.str`を用いる。 -/
instance (R : CommRingCat) : CommRing R.base := R.str

/- `CommRingCat`が実際に圏となることをみてみよう。-/

instance : Category CommRingCat where
  -- 射は環準同型
  Hom R S := RingHom R S
  -- 合成と恒等射を与える
  comp f g := RingHom.comp g f
  id R := RingHom.id R

/- 次は可換環`R`に対して`R`上の可換代数の圏を定義する。-/

/-- `R`上の可換代数の圏 -/
structure CommAlgCat (R : CommRingCat) where
  -- 底集合
  base : Type
  -- 底集合上の可換環の構造
  ringStr : CommRing base
  -- 底集合上の`R`代数の構造
  algStr : Algebra R base

variable {R : CommRingCat}

/- おまじない -/
instance : CoeSort (CommAlgCat R) Type := ⟨fun M ↦ M.base⟩
instance {M : CommAlgCat R} : CommRing M := M.ringStr
instance {M : CommAlgCat R} : Algebra R M := M.algStr

@[simps]
instance {R : CommRingCat} : Category (CommAlgCat R) where
  Hom A B := AlgHom R A B
  comp f g := AlgHom.comp g f
  id A := AlgHom.id R A

/- 定義の上の`@[simps]`はおまじないで、ここでは特に意味がない。`Lecture 2`で役に立つ。 -/

-- おまじない。`Lecture 2`で役に立つ。
instance {A B : CommAlgCat R} : AlgHomClass (Hom A B) R A B :=
  inferInstanceAs <| AlgHomClass (A →ₐ[R] B) R A B

end Tutorial
