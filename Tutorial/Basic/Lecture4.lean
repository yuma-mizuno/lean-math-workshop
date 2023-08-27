import Mathlib.Tactic

/- # 単射と全射についての演習問題
このファイルでは、学部数学の集合論の演習問題でよくある、写像の単射と全射についての問題を通して、
`∀`や`∃`についてのより細かい扱いを学ぶ。また、`have`についても復習する。
-/
namespace Tutorial

-- 以下、`X` `Y` `Z`を集合とする。
variable {X Y Z : Type}

/- ## 単射
写像`f : X → Y`が単射であることを`Injective f`で表す。
これは以下のように定義できる。
-/
def Injective (f : X → Y) : Prop :=
  ∀ {x₁ x₂ : X}, f x₁ = f x₂ → x₁ = x₂ 

-- mathlibには既に単射を表す`Function.Injective f`がある。
-- 上の定義はこれと同じである。実用では`Function.Injective f`を使おう。
example : Injective f ↔ Function.Injective f := Iff.rfl

example : Injective (fun x : ℕ ↦ x + 1) := by
  -- ヒント: `rw [Injective]`をすると単射の定義に戻れる
  -- 積極的に`simp`や`apply?`等のチートコマンドを使おう！
  sorry

/-
2つの単射の合成は単射。

おまけ: 下の`g ∘ f`を`f ∘ g`にわざと書き変えてみよう！
人間はこういうミスをよくするが、Leanは「合成できません」とエラーを出してくる。
Leanの便利なところの一つでもある。
-/
theorem Injective.comp {f : X → Y} {g : Y → Z} (hfinj : Injective f) (hginj : Injective g) : 
    Injective (g ∘ f) := by
  rw [Injective]
  intro x₁ x₂ hgf
  -- `hgf : (g ∘ f) x₁ = (g ∘ f) x₂`に対して、`g`が単射だということを使って`f x₁ = f x₂`という事実を導いて使いたい。
  -- 次のように`have`を使おう。
  have hf := hginj hgf
  -- すると `hf: f x₁ = f x₂`が使える。下の補足も参照。
  sorry

/-
*補足*
`hfinj : Injective f`は、「`f x₁ = f x₂`という事実が与えられたら、`x₁ = x₂`という事実を返す関数」と思える。
なので、例えば`hfx : f x₁ = f x₂`があれば、
`hfinj`という関数にそれを代入した`hfinj hfx`は、`x₁ = x₂`という事実になる。

*上級者向け（最初は読み飛ばしてください）*
「`Injective`の定義を見ると`x₁`と`x₂`も与えなきゃ駄目なんじゃ？」と思った方へ。
実は定義では`∀ {x₁ x₂ : X}, ...`と中括弧で囲っており、すると`x₁`と`x₂`は与える必要がなくなる。
与える必要がないのは、その後の`hfx : f x₁ = f x₂`が与えられれば、
`x₁ x₂`が何かはそれから分かってしまうからである。
詳しくは:
https://aconite-ac.github.io/theorem_proving_in_lean4_ja/dependent_type_theory.html#implicit-arguments-%E6%9A%97%E9%BB%99%E3%81%AE%E5%BC%95%E6%95%B0
-/

-- 別解。実は`have`を使わず`apply`のみで上の証明は書ける。
example {f : X → Y} {g : Y → Z} (hfinj : Injective f) (hginj : Injective g) : Injective (g ∘ f) := by
  rw [Injective]
  intro x₁ x₂ hgf
  apply hfinj -- なぜ`apply`でこう書き換わるか考えよう
  sorry

-- 合成して単射なら先の写像は単射
theorem Injective.of_comp {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  intro x₁ x₂ hf
  -- 一つのやり方。`hf: f x₁ = f x₂`があるので、これを`g`で飛ばそう。
  -- 以下のように、`have name : 示したいこと := by`と書ける。
  -- その後のインデントに注意。
  have h : g (f x₁) = g (f x₂) := by
    sorry
  sorry

-- 強いチートコマンドを使った別解
example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  aesop -- 自動でルーチーンな証明をやってくれる強いやつ。
  -- `aesop?`と`?`をつけると、実際に使われた証明が見える。

/-
全体を通したTIPS。
例えば`Injective f`ってどう定義されていたっけ？と気になったときは、
`Injective`のどこかにカーソルを置いて、以下のいずれかの操作
* F12キーを押す
* Ctrl + 左クリック (Windows), ⌘ + 左クリック (Mac)
* 右クリックして`Go to Definition`
を行うと、それが定義されていた場所にジャンプすることができる。
ジャンプしたあとに、元いた場所に戻るときは、
- WindowsならAlt + 左矢印「←」キー
- MacならCtrl + -
で戻れる。VS Codeの便利機能。
-/

/- ## 全射
全射性についても双対命題を示していこう。
-/

-- 写像`f`が全射であることを`Surjective f`で表す。
def Surjective (f : X → Y) := ∀ y : Y, ∃ x : X, f x = y

-- これはmathlibライブラリ既存の`Function.Surjective`と同じ。
-- 実用上は`Function.Surjective`を使おう。
example : Surjective f ↔ Function.Surjective f := Iff.rfl

example : Surjective (fun x : ℤ ↦ x + 1) := by
  -- `apply?`等のチートコマンドを使ってもいいし、
  -- Lecture 3で学んだ`exists`を使ってもいい
  sorry

-- 以下`f`は`X`から`Y`への写像、`g`は`Y`から`Z`の写像とする。
variable {f : X → Y} {g : Y → Z}

-- 全射の合成は全射
theorem Surjective.comp (hfsurj : Surjective f) (hgsurj : Surjective g) : Surjective (g ∘ f) := by
  rw [Surjective]
  intro z
  -- `g`の全射性から、`z : Z`に飛ぶ`y`が取りたい。
  -- これはLecture3で見たように、次で取れる。
  -- 下の補足も参照。
  have ⟨y, hy⟩ := hgsurj z
  sorry

/-
*補足*
`hfsurj : Surjective f`は、「`y : Y`が与えられたら、`∃ x : X, f x = y`という事実を返す関数」だと思える。
なので、`hsurj y`により`∃ x : X, f x = y`という事実が取り出せる。
よって、`have ⟨x, hx⟩ := hsurj y`によって、
`x : X`と、`hx : f x = y`が得られる。
-/

-- 合成して全射なら後ろの写像は全射
theorem Surjective.of_comp (h : Surjective (g ∘ f)) : Surjective g := by
  sorry

end Tutorial

/-  
Basicチュートリアルは以上です。Advancedチュートリアルではより実践的な数学を扱います。
-/