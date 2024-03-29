import Mathlib.Tactic
/-
# Tacticチートシート

このチュートリアルで学んだ、よく使うコマンド集。
以下も参照。
https://github.com/madvorak/lean4-cheatsheet/blob/main/lean-tactics.pdf

## 一般によく使うやつ

- `intro name`
ゴールが`∀ x, ...`や`P → Q`という形をしている場合に、全称記号`∀`を外して任意に元を取ったり、
`P → Q`から仮定`P`を取ってきたりして、その名前を`name`と名付けるtactic。

`name`の部分は*好きな名前*を入れてよいが、例えばゴールが`P → Q`の状態で`intro`する場合、
`intro hP`のように、「`P`が成り立つという仮定（*h*ypothesis）`hP`」のように名付けると分かりやすかったり、
ゴールが`∀ x : X, ...`の場合、`intro`により`X`の元が取ってこれるので、その名前は慣習的に`x`とするのがよいかもしれない。

また`intro name₁ name₂ name₃`のようにまとめて取ってこれる。
ゴールが`∀ x`だったり`P → Q`の形だったらとりあえず`intro`するとよいかも。
-/
example : ∀ x : ℕ, ∀ f : ℕ → ℕ, f x = 0 → 2 * (f x) = 0 := by
  intro x f hf
  -- `x : ℕ, f : ℕ → ℕ, hf : f x = 0 `
  simp_all

/-
- `rw [h]`
`h : x = y`や`h : P ↔ Q`等がローカルコンテキストにあるとき、`rw [h]`で、ゴールの中のすべての`x`を`y`に変える。
「`h`の*左辺*を`h`の*右辺*に置き換える」ことに注意。
逆に右辺を左辺に置き換えたいときは`rw [← h]`のように`←`を前に付けて書く。
またゴールでなくローカルコンテキストの`h' : ...`の`...`を書き換えたいときは、`rw [h] at h'`とする。
全ての箇所で書き換えたいときは`rw [h] at *`とする。

`rw [h₁, ← h₂, h₃]`のようにすると、`h₁`で書き換え、次に`← h₂`で書き換え、次に`h₃`で書き換える。
-/

example (x y : ℕ) (h : x = y) : x + x = x + y := by
  rw [h]

-- 自然数についての命題`P`と`Q`が同値なら、`P (x + 1)`なら`Q (x + 1)`
example (x : ℕ) (P Q : ℕ → Prop) (h : ∀ n, P n ↔ Q n) : P (x + 1) → Q (x + 1) := by
  intro hPx -- `hPx : P (x + 1)`, Goal: `Q (x + 1)`
  rw [← h] -- Goalが`P (x + 1)`に変わる
  apply hPx

/-
- `apply h`
`Q`を示したいとき、`h : P → Q`（`P`ならば`Q`）がローカルコンテキストにあれば、`apply h`によりゴールが`P`に変わる。

また、ゴールが`P`で、`hP : P`がローカルコンテキストにあるときも、`apply hP`で証明が終わる
（この場合のみに使えるtacticとして`exact`があり、`exact hP`で証明を終了する）。

`rw [h]`との違い：
- `rw [h]`は`h`が等号`=`や同値`↔`で結ばれているとき、左辺を右辺に変える（両方向、同値変形）。
- `apply h`は、`h`が`P → Q`というimplicationのとき、ゴールの`Q`を`P`に変える（片方向、同値性は崩れうる）。
-/
example (P Q : Prop) (h : P → Q) (hP : P) : Q := by
  apply h
  apply hP -- `exact hP`でも可

-- `apply h`の`h`に全称記号等が付いていても使える。
example (f : ℕ → ℕ) (hinj : ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂) (x : ℕ) (h : f x = f 0) : x = 0 := by
  apply hinj -- Goal: `f x = f 0`
  exact h

/-
- `have`
途中で「こういうことが今の仮定から分かる、それを後で使いたい（ローカルコンテキストに追加したい）」ときに使う。

使い方：
1. `have name := ...`
単純に今までの仮定を組み合わせて新しいものを作り、それを`name`と名付けてローカルコンテキストに追加する。
`name`を省略して`have := ...`とすると、`this`という名前が自動的に付けられ、名前を考えるのが面倒なときに便利。
-/
example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  have hQ := hPQ hP -- `hQ : Q`
  have hR := hQR hQ -- `hR : R`
  apply hR

/-
2. `have name : (示したいこと) := by`
ある示したいことがあり、それを`by`以降で示していき、`name : (示したいこと)`をローカルコンテキストに追加する。
-/
-- `f : ℕ → ℕ`が足し算を保つとき、`(f 0) + 1 = 1`になる。
example (f : ℕ → ℕ) (h : ∀ x y, f (x + y) = f x + f y) : f 0 + 1 = 1 := by
  -- まず`f 0 = 0`を別で示しておきたい。
  have hf0 : f 0 = 0 := by
    -- インデントに注意。Tabキーを押してインデントを揃えよう。
    have := h 0 0 -- `this : f (0 + 0) = f 0 + f 0`
    simp_all
  -- これで`hf0 : f 0 = 0`が使える
  rw [hf0]

/-
3. `have ⟨x, hx⟩ := h`
`h : ∃ x : X, P x`という状況のとき、条件を満たす`x`を取ってくる。
`x : X`と`hx : P x`がローカルコンテキストに追加される。
-/
-- `x`が偶数のとき`3 * x`も偶数
example (x : ℕ) (hx : ∃ y, x = 2 * y) : ∃ z, 3 * x = 2 * z := by
  have ⟨y, hy⟩ := hx -- `y : ℕ`, `hy : x = 2 * y`
  exists 3 * y
  rw [hy]
  linarith

/-
## 論理関連

- `constructor`
ゴールが`P ↔ Q`だったり、`P ∧ Q`だったりするとき、ゴールを2つに分割できる。
別れたゴールごとに`· `で書くと見やすい（ゴールが1つに絞られる。）
その場合はインデントを揃える（半角空白2文字あける）ことに注意
-/
example (x : ℕ) : x = 0 ↔ x + 1 = 1 := by
  constructor
  · intro hx -- `hx : x = 0`, Goal: `x + 1 = 1`
    rw [hx]
  · simp

/-
- `exists`
ゴールが`∃ x : X, P x`のとき、`x : X`がローカルコンテキストにあれば、`exists x`により、
ゴールが`P x`に変わる（それが自明な場合は証明が終了する）。
つまり「こういう`x`が存在する」を示したいとき、「この`x`を使え」と指示している。
-/
example : ∃ x : ℕ, 3 * x + 1 = 7 := by
  exists 2

/-
- `left`, `right`
ゴールが`P ∨ Q`のとき、`left`により`P`を示すことにゴールが変わる。
-/

/-
## 特定の状況で使うやつ
- `funext`, `ext`
2つの写像`f₁ f₂ : X → Y`について、ゴールが`f₁ = f₂`のとき、これを示すには任意の`x : X`に対して`f₁ x = f₂ x`を示せばよい。
このときに`funext x`とすると、`x : X`がローカルコンテキストに加わり、ゴールが`f₁ x = f₂ x`に変わる。

`ext x`は、似た状況、例えば「2つの部分集合が等しいことを示すには、任意の元`x`について互いに属することが同値を示せばよい」といった形で使える。
-/
example : (fun x : ℕ ↦ x + x) = (fun x ↦ 2 * x) := by
  funext x
  linarith

/-
その他`linarith`, `ring`等については`Basic/Lecture2.lean`を参照せよ。
-/

/-
## チートコマンド
いろんなことをやってくれるすごいやつ。

- `apply?`
もうゴールの道筋が見えていたり、mathlibにありそうなとき、進む・終わらせるコマンドを探して提案してくれる。

- `simp`
読み込んでいるファイルやmathlibで「これは`simp`で使えるよ」とマークされた定理を使い、ゴールをできるだけ簡単な形に書き換える。
ゴールが複雑な形だったりしたときにとりあえず`simp`で簡単な形にできないか試してみるのは常套手段。

`simp at h`で、ローカルコンテキストにある`h`を簡単な形に書き換える。`simp at *`で全てを簡単な形に書き換える。
さらに`simp [h₁]`で、`h₁`というものも書き換えに使っていいよと与える。

`simp?`により使われた定理が分かる。

- `simp_all`
ゴールや仮定すべてをできるだけ簡単にしようとする。
`simp_all?`で使われた定理が分かる。

- `aesop`
`intro`や`simp`などを使って、ルーチーンな証明をやってくれようとする。成功するか失敗するかのどちらか。
成功した場合、`aesop?`で実際の証明に使えるコードを提出してくれる。
-/
