import Mathlib.Tactic
/-
# Tacticチートシート

このチュートリアルで学んだ、よく使うコマンド集。
以下も参照。
https://github.com/madvorak/lean4-cheatsheet/blob/main/lean-tactics.pdf

## 一般によく使うやつ

- `intro name`
全称記号∀を外して任意に元を取ったり、`P → Q`から仮定`P`を取ってきたりする。 
`intro name₁ name₂ name₃`のようにまとめて取ってこれる。
ゴールが`∀ x`だったり`P → Q`の形だったらとりあえず`intro`するとよいかも。
-/
example : ∀ x : ℕ, ∀ f : ℕ → ℕ, f x = 0 → 2 * (f x) = 0 := by 
  intro x f hf
  -- `x : ℕ, f : ℕ → ℕ, hf : f x = 0 `
  simp_all

/-
- `rw [h]`
ゴールを`h : x = y`や`h : P ↔ Q`等があるとき、`rw [h]`で、ゴールの中のすべての`x`を`y`に変える。
「`h`の左辺を`h`の右辺に置き換える」ことに注意。
逆に置き換えたいときは`y`を`x`に変えたいときは`rw [← h]`を使う。
またゴールでなく`h'`を書き換えたいときは、`rw [h] at h'`とする。
全てを書き換えたいときは`rw [h] at *`とする。

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
`Q`を示したいとき、`h : P → Q`（`P`ならば`Q`）があれば、`apply h`によりゴールが`P`に変わる。
また、ゴールが`P`で、`hP : P`があるとき、`apply hP`で証明が終わる。

`rw [h]`との違い：
- `rw [h]`は`h`が等号`=`や同値`↔`で結ばれているとき、左辺を右辺に変える（両方向、同値変形）。
- `apply h`は、`h`が`P → Q`というimplicationのとき、ゴールの`Q`を`P`に変える（片方向、同値性は崩れうる）。
-/
example (P Q : Prop) (h : P → Q) (hP : P) : Q := by
  apply h
  apply hP


-- `h`に全称記号等が付いていても使える。
example (f : ℕ → ℕ) (hinj : ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂) (x : ℕ) (h : f x = f 0) : x = 0 := by
  apply hinj -- Goal: `f x = f 0`
  apply h

/-
- `have`
途中で「こういうことが今の仮定から分かる、それを後で使いたい」ときに使う。

使い方：
1. `have name := ...`
単純に今までの仮定を組み合わせて新しいものを作れるとき。
-/
example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  have hQ := hPQ hP -- `hQ : Q`
  have hR := hQR hQ -- `hR : R`
  apply hR

/-
2. `have name : (示したいこと) := by`
ある示したいことがあり、それを示していくとき。
-/
-- `f : ℕ → ℕ`が足し算を保つとき、`(f 0) + 1 = 1`になる。
example (f : ℕ → ℕ) (h : ∀ x y, f (x + y) = f x + f y) : f 0 + 1 = 1 := by
  -- まず`f 0 = 0`を別で示しておきたい。
  have hf0 : f 0 = 0 := by
    -- インデントに注意。Tabキーを押してインデントを揃えよう。
    have h' := h 0 0 -- `h' : f (0 + 0) = f 0 + f 0`
    simp_all
  -- これで`hf0 : f 0 = 0`が使える
  rw [hf0]

/-
3. `have ⟨x, hx⟩ := h`
`h : ∃ x : X, P x`という状況のとき、条件を満たす`x`を取ってくる。
`x : X`と`hx : P x`が使える。
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
  · intro hx
    simp_all

/-
- `exists`
ゴールが`∃ x : X, P x`のとき、`x : X`がすでにあれば、`exists x`により、
ゴールが`P x`に変わる。
つまり「こういう`x`が存在する」を示したいので、「この`x`を使え」と指示している。
-/
example : ∃ x : ℕ, 3 * x + 1 = 7 := by
  exists 2

/-
- `left`, `right`
ゴールが`P ∨ Q`のとき、`left`により`P`を示すことにゴールが変わる。
-/

/-
## チートコマンド
いろんなことをやってくれるすごいやつ。

- `apply?`
もうゴールの道筋が見えていたり、mathlibにありそうなとき、進む・終わらせるコマンドを探して提案してくれる。

- `simp`
ゴールを（Leanとmathlibの定理を使い）できるだけ簡単な形に書き換える。
`simp at h`で、`h`を簡単な形に書き換える。`simp at *`で全てを簡単な形に書き換える。
さらに`simp [h₁]`で、`h₁`というものも書き換えに使っていいよと与える。
`simp?`により使われた定理が分かる。

- `simp_all`
ゴールや仮定すべてをできるだけ簡単にしようとする。
`simp_all?`で使われた定理が分かる。

- `aesop`
ルーチーンな証明をやってくれようとする。成功するか失敗するかのどちらか。
成功した場合、`aesop?`で実際の証明に使えるコードを提出してくれる。
-/
