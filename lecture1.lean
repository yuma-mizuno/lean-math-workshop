import Mathlib.Tactic.Basic


/-- # Leanにおける論理
数学的に意味のある文を*命題*と呼ぶ。例えば、「1 + 1 = 2」「3は偶数である」「リーマン予想」などが命題である。ここでいう「命題」はLaTeXの定理環境などで使う「命題」とは異なる意味で使われていることに注意せよ。特に、命題は真である場合もあれば偽である場合もあるし、真偽がわかっていない場合もある。

`P`が命題であることをLeanでは`P : Prop`と書く。さらに、`h : P`と書けば`h`が`P`の証明であるということを意味する。別の言い方をすると、`h : P`は`P`が真であり、その事実に`h`と名前を付けているということもできる。
-/

/- # ならば
Leanでは「ならば」を`→`で表す。例えば「PならばQ」は`P → Q`と書く。記号`→`を出すには`\to`もしくは`\r`と入力する。VSCode上で`→`の上にカーソルを乗せると入力の仕方が表示される。



-/

/-
Leanではtacticを使って証明を書く。論理記号を扱う基本的なtacticについて

- `intro`
- `apply`


-/

example (P : Prop) (hP : P) : P := by
  -- ヒント: `apply hP`と入力すれば仮定をゴールに適用できる。
  sorry

example (P Q : Prop) (h : P → Q) (hP : P) : Q := by
  sorry

example (P Q R : Prop) (h : P → Q) (h' : Q → R) : P → R := by
  -- ヒント: `intro hP`と入力すれば仮定`hP : P`が得られる。
  sorry


/- # 任意

-/



/- # 否定
否定命題`¬P`は`P → False`として定義される。
-/

example (P : Prop) (h : ¬P) (hP : P) : False := by
  -- ヒント: 否定命題も`apply`することができる。
  sorry

/- # 偽
偽からは任意の命題が証明できる。Leanではこの事実に`False.elim`という名前がついている。
-/

example (P : Prop) : False → P := by
  apply False.elim

example (P Q : Prop) (h : ¬ P) : P → Q := by 
  sorry

/-
Leanではtacticを使って証明を書く。論理記号を扱う基本的なtacticについて

- `constructor`
- `cases`

-/

variable (P Q : Prop)

/- # かつ
「PかつQ」は`P ∧ Q`と書かれる。`P ∧ Q`を示したい場合、`constructor` tacticを用いれば右画面に表示されるゴールが`P`と`Q`のそれぞれを示すふたつのゴールに分岐する。
-/

example (hP : P) (hQ : Q) : P ∧ Q := by
  /- `constructor`によってゴールが分岐する。分岐したゴールたちには名前がついていて、`case`を使ってそれぞれのゴールに的を絞ることができる。
  -/
  constructor
  case left =>
    sorry
  case right =>
    sorry

example (hP : P) (hQ : Q) : P ∧ Q := by
  /- `·`を用いて箇条書きすることでも分岐したそれぞれのゴールに的を絞ることができる。-/  
  constructor
  · sorry
  · sorry

/- # かつ
仮定`h : P ∧ Q`を持っているとき、`h.right`で`P`の証明を、`h.left`で`Q`の証明を得ることができる。
-/

example : P ∧ Q → P := by
  sorry

example : P ∧ Q → Q := by
  sorry

example : P ∧ Q → Q ∧ P := by
  sorry


/- # または


-/

example (P : Prop) (h : P ∨ ¬ P) : ¬¬P → P := by 
  intro hp
  cases h
  case inl h => 
    apply h
  case inr h => 
    apply False.elim
    apply hp
    apply h


/-
なお、上の問題では仮定とした`P ∨ ¬ P`はLeanでは`Classical.em`という名前の定理として用意されている。
-/
example : P ∨ ¬P := by
  apply Classical.em

/-以下メモ-/

example (P : Prop) (h : P ∨ ¬ P) : ¬¬P → P :=
fun hP ↦  h.elim (fun h' ↦ h') (fun h' ↦ (hP h').elim)

open Classical

#check Classical.em

example (P : Prop) : P ∨ ¬P := by
  cases (inferInstance : Decidable P)
  apply Or.inr; assumption
  apply Or.inl; assumption

example (P : Prop) : ¬¬P → P := by
  have : Decidable P := inferInstance
  intro hp
  cases this
  case isTrue h => 
    apply h
  case isFalse h => 
    apply False.elim
    apply hp
    apply h