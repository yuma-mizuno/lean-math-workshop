import Std

/- # 遊び方 -/

-- 証明があるべき場所に`sorry`と書いてあるので...
example : 1 + 1 = 2 := by
  sorry

-- 正しい証明に書き直そう！
example : 1 + 1 = 2 := by
  triv

/- # Leanにおける論理
数学的に意味のある文を**命題**と呼ぶ。例えば、「1 + 1 = 2」「3は偶数である」「リーマン予想」などが
命題である。命題は真である場合もあれば偽である場合もあるし、真偽がわかっていない場合もある。数学の
教科書などでは「命題」という単語は「定理」という単語の別名として使われることもあるが、ここでは違う
意味で使われていることに注意しよう。

`P`が命題であることをLeanでは`P : Prop`と書く。また、`h : P`と書けば`h`が`P`の証明であることを
意味する。別の言い方をすると、`h : P`は`P`が真であり、その事実に`h`と名前を付けているという
こともできる。
-/

/-
Leanで証明を書くためのコマンドを**tactic**と呼ぶ。このファイルでは以下のtacticについて学ぶ

- `apply`
- `intro`
- `constructor`
- `cases`

-/

/- # ならば
Leanでは「ならば」を`→`で表す。例えば「PならばQ」は`P → Q`と書く。記号`→`を出すには`\to`もしくは
`\r`と入力する。VSCode上で`→`の上にカーソルを乗せると入力の仕方が表示される。
-/

-- 以下`P, Q, R`は命題とする。
variable (P Q R : Prop)

example (hP : P) : P := by
  -- ヒント: `apply hP`と入力すれば仮定をゴールに適用できる。
  sorry

example (h : P → Q) (hP : P) : Q := by
  -- 改行して複数のtacticを並べることもできる。インデント（行の頭の空白の個数）を
  -- 揃える必要があることに注意しよう。
  -- ヒント: `apply`を2回使う。
  sorry

example (h : P → Q) (h' : Q → R) : P → R := by
  -- ヒント: `intro hP`と入力すれば仮定`hP : P`が得られる。
  sorry

-- TIPS: 入力した`intro`や`apply`の上にカーソルを乗せるとtacticの説明が表示される。

/- # 否定
否定命題`¬P`は`P → False`として定義される。
-/

example (hP : P) (hP' : ¬P) : False := by
  -- ヒント: 否定命題も`apply`することができる。
  sorry

example : (P → Q) → ¬Q → ¬P := by
  sorry

example : ¬¬¬P → ¬P := by
  sorry

/- # 偽
偽命題`False`からは任意の命題が証明できる。この事実には`False.elim`という名前がついている。
-/

example : False → P := by
  apply False.elim

example (h : ¬P) : P → Q := by 
  sorry

/- # かつ
「PかつQ」は`P ∧ Q`と書かれる。`P ∧ Q`を示したい場合、`constructor`を用いれば右画面に表示される
ゴールが`P`と`Q`のそれぞれを示すふたつのゴールに分岐する。
-/

example (hP : P) (hQ : Q) : P ∧ Q := by
  -- `constructor`によってゴールが分岐する。分岐したゴールたちには名前がついていて、`case`を使って
  -- それぞれのゴールに的を絞ることができる。
  constructor
  case left =>
    sorry
  case right =>
    sorry

example (hP : P) (hQ : Q) : P ∧ Q := by
  -- 別の書き方: `·`を用いた箇条書きでも分岐したでもそれぞれのゴールに的を絞ることができる。
  constructor
  · sorry
  · sorry

/- # かつ
仮定`h : P ∧ Q`を持っているとき、`h.left`で`P`の証明を、`h.right`で`Q`の証明を得ることができる。
-/

example : P ∧ Q → P := by
  sorry

example : P ∧ Q → Q := by
  sorry

example : P ∧ Q → Q ∧ P := by
  sorry

/- # または
「PまたはQ」は`P ∨ Q`と書かれる。仮定`h : P ∨ Q`を持っているとき、`cases h`によって場合分けの証明を行える。
-/

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR
  -- `cases h`によって右画面に新しいゴール`inl`と`inr`が現れる。
  -- (これらの名前はinsert leftとinsert rightの略らしい)
  cases h
  -- `case inl hP`で左側の命題`P`の証明に`hP`という名前を付けている。
  case inl hP => 
    sorry
  case inr hQ => 
    sorry

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR
  -- `rcases`という`cases`の別バージョンがある。ひとつの違いとして、こちらは`case`を使わなくても分岐した
  -- 仮定に名前を付けられる。箇条書きを使いたい人はこちらを使おう。
  rcases h with hP | hQ
  · sorry
  · sorry

example (h : P ∨ Q) : (P → R) → (Q → P) → R := by
  sorry

example : ¬¬P → P := by 
  -- `have` tacticで仮定を追加することができる。以降のファイルではヒントとしても用いる。
  have h : P ∨ ¬P := by apply Classical.em
  sorry

/-
最初のチュートリアルファイル`Lecture1.lean`は以上です。
`Lecture2.lean`に進む前に、証明にエラーがないか確認してみましょう。
VS Codeを使っている場合は、エラーが残っているとその箇所に赤線が表示されます。
-/

/- 以下おまけ。スキップして`Lecture2.lean`に進んでも大丈夫です。 -/

-- 連続して`apply`を使うときは...
example (h : P → Q) (h' : Q → R) : P → R := by
  intro hP
  apply h'
  apply h 
  apply hP

-- このようにまとめることができる。なぜなら`h : P → Q`と`hP : P`に対して`h hP : Q`だからである。
example (h : P → Q) (h' : Q → R) : P → R := by
  intro hP
  apply h'
  apply h hP

-- さらにまとめられる。
example (h : P → Q) (h' : Q → R) : P → R := by
  intro hP
  apply h' (h hP)

-- さらにさらにまとめられて...
example (h : P → Q) (h' : Q → R) : P → R := by
  apply (fun hP ↦ h' (h hP))

-- 実はこのようにも書ける。簡単な証明が短く書けるのは嬉しい。
example (h : P → Q) (h' : Q → R) : P → R :=
  fun hP ↦ h' (h hP)

-- 面白い事実: 文字を変えると、関数の合成に見える！
example (f : P → Q) (g : Q → R) : P → R :=
  fun x ↦ g (f x)

/-
Leanでは「ならば」を`→`で表す。`⇒`は用いない。実は、Lean内部では命題`P → Q`の項は`P`から`Q`への関数として
解釈される。ここではこれ以上説明しないが、この考え方は**Curry–Howard対応**と呼ばれていて、Leanで論理を扱う
際の基礎となっている。
-/
