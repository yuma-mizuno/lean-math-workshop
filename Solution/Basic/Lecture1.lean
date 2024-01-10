import Std

/- # ならば
Leanでは「ならば」を`→`で表す。例えば「PならばQ」は`P → Q`と書く。記号`→`を出すには`\to`もしくは
`\r`と入力する。VSCode上で`→`の上にカーソルを乗せると入力の仕方が表示される。
-/

-- 以下`P, Q, R`は命題とする。
variable (P Q R : Prop)

example (hP : P) : P := by
  -- ヒント: `apply hP`と入力すれば仮定をゴールに適用できる。
  apply hP

example (h : P → Q) (hP : P) : Q := by
  -- ヒント: 改行して複数のtacticを並べることもできる。インデント（行の頭の空白の個数）を
  -- 揃える必要があることに注意しよう。
  apply h
  apply hP

example (h : P → Q) (h' : Q → R) : P → R := by
  -- ヒント: `intro hP`と入力すれば仮定`hP : P`が得られる。
  intro hP
  apply h'
  apply h
  apply hP

/- # 否定 -/

example (hP : P) (hP' : ¬P) : False := by
  -- ヒント: 否定命題も`apply`することができる。
  apply hP'
  apply hP

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hQ hP
  apply hQ (hPQ hP)

example : ¬¬¬P → ¬P := by
  intro h hP
  apply h
  intro h'
  apply h' hP

/- # 偽 -/

example : False → P := by
  apply False.elim

example (h : ¬P) : P → Q := by
  intro hP
  apply False.elim
  apply h hP

/- # かつ -/

example (hP : P) (hQ : Q) : P ∧ Q := by
  -- `constructor`によってゴールが分岐する。分岐したゴールたちには名前がついていて、`case`を使ってそれぞれの
  -- ゴールに的を絞ることができる。
  constructor
  case left =>
    apply hP
  case right =>
    apply hQ

example (hP : P) (hQ : Q) : P ∧ Q := by
  -- 別の書き方: `·`を用いた箇条書きでも分岐したでもそれぞれのゴールに的を絞ることができる。
  constructor
  · apply hP
  · apply hQ

/- # かつ -/

example : P ∧ Q → P := by
  intro h
  apply h.left

example : P ∧ Q → Q := by
  intro h
  apply h.right

example : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · apply h.right
  · apply h.left

/- # または -/

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR
  -- `cases h`によって右画面に新しいゴール`inl`と`inr`が現れる。
  -- (これらの名前はinsert leftとinsert rightの略らしい)
  cases h
  -- `case inl hP`で左側の命題`P`の証明に`hP`という名前を付けている。
  case inl hP =>
    apply hPR hP
  case inr hQ =>
    apply hQR hQ

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR
  -- `rcases`という`cases`の別バージョンがある。ひとつの違いとして、こちらは`case`を使わなくても分岐した
  -- 仮定に名前を付けられる。箇条書きを使いたい人はこちらを使おう。
  rcases h with hP | hQ
  · apply hPR hP
  · apply hQR hQ

example (h : P ∨ Q) : (P → R) → (Q → P) → R := by
  intro hPR hQP
  rcases h with hP | hQ
  · apply hPR hP
  · apply hPR (hQP hQ)

example : ¬¬P → P := by
  -- `have` tacticで仮定を追加することができる。以降のファイルではヒントとしても用いる。
  have h : P ∨ ¬P := by apply Classical.em
  rcases h with h | h
  · intro _
    apply h
  · intro h'
    apply False.elim (h' h)
