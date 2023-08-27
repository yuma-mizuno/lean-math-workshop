import Mathlib.Tactic.Linarith

/- # mathlib
mathlibは有志のコミュニテイーによって開発されている数学ライブラリである。
https://leanprover-community.github.io/

mathlibは現在も活発に発展しているライブラリであるが、既に基本的な数学の
かなりの部分をカバーしている。
-/

/- # apply?
現在のゴールに適用可能なmathlibの定理(もしくは定義)を探すtactic
-/

example [Group G] [Group H] (f : G →* H) (a b : G) : 
    f (a * b) = f a * f b := by 
  -- ヒント: `apply?`を使う
  sorry

-- TIPS: 関数の適用は`f (x)`ではなく`f x`と書くことが多い

example [Group G] [Group H] (f : G →* H) (a : G) (n : ℤ) :
    f (a ^ n) = (f a) ^ n := by 
  sorry

example [Group G] (x y : G) : 
    (x * y)⁻¹ = y⁻¹ * x⁻¹ := by
  sorry

-- 環準同型の合成
example [Ring R] [Ring S] [Ring T] (f : R →+* S) (g : S →+* T) : 
    R →+* T := by
  sorry

/- # simp
mathlibの定理を使って式を簡略化するtactic
-/

example [Ring R] [Ring S] (f : R →+* S) (a b c) : 
    f (a + b * c) = f a + f b * f c := by 
  -- ヒント: `simp`を使う
  sorry

/- # ring, linarith, nlinarith
- `ring`: 可換環の等式を証明するtactic
- `linarith`: 線形不等式を証明するtactic
- `nlinarith`: 非線形不等式を証明するtactic
-/

example (x y : ℤ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by 
  ring

example (x : ℤ) (hx : 0 ≤ x) (hy : 3 ≤ y) : 2 < x + y := by
  linarith

example (x : ℤ) (h : 1 < x) : 3 < (x + 1) ^ 2 := by
  nlinarith

example (x y : ℤ) : (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 := by
  sorry

/- # calc 
式変形での証明を直観的に書くための機能
-/

example [CommRing R] (a b c : R) : a * b * c = c * b * a := by
  -- 各式変形では`rw`を用いて式の書き換えを行っている(rwはrewriteの略)
  calc (a * b) * c = c * (a * b)  := by rw [mul_comm (a * b) c]
    _ = c * (b * a)               := by rw [mul_comm a b]
    _ = (c * b) * a               := by rw [mul_assoc]

example (a b c : ℤ) (h₁ : a ≤ b) (h₂ : b = c + 5) : 
    a ≤ c + 5 := by
  -- 等式と不等式をつなげることもできる
  calc a ≤ b       := by apply h₁
       _ = c + 5   := by apply h₂
