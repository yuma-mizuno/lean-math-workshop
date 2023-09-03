import Mathlib.Tactic.Linarith

namespace Tutorial

/- # 存在
命題`∃ x : X, P x`は`P x`を満たす`x : X`が存在することを表す。
-/

example (n : ℤ) : ∃ m : ℤ, n < m := by
  -- 存在命題は`exists` tacticで証明できる
  exists n + 1
  linarith

example (n : ℤ) : ∃ m : ℤ, m < n := by
  exists n-1
  linarith

def Even (n : ℤ) : Prop := ∃ k, n = 2 * k
def Odd  (n : ℤ) : Prop := ∃ k, n = 2 * k + 1

example : Even 4 := by 
  exists 2

example : Odd 11 := by 
  exists 5

/-
存在命題の証明`h : ∃ x : X, P x`が与えられたとき、`have ⟨x, hx⟩ := h`と書くことで
`P x`を満たす`x : X`を仮定に追加できる。`P x`の証明は`hx`という名前で与えられる。
-/

example (m n : ℤ) (hm : Even m) (hn : Even n) : Even (m + n) := by
  have ⟨k₁, hk₁⟩ := hm
  have ⟨k₂, hk₂⟩ := hn
  exists k₁ + k₂
  calc m + n = 2 * k₁ + n := by rw [hk₁] 
    _ = 2 * k₁ + 2 * k₂   := by rw [hk₂]
    _ = 2 * (k₁ + k₂)     := by ring

example (m n : ℤ) (hm : Odd m) (hn : Even n) : Odd (m + n) := by
  have ⟨k₁, hk₁⟩ := hm
  have ⟨k₂, hk₂⟩ := hn
  exists k₁ + k₂
  calc m + n = 2 * k₁ + 1 + n := by rw [hk₁] 
    _ = 2 * k₁ + 1 + 2 * k₂   := by rw [hk₂]
    _ = 2 * (k₁ + k₂) + 1   := by ring

/- # 任意
命題`∀ x : X, P x`は任意の`x : X`について`P x`が成り立つことを表す。
-/

example : ∀ x : ℤ, ∃ y : ℤ, x < y := by
  -- `intro`で全称記号を外せる
  intro x
  exists x + 10000
  linarith

example : ∃ x : ℤ, ∀ y : ℤ, y + y = x * y := by
  exists 2
  intro y 
  ring


end Tutorial
