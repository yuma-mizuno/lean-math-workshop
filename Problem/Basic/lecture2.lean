import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- `rewrite` `simp`  の導入

example [CommRing R] (a b c : R) : a * b * c = c * b * a := by
  calc (a * b) * c = c * (a * b)  := by rw [mul_comm (a * b) c]
    _ = c * (b * a)               := by rw [mul_comm a b]
    _ = (c * b) * a               := by rw [mul_assoc]

example [Ring R] [Ring S] [Ring T] (f : R →+* S) (g : S →+* T) : R →+* T := by
  exact RingHom.comp g f

example [Group G] (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ := by
  exact mul_inv_rev x y

example [Ring R] [Ring S] (f : R →+* S) (a b c) : 
    f (a + b * c) = f a + f b * f c := by 
  simp

example [Ring R] [Ring S] (f : R →+* S) (a b c) : 
    f (a + b * c) = f a + f b * f c := by 
  simp

set_option trace.linarith true in
example (x : ℤ) : (x + 1) ^ 2 < x ^ 2 + 2 * x + 5 := by
  nlinarith

set_option trace.linarith true in
example (x : ℤ) (h : x > 1) : 3 < (x + 1) ^ 2 := by
  nlinarith

example (x : ℤ) : (x + 1) ^ 2 < x ^ 2 + 2 * x + 5 := by
  calc (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by ring
    _ < x ^ 2 + 2 * x + 5 := by
      refine Int.add_lt_add_left ?h (x ^ 2 + 2 * x)
      linarith