/-
このファイルでは、群の*正規部分群*やそれによる*商群*、また*準同型定理*について見ていく。

# 目次
- Section 1: 正規部分群と、それによる商群
- Section 2: 群の準同型定理
-/
import Tutorial.Advanced.Algebra.Lecture2
import Tutorial.Advanced.Algebra.Lecture4

namespace Tutorial

section Section1
-- この節では`G`を群とする。
variable [Group G]

namespace Subgroup

/-- 群`G`の正規部分群。`N : Subgroup G`に対し、`[N.Normal]`により`N`が正規部分群なことを表す。-/
class Normal (N : Subgroup G) : Prop where
  /-- 任意の元での共役を取る操作で閉じている。-/
  conj_mem : ∀ a : G, ∀ n ∈ N, a * n * a⁻¹ ∈ N

variable {N : Subgroup G} [N.Normal]

/-- 正規部分群は共役を取る操作で閉じている。-/
theorem conj_mem (a : G) : n ∈ N → a * n * a⁻¹ ∈ N := Normal.conj_mem a n

/-- 積`a * b`が正規部分群に属することと、`b * a`が属することは同値。
あまり有名でなさそうだが有用な補題。-/
theorem mem_comm {a b} : a * b ∈ N → b * a ∈ N := by
  intro hab
  calc
    b * a = a⁻¹ * (a * b) * a⁻¹⁻¹ := by simp
    _ ∈ N := conj_mem a⁻¹ hab

theorem mem_comm_iff (a b : G) : a * b ∈ N ↔ b * a ∈ N :=
  ⟨mem_comm, mem_comm⟩

/- 正規部分群`N`について、左剰余類の集合`G ⧸ N`に群の構造を入れよう。-/
-- `Quotient.map₂'`は、商集合の上の二項演算を定義するときに使えるもの。
instance : Group (G ⧸ N) where
  mul := Quotient.map₂' (fun a b ↦ a * b) <| by -- 積が剰余類上でwell-definedか？
    intro a₁ a₂ ha b₁ b₂ hb
    simp only [LeftQuotient.leftRel_apply] at *
    rw [mul_inv_rev, ← mul_assoc, mem_comm_iff,
      ← mul_assoc, ← mul_assoc, mul_assoc]
    exact N.mul_mem (mem_comm hb) ha
  one := 1 ⋆ N
  inv := LeftQuotient.lift (fun a ↦ a⁻¹ ⋆ N) <| by
    intro a₁ a₂ ha
    simp at *
    replace ha := N.inv_mem ha
    simp at ha
    exact mem_comm ha
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    -- simp
    change (a * b * c) ⋆ N = (a * (b * c)) ⋆ N
    rw [mul_assoc]
  one_mul := by
    rintro ⟨a⟩
    change (1 * a) ⋆ N = a ⋆ N
    simp 

  mul_inv_left := by
    rintro ⟨a⟩
    change (a⁻¹ * a) ⋆ N = 1 ⋆ N
    simp

@[simp]
theorem QuotientGroup.mul_eq (a b : G) : (a ⋆ N) * (b ⋆ N) = (a * b) ⋆ N := rfl

@[simp]
theorem one : (1 : G ⧸ N) = 1 ⋆ N := rfl

@[simp]
theorem mem_of_eq_one {a : G} : a ⋆ N = (1 : G ⧸ N) ↔ a ∈ N := by
  simp
  exact N.inv_mem_iff


end Subgroup

instance [Group G] {H : Subgroup G} : Group H where
  mul := fun a b ↦ ⟨a.1 * b.1, H.mul_mem a.2 b.2⟩
  one := ⟨1, by simp⟩
  inv := fun a ↦ ⟨a.1⁻¹, H.inv_mem a.2⟩
  mul_assoc := by simp [mul_assoc]
  one_mul := by simp
  mul_inv_left := by simp

variable [Group G] {N : Subgroup G} [N.Normal] [Group H] 
/-
G --→ H
|   ↗
v
G⧸N 
-/

/- 商群の普遍性的な。 -/
def GroupHom.lift (f : G →* H) (h : ∀ a ∈ N, f a = 1) : (G ⧸ N) →* H where
  toFun := by
    apply LeftQuotient.lift f
    intro a b hab
    have := h _ hab
    simp at this
    rw [←inv_mul_eq_one]
    exact this
  map_mul' := by
    rintro ⟨a⟩ ⟨b⟩
    simp

end Section1


section Section2
variable [Group G] [Group H]

structure GroupIso (G) [Group G] (H) [Group H] extends G →* H where
  injective : toFun.Injective
  surjective : toFun.Surjective

infixr:25 (priority := high) " ≅* " => GroupIso

instance (f : G →* H) : f.ker.Normal where
  conj_mem := by
    intro a n hn
    simp at *
    rw [hn]
    simp

namespace GroupHom

def restriction (f : G →* H) : G →* f.range where
  toFun := fun a ↦ ⟨f a, by simp⟩
  map_mul' := by
    intro a b
    simp only [map_mul]
    rfl

def rangeKerLift (f : G →* H) : (G ⧸ f.ker) →* f.range :=
  f.restriction.lift <| by
    intro a ha
    ext
    change f a = 1
    rw [ha]

theorem rangeKerLift_injective (f : G →* H) : Function.Injective f.rangeKerLift := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a⟩
  simp
  intro h
  have : f a = 1 := congrArg Subtype.val h
  simp [this]

theorem rangeKerLift_surjective (f : G →* H) : Function.Surjective f.rangeKerLift := by
  intro ⟨y, x, hx⟩
  exists x ⋆ f.ker
  apply Subtype.coe_injective
  simp
  change f x = _
  exact hx

variable (f : G →* H)

def quotientKerIsoRange (f : G →* H) : (G ⧸ f.ker) ≅* f.range where
  toFun := f.rangeKerLift
  map_mul' := by simp
  injective := f.rangeKerLift_injective
  surjective := f.rangeKerLift_surjective

end GroupHom

end Section2

end Tutorial