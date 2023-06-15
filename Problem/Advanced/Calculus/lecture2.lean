import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Lattice

noncomputable
section

example : (1 : ℝ) = Real.ofCauchy (Quotient.mk CauSeq.equiv (CauSeq.const abs 1)) := 
  Real.ofCauchy_one.symm



def «0.9999999» : CauSeq ℚ abs where
  val n := 1 - (10 ^ n : ℚ)⁻¹
  property := by
    intro ε ε0
    simp only [sub_sub_sub_cancel_left]
    have ⟨i, hi⟩ : ∃ i : ℕ, (ε / 2)⁻¹ < 10 ^ i := pow_unbounded_of_one_lt (ε / 2)⁻¹ (by linarith)
    have hi : 2 * (10 ^ i : ℚ)⁻¹ < ε := (lt_div_iff' (by linarith)).mp (inv_lt_of_inv_lt (half_pos ε0) hi)
    exists i
    intro j hj
    calc |(10 ^ i : ℚ)⁻¹ - (10 ^ j : ℚ)⁻¹|
      _ ≤ |(10 ^ i : ℚ)⁻¹| + |(10 ^ j : ℚ)⁻¹| := by apply abs_sub
      _ ≤ |(10 ^ i : ℚ)⁻¹| + |(10 ^ i : ℚ)⁻¹| := by simpa [abs] using inv_pow_le_inv_pow_of_le (by linarith) hj
      _ = 2 * (10 ^ i : ℚ)⁻¹                  := by simp [abs]; ring
      _ < ε                                   := hi
      

theorem «1 = 0.9999999» : (1 : ℝ) = Real.ofCauchy (Quotient.mk CauSeq.equiv «0.9999999») := by
  calc (1 : ℝ) = Real.ofCauchy (Quotient.mk CauSeq.equiv (CauSeq.const abs 1)) := Real.ofCauchy_one.symm
    _= Real.ofCauchy (Quotient.mk CauSeq.equiv «0.9999999») := by
      rw [«0.9999999»]
      congr 1
      apply Quotient.sound
      intro ε ε0
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ε⁻¹ < 10 ^ n := pow_unbounded_of_one_lt ε⁻¹ rfl
      have : (10 ^ n : ℚ)⁻¹ < ε := inv_lt_of_inv_lt ε0 hn
      exists n
      intro h hj
      simp [abs]
      calc (10 ^ h : ℚ )⁻¹ ≤ (10 ^ n : ℚ)⁻¹ := inv_pow_le_inv_pow_of_le (by linarith) hj
        _ < ε := this

-- def nested_interval  (a b c : ℝ) (hab : a < c) (hbc : c < b) 
--     {U: ι → Set ℝ} {hU : ∀ (i : ι), IsOpen (U i)} {cover : Icc a b ⊆ ⋃ (i : ι), U i} 
--       (h : ∀ (t : Finset ι), ¬Icc a b ⊆ ⋃ i ∈ t, U i) : 
--     (∀ (t : Finset ι), ¬Icc a c ⊆ ⋃ i ∈ t, U i) ∨ ∀ (t : Finset ι), ¬Icc c b ⊆ ⋃ i ∈ t, U i := by
--   sorry

open Set (Icc) 
open Classical

example (a b : ℝ) : IsCompact (Icc a b) := by
  exact isCompact_Icc

structure Cover where
  ι : Type
  opens : ι → Set ℝ
  Icc_subset_union : Icc a b ⊆ ⋃ (i : ι), opens i

def ExistsFinCover (s : Set ℝ) {ι : Type} (U : ι → Set ℝ) := 
  ∃ (t : Finset ι), s ⊆ ⋃ i ∈ t, U i

lemma nested_interval_aux (a b c : ℝ) (hab : a < c) (hcb : c < b) 
    (U: ι → Set ℝ) (hac' : ∃ (t : Finset ι), Icc a c ⊆ ⋃ i ∈ t, U i) 
      (hcb' : ∃ (t : Finset ι), Icc c b ⊆ ⋃ i ∈ t, U i) :
        ∃ (t : Finset ι), Icc a b ⊆ ⋃ i ∈ t, U i := by
  rcases hac' with ⟨ι_ac, cover_ac⟩
  rcases hcb' with ⟨ι_cb, cover_cb⟩
  exists ι_ac ∪ ι_cb
  intro x hx
  suffices ∃ i, (i ∈ ι_ac ∨ i ∈ ι_cb) ∧ x ∈ U i by
    simpa using this
  cases le_total x c
  case inl hxc =>
    obtain ⟨i, hi⟩ : ∃ i, i ∈ ι_ac ∧ x ∈ U i := by simpa using cover_ac ⟨hx.left, hxc⟩
    exact ⟨i, Or.inl hi.1, hi.2⟩
  case inr hxc =>
    obtain ⟨i, hi⟩ : ∃ i, i ∈ ι_cb ∧ x ∈ U i := by simpa using cover_cb ⟨hxc, hx.right⟩
    exact ⟨i, Or.inr hi.1, hi.2⟩

example (P Q R : Prop) : (P ∧ Q → R) → ¬R → (¬P ∨ ¬Q) := by 
  intro h
  contrapose!
  exact fun a => h a

lemma nested_interval_aux' (a b c : ℝ) (hac : a < c) (hcb : c < b) 
    {U: ι → Set ℝ}
      (h : ¬ExistsFinCover (Icc a b) U) : 
       (ExistsFinCover (Icc a c) U) → ¬ExistsFinCover (Icc c b) U := by
  revert h
  contrapose!
  intro H
  apply nested_interval_aux a b c hac hcb
  apply H.1
  apply H.2

lemma nested_interval_aux'' (a b : ℝ) (hac : a < b) 
    {U: ι → Set ℝ}
      (h : ¬ExistsFinCover (Icc a b) U) : 
       (ExistsFinCover (Icc a ((a + b) / 2)) U) → ¬ExistsFinCover (Icc ((a + b) / 2) b) U := 
  nested_interval_aux' a b ((a + b) / 2) (by linarith) (by linarith) h

def NestedIntervalSucc (a b : ℝ) {ι : Type} (U : ι → Set ℝ) : ℝ × ℝ :=
  if ¬ExistsFinCover (Icc a ((a + b) / 2)) U then ⟨a, (a + b) / 2⟩ else ⟨(a + b) / 2, b⟩

def NestedInterval (a b : ℝ) {ι : Type} (U : ι → Set ℝ) : ℕ → ℝ × ℝ 
  | 0 => ⟨a, b⟩
  | n + 1 => NestedIntervalSucc (NestedInterval a b U n).1 (NestedInterval a b U n).2 U

variable (a b : ℝ) (hab : a < b)
  {ι : Type} {U: ι → Set ℝ} (hU : ∀ (i : ι), IsOpen (U i)) (cover : Icc a b ⊆ ⋃ (i : ι), U i)

lemma nestedIntervalSucc_left (h : ¬ExistsFinCover (Icc a ((a + b) / 2)) U) : 
    NestedIntervalSucc a b U = ⟨a, (a + b) / 2⟩ := 
  if_pos h
  
lemma nestedIntervalSucc_right (h : ExistsFinCover (Icc a ((a + b) / 2)) U) : 
    NestedIntervalSucc a b U = ⟨(a + b) / 2, b⟩ := 
  if_neg (not_not_intro h)

variable  (h : ¬∃ (t : Finset ι), Icc a b ⊆ ⋃ i ∈ t, U i)


variable {a b}
variable (U)

theorem nested_interval_left_le_right : 
    ∀ n, (NestedInterval a b U n).1 < (NestedInterval a b U n).2 
  | 0 => hab
  | n + 1 => by
    by_cases H : ExistsFinCover (Icc (NestedInterval a b U n).1 (((NestedInterval a b U n).1 + (NestedInterval a b U n).2) / 2)) U
    case neg => 
      rw [NestedInterval]
      rw [nestedIntervalSucc_left _ _ H]
      dsimp only
      linarith [nested_interval_left_le_right n]
    case pos =>
      rw [NestedInterval]
      rw [nestedIntervalSucc_right _ _ H]
      dsimp only
      linarith [nested_interval_left_le_right n]



theorem nested_inverval_seq_aux : ∀ n : ℕ, ∃ x : ℝ, x ∈ Icc (NestedInterval a b U n).1 (NestedInterval a b U n).2 := by
  -- choose using nested_interval_left_le_right a b hab
  intro n
  have := nested_interval_left_le_right hab U n
  exists ((NestedInterval a b U n).1 + (NestedInterval a b U n).2) / 2
  simp only [ge_iff_le, not_le, gt_iff_lt, Set.mem_Icc]
  constructor <;> linarith

def NestedIntervalSeq (a b : ℝ) {ι : Type} (U : ι → Set ℝ) : ℕ → ℝ := 
  fun n => ((NestedInterval a b U n).1 + (NestedInterval a b U n).2) / 2

theorem NestedIntervalSeq_mem (hab : a < b) (n : ℕ) : 
    NestedIntervalSeq a b U n ∈ Icc (NestedInterval a b U n).1 (NestedInterval a b U n).2 := by
  have := nested_interval_left_le_right hab U n
  simp only [ge_iff_le, not_le, gt_iff_lt, Set.mem_Icc, NestedIntervalSeq]
  constructor <;> linarith

theorem NestedIntervalSeq_mem' (hab : a < b) (i j : ℕ) (hij : i ≤ j): 
    NestedIntervalSeq a b U j ∈ Icc (NestedInterval a b U i).1 (NestedInterval a b U i).2 := by
  have := nested_interval_left_le_right hab U i
  simp only [ge_iff_le, not_le, gt_iff_lt, Set.mem_Icc, NestedIntervalSeq]
  sorry

theorem nested_inverval_seq : ∃ s : ℕ → ℝ, ∀ n : ℕ, s n ∈ Icc (NestedInterval a b U n).1 (NestedInterval a b U n).2 := by
  choose s hs using (nested_inverval_seq_aux hab U)
  exact ⟨s, hs⟩
      
theorem nested_interval_ne_exists_fin_cover (a b : ℝ) (hab : a < b) (U: ι → Set ℝ) 
    (h : ¬ExistsFinCover (Icc a b) U) : ∀ n : ℕ,
    ¬ExistsFinCover (Icc (NestedInterval a b U n).1 (NestedInterval a b U n).2) U
  | 0 => h
  | n + 1 => by
    by_cases H : ExistsFinCover (Icc (NestedInterval a b U n).fst (((NestedInterval a b U n).fst + (NestedInterval a b U n).snd) / 2)) U
    case pos =>
      rw [NestedInterval]
      rw [nestedIntervalSucc_right _ _ H]
      apply nested_interval_aux'' _ _ (nested_interval_left_le_right hab U n) ?_ H
      apply nested_interval_ne_exists_fin_cover a b hab U h n
    case neg =>
      rw [NestedInterval]
      rw [nestedIntervalSucc_left _ _ H]
      dsimp only
      apply H

theorem nested_interval_len (a b : ℝ) (hab : a < b) (U: ι → Set ℝ) : 
    ∀ n : ℕ, (NestedInterval a b U n).2 - (NestedInterval a b U n).1 = (b - a) * (2 ^ n : ℝ)⁻¹
  | 0 => by simp only [pow_zero, inv_one, mul_one]; rfl
  | n + 1 => by
    by_cases H : ExistsFinCover (Icc (NestedInterval a b U n).fst (((NestedInterval a b U n).fst + (NestedInterval a b U n).snd) / 2)) U
    case pos =>
      rw [NestedInterval]
      rw [nestedIntervalSucc_right _ _ H]
      have := nested_interval_len a b hab U n
      field_simp at this ⊢
      rw [←this]
      ring
    case neg =>
      rw [NestedInterval]
      rw [nestedIntervalSucc_left _ _ H]
      have := nested_interval_len a b hab U n
      field_simp at this ⊢
      rw [←this]
      ring

theorem NestedIntervalSeq_is_nested {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : abs (y - x) ≤ (b - a) := by 
  refine Iff.mpr abs_sub_le_iff ?_
  dsimp [Icc] at *
  constructor <;> linarith

theorem NestedIntervalSeq_isCauSeq_aux {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : abs (y - x) ≤ (b - a) := by 
  refine Iff.mpr abs_sub_le_iff ?_
  dsimp [Icc] at *
  constructor <;> linarith

theorem NestedIntervalSeq_isCauSeq_aux' (i j : ℕ) (hij : i ≤ j) : 
    |NestedIntervalSeq a b U j - NestedIntervalSeq a b U i| ≤  (b - a) * (2 ^ i : ℝ)⁻¹ := by
  have := NestedIntervalSeq_isCauSeq_aux (NestedIntervalSeq_mem U hab i) (NestedIntervalSeq_mem' U hab i j hij)
  simpa [nested_interval_len, hab] using this


theorem NestedIntervalSeq_isCauSeq : IsCauSeq abs (NestedIntervalSeq a b U) := by
  intro ε ε0
  have ⟨i, hi⟩ : ∃ i : ℕ, (ε / (b - a))⁻¹ < 2 ^ i := pow_unbounded_of_one_lt (ε / (b - a))⁻¹ (by linarith)
  have hi : (b - a) * (2 ^ i : ℝ)⁻¹ < ε := (lt_div_iff' (by linarith)).mp (inv_lt_of_inv_lt (div_pos ε0 (sub_pos.mpr hab)) hi)
  exists i
  intro j hj
  calc |NestedIntervalSeq a b U j - NestedIntervalSeq a b U i| 
    _ ≤ (b - a) * (2 ^ i : ℝ)⁻¹ := by apply NestedIntervalSeq_isCauSeq_aux' hab U i j hj
    _ < ε := hi

def nestedIntervalCauseq : CauSeq ℝ abs where
  val := NestedIntervalSeq a b U
  property := NestedIntervalSeq_isCauSeq hab U

abbrev nestedIntervalLim : ℝ := (nestedIntervalCauseq hab U).lim

open Filter Topology

lemma tends_to_nestedIntervalLim : Tendsto (NestedIntervalSeq a b U) atTop (𝓝 (nestedIntervalLim hab U)) := by
  sorry


lemma nestedIntervalLim_mem : nestedIntervalLim hab U ∈ Icc a b := by
  have H : IsClosed (Icc a b) := by exact isClosed_Icc
  have := tends_to_nestedIntervalLim hab U
  refine Iff.mpr (IsClosed.mem_iff_closure_subset H) ?_
  
  sorry

example : ∃ i : ι, nestedIntervalLim hab U ∈ U i := by
  rcases cover (nestedIntervalLim_mem hab U) with ⟨s, ⟨i, (hi : U i = s)⟩, hs'⟩
  exists i
  simpa [hi] using hs'

example (U : Set ℝ) (hU : IsOpen U) (hmem : x ∈ U) : ∃ ε > 0, Metric.ball (x : ℝ) ε ⊆ U := by
  rw [Metric.isOpen_iff] at hU
  apply hU _ hmem


end