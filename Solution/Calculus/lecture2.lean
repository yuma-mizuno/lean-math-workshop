import Mathlib.Topology.MetricSpace.CauSeqFilter

noncomputable
section

example : (1 : ℝ) = Real.ofCauchy (Quotient.mk CauSeq.equiv (CauSeq.const abs 1)) := 
  Real.ofCauchy_one.symm

def «0.9999999» : CauSeq ℚ abs where
  val n := 1 - (10 ^ n : ℚ)⁻¹
  property := by
    intro ε ε0
    suffices ∃ i, ∀ (j : ℕ), j ≥ i → |((10 ^ i : ℚ)⁻¹ - (10 ^ j : ℚ)⁻¹)| < ε by simpa
    have h : ∃ i : ℕ, (ε / 2)⁻¹ < 10 ^ i := pow_unbounded_of_one_lt (ε / 2)⁻¹ (by linarith)
    cases h with | intro i hi =>
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

open Filter Topology Set Classical

def HasFinCover {ι : Type} (U : ι → Set ℝ) (s : Set ℝ) := 
  ∃ (t : Finset ι), s ⊆ ⋃ i ∈ t, U i

variable {ι : Type} (U : ι → Set ℝ)

def nestedIntervalSucc (a b : ℝ) : ℝ × ℝ :=
  if ¬HasFinCover U (Icc a ((a + b) / 2)) then ⟨a, (a + b) / 2⟩ else ⟨(a + b) / 2, b⟩

def nestedInterval : ℕ → ℝ × ℝ 
  | 0 => ⟨0, 1⟩
  | n + 1 => nestedIntervalSucc U (nestedInterval n).1 (nestedInterval n).2

local notation "I(" n ")" => Icc (Prod.fst (nestedInterval U n)) (Prod.snd (nestedInterval U n))

def nestedIntervalSeq : ℕ → ℝ := 
  fun n => ((nestedInterval U n).1 + (nestedInterval U n).2) / 2

variable {U}

lemma hasFinCover_concat (hac : HasFinCover U (Icc a c)) (hcb : HasFinCover U (Icc c b)) :
    HasFinCover U (Icc a b) := by
  rcases hac with ⟨ι_ac, cover_ac⟩
  rcases hcb with ⟨ι_cb, cover_cb⟩
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

lemma not_hasFinCover_concat :
    ¬HasFinCover U (Icc a b) → HasFinCover U (Icc a c) → ¬HasFinCover U (Icc c b) := by
  contrapose!
  intro H
  apply hasFinCover_concat H.1 H.2

lemma not_hasFinCover_concat' (h : ¬HasFinCover U (Icc a b)) : 
    HasFinCover U (Icc a ((a + b) / 2)) → ¬HasFinCover U (Icc ((a + b) / 2) b) := 
  not_hasFinCover_concat h

lemma nestedIntervalSucc_left (h : ¬HasFinCover U (Icc a ((a + b) / 2))) : 
    nestedIntervalSucc U a b = ⟨a, (a + b) / 2⟩ := 
  if_pos h
  
lemma nestedIntervalSucc_right (h : HasFinCover U (Icc a ((a + b) / 2))) : 
    nestedIntervalSucc U a b = ⟨(a + b) / 2, b⟩ := 
  if_neg (not_not_intro h)

variable (U)

theorem nestedIntervalSucc_eq_or_eq (a b : ℝ) : 
    nestedIntervalSucc U a b = ⟨a, (a + b) / 2⟩ ∨ 
      nestedIntervalSucc U a b = ⟨(a + b) / 2, b⟩ := by
  apply ite_eq_or_eq

theorem nestedInterval_le : ∀ n, (nestedInterval U n).1 < (nestedInterval U n).2 
  | 0 => Real.zero_lt_one
  | n + 1 => by
    have := nestedInterval_le n
    cases nestedIntervalSucc_eq_or_eq U (nestedInterval U n).1 (nestedInterval U n).2 with
    | inl h => rw [nestedInterval, h]; dsimp only; linarith
    | inr h => rw [nestedInterval, h]; dsimp only; linarith

theorem nestedIntervalSeq_is_nested_succ (n : ℕ) : I(n + 1) ⊆ I(n) := by
  intro x hx
  have := nestedInterval_le U n
  rcases nestedIntervalSucc_eq_or_eq U (nestedInterval U n).1 (nestedInterval U n).2 with h | h <;>
    rw [nestedInterval, h, Set.mem_Icc] at hx <;> dsimp only at hx <;> split_ands <;> linarith

theorem nestedIntervalSeq_is_nested {i j : ℕ} (hij : i ≤ j) : I(j) ⊆ I(i) := by 
  set k := j - i
  have : j = i + k := (Nat.add_sub_of_le hij).symm
  rw [this]
  induction k with
  | zero => apply rfl.subset
  | succ k ih => intro x hx; apply ih (nestedIntervalSeq_is_nested_succ U (i + k) hx)

theorem nestedIntervalSeq_mem (n : ℕ) : nestedIntervalSeq U n ∈ I(n) := by
  have := nestedInterval_le U n
  simp only [mem_Icc, nestedIntervalSeq] 
  split_ands <;> linarith

theorem nestedIntervalSeq_mem_of_le {i j : ℕ} (hij : i ≤ j): 
    nestedIntervalSeq U j ∈ I(i) := 
  nestedIntervalSeq_is_nested _ hij (nestedIntervalSeq_mem _ _)

variable {U}
  
theorem nestedInterval_not_hasFinCover (h : ¬HasFinCover U (Icc 0 1)) : ∀ n : ℕ, ¬HasFinCover U I(n)
  | 0 => h
  | n + 1 => by
    by_cases H : HasFinCover U (Icc (nestedInterval U n).1 (((nestedInterval U n).1 + (nestedInterval U n).2) / 2))
    case pos =>
      rw [nestedInterval]
      rw [nestedIntervalSucc_right H]
      apply not_hasFinCover_concat ?_ H
      apply nestedInterval_not_hasFinCover h n
    case neg =>
      rw [nestedInterval]
      rw [nestedIntervalSucc_left H]
      dsimp only
      apply H

variable (U)

theorem nestedInterval_len : ∀ n : ℕ, (nestedInterval U n).2 - (nestedInterval U n).1 = (2 ^ n : ℝ)⁻¹
  | 0 => by simp [nestedInterval]
  | n + 1 => by
    rw [nestedInterval]
    have := nestedInterval_len n
    set a := (nestedInterval U n).1
    set b := (nestedInterval U n).2
    cases nestedIntervalSucc_eq_or_eq U (nestedInterval U n).1 (nestedInterval U n).2 with
    | inl H =>
      rw [H]
      field_simp at this ⊢
      calc (a + b - 2 * a) * 2 ^ (n + 1) = (b - a) * 2 ^ n * 2 := by ring
        _= 2 := by rw [this]; ring
    | inr H =>
      rw [H]
      field_simp at this ⊢
      calc (b * 2 - (a + b)) * 2 ^ (n + 1) = (b - a) * 2 ^ n * 2 := by ring
        _= 2 := by rw [this]; ring


theorem nestedIntervalSeq_isCauSeq_aux {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : |y - x| ≤ (b - a) := by 
  dsimp [Icc] at hx hy
  apply (abs_sub_le_iff.2 ⟨_, _⟩) <;> linarith

theorem nestedIntervalSeq_isCauSeq_aux' {i j : ℕ} (hij : i ≤ j) : 
    |nestedIntervalSeq U j - nestedIntervalSeq U i| ≤ (2 ^ i : ℝ)⁻¹ := by
  have := nestedIntervalSeq_isCauSeq_aux (nestedIntervalSeq_mem U i) (nestedIntervalSeq_mem_of_le U hij)
  simpa [nestedInterval_len] using this

theorem nestedIntervalSeq_isCauSeq : IsCauSeq abs (nestedIntervalSeq U) := by
  intro ε ε0
  have ⟨i, hi⟩ : ∃ i : ℕ, ε⁻¹ < 2 ^ i := pow_unbounded_of_one_lt ε⁻¹ (by linarith)
  have hi : (2 ^ i : ℝ)⁻¹ < ε := inv_lt_of_inv_lt ε0 hi
  exists i
  intro j hj
  calc |nestedIntervalSeq U j - nestedIntervalSeq U i| 
    _ ≤ (2 ^ i : ℝ)⁻¹ := nestedIntervalSeq_isCauSeq_aux' U hj
    _ < ε := hi

def nestedIntervalCauseq : CauSeq ℝ abs where
  val := nestedIntervalSeq U
  property := nestedIntervalSeq_isCauSeq U

-- set_option trace.Meta.synthInstance true in
local instance : CauSeq.IsComplete ℝ norm := inferInstanceAs (CauSeq.IsComplete ℝ abs)

lemma nestedIntervalSeq_tendsto : 
    Tendsto (nestedIntervalSeq U) atTop (𝓝 (nestedIntervalCauseq U).lim) := by
  apply (nestedIntervalCauseq U).tendsto_limit

lemma nestedIntervalLim_mem (n : ℕ) : (nestedIntervalCauseq U).lim ∈ I(n) := by
  apply isClosed_Icc.mem_of_tendsto (nestedIntervalSeq_tendsto U)
  rw [eventually_atTop]
  exists n
  intro m
  apply nestedIntervalSeq_mem_of_le U

theorem hasFinCover_of_Icc (hU : ∀ (i : ι), IsOpen (U i)) (cover : Icc 0 1 ⊆ ⋃ (i : ι), U i) : 
    HasFinCover U (Icc 0 1) := by 
  by_contra h
  rcases cover (nestedIntervalLim_mem U 0) with ⟨_, ⟨i, rfl⟩, hU'⟩
  rcases Metric.isOpen_iff.1 (hU i) (nestedIntervalCauseq U).lim hU' with ⟨ε, ε0, hε⟩
  have ⟨n, hn⟩ : ∃ n : ℕ, (ε / 2)⁻¹ < 2 ^ n := pow_unbounded_of_one_lt (ε / 2)⁻¹ (by linarith)
  have hn : 2 * (2 ^ n : ℝ)⁻¹ < ε := (lt_div_iff' (by linarith)).mp (inv_lt_of_inv_lt (half_pos ε0) hn)
  apply nestedInterval_not_hasFinCover h n
  exists {i}
  set a := (nestedInterval U n).1
  set b := (nestedInterval U n).2
  set c := (nestedIntervalCauseq U).lim
  intro x (hx : a ≤ x ∧ x ≤ b)
  suffices x ∈ Metric.ball c ε by
    simp_rw [Finset.mem_singleton, iUnion_iUnion_eq_left]
    apply hε this
  have := calc 2 * |x - c| 
    _ = |2 * (x - c)| := by simp [abs_mul] 
    _ = |(x - b) + (x - a) + (b - c) + (a - c)| := by congr 1; ring
    _ ≤ |(x - b) + (x - a) + (b - c)| + |a - c| := by apply abs_add
    _ ≤ |(x - b) + (x - a)| + |b - c| + |a - c| := by apply add_le_add_right (abs_add _ _)
    _ ≤ |x - b| + |x - a| + |b - c| + |a - c|   := by apply add_le_add_right (add_le_add_right (abs_add _ _) _)
    _ ≤ (2 ^ n : ℝ)⁻¹ + (2 ^ n : ℝ)⁻¹ + (2 ^ n : ℝ)⁻¹ + (2 ^ n : ℝ)⁻¹ := by 
      have hba : b - a = (2 ^ n : ℝ)⁻¹ := nestedInterval_len U n
      have hc : a ≤ c ∧ c ≤ b := nestedIntervalLim_mem U n
      repeat apply add_le_add
      repeat apply (abs_sub_le_iff.2 ⟨_, _⟩) <;> linarith
    _ = 2 * (2 * (2 ^ n : ℝ)⁻¹) := by field_simp; ring
  calc |x - c| ≤ 2 * (2 ^ n : ℝ)⁻¹ := (mul_le_mul_left (by linarith)).1 this
    _ < ε := hn
  
end