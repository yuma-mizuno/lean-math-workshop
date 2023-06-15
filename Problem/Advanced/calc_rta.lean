import Mathlib.Analysis.Asymptotics.Asymptotics

open Topology Filter Asymptotics

def HasDerivAt (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) := 
  (fun x' => f x' - f x - (x' - x) * f') =o[𝓝 x] fun x' => x' - x 

variable {f : ℝ → ℝ} {f' : ℝ} {g : ℝ → ℝ} {g' : ℝ} {x : ℝ} 

theorem HasDerivAt.isBigO_sub (h : HasDerivAt f f' x) : (fun x' => f x' - f x) =O[𝓝 x] fun x' => x' - x := by
  rw [h.isBigO.congr_of_sub]
  calc (fun x' => (x' - x) * f') 
    _ = fun x' => f' * (x' - x)  := by ext; ring
    _ =O[𝓝 x] fun x' => x' - x  := by apply isBigO_const_mul_self

theorem HasDerivAt.continuousAt (h : HasDerivAt f f' x) : ContinuousAt f x := by
  have : Tendsto (fun x' => f x' - f x) (𝓝 x) (𝓝 0) := by
    apply h.isBigO_sub.trans_tendsto
    rw [← sub_self x]
    exact tendsto_id.sub tendsto_const_nhds
  have := this.add (@tendsto_const_nhds _ _ _ (f x) _)
  rw [zero_add (f x)] at this
  exact this.congr (by simp)

theorem HasDerivAt.mul (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x * g x) (f x * g' + f' * g x) x := by
  calc (fun x' => f x' * g x' - f x * g x - (x' - x) * (f x * g' + f' * g x))
    _ = fun x' => f x * (g x' - g x - (x' - x) * g') + 
          (g x * (f x' - f x - (x' - x) * f') + (f x' - f x) * (g x' - g x)) := by ext; ring
    _ =o[𝓝 x] fun x' => x' - x                                              := by
      apply (hg.const_mul_left (f x)).add <| (hf.const_mul_left (g x)).add _
      calc (fun x' => (f x' - f x) * (g x' - g x))
        _ =o[𝓝 x] fun x' => (x' - x) * 1      := ?eq
        _ = fun x' => x' - x                   := by ext; ring
      case eq =>
        apply hf.isBigO_sub.mul_isLittleO
        rw [isLittleO_one_iff, tendsto_sub_nhds_zero_iff]
        apply hg.continuousAt.tendsto


theorem HasDerivAt.mul' (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x * g x) (f x * g' + f' * g x) x := by
  calc (fun x' => f x' * g x' - f x * g x - (x' - x) * (f x * g' + f' * g x))
    _ = fun x' => f x * (g x' - g x - (x' - x) * g') + 
          (g x' * (f x' - f x - (x' - x) * f') + f' * ((x' - x) * (g x' - g x))) := by ext; ring
    _ =o[𝓝 x] fun x' => x' - x                                              := by
      apply (hg.const_mul_left (f x)).add <| IsLittleO.add _ _
      · calc (fun x' => g x' * (f x' - f x - (x' - x) * f'))
          _ =o[𝓝 x] fun x' => 1 * (x' - x) := (hg.continuousAt.isBigO_one _).mul_isLittleO hf
          _ = fun x' => x' - x := by ext; ring
      · calc (fun x' => f' * ((x' - x) * (g x' - g x)))
          _ =O[𝓝 x] fun x' => (x' - x) * (g x' - g x) := by apply isBigO_const_mul_self
          _ =o[𝓝 x] fun x' => (x' - x) * 1            := (isBigO_refl _ _).mul_isLittleO ?eq
          _ = fun x' => (x' - x)                       := by ext; ring
        case eq =>
          rw [isLittleO_one_iff, tendsto_sub_nhds_zero_iff]
          apply hg.continuousAt.tendsto


theorem hasDerivAt_pow : ∀ (n : ℕ), HasDerivAt (fun x ↦ x ^ n : ℝ → ℝ) (n * x ^ (n - 1)) x
  | 0 => by simp [HasDerivAt]
  | 1 => by simp [HasDerivAt]
  | n + 1 + 1 => 
    suffices HasDerivAt (fun x => x ^ (n + 1) * x : ℝ → ℝ) (x ^ (n + 1) * 1 + (↑(n + 1) * x ^ n) * x) x by
      convert this using 1
      · ext; ring
      · simp; ring
    (hasDerivAt_pow (n + 1)).mul (by simp [HasDerivAt])
