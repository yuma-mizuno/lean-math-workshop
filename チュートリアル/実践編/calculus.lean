import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Topology Filter

example (x : ℝ) {f : ℝ → ℝ} {f' : ℝ →L[ℝ] ℝ} :
    HasFDerivAt f f' x ↔ 
      (fun x' => f x' - f x - f' (x' - x)) =o[𝓝 x] fun x' => x' - x := 
  by rfl

example (x : ℝ) {f : ℝ → ℝ} {f' : ℝ →L[ℝ] ℝ} (hf : HasFDerivAt f f' x) {g : ℝ → ℝ} {g' : ℝ →L[ℝ] ℝ} (hg : HasFDerivAt g g' (f x))
     : HasFDerivAt (g ∘ f) (g'.comp f') x := by
  have := 
    calc 
      (fun x' ↦ g (f x') - g (f x) - g' (f x' - f x)) 
        =o[𝓝 x] fun x' ↦ f x' - f x         := hg.comp_tendsto (hf.continuousAt)
      _ =O[𝓝 x] fun x' ↦ x' - x            := hf.isBigO_sub
  refine this.triangle ?_
  have hg' : (fun x' ↦ g' (f x' - f x - f' (x' - x))) =O[𝓝 x] fun x' ↦ f x' - f x - f' (x' - x) := g'.isBigO_comp _ _ 
  calc (fun x' ↦ g' (f x' - f x) - g'.comp f' (x' - x)) 
      = fun x' ↦ g' (f x' - f x - f' (x' - x))           := by simp
    _ =O[𝓝 x] fun x' ↦ f x' - f x - f' (x' - x)         := (g'.isBigO_comp _ _)
    _ =o[𝓝 x] fun x' ↦ x' - x                           := hf

example (x : ℝ) : HasFDerivAt ((·)^2) (LinearMap.toContinuousLinearMap (LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (2 : ℝ))) x := by
  simp [HasFDerivAt, HasFDerivAtFilter]
  rw [hasFDerivAt_iff_tendsto]
  simp
  simp only [Tendsto, Real.norm_eq_abs, Pi.pow_apply, map_sub, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, smul_eq_mul]
  linarith
  continuity

noncomputable
instance : Coe ((Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ((Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) := ⟨LinearMap.toContinuousLinearMap⟩

-- set_option trace.Meta.synthInstance true in
example (m n l : ℕ) (x : Fin m → ℝ) {f : (Fin m → ℝ) → (Fin n → ℝ)} {f' : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)} 
  (hf : HasFDerivAt f (LinearMap.toContinuousLinearMap f') x) {g : (Fin n → ℝ) → (Fin l → ℝ)} {g' : (Fin n → ℝ) →ₗ[ℝ] (Fin l → ℝ)} 
    (hg : HasFDerivAt g (LinearMap.toContinuousLinearMap g') (f x))
     : HasFDerivAt (g ∘ f) (LinearMap.toContinuousLinearMap (g'.comp f')) x := by
  unfold HasFDerivAt HasFDerivAtFilter at hg
  have :=
    calc
      (fun x' ↦ g (f x') - g (f x) - g' (f x' - f x)) =o[𝓝 x] fun x' ↦ f x' - f x :=
        hg.comp_tendsto (hf.continuousAt)

      _ =O[𝓝 x] fun x' => x' - x := hf.isBigO_sub
  refine' this.triangle _
  calc
    (fun x' => g' (f x' - f x) - g'.comp f' (x' - x)) =ᶠ[𝓝 x] fun x' =>
        g' (f x' - f x - f' (x' - x)) :=
      eventually_of_forall fun x' => by simp
    _ =O[𝓝 x] fun x' => f x' - f x - f' (x' - x) := (g'.toContinuousLinearMap.isBigO_comp _ _)
    _ =o[𝓝 x] fun x' => x' - x := hf

example (σ : Type) (m n l : ℕ) (x : σ → ℝ) {f : (σ → ℝ) → (Fin n → ℝ)} {f' : (σ → ℝ) →L[ℝ] (Fin n → ℝ)} 
  (hf : HasFDerivAt f f' x) {g : (Fin n → ℝ) → (Fin l → ℝ)} {g' : (Fin n → ℝ) →L[ℝ] (Fin l → ℝ)} 
    (hg : HasFDerivAt g g' (f x))
     : HasFDerivAt (g ∘ f) (g'.comp f') x := by
  unfold HasFDerivAt HasFDerivAtFilter at hg
  have :=
    calc
      (fun x' ↦ g (f x') - g (f x) - g' (f x' - f x)) =o[𝓝 x] fun x' ↦ f x' - f x :=
        hg.comp_tendsto (hf.continuousAt)

      _ =O[𝓝 x] fun x' => x' - x := hf.isBigO_sub
  refine' this.triangle _
  calc
    (fun x' => g' (f x' - f x) - g'.comp f' (x' - x)) =ᶠ[𝓝 x] fun x' =>
        g' (f x' - f x - f' (x' - x)) :=
      eventually_of_forall fun x' => by simp
    _ =O[𝓝 x] fun x' => f x' - f x - f' (x' - x) := (g'.toContinuousLinearMap.isBigO_comp _ _)
    _ =o[𝓝 x] fun x' => x' - x := hf