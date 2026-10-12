import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  intro hs x hxs
  show f x ∈ v
  apply hs; use x

  intro hsv
  simp; exact hsv

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x hxs
  rcases hxs with ⟨a, haux, hax⟩
  apply h at hax
  rwa [hax] at haux

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x ⟨a, b, c⟩
  rw [← c]
  exact b

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x hxu
  rcases h x with ⟨a, b, c⟩
  use a
  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro x ⟨a, b, c⟩
  use a; exact ⟨h b, c⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x ha
  apply h
  exact ha

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  simp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x ⟨a, b, c⟩
  simp
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  simp
  tauto

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro x hint
  simp at *
  tauto

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro x hint
  simp at *
  have idea: ∃ c, ∀ aux : I, c ∈ A aux ∧ f c = x := by
    rcases hint i with ⟨c, aux2, eq⟩
    use c
    by_contra! haux
    rcases haux with ⟨a, b⟩
    by_cases hpass : c ∈ A a
    apply b hpass eq
    rcases hint a with ⟨d, e, f⟩
    rw [← eq] at f
    apply injf at f
    rw [f] at e
    contradiction

  rcases idea with ⟨c,d⟩
  use c
  constructor
  . intro i
    exact (d i).1
  . exact (d i).2

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x₁ hx₁ x₂ hx₂ eq

  have : |x₁| = |x₂| := by
    calc |x₁|
    _ = √ (x₁ * x₁) := by symm; exact Real.sqrt_mul_self_eq_abs x₁
    _ = √ x₁ * √ x₁ := by exact sqrt_mul hx₁ x₁
    _ = √x₂ * √x₂ := by repeat rw [eq]
    _ = √ (x₂ * x₂) := by symm; exact sqrt_mul hx₂ x₂
    _ = |x₂| := by exact Real.sqrt_mul_self_eq_abs x₂

  have huax₁: |x₁| = x₁ := by
    exact abs_of_nonneg hx₁
  have huax₂: |x₂| = x₂ := by
    exact abs_of_nonneg hx₂

  rwa [← huax₂, ← huax₁]


example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x₁ hx₁ x₂ hx₂ eq
  dsimp at *

  calc x₁
  _ = |x₁| := by symm; exact abs_of_nonneg hx₁
  _ = √ (x₁ * x₁) := by symm; exact Real.sqrt_mul_self_eq_abs x₁
  _ = √ (x₁ ^ 2) := by rw [pow_two x₁]
  _ = √ (x₂ ^ 2 ):= by rw [eq]
  _ = √ (x₂ * x₂) := by rw [← pow_two x₂]
  _ = |x₂| := by exact Real.sqrt_mul_self_eq_abs x₂
  _ = x₂ := by exact abs_of_nonneg hx₂


example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x; constructor
  rintro ⟨x₂, hx₂, conx₂⟩
  simp
  have : √ x₂ ≥ 0 := by sorry
  rw [conx₂] at this; exact this

  intro h
  simp at *
  use x ^ 2
  constructor
  . sorry
  . calc √ (x ^ 2)
    _ = |x| := by sorry
    _ = x := by sorry


example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x; simp at *; constructor;
  simp; sorry
  intro hxpos
  sorry
end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

#check inverse_spec
#print LeftInverse

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor; intro h1 x;
  have h: ∃ x₁, f x₁ = f x := by use x
  have h_prop: f (choose h) = f x := choose_spec h
  rw [inverse, dif_pos h];
  apply h1; exact h_prop

  rintro h x y heq;
  calc x
  _ = (inverse f) (f x) := by symm; apply h
  _ = (inverse f ) (f y) := by rw [heq]
  _ = y := by apply h

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor; intro hsur x;
  have h: ∃ x₁, f x₁ = x := by apply hsur x
  have h_prop: f (choose h) = x := choose_spec h
  rw [inverse, dif_pos h]
  exact h_prop

  intro h x;
  use (inverse f x)
  exact h x

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    exact h₁
  have h₃ : j ∉ S := by
    rwa [h] at h₁
  contradiction

end
