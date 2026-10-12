import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
#check le_antisymm

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  . show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

#check max_le_iff

example : max a b = max b a := by
  apply ge_antisymm
  . show max b a ≤ max a b
    apply max_le
    . show b ≤ max a b
      apply le_max_right
    . show a ≤ max a b
      apply le_max_left
  . show max a b ≤ max b a
    apply max_le
    . show a ≤ max b a
      apply le_max_right
    . show b ≤ max b a
      apply le_max_left

#check lt_trans

example : min (min a b) c = min a (min b c) := by
  have h1: min (min a b) c ≤ a := by
    calc
      min (min a b) c
      ≤ min a b := min_le_left (min a b) c
      _ ≤ a     := min_le_left a b

  have h2: min (min a b) c ≤ b := by
    calc
      min (min a b) c
      ≤ min a b := min_le_left (min a b) c
      _ ≤ b     := min_le_right a b

  have h3: min (min a b) c ≤ c := by
    calc
      min (min a b) c
      _ ≤ c := min_le_right (min a b) c

  apply le_antisymm
  . show min (min a b) c ≤ min a (min b c)
    have h: min (min a b) c ≤ min b c := by
      apply le_min
      exact h2
      exact h3
    apply le_min h1 h

  . show min a (min b c) ≤ min (min a b) c
    sorry

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  . show min a b + c ≤ a + c
    have h1: min a b ≤ a := by apply min_le_left a b
    rw [← add_neg_cancel_right (min a b) c] at h1
    exact (OrderedSub.tsub_le_iff_right (min a b + c) c a).mp h1
  . show min a b + c ≤ b + c
    have h2: min a b ≤ b := by apply min_le_right a b
    rw [← add_neg_cancel_right (min a b) c] at h2
    exact (OrderedSub.tsub_le_iff_right (min a b + c) c b).mp h2

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  . show min a b + c ≤ min (a + c) (b + c)
    apply aux
  . show min (a+c) (b+c) ≤ min a b + c
    rw [← add_neg_cancel_right (min (a + c) (b+c)) c, add_assoc, add_comm c, ← add_assoc]
    rw [add_le_add_iff_right c]
    apply le_min
    . show min (a + c) (b + c) - c ≤ a
      have h := min_le_left (a + c) (b + c)
      linarith
    . show min (a + c) (b + c) - c ≤ b
      have h := min_le_right (a + c) (b + c)
      linarith




example (a b c : ℝ): a + c ≤ b + c → a ≤ b := by
  sorry

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  nth_rw 1 [← add_sub_cancel_right a b, add_sub_right_comm]
  have h: |a - b + b| ≤ |a - b| + |b| := by exact abs_add (a - b) b
  linarith
  end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have hsquare: x ∣ w ^ 2 := by
    rw [Nat.pow_two]
    apply dvd_mul_of_dvd_left h
  apply dvd_add
  . show x ∣ y * (x * z) + x ^ 2
    apply dvd_add
    . show x ∣ y * (x * z)
      rw [← mul_assoc]
      apply dvd_mul_of_dvd_left
      apply dvd_mul_left
    . show x ∣  x ^ 2
      apply dvd_mul_left
  . show x ∣  w ^ 2
    exact hsquare
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply _root_.dvd_antisymm
  apply Nat.dvd_gcd_iff.mpr
  exact And.symm (Nat.gcd_dvd m n)
  apply Nat.dvd_gcd_iff.mpr
  exact And.symm (Nat.gcd_dvd n m)
end
