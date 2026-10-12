import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).mpr h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn

  have key : s n + t n - (a + b) = (s n - a) + (t n - b) := by ring
  rw [key]
  apply lt_of_le_of_lt (abs_add (s n - a) (t n - b))

  have hnNs: n ≥ Ns := by apply le_trans (le_max_left Ns Nt) hn
  have key1: |s n - a| < ε / 2 := by apply (hs n hnNs)

  have hnNt: n ≥ Nt := by apply le_trans (le_max_right Ns Nt) hn
  have key2: |t n - b| < ε / 2 := by apply (ht n hnNt)

  convert (add_lt_add key1 key2)
  . norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε epos

  have ecpos: ε / |c| > 0 := by
    field_simp
    exact h

  rcases cs (ε / |c|) ecpos with ⟨N, hn⟩
  use N
  intro n nbig
  dsimp

  have key: c * s n - c * a = c * (s n - a) := by ring
  rw [key]

  rw [abs_mul]
  convert mul_lt_mul_of_pos_left (hn n nbig) acpos
  field_simp


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn

  have key1: |s n| < 1 + |a| := by
    calc 1 + |a|
      1 + |a| > |s n - a| + |a| := by linarith [h n hn]
      _ ≥ |(s n - a) + a| := by apply abs_add (s n - a) a
      _ = |s n| := by ring_nf

  convert key1 using 1
  ring

#check le_rfl

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩

  use max N₀ N₁
  intro n hn

  calc |s n * t n - 0|
  |s n * t n - 0| = |s n * t n| := by ring_nf
  _ = |s n| * |t n| :=  by rw [abs_mul]
  _ ≤ B * |t n| := by apply mul_le_mul_of_nonneg_right (le_of_lt (h₀ n (le_trans (le_max_left N₀ N₁) hn))) (abs_nonneg t n)
  _ < B * (ε / B) := by rw [← sub_zero (t n)]; apply mul_lt_mul_of_pos_left (h₁ n (le_trans (le_max_right N₀ N₁) hn)) Bpos
  _ = ε := by field_simp

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    exact abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩



  let N := max Na Nb
  have ineq1: N ≥ Na := by apply le_max_left Na Nb
  have ineq2: N ≥ Nb := by apply le_max_right Na Nb

  have absa : |s N - a| < ε := by
    apply hNa N ineq1
  have absb : |s N - b| < ε := by
    apply hNb N ineq2

  have : |a - b| < |a - b| := by
    have key2: ε + ε = |a - b| := by
      unfold ε; ring_nf;

    have key1: |s N - a| + |s N - b| < |a - b| := by linarith [absa, absb, key2]

    have key3: |s N - a| + |s N - b| ≥ |a - b| :=
      calc |s N - a| + |s N - b|
      |s N - a| + |s N - b| = |a - s N| + |s N - b| := by rw [abs_sub_comm (s N) a]
      _ ≥ |(a - s N) + (s N - b)| := by apply abs_add (a - s N) (s N - b)
      _ = |a - b| := by ring_nf
    exact lt_of_le_of_lt key3 key1
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
