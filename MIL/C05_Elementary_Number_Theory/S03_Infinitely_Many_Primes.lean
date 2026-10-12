
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

open BigOperators

namespace C05S03

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n

  have : 2 ≤ Nat.factorial n + 1 := by
    simp
    apply Nat.one_le_iff_ne_zero.mpr  (Nat.factorial_ne_zero n)

  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg at ple
  have : p ∣ Nat.factorial n := by
    apply Nat.dvd_factorial (Nat.Prime.pos pp) ple
  have : p ∣ 1 := by
    convert Nat.dvd_sub pdvd this
    simp
  show False
  apply Nat.dvd_one.mp at this
  linarith [(Nat.Prime.one_lt pp), this]
open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp [subset_iff]
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp [subset_iff]
  tauto

end

#check Nat.Prime.eq_one_or_self_of_dvd

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i ∈ s, i :=
  Finset.dvd_prod_of_mem _ h

theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
    have h : p = 1 ∨ p = q := Nat.Prime.eq_one_or_self_of_dvd prime_q p h
    rcases h with h₁ | h₂
    · rw [h₁] at prime_p
      exfalso
      exact Nat.prime_one_false prime_p
    . trivial


theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n ∈ s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
  rcases h₁ with hpdvda | hpdvdprod
  left; exact Nat.Prime.eq_of_dvd_of_prime prime_p h₀.left hpdvda
  right; apply ih h₀.right hpdvdprod

example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i ∈ s', i) + 1 := by
      rw [← one_add_one_eq_two]
      apply Nat.add_le_add_right _ 1

      have (a : ℕ) : 0 < a → 1 ≤ a := by intro a; linarith

      apply this
      apply Finset.prod_pos
      intro i hs

      have i_prime : Nat.Prime i := by apply mem_s'.mp hs
      apply Nat.Prime.pos i_prime

  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i ∈ s', i := by
    have p_in_s : p ∈ s' := by apply mem_s'.mpr pp
    exact dvd_prod_of_mem (fun i ↦ i) p_in_s
  have : p ∣ 1 := by
    convert Nat.dvd_sub pdvd this
    simp
  show False
  apply Nat.Prime.ne_one pp (Nat.dvd_one.mp this)

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

#check Nat.div_dvd_of_dvd
#check Nat.div_lt_self

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  constructor
  · apply Nat.div_dvd_of_dvd h₀
  · apply Nat.div_lt_self <;> linarith

theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
  . by_cases m_prime : Nat.Prime m
    . use m
    . have ⟨p, pp, pdvdm, pmod⟩ := ih _ mltn h1 m_prime
      have pdvdn : p ∣ n := by exact Nat.dvd_trans pdvdm mdvdn
      use p

  .   have n_m_small : n / m < n := by exact (aux mdvdn mge2 mltn).right

      by_cases nm_prime : Nat.Prime (n / m)
      . use n / m
        constructor
        . exact nm_prime
        . exact ⟨(aux mdvdn mge2 mltn).left, h1⟩
      . have ⟨p, pp, pdvdm, pmod⟩ := ih _ n_m_small h1 nm_prime
        have pdvdn : p ∣ n := by exact Nat.dvd_trans pdvdm (aux mdvdn mge2 mltn).left
        use p
example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption

theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i ∈ erase s 3, i) + 3) % 4 = 3 := by
    norm_num
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
    exact (hs p).mp ⟨pp, p4eq⟩
  have pne3 : p ≠ 3 := by
    intro hp3

    have : p ∣ 3 := by rw [hp3]
    have : p ∣4 * ∏ i ∈ s.erase 3, i := by
      apply (Nat.dvd_add_iff_left this).mpr pdvd
    have : p ∣ ∏ i ∈ s.erase 3, i := by
      convert (Nat.Prime.dvd_mul pp).mp this
      constructor
      · intro h_aux
        right; exact h_aux
      · intro h_aux
        rcases h_aux with h_aux1 | h_aux2
        exfalso
        rw [hp3] at h_aux1
        norm_num at h_aux1
        exact h_aux2


    have s_prime (q : ℕ) : q ∈ s.erase 3 → Nat.Prime q := by
      intro h'
      rw [mem_erase] at h'
      exact ((hs q).mpr h'.right).left

    have pins : p ∈ s.erase 3 := by apply mem_of_dvd_prod_primes pp s_prime this
    rw [hp3, mem_erase] at pins
    tauto

  have pser : p ∈ s.erase 3 := by
    rw [mem_erase]
    exact ⟨pne3, ps⟩

  have : p ∣ ∏ i ∈ erase s 3, i := by
    apply dvd_prod_of_mem _ pser

  have : p ∣ 4 * ∏ i ∈ erase s 3, i := by
    exact Nat.dvd_mul_left_of_dvd this 4

  have : p ∣ 3 := by
    rw [add_comm] at pdvd
    apply (Nat.dvd_add_iff_left this).mpr pdvd

  have : p = 3 := by
    refine Nat.Prime.eq_of_dvd_of_prime pp ?_ this
    exact Nat.prime_three

  contradiction
