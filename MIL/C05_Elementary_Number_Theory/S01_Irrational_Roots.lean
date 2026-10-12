import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 1 := by norm_num

example : Nat.gcd 12 8 ≠ 3 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq

  have m2 : 2 ∣ m ^ 2 := by
    exact Dvd.intro (n ^ 2) (id (Eq.symm sqr_eq))

  have : 2 ∣ m := by
    rw [pow_two] at m2
    convert Nat.prime_two.dvd_mul.mp m2
    simp
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this

  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring

  have stupid : 2 ≠ 0 := by norm_num

  have teste: 2 * k ^ 2 = n ^ 2 := by
    apply (Nat.mul_right_inj stupid).mp this

  have n3: 2 ∣ n := by
    have n2: 2 ∣ n ^ 2 := by
      exact Dvd.intro (k ^ 2) (id (teste))
    rw [pow_two] at n2
    convert Nat.prime_two.dvd_mul.mp n2
    simp

  have : 2 ∣ m.gcd n := by
    (expose_names; exact Nat.dvd_gcd this_1 n3)


  have : 2 ∣ 1 := by
    exact (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod coprime_mn) (m ^ 2)) m2).mp this

  norm_num at this

theorem big_ndvd_small {m : ℕ} (h: m ≥ 2) : m ∣ 1 → False := by
  intro hbad
  obtain ⟨k, hk⟩ := hbad

  cases k with
  | zero   => rw [mul_zero] at hk; norm_num at hk
  | succ n =>
    rw [← Nat.succ_eq_add_one] at hk
    rw [Nat.mul_succ m n] at hk

    have : m > 1 := by linarith [h]
    have : m * n ≥ 0 := by exact Nat.zero_le (m * n)

    linarith

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro hmpn

  have pdvdmsq : p ∣ m ^ 2 := by exact Dvd.intro (n ^ 2) (id (Eq.symm hmpn))
  have pdvdm : p ∣ m := by exact Nat.Prime.dvd_of_dvd_pow prime_p pdvdmsq
  have pdvdm' : p ∣ m := by exact pdvdm

  obtain ⟨k, heq⟩ := pdvdm'
  rw [heq] at hmpn

  have : p * k ^ 2 = n ^ 2 := by
    rw [pow_two] at hmpn
    rw [mul_assoc] at hmpn
    convert (Nat.mul_right_inj (Nat.Prime.ne_zero prime_p)).mp hmpn using 1
    ring

  symm at this
  have pdvdnsq : p ∣ n ^ 2 :=  by exact Dvd.intro (k ^ 2) (id (Eq.symm this))
  have pdvdn : p ∣ n := by exact Nat.Prime.dvd_of_dvd_pow prime_p pdvdnsq

  have : p ∣ m.gcd n := by
    apply Nat.dvd_gcd_iff.mpr ⟨pdvdm, pdvdn⟩

  have : p ∣ 1 := by exact
    (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod coprime_mn) (m ^ 2)) pdvdmsq).mp this

  apply big_ndvd_small (Nat.Prime.two_le prime_p) this


#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa

  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    simp

  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [factorization_mul' (Nat.Prime.ne_zero prime_p) nsqr_nez]
    rw [factorization_pow', Nat.Prime.factorization' prime_p]
    ring

  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp

  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)

  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    rw [factorization_pow']

  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
    rw [factorization_mul' (Nat.succ_ne_zero r) npow_nz, factorization_pow']
    rw [Nat.succ_eq_add_one]
    ring

  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  exact Nat.dvd_sub (Nat.dvd_mul_right k (m.factorization p)) (Nat.dvd_mul_right k (n.factorization p))

#check multiplicity

example : ∀ p, (14 < p ∧ p < 16) ∧ (Nat.Prime p) → 2 ∣ p := by
  intro p ⟨⟨a1, a2⟩, a3⟩
  have teste: p = 16 := by sorry
  have this1: ¬ Nat.Prime p := by sorry
  contradiction
