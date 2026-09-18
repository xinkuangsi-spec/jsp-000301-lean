/-
Copyright (c) 2026 xinkuangsi-spec. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: xinkuangsi-spec
-/
import Mathlib

/-!
# JSP-000301 · Consecutive powerful numbers without a perfect square

The catalog problem asks: if two consecutive positive integers are both
*powerful* (every prime factor occurs with exponent at least two), must at
least one of them be a perfect square?

The answer is no. Golomb's 1970 counterexample ([Go70], *Powerful numbers*,
Amer. Math. Monthly 77(8), 848–852) exhibits

* `12167 = 23³` and
* `12168 = 2³ · 3² · 13²`,

which are consecutive powerful numbers lying strictly between the consecutive
squares `110² = 12100` and `111² = 12321`, so neither is a perfect square.

This file formalizes the counterexample and the resulting negative answer.
-/

/-- A natural number is *powerful* if every prime factor divides it with
exponent at least two. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- `12167 = 23³` is powerful: its only prime divisor is `23`. -/
theorem powerful_12167 : Powerful 12167 := by
  intro p hp hdiv
  have hfact : (12167 : ℕ) = 23 ^ 3 := by norm_num
  have hp23 : Nat.Prime 23 := by norm_num
  rw [hfact] at hdiv
  have hdvd : p ∣ 23 := hp.dvd_of_dvd_pow hdiv
  have hle : p ≤ 23 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := hp.two_le
  -- 2 ≤ p ≤ 23, p ∣ 23 and p prime, and 23 is prime, so p = 23.
  interval_cases p <;> first
    | decide
    | (norm_num at hdvd)

/-- `12168 = 2³ · 3² · 13²` is powerful: its prime divisors lie in `{2, 3, 13}`
and each of their squares divides `12168`. -/
theorem powerful_12168 : Powerful 12168 := by
  intro p hp hdiv
  have hfact : (12168 : ℕ) = 2 ^ 3 * (3 ^ 2 * 13 ^ 2) := by norm_num
  rw [hfact] at hdiv
  have hcases : p = 2 ∨ p = 3 ∨ p = 13 := by
    rcases hp.dvd_mul.mp hdiv with h2 | hrest
    · left
      have hd : p ∣ 2 := hp.dvd_of_dvd_pow h2
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      have hge : 2 ≤ p := hp.two_le
      omega
    · rcases hp.dvd_mul.mp hrest with h3 | h13
      · right; left
        have hd : p ∣ 3 := hp.dvd_of_dvd_pow h3
        have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hd
        have hge : 2 ≤ p := hp.two_le
        interval_cases p
        · norm_num at hd
        · rfl
      · right; right
        have hd : p ∣ 13 := hp.dvd_of_dvd_pow h13
        have hle : p ≤ 13 := Nat.le_of_dvd (by norm_num) hd
        have hge : 2 ≤ p := hp.two_le
        interval_cases p <;> first
          | rfl
          | (norm_num at hd)
  rcases hcases with rfl | rfl | rfl <;> decide

/-- Any natural number strictly between `110²` and `111²` is not a perfect
square. -/
theorem not_isSquare_between_sq {n : ℕ} (h : 110 ^ 2 < n ∧ n < 111 ^ 2) :
    ¬ IsSquare n := by
  rintro ⟨r, hr⟩
  rcases h with ⟨h1, h2⟩
  rw [hr] at h1 h2
  norm_num at h1 h2
  by_cases hc : r ≤ 110
  · have hb : r * r ≤ 110 * 110 := Nat.mul_le_mul hc hc
    norm_num at hb
    omega
  · have hb : 111 * 111 ≤ r * r :=
      Nat.mul_le_mul (show (111 : ℕ) ≤ r by omega) (show (111 : ℕ) ≤ r by omega)
    norm_num at hb
    omega

/-- `12167` is not a perfect square. -/
theorem not_isSquare_12167 : ¬ IsSquare (12167 : ℕ) :=
  not_isSquare_between_sq ⟨by norm_num, by norm_num⟩

/-- `12168` is not a perfect square. -/
theorem not_isSquare_12168 : ¬ IsSquare (12168 : ℕ) :=
  not_isSquare_between_sq ⟨by norm_num, by norm_num⟩

/-- Golomb's counterexample, packaged as an existential statement. -/
theorem exists_consecutive_powerful_not_square :
    ∃ n : ℕ, Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1) :=
  ⟨12167, powerful_12167, powerful_12168, not_isSquare_12167, not_isSquare_12168⟩

/-- The stated yes/no question of JSP-000301 has a negative answer. -/
theorem jsp_000301_answer :
    ¬ (∀ n : ℕ, Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  obtain h | h := h 12167 powerful_12167 powerful_12168
  · exact not_isSquare_12167 h
  · exact not_isSquare_12168 h
