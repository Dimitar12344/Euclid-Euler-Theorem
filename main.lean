import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
namespace Nathan

--Nathan is the name of the team of two working on this project

--DEFINITIONS

-- mathematically, a mersenne prime is defined by:
-- M = 2^p - 1 , which is prime and p is prime
def MersennePrime (M : ℕ) := Prime M ∧ ∃ (p : ℕ), Prime p ∧ M = 2^p - 1

-- mathematically, a perfect number is defined by:
-- sigma(N) = 2N, where N is a perfect number and sigma(x) is a function for the sum of all divisors
def Euclid_Euler_Def (P : ℕ) := ∃ p : ℕ,
MersennePrime (2^p - 1) ∧ P = 2^(p-1) * (2^p - 1)

def sumDivisors : ℕ → ℕ → ℕ
  | _, 0 => 0
  | P, k + 1 =>
    if (k + 1) ∣ P
    then (k + 1) + sumDivisors P k
    else sumDivisors P k

--def sumDivisors (P : ℕ) : ℕ :=
 -- (List.range (P + 1)).foldl (fun acc k => if k ∣ P then acc + k else acc) 0

def PerfectCool (P : ℕ) : Prop :=
  0 < P ∧ sumDivisors P P = 2 * P

def Perfect (P : ℕ) : Prop :=
  0 < P ∧ sumDivisors P P = 2 * P


#check PerfectCool 7 --Check checks the type
#check Perfect 7

--INTERMEDIATES
lemma a_times_b_coprime (M a b : ℕ) (h : M = a*b) (hcop : Nat.Coprime a b) (hdiv :sumDivisors (a*b) (a*b)
  = sumDivisors a a * sumDivisors b b) :
    sumDivisors M M = sumDivisors a a * sumDivisors b b := by
  rw [h]
  exact hdiv

lemma sumDivisors_pow_two : ∀ k : ℕ,
    sumDivisors (2^k) (2^k) = 2^(k+1) - 1 := by
  sorry
  -- Mathematical proof sketch:
  -- The divisors of 2^k are exactly 1, 2, 4, ..., 2^k
  -- Their sum is the geometric series 1 + 2 + 4 + ... + 2^k = 2^(k+1) - 1
  -- Proved by induction on k:
  -- Base case k=0: sumDivisors 1 1 = 1 = 2^1 - 1 ✓
  -- Inductive step: sumDivisors (2^(k+1)) (2^(k+1))
  --   = 2^(k+1) + sumDivisors (2^k) (2^k)
  --   = 2^(k+1) + (2^(k+1) - 1)
  --   = 2^(k+2) - 1 ✓

lemma divisors_of_coprime_product
    (a b d : ℕ)
    (hcop : Nat.Coprime a b)
    (hd : d ∣ a*b) :
    ∃ x y : ℕ, x ∣ a ∧ y ∣ b ∧ d = x*y := by
  sorry

lemma sumDivisors_multiplicative
    (a b : ℕ) (hcop : Nat.Coprime a b) :
    sumDivisors (a*b) (a*b)
      = sumDivisors a a * sumDivisors b b := by
  have hdiv :
      ∀ d : ℕ, d ∣ a*b →
      ∃ x y : ℕ, x ∣ a ∧ y ∣ b ∧ d = x*y := by
    intro d hd
    exact divisors_of_coprime_product a b d hcop hd

  have hsum :
      sumDivisors (a*b) (a*b)
        = sumDivisors a a * sumDivisors b b := by
    sorry

  exact hsum

lemma sumDivisors_prime (q : ℕ) (hq : Prime q) :
    sumDivisors q q = q + 1 := by
    sorry
  -- Mathematical proof:
  -- since q is prime its only divisors are 1 and q
  -- so sumDivisors q q = 1 + q = q + 1 ✓

--PROOF

theorem Euclid_Theorem (p : ℕ) (hp : 1 ≤ p) (h : MersennePrime (2^p - 1))
  (hcop : Nat.Coprime (2^(p-1)) (2^p - 1)) (hprime : Prime (2^p - 1)) :
  Perfect ((2^(p-1)) * (2^p - 1)) := by

  obtain ⟨q, hq_prime, hM_prime⟩ := h
  unfold Perfect

  have hmul : sumDivisors (2^(p-1) * (2^p - 1)) (2^(p-1) * (2^p - 1))
            = sumDivisors (2^(p-1)) (2^(p-1)) * sumDivisors (2^p - 1) (2^p - 1) := by
    exact sumDivisors_multiplicative (2^(p-1)) (2^p - 1) hcop

  rw [hmul]

  have hsigma_pow2 : sumDivisors (2^(p-1)) (2^(p-1)) = 2^p - 1 := by
    have h1 := sumDivisors_pow_two (p-1)
    have hstep : p - 1 + 1 = p := Nat.sub_add_cancel hp
    calc sumDivisors (2^(p-1)) (2^(p-1))
        = 2^(p-1+1) - 1 := h1
      _ = 2^p - 1 := by rw [hstep]

  have hsigma_mersenne : sumDivisors (2^p - 1) (2^p - 1) = 2^p := by
    have h1 : 1 ≤ 2^p := Nat.one_le_two_pow p
    calc sumDivisors (2^p - 1) (2^p - 1)
        = (2^p - 1) + 1 := sumDivisors_prime (2^p - 1) hprime
      _ = 2^p := Nat.sub_add_cancel h1

  rw [hsigma_pow2, hsigma_mersenne]
  constructor
  · apply Nat.mul_pos
    · apply Nat.pos_pow_of_pos
      numbers
    · calc 0 < 2 := by numbers
          _ ≤ 2^p - 1 := hprime.1
  · have hpow : 2^(p-1) * 2 = 2^p := by
      calc 2^(p-1) * 2 = 2^(p-1) * 2^1 := by ring
          _ = 2^(p-1+1) := by rw [pow_add]
          _ = 2^p := by rw [Nat.sub_add_cancel hp]
    calc (2^p - 1) * 2^p
        = (2^p - 1) * (2^(p-1) * 2) := by rw [hpow]
      _ = 2 * (2^(p-1) * (2^p - 1)) := by ring


theorem Euclid_Euler_Theorem (n : ℕ) (h: Even n):
  Perfect n ↔  ∃ (p:ℕ), MersennePrime (2^p - 1) ∧ n = (2^(p-1)) * (2^p - 1):= by
  sorry


end Nathan
