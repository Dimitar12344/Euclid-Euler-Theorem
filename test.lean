import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init















--Work on definitions with Luiz (05-04-2026)

namespace MySpace

def Even (n : ℕ) := ∃ (k : ℕ), n = 2*k

def Odd (n : ℕ) := ∃ (k : ℕ), n = 2*k + 1

-- we call a number fantastic if it is even and divisible by 3
def Fantastic (n : ℕ) := Even n ∧ (∃ (k : ℕ), n = 3*k)

example : Even 10 := by
    dsimp[Even]
    use 5
    numbers

example : Fantastic 6 := by
    dsimp[Fantastic]
    constructor
    · use 3
      numbers
    · use 2
      numbers

theorem even_plus_odd_eq_odd (n m : ℕ) (hn : Even n) (hm : Odd m) : Odd (n+m) := by
    sorry

end MySpace









--Work on sums with Ian (12-04-2026)

#eval [1,2,3].sum

partial def divisorsOf (n : Nat) (i : Nat) : List Nat := --using partial because of recursion
  if i == 1 then [1]
  else
    if n % i == 0
    then i :: divisorsOf n (i - 1)
    else divisorsOf n (i - 1)

#eval divisorsOf 100 100

def Divisors (n : Nat) := { x : Nat // ∃ a : Nat, n = a * x }

def sumDiv (n : Nat) (count : Nat) : Nat :=
  match count with
  | 0 => 0
  | count' + 1 => if n % count == 0
                  then count + sumDiv n count'
                  else sumDiv n count'

#eval sumDiv 6 6


-- Some examples of "summing" with folds:
-- btw `(· + ·)` is like a shorthand for `def add x y := x + y`

def nums := [1,2,3,4,5,6,7,8,9]
#eval nums.foldl (· + ·) (0:Nat)

def concat (x : String) (y : Nat) : String := s!"{x} then {y}"
#eval nums.foldl concat ""




--test for loops (16-04-2026)



def forloop (n:Nat) := List Nat
  for i in range (n) do
    if n==1 then [1]
    else [n]

#eval List.forM [1]



--lemma tests
def sumDivisors : ℕ → ℕ → ℕ
  | _, 0 => 0
  | P, k + 1 =>
    if (k + 1) ∣ P
    then (k + 1) + sumDivisors P k
    else sumDivisors P k


lemma sumDivisors_prime (q : ℕ) (hq : Prime q) :
    sumDivisors q q = q + 1 := by
    sorry

lemma sumDivisors_multiplicative (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (h : Nat.Coprime a b) :
    sumDivisors (a * b) (a * b) =
    sumDivisors a a * sumDivisors b b := by
  sorry
