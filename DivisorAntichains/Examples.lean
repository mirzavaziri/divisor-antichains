/-
Sanity checks against OEIS A096826.
-/
import DivisorAntichains.Binomial

namespace DivisorAntichains

/-- `a(48) = 10`: `48 = 2^4 * 3`. -/
example : a (2 ^ 4 * 3 ^ 1) = 10 := by
  rw [a_two_primes Nat.prime_two Nat.prime_three (by decide) (by decide)]
  decide

/-- `a(24) = 6`: `24 = 2^3 * 3`. -/
example : a (2 ^ 3 * 3 ^ 1) = 6 := by
  rw [a_two_primes Nat.prime_two Nat.prime_three (by decide) (by decide)]
  decide

/-- `a(72) = 4`: `72 = 2^3 * 3^2`. -/
example : a (2 ^ 3 * 3 ^ 2) = 4 := by
  rw [a_two_primes Nat.prime_two Nat.prime_three (by decide) (by decide)]
  decide

/-- `a(36) = 1`: `36 = 2^2 * 3^2`. -/
example : a (2 ^ 2 * 3 ^ 2) = 1 := by
  rw [a_two_primes Nat.prime_two Nat.prime_three (by decide) (by decide)]
  decide

/-- `a(16) = 5`: a prime power `p^L` is the case `s = 0`. -/
example : a (2 ^ 4 * 3 ^ 0) = 5 := by
  rw [a_two_primes Nat.prime_two Nat.prime_three (by decide) (by decide)]
  decide

end DivisorAntichains
