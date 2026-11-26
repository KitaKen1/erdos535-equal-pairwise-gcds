import Erdos535.Reduction
import OAI.Combinatorics.Sunflower.FixedBase

/-!
# Erdős Problem 535

* [Er64] P. Erdős, [On a problem in elementary number theory and a combinatorial problem](https://combinatorica.hu/~p_erdos/1964-10.pdf), 1964.
* [Er73] P. Erdős, [Problems and results on combinatorial number theory](https://www.renyi.hu/~p_erdos/1973-21.pdf), 1973.
* [OAI26] OpenAI, [An exponential bound for sunflowers](https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/An-exponential-bound-for-sunflowers-November-24-2026), 2026.
-/

open Filter Real

namespace Erdos535

private theorem exponentialSunflower : ExponentialSunflowerStatement :=
  OAI.Combinatorics.Sunflower.erdosRadoSunflower.{0}

/-- The upper bound in [Er64, equation (7)] follows by applying the fixed-petal
sunflower theorem [OAI26] to prime-exponent layers after fixing the small-prime valuations. -/
theorem erdos_535 : ∀ r ≥ 3, ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (f r N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ))) :=
  erdos_535_of_sunflower exponentialSunflower

/-- The case of three integers follows by specializing `erdos_535` to `r = 3`. -/
theorem erdos_535.variants.first_open_case : ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (f 3 N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ))) :=
  erdos_535 3 le_rfl

/-- The stronger conjecture in [Er73, equation (4.3)] follows from [OAI26] by adding
the full prime valuation to a second copy of each prime-exponent layer. -/
theorem erdos_535.variants.sunflower_strong {r : ℕ} (hr : 3 ≤ r) :
    ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k :=
  sunflower_strong_of_sunflower exponentialSunflower hr

end Erdos535
