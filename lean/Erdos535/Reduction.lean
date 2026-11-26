import Erdos535.Strong
import Erdos535.UpperBound

open Filter Real
open scoped Classical

namespace Erdos535

/-- The universe-zero instance of OpenAI's `erdosRadoSunflower`, with its
implicit classical decision procedure for set intersection. -/
def ExponentialSunflowerStatement : Prop :=
  ∀ (r : ℕ) (_ : 3 ≤ r),
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (k : ℕ) (α : Type) (F : Finset (Finset α)),
      (∀ A ∈ F, A.card = k) → C ^ k < F.card →
      ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset α,
        ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K

private theorem uniform_of_sunflower (hs : ExponentialSunflowerStatement) {r : ℕ}
    (hr : 3 ≤ r) : ∃ C : ℕ, 1 ≤ C ∧ UniformBound r C := by
  obtain ⟨C, hC, h⟩ := hs r hr
  refine ⟨C, hC, ?_⟩
  intro k α inst F hsize hcard
  have heq : inst = Classical.decEq α := Subsingleton.elim _ _
  subst inst
  exact h k α F hsize hcard

theorem erdos_535_of_sunflower (hs : ExponentialSunflowerStatement) :
    ∀ r ≥ 3, ∃ c > (0 : ℝ),
      ∀ᶠ (N : ℕ) in atTop,
        (f r N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ))) := by
  intro r hr
  obtain ⟨C, hC, bound⟩ := uniform_of_sunflower hs hr
  exact upper_bound_of_uniform hr hC bound

theorem first_open_case_of_sunflower (hs : ExponentialSunflowerStatement) :
    ∃ c > (0 : ℝ),
      ∀ᶠ (N : ℕ) in atTop,
        (f 3 N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ))) :=
  erdos_535_of_sunflower hs 3 le_rfl

theorem sunflower_strong_of_sunflower (hs : ExponentialSunflowerStatement)
    {r : ℕ} (hr : 3 ≤ r) :
    ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k := by
  obtain ⟨C, hC, bound⟩ := uniform_of_sunflower hs hr
  exact sunflower_strong_of_uniform hr hC bound

end Erdos535
