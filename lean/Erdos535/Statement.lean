/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
https://www.apache.org/licenses/LICENSE-2.0
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
The three definitions from Formal Conjectures' `ErdosProblems/535.lean` at
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`.
The proof and type audit use the 4.34.1 toolchain of the OpenAI dependency.
-/

open ArithmeticFunction
open scoped Omega

namespace Erdos535

/-- No `r`-subset has constant pairwise GCD with coprime quotients. -/
def NoConstantPairwiseGcdCoprimeSubsets (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.card = r →
    ¬ (∃ d, 0 < d ∧ (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d) ∧
      ∀ a ∈ S, ∃ b, a = d * b ∧ Nat.gcd b d = 1)

/-- Every element is positive and has exactly `k` prime factors with multiplicity. -/
def AllBigOmega (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ Ω a = k

/-- Largest size of a subset of `[1,N]` avoiding constant pairwise GCDs. -/
noncomputable def f (r N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)) ∧
    A.card = k}

end Erdos535
