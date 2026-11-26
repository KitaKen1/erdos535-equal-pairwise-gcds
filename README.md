# Erdős 535 — An upper bound for sets avoiding equal pairwise GCDs

Erdős Problem #535 asks how large a subset of $\{1,\ldots,N\}$ can be if it has no $r$ distinct elements whose pairwise greatest common divisors are all equal. Formal Conjectures (FC) records three open declarations about this problem. [Problem statement](https://www.erdosproblems.com/535) · [FC statements](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/535.lean#L75-L125)

> [!NOTE]
> **1. The upper bound for general $r$.** For every fixed $r\ge3$, is there a constant $c_r>0$ such that, for all sufficiently large $N$, every subset of $\{1,\ldots,N\}$ avoiding $r$ distinct elements with equal pairwise GCDs has size at most $N^{c_r/\log\log N}$?

> [!NOTE]
> **2. The case $r=3$.** Is there a constant $c>0$ such that, for all sufficiently large $N$, every subset of $\{1,\ldots,N\}$ avoiding three distinct elements with equal pairwise GCDs has size at most $N^{c/\log\log N}$?

> [!NOTE]
> **3. The strong integer sunflower conjecture.** Fix $r\ge3$. Let $A$ be a finite set of positive integers, each with exactly $k$ prime factors counted with multiplicity. Suppose $A$ contains no $r$ distinct elements whose pairwise GCDs all equal $d$ and whose quotients $a/d$ are all coprime to $d$. Does there exist a constant $C_r>0$, depending only on $r$, such that $|A|\le C_r^k$ for every $k$ and every such $A$?

This repository proves **all three bounds** in Lean using OpenAI's fixed-petal exponential sunflower theorem. [Lean theorems](lean/Erdos535.lean#L19-L40)

### Prior work

| FC case | Prior work and contribution |
| --- | --- |
| **1. General $r$** | **Known reduction formalized here.** Erdős sketched the implication. The prime-power layer reduction of Sunder, Kumrawat, and Cheri gives the bound using OpenAI's result that more than $C_r^k$ distinct $k$-sets force an $r$-sunflower. [Erdős (1964), eq. (7)](https://users.renyi.hu/~p_erdos/1964-10.pdf#page=2) · [Sunder et al. (2026)](https://www.erdosproblems.com/forum/thread/535?order=newest) · [OpenAI Lean theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Sunflower/FixedBase.lean#L39-L45) |
| **2. The case $r=3$** | **Known special case formalized here.** By OpenAI's bound, more than $C_3^k$ distinct large-prime layer sets of size $k$ force three with equal pairwise intersections. Fixed small-prime valuations then give equal pairwise GCDs. [Erdős (1973), eq. (4.1)](https://www.renyi.hu/~p_erdos/1973-21.pdf#page=7) · [OpenAI Lean theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Sunflower/FixedBase.lean#L39-L45) |
| **3. Strong integer sunflower** | **Additional reduction proved here.** Tagging a second copy of each prime-power layer with its full valuation lets OpenAI's $C_r^{2k}$ sunflower bound force Erdős's coprime quotients. Priority for this reduction remains unverified. [Erdős (1973), eq. (4.3)](https://www.renyi.hu/~p_erdos/1973-21.pdf#page=7) · [OpenAI Lean theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Sunflower/FixedBase.lean#L39-L45) · [Tagged reduction in Lean](lean/Erdos535/Strong.lean#L9-L15) |

### Exact Formal Conjectures targets

The verifier extracts the three types and their definitions from the pinned FC source. Lean checks each type by `rfl`. The proof below uses `exponentialSunflower`, the universe-zero instance of OpenAI's `erdosRadoSunflower`. [Pinned FC source](verification/reference/535.lean.txt) · [Type-check generator](verification/check_against_fc.py) · [Upstream Lean theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Sunflower/FixedBase.lean#L35-L45)

```lean
theorem erdos_535 : ∀ r ≥ 3, ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (f r N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ))) :=
  erdos_535_of_sunflower exponentialSunflower

theorem erdos_535.variants.first_open_case : ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (f 3 N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ))) :=
  erdos_535 3 le_rfl

theorem erdos_535.variants.sunflower_strong {r : ℕ} (hr : 3 ≤ r) :
    ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k :=
  sunflower_strong_of_sunflower exponentialSunflower hr
```

### Mathematical Explanation (AI generated)

**1. Encode GCDs by intersections.** For a positive integer $a$, let $S(a)=\{(p,j):1\le j\le v_p(a)\}$, where $p$ runs over primes. The set determines $a$ uniquely. Since a GCD takes the minimum valuation at each prime,

```math
S(a)\cap S(b)=S(\gcd(a,b)).
```

Thus a sunflower of encoded sets gives integers with the same pairwise GCD. [Lean encoding](lean/Erdos535/Encoding.lean)

**2. Fix the small-prime valuations.** Write $L=\log N$ and group the integers by their valuations at primes up to $\lfloor\sqrt L\rfloor$ and by the number of remaining layers. The small-prime valuations have $\exp(O(\sqrt L\log L))$ possible patterns. For $a\le N$, the remaining part has at most $2L/\log L$ layers, since each of those primes exceeds $\sqrt L$. Within each group the remaining sets all have the same size $k$. Applying the fixed-petal sunflower theorem with base $C_r$ gives at most $C_r^k$ members in each group. Summing over the groups yields

```math
\log f_r(N)=O_r(L/\log L),
```

where $f_r(N)$ denotes the largest size of a set avoiding the required $r$ integers. This gives the conjectured exponent for every $r\ge3$. [Erdős (1964), equation (7)](https://users.renyi.hu/~p_erdos/1964-10.pdf#page=2) · [Finite counting](lean/Erdos535/Counting.lean) · [Asymptotic bound](lean/Erdos535/UpperBound.lean)

**3. Tag the layers to get coprime quotients.** Add a second copy of every layer tagged with its prime's full valuation in $a$. Each encoded set now has exactly $2k$ elements. In a sunflower of these sets, the ordinary layers give a common pairwise GCD $g$. Suppose a prime occurs in $g$ with exponent $e>0$ and in one member with exponent greater than $e$. Two other members must both have exponent $e$, because their GCD with the first has exponent $e$. Their intersection contains the tag $e$ for that prime, whereas an intersection with the first member lacks that tag. This contradicts the sunflower property. Hence every quotient $a/g$ is coprime to $g$, and a family avoiding such $r$ members has size at most $(C_r^2)^k$. [Erdős (1973), equation (4.3)](https://www.renyi.hu/~p_erdos/1973-21.pdf#page=7) · [Lean proof](lean/Erdos535/Strong.lean)

## Appendix: Timeline

| Year | Result |
| --- | --- |
| 1964 | Erdős proved an upper bound with exponent $3/4+o(1)$ and showed how an exponential sunflower bound would give the conjectured order of the exponent. [Paper, pp. 644–646](https://users.renyi.hu/~p_erdos/1964-10.pdf) |
| 1970 | Abbott and Hanson improved the upper-bound exponent to $1/2+o(1)$. [Paper](https://doi.org/10.1112/blms/2.3.324) |
| 1973 | Erdős formulated the integer sunflower conjecture with prime factors counted with multiplicity and quotients coprime to the common GCD. [Equation (4.3)](https://www.renyi.hu/~p_erdos/1973-21.pdf#page=7) |
| 2026 | OpenAI released a fixed-petal exponential bound for sunflowers and Lean source for the uniform-family theorem used here. [Preprint and formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/An-exponential-bound-for-sunflowers-November-24-2026/README.md) |
| 2026 | **This repo** proves all three Formal Conjectures bounds for Erdős #535 in Lean. [Lean theorems](lean/Erdos535.lean#L19-L40) · [Type and axiom audit](verification/logs/full-audit-lean-4.34.1.txt) |

## Appendix: Verification by Lean Comparator on GitHub CI runner

On pushes and pull requests, GitHub Actions builds the pinned OpenAI sunflower theorem and checks all three unconditional declarations. Lean Comparator compares statement-only exports against a challenge generated from the pinned FC source. Lean checks that each proof has the exact FC type, and `#print axioms` enforces the allowlist of `propext`, `Classical.choice`, and `Quot.sound`. `leanchecker` replays this repository's compiled declarations using the pinned imports. [GitHub workflow](.github/workflows/lean.yml) · [Comparator check](verification/Compare.lean)

Up to 12 runners build modules whose imports are already cached. The final build merges their outputs and gives the remaining dependencies a longer build window. If a runner stops, the next runner resumes from the saved cache. The workflow requires the reduction audit, the Comparator check, and proof replay for all three unconditional declarations. [Parallel build](.github/workflows/frontier.yml) · [Final audit](.github/workflows/comparator.yml)

### Certification within 90 days

Each runner uploads `comparator-audit-<run-id>-<attempt>-<stage>` with its build and verification logs. The separate reduction job uploads `reduction-audit-<run-id>-<attempt>`. GitHub retains these artifacts for 90 days. [GitHub Actions runs](https://github.com/KitaKen1/erdos535-equal-pairwise-gcds/actions/workflows/lean.yml)

The checked-in local audit passed on Lean 4.34.1. It compiled some upstream modules in batches to reuse imports, with name and tactic adjustments for the combined scopes. [Local type and axiom audit](verification/logs/full-audit-lean-4.34.1.txt) · [Local reduction audit](verification/logs/reduction-lean-4.34.1.txt)

### Reproduce the verification

With elan installed, build Comparator and its exporter at commit `fd5d5bc` using `lake +leanprover/lean4:v4.34.1 build Comparator lean4export`. Then run the following from the `lean/` directory of OpenAI's checkout at `3344da5`. The first full run builds the sunflower theorem's dependencies. [Pinned Comparator](https://github.com/leanprover/comparator/tree/fd5d5bcf14177b187f66d4502071268d877887c3) · [Pinned OpenAI checkout](https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean)

```sh
lake update
lake exe cache get Mathlib
lake build +OAI.Combinatorics.Sunflower.FixedBase:olean
lake env bash /path/to/erdos535/verification/verify.sh --comparator /path/to/comparator
```

To verify the reduction with the sunflower theorem supplied as an explicit argument, run from this repository's root.

```sh
cd lean
lake exe cache get Mathlib
lake env bash ../verification/verify.sh --reduction
```

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from OpenAI Codex using GPT-6.2 Astra.
