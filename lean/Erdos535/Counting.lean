import Erdos535.Encoding

open Finset
open scoped BigOperators

namespace Erdos535

private def largeLayers (T n : ℕ) : Finset Layer :=
  (n.factorization.support.filter (T < ·)).sigma fun p => Icc 1 (n.factorization p)

private theorem mem_largeLayers (T n p j : ℕ) :
    (⟨p, j⟩ : Layer) ∈ largeLayers T n ↔
      T < p ∧ 1 ≤ j ∧ j ≤ n.factorization p := by
  rw [largeLayers, mem_sigma, mem_filter, mem_Icc, Finsupp.mem_support_iff]
  change ((n.factorization p ≠ 0 ∧ T < p) ∧ (1 ≤ j ∧ j ≤ n.factorization p)) ↔ _
  omega

theorem pow_card_largeLayers_le {T n : ℕ} (hn : n ≠ 0) :
    (T + 1) ^ (largeLayers T n).card ≤ n := by
  calc
    _ = (T + 1) ^ ∑ p ∈ n.factorization.support.filter (T < ·), n.factorization p := by
      simp [largeLayers, Finset.card_sigma, Nat.card_Icc]
    _ = ∏ p ∈ n.factorization.support.filter (T < ·), (T + 1) ^ n.factorization p := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ p ∈ n.factorization.support.filter (T < ·), p ^ n.factorization p :=
      Finset.prod_le_prod fun p hp => Nat.pow_le_pow_left (by
        exact Nat.succ_le_of_lt (mem_filter.mp hp).2) _
    _ ≤ ∏ p ∈ n.factorization.support, p ^ n.factorization p := by
      apply Finset.prod_le_prod_of_subset_of_one_le (filter_subset _ _)
      intro p hp _
      have hp' : p ∈ n.primeFactors := (Nat.support_factorization n) ▸ hp
      exact Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp').pos
    _ = n := Nat.prod_factorization_pow_eq_self hn

theorem two_pow_factorization_le {n : ℕ} (hn : n ≠ 0) (p : ℕ) :
    2 ^ n.factorization p ≤ n := by
  by_cases hp : p ∈ n.factorization.support
  · have hp' : p ∈ n.primeFactors := (Nat.support_factorization n) ▸ hp
    have hprime := Nat.prime_of_mem_primeFactors hp'
    exact (Nat.pow_le_pow_left hprime.two_le _).trans
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
        ((hprime.pow_dvd_iff_le_factorization hn).mpr le_rfl))
  · have hzero : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simpa [hzero] using Nat.one_le_iff_ne_zero.mpr hn

private def smallCode (T E n : ℕ) (p : Fin (T + 1)) : Fin (E + 1) :=
  ⟨min (n.factorization p) E, Nat.lt_succ_of_le (min_le_right _ _)⟩

private theorem factorization_eq_of_smallCode_eq {T E a b p : ℕ} (hp : p ≤ T)
    (ha : a.factorization p ≤ E) (hb : b.factorization p ≤ E)
    (h : smallCode T E a = smallCode T E b) :
    a.factorization p = b.factorization p := by
  have := congrArg (fun code : Fin (T + 1) → Fin (E + 1) =>
    (code ⟨p, Nat.lt_succ_of_le hp⟩).val) h
  simpa [smallCode, min_eq_left ha, min_eq_left hb] using this

private theorem layers_eq_of_codes_eq {T a b : ℕ}
    (hsmall : ∀ p ≤ T, a.factorization p = b.factorization p)
    (hlarge : largeLayers T a = largeLayers T b) :
    layers a = layers b := by
  apply Finset.ext
  rintro ⟨p, j⟩
  by_cases hp : p ≤ T
  · simp only [mem_layers, hsmall p hp]
  · have hh := congrArg (fun S : Finset Layer => (⟨p, j⟩ : Layer) ∈ S) hlarge
    simpa only [mem_largeLayers, Nat.lt_of_not_ge hp, true_and, mem_layers, eq_iff_iff] using hh

private theorem gcd_eq_of_large_inter_eq {T a b c d : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hsmall₁ : ∀ p ≤ T, a.factorization p = c.factorization p)
    (hsmall₂ : ∀ p ≤ T, b.factorization p = d.factorization p)
    (hlarge : largeLayers T a ∩ largeLayers T b = largeLayers T c ∩ largeLayers T d) :
    a.gcd b = c.gcd d := by
  apply layers_injOn (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hc)
  rw [← layers_inter ha hb, ← layers_inter hc hd]
  apply Finset.ext
  rintro ⟨p, j⟩
  by_cases hp : p ≤ T
  · simp only [mem_inter, mem_layers, hsmall₁ p hp, hsmall₂ p hp]
  · have hh := congrArg (fun S : Finset Layer => (⟨p, j⟩ : Layer) ∈ S) hlarge
    simpa only [mem_inter, mem_largeLayers, Nat.lt_of_not_ge hp, true_and, mem_layers,
      eq_iff_iff] using hh

/-- Count the possible small-prime codes and large-layer sizes, then use the uniform bound
on each fiber. -/
theorem card_le_of_layers_bounds {r C T E K : ℕ} (hr : 3 ≤ r) (hC : 1 ≤ C)
    (bound : UniformBound r C) (A : Finset ℕ)
    (hpos : ∀ a ∈ A, a ≠ 0)
    (hexp : ∀ a ∈ A, ∀ p, a.factorization p ≤ E)
    (hlarge : ∀ a ∈ A, (largeLayers T a).card ≤ K)
    (hfree : ∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => a.gcd b = d)) :
    A.card ≤ ((E + 1) ^ (T + 1) * (K + 1)) * C ^ K := by
  let bin (n : ℕ) := (smallCode T E n, (largeLayers T n).card)
  let bins : Finset ((Fin (T + 1) → Fin (E + 1)) × ℕ) :=
    univ ×ˢ range (K + 1)
  have hbcard : bins.card = (E + 1) ^ (T + 1) * (K + 1) := by
    simp [bins]
  rw [← hbcard]
  apply card_le_mul_of_fibers bin bins (C ^ K)
  · intro a ha
    exact mem_product.mpr ⟨mem_univ _, mem_range.mpr (Nat.lt_succ_of_le (hlarge a ha))⟩
  · rintro ⟨code, j⟩ hj
    let fiber := A.filter fun a => bin a = (code, j)
    have hjK : j ≤ K := Nat.lt_succ_iff.mp (mem_range.mp (mem_product.mp hj).2)
    have haA : ∀ a ∈ fiber, a ∈ A := fun _ h => (mem_filter.mp h).1
    have hbin : ∀ a ∈ fiber, bin a = (code, j) := fun _ h => (mem_filter.mp h).2
    have hsmall : ∀ a ∈ fiber, ∀ b ∈ fiber, ∀ p ≤ T,
        a.factorization p = b.factorization p := by
      intro a ha b hb p hp
      exact factorization_eq_of_smallCode_eq hp (hexp a (haA a ha) p) (hexp b (haA b hb) p)
        (congrArg Prod.fst ((hbin a ha).trans (hbin b hb).symm))
    have hinj : Set.InjOn (largeLayers T) fiber := by
      intro a ha b hb heq
      exact layers_injOn (hpos a (haA a ha)) (hpos b (haA b hb))
        (layers_eq_of_codes_eq (hsmall a ha b hb) heq)
    have hc : fiber.card ≤ C ^ j := by
      by_contra! hcard
      obtain ⟨S, hS, hScard, core, hcore⟩ :=
        sunflower_in_image bound fiber (largeLayers T) hinj
          (fun a ha => congrArg Prod.snd (hbin a ha)) hcard
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
      have nz : ∀ a ∈ S, a ≠ 0 := fun a ha => hpos a (haA a (hS ha))
      apply hfree S (hS.trans (filter_subset _ _)) hScard
      refine ⟨a.gcd b, ?_⟩
      intro x hx y hy hxy
      exact gcd_eq_of_large_inter_eq (nz x hx) (nz y hy) (nz a ha) (nz b hb)
        (hsmall x (hS hx) a (hS ha)) (hsmall y (hS hy) b (hS hb))
        ((hcore x hx y hy hxy).trans (hcore a ha b hb hab).symm)
    exact hc.trans (Nat.pow_le_pow_right (by omega) hjK)

theorem f_le_of_power_bounds {r C N T E K : ℕ} (hr : 3 ≤ r) (hC : 1 ≤ C)
    (bound : UniformBound r C) (hE : ∀ j, 2 ^ j ≤ N → j ≤ E)
    (hK : ∀ j, (T + 1) ^ j ≤ N → j ≤ K) :
    f r N ≤ ((E + 1) ^ (T + 1) * (K + 1)) * C ^ K := by
  unfold f
  apply csSup_le
  · refine ⟨0, ∅, empty_subset _, ?_, rfl⟩
    intro S hS hc
    have hcard := Finset.card_le_card hS
    simp only [card_empty] at hcard
    omega
  · rintro k ⟨A, hA, hfree, rfl⟩
    have hn : ∀ a ∈ A, a ≠ 0 := fun a ha => Nat.ne_of_gt ((mem_Icc.mp (hA ha)).1)
    exact card_le_of_layers_bounds hr hC bound A hn
      (fun a ha p => hE _ ((two_pow_factorization_le (hn a ha) p).trans (mem_Icc.mp (hA ha)).2))
      (fun a ha => hK _ ((pow_card_largeLayers_le (hn a ha)).trans (mem_Icc.mp (hA ha)).2))
      hfree

end Erdos535
