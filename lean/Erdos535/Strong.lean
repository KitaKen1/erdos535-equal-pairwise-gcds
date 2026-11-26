import Erdos535.Encoding

open Finset
open ArithmeticFunction
open scoped Omega

namespace Erdos535

/- Each ordinary layer has a tagged copy carrying the full valuation of its prime.
   The ordinary layers force equal GCDs. The tags force equal valuations on the core. -/
private def taggedLayers (n : ℕ) : Finset (Layer × ℕ) :=
  (layers n).image fun x => (x, n.factorization x.1)

private def strongCode (n : ℕ) : Finset (Layer ⊕ (Layer × ℕ)) :=
  (layers n).disjSum (taggedLayers n)

private theorem inl_mem_strongCode {x : Layer} {n : ℕ} :
    Sum.inl x ∈ strongCode n ↔ x ∈ layers n := by simp [strongCode]

private theorem tag_mem_strongCode {n p j e : ℕ} :
    Sum.inr ((⟨p, j⟩ : Layer), e) ∈ strongCode n ↔
      1 ≤ j ∧ j ≤ n.factorization p ∧ n.factorization p = e := by
  rw [strongCode, inr_mem_disjSum, taggedLayers, mem_image]
  constructor
  · rintro ⟨x, hx, heq⟩
    have hx' : x = (⟨p, j⟩ : Layer) := congrArg Prod.fst heq
    subst x
    exact ⟨(mem_layers _ _ _).mp hx |>.1, (mem_layers _ _ _).mp hx |>.2,
      congrArg Prod.snd heq⟩
  · rintro ⟨hj, hv, rfl⟩
    exact ⟨⟨p, j⟩, (mem_layers _ _ _).mpr ⟨hj, hv⟩, rfl⟩

private theorem card_strongCode (n : ℕ) : (strongCode n).card = 2 * Ω n := by
  have hc : (taggedLayers n).card = (layers n).card :=
    card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
  rw [strongCode, card_disjSum, hc, card_layers, two_mul]

private theorem strongCode_injOn : Set.InjOn strongCode {n | n ≠ 0} := by
  intro a ha b hb h
  apply layers_injOn ha hb
  apply Finset.ext
  intro x
  rw [← inl_mem_strongCode, h, inl_mem_strongCode]

private theorem gcd_eq_of_strongCode_inter_eq {a b c d : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : strongCode a ∩ strongCode b = strongCode c ∩ strongCode d) :
    a.gcd b = c.gcd d := by
  apply layers_injOn (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hc)
  rw [← layers_inter ha hb, ← layers_inter hc hd]
  apply Finset.ext
  intro x
  have hx := congrArg (fun S : Finset (Layer ⊕ (Layer × ℕ)) => Sum.inl x ∈ S) h
  simpa only [mem_inter, inl_mem_strongCode, eq_iff_iff] using hx

private theorem coprime_quotient_of_core {a b c d : ℕ} {K : Finset (Layer ⊕ (Layer × ℕ))}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : 0 < d)
    (hab : a.gcd b = d) (hac : a.gcd c = d)
    (hAB : strongCode a ∩ strongCode b = K)
    (hBC : strongCode b ∩ strongCode c = K) :
    a = d * (a / d) ∧ (a / d).gcd d = 1 := by
  have hda : d ∣ a := hab ▸ Nat.gcd_dvd_left a b
  refine ⟨(Nat.mul_div_cancel' hda).symm, ?_⟩
  by_contra hn
  obtain ⟨p, hp, hpGcd⟩ := Nat.exists_prime_and_dvd hn
  have hpd : p ∣ d := hpGcd.trans (Nat.gcd_dvd_right _ _)
  have hpq : p ∣ a / d := hpGcd.trans (Nat.gcd_dvd_left _ _)
  have hq : a / d ≠ 0 := by
    intro h
    have := Nat.mul_div_cancel' hda
    rw [h, mul_zero] at this
    exact ha this.symm
  have hdp : 1 ≤ d.factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization hd.ne', pow_one]
    exact hpd
  have hqp : 1 ≤ (a / d).factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization hq, pow_one]
    exact hpq
  have hgt : d.factorization p < a.factorization p := by
    rw [Nat.factorization_div hda, Finsupp.tsub_apply] at hqp
    omega
  have hbEq : b.factorization p = d.factorization p := by
    have heq := congrArg (fun n : ℕ => n.factorization p) hab
    simp only [Nat.factorization_gcd ha hb, Finsupp.inf_apply] at heq
    change min (a.factorization p) (b.factorization p) = d.factorization p at heq
    omega
  have hcEq : c.factorization p = d.factorization p := by
    have heq := congrArg (fun n : ℕ => n.factorization p) hac
    simp only [Nat.factorization_gcd ha hc, Finsupp.inf_apply] at heq
    change min (a.factorization p) (c.factorization p) = d.factorization p at heq
    omega
  let tag : Layer ⊕ (Layer × ℕ) := Sum.inr (⟨p, 1⟩, d.factorization p)
  have htag : tag ∈ strongCode b ∩ strongCode c := by
    exact mem_inter.mpr ⟨tag_mem_strongCode.mpr ⟨le_rfl, hbEq.symm ▸ hdp, hbEq⟩,
      tag_mem_strongCode.mpr ⟨le_rfl, hcEq.symm ▸ hdp, hcEq⟩⟩
  rw [hBC, ← hAB] at htag
  exact hgt.ne' (tag_mem_strongCode.mp (mem_inter.mp htag).1).2.2

theorem sunflower_strong_of_uniform {r C : ℕ} (hr : 3 ≤ r) (hC : 1 ≤ C)
    (bound : UniformBound r C) :
    ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k := by
  refine ⟨(C : ℝ) ^ 2, pow_pos (by exact_mod_cast (by omega : 0 < C)) _, ?_⟩
  intro k A hA hfree
  rw [← pow_mul, ← Nat.cast_pow]
  exact_mod_cast (show A.card ≤ C ^ (2 * k) from by
    by_contra! hcard
    have hpos : ∀ a ∈ A, a ≠ 0 := fun a ha => Nat.ne_of_gt ((hA a ha).1)
    obtain ⟨S, hS, hsCard, K, hk⟩ :=
      sunflower_in_image bound A strongCode (strongCode_injOn.mono hpos)
        (fun a ha => by rw [card_strongCode, (hA a ha).2]) hcard
    have hsPos : ∀ a ∈ S, a ≠ 0 := fun a ha => hpos a (hS ha)
    have hh : 1 < S.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hh
    let d := a.gcd b
    have hd : 0 < d := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (hsPos a ha))
    have hpair : (S : Set ℕ).Pairwise (fun x y => x.gcd y = d) := by
      intro x hx y hy hxy
      exact gcd_eq_of_strongCode_inter_eq (hsPos x hx) (hsPos y hy) (hsPos a ha) (hsPos b hb)
        ((hk x hx y hy hxy).trans (hk a ha b hb hab).symm)
    apply hfree S hS hsCard
    refine ⟨d, hd, hpair, ?_⟩
    intro x hx
    have herase : 1 < (S.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
    obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp herase
    obtain ⟨hyx, hyS⟩ := mem_erase.mp hy
    obtain ⟨hzx, hzS⟩ := mem_erase.mp hz
    exact ⟨x / d, coprime_quotient_of_core (hsPos x hx) (hsPos y hyS) (hsPos z hzS) hd
      (hpair hx hyS hyx.symm) (hpair hx hzS hzx.symm)
      (hk x hx y hyS hyx.symm) (hk y hyS z hzS hyz)⟩)

end Erdos535
