import Erdos535.Statement
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Sum

open Finset
open ArithmeticFunction
open scoped Omega

namespace Erdos535

abbrev Layer := Σ _ : ℕ, ℕ

/-- Each prime contributes one element for each positive exponent up to its valuation. -/
def layers (n : ℕ) : Finset Layer :=
  n.factorization.support.sigma fun p => Icc 1 (n.factorization p)

@[simp] theorem mem_layers (n p j : ℕ) :
    (⟨p, j⟩ : Layer) ∈ layers n ↔ 1 ≤ j ∧ j ≤ n.factorization p := by
  rw [layers, mem_sigma, mem_Icc, Finsupp.mem_support_iff]
  change (n.factorization p ≠ 0 ∧ 1 ≤ j ∧ j ≤ n.factorization p) ↔
    1 ≤ j ∧ j ≤ n.factorization p
  omega

theorem layers_inter {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    layers a ∩ layers b = layers (a.gcd b) := by
  apply Finset.ext
  rintro ⟨p, j⟩
  simp only [mem_inter, mem_layers, Nat.factorization_gcd ha hb, Finsupp.inf_apply, le_inf_iff]
  tauto

theorem layers_injOn : Set.InjOn layers {n | n ≠ 0} := by
  intro a ha b hb h
  apply Nat.factorization_inj ha hb
  ext p
  have le_of_layers_eq (x y : ℕ) (heq : layers x = layers y) :
      x.factorization p ≤ y.factorization p := by
    by_cases hx : x.factorization p = 0
    · simp [hx]
    · have hm := (mem_layers x p (x.factorization p)).2 ⟨by omega, le_rfl⟩
      rw [heq] at hm
      exact ((mem_layers _ _ _).1 hm).2
  exact le_antisymm (le_of_layers_eq a b h) (le_of_layers_eq b a h.symm)

@[simp] theorem card_layers (n : ℕ) : (layers n).card = Ω n := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
  simp [layers, Finset.card_sigma, Finsupp.sum, Nat.card_Icc]

/-- Uniform sunflower bounds as supplied by the OpenAI theorem. -/
def UniformBound (r C : ℕ) : Prop :=
  ∀ (k : ℕ) (α : Type) [DecidableEq α] (F : Finset (Finset α)),
    (∀ A ∈ F, A.card = k) → C ^ k < F.card →
    ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset α,
      ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K

/-- Bound a finite set by the number of bins times the largest fiber. -/
theorem card_le_mul_of_fibers {α β : Type*} [DecidableEq β] {A : Finset α}
    (g : α → β) (B : Finset β) (M : ℕ) (hmap : ∀ a ∈ A, g a ∈ B)
    (hbound : ∀ b ∈ B, (A.filter fun a => g a = b).card ≤ M) :
    A.card ≤ B.card * M := by
  calc
    A.card = ∑ b ∈ B, (A.filter fun a => g a = b).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _b ∈ B, M := Finset.sum_le_sum hbound
    _ = B.card * M := by simp

/-- Pull back the sunflower selected from an injective image. -/
theorem sunflower_in_image {α : Type} [DecidableEq α] {r C k : ℕ}
    (bound : UniformBound r C) (A : Finset ℕ) (encode : ℕ → Finset α)
    (hinj : Set.InjOn encode A) (hsize : ∀ a ∈ A, (encode a).card = k)
    (h : C ^ k < A.card) :
    ∃ S ⊆ A, S.card = r ∧ ∃ K : Finset α,
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → encode a ∩ encode b = K := by
  have imageCard := Finset.card_image_of_injOn hinj
  obtain ⟨G, hG, hcard, K, hK⟩ :=
    bound k α (A.image encode)
      (by simpa only [Finset.forall_mem_image] using hsize) (by rwa [imageCard])
  let S := A.filter fun a => encode a ∈ G
  have hs : S ⊆ A := filter_subset _ _
  have himage : S.image encode = G := by
    apply Finset.Subset.antisymm
    · simp [S, image_subset_iff]
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := mem_image.mp (hG hy)
      exact mem_image_of_mem encode (mem_filter.mpr ⟨ha, hy⟩)
  refine ⟨S, hs, ?_, K, ?_⟩
  · rw [← hcard, ← himage, card_image_of_injOn (hinj.mono hs)]
  · intro a ha b hb hab
    exact hK _ (mem_filter.mp ha).2 _ (mem_filter.mp hb).2
      (fun heq => hab (hinj (hs ha) (hs hb) heq))

end Erdos535
