import Erdos535.Counting

open Filter Real

namespace Erdos535

private theorem eventually_log_le_fourthRoot :
    ∀ᶠ x : ℝ in atTop, log x ≤ x ^ (1 / 4 : ℝ) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 4 : ℝ))).bound
    (show 0 < (1 : ℝ) by norm_num)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx h₁
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h₁),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _), one_mul] using hx

private theorem exponent_le_of_pow_le {B j N : ℕ} (hB : 0 < B) (h : B ^ j ≤ N) :
    (j : ℝ) * log (B : ℝ) ≤ log (N : ℝ) := by
  have hB' : 0 < (B : ℝ) := by exact_mod_cast hB
  have hp : (B : ℝ) ^ j ≤ (N : ℝ) := by exact_mod_cast h
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos hB' j) hp

theorem upper_bound_of_uniform {r C : ℕ} (hr : 3 ≤ r) (hC : 1 ≤ C)
    (bound : UniformBound r C) :
    ∃ c > (0 : ℝ), ∀ᶠ (N : ℕ) in atTop,
      (f r N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ))) := by
  have hCReal : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hlogC : 0 ≤ log (C : ℝ) := Real.log_nonneg hCReal
  have hCPos : 0 < (C : ℝ) := by linarith
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨8 + 2 * log (C : ℝ), by linarith, ?_⟩
  have hL : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hL.eventually (eventually_ge_atTop (2 : ℝ)),
    hL.eventually (eventually_ge_atTop (1 / log (2 : ℝ))),
    hL.eventually eventually_log_le_fourthRoot, eventually_ge_atTop (1 : ℕ)] with
    N hL₂ hL₂' hroot hN
  set L : ℝ := log (N : ℝ)
  let T := ⌊sqrt L⌋₊
  let E := ⌊L ^ 2⌋₊
  let K := ⌊2 * L / log L⌋₊
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hLpos : 0 < L := by linarith
  have hLnonneg : 0 ≤ L := hLpos.le
  have hlogL : 0 < log L := log_pos (by linarith)
  have hLs : 1 ≤ sqrt L := (Real.one_le_sqrt).2 (by linarith)
  have hT_lower : sqrt L ≤ (T : ℝ) + 1 := (Nat.lt_floor_add_one (sqrt L)).le
  have hT_upper : (T : ℝ) + 1 ≤ 2 * sqrt L := by
    have h := Nat.floor_le (Real.sqrt_nonneg L)
    change (T : ℝ) ≤ sqrt L at h
    linarith
  have hlogT : log L / 2 ≤ log ((T : ℝ) + 1) := by
    rw [← Real.log_sqrt hLnonneg]
    exact Real.log_le_log (by linarith) hT_lower
  have hE : ∀ j, 2 ^ j ≤ N → j ≤ E := by
    intro j hj
    have h₁ : (j : ℝ) * log 2 ≤ L := exponent_le_of_pow_le (by decide) hj
    have h₂ : 1 ≤ L * log 2 := (div_le_iff₀ hlog2).mp hL₂'
    apply Nat.le_floor
    apply (le_of_mul_le_mul_right _ hlog2)
    calc
      (j : ℝ) * log 2 ≤ L := h₁
      _ = L * 1 := by ring
      _ ≤ L * (L * log 2) := mul_le_mul_of_nonneg_left h₂ hLnonneg
      _ = L ^ 2 * log 2 := by ring
  have hK : ∀ j, (T + 1) ^ j ≤ N → j ≤ K := by
    intro j hj
    have h₁ := exponent_le_of_pow_le (Nat.succ_pos T) hj
    push_cast at h₁
    have h₂ := (mul_le_mul_of_nonneg_left hlogT (by positivity : 0 ≤ (j : ℝ))).trans h₁
    apply Nat.le_floor
    apply (le_div_iff₀ hlogL).2
    linarith
  have hf := f_le_of_power_bounds hr hC bound hE hK
  have hf' : (f r N : ℝ) ≤ (((E : ℝ) + 1) ^ (T + 1) * ((K : ℝ) + 1)) * (C : ℝ) ^ K := by
    exact_mod_cast hf
  have hE_le : (E : ℝ) ≤ L ^ 2 := Nat.floor_le (sq_nonneg L)
  have hlogE : log ((E : ℝ) + 1) ≤ 3 * log L := by
    have hb : (E : ℝ) + 1 ≤ L ^ 3 := by nlinarith [mul_nonneg (show 0 ≤ L - 2 by linarith) (sq_nonneg L)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by positivity) hb
  have hElog₀ : 0 ≤ log ((E : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) E])
  have hsq : (log L) ^ 2 ≤ sqrt L := by
    calc
      (log L) ^ 2 ≤ (L ^ (1 / 4 : ℝ)) ^ 2 := by gcongr
      _ = sqrt L := by
        rw [pow_two, ← Real.rpow_add hLpos, Real.sqrt_eq_rpow]
        norm_num
  have hsmall : ((T : ℝ) + 1) * log ((E : ℝ) + 1) ≤ 6 * L / log L := by
    apply (le_div_iff₀ hlogL).2
    calc
      _ ≤ (2 * sqrt L * (3 * log L)) * log L := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hT_upper hlogE hElog₀ (by positivity)) hlogL.le
      _ = 6 * (sqrt L * (log L) ^ 2) := by ring
      _ ≤ 6 * (sqrt L * sqrt L) := by gcongr
      _ = 6 * L := by rw [← pow_two, Real.sq_sqrt hLnonneg]
  have hK_le : (K : ℝ) ≤ 2 * L / log L := Nat.floor_le (by positivity)
  have hKlog : log ((K : ℝ) + 1) ≤ (K : ℝ) := by
    simpa using Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < (K : ℝ) + 1 by positivity)
  refine hf'.trans ((Real.log_le_log_iff (by positivity)
    (Real.rpow_pos_of_pos hNpos _)).mp ?_)
  rw [Real.log_rpow hNpos, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  change ((T : ℝ) + 1) * log ((E : ℝ) + 1) + log ((K : ℝ) + 1) +
    (K : ℝ) * log (C : ℝ) ≤ ((8 + 2 * log (C : ℝ)) / log L) * L
  calc
    _ ≤ 6 * L / log L + (K : ℝ) + (K : ℝ) * log (C : ℝ) :=
      add_le_add (add_le_add hsmall hKlog) le_rfl
    _ = 6 * L / log L + (K : ℝ) * (1 + log (C : ℝ)) := by ring
    _ ≤ 6 * L / log L + 2 * L / log L * (1 + log (C : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hK_le
        (show 0 ≤ 1 + log (C : ℝ) by linarith))
    _ = _ := by ring

end Erdos535
