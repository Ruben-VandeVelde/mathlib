/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
import topology.instances.nnreal
import data.nat.log

/-!
# Square root of a real number

In this file we define

* `nnreal.sqrt` to be the square root of a nonnegative real number.
* `real.sqrt` to be the square root of a real number, defined to be zero on negative numbers.

Then we prove some basic properties of these functions.

## Implementation notes

We define `nnreal.sqrt` as the noncomputable inverse to the function `x ↦ x * x`. We use general
theory of inverses of strictly monotone functions to prove that `nnreal.sqrt x` exists. As a side
effect, `nnreal.sqrt` is a bundled `order_iso`, so for `nnreal` numbers we get continuity as well as
theorems like `sqrt x ≤ y ↔ x * x ≤ y` for free.

Then we define `real.sqrt x` to be `nnreal.sqrt (nnreal.of_real x)`. We also define a Cauchy
sequence `real.sqrt_aux (f : cau_seq ℚ abs)` which converges to `sqrt (mk f)` but do not prove (yet)
that this sequence actually converges to `sqrt (mk f)`.

## Tags

square root
-/

open set filter
open_locale filter nnreal topological_space

namespace nnreal

variables {x y : ℝ≥0}

/-- Square root of a nonnegative real number. -/
@[pp_nodot] noncomputable def sqrt : ℝ≥0 ≃o ℝ≥0 :=
order_iso.symm $ strict_mono.order_iso_of_surjective (λ x, x * x)
  (λ x y h, mul_self_lt_mul_self x.2 h) $
  surjective_of_continuous (continuous_id.mul continuous_id) tendsto_mul_self_at_top
    (by simp [order_bot.at_bot_eq])

lemma sqrt_eq_iff_sqr_eq : sqrt x = y ↔ y * y = x :=
sqrt.to_equiv.apply_eq_iff_eq_symm_apply.trans eq_comm

lemma sqrt_le_iff : sqrt x ≤ y ↔ x ≤ y * y :=
sqrt.to_galois_connection _ _

lemma le_sqrt_iff : x ≤ sqrt y ↔ x * x ≤ y :=
(sqrt.symm.to_galois_connection _ _).symm

@[simp] lemma sqrt_eq_zero : sqrt x = 0 ↔ x = 0 :=
sqrt_eq_iff_sqr_eq.trans $ by rw [eq_comm, zero_mul]

@[simp] lemma sqrt_zero : sqrt 0 = 0 := sqrt_eq_zero.2 rfl

@[simp] lemma sqrt_one : sqrt 1 = 1 := sqrt_eq_iff_sqr_eq.2 $ mul_one 1

@[simp] lemma mul_sqrt_self (x : ℝ≥0) : sqrt x * sqrt x = x :=
sqrt.symm_apply_apply x

@[simp] lemma sqrt_mul_self (x : ℝ≥0) : sqrt (x * x) = x := sqrt.apply_symm_apply x

lemma sqrt_mul (x y : ℝ≥0) : sqrt (x * y) = sqrt x * sqrt y :=
by rw [sqrt_eq_iff_sqr_eq, mul_mul_mul_comm, mul_sqrt_self, mul_sqrt_self]

/-- `nnreal.sqrt` as a `monoid_with_zero_hom`. -/
noncomputable def sqrt_hom : monoid_with_zero_hom ℝ≥0 ℝ≥0 := ⟨sqrt, sqrt_zero, sqrt_one, sqrt_mul⟩

lemma sqrt_inv (x : ℝ≥0) : sqrt (x⁻¹) = (sqrt x)⁻¹ := sqrt_hom.map_inv' x

lemma sqrt_div (x y : ℝ≥0) : sqrt (x / y) = sqrt x / sqrt y := sqrt_hom.map_div x y

lemma continuous_sqrt : continuous sqrt := sqrt.continuous

end nnreal

namespace real

/-- An auxiliary sequence of rational numbers that converges to `real.sqrt (mk f)`.
Currently this sequence is not used in `mathlib`.  -/
def sqrt_aux (f : cau_seq ℚ abs) : ℕ → ℚ
| 0       := rat.mk_nat (f 0).num.to_nat.sqrt (f 0).denom.sqrt
| (n + 1) := let s := sqrt_aux n in max 0 $ (s + f (n+1) / s) / 2

theorem sqrt_aux_nonneg (f : cau_seq ℚ abs) : ∀ i : ℕ, 0 ≤ sqrt_aux f i
| 0       := by rw [sqrt_aux, rat.mk_nat_eq, rat.mk_eq_div];
  apply div_nonneg; exact int.cast_nonneg.2 (int.of_nat_nonneg _)
| (n + 1) := le_max_left _ _

/-- The square root of a real number. This returns 0 for negative inputs. -/
@[pp_nodot] noncomputable def sqrt (x : ℝ) : ℝ :=
nnreal.sqrt (nnreal.of_real x)
/-quotient.lift_on x
  (λ f, mk ⟨sqrt_aux f, (sqrt_aux_converges f).fst⟩)
  (λ f g e, begin
    rcases sqrt_aux_converges f with ⟨hf, x, x0, xf, xs⟩,
    rcases sqrt_aux_converges g with ⟨hg, y, y0, yg, ys⟩,
    refine xs.trans (eq.trans _ ys.symm),
    rw [← @mul_self_inj_of_nonneg ℝ _ x y x0 y0, xf, yg],
    congr' 1, exact quotient.sound e
  end)-/

variables {x y : ℝ}

lemma continuous_sqrt : continuous sqrt :=
nnreal.continuous_coe.comp $ nnreal.sqrt.continuous.comp nnreal.continuous_of_real

theorem sqrt_eq_zero_of_nonpos (h : x ≤ 0) : sqrt x = 0 :=
by simp [sqrt, nnreal.of_real_eq_zero.2 h]

theorem sqrt_nonneg (x : ℝ) : 0 ≤ sqrt x := nnreal.coe_nonneg _

@[simp] theorem mul_self_sqrt (h : 0 ≤ x) : sqrt x * sqrt x = x :=
by simp [sqrt, ← nnreal.coe_mul, nnreal.coe_of_real _ h]

@[simp] theorem sqrt_mul_self (h : 0 ≤ x) : sqrt (x * x) = x :=
(mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))


example (a b : ℝ) (h : a ≤ b) (ha : 0 < a) (hb : 0 < b) : 1/b ≤ 1/a := by {
  rw le_div_iff ha,
  rw mul_comm,
  rw ←mul_div_assoc,
  rw div_le_iff hb,
  rw [one_mul, mul_one],
  exact h,
}
theorem sqrt_exists : ∀ {x : ℝ}, 0 ≤ x → ∃ y, 0 ≤ y ∧ y * y = x := by {
  intros x hx,
  let y := sqrt x,
  use sqrt x,
  split,
  apply sqrt_nonneg,
  apply mul_self_sqrt hx, }
theorem xxx (a : ℝ) (i j : ℕ) (h : i ≤ j) (h' : 0 ≤ a) : a / 2 ^ j ≤ a / 2 ^ i := by {
  rw le_div_iff,
  rw mul_comm,
  rw ←mul_div_assoc,
  rw div_le_iff,
  rw mul_comm,
  exact mul_le_mul_of_nonneg_left (pow_le_pow one_le_two h) h',-- ,
  norm_num,
  norm_num,
}
example (a b : ℝ) (h : b ≠ 0) : a / b * b = a := by {
  exact (eq_div_iff h).mp rfl,
}
lemma zzz (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) : ∃ i : ℕ, δ < 2 ^ i * ε :=
begin

      suffices : ∃ a, δ < a * ε,
      { obtain ⟨a, ha⟩ := this,
        obtain ⟨b, hb: a < ↑b⟩ := exists_nat_gt a,
        let c := nat.log 2 b,
        have : (b : ℝ) < (2 : ℝ) ^ (nat.log 2 b + 1),
        {
          norm_cast,
          exact nat.pow_succ_log_gt_self 2 b one_lt_two sorry,
        },
--        have := (mul_lt_mul_right H).mpr this,
        use nat.log 2 b + 1,
        calc δ
            < a * ε : ha
        ... < b * ε : (mul_lt_mul_right hε).mpr hb
        ... < _ : _,
        sorry,
        rw mul_lt_mul_right hε,
        sorry},
      use δ / ε + 1,
      rwa [add_mul, one_mul, (eq_div_iff hε.ne.symm).mp rfl, lt_add_iff_pos_right]
end

theorem sqrt_aux_converges (f : cau_seq ℚ abs) : ∃ h x, 0 ≤ x ∧ x * x = max 0 (mk f) ∧
  mk ⟨sqrt_aux f, h⟩ = x :=
begin
  let x := sqrt (max 0 (mk f)),
  --have x0 := le_max_left 0 (mk f),
  have x0 : 0 ≤ x := sqrt_nonneg _,
  have hx : x * x = _ := mul_self_sqrt (le_max_left 0 (mk f)),
--  rcases sqrt_exists (le_max_left 0 (mk f)) with ⟨x, x0, hx⟩,
  suffices : ∃ h, mk ⟨sqrt_aux f, h⟩ = x,
  { exact this.imp (λ h e, ⟨x, x0, hx, e⟩) },
  apply of_near,

  suffices : ∃ δ > 0, ∀ i, abs (↑(sqrt_aux f i) - x) < δ / 2 ^ i,
  { rcases this with ⟨δ, δ0, hδ⟩,
    intros,
    obtain ⟨i : ℕ, hi⟩ : ∃ i, δ < 2 ^ i * ε,
    { apply zzz _ _ H δ0 },
    use i,
    intros j hj,
    have : δ / 2 ^ j < ε,
    {
      calc δ / 2 ^ j
          ≤ δ / 2 ^ i : xxx _ _ _ hj δ0.lt.le
      ... < ε : by { rwa [div_lt_iff, mul_comm], norm_num },
    },
    refine lt_of_lt_of_le _ this.le,
    have := hδ j,
    apply lt_of_lt_of_le,
    { exact this, },
    refl,
    /-
    calc _
        < δ / 2 ^ j : _
    ... ≤ δ / 2 ^ i : _
    ... < ε : _,


    have yyy := xxx _ _ _ hj δ0.lt.le,
    calc _
        < δ / 2 ^ j : hδ _
    ... ≤ δ / 2 ^ i : yyy
    ... < ε : by { rwa [div_lt_iff, mul_comm], sorry, norm_num },
    -/
  },

  use [1, by norm_num],
  intro i,
  induction i,
  { simp [sqrt_aux, x],
  },
  sorry,
/-
def sqrt_aux (f : cau_seq ℚ abs) : ℕ → ℚ
| 0       := rat.mk_nat (f 0).num.to_nat.sqrt (f 0).denom.sqrt
| (n + 1) := let s := sqrt_aux n in max 0 $ (s + f (n+1) / s) / 2
-/
end

theorem sqrt_eq_iff_mul_self_eq (hx : 0 ≤ x) (hy : 0 ≤ y) :
  sqrt x = y ↔ y * y = x :=
⟨λ h, by rw [← h, mul_self_sqrt hx], λ h, by rw [← h, sqrt_mul_self hy]⟩

@[simp] theorem sqr_sqrt (h : 0 ≤ x) : sqrt x ^ 2 = x :=
by rw [pow_two, mul_self_sqrt h]

@[simp] theorem sqrt_sqr (h : 0 ≤ x) : sqrt (x ^ 2) = x :=
by rw [pow_two, sqrt_mul_self h]

theorem sqrt_eq_iff_sqr_eq (hx : 0 ≤ x) (hy : 0 ≤ y) :
  sqrt x = y ↔ y ^ 2 = x :=
by rw [pow_two, sqrt_eq_iff_mul_self_eq hx hy]

theorem sqrt_mul_self_eq_abs (x : ℝ) : sqrt (x * x) = abs x :=
by rw [← abs_mul_abs_self x, sqrt_mul_self (abs_nonneg _)]

theorem sqrt_sqr_eq_abs (x : ℝ) : sqrt (x ^ 2) = abs x :=
by rw [pow_two, sqrt_mul_self_eq_abs]

@[simp] theorem sqrt_zero : sqrt 0 = 0 := by simp [sqrt]

@[simp] theorem sqrt_one : sqrt 1 = 1 := by simp [sqrt]

@[simp] theorem sqrt_le (hy : 0 ≤ y) : sqrt x ≤ sqrt y ↔ x ≤ y :=
by simp [sqrt, nnreal.of_real_le_of_real_iff, *]

@[simp] theorem sqrt_lt (hx : 0 ≤ x) : sqrt x < sqrt y ↔ x < y :=
lt_iff_lt_of_le_iff_le (sqrt_le hx)

lemma sqrt_le_sqrt (h : x ≤ y) : sqrt x ≤ sqrt y :=
by simp [sqrt, nnreal.of_real_le_of_real h]

lemma sqrt_le_left (hy : 0 ≤ y) : sqrt x ≤ y ↔ x ≤ y ^ 2 :=
by rw [sqrt, ← nnreal.le_of_real_iff_coe_le hy, nnreal.sqrt_le_iff, ← nnreal.of_real_mul hy,
  nnreal.of_real_le_of_real_iff (mul_self_nonneg y), pow_two]

lemma sqrt_le_iff : sqrt x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2 :=
begin
  rw [← and_iff_right_of_imp (λ h, (sqrt_nonneg x).trans h), and.congr_right_iff],
  exact sqrt_le_left
end

/- note: if you want to conclude `x ≤ sqrt y`, then use `le_sqrt_of_sqr_le`.
   if you have `x > 0`, consider using `le_sqrt'` -/
lemma le_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
by rw [mul_self_le_mul_self_iff hx (sqrt_nonneg _), pow_two, mul_self_sqrt hy]

lemma le_sqrt' (hx : 0 < x) : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
by { rw [sqrt, ← nnreal.coe_mk x hx.le, nnreal.coe_le_coe, nnreal.le_sqrt_iff,
  nnreal.le_of_real_iff_coe_le', pow_two, nnreal.coe_mul], exact mul_pos hx hx }

lemma le_sqrt_of_sqr_le (h : x ^ 2 ≤ y) : x ≤ sqrt y :=
begin
  cases lt_or_ge 0 x with hx hx,
  { rwa [le_sqrt' hx] },
  { exact le_trans hx (sqrt_nonneg y) }
end

@[simp] theorem sqrt_inj (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x = sqrt y ↔ x = y :=
by simp [le_antisymm_iff, hx, hy]

@[simp] theorem sqrt_eq_zero (h : 0 ≤ x) : sqrt x = 0 ↔ x = 0 :=
by simpa using sqrt_inj h (le_refl _)

theorem sqrt_eq_zero' : sqrt x = 0 ↔ x ≤ 0 :=
by rw [sqrt, nnreal.coe_eq_zero, nnreal.sqrt_eq_zero, nnreal.of_real_eq_zero]

@[simp] theorem sqrt_pos : 0 < sqrt x ↔ 0 < x :=
lt_iff_lt_of_le_iff_le (iff.trans
  (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')

@[simp] theorem sqrt_mul (hx : 0 ≤ x) (y : ℝ) : sqrt (x * y) = sqrt x * sqrt y :=
by simp_rw [sqrt, ← nnreal.coe_mul, nnreal.coe_eq, nnreal.of_real_mul hx, nnreal.sqrt_mul]

@[simp] theorem sqrt_mul' (x) {y : ℝ} (hy : 0 ≤ y) : sqrt (x * y) = sqrt x * sqrt y :=
by rw [mul_comm, sqrt_mul hy, mul_comm]

@[simp] theorem sqrt_inv (x : ℝ) : sqrt x⁻¹ = (sqrt x)⁻¹ :=
by rw [sqrt, nnreal.of_real_inv, nnreal.sqrt_inv, nnreal.coe_inv, sqrt]

@[simp] theorem sqrt_div (hx : 0 ≤ x) (y : ℝ) : sqrt (x / y) = sqrt x / sqrt y :=
by rw [division_def, sqrt_mul hx, sqrt_inv, division_def]

end real

open real

variables {α : Type*}

lemma filter.tendsto.sqrt {f : α → ℝ} {l : filter α} {x : ℝ} (h : tendsto f l (𝓝 x)) :
  tendsto (λ x, sqrt (f x)) l (𝓝 (sqrt x)) :=
(continuous_sqrt.tendsto _).comp h

variables [topological_space α] {f : α → ℝ} {s : set α} {x : α}

lemma continuous_within_at.sqrt (h : continuous_within_at f s x) :
  continuous_within_at (λ x, sqrt (f x)) s x :=
h.sqrt

lemma continuous_at.sqrt (h : continuous_at f x) : continuous_at (λ x, sqrt (f x)) x := h.sqrt

lemma continuous_on.sqrt (h : continuous_on f s) : continuous_on (λ x, sqrt (f x)) s :=
λ x hx, (h x hx).sqrt

lemma continuous.sqrt (h : continuous f) : continuous (λ x, sqrt (f x)) := continuous_sqrt.comp h
