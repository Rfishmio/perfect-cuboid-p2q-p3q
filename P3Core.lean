import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace FormalCuboid.P3

private theorem int_square_of_scaled_square {d z k : ℤ} (hd : d ≠ 0)
    (h : z ^ 2 = d ^ 2 * k) : IsSquare k := by
  apply Rat.isSquare_intCast_iff.mp
  refine ⟨(z : ℚ) / d, ?_⟩
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hq : (z : ℚ) ^ 2 = (d : ℚ) ^ 2 * (k : ℚ) := by exact_mod_cast h
  field_simp [hdq] <;> nlinarith only [hq]

private theorem square_mod8 (x : ZMod 8) : x ^ 2 ≠ 6 ∧ x ^ 2 ≠ 7 := by
  fin_cases x <;> decide

private theorem zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private theorem sq_sum_zero_mod3 (x y : ZMod 3) :
    x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by
  intro h
  rcases zmod3_cases x with rfl | rfl | rfl <;>
    rcases zmod3_cases y with rfl | rfl | rfl <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

private theorem mod8_odd_sq {x : ℤ} (h : Odd x) : (x : ZMod 8) ^ 2 = 1 := by
  obtain ⟨t, ht⟩ := h
  rw [ht]
  push_cast
  generalize (t : ZMod 8) = g
  fin_cases g <;> decide

private theorem mod8_dvd4_sq {x : ℤ} (h : (4 : ℤ) ∣ x) : (x : ZMod 8) ^ 2 = 0 := by
  obtain ⟨t, ht⟩ := h
  rw [ht]
  push_cast
  generalize (t : ZMod 8) = g
  fin_cases g <;> decide

abbrev reFourth (R S : ℤ) := R ^ 2 - S ^ 2
abbrev imFourth (R S : ℤ) := 2 * R * S
abbrev reSixth (R S : ℤ) := R * (R ^ 2 - 3 * S ^ 2)
abbrev imSixth (R S : ℤ) := S * (3 * R ^ 2 - S ^ 2)

theorem sixth_component_product (R S : ℤ) :
    reSixth R S * imSixth R S =
      R * S * (3 * (reFourth R S) ^ 2 - (imFourth R S) ^ 2) := by
  unfold reSixth imSixth reFourth imFourth
  ring

private theorem homogeneous_discriminant (a b c u v : ℤ)
    (h : a * v ^ 2 + b * u * v + c * u ^ 2 = 0) :
    (2 * a * v + b * u) ^ 2 = (b ^ 2 - 4 * a * c) * u ^ 2 := by
  linear_combination (4 * a) * h

/-- Odd real parts and imaginary parts divisible by four prohibit the
  third leg from coming from B₁ when both top B legs occur. -/
theorem b1_leg_impossible
    (R S U V η : ℤ) (hR : Odd R) (hS : (4 : ℤ) ∣ S)
    (hRn : R ≠ 0) (hSn : S ≠ 0) (hUn : U ≠ 0)
    (hNorm3 : (((R ^ 2 + S ^ 2 : ℤ) : ZMod 3)) ≠ 0)
    (hη : η = 1 ∨ η = -1) :
    (R ^ 2 + S ^ 2) ^ 2 * (S * U + R * V) ^ 2 ≠
       η * 4 * reSixth R S * imSixth R S * U * V := by
  intro h
  let P := (R ^ 2 + S ^ 2) ^ 2
  let K := 3 * (reFourth R S) ^ 2 - (imFourth R S) ^ 2
  let a := P * R ^ 2
  let b := 2 * P * R * S - η * 4 * reSixth R S * imSixth R S
  let c := P * S ^ 2
  have hhom : a * V ^ 2 + b * U * V + c * U ^ 2 = 0 := by
    dsimp [a, b, c, P]
    linear_combination h
  have hd := homogeneous_discriminant a b c U V hhom
  have hd' : b ^ 2 - 4 * a * c = (4 * R * S) ^ 2 * (K * (K - η * P)) := by
    rcases hη with rfl | rfl <;>
      dsimp [a, b, c, P, K, reSixth, imSixth, reFourth, imFourth] <;> ring
  rw [hd'] at hd
  have hscaled : (2 * a * V + b * U) ^ 2 = (4 * R * S * U) ^ 2 * (K * (K - η * P)) := by
    linear_combination hd
  have hsq := int_square_of_scaled_square
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℤ) ≠ 0) hRn) hSn) hUn) hscaled
  have hT8 : ((reFourth R S : ℤ) : ZMod 8) ^ 2 = 1 := by
    have h' : ((reFourth R S : ℤ) : ZMod 8) = 1 := by
      unfold reFourth
      push_cast
      rw [mod8_odd_sq hR, mod8_dvd4_sq hS] <;> decide
    rw [h'] <;> decide
  have hW8 : ((imFourth R S : ℤ) : ZMod 8) ^ 2 = 0 := by
    apply mod8_dvd4_sq
    obtain ⟨t, ht⟩ := hS
    exact ⟨2 * R * t, by unfold imFourth; rw [ht]; ring⟩
  have hK8 : (K : ZMod 8) = 3 := by
    have hT8' := hT8
    have hW8' := hW8
    dsimp [K]
    push_cast at hT8' hW8' ⊢
    rw [hT8', hW8'] <;> decide
  have hP8 : (P : ZMod 8) = 1 := by
    dsimp [P]
    push_cast
    rw [mod8_odd_sq hR, mod8_dvd4_sq hS] <;> decide
  rcases hη with h1 | h1
  · obtain ⟨z, hz⟩ := hsq
    have hz' : (z : ZMod 8) ^ 2 = 6 := by
      have hz8 := congrArg (fun x : ℤ => (x : ZMod 8)) hz
      push_cast at hz8
      have hη8 : (η : ZMod 8) = 1 := by simp [h1]
      rw [hη8, hK8, hP8] at hz8
      rw [show (3 : ZMod 8) * (3 - 1 * 1) = 6 by decide] at hz8
      simpa [pow_two] using hz8.symm
    exact (square_mod8 (z : ZMod 8)).1 hz'
  · have hKP : K + P = (2 * reFourth R S) ^ 2 := by
      dsimp [K, P, reFourth, imFourth]
      ring
    have hTn : reFourth R S ≠ 0 := by
      intro hzero
      exact (by decide : (0 : ZMod 8) ^ 2 ≠ 1) (by simpa [hzero] using hT8)
    obtain ⟨z, hz⟩ := hsq
    have hz' : z ^ 2 = (2 * reFourth R S) ^ 2 * K := by
      rw [h1] at hz
      have he : K - -1 * P = K + P := by ring
      rw [he, hKP] at hz
      linear_combination -hz
    obtain ⟨w, hw⟩ := int_square_of_scaled_square (by exact mul_ne_zero (by norm_num) hTn) hz'
    have hwW : w ^ 2 + (imFourth R S) ^ 2 = 3 * (reFourth R S) ^ 2 := by
      dsimp [K] at hw
      linear_combination -hw
    have hc := congrArg (fun x : ℤ => (x : ZMod 3)) hwW
    push_cast at hc
    have hthree : (3 : ZMod 3) = 0 := by decide
    simp only [hthree, zero_mul] at hc
    obtain ⟨hw0, hW0⟩ := sq_sum_zero_mod3 (w : ZMod 3) _ hc
    have hTeq : 3 * (reFourth R S) ^ 2 = w ^ 2 + (imFourth R S) ^ 2 := hwW.symm
    -- Use the original equality modulo 9 to promote the two known factors of 3.
    have hwdiv : (3 : ℤ) ∣ w := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd w 3).mp hw0
    have hWdiv : (3 : ℤ) ∣ imFourth R S := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (imFourth R S) 3).mp
      push_cast
      exact hW0
    obtain ⟨m, hm⟩ := hwdiv
    obtain ⟨n, hn⟩ := hWdiv
    have hdivT : (3 : ℤ) ∣ (reFourth R S) ^ 2 := by
      refine ⟨m ^ 2 + n ^ 2, ?_⟩
      rw [hm, hn] at hTeq
      have hmul : 3 * (reFourth R S) ^ 2 = 3 * (3 * (m ^ 2 + n ^ 2)) := by
        linear_combination hTeq
      exact mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) hmul
    have hTcast : ((reFourth R S : ℤ) : ZMod 3) ^ 2 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((reFourth R S) ^ 2) 3).mpr hdivT
      simpa using this
    have hnorm : (reFourth R S) ^ 2 + (imFourth R S) ^ 2 = (R ^ 2 + S ^ 2) ^ 2 := by
      unfold reFourth imFourth
      ring
    have hn3 := congrArg (fun x : ℤ => (x : ZMod 3)) hnorm
    push_cast at hTcast hn3
    rw [hTcast, hW0] at hn3
    have hN : ((R : ZMod 3) ^ 2 + (S : ZMod 3) ^ 2) ^ 2 = 0 := by
      simpa using hn3.symm
    apply hNorm3
    push_cast
    exact (sq_sum_zero_mod3 _ 0 (by simpa using hN)).1

theorem b1_hypotenuse_impossible
    (R S U V : ℤ) (hR : Odd R) (hS : (4 : ℤ) ∣ S)
    (hRn : R ≠ 0) (hSn : S ≠ 0) (hUn : U ≠ 0)
    (hTn : reFourth R S ≠ 0) :
    (R ^ 2 + S ^ 2) ^ 2 * (S * U + R * V) ^ 2 ≠
        2 * ((imSixth R S) ^ 2 * U ^ 2 + (reSixth R S) ^ 2 * V ^ 2) := by
  intro h
  let P := (R ^ 2 + S ^ 2) ^ 2
  let a := P * R ^ 2 - 2 * (reSixth R S) ^ 2
  let b := 2 * P * R * S
  let c := P * S ^ 2 - 2 * (imSixth R S) ^ 2
  let K := 14 * R ^ 2 * S ^ 2 - R ^ 4 - S ^ 4
  have hhom : a * V ^ 2 + b * U * V + c * U ^ 2 = 0 := by
    dsimp [a, b, c, P]
    linear_combination h
  have hd := homogeneous_discriminant a b c U V hhom
  have hd' : b ^ 2 - 4 * a * c = (8 * R * S * reFourth R S) ^ 2 * K := by
    dsimp [a, b, c, P, K, reSixth, imSixth, reFourth]
    ring
  rw [hd'] at hd
  have hscaled : (2 * a * V + b * U) ^ 2 = (8 * R * S * reFourth R S * U) ^ 2 * K := by
    linear_combination hd
  obtain ⟨z, hz⟩ := int_square_of_scaled_square (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (8 : ℤ) ≠ 0) hRn) hSn) hTn) hUn) hscaled
  have hK8 : (K : ZMod 8) = 7 := by
    dsimp [K]
    push_cast
    rw [show (R : ZMod 8) ^ 4 = ((R : ZMod 8) ^ 2) ^ 2 by ring,
        show (S : ZMod 8) ^ 4 = ((S : ZMod 8) ^ 2) ^ 2 by ring,
        mod8_odd_sq hR, mod8_dvd4_sq hS] <;> decide
  have hz' : (z : ZMod 8) ^ 2 = 7 := by
    have hz8 := congrArg (fun x : ℤ => (x : ZMod 8)) hz
    push_cast at hz8
    rw [hK8] at hz8
    simpa [pow_two] using hz8.symm
  exact (square_mod8 (z : ZMod 8)).2 hz'

/-- Both choices of sign of the lower B₁ component. -/
theorem b1_leg_sign_impossible
    (R S U V σ η : ℤ) (hR : Odd R) (hS : (4 : ℤ) ∣ S)
    (hRn : R ≠ 0) (hSn : S ≠ 0) (hUn : U ≠ 0)
    (hNorm3 : ((R ^ 2 + S ^ 2 : ℤ) : ZMod 3) ≠ 0)
    (hσ : σ = 1 ∨ σ = -1) (hη : η = 1 ∨ η = -1) :
    (R ^ 2 + S ^ 2) ^ 2 * (S * U + σ * R * V) ^ 2 ≠
       η * 4 * reSixth R S * imSixth R S * U * V := by
  intro h
  rcases hσ with rfl | rfl
  · exact b1_leg_impossible R S U V η hR hS hRn hSn hUn hNorm3 hη
      (by simpa only [one_mul] using h)
  · have hηneg : -η = 1 ∨ -η = -1 := by
      rcases hη with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (by norm_num)
    apply b1_leg_impossible R S U (-V) (-η) hR hS hRn hSn hUn hNorm3 hηneg
    linear_combination h

theorem b1_hypotenuse_sign_impossible
    (R S U V σ : ℤ) (hR : Odd R) (hS : (4 : ℤ) ∣ S)
    (hRn : R ≠ 0) (hSn : S ≠ 0) (hUn : U ≠ 0)
    (hTn : reFourth R S ≠ 0) (hσ : σ = 1 ∨ σ = -1) :
    (R ^ 2 + S ^ 2) ^ 2 * (S * U + σ * R * V) ^ 2 ≠
        2 * ((imSixth R S) ^ 2 * U ^ 2 + (reSixth R S) ^ 2 * V ^ 2) := by
  intro h
  rcases hσ with rfl | rfl
  · exact b1_hypotenuse_impossible R S U V hR hS hRn hSn hUn hTn
      (by simpa only [one_mul] using h)
  · apply b1_hypotenuse_impossible R S U (-V) hR hS hRn hSn hUn hTn
    linear_combination h

abbrev finalDiscriminant (R S : ℤ) := R ^ 4 - 10 * R ^ 2 * S ^ 2 + 5 * S ^ 4

private theorem mod3_sq_unit (x : ZMod 3) : x ≠ 0 → x ^ 2 = 1 := by
  intro hx
  rcases zmod3_cases x with rfl | rfl | rfl
  · exact (hx rfl).elim
  · decide
  · decide

theorem final_discriminant_eq_sq
    (p q R S : ℤ) (hR : Odd R) (hS : (4 : ℤ) ∣ S) (hqOdd : Odd q) (hRn : R ≠ 0)
    (hNorm : R ^ 2 + S ^ 2 = p ^ 2) (hq : p ^ 2 < q)
    (hdiv : q ^ 2 ∣ finalDiscriminant R S) :
    finalDiscriminant R S = q ^ 2 := by
  have hqpos : 0 < q := lt_of_le_of_lt (sq_nonneg p) hq
  have hq2 : 0 < q ^ 2 := sq_pos_of_ne_zero (ne_of_gt hqpos)
  have hp4 : p ^ 4 < q ^ 2 := by
    have hpositive := mul_pos (sub_pos.mpr hq) (add_pos_of_pos_of_nonneg hqpos (sq_nonneg p))
    nlinarith only [hpositive]
  have hu : finalDiscriminant R S < 5 * (R ^ 2 + S ^ 2) ^ 2 := by
    have hprod := mul_nonneg (sq_nonneg R) (sq_nonneg S)
    have h4 := sq_pos_of_ne_zero (pow_ne_zero 2 hRn)
    dsimp [finalDiscriminant]
    nlinarith only [hprod, h4]
  have hl : -(5 * (R ^ 2 + S ^ 2) ^ 2) < finalDiscriminant R S := by
    have h4 := sq_pos_of_ne_zero (pow_ne_zero 2 hRn)
    have hs := sq_nonneg (S ^ 2)
    dsimp [finalDiscriminant]
    nlinarith only [h4, hs]
  rw [hNorm] at hu hl
  have hu' : finalDiscriminant R S < 5 * q ^ 2 := by linarith only [hu, hp4]
  have hl' : -(5 * q ^ 2) < finalDiscriminant R S := by linarith only [hl, hp4]
  obtain ⟨k, hk⟩ := hdiv
  have hku : k < 5 := by
    by_contra! hn
    have hm := mul_le_mul_of_nonneg_left hn (le_of_lt hq2)
    linarith only [hm, hk, hu']
  have hkl : -5 < k := by
    by_contra! hn
    have hm := mul_le_mul_of_nonneg_left hn (le_of_lt hq2)
    linarith only [hm, hk, hl']
  have hE8 : ((finalDiscriminant R S : ℤ) : ZMod 8) = 1 := by
    dsimp [finalDiscriminant]
    push_cast
    rw [show (R : ZMod 8) ^ 4 = ((R : ZMod 8) ^ 2) ^ 2 by ring,
        show (S : ZMod 8) ^ 4 = ((S : ZMod 8) ^ 2) ^ 2 by ring,
        mod8_odd_sq hR, mod8_dvd4_sq hS] <;> decide
  have hk8 := congrArg (fun x : ℤ => (x : ZMod 8)) hk
  push_cast at hE8 hk8
  rw [hE8, mod8_odd_sq hqOdd, one_mul] at hk8
  have hrem := (ZMod.intCast_eq_intCast_iff' k 1 8).mp (by simpa using hk8.symm)
  have hk1 : k = 1 := by omega
  simpa [hk1] using hk

theorem final_discriminant_mod3
    (p q R S : ℤ) (hp : (p : ZMod 3) ≠ 0) (hq : (q : ZMod 3) ≠ 0)
    (hNorm : R ^ 2 + S ^ 2 = p ^ 2)
    (hE : finalDiscriminant R S = q ^ 2) :
    (R : ZMod 3) ≠ 0 ∧ (S : ZMod 3) = 0 := by
  have hN3 := congrArg (fun x : ℤ => (x : ZMod 3)) hNorm
  push_cast at hN3
  rw [mod3_sq_unit _ hp] at hN3
  have hE3 := congrArg (fun x : ℤ => (x : ZMod 3)) hE
  dsimp [finalDiscriminant] at hE3
  push_cast at hE3
  rw [mod3_sq_unit _ hq] at hE3
  have hR : (R : ZMod 3) ≠ 0 := by
    intro hZero
    rw [hZero] at hN3 hE3
    have hS2 : (S : ZMod 3) ^ 2 = 1 := by simpa using hN3
    rw [show (S : ZMod 3) ^ 4 = ((S : ZMod 3) ^ 2) ^ 2 by ring, hS2] at hE3
    exact (by decide : (5 : ZMod 3) ≠ 1) (by simpa using hE3)
  refine ⟨hR, ?_⟩
  rw [mod3_sq_unit _ hR] at hN3
  have hS2 : (S : ZMod 3) ^ 2 = 0 := by
    exact add_left_cancel (show 1 + (S : ZMod 3) ^ 2 = 1 + 0 by simpa using hN3)
  exact (sq_sum_zero_mod3 _ 0 (by simpa using hS2)).1

private theorem cancel_pythagorean_scale (s a b c : ℤ) (hs : s ≠ 0)
    (h : (s * a) ^ 2 + (s * b) ^ 2 = (s * c) ^ 2) : a ^ 2 + b ^ 2 = c ^ 2 := by
  have := show s ^ 2 * (a ^ 2 + b ^ 2) = s ^ 2 * c ^ 2 by linear_combination h
  exact mul_left_cancel₀ (pow_ne_zero 2 hs) this

/-- The three-adic argument at the end of the A₃-as-hypotenuse case.
The witnesses encode the integer decompositions at 3, rather than references to a valuation API. -/
theorem a3_final_scaled_impossible
    (p q X T U V Y W σ w v y : ℤ) (r b : ℕ)
    (hp : (p : ZMod 3) ≠ 0) (hX : (X : ZMod 3) ≠ 0)
    (hw : (w : ZMod 3) ≠ 0) (hv : (v : ZMod 3) ≠ 0) (hσ : (σ : ZMod 3) ≠ 0)
    (hq : (q : ZMod 3) ≠ 0) (hNorm : U ^ 2 + V ^ 2 = q ^ 2)
    (hY : Y = 3 ^ (r + 1) * y) (hW : W = 3 ^ r * w) (hV : V = 3 ^ b * v) :
    (Y * U + σ * X * V) ^ 2 + (p * (W * U - σ * T * V)) ^ 2 ≠ (q * Y) ^ 2 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro h
  by_cases hbr : b ≤ r
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hbr
    have hs : (3 : ℤ) ^ b ≠ 0 := by positivity
    have hfact :
        ((3 : ℤ) ^ b * (3 * 3 ^ j * y * U + σ * X * v)) ^ 2 +
        ((3 : ℤ) ^ b * (p * (3 ^ j * w * U - σ * T * v))) ^ 2 =
        ((3 : ℤ) ^ b * (q * 3 * 3 ^ j * y)) ^ 2 := by
      rw [hY, hW, hV] at h
      simp only [pow_add, pow_one] at h
      linear_combination h
    have hscaled := cancel_pythagorean_scale _ _ _ _ hs hfact
    have hz := congrArg (fun x : ℤ => (x : ZMod 3)) hscaled
    push_cast at hz
    have hthree : (3 : ZMod 3) = 0 := by decide
    have hz' : ((σ : ZMod 3) * X * v) ^ 2 +
        ((p : ZMod 3) * (0 ^ j * w * U - σ * T * v)) ^ 2 = 0 := by
      simpa only [hthree, zero_mul, zero_add, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hz
    exact (mul_ne_zero (mul_ne_zero hσ hX) hv) (sq_sum_zero_mod3 _ _ hz').1
  · have hlt : r + 1 ≤ b := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hlt
    have hs : (3 : ℤ) ^ r ≠ 0 := by positivity
    have hfact :
        ((3 : ℤ) ^ r * (3 * y * U + σ * X * (3 * 3 ^ j * v))) ^ 2 +
        ((3 : ℤ) ^ r * (p * (w * U - σ * T * (3 * 3 ^ j * v)))) ^ 2 =
        ((3 : ℤ) ^ r * (q * 3 * y)) ^ 2 := by
      rw [hY, hW, hV] at h
      simp only [pow_add, pow_one] at h
      linear_combination h
    have hscaled := cancel_pythagorean_scale _ _ _ _ hs hfact
    have hz := congrArg (fun x : ℤ => (x : ZMod 3)) hscaled
    push_cast at hz
    have hthree : (3 : ZMod 3) = 0 := by decide
    have hz' : (0 : ZMod 3) ^ 2 + ((p : ZMod 3) * (w * U)) ^ 2 = 0 := by
      simpa only [hthree, zero_mul, zero_add, add_zero, mul_zero, sub_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0)] using hz
    have hV0 : (V : ZMod 3) = 0 := by
      rw [hV]
      push_cast
      simp [pow_add, hthree]
    have hU : (U : ZMod 3) ≠ 0 := by
      intro hzero
      have hN := congrArg (fun x : ℤ => (x : ZMod 3)) hNorm
      push_cast at hN
      rw [hzero, hV0, mod3_sq_unit _ hq] at hN
      exact (by decide : (0 : ZMod 3) ≠ 1) (by simpa using hN)
    exact (mul_ne_zero hp (mul_ne_zero hw hU)) (sq_sum_zero_mod3 _ _ hz').2

end FormalCuboid.P3

