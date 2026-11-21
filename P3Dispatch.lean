import P2Core
import P3Core
import P3Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
Finite dispatch for the 10 signed Gaussian candidates of diagonal p³q.
Bridge fields are the residual modular and coprimality comparisons, stated
explicitly so that the downstream theorem is not mistaken for the cuboid theorem.
-/

namespace FormalCuboid.P3

inductive Leg where
  | a1 | a2 | a3 | b1p | b1m | b2p | b2m | b3p | b3m | c
  deriving DecidableEq

def Triangle (a b c : ℤ) : Prop :=
  a ^ 2 = b ^ 2 + c ^ 2 ∨ b ^ 2 = a ^ 2 + c ^ 2 ∨ c ^ 2 = a ^ 2 + b ^ 2

theorem Triangle.swap₁₂ {a b c : ℤ} (h : Triangle a b c) : Triangle b a c := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (by linarith only [h]))

theorem Triangle.swap₂₃ {a b c : ℤ} (h : Triangle a b c) : Triangle a c b := by
  rcases h with h | h | h
  · exact Or.inl (by linarith only [h])
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

structure Data where
  p : ℤ
  q : ℤ
  R : ℤ
  S : ℤ
  U : ℤ
  V : ℤ
  p_ge : 5 ≤ p
  q_ge : 5 ≤ q
  odd_p : Odd p
  odd_q : Odd q
  odd_R : Odd R
  odd_U : Odd U
  odd_T : Odd (reFourth R S)
  odd_X : Odd (reSixth R S)
  four_S : (4 : ℤ) ∣ S
  R_zero : R ≠ 0
  S_zero : S ≠ 0
  U_zero : U ≠ 0
  V_zero : V ≠ 0
  p3 : (p : ZMod 3) ≠ 0
  q3 : (q : ZMod 3) ≠ 0
  norm_p : R ^ 2 + S ^ 2 = p ^ 2
  norm_q : U ^ 2 + V ^ 2 = q ^ 2

variable (d : Data)

abbrev Data.T := reFourth d.R d.S
abbrev Data.W := imFourth d.R d.S
abbrev Data.X := reSixth d.R d.S
abbrev Data.Y := imSixth d.R d.S

def Data.b₁ (σ : ℤ) := d.p ^ 2 * (d.S * d.U + σ * d.R * d.V)
def Data.b₂ (σ : ℤ) := d.p * (d.W * d.U + σ * d.T * d.V)
def Data.b₃ (σ : ℤ) := d.Y * d.U + σ * d.X * d.V
def Data.a₃ := d.q * d.Y

def Data.value : Leg → ℤ
  | .a1 => d.p ^ 2 * d.q * d.S
  | .a2 => d.p * d.q * d.W
  | .a3 => d.a₃
  | .b1p => d.b₁ 1
  | .b1m => d.b₁ (-1)
  | .b2p => d.b₂ 1
  | .b2m => d.b₂ (-1)
  | .b3p => d.b₃ 1
  | .b3m => d.b₃ (-1)
  | .c => d.p ^ 3 * d.V

def Top (a : Leg) : Prop := a = .a3 ∨ a = .b3p ∨ a = .b3m

def Sign (σ : ℤ) : Prop := σ = 1 ∨ σ = -1

def IsLowerA (a : Leg) : Prop := a = .a1 ∨ a = .a2

def IsBottomMixed (a : Leg) : Prop := a = .b1p ∨ a = .b1m ∨ a = .c

/-- Precisely the modular/norm consequences left to prove from the Gaussian representations. -/
structure Bridge where
  lowerA_mod_q (a : Leg) (ha : IsLowerA a) (σ : ℤ) (hσ : Sign σ) :
    Triangle d.a₃ (d.b₃ σ) (d.value a) → False
  bottom_mixed_bounds (a : Leg) (ha : IsBottomMixed a) (σ : ℤ) (hσ : Sign σ) :
    Triangle d.a₃ (d.b₃ σ) (d.value a) → d.p ^ 4 < d.q ∧ d.q ^ 2 < d.p ^ 4
  middle_a₃_leg (σ τ : ℤ) (hσ : Sign σ) (hτ : Sign τ) :
    (d.b₃ σ) ^ 2 - (d.b₂ τ) ^ 2 = d.a₃ ^ 2 ∨
       (d.b₂ τ) ^ 2 - (d.b₃ σ) ^ 2 = d.a₃ ^ 2 →
    d.p ^ 2 < d.q ∧ d.q ^ 4 < d.p ^ 5
  middle_a₃_hyp (σ τ : ℤ) (hσ : Sign σ) (hτ : Sign τ) :
    (d.b₃ σ) ^ 2 + (d.b₂ τ) ^ 2 = d.a₃ ^ 2 →
    τ = -σ ∧ d.p ^ 2 < d.q ∧ d.q ^ 2 ∣ finalDiscriminant d.R d.S
  lower_a_difference (a : Leg) (ha : IsLowerA a) :
    (d.b₃ 1) ^ 2 - (d.b₃ (-1)) ^ 2 = (d.value a) ^ 2 ∨
      (d.b₃ (-1)) ^ 2 - (d.b₃ 1) ^ 2 = (d.value a) ^ 2 →
    d.p ^ 2 < d.q ∧ d.q ^ 2 < d.p ^ 3
  lower_a_sum (a : Leg) (ha : IsLowerA a) :
    (d.b₃ 1) ^ 2 + (d.b₃ (-1)) ^ 2 = (d.value a) ^ 2 →
    d.p ^ 4 ≤ 2 * d.q ^ 2 ∧ d.q ^ 4 ≤ 2 * d.p ^ 6
  top_a_difference :
    (d.b₃ 1) ^ 2 - (d.b₃ (-1)) ^ 2 = d.a₃ ^ 2 ∨
      (d.b₃ (-1)) ^ 2 - (d.b₃ 1) ^ 2 = d.a₃ ^ 2 →
    d.q ^ 4 - 1 = 2 * |d.Y| ∧ |d.Y| ≤ 2 * d.q ^ 2
  c_difference :
    (d.b₃ 1) ^ 2 - (d.b₃ (-1)) ^ 2 = (d.value .c) ^ 2 ∨
      (d.b₃ (-1)) ^ 2 - (d.b₃ 1) ^ 2 = (d.value .c) ^ 2 →
    d.p ^ 12 - 1 = 2 * |d.V| ∧ |d.V| ≤ 2 * d.p ^ 6
  norm_top : d.X ^ 2 + d.Y ^ 2 = d.p ^ 6
  Y_ne_zero : d.Y ≠ 0

private theorem is_int_odd_mod2 {z : ℤ} (h : Odd z) : z % 2 = 1 := by
  obtain ⟨k, hk⟩ := h
  omega

private theorem odd_ne_zero {z : ℤ} (h : Odd z) : z ≠ 0 := by
  have h' := is_int_odd_mod2 h
  omega

private theorem odd_mod2_sqr {z : ℤ} (h : z % 2 = 1) : z ^ 2 % 2 = 1 := by
  rw [pow_two, Int.mul_emod, h] <;> decide

private theorem odd_mod2_mul {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 1) :
    (x * y) % 2 = 1 := by
  rw [Int.mul_emod, hx, hy] <;> decide

private theorem odd_minus_even_mod2 {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 0) :
    (x - y) % 2 = 1 := by omega

private theorem twice_mod2 (x : ℤ) : (2 * x) % 2 = 0 := by omega

private theorem int_three_split_aux (n : ℕ) (z : ℤ) (hz : z ≠ 0)
    (hl : -(n : ℤ) < z) (hr : z < n) :
    ∃ k : ℕ, ∃ u : ℤ, z = 3 ^ k * u ∧ (u : ZMod 3) ≠ 0 := by
  induction n generalizing z with
  | zero => omega
  | succ n ih =>
    by_cases h : (3 : ℤ) ∣ z
    · have hmod := Int.emod_eq_zero_of_dvd h
      have hs : z = 3 * (z / 3) := by omega
      have hzn : z / 3 ≠ 0 := by omega
      have hzl : -(n : ℤ) < z / 3 := by omega
      have hzr : z / 3 < n := by omega
      obtain ⟨k,u,hu,hmu⟩ := ih (z / 3) hzn hzl hzr
      refine ⟨k+1,u,?_,hmu⟩
      calc
        z = 3 * (z / 3) := hs
        _ = 3 ^ (k + 1) * u := by rw [hu, pow_succ]; ring
    · exact ⟨0,z,by simp,fun h0 => h ((ZMod.intCast_zmod_eq_zero_iff_dvd z 3).mp h0)⟩

private theorem int_three_split (z : ℤ) (hz : z ≠ 0) :
    ∃ k : ℕ, ∃ u : ℤ, z = 3 ^ k * u ∧ (u : ZMod 3) ≠ 0 := by
  let n := (z+1).toNat + (-z+1).toNat
  apply int_three_split_aux n z hz <;> dsimp [n] <;> omega

private theorem middle_a₃_hyp_impossible {σ τ : ℤ} (hσ : Sign σ) (hτ : Sign τ)
    (bridge : Bridge d) (h : (d.b₃ σ) ^ 2 + (d.b₂ τ) ^ 2 = d.a₃ ^ 2) : False := by
  obtain ⟨hsigns, hpq, hdiv⟩ := bridge.middle_a₃_hyp σ τ hσ hτ h
  have hE := final_discriminant_eq_sq d.p d.q d.R d.S
    d.odd_R d.four_S d.odd_q d.R_zero d.norm_p hpq hdiv
  obtain ⟨hR3,hS3⟩ := final_discriminant_mod3 d.p d.q d.R d.S d.p3 d.q3 d.norm_p hE
  obtain ⟨r, s, hs, hsu⟩ := int_three_split d.S d.S_zero
  obtain ⟨b, v, hv, hvu⟩ := int_three_split d.V d.V_zero
  have hdivS := (ZMod.intCast_zmod_eq_zero_iff_dvd d.S 3).mp hS3
  obtain ⟨t, ht⟩ := hdivS
  have hY : d.Y = 3 ^ (r + 1) * (s * (d.R ^ 2 - 3 * t ^ 2)) := by
    have hSq : d.S ^ 2 = 9 * t ^ 2 := by rw [ht]; ring
    unfold Data.Y imSixth
    rw [hSq, hs, pow_succ]
    ring
  have hW : d.W = 3 ^ r * (2 * d.R * s) := by
    unfold Data.W imFourth
    rw [hs]
    ring
  have hw3 : ((2 * d.R * s : ℤ) : ZMod 3) ≠ 0 := by
    push_cast
    exact mul_ne_zero (mul_ne_zero (by decide) hR3) hsu
  have hX3 : (d.X : ZMod 3) ≠ 0 := by
    unfold Data.X reSixth
    push_cast
    rw [show (3 : ZMod 3) = 0 by decide, zero_mul, sub_zero]
    exact mul_ne_zero hR3 (pow_ne_zero 2 hR3)
  have hσ3 : (σ : ZMod 3) ≠ 0 := by
    rcases hσ with rfl | rfl <;> decide
  apply a3_final_scaled_impossible d.p d.q d.X d.T d.U d.V d.Y d.W σ
    (2 * d.R * s) v (s * (d.R ^ 2 - 3 * t ^ 2)) r b
    d.p3 hX3 hw3 hvu hσ3 d.q3 d.norm_q hY hW hv
  unfold Data.b₃ Data.b₂ Data.a₃ at h
  rw [hsigns] at h
  linear_combination h

private theorem square_lt_square {x y : ℤ} (hx : 0 ≤ x) (hxy : x < y) :
    x ^ 2 < y ^ 2 := by
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  nlinarith only [mul_pos (sub_pos.mpr hxy) (add_pos_of_pos_of_nonneg hy hx)]

private theorem cannot_mixed_bounds (d : Data) (h₁ : d.p ^ 2 < d.q)
    (h₂ : d.q ^ 2 < d.p ^ 3) : False := by
  have hq := square_lt_square (sq_nonneg d.p) h₁
  have hp_pos : 0 < d.p := by linarith only [d.p_ge]
  have hp : d.p ^ 3 < d.p ^ 4 := by
    have := mul_pos (show 0 < d.p ^ 3 by positivity)
      (show 0 < d.p - 1 by linarith only [d.p_ge])
    nlinarith only [this]
  nlinarith only [hq, h₂, hp]

private theorem small_from_large_component (m w : ℤ) (hm : 5 ≤ m)
    (h : m ^ 2 - 1 = 2 * w) (hw : w ≤ 2 * m) : False := by
  have hp := mul_nonneg (show 0 ≤ m-5 by linarith only [hm])
    (show 0 ≤ m+1 by linarith only [hm])
  nlinarith only [hp,h,hw]

private theorem b3PairExcluded (d : Data) (bridge : Bridge d) {c : Leg}
    (hF : c ≠ .b3p) (hG : c ≠ .b3m) :
    ¬ Triangle (d.b₃ 1) (d.b₃ (-1)) (d.value c) := by
  have hPpos : 0 < d.p := by linarith only [d.p_ge]
  have hQpos : 0 < d.q := by linarith only [d.q_ge]
  have hTn := odd_ne_zero d.odd_T
  have hS2 : d.S % 2 = 0 := by
    obtain ⟨k,hk⟩ := d.four_S
    omega
  have hN3 : ((d.R ^ 2 + d.S ^ 2 : ℤ) : ZMod 3) ≠ 0 := by
    rw [d.norm_p]
    push_cast
    exact pow_ne_zero 2 d.p3
  have hb1 (σ : ℤ) (hσ : Sign σ) : ¬ Triangle (d.b₃ 1) (d.b₃ (-1)) (d.b₁ σ) := by
    intro h
    rcases h with h | h | h
    · apply b1_leg_sign_impossible d.R d.S d.U d.V σ 1 d.odd_R d.four_S d.R_zero d.S_zero
        d.U_zero hN3 hσ (Or.inl rfl)
      unfold Data.b₃ Data.b₁ Data.X Data.Y at h
      rw [← d.norm_p] at h
      linear_combination -h
    · apply b1_leg_sign_impossible d.R d.S d.U d.V σ (-1) d.odd_R d.four_S d.R_zero d.S_zero
        d.U_zero hN3 hσ (Or.inr rfl)
      unfold Data.b₃ Data.b₁ Data.X Data.Y at h
      rw [← d.norm_p] at h
      linear_combination -h
    · apply b1_hypotenuse_sign_impossible d.R d.S d.U d.V σ d.odd_R d.four_S
        d.R_zero d.S_zero d.U_zero hTn hσ
      unfold Data.b₃ Data.b₁ Data.X Data.Y at h
      rw [← d.norm_p] at h
      linear_combination h
  have hb2 (σ : ℤ) (hσ : Sign σ) : ¬ Triangle (d.b₃ 1) (d.b₃ (-1)) (d.b₂ σ) := by
    simpa [Triangle, Data.b₃, Data.b₂, Data.W, Data.Y, imFourth, imSixth, sub_eq_add_neg] using
      PerfectCuboid.p3_b2_top_pair_excluded d.p d.R d.S d.T d.X d.U d.V σ
        d.odd_p d.odd_R hS2 d.S_zero d.odd_T d.odd_X d.odd_U hσ
  have hAlower (c : Leg) (hc : IsLowerA c) : ¬ Triangle (d.b₃ 1) (d.b₃ (-1)) (d.value c) := by
    intro h
    rcases h with h | h | h
    · have hd : (d.b₃ 1)^2-(d.b₃ (-1))^2=(d.value c)^2 := by linarith only [h]
      obtain ⟨hl,hu⟩ := bridge.lower_a_difference c hc (Or.inl hd)
      exact cannot_mixed_bounds d hl hu
    · have hd : (d.b₃ (-1))^2-(d.b₃ 1)^2=(d.value c)^2 := by linarith only [h]
      obtain ⟨hl,hu⟩ := bridge.lower_a_difference c hc (Or.inr hd)
      exact cannot_mixed_bounds d hl hu
    · obtain ⟨hl,hu⟩ := bridge.lower_a_sum c hc h.symm
      have hx : d.p ^ 8 ≤ 4 * d.q ^ 4 := by
        have hp4 : 0 ≤ d.p ^ 4 := by positivity
        have hm := mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ 2*d.q^2+d.p^4 by positivity)
        nlinarith only [hm]
      have hy : 8 * d.p ^ 6 < d.p ^ 8 := by
        have hpsq : 8 < d.p ^ 2 := by
          have hm := mul_nonneg (sub_nonneg.mpr d.p_ge) (show 0 ≤ d.p + 5 by positivity)
          nlinarith only [hm]
        have hm := mul_pos (sub_pos.mpr hpsq) (show 0 < d.p ^ 6 by positivity)
        nlinarith only [hm]
      linarith only [hx,hy,hu]
  have hTopC : ¬ Triangle (d.b₃ 1) (d.b₃ (-1)) (d.value .c) := by
    intro h
    rcases h with h | h | h
    · have hd : (d.b₃ 1)^2-(d.b₃ (-1))^2=(d.value .c)^2 := by linarith only [h]
      obtain ⟨hk,hw⟩ := bridge.c_difference (Or.inl hd)
      have hge : 5 ≤ d.p ^ 6 := by
        have ht := mul_nonneg (show 0 ≤ d.p-5 by linarith only [d.p_ge])
          (show 0 ≤ d.p^5+d.p^4*5+d.p^3*25+d.p^2*125+d.p*625+3125 by positivity)
        nlinarith only [ht]
      apply small_from_large_component (d.p^6) |d.V| hge
        (by linear_combination hk) hw
    · have hd : (d.b₃ (-1))^2-(d.b₃ 1)^2=(d.value .c)^2 := by linarith only [h]
      obtain ⟨hk,hw⟩ := bridge.c_difference (Or.inr hd)
      have hge : 5 ≤ d.p ^ 6 := by
        have ht := mul_nonneg (show 0 ≤ d.p-5 by linarith only [d.p_ge])
          (show 0 ≤ d.p^5+d.p^4*5+d.p^3*25+d.p^2*125+d.p*625+3125 by positivity)
        nlinarith only [ht]
      apply small_from_large_component (d.p^6) |d.V| hge
        (by linear_combination hk) hw
    · unfold Data.b₃ Data.value at h
      have eqn : 2 * (d.U^2) * d.Y^2 = (d.p^6-2*d.X^2)*d.V^2 := by
        linear_combination -h
      have hU := odd_mod2_sqr (is_int_odd_mod2 d.odd_U)
      have hP := odd_mod2_sqr (is_int_odd_mod2 d.odd_p)
      have hP6 : d.p ^ 6 % 2 = 1 := by
        rw [show d.p ^ 6 = (d.p^2)*((d.p^2)*(d.p^2)) by ring]
        exact odd_mod2_mul hP (odd_mod2_mul hP hP)
      exact Cuboid.P2.no_twice_square hU
        (odd_minus_even_mod2 hP6 (twice_mod2 _)) bridge.Y_ne_zero eqn
  have hTopA : ¬ Triangle (d.b₃ 1) (d.b₃ (-1)) d.a₃ := by
    have hge : 5 ≤ d.q ^ 2 := by
      have hprod := mul_nonneg (show 0 ≤ d.q - 5 by linarith only [d.q_ge])
        (show 0 ≤ d.q + 5 by positivity)
      nlinarith only [hprod]
    intro h
    rcases h with h | h | h
    · have hd : (d.b₃ 1)^2-(d.b₃ (-1))^2=d.a₃^2 := by linarith only [h]
      obtain ⟨hk,hw⟩ := bridge.top_a_difference (Or.inl hd)
      exact small_from_large_component (d.q^2) |d.Y| hge
        (by linear_combination hk) hw
    · have hd : (d.b₃ (-1))^2-(d.b₃ 1)^2=d.a₃^2 := by linarith only [h]
      obtain ⟨hk,hw⟩ := bridge.top_a_difference (Or.inr hd)
      exact small_from_large_component (d.q^2) |d.Y| hge
        (by linear_combination hk) hw
    · unfold Data.b₃ Data.a₃ at h
      have eqn : 2 * (d.X^2-d.Y^2) * d.V^2 = (-d.q^2)*d.Y^2 := by
        linear_combination -h - 2 * d.Y ^ 2 * d.norm_q
      have hYEven : d.Y % 2 = 0 := by
        change (d.S * (3 * d.R ^ 2 - d.S ^ 2)) % 2 = 0
        rw [Int.mul_emod, hS2]
        simp
      have hYSqEven : d.Y ^ 2 % 2 = 0 := by
        rw [pow_two, Int.mul_emod, hYEven]
        decide
      have hqOdd : (-d.q ^ 2) % 2 = 1 := by
        have h := odd_mod2_sqr (is_int_odd_mod2 d.odd_q)
        omega
      exact Cuboid.P2.no_twice_square
        (odd_minus_even_mod2 (odd_mod2_sqr (is_int_odd_mod2 d.odd_X)) hYSqEven)
        hqOdd d.V_zero eqn
  cases c
  · exact hAlower .a1 (Or.inl rfl)
  · exact hAlower .a2 (Or.inr rfl)
  · exact hTopA
  · exact hb1 1 (Or.inl rfl)
  · exact hb1 (-1) (Or.inr rfl)
  · exact hb2 1 (Or.inl rfl)
  · exact hb2 (-1) (Or.inr rfl)
  · exact False.elim (hF rfl)
  · exact False.elim (hG rfl)
  · exact hTopC

private theorem a₃_b₃_pair_excluded (d : Data) (bridge : Bridge d) (σ : ℤ) (hσ : Sign σ)
    {c : Leg} (hc : c ≠ .a3)
    (hDistinct : σ = 1 → c ≠ .b3p) (hDistinct' : σ = -1 → c ≠ .b3m) :
    ¬ Triangle d.a₃ (d.b₃ σ) (d.value c) := by
  have hPpos : 0 < d.p := by linarith only [d.p_ge]
  have hmid (τ : ℤ) (hτ : Sign τ) : ¬ Triangle d.a₃ (d.b₃ σ) (d.b₂ τ) := by
    intro h
    rcases h with h | h | h
    · exact middle_a₃_hyp_impossible d hσ hτ bridge h.symm
    · have hd : (d.b₃ σ)^2-(d.b₂ τ)^2=d.a₃^2 := by linarith only [h]
      obtain ⟨hl,hu⟩ := bridge.middle_a₃_leg σ τ hσ hτ (Or.inl hd)
      have hq := square_lt_square (sq_nonneg d.p) hl
      have hqq := square_lt_square (by positivity : 0 ≤ d.p ^ 4)
        (by nlinarith only [hq] : d.p ^ 4 < d.q ^ 2)
      have hp8 : d.p ^ 5 < d.p ^ 8 := by
        have hm := mul_pos (show 0 < d.p^5 by positivity)
          (show 0 < d.p^3-1 by
            have hh := mul_pos (show 0 < d.p -1 by linarith only [d.p_ge])
              (show 0<d.p^2+d.p+1 by positivity)
            nlinarith only [hh])
        nlinarith only [hm]
      nlinarith only [hqq, hu, hp8]
    · have hd : (d.b₂ τ)^2-(d.b₃ σ)^2=d.a₃^2 := by linarith only [h]
      obtain ⟨hl,hu⟩ := bridge.middle_a₃_leg σ τ hσ hτ (Or.inr hd)
      have hq := square_lt_square (sq_nonneg d.p) hl
      have hqq := square_lt_square (by positivity : 0 ≤ d.p ^ 4)
        (by nlinarith only [hq] : d.p ^ 4 < d.q ^ 2)
      have hp8 : d.p ^ 5 < d.p ^ 8 := by
        have hm := mul_pos (show 0 < d.p^5 by positivity)
          (show 0 < d.p^3-1 by
            have hh := mul_pos (show 0 < d.p -1 by linarith only [d.p_ge])
              (show 0<d.p^2+d.p+1 by positivity)
            nlinarith only [hh])
        nlinarith only [hm]
      nlinarith only [hqq, hu, hp8]
  have hbot (b : Leg) (hb : IsBottomMixed b) :
      ¬ Triangle d.a₃ (d.b₃ σ) (d.value b) := by
    intro h
    obtain ⟨hl,hu⟩ := bridge.bottom_mixed_bounds b hb σ hσ h
    have hs := square_lt_square (by positivity : 0 ≤ d.p^4) hl
    have hp : d.p^4 < d.p^8 := by
      have hm := mul_pos (show 0<d.p^4 by positivity) (show 0<d.p^4-1 by
        have hh := mul_pos (show 0 < d.p - 1 by linarith only [d.p_ge])
          (show 0 < d.p^3+d.p^2+d.p+1 by positivity)
        nlinarith only [hh])
      nlinarith only [hm]
    nlinarith only [hs,hu,hp]
  cases c
  · exact bridge.lowerA_mod_q .a1 (Or.inl rfl) σ hσ
  · exact bridge.lowerA_mod_q .a2 (Or.inr rfl) σ hσ
  · exact False.elim (hc rfl)
  · exact hbot .b1p (Or.inl rfl)
  · exact hbot .b1m (Or.inr (Or.inl rfl))
  · exact hmid 1 (Or.inl rfl)
  · exact hmid (-1) (Or.inr rfl)
  · rcases hσ with rfl | rfl
    · exact False.elim (hDistinct rfl rfl)
    · intro h
      exact b3PairExcluded d bridge (c := .a3) (by decide) (by decide)
        h.swap₁₂.swap₂₃.swap₁₂
  · rcases hσ with rfl | rfl
    · intro h
      exact b3PairExcluded d bridge (c := .a3) (by decide) (by decide)
        h.swap₁₂.swap₂₃
    · exact False.elim (hDistinct' rfl rfl)
  · exact hbot .c (Or.inr (Or.inr rfl))

private theorem top_pair_excluded (d : Data) (bridge : Bridge d) {a b c : Leg}
    (ha : Top a) (hb : Top b) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Triangle (d.value a) (d.value b) (d.value c) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact False.elim (hab rfl)
  · exact a₃_b₃_pair_excluded d bridge 1 (Or.inl rfl) (Ne.symm hac)
      (fun _ => Ne.symm hbc) (fun h => False.elim (by omega))
  · exact a₃_b₃_pair_excluded d bridge (-1) (Or.inr rfl) (Ne.symm hac)
      (fun h => False.elim (by omega)) (fun _ => Ne.symm hbc)
  · exact fun h => a₃_b₃_pair_excluded d bridge 1 (Or.inl rfl) (Ne.symm hbc)
      (fun _ => Ne.symm hac) (fun he => False.elim (by omega)) h.swap₁₂
  · exact False.elim (hab rfl)
  · exact b3PairExcluded d bridge (Ne.symm hac) (Ne.symm hbc)
  · exact fun h => a₃_b₃_pair_excluded d bridge (-1) (Or.inr rfl) (Ne.symm hbc)
      (fun he => False.elim (by omega)) (fun _ => Ne.symm hac) h.swap₁₂
  · exact fun h => b3PairExcluded d bridge (Ne.symm hbc) (Ne.symm hac) h.swap₁₂
  · exact False.elim (hab rfl)

/-- All choices of three distinct states with at least two top states are
eliminated, provided the indicated Gaussian modular comparisons. -/
theorem no_qualified_triangle (d : Data) (bridge : Bridge d) {a b c : Leg}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (htop : (Top a ∧ Top b) ∨ (Top a ∧ Top c) ∨ (Top b ∧ Top c)) :
    ¬ Triangle (d.value a) (d.value b) (d.value c) := by
  intro h
  rcases htop with htop | htop | htop
  · exact top_pair_excluded d bridge htop.1 htop.2 hab hac hbc h
  · exact top_pair_excluded d bridge htop.1 htop.2 hac hab (Ne.symm hbc) h.swap₂₃
  · exact top_pair_excluded d bridge htop.1 htop.2 hbc (Ne.symm hab) (Ne.symm hac) h.swap₁₂.swap₂₃

end FormalCuboid.P3

