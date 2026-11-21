import CuboidGaussian
import GaussianPhase
import P3Dispatch

namespace PerfectCuboid.P3Data

open GaussianRepr GaussianPhase CuboidFormal FormalCuboid.P3

theorem fourth_re (a : GaussianInt) :
    (a ^ 4).re = reFourth (a ^ 2).re (a ^ 2).im := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
  simp only [reFourth, pow_two, Zsqrtd.re_mul, neg_mul, one_mul]
  ring

theorem fourth_im (a : GaussianInt) :
    (a ^ 4).im = imFourth (a ^ 2).re (a ^ 2).im := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
  simp only [imFourth, pow_two, Zsqrtd.im_mul]
  ring

theorem sixth_re (a : GaussianInt) :
    (a ^ 6).re = reSixth (a ^ 2).re (a ^ 2).im := by
  rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, pow_succ _ 2, pow_two (a ^ 2)]
  simp only [reSixth, Zsqrtd.re_mul, Zsqrtd.im_mul, neg_mul, one_mul]
  ring

theorem sixth_im (a : GaussianInt) :
    (a ^ 6).im = imSixth (a ^ 2).re (a ^ 2).im := by
  rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, pow_succ _ 2, pow_two (a ^ 2)]
  simp only [imSixth, Zsqrtd.re_mul, Zsqrtd.im_mul, neg_mul, one_mul]
  ring

theorem component_norm_power {a : GaussianInt} {p : ℕ} (hn : normN a = p) (n : ℕ) :
    (a ^ n).re ^ 2 + (a ^ n).im ^ 2 = (p : ℤ) ^ n := by
  rw [← gaussian_norm_eq]
  have hn' : normN (a ^ n) = p ^ n := by simp [hn]
  exact_mod_cast norm_eq_natCast hn'

theorem odd_re {a : GaussianInt} (ha : OddEven a) : Odd a.re := by
  obtain ⟨r, _, hr, _⟩ := ha
  exact ⟨r, hr⟩

theorem even_im {a : GaussianInt} (ha : OddEven a) : Even a.im := by
  obtain ⟨_, s, _, hs⟩ := ha
  exact ⟨s, by omega⟩

theorem four_dvd_square_im {a : GaussianInt} (ha : OddEven a) : (4 : ℤ) ∣ (a ^ 2).im := by
  obtain ⟨_, s, _, hs⟩ := ha
  refine ⟨a.re * s, ?_⟩
  rw [pow_two, Zsqrtd.im_mul, hs]
  ring

theorem nonzero_power_coordinates {a : GaussianInt} {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : normN a = p) (hn0 : n ≠ 0) :
    (a ^ n).re ≠ 0 ∧ (a ^ n).im ≠ 0 := by
  have hprime := prime_of_prime_norm hp hn
  have hc := conjugates_coprime_of_prime_norm hp hp2 hprime (norm_eq_natCast hn)
  exact nonzero_components_of_one_sided_power hprime hn0 (hprime.irreducible.coprime_iff_not_dvd.mp hc)

private theorem int_prime_mod_three {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (((p : ℤ) : ZMod 3)) ≠ 0 := by
  intro h
  have hd : 3 ∣ p := Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  rcases hp.eq_one_or_self_of_dvd 3 hd with h1 | h2 <;> omega

def mkData {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp4 : p % 4 = 1) (hq4 : q % 4 = 1)
    {π ρ : GaussianInt} (hπ : normN π = p) (hρ : normN ρ = q)
    (oπ : OddEven π) (oρ : OddEven ρ) : Data := by
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hπ2 := nonzero_power_coordinates hp (by omega) hπ (n := 2) (by decide)
  have hρ2 := nonzero_power_coordinates hq (by omega) hρ (n := 2) (by decide)
  have hp4' : (p : ℤ) % 4 = 1 := by exact_mod_cast hp4
  have hq4' : (q : ℤ) % 4 = 1 := by exact_mod_cast hq4
  refine {
    p := p, q := q, R := (π ^ 2).re, S := (π ^ 2).im, U := (ρ ^ 2).re, V := (ρ ^ 2).im
    p_ge := by exact_mod_cast hp5
    q_ge := by exact_mod_cast hq5
    odd_p := ⟨(p : ℤ) / 2, by omega⟩
    odd_q := ⟨(q : ℤ) / 2, by omega⟩
    odd_R := odd_re (oddEven_pow oπ 2)
    odd_U := odd_re (oddEven_pow oρ 2)
    odd_T := (fourth_re π) ▸ odd_re (oddEven_pow oπ 4)
    odd_X := (sixth_re π) ▸ odd_re (oddEven_pow oπ 6)
    four_S := four_dvd_square_im oπ
    R_zero := hπ2.1
    S_zero := hπ2.2
    U_zero := hρ2.1
    V_zero := hρ2.2
    p3 := int_prime_mod_three hp hp5
    q3 := int_prime_mod_three hq hq5
    norm_p := component_norm_power hπ 2
    norm_q := component_norm_power hρ 2 }

theorem nonTop_dvd (d : Data) (a : Leg) (h : ¬ Top a) : d.p ∣ d.value a := by
  cases a with
  | a1 => exact ⟨d.p * d.q * d.S, by unfold Data.value; ring⟩
  | a2 => exact ⟨d.q * d.W, by unfold Data.value; ring⟩
  | a3 => exact (h (Or.inl rfl)).elim
  | b1p => exact ⟨d.p * (d.S * d.U + 1 * d.R * d.V), by unfold Data.value Data.b₁; ring⟩
  | b1m => exact ⟨d.p * (d.S * d.U + (-1) * d.R * d.V), by unfold Data.value Data.b₁; ring⟩
  | b2p => exact ⟨d.W * d.U + 1 * d.T * d.V, rfl⟩
  | b2m => exact ⟨d.W * d.U + (-1) * d.T * d.V, rfl⟩
  | b3p => exact (h (Or.inr (Or.inl rfl))).elim
  | b3m => exact (h (Or.inr (Or.inr rfl))).elim
  | c => exact ⟨d.p ^ 2 * d.V, by unfold Data.value; ring⟩

end PerfectCuboid.P3Data
