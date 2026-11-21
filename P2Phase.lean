import GaussianPhase
import GaussianRepr
import P2Data

namespace PerfectCuboid.P2Phase

open GaussianPhase GaussianRepr
open P2Data (norm_eq_coe_of_normN)

theorem opposite_pow_dvd_star_mul (a z : GaussianInt) (n m : ℕ) (h : n ≤ m) :
    (star a) ^ n ∣ star (z * a ^ m) := by
  rw [star_mul, star_pow]
  exact dvd_mul_of_dvd_left (pow_dvd_pow (star a) h) _

theorem opposed_phase_imag_not_dvd {a z : GaussianInt} (ha : Prime a)
    (hz : ¬a ∣ z) (hstar : a ∣ star z) : ¬a.norm ∣ z.im := by
  intro hd
  have hdCast : a ∣ (z.im : GaussianInt) := by
    simpa using gaussian_pow_dvd_of_norm_pow_dvd (a := a) (n := 1) (by simpa using hd)
  have hdSquare : a ∣ ((z.im ^ 2 : ℤ) : GaussianInt) := by
    rw [Int.cast_pow]
    exact dvd_pow hdCast two_ne_zero
  have ht := dvd_phase_sq_sub_of_dvd_imag_sq_sub (y := 0) (ε := 0) hstar
    (by simp) (by simpa using hdSquare)
  exact hz (ha.dvd_of_dvd_pow (by simpa using ht))

private theorem pyth_square_congruence_middle {A B L l : ℤ} (h : Cuboid.P2.Pyth A B L)
    (hd : l ∣ A) : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ l ^ 2 ∣ B ^ 2 - e * L ^ 2 := by
  have hd' : l ^ 2 ∣ A ^ 2 := pow_dvd_pow_of_dvd hd 2
  rcases h with h | h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    convert (dvd_neg.mpr hd' : l ^ 2 ∣ -(A ^ 2)) using 1
    linear_combination h
  · refine ⟨1, Or.inl rfl, ?_⟩
    convert hd' using 1
    linear_combination -h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    convert hd' using 1
    linear_combination h

/-- Compare phases oriented along the same prime factor `a` and cancel
their common block, leaving just the gap `δ` of their `b`-exponents. -/
theorem backward_comparison_phase {p q m δ : ℕ} {a b : GaussianInt} {e : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (ha : normN a = q) (hb : normN b = p) (hm : δ ≤ m)
    (h : (q : ℤ) ^ 2 ∣
      (a ^ 2 * b ^ m).im ^ 2 - e * (a ^ 2 * (b ^ (m - δ) * (star b) ^ δ)).im ^ 2) :
    (star a) ^ 2 ∣ (b ^ δ) ^ 2 - (e : GaussianInt) * star ((b ^ δ) ^ 2) := by
  have haN := norm_eq_coe_of_normN ha
  have hbN := norm_eq_coe_of_normN hb
  have haSN : (star a).norm = (q : ℤ) := by simpa using haN
  have haP := prime_of_prime_norm hq ha
  have haSP : Prime (star a) := prime_of_prime_norm hq (by simpa using ha)
  have haC := conjugates_coprime_of_prime_norm hq hq2 haP haN
  let u := a ^ 2 * b ^ (m - δ)
  let x := b ^ δ
  have hu : ¬ star a ∣ u := by
    intro hu
    rcases haSP.dvd_mul.mp hu with hv | hv
    · exact haSP.not_isUnit (haC.symm.isUnit_of_dvd (haSP.dvd_of_dvd_pow hv))
    · exact not_dvd_of_distinct_prime_norms hq hp hpq.symm haSN hbN (haSP.dvd_of_dvd_pow hv)
  have hH : u * x = a ^ 2 * b ^ m := by
    dsimp [u, x]
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
  have hL : u * star x = a ^ 2 * (b ^ (m - δ) * (star b) ^ δ) := by
    dsimp [u, x]
    rw [star_pow, mul_assoc]
  have hHs : (star a) ^ 2 ∣ star (u * x) := by
    rw [hH, mul_comm]
    exact opposite_pow_dvd_star_mul a _ 2 2 (le_refl _)
  have hLs : (star a) ^ 2 ∣ star (u * star x) := by
    rw [hL, mul_comm]
    exact opposite_pow_dvd_star_mul a _ 2 2 (le_refl _)
  have hqd : (star a).norm ^ 2 ∣ (u * x).im ^ 2 - e * (u * star x).im ^ 2 := by
    rwa [haSN, hH, hL]
  have hphase := cancel_gaussian_phase_factor haSP hu hHs hLs
    (gaussian_pow_dvd_of_norm_pow_dvd hqd)
  simpa only [x, star_pow] using hphase

theorem backward_comparison {p q m δ : ℕ} {a b : GaussianInt} {e : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (ha : normN a = q) (hb : normN b = p) (he : e = 1 ∨ e = -1)
    (hδ : δ ≠ 0) (hm : δ ≤ m)
    (h : (q : ℤ) ^ 2 ∣
      (a ^ 2 * b ^ m).im ^ 2 - e * (a ^ 2 * (b ^ (m - δ) * (star b) ^ δ)).im ^ 2) :
    (q : ℤ) ^ 2 < (p : ℤ) ^ δ := by
  have haSN : (star a).norm = (q : ℤ) := by simpa using norm_eq_coe_of_normN ha
  have hbN := norm_eq_coe_of_normN hb
  have haSP : Prime (star a) := prime_of_prime_norm hq (by simpa using ha)
  have hbP := prime_of_prime_norm hp hb
  have hbC := conjugates_coprime_of_prime_norm hp hp2 hbP hbN
  have hC : ((b ^ δ) ^ 2).norm = ((p : ℤ) ^ δ) ^ 2 := by
    rw [← pow_mul]
    simpa [hbN, pow_mul] using norm_pow_mul b 1 (δ * 2) 0
  have hD : ((b ^ δ) ^ 2).re ≠ 0 ∧ ((b ^ δ) ^ 2).im ≠ 0 := by
    rw [← pow_mul]
    exact nonzero_components_of_one_sided_power hbP (Nat.mul_ne_zero hδ (by decide))
      (fun h => hbP.not_isUnit (hbC.isUnit_of_dvd h))
  have hQ : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hP : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have haCS := conjugates_coprime_of_prime_norm hq hq2 haSP haSN
  have hmod : IsCoprime ((star a).norm ^ 2) (2 : ℤ) := norm_pow_coprime_two hq hq2 haSN
  have hcoord := prime_power_dvd_signed_component haCS hmod he
    (backward_comparison_phase hp hq hpq hq2 ha hb hm h)
  have hbound := norm_power_lt_of_dvd_coordinate (haSN.symm ▸ hQ) (pow_pos hP δ) hC hD hcoord
  simpa [haSN] using hbound

/-- A phase with only one Gaussian direction at `p` has imaginary
coordinate prime to `p` whenever its remaining factor does. -/
theorem unit_imag_mul_pow {p : ℕ} {a z : GaussianInt} {n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : normN a = p) (hn : n ≠ 0) (hz : ¬ star a ∣ z) :
    ¬ (p : ℤ) ∣ (z * a ^ n).im := by
  have haN := norm_eq_coe_of_normN ha
  have haSN : (star a).norm = (p : ℤ) := by simpa using haN
  have haP := prime_of_prime_norm hp ha
  have haSP : Prime (star a) := prime_of_prime_norm hp (by simpa using ha)
  have haC := conjugates_coprime_of_prime_norm hp hp2 haP haN
  have hNZ : ¬ star a ∣ z * a ^ n := by
    intro h
    rcases haSP.dvd_mul.mp h with h | h
    · exact hz h
    · exact haSP.not_isUnit (haC.symm.isUnit_of_dvd (haSP.dvd_of_dvd_pow h))
  have hs : star a ∣ star (z * a ^ n) := by
    simpa using opposite_pow_dvd_star_mul a z 1 n (Nat.one_le_iff_ne_zero.mpr hn)
  rw [← haSN]
  exact opposed_phase_imag_not_dvd haSP hNZ hs

/-- Powers of a Gaussian factor at a different rational prime cannot
contain the given Gaussian prime. -/
theorem not_dvd_other_pow {p q : ℕ} {a b : GaussianInt} {n : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : normN a = p) (hb : normN b = q) :
    ¬ a ∣ b ^ n := by
  intro h
  exact not_dvd_of_distinct_prime_norms hp hq hpq (norm_eq_coe_of_normN ha)
    (norm_eq_coe_of_normN hb) ((prime_of_prime_norm hp ha).dvd_of_dvd_pow h)

theorem cast_eq_norm_factors {p : ℕ} {a : GaussianInt} (ha : normN a = p) :
    (p : GaussianInt) = a * star a := by
  rw [← Zsqrtd.norm_eq_mul_conj, norm_eq_coe_of_normN ha, Int.cast_natCast]

theorem not_dvd_other_natCast {p q : ℕ} {a b : GaussianInt}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : normN a = p) (hb : normN b = q) :
    ¬ a ∣ (q : GaussianInt) := by
  rw [cast_eq_norm_factors hb]
  intro h
  rcases (prime_of_prime_norm hp ha).dvd_mul.mp h with h | h
  · exact not_dvd_of_distinct_prime_norms hp hq hpq (norm_eq_coe_of_normN ha)
      (norm_eq_coe_of_normN hb) h
  · exact not_dvd_of_distinct_prime_norms hp hq hpq (norm_eq_coe_of_normN ha)
      (by simpa using norm_eq_coe_of_normN hb) h

open Cuboid.P2

section Candidates

variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
  (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) {π ρ : GaussianInt}
  (hπ : normN π = p) (hρ : normN ρ = q) (oπ : OddEven π) (oρ : OddEven ρ)

local notation "d" => P2Data.mkData hp hq hpq hp4 hq4 hπ hρ oπ oρ

private theorem B_imag : B d = ((q : GaussianInt) * π ^ 4).im := by
  change (q : ℤ) * (π ^ 4).im = ((q : GaussianInt) * π ^ 4).im
  simp [Zsqrtd.im_mul]

private theorem F_imag : F d = (π ^ 4 * ρ ^ 2).im := by
  change (π ^ 4).im * (ρ ^ 2).re + (π ^ 4).re * (ρ ^ 2).im = (π ^ 4 * ρ ^ 2).im
  simp [Zsqrtd.im_mul, add_comm]

private theorem G_imag : G d = (π ^ 4 * (star ρ) ^ 2).im := by
  change (π ^ 4).im * (ρ ^ 2).re - (π ^ 4).re * (ρ ^ 2).im = (π ^ 4 * (star ρ) ^ 2).im
  rw [← star_pow]
  simp only [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

private theorem unit_p : ∀ i : Fin 7, top i → ¬ (d).p ∣ leg d i := by
  have hπs : normN (star π) = p := by simpa using hπ
  have hρs : normN (star ρ) = q := by simpa using hρ
  have hp2 : p ≠ 2 := by omega
  have huB : ¬ (p : ℤ) ∣ ((q : GaussianInt) * π ^ 4).im :=
    unit_imag_mul_pow hp hp2 hπ (by decide)
      (not_dvd_other_natCast hp hq hpq hπs hρ)
  have huF : ¬ (p : ℤ) ∣ (ρ ^ 2 * π ^ 4).im :=
    unit_imag_mul_pow hp hp2 hπ (by decide) (not_dvd_other_pow hp hq hpq hπs hρ)
  have huG : ¬ (p : ℤ) ∣ ((star ρ) ^ 2 * π ^ 4).im :=
    unit_imag_mul_pow hp hp2 hπ (by decide) (not_dvd_other_pow hp hq hpq hπs hρs)
  intro i hi
  rcases hi with rfl | rfl | rfl
  · rw [show leg d 1 = B d from rfl, B_imag hp hq hpq hp4 hq4 hπ hρ oπ oρ]
    exact huB
  · rw [show leg d 5 = F d from rfl, F_imag hp hq hpq hp4 hq4 hπ hρ oπ oρ, mul_comm]
    exact huF
  · rw [show leg d 6 = G d from rfl, G_imag hp hq hpq hp4 hq4 hπ hρ oπ oρ, mul_comm]
    exact huG

private theorem divisible_p : ∀ i : Fin 7, ¬ top i → (d).p ∣ leg d i := by
  intro i hi
  fin_cases i
  · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · exact (hi (Or.inl rfl)).elim
  · exact dvd_mul_of_dvd_left (dvd_pow (dvd_refl _) two_ne_zero) _
  · exact dvd_mul_right _ _
  · exact dvd_mul_right _ _
  · exact (hi (Or.inr (Or.inl rfl))).elim
  · exact (hi (Or.inr (Or.inr rfl))).elim

private theorem unit_q_F : ¬ (d).q ∣ F d := by
  have hρs : normN (star ρ) = q := by simpa using hρ
  rw [F_imag hp hq hpq hp4 hq4 hπ hρ oπ oρ]
  exact unit_imag_mul_pow hq (by omega : q ≠ 2) hρ (by decide)
    (not_dvd_other_pow hq hp hpq.symm hρs hπ)

private theorem unit_q_G : ¬ (d).q ∣ G d := by
  have hρs : normN (star ρ) = q := by simpa using hρ
  rw [G_imag hp hq hpq hp4 hq4 hπ hρ oπ oρ]
  exact unit_imag_mul_pow hq (by omega : q ≠ 2) hρs (by decide)
    (by simpa using not_dvd_other_pow (n := 4) hq hp hpq.symm hρ hπ)

private theorem C_imag : C d = (ρ ^ 2 * ((p : GaussianInt) ^ 2)).im := by
  change (p : ℤ) ^ 2 * (ρ ^ 2).im = (ρ ^ 2 * ((p : GaussianInt) ^ 2)).im
  rw [show (p : GaussianInt) ^ 2 = ((p ^ 2 : ℕ) : GaussianInt) from (Nat.cast_pow p 2).symm]
  simp only [Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast, mul_zero]
  rw [Nat.cast_pow]
  ring

private theorem D_imag : D d = (ρ ^ 2 * ((p : GaussianInt) * π ^ 2)).im := by
  change (p : ℤ) * ((π ^ 2).im * (ρ ^ 2).re + (π ^ 2).re * (ρ ^ 2).im) =
    (ρ ^ 2 * ((p : GaussianInt) * π ^ 2)).im
  simp only [Zsqrtd.im_mul, Zsqrtd.re_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast,
    mul_zero, zero_mul, add_zero]
  ring

private theorem E_imag : E d = -(ρ ^ 2 * ((p : GaussianInt) * (star π) ^ 2)).im := by
  change (p : ℤ) * ((π ^ 2).im * (ρ ^ 2).re - (π ^ 2).re * (ρ ^ 2).im) =
    -(ρ ^ 2 * ((p : GaussianInt) * (star π) ^ 2)).im
  rw [← star_pow]
  simp only [Zsqrtd.im_mul, Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star,
    Zsqrtd.re_natCast, Zsqrtd.im_natCast, mul_zero, zero_mul, add_zero]
  ring

private theorem G_sq_oriented : (G d) ^ 2 = (ρ ^ 2 * (star π) ^ 4).im ^ 2 := by
  have h : ρ ^ 2 * (star π) ^ 4 = star (π ^ 4 * (star ρ) ^ 2) := by
    simp [star_mul, star_pow]
  rw [h, Zsqrtd.im_star, neg_sq, G_imag hp hq hpq hp4 hq4 hπ hρ oπ oρ]

private theorem phase_q : ∀ H L : ℤ, (H = F d ∨ H = G d) → lowerMixed d L →
    Pyth (B d) H L →
      ∃ k x : ℤ, x ≠ 0 ∧ x = (d).q ^ 2 * k ∧ x < (d).p ^ 3 ∧ -x < (d).p ^ 3 := by
  intro H L hH hL h
  obtain ⟨e, he, hd⟩ := pyth_square_congruence_middle h
    (show (q : ℤ) ∣ B d from ⟨(d).w, rfl⟩)
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hπs : normN (star π) = p := by simpa using hπ
  have hpow (b : GaussianInt) (hb : normN b = p) :
      (b ^ (4 - 1 : ℕ) * (star b) ^ 1 = (p : GaussianInt) * b ^ 2) ∧
      (b ^ (4 - 2 : ℕ) * (star b) ^ 2 = (p : GaussianInt) ^ 2) ∧
      (b ^ (4 - 3 : ℕ) * (star b) ^ 3 = (p : GaussianInt) * (star b) ^ 2) := by
    rw [cast_eq_norm_factors hb]
    constructor
    · norm_num
      ring
    · constructor <;> norm_num <;> ring
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.pos
  have hbound (b : GaussianInt) (hb : normN b = p) (δ : ℕ) (hδ : δ ≠ 0) (hδ3 : δ ≤ 3)
      (hHi : H ^ 2 = (ρ ^ 2 * b ^ 4).im ^ 2)
      (hLo : L ^ 2 = (ρ ^ 2 * (b ^ (4 - δ) * (star b) ^ δ)).im ^ 2) :
      (q : ℤ) ^ 2 < (p : ℤ) ^ 3 := by
    have hδ4 : δ ≤ 4 := by omega
    have hbnd := backward_comparison hp hq hpq hp2 hq2 hρ hb he hδ hδ4
      (by rwa [← hHi, ← hLo])
    exact hbnd.trans_le (pow_le_pow_right₀ hp1 hδ3)
  have hc := C_imag hp hq hpq hp4 hq4 hπ hρ oπ oρ
  have hdc := D_imag hp hq hpq hp4 hq4 hπ hρ oπ oρ
  have hec := E_imag hp hq hpq hp4 hq4 hπ hρ oπ oρ
  have hqbound : (q : ℤ) ^ 2 < (p : ℤ) ^ 3 := by
    rcases hH with rfl | rfl
    · have hHi : (F d) ^ 2 = (ρ ^ 2 * π ^ 4).im ^ 2 := by
        rw [F_imag hp hq hpq hp4 hq4 hπ hρ oπ oρ, mul_comm]
      rcases hL with rfl | rfl | rfl
      · exact hbound π hπ 2 (by decide) (by decide) hHi (by rw [(hpow π hπ).2.1, hc])
      · exact hbound π hπ 1 (by decide) (by decide) hHi (by rw [(hpow π hπ).1, hdc])
      · exact hbound π hπ 3 (by decide) (by decide) hHi
          (by rw [(hpow π hπ).2.2, hec, neg_sq])
    · have hHi := G_sq_oriented hp hq hpq hp4 hq4 hπ hρ oπ oρ
      rcases hL with rfl | rfl | rfl
      · exact hbound (star π) hπs 2 (by decide) (by decide) hHi
          (by rw [(hpow (star π) hπs).2.1, hc])
      · exact hbound (star π) hπs 3 (by decide) (by decide) hHi
          (by rw [(hpow (star π) hπs).2.2, star_star, hdc])
      · exact hbound (star π) hπs 1 (by decide) (by decide) hHi
          (by rw [(hpow (star π) hπs).1, hec, neg_sq])
  have hQ : (0 : ℤ) < q := by exact_mod_cast hq.pos
  refine ⟨1, (q : ℤ) ^ 2, pow_ne_zero 2 hQ.ne', ?_, hqbound, ?_⟩
  · change (q : ℤ) ^ 2 = (q : ℤ) ^ 2 * 1
    rw [mul_one]
  · change -(q : ℤ) ^ 2 < (p : ℤ) ^ 3
    nlinarith only [hqbound, sq_nonneg (q : ℤ)]

/-- The divisibility and both Gaussian phase comparisons needed by the
seven-state elimination. -/
theorem mkPhaseFacts : PhaseFacts d where
  unit_p := unit_p hp hq hpq hp4 hq4 hπ hρ oπ oρ
  divisible_p := divisible_p hp hq hpq hp4 hq4 hπ hρ oπ oρ
  unit_q_F := unit_q_F hp hq hpq hp4 hq4 hπ hρ oπ oρ
  unit_q_G := unit_q_G hp hq hpq hp4 hq4 hπ hρ oπ oρ
  phase_p := P2Data.phase_p hp hq hpq hp4 hq4 hπ hρ oπ oρ
  phase_q := phase_q hp hq hpq hp4 hq4 hπ hρ oπ oρ

end Candidates

end PerfectCuboid.P2Phase
