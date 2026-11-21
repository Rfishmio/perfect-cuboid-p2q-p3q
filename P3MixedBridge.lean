import GaussianPhase
import GaussianRepr
import P3Dispatch
import Mathlib.Data.Int.Lemmas

namespace FormalCuboid.P3

open PerfectCuboid.GaussianPhase PerfectCuboid.GaussianRepr

structure MixedData (d : Data) where
  p : ℕ
  q : ℕ
  hp : p.Prime
  hq : q.Prime
  distinct : p ≠ q
  π : GaussianInt
  ρ : GaussianInt
  normπ : normN π = p
  normρ : normN ρ = q
  eq_p : d.p = (p : ℤ)
  eq_q : d.q = (q : ℤ)
  realπ : (π ^ 2).re = d.R
  imagπ : (π ^ 2).im = d.S
  realρ : (ρ ^ 2).re = d.U
  imagρ : (ρ ^ 2).im = d.V

variable {d : Data} (g : MixedData d)

private theorem normπ_int : g.π.norm = d.p := by
  rw [g.eq_p, ← g.normπ]
  exact (Int.natAbs_of_nonneg (GaussianInt.norm_nonneg _)).symm

private theorem normρ_int : g.ρ.norm = d.q := by
  rw [g.eq_q, ← g.normρ]
  exact (Int.natAbs_of_nonneg (GaussianInt.norm_nonneg _)).symm

private theorem p_ne_two : g.p ≠ 2 := by
  have h := d.p_ge
  rw [g.eq_p] at h
  omega

private theorem q_ne_two : g.q ≠ 2 := by
  have h := d.q_ge
  rw [g.eq_q] at h
  omega

private theorem pi_star_prime : Prime (star g.π) :=
  prime_of_prime_norm g.hp (by simpa using g.normπ)

private theorem rho_star_prime : Prime (star g.ρ) :=
  prime_of_prime_norm g.hq (by simpa using g.normρ)

private theorem pi_star_coprime : IsCoprime (star g.π) g.π := by
  simpa using conjugates_coprime_of_prime_norm g.hp (p_ne_two g) (pi_star_prime g)
    (show (star g.π).norm = (g.p : ℤ) by rw [Zsqrtd.norm_conj, normπ_int g, g.eq_p])

private theorem rho_star_coprime : IsCoprime (star g.ρ) g.ρ := by
  simpa using conjugates_coprime_of_prime_norm g.hq (q_ne_two g) (rho_star_prime g)
    (show (star g.ρ).norm = (g.q : ℤ) by rw [Zsqrtd.norm_conj, normρ_int g, g.eq_q])

private theorem prime_not_dvd_of_coprime {a b : GaussianInt} (ha : Prime a)
    (hc : IsCoprime a b) : ¬ a ∣ b :=
  (ha.irreducible.coprime_iff_not_dvd).mp hc

private theorem pi_phase (u : GaussianInt) (hu : u = g.ρ ∨ u = star g.ρ) :
    ¬ star g.π ∣ u := by
  apply not_dvd_of_distinct_prime_norms g.hp g.hq g.distinct
  · simp [Zsqrtd.norm_conj, normπ_int g, g.eq_p]
  · rcases hu with rfl | rfl <;> simp [Zsqrtd.norm_conj, normρ_int g, g.eq_q]

private theorem rho_phase (u : GaussianInt) (hu : u = g.π ∨ u = star g.π) :
    ¬ star g.ρ ∣ u := by
  apply not_dvd_of_distinct_prime_norms g.hq g.hp (Ne.symm g.distinct)
  · simp [Zsqrtd.norm_conj, normρ_int g, g.eq_q]
  · rcases hu with rfl | rfl <;> simp [Zsqrtd.norm_conj, normπ_int g, g.eq_p]

private theorem no_dvd_pow {a b : GaussianInt} (ha : Prime a) (h : ¬ a ∣ b)
    (n : ℕ) : ¬ a ∣ b ^ n := fun hd => h (ha.dvd_of_dvd_pow hd)

private theorem pow_dvd_pow_gaussian (a : GaussianInt) {m n : ℕ} (h : m ≤ n) :
    a ^ m ∣ a ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨a ^ k, pow_add a m k⟩

private theorem dvd_mul_of_dvd_left {a b : GaussianInt} (h : a ∣ b) (c : GaussianInt) :
    a ∣ b * c := dvd_trans h (dvd_mul_right b c)

private theorem pi_four_coords : (g.π ^ 4).re = d.T ∧ (g.π ^ 4).im = d.W := by
  rw [show g.π ^ 4 = (g.π ^ 2) * (g.π ^ 2) by ring]
  simp [Zsqrtd.re_mul, Zsqrtd.im_mul, g.realπ, g.imagπ]
  constructor <;> ring

private theorem pi_six_coords : (g.π ^ 6).re = d.X ∧ (g.π ^ 6).im = d.Y := by
  rw [show g.π ^ 6 = g.π ^ 4 * g.π ^ 2 by ring]
  simp [Zsqrtd.re_mul, Zsqrtd.im_mul, g.realπ, g.imagπ, (pi_four_coords g).1,
    (pi_four_coords g).2]
  constructor <;> ring

private theorem q_orientation_norm (u : GaussianInt) (hu : u = g.ρ ∨ u = star g.ρ) :
    u.norm = d.q := by
  rcases hu with rfl | rfl <;> simp [Zsqrtd.norm_conj, normρ_int g]

private theorem im_top_plus : (g.π ^ 6 * g.ρ ^ 2).im = d.b₃ 1 := by
  simp [Zsqrtd.im_mul, g.realρ, g.imagρ, (pi_six_coords g).1, (pi_six_coords g).2, Data.b₃]
  ring

private theorem im_top_minus : (g.π ^ 6 * (star g.ρ) ^ 2).im = d.b₃ (-1) := by
  simp [← star_pow, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star, g.realρ, g.imagρ,
    (pi_six_coords g).1, (pi_six_coords g).2, Data.b₃]
  ring

private theorem forward_lower_bound (u : GaussianInt) (hu : u = g.ρ ∨ u = star g.ρ)
    (m : ℕ) (hm : m ≤ 6) {ε : ℤ} (he : Sign ε)
    (h : d.p ^ m ∣ d.a₃ ^ 2 - ε * (g.π ^ 6 * u ^ 2).im ^ 2) :
    d.p ^ m < d.q := by
  have hp : Prime (star g.π) := pi_star_prime g
  have hn : (star g.π).norm = (g.p : ℤ) := by
    rw [Zsqrtd.norm_conj, normπ_int g, g.eq_p]
  have huc : (u ^ 2).re ≠ 0 ∧ (u ^ 2).im ≠ 0 := by
    rcases hu with rfl | rfl
    · simpa [g.realρ, g.imagρ] using And.intro d.U_zero d.V_zero
    · simpa [← star_pow, Zsqrtd.re_star, Zsqrtd.im_star, g.realρ, g.imagρ] using
        And.intro d.U_zero d.V_zero
  have hx : (star g.π) ^ m ∣ star (g.π ^ 6 * (u.norm : GaussianInt)) := by
    simpa only [star_mul, star_pow, mul_comm] using
      dvd_mul_of_dvd_left (pow_dvd_pow_gaussian (star g.π) hm) (star (u.norm : GaussianInt))
  have hy : (star g.π) ^ m ∣ star (g.π ^ 6 * u ^ 2) := by
    simpa only [star_mul, star_pow, mul_comm] using
      dvd_mul_of_dvd_left (pow_dvd_pow_gaussian (star g.π) hm) ((star u) ^ 2)
  have hA : (g.π ^ 6 * (u.norm : GaussianInt)).im = d.a₃ := by
    simp [Zsqrtd.im_mul, q_orientation_norm g u hu, (pi_six_coords g).2, Data.a₃, mul_comm]
  have h' : (star g.π).norm ^ m ∣
      (g.π ^ 6 * (u.norm : GaussianInt)).im ^ 2 - ε * (g.π ^ 6 * u ^ 2).im ^ 2 := by
    rw [hA, Zsqrtd.norm_conj, normπ_int g]
    exact h
  have hlt := forward_norm_bound hp (by simpa using pi_star_coprime g)
    (norm_pow_coprime_two g.hp (p_ne_two g) hn)
    (by rw [Zsqrtd.norm_conj, normπ_int g]; linarith only [d.p_ge])
    (by rw [q_orientation_norm g u hu]; linarith only [d.q_ge])
    (no_dvd_pow hp (prime_not_dvd_of_coprime hp (pi_star_coprime g)) 6)
    (pi_phase g u hu) huc he hx hy h'
  simpa [Zsqrtd.norm_conj, normπ_int g, q_orientation_norm g u hu] using hlt

include g in
private theorem forward_triangle {L σ : ℤ} (hσ : Sign σ) (m : ℕ) (hm : m ≤ 6)
    (hL : d.p ^ m ∣ L ^ 2) (h : Triangle d.a₃ (d.b₃ σ) L) : d.p ^ m < d.q := by
  have bound {ε : ℤ} (he : Sign ε) (hd : d.p ^ m ∣ d.a₃ ^ 2 - ε * (d.b₃ σ) ^ 2) :
      d.p ^ m < d.q := by
    rcases hσ with rfl | rfl
    · apply forward_lower_bound g g.ρ (Or.inl rfl) m hm he
      rwa [im_top_plus g]
    · apply forward_lower_bound g (star g.ρ) (Or.inr rfl) m hm he
      rwa [im_top_minus g]
  rcases h with h | h | h
  · apply bound (ε := 1) (Or.inl rfl)
    convert hL using 1
    linarith only [h]
  · apply bound (ε := 1) (Or.inl rfl)
    convert (dvd_neg.mpr hL) using 1
    linarith only [h]
  · apply bound (ε := -1) (Or.inr rfl)
    convert hL using 1
    linarith only [h]

private theorem rho_norm_two_coprime (n : ℕ) : IsCoprime ((star g.ρ).norm ^ n) (2 : ℤ) :=
  norm_pow_coprime_two g.hq (q_ne_two g)
    (by rw [Zsqrtd.norm_conj, normρ_int g, g.eq_q])

private theorem q_oriented_component_nonzero {c : GaussianInt} (hc : c = g.π ∨ c = star g.π) :
    ¬ d.q ∣ (g.ρ ^ 2 * c ^ 6).im := by
  intro hd
  have hp := rho_star_prime g
  let z := g.ρ ^ 2 * c ^ 6
  have hprime : star g.ρ ∣ star z := by
    rw [show star z = (star g.ρ) ^ 2 * (star c) ^ 6 by simp [z]]
    exact dvd_mul_of_dvd_left (by exact ⟨star g.ρ, pow_two _⟩) _
  have hd' : star g.ρ ∣ ((z.im ^ 2 - (0 : ℤ) * (0 : GaussianInt).im ^ 2 : ℤ) : GaussianInt) := by
    have hcast := gaussian_pow_dvd_of_norm_pow_dvd (a := star g.ρ) (n := 1)
      (u := z.im ^ 2) (by simpa [z, Zsqrtd.norm_conj, normρ_int g] using dvd_pow hd (by decide : 2 ≠ 0))
    simpa using hcast
  have hpow : star g.ρ ∣ z ^ 2 := by
    simpa using dvd_phase_sq_sub_of_dvd_imag_sq_sub hprime (by simp) hd'
  have hZ := hp.dvd_of_dvd_pow hpow
  exact (hp.dvd_mul.mp hZ).elim
    (no_dvd_pow hp (prime_not_dvd_of_coprime hp (rho_star_coprime g)) 2)
    (no_dvd_pow hp (rho_phase g c hc) 6)

private theorem q_oriented_top_plus : (g.ρ ^ 2 * g.π ^ 6).im = d.b₃ 1 := by
  rw [mul_comm, im_top_plus g]

private theorem q_oriented_top_minus : (g.ρ ^ 2 * (star g.π) ^ 6).im = -d.b₃ (-1) := by
  rw [show g.ρ ^ 2 * (star g.π) ^ 6 = star (g.π ^ 6 * (star g.ρ) ^ 2) by simp [mul_comm],
    Zsqrtd.im_star, im_top_minus g]

include g in
theorem mixed_lowerA_mod_q (a : Leg) (ha : IsLowerA a) (σ : ℤ) (hσ : Sign σ) :
    Triangle d.a₃ (d.b₃ σ) (d.value a) → False := by
  intro h
  have hA : d.q ∣ d.a₃ := ⟨d.Y, rfl⟩
  have hB : d.q ∣ d.value a := by
    rcases ha with rfl | rfl
    · exact ⟨d.p ^ 2 * d.S, by unfold Data.value; ring⟩
    · exact ⟨d.p * d.W, by unfold Data.value; ring⟩
  have hsA := dvd_pow hA (by decide : 2 ≠ 0)
  have hsB := dvd_pow hB (by decide : 2 ≠ 0)
  have hs : d.q ∣ (d.b₃ σ) ^ 2 := by
    rcases h with h | h | h
    · convert dvd_sub hsA hsB using 1
      linarith only [h]
    · rw [h]
      exact dvd_add hsA hsB
    · convert dvd_sub hsB hsA using 1
      linarith only [h]
  have hq : Prime d.q := by
    rw [g.eq_q]
    exact Nat.prime_iff_prime_int.mp g.hq
  have ht := hq.dvd_of_dvd_pow hs
  rcases hσ with rfl | rfl
  · exact q_oriented_component_nonzero g (Or.inl rfl) (by rwa [q_oriented_top_plus g])
  · exact q_oriented_component_nonzero g (Or.inr rfl) (by simpa [q_oriented_top_minus g] using ht)

private def lowValue (d : Data) (j : ℕ) (τ : ℤ) : ℤ :=
  match j with
  | 0 => d.value .c
  | 1 => d.b₁ τ
  | _ => d.b₂ τ

private theorem low_square_dvd {j : ℕ} (hj : j = 0 ∨ j = 1 ∨ j = 2) (τ : ℤ) :
    d.p ^ (2 * (3 - j)) ∣ (lowValue d j τ) ^ 2 := by
  have h : d.p ^ (3 - j) ∣ lowValue d j τ := by
    rcases hj with rfl | rfl | rfl
    · exact ⟨d.V, rfl⟩
    · exact ⟨d.S * d.U + τ * d.R * d.V, rfl⟩
    · exact ⟨d.W * d.U + τ * d.T * d.V, by simp [lowValue, Data.b₂]⟩
  simpa only [pow_mul, Nat.mul_comm 2] using pow_dvd_pow_of_dvd h 2

private theorem q_row {c : GaussianInt} (hc : c = g.π ∨ c = star g.π)
    (j m : ℕ) :
    g.ρ ^ 2 * (c ^ (m + 2 * j) * (star c) ^ m) =
      (d.p : GaussianInt) ^ m * (g.ρ ^ 2 * c ^ (2 * j)) := by
  have hcn : c.norm = d.p := by
    rcases hc with rfl | rfl <;> simp [Zsqrtd.norm_conj, normπ_int g]
  have hprod : c * star c = (d.p : GaussianInt) := by
    rw [← Zsqrtd.norm_eq_mul_conj, hcn]
  rw [← hprod, mul_pow, pow_add]
  ring

private theorem cast_scale_im (z : GaussianInt) (t : ℤ) (m : ℕ) :
    ((t : GaussianInt) ^ m * z).im = t ^ m * z.im := by
  rw [← Int.cast_pow]
  simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, zero_mul, add_zero]

private theorem q_row_plus {j : ℕ} (hj : j = 0 ∨ j = 1 ∨ j = 2) :
    (g.ρ ^ 2 * (g.π ^ (3 + j) * (star g.π) ^ (3 - j))).im ^ 2 = (lowValue d j 1) ^ 2 := by
  have hidx : 3 + j = (3 - j) + 2 * j := by rcases hj with rfl | rfl | rfl <;> decide
  rw [hidx, q_row g (Or.inl rfl), cast_scale_im]
  rcases hj with rfl | rfl | rfl <;>
    simp [lowValue, Data.value, Data.b₁, Data.b₂, Zsqrtd.im_mul, g.realπ, g.imagπ,
      g.realρ, g.imagρ, (pi_four_coords g).1, (pi_four_coords g).2] <;> ring

private theorem q_row_minus {j : ℕ} (hj : j = 0 ∨ j = 1 ∨ j = 2) :
    (g.ρ ^ 2 * ((star g.π) ^ (3 + j) * g.π ^ (3 - j))).im ^ 2 = (lowValue d j (-1)) ^ 2 := by
  have hidx : 3 + j = (3 - j) + 2 * j := by rcases hj with rfl | rfl | rfl <;> decide
  rw [hidx]
  have h := q_row g (Or.inr rfl) j (3 - j)
  rw [star_star] at h
  rw [h, cast_scale_im]
  rcases hj with rfl | rfl | rfl <;>
    simp [lowValue, Data.value, Data.b₁, Data.b₂, Zsqrtd.im_mul, ← star_pow,
      Zsqrtd.re_star, Zsqrtd.im_star, g.realπ, g.imagπ, g.realρ, g.imagρ,
      (pi_four_coords g).1, (pi_four_coords g).2] <;> ring

private theorem q_phase_dvd {c : GaussianInt} (hc : c = g.π ∨ c = star g.π)
    {r s : ℕ} (hrs : r + s = 6) {ε : ℤ}
    (h : d.q ^ 2 ∣ (g.ρ ^ 2 * c ^ 6).im ^ 2 -
        ε * (g.ρ ^ 2 * (c ^ r * (star c) ^ s)).im ^ 2) :
    (star g.ρ) ^ 2 ∣ (c ^ s) ^ 2 - (ε : GaussianInt) * (star (c ^ s)) ^ 2 := by
  have hp := rho_star_prime g
  let u := g.ρ ^ 2 * c ^ r
  have hu : ¬ star g.ρ ∣ u := by
    intro hu
    exact (hp.dvd_mul.mp hu).elim
      (no_dvd_pow hp (prime_not_dvd_of_coprime hp (rho_star_coprime g)) 2)
      (no_dvd_pow hp (rho_phase g c hc) r)
  have hstar (x : GaussianInt) : (star g.ρ) ^ 2 ∣ star (u * x) := by
    rw [show star (u * x) = (star g.ρ) ^ 2 * ((star c) ^ r * star x) by simp [u, mul_assoc]]
    exact dvd_mul_right _ _
  apply cancel_gaussian_phase_factor hp hu (hstar (c ^ s)) (hstar (star (c ^ s)))
  apply gaussian_pow_dvd_of_norm_pow_dvd
  simpa only [u, Zsqrtd.norm_conj, normρ_int g, mul_assoc, ← pow_add, hrs, star_pow] using h

private theorem q_compare {j : ℕ} (hj : j = 0 ∨ j = 1 ∨ j = 2)
    {σ τ ε : ℤ} (hσ : Sign σ) (hτ : Sign τ)
    (h : d.q ^ 2 ∣ (d.b₃ σ) ^ 2 - ε * (lowValue d j τ) ^ 2) :
    ∃ c : GaussianInt, (c = g.π ∨ c = star g.π) ∧
      let k := if σ = τ then 3 - j else 3 + j
      (star g.ρ) ^ 2 ∣ (c ^ k) ^ 2 - (ε : GaussianInt) * (star (c ^ k)) ^ 2 := by
  have hle : j ≤ 3 := by rcases hj with rfl | rfl | rfl <;> decide
  have hpos : (3 + j) + (3 - j) = 6 := by omega
  have hneg : (3 - j) + (3 + j) = 6 := by omega
  have hTopMinus : (g.ρ ^ 2 * (star g.π) ^ 6).im ^ 2 = (d.b₃ (-1)) ^ 2 := by
    rw [q_oriented_top_minus g]
    ring
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
  · refine ⟨g.π, Or.inl rfl, ?_⟩
    simp only
    apply q_phase_dvd g (Or.inl rfl) hpos
    rwa [q_oriented_top_plus g, q_row_plus g hj]
  · refine ⟨g.π, Or.inl rfl, ?_⟩
    simp only [ite_eq_right (by decide : (1 : ℤ) ≠ -1)]
    apply q_phase_dvd g (Or.inl rfl) hneg
    rwa [q_oriented_top_plus g, mul_comm (g.π ^ (3 - j)), q_row_minus g hj]
  · refine ⟨star g.π, Or.inr rfl, ?_⟩
    simp only [ite_eq_right (by decide : (-1 : ℤ) ≠ 1)]
    apply q_phase_dvd g (Or.inr rfl) hneg
    rwa [hTopMinus, star_star, mul_comm ((star g.π) ^ (3 - j)), q_row_plus g hj]
  · refine ⟨star g.π, Or.inr rfl, ?_⟩
    simp only
    apply q_phase_dvd g (Or.inr rfl) hpos
    rwa [hTopMinus, star_star, q_row_minus g hj]

private theorem q_divides_triangle {L σ : ℤ} (h : Triangle d.a₃ (d.b₃ σ) L) :
    ∃ ε : ℤ, Sign ε ∧ d.q ^ 2 ∣ (d.b₃ σ) ^ 2 - ε * L ^ 2 := by
  have hd : d.q ^ 2 ∣ d.a₃ ^ 2 := ⟨d.Y ^ 2, by unfold Data.a₃; ring⟩
  rcases h with h | h | h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    convert hd using 1
    linarith only [h]
  · refine ⟨1, Or.inl rfl, ?_⟩
    convert hd using 1
    linarith only [h]
  · refine ⟨1, Or.inl rfl, ?_⟩
    convert dvd_neg.mpr hd using 1
    linarith only [h]

private theorem q_not_dvd_two : ¬ star g.ρ ∣ (2 : GaussianInt) := by
  intro h
  have h' : (star g.ρ) ^ 1 ∣ ((2 : ℤ) : GaussianInt) := by simpa using h
  have h₂ : g.q ∣ 2 := Int.natCast_dvd.mp (by
    simpa [Zsqrtd.norm_conj, normρ_int g, g.eq_q] using
      norm_pow_dvd_of_gaussian_pow_dvd_real (by simpa using rho_star_coprime g) h')
  rcases Nat.prime_two.eq_one_or_self_of_dvd g.q h₂ with h1 | h2
  · exact g.hq.ne_one h1
  · exact q_ne_two g h2

private theorem q_square_divisor_split {x : GaussianInt} (hx : ¬ star g.ρ ∣ x)
    (h : (star g.ρ) ^ 2 ∣ x ^ 2 - (star x) ^ 2) :
    d.q ^ 2 ∣ x.re ∨ d.q ^ 2 ∣ x.im := by
  let a := star g.ρ
  have ha : Prime a := rho_star_prime g
  have hm : a ^ 2 ∣ (x - star x) * (x + star x) := by
    convert h using 1
    ring
  have hcop : IsCoprime a (star a) := by simpa [a] using rho_star_coprime g
  have hTwo : IsCoprime (a.norm ^ 2) 2 := rho_norm_two_coprime g 2
  have hn : a.norm = d.q := by simp [a, Zsqrtd.norm_conj, normρ_int g]
  rw [← hn]
  by_cases hsub : a ∣ x - star x
  · have hadd : ¬ a ∣ x + star x := by
      intro hadd
      have htwo : a ∣ (2 : GaussianInt) * x := by
        convert dvd_add hsub hadd using 1
        ring
      exact (ha.dvd_mul.mp htwo).elim (q_not_dvd_two g) hx
    right
    exact hTwo.dvd_of_dvd_mul_left (norm_pow_dvd_of_phase_sub hcop
      (ha.pow_dvd_of_dvd_mul_left 2 hadd (by simpa [mul_comm] using hm)))
  · left
    exact hTwo.dvd_of_dvd_mul_left (norm_pow_dvd_of_phase_sum hcop
      (ha.pow_dvd_of_dvd_mul_left 2 hsub hm))

private theorem q_qsq_coord {x : GaussianInt} {ε : ℤ} (he : Sign ε)
    (h : (star g.ρ) ^ 2 ∣ x ^ 2 - (ε : GaussianInt) * (star x) ^ 2) :
    d.q ^ 2 ∣ (x ^ 2).re ∨ d.q ^ 2 ∣ (x ^ 2).im := by
  have hh := prime_power_dvd_signed_component (a := star g.ρ) (z := x ^ 2)
    (by simpa using rho_star_coprime g) (rho_norm_two_coprime g 2) he
    (by simpa only [star_pow] using h)
  simpa [Zsqrtd.norm_conj, normρ_int g] using hh

private theorem power_coord_bound {c : GaussianInt} (hc : c = g.π ∨ c = star g.π)
    {k : ℕ} (hk : k ≠ 0)
    (hd : d.q ^ 2 ∣ (c ^ k).re ∨ d.q ^ 2 ∣ (c ^ k).im) :
    d.q ^ 4 < d.p ^ k := by
  have hp : Prime c := by
    rcases hc with rfl | rfl
    · exact prime_of_prime_norm g.hp g.normπ
    · exact pi_star_prime g
  have hcop : IsCoprime c (star c) := by
    rcases hc with rfl | rfl
    · exact (pi_star_coprime g).symm
    · simpa using pi_star_coprime g
  obtain ⟨hR, hI⟩ := nonzero_components_of_one_sided_power hp hk
    (prime_not_dvd_of_coprime hp hcop)
  have hcn : c.norm = d.p := by
    rcases hc with rfl | rfl <;> simp [Zsqrtd.norm_conj, normπ_int g]
  have hn : (c ^ k).re ^ 2 + (c ^ k).im ^ 2 = d.p ^ k := by
    have h := norm_pow_mul c 1 k 0
    have h' : (c ^ k).norm = d.p ^ k := by simpa [hcn] using h
    simp only [Zsqrtd.norm_def] at h'
    nlinarith only [h']
  have sq_bound {x : ℤ} (hx : x ≠ 0) (hd : d.q ^ 2 ∣ x) : d.q ^ 4 ≤ x ^ 2 := by
    obtain ⟨t, ht⟩ := hd
    have htn : t ≠ 0 := by rintro rfl; simp at ht; exact hx ht
    have ht1 : 1 ≤ t ^ 2 := by have := sq_pos_of_ne_zero htn; omega
    have hmul := mul_nonneg (sq_nonneg (d.q ^ 2)) (sub_nonneg.mpr ht1)
    rw [ht]
    nlinarith only [hmul]
  rcases hd with hd | hd
  · linarith only [hn, sq_bound hR hd, sq_pos_of_ne_zero hI]
  · linarith only [hn, sq_bound hI hd, sq_pos_of_ne_zero hR]

include g in
private theorem bottom_bounds {j : ℕ} (hj : j = 0 ∨ j = 1) {σ τ : ℤ}
    (hσ : Sign σ) (hτ : Sign τ) (h : Triangle d.a₃ (d.b₃ σ) (lowValue d j τ)) :
    d.p ^ 4 < d.q ∧ d.q ^ 2 < d.p ^ 4 := by
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := hj.imp_right Or.inl
  have hm : 2 * (3 - j) ≤ 6 := by rcases hj with rfl | rfl <;> decide
  have hm4 : 4 ≤ 2 * (3 - j) := by rcases hj with rfl | rfl <;> decide
  have hp : 1 ≤ d.p := by linarith only [d.p_ge]
  have hforward := forward_triangle g hσ _ hm (low_square_dvd hj' τ) h
  refine ⟨lt_of_le_of_lt (pow_le_pow_right₀ hp hm4) hforward, ?_⟩
  obtain ⟨ε, he, hε⟩ := q_divides_triangle h
  obtain ⟨c, hc, hd⟩ := q_compare g hj' hσ hτ hε
  let k := if σ = τ then 3 - j else 3 + j
  have hk : k ≠ 0 := by dsimp [k]; split <;> omega
  have hk8 : k * 2 ≤ 8 := by dsimp [k]; split <;> omega
  have hkd := q_qsq_coord g he (show (star g.ρ) ^ 2 ∣
      (c ^ k) ^ 2 - (ε : GaussianInt) * (star (c ^ k)) ^ 2 from hd)
  have hback := power_coord_bound g hc (show k * 2 ≠ 0 by omega)
    (by simpa only [pow_mul] using hkd)
  have hstrict : d.q ^ 4 < d.p ^ 8 := lt_of_lt_of_le hback (pow_le_pow_right₀ hp hk8)
  apply lt_of_pow_lt_pow_left₀ 2 (show 0 ≤ d.p ^ 4 by positivity)
  simpa only [← pow_mul] using hstrict

include g in
theorem mixed_bottom_mixed_bounds (a : Leg) (ha : IsBottomMixed a) (σ : ℤ) (hσ : Sign σ) :
    Triangle d.a₃ (d.b₃ σ) (d.value a) → d.p ^ 4 < d.q ∧ d.q ^ 2 < d.p ^ 4 := by
  intro h
  rcases ha with rfl | rfl | rfl
  · exact bottom_bounds g (j := 1) (Or.inr rfl) hσ (Or.inl rfl) h
  · exact bottom_bounds g (j := 1) (Or.inr rfl) hσ (Or.inr rfl) h
  · exact bottom_bounds g (j := 0) (Or.inl rfl) hσ hσ h

include g in
theorem mixed_middle_a₃_leg (σ τ : ℤ) (hσ : Sign σ) (hτ : Sign τ) :
    (d.b₃ σ) ^ 2 - (d.b₂ τ) ^ 2 = d.a₃ ^ 2 ∨
      (d.b₂ τ) ^ 2 - (d.b₃ σ) ^ 2 = d.a₃ ^ 2 →
    d.p ^ 2 < d.q ∧ d.q ^ 4 < d.p ^ 5 := by
  intro h
  have ht : Triangle d.a₃ (d.b₃ σ) (d.b₂ τ) := by
    rcases h with h | h
    · exact Or.inr (Or.inl (by linarith only [h]))
    · exact Or.inr (Or.inr (by linarith only [h]))
  have hpq : d.p ^ 2 < d.q := forward_triangle g hσ 2 (by decide)
    (low_square_dvd (j := 2) (Or.inr (Or.inr rfl)) τ) ht
  refine ⟨hpq, ?_⟩
  have hA : d.q ^ 2 ∣ d.a₃ ^ 2 := ⟨d.Y ^ 2, by unfold Data.a₃; ring⟩
  have hd : d.q ^ 2 ∣ (d.b₃ σ) ^ 2 - 1 * (lowValue d 2 τ) ^ 2 := by
    rcases h with h | h
    · simpa [lowValue, h] using hA
    · have h' := dvd_neg.mpr hA
      convert h' using 1
      change d.b₃ σ ^ 2 - 1 * (d.b₂ τ) ^ 2 = -d.a₃ ^ 2
      linarith only [h]
  obtain ⟨c, hc, hphase⟩ := q_compare g (Or.inr (Or.inr rfl)) hσ hτ hd
  let k := if σ = τ then 1 else 5
  have hk : k ≠ 0 := by dsimp [k]; split <;> decide
  have hk5 : k ≤ 5 := by dsimp [k]; split <;> decide
  have hcoord := q_square_divisor_split g
    (no_dvd_pow (rho_star_prime g) (rho_phase g c hc) k)
    (by simpa [k] using hphase)
  exact lt_of_lt_of_le (power_coord_bound g hc hk hcoord)
    (pow_le_pow_right₀ (by linarith only [d.p_ge]) hk5)

private theorem pi_ten_real : (g.π ^ 10).re = d.R * finalDiscriminant d.R d.S := by
  rw [show g.π ^ 10 = g.π ^ 6 * g.π ^ 4 by ring]
  simp [Zsqrtd.re_mul, (pi_six_coords g).1, (pi_six_coords g).2,
    (pi_four_coords g).1, (pi_four_coords g).2, finalDiscriminant]
  ring

include g in
theorem mixed_middle_a₃_hyp (σ τ : ℤ) (hσ : Sign σ) (hτ : Sign τ) :
    (d.b₃ σ) ^ 2 + (d.b₂ τ) ^ 2 = d.a₃ ^ 2 →
    τ = -σ ∧ d.p ^ 2 < d.q ∧ d.q ^ 2 ∣ finalDiscriminant d.R d.S := by
  intro h
  have ht : Triangle d.a₃ (d.b₃ σ) (d.b₂ τ) := Or.inl h.symm
  have hpq : d.p ^ 2 < d.q := forward_triangle g hσ 2 (by decide)
    (low_square_dvd (j := 2) (Or.inr (Or.inr rfl)) τ) ht
  have hA : d.q ^ 2 ∣ d.a₃ ^ 2 := ⟨d.Y ^ 2, by unfold Data.a₃; ring⟩
  have hd : d.q ^ 2 ∣ (d.b₃ σ) ^ 2 - (-1) * (lowValue d 2 τ) ^ 2 := by
    convert hA using 1
    change d.b₃ σ ^ 2 - (-1) * (d.b₂ τ) ^ 2 = d.a₃ ^ 2
    linarith only [h]
  obtain ⟨c, hc, hphase⟩ := q_compare g (Or.inr (Or.inr rfl)) hσ hτ hd
  have hpq' : d.p < d.q := by
    exact lt_of_le_of_lt (by nlinarith only [d.p_ge, sq_nonneg (d.p - 1)]) hpq
  have hpq2 : d.p ^ 2 < d.q ^ 2 := pow_lt_pow_left₀ hpq' (by linarith only [d.p_ge]) (by decide)
  have hneq : σ ≠ τ := by
    intro heq
    have hz : (star g.ρ) ^ 2 ∣ c ^ 2 - ((-1 : ℤ) : GaussianInt) * (star c) ^ 2 := by
      simpa [heq] using hphase
    have hcomp := q_qsq_coord g (Or.inr rfl) hz
    have hqbound := power_coord_bound g hc (k := 2) (by decide) hcomp
    have hqq : d.q ^ 2 ≤ d.q ^ 4 := by
      convert pow_le_pow_right₀ (show 1 ≤ d.q by linarith only [d.q_ge]) (show 2 ≤ 4 by decide)
    linarith only [hpq2, hqbound, hqq]
  have hsign : τ = -σ := by rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> omega
  refine ⟨hsign, hpq, ?_⟩
  have hz : (star g.ρ) ^ 2 ∣ c ^ 10 + star (c ^ 10) := by
    have hphase' : (star g.ρ) ^ 2 ∣ (c ^ 5) ^ 2 - ((-1 : ℤ) : GaussianInt) * (star (c ^ 5)) ^ 2 := by
      simpa [hneq] using hphase
    simpa [star_pow, show (c ^ 5) ^ 2 = c ^ 10 by ring,
      show ((star c) ^ 5) ^ 2 = (star c) ^ 10 by ring] using hphase'
  have hzdiv := (rho_norm_two_coprime g 2).dvd_of_dvd_mul_left
    (norm_pow_dvd_of_phase_sum (by simpa using rho_star_coprime g) hz)
  have hpdiv : d.q ^ 2 ∣ d.R * finalDiscriminant d.R d.S := by
    rcases hc with rfl | rfl
    · simpa [Zsqrtd.norm_conj, normρ_int g, pi_ten_real g] using hzdiv
    · simpa [Zsqrtd.norm_conj, normρ_int g, ← star_pow, Zsqrtd.re_star, pi_ten_real g] using hzdiv
  have hRbound : d.R.natAbs < d.q.natAbs := (Int.natAbs_lt_iff_sq_lt).mpr
    (by linarith only [hpq2, d.norm_p, sq_nonneg d.S])
  have hR : ¬ d.q ∣ d.R := fun h =>
    (not_le_of_gt hRbound) (Nat.le_of_dvd (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr d.R_zero))
      (Int.natAbs_dvd_natAbs.mpr h))
  have hq : Prime d.q := by
    rw [g.eq_q]
    exact Nat.prime_iff_prime_int.mp g.hq
  exact hq.pow_dvd_of_dvd_mul_left 2 hR hpdiv

end FormalCuboid.P3
