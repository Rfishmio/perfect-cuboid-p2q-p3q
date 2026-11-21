import GaussianPhase
import GaussianRepr
import P2Core

namespace PerfectCuboid.P2Data

open GaussianRepr GaussianPhase

theorem norm_eq_coe_of_normN {z : GaussianInt} {p : ℕ}
    (h : normN z = p) : z.norm = (p : ℤ) := by
  rw [← h]
  exact (Int.natAbs_of_nonneg (GaussianInt.norm_nonneg z)).symm

private theorem norm_coords (z : GaussianInt) : z.re ^ 2 + z.im ^ 2 = z.norm := by
  simp only [Zsqrtd.norm_def]
  ring

private theorem norm_power {z : GaussianInt} (n : ℕ) : (z ^ n).norm = z.norm ^ n := by
  simpa using norm_pow_mul z 1 n 0

private theorem pow_dvd_self {z : GaussianInt} {n : ℕ} (hn : n ≠ 0) : z ∣ z ^ n := by
  cases n with
  | zero => contradiction
  | succ n =>
    refine ⟨z ^ n, ?_⟩
    rw [pow_succ, mul_comm]

private theorem gaussian_star_not_dvd_of_prime_norm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {z : GaussianInt} (hz : normN z = p) : ¬ z ∣ star z :=
  (prime_of_prime_norm hp hz).irreducible.coprime_iff_not_dvd.mp
    (conjugates_coprime_of_prime_norm hp hp2 (prime_of_prime_norm hp hz)
      (norm_eq_coe_of_normN hz))

private theorem dvd_cast_of_prime_norm {p : ℕ} {z : GaussianInt} (hz : normN z = p)
    {x : ℤ} (hx : (p : ℤ) ∣ x) : z ∣ (x : GaussianInt) := by
  have hd : z.norm ^ 1 ∣ x := by simpa [norm_eq_coe_of_normN hz] using hx
  simpa using gaussian_pow_dvd_of_norm_pow_dvd (a := z) hd

/-- Neither coordinate of a positive power in one Gaussian prime direction is
divisible by the corresponding rational prime. -/
theorem prime_not_dvd_coords_of_power {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {z : GaussianInt} (hz : normN z = p) (hn : n ≠ 0) :
    (¬ (p : ℤ) ∣ (z ^ n).re) ∧ (¬ (p : ℤ) ∣ (z ^ n).im) := by
  have hzp : Prime z := prime_of_prime_norm hp hz
  have hstar : ¬ z ∣ star (z ^ n) := by
    rw [star_pow]
    exact fun hd => gaussian_star_not_dvd_of_prime_norm hp hp2 hz (hzp.dvd_of_dvd_pow hd)
  have hzpow : z ∣ z ^ n := pow_dvd_self hn
  constructor
  · intro hd
    have hd' := dvd_mul_of_dvd_right (dvd_cast_of_prime_norm hz hd) (2 : GaussianInt)
    have he : ((2 : GaussianInt) * ((z ^ n).re : GaussianInt)) = z ^ n + star (z ^ n) := by
      apply Zsqrtd.ext
      · rw [Zsqrtd.re_add, Zsqrtd.re_star]
        simp [two_mul]
      · rw [Zsqrtd.im_add, Zsqrtd.im_star]
        simp [Zsqrtd.im_mul]
    exact hstar (by simpa [he] using dvd_sub hd' hzpow)
  · intro hd
    let i : GaussianInt := ⟨0, 1⟩
    have hd' := dvd_mul_of_dvd_right (dvd_cast_of_prime_norm hz hd) (i * 2)
    have he : (i * 2) * ((z ^ n).im : GaussianInt) = z ^ n - star (z ^ n) := by
      apply Zsqrtd.ext
      · rw [Zsqrtd.re_sub, Zsqrtd.re_star]
        simp [i, Zsqrtd.re_mul, Zsqrtd.im_mul]
      · rw [Zsqrtd.im_sub, Zsqrtd.im_star]
        simp [i, Zsqrtd.re_mul, Zsqrtd.im_mul]
        ring
    exact hstar (by simpa [he] using dvd_sub hzpow hd')

private theorem gcd_one_of_no_common_prime {x y : ℤ}
    (h : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ x → (r : ℤ) ∣ y → False) : Int.gcd x y = 1 := by
  by_contra hd
  obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hd
  have hrg' : (r : ℤ) ∣ (Int.gcd x y : ℤ) := by exact_mod_cast hrg
  exact h r hr (dvd_trans hrg' (Int.gcd_dvd_left x y)) (dvd_trans hrg' (Int.gcd_dvd_right x y))

private theorem no_common_prime_of_gcd_one {x y : ℤ} (h : Int.gcd x y = 1)
    {r : ℕ} (hr : r.Prime) (hx : (r : ℤ) ∣ x) (hy : (r : ℤ) ∣ y) : False := by
  have hd : r ∣ Int.gcd x y := by
    rw [Int.gcd_def]
    exact Nat.dvd_gcd (Int.natCast_dvd.mp hx) (Int.natCast_dvd.mp hy)
  exact hr.ne_one (Nat.dvd_one.mp (h ▸ hd))

private theorem prime_dvd_int_sq {r : ℕ} (hr : r.Prime) {x : ℤ}
    (h : (r : ℤ) ∣ x ^ 2) : (r : ℤ) ∣ x := by
  apply Int.natCast_dvd.mpr
  apply hr.dvd_of_dvd_pow
  simpa only [Int.natAbs_pow] using Int.natCast_dvd.mp h

private theorem prime_eq_of_dvd_natcast_pow {p r n : ℕ} (hp : p.Prime) (hr : r.Prime)
    (h : (r : ℤ) ∣ (p : ℤ) ^ n) : r = p :=
  (Nat.prime_dvd_prime_iff_eq hr hp).mp
    (hr.dvd_of_dvd_pow (by exact_mod_cast h : r ∣ p ^ n))

theorem gcd_coords_of_power {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {z : GaussianInt} (hz : normN z = p) (hn : n ≠ 0) :
    Int.gcd (z ^ n).re (z ^ n).im = 1 := by
  apply gcd_one_of_no_common_prime
  intro r hr hx hy
  have hd : (r : ℤ) ∣ (p : ℤ) ^ n := by
    rw [← norm_eq_coe_of_normN hz, ← norm_power n, ← norm_coords]
    simpa only [pow_two] using
      dvd_add (dvd_mul_of_dvd_left hx (z ^ n).re) (dvd_mul_of_dvd_left hy (z ^ n).im)
  have hrp := prime_eq_of_dvd_natcast_pow hp hr hd
  exact (prime_not_dvd_coords_of_power hp hp2 hz hn).1 (hrp ▸ hx)

private theorem dvd_of_dvd_two_mul {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {x : ℤ}
    (h : (r : ℤ) ∣ 2 * x) : (r : ℤ) ∣ x := by
  apply Int.natCast_dvd.mpr
  have hd : r ∣ 2 * x.natAbs := by simpa [Int.natAbs_mul] using Int.natCast_dvd.mp h
  exact (hr.dvd_mul.mp hd).resolve_left (fun h2 => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2))

theorem gcd_pm_of_odd_even {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 0)
    (hxy : Int.gcd x y = 1) : Int.gcd (x - y) (x + y) = 1 := by
  apply gcd_one_of_no_common_prime
  intro r hr hm hp
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hm
    norm_num at hk
    omega
  have htwoX : (r : ℤ) ∣ 2 * x := by
    convert dvd_add hm hp using 1
    ring
  have htwoY : (r : ℤ) ∣ 2 * y := by
    convert dvd_sub hp hm using 1
    ring
  exact no_common_prime_of_gcd_one hxy hr (dvd_of_dvd_two_mul hr hr2 htwoX) (dvd_of_dvd_two_mul hr hr2 htwoY)

private theorem gcd_real_square_real {x y t : ℤ} (hxy : Int.gcd x y = 1)
    (h : t = x ^ 2 - y ^ 2) : Int.gcd x t = 1 := by
  apply gcd_one_of_no_common_prime
  intro r hr hx ht
  have hd : (r : ℤ) ∣ y ^ 2 := by
    have hx' : (r : ℤ) ∣ x ^ 2 := by simpa only [pow_two] using dvd_mul_of_dvd_left hx x
    convert dvd_sub hx' ht using 1
    rw [h]
    ring
  exact no_common_prime_of_gcd_one hxy hr hx (prime_dvd_int_sq hr hd)

theorem gcd_prime_power_of_not_dvd {p n : ℕ} (hp : p.Prime) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) : Int.gcd ((p : ℤ) ^ n) x = 1 := by
  apply gcd_one_of_no_common_prime
  intro r hr hrp hrx
  exact hx (prime_eq_of_dvd_natcast_pow hp hr hrp ▸ hrx)

private theorem prime_not_dvd_int_mul {p : ℕ} (hp : p.Prime) {x y : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) (hy : ¬ (p : ℤ) ∣ y) : ¬ (p : ℤ) ∣ x * y := by
  intro h
  have hNat : p ∣ x.natAbs * y.natAbs := by simpa only [Int.natAbs_mul] using Int.natCast_dvd.mp h
  exact (hp.dvd_mul.mp hNat).elim (fun h => hx (Int.natCast_dvd.mpr h)) (fun h => hy (Int.natCast_dvd.mpr h))

private theorem prime_not_dvd_small_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (n : ℕ) : ¬ (p : ℤ) ∣ (2 : ℤ) ^ n :=
  fun hd => hp2 (prime_eq_of_dvd_natcast_pow Nat.prime_two hp hd)

theorem gcd_prime_power_mul_coords {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x y : ℤ} (hx : ¬ (p : ℤ) ∣ x) (hy : ¬ (p : ℤ) ∣ y) (k : ℕ) :
    Int.gcd ((p : ℤ) ^ n) ((2 : ℤ) ^ k * x * y) = 1 :=
  gcd_prime_power_of_not_dvd hp
    (prime_not_dvd_int_mul hp (prime_not_dvd_int_mul hp (prime_not_dvd_small_pow hp hp2 k) hx) hy)

private theorem coords_sq (z : GaussianInt) :
    (z ^ 2).re = z.re ^ 2 - z.im ^ 2 ∧ (z ^ 2).im = 2 * z.re * z.im := by
  rw [pow_two]
  constructor <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

theorem mod_of_oddEven {z : GaussianInt} (h : OddEven z) :
    z.re % 2 = 1 ∧ z.im % 2 = 0 := by
  obtain ⟨a, b, ha, hb⟩ := h
  omega

private theorem prime_ne_two {p : ℕ} (hp4 : p % 4 = 1) : p ≠ 2 := by omega

private theorem prime_ge_five {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    5 ≤ (p : ℤ) := by
  have := hp.two_le
  omega

/-- Evaluate the Gaussian coordinate arithmetic required by the seven-state proof. -/
def mkData {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (_hpq : p ≠ q)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) {π ρ : GaussianInt}
    (hπ : normN π = p) (hρ : normN ρ = q) (oπ : OddEven π) (oρ : OddEven ρ) :
    Cuboid.P2.Data := by
  have hp2 := prime_ne_two hp4
  have hq2 := prime_ne_two hq4
  have np := norm_eq_coe_of_normN hπ
  have nq := norm_eq_coe_of_normN hρ
  have hpπ := prime_of_prime_norm hp hπ
  have hqρ := prime_of_prime_norm hq hρ
  have π2ne := nonzero_components_of_one_sided_power hpπ (by decide : (2 : ℕ) ≠ 0)
    (gaussian_star_not_dvd_of_prime_norm hp hp2 hπ)
  have π4ne := nonzero_components_of_one_sided_power hpπ (by decide : (4 : ℕ) ≠ 0)
    (gaussian_star_not_dvd_of_prime_norm hp hp2 hπ)
  have ρ2ne := nonzero_components_of_one_sided_power hqρ (by decide : (2 : ℕ) ≠ 0)
    (gaussian_star_not_dvd_of_prime_norm hq hq2 hρ)
  have π2gcd := gcd_coords_of_power hp hp2 hπ (by decide : (2 : ℕ) ≠ 0)
  have π4gcd := gcd_coords_of_power hp hp2 hπ (by decide : (4 : ℕ) ≠ 0)
  have ρ2gcd := gcd_coords_of_power hq hq2 hρ (by decide : (2 : ℕ) ≠ 0)
  have ρ1gcd : Int.gcd ρ.re ρ.im = 1 := by
    simpa using gcd_coords_of_power hq hq2 hρ (by decide : (1 : ℕ) ≠ 0)
  have π2nd := prime_not_dvd_coords_of_power hp hp2 hπ (by decide : (2 : ℕ) ≠ 0)
  have π4nd := prime_not_dvd_coords_of_power hp hp2 hπ (by decide : (4 : ℕ) ≠ 0)
  have ρ2nd := prime_not_dvd_coords_of_power hq hq2 hρ (by decide : (2 : ℕ) ≠ 0)
  have π2par := mod_of_oddEven (oddEven_pow oπ 2)
  have π4par := mod_of_oddEven (oddEven_pow oπ 4)
  have ρ2par := mod_of_oddEven (oddEven_pow oρ 2)
  have ρ1par := mod_of_oddEven oρ
  have π4eq : π ^ 4 = (π ^ 2)^2 := by ring
  have π4re : (π ^ 4).re = (π ^ 2).re ^ 2 - (π ^ 2).im ^ 2 := by
    rw [π4eq]
    exact (coords_sq _).1
  refine {
    p := p
    q := q
    r := (π ^ 2).re
    s := (π ^ 2).im
    t := (π ^ 4).re
    w := (π ^ 4).im
    u := (ρ ^ 2).re
    v := (ρ ^ 2).im
    m := ρ.re
    n := ρ.im
    hp := prime_ge_five hp hp4
    hq := prime_ge_five hq hq4
    pp := by simpa using hp
    qp := by simpa using hq
    hp_odd := by omega
    hq_odd := by omega
    hr_odd := π2par.1
    ht_odd := π4par.1
    hu_odd := ρ2par.1
    hs_even := π2par.2
    hw_even := π4par.2
    hr_nz := π2ne.1
    hs_nz := π2ne.2
    ht_nz := π4ne.1
    hw_nz := π4ne.2
    hu_nz := ρ2ne.1
    hv_nz := ρ2ne.2
    rs := by rw [norm_coords, norm_power, np]
    tw := by rw [norm_coords, norm_power, np]
    uv := by rw [norm_coords, norm_power, nq]
    t_eq := π4re
    w_eq := by rw [π4eq]; exact (coords_sq _).2
    u_eq := (coords_sq _).1
    v_eq := (coords_sq _).2
    gcd_tw := π4gcd
    gcd_uv := ρ2gcd
    gcd_rt := gcd_real_square_real π2gcd π4re
    gcd_rs_pm := gcd_pm_of_odd_even π2par.1 π2par.2 π2gcd
    gcd_mn_pm := gcd_pm_of_odd_even ρ1par.1 ρ1par.2 ρ1gcd
    gcd_q2_4uv := gcd_prime_power_mul_coords hq hq2 ρ2nd.1 ρ2nd.2 2
    gcd_p4_4wt := gcd_prime_power_mul_coords hp hp2 π4nd.2 π4nd.1 2
    gcd_p2_8rt := gcd_prime_power_mul_coords hp hp2 π2nd.1 π4nd.1 3
    gcd_q2_8uv := gcd_prime_power_mul_coords hq hq2 ρ2nd.1 ρ2nd.2 3
  }


private theorem star_dvd_of_pi_four (π x : GaussianInt) :
    (star π) ^ 2 ∣ star (π ^ 4 * x) := by
  refine ⟨(star π) ^ 2 * star x, ?_⟩
  rw [star_mul, star_pow]
  ring

private theorem phase_p_comparison {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hp2 : p ≠ 2) {π z : GaussianInt}
    (hπ : normN π = p) (hz : normN z = q) {e : ℤ} (he : e = 1 ∨ e = -1)
    (h : (p : ℤ) ^ 2 ∣ ((π ^ 4 * (z.norm : GaussianInt)).im) ^ 2 -
      e * ((π ^ 4 * z ^ 2).im) ^ 2) :
    (p : ℤ) ^ 2 ∣ (z ^ 2).re ∨ (p : ℤ) ^ 2 ∣ (z ^ 2).im := by
  have hπs : normN (star π) = p := by simpa using hπ
  have hnp := norm_eq_coe_of_normN hπs
  have hnz := norm_eq_coe_of_normN hz
  have hπp := prime_of_prime_norm hp hπs
  have hπc := conjugates_coprime_of_prime_norm hp hp2 hπp hnp
  have hu : ¬ star π ∣ π ^ 4 := by
    intro hd
    have hs := hπp.irreducible.coprime_iff_not_dvd.mp hπc
    exact hs (by simpa using hπp.dvd_of_dvd_pow hd)
  have hv := not_dvd_of_distinct_prime_norms hp hq hpq hnp hnz
  have hdiv := cancel_gaussian_phase_factor (n := 2) hπp hu
    (star_dvd_of_pi_four π (z.norm : GaussianInt)) (star_dvd_of_pi_four π (z ^ 2))
    (gaussian_pow_dvd_of_norm_pow_dvd (a := star π) (by rwa [hnp]))
  have hdiv' : (star π) ^ 2 ∣ (z.norm : GaussianInt) ^ 2 - (e : GaussianInt) * z ^ 4 := by
    simpa only [show (z ^ 2)^2 = z ^ 4 by ring] using hdiv
  simpa only [hnp] using
    prime_power_dvd_phase_coordinate hπp hπc (norm_pow_coprime_two hp hp2 hnp) hv he hdiv'

private theorem pyth_sq_congr {p x y z : ℤ} (hd : p ∣ z)
    (h : Cuboid.P2.Pyth x y z) : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      p ^ 2 ∣ x ^ 2 - e * y ^ 2 := by
  obtain ⟨k, hk⟩ := hd
  have hd' : p ^ 2 ∣ z ^ 2 := ⟨k ^ 2, by rw [hk, mul_pow]⟩
  rcases h with h | h | h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    convert hd' using 1
    linarith only [h]
  · refine ⟨1, Or.inl rfl, ?_⟩
    convert dvd_neg.mpr hd' using 1
    linarith only [h]
  · refine ⟨1, Or.inl rfl, ?_⟩
    convert hd' using 1
    linarith only [h]

/-- The forward phase comparison for the two possible top mixed values. -/
theorem phase_p {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) {π ρ : GaussianInt}
    (hπ : normN π = p) (hρ : normN ρ = q) (oπ : OddEven π) (oρ : OddEven ρ) :
    let d := mkData hp hq hpq hp4 hq4 hπ hρ oπ oρ
    ∀ H L : ℤ, (H = Cuboid.P2.F d ∨ H = Cuboid.P2.G d) → Cuboid.P2.lowerMixed d L →
      Cuboid.P2.Pyth (Cuboid.P2.B d) H L →
      ((d.p ^ 2 ∣ d.u) ∨ (d.p ^ 2 ∣ d.v)) := by
  intro d H L hH hL h
  have hd : d.p ∣ L := by
    rcases hL with rfl | rfl | rfl
    · refine ⟨d.p * d.v, ?_⟩
      unfold Cuboid.P2.C
      ring
    · exact ⟨d.s * d.u + d.r * d.v, rfl⟩
    · exact ⟨d.s * d.u - d.r * d.v, rfl⟩
  obtain ⟨e, he, hdiv⟩ := pyth_sq_congr hd h
  change (p : ℤ) ^ 2 ∣ Cuboid.P2.B d ^ 2 - e * H ^ 2 at hdiv
  have hB (z : GaussianInt) (hz : normN z = q) :
      (π ^ 4 * (z.norm : GaussianInt)).im = Cuboid.P2.B d := by
    change (π ^ 4 * (z.norm : GaussianInt)).im = (q : ℤ) * (π ^ 4).im
    rw [norm_eq_coe_of_normN hz]
    simp [Zsqrtd.im_mul]
    ring
  have hF : (π ^ 4 * ρ ^ 2).im = Cuboid.P2.F d := by
    change (π ^ 4 * ρ ^ 2).im = (π ^ 4).im * (ρ ^ 2).re + (π ^ 4).re * (ρ ^ 2).im
    simp [Zsqrtd.im_mul, add_comm]
  have hG : (π ^ 4 * (star ρ) ^ 2).im = Cuboid.P2.G d := by
    change (π ^ 4 * (star ρ) ^ 2).im =
      (π ^ 4).im * (ρ ^ 2).re - (π ^ 4).re * (ρ ^ 2).im
    rw [← star_pow]
    simp only [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
    ring
  change (p : ℤ) ^ 2 ∣ (ρ ^ 2).re ∨ (p : ℤ) ^ 2 ∣ (ρ ^ 2).im
  rcases hH with rfl | rfl
  · apply phase_p_comparison hp hq hpq (prime_ne_two hp4) hπ hρ he
    simpa only [hB ρ hρ, hF] using hdiv
  · have hρs : normN (star ρ) = q := by simpa using hρ
    have h := phase_p_comparison hp hq hpq (prime_ne_two hp4) hπ hρs he
      (by simpa only [hB (star ρ) hρs, hG] using hdiv)
    simpa only [← star_pow, Zsqrtd.re_star, Zsqrtd.im_star, dvd_neg] using h

end PerfectCuboid.P2Data
