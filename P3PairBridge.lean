import P2Data
import P3Data
import Mathlib.RingTheory.Int.Basic

namespace FormalCuboid.P3

/-- The arithmetic of Gaussian square coordinates needed for the two top mixed candidates. -/
structure PairFacts (d : Data) where
  p_prime : d.p.natAbs.Prime
  q_prime : d.q.natAbs.Prime
  p_not_X : ¬ d.p ∣ d.X
  p_not_Y : ¬ d.p ∣ d.Y
  q_not_U : ¬ d.q ∣ d.U
  q_not_V : ¬ d.q ∣ d.V
  gcd_XY : Int.gcd d.X d.Y = 1
  gcd_UV : Int.gcd d.U d.V = 1
  gcd_X_pm : Int.gcd (d.X - d.Y) (d.X + d.Y) = 1
  gcd_U_pm : Int.gcd (d.U - d.V) (d.U + d.V) = 1
  Y_ne : d.Y ≠ 0
  V_even : Even d.V
  top_square : ∃ m n : ℤ, d.X = m ^ 2 - n ^ 2 ∧ d.Y = 2 * m * n
  q_square : ∃ m n : ℤ, d.U = m ^ 2 - n ^ 2 ∧ d.V = 2 * m * n

theorem top_norm (d : Data) : d.X ^ 2 + d.Y ^ 2 = d.p ^ 6 := by
  have h := congrArg (fun z : ℤ => z ^ 3) d.norm_p
  unfold Data.X Data.Y reSixth imSixth
  linear_combination h

private theorem pair_difference (d : Data) :
    (d.b₃ 1) ^ 2 - (d.b₃ (-1)) ^ 2 = 4 * d.X * d.Y * d.U * d.V := by
  unfold Data.b₃
  ring

private theorem pair_sum (d : Data) :
    (d.b₃ 1) ^ 2 + (d.b₃ (-1)) ^ 2 = 2 * (d.Y ^ 2 * d.U ^ 2 + d.X ^ 2 * d.V ^ 2) := by
  unfold Data.b₃
  ring

private theorem lower_a_dvd (d : Data) (a : Leg) (ha : IsLowerA a) :
    d.p ∣ d.value a ∧ d.q ∣ d.value a := by
  rcases ha with rfl | rfl
  · constructor
    · exact ⟨d.p * d.q * d.S, by simp only [Data.value]; ring⟩
    · exact ⟨d.p ^ 2 * d.S, by simp only [Data.value]; ring⟩
  · constructor
    · exact ⟨d.q * d.W, by simp only [Data.value]; ring⟩
    · exact ⟨d.p * d.W, by simp only [Data.value]; ring⟩

private theorem prime_not_dvd_small {p b : ℤ} (hp : 5 ≤ p) (hb : 0 < b) (hbp : b < 5) :
    ¬ p ∣ b := by
  intro h
  have hd := Int.natAbs_le_of_dvd_ne_zero h (by omega : b ≠ 0)
  omega

private theorem prime_not_dvd_four_block {p x y : ℤ} (hp : Prime p) (hp5 : 5 ≤ p)
    (hx : ¬ p ∣ x) (hy : ¬ p ∣ y) : ¬ p ∣ 4 * x * y :=
  hp.not_dvd_mul (hp.not_dvd_mul (prime_not_dvd_small hp5 (by decide) (by decide)) hx) hy

private theorem prime_not_dvd_two_square {p x : ℤ} (hp : Prime p) (hp5 : 5 ≤ p)
    (hx : ¬ p ∣ x) : ¬ p ∣ 2 * x ^ 2 :=
  hp.not_dvd_mul (prime_not_dvd_small hp5 (by decide) (by decide))
    (fun h => hx (hp.dvd_of_dvd_pow h))

private theorem power_gcd_one {p x : ℤ} (hp : p.natAbs.Prime) (hx : ¬ p ∣ x) (k : ℕ) :
    Int.gcd (p ^ k) x = 1 := by
  have h := ((hp.coprime_iff_not_dvd).mpr (fun hd => hx (Int.natAbs_dvd_natAbs.mp hd))).pow_left k
  simpa only [Int.gcd_def, Int.natAbs_pow, Nat.Coprime] using h

private theorem gcd_factor_pm {a b : ℤ} (h : Int.gcd (a ^ 2 - b ^ 2) (2 * a * b) = 1) :
    Int.gcd (a - b) (a + b) = 1 := by
  let g := Int.gcd (a - b) (a + b)
  have hg₁ : (g : ℤ) ∣ a - b := Int.gcd_dvd_left _ _
  have hg₂ : (g : ℤ) ∣ a + b := Int.gcd_dvd_right _ _
  have hD : (g : ℤ) ∣ a ^ 2 - b ^ 2 := by
    convert dvd_mul_of_dvd_left hg₁ (a + b) using 1
    ring
  have hP : (g : ℤ) ∣ 2 * a * b := by
    have hs : (g : ℤ) ∣ 2 * a := by
      convert dvd_add hg₁ hg₂ using 1
      ring
    exact dvd_mul_of_dvd_left hs b
  have hg : g ∣ Int.gcd (a ^ 2 - b ^ 2) (2 * a * b) := Int.dvd_gcd hD hP
  rw [h] at hg
  exact Nat.dvd_one.mp hg

private theorem sq_le_of_dvd {m x : ℤ} (hx : x ≠ 0) (hd : m ∣ x) : m ^ 2 ≤ x ^ 2 := by
  apply sq_le_sq.mpr
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  have hh := Int.natAbs_le_of_dvd_ne_zero hd hx
  exact_mod_cast hh

private theorem odd_even_pm_ne_zero {x y : ℤ} (hx : Odd x) (hy : Even y) :
    x - y ≠ 0 ∧ x + y ≠ 0 := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  omega

private theorem Y_even (d : Data) : Even d.Y := by
  obtain ⟨s, hs⟩ := d.four_S
  refine ⟨2 * s * (3 * d.R ^ 2 - d.S ^ 2), ?_⟩
  unfold Data.Y imSixth
  linear_combination hs * (3 * d.R ^ 2 - d.S ^ 2)

private theorem odd_mod_two {z : ℤ} (h : Odd z) : z % 2 = 1 := by
  obtain ⟨a, ha⟩ := h
  omega

private theorem even_mod_two {z : ℤ} (h : Even z) : z % 2 = 0 := by
  obtain ⟨a, ha⟩ := h
  omega

private theorem square_re (a : GaussianInt) : (a ^ 2).re = a.re ^ 2 - a.im ^ 2 := by
  simp only [pow_two, Zsqrtd.re_mul]
  ring

private theorem square_im (a : GaussianInt) : (a ^ 2).im = 2 * a.re * a.im := by
  simp only [pow_two, Zsqrtd.im_mul]
  ring

open PerfectCuboid.GaussianRepr PerfectCuboid.P2Data PerfectCuboid.P3Data in
/-- The Gaussian prime data imply all hypotheses for the pair comparisons. -/
theorem mkPairFacts {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) {π ρ : GaussianInt}
    (hπ : normN π = p) (hρ : normN ρ = q) (oπ : OddEven π) (oρ : OddEven ρ) :
    PairFacts (mkData hp hq hp4 hq4 hπ hρ oπ oρ) := by
  let d := mkData hp hq hp4 hq4 hπ hρ oπ oρ
  change PairFacts d
  have hX : d.X = (π ^ 6).re := (sixth_re π).symm
  have hY : d.Y = (π ^ 6).im := (sixth_im π).symm
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hpUnit := prime_not_dvd_coords_of_power hp hp2 hπ (n := 6) (by decide)
  have hqUnit := prime_not_dvd_coords_of_power hq hq2 hρ (n := 2) (by decide)
  have hXY : Int.gcd d.X d.Y = 1 := by
    rw [hX, hY]
    exact gcd_coords_of_power hp hp2 hπ (by decide)
  have hUV : Int.gcd d.U d.V = 1 := gcd_coords_of_power hq hq2 hρ (n := 2) (by decide)
  have hV := even_im (oddEven_pow oρ 2)
  refine {
    p_prime := by change ((p : ℤ).natAbs).Prime; simpa using hp
    q_prime := by change ((q : ℤ).natAbs).Prime; simpa using hq
    p_not_X := by change ¬ (p : ℤ) ∣ d.X; rw [hX]; exact hpUnit.1
    p_not_Y := by change ¬ (p : ℤ) ∣ d.Y; rw [hY]; exact hpUnit.2
    q_not_U := hqUnit.1
    q_not_V := hqUnit.2
    gcd_XY := hXY
    gcd_UV := hUV
    gcd_X_pm := gcd_pm_of_odd_even (odd_mod_two d.odd_X) (even_mod_two (Y_even d)) hXY
    gcd_U_pm := gcd_pm_of_odd_even (odd_mod_two d.odd_U) (even_mod_two hV) hUV
    Y_ne := by rw [hY]; exact (nonzero_power_coordinates hp hp2 hπ (by decide)).2
    V_even := hV
    top_square := ?_
    q_square := ⟨ρ.re, ρ.im, square_re ρ, square_im ρ⟩ }
  refine ⟨(π ^ 3).re, (π ^ 3).im, ?_, ?_⟩
  · rw [hX, show (6 : ℕ) = 3 * 2 by decide, pow_mul]
    exact square_re _
  · rw [hY, show (6 : ℕ) = 3 * 2 by decide, pow_mul]
    exact square_im _

theorem pair_lower_a_difference (d : Data) (f : PairFacts d) (a : Leg) (ha : IsLowerA a)
    (h : (d.b₃ 1) ^ 2 - (d.b₃ (-1)) ^ 2 = (d.value a) ^ 2 ∨
      (d.b₃ (-1)) ^ 2 - (d.b₃ 1) ^ 2 = (d.value a) ^ 2) :
    d.p ^ 2 < d.q ∧ d.q ^ 2 < d.p ^ 3 := by
  have hd {m : ℤ} (hm : m ∣ d.value a) : m ^ 2 ∣ 4 * d.X * d.Y * d.U * d.V := by
    have hm' : m ^ 2 ∣ (d.value a) ^ 2 := pow_dvd_pow_of_dvd hm 2
    rcases h with h | h
    · rwa [← h, pair_difference d] at hm'
    · have he : (d.value a) ^ 2 = -(4 * d.X * d.Y * d.U * d.V) := by
        linear_combination -h - pair_difference d
      rwa [he, dvd_neg] at hm'
  have hp := Int.prime_iff_natAbs_prime.mpr f.p_prime
  have hq := Int.prime_iff_natAbs_prime.mpr f.q_prime
  obtain ⟨hpA, hqA⟩ := lower_a_dvd d a ha
  have hpUV : d.p ^ 2 ∣ d.U * d.V := by
    apply hp.pow_dvd_of_dvd_mul_left 2 (prime_not_dvd_four_block hp d.p_ge f.p_not_X f.p_not_Y)
    simpa only [mul_assoc] using hd hpA
  have hqXY : d.q ^ 2 ∣ d.X * d.Y := by
    apply hq.pow_dvd_of_dvd_mul_left 2 (prime_not_dvd_four_block hq d.q_ge f.q_not_U f.q_not_V)
    convert hd hqA using 1
    ring
  have hX : d.X ≠ 0 := fun hx => f.p_not_X (hx ▸ dvd_zero d.p)
  have hpPos : 0 < d.p := by linarith only [d.p_ge]
  have hqPos : 0 < d.q := by linarith only [d.q_ge]
  constructor
  · rcases Cuboid.P2.pow_dvd_one_factor f.p_prime f.gcd_UV hpUV with hU | hV
    · exact Cuboid.P2.divisor_lt_hypotenuse (pow_pos hpPos _) d.U_zero d.V_zero hqPos d.norm_q hU
    · exact Cuboid.P2.divisor_lt_hypotenuse (pow_pos hpPos _) d.V_zero d.U_zero hqPos
        (by linarith only [d.norm_q]) hV
  · have hnorm : d.X ^ 2 + d.Y ^ 2 = (d.p ^ 3) ^ 2 := by
      linear_combination top_norm d
    rcases Cuboid.P2.pow_dvd_one_factor f.q_prime f.gcd_XY hqXY with hX' | hY'
    · exact Cuboid.P2.divisor_lt_hypotenuse (pow_pos hqPos _) hX f.Y_ne (pow_pos hpPos _) hnorm hX'
    · exact Cuboid.P2.divisor_lt_hypotenuse (pow_pos hqPos _) f.Y_ne hX (pow_pos hpPos _)
        (by linarith only [hnorm]) hY'

theorem pair_lower_a_sum (d : Data) (f : PairFacts d) (a : Leg) (ha : IsLowerA a)
    (h : (d.b₃ 1) ^ 2 + (d.b₃ (-1)) ^ 2 = (d.value a) ^ 2) :
    d.p ^ 4 ≤ 2 * d.q ^ 2 ∧ d.q ^ 4 ≤ 2 * d.p ^ 6 := by
  obtain ⟨hpA, hqA⟩ := lower_a_dvd d a ha
  have hd {m : ℤ} (hm : m ∣ d.value a) :
      m ^ 2 ∣ 2 * (d.Y ^ 2 * d.U ^ 2 + d.X ^ 2 * d.V ^ 2) := by
    rw [← pair_sum, h]
    exact pow_dvd_pow_of_dvd hm 2
  have hp := Int.prime_iff_natAbs_prime.mpr f.p_prime
  have hq := Int.prime_iff_natAbs_prime.mpr f.q_prime
  have hpUV : d.p ^ 2 ∣ (d.U - d.V) * (d.U + d.V) := by
    apply hp.pow_dvd_of_dvd_mul_left 2 (prime_not_dvd_two_square hp d.p_ge f.p_not_Y)
    have h2 : d.p ^ 2 ∣ d.p ^ 6 * (2 * d.V ^ 2) :=
      dvd_mul_of_dvd_left (pow_dvd_pow _ (by decide)) _
    convert dvd_sub (hd hpA) h2 using 1
    rw [← top_norm d]
    ring
  have hqXY : d.q ^ 2 ∣ (d.X - d.Y) * (d.X + d.Y) := by
    apply hq.pow_dvd_of_dvd_mul_left 2 (prime_not_dvd_two_square hq d.q_ge f.q_not_V)
    have h2 : d.q ^ 2 ∣ d.q ^ 2 * (2 * d.Y ^ 2) := dvd_mul_right _ _
    convert dvd_sub (hd hqA) h2 using 1
    rw [← d.norm_q]
    ring
  obtain ⟨hUV₁,hUV₂⟩ := odd_even_pm_ne_zero d.odd_U f.V_even
  obtain ⟨hXY₁,hXY₂⟩ := odd_even_pm_ne_zero d.odd_X (Y_even d)
  constructor
  · rcases Cuboid.P2.pow_dvd_one_factor f.p_prime f.gcd_U_pm hpUV with h₁ | h₂
    · nlinarith only [sq_le_of_dvd hUV₁ h₁, sq_nonneg (d.U + d.V), d.norm_q]
    · nlinarith only [sq_le_of_dvd hUV₂ h₂, sq_nonneg (d.U - d.V), d.norm_q]
  · rcases Cuboid.P2.pow_dvd_one_factor f.q_prime f.gcd_X_pm hqXY with h₁ | h₂
    · nlinarith only [sq_le_of_dvd hXY₁ h₁, sq_nonneg (d.X + d.Y), top_norm d]
    · nlinarith only [sq_le_of_dvd hXY₂ h₂, sq_nonneg (d.X - d.Y), top_norm d]

private theorem difference_small_bounds {a b t w h : ℤ} (hn : a ^ 2 + b ^ 2 = t)
    (hu : h.natAbs = 1) (hw : w = 4 * a * b * h ∨ w = -(4 * a * b * h)) :
    -(2 * t) ≤ w ∧ w ≤ 2 * t := by
  have hAbs : |h| = 1 := by rw [Int.abs_eq_natAbs, hu]; norm_num
  have hW : |w| = 4 * |a| * |b| := by
    rcases hw with hw | hw <;> simp [hw, abs_mul, hAbs]
  have hW' : |w| ≤ 2 * t := by
    have hn' : |a| ^ 2 + |b| ^ 2 = t := by simpa only [sq_abs] using hn
    nlinarith only [hW, hn', sq_nonneg (|a| - |b|)]
  exact abs_le.mp hW'

theorem pair_top_a_difference (d : Data) (f : PairFacts d)
    (h : (d.b₃ 1) ^ 2 - (d.b₃ (-1)) ^ 2 = d.a₃ ^ 2 ∨
      (d.b₃ (-1)) ^ 2 - (d.b₃ 1) ^ 2 = d.a₃ ^ 2) :
    d.q ^ 4 - 1 = 2 * |d.Y| ∧ |d.Y| ≤ 2 * d.q ^ 2 := by
  have hzero : d.q ^ 2 ≠ 0 := by have := d.q_ge; positivity
  have hq := Int.prime_iff_natAbs_prime.mpr f.q_prime
  have hc : d.q ^ 2 * d.Y = 4 * d.X * d.U * d.V ∨
      d.q ^ 2 * d.Y = -(4 * d.X * d.U * d.V) := by
    rcases h with h | h
    · left
      apply mul_right_cancel₀ f.Y_ne
      unfold Data.a₃ at h
      linear_combination -h + pair_difference d
    · right
      apply mul_right_cancel₀ f.Y_ne
      unfold Data.a₃ at h
      linear_combination -h - pair_difference d
  obtain ⟨k, hk, hk1, hY⟩ := Cuboid.P2.difference_factor hzero
    (power_gcd_one f.q_prime (prime_not_dvd_four_block hq d.q_ge f.q_not_U f.q_not_V) 2) f.gcd_XY hc
  obtain ⟨m, n, hX, hy⟩ := f.top_square
  have hcop : Int.gcd (m - n) (m + n) = 1 :=
    gcd_factor_pm (by rw [← hX, ← hy]; exact f.gcd_XY)
  have hproduct : (m - n) * (m + n) = d.q ^ 2 * k := by
    linear_combination hX.symm + hk
  obtain ⟨hlo, hhi⟩ := difference_small_bounds d.norm_q hk1 hY
  have hq2 : 5 ≤ d.q ^ 2 := by nlinarith only [d.q_ge, sq_nonneg (d.q - 3)]
  exact (Cuboid.P2.impossible_unbalanced f.q_prime hq2 hcop hk1 hproduct hy hlo hhi).elim

theorem pair_c_difference (d : Data) (f : PairFacts d)
    (h : (d.b₃ 1) ^ 2 - (d.b₃ (-1)) ^ 2 = (d.value .c) ^ 2 ∨
      (d.b₃ (-1)) ^ 2 - (d.b₃ 1) ^ 2 = (d.value .c) ^ 2) :
    d.p ^ 12 - 1 = 2 * |d.V| ∧ |d.V| ≤ 2 * d.p ^ 6 := by
  have hpPos : 0 < d.p := by linarith only [d.p_ge]
  have hzero : d.p ^ 6 ≠ 0 := pow_ne_zero _ hpPos.ne'
  have hp := Int.prime_iff_natAbs_prime.mpr f.p_prime
  have hc : d.p ^ 6 * d.V = 4 * d.U * d.X * d.Y ∨
      d.p ^ 6 * d.V = -(4 * d.U * d.X * d.Y) := by
    rcases h with h | h
    · left
      apply mul_right_cancel₀ d.V_zero
      unfold Data.value at h
      linear_combination -h + pair_difference d
    · right
      apply mul_right_cancel₀ d.V_zero
      unfold Data.value at h
      linear_combination -h - pair_difference d
  obtain ⟨k, hk, hk1, hV⟩ := Cuboid.P2.difference_factor hzero
    (power_gcd_one f.p_prime (prime_not_dvd_four_block hp d.p_ge f.p_not_X f.p_not_Y) 6) f.gcd_UV hc
  obtain ⟨m, n, hU, hv⟩ := f.q_square
  have hcop : Int.gcd (m - n) (m + n) = 1 :=
    gcd_factor_pm (by rw [← hU, ← hv]; exact f.gcd_UV)
  have hproduct : (m - n) * (m + n) = d.p ^ 6 * k := by
    linear_combination hU.symm + hk
  obtain ⟨hlo, hhi⟩ := difference_small_bounds (top_norm d) hk1 hV
  have hp6 : 5 ≤ d.p ^ 6 := by
    have hh : (5 : ℤ) ^ 6 ≤ d.p ^ 6 := pow_le_pow_left₀ (by decide) d.p_ge 6
    norm_num at hh
    omega
  exact (Cuboid.P2.impossible_unbalanced f.p_prime hp6 hcop hk1 hproduct hv hlo hhi).elim

end FormalCuboid.P3
