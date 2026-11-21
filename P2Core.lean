import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
Arithmetic elimination for the seven Gaussian values arising at body
diagonal p²q. The interface isolates the needed Gaussian factorization
and congruence facts.
-/

namespace Cuboid.P2

private abbrev OddI (a : ℤ) : Prop := a % 2 = 1
private abbrev EvenI (a : ℤ) : Prop := a % 2 = 0

private theorem odd_mul {a b : ℤ} (ha : OddI a) (hb : OddI b) :
    OddI (a * b) := by
  change a % 2 = 1 at ha
  change b % 2 = 1 at hb
  change (a * b) % 2 = 1
  rw [Int.mul_emod, ha, hb]; decide

private theorem even_mul {a b : ℤ} (ha : EvenI a) :
    EvenI (a * b) := by
  change a % 2 = 0 at ha
  change (a * b) % 2 = 0
  rw [Int.mul_emod, ha]; simp

private theorem even_mul_right {a b : ℤ} (hb : EvenI b) :
    EvenI (a * b) := by
  rw [mul_comm]
  exact even_mul hb

private theorem odd_sq {a : ℤ} (ha : OddI a) : OddI (a ^ 2) := by
  rw [pow_two]
  exact odd_mul ha ha

private theorem residue_two_mul_odd {a : ℤ} (ha : OddI a) :
    (2 * a) % 4 = 2 := by
  unfold OddI at ha
  omega

private theorem residue_eight_mul_odd {a : ℤ} (ha : OddI a) :
    (8 * a) % 16 = 8 := by
  unfold OddI at ha
  omega

private theorem square_mod_four_of_even {a : ℤ} (ha : EvenI a) :
    a ^ 2 % 4 = 0 := by
  unfold EvenI at ha
  have hm : a % 4 = 0 ∨ a % 4 = 2 := by omega
  rw [pow_two, Int.mul_emod]
  rcases hm with h | h <;> norm_num [h]

private theorem square_mod_sixteen_ne_eight (a : ℤ) :
    a ^ 2 % 16 ≠ 8 := by
  have h0 : 0 ≤ a % 16 := by omega
  have h1 : a % 16 < 16 := by omega
  rw [pow_two, Int.mul_emod]
  interval_cases h : a % 16 <;> norm_num

/-- Remove the common dyadic factor of two integers. A bounded induction
provides a proof without a valuation library or any primality assumption. -/
private theorem dyadic_pair_aux (n : ℕ) (x y : ℤ) (hx : x ≠ 0)
    (hl : -(n : ℤ) < x) (hr : x < n) :
    ∃ d a b : ℤ, d ≠ 0 ∧ x = d * a ∧ y = d * b ∧ (OddI a ∨ OddI b) := by
  induction n generalizing x y with
  | zero => omega
  | succ n ih =>
    by_cases ho : OddI x ∨ OddI y
    · exact ⟨1, x, y, one_ne_zero, by simp, by simp, ho⟩
    · have hx0 : x % 2 = 0 := by
        have hno : ¬OddI x := fun h => ho (Or.inl h)
        unfold OddI at hno
        omega
      have hy0 : y % 2 = 0 := by
        have hno : ¬OddI y := fun h => ho (Or.inr h)
        unfold OddI at hno
        omega
      have hn : 0 < n := by omega
      have hxn : x / 2 ≠ 0 := by omega
      have hxl : -(n : ℤ) < x / 2 := by omega
      have hxr : x / 2 < n := by omega
      obtain ⟨d, a, b, hd, ha, hb, hab⟩ := ih (x / 2) (y / 2) hxn hxl hxr
      refine ⟨2 * d, a, b, mul_ne_zero (by norm_num) hd, ?_, ?_, hab⟩
      · calc
          x = 2 * (x / 2) := by omega
          _ = (2 * d) * a := by rw [ha]; ring
      · calc
          y = 2 * (y / 2) := by omega
          _ = (2 * d) * b := by rw [hb]; ring

private theorem dyadic_pair (x y : ℤ) (hx : x ≠ 0) :
    ∃ d a b : ℤ, d ≠ 0 ∧ x = d * a ∧ y = d * b ∧ (OddI a ∨ OddI b) := by
  let n := (x + 1).toNat + (-x + 1).toNat
  apply dyadic_pair_aux n x y hx <;> dsimp [n] <;> omega

private theorem mul_cancel_int {d a b : ℤ} (hd : d ≠ 0) (h : d * a = d * b) : a = b := by
  exact mul_left_cancel₀ hd h

/-- If u and v are odd, 2u x² = v y² with x nonzero is impossible. -/
theorem no_twice_square {u v x y : ℤ}
    (hu : OddI u) (hv : OddI v) (hx : x ≠ 0)
    (h : 2 * u * x ^ 2 = v * y ^ 2) : False := by
  obtain ⟨d, a, b, hd, hx', hy', hab⟩ := dyadic_pair x y hx
  have hh : 2 * u * a ^ 2 = v * b ^ 2 := by
    apply mul_cancel_int (d := d ^ 2) (pow_ne_zero _ hd)
    rw [hx', hy'] at h
    linear_combination h
  by_cases hb : OddI b
  · have hodd := odd_mul hv (odd_sq hb)
    have heven : EvenI (2 * u * a ^ 2) := even_mul (even_mul (by decide : EvenI 2))
    rw [hh] at heven
    unfold OddI at hodd
    unfold EvenI at heven
    omega
  · have ha : OddI a := hab.resolve_right hb
    have hb' : EvenI b := by
      unfold OddI at hb
      unfold EvenI
      omega
    have hleft : (2 * u * a ^ 2) % 4 = 2 := by
      rw [mul_assoc]
      exact residue_two_mul_odd (odd_mul hu (odd_sq ha))
    have hright : (v * b ^ 2) % 4 = 0 := by
      rw [Int.mul_emod, square_mod_four_of_even hb']; simp
    rw [hh] at hleft
    omega

/-- Dyadic obstruction for the signed difference of the two top Gaussian
values when the third value is a partially p-divisible mixed value. -/
theorem no_mixed_difference {p r s t u v e f : ℤ}
    (hp : OddI p) (hr : OddI r) (ht : OddI t) (hu : OddI u)
    (he : OddI e) (hf : OddI f) (hs : s ≠ 0)
    (h : p ^ 2 * (s * u + e * (r * v)) ^ 2 = 8 * (f * r * s * t * u * v)) :
    False := by
  obtain ⟨d, a, b, hd, hs', hv', hab⟩ := dyadic_pair s v hs
  have hh : (p * (a * u + e * (r * b))) ^ 2 = 8 * (f * r * a * t * u * b) := by
    apply mul_cancel_int (d := d ^ 2) (pow_ne_zero _ hd)
    rw [hs', hv'] at h
    linear_combination h
  by_cases ha : OddI a <;> by_cases hb : OddI b
  · have ho : OddI (f * r * a * t * u * b) :=
      odd_mul (odd_mul (odd_mul (odd_mul (odd_mul hf hr) ha) ht) hu) hb
    have hres := residue_eight_mul_odd ho
    rw [← hh] at hres
    exact square_mod_sixteen_ne_eight _ hres
  · have hbe : EvenI b := by unfold OddI at hb; unfold EvenI; omega
    have hx := odd_mul ha hu
    have hy := even_mul_right (a := e) (even_mul_right (a := r) hbe)
    have hz : OddI (a * u + e * (r * b)) := by unfold OddI at hx ⊢; unfold EvenI at hy; omega
    have hodd := odd_sq (odd_mul hp hz)
    have hEven := even_mul (b := f * r * a * t * u * b) (by decide : EvenI 8)
    rw [← hh] at hEven
    unfold OddI at hodd
    unfold EvenI at hEven
    omega
  · have hae : EvenI a := by unfold OddI at ha; unfold EvenI; omega
    have hx := even_mul (b := u) hae
    have hy := odd_mul he (odd_mul hr hb)
    have hz : OddI (a * u + e * (r * b)) := by unfold OddI at hy ⊢; unfold EvenI at hx; omega
    have hodd := odd_sq (odd_mul hp hz)
    have hEven := even_mul (b := f * r * a * t * u * b) (by decide : EvenI 8)
    rw [← hh] at hEven
    unfold OddI at hodd
    unfold EvenI at hEven
    omega
  · exact hab.elim ha hb

/-- The analogous sum is impossible for either sign of the lower mixed value. -/
theorem no_mixed_sum {p r s t u v e : ℤ}
    (hp : OddI p) (hr : OddI r) (ht : OddI t) (hu : OddI u)
    (he : OddI e) (hs : s ≠ 0)
    (h : p ^ 2 * (s * u + e * (r * v)) ^ 2 =
      2 * ((2 * r * s * u) ^ 2 + (t * v) ^ 2)) : False := by
  obtain ⟨d, a, b, hd, hs', hv', hab⟩ := dyadic_pair s v hs
  have hh : (p * (a * u + e * (r * b))) ^ 2 =
      2 * ((2 * r * a * u) ^ 2 + (t * b) ^ 2) := by
    apply mul_cancel_int (d := d ^ 2) (pow_ne_zero _ hd)
    rw [hs', hv'] at h
    linear_combination h
  by_cases ha : OddI a <;> by_cases hb : OddI b
  · have hx := odd_mul ha hu
    have hy := odd_mul he (odd_mul hr hb)
    have hz : EvenI (a * u + e * (r * b)) := by unfold OddI at hx hy; unfold EvenI; omega
    have hl := square_mod_four_of_even (even_mul_right (a := p) hz)
    have hterm1 : EvenI ((2 * r * a * u) ^ 2) := by
      rw [pow_two]
      exact even_mul (even_mul (even_mul (even_mul (by decide : EvenI 2))))
    have hterm2 := odd_sq (odd_mul ht hb)
    have ho : OddI ((2 * r * a * u) ^ 2 + (t * b) ^ 2) := by
      unfold EvenI at hterm1
      unfold OddI at hterm2 ⊢
      omega
    have hr' := residue_two_mul_odd ho
    rw [hh] at hl
    omega
  · have hbe : EvenI b := by unfold OddI at hb; unfold EvenI; omega
    have hx := odd_mul ha hu
    have hy := even_mul_right (a := e) (even_mul_right (a := r) hbe)
    have hz : OddI (a * u + e * (r * b)) := by unfold OddI at hx ⊢; unfold EvenI at hy; omega
    have hl := odd_sq (odd_mul hp hz)
    have hr' := even_mul (b := (2 * r * a * u) ^ 2 + (t * b) ^ 2) (by decide : EvenI 2)
    rw [hh] at hl
    unfold OddI at hl
    unfold EvenI at hr'
    omega
  · have hae : EvenI a := by unfold OddI at ha; unfold EvenI; omega
    have hx := even_mul (b := u) hae
    have hy := odd_mul he (odd_mul hr hb)
    have hz : OddI (a * u + e * (r * b)) := by unfold OddI at hy ⊢; unfold EvenI at hx; omega
    have hl := odd_sq (odd_mul hp hz)
    have hr' := even_mul (b := (2 * r * a * u) ^ 2 + (t * b) ^ 2) (by decide : EvenI 2)
    rw [hh] at hl
    unfold OddI at hl
    unfold EvenI at hr'
    omega
  · exact hab.elim ha hb

/-- Any nonzero multiple of k on a nondegenerate integral circle has k < z. -/
theorem divisor_lt_hypotenuse {k x y z : ℤ}
    (hk : 0 < k) (hx : x ≠ 0) (hy : y ≠ 0) (hz : 0 < z)
    (hh : x ^ 2 + y ^ 2 = z ^ 2) (hd : k ∣ x) : k < z := by
  obtain ⟨c, hc⟩ := hd
  have hc0 : c ≠ 0 := by
    intro h
    apply hx
    simp [hc, h]
  have hc1 : 1 ≤ c ^ 2 := by
    rcases lt_or_gt_of_ne hc0 with h | h
    · have h' : c ≤ -1 := by omega
      nlinarith [mul_nonneg (show 0 ≤ -1 - c by omega) (show 0 ≤ 1 - c by omega)]
    · have h' : 1 ≤ c := by omega
      nlinarith [mul_nonneg (show 0 ≤ c - 1 by omega) (show 0 ≤ c + 1 by omega)]
  have hc2 : 0 ≤ c ^ 2 - 1 := by linarith
  have hx2 : k ^ 2 ≤ x ^ 2 := by
    rw [hc]
    nlinarith only [mul_nonneg (sq_nonneg k) hc2]
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  by_contra hn
  have h' : z ≤ k := by omega
  have hf : 0 ≤ (k-z)*(k+z) := mul_nonneg (by omega) (by omega)
  nlinarith only [hh, hx2, hy2, hf]

private theorem incompatible_bounds {p q : ℤ}
    (hp : 2 ≤ p) (h₁ : p ^ 2 < q) (h₂ : q ^ 2 < p ^ 3) : False := by
  have hp0 : 0 ≤ p := by omega
  have hq0 : 0 < q := lt_of_le_of_lt (sq_nonneg p) h₁
  have hh : 0 < (q-p^2)*(q+p^2) :=
    mul_pos (sub_pos.mpr h₁) (add_pos_of_pos_of_nonneg hq0 (sq_nonneg p))
  have hpp : 0 ≤ p ^ 3 * (p-1) := mul_nonneg (pow_nonneg hp0 _) (by omega)
  nlinarith only [hh, hpp, h₂]

/-- Divisibility does not split a prime power over relatively prime factors. -/
theorem pow_dvd_one_factor {l x y : ℤ} {n : ℕ}
    (hl : l.natAbs.Prime) (hxy : Int.gcd x y = 1)
    (h : l ^ n ∣ x * y) : l ^ n ∣ x ∨ l ^ n ∣ y := by
  by_cases hx : l.natAbs ∣ x.natAbs
  · have hy : ¬l.natAbs ∣ y.natAbs := by
      intro hy
      have h1 : l.natAbs ∣ Int.gcd x y := by
        rw [Int.gcd_def]
        exact Nat.dvd_gcd hx hy
      rw [hxy] at h1
      have he := Nat.dvd_one.mp h1
      have := hl.two_le
      omega
    have hc := (hl.coprime_iff_not_dvd.mpr hy).pow_left n
    have hyc : Int.gcd (l ^ n) y = 1 := by
      simpa only [Int.gcd_def, Int.natAbs_pow, Nat.Coprime] using hc
    exact Or.inl (Int.dvd_of_dvd_mul_left_of_gcd_one h hyc)
  · have hc := (hl.coprime_iff_not_dvd.mpr hx).pow_left n
    have hxc : Int.gcd (l ^ n) x = 1 := by
      simpa only [Int.gcd_def, Int.natAbs_pow, Nat.Coprime] using hc
    exact Or.inr (Int.dvd_of_dvd_mul_right_of_gcd_one h hxc)

private theorem gcd_one_of_common_factor {x y k : ℤ}
    (h : Int.gcd x y = 1) (hx : k ∣ x) (hy : k ∣ y) : k.natAbs = 1 := by
  have hh : k.natAbs ∣ Int.gcd x y := by
    rw [Int.gcd_def]
    exact Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr hx) (Int.natAbs_dvd_natAbs.mpr hy)
  rw [h] at hh
  exact Nat.dvd_one.mp hh

private theorem eq_or_neg {x : ℤ} (h : x.natAbs = 1) : x = 1 ∨ x = -1 :=
  Int.natAbs_eq_natAbs_iff.mp (show x.natAbs = (1 : ℤ).natAbs by simpa using h)

private theorem one_unit_of_prime_power_of_coprime_squares
    {l x y h : ℤ} {n : ℕ} (hl : l.natAbs.Prime) (hxy : Int.gcd x y = 1)
    (hh : h.natAbs = 1) (he : x * y = l ^ n * h) :
    x ^ 2 = 1 ∨ y ^ 2 = 1 := by
  have a := congrArg Int.natAbs he
  simp only [Int.natAbs_mul, Int.natAbs_pow, hh, mul_one] at a
  have hd : l.natAbs ^ n ∣ x.natAbs * y.natAbs := ⟨1, by simp [a]⟩
  have hd' : l ^ n ∣ x * y := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa only [Int.natAbs_mul, Int.natAbs_pow] using hd
  rcases pow_dvd_one_factor hl hxy hd' with hx | hy
  · have hx' : l.natAbs ^ n ∣ x.natAbs := by simpa only [Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr hx
    obtain ⟨v, hv⟩ := hx'
    rw [hv] at a
    have ht : 0 < l.natAbs ^ n := pow_pos (Nat.zero_lt_of_lt hl.one_lt) _
    have he' : v * y.natAbs = 1 := by
      apply Nat.eq_of_mul_eq_mul_left ht
      simpa only [mul_assoc, mul_one] using a
    have hd1 : y.natAbs ∣ 1 := ⟨v, by simpa [mul_comm] using he'.symm⟩
    right
    rcases eq_or_neg (Nat.dvd_one.mp hd1) with hz | hz <;> norm_num [hz]
  · have hy' : l.natAbs ^ n ∣ y.natAbs := by simpa only [Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr hy
    obtain ⟨v, hv⟩ := hy'
    have a' : y.natAbs * x.natAbs = l.natAbs ^ n := by simpa [mul_comm] using a
    rw [hv] at a'
    have ht : 0 < l.natAbs ^ n := pow_pos (Nat.zero_lt_of_lt hl.one_lt) _
    have he' : v * x.natAbs = 1 := by
      apply Nat.eq_of_mul_eq_mul_left ht
      simpa only [mul_assoc, mul_one] using a'
    have hd1 : x.natAbs ∣ 1 := ⟨v, by simpa [mul_comm] using he'.symm⟩
    left
    rcases eq_or_neg (Nat.dvd_one.mp hd1) with hz | hz <;> norm_num [hz]

theorem impossible_unbalanced
    {l x y w h : ℤ} {n : ℕ} (hl : l.natAbs.Prime) (hl5 : 5 ≤ l ^ n)
    (hxy : Int.gcd (x - y) (x + y) = 1) (hh : h.natAbs = 1)
    (hf : (x - y) * (x + y) = l ^ n * h)
    (hw : w = 2 * x * y) (hlo : -(2 * l ^ n) ≤ w)
    (hhi : w ≤ 2 * l ^ n) : False := by
  have hpow : (x-y)^2 * (x+y)^2 = (l^n)^2 := by
    rcases eq_or_neg hh with hz | hz
    · have hhf := congrArg (fun k : ℤ => k ^ 2) hf
      rw [hz, mul_one, mul_pow] at hhf
      exact hhf
    · have hhf := congrArg (fun k : ℤ => k ^ 2) hf
      rw [hz] at hhf
      rw [mul_pow, mul_pow] at hhf
      norm_num at hhf
      exact hhf
  have hb : (l ^ n) ^ 2 - 1 > 4 * l ^ n := by
    have h0 : 0 ≤ l ^ n - 5 := by omega
    have h1 : 0 ≤ l ^ n + 1 := by omega
    nlinarith only [mul_nonneg h0 h1]
  rcases one_unit_of_prime_power_of_coprime_squares hl hxy hh hf with ha | ha
  · rw [ha, one_mul] at hpow
    nlinarith only [ha, hpow, hw, hhi, hb]
  · rw [ha, mul_one] at hpow
    nlinarith only [ha, hpow, hw, hlo, hb]

theorem difference_factor
    {l A B X Y : ℤ}
    (hl : l ≠ 0) (hg : Int.gcd l (4 * X * Y) = 1)
    (hab : Int.gcd A B = 1)
    (h : l * B = 4 * A * X * Y ∨ l * B = -(4 * A * X * Y)) :
    ∃ k : ℤ, A = l * k ∧ k.natAbs = 1 ∧
      (B = 4 * X * Y * k ∨ B = -(4 * X * Y * k)) := by
  have hdprod : l ∣ (4 * X * Y) * A := by
    rcases h with he | he
    · exact ⟨B, by linear_combination -he⟩
    · exact ⟨-B, by linear_combination he⟩
  obtain ⟨k, hk⟩ := Int.dvd_of_dvd_mul_right_of_gcd_one hdprod hg
  have hb : B = 4 * X * Y * k ∨ B = -(4 * X * Y * k) := by
    rcases h with he | he
    · left
      apply mul_cancel_int hl
      rw [hk] at he
      linear_combination he
    · right
      apply mul_cancel_int hl
      rw [hk] at he
      linear_combination he
  have hkA : k ∣ A := ⟨l, by rw [hk, mul_comm]⟩
  have hkB : k ∣ B := by
    rcases hb with hb | hb
    · exact ⟨4 * X * Y, by rw [hb, mul_comm]⟩
    · exact ⟨-(4 * X * Y), by rw [hb]; ring⟩
  exact ⟨k, hk, gcd_one_of_common_factor hab hkA hkB, hb⟩

def Pyth (a b c : ℤ) : Prop :=
  a ^ 2 + b ^ 2 = c ^ 2 ∨ a ^ 2 + c ^ 2 = b ^ 2 ∨ b ^ 2 + c ^ 2 = a ^ 2

private theorem pyth_rotate {a b c : ℤ} (h : Pyth a b c) : Pyth b c a := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl (by simpa [add_comm] using h))
  · exact Or.inr (Or.inr (by simpa [add_comm] using h))
  · exact Or.inl h

private theorem pyth_swap {a b c : ℤ} (h : Pyth a b c) : Pyth b a c := by
  rcases h with h | h | h
  · exact Or.inl (by simpa [add_comm] using h)
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

private theorem pyth_cases {a b c : ℤ} (h : Pyth a b c) :
    a ^ 2 + b ^ 2 = c ^ 2 ∨ a ^ 2 - b ^ 2 = c ^ 2 ∨ a ^ 2 - b ^ 2 = -(c ^ 2) := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (by linear_combination h))
  · exact Or.inr (Or.inl (by linear_combination -h))

private theorem pyth_dvd_of_dvd_right_two {l a b c : ℤ}
    (hb : l ∣ b) (hc : l ∣ c) (h : Pyth a b c) : l ∣ a := by
  obtain ⟨x, hx⟩ := hb
  obtain ⟨y, hy⟩ := hc
  apply (Int.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
  rcases h with h | h | h
  · refine ⟨y ^ 2 - x ^ 2, ?_⟩
    rw [hx, hy] at h
    linear_combination h
  · refine ⟨x ^ 2 - y ^ 2, ?_⟩
    rw [hx, hy] at h
    linear_combination h
  · refine ⟨x ^ 2 + y ^ 2, ?_⟩
    rw [hx, hy] at h
    linear_combination -h

/-- Integer coordinates and precise norm/coprimality properties of the
Gaussian powers used in the seven-state table. -/
structure Data where
  p : ℤ
  q : ℤ
  r : ℤ
  s : ℤ
  t : ℤ
  w : ℤ
  u : ℤ
  v : ℤ
  m : ℤ
  n : ℤ
  hp : 5 ≤ p
  hq : 5 ≤ q
  pp : p.natAbs.Prime
  qp : q.natAbs.Prime
  hp_odd : p % 2 = 1
  hq_odd : q % 2 = 1
  hr_odd : r % 2 = 1
  ht_odd : t % 2 = 1
  hu_odd : u % 2 = 1
  hs_even : s % 2 = 0
  hw_even : w % 2 = 0
  hr_nz : r ≠ 0
  hs_nz : s ≠ 0
  ht_nz : t ≠ 0
  hw_nz : w ≠ 0
  hu_nz : u ≠ 0
  hv_nz : v ≠ 0
  rs : r ^ 2 + s ^ 2 = p ^ 2
  tw : t ^ 2 + w ^ 2 = p ^ 4
  uv : u ^ 2 + v ^ 2 = q ^ 2
  t_eq : t = r ^ 2 - s ^ 2
  w_eq : w = 2 * r * s
  u_eq : u = m ^ 2 - n ^ 2
  v_eq : v = 2 * m * n
  gcd_tw : Int.gcd t w = 1
  gcd_uv : Int.gcd u v = 1
  gcd_rt : Int.gcd r t = 1
  gcd_rs_pm : Int.gcd (r-s) (r+s) = 1
  gcd_mn_pm : Int.gcd (m-n) (m+n) = 1
  gcd_q2_4uv : Int.gcd (q ^ 2) (4 * u * v) = 1
  gcd_p4_4wt : Int.gcd (p ^ 4) (4 * w * t) = 1
  gcd_p2_8rt : Int.gcd (p ^ 2) (8 * r * t) = 1
  gcd_q2_8uv : Int.gcd (q ^ 2) (8 * u * v) = 1

private theorem Data.p_pos (d : Data) : 0 < d.p := by
  have hp := d.hp
  omega

private theorem Data.q_pos (d : Data) : 0 < d.q := by
  have hq := d.hq
  omega

def A (d : Data) : ℤ := d.p * d.q * d.s
def B (d : Data) : ℤ := d.q * d.w
def C (d : Data) : ℤ := d.p ^ 2 * d.v
def D (d : Data) : ℤ := d.p * (d.s * d.u + d.r * d.v)
def E (d : Data) : ℤ := d.p * (d.s * d.u - d.r * d.v)
def F (d : Data) : ℤ := d.w * d.u + d.t * d.v
def G (d : Data) : ℤ := d.w * d.u - d.t * d.v

def leg (d : Data) (i : Fin 7) : ℤ :=
  match i.val with
  | 0 => A d
  | 1 => B d
  | 2 => C d
  | 3 => D d
  | 4 => E d
  | 5 => F d
  | _ => G d

abbrev top (i : Fin 7) : Prop := i = 1 ∨ i = 5 ∨ i = 6

abbrev twoTop (i j k : Fin 7) : Prop :=
  (top i ∧ top j) ∨ (top i ∧ top k) ∨ (top j ∧ top k)

private theorem twoTop_rotate {i j k : Fin 7} (h : twoTop i j k) : twoTop j k i := by
  rcases h with ⟨hi, hj⟩ | ⟨hi, hk⟩ | ⟨hj, hk⟩
  · exact Or.inr (Or.inl ⟨hj, hi⟩)
  · exact Or.inr (Or.inr ⟨hk, hi⟩)
  · exact Or.inl ⟨hj, hk⟩

private theorem twoTop_swap {i j k : Fin 7} (h : twoTop i j k) : twoTop j i k := by
  rcases h with ⟨hi, hj⟩ | ⟨hi, hk⟩ | ⟨hj, hk⟩
  · exact Or.inl ⟨hj, hi⟩
  · exact Or.inr (Or.inr ⟨hi, hk⟩)
  · exact Or.inr (Or.inl ⟨hj, hk⟩)

def lowerMixed (d : Data) (L : ℤ) : Prop :=
  L = C d ∨ L = D d ∨ L = E d

/-- Interface for the unconditional Gaussian phase facts not proved in
this file. The high-state branch uses two separate phase tests: one
provides the divisibility of U or V, the other a bounded nonzero
multiple of q² coming from a component of a Gaussian power. -/
structure PhaseFacts (d : Data) where
  unit_p : ∀ i : Fin 7, top i → ¬ d.p ∣ leg d i
  divisible_p : ∀ i : Fin 7, ¬top i → d.p ∣ leg d i
  unit_q_F : ¬ d.q ∣ F d
  unit_q_G : ¬ d.q ∣ G d
  phase_p : ∀ H L : ℤ, (H = F d ∨ H = G d) → lowerMixed d L →
    Pyth (B d) H L → (d.p ^ 2 ∣ d.u ∨ d.p ^ 2 ∣ d.v)
  phase_q : ∀ H L : ℤ, (H = F d ∨ H = G d) → lowerMixed d L →
    Pyth (B d) H L →
      ∃ k x : ℤ, x ≠ 0 ∧ x = d.q ^ 2 * k ∧ x < d.p ^ 3 ∧ -x < d.p ^ 3

private theorem phase_q_bound (d : Data) {k x : ℤ} (hn : x ≠ 0)
    (hx : x = d.q ^ 2 * k) (hu : x < d.p ^ 3) (hl : -x < d.p ^ 3) :
    d.q ^ 2 < d.p ^ 3 := by
  have hk : k ≠ 0 := by
    intro h
    exact hn (by simp [hx, h])
  rcases lt_or_gt_of_ne hk with h | h
  · have hz : 0 ≤ -k-1 := by omega
    nlinarith only [hl, hx, mul_nonneg (sq_nonneg d.q) hz]
  · have hz : 0 ≤ k-1 := by omega
    nlinarith only [hu, hx, mul_nonneg (sq_nonneg d.q) hz]

private theorem no_B_H_L (d : Data) (facts : PhaseFacts d) {H L : ℤ}
    (hH : H = F d ∨ H = G d) (hL : L = A d ∨ lowerMixed d L)
    (h : Pyth (B d) H L) : False := by
  rcases hL with rfl | hl
  · have ha : d.q ∣ A d := ⟨d.p * d.s, by unfold A; ring⟩
    have hb : d.q ∣ B d := ⟨d.w, rfl⟩
    have hd : d.q ∣ H := pyth_dvd_of_dvd_right_two ha hb (pyth_rotate h)
    rcases hH with hH | hH
    · exact facts.unit_q_F (hH ▸ hd)
    · exact facts.unit_q_G (hH ▸ hd)
  · have hpq : d.p ^ 2 < d.q := by
      rcases facts.phase_p H L hH hl h with hx | hx
      · exact divisor_lt_hypotenuse (pow_pos d.p_pos _) d.hu_nz d.hv_nz d.q_pos d.uv hx
      · exact divisor_lt_hypotenuse (pow_pos d.p_pos _) d.hv_nz d.hu_nz d.q_pos
          (by simpa [add_comm] using d.uv) hx
    obtain ⟨k, x, hn, hx, hu, hl⟩ := facts.phase_q H L hH hl h
    exact incompatible_bounds (by have := d.hp; omega) hpq (phase_q_bound d hn hx hu hl)

private theorem no_FG_A_diff (d : Data)
    (h : (F d) ^ 2 - (G d) ^ 2 = (A d) ^ 2 ∨ (F d) ^ 2 - (G d) ^ 2 = -((A d) ^ 2)) :
    False := by
  have hST : 8 * d.r * d.t * d.u * d.v = d.p ^ 2 * d.q ^ 2 * d.s ∨
      8 * d.r * d.t * d.u * d.v = -(d.p ^ 2 * d.q ^ 2 * d.s) := by
    rcases h with h | h
    · left
      apply mul_cancel_int d.hs_nz
      unfold F G A at h
      rw [d.w_eq] at h
      linear_combination h
    · right
      apply mul_cancel_int d.hs_nz
      unfold F G A at h
      rw [d.w_eq] at h
      linear_combination h
  have hp2prod : d.p ^ 2 ∣ (8 * d.r * d.t) * (d.u * d.v) := by
    rcases hST with h | h
    · exact ⟨d.q^2*d.s, by linear_combination h⟩
    · exact ⟨-(d.q^2*d.s), by linear_combination h⟩
  have hq2prod : d.q ^ 2 ∣ (8 * d.u * d.v) * (d.r * d.t) := by
    rcases hST with h | h
    · exact ⟨d.p^2*d.s, by linear_combination h⟩
    · exact ⟨-(d.p^2*d.s), by linear_combination h⟩
  have hpq : d.p ^ 2 < d.q := by
    rcases pow_dvd_one_factor d.pp d.gcd_uv
        (Int.dvd_of_dvd_mul_right_of_gcd_one hp2prod d.gcd_p2_8rt) with hx | hx
    · exact divisor_lt_hypotenuse (pow_pos d.p_pos _) d.hu_nz d.hv_nz d.q_pos d.uv hx
    · exact divisor_lt_hypotenuse (pow_pos d.p_pos _) d.hv_nz d.hu_nz d.q_pos
        (by simpa [add_comm] using d.uv) hx
  have hqp : d.q ^ 2 < d.p ^ 2 := by
    rcases pow_dvd_one_factor d.qp d.gcd_rt
        (Int.dvd_of_dvd_mul_right_of_gcd_one hq2prod d.gcd_q2_8uv) with hx | hx
    · have hh := divisor_lt_hypotenuse (pow_pos d.q_pos _) d.hr_nz d.hs_nz d.p_pos d.rs hx
      nlinarith only [hh, sq_nonneg (d.p-1), d.hp]
    · apply divisor_lt_hypotenuse (x := d.t) (y := d.w) (pow_pos d.q_pos _) d.ht_nz d.hw_nz (pow_pos d.p_pos _) ?_ hx
      linear_combination d.tw
  exact incompatible_bounds (by have := d.hp; omega) hpq (by
    have hg : d.p ^ 2 ≤ d.p ^ 3 := by
      nlinarith only [mul_nonneg (sq_nonneg d.p) (show 0 ≤ d.p-1 by have := d.hp; omega)]
    exact lt_of_lt_of_le hqp hg)

private theorem no_FG_B_diff (d : Data)
    (h : (F d) ^ 2 - (G d) ^ 2 = (B d) ^ 2 ∨ (F d) ^ 2 - (G d) ^ 2 = -((B d) ^ 2)) :
    False := by
  have hST : d.q ^ 2 * d.w = 4 * d.t * d.u * d.v ∨
      d.q ^ 2 * d.w = -(4 * d.t * d.u * d.v) := by
    rcases h with h | h
    · left
      apply mul_cancel_int d.hw_nz
      unfold F G B at h
      linear_combination -h
    · right
      apply mul_cancel_int d.hw_nz
      unfold F G B at h
      linear_combination h
  obtain ⟨k, hk, hk1, hb⟩ := difference_factor (ne_of_gt (pow_pos d.q_pos 2))
      d.gcd_q2_4uv d.gcd_tw hST
  have hwbound : -(2 * d.q ^ 2) ≤ d.w ∧ d.w ≤ 2 * d.q ^ 2 := by
    rcases hb with hb | hb <;> rcases eq_or_neg hk1 with hz | hz <;>
      rw [hz] at hb <;> constructor <;>
      nlinarith only [hb, d.uv, sq_nonneg (d.u+d.v), sq_nonneg (d.u-d.v)]
  have hq2 : 5 ≤ d.q ^ 2 := by
    have hsub : 0 ≤ d.q - 5 := sub_nonneg.mpr d.hq
    have hadd : 0 ≤ d.q + 5 := by have := d.hq; omega
    nlinarith only [mul_nonneg hsub hadd]
  apply impossible_unbalanced d.qp hq2 d.gcd_rs_pm hk1 ?_ d.w_eq hwbound.1 hwbound.2
  linear_combination -d.t_eq + hk

private theorem no_FG_C_diff (d : Data)
    (h : (F d) ^ 2 - (G d) ^ 2 = (C d) ^ 2 ∨ (F d) ^ 2 - (G d) ^ 2 = -((C d) ^ 2)) :
    False := by
  have hST : d.p ^ 4 * d.v = 4 * d.u * d.w * d.t ∨
      d.p ^ 4 * d.v = -(4 * d.u * d.w * d.t) := by
    rcases h with h | h
    · left
      apply mul_cancel_int d.hv_nz
      unfold F G C at h
      linear_combination -h
    · right
      apply mul_cancel_int d.hv_nz
      unfold F G C at h
      linear_combination h
  obtain ⟨k, hk, hk1, hb⟩ := difference_factor (ne_of_gt (pow_pos d.p_pos 4))
      d.gcd_p4_4wt d.gcd_uv hST
  have hwbound : -(2 * d.p ^ 4) ≤ d.v ∧ d.v ≤ 2 * d.p ^ 4 := by
    rcases hb with hb | hb <;> rcases eq_or_neg hk1 with hz | hz <;>
      rw [hz] at hb <;> constructor <;>
      nlinarith only [hb, d.tw, sq_nonneg (d.t+d.w), sq_nonneg (d.t-d.w)]
  have hp2 : 25 ≤ d.p ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ d.p-5 by have := d.hp; omega) (show 0 ≤ d.p+5 by have := d.hp; omega)]
  have hp4 : 5 ≤ d.p ^ 4 := by
    nlinarith only [hp2, mul_nonneg (show 0 ≤ d.p^2-25 by omega) (show 0 ≤ d.p^2+25 by omega)]
  apply impossible_unbalanced d.pp hp4 d.gcd_mn_pm hk1 ?_ d.v_eq hwbound.1 hwbound.2
  linear_combination -d.u_eq + hk

private theorem no_FG_ABCDE (d : Data) {L : ℤ}
    (hL : L = A d ∨ L = B d ∨ L = C d ∨ L = D d ∨ L = E d)
    (h : Pyth (F d) (G d) L) : False := by
  have hsodd : OddI (d.t ^ 2 - d.w ^ 2) := by
    have ht := odd_sq d.ht_odd
    have hw : EvenI (d.w^2) := by
      rw [pow_two]
      exact even_mul d.hw_even
    unfold OddI at ht ⊢
    unfold EvenI at hw
    omega
  have hpodd1 : OddI (d.p ^ 2 - 8 * d.r ^ 2) := by
    have hp := odd_sq d.hp_odd
    have hr := even_mul (b := d.r ^ 2) (by decide : EvenI 8)
    unfold EvenI at hr
    unfold OddI at hp ⊢
    omega
  have hpodd2 : OddI (d.p ^ 4 - 2 * d.t ^ 2) := by
    have hp : OddI (d.p^4) := by
      have hpow : d.p ^ 4 = (d.p ^ 2) ^ 2 := by ring
      rw [hpow]
      exact odd_sq (odd_sq d.hp_odd)
    have ht := even_mul (b := d.t ^ 2) (by decide : EvenI 2)
    unfold EvenI at ht
    unfold OddI at hp ⊢
    omega
  rcases pyth_cases h with sum | diff | diff
  · rcases hL with rfl | rfl | rfl | rfl | rfl
    · apply no_twice_square hsodd (odd_mul (odd_sq d.hq_odd) hpodd1) d.hv_nz (y := d.s)
      unfold F G A at sum
      linear_combination sum - 2 * d.w ^ 2 * d.uv - (2 * d.q ^ 2 * (d.w + 2*d.r*d.s)) * d.w_eq
    · have hodd : OddI (-(d.q ^ 2)) := by
        have hq := odd_sq d.hq_odd
        unfold OddI at hq ⊢
        omega
      apply no_twice_square hsodd hodd d.hv_nz (y := d.w)
      unfold F G B at sum
      linear_combination sum - 2 * d.w ^ 2 * d.uv
    · apply no_twice_square (odd_sq d.hu_odd) hpodd2 d.hw_nz (y := d.v)
      unfold F G C at sum
      linear_combination sum
    · apply no_mixed_sum d.hp_odd d.hr_odd d.ht_odd d.hu_odd (by decide : OddI 1) d.hs_nz
        (v := d.v)
      unfold F G D at sum
      rw [d.w_eq] at sum
      linear_combination -sum
    · apply no_mixed_sum d.hp_odd d.hr_odd d.ht_odd d.hu_odd (by decide : OddI (-1)) d.hs_nz
        (v := d.v)
      unfold F G E at sum
      rw [d.w_eq] at sum
      linear_combination -sum
  · rcases hL with rfl | rfl | rfl | rfl | rfl
    · exact no_FG_A_diff d (Or.inl diff)
    · exact no_FG_B_diff d (Or.inl diff)
    · exact no_FG_C_diff d (Or.inl diff)
    · apply no_mixed_difference d.hp_odd d.hr_odd d.ht_odd d.hu_odd (by decide : OddI 1)
        (by decide : OddI 1) d.hs_nz (v := d.v)
      unfold F G D at diff
      rw [d.w_eq] at diff
      linear_combination -diff
    · apply no_mixed_difference d.hp_odd d.hr_odd d.ht_odd d.hu_odd (by decide : OddI (-1))
        (by decide : OddI 1) d.hs_nz (v := d.v)
      unfold F G E at diff
      rw [d.w_eq] at diff
      linear_combination -diff
  · rcases hL with rfl | rfl | rfl | rfl | rfl
    · exact no_FG_A_diff d (Or.inr diff)
    · exact no_FG_B_diff d (Or.inr diff)
    · exact no_FG_C_diff d (Or.inr diff)
    · apply no_mixed_difference d.hp_odd d.hr_odd d.ht_odd d.hu_odd (by decide : OddI 1)
        (by decide : OddI (-1)) d.hs_nz (v := d.v)
      unfold F G D at diff
      rw [d.w_eq] at diff
      linear_combination diff
    · apply no_mixed_difference d.hp_odd d.hr_odd d.ht_odd d.hu_odd (by decide : OddI (-1))
        (by decide : OddI (-1)) d.hs_nz (v := d.v)
      unfold F G E at diff
      rw [d.w_eq] at diff
      linear_combination diff

private abbrev lower (i : Fin 7) : Prop := i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4

private theorem sorted_case :
    ∀ i j k : Fin 7, i < j → j < k → twoTop i j k →
      (j = 5 ∧ k = 6 ∧ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) ∨
      ((k = 5 ∨ k = 6) ∧ ((i = 1 ∧ lower j) ∨ (j = 1 ∧ i = 0))) := by
  intro i j k hij hjk h
  unfold twoTop top at h
  unfold lower
  omega

private theorem no_sorted (d : Data) (facts : PhaseFacts d) {i j k : Fin 7}
    (hij : i < j) (hjk : j < k) (t : twoTop i j k)
    (h : Pyth (leg d i) (leg d j) (leg d k)) : False := by
  rcases sorted_case i j k hij hjk t with ⟨rfl, rfl, hi⟩ | ⟨hk, hij⟩
  · have hl : leg d i = A d ∨ leg d i = B d ∨ leg d i = C d ∨ leg d i = D d ∨ leg d i = E d := by
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    exact no_FG_ABCDE d hl (pyth_rotate h)
  · have hH : leg d k = F d ∨ leg d k = G d := by
      rcases hk with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hij with ⟨rfl, hj⟩ | ⟨rfl, rfl⟩
    · have hL : leg d j = A d ∨ lowerMixed d (leg d j) := by
        rcases hj with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      exact no_B_H_L d facts hH hL (pyth_swap (pyth_rotate (pyth_rotate h)))
    · have hL : leg d (0 : Fin 7) = A d ∨ lowerMixed d (leg d (0 : Fin 7)) :=
        Or.inl rfl
      exact no_B_H_L d facts hH hL (pyth_rotate h)

/-- All seven Gaussian states lead to contradiction. A (primitive) candidate
must have three distinct labels with at least one value not divisible by p.
The obligations upstream of this result are stated in Data and PhaseFacts. -/
theorem seven_state_elimination (d : Data) (facts : PhaseFacts d)
    {i j k : Fin 7} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (prim : ¬(d.p ∣ leg d i ∧ d.p ∣ leg d j ∧ d.p ∣ leg d k))
    (h : Pyth (leg d i) (leg d j) (leg d k)) : False := by
  have t : twoTop i j k := by
    by_cases ti : top i <;> by_cases tj : top j <;> by_cases tk : top k
    · exact Or.inl ⟨ti, tj⟩
    · exact Or.inl ⟨ti, tj⟩
    · exact Or.inr (Or.inl ⟨ti, tk⟩)
    · exact False.elim ((facts.unit_p i ti)
        (pyth_dvd_of_dvd_right_two (facts.divisible_p j tj) (facts.divisible_p k tk) h))
    · exact Or.inr (Or.inr ⟨tj, tk⟩)
    · exact False.elim ((facts.unit_p j tj)
        (pyth_dvd_of_dvd_right_two (facts.divisible_p i ti) (facts.divisible_p k tk) (pyth_swap h)))
    · exact False.elim ((facts.unit_p k tk)
        (pyth_dvd_of_dvd_right_two (facts.divisible_p i ti) (facts.divisible_p j tj)
          (pyth_rotate (pyth_rotate h))))
    · exact False.elim (prim ⟨facts.divisible_p i ti, facts.divisible_p j tj, facts.divisible_p k tk⟩)
  rcases lt_or_gt_of_ne hij with hi | hi
  · rcases lt_or_gt_of_ne hjk with hj | hj
    · exact no_sorted d facts hi hj t h
    · rcases lt_or_gt_of_ne hik with hk | hk
      · exact no_sorted d facts hk hj (twoTop_rotate (twoTop_swap t))
          (pyth_rotate (pyth_swap h))
      · exact no_sorted d facts hk hi (twoTop_rotate (twoTop_rotate t))
          (pyth_rotate (pyth_rotate h))
  · rcases lt_or_gt_of_ne hik with hk | hk
    · exact no_sorted d facts hi hk (twoTop_swap t) (pyth_swap h)
    · rcases lt_or_gt_of_ne hjk with hj | hj
      · exact no_sorted d facts hj hk (twoTop_rotate t) (pyth_rotate h)
      · exact no_sorted d facts hj hi (twoTop_swap (twoTop_rotate t))
          (pyth_swap (pyth_rotate h))

end Cuboid.P2

