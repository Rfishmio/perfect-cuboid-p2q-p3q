import CuboidGaussian
import P2Data
import GaussianPhase
import Mathlib.Tactic.FinCases

/-!
The lower diagonal exclusions in Korec, *Lower bounds for perfect rational
cuboids*, Theorem 5.1 (1992), https://dml.cz/handle/10338.dmlcz/132903.
-/

namespace CuboidFormal

open PerfectCuboid.GaussianRepr
open PerfectCuboid.GaussianPhase
open PerfectCuboid.P2Data

private theorem prime_power_even_leg_sq {p k : ℕ} (hp : p.Prime)
    {π z : GaussianInt} (hπ : normN π = p) (hπP : OddEven π) (hzP : OddEven z)
    (hz : normN z = (p ^ k) ^ 2) (hd : ¬ (p : ℤ) ∣ z.im) :
    z.im ^ 2 = (π ^ (2 * k)).im ^ 2 := by
  have hfac : π ^ (2 * k) * (star π) ^ (2 * k) = z * star z := by
    calc
      _ = (π * star π) ^ (2*k) := by rw [mul_pow]
      _ = (↑((p ^ k) ^ 2) : GaussianInt) := by rw [← cast_normN, hπ]; simp [pow_mul, Nat.mul_comm]
      _ = _ := by rw [← hz, cast_normN]
  obtain ⟨x,y,hx,hy,hxy⟩ := exists_dvd_and_dvd_of_dvd_mul (show
    z ∣ π ^ (2*k) * (star π) ^ (2*k) from ⟨star z, hfac⟩)
  obtain ⟨a,_,ha⟩ := (dvd_prime_pow (prime_of_prime_norm hp hπ) (2*k)).mp hx
  obtain ⟨b,_,hb⟩ := (dvd_prime_pow (prime_of_prime_norm hp (by simpa using hπ)) (2*k)).mp hy
  obtain ⟨ua,ha⟩ := ha.symm
  obtain ⟨ub,hb⟩ := hb.symm
  have hrep : z = ↑(ua * ub) * (π^a * (star π)^b) := by
    rw [hxy, ← ha, ← hb, Units.val_mul]
    ac_rfl
  have exp : a + b = 2*k := by
    have hn := congrArg normN hrep
    rw [hz, normN_mul, normN_isUnit.mpr (Units.isUnit (ua * ub)), one_mul] at hn
    simp only [normN_mul, normN_pow, normN_star, hπ, ← pow_add, ← pow_mul] at hn
    exact (pow_right_injective₀ hp.pos hp.ne_one hn).symm.trans (Nat.mul_comm k 2)
  have hzrep : z = ↑(ua * ub) * π ^ (2*k) ∨ z = ↑(ua * ub) * (star π) ^ (2*k) := by
    by_cases ha : a = 0
    · right
      have hb : b = 2*k := by omega
      simpa [ha, hb] using hrep
    · by_cases hb : b = 0
      · left
        have ha : a = 2*k := by omega
        simpa [ha, hb] using hrep
      · exfalso
        apply hd
        have has : a - 1 + 1 = a := by omega
        have hbs : b - 1 + 1 = b := by omega
        have hprod : (π * star π) * (↑(ua * ub) * (π^(a-1) * (star π)^(b-1))) = z := by
          rw [hrep]
          conv_rhs => rw [← has, ← hbs, pow_add, pow_add]
          simp only [pow_one]
          ring
        rw [← cast_normN, hπ] at hprod
        refine ⟨(↑(ua * ub) * (π^(a-1) * (star π)^(b-1)) : GaussianInt).im, ?_⟩
        simpa [Zsqrtd.im_mul] using (congrArg Zsqrtd.im hprod).symm
  rcases hzrep with h | h
  · rw [h] at hzP ⊢
    exact imag_sq_of_unit_mul (Units.isUnit _) (oddEven_pow hπP _) hzP
  · rw [h] at hzP ⊢
    have heq := imag_sq_of_unit_mul (Units.isUnit _) (oddEven_pow (oddEven_star hπP) (2*k)) hzP
    simpa [← star_pow, Zsqrtd.im_star] using heq

theorem forbidden_primitive_prime_power (p k : ℕ) (C : Cuboid) (hp : p.Prime)
    (hk : 0 < k) (hC : C.Primitive) : C.g ≠ (p : ℤ)^k := by
  intro hg
  obtain ⟨E⟩ := C.evenLegs hC
  have hd : (p : ℤ) ∣ C.g := by
    rw [hg]
    exact dvd_pow (dvd_refl _) hk.ne'
  have hp4 := E.prime_mod_four_of_dvd hp hd
  obtain ⟨π, hπ, hπP⟩ := split_prime_oddEven hp hp4
  have unique {e o : ℤ} (he : e % 2 = 0) (hn : e^2 + o^2 = C.g^2)
      (hnd : ¬ (p : ℤ) ∣ e) : e^2 = (π ^ (2*k)).im ^ 2 := by
    exact prime_power_even_leg_sq hp hπ hπP (gaussian_oddEven E.g_odd he hn)
      (gaussian_normN (by push_cast; exact hg) hn) hnd
  have hp1 : 1 < (p : ℤ) := by exact_mod_cast hp.one_lt
  rcases E.two_not_dvd_of_dvd_diagonal hp1 hd with ⟨hx,hy⟩ | ⟨hx,hz⟩ | ⟨hy,hz⟩
  · exact E.xy_ne (eq_of_pos_of_sq_eq E.x_pos E.y_pos
      ((unique E.x_even E.norm_x hx).trans (unique E.y_even E.norm_y hy).symm))
  · exact E.x_lt_z.ne (eq_of_pos_of_sq_eq E.x_pos E.z_pos
      ((unique E.x_even E.norm_x hx).trans (unique E.z_even E.norm_z hz).symm))
  · exact E.y_lt_z.ne (eq_of_pos_of_sq_eq E.y_pos E.z_pos
      ((unique E.y_even E.norm_y hy).trans (unique E.z_even E.norm_z hz).symm))

private def pqLeg (p q : ℕ) (π ρ : GaussianInt) (i : Fin 4) : ℤ :=
  let R := (π ^ 2).re
  let S := (π ^ 2).im
  let U := (ρ ^ 2).re
  let V := (ρ ^ 2).im
  ![(q : ℤ) * S, (p : ℤ) * V, S * U + R * V, S * U - R * V] i

private theorem pq_even_leg_state {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpodd : p%2 = 1) (hqodd : q%2 = 1) {π ρ z : GaussianInt}
    (hπ : normN π = p) (hρ : normN ρ = q) (hπP : OddEven π) (hρP : OddEven ρ)
    (hzP : OddEven z) (hz : normN z = (p*q)^2) (h0 : z.im ≠ 0) :
    ∃ i : Fin 4, z.im^2 = (pqLeg p q π ρ i)^2 := by
  obtain ⟨j,hj,l,hl,h⟩ := even_leg_signed_phase (k := 1) hp hq hpq hπ hρ hπP hρP hzP hpodd hqodd
    (by simpa using hz)
  have hj' : j = 0 ∨ j = 1 := by omega
  have hl' : l = 0 ∨ l = 1 := by omega
  rcases hj' with rfl | rfl <;> rcases hl' with rfl | rfl <;> rcases h with h | h
  · simp at h
    exact False.elim (h0 h)
  · simp at h
    exact False.elim (h0 h)
  · exact ⟨1, by simpa [pqLeg] using h⟩
  · exact ⟨1, by simpa [pqLeg] using h⟩
  · exact ⟨0, by simpa [pqLeg] using h⟩
  · exact ⟨0, by simpa [pqLeg] using h⟩
  · exact ⟨2, by simpa [pqLeg] using h⟩
  · exact ⟨3, by simpa [pqLeg] using h⟩

private theorem pq_phase_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) {π ρ : GaussianInt}
    (hπ : normN π = p) (hρ : normN ρ = q) {ε : ℤ} (he : ε = 1 ∨ ε = -1)
    (h : (p : ℤ)^2 ∣ ((q : ℤ)*(π^2).im)^2 - ε*(π^2*ρ^2).im^2) :
    (p : ℤ)^2 < (q : ℤ) := by
  have pn := norm_eq_natCast hπ
  have qn := norm_eq_natCast hρ
  have pp := prime_of_prime_norm hp hπ
  have qp := prime_of_prime_norm hq hρ
  have hπc := conjugates_coprime_of_prime_norm hp hp2 pp pn
  have hρc := conjugates_coprime_of_prime_norm hq hq2 qp qn
  have hρs : ¬ ρ ∣ star ρ := (qp.irreducible.coprime_iff_not_dvd).mp hρc
  have hc := nonzero_components_of_one_sided_power qp (show (2 : ℕ) ≠ 0 by decide) hρs
  have hx : (star π)^2 ∣ star (π^2 * (ρ.norm : GaussianInt)) := by
    refine ⟨(ρ.norm : GaussianInt), ?_⟩
    simp [star_mul, mul_comm]
  have hy : (star π)^2 ∣ star (π^2 * ρ^2) := by
    refine ⟨(star ρ)^2, ?_⟩
    simp [star_mul, star_pow, mul_comm]
  have hstarNorm : (star π).norm = (p : ℤ) := by simpa using pn
  have hstarρ := not_dvd_of_distinct_prime_norms hp hq hpq hstarNorm qn
  have hps : Prime (star π) := prime_of_prime_norm hp (by simpa using hπ)
  have hstarπ : ¬ star π ∣ π := (hps.irreducible.coprime_iff_not_dvd).mp hπc.symm
  have hu : ¬ star π ∣ π^2 := fun h => hstarπ (hps.dvd_of_dvd_pow h)
  have hb := forward_norm_bound (a := star π) (u := π^2) (z := ρ)
    hps (by simpa using hπc.symm)
    (norm_pow_coprime_two hp hp2 hstarNorm)
    (by rw [hstarNorm]; exact_mod_cast hp.pos)
    (by rw [qn]; exact_mod_cast hq.pos) hu hstarρ hc he hx hy
    (by simpa [hstarNorm, qn, Zsqrtd.im_mul, mul_comm] using h)
  simpa [hstarNorm, qn] using hb

private theorem pyth_compare {p x t z : ℤ} (h : Cuboid.P2.Pyth x (p*t) z) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ p^2 ∣ x^2 - ε*z^2 := by
  rcases h with h | h | h
  · exact ⟨1, Or.inl rfl, -t^2, by linear_combination h⟩
  · exact ⟨-1, Or.inr rfl, t^2, by linear_combination h⟩
  · exact ⟨1, Or.inl rfl, t^2, by linear_combination -h⟩

private theorem no_pq_both_single {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) {π ρ : GaussianInt}
    (hπ : normN π = p) (hρ : normN ρ = q)
    (h : Cuboid.P2.Pyth ((q : ℤ)*(π^2).im) ((p : ℤ)*(ρ^2).im) (π^2*ρ^2).im) : False := by
  obtain ⟨ε, he, hd⟩ := pyth_compare h
  have hpq' := pq_phase_bound hp hq hpq hp2 hq2 hπ hρ he hd
  have hs : Cuboid.P2.Pyth ((p : ℤ)*(ρ^2).im) ((q : ℤ)*(π^2).im) (ρ^2*π^2).im := by
    rw [mul_comm (ρ^2) (π^2)]
    rcases h with h | h | h
    · exact Or.inl (by simpa [add_comm] using h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  obtain ⟨η, hη, hqd⟩ := pyth_compare hs
  have hqp' := pq_phase_bound hq hp hpq.symm hq2 hp2 hρ hπ hη hqd
  have hp' : 1 ≤ (p : ℤ) := by exact_mod_cast hp.one_lt.le
  have hq' : 1 ≤ (q : ℤ) := by exact_mod_cast hq.one_lt.le
  nlinarith only [hpq', hqp', mul_nonneg (show 0 ≤ (p : ℤ) by omega) (sub_nonneg.mpr hp'),
    mul_nonneg (show 0 ≤ (q : ℤ) by omega) (sub_nonneg.mpr hq')]

private theorem no_pq_one_single {q r s R S U V : ℤ}
    (hq : q.natAbs.Prime) (hq5 : 5 ≤ q) (hR : R = r^2 - s^2) (hS : S = 2*r*s)
    (hRodd : R % 2 = 1) (hUodd : U % 2 = 1) (hVeven : V % 2 = 0)
    (hc : Int.gcd (r-s) (r+s) = 1) (hRS : Int.gcd R S = 1)
    (hub : Int.gcd (q^2) (4*U*V) = 1) (hSn : S ≠ 0) (hVn : V ≠ 0)
    (hqn : U^2 + V^2 = q^2)
    (h : Cuboid.P2.Pyth (q*S) (S*U+R*V) (S*U-R*V)) : False := by
  have hnd (he : q^2*S = 4*R*U*V ∨ q^2*S = -(4*R*U*V)) : False := by
    have hq0 : 0 < q := by omega
    obtain ⟨k, hk, hk1, hSk⟩ := Cuboid.P2.difference_factor
      (ne_of_gt (pow_pos hq0 2)) hub hRS he
    have hkpm : k = 1 ∨ k = -1 :=
      Int.natAbs_eq_natAbs_iff.mp (show k.natAbs = (1 : ℤ).natAbs by simpa using hk1)
    have hbound : -(2*q^2) ≤ S ∧ S ≤ 2*q^2 := by
      rcases hSk with hSk | hSk <;> rcases hkpm with hkpm | hkpm <;>
        rw [hkpm] at hSk <;> constructor <;>
        nlinarith only [hSk, hqn, sq_nonneg (U+V), sq_nonneg (U-V)]
    have hq2 : 5 ≤ q^2 := by
      nlinarith only [mul_nonneg (show 0 ≤ q - 5 by omega) (show 0 ≤ q + 5 by omega)]
    exact Cuboid.P2.impossible_unbalanced hq hq2 hc hk1
      (by linear_combination -hR + hk) hS hbound.1 hbound.2
  rcases h with h | h | h
  · apply hnd
    right
    apply mul_left_cancel₀ hSn
    linear_combination h
  · apply hnd
    left
    apply mul_left_cancel₀ hSn
    linear_combination h
  · have hoc : (V^2 - U^2) % 2 = 1 := by
      simp only [pow_two]
      rw [Int.sub_emod, Int.mul_emod V V, Int.mul_emod U U, hUodd, hVeven]; norm_num
    have hor : R^2 % 2 = 1 := by
      rw [pow_two, Int.mul_emod, hRodd]; norm_num
    exact Cuboid.P2.no_twice_square (y := S) hor hoc hVn (by linear_combination h - S^2 * hqn)

private theorem pq_single_and_mixed {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) {π ρ : GaussianInt}
    (hπ : normN π = p) (hρ : normN ρ = q) (hπP : OddEven π) (hρP : OddEven ρ) :
    ¬ Cuboid.P2.Pyth ((q : ℤ)*(π^2).im)
      ((π^2).im*(ρ^2).re + (π^2).re*(ρ^2).im)
      ((π^2).im*(ρ^2).re - (π^2).re*(ρ^2).im) := by
  intro h
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hqge := hq.two_le
  have hq5 : 5 ≤ (q : ℤ) := by
    have hqn : 5 ≤ q := by omega
    exact_mod_cast hqn
  have hpc := gcd_coords_of_power hp hp2 hπ (show (2 : ℕ) ≠ 0 by decide)
  have hπg : Int.gcd π.re π.im = 1 := by
    simpa using gcd_coords_of_power hp hp2 hπ (show (1 : ℕ) ≠ 0 by decide)
  have hπm := mod_of_oddEven hπP
  have hπpm := gcd_pm_of_odd_even hπm.1 hπm.2 hπg
  have hπsq := mod_of_oddEven (oddEven_pow hπP 2)
  have hρsq := mod_of_oddEven (oddEven_pow hρP 2)
  have hπd := prime_not_dvd_coords_of_power hp hp2 hπ (show (2 : ℕ) ≠ 0 by decide)
  have hρd := prime_not_dvd_coords_of_power hq hq2 hρ (show (2 : ℕ) ≠ 0 by decide)
  have hqc : Int.gcd ((q : ℤ)^2) (4*(ρ^2).re*(ρ^2).im) = 1 := by
    simpa using gcd_prime_power_mul_coords (n := 2) hq hq2 hρd.1 hρd.2 2
  have hqnorm : (ρ^2).re^2 + (ρ^2).im^2 = (q : ℤ)^2 := by
    rw [← gaussian_norm_eq]
    have hn : normN (ρ^2) = q^2 := by rw [normN_pow, hρ]
    exact_mod_cast norm_eq_natCast hn
  have hR : (π^2).re = π.re^2 - π.im^2 := by
    rw [pow_two, Zsqrtd.re_mul]
    ring
  have hS : (π^2).im = 2*π.re*π.im := by
    rw [pow_two, Zsqrtd.im_mul]
    ring
  exact no_pq_one_single (by simpa using hq) hq5 hR hS hπsq.1 hρsq.1 hρsq.2
    hπpm hpc hqc (fun h => hπd.2 (h ▸ dvd_zero _)) (fun h => hρd.2 (h ▸ dvd_zero _))
    hqnorm h

private theorem four_values_no_pyth (f : Fin 4 → ℤ)
    (h012 : ¬ Cuboid.P2.Pyth (f 0) (f 1) (f 2))
    (h013 : ¬ Cuboid.P2.Pyth (f 0) (f 1) (f 3))
    (h023 : ¬ Cuboid.P2.Pyth (f 0) (f 2) (f 3))
    (h123 : ¬ Cuboid.P2.Pyth (f 1) (f 2) (f 3))
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ Cuboid.P2.Pyth (f i) (f j) (f k) := by
  intro h
  have swap {a b c : ℤ} (ht : Cuboid.P2.Pyth a b c) : Cuboid.P2.Pyth b a c := by
    rcases ht with ht | ht | ht
    · exact Or.inl (by simpa only [add_comm] using ht)
    · exact Or.inr (Or.inr ht)
    · exact Or.inr (Or.inl ht)
  have rotate {a b c : ℤ} (ht : Cuboid.P2.Pyth a b c) : Cuboid.P2.Pyth b c a := by
    rcases ht with ht | ht | ht
    · exact Or.inr (Or.inl (by simpa only [add_comm] using ht))
    · exact Or.inr (Or.inr (by simpa only [add_comm] using ht))
    · exact Or.inl ht
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    first
    | exact hij rfl
    | exact hik rfl
    | exact hjk rfl
    | have hs := swap h
      have hr := rotate h
      have hrr := rotate hr
      have hrs := swap hr
      have hrrs := swap hrr
      first
      | exact h012 (by assumption)
      | exact h013 (by assumption)
      | exact h023 (by assumption)
      | exact h123 (by assumption)

theorem forbidden_primitive_prime_product : ForbiddenPrimitiveDiagonal 1 := by
  intro p q C hp hq hpq hC hg
  obtain ⟨E⟩ := C.evenLegs hC
  have hg' : C.g = (p : ℤ)*(q : ℤ) := by simpa using hg
  have hpd : (p : ℤ) ∣ C.g := hg' ▸ dvd_mul_right _ _
  have hqd : (q : ℤ) ∣ C.g := hg' ▸ dvd_mul_left _ _
  have hp4 := E.prime_mod_four_of_dvd hp hpd
  have hq4 := E.prime_mod_four_of_dvd hq hqd
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  obtain ⟨π, hπ, hπP⟩ := split_prime_oddEven hp hp4
  obtain ⟨ρ, hρ, hρP⟩ := split_prime_oddEven hq hq4
  let f := pqLeg p q π ρ
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := E.choose_labels f (by
    intro e o hep he hn
    exact pq_even_leg_state hp hq hpq (by omega) (by omega) hπ hρ hπP hρP
      (gaussian_oddEven E.g_odd he hn) (gaussian_normN (by push_cast; exact hg') hn)
      (ne_of_gt hep))
  have h012 : ¬ Cuboid.P2.Pyth (f 0) (f 1) (f 2) := by
    intro h
    apply no_pq_both_single hp hq hpq hp2 hq2 hπ hρ
    simpa [f, pqLeg, Zsqrtd.im_mul, add_comm] using h
  have h013 : ¬ Cuboid.P2.Pyth (f 0) (f 1) (f 3) := by
    intro h
    apply no_pq_both_single hp hq hpq hp2 hq2 hπ (ρ := star ρ) (by simpa using hρ)
    have hm : (π^2*(star ρ)^2).im = (π^2).im*(ρ^2).re - (π^2).re*(ρ^2).im := by
      rw [← star_pow, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
      ring
    rw [hm, ← star_pow, Zsqrtd.im_star]
    simpa [f, pqLeg, Cuboid.P2.Pyth] using h
  have h023 : ¬ Cuboid.P2.Pyth (f 0) (f 2) (f 3) := by
    simpa [f, pqLeg] using pq_single_and_mixed hp hq hp4 hq4 hπ hρ hπP hρP
  have h123 : ¬ Cuboid.P2.Pyth (f 1) (f 2) (f 3) := by
    have hsum : (ρ^2).im*(π^2).re + (ρ^2).re*(π^2).im =
        (π^2).im*(ρ^2).re + (π^2).re*(ρ^2).im := by ring
    have hsub : ((ρ^2).im*(π^2).re - (ρ^2).re*(π^2).im)^2 =
        ((π^2).im*(ρ^2).re - (π^2).re*(ρ^2).im)^2 := by ring
    have h := pq_single_and_mixed hq hp hq4 hp4 hρ hπ hρP hπP
    unfold Cuboid.P2.Pyth at h ⊢
    rw [hsum, hsub] at h
    exact h
  apply four_values_no_pyth f h012 h013 h023 h123 i j k hij hik hjk
  left
  rw [← hi, ← hj, ← hk]
  exact E.sum_sq

/-- Korec's prime-power exclusion for arbitrary integral cuboids. -/
theorem forbidden_prime_power (p k : ℕ) (C : Cuboid) (hp : p.Prime) :
    C.g ≠ (p : ℤ)^k := by
  intro hg
  obtain ⟨d, P, hd, hP, _, _, _, _, _, _, hscale⟩ := C.exists_primitive_core
  have hPn := Int.toNat_of_nonneg P.g_pos.le
  have hdn := Int.toNat_of_nonneg hd.le
  have hscaled : (P.g.toNat : ℤ) * (d.toNat : ℤ) = (p : ℤ)^k := by
    rw [hPn, hdn, mul_comm, ← hscale, hg]
  have hdiv : P.g.toNat ∣ p^k := ⟨d.toNat, by exact_mod_cast hscaled.symm⟩
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hdiv
  have hgP : P.g = (p : ℤ)^j := by
    rw [← hPn]
    exact_mod_cast hj
  by_cases h0 : j = 0
  · exact P.g_ne_one (by simpa [h0] using hgP)
  · exact forbidden_primitive_prime_power p j P hp (Nat.pos_of_ne_zero h0) hP hgP

/-- Korec's two-prime exclusion for arbitrary integral cuboids. -/
theorem forbidden_prime_product : ForbiddenDiagonal 1 :=
  forbidden_of_primitive_reductions 1 forbidden_primitive_prime_power
    forbidden_primitive_prime_product (by intro i hi hi'; omega)

end CuboidFormal
