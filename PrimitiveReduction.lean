import CuboidBasic
import Mathlib.Algebra.GCDMonoid.Nat

namespace CuboidFormal

private theorem int_quotient_positive {d x : ℤ}
    (hd : 0 < d) (hx : 0 < x) (hdiv : d ∣ x) :
    0 < x / d := by
  have heq : x / d * d = x := Int.ediv_mul_cancel hdiv
  by_contra! hn
  have hm := mul_nonpos_of_nonpos_of_nonneg hn hd.le
  rw [heq] at hm
  exact (not_le_of_gt hx) hm

/-- A common factor of both legs of an integral right triangle divides the third side. -/
theorem common_dvd_face_diag {d x y z : ℤ}
    (hx : d ∣ x) (hy : d ∣ y) (h : z ^ 2 = x ^ 2 + y ^ 2) :
    d ∣ z := by
  apply (Int.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
  rw [h]
  exact Int.dvd_add (pow_dvd_pow_of_dvd hx 2) (pow_dvd_pow_of_dvd hy 2)

/-- A common factor of all three edges divides the body diagonal. -/
theorem common_dvd_body_diag {d x y z g : ℤ}
    (hx : d ∣ x) (hy : d ∣ y) (hz : d ∣ z)
    (h : g ^ 2 = x ^ 2 + y ^ 2 + z ^ 2) :
    d ∣ g := by
  apply (Int.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
  rw [h]
  exact Int.dvd_add (Int.dvd_add (pow_dvd_pow_of_dvd hx 2) (pow_dvd_pow_of_dvd hy 2))
    (pow_dvd_pow_of_dvd hz 2)

/-- At least two of the three even legs avoid any nontrivial divisor of the diagonal. -/
theorem EvenLegs.two_not_dvd_of_dvd_diagonal {g d : ℤ} (E : EvenLegs g)
    (hd : 1 < d) (hg : d ∣ g) :
    (¬ d ∣ E.x ∧ ¬ d ∣ E.y) ∨
      (¬ d ∣ E.x ∧ ¬ d ∣ E.z) ∨ (¬ d ∣ E.y ∧ ¬ d ∣ E.z) := by
  have dvd_of_square_diff {u v w : ℤ} (hu : d ∣ u) (hv : d ∣ v)
      (h : w ^ 2 = u ^ 2 - v ^ 2) : d ∣ w := by
    apply (Int.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
    rw [h]
    exact Int.dvd_sub (pow_dvd_pow_of_dvd hu 2) (pow_dvd_pow_of_dvd hv 2)
  have not_all (hx : d ∣ E.x) (hy : d ∣ E.y) (hz : d ∣ E.z) : False :=
    E.primitive d hd hx hy (dvd_of_square_diff hg hz (by linarith only [E.norm_z]))
  by_cases hx : d ∣ E.x
  · have hy : ¬ d ∣ E.y := fun hy => not_all hx hy
      (common_dvd_face_diag hx hy E.sum_sq.symm)
    have hz : ¬ d ∣ E.z := fun hz =>
      not_all hx (dvd_of_square_diff hz hx (by linarith only [E.sum_sq])) hz
    exact Or.inr (Or.inr ⟨hy, hz⟩)
  · by_cases hy : d ∣ E.y
    · have hz : ¬ d ∣ E.z := fun hz =>
        not_all (dvd_of_square_diff hz hy (by linarith only [E.sum_sq])) hy hz
      exact Or.inr (Or.inl ⟨hx, hz⟩)
    · exact Or.inl ⟨hx, hy⟩

private theorem quotient_face_sq {d x y z : ℤ}
    (hd : d ≠ 0) (hx : d ∣ x) (hy : d ∣ y) (hz : d ∣ z)
    (h : z ^ 2 = x ^ 2 + y ^ 2) :
    (z / d) ^ 2 = (x / d) ^ 2 + (y / d) ^ 2 := by
  have ht : ((z / d) * d) ^ 2 = ((x / d) * d) ^ 2 + ((y / d) * d) ^ 2 := by
    rw [Int.ediv_mul_cancel hz, Int.ediv_mul_cancel hx, Int.ediv_mul_cancel hy]
    exact h
  have hcancel : d ^ 2 * ((z / d) ^ 2 - ((x / d) ^ 2 + (y / d) ^ 2)) = 0 := by
    linear_combination ht
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left (pow_ne_zero 2 hd))

private theorem quotient_body_sq {d x y z g : ℤ}
    (hd : d ≠ 0) (hx : d ∣ x) (hy : d ∣ y) (hz : d ∣ z) (hg : d ∣ g)
    (h : g ^ 2 = x ^ 2 + y ^ 2 + z ^ 2) :
    (g / d) ^ 2 = (x / d) ^ 2 + (y / d) ^ 2 + (z / d) ^ 2 := by
  have ht : ((g / d) * d) ^ 2 =
      ((x / d) * d) ^ 2 + ((y / d) * d) ^ 2 + ((z / d) * d) ^ 2 := by
    rw [Int.ediv_mul_cancel hg, Int.ediv_mul_cancel hx,
      Int.ediv_mul_cancel hy, Int.ediv_mul_cancel hz]
    exact h
  have hcancel : d ^ 2 * ((g / d) ^ 2 - ((x / d) ^ 2 + (y / d) ^ 2 + (z / d) ^ 2)) = 0 := by
    linear_combination ht
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left (pow_ne_zero 2 hd))

/-- Divide all seven lengths by a positive common divisor of the edges. -/
def Cuboid.divide (C : Cuboid) (d : ℤ) (hd : 0 < d)
    (ha : d ∣ C.a) (hb : d ∣ C.b) (hc : d ∣ C.c) : Cuboid := by
  have hab := common_dvd_face_diag ha hb C.ab_sq
  have hac := common_dvd_face_diag ha hc C.ac_sq
  have hbc := common_dvd_face_diag hb hc C.bc_sq
  have hg := common_dvd_body_diag ha hb hc C.g_sq
  exact {
    a := C.a / d
    b := C.b / d
    c := C.c / d
    ab := C.ab / d
    ac := C.ac / d
    bc := C.bc / d
    g := C.g / d
    a_pos := int_quotient_positive hd C.a_pos ha
    b_pos := int_quotient_positive hd C.b_pos hb
    c_pos := int_quotient_positive hd C.c_pos hc
    ab_pos := int_quotient_positive hd C.ab_pos hab
    ac_pos := int_quotient_positive hd C.ac_pos hac
    bc_pos := int_quotient_positive hd C.bc_pos hbc
    g_pos := int_quotient_positive hd C.g_pos hg
    ab_sq := quotient_face_sq (ne_of_gt hd) ha hb hab C.ab_sq
    ac_sq := quotient_face_sq (ne_of_gt hd) ha hc hac C.ac_sq
    bc_sq := quotient_face_sq (ne_of_gt hd) hb hc hbc C.bc_sq
    g_sq := quotient_body_sq (ne_of_gt hd) ha hb hc hg C.g_sq
  }

/-- Every integral cuboid reduces to a primitive one, with the same positive
scale in every edge, face diagonal, and body diagonal. -/
theorem Cuboid.exists_primitive_core (C : Cuboid) :
    ∃ (d : ℤ) (P : Cuboid), 0 < d ∧ P.Primitive ∧
      C.a = d * P.a ∧ C.b = d * P.b ∧ C.c = d * P.c ∧
      C.ab = d * P.ab ∧ C.ac = d * P.ac ∧ C.bc = d * P.bc ∧ C.g = d * P.g := by
  let gAB : ℤ := Int.gcd C.a C.b
  let d : ℤ := Int.gcd gAB C.c
  have hd : 0 < d := by
    have hne : Int.gcd gAB C.c ≠ 0 := by
      intro hz
      exact (ne_of_gt C.c_pos) (Int.gcd_eq_zero_iff.mp hz).2
    change (0 : ℤ) < (Int.gcd gAB C.c : ℤ)
    exact_mod_cast (Nat.pos_of_ne_zero hne)
  have hdAB : d ∣ gAB := Int.gcd_dvd_left gAB C.c
  have ha : d ∣ C.a := hdAB.trans (Int.gcd_dvd_left C.a C.b)
  have hb : d ∣ C.b := hdAB.trans (Int.gcd_dvd_right C.a C.b)
  have hc : d ∣ C.c := Int.gcd_dvd_right gAB C.c
  let P := C.divide d hd ha hb hc
  have restore {n : ℤ} (hn : d ∣ n) : n = d * (n / d) := by
    simpa [mul_comm] using (Int.ediv_mul_cancel hn).symm
  have hA : C.a = d * P.a := restore ha
  have hB : C.b = d * P.b := restore hb
  have hC : C.c = d * P.c := restore hc
  refine ⟨d, P, hd, ?_, hA, hB, hC, ?_, ?_, ?_, ?_⟩
  · intro e he heA heB heC
    have hA' : e * d ∣ C.a := by
      obtain ⟨k, hk⟩ := heA
      exact ⟨k, by rw [hA, hk]; ring⟩
    have hB' : e * d ∣ C.b := by
      obtain ⟨k, hk⟩ := heB
      exact ⟨k, by rw [hB, hk]; ring⟩
    have hC' : e * d ∣ C.c := by
      obtain ⟨k, hk⟩ := heC
      exact ⟨k, by rw [hC, hk]; ring⟩
    have hdd : e * d ∣ d :=
      Int.dvd_coe_gcd (Int.dvd_coe_gcd hA' hB') hC'
    obtain ⟨k, hk⟩ := hdd
    have hmul : d * (e * k) = d * 1 := by
      calc
        d * (e * k) = e * d * k := by ring
        _ = d := hk.symm
        _ = d * 1 := by ring
    have hzero : d * (e * k - 1) = 0 := by linear_combination hmul
    have hk1 : e * k = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt hd))
    by_cases hkpos : 0 < k
    · have hprod : 0 < (e - 1) * k := mul_pos (sub_pos.mpr he) hkpos
      nlinarith only [hprod, hk1, hkpos]
    · have hprod : e * k ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
  · exact restore (common_dvd_face_diag ha hb C.ab_sq)
  · exact restore (common_dvd_face_diag ha hc C.ac_sq)
  · exact restore (common_dvd_face_diag hb hc C.bc_sq)
  · exact restore (common_dvd_body_diag ha hb hc C.g_sq)


/-- No positive integral cuboid has body diagonal one. -/
theorem Cuboid.g_ne_one (C : Cuboid) : C.g ≠ 1 := by
  intro h
  have ha : 1 ≤ C.a := Int.add_one_le_iff.mpr C.a_pos
  have hb : 1 ≤ C.b := Int.add_one_le_iff.mpr C.b_pos
  have hc : 1 ≤ C.c := Int.add_one_le_iff.mpr C.c_pos
  have haa := mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ C.a + 1 by omega)
  have hbb := mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ C.b + 1 by omega)
  have hcc := mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ C.c + 1 by omega)
  have hsq := C.g_sq
  rw [h] at hsq
  nlinarith only [haa, hbb, hcc, hsq]

/-- A positive divisor of p^k*q has exponents at most k and one, respectively. -/
theorem divisor_of_prime_power_mul {m p q k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : m ∣ p ^ k * q) :
    ∃ i j : ℕ, i ≤ k ∧ j ≤ 1 ∧ m = p ^ i * q ^ j := by
  obtain ⟨a, b, ha, hb, heq⟩ := exists_dvd_and_dvd_of_dvd_mul hm
  obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow hp).mp ha
  have hbb : b ∣ q ^ 1 := by simpa using hb
  obtain ⟨j, hj, hbj⟩ := (Nat.dvd_prime_pow hq).mp hbb
  exact ⟨i, j, hi, hj, heq.trans (congrArg₂ (· * ·) hai hbj)⟩

/-- Extend primitive exclusions to the full claim. The prior prime-power
and two-prime exclusions are explicit inputs, alongside the exclusions of
the other primitive diagonal types with exponent at most k. -/
theorem forbidden_of_primitive_reductions (k : ℕ)
    (hPow : ∀ (p : ℕ) (i : ℕ) (C : Cuboid), p.Prime → 0 < i →
      C.Primitive → C.g ≠ (p : ℤ) ^ i)
    (hProd : ForbiddenPrimitiveDiagonal 1)
    (hAtLeastTwo : ∀ i : ℕ, 2 ≤ i → i ≤ k → ForbiddenPrimitiveDiagonal i) :
    ForbiddenDiagonal k := by
  intro p q C hp hq hpq hg
  obtain ⟨d, P, hd, hP, _, _, _, _, _, _, hscale⟩ := C.exists_primitive_core
  have hPa : 0 ≤ P.g := P.g_pos.le
  have hPn : (P.g.toNat : ℤ) = P.g := Int.toNat_of_nonneg hPa
  have hd' : 0 ≤ d := hd.le
  have hdn : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd'
  have hg' : (P.g.toNat : ℤ) * (d.toNat : ℤ) = (p : ℤ) ^ k * (q : ℤ) := by
    rw [hPn, hdn, mul_comm, ← hscale, hg]
  have hdiv : P.g.toNat ∣ p ^ k * q := ⟨d.toNat, by exact_mod_cast hg'.symm⟩
  obtain ⟨i, j, hi, hj, hshape⟩ := divisor_of_prime_power_mul hp hq hdiv
  have hshape' : P.g = (p : ℤ) ^ i * (q : ℤ) ^ j := by
    have hcast : (P.g.toNat : ℤ) = (p : ℤ) ^ i * (q : ℤ) ^ j := by
      exact_mod_cast hshape
    exact hPn.symm.trans hcast
  by_cases hj0 : j = 0
  · have heq : P.g = (p : ℤ) ^ i := by simpa [hj0] using hshape'
    by_cases hi0 : i = 0
    · exact P.g_ne_one (by simpa [hi0] using heq)
    · exact hPow p i P hp (by omega) hP heq
  · have hj1 : j = 1 := by omega
    have heq : P.g = (p : ℤ) ^ i * (q : ℤ) := by simpa [hj1] using hshape'
    by_cases hi0 : i = 0
    · exact hPow q 1 P hq (by decide) hP (by simpa [hi0] using heq)
    · by_cases hi1 : i = 1
      · exact hProd p q P hp hq hpq hP (by simpa [hi1] using heq)
      · exact hAtLeastTwo i (by omega) hi p q P hp hq hpq hP heq

end CuboidFormal

