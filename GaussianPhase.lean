import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
Gaussian divisibility lemmas for the body-diagonal argument. These lemmas use
divisibility by conjugate Gaussian prime powers in place of choosing square
roots of -1 modulo rational prime powers.
-/

namespace PerfectCuboid.GaussianPhase

private def I : GaussianInt := ⟨0, 1⟩

private theorem conjugate_sub (a : GaussianInt) :
    a - star a = I * ((2 * a.im : ℤ) : GaussianInt) := by
  apply Zsqrtd.ext
  · simp [I, Zsqrtd.re_sub, Zsqrtd.re_mul]
  · simp [I, Zsqrtd.im_sub, Zsqrtd.im_mul]
    ring

private theorem star_dvd {a b : GaussianInt} (h : a ∣ b) : star a ∣ star b := by
  obtain ⟨c, hc⟩ := h
  refine ⟨star c, ?_⟩
  simpa [star_mul, mul_comm] using congrArg star hc

private theorem mul_left_dvd {a b : GaussianInt} (h : a ∣ b) (c : GaussianInt) :
    a ∣ c*b := by
  obtain ⟨w,hw⟩ := h
  refine ⟨c*w,?_⟩
  rw [hw]
  ac_rfl

/-- A Gaussian prime power divides the rational norm power. -/
theorem gaussian_pow_dvd_norm_pow (a : GaussianInt) (n : ℕ) :
    a^n ∣ ((a.norm^n : ℤ) : GaussianInt) := by
  refine ⟨(star a)^n, ?_⟩
  rw [Int.cast_pow, Zsqrtd.norm_eq_mul_conj, mul_pow]

theorem gaussian_pow_dvd_of_norm_pow_dvd {a : GaussianInt} {n : ℕ} {u : ℤ}
    (h : a.norm^n ∣ u) : a^n ∣ (u : GaussianInt) :=
  dvd_trans (gaussian_pow_dvd_norm_pow a n) ((Zsqrtd.intCast_dvd_intCast _ _).mpr h)

private theorem coprime_pow_pow {a b : GaussianInt} (h : IsCoprime a b)
    (m n : ℕ) : IsCoprime (a^m) (b^n) := by
  have hright (k : ℕ) : IsCoprime a (b^k) := by
    induction k with
    | zero => simpa using (isCoprime_one_right : IsCoprime a (1 : GaussianInt))
    | succ k ih =>
      rw [pow_succ]
      exact ih.mul_right h
  induction m with
  | zero => simpa using (isCoprime_one_left : IsCoprime (1 : GaussianInt) (b^n))
  | succ m ih =>
    rw [pow_succ]
    exact ih.mul_left (hright n)

/-- Rational divisibility of Gaussian coordinates can be checked in either
conjugate factor for a real input with coprime conjugate factors. -/
theorem norm_pow_dvd_of_gaussian_pow_dvd_real {a : GaussianInt} {u : ℤ} {n : ℕ}
    (hc : IsCoprime a (star a)) (h : a^n ∣ (u : GaussianInt)) :
    a.norm^n ∣ u := by
  have h' : (star a)^n ∣ (u : GaussianInt) := by
    simpa [star_pow, star_intCast] using star_dvd h
  have hmul : a^n * (star a)^n ∣ (u : GaussianInt) :=
    (coprime_pow_pow hc n n).mul_dvd h h'
  rw [← mul_pow, ← Zsqrtd.norm_eq_mul_conj, ← Int.cast_pow] at hmul
  exact (Zsqrtd.intCast_dvd_intCast _ _).mp hmul

theorem norm_pow_dvd_of_gaussian_pow_dvd_imag {a : GaussianInt} {u : ℤ} {n : ℕ}
    (hc : IsCoprime a (star a)) (h : a^n ∣ I * (u : GaussianInt)) :
    a.norm^n ∣ u := by
  apply norm_pow_dvd_of_gaussian_pow_dvd_real hc
  have hi : -I * I = (1 : GaussianInt) := by
    apply Zsqrtd.ext <;> norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul]
  have h' := mul_left_dvd h (-I)
  simpa only [← mul_assoc, hi, one_mul] using h'

/-- The real/imaginary factor of a Gaussian sum or difference is divisible
by the corresponding rational norm power. -/
theorem norm_pow_dvd_of_phase_sum {a z : GaussianInt} {n : ℕ}
    (hc : IsCoprime a (star a)) (h : a^n ∣ z + star z) :
    a.norm^n ∣ 2*z.re := by
  apply norm_pow_dvd_of_gaussian_pow_dvd_real hc
  convert h using 1
  · apply Zsqrtd.ext
    · simp [Zsqrtd.re_add]
      ring
    · simp [Zsqrtd.im_add]

theorem norm_pow_dvd_of_phase_sub {a z : GaussianInt} {n : ℕ}
    (hc : IsCoprime a (star a)) (h : a^n ∣ z - star z) :
    a.norm^n ∣ 2*z.im := by
  apply norm_pow_dvd_of_gaussian_pow_dvd_imag hc
  rwa [← conjugate_sub]

/-- If a modulus annihilates both conjugate phases, congruences between the
squared imaginary parts transfer to congruences between squared phases. -/
theorem dvd_phase_sq_sub_of_dvd_imag_sq_sub {a x y : GaussianInt} {ε : ℤ}
    (hx : a ∣ star x) (hy : a ∣ star y)
    (h : a ∣ ((x.im^2 - ε*y.im^2 : ℤ) : GaussianInt)) :
    a ∣ x^2 - (ε : GaussianInt)*y^2 := by
  have hx' : a ∣ x^2 - (x - star x)^2 := by
    convert mul_left_dvd hx (2*x - star x) using 1
    ring
  have hy' : a ∣ y^2 - (y - star y)^2 := by
    convert mul_left_dvd hy (2*y - star y) using 1
    ring
  have hy'' := mul_left_dvd hy' (ε : GaussianInt)
  have hd := dvd_sub hx' hy''
  have hi : a ∣ (x - star x)^2 - (ε : GaussianInt)*(y - star y)^2 := by
    rw [conjugate_sub, conjugate_sub]
    convert mul_left_dvd h (4*I^2) using 1
    push_cast
    ring
  convert dvd_add hd hi using 1
  ring

/-- Cancel a common Gaussian phase factor from an integral square congruence.
The prime-power exponent is arbitrary. -/
theorem cancel_gaussian_phase_factor {a u x y : GaussianInt} {ε : ℤ} {n : ℕ}
    (hp : Prime a) (hu : ¬a ∣ u)
    (hx : a^n ∣ star (u*x)) (hy : a^n ∣ star (u*y))
    (h : a^n ∣ (((u*x).im^2 - ε*(u*y).im^2 : ℤ) : GaussianInt)) :
    a^n ∣ x^2 - (ε : GaussianInt)*y^2 := by
  have hphase := dvd_phase_sq_sub_of_dvd_imag_sq_sub hx hy h
  have hu' : ¬a ∣ u^2 := fun hh => hu (hp.dvd_of_dvd_pow hh)
  apply hp.pow_dvd_of_dvd_mul_left n hu'
  convert hphase using 1
  ring

/-- Compare a rational norm to one Gaussian phase, then remove the rational
factor 2 using coprimality. This is the forward prime-power comparison. -/
theorem prime_power_dvd_phase_coordinate {a z : GaussianInt} {n : ℕ}
    (ha : Prime a) (haStar : IsCoprime a (star a))
    (hTwo : IsCoprime (a.norm^n) (2 : ℤ))
    (hza : ¬a ∣ z)
    {ε : ℤ} (he : ε = 1 ∨ ε = -1)
    (h : a^n ∣ ((z.norm : GaussianInt)^2 - (ε : GaussianInt)*z^4)) :
    a.norm^n ∣ (z^2).re ∨ a.norm^n ∣ (z^2).im := by
  have hab : a^n ∣ (star z)^2 - (ε : GaussianInt)*z^2 := by
    apply ha.pow_dvd_of_dvd_mul_left n (show ¬a ∣ z^2 from
      fun hd => hza (ha.dvd_of_dvd_pow hd))
    convert h using 1
    rw [Zsqrtd.norm_eq_mul_conj]
    ring
  rcases he with rfl | rfl
  · right
    apply hTwo.dvd_of_dvd_mul_left
    apply norm_pow_dvd_of_phase_sub haStar
    have hneg := dvd_neg.mpr hab
    simpa [star_pow] using hneg
  · left
    apply hTwo.dvd_of_dvd_mul_left
    apply norm_pow_dvd_of_phase_sum haStar
    simpa [star_pow, add_comm] using hab

/-- The backward comparison after cancelling the common Gaussian block. -/
theorem prime_power_dvd_signed_component {a z : GaussianInt} {n : ℕ}
    (haStar : IsCoprime a (star a))
    (hTwo : IsCoprime (a.norm^n) (2 : ℤ))
    {ε : ℤ} (he : ε = 1 ∨ ε = -1)
    (h : a^n ∣ z - (ε : GaussianInt)*star z) :
    a.norm^n ∣ z.re ∨ a.norm^n ∣ z.im := by
  rcases he with rfl | rfl
  · right
    apply hTwo.dvd_of_dvd_mul_left
    apply norm_pow_dvd_of_phase_sub haStar
    simpa using h
  · left
    apply hTwo.dvd_of_dvd_mul_left
    apply norm_pow_dvd_of_phase_sum haStar
    simpa using h


/-- Primitive Gaussian phases retain the norm of the predicted base. This
also handles powers with a factor supported at the other rational prime. -/
theorem norm_pow_mul (a b : GaussianInt) (n m : ℕ) :
    (a^n * b^m).norm = a.norm^n * b.norm^m := by
  have hn (z : GaussianInt) (k : ℕ) : (z^k).norm = z.norm^k := by
    induction k with
    | zero => simp
    | succ k ih => simp [pow_succ, Zsqrtd.norm_mul, ih]
  rw [Zsqrtd.norm_mul, hn, hn]

/-- Distinct rational prime norms forbid Gaussian divisibility. -/
theorem not_dvd_of_distinct_prime_norms {a b : GaussianInt} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : a.norm = (p : ℤ)) (hb : b.norm = (q : ℤ)) : ¬a ∣ b := by
  rintro ⟨w,hw⟩
  have he : (q : ℤ) = (p : ℤ) * w.norm := by
    simpa [hb,ha,Zsqrtd.norm_mul] using congrArg Zsqrtd.norm hw
  have heN : q = p*w.norm.natAbs := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs he
  rcases hq.eq_one_or_self_of_dvd p ⟨_,heN⟩ with hp1 | hbq
  · exact hp.ne_one hp1
  · exact hpq hbq

/-- If a translated phase comparison forces divisibility of a nonzero
coordinate, then the corresponding norm supplies the strict real bound. -/
theorem norm_power_lt_of_dvd_coordinate {a z : GaussianInt} {n : ℕ}
    {g : ℤ} (ha : 0 < a.norm) (hg : 0 < g) (hn : z.norm = g^2)
    (h : (z.re ≠ 0 ∧ z.im ≠ 0))
    (hd : a.norm^n ∣ z.re ∨ a.norm^n ∣ z.im) :
    a.norm^n < g := by
  have hm : 0 < a.norm^n := pow_pos ha n
  have hsum : z.re ^ 2 + z.im ^ 2 = g ^ 2 := by
    simp only [Zsqrtd.norm_def] at hn
    nlinarith only [hn]
  rcases hd with hr | hi
  · rcases hr with ⟨w,hw⟩
    have hw0 : w ≠ 0 := by
      intro hw0
      exact h.1 (by simp [hw,hw0])
    have hlarge : (a.norm^n)^2 ≤ z.re^2 := by
      have hw1 : 1 ≤ w^2 := by
        rcases lt_or_gt_of_ne hw0 with hlt | hlt
        · have hlt' : w ≤ -1 := by omega
          nlinarith
        · have hlt' : 1 ≤ w := by omega
          nlinarith
      rw [hw,mul_pow]
      simpa using mul_le_mul_of_nonneg_left hw1 (sq_nonneg (a.norm^n))
    by_contra! hnot
    have hle := mul_le_mul hnot hnot hg.le hm.le
    have hg' : g^2 ≤ (a.norm^n)^2 := by simpa [pow_two] using hle
    have hi' : 0 < z.im^2 := sq_pos_iff.mpr h.2
    linarith
  · rcases hi with ⟨w,hw⟩
    have hw0 : w ≠ 0 := by
      intro hw0
      exact h.2 (by simp [hw,hw0])
    have hlarge : (a.norm^n)^2 ≤ z.im^2 := by
      have hw1 : 1 ≤ w^2 := by
        rcases lt_or_gt_of_ne hw0 with hlt | hlt
        · have hlt' : w ≤ -1 := by omega
          nlinarith
        · have hlt' : 1 ≤ w := by omega
          nlinarith
      rw [hw,mul_pow]
      simpa using mul_le_mul_of_nonneg_left hw1 (sq_nonneg (a.norm^n))
    by_contra! hnot
    have hle := mul_le_mul hnot hnot hg.le hm.le
    have hg' : g^2 ≤ (a.norm^n)^2 := by simpa [pow_two] using hle
    have hr' : 0 < z.re^2 := sq_pos_iff.mpr h.1
    linarith


private theorem natAbs_norm_dvd {a b : GaussianInt} (h : a ∣ b) :
    a.norm.natAbs ∣ b.norm.natAbs := by
  obtain ⟨w,hw⟩ := h
  exact ⟨w.norm.natAbs, by rw [hw,Zsqrtd.norm_mul,Int.natAbs_mul]⟩

/-- Coprimality of the two Gaussian factors of a split odd prime.
The separate Gaussian primality hypothesis follows from the norm-prime lemma. -/
theorem conjugates_coprime_of_prime_norm {a : GaussianInt} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : Prime a)
    (hna : a.norm = (p : ℤ)) : IsCoprime a (star a) := by
  apply ha.irreducible.coprime_iff_not_dvd.mpr
  intro h
  have hs : a + star a = ((2*a.re : ℤ) : GaussianInt) := by
    apply Zsqrtd.ext
    · simp [Zsqrtd.re_add, two_mul]
    · simp [Zsqrtd.im_add]
  have hdiv : a ∣ ((2*a.re : ℤ) : GaussianInt) := by
    rw [← hs]
    exact dvd_add (dvd_refl a) h
  have hreal : p ∣ (2*a.re).natAbs^2 := by
    simpa only [hna, Int.natAbs_natCast, Zsqrtd.norm_intCast, Int.natAbs_mul, pow_two]
      using natAbs_norm_dvd hdiv
  have hreal' : p ∣ 2*a.re.natAbs := by
    simpa [Int.natAbs_mul] using hp.dvd_of_dvd_pow hreal
  have hnot2 : ¬ p ∣ 2 := by
    intro h2
    rcases Nat.prime_two.eq_one_or_self_of_dvd p h2 with hp1 | hp'
    · exact hp.ne_one hp1
    · exact hp2 hp'
  have hR : (p : ℤ) ∣ a.re := Int.natCast_dvd.mpr
    ((hp.dvd_mul.mp hreal').resolve_left hnot2)
  have hsum : (p : ℤ) = a.re ^ 2 + a.im ^ 2 := by
    simp only [Zsqrtd.norm_def] at hna
    nlinarith only [hna]
  have hRne : a.re ≠ 0 := by
    intro hr
    have hsq : a.im.natAbs ^ 2 = p := by
      have h' : (p : ℤ) = a.im^2 := by simpa [hr] using hsum
      simpa [pow_two, Int.natAbs_mul] using (congrArg Int.natAbs h').symm
    have hfalse : (2 : ℕ) = 1 := (hp.pow_eq_iff.mp hsq).2
    omega
  obtain ⟨u,hu⟩ := hR
  have hu0 : u ≠ 0 := by
    intro hu0
    exact hRne (by simp [hu,hu0])
  have hpz : (1 : ℤ) < (p : ℤ) := by exact_mod_cast hp.one_lt
  have hu1 : 1 ≤ u^2 := by
    rcases lt_or_gt_of_ne hu0 with hlt | hlt
    · have hlt' : u ≤ -1 := by omega
      nlinarith
    · have hlt' : 1 ≤ u := by omega
      nlinarith
  have hlarge : (p : ℤ)^2 ≤ a.re^2 := by
    rw [hu,mul_pow]
    simpa using mul_le_mul_of_nonneg_left hu1 (sq_nonneg (p : ℤ))
  have hpsq : (p : ℤ) < (p : ℤ)^2 := by
    have hprod := mul_pos (show (0 : ℤ) < (p : ℤ) by omega)
      (show (0 : ℤ) < (p : ℤ) - 1 by omega)
    nlinarith
  linarith [sq_nonneg a.im]

theorem norm_pow_coprime_two {a : GaussianInt} {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hna : a.norm = (p : ℤ)) :
    IsCoprime (a.norm^n) (2 : ℤ) := by
  have h : (p ^ n).Coprime 2 := by
    have hc : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    exact hc.pow_left n
  rw [hna, ← Int.natCast_pow]
  exact h.isCoprime


/-- The forward comparison. The Gaussian factors are already oriented;
both star phases are killed by the relevant modulus. -/
theorem forward_norm_bound {a u z : GaussianInt} {n : ℕ} {ε : ℤ}
    (ha : Prime a) (haStar : IsCoprime a (star a))
    (hTwo : IsCoprime (a.norm^n) (2 : ℤ))
    (haPos : 0 < a.norm) (hzPos : 0 < z.norm)
    (hu : ¬a ∣ u) (hz : ¬a ∣ z)
    (hCoords : (z^2).re ≠ 0 ∧ (z^2).im ≠ 0)
    (he : ε = 1 ∨ ε = -1)
    (hx : a^n ∣ star (u*(z.norm : GaussianInt)))
    (hy : a^n ∣ star (u*z^2))
    (h : a.norm^n ∣
      (u*(z.norm : GaussianInt)).im^2 - ε*(u*z^2).im^2) :
    a.norm^n < z.norm := by
  have hdiv := cancel_gaussian_phase_factor ha hu hx hy
    (gaussian_pow_dvd_of_norm_pow_dvd h)
  have hdiv' : a^n ∣ (z.norm : GaussianInt)^2 - (ε : GaussianInt)*z^4 := by
    simpa only [show (z^2)^2 = z^4 by ring] using hdiv
  have hc := prime_power_dvd_phase_coordinate ha haStar hTwo hz he hdiv'
  apply norm_power_lt_of_dvd_coordinate haPos hzPos _ hCoords hc
  simpa using norm_pow_mul z 1 2 0

/-- The backward comparison for opposite blocks with a common factor.
The two surviving coordinate terms come from x² and its conjugate. -/
theorem backward_norm_bound {a u x : GaussianInt} {n : ℕ} {ε : ℤ}
    (ha : Prime a) (haStar : IsCoprime a (star a))
    (hTwo : IsCoprime (a.norm^n) (2 : ℤ))
    (haPos : 0 < a.norm) (hxPos : 0 < x.norm)
    (hu : ¬a ∣ u) (he : ε = 1 ∨ ε = -1)
    (hCoords : (x^2).re ≠ 0 ∧ (x^2).im ≠ 0)
    (hxs : a^n ∣ star (u*x))
    (hys : a^n ∣ star (u*star x))
    (h : a.norm^n ∣ (u*x).im^2 - ε*(u*star x).im^2) :
    a.norm^n < x.norm := by
  have hdiv := cancel_gaussian_phase_factor ha hu hxs hys
    (gaussian_pow_dvd_of_norm_pow_dvd h)
  have hdiv' : a^n ∣ x^2 - (ε : GaussianInt)*star (x^2) := by
    simpa only [star_pow] using hdiv
  have hc := prime_power_dvd_signed_component haStar hTwo he hdiv'
  apply norm_power_lt_of_dvd_coordinate haPos hxPos _ hCoords hc
  simpa using norm_pow_mul x 1 2 0


/-- A nonzero power lying in only one of the two Gaussian prime directions
can have neither an exactly real nor an exactly imaginary value. -/
theorem nonzero_components_of_one_sided_power {z : GaussianInt} {n : ℕ}
    (hp : Prime z) (hn : n ≠ 0) (hc : ¬z ∣ star z) :
    (z^n).re ≠ 0 ∧ (z^n).im ≠ 0 := by
  have hh : z ∣ z^n := by
    cases n with
    | zero => simp at hn
    | succ n =>
      refine ⟨z^n, ?_⟩
      rw [pow_succ]
      ac_rfl
  have hob : ¬z ∣ star (z^n) := by
    rw [star_pow]
    exact fun h => hc (hp.dvd_of_dvd_pow h)
  constructor
  · intro hz
    have he : star (z^n) = -(z^n) := by
      apply Zsqrtd.ext
      · simp only [Zsqrtd.re_star, Zsqrtd.re_neg, hz, neg_zero]
      · simp only [Zsqrtd.im_star, Zsqrtd.im_neg]
    exact hob (by rw [he]; exact dvd_neg.mpr hh)
  · intro hz
    have he : star (z^n) = z^n := by
      apply Zsqrtd.ext
      · simp only [Zsqrtd.re_star]
      · simp only [Zsqrtd.im_star, hz, neg_zero]
    exact hob (he.symm ▸ hh)

end PerfectCuboid.GaussianPhase

