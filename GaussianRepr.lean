import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

namespace PerfectCuboid.GaussianRepr

/-- The natural-valued Gaussian norm is multiplicative. -/
def normN (z : GaussianInt) : ℕ := z.norm.natAbs

@[simp] theorem normN_mul (w z : GaussianInt) :
    normN (w * z) = normN w * normN z := by
  simp [normN, Zsqrtd.norm_mul, Int.natAbs_mul]

@[simp] theorem normN_one : normN (1 : GaussianInt) = 1 := by
  simp [normN]

@[simp] theorem normN_pow (z : GaussianInt) (n : ℕ) : normN (z ^ n) = normN z ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

@[simp] theorem normN_star (z : GaussianInt) : normN (star z) = normN z := by
  simp [normN]

theorem normN_isUnit {z : GaussianInt} :
    normN z = 1 ↔ IsUnit z :=
  Zsqrtd.norm_eq_one_iff

theorem prime_of_prime_norm {p : ℕ} (hp : p.Prime) {z : GaussianInt}
    (hn : normN z = p) : Prime z := by
  apply irreducible_iff_prime.mp
  constructor
  · intro h
    exact hp.ne_one (hn.symm.trans (normN_isUnit.mpr h))
  · intro x y h
    have hnorm : normN x * normN y = p := by simpa [h] using hn
    rcases hp.eq_one_or_self_of_dvd _ ⟨normN y, hnorm.symm⟩ with hx | hx
    · exact Or.inl (normN_isUnit.mp hx)
    · apply Or.inr
      apply normN_isUnit.mp
      apply mul_left_cancel₀ hp.ne_zero
      simpa [hx] using hnorm

/-- A Gaussian integer of rational prime-power product norm has the expected
four-factor form once Gaussian factors of the two rational primes are fixed. -/
theorem four_factor_representation
    {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {π ρ z : GaussianInt} (hπ : normN π = p) (hρ : normN ρ = q)
    (hz : normN z = (p ^ k * q) ^ 2) :
    ∃ a b c d : ℕ, a + b = 2 * k ∧ c + d = 2 ∧
      ∃ u : GaussianIntˣ,
        z = ↑u * (π ^ a * (star π) ^ b * (ρ ^ c * (star ρ) ^ d)) := by
  have hz' : z.norm = (↑((p ^ k * q) ^ 2) : ℤ) := by
    rw [← hz]
    exact (Int.natAbs_of_nonneg (GaussianInt.norm_nonneg z)).symm
  have hp' : π * star π = (p : GaussianInt) := by
    rw [← Zsqrtd.norm_eq_mul_conj]
    have hπ' : π.norm = (p : ℤ) := by
      rw [← hπ]
      exact (Int.natAbs_of_nonneg (GaussianInt.norm_nonneg π)).symm
    simp [hπ']
  have hq' : ρ * star ρ = (q : GaussianInt) := by
    rw [← Zsqrtd.norm_eq_mul_conj]
    have hρ' : ρ.norm = (q : ℤ) := by
      rw [← hρ]
      exact (Int.natAbs_of_nonneg (GaussianInt.norm_nonneg ρ)).symm
    simp [hρ']
  have hfac :
      π ^ (2*k) * (star π) ^ (2*k) * (ρ ^ 2 * (star ρ) ^ 2) = z * star z := by
    calc
      _ = (((π * star π) ^ k) * (ρ * star ρ)) ^ 2 := by
        simp only [mul_pow, ← pow_mul, Nat.mul_comm 2 k]
      _ = (↑((p ^ k * q) ^ 2) : GaussianInt) := by
        simp [hp', hq']
      _ = _ := by
        simpa [hz'] using Zsqrtd.norm_eq_mul_conj z
  have hdiv : z ∣ π ^ (2*k) * (star π) ^ (2*k) * (ρ ^ 2 * (star ρ) ^ 2) :=
    ⟨star z, hfac⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
  obtain ⟨x₁, x₂, hx₁, hx₂, hx⟩ := exists_dvd_and_dvd_of_dvd_mul hx
  obtain ⟨y₁, y₂, hy₁, hy₂, hy⟩ := exists_dvd_and_dvd_of_dvd_mul hy
  have hπp := prime_of_prime_norm hp hπ
  have hπsp : Prime (star π) := prime_of_prime_norm hp (by simpa using hπ)
  have hρp := prime_of_prime_norm hq hρ
  have hρsp : Prime (star ρ) := prime_of_prime_norm hq (by simpa using hρ)
  obtain ⟨a, _, ha⟩ := (dvd_prime_pow hπp (2 * k)).mp hx₁
  obtain ⟨b, _, hb⟩ := (dvd_prime_pow hπsp (2 * k)).mp hx₂
  obtain ⟨c, _, hc⟩ := (dvd_prime_pow hρp 2).mp hy₁
  obtain ⟨d, _, hd⟩ := (dvd_prime_pow hρsp 2).mp hy₂
  obtain ⟨ua, ha⟩ := ha.symm
  obtain ⟨ub, hb⟩ := hb.symm
  obtain ⟨uc, hc⟩ := hc.symm
  obtain ⟨ud, hd⟩ := hd.symm
  have heq : z = ↑(ua * ub * (uc * ud)) * (π ^ a * (star π) ^ b * (ρ ^ c * (star ρ) ^ d)) := by
    rw [hxy, hx, hy, ← ha, ← hb, ← hc, ← hd]
    simp only [Units.val_mul]
    ac_rfl
  have hpowers : p ^ (a + b) * q ^ (c + d) = p ^ (k * 2) * q ^ 2 := by
    have ht := congrArg normN heq
    rw [hz] at ht
    have hu : normN (↑(ua * ub * (uc * ud)) : GaussianInt) = 1 :=
      normN_isUnit.mpr (Units.isUnit _)
    rw [normN_mul, hu, one_mul] at ht
    simp only [normN_mul, normN_pow, normN_star, hπ, hρ] at ht
    rw [mul_pow, ← pow_mul] at ht
    simpa only [pow_add, mul_assoc] using ht.symm
  have hpcount (n : ℕ) : (p ^ n).factorization p = n := by
    rw [Nat.factorization_pow, hp.factorization]
    simp
  have hqcount (n : ℕ) : (q ^ n).factorization q = n := by
    rw [Nat.factorization_pow, hq.factorization]
    simp
  have hpzero (n : ℕ) : (p ^ n).factorization q = 0 := by
    rw [Nat.factorization_pow, hp.factorization]
    simp [hpq]
  have hqzero (n : ℕ) : (q ^ n).factorization p = 0 := by
    rw [Nat.factorization_pow, hq.factorization]
    simp [hpq]
  have hab := congrArg (fun m : ℕ => m.factorization p) hpowers
  have hcd := congrArg (fun m : ℕ => m.factorization q) hpowers
  simp only [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero)
    (pow_ne_zero _ hq.ne_zero), Finsupp.add_apply, hpcount, hqcount, hpzero, hqzero,
    add_zero, zero_add] at hab hcd
  exact ⟨a,b,c,d, by omega, hcd, _, heq⟩


theorem cast_normN (z : GaussianInt) : (normN z : GaussianInt) = z * star z := by
  rw [← Zsqrtd.norm_eq_mul_conj]
  have hn : ((normN z : ℕ) : ℤ) = z.norm :=
    Int.natAbs_of_nonneg (GaussianInt.norm_nonneg z)
  simpa using congrArg (fun n : ℤ => (n : GaussianInt)) hn

/-- An inert rational prime dividing a Gaussian norm divides both coordinates. -/
theorem inert_prime_dvd_components {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 3)
    {z : GaussianInt} (hn : (p : ℤ) ∣ z.norm) :
    (p : ℤ) ∣ z.re ∧ (p : ℤ) ∣ z.im := by
  let : Fact p.Prime := ⟨hp⟩
  have hprime : Prime (p : GaussianInt) :=
    (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mpr hmod
  have hcast : ((p : ℤ) : GaussianInt) ∣ (z.norm : GaussianInt) :=
    (Zsqrtd.intCast_dvd_intCast (d := -1) _ _).mpr hn
  have hprod : (p : GaussianInt) ∣ z * star z := by
    simpa [Zsqrtd.norm_eq_mul_conj] using hcast
  have hd : (p : GaussianInt) ∣ z := by
    rcases hprime.dvd_mul.mp hprod with h | ⟨w, hw⟩
    · exact h
    · refine ⟨star w, ?_⟩
      simpa [star_mul, mul_comm] using congrArg star hw
  obtain ⟨w, hw⟩ := hd
  exact ⟨⟨w.re, by simpa [Zsqrtd.re_mul] using congrArg Zsqrtd.re hw⟩,
    ⟨w.im, by simpa [Zsqrtd.im_mul] using congrArg Zsqrtd.im hw⟩⟩

/-- An exponent pair adding to an even number reduces to a rational factor
times a one-sided even exponent. -/
theorem balanced_powers {z : GaussianInt} {a b k : ℕ}
    (h : a + b = 2 * k) :
    ∃ j ≤ k, z ^ a * (star z) ^ b =
       ((normN z : GaussianInt) ^ (k - j)) *
         (z ^ (2 * j)) ∨
      z ^ a * (star z) ^ b =
       ((normN z : GaussianInt) ^ (k - j)) *
         ((star z) ^ (2 * j)) := by
  by_cases hab : b ≤ a
  · refine ⟨k-b, Nat.sub_le _ _, Or.inl ?_⟩
    have hb : k - (k-b) = b := by omega
    have ha : a = b + 2*(k-b) := by omega
    rw [hb, cast_normN, mul_pow, ha, pow_add]
    ring
  · refine ⟨k-a, Nat.sub_le _ _, Or.inr ?_⟩
    have ha : k - (k-a) = a := by omega
    have hb : b = a + 2*(k-a) := by omega
    rw [ha, cast_normN, mul_pow, hb, pow_add]
    ring

/-- A product of Gaussian primes of norms p and q can be expressed with
normalized exponents in [0,k] and [0,1] after choosing the directions. -/
theorem reduced_factor_representation
    {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {π ρ z : GaussianInt} (hπ : normN π = p) (hρ : normN ρ = q)
    (hz : normN z = (p ^ k * q) ^ 2) :
    ∃ j ≤ k, ∃ l ≤ 1, ∃ x y : GaussianInt,
      (x = π ∨ x = star π) ∧ (y = ρ ∨ y = star ρ) ∧
      ∃ u : GaussianIntˣ,
        z = ↑u * ((p : GaussianInt) ^ (k-j) * (q : GaussianInt) ^ (1-l) *
          (x ^ (2*j) * y ^ (2*l))) := by
  obtain ⟨a,b,c,d,hab,hcd,u,hu⟩ := four_factor_representation hp hq hpq hπ hρ hz
  obtain ⟨j, hj, hj'⟩ := balanced_powers (z := π) hab
  obtain ⟨l, hl, hl'⟩ := balanced_powers (z := ρ) (k := 1) (by omega : c + d = 2 * 1)
  rcases hj' with hj' | hj' <;> rcases hl' with hl' | hl'
  · refine ⟨j,hj,l,hl,π,ρ,Or.inl rfl,Or.inl rfl,u,?_⟩
    rw [hu, hj', hl', hπ, hρ]
    ac_rfl
  · refine ⟨j,hj,l,hl,π,star ρ,Or.inl rfl,Or.inr rfl,u,?_⟩
    rw [hu, hj', hl', hπ, hρ]
    ac_rfl
  · refine ⟨j,hj,l,hl,star π,ρ,Or.inr rfl,Or.inl rfl,u,?_⟩
    rw [hu, hj', hl', hπ, hρ]
    ac_rfl
  · refine ⟨j,hj,l,hl,star π,star ρ,Or.inr rfl,Or.inr rfl,u,?_⟩
    rw [hu, hj', hl', hπ, hρ]
    ac_rfl


/-- A convenient representation of odd real and even imaginary coordinates. -/
def OddEven (z : GaussianInt) : Prop :=
  ∃ x y : ℤ, z.re = 2*x+1 ∧ z.im = 2*y

theorem oddEven_mul {x y : GaussianInt} (hx : OddEven x) (hy : OddEven y) :
    OddEven (x*y) := by
  obtain ⟨a,b,ha,hb⟩ := hx
  obtain ⟨c,d,hc,hd⟩ := hy
  refine ⟨a+c+2*a*c-2*b*d, d+2*a*d+b+2*b*c, ?_, ?_⟩
  · simp only [Zsqrtd.re_mul, ha, hb, hc, hd]
    ring
  · simp only [Zsqrtd.im_mul, ha, hb, hc, hd]
    ring

@[simp] theorem oddEven_one : OddEven (1 : GaussianInt) := by
  exact ⟨0,0,by simp,by simp⟩

theorem oddEven_pow {z : GaussianInt} (h : OddEven z) (n : ℕ) : OddEven (z^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact oddEven_mul ih h

theorem oddEven_star {z : GaussianInt} (h : OddEven z) : OddEven (star z) := by
  obtain ⟨a,b,ha,hb⟩ := h
  exact ⟨a,-b,by simpa using ha,by simp [hb, mul_neg]⟩

theorem oddEven_natCast {n : ℕ} (h : n % 2 = 1) : OddEven (n : GaussianInt) := by
  have h' : (n : ℤ) % 2 = 1 := by exact_mod_cast h
  refine ⟨(n : ℤ)/2,0,?_,by simp⟩
  change (n : ℤ) = 2 * ((n : ℤ) / 2) + 1
  omega

theorem pair_norm (a b : ℕ) :
    normN (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) = a^2 + b^2 := by
  have h : (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt).norm = ((a^2+b^2 : ℕ) : ℤ) := by
    push_cast
    simp only [Zsqrtd.norm_def]
    ring
  exact congrArg Int.natAbs h

theorem split_prime_oddEven {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ z : GaussianInt, normN z = p ∧ OddEven z := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,b,hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  have hpodd : p % 2 = 1 := by omega
  have hm : (a^2+b^2)%2 = 1 := by simpa [hab] using hpodd
  rw [Nat.add_mod, Nat.pow_mod a 2 2, Nat.pow_mod b 2 2] at hm
  have ha : a%2=0 ∨ a%2=1 := by omega
  have hb : b%2=0 ∨ b%2=1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · norm_num [ha,hb] at hm
  · refine ⟨⟨(b : ℤ),(a : ℤ)⟩, ?_, ?_⟩
    · rw [pair_norm, add_comm, hab]
    · have ha' : (a : ℤ) % 2 = 0 := by exact_mod_cast ha
      have hb' : (b : ℤ) % 2 = 1 := by exact_mod_cast hb
      exact ⟨(b : ℤ)/2,(a : ℤ)/2,by change (b : ℤ) = _; omega,
        by change (a : ℤ) = _; omega⟩
  · refine ⟨⟨(a : ℤ),(b : ℤ)⟩, by rw [pair_norm, hab], ?_⟩
    have ha' : (a : ℤ) % 2 = 1 := by exact_mod_cast ha
    have hb' : (b : ℤ) % 2 = 0 := by exact_mod_cast hb
    exact ⟨(a : ℤ)/2,(b : ℤ)/2,by change (a : ℤ) = _; omega,
      by change (b : ℤ) = _; omega⟩
  · norm_num [ha,hb] at hm

/-- A unit cannot exchange the even and odd coordinates in an odd-even product. -/
theorem imag_sq_of_unit_mul {u z : GaussianInt} (hu : IsUnit u)
    (hz : OddEven z) (huz : OddEven (u*z)) : (u*z).im^2 = z.im^2 := by
  have hn : u.norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by decide) u).mpr hu
  have hsum : u.re^2 + u.im^2 = 1 := by
    simp only [Zsqrtd.norm_def] at hn
    nlinarith
  have hn1 : u.re = 0 ∨ u.im = 0 := by
    by_contra hn1
    push Not at hn1
    have hr : u.re^2 ≥ 1 := by
      rcases lt_or_gt_of_ne hn1.1 with h | h
      · have : u.re ≤ -1 := by omega
        nlinarith
      · have : 1 ≤ u.re := by omega
        nlinarith
    have hi : u.im^2 ≥ 1 := by
      rcases lt_or_gt_of_ne hn1.2 with h | h
      · have : u.im ≤ -1 := by omega
        nlinarith
      · have : 1 ≤ u.im := by omega
        nlinarith
    omega
  rcases hn1 with hu0 | hu0
  · obtain ⟨a,b,ha,hb⟩ := hz
    obtain ⟨c,d,hc,hd⟩ := huz
    simp only [Zsqrtd.re_mul, hu0, hb, zero_mul, zero_add] at hc
    have hh : (2*(u.im * b)) % 2 = 0 := by omega
    have heq : 2 * c + 1 = - 2*(u.im*b) := by nlinarith [hc]
    have := congrArg (fun x : ℤ => x % 2) heq
    omega
  · simp only [Zsqrtd.im_mul, hu0, zero_mul, add_zero]
    have hur : u.re^2 = 1 := by simpa [hu0] using hsum
    rw [mul_pow, hur, one_mul]

theorem even_leg_phase {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpodd : p%2=1) (hqodd : q%2=1)
    {π ρ z : GaussianInt} (hπ : normN π = p) (hρ : normN ρ = q)
    (hπP : OddEven π) (hρP : OddEven ρ) (hzP : OddEven z)
    (hz : normN z = (p ^ k * q) ^ 2) :
    ∃ j ≤ k, ∃ l ≤ 1, ∃ x y : GaussianInt,
      (x = π ∨ x = star π) ∧ (y = ρ ∨ y = star ρ) ∧
      z.im^2 = (((p : GaussianInt) ^ (k-j) * (q : GaussianInt) ^ (1-l) *
        (x ^ (2*j) * y ^ (2*l))).im)^2 := by
  obtain ⟨j,hj,l,hl,x,y,hx,hy,u,hu⟩ :=
    reduced_factor_representation hp hq hpq hπ hρ hz
  refine ⟨j,hj,l,hl,x,y,hx,hy,?_⟩
  have hxP : OddEven x := by
    rcases hx with rfl | rfl
    · exact hπP
    · exact oddEven_star hπP
  have hyP : OddEven y := by
    rcases hy with rfl | rfl
    · exact hρP
    · exact oddEven_star hρP
  have hprod := oddEven_mul
    (oddEven_mul (oddEven_pow (oddEven_natCast hpodd) (k-j))
      (oddEven_pow (oddEven_natCast hqodd) (1-l)))
    (oddEven_mul (oddEven_pow hxP (2*j)) (oddEven_pow hyP (2*l)))
  rw [hu] at hzP ⊢
  exact imag_sq_of_unit_mul (Units.isUnit u) hprod hzP


/-- Conjugation changes only signs in the squared even-leg equation. We use
one sign for the contribution of the second Gaussian factor. -/
theorem even_leg_signed_phase {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {π ρ z : GaussianInt} (hπ : normN π = p) (hρ : normN ρ = q)
    (hπP : OddEven π) (hρP : OddEven ρ) (hzP : OddEven z)
    (hpodd : p%2=1) (hqodd : q%2=1)
    (hz : normN z = (p ^ k * q) ^ 2) :
    ∃ j ≤ k, ∃ l ≤ 1,
      let A := (π^(2*j)).im * (ρ^(2*l)).re
      let B := (π^(2*j)).re * (ρ^(2*l)).im
      let C : ℤ := (p : ℤ)^(k-j) * (q : ℤ)^(1-l)
      z.im^2 = (C*(A+B))^2 ∨ z.im^2 = (C*(A-B))^2 := by
  obtain ⟨j,hj,l,hl,x,y,hx,hy,hxy⟩ :=
    even_leg_phase hp hq hpq hpodd hqodd hπ hρ hπP hρP hzP hz
  have hcast : (p : GaussianInt) ^ (k-j) * (q : GaussianInt) ^ (1-l) =
      (((p : ℤ) ^ (k-j) * (q : ℤ) ^ (1-l) : ℤ) : GaussianInt) := by
    simp [Int.cast_mul, Int.cast_pow]
  rw [hcast] at hxy
  refine ⟨j,hj,l,hl,?_⟩
  dsimp
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · left
    simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, zero_mul, add_zero] at hxy
    linear_combination hxy
  · right
    simp only [← star_pow,
      Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, Zsqrtd.re_star,
      Zsqrtd.im_star, zero_mul, add_zero] at hxy
    linear_combination hxy
  · right
    simp only [← star_pow,
      Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, Zsqrtd.re_star,
      Zsqrtd.im_star, zero_mul, add_zero] at hxy
    linear_combination hxy
  · left
    simp only [← star_pow,
      Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, Zsqrtd.re_star,
      Zsqrtd.im_star, zero_mul, add_zero] at hxy
    linear_combination hxy

/-- The explicit candidate list for a nonzero even leg at diagonal p²q.
All seven entries are signed integers, so the readout compares squares. -/
def candidates2 (p q : ℕ) (π ρ : GaussianInt) : List ℤ :=
  let R := (π^2).re
  let S := (π^2).im
  let T := (π^4).re
  let W := (π^4).im
  let U := (ρ^2).re
  let V := (ρ^2).im
  [(p : ℤ)*q*S, (q : ℤ)*W, (p : ℤ)^2*V,
   (p : ℤ)*(S*U+R*V), (p : ℤ)*(S*U-R*V),
   W*U+T*V, W*U-T*V]

/-- The explicit candidate list for a nonzero even leg at diagonal p³q. -/
def candidates3 (p q : ℕ) (π ρ : GaussianInt) : List ℤ :=
  let R := (π^2).re
  let S := (π^2).im
  let T := (π^4).re
  let W := (π^4).im
  let X := (π^6).re
  let Y := (π^6).im
  let U := (ρ^2).re
  let V := (ρ^2).im
  [(p : ℤ)^2*q*S, (p : ℤ)*q*W, (q : ℤ)*Y, (p : ℤ)^3*V,
   (p : ℤ)^2*(S*U+R*V), (p : ℤ)^2*(S*U-R*V),
   (p : ℤ)*(W*U+T*V), (p : ℤ)*(W*U-T*V),
   Y*U+X*V, Y*U-X*V]

theorem even_leg_mem_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {π ρ z : GaussianInt} (hπ : normN π = p) (hρ : normN ρ = q)
    (hπP : OddEven π) (hρP : OddEven ρ) (hzP : OddEven z)
    (hpodd : p%2=1) (hqodd : q%2=1)
    (hz : normN z = (p ^ 2 * q) ^ 2) (hne : z.im ≠ 0) :
    ∃ e ∈ candidates2 p q π ρ, z.im^2 = e^2 := by
  obtain ⟨j,hj,l,hl,heq⟩ :=
    even_leg_signed_phase hp hq hpq hπ hρ hπP hρP hzP hpodd hqodd hz
  interval_cases j <;> interval_cases l <;> dsimp at heq
  · rcases heq with h | h
    all_goals
      simp at h
      exact (hne h).elim
  · refine ⟨(p : ℤ)^2*(ρ^2).im, by simp [candidates2], ?_⟩
    rcases heq with h | h <;> norm_num at h <;> linear_combination h
  · refine ⟨(p : ℤ)*q*(π^2).im, by simp [candidates2], ?_⟩
    rcases heq with h | h <;> norm_num at h <;> linear_combination h
  · rcases heq with h | h
    · refine ⟨(p : ℤ)*((π^2).im*(ρ^2).re+(π^2).re*(ρ^2).im),
        by simp [candidates2], ?_⟩
      norm_num at h
      linear_combination h
    · refine ⟨(p : ℤ)*((π^2).im*(ρ^2).re-(π^2).re*(ρ^2).im),
        by simp [candidates2], ?_⟩
      norm_num at h
      linear_combination h
  · refine ⟨(q : ℤ)*(π^4).im, by simp [candidates2], ?_⟩
    rcases heq with h | h <;> norm_num at h <;> linear_combination h
  · rcases heq with h | h
    · refine ⟨(π^4).im*(ρ^2).re+(π^4).re*(ρ^2).im,
        by simp [candidates2], ?_⟩
      norm_num at h
      linear_combination h
    · refine ⟨(π^4).im*(ρ^2).re-(π^4).re*(ρ^2).im,
        by simp [candidates2], ?_⟩
      norm_num at h
      linear_combination h

theorem even_leg_mem_three {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {π ρ z : GaussianInt} (hπ : normN π = p) (hρ : normN ρ = q)
    (hπP : OddEven π) (hρP : OddEven ρ) (hzP : OddEven z)
    (hpodd : p%2=1) (hqodd : q%2=1)
    (hz : normN z = (p ^ 3 * q) ^ 2) (hne : z.im ≠ 0) :
    ∃ e ∈ candidates3 p q π ρ, z.im^2 = e^2 := by
  obtain ⟨j,hj,l,hl,heq⟩ :=
    even_leg_signed_phase hp hq hpq hπ hρ hπP hρP hzP hpodd hqodd hz
  interval_cases j <;> interval_cases l <;> dsimp at heq
  · rcases heq with h | h
    all_goals
      simp at h
      exact (hne h).elim
  · refine ⟨(p : ℤ)^3*(ρ^2).im, by simp [candidates3], ?_⟩
    rcases heq with h | h <;> norm_num at h <;> linear_combination h
  · refine ⟨(p : ℤ)^2*q*(π^2).im, by simp [candidates3], ?_⟩
    rcases heq with h | h <;> norm_num at h <;> linear_combination h
  · rcases heq with h | h
    · refine ⟨(p : ℤ)^2*((π^2).im*(ρ^2).re+(π^2).re*(ρ^2).im),
        by simp [candidates3], ?_⟩
      norm_num at h
      linear_combination h
    · refine ⟨(p : ℤ)^2*((π^2).im*(ρ^2).re-(π^2).re*(ρ^2).im),
        by simp [candidates3], ?_⟩
      norm_num at h
      linear_combination h
  · refine ⟨(p : ℤ)*q*(π^4).im, by simp [candidates3], ?_⟩
    rcases heq with h | h <;> norm_num at h <;> linear_combination h
  · rcases heq with h | h
    · refine ⟨(p : ℤ)*((π^4).im*(ρ^2).re+(π^4).re*(ρ^2).im),
        by simp [candidates3], ?_⟩
      norm_num at h
      linear_combination h
    · refine ⟨(p : ℤ)*((π^4).im*(ρ^2).re-(π^4).re*(ρ^2).im),
        by simp [candidates3], ?_⟩
      norm_num at h
      linear_combination h
  · refine ⟨(q : ℤ)*(π^6).im, by simp [candidates3], ?_⟩
    rcases heq with h | h <;> norm_num at h <;> linear_combination h
  · rcases heq with h | h
    · refine ⟨(π^6).im*(ρ^2).re+(π^6).re*(ρ^2).im,
        by simp [candidates3], ?_⟩
      norm_num at h
      linear_combination h
    · refine ⟨(π^6).im*(ρ^2).re-(π^6).re*(ρ^2).im,
        by simp [candidates3], ?_⟩
      norm_num at h
      linear_combination h

end PerfectCuboid.GaussianRepr

