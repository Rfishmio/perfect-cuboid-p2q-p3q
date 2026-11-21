import P3Data

namespace CuboidFormal

open PerfectCuboid.GaussianRepr

theorem prime_dvd_diag_power_mul (p q k : ℕ) (hk : k ≠ 0) :
    (p : ℤ) ∣ (p : ℤ) ^ k * (q : ℤ) :=
  dvd_mul_of_dvd_left (dvd_pow_self _ hk) _

theorem Cuboid.split_diagonal {p q k : ℕ} (C : Cuboid) (hC : C.Primitive)
    (hp : p.Prime) (hq : q.Prime) (hk : k ≠ 0) (hg : C.g = (p : ℤ) ^ k * (q : ℤ)) :
    ∃ (_ : EvenLegs ((p : ℤ) ^ k * (q : ℤ))) (π ρ : GaussianInt),
      p % 4 = 1 ∧ q % 4 = 1 ∧ normN π = p ∧ normN ρ = q ∧ OddEven π ∧ OddEven ρ := by
  obtain ⟨E⟩ := C.evenLegs hC
  rw [hg] at E
  have hp4 := E.prime_mod_four_of_dvd hp (prime_dvd_diag_power_mul p q k hk)
  have hq4 := E.prime_mod_four_of_dvd hq ⟨(p : ℤ) ^ k, mul_comm _ _⟩
  obtain ⟨π, hπ, oπ⟩ := split_prime_oddEven hp hp4
  obtain ⟨ρ, hρ, oρ⟩ := split_prime_oddEven hq hq4
  exact ⟨E, π, ρ, hp4, hq4, hπ, hρ, oπ, oρ⟩

section P3

open FormalCuboid.P3 PerfectCuboid.P3Data

theorem evenLegs_three_label {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) {π ρ : GaussianInt}
    (hπ : normN π = p) (hρ : normN ρ = q) (oπ : OddEven π) (oρ : OddEven ρ)
    (E : EvenLegs ((p : ℤ) ^ 3 * (q : ℤ))) (e o : ℤ) (he : 0 < e) (hev : e % 2 = 0)
    (hn : e ^ 2 + o ^ 2 = ((p : ℤ) ^ 3 * (q : ℤ)) ^ 2) :
    ∃ i, e ^ 2 = ((mkData hp hq hp4 hq4 hπ hρ oπ oρ).value i) ^ 2 := by
  let z : GaussianInt := ⟨o, e⟩
  have hnorm : normN z = (p ^ 3 * q) ^ 2 :=
    gaussian_normN (by simp : (p : ℤ) ^ 3 * (q : ℤ) = ((p ^ 3 * q : ℕ) : ℤ)) hn
  obtain ⟨v, hmem, hv⟩ := even_leg_mem_three hp hq hpq hπ hρ oπ oρ
    (gaussian_oddEven E.g_odd hev hn) (by omega) (by omega) hnorm (ne_of_gt he)
  change e ^ 2 = v ^ 2 at hv
  simp only [candidates3, fourth_re, fourth_im, sixth_re, sixth_im, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.a1, hv⟩
  · exact ⟨.a2, hv⟩
  · exact ⟨.a3, hv⟩
  · exact ⟨.c, hv⟩
  · exact ⟨.b1p, by simpa only [Data.value, Data.b₁, mkData, one_mul] using hv⟩
  · exact ⟨.b1m, by simpa only [Data.value, Data.b₁, mkData, neg_one_mul, neg_mul, one_mul,
      sub_eq_add_neg] using hv⟩
  · exact ⟨.b2p, by simpa only [Data.value, Data.b₂, mkData, one_mul] using hv⟩
  · exact ⟨.b2m, by simpa only [Data.value, Data.b₂, Data.W, Data.T, mkData, neg_one_mul, neg_mul, one_mul,
      sub_eq_add_neg] using hv⟩
  · exact ⟨.b3p, by simpa only [Data.value, Data.b₃, mkData, one_mul] using hv⟩
  · exact ⟨.b3m, by simpa only [Data.value, Data.b₃, Data.X, Data.Y, mkData, neg_one_mul, neg_mul, one_mul,
      sub_eq_add_neg] using hv⟩

theorem evenLegs_three_excluded {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) {π ρ : GaussianInt}
    (hπ : normN π = p) (hρ : normN ρ = q) (oπ : OddEven π) (oρ : OddEven ρ)
    (bridge : Bridge (mkData hp hq hp4 hq4 hπ hρ oπ oρ))
    (E : EvenLegs ((p : ℤ) ^ 3 * (q : ℤ))) : False := by
  let d := mkData hp hq hp4 hq4 hπ hρ oπ oρ
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := E.choose_labels d.value
    (evenLegs_three_label hp hq hpq hp4 hq4 hπ hρ oπ oρ E)
  have htop := E.two_unit_labels (by exact_mod_cast hp.one_lt)
    (prime_dvd_diag_power_mul p q 3 (by decide)) hi hj hk (nonTop_dvd d)
  have hsum := E.sum_sq.symm
  rw [hi, hj, hk] at hsum
  exact no_qualified_triangle d bridge hij hik hjk htop (Or.inr (Or.inr hsum))

end P3

end CuboidFormal
