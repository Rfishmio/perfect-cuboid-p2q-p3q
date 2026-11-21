import CuboidCandidates
import P2Data

namespace CuboidFormal

open PerfectCuboid.GaussianRepr PerfectCuboid.P2Data _root_.Cuboid.P2

theorem evenLegs_two_label {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) {π ρ : GaussianInt}
    (hπ : normN π = p) (hρ : normN ρ = q) (oπ : OddEven π) (oρ : OddEven ρ)
    (E : EvenLegs ((p : ℤ) ^ 2 * (q : ℤ))) (e o : ℤ) (he : 0 < e) (hev : e % 2 = 0)
    (hn : e ^ 2 + o ^ 2 = ((p : ℤ) ^ 2 * (q : ℤ)) ^ 2) :
    ∃ i, e ^ 2 = (leg (mkData hp hq hpq hp4 hq4 hπ hρ oπ oρ) i) ^ 2 := by
  let z : GaussianInt := ⟨o, e⟩
  have hnorm : normN z = (p ^ 2 * q) ^ 2 :=
    gaussian_normN (by simp : (p : ℤ) ^ 2 * (q : ℤ) = ((p ^ 2 * q : ℕ) : ℤ)) hn
  obtain ⟨v, hmem, hv⟩ := even_leg_mem_two hp hq hpq hπ hρ oπ oρ
    (gaussian_oddEven E.g_odd hev hn) (by omega) (by omega) hnorm (ne_of_gt he)
  change e ^ 2 = v ^ 2 at hv
  simp only [candidates2, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, hv⟩
  · exact ⟨1, hv⟩
  · exact ⟨2, hv⟩
  · exact ⟨3, hv⟩
  · exact ⟨4, hv⟩
  · exact ⟨5, hv⟩
  · exact ⟨6, hv⟩

theorem evenLegs_two_excluded {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) {π ρ : GaussianInt}
    (hπ : normN π = p) (hρ : normN ρ = q) (oπ : OddEven π) (oρ : OddEven ρ)
    (facts : PhaseFacts (mkData hp hq hpq hp4 hq4 hπ hρ oπ oρ))
    (E : EvenLegs ((p : ℤ) ^ 2 * (q : ℤ))) : False := by
  let d := mkData hp hq hpq hp4 hq4 hπ hρ oπ oρ
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := E.choose_labels (leg d)
    (evenLegs_two_label hp hq hpq hp4 hq4 hπ hρ oπ oρ E)
  have hprim : ¬ (d.p ∣ leg d i ∧ d.p ∣ leg d j ∧ d.p ∣ leg d k) := by
    rintro ⟨di, dj, _⟩
    have dx : (p : ℤ) ∣ E.x := (dvd_iff_of_sq_eq hi).mpr di
    have dy : (p : ℤ) ∣ E.y := (dvd_iff_of_sq_eq hj).mpr dj
    rcases E.two_not_dvd_of_dvd_diagonal (by exact_mod_cast hp.one_lt)
      (prime_dvd_diag_power_mul p q 2 (by decide)) with h | h | h
    · exact h.1 dx
    · exact h.1 dx
    · exact h.1 dy
  have hsum := E.sum_sq
  rw [hi, hj, hk] at hsum
  exact seven_state_elimination d facts hij hjk hik hprim (Or.inl hsum)

end CuboidFormal
