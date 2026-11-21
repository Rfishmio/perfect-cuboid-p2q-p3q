import PrimitiveReduction
import GaussianRepr

namespace CuboidFormal

open PerfectCuboid.GaussianRepr

theorem gaussian_norm_eq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  simp only [Zsqrtd.norm_def, neg_mul, one_mul, sub_neg_eq_add, pow_two]

theorem norm_eq_natCast {z : GaussianInt} {n : ℕ} (h : normN z = n) :
    z.norm = (n : ℤ) := by
  rw [← h]
  exact (Int.natAbs_of_nonneg (GaussianInt.norm_nonneg z)).symm

theorem gaussian_oddEven {g e o : ℤ} (hg : g % 2 = 1) (he : e % 2 = 0)
    (hn : e ^ 2 + o ^ 2 = g ^ 2) : OddEven (⟨o, e⟩ : GaussianInt) := by
  have ho := square_mod_four g
  rw [← hn, Int.add_emod, square_mod_four e, square_mod_four o, hg, he] at ho
  have hodd : o % 2 = 1 := by omega
  exact ⟨o / 2, e / 2, by change o = _; omega, by change e = _; omega⟩

theorem gaussian_normN {g e o : ℤ} {n : ℕ} (hg : g = (n : ℤ))
    (hn : e ^ 2 + o ^ 2 = g ^ 2) : normN (⟨o, e⟩ : GaussianInt) = n ^ 2 := by
  have hnorm : (⟨o, e⟩ : GaussianInt).norm = (n : ℤ) ^ 2 := by
    rw [gaussian_norm_eq, ← hg, ← hn]
    exact add_comm _ _
  simpa [normN, pow_two, Int.natAbs_mul] using congrArg Int.natAbs hnorm

theorem EvenLegs.prime_mod_four_of_dvd {g : ℤ} {p : ℕ} (E : EvenLegs g)
    (hp : p.Prime) (hd : (p : ℤ) ∣ g) : p % 4 = 1 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hz : g % 2 = 0 := Int.emod_eq_zero_of_dvd hd
    have := E.g_odd
    omega
  have hodd := hp.eq_two_or_odd.resolve_left hp2
  by_contra h1
  have h3 : p % 4 = 3 := by omega
  have hcoord {e o : ℤ} (hn : e ^ 2 + o ^ 2 = g ^ 2) :
      (p : ℤ) ∣ o ∧ (p : ℤ) ∣ e := by
    have hnorm : (⟨o, e⟩ : GaussianInt).norm = g ^ 2 := by
      rw [gaussian_norm_eq, ← hn]
      exact add_comm _ _
    apply inert_prime_dvd_components (z := ⟨o, e⟩) hp h3
    rw [hnorm]
    exact dvd_trans hd (dvd_pow_self _ (by decide))
  exact E.primitive (p : ℤ) (by exact_mod_cast hp.one_lt)
    (hcoord E.norm_x).2 (hcoord E.norm_y).2 (hcoord E.norm_z).1

theorem eq_of_pos_of_sq_eq {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  have hh : (a - b) * (a + b) = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (ne_of_gt (add_pos ha hb)))

theorem dvd_iff_of_sq_eq {d a b : ℤ} (h : a ^ 2 = b ^ 2) : d ∣ a ↔ d ∣ b := by
  rw [← Int.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0), h,
    Int.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)]

/-- Choosing labels for the three even legs preserves distinctness and their square relation. -/
theorem EvenLegs.choose_labels {g : ℤ} (E : EvenLegs g) {L : Type*} (f : L → ℤ)
    (h : ∀ (e o : ℤ), 0 < e → e % 2 = 0 → e ^ 2 + o ^ 2 = g ^ 2 →
      ∃ l : L, e ^ 2 = (f l) ^ 2) :
    ∃ i j k : L, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      E.x ^ 2 = (f i) ^ 2 ∧ E.y ^ 2 = (f j) ^ 2 ∧ E.z ^ 2 = (f k) ^ 2 := by
  obtain ⟨i, hi⟩ := h E.x E.ox E.x_pos E.x_even E.norm_x
  obtain ⟨j, hj⟩ := h E.y E.oy E.y_pos E.y_even E.norm_y
  obtain ⟨k, hk⟩ := h E.z E.oz E.z_pos E.z_even E.norm_z
  refine ⟨i, j, k, ?_, ?_, ?_, hi, hj, hk⟩
  · rintro rfl
    exact E.xy_ne (eq_of_pos_of_sq_eq E.x_pos E.y_pos (hi.trans hj.symm))
  · rintro rfl
    exact (ne_of_lt E.x_lt_z) (eq_of_pos_of_sq_eq E.x_pos E.z_pos (hi.trans hk.symm))
  · rintro rfl
    exact (ne_of_lt E.y_lt_z) (eq_of_pos_of_sq_eq E.y_pos E.z_pos (hj.trans hk.symm))

theorem EvenLegs.two_unit_labels {g d : ℤ} (E : EvenLegs g) (hd : 1 < d) (hdiv : d ∣ g)
    {L : Type*} {f : L → ℤ} {i j k : L} {top : L → Prop}
    (hi : E.x ^ 2 = (f i) ^ 2) (hj : E.y ^ 2 = (f j) ^ 2) (hk : E.z ^ 2 = (f k) ^ 2)
    (htop : ∀ i : L, ¬top i → d ∣ f i) :
    (top i ∧ top j) ∨ (top i ∧ top k) ∨ (top j ∧ top k) := by
  classical
  have unit_top {l : L} (hn : ¬d ∣ f l) : top l := by
    by_contra hl
    exact hn (htop l hl)
  rcases E.two_not_dvd_of_dvd_diagonal hd hdiv with ⟨hx, hy⟩ | ⟨hx, hz⟩ | ⟨hy, hz⟩
  · exact Or.inl ⟨unit_top (hx ∘ (dvd_iff_of_sq_eq hi).mpr),
      unit_top (hy ∘ (dvd_iff_of_sq_eq hj).mpr)⟩
  · exact Or.inr (Or.inl ⟨unit_top (hx ∘ (dvd_iff_of_sq_eq hi).mpr),
      unit_top (hz ∘ (dvd_iff_of_sq_eq hk).mpr)⟩)
  · exact Or.inr (Or.inr ⟨unit_top (hy ∘ (dvd_iff_of_sq_eq hj).mpr),
      unit_top (hz ∘ (dvd_iff_of_sq_eq hk).mpr)⟩)

end CuboidFormal
