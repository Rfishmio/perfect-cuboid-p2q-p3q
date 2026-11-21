import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
The problem is stated directly in terms of the seven integral lengths.
There is no bound on the edges or primes.
-/

namespace CuboidFormal

structure Cuboid where
  a : ℤ
  b : ℤ
  c : ℤ
  ab : ℤ
  ac : ℤ
  bc : ℤ
  g : ℤ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  ab_pos : 0 < ab
  ac_pos : 0 < ac
  bc_pos : 0 < bc
  g_pos : 0 < g
  ab_sq : ab ^ 2 = a ^ 2 + b ^ 2
  ac_sq : ac ^ 2 = a ^ 2 + c ^ 2
  bc_sq : bc ^ 2 = b ^ 2 + c ^ 2
  g_sq : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2

def Cuboid.Primitive (C : Cuboid) : Prop :=
  ∀ d : ℤ, 1 < d → d ∣ C.a → d ∣ C.b → d ∣ C.c → False

def ForbiddenDiagonal (k : ℕ) : Prop :=
  ∀ (p q : ℕ) (C : Cuboid),
    p.Prime → q.Prime → p ≠ q → C.g ≠ (p : ℤ) ^ k * (q : ℤ)

def ForbiddenPrimitiveDiagonal (k : ℕ) : Prop :=
  ∀ (p q : ℕ) (C : Cuboid),
    p.Prime → q.Prime → p ≠ q → C.Primitive →
    C.g ≠ (p : ℤ) ^ k * (q : ℤ)

theorem square_mod_four (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  let r := x % 2
  let u := x / 2
  have hx : x = 2 * u + r := by dsimp [r, u]; omega
  have h : x ^ 2 = r ^ 2 + 4 * (u ^ 2 + r * u) := by
    calc
      x ^ 2 = (2 * u + r) ^ 2 := congrArg (fun y : ℤ => y ^ 2) hx
      _ = _ := by ring
  change x ^ 2 % 4 = r
  have hr : r = 0 ∨ r = 1 := by dsimp [r]; omega
  rcases hr with hr | hr
  · rw [hr] at h ⊢
    norm_num at h
    omega
  · rw [hr] at h ⊢
    norm_num at h
    omega

theorem square_mod_three (x : ℤ) : x ^ 2 % 3 = 0 ∨ x ^ 2 % 3 = 1 := by
  let r := x % 3
  let u := x / 3
  have hx : x = 3 * u + r := by dsimp [r, u]; omega
  have h : x ^ 2 = r ^ 2 + 3 * (3 * u ^ 2 + 2 * r * u) := by
    calc
      x ^ 2 = (3 * u + r) ^ 2 := congrArg (fun y : ℤ => y ^ 2) hx
      _ = _ := by ring
  have hr : r = 0 ∨ r = 1 ∨ r = 2 := by dsimp [r]; omega
  rcases hr with hr | hr | hr
  · rw [hr] at h
    norm_num at h
    omega
  · rw [hr] at h
    norm_num at h
    omega
  · rw [hr] at h
    norm_num at h
    omega

theorem two_odd_legs_impossible {x y z : ℤ}
    (h : z ^ 2 = x ^ 2 + y ^ 2) (hx : x % 2 = 1) (hy : y % 2 = 1) :
    False := by
  have hmx : x ^ 2 % 4 = 1 := (square_mod_four x).trans hx
  have hmy : y ^ 2 % 4 = 1 := (square_mod_four y).trans hy
  have hmz := square_mod_four z
  have hs : (x ^ 2 + y ^ 2) % 4 = 2 := by
    rw [Int.add_emod, hmx, hmy]
    norm_num
  rw [← h] at hs
  omega

theorem dvd_two_of_even {x : ℤ} (h : x % 2 = 0) : (2 : ℤ) ∣ x :=
  ⟨x / 2, by omega⟩

def Cuboid.swapAB (C : Cuboid) : Cuboid where
  a := C.b
  b := C.a
  c := C.c
  ab := C.ab
  ac := C.bc
  bc := C.ac
  g := C.g
  a_pos := C.b_pos
  b_pos := C.a_pos
  c_pos := C.c_pos
  ab_pos := C.ab_pos
  ac_pos := C.bc_pos
  bc_pos := C.ac_pos
  g_pos := C.g_pos
  ab_sq := by rw [C.ab_sq]; ring
  ac_sq := C.bc_sq
  bc_sq := C.ac_sq
  g_sq := by rw [C.g_sq]; ring

def Cuboid.swapAC (C : Cuboid) : Cuboid where
  a := C.c
  b := C.b
  c := C.a
  ab := C.bc
  ac := C.ac
  bc := C.ab
  g := C.g
  a_pos := C.c_pos
  b_pos := C.b_pos
  c_pos := C.a_pos
  ab_pos := C.bc_pos
  ac_pos := C.ac_pos
  bc_pos := C.ab_pos
  g_pos := C.g_pos
  ab_sq := by rw [C.bc_sq]; ring
  ac_sq := by rw [C.ac_sq]; ring
  bc_sq := by rw [C.ab_sq]; ring
  g_sq := by rw [C.g_sq]; ring

theorem Cuboid.orient (C : Cuboid) (hC : C.Primitive) :
    ∃ D : Cuboid, D.g = C.g ∧ D.Primitive ∧
      D.a % 2 = 1 ∧ D.b % 2 = 0 ∧ D.c % 2 = 0 := by
  by_cases ha : C.a % 2 = 1
  · have hb : C.b % 2 = 0 := by
      by_contra hn
      exact two_odd_legs_impossible C.ab_sq ha (by omega)
    have hc : C.c % 2 = 0 := by
      by_contra hn
      exact two_odd_legs_impossible C.ac_sq ha (by omega)
    exact ⟨C, rfl, hC, ha, hb, hc⟩
  · have ha0 : C.a % 2 = 0 := by omega
    by_cases hb : C.b % 2 = 1
    · have hc : C.c % 2 = 0 := by
        by_contra hn
        exact two_odd_legs_impossible C.bc_sq hb (by omega)
      refine ⟨C.swapAB, rfl, ?_, hb, ha0, hc⟩
      intro d hd hab hba hcc
      exact hC d hd hba hab hcc
    · have hb0 : C.b % 2 = 0 := by omega
      by_cases hc : C.c % 2 = 1
      · refine ⟨C.swapAC, rfl, ?_, hc, hb0, ha0⟩
        intro d hd hca hbb hac
        exact hC d hd hac hbb hca
      · have hc0 : C.c % 2 = 0 := by omega
        exact False.elim (hC 2 (by norm_num)
          (dvd_two_of_even ha0) (dvd_two_of_even hb0) (dvd_two_of_even hc0))

theorem no_equal_positive_legs {x d : ℤ} (hx : 0 < x) (_hd : 0 < d)
    (h : d ^ 2 = x ^ 2 + x ^ 2) : False := by
  have hdiv : x ∣ d := by
    apply (Int.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
    exact ⟨2, by linear_combination h⟩
  obtain ⟨k, hk⟩ := hdiv
  have hcancel : x ^ 2 * k ^ 2 = x ^ 2 * 2 := by
    rw [hk] at h
    linear_combination h
  have hk2 : k ^ 2 = 2 := mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hx)) hcancel
  have hm := square_mod_four k
  rw [hk2] at hm
  omega

structure EvenLegs (g : ℤ) where
  x : ℤ
  y : ℤ
  z : ℤ
  ox : ℤ
  oy : ℤ
  oz : ℤ
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z
  x_even : x % 2 = 0
  y_even : y % 2 = 0
  z_even : z % 2 = 0
  g_odd : g % 2 = 1
  xy_ne : x ≠ y
  sum_sq : x ^ 2 + y ^ 2 = z ^ 2
  norm_x : x ^ 2 + ox ^ 2 = g ^ 2
  norm_y : y ^ 2 + oy ^ 2 = g ^ 2
  norm_z : z ^ 2 + oz ^ 2 = g ^ 2
  primitive : ∀ d : ℤ, 1 < d → d ∣ x → d ∣ y → d ∣ oz → False

theorem EvenLegs.x_lt_z {g : ℤ} (E : EvenLegs g) : E.x < E.z := by
  by_contra! h
  have hh : (E.x - E.z) * (E.x + E.z) ≥ 0 := by
    exact mul_nonneg (sub_nonneg.mpr h) (by linarith [E.x_pos,E.z_pos])
  nlinarith [E.sum_sq, sq_pos_of_pos E.y_pos]

theorem EvenLegs.y_lt_z {g : ℤ} (E : EvenLegs g) : E.y < E.z := by
  by_contra! h
  have hh : (E.y - E.z) * (E.y + E.z) ≥ 0 := by
    exact mul_nonneg (sub_nonneg.mpr h) (by linarith [E.y_pos,E.z_pos])
  nlinarith [E.sum_sq, sq_pos_of_pos E.x_pos]

theorem Cuboid.evenLegs (C : Cuboid) (hC : C.Primitive) :
    Nonempty (EvenLegs C.g) := by
  obtain ⟨D, hg, hD, ha, hb, hc⟩ := C.orient hC
  have hbc : D.bc % 2 = 0 := by
    have h := square_mod_four D.bc
    rw [D.bc_sq, Int.add_emod, square_mod_four D.b, square_mod_four D.c, hb, hc] at h
    norm_num at h
    omega
  have hgOdd : D.g % 2 = 1 := by
    have h := square_mod_four D.g
    rw [D.g_sq, Int.add_emod, Int.add_emod (D.a ^ 2) (D.b ^ 2),
      square_mod_four D.a, square_mod_four D.b, square_mod_four D.c, ha, hb, hc] at h
    norm_num at h
    omega
  rw [← hg]
  exact ⟨{
    x := D.b
    y := D.c
    z := D.bc
    ox := D.ac
    oy := D.ab
    oz := D.a
    x_pos := D.b_pos
    y_pos := D.c_pos
    z_pos := D.bc_pos
    x_even := hb
    y_even := hc
    z_even := hbc
    g_odd := hgOdd
    xy_ne := by
      intro heq
      exact no_equal_positive_legs D.b_pos D.bc_pos (by rw [D.bc_sq, ← heq])
    sum_sq := D.bc_sq.symm
    norm_x := by rw [D.ac_sq, D.g_sq]; ring
    norm_y := by rw [D.ab_sq, D.g_sq]; ring
    norm_z := by rw [D.bc_sq, D.g_sq]; ring
    primitive := fun d hd hx hy hz => hD d hd hz hx hy
  }⟩

end CuboidFormal

