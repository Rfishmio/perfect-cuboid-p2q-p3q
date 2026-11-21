import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PerfectCuboid

private theorem zmod2_odd {x : ℤ} (hx : Odd x) : (x : ZMod 2) = 1 := by
  obtain ⟨k, hk⟩ := hx
  rw [hk]
  push_cast <;> simp [show (2 : ZMod 2) = 0 by decide]

private theorem zmod2_even {x : ℤ} (hx : x % 2 = 0) : (x : ZMod 2) = 0 := by
  have h : x = 2 * (x / 2) := by omega
  rw [h]
  push_cast <;> simp [show (2 : ZMod 2) = 0 by decide]

private theorem zmod4_odd_sq {x : ℤ} (hx : Odd x) : (x : ZMod 4) ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hx
  rw [hk]
  push_cast
  calc
    (2 * (k : ZMod 4) + 1) ^ 2 =
        (4 : ZMod 4) * ((k : ZMod 4) ^ 2 + (k : ZMod 4)) + 1 := by ring
    _ = 1 := by simp [show (4 : ZMod 4) = 0 by decide]

private theorem zmod4_even_sq {x : ℤ} (hx : x % 2 = 0) :
    (x : ZMod 4) ^ 2 = 0 := by
  have h : x = 2 * (x / 2) := by omega
  rw [h]
  push_cast
  calc
    (2 * ((x / 2 : ℤ) : ZMod 4)) ^ 2 =
        (4 : ZMod 4) * ((x / 2 : ℤ) : ZMod 4) ^ 2 := by ring
    _ = 0 := by simp [show (4 : ZMod 4) = 0 by decide]

private theorem zmod4_twice_odd {x : ℤ} (hx : Odd x) :
    (2 : ZMod 4) * (x : ZMod 4) = 2 := by
  obtain ⟨k, hk⟩ := hx
  rw [hk]
  push_cast
  calc
    2 * (2 * (k : ZMod 4) + 1) = (4 : ZMod 4) * (k : ZMod 4) + 2 := by ring
    _ = 2 := by simp [show (4 : ZMod 4) = 0 by decide]

private theorem zmod4_sq_ne_two (x : ZMod 4) : x ^ 2 ≠ 2 := by
  fin_cases x <;> decide

private theorem homogeneous_descent
    (P : ℤ → ℤ → Prop)
    (step : ∀ s v : ℤ, P s v →
      ∃ a b : ℤ, s = 2 * a ∧ v = 2 * b ∧ P a b)
    {s v : ℤ} (hs : s ≠ 0) : ¬ P s v := by
  have bounded : ∀ n : ℕ, ∀ s v : ℤ, s.natAbs ≤ n → s ≠ 0 → ¬ P s v := by
    intro n
    induction n with
    | zero =>
        intro u w hu hne _
        have hz : u.natAbs = 0 := by omega
        exact hne (Int.natAbs_eq_zero.mp hz)
    | succ n ih =>
        intro u w hu hne hw
        obtain ⟨a, b, ha, _, hab⟩ := step u w hw
        have hane : a ≠ 0 := by
          intro hzero
          apply hne
          simp [ha, hzero]
        have hapos : 0 < a.natAbs :=
          Nat.pos_of_ne_zero (fun hzero => hane (Int.natAbs_eq_zero.mp hzero))
        have hm : u.natAbs = 2 * a.natAbs := by
          rw [ha, Int.natAbs_mul]
          rfl
        exact ih a b (by omega) hane hab
  exact bounded s.natAbs s v (Nat.le_refl _) hs

/-- A homogeneous square relation that excludes the difference of the two highest
Gaussian-leg squares against a middle-layer square. Signs are included in b and d. -/
theorem p3_middle_difference
    (p a b d s v : ℤ) (hp : Odd p) (ha : Odd a) (hb : Odd b)
    (hd : Odd d) (hs : s ≠ 0) :
    (p * (2 * a * s + b * v)) ^ 2 ≠ 4 * d * s * v := by
  refine homogeneous_descent
    (fun u w => (p * (2 * a * u + b * w)) ^ 2 = 4 * d * u * w) (s := s) (v := v) ?_ hs
  intro u w eqn
  have hw : w % 2 = 0 := by
    by_contra hn
    have hodd : Odd w := ⟨w / 2, by omega⟩
    have h := congrArg (fun z : ℤ => (z : ZMod 2)) eqn
    push_cast at h
    simp [zmod2_odd hp, zmod2_odd hb, zmod2_odd hodd,
      show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide] at h
  let w' : ℤ := w / 2
  have hwe : w = 2 * w' := by
    dsimp [w']
    omega
  have halved : (p * (a * u + b * w')) ^ 2 = 2 * d * u * w' := by
    have hz : (4 : ℤ) * ((p * (a * u + b * w')) ^ 2 - 2 * d * u * w') = 0 := by
      calc
        _ = (p * (2 * a * u + b * (2 * w'))) ^ 2 - 4 * d * u * (2 * w') := by
          ring
        _ = 0 := by
          rw [← hwe, eqn, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  have hu : u % 2 = 0 := by
    by_contra hn
    have huo : Odd u := ⟨u / 2, by omega⟩
    by_cases ht : w' % 2 = 0
    · have h := congrArg (fun z : ℤ => (z : ZMod 2)) halved
      push_cast at h
      simp [zmod2_odd hp, zmod2_odd ha, zmod2_odd huo, zmod2_even ht,
        show (2 : ZMod 2) = 0 by decide] at h
    · have hto : Odd w' := ⟨w' / 2, by omega⟩
      have hh : Odd (d * u * w') := (hd.mul huo).mul hto
      have h := congrArg (fun z : ℤ => (z : ZMod 4)) halved
      have immediate : ((p * (a * u + b * w') : ℤ) : ZMod 4) ^ 2 = 2 := by
        calc
          ((p * (a * u + b * w') : ℤ) : ZMod 4) ^ 2 =
              (((p * (a * u + b * w')) ^ 2 : ℤ) : ZMod 4) := by push_cast <;> rfl
          _ = ((2 * d * u * w' : ℤ) : ZMod 4) := h
          _ = (2 : ZMod 4) * ((d * u * w' : ℤ) : ZMod 4) := by push_cast <;> ring
          _ = 2 := zmod4_twice_odd hh
      exact zmod4_sq_ne_two _ immediate
  let u' : ℤ := u / 2
  have hue : u = 2 * u' := by
    dsimp [u']
    omega
  refine ⟨u', w', hue, hwe, ?_⟩
  have hz : (4 : ℤ) *
      ((p * (2 * a * u' + b * w')) ^ 2 - 4 * d * u' * w') = 0 := by
    calc
      _ = (p * (2 * a * (2 * u') + b * (2 * w'))) ^ 2
          - 4 * d * (2 * u') * (2 * w') := by ring
      _ = 0 := by rw [← hue, ← hwe, eqn, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by norm_num))

/-- The corresponding sum of the two highest Gaussian-leg squares cannot be a
middle-layer square. The signs are included in b, and signs of d,e are irrelevant. -/
theorem p3_middle_sum
    (p a b d e s v : ℤ)
    (hp : Odd p) (hb : Odd b) (hd : Odd d) (hs : s ≠ 0) :
    (p * (2 * a * s + b * v)) ^ 2 ≠ 2 * ((d * s) ^ 2 + (e * v) ^ 2) := by
  apply homogeneous_descent
    (fun u w => (p * (2 * a * u + b * w)) ^ 2
      = 2 * ((d * u) ^ 2 + (e * w) ^ 2)) (s := s) (v := v) ?_ hs
  intro u w eqn
  have hw : w % 2 = 0 := by
    by_contra hn
    have hodd : Odd w := ⟨w / 2, by omega⟩
    have h := congrArg (fun z : ℤ => (z : ZMod 2)) eqn
    push_cast at h
    simp [zmod2_odd hp, zmod2_odd hb, zmod2_odd hodd,
      show (2 : ZMod 2) = 0 by decide] at h
  let w' : ℤ := w / 2
  have hwe : w = 2 * w' := by
    dsimp [w']
    omega
  have hu : u % 2 = 0 := by
    by_contra hn
    have huo : Odd u := ⟨u / 2, by omega⟩
    have hleft : (p * (2 * a * u + b * w)) % 2 = 0 := by
      rw [hwe]
      have he : p * (2 * a * u + b * (2 * w')) = 2 * (p * (a * u + b * w')) := by ring
      rw [he]
      omega
    have hright : (e * w) % 2 = 0 := by
      rw [hwe]
      have he : e * (2 * w') = 2 * (e * w') := by ring
      rw [he]
      omega
    have hz := congrArg (fun z : ℤ => (z : ZMod 4)) eqn
    have hc : ((p * (2 * a * u + b * w) : ℤ) : ZMod 4) ^ 2 =
        (2 : ZMod 4) * (((d * u : ℤ) : ZMod 4) ^ 2 + ((e * w : ℤ) : ZMod 4) ^ 2) := by
      push_cast at hz ⊢
      exact hz
    rw [zmod4_even_sq hleft, zmod4_even_sq hright, zmod4_odd_sq (hd.mul huo)] at hc
    exact (by decide : (0 : ZMod 4) ≠ 2) (by simpa using hc)
  let u' : ℤ := u / 2
  have hue : u = 2 * u' := by
    dsimp [u']
    omega
  refine ⟨u', w', hue, hwe, ?_⟩
  have hz : (4 : ℤ) *
      ((p * (2 * a * u' + b * w')) ^ 2 - 2 * ((d * u') ^ 2 + (e * w') ^ 2)) = 0 := by
    calc
      _ = (p * (2 * a * (2 * u') + b * (2 * w'))) ^ 2
          - 2 * ((d * (2 * u')) ^ 2 + (e * (2 * w')) ^ 2) := by ring
      _ = 0 := by rw [← hue, ← hwe, eqn, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by norm_num))


/-- The two top signed Gaussian legs and a B₂ signed leg do not form a right triangle.
This statement includes either B₂ sign and every choice of the hypotenuse. -/
theorem p3_b2_top_pair_excluded
    (p R S T X U V σ : ℤ)
    (hp : Odd p) (hR : Odd R) (hS : S % 2 = 0) (hS0 : S ≠ 0)
    (hT : Odd T) (hX : Odd X) (hU : Odd U) (hσ : σ = 1 ∨ σ = -1) :
    let W := 2 * R * S
    let Y := S * (3 * R ^ 2 - S ^ 2)
    let F := Y * U + X * V
    let G := Y * U - X * V
    let L := p * (W * U + σ * T * V)
    ¬ (F ^ 2 = G ^ 2 + L ^ 2 ∨ G ^ 2 = F ^ 2 + L ^ 2 ∨ L ^ 2 = F ^ 2 + G ^ 2) := by
  dsimp
  have hσo : Odd σ := by
    rcases hσ with rfl | rfl
    · exact ⟨0, by norm_num⟩
    · exact ⟨-1, by norm_num⟩
  have hY0 : Odd (3 * R ^ 2 - S ^ 2) := by
    obtain ⟨r, hr⟩ := hR
    have hse : S = 2 * (S / 2) := by omega
    refine ⟨6 * r ^ 2 + 6 * r + 1 - 2 * (S / 2) ^ 2, ?_⟩
    calc
      3 * R ^ 2 - S ^ 2 = 3 * (2 * r + 1) ^ 2 - (2 * (S / 2)) ^ 2 := by
        rw [hr, ← hse]
      _ = 2 * (6 * r ^ 2 + 6 * r + 1 - 2 * (S / 2) ^ 2) + 1 := by ring
  have hCoeff : Odd (X * (3 * R ^ 2 - S ^ 2) * U) := (hX.mul hY0).mul hU
  intro h
  rcases h with h | h | h
  · apply p3_middle_difference p (R * U) (σ * T) (X * (3 * R ^ 2 - S ^ 2) * U)
      S V hp (hR.mul hU) (hσo.mul hT) hCoeff hS0
    linear_combination -h
  · apply p3_middle_difference p (R * U) (σ * T) (-(X * (3 * R ^ 2 - S ^ 2) * U))
      S V hp (hR.mul hU) (hσo.mul hT) hCoeff.neg hS0
    linear_combination -h
  · apply p3_middle_sum p (R * U) (σ * T) ((3 * R ^ 2 - S ^ 2) * U) X S V
      hp (hσo.mul hT) (hY0.mul hU) hS0
    linear_combination h

end PerfectCuboid

