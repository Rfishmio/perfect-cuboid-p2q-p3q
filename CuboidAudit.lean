import CuboidTheorems

open CuboidFormal

#check (forbidden_p2q : ∀ (p q : ℕ) (C : Cuboid),
  p.Prime → q.Prime → p ≠ q → C.g ≠ (p : ℤ) ^ 2 * (q : ℤ))

#check (forbidden_p3q : ∀ (p q : ℕ) (C : Cuboid),
  p.Prime → q.Prime → p ≠ q → C.g ≠ (p : ℤ) ^ 3 * (q : ℤ))

#print axioms forbidden_p2q
#print axioms forbidden_p3q
