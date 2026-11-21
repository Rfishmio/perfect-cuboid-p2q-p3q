import LowerDiagonal
import P2Proof
import P3Proof

namespace CuboidFormal

/-- A perfect cuboid cannot have body diagonal p²q for distinct primes p and q. -/
theorem forbidden_p2q : ForbiddenDiagonal 2 := by
  apply forbidden_of_primitive_reductions 2
    forbidden_primitive_prime_power forbidden_primitive_prime_product
  intro i hmin hmax
  have hi : i = 2 := by omega
  subst i
  exact forbidden_primitive_p2q

/-- A perfect cuboid cannot have body diagonal p³q for distinct primes p and q. -/
theorem forbidden_p3q : ForbiddenDiagonal 3 := by
  apply forbidden_of_primitive_reductions 3
    forbidden_primitive_prime_power forbidden_primitive_prime_product
  intro i hmin hmax
  by_cases hi : i = 2
  · subst i
    exact forbidden_primitive_p2q
  · have hi' : i = 3 := by omega
    subst i
    exact forbidden_primitive_p3q

end CuboidFormal
