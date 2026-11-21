import CuboidP2Candidates
import P2Phase

namespace CuboidFormal

theorem forbidden_primitive_p2q : ForbiddenPrimitiveDiagonal 2 := by
  intro p q C hp hq hpq hC hg
  obtain ⟨E, π, ρ, hp4, hq4, hπ, hρ, oπ, oρ⟩ := C.split_diagonal hC hp hq (by decide) hg
  exact evenLegs_two_excluded hp hq hpq hp4 hq4 hπ hρ oπ oρ
    (PerfectCuboid.P2Phase.mkPhaseFacts hp hq hpq hp4 hq4 hπ hρ oπ oρ) E

end CuboidFormal
