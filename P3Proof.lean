import CuboidCandidates
import P3PairBridge
import P3MixedBridge

namespace CuboidFormal

open FormalCuboid.P3 PerfectCuboid.P3Data

theorem forbidden_primitive_p3q : ForbiddenPrimitiveDiagonal 3 := by
  intro p q C hp hq hpq hC hg
  obtain ⟨E, π, ρ, hp4, hq4, hπ, hρ, oπ, oρ⟩ := C.split_diagonal hC hp hq (by decide) hg
  let d := mkData hp hq hp4 hq4 hπ hρ oπ oρ
  let mixed : MixedData d := {
    p := p, q := q, hp := hp, hq := hq, distinct := hpq, π := π, ρ := ρ
    normπ := hπ, normρ := hρ, eq_p := rfl, eq_q := rfl
    realπ := rfl, imagπ := rfl, realρ := rfl, imagρ := rfl }
  let pair : PairFacts d := mkPairFacts hp hq hp4 hq4 hπ hρ oπ oρ
  have bridge : Bridge d := {
    lowerA_mod_q := mixed_lowerA_mod_q mixed
    bottom_mixed_bounds := mixed_bottom_mixed_bounds mixed
    middle_a₃_leg := mixed_middle_a₃_leg mixed
    middle_a₃_hyp := mixed_middle_a₃_hyp mixed
    lower_a_difference := pair_lower_a_difference d pair
    lower_a_sum := pair_lower_a_sum d pair
    top_a_difference := pair_top_a_difference d pair
    c_difference := pair_c_difference d pair
    norm_top := top_norm d
    Y_ne_zero := pair.Y_ne }
  exact evenLegs_three_excluded hp hq hpq hp4 hq4 hπ hρ oπ oρ bridge E

end CuboidFormal
