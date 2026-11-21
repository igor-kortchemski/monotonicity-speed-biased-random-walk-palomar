module

public import LPPMonotonicityProof.Speed.Escape.Positive
public import LPPMonotonicityProof.Speed.Ergodic.Moves

/-!
# The first three steps of the ergodicity proof

This module gathers three steps of the proof that the environment seen by the walk is
ergodic: some degree at least two has positive mass
(`LPPMonotonicityProof.Speed.exists_degree_ge_two`); an invariant event depends only
on the initial environment (`Ergodic.Initial`); and its future probability is
invariant across every neighbour (`Ergodic.Moves`).
-/
