# Room-by-room push-optimal Sokoban solver

`main.ts` (Node 22, no dependencies) answers a set of Sokoban instances:
it reads `/input/<id>/level.txt` and writes `/output/<id>/solution.txt`
with the player's moves in LURD.

The score pays full points only for a push-optimal solution (one push over
the optimum loses more than half an instance), so the solver searches in
pushes, not moves:

- The level is split into its independent rooms by cutting the hallway row
  (every hallway square is a dead square: a box there reaches no goal).
- Each room is solved with a breadth-first search over pushes, which is
  push-optimal by construction. A state is the sorted box squares plus the
  player's reachable region, named by its lowest square.
- Deadlock pruning: pushes onto dead squares (computed by pulling boxes
  backwards from the goals) and pushes that complete a frozen 2x2 block of
  walls and boxes with a box off its goal are never made. Neither prune can
  remove a solvable state.
- The search is bounded by a fixed state count — work, never the clock —
  so two runs write byte-identical answers.

The rooms' push optima add up to the level's optimum, because a box pushed
out of a room into the hallway can never be pushed back.

License: MIT (see `LICENSE`, SPDX-License-Identifier: MIT).
