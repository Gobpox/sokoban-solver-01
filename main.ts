// SPDX-License-Identifier: MIT
// Room-by-room push-optimal Sokoban solver.
//
// Why this shape: the scoring pays 1,000 points for a solution in the push-optimal
// count P*, and only 500 * P* / pushes for anything longer — one push over optimum
// loses more than half an instance. So the search must be optimal in pushes, not
// in moves. The levels are a hallway with independent rooms off it (a box pushed
// out of a room into the hallway can never come back), so each room is solved on
// its own with a breadth-first search over pushes — BFS over pushes is push-optimal
// by construction — and the room optima add up to the level optimum.
//
// A search state is the sorted box squares plus the player's reachable region
// (named by its lowest square): two states that differ only in where the player
// stands inside one region are the same state. Two deadlock prunes keep the search
// small, and neither can prune a solvable state:
//   - a box pushed onto a dead square (one from which no push, ignoring the other
//     boxes, can bring a box to any goal) is lost, so such pushes are never made;
//   - a box that completes a frozen 2x2 block of walls and boxes, with a box of
//     the block off its goal, can never move again.
// The search is bounded by a fixed number of states (work, never the clock), so
// two runs of the program write byte-identical answers.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Direction order is fixed everywhere (u, d, l, r) so ties always break alike.
const DX = [0, 0, -1, 1];
const DY = [-1, 1, 0, 0];
const WALK = ['u', 'd', 'l', 'r'];
const PUSH = ['U', 'D', 'L', 'R'];

const ROOM_STATES = 1_000_000; // a room is guaranteed solvable far below this
const WHOLE_STATES = 600_000; // fallback for a level that is not a set of rooms

interface Level {
  w: number;
  h: number;
  wall: Uint8Array;
  goals: number[];
  boxes: number[];
  player: number;
}

function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  // The outermost frame is wall whatever the text shows: nothing leaves the board.
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  return { w, h, wall, goals, boxes: boxes.sort((a, b) => a - b), player };
}

// Squares from which a box alone can be pushed onto some goal: pull the box
// backwards from every goal over open floor (the player needs the square behind).
function liveSquares(w: number, wall: Uint8Array, goals: number[]): Uint8Array {
  const live = new Uint8Array(wall.length);
  const queue: number[] = [];
  for (const g of goals) {
    live[g] = 1;
    queue.push(g);
  }
  for (let qi = 0; qi < queue.length; qi++) {
    const x = queue[qi];
    for (let k = 0; k < 4; k++) {
      const d = DY[k] * w + DX[k];
      const y = x - d;
      if (!wall[y] && !wall[y - d] && !live[y]) {
        live[y] = 1;
        queue.push(y);
      }
    }
  }
  return live;
}

// Flood the player's reachable region from `from` around walls and boxes.
// Marks cells with `stamp` in `seen` and returns the region's lowest square.
function reach(
  w: number,
  wall: Uint8Array,
  occupied: Uint8Array,
  from: number,
  seen: Int32Array,
  stamp: number,
  stack: Int32Array,
): number {
  let low = from;
  let n = 0;
  stack[n++] = from;
  seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n];
    if (p < low) low = p;
    const up = p - w;
    const dn = p + w;
    const lf = p - 1;
    const rt = p + 1;
    if (!wall[up] && !occupied[up] && seen[up] !== stamp) { seen[up] = stamp; stack[n++] = up; }
    if (!wall[dn] && !occupied[dn] && seen[dn] !== stamp) { seen[dn] = stamp; stack[n++] = dn; }
    if (!wall[lf] && !occupied[lf] && seen[lf] !== stamp) { seen[lf] = stamp; stack[n++] = lf; }
    if (!wall[rt] && !occupied[rt] && seen[rt] !== stamp) { seen[rt] = stamp; stack[n++] = rt; }
  }
  return low;
}

// True when the box just pushed to `t` completes a frozen 2x2 of walls/boxes
// that holds a box off its goal.
function frozenBlock(
  w: number,
  wall: Uint8Array,
  occupied: Uint8Array,
  goal: Uint8Array,
  t: number,
): boolean {
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1;
    const c = a + w;
    const d = c + 1;
    if (!(wall[a] || occupied[a]) || !(wall[b] || occupied[b])) continue;
    if (!(wall[c] || occupied[c]) || !(wall[d] || occupied[d])) continue;
    if ((occupied[a] && !goal[a]) || (occupied[b] && !goal[b])) return true;
    if ((occupied[c] && !goal[c]) || (occupied[d] && !goal[d])) return true;
  }
  return false;
}

// The shortest walk from `from` to `to` around walls and boxes, lower-case LURD.
function walkTo(
  w: number,
  wall: Uint8Array,
  occupied: Uint8Array,
  from: number,
  to: number,
): string {
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1);
  const how = new Array<string>(wall.length);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi];
    if (p === to) break;
    for (let k = 0; k < 4; k++) {
      const q = p + DY[k] * w + DX[k];
      if (wall[q] || occupied[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = WALK[k];
      queue.push(q);
    }
  }
  if (prev[to] === -1) return '';
  let s = '';
  for (let p = to; p !== from; p = prev[p]) s = how[p] + s;
  return s;
}

interface Solved {
  pushes: number;
  moves: string;
}

// Push-optimal BFS over one (sub)level: `wall` already carries any foreign boxes
// as walls, `goals`/`boxes` are this sublevel's own, `player` where the player starts.
function solvePushes(
  w: number,
  wall: Uint8Array,
  goals: number[],
  boxes0: number[],
  player0: number,
  maxStates: number,
): Solved | null {
  const size = wall.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(w, wall, goals);
  if (boxes0.some((b) => !live[b])) return null;
  const solvedAll = (bs: number[]): boolean => bs.every((b) => goal[b] === 1);
  if (solvedAll(boxes0)) return { pushes: 0, moves: '' };

  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const mark = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;

  // Numeric state keys while size^(boxes+1) is exact, else a string key.
  const nB = boxes0.length;
  const numeric = Math.pow(size, nB + 1) < Number.MAX_SAFE_INTEGER;
  const keyOf = (bs: number[], low: number): number | string => {
    if (numeric) {
      let k = low;
      for (const b of bs) k = k * size + b;
      return k;
    }
    return low + '|' + bs.join(',');
  };

  const statesBoxes: number[][] = [boxes0.slice()];
  const statesPlayer: number[] = [player0];
  const parent: number[] = [-1];
  const index = new Map<number | string, number>();
  for (const b of boxes0) occupied[b] = 1;
  index.set(keyOf(boxes0, reach(w, wall, occupied, player0, seen, ++stamp, stack)), 0);
  for (const b of boxes0) occupied[b] = 0;

  let found = -1;
  for (let head = 0; found < 0 && head < statesBoxes.length; head++) {
    const boxes = statesBoxes[head];
    for (const b of boxes) occupied[b] = 1;
    reach(w, wall, occupied, statesPlayer[head], seen, ++stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const b = boxes[bi];
      for (let k = 0; k < 4; k++) {
        const d = DY[k] * w + DX[k];
        const t = b + d;
        // The player must stand on b-d, the target must be open floor and live.
        if (seen[b - d] !== here || wall[t] || occupied[t] || !live[t]) continue;
        occupied[b] = 0;
        occupied[t] = 1;
        const frozen = frozenBlock(w, wall, occupied, goal, t);
        let key: number | string = '';
        let next: number[] | null = null;
        if (!frozen) {
          next = boxes.slice();
          next[bi] = t;
          next.sort((a, z) => a - z);
          key = keyOf(next, reach(w, wall, occupied, b, mark, ++stamp, stack));
        }
        occupied[t] = 0;
        occupied[b] = 1;
        if (frozen || next === null || index.has(key)) continue;
        if (statesBoxes.length >= maxStates) {
          for (const x of boxes) occupied[x] = 0;
          return null;
        }
        index.set(key, statesBoxes.length);
        statesBoxes.push(next);
        statesPlayer.push(b); // after the push the player stands on the box's old square
        parent.push(head);
        if (solvedAll(next)) found = statesBoxes.length - 1;
      }
    }
    for (const x of boxes) occupied[x] = 0;
  }
  if (found < 0) return null;

  // Rebuild the moves: walk to each push's standing square, then push.
  const path: number[] = [];
  for (let s = found; s > 0; s = parent[s]) path.push(s);
  path.reverse();
  let moves = '';
  let player = player0;
  let boxes = boxes0;
  const occ = new Uint8Array(size);
  for (const s of path) {
    const nextBoxes = statesBoxes[s];
    const from = boxes.find((b) => !nextBoxes.includes(b))!;
    const to = nextBoxes.find((b) => !boxes.includes(b))!;
    const d = to - from;
    const k = DX.findIndex((_, j) => DY[j] * w + DX[j] === d);
    for (const b of boxes) occ[b] = 1;
    moves += walkTo(w, wall, occ, player, from - d);
    for (const b of boxes) occ[b] = 0;
    moves += PUSH[k];
    player = from;
    boxes = nextBoxes;
  }
  return { pushes: path.length, moves };
}

// Split the level into rooms: cut the player's own row (the hallway — a box
// there reaches no goal, so every hallway square is a dead square) out of the
// floor; each remaining part that holds boxes is one room. Null when the level
// is not a clean set of rooms (a box in the hallway, a goal in the hallway, or
// a part whose boxes and goals do not balance).
function roomsOf(level: Level): { boxes: number[]; goals: number[] }[] | null {
  const { w, wall, goals, boxes, player } = level;
  const live = liveSquares(w, wall, goals);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) {
    if (!wall[i] && !live[i]) cut[i] = 1;
  }
  if (boxes.some((b) => cut[b] === 1)) return null;
  const part = new Int32Array(wall.length).fill(-1);
  const parts: { squares: number[]; boxes: number[]; goals: number[] }[] = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = parts.length;
    for (let i = 0; i < squares.length; i++) {
      for (let k = 0; k < 4; k++) {
        const q = squares[i] + DY[k] * w + DX[k];
        if (!wall[q] && !cut[q] && part[q] < 0) {
          part[q] = parts.length;
          squares.push(q);
        }
      }
    }
    parts.push({ squares, boxes: [], goals: [] });
  }
  for (const b of boxes) parts[part[b]].boxes.push(b);
  for (const g of goals) {
    if (part[g] < 0) return null;
    parts[part[g]].goals.push(g);
  }
  if (parts.some((p) => p.boxes.length !== p.goals.length)) return null;
  return parts.filter((p) => p.boxes.length > 0);
}

function solveLevel(level: Level): string {
  const rooms = roomsOf(level);
  if (rooms === null) {
    const whole = solvePushes(level.w, level.wall, level.goals, level.boxes, level.player, WHOLE_STATES);
    return whole === null ? '' : whole.moves;
  }
  // Solve room by room. While a room is being solved, every other room's boxes
  // stand as walls (a finished room's boxes stand on its goals); the player
  // walks on from wherever the previous room's solution left them.
  let player = level.player;
  let moves = '';
  const done = new Set<number>();
  for (let ri = 0; ri < rooms.length; ri++) {
    const room = rooms[ri];
    const wall = level.wall.slice();
    for (let oj = 0; oj < rooms.length; oj++) {
      if (oj === ri) continue;
      const spots = done.has(oj) ? rooms[oj].goals : rooms[oj].boxes;
      for (const b of spots) wall[b] = 1;
    }
    const solved = solvePushes(level.w, wall, room.goals, room.boxes, player, ROOM_STATES);
    if (solved === null) {
      const whole = solvePushes(level.w, level.wall, level.goals, level.boxes, level.player, WHOLE_STATES);
      return whole === null ? '' : whole.moves;
    }
    moves += solved.moves;
    // Advance the player along the moves just made.
    for (const ch of solved.moves) {
      const k = WALK.indexOf(ch.toLowerCase());
      player += DY[k] * level.w + DX[k];
    }
    done.add(ri);
  }
  return moves;
}

for (const id of readdirSync(I).sort()) {
  const level = parseLevel(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  const moves = solveLevel(level);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
