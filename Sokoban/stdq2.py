"""
Sokoban Solver using SAT (Action-based BMC)
-------------------------------------------
This implements a bounded SAT encoding of Sokoban using per-timestep actions
(move or push) with preconditions and effects.

Notes:
- Grid chars: 'P' player, 'B' box, 'G' goal, '#' wall, '.' empty.
- Multiple goals allowed; any box can satisfy any goal at T.
- Encoding uses:
    P(x,y,t)              : player at cell (x,y) at time t
    B(b,x,y,t)            : box b at cell (x,y) at time t
    M(x,y,dir,t)          : action "move from (x,y) to neighbor dir" at t
    U(b,x,y,dir,t)        : action "push box b from (x,y)+dir into (x,y)+2*dir" at t
- Exactly one action per timestep; exactly one player position per timestep;
  exactly one position per box per timestep; boxes are non-overlapping.

This follows the bounded-model-checking approach in the shared paper, but
with an action-variable CNF rather than the paper's 2-bit-per-cell state
encoding.
"""

from pysat.formula import CNF
from pysat.solvers import Solver

# Directions for movement
DIRS = {'U': (-1, 0), 'D': (1, 0), 'L': (0, -1), 'R': (0, 1)}
DIR_KEYS = list(DIRS.keys())


class SokobanEncoder:
    def __init__(self, grid, T):
        """
        Initialize encoder with grid and time limit.

        Args:
            grid (list[list[str]]): Sokoban grid.
            T (int): Max number of steps allowed.
        """
        self.grid = grid
        self.T = T
        self.N = len(grid)
        self.M = len(grid[0])

        self.goals = []
        self.boxes = []
        self.player_start = None
        self.walls = set()
        self.floors = set()

        self._parse_grid()

        self.num_boxes = len(self.boxes)
        self.cnf = CNF()

        # variable id map
        self._varmap = {}
        self._varcnt = 0

    def _parse_grid(self):
        """Parse grid to find player, boxes, goals, and wall/floor sets."""
        for x in range(self.N):
            for y in range(self.M):
                ch = self.grid[x][y]
                if ch == '#':
                    self.walls.add((x, y))
                else:
                    self.floors.add((x, y))
                if ch == 'P':
                    self.player_start = (x, y)
                elif ch == 'B':
                    self.boxes.append((x, y))
                elif ch == 'G':
                    self.goals.append((x, y))
                # '.' is empty; anything else handled above

        if self.player_start is None:
            raise ValueError("No player 'P' found in grid.")
        if not self.boxes:
            raise ValueError("No boxes 'B' found in grid.")
        if len(self.goals) < len(self.boxes):
            # Allow, but it will be unsat unless fixed. Warn softly.
            pass

    # ---------------- Variable Encoding ----------------
    def _id(self, key):
        """Get or create a unique positive integer variable id for a key."""
        if key in self._varmap:
            return self._varmap[key]
        self._varcnt += 1
        self._varmap[key] = self._varcnt
        return self._varcnt

    def var_player(self, x, y, t):
        """Variable ID for player at (x, y) at time t."""
        return self._id(('P', x, y, t))

    def var_box(self, b, x, y, t):
        """Variable ID for box b at (x, y) at time t."""
        return self._id(('B', b, x, y, t))

    def var_move(self, x, y, d, t):
        """Variable ID for move action from (x,y) in direction d at time t (no push)."""
        return self._id(('M', x, y, d, t))

    def var_push(self, b, x, y, d, t):
        """Variable ID for push action of box b, player at (x,y) pushing in direction d at time t."""
        return self._id(('U', b, x, y, d, t))

    # ------------- Helper: CNF Patterns (one-hot etc.) -------------
    def _at_least_one(self, lits):
        if lits:
            self.cnf.append(list(lits))

    def _at_most_one(self, lits):
        # pairwise
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                self.cnf.append([-lits[i], -lits[j]])

    def _exactly_one(self, lits):
        self._at_least_one(lits)
        self._at_most_one(lits)

    def _is_floor(self, x, y):
        return (x, y) in self.floors

    def _neighbor(self, x, y, d):
        dx, dy = DIRS[d]
        return x + dx, y + dy

    # ---------------- Encoding Logic ----------------
    def encode(self):
        """
        Build CNF constraints for Sokoban:
        - Initial state
        - Valid moves (player + box pushes) via action variables
        - Frame axioms and effects
        - Non-overlapping boxes & one-hot positions
        - Goal condition at final timestep
        """
        N, M, T = self.N, self.M, self.T
        floors = list(self.floors)

        # 0) One-hot player and box positions for every t
        for t in range(T + 1):
            # player exactly one
            p_vars = [self.var_player(x, y, t) for (x, y) in floors]
            self._exactly_one(p_vars)

            # for each box: exactly one
            for b in range(self.num_boxes):
                b_vars = [self.var_box(b, x, y, t) for (x, y) in floors]
                self._exactly_one(b_vars)

            # Boxes non-overlapping: at most one box in any cell
            for (x, y) in floors:
                cell_box_vars = [self.var_box(b, x, y, t) for b in range(self.num_boxes)]
                self._at_most_one(cell_box_vars)

            # Player cannot share cell with any box
            for (x, y) in floors:
                pxy = self.var_player(x, y, t)
                for b in range(self.num_boxes):
                    self.cnf.append([-pxy, -self.var_box(b, x, y, t)])

        # 1) Initial conditions at t=0
        px0, py0 = self.player_start
        self.cnf.append([self.var_player(px0, py0, 0)])  # unit
        # Fix boxes initial positions (order boxes by their appearance)
        if len(self.boxes) != self.num_boxes:
            raise AssertionError("num_boxes mismatch")
        for b, (bx, by) in enumerate(self.boxes):
            self.cnf.append([self.var_box(b, bx, by, 0)])

        # 2) Actions per timestep t=0..T-1: exactly one action, with preconditions & effects
        for t in range(T):
            # collect all candidate action vars for this t
            action_vars = []

            # MOVE actions (no push): for each floor cell & direction where neighbor is floor
            for (x, y) in floors:
                for d in DIR_KEYS:
                    nx, ny = self._neighbor(x, y, d)
                    if not self._is_floor(nx, ny):
                        continue
                    a = self.var_move(x, y, d, t)
                    action_vars.append(a)
                    # Preconditions: player at (x,y,t) and neighbor has NO box
                    self.cnf.append([-a, self.var_player(x, y, t)])
                    for b in range(self.num_boxes):
                        self.cnf.append([-a, -self.var_box(b, nx, ny, t)])

                    # Effects: player at (nx,ny,t+1)
                    self.cnf.append([-a, self.var_player(nx, ny, t + 1)])
                    # Frame for boxes: (handled globally below via stay/move rules)

            # PUSH actions: for each floor cell (player), direction where next and beyond are floors
            for (x, y) in floors:
                for d in DIR_KEYS:
                    nx, ny = self._neighbor(x, y, d)          # where the box must be
                    fx, fy = self._neighbor(nx, ny, d)        # box destination
                    if not (self._is_floor(nx, ny) and self._is_floor(fx, fy)):
                        continue
                    for b in range(self.num_boxes):
                        u = self.var_push(b, x, y, d, t)
                        action_vars.append(u)
                        # Preconditions:
                        # - player at (x,y,t)
                        self.cnf.append([-u, self.var_player(x, y, t)])
                        # - targeted box b at (nx,ny,t)
                        self.cnf.append([-u, self.var_box(b, nx, ny, t)])
                        # - destination (fx,fy) empty of ANY box
                        for bb in range(self.num_boxes):
                            self.cnf.append([-u, -self.var_box(bb, fx, fy, t)])

                        # Effects:
                        # - player moves into (nx,ny) at t+1
                        self.cnf.append([-u, self.var_player(nx, ny, t + 1)])
                        # - box b moves to (fx,fy) at t+1
                        self.cnf.append([-u, self.var_box(b, fx, fy, t + 1)])

            # Exactly one action per timestep
            self._exactly_one(action_vars)

            # 3) Frame axioms for boxes: if a box isn't pushed out, it stays.
            #    And push-in implies occupancy (already added).
            for b in range(self.num_boxes):
                for (cx, cy) in floors:
                    # Identify pushes that move box b OUT of (cx,cy)
                    # These have the player at (cx,cy) - dir and push dir so that (nx,ny) == (cx,cy)
                    push_out_vars = []
                    for d in DIR_KEYS:
                        px, py = self._neighbor(cx, cy, {'U':'D','D':'U','L':'R','R':'L'}[d])  # player source must be opposite neighbor
                        # More directly: player source is (cx,cy) - DIRS[d]
                        dx, dy = DIRS[d]
                        px, py = cx - dx, cy - dy
                        nx, ny = cx, cy
                        fx, fy = cx + dx, cy + dy
                        if self._is_floor(px, py) and self._is_floor(nx, ny) and self._is_floor(fx, fy):
                            push_out_vars.append(self.var_push(b, px, py, d, t))

                    # If box b at (cx,cy) at t and no push-out happens, then it remains at (cx,cy) at t+1
                    # Clause: (-B(b,c,t) OR -u1 OR -u2 ... OR B(b,c,t+1))
                    clause = [-self.var_box(b, cx, cy, t)]
                    clause.extend([-u for u in push_out_vars])
                    clause.append(self.var_box(b, cx, cy, t + 1))
                    self.cnf.append(clause)

                    # Also ensure any push-IN already forces B(b,c,t+1) (done in effects above).

            # 4) Frame for player is handled by action effects + exactly-one player per t

        # 5) Goal condition at final timestep: every box on some goal cell
        if not self.goals:
            # If there are no goals, require no-op (will likely be unsat if boxes exist)
            pass
        else:
            for b in range(self.num_boxes):
                goal_lits = [self.var_box(b, gx, gy, T) for (gx, gy) in self.goals]
                self._at_least_one(goal_lits)

        return self.cnf


def decode(model, encoder):
    """
    Decode SAT model into list of moves ('U', 'D', 'L', 'R').

    Args:
        model (list[int]): Satisfying assignment from SAT solver.
        encoder (SokobanEncoder): Encoder object with grid info.

    Returns:
        list[str]: Sequence of moves (length T).
    """
    # Build a set for fast lookup
    true_set = set(l for l in model if l > 0)

    def is_true(var_id):
        return var_id in true_set

    # Extract player positions per t
    pos = []
    for t in range(encoder.T + 1):
        found = None
        for (x, y) in encoder.floors:
            if is_true(encoder.var_player(x, y, t)):
                found = (x, y)
                break
        if found is None:
            # Fallback: no clear position; return empty
            return []
        pos.append(found)

    # Convert consecutive positions to directions
    moves = []
    for t in range(encoder.T):
        (x1, y1) = pos[t]
        (x2, y2) = pos[t + 1]
        dx, dy = x2 - x1, y2 - y1
        dmap = {(-1, 0): 'U', (1, 0): 'D', (0, -1): 'L', (0, 1): 'R'}
        if (dx, dy) in dmap:
            moves.append(dmap[(dx, dy)])
        else:
            # Stayed in place (shouldn't happen with our encoding) — emit empty or skip
            moves.append('U')  # arbitrary fallback
    return moves


def solve_sokoban(grid, T):
    """
    DO NOT MODIFY THIS FUNCTION.

    Solve Sokoban using SAT encoding.

    Args:
        grid (list[list[str]]): Sokoban grid.
        T (int): Max number of steps allowed.

    Returns:
        list[str] or "unsat": Move sequence or unsatisfiable.
    """
    encoder = SokobanEncoder(grid, T)
    cnf = encoder.encode()

    with Solver(name='g3') as solver:
        solver.append_formula(cnf)
        if not solver.solve():
            return -1

        model = solver.get_model()
        if not model:
            return -1

        return decode(model, encoder)
