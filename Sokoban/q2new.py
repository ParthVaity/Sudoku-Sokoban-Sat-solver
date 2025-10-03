"""
Sokoban Solver using SAT (Boilerplate)
--------------------------------------
Instructions:
- Implement encoding of Sokoban into CNF.
- Use PySAT to solve the CNF and extract moves.
- Ensure constraints for player movement,box pushes,and goal conditions.

Grid Encoding:
- 'P'=Player
- 'B'=Box
- 'G'=Goal
- '#'=Wall
- '.'=Empty space
"""

from pysat.formula import CNF
from pysat.solvers import Solver

# Directions for movement
DIRS={'U': (-1,0),'D': (1,0),'L': (0,-1),'R': (0,1)}


class SokobanEncoder:
    def __init__(self,grid,T):
        """
        Initialize encoder with grid and time limit.

        Args:
            grid (list[list[str]]): Sokoban grid.
            T (int): Max number of steps allowed.
        """
        self.grid=grid
        self.T=T
        self.N=len(grid)
        self.M=len(grid[0])

        self.goals=[]
        self.boxes=[]
        self.walls=[]
        self.player_start=None
        self._parse_grid()

        self.num_boxes=len(self.boxes)
        self.cnf=CNF()

        self.map={}
        self.count=1

    def _parse_grid(self):
        """Parse grid to find player,boxes,goals,and walls."""
        for i in range(self.N):
            for j in range(self.M):
                c=self.grid[i][j]
                if (c=='P'):
                    self.player_start=(i,j)
                elif (c=='B'):
                    self.boxes.append((i,j))
                elif (c=='G'):
                    self.goals.append((i,j))
                elif (c=='#'):
                    self.walls.append((i,j))

    # ---------------- Variable Encoding ----------------
    def encoder(self,key):
        if key not in self.map:
            self.map[key]=self.count
            self.count+=1
        return self.map[key]
    
    def var_player(self,x,y,t):
        """
        Variable ID for player at (x,y) at time t.
        """
        return self.encoder(("P",x,y,t))
        
    def var_box(self,b,x,y,t):
        """
        Variable ID for box b at (x,y) at time t.
        """
        return self.encoder(("B",b,x,y,t))
    
    def var_move(self,d,t):
        return self.encoder(("M",d,t))
    
    def var_q(self,x,y,d,t):
        return self.encoder(("Q",x,y,d,t))

    def clamp(self,x,y):
        return (0<=x<self.N) and (0<=y<self.M) and ((x,y) not in self.walls)

    # ---------------- Encoding Logic ----------------
    def encode(self):
        """
        Build CNF constraints for Sokoban:
        - Initial state
        - Valid moves (exactly one move per step; legal from the current cell)
        - Player transitions
        - Box pushes+robust frame axioms (via Tseitin Q)
        - Non-overlap (boxes with boxes; player with boxes)
        - Goal condition at final timestep
        """

        self.cnf.append([self.var_player(*self.player_start,0)]) #player

        for b,(x,y) in enumerate(self.boxes): #boses
            self.cnf.append([self.var_box(b,x,y,0)])

        for t in range(self.T): #one move per cycle of T
            mv=[]
            for d in DIRS:
                mv.append(self.var_move(d,t))
            self.cnf.append(mv)  
            for i in range(len(mv)): 
                for j in range(i+1,len(mv)):
                    self.cnf.append([-mv[i],-mv[j]])

        for t in range(self.T+1): #one player position only
            pos=[]
            for x in range(self.N):
                for y in range(self.M):
                    if(x,y) not in self.walls:
                        pos.append(self.var_player(x,y,t))
            self.cnf.append(pos)
            for i in range(len(pos)):
                for j in range(i+1,len(pos)):
                    self.cnf.append([-pos[i],-pos[j]])

        for t in range(self.T+1): #one position per box
            for b in range(self.num_boxes):
                box=[]
                for x in range(self.N):
                    for y in range(self.M):
                        if(x,y) not in self.walls:
                            box.append(self.var_box(b,x,y,t))
                self.cnf.append(box)
                for i in range(len(box)):
                    for j in range(i+1,len(box)):
                        self.cnf.append([-box[i],-box[j]])

        for t in range(self.T+1): #boxes stay on unique cells
            for x in range(self.N):
                for y in range(self.M):
                    for b1 in range(self.num_boxes):
                        for b2 in range(b1+1,self.num_boxes):
                            self.cnf.append([-self.var_box(b1,x,y,t),-self.var_box(b2,x,y,t)])

        for t in range(self.T+1): #player and box cannot be together
            for x in range(self.N):
                for y in range(self.M):
                    for b in range(self.num_boxes):
                        self.cnf.append([-self.var_player(x,y,t),-self.var_box(b,x,y,t)])

        for t in range(self.T): #all possible moves
            for x in range(self.N):
                for y in range(self.M):
                    if (x,y) in self.walls:
                        continue
                    poss=[]
                    for d,(dx,dy) in DIRS.items():
                        if self.clamp(x+dx,y+dy):
                            poss.append(self.var_move(d,t))
                    if poss:
                        self.cnf.append([-self.var_player(x,y,t)]+poss)
                    else:
                        self.cnf.append([-self.var_player(x,y,t)])

        for t in range(self.T): #new variable q to denote p(x,y,t) moves (d,t)
            for x in range(self.N):
                for y in range(self.M):
                    if (x,y) in self.walls:
                        continue
                    for d in DIRS:
                        self.cnf.append([-self.var_q(x,y,d,t),self.var_player(x,y,t)])
                        self.cnf.append([-self.var_q(x,y,d,t),self.var_move(d,t)])
                        self.cnf.append([-self.var_player(x,y,t),-self.var_move(d,t),self.var_q(x,y,d,t)])

        for t in range(self.T): #movement of player
            for x in range(self.N):
                for y in range(self.M):
                    if (x,y) in self.walls:
                        continue
                    for d,(dx,dy) in DIRS.items():
                        if self.clamp(x+dx,y+dy):
                            self.cnf.append([-self.var_player(x,y,t),-self.var_move(d,t),self.var_player(x+dx,y+dy,t+1)])

        for t in range(self.T): #wrong pushes
            for x in range(self.N):
                for y in range(self.M):
                    if (x,y) in self.walls:
                        continue
                    for d,(dx,dy) in DIRS.items():
                        px,py=x-dx,y-dy
                        nx,ny=x+dx,y+dy
                        if not self.clamp(px,py):
                            continue
                        if not self.clamp(nx,ny):
                            for b in range(self.num_boxes):
                                self.cnf.append([-self.var_q(px,py,d,t),-self.var_box(b,x,y,t)])

        for t in range(self.T): #pushing
            for x in range(self.N):
                for y in range(self.M):
                    if (x,y) in self.walls:
                        continue
                    for d,(dx,dy) in DIRS.items():
                        px,py=x-dx,y-dy
                        nx,ny=x+dx,y+dy
                        if not (0<=px<self.N and 0<=py<self.M):
                            continue
                        if self.clamp(nx,ny):
                            for b in range(self.num_boxes):
                                self.cnf.append([-self.var_q(px,py,d,t),-self.var_box(b,x,y,t),self.var_box(b,nx,ny,t+1)])

        for t in range(self.T): #nopushing boxed with each other
            for x in range(self.N):
                for y in range(self.M):
                    if (x,y) in self.walls:
                        continue
                    for d,(dx,dy) in DIRS.items():
                        px,py=x-dx,y-dy
                        nx,ny=x+dx,y+dy
                        if not (0 <= px < self.N and 0 <= py < self.M):
                            continue
                        if self.clamp(nx,ny):
                            for b in range(self.num_boxes):
                                for b2 in range(self.num_boxes):
                                    if (b2==b):
                                        continue
                                    self.cnf.append([-self.var_q(px,py,d,t),-self.var_box(b,x,y,t),-self.var_box(b2,nx,ny,t)])

        for t in range(self.T): #box stays stationary if not moved
            for b in range(self.num_boxes):
                for x in range(self.N):
                    for y in range(self.M):
                        if (x,y) in self.walls:
                            continue
                        check=[-self.var_box(b,x,y,t),self.var_box(b,x,y,t+1)]
                        for d,(dx,dy) in DIRS.items():
                            px,py=x-dx,y-dy
                            nx,ny=x+dx,y+dy
                            if ((0<=px<self.N) and (0<=py<self.M) and self.clamp(nx,ny)):
                                check.append(self.var_q(px,py,d,t))
                        self.cnf.append(check)

        for b in range(self.num_boxes): #goal
            goal=[]
            for (x,y) in self.goals:
                goal.append(self.var_box(b,x,y,self.T))
            self.cnf.append(goal)

        for t in range(self.T): #once on goal no more moving
            for b in range(self.num_boxes):
                for (x,y) in self.goals:
                    self.cnf.append([-self.var_box(b,x,y,t),self.var_box(b,x,y,t+1)])

        return self.cnf


def decode(model,encoder):
    """
    Decode SAT model into list of moves ('U','D','L','R').

    Returns the shortest prefix up to the *first* time all boxes are on goal cells.
    """
    N,M,T=encoder.N,encoder.M,encoder.T
    s=set(model)
    moves=[]
    for t in range(encoder.T):
        curr=None
        for d in DIRS:
            if encoder.var_move(d,t) in s:
                curr=d
                break
        if curr is None:
            break
        moves.append(curr)

    def done(t): #all boxes reached
        for b in range(encoder.num_boxes):
            hit=False
            for (x,y) in encoder.goals:
                if encoder.var_box(b,x,y,t) in s:
                    hit=True
                    break
            if not hit:
                return False
        return True

    final=None
    for t in range(encoder.T+1):
        if done(t):
            final=t
            break

    if final is None:
        return moves 
    return moves[:final]


def solve_sokoban(grid,T):
    """
    DO NOT MODIFY THIS FUNCTION.

    Solve Sokoban using SAT encoding.

    Args:
        grid (list[list[str]]): Sokoban grid.
        T (int): Max number of steps allowed.

    Returns:
        list[str] or "unsat": Move sequence or unsatisfiable.
    """
    encoder=SokobanEncoder(grid,T)
    cnf=encoder.encode()

    with Solver(name='g3') as solver:
        solver.append_formula(cnf)
        if not solver.solve():
            return -1

        model=solver.get_model()
        if not model:
            return -1

        return decode(model,encoder)
