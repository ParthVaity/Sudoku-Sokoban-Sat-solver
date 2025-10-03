"""
sudoku_solver.py

Implement the function `solve_sudoku(grid: List[List[int]]) -> List[List[int]]` using a SAT solver from PySAT.
"""

from pysat.formula import CNF
from pysat.solvers import Solver
from typing import List

def solve_sudoku(grid: List[List[int]]) -> List[List[int]]:
    """Solves a Sudoku puzzle using a SAT solver. Input is a 2D grid with 0s for blanks."""
    cnf=CNF()
    #rowcheck
    for row in range(1,10):
        for n in range(1,10):
            rc=[]
            for column in range(1,10):
                rc.append(row*100 + column*10 + n)
            cnf.append(rc)   

    #columncheck
    for column in range(1,10):
        for n in range(1,10):
            cc=[]
            for row in range(1,10):
                cc.append(row*100 + column*10 + n)
            cnf.append(cc)

    #blockcheck
    for rowblock in range(1,4):
        for columnblock in range(1,4):
            for n in range(1,10):
                bc=[]
                for i in range(1,4):
                    for j in range(1,4):
                        bc.append(((3*(rowblock-1))+i)*100 + ((3*(columnblock-1))+j)*10 + n)
                cnf.append(bc)

    #multicheck
    for row in range(1,10):
        for column in range(1,10):
            for n1 in range(1,10):
                for n2 in range(1,10):
                    if(n2!=n1):
                        cnf.append([-1*(row*100 + column*10 + n1),-1*(row*100 + column*10 + n2)])
    
    #initial
    initial=[]
    for row in range(1,10):
        for column in range(1,10):
            if(grid[row-1][column-1]!=0):
                initial.append(row*100 + column*10 + grid[row-1][column-1])
    
    #solving
    with Solver(name='glucose3') as solver:
        solver.append_formula(cnf.clauses)
        if(solver.solve(assumptions=initial)):
            final=[]
            for row in range(9):
                row=[]
                for column in range(9):
                    row.append(0)
                final.append(row)
            
            model=solver.get_model()
            for i in model:
                if(i>0):
                    num=i%10
                    i=i//10
                    column=i%10
                    i=i//10
                    row=i
                    final[row-1][column-1]=num
                else:
                    continue
        else:
            final=[[]]
    # TODO: implement encoding and solving using PySAT
    return final
