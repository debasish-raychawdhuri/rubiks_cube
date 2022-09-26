from ctypes.wintypes import HPALETTE
from z3 import *
from enum import Enum


def minimize(phi, objective):
    s = Optimize()
    s.add(phi)
    h = s.minimize(objective)
    c = s.check()
    if c == sat:
        print(s.model())
    elif c == unsat:
        print("unsat")
    else:
        print("That was too hard a problem for me, maybe I should go to IITB")


# Symmetric encoding of a Rubik's cube. Each color is encoded by a BitVector with 6 bits, each corresponding to one color. The faces are marked by the direction, X,Y,Z (in a right handed coordinate system) and each face is marked by the axis and a positive or negative direction. Each square on a face is marked using which other faces they are connected to. Each face is connected to four other faces. This is encoded in two trinary bits (0 representing the negative side of the axis, 1 non-attachment to the axis, 2-attachment with the positive side.). If we are considering the (X,+) face, the (Y,+) side is on the right and (Z,+) face is on the top. The square connected to (Y,-) and (Z,+) is at position (0,2) on the face. The center square is (1,1). The square connected to only the (Z,+) face is (1,2) [1 because it is not connected to the Y axis and 2 because it is attached to the positive side of Z]. The faces are numberd 0 to 5 in (X,-), (X,+),...,(Z,+).

# Positions on a negative face -
#           2  5  8
#           1  4  7
#           0  3  6
#          ---------
# 6  3  0 | 0  1  2 | 0  3  6
# 7  4  1 | 3  4  5 | 1  4  7
# 8  5  2 | 6  7  8 | 2  5  8
#          ---------
#           0  3  6
#           1  4  7
#           2  5  8


# Postions on a positive face -
#           6  3  0
#           7  4  1
#           8  5  2
#          ---------
# 0  3  6 | 2  1  0 | 6  3  0
# 1  4  7 | 5  4  3 | 7  4  1
# 2  5  8 | 8  7  6 | 8  5  2
#          ---------
#           8  5  2
#           7  4  1
#           6  3  0

class NeighborDirection(Enum):
    HP = 0,
    HN = 1,
    VP = 2,
    VN = 3


class FaceState:
    def __init__(self):
        self.array = [BitVec(""), BitVec(""), BitVec(""),
                      BitVec(""), BitVec(""), BitVec(""),
                      BitVec(""), BitVec(""), BitVec("")]

    def get_bits(self, square):
        return self.array[square]


class CubeState:
    def __init__(self):
        self.array = [FaceState(), FaceState(), FaceState(),
                      FaceState(), FaceState(), FaceState()]

    @staticmethod
    def get_neighbor_array_pos(face, position, n_dir):
        vpos = position//3
        hpos = position % 3
        self_pos = (face % 2)*2

        if n_dir == NeighborDirection.HN or n_dir == n_dir == NeighborDirection.HP:
            nvpos = self_pos
            nhpos = vpos
        else:
            nvpos = hpos
            nhpos = self_pos
        if ((n_dir == NeighborDirection.HP and hpos != 2)
                or (n_dir == NeighborDirection.HN and hpos != 0)
                or (n_dir == NeighborDirection.VP and vpos != 2)
                or (n_dir == NeighborDirection.VN and vpos != 0)):
            return -1
        return nvpos*3+nhpos

    def rotate_sides(self, final_state, face, constraints):
        negative_face = (face >> 1) << 1
        face_h_neg = (negative_face+2) % 6
        face_h_pos = (negative_face+3) % 6
        face_v_neg = (negative_face+4) % 6
        face_v_pos = (negative_face+5) % 6
        if face % 2 == 0:
            constraints.add(self.array[face_h_neg][0]
                            == final_state.array[face_v_neg][6])
            constraints.add(self.array[face_h_neg][1]
                            == final_state.array[face_v_neg][3])
            constraints.add(self.array[face_v_neg][2]
                            == final_state.array[face][0])

            constraints.add(self.array[face_v_pos][0] ==
                            final_state.array[face_h_neg][0])
            constraints.add(self.array[face_v_pos][3] ==
                            final_state.array[face_h_neg][1])
            constraints.add(self.array[face_v_pos][6] ==
                            final_state.array[face_h_neg][2])

            constraints.add(self.array[face_h_pos][0] ==
                            final_state.array[face_v_pos][6])
            constraints.add(self.array[face_h_pos][1] ==
                            final_state.array[face_v_pos][3])
            constraints.add(self.array[face_h_pos][2] ==
                            final_state.array[face_v_pos][0])

            constraints.add(self.array[face_v_neg][0] ==
                            final_state.array[face_h_pos][0])
            constraints.add(self.array[face_v_neg][3] ==
                            final_state.array[face_h_pos][1])
            constraints.add(self.array[face_v_neg][6] ==
                            final_state.array[face_h_pos][2])
        else:
            constraints.add(self.array[face_h_neg][6]
                            == final_state.array[face_v_neg][8])
            constraints.add(self.array[face_h_neg][7]
                            == final_state.array[face_v_neg][5])
            constraints.add(self.array[face_v_neg][8]
                            == final_state.array[face][2])

            constraints.add(self.array[face_v_pos][8] ==
                            final_state.array[face_h_neg][6])
            constraints.add(self.array[face_v_pos][5] ==
                            final_state.array[face_h_neg][7])
            constraints.add(self.array[face_v_pos][2] ==
                            final_state.array[face_h_neg][8])

            constraints.add(self.array[face_h_pos][6] ==
                            final_state.array[face_v_pos][8])
            constraints.add(self.array[face_h_pos][7] ==
                            final_state.array[face_v_pos][5])
            constraints.add(self.array[face_h_pos][8] ==
                            final_state.array[face_v_pos][2])

            constraints.add(self.array[face_v_neg][8] ==
                            final_state.array[face_h_pos][8])
            constraints.add(self.array[face_v_neg][5] ==
                            final_state.array[face_h_pos][7])
            constraints.add(self.array[face_v_neg][2] ==
                            final_state.array[face_h_pos][6])

    # Rotates positive face anti clockwise and negative face clockwise

    def __rotate_face(self, final_state, face, constraints):
        constraints.add(self.array[face][0] == final_state.array[face][2])
        constraints.add(self.array[face][1] == final_state.array[face][5])
        constraints.add(self.array[face][2] == final_state.array[face][8])
        constraints.add(self.array[face][3] == final_state.array[face][1])
        constraints.add(self.array[face][4] == final_state.array[face][4])
        constraints.add(self.array[face][5] == final_state.array[face][7])
        constraints.add(self.array[face][6] == final_state.array[face][0])
        constraints.add(self.array[face][7] == final_state.array[face][3])
        constraints.add(self.array[face][8] == final_state.array[face][6])

        self.rotate_sides(final_state, face, constraints)


b1 = Bool("b1")
b2 = Bool("b2")
x = Int("x")
y = Int("y")
solver = Solver()
cond1 = Implies(x < y, b1)
cond2 = Implies(x > y, b2)
phi = And(cond1, cond2, Or(b1, b2), x >= 0, y > 0)
minimize(phi, y)


print(CubeState.get_neighbor_array_pos(0, 2, NeighborDirection.HN))
print(CubeState.get_neighbor_array_pos(0, 8, NeighborDirection.VP))
print(CubeState.get_neighbor_array_pos(3, 8, NeighborDirection.VP))
print(CubeState.get_neighbor_array_pos(3, 2, NeighborDirection.HP))


def solve(phi):
    s = Solver()

    s.add(phi)
    c = s.check()
    if c == sat:
        print(s.model())
    elif c == unsat:
        print("unsat")
    else:
        print("That was too hard a problem for me, maybe I should go to IITB")
