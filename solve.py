from ast import For
from asyncio import constants
from ctypes.wintypes import HPALETTE
from z3 import *
from enum import Enum
from colorama import Fore
from colorama import Style


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
    VP = 1,
    HN = 2,
    VN = 3


class FaceState:
    def __init__(self, cube, face):
        lead_str = "C:"+str(cube)+"F:"+str(face) + "S:"
        self.array = [
            BitVec(lead_str+"0", 3), BitVec(lead_str +
                                            "1", 3), BitVec(lead_str+"2", 3),
            BitVec(lead_str+"3", 3), BitVec(lead_str +
                                            "4", 3), BitVec(lead_str+"5", 3),
            BitVec(lead_str+"6", 3), BitVec(lead_str +
                                            "7", 3), BitVec(lead_str+"8", 3)
        ]

    def get_bits(self, square):
        return self.array[square]


class CubeState:
    def __init__(self, id):
        self.id = id
        self.array = [FaceState(id, 0), FaceState(id, 1), FaceState(id, 2),
                      FaceState(id, 3), FaceState(id, 4), FaceState(id, 5)]

    @staticmethod
    def is_attached(face, pos, neighbor_face):
        if face//2 == neighbor_face//2:
            return False
        neg_face = (face >> 1) << 1
        neg_neighbor_face = (neighbor_face >> 1) << 1
        neighbor_dir = (neighbor_face % 2)*2

        vpos = pos//3
        hpos = pos % 3
        if (neg_neighbor_face+6-neg_face) % 6 == 4:
            return vpos == neighbor_dir
        else:
            return hpos == neighbor_dir

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

    # Rotates positive face anti clockwise and negative face clockwise

    def __rotate_face(self, final_state, face):
        constraints = []
        rotation_map = [2, 5, 8, 1, 4, 7, 0, 3, 6]

        negative_face = (face >> 1) << 1
        face_h_neg = (negative_face+2) % 6
        face_h_pos = (negative_face+3) % 6
        face_v_neg = (negative_face+4) % 6
        face_v_pos = (negative_face+5) % 6

        for i in range(0, 9):
            f_i = rotation_map[i]
            constraints.append(self.array[face].array[i] ==
                               final_state.array[face].array[f_i])
            hn_pos = CubeState.get_neighbor_array_pos(
                face, i, NeighborDirection.HN)
            hp_pos = CubeState.get_neighbor_array_pos(
                face, i, NeighborDirection.HP)
            vn_pos = CubeState.get_neighbor_array_pos(
                face, i, NeighborDirection.VN)
            vp_pos = CubeState.get_neighbor_array_pos(
                face, i, NeighborDirection.VP)

            if hn_pos >= 0:
                nvn_pos = CubeState.get_neighbor_array_pos(
                    face, f_i, NeighborDirection.VN)
                constraints.append(self.array[face_h_neg].array[hn_pos] ==
                                   final_state.array[face_v_neg].array[nvn_pos])
            if vn_pos >= 0:
                nhp_pos = CubeState.get_neighbor_array_pos(
                    face, f_i, NeighborDirection.HP)
                constraints.append(self.array[face_v_neg].array[vn_pos] ==
                                   final_state.array[face_h_pos].array[nhp_pos])
            if hp_pos >= 0:
                nvp_pos = CubeState.get_neighbor_array_pos(
                    face, f_i, NeighborDirection.VP)
                constraints.append(self.array[face_h_pos].array[hp_pos] ==
                                   final_state.array[face_v_pos].array[nvp_pos])

            if vp_pos >= 0:
                nhn_pos = CubeState.get_neighbor_array_pos(
                    face, f_i, NeighborDirection.HN)
                constraints.append(self.array[face_v_pos].array[vp_pos] ==
                                   final_state.array[face_h_neg].array[nhn_pos])

        for f in range(0, 6):
            if f != face:
                for i in range(0, 9):
                    if not CubeState.is_attached(f, i, face):
                        constraints.append(
                            self.array[f].array[i] == final_state.array[f].array[i])
        return And(constraints)

    def __rotate_nothing(self, final_state):
        constraints = []
        for f in range(0, 6):
            for i in range(0, 9):
                constraints.append(
                    self.array[f].array[i] == final_state.array[f].array[i])
        return And(constraints)

    def rotate_face(self, final_state, face, dir):
        if face == 6:
            return self.__rotate_nothing(final_state)
        if dir == 0:
            return self.__rotate_face(final_state, face)
        else:
            return final_state.__rotate_face(self, face)


class CubePath:
    def __init__(self):
        self.states = [CubeState(0)]
        self.moves = []
        self.is_rotated = []
        self.constraints = []

    def add_rotation(self):
        constraints = []
        final_state = CubeState(len(self.states))
        move = BitVec("M:"+str(len(self.moves)), 4)
        rotated = Int("R:"+str(len(self.is_rotated)))
        last_state = self.states[len(self.states)-1]
        self.states.append(final_state)
        self.moves.append(move)
        self.is_rotated.append(rotated)

        constraints.append((rotated >= 0))
        constraints.append(Implies((rotated == 0), move == 12))
        for i in range(0, 13):
            face = i//2
            dir = i % 2
            constraints.append(Implies(move == i,
                               last_state.rotate_face(final_state, face, dir)))
        self.constraints.append(And(constraints))

    def add_n_rotations(self, n):
        for i in range(0, n):
            self.add_rotation()

    def get_constraints(self):
        return And(self.contraints)


class ValueCubeFace:
    def __init__(self, id):
        self.id = id
        self.array = [id, id, id, id, id, id, id, id, id]


class ValueCube:
    def __init__(self):
        self.array = [ValueCubeFace(0), ValueCubeFace(
            1), ValueCubeFace(2), ValueCubeFace(3), ValueCubeFace(4), ValueCubeFace(5)]

    def __rotate_face(self, face, dir):
        if dir == 1:
            return self.__rotate_face(face, 0).__rotate_face(face, 0).__rotate_face(face, 0)

        rotation_map = [2, 5, 8, 1, 4, 7, 0, 3, 6]
        final_state = ValueCube()
        negative_face = (face >> 1) << 1
        face_h_neg = (negative_face+2) % 6
        face_h_pos = (negative_face+3) % 6
        face_v_neg = (negative_face+4) % 6
        face_v_pos = (negative_face+5) % 6

        for i in range(0, 9):

            f_i = rotation_map[i]
            final_state.array[face].array[f_i] = self.array[face].array[i]
            hn_pos = CubeState.get_neighbor_array_pos(
                face, i, NeighborDirection.HN)
            hp_pos = CubeState.get_neighbor_array_pos(
                face, i, NeighborDirection.HP)
            vn_pos = CubeState.get_neighbor_array_pos(
                face, i, NeighborDirection.VN)
            vp_pos = CubeState.get_neighbor_array_pos(
                face, i, NeighborDirection.VP)

            if hn_pos >= 0:
                nvn_pos = CubeState.get_neighbor_array_pos(
                    face, f_i, NeighborDirection.VN)
                final_state.array[face_v_neg].array[nvn_pos] = self.array[face_h_neg].array[hn_pos]
            if vn_pos >= 0:
                nhp_pos = CubeState.get_neighbor_array_pos(
                    face, f_i, NeighborDirection.HP)
                final_state.array[face_h_pos].array[nhp_pos] = self.array[face_v_neg].array[vn_pos]
            if hp_pos >= 0:
                nvp_pos = CubeState.get_neighbor_array_pos(
                    face, f_i, NeighborDirection.VP)
                final_state.array[face_v_pos].array[nvp_pos] = self.array[face_h_pos].array[hp_pos]

            if vp_pos >= 0:
                nhn_pos = CubeState.get_neighbor_array_pos(
                    face, f_i, NeighborDirection.HN)
                final_state.array[face_h_neg].array[nhn_pos] = self.array[face_v_pos].array[vp_pos]

        for f in range(0, 6):
            if f != face:
                for j in range(0, 9):
                    if not CubeState.is_attached(f, j, face):
                        final_state.array[f].array[j] = self.array[f].array[j]
        return final_state

    def rotate_face(self, face, dir):
        if face == 6:
            return self
        if dir == 0:
            return self.__rotate_face(face, dir)
        else:
            return self.__rotate_face(face, dir)

    # Print the cube in human readable format.
    # Positions on a negative face -
    #
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

    @staticmethod
    def get_face_id_index(x, y):
        if (y//3) != 1 and (x//3) != 1:
            return (-1, 0)

        elif (y//3) == 0:
            hpos = 2-y
            vpos = x-3
            face = 4
        elif (y//3) == 3:
            vpos = 11-y
            hpos = x-3
            face = 1
        elif (y//3) == 2:
            hpos = y-6
            vpos = x-3
            face = 5
        elif (x//3) == 0:
            vpos = 2-x
            hpos = y-3
            face = 2
        elif (x//3) == 1 and (y//3) == 1:
            hpos = x-3
            vpos = y-3
            face = 0
        elif (x//3) == 2:
            vpos = x-6
            hpos = y-3
            face = 3

        return (face, vpos*3+hpos)

    def print_index_chart(self):
        colors = [Fore.RED, Fore.LIGHTMAGENTA_EX,
                  Fore.GREEN, Fore.BLUE, Fore.WHITE, Fore.YELLOW]

        for x in range(0, 3):
            print("   ", end="")
        for x in range(3, 6):
            print("--", end="")
        print("-", end="")
        for y in range(0, 12):
            print("")

            for x in range(0, 9):
                if x % 3 == 0 and (x > 0 or y > 2 and y < 6):
                    print("| ", end="")
                elif x == 0:
                    print("  ", end="")
                (face, index) = ValueCube.get_face_id_index(x, y)
                if face >= 0:
                    color = colors[self.array[face].array[index]]

                    print(f"{color}{index}{Fore.RESET}", end=" ")
                else:
                    print(" ", end=" ")
                if y >= 3 and y < 6 and x >= 8:
                    print("|", end=" ")
            if y % 3 == 2:
                print("")
                for x in range(0, 9):
                    if x % 3 == 0 and (x//3 == 1 or y < 6):
                        print(" -", end="")
                    elif x % 3 == 0:
                        print("  ", end="")
                    (face, index) = ValueCube.get_face_id_index(x, y)
                    if y < 6 or (x//3) % 3 == 1:
                        print("-", end="-")
                    else:
                        print(" ", end=" ")

    def print_cube(self):
        self.print_index_chart()


# b1 = Bool("b1")
# b2 = Bool("b2")
# x = Int("x")
# y = Int("y")
# solver = Solver()
# cond1 = Implies(x < y, b1)
# cond2 = Implies(x > y, b2)
# phi = And(cond1, cond2, Or(b1, b2), x >= 0, y > 0)
# minimize(phi, x)

# cubepath = CubePath()
# cubepath.add_n_rotations(10)

ValueCube().rotate_face(0, 0).rotate_face(2, 1).print_index_chart()


# print(CubeState.get_neighbor_array_pos(0, 2, NeighborDirection.HN))
# print(CubeState.get_neighbor_array_pos(0, 8, NeighborDirection.VP))
# print(CubeState.get_neighbor_array_pos(3, 8, NeighborDirection.VP))
# print(CubeState.get_neighbor_array_pos(3, 2, NeighborDirection.HP))

print(CubeState.is_attached(1, 8, 3))


def solve(phi):
    s = Solver()

    s.append(phi)
    c = s.check()
    if c == sat:
        print(s.model())
    elif c == unsat:
        print("unsat")
    else:
        print("That was too hard a problem for me, maybe I should go to IITB")
