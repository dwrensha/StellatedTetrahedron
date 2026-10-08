module

public import Noperts.Stellated.Vertices

@[expose] public section

/-!
# The octahedral rotations and the stellated tetrahedron

The 24 rotation matrices that are signed permutations form the octahedral
rotation group `O`.  Indices `0..11` form the tetrahedral subgroup `T`,
which maps the solid onto itself; indices `12..23` form the coset `O \ T`,
each of which maps the solid onto its negative.  Index `0` is the identity
and indices `1,2,3` are the diagonal half-turns used as Cayley charts.

Everything here is exact rational data checked by `decide`.
-/

namespace Noperts.Stellated

open scoped Matrix

abbrev SymIndex := Fin 24

/-- Whether a symmetry lies in the coset `O \ T` (and so negates the solid). -/
def isFlip (g : SymIndex) : Bool := 12 ≤ g.val

/-- `+1` on `T`, `-1` on `O \ T`. -/
def symSign (g : SymIndex) : ℚ := if isFlip g then -1 else 1

def symMatrix : SymIndex → Matrix (Fin 3) (Fin 3) ℚ := ![
  !![1, 0, 0; 0, 1, 0; 0, 0, 1],
  !![1, 0, 0; 0, -1, 0; 0, 0, -1],
  !![-1, 0, 0; 0, 1, 0; 0, 0, -1],
  !![-1, 0, 0; 0, -1, 0; 0, 0, 1],
  !![0, 1, 0; 0, 0, 1; 1, 0, 0],
  !![0, 1, 0; 0, 0, -1; -1, 0, 0],
  !![0, -1, 0; 0, 0, 1; -1, 0, 0],
  !![0, -1, 0; 0, 0, -1; 1, 0, 0],
  !![0, 0, 1; 1, 0, 0; 0, 1, 0],
  !![0, 0, 1; -1, 0, 0; 0, -1, 0],
  !![0, 0, -1; 1, 0, 0; 0, -1, 0],
  !![0, 0, -1; -1, 0, 0; 0, 1, 0],
  !![1, 0, 0; 0, 0, 1; 0, -1, 0],
  !![1, 0, 0; 0, 0, -1; 0, 1, 0],
  !![-1, 0, 0; 0, 0, 1; 0, 1, 0],
  !![-1, 0, 0; 0, 0, -1; 0, -1, 0],
  !![0, 1, 0; 1, 0, 0; 0, 0, -1],
  !![0, 1, 0; -1, 0, 0; 0, 0, 1],
  !![0, -1, 0; 1, 0, 0; 0, 0, 1],
  !![0, -1, 0; -1, 0, 0; 0, 0, -1],
  !![0, 0, 1; 0, 1, 0; -1, 0, 0],
  !![0, 0, 1; 0, -1, 0; 1, 0, 0],
  !![0, 0, -1; 0, 1, 0; 1, 0, 0],
  !![0, 0, -1; 0, -1, 0; -1, 0, 0]]

def symAction : SymIndex → VertexIndex → VertexIndex := ![
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![1, 0, 3, 2, 5, 4, 7, 6],
  ![2, 3, 0, 1, 6, 7, 4, 5],
  ![3, 2, 1, 0, 7, 6, 5, 4],
  ![0, 3, 1, 2, 4, 7, 5, 6],
  ![1, 2, 0, 3, 5, 6, 4, 7],
  ![2, 1, 3, 0, 6, 5, 7, 4],
  ![3, 0, 2, 1, 7, 4, 6, 5],
  ![0, 2, 3, 1, 4, 6, 7, 5],
  ![1, 3, 2, 0, 5, 7, 6, 4],
  ![2, 0, 1, 3, 6, 4, 5, 7],
  ![3, 1, 0, 2, 7, 5, 4, 6],
  ![3, 2, 0, 1, 7, 6, 4, 5],
  ![2, 3, 1, 0, 6, 7, 5, 4],
  ![1, 0, 2, 3, 5, 4, 6, 7],
  ![0, 1, 3, 2, 4, 5, 7, 6],
  ![3, 1, 2, 0, 7, 5, 6, 4],
  ![2, 0, 3, 1, 6, 4, 7, 5],
  ![1, 3, 0, 2, 5, 7, 4, 6],
  ![0, 2, 1, 3, 4, 6, 5, 7],
  ![3, 0, 1, 2, 7, 4, 5, 6],
  ![2, 1, 0, 3, 6, 5, 4, 7],
  ![1, 2, 3, 0, 5, 6, 7, 4],
  ![0, 3, 2, 1, 4, 7, 6, 5]]

def symMul : SymIndex → SymIndex → SymIndex := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22],
  ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21],
  ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20],
  ![4, 7, 5, 6, 8, 11, 9, 10, 0, 3, 1, 2, 21, 22, 20, 23, 13, 14, 12, 15, 17, 18, 16, 19],
  ![5, 6, 4, 7, 9, 10, 8, 11, 1, 2, 0, 3, 20, 23, 21, 22, 12, 15, 13, 14, 16, 19, 17, 18],
  ![6, 5, 7, 4, 10, 9, 11, 8, 2, 1, 3, 0, 23, 20, 22, 21, 15, 12, 14, 13, 19, 16, 18, 17],
  ![7, 4, 6, 5, 11, 8, 10, 9, 3, 0, 2, 1, 22, 21, 23, 20, 14, 13, 15, 12, 18, 17, 19, 16],
  ![8, 10, 11, 9, 0, 2, 3, 1, 4, 6, 7, 5, 18, 16, 17, 19, 22, 20, 21, 23, 14, 12, 13, 15],
  ![9, 11, 10, 8, 1, 3, 2, 0, 5, 7, 6, 4, 19, 17, 16, 18, 23, 21, 20, 22, 15, 13, 12, 14],
  ![10, 8, 9, 11, 2, 0, 1, 3, 6, 4, 5, 7, 16, 18, 19, 17, 20, 22, 23, 21, 12, 14, 15, 13],
  ![11, 9, 8, 10, 3, 1, 0, 2, 7, 5, 4, 6, 17, 19, 18, 16, 21, 23, 22, 20, 13, 15, 14, 12],
  ![12, 13, 15, 14, 16, 17, 19, 18, 20, 21, 23, 22, 1, 0, 2, 3, 5, 4, 6, 7, 9, 8, 10, 11],
  ![13, 12, 14, 15, 17, 16, 18, 19, 21, 20, 22, 23, 0, 1, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10],
  ![14, 15, 13, 12, 18, 19, 17, 16, 22, 23, 21, 20, 3, 2, 0, 1, 7, 6, 4, 5, 11, 10, 8, 9],
  ![15, 14, 12, 13, 19, 18, 16, 17, 23, 22, 20, 21, 2, 3, 1, 0, 6, 7, 5, 4, 10, 11, 9, 8],
  ![16, 18, 17, 19, 20, 22, 21, 23, 12, 14, 13, 15, 8, 10, 9, 11, 0, 2, 1, 3, 4, 6, 5, 7],
  ![17, 19, 16, 18, 21, 23, 20, 22, 13, 15, 12, 14, 9, 11, 8, 10, 1, 3, 0, 2, 5, 7, 4, 6],
  ![18, 16, 19, 17, 22, 20, 23, 21, 14, 12, 15, 13, 10, 8, 11, 9, 2, 0, 3, 1, 6, 4, 7, 5],
  ![19, 17, 18, 16, 23, 21, 22, 20, 15, 13, 14, 12, 11, 9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4],
  ![20, 23, 22, 21, 12, 15, 14, 13, 16, 19, 18, 17, 6, 5, 4, 7, 10, 9, 8, 11, 2, 1, 0, 3],
  ![21, 22, 23, 20, 13, 14, 15, 12, 17, 18, 19, 16, 7, 4, 5, 6, 11, 8, 9, 10, 3, 0, 1, 2],
  ![22, 21, 20, 23, 14, 13, 12, 15, 18, 17, 16, 19, 4, 7, 6, 5, 8, 11, 10, 9, 0, 3, 2, 1],
  ![23, 20, 21, 22, 15, 12, 13, 14, 19, 16, 17, 18, 5, 6, 7, 4, 9, 10, 11, 8, 1, 2, 3, 0]]

/-! Explicit forms, for `simp`. -/

theorem symMatrix_0 : symMatrix 0 = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := rfl

theorem symMatrix_1 : symMatrix 1 = !![1, 0, 0; 0, -1, 0; 0, 0, -1] := rfl

theorem symMatrix_2 : symMatrix 2 = !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := rfl

theorem symMatrix_3 : symMatrix 3 = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := rfl

theorem symMatrix_4 : symMatrix 4 = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := rfl

theorem symMatrix_5 : symMatrix 5 = !![0, 1, 0; 0, 0, -1; -1, 0, 0] := rfl

theorem symMatrix_6 : symMatrix 6 = !![0, -1, 0; 0, 0, 1; -1, 0, 0] := rfl

theorem symMatrix_7 : symMatrix 7 = !![0, -1, 0; 0, 0, -1; 1, 0, 0] := rfl

theorem symMatrix_8 : symMatrix 8 = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl

theorem symMatrix_9 : symMatrix 9 = !![0, 0, 1; -1, 0, 0; 0, -1, 0] := rfl

theorem symMatrix_10 : symMatrix 10 = !![0, 0, -1; 1, 0, 0; 0, -1, 0] := rfl

theorem symMatrix_11 : symMatrix 11 = !![0, 0, -1; -1, 0, 0; 0, 1, 0] := rfl

theorem symMatrix_12 : symMatrix 12 = !![1, 0, 0; 0, 0, 1; 0, -1, 0] := rfl

theorem symMatrix_13 : symMatrix 13 = !![1, 0, 0; 0, 0, -1; 0, 1, 0] := rfl

theorem symMatrix_14 : symMatrix 14 = !![-1, 0, 0; 0, 0, 1; 0, 1, 0] := rfl

theorem symMatrix_15 : symMatrix 15 = !![-1, 0, 0; 0, 0, -1; 0, -1, 0] := rfl

theorem symMatrix_16 : symMatrix 16 = !![0, 1, 0; 1, 0, 0; 0, 0, -1] := rfl

theorem symMatrix_17 : symMatrix 17 = !![0, 1, 0; -1, 0, 0; 0, 0, 1] := rfl

theorem symMatrix_18 : symMatrix 18 = !![0, -1, 0; 1, 0, 0; 0, 0, 1] := rfl

theorem symMatrix_19 : symMatrix 19 = !![0, -1, 0; -1, 0, 0; 0, 0, -1] := rfl

theorem symMatrix_20 : symMatrix 20 = !![0, 0, 1; 0, 1, 0; -1, 0, 0] := rfl

theorem symMatrix_21 : symMatrix 21 = !![0, 0, 1; 0, -1, 0; 1, 0, 0] := rfl

theorem symMatrix_22 : symMatrix 22 = !![0, 0, -1; 0, 1, 0; 1, 0, 0] := rfl

theorem symMatrix_23 : symMatrix 23 = !![0, 0, -1; 0, -1, 0; -1, 0, 0] := rfl

theorem symMatrix_mulVec_rationalVertex :
    ∀ g i, symMatrix g *ᵥ rationalVertex i =
      symSign g • rationalVertex (symAction g i) := by
  decide +kernel

theorem symMatrix_mul :
    ∀ g h, symMatrix g * symMatrix h = symMatrix (symMul g h) := by
  decide +kernel

theorem isFlip_symMul :
    ∀ g h, isFlip (symMul g h) = (isFlip g ^^ isFlip h) := by
  decide +kernel

theorem symMatrix_mul_transpose :
    ∀ g, symMatrix g * (symMatrix g)ᵀ = 1 := by
  decide +kernel

theorem symMatrix_det (g : SymIndex) : (symMatrix g).det = 1 := by
  rw [Matrix.det_fin_three]
  revert g
  decide +kernel

end Noperts.Stellated

end
