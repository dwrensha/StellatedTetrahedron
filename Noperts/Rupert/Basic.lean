module

public import Noperts.EuclideanSpaceNotation
public import Noperts.MainTheorem

@[expose] public section


abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

end
