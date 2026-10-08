module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype

namespace Noperts

-- POC (module-system migration): this leaf provides `VertexIndex`, whose
-- constructor/projections and `ofFin90` are reduced by `decide +kernel` in
-- downstream files (e.g. `Vertices/PythonNat.lean`). Those reductions cross a
-- module boundary, so the bodies must be exposed, not merely public.
@[expose] public section

/--
Identifier for a Noperts vertex.
Corresponds to the point at `(-1)^ℓ • Rz(2π k / 15) (C i)`
-/
structure VertexIndex : Type where
  k : Fin 15
  ℓ : Fin 2
  i : Fin 3
deriving Fintype, DecidableEq, Repr, Nonempty

instance instOfNatVertexIndexZero : OfNat VertexIndex 0 where
  ofNat := ⟨0, 0, 0⟩

end

end Noperts
