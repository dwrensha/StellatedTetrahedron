#!/usr/bin/env python3
"""Write the hand-shaped parts of the generated kernel proof (run by gen_kernel.sh):

* `StellatedKernel/T49/*`: corner table 49 (nine nodes on the specification path), split into
  one module per row so that each `decide +kernel` gets a fresh kernel cache;
* `StellatedKernel/Main.lean`: the final theorem, covering every corner case with the
  corresponding table.

Table 49's data file `StellatedKernel/data/corner/T49.slice3` comes from
`kernelCorner slice`.
"""
import hashlib, os

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
os.chdir(ROOT)

tables = {}
for line in open('scripts/kernel_corner_tables.tsv'):
    if line.startswith('#'):
        continue
    i, gen, root, stage = line.rstrip('\n').split('\t')
    tables[int(i)] = (gen, root, stage)

# --- table 49 ---------------------------------------------------------------------------------
data = 'StellatedKernel/data/corner/T49.slice3'
dhash = hashlib.sha256(open(data, 'rb').read()).hexdigest()[:16]
_, root49, stage49 = tables[49]
ns = 'Noperts.Stellated.KernelCorner.T49'
opens = 'open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerKernel\n'
hdr = f'''{opens}
set_option Elab.async false

namespace {ns}

set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
os.makedirs('StellatedKernel/T49', exist_ok=True)
open('StellatedKernel/T49/Data.lean', 'w').write(f'''import Noperts.Stellated.KernelLoad
import Noperts.Stellated.AtlasProjectiveSolutionTree
import Noperts.Stellated.CornerCoverage

{opens}
set_option Elab.async false

namespace {ns}

stellated_corner_chunk "{data}" 0 0 9 n
-- data hash {dhash} (the loaded file is not tracked by Lake)

abbrev H : Handoffs := CornerCoverage.stage AtlasProjectiveSolutionTree.cornerEps {stage49}

noncomputable def t : Table where
  get i := n.getD i (n.getD 0 (Node.split 0 ⟨false, .plain, [], [], []⟩ 0 0 0 0))
  size := 9
  facts := n.facts.toArray
  fpolys := n.fpolys.toArray

end {ns}
''')
for i in range(9):
    open(f'StellatedKernel/T49/R{i}.lean', 'w').write(f'''import StellatedKernel.T49.Data

{hdr}
theorem row{i} : (t.get {i}).id = {i} ∧ (t.get {i}).ValidAt H t.facts t.fpolys t.get t.size := by
  decide +kernel

end {ns}
''')
open('StellatedKernel/T49/Facts.lean', 'w').write(f'''import StellatedKernel.T49.Data

{hdr}
theorem facts_ok : ∀ fact ∈ t.facts, fact.KeyFacts := by decide +kernel

theorem fps_ok : FactPolysOk t.facts t.fpolys := by decide +kernel

end {ns}
''')
rows = '\n'.join(f'import StellatedKernel.T49.R{i}' for i in range(9))
cases = ' '.join(f'| {i}, _ => exact row{i}' for i in range(9))
open('StellatedKernel/T49/Table.lean', 'w').write(f'''import StellatedKernel.T49.Facts
{rows}

{hdr}
theorem t_valid : t.Valid H {root49} := by
  refine ⟨by decide +kernel, by decide +kernel, facts_ok, fps_ok, ?_⟩
  intro ⟨i, hi⟩
  have hs : t.size = 9 := rfl
  rw [hs] at hi
  match i, hi with
  {cases}

theorem table_covered (hH : ∀ h f, H.Valid h f → Covered f) : Covered {root49} :=
  Table.covered H hH t _ t_valid

end {ns}
''')

# --- Main -------------------------------------------------------------------------------------
T = lambda i: f'KernelCorner.T{i}.table_covered hH'
def cases2(n1, n2, f):
    return '\n'.join(f'    · exact {T(f(a, b))}' for a in range(n1) for b in range(n2))
imp = ['import StellatedKernel.Chart.Assembly', 'import StellatedKernel.Local.Assembly',
       'import Noperts.Stellated.IsNotRupert'] + [f'import StellatedKernel.T{i}.Table' for i in sorted(tables)]
nl = '\n'
body = f'''
open Noperts.Stellated Noperts.Stellated.CornerTree Noperts.Stellated.CornerCoverage
open Noperts.Stellated.AtlasProjectiveSolutionTree

set_option Elab.async false

namespace Noperts.Stellated

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every corner case is covered: each field is discharged by its corner table. -/
theorem kernel_cov : Cov cornerEps where
  tpocket face m hH := by
    fin_cases face <;> fin_cases m
{cases2(2, 3, lambda f, m: 77 + 3 * f + m)}
  ppocket k m hH := by
    fin_cases k <;> fin_cases m
{cases2(3, 3, lambda k, m: (71 + 3 * k if k < 2 else 83) + m)}
  spocket m hH := by
    fin_cases m
{cases2(1, 3, lambda _, m: 68 + m)}
  pocket k m hH := by
    fin_cases k <;> fin_cases m
{cases2(3, 3, lambda k, m: 59 + 3 * k + m)}
  cone neg hH := by
    have e : neg = ![neg 0, neg 1, neg 2, neg 3] := by funext i; fin_cases i <;> rfl
    rw [e]
    generalize neg 0 = a; generalize neg 1 = b; generalize neg 2 = c; generalize neg 3 = d
    cases a <;> cases b <;> cases c <;> cases d
{nl.join(f"    · exact {T(43 + a + 2 * b + 4 * c + 8 * d)}" for a in range(2) for b in range(2) for c in range(2) for d in range(2))}
  tube seg face hH := by
    cases seg <;> fin_cases face
{nl.join(f"    · exact {T((18 if s else 0) + 7 + f)}" for s in range(2) for f in range(6))}
  wtube seg face hH := by
    cases seg <;> fin_cases face
{nl.join(f"    · exact {T((18 if s else 0) + 14 + f)}" for s in range(2) for f in range(4))}
  wedge seg hH := by
    cases seg
{nl.join(f"    · exact {T((18 if s else 0) + 13)}" for s in range(2))}
  skew hH := {T(36)}
  zero face hH := by
    fin_cases face
{nl.join(f"    · exact {T(37 + f)}" for f in range(6))}
  plain seg face hH := by
    cases seg <;> fin_cases face
{nl.join(f"    · exact {T((18 if s else 0) + f)}" for s in range(2) for f in range(7))}

theorem kernel_cornerCovered : CornerCovered := kernel_cov.covered

/-- The 11/20 stellated tetrahedron is not Rupert: every step checked by the kernel. -/
theorem stellated_not_rupert_kernel : ¬ IsRupert exactVerts :=
  not_rupert_of_root (ChartK.chart_root LocalK.headers_covered kernel_cornerCovered)

end Noperts.Stellated
'''
open('StellatedKernel/Main.lean', 'w').write('\n'.join(imp) + '\n' + body)
print('wrote StellatedKernel/T49 and StellatedKernel/Main.lean')
