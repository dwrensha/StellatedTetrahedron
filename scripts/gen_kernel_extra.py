#!/usr/bin/env python3
"""Write corner table 49 of the generated kernel proof (run by gen_kernel.sh):

* `StellatedKernel/T49/*`: corner table 49 (nine nodes on the specification path), split into
  one module per row so that each `decide +kernel` gets a fresh kernel cache;

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
print('wrote StellatedKernel/T49')
