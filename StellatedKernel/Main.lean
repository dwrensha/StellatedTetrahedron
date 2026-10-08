import StellatedKernel.Chart.Assembly
import StellatedKernel.Local.Assembly
import Noperts.Stellated.IsNotRupert
import StellatedKernel.T0.Table
import StellatedKernel.T1.Table
import StellatedKernel.T2.Table
import StellatedKernel.T3.Table
import StellatedKernel.T4.Table
import StellatedKernel.T5.Table
import StellatedKernel.T6.Table
import StellatedKernel.T7.Table
import StellatedKernel.T8.Table
import StellatedKernel.T9.Table
import StellatedKernel.T10.Table
import StellatedKernel.T11.Table
import StellatedKernel.T12.Table
import StellatedKernel.T13.Table
import StellatedKernel.T14.Table
import StellatedKernel.T15.Table
import StellatedKernel.T16.Table
import StellatedKernel.T17.Table
import StellatedKernel.T18.Table
import StellatedKernel.T19.Table
import StellatedKernel.T20.Table
import StellatedKernel.T21.Table
import StellatedKernel.T22.Table
import StellatedKernel.T23.Table
import StellatedKernel.T24.Table
import StellatedKernel.T25.Table
import StellatedKernel.T26.Table
import StellatedKernel.T27.Table
import StellatedKernel.T28.Table
import StellatedKernel.T29.Table
import StellatedKernel.T30.Table
import StellatedKernel.T31.Table
import StellatedKernel.T32.Table
import StellatedKernel.T33.Table
import StellatedKernel.T34.Table
import StellatedKernel.T35.Table
import StellatedKernel.T36.Table
import StellatedKernel.T37.Table
import StellatedKernel.T38.Table
import StellatedKernel.T39.Table
import StellatedKernel.T40.Table
import StellatedKernel.T41.Table
import StellatedKernel.T42.Table
import StellatedKernel.T43.Table
import StellatedKernel.T44.Table
import StellatedKernel.T45.Table
import StellatedKernel.T46.Table
import StellatedKernel.T47.Table
import StellatedKernel.T48.Table
import StellatedKernel.T49.Table
import StellatedKernel.T50.Table
import StellatedKernel.T51.Table
import StellatedKernel.T52.Table
import StellatedKernel.T53.Table
import StellatedKernel.T54.Table
import StellatedKernel.T55.Table
import StellatedKernel.T56.Table
import StellatedKernel.T57.Table
import StellatedKernel.T58.Table
import StellatedKernel.T59.Table
import StellatedKernel.T60.Table
import StellatedKernel.T61.Table
import StellatedKernel.T62.Table
import StellatedKernel.T63.Table
import StellatedKernel.T64.Table
import StellatedKernel.T65.Table
import StellatedKernel.T66.Table
import StellatedKernel.T67.Table
import StellatedKernel.T68.Table
import StellatedKernel.T69.Table
import StellatedKernel.T70.Table
import StellatedKernel.T71.Table
import StellatedKernel.T72.Table
import StellatedKernel.T73.Table
import StellatedKernel.T74.Table
import StellatedKernel.T75.Table
import StellatedKernel.T76.Table
import StellatedKernel.T77.Table
import StellatedKernel.T78.Table
import StellatedKernel.T79.Table
import StellatedKernel.T80.Table
import StellatedKernel.T81.Table
import StellatedKernel.T82.Table
import StellatedKernel.T83.Table
import StellatedKernel.T84.Table
import StellatedKernel.T85.Table

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
    · exact KernelCorner.T77.table_covered hH
    · exact KernelCorner.T78.table_covered hH
    · exact KernelCorner.T79.table_covered hH
    · exact KernelCorner.T80.table_covered hH
    · exact KernelCorner.T81.table_covered hH
    · exact KernelCorner.T82.table_covered hH
  ppocket k m hH := by
    fin_cases k <;> fin_cases m
    · exact KernelCorner.T71.table_covered hH
    · exact KernelCorner.T72.table_covered hH
    · exact KernelCorner.T73.table_covered hH
    · exact KernelCorner.T74.table_covered hH
    · exact KernelCorner.T75.table_covered hH
    · exact KernelCorner.T76.table_covered hH
    · exact KernelCorner.T83.table_covered hH
    · exact KernelCorner.T84.table_covered hH
    · exact KernelCorner.T85.table_covered hH
  spocket m hH := by
    fin_cases m
    · exact KernelCorner.T68.table_covered hH
    · exact KernelCorner.T69.table_covered hH
    · exact KernelCorner.T70.table_covered hH
  pocket k m hH := by
    fin_cases k <;> fin_cases m
    · exact KernelCorner.T59.table_covered hH
    · exact KernelCorner.T60.table_covered hH
    · exact KernelCorner.T61.table_covered hH
    · exact KernelCorner.T62.table_covered hH
    · exact KernelCorner.T63.table_covered hH
    · exact KernelCorner.T64.table_covered hH
    · exact KernelCorner.T65.table_covered hH
    · exact KernelCorner.T66.table_covered hH
    · exact KernelCorner.T67.table_covered hH
  cone neg hH := by
    have e : neg = ![neg 0, neg 1, neg 2, neg 3] := by funext i; fin_cases i <;> rfl
    rw [e]
    generalize neg 0 = a; generalize neg 1 = b; generalize neg 2 = c; generalize neg 3 = d
    cases a <;> cases b <;> cases c <;> cases d
    · exact KernelCorner.T43.table_covered hH
    · exact KernelCorner.T51.table_covered hH
    · exact KernelCorner.T47.table_covered hH
    · exact KernelCorner.T55.table_covered hH
    · exact KernelCorner.T45.table_covered hH
    · exact KernelCorner.T53.table_covered hH
    · exact KernelCorner.T49.table_covered hH
    · exact KernelCorner.T57.table_covered hH
    · exact KernelCorner.T44.table_covered hH
    · exact KernelCorner.T52.table_covered hH
    · exact KernelCorner.T48.table_covered hH
    · exact KernelCorner.T56.table_covered hH
    · exact KernelCorner.T46.table_covered hH
    · exact KernelCorner.T54.table_covered hH
    · exact KernelCorner.T50.table_covered hH
    · exact KernelCorner.T58.table_covered hH
  tube seg face hH := by
    cases seg <;> fin_cases face
    · exact KernelCorner.T7.table_covered hH
    · exact KernelCorner.T8.table_covered hH
    · exact KernelCorner.T9.table_covered hH
    · exact KernelCorner.T10.table_covered hH
    · exact KernelCorner.T11.table_covered hH
    · exact KernelCorner.T12.table_covered hH
    · exact KernelCorner.T25.table_covered hH
    · exact KernelCorner.T26.table_covered hH
    · exact KernelCorner.T27.table_covered hH
    · exact KernelCorner.T28.table_covered hH
    · exact KernelCorner.T29.table_covered hH
    · exact KernelCorner.T30.table_covered hH
  wtube seg face hH := by
    cases seg <;> fin_cases face
    · exact KernelCorner.T14.table_covered hH
    · exact KernelCorner.T15.table_covered hH
    · exact KernelCorner.T16.table_covered hH
    · exact KernelCorner.T17.table_covered hH
    · exact KernelCorner.T32.table_covered hH
    · exact KernelCorner.T33.table_covered hH
    · exact KernelCorner.T34.table_covered hH
    · exact KernelCorner.T35.table_covered hH
  wedge seg hH := by
    cases seg
    · exact KernelCorner.T13.table_covered hH
    · exact KernelCorner.T31.table_covered hH
  skew hH := KernelCorner.T36.table_covered hH
  zero face hH := by
    fin_cases face
    · exact KernelCorner.T37.table_covered hH
    · exact KernelCorner.T38.table_covered hH
    · exact KernelCorner.T39.table_covered hH
    · exact KernelCorner.T40.table_covered hH
    · exact KernelCorner.T41.table_covered hH
    · exact KernelCorner.T42.table_covered hH
  plain seg face hH := by
    cases seg <;> fin_cases face
    · exact KernelCorner.T0.table_covered hH
    · exact KernelCorner.T1.table_covered hH
    · exact KernelCorner.T2.table_covered hH
    · exact KernelCorner.T3.table_covered hH
    · exact KernelCorner.T4.table_covered hH
    · exact KernelCorner.T5.table_covered hH
    · exact KernelCorner.T6.table_covered hH
    · exact KernelCorner.T18.table_covered hH
    · exact KernelCorner.T19.table_covered hH
    · exact KernelCorner.T20.table_covered hH
    · exact KernelCorner.T21.table_covered hH
    · exact KernelCorner.T22.table_covered hH
    · exact KernelCorner.T23.table_covered hH
    · exact KernelCorner.T24.table_covered hH

theorem kernel_cornerCovered : CornerCovered := kernel_cov.covered

/-- The 11/20 stellated tetrahedron is not Rupert: every step checked by the kernel. -/
theorem stellated_not_rupert_kernel : ¬ IsRupert exactVerts :=
  not_rupert_of_root (ChartK.chart_root LocalK.headers_covered kernel_cornerCovered)

end Noperts.Stellated
