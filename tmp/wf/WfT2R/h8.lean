/-
**WfT2R8: the top theorem with `T2BelowXResV2X` (2026-11-01, t = 2 Bad2 route).**

`trio_terminates_main_V2_baseXR`: `trio_terminates_main_V2_base` (V3TopV2) with `hB : T2BelowXResV2X`; every
consumer of `hB` is the X copy (WfT2R1〜R7), `R2V2` is `R2V2X` (`r2V2_ofXR`) and the drop for `n ≥ 2` is
`T2Drop2X` (`t2Drop2X_of`).
`trio_terminates_main_V2_curXR`: `trio_terminates_main_V2_cur` (V3TopT2B) with `hBX` built by
`WfT2X.t2BelowXResV2X_of` from `WfT2X.T2BelowRV2X` (fields `AbsWNx`・`NotBumpKidX` in place of the false `AbsWN`),
so the hypothesis `T2BadRes` (whose first part `SrcC3Res` is false) is replaced by its second part `T2QNDomBad2`
and `WfT2X.T2BelowRV2X`.
-/
import Ytosk.WfT2R7
