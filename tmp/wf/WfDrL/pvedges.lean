import Ytosk.V3TopT2B
import Ytosk.V3T2AbsNWeak
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let isPV : Name → Bool := fun n => match env.find? n with
    | some ci => let tc := ci.type.getUsedConstantsAsSet
        tc.contains `Ytosk.PV || tc.contains `Ytosk.WeakCS || tc.contains `Ytosk.WCSP
    | none => false
  for (n, ci) in env.constants.toList do
    if (`Ytosk).isPrefixOf n && isPV n && !n.isInternal then
      let deps := ci.getUsedConstantsAsSet.toList.filter (fun c => c != n && isPV c)
      let mod := match env.getModuleIdxFor? n with
        | some i => env.header.moduleNames[i.toNat]!.toString
        | none => "?"
      IO.println s!"E {mod} {n} {deps}"
