import Ytosk.V3TopT2B
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut stack : List Name := [`Ytosk.trio_terminates_main_V2_cur]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.getUsedConstantsAsSet.toList do
        if (`Ytosk).isPrefixOf c && !seen.contains c then stack := c :: stack
  IO.println s!"live {seen.size}"
  for n in seen.toList do
    if let some ci := env.find? n then
      let tc := ci.type.getUsedConstantsAsSet
      let isE := tc.contains `Ytosk.ExpStepT1 || tc.contains `Ytosk.ExpStepT1At || tc.contains `Ytosk.ExpStepT1R || tc.contains `Ytosk.HoleData
      let pc := ci.getUsedConstantsAsSet
      let rd := pc.contains `Ytosk.HoleData.S
      if isE || rd then
        let mod := match env.getModuleIdxFor? n with
          | some i => env.header.moduleNames[i.toNat]!.toString
          | none => "?"
        IO.println s!"EXPLIVE {mod} {n} type={isE} readsS={rd}"
