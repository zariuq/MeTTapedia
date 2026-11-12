import Mettapedia.Logic.KernelFoundationManifest

/-!
# Enforced dependency audit for the machine-profile mathematics

Inspect every safe declaration by recorded module ownership. Build adapters
and the audit implementation have nonlogical checking roles. Unsafe runtime
counterparts are counted separately and receive no mathematical proof credit.
-/

set_option autoImplicit false

open Lean Elab Command

private def tisaMathematics (name : Name) : Bool :=
  (`Mettapedia.Machines.TIsa).isPrefixOf name &&
    name != `Mettapedia.Machines.TIsa.JsonImport &&
    name != `Mettapedia.Machines.TIsa.P1JsonImport &&
    name != `Mettapedia.Machines.TIsa.ModelImport &&
    name != `Mettapedia.Machines.TIsa.FoundationAudit

elab "#tisa_foundations" : command => do
  let (modules, checked, theorems, nonLogical, compilerOnly) ← liftTermElabM do
    let env ← getEnv
    let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
    let mut modules := 0
    let mut checked := 0
    let mut theorems := 0
    let mut nonLogical := 0
    let mut compilerOnly := 0
    for (name, index) in env.header.moduleNames.toList.zipIdx do
      unless tisaMathematics name do continue
      modules := modules + 1
      let data := env.header.moduleData[index]!
      for declaration in (data.constNames ++ data.extraConstNames).toList.eraseDups do
        let some info := env.checked.get.find? declaration
          | compilerOnly := compilerOnly + 1; continue
        if info.isUnsafe || info.isPartial then
          nonLogical := nonLogical + 1
          continue
        checked := checked + 1
        if info matches .thmInfo _ then theorems := theorems + 1
        for axiomName in ← collectAxioms declaration do
          unless allowed.contains axiomName do
            throwError "unexpected foundation {axiomName} in {declaration}"
    pure (modules, checked, theorems, nonLogical, compilerOnly)
  logInfo (m!"t-ISA foundations: {modules} modules, {checked} safe declarations ({theorems} theorems); " ++
    m!"{nonLogical} nonlogical runtime declarations and {compilerOnly} compiler-only names receive no proof credit. " ++
    m!"All safe dependencies use only propext, Quot.sound and Classical.choice.")
