import Mettapedia.InformationTheory.ShannonEntropy.Main
import Lean.Util.CollectAxioms

/-!
# Faddeev Proof Qualification

Run from the Lean project root after building
`Mettapedia.InformationTheory.ShannonEntropy.Main`:

```
lake env lean scripts/check_faddeev_axioms.lean
```

This checks the public theorem types, concrete entropy controls and transitive
axioms of every kernel declaration in the finite entropy characterization chain.
It includes the canonical standalone proof, so an imported admission cannot pass
merely because Mettapedia's own sources contain no proof placeholders.
-/

namespace FaddeevQualification

open Mettapedia.InformationTheory
open Lean Elab Command

/-- The normalization remains one bit for the fair coin. -/
example (E : FaddeevEntropy) : E.H binaryUniform = 1 := E.normalization

/-- The adapter must preserve entropy at every arity. -/
example (E : FaddeevEntropy) {n : ℕ} (p : ProbVec n) :
    E.toStandalone.H p = E.H p := E.toStandalone_H p

/-- The original all-primes theorem remains unconditional. -/
example (E : FaddeevEntropy) (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    c_prime E p hp = c_prime E q hq := faddeev_c_prime_all_equal E p q hp hq

/-- The original full uniqueness theorem retains its probability-vector interface. -/
example (E : FaddeevEntropy) {n : ℕ} (p : ProbVec n) :
    E.H p = shannonEntropyNormalized p := faddeev_H_eq_shannon E p

/-- Independent prime assignments cannot make ternary uniform entropy zero. -/
example (E : FaddeevEntropy) : E.H (uniformDist 3 (by decide)) ≠ 0 := by
  have h := faddeev_F_eq_log2 E (n := 3) (by decide)
  change E.H (uniformDist 3 (by decide)) = Real.log 3 / Real.log 2 at h
  rw [h]
  exact ne_of_gt (div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num)))

/-- Prime factors of p^k-1 need not be smaller than p. -/
example : Nat.Prime 13 ∧ 13 ∣ (3 ^ 3 - 1) ∧ ¬ (13 < 3) := by norm_num

private def unexpectedAxioms (declName : Name) : CoreM (Array Name) := do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  return (← collectAxioms declName).filter fun dependency => !allowed.contains dependency

run_cmd do
  -- Exercise the same rejection predicate used for every audited declaration.
  -- This refers to the existing kernel admission primitive; it introduces no axiom.
  let rejected ← liftCoreM <| unexpectedAxioms ``sorryAx
  unless rejected.contains ``sorryAx do
    throwError "negative control failed: admitted proofs would pass the audit"
  logInfo "NEGATIVE_CONTROL: sorryAx rejected"

  let modules := #[
    `InformationTheory.Basic,
    `InformationTheory.ShannonEntropy.Properties,
    `InformationTheory.ShannonEntropy.Faddeev,
    `Mettapedia.InformationTheory.Basic,
    `Mettapedia.InformationTheory.ShannonEntropy.Properties,
    `Mettapedia.InformationTheory.ShannonEntropy.Faddeev,
    `Mettapedia.InformationTheory.ShannonEntropy.Shannon1948,
    `Mettapedia.InformationTheory.ShannonEntropy.ShannonKhinchin,
    `Mettapedia.InformationTheory.ShannonEntropy.Interface,
    `Mettapedia.InformationTheory.ShannonEntropy.Equivalence,
    `Mettapedia.InformationTheory.ShannonEntropy.MeasureTheoreticBridge,
    `Mettapedia.InformationTheory.ShannonEntropy.Main
  ]
  let env ← getEnv
  let mut total := 0
  let mut compilerOnly := 0
  for moduleName in modules do
    let some moduleIndex := env.header.moduleNames.toList.idxOf? moduleName
      | throwError "missing audited module {moduleName}"
    let moduleData := env.header.moduleData[moduleIndex]!
    let names := (moduleData.constNames ++ moduleData.extraConstNames).toList.eraseDups
    let mut checked := 0
    for declName in names do
      let some info := env.checked.get.find? declName | do
        unless moduleData.extraConstNames.contains declName do
          throwError "unavailable kernel declaration {declName}"
        compilerOnly := compilerOnly + 1
        logInfo m!"COMPILER_ONLY: {declName}"
        continue
      if info matches .axiomInfo _ then
        throwError "owned axiom declaration {declName}"
      if info.isUnsafe || info.isPartial then
        throwError "unsafe or partial declaration {declName}"
      let unexpected ← liftCoreM <| unexpectedAxioms declName
      unless unexpected.isEmpty do
        throwError "unexpected transitive axioms for {declName}: {unexpected.toList}"
      checked := checked + 1
    if !names.isEmpty && checked == 0 then
      throwError "no kernel declarations checked in {moduleName}"
    total := total + checked
    logInfo m!"AUDIT: {moduleName}; {checked} kernel declarations"
  logInfo m!"QUALIFIED: {modules.size} modules; {total} kernel declarations; {compilerOnly} compiler-only entries; allowed axioms: propext, Classical.choice, Quot.sound"

end FaddeevQualification
