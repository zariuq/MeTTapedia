import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Formula

/-!
# Petri Net OSLF Instance

Third example instantiation of the OSLF pipeline. A binder-free language
validating that multiset (bag) matching works correctly without any
abstraction or substitution machinery.

## Petri Net

A simple Petri net with four places (A, B, C, D) and two transitions:

```
        T1: {A, B} → {C, D}       T2: {C} → {A}
```

Markings are multisets of place-tokens. A transition fires by consuming
tokens from input places and producing tokens at output places. The
`rest` variable captures remaining tokens unchanged.

## Pipeline

```
petriNet : LanguageDef
    ↓ langRewriteSystem
petriRS : RewriteSystem
    ↓ langSpan
petriSpan : ReductionSpan
    ↓ langOSLF
petriOSLF : OSLFTypeSystem  (with proven Galois connection)
```

## Why This Language Matters

- **No binders**: validates bag matching without substitution/alpha issues
- **Multiple transitions**: tests non-deterministic choice
- **Multiplicity-sensitive**: {A, A, B} can fire T1 once, leaving {A, C, D}
- **Reachability reasoning**: demonstrates ◇/□ for marking reachability

## References

- Petri, "Kommunikation mit Automaten" (1962)
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF.Framework.PetriNetInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Formula

/-! ## Language Definition -/

/-- A simple Petri net with four places and two transitions.

    - **Types**: `["Marking"]`
    - **Places**: `A`, `B`, `C`, `D` (nullary constructors)
    - **Transitions**:
      - `T1`: `{A | B | rest} ~> {C | D | rest}` (consume A+B, produce C+D)
      - `T2`: `{C | rest} ~> {A | rest}` (consume C, produce A)

    Markings are represented as hash-bags of place tokens. -/
def petriNet : LanguageDef := {
  name := "PetriNet",
  types := ["Marking"],
  terms := [
    -- Place A (nullary token)
    { label := "A", category := "Marking", params := [],
      syntaxPattern := [.terminal "A"] },
    -- Place B
    { label := "B", category := "Marking", params := [],
      syntaxPattern := [.terminal "B"] },
    -- Place C
    { label := "C", category := "Marking", params := [],
      syntaxPattern := [.terminal "C"] },
    -- Place D
    { label := "D", category := "Marking", params := [],
      syntaxPattern := [.terminal "D"] }
  ],
  equations := [],
  rewrites := [
    -- T1: {A | B | rest} ~> {C | D | rest}
    { name := "T1",
      typeContext := [],
      premises := [],
      left := .collection .hashBag [.apply "A" [], .apply "B" []] (some "rest"),
      right := .collection .hashBag [.apply "C" [], .apply "D" []] (some "rest") },
    -- T2: {C | rest} ~> {A | rest}
    { name := "T2",
      typeContext := [],
      premises := [],
      left := .collection .hashBag [.apply "C" []] (some "rest"),
      right := .collection .hashBag [.apply "A" []] (some "rest") }
  ]
}

/-! ## OSLF Pipeline Instantiation -/

/-- The OSLF type system for the Petri net.
    Galois connection ◇ ⊣ □ is proven automatically. -/
def petriOSLF := langOSLF petriNet "Marking"

/-- The Galois connection for the Petri net. -/
theorem petriGalois :
    GaloisConnection (langDiamond petriNet) (langBox petriNet) :=
  langGalois petriNet

/-! ## Helper Constructors -/

/-- Token at place A -/
private def tokA : Pattern := .apply "A" []

/-- Token at place B -/
private def tokB : Pattern := .apply "B" []

/-- Token at place C -/
private def tokC : Pattern := .apply "C" []

/-- Token at place D -/
private def tokD : Pattern := .apply "D" []

/-- Marking: bag of tokens -/
private def marking (tokens : List Pattern) : Pattern :=
  .collection .hashBag tokens none

/-- Simple display for Petri net markings -/
private def markingToString : Pattern → String
  | .apply "A" [] => "A"
  | .apply "B" [] => "B"
  | .apply "C" [] => "C"
  | .apply "D" [] => "D"
  | .collection .hashBag elems _ =>
    "{" ++ String.intercalate ", " (elems.map markingToString) ++ "}"
  | p => repr p |>.pretty

private instance : ToString Pattern := ⟨markingToString⟩

/-! ## Executable Demos -/

-- Demo 1: Fire T1 on [A, B] → [C, D]
#eval! do
  let m := marking [tokA, tokB]
  let reducts := rewriteWithContext petriNet m
  IO.println ("Demo 1: Fire T1 on {A, B}")
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 2: [A, A, B] — T1 fires, consuming one A and one B
-- Non-deterministic: which A is consumed?
#eval! do
  let m := marking [tokA, tokA, tokB]
  let reducts := rewriteWithContext petriNet m
  IO.println ("Demo 2: Fire on {A, A, B}")
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 3: [C] — only T2 fires: [C] → [A]
#eval! do
  let m := marking [tokC]
  let reducts := rewriteWithContext petriNet m
  IO.println ("Demo 3: Fire on {C}")
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 4: Multi-step: [A, B] →* (T1 then T2 on C)
#eval! do
  let m := marking [tokA, tokB]
  let nf := fullRewriteToNormalForm petriNet m 100
  IO.println ("Demo 4: Multi-step from {A, B}")
  IO.println s!"  normal form: {nf}"

-- Demo 5: [D] is a dead marking — nothing can fire
#eval! do
  let m := marking [tokD]
  let reducts := rewriteWithContext petriNet m
  IO.println ("Demo 5: {D} is dead")
  IO.println s!"  reducts ({reducts.length}): expected 0"
  assert! reducts.isEmpty

-- Demo 6: Formula — can [A, B] reduce? (◇⊤ should be sat)
#eval! do
  let m := marking [tokA, tokB]
  let noAtoms : AtomCheck := fun _ _ => false
  let result := check (rewriteWithContext petriNet) noAtoms 50 m (.dia .top)
  IO.println ("Demo 6: Can {A, B} reduce?")
  IO.println s!"  check (◇⊤) = {result}"

-- Demo 7: Formula — can [D] reduce? (◇⊤ should be unsat)
#eval! do
  let m := marking [tokD]
  let noAtoms : AtomCheck := fun _ _ => false
  let result := check (rewriteWithContext petriNet) noAtoms 50 m (.dia .top)
  IO.println ("Demo 7: Can {D} reduce?")
  IO.println s!"  check (◇⊤) = {result}"

-- Demo 8: Non-determinism — [A, B, C] has both T1 and T2 applicable
#eval! do
  let m := marking [tokA, tokB, tokC]
  let reducts := rewriteWithContext petriNet m
  IO.println ("Demo 8: {A, B, C} — both transitions applicable")
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

/-! ## Structural Theorems -/

/-- Place tokens are pairwise distinct. -/
theorem A_ne_B : tokA ≠ tokB := by decide
theorem A_ne_C : tokA ≠ tokC := by decide
theorem C_ne_D : tokC ≠ tokD := by decide

/-- {D} is a dead marking: no transition matches (proven via negation). -/
theorem D_is_dead : rewriteWithContext petriNet (marking [tokD]) = [] := by native_decide

/-- {A, B} has exactly one reduct via T1. -/
theorem AB_has_one_reduct :
    (rewriteWithContext petriNet (marking [tokA, tokB])).length = 1 := by native_decide

-- Verification: OSLF pipeline type-checks
#check petriOSLF
#check petriGalois

end Mettapedia.OSLF.Framework.PetriNetInstance
