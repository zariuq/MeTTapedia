import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm

/-!
# π's static theory, decided

The restriction-block theory with replication decides π's static theory by the canonical form on object processes
(`RestrictionBlocks.equationEquiv_iff_canonR_eq` at π's blocks with replication). The controls below decide it on
named processes, both ways: extrusion and garbage restrictions, a server and its unfolding, two copies of a server; a
restriction kept in front of a guard, one private channel against two, a server against one copy. Beyond the named
calculus, which replicates inputs only, it decides general replication: `!(P | Q)` is `!P | !Q`, `!(P | P)` is `!P`,
`!!P` is `!P` and `!0` is `0`, while finitely many copies are not a replicated output.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (equationEquiv_iff_canonR_eq)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks (piRepBlock piNameContext_base)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piCalc piToPattern piToPattern_hasType
  piNameContext)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType checkOpenPatternWellSorted checkOpenPatternWellSorted_eq_true_iff)

/-! ### Controls through the decision -/

/-- Extrusion, decided: `(νx)(x⟨w⟩ | a⟨b⟩)` and `(νx) x⟨w⟩ | a⟨b⟩` are equivalent. -/
example : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
    (piToPattern (.nu "x" (.par (.output "x" "w") (.output "a" "b"))))
    (piToPattern (.par (.nu "x" (.output "x" "w")) (.output "a" "b"))) := by
  rw [equationEquiv_iff_canonR_eq (block := piRepBlock) piNameContext_base (piToPattern_hasType _)
    (piToPattern_hasType _) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- Garbage, decided: `(νx)(νy) a⟨b⟩` is `a⟨b⟩`. -/
example : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
    (piToPattern (.nu "x" (.nu "y" (.output "a" "b")))) (piToPattern (.output "a" "b")) := by
  rw [equationEquiv_iff_canonR_eq (block := piRepBlock) piNameContext_base (piToPattern_hasType _)
    (piToPattern_hasType _) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- **Negative**, decided: a restriction does not leave a guard, under the whole static theory. -/
example : ¬ EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
    (piToPattern (.nu "x" (.input "a" "z" (.output "x" "z"))))
    (piToPattern (.input "a" "z" (.nu "x" (.output "x" "z")))) := by
  rw [equationEquiv_iff_canonR_eq (block := piRepBlock) piNameContext_base (piToPattern_hasType _)
    (piToPattern_hasType _) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- **Negative**, decided: one private channel used twice is not two private channels. -/
example : ¬ EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
    (piToPattern (.nu "v" (.par (.output "c" "v") (.output "c" "v"))))
    (piToPattern (.nu "v" (.nu "u" (.par (.output "c" "v") (.output "c" "u"))))) := by
  rw [equationEquiv_iff_canonR_eq (block := piRepBlock) piNameContext_base (piToPattern_hasType _)
    (piToPattern_hasType _) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- A server is its unfolding, decided: `!x(y).0` and `x(y).0 | !x(y).0` are equivalent. -/
example : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
    (piToPattern (.replicate "x" "y" .nil))
    (piToPattern (.par (.input "x" "y" .nil) (.replicate "x" "y" .nil))) := by
  rw [equationEquiv_iff_canonR_eq (block := piRepBlock) piNameContext_base (piToPattern_hasType _)
    (piToPattern_hasType _) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- Two copies of a server are one, decided: `!x(y).y⟨a⟩ | !x(y).y⟨a⟩` is `!x(y).y⟨a⟩`. -/
example : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
    (piToPattern (.par (.replicate "x" "y" (.output "y" "a")) (.replicate "x" "y" (.output "y" "a"))))
    (piToPattern (.replicate "x" "y" (.output "y" "a"))) := by
  rw [equationEquiv_iff_canonR_eq (block := piRepBlock) piNameContext_base (piToPattern_hasType _)
    (piToPattern_hasType _) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- **Negative**, decided: a server is not one copy of its input. -/
example : ¬ EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
    (piToPattern (.replicate "x" "y" .nil)) (piToPattern (.input "x" "y" .nil)) := by
  rw [equationEquiv_iff_canonR_eq (block := piRepBlock) piNameContext_base (piToPattern_hasType _)
    (piToPattern_hasType _) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-! ### General replication -/

theorem typed_of_checked {pattern : Pattern}
    (checked : checkOpenPatternWellSorted piCalc piNameContext [] (.base "Proc") pattern = true) :
    HasType piCalc piNameContext [] pattern (.base "Proc") :=
  ((checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _).mp checked).1

private def sends : Pattern := .apply "PiOut" [.fvar "x", .fvar "w"]
private def receives : Pattern := .apply "PiInp" [.fvar "x", .lambda none (.apply "PiNil" [])]
private def bang (process : Pattern) : Pattern := .apply "PiRep" [process]
private def bag (processes : List Pattern) : Pattern := .collection .hashBag processes none

/-- Replication distributes, decided: `!(x⟨w⟩ | x(y).0)` is `!x⟨w⟩ | !x(y).0`. -/
example : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (bang (bag [sends, receives]))
    (bag [bang sends, bang receives]) := by
  rw [equationEquiv_iff_canonR_eq (block := piRepBlock) piNameContext_base (typed_of_checked (by decide +kernel))
    (typed_of_checked (by decide +kernel)) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- Replicating two copies is replicating one, decided: `!(x⟨w⟩ | x⟨w⟩)` is `!x⟨w⟩`. -/
example : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (bang (bag [sends, sends])) (bang sends) := by
  rw [equationEquiv_iff_canonR_eq (block := piRepBlock) piNameContext_base (typed_of_checked (by decide +kernel))
    (typed_of_checked (by decide +kernel)) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- `!!x⟨w⟩` is `!x⟨w⟩`, and `!0` is `0`, decided. -/
example : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (bang (bang sends)) (bang sends) ∧
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (bang (.apply "PiNil" [])) (.apply "PiNil" []) := by
  constructor
  all_goals
    rw [equationEquiv_iff_canonR_eq (block := piRepBlock) piNameContext_base (typed_of_checked (by decide +kernel))
      (typed_of_checked (by decide +kernel)) (by decide +kernel) (by decide +kernel)]
    decide +kernel

/-- **Negative**, decided: two copies of an output are not a replicated output. -/
example : ¬ EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (bag [sends, sends]) (bang sends) := by
  rw [equationEquiv_iff_canonR_eq (block := piRepBlock) piNameContext_base (typed_of_checked (by decide +kernel))
    (typed_of_checked (by decide +kernel)) (by decide +kernel) (by decide +kernel)]
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm
