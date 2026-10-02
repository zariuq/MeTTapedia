import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelTypings
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectRules
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerEliminator

/-!
# The object package at every level

The language declares identity elimination `id:eliminate` with two level
parameters, the carrier's and the motive's (`identityEliminateType`), and the
recursor `num-rec` of the numbers with the level of its motive. The object
package declares both at the lowest universes (`Package.jType`,
`Package.numRecType`). Its successor declares them at the universes of three
level expressions, every other constant as the object package does, and it
computes as the object package does (`objectRulesAt lu lw lr`):

* identity elimination at carrier `U lu` and motive `U lw`,
  `elimType (U lu) (U lw)`, and the recursor with its motive into `U lr`,
  `numRecTypeAt (U lr)`;
* at the level parameters it is the language's own declaration
  (`polyRules`), identity elimination at `identityEliminateType`
  (`polyRules_j`);
* at the lowest universes it is the object package (`objectRulesAt_zero`);
* its declared types are typed in it, at universes (`objectRulesAt_j_typed`,
  `objectRulesAt_numRec_typed`), and its other declarations are the object
  package's.

A level expression may mention the level parameters, and by cumulativity one
instance serves every use below its levels: a carrier of `U l`, with `l` at most
`lu` under every valuation, is a type of `U lu`, and a motive into `U m`, with `m`
at most `lw`, is a function into `U lw`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Package (jName numRecName)

namespace CodeModel

/-! ## The object package's identity elimination and recursor -/

/-- Identity elimination is declared at the lowest universes. -/
theorem allTypes_j : allTypes jName = some Package.jType := by
  decide

/-- Identity elimination is no code. -/
theorem codeType_j : programCodes.codeType jName = none := by
  decide

/-- The object package declares identity elimination at the lowest universes. -/
theorem objectRules_declared_j : objectRules.constantType jName = some Package.jType := by
  change (programCodes.codeType jName).orElse (fun _ => allTypes jName) = some Package.jType
  rw [codeType_j]
  exact allTypes_j

/-- The object package declares the recursor with its motive into the lowest
universe. -/
theorem objectRules_declared_numRec :
    objectRules.constantType numRecName = some Package.numRecType := by
  decide

/-! ## The package at every level -/

/-- **The object package at every level**: identity elimination declared at
carrier `U lu` and motive `U lw`, the recursor with its motive into `U lr`, and
every other constant, and the computation, as in the object package. -/
def objectRulesAt (lu lw lr : LevelExpr Nat) : Rules Tower.Head :=
  { objectRules with
    constantType := fun name =>
      if name = jName then some (elimType (.sort lu) (.sort lw))
      else if name = numRecName then some (numRecTypeAt (.sort lr))
      else objectRules.constantType name }

section At

variable (lu lw lr : LevelExpr Nat)

/-- Identity elimination is declared at `elimType (U lu) (U lw)`. -/
theorem objectRulesAt_j :
    (objectRulesAt lu lw lr).constantType jName = some (elimType (.sort lu) (.sort lw)) := by
  dsimp only [objectRulesAt]
  rw [if_pos rfl]

/-- The recursor is declared with its motive into `U lr`. -/
theorem objectRulesAt_numRec :
    (objectRulesAt lu lw lr).constantType numRecName = some (numRecTypeAt (.sort lr)) := by
  dsimp only [objectRulesAt]
  rw [if_neg (by decide), if_pos rfl]

/-- Every other constant is declared as in the object package. -/
theorem objectRulesAt_other {name : DeclName} (notJ : name ≠ jName)
    (notRec : name ≠ numRecName) :
    (objectRulesAt lu lw lr).constantType name = objectRules.constantType name := by
  dsimp only [objectRulesAt]
  rw [if_neg notJ, if_neg notRec]

/-- The package computes as the object package does. -/
theorem objectRulesAt_computation :
    (objectRulesAt lu lw lr).computation = objectRules.computation :=
  rfl

/-- The tower is inside the package. -/
theorem tower_sub_objectRulesAt : RulesSub Tower.rules (objectRulesAt lu lw lr) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun declared => nomatch declared
  computation := fun step => step.elim

/-- The stage of the numbers and their constructors is inside the package. -/
theorem ctorStage_sub_objectRulesAt : RulesSub ctorStage (objectRulesAt lu lw lr) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := by
    intro name type declared
    change (if allowedIn [numN, zeroN, sucN] name then allTypes name else none) = some type
      at declared
    by_cases allowed : allowedIn [numN, zeroN, sucN] name = true
    · rw [if_pos allowed] at declared
      have mem : name ∈ [numN, zeroN, sucN] := by simpa [allowedIn] using allowed
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;>
        rw [objectRulesAt_other lu lw lr (by decide) (by decide)] <;> exact declared
    · rw [if_neg allowed] at declared
      cases declared
  computation := fun step => .inl ((stage_sub_rules _).computation step)

/-- **Identity elimination's declared type is typed** in the package, at a
universe. -/
theorem objectRulesAt_j_typed : ∃ w, (objectRulesAt lu lw lr).isUniverse w ∧
    Typed (objectRulesAt lu lw lr) .nil (elimType (.sort lu) (.sort lw)) (.head w) := by
  obtain ⟨w, hw, typed⟩ := TowerEliminatorModel.elimType_typed lu lw
  exact ⟨w, hw, Derivable.mono (tower_sub_objectRulesAt lu lw lr) typed⟩

/-- **The recursor's declared type is typed** in the package, at the universe
above its motive's. -/
theorem objectRulesAt_numRec_typed :
    Typed (objectRulesAt lu lw lr) .nil (numRecTypeAt (.sort lr)) (sortTm (.succ lr)) :=
  Derivable.mono (ctorStage_sub_objectRulesAt lu lw lr) (numRecTypeAt_typed lr)

end At

/-- **At the lowest universes the package is the object package.** -/
theorem objectRulesAt_zero : objectRulesAt Tower.zero Tower.zero Tower.zero = objectRules := by
  have types : (fun name => if name = jName then some (elimType (.sort Tower.zero) (.sort Tower.zero))
      else if name = numRecName then some (numRecTypeAt (.sort Tower.zero))
      else objectRules.constantType name) = objectRules.constantType := by
    funext name
    by_cases hj : name = jName
    · subst hj
      rw [if_pos rfl, objectRules_declared_j]
      rfl
    · by_cases hr : name = numRecName
      · subst hr
        rw [if_neg hj, if_pos rfl, objectRules_declared_numRec, numRecTypeAt_zero]
      · rw [if_neg hj, if_neg hr]
  unfold objectRulesAt
  rw [types]

/-- **The language's declaration**: the package at the level parameters, with
identity elimination's carrier and motive at the parameters `0` and `1` and the
recursor's motive at the parameter `2`. -/
def polyRules : Rules Tower.Head := objectRulesAt (.param 0) (.param 1) (.param 2)

/-- At the level parameters, identity elimination is declared at the type the
language gives `id:eliminate`. -/
theorem polyRules_j :
    polyRules.constantType jName = some NativeIndexedFamilies.Intrinsic.identityEliminateType :=
  objectRulesAt_j _ _ _

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
