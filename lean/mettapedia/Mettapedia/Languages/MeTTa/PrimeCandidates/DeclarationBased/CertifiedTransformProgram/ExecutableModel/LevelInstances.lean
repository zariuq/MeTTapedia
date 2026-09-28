import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelPackage
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectShape
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Model
import Mettapedia.TypeTheory.UniverseLevel.Names
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ConstantRenaming

/-!
# The object package with every level instance

The language declares identity elimination `id:eliminate` with two level
parameters and instantiates them afresh at every use. Each use stands for one
instance, and each instance is one constant:

* `jAt lu lw`, identity elimination at carrier `U lu` and motive `U lw`, declared
  at `elimType (U lu) (U lw)`;
* `numRecAt lr`, the recursor of the numbers with its motive into `U lr`,
  declared at `numRecTypeAt (U lr)`.

An instance's name is the constant's name followed by the spellings of its
levels (`appendLevel`); the spelling is injective (`jAt_inj`, `numRecAt_inj`),
the two families are disjoint (`jAt_ne_numRecAt`), and the object package
declares none of their names (`objectRules_jAt`, `objectRules_numRecAt`), since
all its names end in a string.

**The package with every instance** (`objectRulesInstances`) is the object
package with every instance of identity elimination, with its linear rule at
reflexivity, and every instance of the recursor, with its rules at the
constructors. It contains the object package (`objectRules_sub_objectRulesInstances`),
whose own `id:eliminate` and `num-rec` remain the constants its definitions
compute with.

**Roles.** Each instance has the role of its constant (`instanceRoles`), and
under these roles the package has root shape (`instanceShape`): its root steps
occur at spines of computing constants, and at most one applies.

**Renamings.**

* Erasing the levels of the instances (`eraseLevels`) sends each root step of the
  package to a root step of the object package (`objectRulesInstances_eraseLevels`):
  identity elimination's rule at an instance to its rule, the recursor's rules
  at an instance to its rules, and every other rule to itself.
* Instantiating the package at every level (`instanceRenaming lu lw lr`: identity
  elimination to `jAt lu lw`, the recursor to `numRecAt lr`) renames it into the
  package with every instance, once `sucMove`'s equation is dropped
  (`objectRulesAtWithoutSucMove_renames`): typing, typed equality and reduction are
  preserved (`objectRulesAtWithoutSucMove_embeds`, `objectRulesAtWithoutSucMove_reduces`).
  The right-hand side of `sucMove`'s equation holds the package's own identity
  eliminator, which the renaming would replace by the instance: the renamed
  equation is no step of the package with every instance
  (`sucMove_renamed_not_step`), whose `sucMove` computes with `id:eliminate`.
* At the level parameters the instance is the language's declaration
  (`objectRulesInstances_poly_j`), and the proposed recursor with its motive at
  the level parameter `0` is `numRecAt (param 0)` (`objectRulesInstances_poly_numRec`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Package (jName numRecName sucMoveName eqAtName)
open TelescopeAbstraction (applyClosed)

namespace CodeModel

/-! ## Instance names -/

/-- **The instance of identity elimination** at carrier level `lu` and motive
level `lw`: `id:eliminate` followed by the spellings of the two levels. -/
def jAt (lu lw : LevelExpr) : DeclName := appendLevel (appendLevel jName lu) lw

/-- **The instance of the recursor of the numbers** with its motive at level
`lr`: `num-rec` followed by the spelling of the level. -/
def numRecAt (lr : LevelExpr) : DeclName := appendLevel numRecName lr

/-- The instances of identity elimination are distinct for distinct levels. -/
theorem jAt_inj {lu lw lu' lw' : LevelExpr} (same : jAt lu lw = jAt lu' lw') :
    lu = lu' ∧ lw = lw' := by
  obtain ⟨rfl, inner⟩ := appendLevel_inj same
  obtain ⟨rfl, -⟩ := appendLevel_inj inner
  exact ⟨rfl, rfl⟩

/-- The instances of the recursor are distinct for distinct levels. -/
theorem numRecAt_inj {lr lr' : LevelExpr} (same : numRecAt lr = numRecAt lr') : lr = lr' :=
  (appendLevel_inj same).1

/-- No instance of identity elimination is an instance of the recursor. -/
theorem jAt_ne_numRecAt (lu lw lr : LevelExpr) : jAt lu lw ≠ numRecAt lr := by
  intro same
  obtain ⟨-, inner⟩ := appendLevel_inj same
  exact appendLevel_ne_str jName lu .anonymous "num-rec" inner

theorem jAt_ne_jName (lu lw : LevelExpr) : jAt lu lw ≠ jName :=
  appendLevel_ne_str _ lw .anonymous "id:eliminate"

theorem numRecAt_ne_numRecName (lr : LevelExpr) : numRecAt lr ≠ numRecName :=
  appendLevel_ne_str _ lr .anonymous "num-rec"

theorem jAt_ne_numRecName (lu lw : LevelExpr) : jAt lu lw ≠ numRecName :=
  appendLevel_ne_str _ lw .anonymous "num-rec"

theorem numRecAt_ne_jName (lr : LevelExpr) : numRecAt lr ≠ jName :=
  appendLevel_ne_str _ lr .anonymous "id:eliminate"

/-- The levels of an instance of identity elimination, read from its name. -/
def jLevels? (name : DeclName) : Option (LevelExpr × LevelExpr) :=
  match readLevel name with
  | some (lw, q) =>
      match readLevel q with
      | some (lu, r) => if r = jName then some (lu, lw) else none
      | none => none
  | none => none

/-- The level of an instance of the recursor, read from its name. -/
def numRecLevel? (name : DeclName) : Option LevelExpr :=
  match readLevel name with
  | some (lr, q) => if q = numRecName then some lr else none
  | none => none

@[simp] theorem jLevels?_jAt (lu lw : LevelExpr) : jLevels? (jAt lu lw) = some (lu, lw) := by
  simp only [jLevels?, jAt, readLevel_appendLevel, if_pos]

@[simp] theorem numRecLevel?_numRecAt (lr : LevelExpr) : numRecLevel? (numRecAt lr) = some lr := by
  simp only [numRecLevel?, numRecAt, readLevel_appendLevel, if_pos]

theorem jLevels?_eq_some {name : DeclName} {lu lw : LevelExpr}
    (found : jLevels? name = some (lu, lw)) : name = jAt lu lw := by
  unfold jLevels? at found
  split at found
  next lw' q read =>
    split at found
    next lu' r read' =>
      split at found
      next same =>
        cases found
        rw [readLevel_sound read, readLevel_sound read', same]
        rfl
      next => cases found
    next => cases found
  next => cases found

theorem numRecLevel?_eq_some {name : DeclName} {lr : LevelExpr}
    (found : numRecLevel? name = some lr) : name = numRecAt lr := by
  unfold numRecLevel? at found
  split at found
  next lr' q read =>
    split at found
    next same =>
      cases found
      rw [readLevel_sound read, same]
      rfl
    next => cases found
  next => cases found

theorem jLevels?_of_readLevel {name : DeclName} (none_ : readLevel name = none) :
    jLevels? name = none := by
  simp only [jLevels?, none_]

theorem numRecLevel?_of_readLevel {name : DeclName} (none_ : readLevel name = none) :
    numRecLevel? name = none := by
  simp only [numRecLevel?, none_]

@[simp] theorem jLevels?_numRecAt (lr : LevelExpr) : jLevels? (numRecAt lr) = none := by
  simp only [jLevels?, numRecAt, readLevel_appendLevel]
  rfl

@[simp] theorem numRecLevel?_jAt (lu lw : LevelExpr) : numRecLevel? (jAt lu lw) = none := by
  simp only [numRecLevel?, jAt, readLevel_appendLevel]
  exact if_neg (appendLevel_ne_str jName lu .anonymous "num-rec")

/-! ## The object package declares no instance -/

/-- The object package declares no name ending in a numeric component. -/
theorem objectRules_constantType_num (p : DeclName) (k : Nat) :
    objectRules.constantType (.num p k) = none := by
  have noAll : SetProfile.allInstance? (.num p k) = none := rfl
  have noEq : SetProfile.eqInstance? (.num p k) = none := rfl
  have code : programCodes.codeType (.num p k) = none := by
    simp only [Codes.codeType, programCodes, noAll, noEq, Option.map_none, Codes.equationCarrier,
      if_true]
    rw [if_neg (Lean.Name.noConfusion), if_neg (Lean.Name.noConfusion),
      if_neg (Lean.Name.noConfusion)]
  change (programCodes.codeType (.num p k)).orElse (fun _ => rules.constantType (.num p k)) = none
  rw [code]
  rfl

/-- A name the object package declares spells no level. -/
theorem readLevel_of_declared {name : DeclName} {type : Tower.Tm 0}
    (declared : objectRules.constantType name = some type) : readLevel name = none := by
  cases name with
  | anonymous => rfl
  | str p s => rfl
  | num p k => rw [objectRules_constantType_num] at declared; cases declared

theorem appendLevel_num (p : DeclName) (e : LevelExpr) : ∃ q k, appendLevel p e = .num q k := by
  cases e <;> exact ⟨_, _, rfl⟩

/-- **The object package declares no instance of identity elimination.** -/
theorem objectRules_jAt (lu lw : LevelExpr) : objectRules.constantType (jAt lu lw) = none := by
  obtain ⟨q, k, e⟩ := appendLevel_num (appendLevel jName lu) lw
  unfold jAt
  rw [e]
  exact objectRules_constantType_num q k

/-- **The object package declares no instance of the recursor.** -/
theorem objectRules_numRecAt (lr : LevelExpr) : objectRules.constantType (numRecAt lr) = none := by
  obtain ⟨q, k, e⟩ := appendLevel_num numRecName lr
  unfold numRecAt
  rw [e]
  exact objectRules_constantType_num q k

/-- **Every name the object package declares is distinct from every instance of
identity elimination.** -/
theorem declared_ne_jAt {name : DeclName} {type : Tower.Tm 0}
    (declared : objectRules.constantType name = some type) (lu lw : LevelExpr) :
    name ≠ jAt lu lw := fun same => by
  rw [same, objectRules_jAt] at declared
  cases declared

/-- **Every name the object package declares is distinct from every instance of the
recursor.** -/
theorem declared_ne_numRecAt {name : DeclName} {type : Tower.Tm 0}
    (declared : objectRules.constantType name = some type) (lr : LevelExpr) :
    name ≠ numRecAt lr := fun same => by
  rw [same, objectRules_numRecAt] at declared
  cases declared

/-! ## The package with every instance -/

/-- **The computation rules of the instances**: identity elimination's linear rule
at every instance of it, and the recursor's rules at every instance of it. -/
def instanceComputation : RootComputation Tower.Head where
  step := fun {n} l r => (∃ lu lw, (eliminatorComputation (jAt lu lw)).step (n := n) l r) ∨
    ∃ lr, (iotaComputation (numRecAt lr) ctors).step (n := n) l r
  rename := by
    intro n m ρ l r step
    rcases step with ⟨lu, lw, h⟩ | ⟨lr, h⟩
    · exact .inl ⟨lu, lw, (eliminatorComputation (jAt lu lw)).rename ρ h⟩
    · exact .inr ⟨lr, (iotaComputation (numRecAt lr) ctors).rename ρ h⟩
  substitute := by
    intro n m σ l r step
    rcases step with ⟨lu, lw, h⟩ | ⟨lr, h⟩
    · exact .inl ⟨lu, lw, (eliminatorComputation (jAt lu lw)).substitute σ h⟩
    · exact .inr ⟨lr, (iotaComputation (numRecAt lr) ctors).substitute σ h⟩

/-- The declarations of the package with every instance. -/
def instanceTypes (name : DeclName) : Option (Tower.Tm 0) :=
  match jLevels? name with
  | some (lu, lw) => some (elimType (.sort lu) (.sort lw))
  | none =>
      match numRecLevel? name with
      | some lr => some (numRecTypeAt (.sort lr))
      | none => objectRules.constantType name

/-- **The object package with every level instance**: identity elimination
declared at `elimType (U lu) (U lw)` as the constant `jAt lu lw` for every pair of
level expressions, the recursor with its motive into `U lr` as `numRecAt lr` for
every level expression, each instance with the computation rules of its constant,
and every declaration and rule of the object package. -/
def objectRulesInstances : Rules Tower.Head :=
  { objectRules with
    constantType := instanceTypes
    computation := RootComputation.union objectRules.computation instanceComputation }

/-- The instance `jAt lu lw` is declared at `elimType (U lu) (U lw)`. -/
theorem objectRulesInstances_j (lu lw : LevelExpr) :
    objectRulesInstances.constantType (jAt lu lw) = some (elimType (.sort lu) (.sort lw)) := by
  change instanceTypes (jAt lu lw) = _
  simp only [instanceTypes, jLevels?_jAt]

/-- The instance `numRecAt lr` is declared with its motive into `U lr`. -/
theorem objectRulesInstances_numRec (lr : LevelExpr) :
    objectRulesInstances.constantType (numRecAt lr) = some (numRecTypeAt (.sort lr)) := by
  change instanceTypes (numRecAt lr) = _
  simp only [instanceTypes, jLevels?_numRecAt, numRecLevel?_numRecAt]

/-- A name that spells no level is declared as in the object package. -/
theorem objectRulesInstances_other {name : DeclName} (plain : readLevel name = none) :
    objectRulesInstances.constantType name = objectRules.constantType name := by
  change instanceTypes name = _
  simp only [instanceTypes, jLevels?_of_readLevel plain, numRecLevel?_of_readLevel plain]

/-- The declarations of the package with every instance, by the reading of the
name. -/
theorem objectRulesInstances_declared_cases {name : DeclName} {type : Tower.Tm 0}
    (declared : objectRulesInstances.constantType name = some type) :
    (∃ lu lw, name = jAt lu lw ∧ type = elimType (.sort lu) (.sort lw)) ∨
      (∃ lr, name = numRecAt lr ∧ type = numRecTypeAt (.sort lr)) ∨
      (jLevels? name = none ∧ numRecLevel? name = none ∧
        objectRules.constantType name = some type) := by
  change instanceTypes name = some type at declared
  unfold instanceTypes at declared
  split at declared
  next lu lw found =>
    cases declared
    exact .inl ⟨lu, lw, jLevels?_eq_some found, rfl⟩
  next noJ =>
    split at declared
    next lr found =>
      cases declared
      exact .inr (.inl ⟨lr, numRecLevel?_eq_some found, rfl⟩)
    next noRec => exact .inr (.inr ⟨noJ, noRec, declared⟩)

/-- **The object package is contained in the package with every instance.** -/
theorem objectRules_sub_objectRulesInstances : RulesSub objectRules objectRulesInstances where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun declared =>
    (objectRulesInstances_other (readLevel_of_declared declared)).trans declared
  computation := fun step => .inl step

/-- An instance of identity elimination is declared at every pair of levels, and
at the level parameters it is the language's declaration of `id:eliminate`. -/
theorem objectRulesInstances_poly_j :
    objectRulesInstances.constantType (jAt (.param 0) (.param 1)) =
      some NativeIndexedFamilies.Intrinsic.identityEliminateType :=
  objectRulesInstances_j _ _

/-- At the level parameters, the instance declares identity elimination as the
language's declaration does (`polyRules`). -/
theorem objectRulesInstances_poly_j_eq :
    objectRulesInstances.constantType (jAt (.param 0) (.param 1)) =
      polyRules.constantType jName :=
  objectRulesInstances_poly_j.trans polyRules_j.symm

/-- The recursor at the level parameter `0`, whose motive lands in `U (param 0)`. -/
theorem objectRulesInstances_poly_numRec :
    objectRulesInstances.constantType (numRecAt (.param 0)) =
      some (numRecTypeAt (.sort (.param 0))) :=
  objectRulesInstances_numRec _

/-! ## The equations of the object package -/

/-- The names of the object package's equations other than identity
elimination's, the recursor's and `sucMove`'s. -/
def plainEquation (name : DeclName) : Bool :=
  name != jName && name != numRecName && name != sucMoveName

/-- The object package's other equations, with the decoding of codes. -/
abbrev plainRules : Rules Tower.Head := programCodes.extend (stage plainEquation)

/-- **Every root step of the object package** is identity elimination's linear
rule, a rule of the recursor, `sucMove`'s equation, or a step of the other
equations or of the decoding. -/
theorem objectRules_step_cases {n : Nat} {l r : Tower.Tm n}
    (step : objectRules.computation.step l r) :
    (eliminatorComputation jName).step l r ∨ (iotaComputation numRecName ctors).step l r ∨
      (definitionComputation sucMoveName Package.eqAtTelescope sucMoveRhs).step l r ∨
      plainRules.computation.step l r := by
  rcases step with step | step
  · obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
    have listedIn := (List.mem_filter.mp mem).1
    have plain : ∀ {e : DeclName × RootComputation Tower.Head}, e ∈ computations →
        plainEquation e.1 = true → e.2.step l r → plainRules.computation.step l r :=
      fun {_} listed allowed h' =>
        .inl (RootComputation.step_unionAll (List.mem_filter.mpr ⟨listed, allowed⟩) h')
    simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listedIn
    rcases listedIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr (plain (listed 1 (by decide)) (by decide) h)))
    · exact .inr (.inr (.inr (plain (listed 2 (by decide)) (by decide) h)))
    · exact .inl h
    · exact .inr (.inr (.inr (plain (listed 4 (by decide)) (by decide) h)))
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (plain (listed 6 (by decide)) (by decide) h)))
    · exact .inr (.inr (.inr (plain (listed 7 (by decide)) (by decide) h)))
    · exact .inr (.inr (.inr (plain (listed 8 (by decide)) (by decide) h)))
    · exact .inr (.inr (.inr (plain (listed 9 (by decide)) (by decide) h)))
    · exact .inr (.inr (.inr (plain (listed 10 (by decide)) (by decide) h)))
    · exact .inr (.inr (.inr (plain (listed 11 (by decide)) (by decide) h)))
  · exact .inr (.inr (.inr (.inr step)))

theorem plainRules_sub_objectRules {n : Nat} {l r : Tower.Tm n}
    (step : plainRules.computation.step l r) : objectRules.computation.step l r := by
  rcases step with step | step
  · exact .inl ((stage_sub fun _ _ => rfl).computation step)
  · exact .inr step

/-- A name the package's computations mention outside identity elimination and
the recursor: it spells no level, and it is neither `id:eliminate` nor
`num-rec`. -/
def plainName (name : DeclName) : Bool :=
  (readLevel name).isNone && name != jName && name != numRecName

/-- A term whose constants are plain names is fixed by a renaming that fixes
plain names. -/
theorem mapConst_plain {f : DeclName → DeclName}
    (fixes : ∀ c, plainName c = true → f c = c) {n : Nat} {t : Tower.Tm n}
    (plain : t.allConstants plainName = true) : t.mapConst f = t :=
  Tm.mapConst_eq_self f fixes plain

theorem mapConst_typeTerm {f : DeclName → DeclName}
    (fixes : ∀ c, plainName c = true → f c = c) :
    ∀ {n : Nat} (type : Mettapedia.Logic.HOL.Ty SetProfile.SetBase),
      (FormationSensitiveHOLInterface.typeAt SetProfile.types n type).mapConst f =
        FormationSensitiveHOLInterface.typeAt SetProfile.types n type
  | _, .prop => by
      simp only [FormationSensitiveHOLInterface.typeAt, Tm.mapConst_liftClosed, SetProfile.types,
        Tm.mapConst, fixes _ (by decide : plainName SetProfile.propName = true)]
  | _, .base .num => by
      simp only [FormationSensitiveHOLInterface.typeAt, Tm.mapConst_liftClosed, SetProfile.types,
        Tm.mapConst, fixes _ (by decide : plainName (SetProfile.baseName .num) = true)]
  | _, .base .set => by
      simp only [FormationSensitiveHOLInterface.typeAt, Tm.mapConst_liftClosed, SetProfile.types,
        Tm.mapConst, fixes _ (by decide : plainName (SetProfile.baseName .set) = true)]
  | _, .arr a b => by
      simp only [FormationSensitiveHOLInterface.typeAt, Tm.mapConst, mapConst_typeTerm fixes a,
        mapConst_typeTerm fixes b]

/-- **The declared types of the object package are fixed** by a renaming that
fixes plain names. -/
theorem objectRules_type_fixed {f : DeclName → DeclName}
    (fixes : ∀ c, plainName c = true → f c = c) {name : DeclName} {type : Tower.Tm 0}
    (declared : objectRules.constantType name = some type) : type.mapConst f = type := by
  change (programCodes.codeType name).orElse (fun _ => rules.constantType name) = some type
    at declared
  cases code : programCodes.codeType name with
  | some T =>
      rw [code] at declared
      cases declared
      unfold Codes.codeType at code
      split_ifs at code with hp hh hi
      · cases code; rfl
      · cases code
        simp only [Codes.holdsType, Codes.propT, Tm.mapConst, programCodes,
          fixes _ (by decide : plainName propN = true)]
      · cases code
        simp only [Codes.impType, Codes.propT, Tm.mapConst, programCodes,
          fixes _ (by decide : plainName propN = true)]
      · split at code
        next A carrier =>
          cases code
          change (SetProfile.allInstance? name).map typeTerm = some A at carrier
          cases found : SetProfile.allInstance? name with
          | none => rw [found] at carrier; cases carrier
          | some type =>
              rw [found] at carrier
              cases carrier
              simp only [Codes.allType, Codes.propT, Tm.mapConst, programCodes,
                fixes _ (by decide : plainName propN = true), typeTerm, mapConst_typeTerm fixes]
        next =>
          change (Codes.equationCarrier programCodes name).map programCodes.eqType = some _ at code
          cases found : SetProfile.eqInstance? name with
          | none =>
              simp only [Codes.equationCarrier, programCodes, if_true, found, Option.map_none]
                at code
              cases code
          | some type =>
              simp only [Codes.equationCarrier, programCodes, if_true, found, Option.map_some,
                Option.some.injEq] at code
              subst code
              simp only [Codes.eqType, Codes.propT, Tm.mapConst, Tm.mapConst_rename,
                fixes _ (by decide : plainName propN = true), typeTerm, mapConst_typeTerm fixes]
  | none =>
      rw [code] at declared
      change (if true then allTypes name else none) = some type at declared
      rw [if_pos rfl] at declared
      have mem : (name, type) ∈ declarations := mem_of_lookup declared
      simp only [declarations, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact mapConst_plain fixes (by decide)

theorem allInstance?_jName : SetProfile.allInstance? jName = none := by decide
theorem allInstance?_numRecName : SetProfile.allInstance? numRecName = none := by decide
theorem eqInstance?_jName : SetProfile.eqInstance? jName = none := by decide
theorem eqInstance?_numRecName : SetProfile.eqInstance? numRecName = none := by decide

theorem plainName_allName (type : Mettapedia.Logic.HOL.Ty SetProfile.SetBase) :
    plainName (SetProfile.allName type) = true := by
  have notJ : SetProfile.allName type ≠ jName := fun same => by
    have h := SetProfile.allInstance?_allName type
    rw [same, allInstance?_jName] at h
    cases h
  have notRec : SetProfile.allName type ≠ numRecName := fun same => by
    have h := SetProfile.allInstance?_allName type
    rw [same, allInstance?_numRecName] at h
    cases h
  have spells : readLevel (SetProfile.allName type) = none := rfl
  simp only [plainName, Bool.and_eq_true, bne_iff_ne, ne_eq, spells, Option.isNone_none, notJ,
    notRec, not_false_eq_true, and_self]

theorem plainName_eqName (type : Mettapedia.Logic.HOL.Ty SetProfile.SetBase) :
    plainName (SetProfile.eqName type) = true := by
  have notJ : SetProfile.eqName type ≠ jName := fun same => by
    have h := SetProfile.eqInstance?_eqName type
    rw [same, eqInstance?_jName] at h
    cases h
  have notRec : SetProfile.eqName type ≠ numRecName := fun same => by
    have h := SetProfile.eqInstance?_eqName type
    rw [same, eqInstance?_numRecName] at h
    cases h
  have spells : readLevel (SetProfile.eqName type) = none := rfl
  simp only [plainName, Bool.and_eq_true, bne_iff_ne, ne_eq, spells, Option.isNone_none, notJ,
    notRec, not_false_eq_true, and_self]

/-- **The other equations and the decoding are sent to themselves** by a renaming
that fixes plain names and the default term. -/
theorem plainRules_step_mapConst {f : DeclName → DeclName}
    (fixes : ∀ c, plainName c = true → f c = c) (fixDefault : f .anonymous = .anonymous)
    {n : Nat} {l r : Tower.Tm n} (step : plainRules.computation.step l r) :
    plainRules.computation.step (l.mapConst f) (r.mapConst f) := by
  have fixName : ∀ {c : DeclName}, plainName c = true → f c = c := fun h => fixes _ h
  have fixCtors : ∀ entry ∈ ctors, f entry.1 = entry.1 := by
    intro entry mem
    simp only [ctors, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact fixName (by decide)
    · exact fixName (by decide)
  rcases step with step | step
  · obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
    obtain ⟨listedIn, allowed⟩ := List.mem_filter.mp mem
    have back : ∀ {e : DeclName × RootComputation Tower.Head}, e ∈ computations →
        plainEquation e.1 = true → e.2.step (l.mapConst f) (r.mapConst f) →
        plainRules.computation.step (l.mapConst f) (r.mapConst f) :=
      fun {_} listed ok h' =>
        .inl (RootComputation.step_unionAll (List.mem_filter.mpr ⟨listed, ok⟩) h')
    simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listedIn
    rcases listedIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd allowed (by decide)
    · refine back (listed 1 (by decide)) (by decide) (RecursionStep.mapConst f
        (fixName (by decide)) fixCtors fixDefault ?_ h)
      intro entry mem
      simp only [ctors, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> exact mapConst_plain fixes (by decide)
    · refine back (listed 2 (by decide)) (by decide) (RecursionStep.mapConst f
        (fixName (by decide)) fixCtors fixDefault ?_ h)
      intro entry mem
      simp only [ctors, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> exact mapConst_plain fixes (by decide)
    · exact absurd allowed (by decide)
    · exact back (listed 4 (by decide)) (by decide)
        (DefinitionStep.mapConst f (fixName (by decide)) (mapConst_plain fixes (by decide)) h)
    · exact absurd allowed (by decide)
    · exact back (listed 6 (by decide)) (by decide)
        (DefinitionStep.mapConst f (fixName (by decide)) (mapConst_plain fixes (by decide)) h)
    · exact back (listed 7 (by decide)) (by decide)
        (DefinitionStep.mapConst f (fixName (by decide)) (mapConst_plain fixes (by decide)) h)
    · exact back (listed 8 (by decide)) (by decide)
        (DefinitionStep.mapConst f (fixName (by decide)) (mapConst_plain fixes (by decide)) h)
    · refine back (listed 9 (by decide)) (by decide) (RecursionStep.mapConst f
        (fixName (by decide)) fixCtors fixDefault ?_ h)
      intro entry mem
      simp only [ctors, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> exact mapConst_plain fixes (by decide)
    · exact back (listed 10 (by decide)) (by decide)
        (DefinitionStep.mapConst f (fixName (by decide)) (mapConst_plain fixes (by decide)) h)
    · exact back (listed 11 (by decide)) (by decide)
        (DefinitionStep.mapConst f (fixName (by decide)) (mapConst_plain fixes (by decide)) h)
  · refine .inr (DecoderStep.mapConst f (fixName (by decide)) (fixName (by decide))
      (fun {a A} carrier => ?_) (fun {c A} carrier => ?_) (fun {a A} carrier => ?_)
      (fun {c A} carrier => ?_) step)
    · change (SetProfile.allInstance? a).map typeTerm = some A at carrier
      cases found : SetProfile.allInstance? a with
      | none => rw [found] at carrier; cases carrier
      | some type =>
          rw [SetProfile.allInstance?_eq_some found]
          exact fixName (plainName_allName type)
    · change (if true then (SetProfile.eqInstance? c).map typeTerm else none) = some A at carrier
      rw [if_pos rfl] at carrier
      cases found : SetProfile.eqInstance? c with
      | none => rw [found] at carrier; cases carrier
      | some type =>
          rw [SetProfile.eqInstance?_eq_some found]
          exact fixName (plainName_eqName type)
    · change (SetProfile.allInstance? a).map typeTerm = some A at carrier
      cases found : SetProfile.allInstance? a with
      | none => rw [found] at carrier; cases carrier
      | some type =>
          rw [found] at carrier
          cases carrier
          exact mapConst_typeTerm fixes type
    · change (if true then (SetProfile.eqInstance? c).map typeTerm else none) = some A at carrier
      rw [if_pos rfl] at carrier
      cases found : SetProfile.eqInstance? c with
      | none => rw [found] at carrier; cases carrier
      | some type =>
          rw [found] at carrier
          cases carrier
          exact mapConst_typeTerm fixes type

/-- The root steps of the object package are headed by constants that spell no
level. -/
theorem objectRules_step_head {n : Nat} {l r : Tower.Tm n}
    (step : objectRules.computation.step l r) :
    ∃ c args, l = appSpine (.const c) args ∧ readLevel c = none := by
  rcases step with step | step
  · obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
    have listedIn := (List.mem_filter.mp mem).1
    simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listedIn
    rcases listedIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨args, e⟩ := iotaComputation_headed h; exact ⟨_, args, e, rfl⟩
    · obtain ⟨args, e⟩ := recursionComputation_headed h; exact ⟨_, args, e, rfl⟩
    · obtain ⟨args, e⟩ := recursionComputation_headed h; exact ⟨_, args, e, rfl⟩
    · obtain ⟨args, e⟩ := eliminatorComputation_headed h; exact ⟨_, args, e, rfl⟩
    · obtain ⟨args, e⟩ := definitionComputation_headed h; exact ⟨_, args, e, rfl⟩
    · obtain ⟨args, e⟩ := definitionComputation_headed h; exact ⟨_, args, e, rfl⟩
    · obtain ⟨args, e⟩ := definitionComputation_headed h; exact ⟨_, args, e, rfl⟩
    · obtain ⟨args, e⟩ := definitionComputation_headed h; exact ⟨_, args, e, rfl⟩
    · obtain ⟨args, e⟩ := definitionComputation_headed h; exact ⟨_, args, e, rfl⟩
    · obtain ⟨args, e⟩ := recursionComputation_headed h; exact ⟨_, args, e, rfl⟩
    · obtain ⟨args, e⟩ := definitionComputation_headed h; exact ⟨_, args, e, rfl⟩
    · obtain ⟨args, e⟩ := definitionComputation_headed h; exact ⟨_, args, e, rfl⟩
  · obtain ⟨args, e⟩ := decoderComputation_headed _ step
    exact ⟨_, args, e, rfl⟩

/-! ## Erasing the levels of the instances -/

/-- **Erasing the levels of the instances**: every instance of identity elimination
to `id:eliminate`, every instance of the recursor to `num-rec`, and every other
name to itself. -/
def eraseLevels (name : DeclName) : DeclName :=
  match jLevels? name with
  | some _ => jName
  | none =>
      match numRecLevel? name with
      | some _ => numRecName
      | none => name

@[simp] theorem eraseLevels_jAt (lu lw : LevelExpr) : eraseLevels (jAt lu lw) = jName := by
  simp only [eraseLevels, jLevels?_jAt]

@[simp] theorem eraseLevels_numRecAt (lr : LevelExpr) : eraseLevels (numRecAt lr) = numRecName := by
  simp only [eraseLevels, jLevels?_numRecAt, numRecLevel?_numRecAt]

theorem eraseLevels_of_readLevel {name : DeclName} (plain : readLevel name = none) :
    eraseLevels name = name := by
  simp only [eraseLevels, jLevels?_of_readLevel plain, numRecLevel?_of_readLevel plain]

theorem eraseLevels_plain : ∀ c, plainName c = true → eraseLevels c = c := by
  intro c plain
  simp only [plainName, Bool.and_eq_true, Option.isNone_iff_eq_none] at plain
  exact eraseLevels_of_readLevel plain.1.1

/-- **Erasing levels sends every root step of the package with every instance to a
root step of the object package.** -/
theorem objectRulesInstances_eraseLevels {n : Nat} {l r : Tower.Tm n}
    (step : objectRulesInstances.computation.step l r) :
    objectRules.computation.step (l.mapConst eraseLevels) (r.mapConst eraseLevels) := by
  rcases step with step | step
  · rcases objectRules_step_cases step with h | h | h | h
    · have h' := eliminatorComputation_mapConst eraseLevels h
      rw [eraseLevels_of_readLevel rfl] at h'
      exact .inl (RootComputation.step_unionAll
        (List.mem_filter.mpr ⟨listed 3 (by decide), rfl⟩) h')
    · have h' := IotaStep.mapConst eraseLevels (fun entry mem => by
        simp only [ctors, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl <;> rfl) h
      rw [eraseLevels_of_readLevel rfl] at h'
      exact .inl (RootComputation.step_unionAll
        (List.mem_filter.mpr ⟨listed 0 (by decide), rfl⟩) h')
    · have h' := DefinitionStep.mapConst eraseLevels (rfl : eraseLevels sucMoveName = sucMoveName)
        (Tm.mapConst_eq_self eraseLevels
          (p := fun c => (readLevel c).isNone) (fun c plain => eraseLevels_of_readLevel
            (Option.isNone_iff_eq_none.mp plain)) (by decide)) h
      exact .inl (RootComputation.step_unionAll
        (List.mem_filter.mpr ⟨listed 5 (by decide), rfl⟩) h')
    · exact plainRules_sub_objectRules (plainRules_step_mapConst eraseLevels_plain rfl h)
  · rcases step with ⟨lu, lw, h⟩ | ⟨lr, h⟩
    · have h' := eliminatorComputation_mapConst eraseLevels h
      rw [eraseLevels_jAt] at h'
      exact .inl (RootComputation.step_unionAll
        (List.mem_filter.mpr ⟨listed 3 (by decide), rfl⟩) h')
    · have h' := IotaStep.mapConst eraseLevels (fun entry mem => by
        simp only [ctors, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl <;> rfl) h
      rw [eraseLevels_numRecAt] at h'
      exact .inl (RootComputation.step_unionAll
        (List.mem_filter.mpr ⟨listed 0 (by decide), rfl⟩) h')

/-- The declared types of the package with every instance are fixed by erasing
levels. -/
theorem objectRulesInstances_type_erased {name : DeclName} {type : Tower.Tm 0}
    (declared : objectRulesInstances.constantType name = some type) :
    type.mapConst eraseLevels = type := by
  rcases objectRulesInstances_declared_cases declared with
    ⟨lu, lw, -, rfl⟩ | ⟨lr, -, rfl⟩ | ⟨-, -, declared'⟩
  · exact mapConst_plain eraseLevels_plain rfl
  · exact mapConst_plain eraseLevels_plain rfl
  · exact objectRules_type_fixed eraseLevels_plain declared'

/-! ## Instantiating the package at every level -/

/-- **Instantiating the package at every level**: identity elimination to its
instance at `lu lw`, the recursor to its instance at `lr`, every other name to
itself. -/
def instanceRenaming (lu lw lr : LevelExpr) (name : DeclName) : DeclName :=
  if name = jName then jAt lu lw else if name = numRecName then numRecAt lr else name

section Instantiate

variable (lu lw lr : LevelExpr)

@[simp] theorem instanceRenaming_j : instanceRenaming lu lw lr jName = jAt lu lw := by
  simp only [instanceRenaming, if_pos]

@[simp] theorem instanceRenaming_numRec : instanceRenaming lu lw lr numRecName = numRecAt lr := by
  unfold instanceRenaming
  rw [if_neg (by decide), if_pos rfl]

theorem instanceRenaming_plain : ∀ c, plainName c = true → instanceRenaming lu lw lr c = c := by
  intro c plain
  simp only [plainName, Bool.and_eq_true, bne_iff_ne, ne_eq] at plain
  unfold instanceRenaming
  rw [if_neg plain.1.2, if_neg plain.2]

/-- **The object package at every level without `sucMove`'s equation**: its
declarations, and every rule of the object package other than `sucMove`'s
equation. -/
def objectRulesAtWithoutSucMove : Rules Tower.Head :=
  { objectRulesAt lu lw lr with
    computation := (programCodes.extend (stage fun name => name != sucMoveName)).computation }

/-- **Instantiating renames the package at every level, without `sucMove`'s
equation, into the package with every instance**: its universe rules are kept,
each declaration is sent to a declaration at the renamed type, and each root step
to a root step. -/
theorem objectRulesAtWithoutSucMove_renames :
    RulesRenaming (objectRulesAtWithoutSucMove lu lw lr) objectRulesInstances
      (instanceRenaming lu lw lr) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := by
    intro name type declared
    change (objectRulesAt lu lw lr).constantType name = some type at declared
    by_cases hj : name = jName
    · subst hj
      rw [objectRulesAt_j] at declared
      cases declared
      rw [instanceRenaming_j, objectRulesInstances_j, mapConst_plain (instanceRenaming_plain lu lw lr) rfl]
    by_cases hr : name = numRecName
    · subst hr
      rw [objectRulesAt_numRec] at declared
      cases declared
      rw [instanceRenaming_numRec, objectRulesInstances_numRec,
        mapConst_plain (instanceRenaming_plain lu lw lr) rfl]
    rw [objectRulesAt_other lu lw lr hj hr] at declared
    have fixName : instanceRenaming lu lw lr name = name := by
      unfold instanceRenaming
      rw [if_neg hj, if_neg hr]
    rw [fixName, objectRules_type_fixed (instanceRenaming_plain lu lw lr) declared,
      objectRulesInstances_other (readLevel_of_declared declared)]
    exact declared
  computation := by
    intro n l r step
    have fixCtors : ∀ entry ∈ ctors, instanceRenaming lu lw lr entry.1 = entry.1 := by
      intro entry mem
      simp only [ctors, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> exact instanceRenaming_plain lu lw lr _ (by decide)
    rcases step with step | step
    · obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
      obtain ⟨listedIn, allowed⟩ := List.mem_filter.mp mem
      have plain : ∀ {e : DeclName × RootComputation Tower.Head}, e ∈ computations →
          plainEquation e.1 = true → e.2.step l r →
          objectRulesInstances.computation.step ((l.mapConst (instanceRenaming lu lw lr)))
            (r.mapConst (instanceRenaming lu lw lr)) :=
        fun {_} listed ok h' => .inl (plainRules_sub_objectRules
          (plainRules_step_mapConst (instanceRenaming_plain lu lw lr) rfl
            (.inl (RootComputation.step_unionAll (List.mem_filter.mpr ⟨listed, ok⟩) h'))))
      simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listedIn
      rcases listedIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have h' := IotaStep.mapConst (instanceRenaming lu lw lr) fixCtors h
        rw [instanceRenaming_numRec] at h'
        exact .inr (.inr ⟨lr, h'⟩)
      · exact plain (listed 1 (by decide)) (by decide) h
      · exact plain (listed 2 (by decide)) (by decide) h
      · have h' := eliminatorComputation_mapConst (instanceRenaming lu lw lr) h
        rw [instanceRenaming_j] at h'
        exact .inr (.inl ⟨lu, lw, h'⟩)
      · exact plain (listed 4 (by decide)) (by decide) h
      · exact absurd allowed (by decide)
      · exact plain (listed 6 (by decide)) (by decide) h
      · exact plain (listed 7 (by decide)) (by decide) h
      · exact plain (listed 8 (by decide)) (by decide) h
      · exact plain (listed 9 (by decide)) (by decide) h
      · exact plain (listed 10 (by decide)) (by decide) h
      · exact plain (listed 11 (by decide)) (by decide) h
    · exact .inl (plainRules_sub_objectRules
        (plainRules_step_mapConst (instanceRenaming_plain lu lw lr) rfl (.inr step)))

/-- **Instantiating preserves derivability**: typing, typed equality and
inclusion of the package at every level without `sucMove`'s equation hold in the
package with every instance once instantiated. -/
theorem objectRulesAtWithoutSucMove_embeds {st : Statement Tower.Head}
    (derivation : Derivable (objectRulesAtWithoutSucMove lu lw lr) st) :
    Derivable objectRulesInstances (st.mapConst (instanceRenaming lu lw lr)) :=
  Derivable.mapConst (objectRulesAtWithoutSucMove_renames lu lw lr) derivation

/-- **Instantiating preserves reduction.** -/
theorem objectRulesAtWithoutSucMove_reduces {n : Nat} {t u : Tower.Tm n}
    (step : StrongNormalization.Reduces (objectRulesAtWithoutSucMove lu lw lr) t u) :
    StrongNormalization.Reduces objectRulesInstances (t.mapConst (instanceRenaming lu lw lr))
      (u.mapConst (instanceRenaming lu lw lr)) :=
  Reduces.mapConst (objectRulesAtWithoutSucMove_renames lu lw lr).computation step

/-- The package at every level without `sucMove`'s equation is contained in the
package at every level. -/
theorem objectRulesAtWithoutSucMove_sub : RulesSub (objectRulesAtWithoutSucMove lu lw lr)
    (objectRulesAt lu lw lr) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := id
  computation := fun step => by
    rcases step with step | step
    · exact .inl ((stage_sub fun _ _ => rfl).computation step)
    · exact .inr step

/-- **The language's declaration without `sucMove`'s equation embeds** by renaming
identity elimination to `jAt (param 0) (param 1)` and the recursor to
`numRecAt (param 2)`. -/
theorem polyRulesWithoutSucMove_embeds {st : Statement Tower.Head}
    (derivation : Derivable (objectRulesAtWithoutSucMove (.param 0) (.param 1) (.param 2)) st) :
    Derivable objectRulesInstances
      (st.mapConst (instanceRenaming (.param 0) (.param 1) (.param 2))) :=
  objectRulesAtWithoutSucMove_embeds _ _ _ derivation

/-- The right-hand side of `sucMove`'s equation is an elimination by the
package's own `id:eliminate`. -/
theorem sucMoveRhs_spine : ∃ args, sucMoveRhs = appSpine (.const jName) args :=
  ⟨[Package.numT, SetProfile.addNative SetProfile.zeroNative (.var 1), Package.sucMotive (.var 1),
    .refl (SetProfile.sucNative (SetProfile.addNative SetProfile.zeroNative (.var 1))), .var 1,
    .var 0], rfl⟩

/-- **Instantiating does not preserve `sucMove`'s equation**: at any arguments,
the equation of the package at every level, renamed, is no root step of the
package with every instance, whose `sucMove` computes with `id:eliminate`
itself. -/
theorem sucMove_renamed_not_step {n : Nat} (σ : Sub Tower.Head 2 n) :
    ¬ objectRulesInstances.computation.step
      ((applyClosed Package.eqAtTelescope σ (.const sucMoveName)).mapConst
        (instanceRenaming lu lw lr))
      ((Presentation.subst σ sucMoveRhs).mapConst (instanceRenaming lu lw lr)) := by
  intro step
  have fixName : instanceRenaming lu lw lr sucMoveName = sucMoveName :=
    instanceRenaming_plain lu lw lr _ (by decide)
  have lhs : (applyClosed Package.eqAtTelescope σ (.const sucMoveName)).mapConst
      (instanceRenaming lu lw lr) = applyClosed Package.eqAtTelescope
        (fun i => (σ i).mapConst (instanceRenaming lu lw lr)) (.const sucMoveName) := by
    rw [Tm.mapConst_applyClosed]
    simp only [Tm.mapConst, fixName]
  rw [lhs] at step
  have own : objectRules.computation.step
      (applyClosed Package.eqAtTelescope (fun i => (σ i).mapConst (instanceRenaming lu lw lr))
        (.const sucMoveName))
      (Presentation.subst (fun i => (σ i).mapConst (instanceRenaming lu lw lr)) sucMoveRhs) :=
    .inl (RootComputation.step_unionAll (List.mem_filter.mpr ⟨listed 5 (by decide), rfl⟩)
      ⟨_, rfl, rfl⟩)
  rcases step with step | ⟨⟨lu', lw', h⟩ | ⟨lr', h⟩⟩
  · have same := objectShape.deterministic own step
    obtain ⟨args, rhs⟩ := sucMoveRhs_spine
    rw [Tm.mapConst_subst, rhs, Tm.mapConst_appSpine, subst_appSpine, subst_appSpine] at same
    have heads := (appSpine_const_injective same).1
    simp only [instanceRenaming_j] at heads
    exact jAt_ne_jName lu lw heads.symm
  · obtain ⟨args, e⟩ := eliminatorComputation_headed h
    rw [applyClosed_eq_appSpine] at e
    exact appendLevel_ne_str _ _ .anonymous "sucMove" (appSpine_const_injective e).1.symm
  · obtain ⟨args, e⟩ := iotaComputation_headed h
    rw [applyClosed_eq_appSpine] at e
    exact appendLevel_ne_str _ _ .anonymous "sucMove" (appSpine_const_injective e).1.symm

end Instantiate

/-! ## Roles and root shape -/

/-- **The roles of the package with every instance**: each instance has the role of
its constant, and every other name its role in the object package. -/
def instanceRoles : Roles Tower.Head := fun name => objectRoles (eraseLevels name)

theorem objectRoles_jName :
    objectRoles jName = .computes 6 (.split 5 .constructor fun _ => .leaf) :=
  (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_j

theorem objectRoles_numRecName :
    objectRoles numRecName = .computes 4 (.split 3 .constructor fun _ => .leaf) :=
  (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_numRec

theorem instanceRoles_jAt (lu lw : LevelExpr) :
    instanceRoles (jAt lu lw) = .computes 6 (.split 5 .constructor fun _ => .leaf) := by
  simp only [instanceRoles, eraseLevels_jAt]
  exact objectRoles_jName

theorem instanceRoles_numRecAt (lr : LevelExpr) :
    instanceRoles (numRecAt lr) = .computes 4 (.split 3 .constructor fun _ => .leaf) := by
  simp only [instanceRoles, eraseLevels_numRecAt]
  exact objectRoles_numRecName

theorem instanceRoles_of_readLevel {name : DeclName} (plain : readLevel name = none) :
    instanceRoles name = objectRoles name := by
  simp only [instanceRoles, eraseLevels_of_readLevel plain]

/-- A name ending in a numeric component is rigid in the object package. -/
theorem objectRoles_num_name (p : DeclName) (k : Nat) : objectRoles (.num p k) = .rigid := by
  have notMem : Lean.Name.num p k ∉ nonrigidNames := by
    intro mem
    simp only [nonrigidNames, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h
  rw [objectRoles_of (fun h => by cases h) (fun h => by cases h) rfl rfl]
  exact roles_of_not_mem notMem

/-- A name that is not rigid in the object package spells no level. -/
theorem readLevel_of_nonrigid {name : DeclName} (nonrigid : objectRoles name ≠ .rigid) :
    readLevel name = none := by
  cases name with
  | anonymous => rfl
  | str p s => rfl
  | num p k => exact absurd (objectRoles_num_name p k) nonrigid

/-- The inspections of the object package's computing constants test constructor
forms only. -/
theorem objectRoles_onlyConstructors {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (role : objectRoles c = .computes arity inspect) : inspect.OnlyConstructors := by
  unfold objectRoles at role
  split_ifs at role
  · cases role
    exact .split fun _ => .leaf
  · exact roles_onlyConstructors role

/-- The constructors of the package with every instance are the object
package's. -/
theorem instanceConstructorsDeclared : ConstructorsDeclared instanceRoles where
  arity := by
    intro T cs k fields role mem
    obtain ⟨sameT, rfl⟩ := objectRoles_inductive role
    have hk : readLevel k = none := by
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    rw [instanceRoles_of_readLevel hk]
    exact objectConstructorsDeclared.arity (T := numN) objectRoles_num mem
  distinct := by
    intro T cs role
    obtain ⟨-, rfl⟩ := objectRoles_inductive role
    exact objectConstructorsDeclared.distinct objectRoles_num

theorem instanceRoles_num : instanceRoles numN = .inductive ctors :=
  (instanceRoles_of_readLevel rfl).trans objectRoles_num

/-- **Root shape of the package with every instance** under its roles: each root
step occurs at a spine of a computing constant of exact arity whose inspected
values have the forms its role requires, the step of an instance as the step of
its constant, and at most one root step applies. -/
theorem instanceShape : RootShape objectRulesInstances instanceRoles where
  spine := by
    intro n t u step
    rcases step with step | ⟨⟨lu, lw, h⟩ | ⟨lr, h⟩⟩
    · obtain ⟨c, arity, inspect, args, role, rfl, length, accepts⟩ := objectShape.spine step
      obtain ⟨c', args', same, plain⟩ := objectRules_step_head step
      obtain ⟨rfl, -⟩ := appSpine_const_injective same
      refine ⟨c, arity, inspect, args, (instanceRoles_of_readLevel plain).trans role, rfl, length,
        accepts.of_constructors (fun {k a} constructor => ?_) (objectRoles_onlyConstructors role)⟩
      rw [instanceRoles_of_readLevel (readLevel_of_nonrigid (by rw [constructor]; exact nofun))]
      exact constructor
    · exact eliminatorComputation_spine (instanceRoles_jAt lu lw) h
    · exact IotaStep.spine (T := numN) instanceRoles_num (instanceRoles_numRecAt lr)
        instanceConstructorsDeclared h
  deterministic := by
    intro n t u u' step step'
    have plainHead : ∀ {v : Tower.Tm n}, objectRules.computation.step t v →
        ∀ {c : DeclName} {args : List (Tower.Tm n)}, t = appSpine (.const c) args →
          readLevel c = none := by
      intro v h c args e
      obtain ⟨c', args', e', plain⟩ := objectRules_step_head h
      obtain ⟨rfl, -⟩ := appSpine_const_injective (e.symm.trans e')
      exact plain
    rcases step with step | ⟨⟨lu, lw, h⟩ | ⟨lr, h⟩⟩ <;>
      rcases step' with step' | ⟨⟨lu', lw', h'⟩ | ⟨lr', h'⟩⟩
    · exact objectShape.deterministic step step'
    · obtain ⟨args, e⟩ := eliminatorComputation_headed h'
      have := plainHead step e
      simp only [jAt, readLevel_appendLevel] at this
      cases this
    · obtain ⟨args, e⟩ := iotaComputation_headed h'
      have := plainHead step e
      simp only [numRecAt, readLevel_appendLevel] at this
      cases this
    · obtain ⟨args, e⟩ := eliminatorComputation_headed h
      have := plainHead step' e
      simp only [jAt, readLevel_appendLevel] at this
      cases this
    · obtain ⟨args, e⟩ := eliminatorComputation_headed h
      obtain ⟨args', e'⟩ := eliminatorComputation_headed h'
      obtain ⟨rfl, rfl⟩ := jAt_inj (appSpine_const_injective (e.symm.trans e')).1
      exact (eliminatorComputation_deterministic h h').symm
    · obtain ⟨args, e⟩ := eliminatorComputation_headed h
      obtain ⟨args', e'⟩ := iotaComputation_headed h'
      exact absurd (appSpine_const_injective (e.symm.trans e')).1 (jAt_ne_numRecAt lu lw lr')
    · obtain ⟨args, e⟩ := iotaComputation_headed h
      have := plainHead step' e
      simp only [numRecAt, readLevel_appendLevel] at this
      cases this
    · obtain ⟨args, e⟩ := iotaComputation_headed h
      obtain ⟨args', e'⟩ := eliminatorComputation_headed h'
      exact absurd (appSpine_const_injective (e'.symm.trans e)).1 (jAt_ne_numRecAt lu' lw' lr)
    · obtain ⟨args, e⟩ := iotaComputation_headed h
      obtain ⟨args', e'⟩ := iotaComputation_headed h'
      obtain rfl := numRecAt_inj (appSpine_const_injective (e.symm.trans e')).1
      exact (IotaStep.deterministic (T := numN) objectRoles_num objectConstructorsDeclared h h').symm

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
