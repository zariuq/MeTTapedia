import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConversionCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHead

/-!
# Declaring further constants

`withConstants R types` is the rule package `R` with further constants
declared: a name listed in `types` has its listed type, and every other name
keeps the type `R` declares. Universes, head equality and root computation are
those of `R`.

Declared types do not enter reduction. So the package with further constants
is Church–Rosser exactly when `R` is (`churchRosser_withConstants`), and it
meets the root-shape obligations of weak-head reduction under given roles
exactly when `R` does (`rootShape_withConstants`).

The package with further constants contains `R` when `R` declares no listed
name (`withConstants_sub`); every derivation of `R` is then a derivation of
it. Listing the same constants is monotone in the package
(`withConstants_mono`).

Positive example: the object package extended by the case trees of `max`,
`half` and `pick`, with the three names declared at their types, is
Church–Rosser and has root shape because the extension without the declared
types is (`ObjectCaseTrees.treeRules_churchRosser`,
`ObjectCaseTrees.treeRules_rootShape`). Negative example: a package that
declares every name at its one head, with every name listed at another type,
is not contained in the result
(`ConstantDeclarationControls.everyName_not_sub`), so the inclusion needs the
listed names to be new.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open ConversionCoherence (ChurchRosser)

variable {Head : Type}

/-- The package `R` with further constants declared: a name listed in `types`
has its listed type, and every other name the type `R` declares. -/
def withConstants (R : Rules Head) (types : DeclName → Option (Tm Head 0)) : Rules Head :=
  { R with constantType := fun name => (types name).orElse fun _ => R.constantType name }

section Laws

variable {R : Rules Head} {types : DeclName → Option (Tm Head 0)}

/-- A listed name is declared at its listed type. -/
theorem withConstants_listed {name : DeclName} {type : Tm Head 0}
    (listed : types name = some type) :
    (withConstants R types).constantType name = some type :=
  congrArg (fun known => known.orElse fun _ => R.constantType name) listed

/-- A name that is not listed keeps the type `R` declares. -/
theorem withConstants_unlisted {name : DeclName} (unlisted : types name = none) :
    (withConstants R types).constantType name = R.constantType name :=
  congrArg (fun known => known.orElse fun _ => R.constantType name) unlisted

/-- The package with further constants has the root steps of `R`. -/
theorem withConstants_step {n : Nat} {t u : Tm Head n} :
    (withConstants R types).computation.step t u ↔ R.computation.step t u :=
  Iff.rfl

/-- The package with further constants contains `R`, when `R` declares no
listed name. -/
theorem withConstants_sub
    (fresh : ∀ {name : DeclName} {type : Tm Head 0}, types name = some type →
      R.constantType name = none) :
    RulesSub R (withConstants R types) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := by
    intro name type declared
    cases listed : types name with
    | none => exact (withConstants_unlisted listed).trans declared
    | some listedType => cases (fresh listed).symm.trans declared
  computation := id

/-- Listing the same constants is monotone in the package. -/
theorem withConstants_mono {R' : Rules Head} (sub : RulesSub R R') :
    RulesSub (withConstants R types) (withConstants R' types) where
  headTyping := sub.headTyping
  isUniverse := sub.isUniverse
  join := sub.join
  cumulative := sub.cumulative
  headEq := sub.headEq
  constantType := by
    intro name type declared
    cases listed : types name with
    | none =>
        rw [withConstants_unlisted listed] at declared ⊢
        exact sub.constantType declared
    | some listedType =>
        rw [withConstants_listed listed] at declared ⊢
        exact declared
  computation := sub.computation

/-- **Declared types do not enter reduction**: the package with further
constants meets the root-shape obligations exactly when `R` does. -/
theorem rootShape_withConstants {roles : Roles Head} :
    RootShape (withConstants R types) roles ↔ RootShape R roles :=
  ⟨fun shape => ⟨shape.spine, shape.deterministic⟩,
    fun shape => ⟨shape.spine, shape.deterministic⟩⟩

/-- **Declared types do not enter reduction**: the package with further
constants is Church–Rosser exactly when `R` is. -/
theorem churchRosser_withConstants :
    ChurchRosser (withConstants R types) ↔ ChurchRosser R :=
  Iff.rfl

end Laws

/-! ## The listed names must be new for the inclusion -/

namespace ConstantDeclarationControls

/-- A package over one head that declares every name at the head. -/
def everyName : Rules Unit where
  headTyping := fun _ _ => False
  isUniverse := fun _ => False
  join := fun _ _ _ => False
  cumulative := fun _ _ => False
  headEq := fun _ _ => False
  constantType := fun _ => some (.head ())

/-- Every name listed at the constant `c`. -/
def relisted : DeclName → Option (Tm Unit 0) := fun _ => some (.const `c)

/-- The listed type replaces the declared one. -/
theorem relisted_declared (name : DeclName) :
    (withConstants everyName relisted).constantType name = some (.const `c) :=
  withConstants_listed rfl

/-- **Without new names there is no inclusion**: a package that declares a
name at one type is not contained in the package that lists the name at
another. -/
theorem everyName_not_sub : ¬ RulesSub everyName (withConstants everyName relisted) := by
  intro sub
  have declared : (withConstants everyName relisted).constantType `c = some (.head ()) :=
    sub.constantType (name := `c) rfl
  cases (relisted_declared `c).symm.trans declared

end ConstantDeclarationControls

/-! ## Axiom audit -/

#print axioms withConstants_listed
#print axioms withConstants_unlisted
#print axioms withConstants_step
#print axioms withConstants_sub
#print axioms withConstants_mono
#print axioms rootShape_withConstants
#print axioms churchRosser_withConstants
#print axioms ConstantDeclarationControls.relisted_declared
#print axioms ConstantDeclarationControls.everyName_not_sub

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
