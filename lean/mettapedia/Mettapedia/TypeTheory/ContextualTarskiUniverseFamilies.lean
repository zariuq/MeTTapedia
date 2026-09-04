import Mettapedia.TypeTheory.ContextualModalCapabilities
import Mettapedia.TypeTheory.TarskiUniverseCapabilities

/-!
# Level-indexed Tarski universes over contextual structure

`TarskiUniverseFormation` supplies one internal universe object and a decoding
operation.  A hierarchy requires additional, independently selectable data:
an index of levels, substitution stability, code lifting, and closure under
chosen type formers.  This module separates those capabilities without
selecting a dependent calculus or a semantic model.

An internal decoded code is a type object of the contextual structure, not a
Lean type.  `externalizeAt` therefore takes an explicit interpretation of
internal type objects before producing a semantic `TarskiCodeFamily`.  This
keeps syntax, hierarchy policy, and model interpretation distinct.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualTarskiUniverseFamilies

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.ContextualModalCapabilities
open Mettapedia.TypeTheory.TarskiUniverseCapabilities

universe uLevel uSemantic

/-- A level-indexed family of internal Tarski universes over one contextual
core.  No ordering, cumulativity, closure, or substitution law is included. -/
structure ContextualTarskiUniverseFamily (Level : Type uLevel)
    (modes : ModeTheory) (core : ModeIndexedContextualCore modes) where
  univ : {mode : modes.Mode} → (context : core.Con mode) →
    Level → core.Ty context
  el : {mode : modes.Mode} → {context : core.Con mode} →
    {level : Level} → core.Tm context (univ context level) → core.Ty context

namespace ContextualTarskiUniverseFamily

variable {Level : Type uLevel} {modes : ModeTheory}
  {core : ModeIndexedContextualCore modes}

/-- Transport an internal term along equality of its internal types. -/
def castTm {mode : modes.Mode} {context : core.Con mode}
    {first second : core.Ty context} (equalTypes : first = second)
    (term : core.Tm context first) : core.Tm context second := by
  subst second
  exact term

/-- Substitution stability of every universe level and its decoding
operation. -/
structure SubstitutionStable
    (family : ContextualTarskiUniverseFamily Level modes core) where
  univ_natural : ∀ {mode : modes.Mode}
    {source target : core.Con mode} (level : Level)
    (substitution : core.Sub source target),
    core.tySub (family.univ target level) substitution =
      family.univ source level
  el_natural : ∀ {mode : modes.Mode}
    {source target : core.Con mode} {level : Level}
    (code : core.Tm target (family.univ target level))
    (substitution : core.Sub source target),
    family.el
        (castTm (univ_natural level substitution)
          (core.tmSub code substitution)) =
      core.tySub (family.el code) substitution

/-- Strict internal cumulativity along a separately supplied level relation.
The decoded internal type object is preserved exactly.  A weaker notion based
on internal equivalence requires an equivalence structure on the core and is
deliberately not manufactured here. -/
structure StrictlyCumulative
    (family : ContextualTarskiUniverseFamily Level modes core)
    (Below : Level → Level → Prop) where
  liftCode : ∀ {lower upper}, Below lower upper →
    {mode : modes.Mode} → {context : core.Con mode} →
    core.Tm context (family.univ context lower) →
      core.Tm context (family.univ context upper)
  el_liftCode : ∀ {lower upper} (below : Below lower upper)
    {mode : modes.Mode} {context : core.Con mode}
    (code : core.Tm context (family.univ context lower)),
    family.el (liftCode below code) = family.el code

/-- Closure of an internal universe family under a selected dependent-product
formation.  This is code closure, not function extensionality. -/
structure PiClosed
    (family : ContextualTarskiUniverseFamily Level modes core)
    (products : DependentProductFormation modes core) where
  piCode : ∀ {mode : modes.Mode} {context : core.Con mode}
    {level : Level}
    (domainCode : core.Tm context (family.univ context level))
    (_codomainCode :
      core.Tm (core.ext context (family.el domainCode))
        (family.univ (core.ext context (family.el domainCode)) level)),
    core.Tm context (family.univ context level)
  el_piCode : ∀ {mode : modes.Mode} {context : core.Con mode}
    {level : Level}
    (domainCode : core.Tm context (family.univ context level))
    (codomainCode :
      core.Tm (core.ext context (family.el domainCode))
        (family.univ (core.ext context (family.el domainCode)) level)),
    family.el (piCode domainCode codomainCode) =
      products.pi (family.el domainCode) (family.el codomainCode)

/-- Select one level as an ordinary one-universe formation. -/
def atLevel (family : ContextualTarskiUniverseFamily Level modes core)
    (level : Level) : TarskiUniverseFormation modes core where
  univ := fun context => family.univ context level
  el := fun code => family.el code

/-- Promote an ordinary one-universe formation to a unit-indexed family. -/
def oneLevel (formation : TarskiUniverseFormation modes core) :
    ContextualTarskiUniverseFamily PUnit modes core where
  univ := fun context _ => formation.univ context
  el := fun code => formation.el code

/-- Selecting the unique level after promotion recovers the original
formation definitionally. -/
theorem atLevel_oneLevel
    (formation : TarskiUniverseFormation modes core) :
    (oneLevel formation).atLevel PUnit.unit = formation :=
  rfl

/-- Promotion to a unit-indexed family loses no one-universe information. -/
theorem oneLevel_injective :
    Function.Injective
      (oneLevel : TarskiUniverseFormation modes core →
        ContextualTarskiUniverseFamily PUnit modes core) := by
  intro first second equalFamilies
  have selectedEqual := congrArg
    (fun family : ContextualTarskiUniverseFamily PUnit modes core =>
      family.atLevel PUnit.unit)
    equalFamilies
  simpa only [atLevel_oneLevel] using selectedEqual

/-- Externally interpret the codes at one context.  The interpretation is an
explicit parameter because an internal type object is not itself a semantic
type. -/
def externalizeAt
    (family : ContextualTarskiUniverseFamily Level modes core)
    {mode : modes.Mode} (context : core.Con mode)
    (interpret : core.Ty context → Type uSemantic) :
    TarskiCodeFamily.{uLevel, 0, uSemantic} where
  Level := Level
  Code := fun level => core.Tm context (family.univ context level)
  El := fun _level code => interpret (family.el code)

/-- A strict internal cumulative lift becomes semantic cumulativity under
every independently supplied interpretation. -/
def StrictlyCumulative.externalCumulative
    {family : ContextualTarskiUniverseFamily Level modes core}
    {Below : Level → Level → Prop}
    (cumulative : family.StrictlyCumulative Below)
    {mode : modes.Mode} (context : core.Con mode)
    (interpret : core.Ty context → Type uSemantic) :
    (family.externalizeAt context interpret).Cumulative Below where
  lift := fun below code => cumulative.liftCode below code
  decodeLift := by
    intro lower upper below code
    change interpret (family.el (cumulative.liftCode below code)) ≃
      interpret (family.el code)
    rw [cumulative.el_liftCode below code]

/-! ## Positive and negative controls -/

open UniverseChoiceCanary

/-- The embedding/extraction control is positive on an actual contextual
universe formation. -/
example :
    (oneLevel falseUniverse).atLevel PUnit.unit = falseUniverse :=
  atLevel_oneLevel falseUniverse

/-- The same contextual core can still carry distinct unit-indexed universe
families.  Introducing a hierarchy interface does not choose its universe. -/
theorem oneLevel_universe_choices_distinct :
    oneLevel falseUniverse ≠ oneLevel trueUniverse := by
  intro equalFamilies
  exact universe_formations_distinct (oneLevel_injective equalFamilies)

end ContextualTarskiUniverseFamily

#print axioms ContextualTarskiUniverseFamily.atLevel_oneLevel
#print axioms ContextualTarskiUniverseFamily.oneLevel_injective
#print axioms ContextualTarskiUniverseFamily.oneLevel_universe_choices_distinct

end Mettapedia.TypeTheory.ContextualTarskiUniverseFamilies
