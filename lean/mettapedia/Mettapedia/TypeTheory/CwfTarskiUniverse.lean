import Mettapedia.TypeTheory.ContextualIdentityTypes
import Mettapedia.TypeTheory.ContextualProductComparison
import Mettapedia.TypeTheory.ContextualSumComparison

/-!
# Tarski universes over universe-polymorphic CwFs

This module states Tarski-universe structure directly over the
universe-polymorphic `Cwf` interface.  It complements the mode-indexed
formation comparison: the latter is useful for modal decomposition, while
this interface can express the standard set-family model one metatheoretic
universe above the types it codes.

Universe formation, substitution stability, and closure under dependent
products and sums remain separate capabilities.  The canonical families CwF
at level `u+1` contains a universe whose codes are the types in `Type u`.
Decoding is evaluation through an explicit universe lift.  Semantic Π/Σ
closure holds by canonical fibrewise equivalence; the stronger demand of
judgmental closure remains a separately named capability.  The same CwF also
carries the fibrewise equality identity type and contextual J from
`ContextualIdentityTypes`.

This is a relative semantic model inside Lean's universe hierarchy.  It does
not choose an object-language universe syntax, cumulativity policy, resizing,
conversion algorithm, or consistency-strength claim.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfTarskiUniverse

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison
open Mettapedia.TypeTheory.ContextualIdentityTypes

universe u v w w'

/-! ## General universe capabilities -/

/-- One internal Tarski universe over a CwF. -/
structure TarskiUniverse (C : Cwf.{u, v, w, w'}) where
  univ : (context : C.Ctx) -> C.Ty context
  el : {context : C.Ctx} -> C.Tm context (univ context) -> C.Ty context

namespace TarskiUniverse

variable {C : Cwf.{u, v, w, w'}}

/-- Transport a term along equality of its internal CwF types. -/
def castTm {context : C.Ctx} {first second : C.Ty context}
    (equalTypes : first = second) (term : C.Tm context first) :
    C.Tm context second := by
  subst second
  exact term

/-- Universe codes and decoding commute with contextual substitution. -/
structure SubstitutionStable (tarski : TarskiUniverse C) where
  univ_sub : forall {source target : C.Ctx}
    (substitution : C.Sub source target),
    C.tySub (tarski.univ target) substitution = tarski.univ source
  el_sub : forall {source target : C.Ctx}
    (code : C.Tm target (tarski.univ target))
    (substitution : C.Sub source target),
    tarski.el
        (castTm (univ_sub substitution) (C.tmSub code substitution)) =
      C.tySub (tarski.el code) substitution

/-- Code-level closure under a selected dependent-product operation.  This
does not include function extensionality or a universe hierarchy. -/
structure PiClosed (tarski : TarskiUniverse C)
    (products : DependentProductBeta C) where
  piCode : forall {context : C.Ctx}
    (domainCode : C.Tm context (tarski.univ context))
    (_codomainCode :
      C.Tm (C.ext context (tarski.el domainCode))
        (tarski.univ (C.ext context (tarski.el domainCode)))),
    C.Tm context (tarski.univ context)
  el_piCode : forall {context : C.Ctx}
    (domainCode : C.Tm context (tarski.univ context))
    (codomainCode :
      C.Tm (C.ext context (tarski.el domainCode))
        (tarski.univ (C.ext context (tarski.el domainCode)))),
    tarski.el (piCode domainCode codomainCode) =
      products.pi (tarski.el domainCode) (tarski.el codomainCode)

/-- Code-level closure under a selected dependent-sum operation. -/
structure SigmaClosed (tarski : TarskiUniverse C)
    (sums : DependentSumBeta C) where
  sigmaCode : forall {context : C.Ctx}
    (domainCode : C.Tm context (tarski.univ context))
    (_codomainCode :
      C.Tm (C.ext context (tarski.el domainCode))
        (tarski.univ (C.ext context (tarski.el domainCode)))),
    C.Tm context (tarski.univ context)
  el_sigmaCode : forall {context : C.Ctx}
    (domainCode : C.Tm context (tarski.univ context))
    (codomainCode :
      C.Tm (C.ext context (tarski.el domainCode))
        (tarski.univ (C.ext context (tarski.el domainCode)))),
    tarski.el (sigmaCode domainCode codomainCode) =
      sums.sigma (tarski.el domainCode) (tarski.el codomainCode)

end TarskiUniverse

/-! ## The set-family model one universe up -/

namespace SetFamilies

universe small

/-- The set-family CwF in `Type (small+1)`. -/
abbrev semanticCwf := familiesCwf.{small + 1}

/-- Lift a small decoded type into the semantic CwF's type universe. -/
abbrev SmallLift (type : Type small) : Type (small + 1) :=
  ULift.{small + 1, small} type

/-- A universe-lifted carrier of codes for small Lean types. -/
abbrev CodeCarrier : Type (small + 1) :=
  ULift.{small + 1, small + 1} (Type small)

/-- Codes are lifted small Lean types.  Decoding performs a second explicit
lift into the CwF's type universe; Lean universes are therefore not being
treated as judgmentally cumulative. -/
def smallTypes : TarskiUniverse semanticCwf where
  univ _context := fun _ => CodeCarrier
  el code := fun point => SmallLift (code point).down

def smallTypes_substitutionStable : smallTypes.SubstitutionStable where
  univ_sub _ := rfl
  el_sub _ _ := rfl

/-- Fibrewise semantic Π-closure.  Unlike `PiClosed`, decoding agrees with the
ambient dependent product by equivalence rather than judgmental equality. -/
structure FibrewisePiClosed where
  piCode : forall {context : Type (small + 1)}
    (domainCode : semanticCwf.Tm context (smallTypes.univ context))
    (_codomainCode :
      semanticCwf.Tm (semanticCwf.ext context (smallTypes.el domainCode))
        (smallTypes.univ
          (semanticCwf.ext context (smallTypes.el domainCode)))),
    semanticCwf.Tm context (smallTypes.univ context)
  el_piCode : forall {context : Type (small + 1)}
    (domainCode : semanticCwf.Tm context (smallTypes.univ context))
    (codomainCode :
      semanticCwf.Tm (semanticCwf.ext context (smallTypes.el domainCode))
        (smallTypes.univ
          (semanticCwf.ext context (smallTypes.el domainCode))))
    (point : context),
    smallTypes.el (piCode domainCode codomainCode) point ≃
      (familiesProducts.pi (smallTypes.el domainCode)
        (smallTypes.el codomainCode)) point

/-- Fibrewise semantic Σ-closure. -/
structure FibrewiseSigmaClosed where
  sigmaCode : forall {context : Type (small + 1)}
    (domainCode : semanticCwf.Tm context (smallTypes.univ context))
    (_codomainCode :
      semanticCwf.Tm (semanticCwf.ext context (smallTypes.el domainCode))
        (smallTypes.univ
          (semanticCwf.ext context (smallTypes.el domainCode)))),
    semanticCwf.Tm context (smallTypes.univ context)
  el_sigmaCode : forall {context : Type (small + 1)}
    (domainCode : semanticCwf.Tm context (smallTypes.univ context))
    (codomainCode :
      semanticCwf.Tm (semanticCwf.ext context (smallTypes.el domainCode))
        (smallTypes.univ
          (semanticCwf.ext context (smallTypes.el domainCode))))
    (point : context),
    smallTypes.el (sigmaCode domainCode codomainCode) point ≃
      (familiesSums.sigma (smallTypes.el domainCode)
        (smallTypes.el codomainCode)) point

/-- Canonical equivalence between a lifted small dependent function and the
ambient dependent function between lifted fibres. -/
def piLiftEquiv (domain : Type small)
    (codomain : SmallLift domain -> Type small) :
    SmallLift ((argument : domain) -> codomain ⟨argument⟩) ≃
      ((argument : SmallLift domain) -> SmallLift (codomain argument)) where
  toFun function argument := ⟨function.down argument.down⟩
  invFun function := ⟨fun argument => (function ⟨argument⟩).down⟩
  left_inv function := by
    rcases function with ⟨function⟩
    rfl
  right_inv function := by
    funext argument
    rcases argument with ⟨argument⟩
    exact ULift.up_down (function ⟨argument⟩)

/-- Canonical equivalence between a lifted small dependent pair and the
ambient sigma of lifted fibres. -/
def sigmaLiftEquiv (domain : Type small)
    (codomain : SmallLift domain -> Type small) :
    SmallLift (Sigma fun argument : domain => codomain ⟨argument⟩) ≃
      (Sigma fun argument : SmallLift domain => SmallLift (codomain argument)) where
  toFun pair := ⟨⟨pair.down.1⟩, ⟨pair.down.2⟩⟩
  invFun pair := by
    rcases pair with ⟨⟨argument⟩, ⟨value⟩⟩
    exact ⟨⟨argument, value⟩⟩
  left_inv pair := by
    rcases pair with ⟨⟨argument, value⟩⟩
    rfl
  right_inv pair := by
    rcases pair with ⟨⟨argument⟩, ⟨value⟩⟩
    rfl

/-- Dependent products of lifted small types are represented by small codes,
with a canonical fibrewise equivalence to the ambient Π. -/
def smallTypes_piClosed : FibrewisePiClosed where
  piCode domainCode codomainCode point :=
    ⟨(argument : (domainCode point).down) ->
      (codomainCode ⟨point, ⟨argument⟩⟩).down⟩
  el_piCode domainCode codomainCode point :=
    piLiftEquiv (domainCode point).down
      (fun argument => (codomainCode ⟨point, argument⟩).down)

/-- Dependent sums of lifted small types are represented likewise. -/
def smallTypes_sigmaClosed : FibrewiseSigmaClosed where
  sigmaCode domainCode codomainCode point :=
    ⟨Sigma fun argument : (domainCode point).down =>
      (codomainCode ⟨point, ⟨argument⟩⟩).down⟩
  el_sigmaCode domainCode codomainCode point :=
    sigmaLiftEquiv (domainCode point).down
      (fun argument => (codomainCode ⟨point, argument⟩).down)

/-- Every externally supplied small family has an internal code. -/
def codeFamily {context : Type (small + 1)}
    (family : context -> Type small) :
    semanticCwf.Tm context (smallTypes.univ context) :=
  fun point => ⟨family point⟩

/-- Decoding an encoded small family is fibrewise equivalent to it. -/
def elCodeFamilyEquiv {context : Type (small + 1)}
    (family : context -> Type small) :
    forall point, smallTypes.el (codeFamily family) point ≃ family point :=
  fun _ => Equiv.ulift

/-- A genuine varying small family is represented without collapsing it to a
constant simple type. -/
abbrev BoolContext : Type (small + 1) := ULift.{small + 1, 0} Bool

def varyingCode :
    semanticCwf.Tm BoolContext (smallTypes.univ BoolContext) :=
  fun point => ⟨if point.down then Bool else PUnit⟩

def varyingCode_decodes_at_false :
    smallTypes.el varyingCode (ULift.up false) ≃ PUnit :=
  Equiv.ulift

def varyingCode_decodes_at_true :
    smallTypes.el varyingCode (ULift.up true) ≃ Bool :=
  Equiv.ulift

/-! ### The carrier is simple; decoding is genuinely dependent -/

/-- A context at the semantic universe used by the level-zero discriminator. -/
abbrev UnitContext : Type 1 := ULift.{1, 0} PUnit

def unitTypeCode :
    semanticCwf.{0}.Tm UnitContext
      (smallTypes.{0}.univ UnitContext) :=
  fun _ => ⟨PUnit⟩

def boolTypeCode :
    semanticCwf.{0}.Tm UnitContext
      (smallTypes.{0}.univ UnitContext) :=
  fun _ => ⟨Bool⟩

/-- Universe formation itself is a context-constant family, hence lies in the
simple constant-family image. -/
theorem universe_carrier_is_constant :
    smallTypes.{0}.univ UnitContext =
      constantFamily (Γ := UnitContext) CodeCarrier.{0} :=
  rfl

/-- Decoding is nevertheless genuinely code-dependent: lifted unit and
lifted Boolean fibres have different finite cardinalities. -/
theorem decoded_unit_not_equivalent_bool :
    Not (Nonempty
      (smallTypes.{0}.el unitTypeCode (⟨PUnit.unit⟩ : UnitContext) ≃
        smallTypes.{0}.el boolTypeCode (⟨PUnit.unit⟩ : UnitContext))) := by
  rintro ⟨equivalence⟩
  change ULift.{1, 0} PUnit ≃ ULift.{1, 0} Bool at equivalence
  obtain ⟨unitForFalse, mapsToFalse⟩ :=
    equivalence.surjective (⟨false⟩ : ULift.{1, 0} Bool)
  obtain ⟨unitForTrue, mapsToTrue⟩ :=
    equivalence.surjective (⟨true⟩ : ULift.{1, 0} Bool)
  have sameUnit : unitForFalse = unitForTrue := Subsingleton.elim _ _
  have liftedFalseEqualsTrue :
      (⟨false⟩ : ULift.{1, 0} Bool) = ⟨true⟩ :=
    mapsToFalse.symm.trans
      ((congrArg equivalence sameUnit).trans mapsToTrue)
  exact Bool.false_ne_true (congrArg ULift.down liftedFalseEqualsTrue)

/-- The exact simple/dependent universe boundary in the set-family model. -/
theorem constant_code_carrier_with_genuine_dependent_decoding :
    smallTypes.{0}.univ UnitContext =
        constantFamily (Γ := UnitContext) CodeCarrier.{0} /\
      Not (Nonempty
        (smallTypes.{0}.el unitTypeCode (⟨PUnit.unit⟩ : UnitContext) ≃
          smallTypes.{0}.el boolTypeCode (⟨PUnit.unit⟩ : UnitContext))) :=
  ⟨universe_carrier_is_constant, decoded_unit_not_equivalent_bool⟩

/-- The standard dependent capability family is jointly inhabited in one
semantic CwF.  This is a compatibility witness, not a bundled syntax. -/
theorem dependent_capabilities_have_common_set_model :
    Nonempty (DependentProductBeta semanticCwf) /\
    Nonempty (DependentSumBeta semanticCwf) /\
    Nonempty
      (IdentityEliminationBeta semanticCwf
        ContextualIdentityTypes.Families.identityFormation
        ContextualIdentityTypes.Families.identityReflexivity) /\
    Nonempty (TarskiUniverse semanticCwf) /\
    Nonempty smallTypes.SubstitutionStable /\
    Nonempty FibrewisePiClosed.{small} /\
    Nonempty FibrewiseSigmaClosed.{small} :=
  ⟨⟨familiesProducts⟩, ⟨familiesSums⟩,
    ⟨ContextualIdentityTypes.Families.identityElimination⟩,
    ⟨smallTypes⟩, ⟨smallTypes_substitutionStable⟩,
    ⟨smallTypes_piClosed.{small}⟩,
    ⟨smallTypes_sigmaClosed.{small}⟩⟩

end SetFamilies

#print axioms SetFamilies.smallTypes_substitutionStable
#print axioms SetFamilies.smallTypes_piClosed
#print axioms SetFamilies.smallTypes_sigmaClosed
#print axioms SetFamilies.elCodeFamilyEquiv
#print axioms SetFamilies.constant_code_carrier_with_genuine_dependent_decoding
#print axioms SetFamilies.dependent_capabilities_have_common_set_model

end Mettapedia.TypeTheory.CwfTarskiUniverse
