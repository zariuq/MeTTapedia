import Mettapedia.TypeTheory.ContextualTarskiUniverseFamilies
import Mettapedia.TypeTheory.CwfTarskiUniverse
import Mathlib.Logic.Small.Basic

/-!
# Level-indexed Tarski universes over universe-polymorphic CwFs

The mode-indexed contextual interface and the universe-polymorphic `Cwf`
interface serve different purposes.  The former exposes modal structure; the
latter can state semantic universe hierarchies without fixing all contexts and
types in `Type 1`.  This module gives the latter its level-indexed Tarski
universe structure.

The concrete model has two predicative levels.  The lower level codes types in
`Type u`, the upper level codes types in `Type (u+1)`, and both live in the
set-family CwF in `Type (u+2)`.  The lower level lifts strictly into the upper
one, and both levels are closed under dependent products and sums.  Neither
level codes its own code carrier.  Reversing the cumulative edge is
impossible.

This is a semantic compatibility model.  It does not select an object syntax,
a conversion algorithm, resizing, identity principles, or a product
language.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison
open Mettapedia.TypeTheory.CwfTarskiUniverse
open Mettapedia.TypeTheory.TarskiUniverseCapabilities

universe uLevel u v w w' uSemantic

/-- A level-indexed family of internal Tarski universes over a
universe-polymorphic CwF.  Ordering, cumulativity, closure, and substitution
stability are separate properties. -/
structure TarskiUniverseFamily (Level : Type uLevel)
    (C : Cwf.{u, v, w, w'}) where
  univ : (context : C.Ctx) → Level → C.Ty context
  el : {context : C.Ctx} → {level : Level} →
    C.Tm context (univ context level) → C.Ty context

namespace TarskiUniverseFamily

variable {Level : Type uLevel} {C : Cwf.{u, v, w, w'}}

/-- Transport a term along equality of its internal CwF types. -/
def castTm {context : C.Ctx} {first second : C.Ty context}
    (equalTypes : first = second) (term : C.Tm context first) :
    C.Tm context second := by
  subst second
  exact term

/-- Universe formation and decoding commute with contextual substitution at
every level. -/
structure SubstitutionStable
    (family : TarskiUniverseFamily Level C) where
  univ_sub : ∀ {source target : C.Ctx} (level : Level)
    (substitution : C.Sub source target),
    C.tySub (family.univ target level) substitution =
      family.univ source level
  el_sub : ∀ {source target : C.Ctx} {level : Level}
    (code : C.Tm target (family.univ target level))
    (substitution : C.Sub source target),
    family.el
        (castTm (univ_sub level substitution)
          (C.tmSub code substitution)) =
      C.tySub (family.el code) substitution

/-- Strict cumulativity preserves the decoded internal type exactly. -/
structure StrictlyCumulative
    (family : TarskiUniverseFamily Level C)
    (Below : Level → Level → Prop) where
  liftCode : ∀ {lower upper}, Below lower upper →
    {context : C.Ctx} →
    C.Tm context (family.univ context lower) →
      C.Tm context (family.univ context upper)
  el_liftCode : ∀ {lower upper} (below : Below lower upper)
    {context : C.Ctx}
    (code : C.Tm context (family.univ context lower)),
    family.el (liftCode below code) = family.el code

/-- Code-level closure under a selected dependent-product operation.  This is
independent of function extensionality. -/
structure PiClosed (family : TarskiUniverseFamily Level C)
    (products : DependentProductBeta C) where
  piCode : ∀ {context : C.Ctx} {level : Level}
    (domainCode : C.Tm context (family.univ context level))
    (_codomainCode :
      C.Tm (C.ext context (family.el domainCode))
        (family.univ (C.ext context (family.el domainCode)) level)),
    C.Tm context (family.univ context level)
  el_piCode : ∀ {context : C.Ctx} {level : Level}
    (domainCode : C.Tm context (family.univ context level))
    (codomainCode :
      C.Tm (C.ext context (family.el domainCode))
        (family.univ (C.ext context (family.el domainCode)) level)),
    family.el (piCode domainCode codomainCode) =
      products.pi (family.el domainCode) (family.el codomainCode)

/-- Code-level closure under a selected dependent-sum operation. -/
structure SigmaClosed (family : TarskiUniverseFamily Level C)
    (sums : DependentSumBeta C) where
  sigmaCode : ∀ {context : C.Ctx} {level : Level}
    (domainCode : C.Tm context (family.univ context level))
    (_codomainCode :
      C.Tm (C.ext context (family.el domainCode))
        (family.univ (C.ext context (family.el domainCode)) level)),
    C.Tm context (family.univ context level)
  el_sigmaCode : ∀ {context : C.Ctx} {level : Level}
    (domainCode : C.Tm context (family.univ context level))
    (codomainCode :
      C.Tm (C.ext context (family.el domainCode))
        (family.univ (C.ext context (family.el domainCode)) level)),
    family.el (sigmaCode domainCode codomainCode) =
      sums.sigma (family.el domainCode) (family.el codomainCode)

/-- Select one level as an ordinary one-universe structure. -/
def atLevel (family : TarskiUniverseFamily Level C) (level : Level) :
    TarskiUniverse C where
  univ := fun context => family.univ context level
  el := fun code => family.el code

/-- Externally interpret the codes at one context. -/
def externalizeAt (family : TarskiUniverseFamily Level C)
    (context : C.Ctx) (interpret : C.Ty context → Type uSemantic) :
    TarskiCodeFamily.{uLevel, w', uSemantic} where
  Level := Level
  Code := fun level => C.Tm context (family.univ context level)
  El := fun _level code => interpret (family.el code)

/-- Strict internal cumulativity becomes semantic cumulativity under any
independently supplied interpretation. -/
def StrictlyCumulative.externalCumulative
    {family : TarskiUniverseFamily Level C}
    {Below : Level → Level → Prop}
    (cumulative : family.StrictlyCumulative Below)
    (context : C.Ctx) (interpret : C.Ty context → Type uSemantic) :
    (family.externalizeAt context interpret).Cumulative Below where
  lift := fun below code => cumulative.liftCode below code
  decodeLift := by
    intro lower upper below code
    change interpret (family.el (cumulative.liftCode below code)) ≃
      interpret (family.el code)
    rw [cumulative.el_liftCode below code]

end TarskiUniverseFamily

/-! ## A two-level predicative set-family model -/

namespace TwoLevelSetFamilies

universe small

/-- Both universe levels live two Lean universes above the lower decoded
types. -/
abbrev semanticCwf := familiesCwf.{small + 2}

/-- Lower codes are lifted inhabitants of `Type small`; upper codes are
lifted inhabitants of `Type (small+1)`.  The lifts make every universe change
visible in the model. -/
def Code : Bool → Type (small + 2)
  | false => ULift.{small + 2, small + 1} (Type small)
  | true => ULift.{small + 2, small + 2} (Type (small + 1))

/-- The lower decoding has two explicit lifts and the upper decoding one.
This makes lower-to-upper lifting preserve the decoded type definitionally. -/
def decode : (level : Bool) → Code level → Type (small + 2)
  | false, code =>
      ULift.{small + 2, small + 1}
        (ULift.{small + 1, small} code.down)
  | true, code => ULift.{small + 2, small + 1} code.down

def decodeFamily {context : Type (small + 2)} {level : Bool}
    (code : context → Code.{small} level) : context → Type (small + 2) :=
  fun point => decode.{small} level (code point)

/-- The two internal Tarski universes in the large set-family CwF. -/
def hierarchy : TarskiUniverseFamily Bool semanticCwf where
  univ := fun _context level _point => Code level
  el := decodeFamily

def substitutionStable : hierarchy.SubstitutionStable where
  univ_sub _ _ := rfl
  el_sub _ _ := rfl

/-- The sole strict hierarchy edge. -/
def Below (lower upper : Bool) : Prop := lower = false ∧ upper = true

/-- Lower codes are also upper codes, with exactly the same decoding. -/
def cumulative : hierarchy.StrictlyCumulative Below where
  liftCode := by
    intro lower upper below context code
    rcases below with ⟨rfl, rfl⟩
    exact fun point => ⟨ULift.{small + 1, small} (code point).down⟩
  el_liftCode := by
    intro lower upper below context code
    rcases below with ⟨rfl, rfl⟩
    rfl

/-! ### Fibrewise product and sum closure -/

/-- Canonical equivalence for a doubly lifted lower-level dependent
function. -/
def lowerPiEquiv (domain : Type small)
    (codomain :
      ULift.{small + 2, small + 1} (ULift.{small + 1, small} domain) →
        Type small) :
    ULift.{small + 2, small + 1}
        (ULift.{small + 1, small}
          ((argument : domain) → codomain ⟨⟨argument⟩⟩)) ≃
      ((argument :
          ULift.{small + 2, small + 1}
            (ULift.{small + 1, small} domain)) →
        ULift.{small + 2, small + 1}
          (ULift.{small + 1, small} (codomain argument))) where
  toFun function argument :=
    ⟨⟨function.down.down argument.down.down⟩⟩
  invFun function :=
    ⟨⟨fun argument => (function ⟨⟨argument⟩⟩).down.down⟩⟩
  left_inv function := by
    rcases function with ⟨⟨function⟩⟩
    rfl
  right_inv function := by
    funext argument
    rcases argument with ⟨⟨argument⟩⟩
    calc
      ⟨⟨(function ⟨⟨argument⟩⟩).down.down⟩⟩ =
          ⟨(function ⟨⟨argument⟩⟩).down⟩ := by
            rw [ULift.up_down]
      _ = function ⟨⟨argument⟩⟩ := ULift.up_down _

/-- Canonical equivalence for a singly lifted upper-level dependent
function. -/
def upperPiEquiv (domain : Type (small + 1))
    (codomain : ULift.{small + 2, small + 1} domain → Type (small + 1)) :
    ULift.{small + 2, small + 1}
        ((argument : domain) → codomain ⟨argument⟩) ≃
      ((argument : ULift.{small + 2, small + 1} domain) →
        ULift.{small + 2, small + 1} (codomain argument)) where
  toFun function argument := ⟨function.down argument.down⟩
  invFun function := ⟨fun argument => (function ⟨argument⟩).down⟩
  left_inv function := by
    rcases function with ⟨function⟩
    rfl
  right_inv function := by
    funext argument
    rcases argument with ⟨argument⟩
    exact ULift.up_down (function ⟨argument⟩)

/-- The code for a dependent product at either level. -/
def piCode (level : Bool) (domain : Code.{small} level)
    (codomain : decode.{small} level domain → Code.{small} level) :
    Code.{small} level := by
  cases level with
  | false =>
      exact ⟨(argument : domain.down) →
        (codomain ⟨⟨argument⟩⟩).down⟩
  | true =>
      exact ⟨(argument : domain.down) →
        (codomain ⟨argument⟩).down⟩

/-- Decoding the product code agrees fibrewise with the ambient dependent
product. -/
def decodePiEquiv (level : Bool) (domain : Code.{small} level)
    (codomain : decode.{small} level domain → Code.{small} level) :
    decode.{small} level (piCode.{small} level domain codomain) ≃
      ((argument : decode.{small} level domain) →
        decode.{small} level (codomain argument)) := by
  cases level with
  | false =>
      exact lowerPiEquiv domain.down
        (fun argument => (codomain argument).down)
  | true =>
      exact upperPiEquiv domain.down
        (fun argument => (codomain argument).down)

/-- Level-indexed semantic Π closure for the set-family hierarchy. -/
structure FibrewisePiClosed where
  piCode : ∀ {context : Type (small + 2)} {level : Bool}
    (domainCode : context → Code.{small} level)
    (_codomainCode :
      (Σ point : context, decode.{small} level (domainCode point)) →
        Code.{small} level),
    context → Code.{small} level
  el_piCode : ∀ {context : Type (small + 2)} {level : Bool}
    (domainCode : context → Code.{small} level)
    (codomainCode :
      (Σ point : context, decode.{small} level (domainCode point)) →
        Code.{small} level)
    (point : context),
    decode.{small} level (piCode domainCode codomainCode point) ≃
      ((argument : decode.{small} level (domainCode point)) →
        decode.{small} level (codomainCode ⟨point, argument⟩))

def piClosed : FibrewisePiClosed where
  piCode domainCode codomainCode point :=
    piCode.{small} _ (domainCode point) (fun argument =>
      codomainCode ⟨point, argument⟩)
  el_piCode domainCode codomainCode point :=
    decodePiEquiv.{small} _ (domainCode point) (fun argument =>
      codomainCode ⟨point, argument⟩)

/-- Canonical equivalence for a doubly lifted lower-level dependent sum. -/
def lowerSigmaEquiv (domain : Type small)
    (codomain :
      ULift.{small + 2, small + 1} (ULift.{small + 1, small} domain) →
        Type small) :
    ULift.{small + 2, small + 1}
        (ULift.{small + 1, small}
          (Σ argument : domain, codomain ⟨⟨argument⟩⟩)) ≃
      (Σ argument :
          ULift.{small + 2, small + 1}
            (ULift.{small + 1, small} domain),
        ULift.{small + 2, small + 1}
          (ULift.{small + 1, small} (codomain argument))) where
  toFun pair := ⟨⟨⟨pair.down.down.1⟩⟩, ⟨⟨pair.down.down.2⟩⟩⟩
  invFun pair := by
    rcases pair with ⟨⟨⟨argument⟩⟩, ⟨⟨value⟩⟩⟩
    exact ⟨⟨⟨argument, value⟩⟩⟩
  left_inv pair := by
    rcases pair with ⟨⟨⟨argument, value⟩⟩⟩
    rfl
  right_inv pair := by
    rcases pair with ⟨⟨⟨argument⟩⟩, ⟨⟨value⟩⟩⟩
    rfl

/-- Canonical equivalence for a singly lifted upper-level dependent sum. -/
def upperSigmaEquiv (domain : Type (small + 1))
    (codomain : ULift.{small + 2, small + 1} domain → Type (small + 1)) :
    ULift.{small + 2, small + 1}
        (Σ argument : domain, codomain ⟨argument⟩) ≃
      (Σ argument : ULift.{small + 2, small + 1} domain,
        ULift.{small + 2, small + 1} (codomain argument)) where
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

/-- The code for a dependent sum at either level. -/
def sigmaCode (level : Bool) (domain : Code.{small} level)
    (codomain : decode.{small} level domain → Code.{small} level) :
    Code.{small} level := by
  cases level with
  | false =>
      exact ⟨Σ argument : domain.down,
        (codomain ⟨⟨argument⟩⟩).down⟩
  | true =>
      exact ⟨Σ argument : domain.down,
        (codomain ⟨argument⟩).down⟩

def decodeSigmaEquiv (level : Bool) (domain : Code.{small} level)
    (codomain : decode.{small} level domain → Code.{small} level) :
    decode.{small} level (sigmaCode.{small} level domain codomain) ≃
      (Σ argument : decode.{small} level domain,
        decode.{small} level (codomain argument)) := by
  cases level with
  | false =>
      exact lowerSigmaEquiv domain.down
        (fun argument => (codomain argument).down)
  | true =>
      exact upperSigmaEquiv domain.down
        (fun argument => (codomain argument).down)

/-- Level-indexed semantic Σ closure for the set-family hierarchy. -/
structure FibrewiseSigmaClosed where
  sigmaCode : ∀ {context : Type (small + 2)} {level : Bool}
    (domainCode : context → Code.{small} level)
    (_codomainCode :
      (Σ point : context, decode.{small} level (domainCode point)) →
        Code.{small} level),
    context → Code.{small} level
  el_sigmaCode : ∀ {context : Type (small + 2)} {level : Bool}
    (domainCode : context → Code.{small} level)
    (codomainCode :
      (Σ point : context, decode.{small} level (domainCode point)) →
        Code.{small} level)
    (point : context),
    decode.{small} level (sigmaCode domainCode codomainCode point) ≃
      (Σ argument : decode.{small} level (domainCode point),
        decode.{small} level (codomainCode ⟨point, argument⟩))

def sigmaClosed : FibrewiseSigmaClosed where
  sigmaCode domainCode codomainCode point :=
    sigmaCode.{small} _ (domainCode point) (fun argument =>
      codomainCode ⟨point, argument⟩)
  el_sigmaCode domainCode codomainCode point :=
    decodeSigmaEquiv.{small} _ (domainCode point) (fun argument =>
      codomainCode ⟨point, argument⟩)

/-- The corresponding external code family, used to state semantic rank
properties without referring to a selected context. -/
def externalFamily : TarskiCodeFamily.{0, small + 2, small + 2} where
  Level := Bool
  Code := Code.{small}
  El := decode.{small}

def lowerDecodeEquiv (code : Code.{small} false) :
    decode.{small} false code ≃ code.down :=
  Equiv.ulift.trans Equiv.ulift

def upperDecodeEquiv (code : Code.{small} true) :
    decode.{small} true code ≃ code.down :=
  Equiv.ulift

def lowerCodeEquiv : Code.{small} false ≃ Type small :=
  Equiv.ulift

def upperCodeEquiv : Code.{small} true ≃ Type (small + 1) :=
  Equiv.ulift

/-- Neither level codes its own code carrier.  This is the semantic
predicativity property, not merely the absence of a syntactic `U : U` rule. -/
theorem predicativeRanks : externalFamily.{small}.PredicativeRanks := by
  intro level selfCode
  cases level with
  | false =>
      rcases selfCode with ⟨code, ⟨equivalence⟩⟩
      let decodedToType : code.down ≃ Type small :=
        ((lowerDecodeEquiv.{small} code).symm.trans equivalence).trans
          lowerCodeEquiv.{small}
      have smallUniverse : Small.{small} (Type small) :=
        Small.mk' decodedToType.symm
      exact not_small_type.{small, 0} smallUniverse
  | true =>
      rcases selfCode with ⟨code, ⟨equivalence⟩⟩
      let decodedToType : code.down ≃ Type (small + 1) :=
        ((upperDecodeEquiv.{small} code).symm.trans equivalence).trans
          upperCodeEquiv.{small}
      have smallUniverse : Small.{small + 1} (Type (small + 1)) :=
        Small.mk' decodedToType.symm
      exact not_small_type.{small + 1, 0} smallUniverse

/-- The external family is strictly cumulative along the lower-to-upper
edge. -/
def externalCumulative : externalFamily.{small}.Cumulative Below where
  lift := by
    intro lower upper below code
    rcases below with ⟨rfl, rfl⟩
    exact ⟨ULift.{small + 1, small} code.down⟩
  decodeLift := by
    intro lower upper below code
    rcases below with ⟨rfl, rfl⟩
    exact Equiv.refl _

/-- A lower Boolean code lifts without changing either code or denotation. -/
theorem bool_lift_is_exact :
    externalFamily.{small}.El true
        (externalCumulative.{small}.lift
          (show Below false true by exact ⟨rfl, rfl⟩)
          (⟨ULift.{small, 0} Bool⟩ :
            externalFamily.{small}.Code false)) =
      externalFamily.{small}.El false
        (⟨ULift.{small, 0} Bool⟩ :
          externalFamily.{small}.Code false) :=
  rfl

/-- Reversing the hierarchy would force the lower universe to contain a code
for its own code carrier. -/
def ReverseBelow (lower upper : Bool) : Prop :=
  lower = true ∧ upper = false

theorem no_reverse_cumulative :
    ¬ Nonempty (externalFamily.{small}.Cumulative ReverseBelow) := by
  rintro ⟨reverse⟩
  have below : ReverseBelow true false := ⟨rfl, rfl⟩
  let lowered : externalFamily.{small}.Code false :=
    reverse.lift below
      (⟨Type small⟩ : externalFamily.{small}.Code true)
  have decoded := reverse.decodeLift below
    (⟨Type small⟩ : externalFamily.{small}.Code true)
  let loweredToType : lowered.down ≃ Type small :=
    ((lowerDecodeEquiv.{small} lowered).symm.trans decoded).trans
      (upperDecodeEquiv.{small}
        (⟨Type small⟩ : externalFamily.{small}.Code true))
  have smallUniverse : Small.{small} (Type small) :=
    Small.mk' loweredToType.symm
  exact not_small_type.{small, 0} smallUniverse

/-- Cumulativity, Π/Σ closure, and predicative rank separation coexist in one
semantic hierarchy. -/
theorem hierarchy_capabilities_coexist :
    Nonempty hierarchy.SubstitutionStable ∧
      Nonempty (hierarchy.StrictlyCumulative Below) ∧
      Nonempty FibrewisePiClosed ∧
      Nonempty FibrewiseSigmaClosed ∧
      externalFamily.{small}.PredicativeRanks ∧
      ¬ Nonempty (externalFamily.{small}.Cumulative ReverseBelow) :=
  ⟨⟨substitutionStable⟩, ⟨cumulative⟩, ⟨piClosed⟩, ⟨sigmaClosed⟩,
    predicativeRanks, no_reverse_cumulative⟩

end TwoLevelSetFamilies

#print axioms TarskiUniverseFamily.StrictlyCumulative.externalCumulative
#print axioms TwoLevelSetFamilies.substitutionStable
#print axioms TwoLevelSetFamilies.cumulative
#print axioms TwoLevelSetFamilies.piClosed
#print axioms TwoLevelSetFamilies.sigmaClosed
#print axioms TwoLevelSetFamilies.predicativeRanks
#print axioms TwoLevelSetFamilies.no_reverse_cumulative
#print axioms TwoLevelSetFamilies.hierarchy_capabilities_coexist

end Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy
