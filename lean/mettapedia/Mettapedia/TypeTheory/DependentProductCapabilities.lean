import Mettapedia.TypeTheory.ModalCwF
import Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-!
# Capabilities of dependent products

Dependent-product computation and function extensionality are separate
mathematical structures.  `PiBetaStructure` contains formation already stored
by a `ModalCwF`, introduction, elimination, beta, and substitution stability.
`PiApplicationExtensionality` adds generalized function extensionality.

The older all-in-one `PiStructure` decomposes into these two records and can be
reconstructed from them.  The constructive function-space controls imported
below show why the split has content: beta exists both for a constant result
family and for a genuinely dependent family even when application identifies
two distinct route-bearing functions.

This module does not decide whether eta or function extensionality is
judgmental, propositional, observed in a model, or absent.  Concrete type
theories must select and justify that capability independently of dependency.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentProductCapabilities

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-- Dependent products with beta computation and substitution stability, but
without eta or function extensionality. -/
structure PiBetaStructure (modes : ModeTheory) (cwf : ModalCwF modes) where
  lam : {mode : modes.Mode} → {context : cwf.Con mode} →
    {domain : cwf.Ty context} → {codomain : cwf.Ty (cwf.ext context domain)} →
    cwf.Tm (cwf.ext context domain) codomain →
      cwf.Tm context (cwf.pi domain codomain)
  app : {mode : modes.Mode} → {context : cwf.Con mode} →
    {domain : cwf.Ty context} → {codomain : cwf.Ty (cwf.ext context domain)} →
    cwf.Tm context (cwf.pi domain codomain) →
    (argument : cwf.Tm context domain) →
      cwf.Tm context (cwf.tySub codomain (cwf.selfExtend argument))
  beta : ∀ {mode : modes.Mode} {context : cwf.Con mode}
    {domain : cwf.Ty context} {codomain : cwf.Ty (cwf.ext context domain)}
    (body : cwf.Tm (cwf.ext context domain) codomain)
    (argument : cwf.Tm context domain),
    app (lam body) argument = cwf.tmSub body (cwf.selfExtend argument)
  pi_sub : ∀ {mode : modes.Mode} {first last : cwf.Con mode}
    (domain : cwf.Ty last) (codomain : cwf.Ty (cwf.ext last domain))
    (substitution : cwf.Sub first last),
    cwf.tySub (cwf.pi domain codomain) substitution =
      cwf.pi (cwf.tySub domain substitution)
        (cwf.tySub codomain (cwf.liftSub substitution))

/-- Generalized function extensionality for a beta-dependent-product
structure.  It remains separate because intensional theories may instead
offer propositional extensionality, a hosted extensional model, or neither. -/
structure PiApplicationExtensionality (modes : ModeTheory)
    (cwf : ModalCwF modes) (products : PiBetaStructure modes cwf) where
  extensional : ∀ {mode : modes.Mode} {context : cwf.Con mode}
    {domain : cwf.Ty context} {codomain : cwf.Ty (cwf.ext context domain)}
    (left right : cwf.Tm context (cwf.pi domain codomain)),
    (∀ {otherContext : cwf.Con mode}
      (substitution : cwf.Sub otherContext context)
      (argument : cwf.Tm otherContext (cwf.tySub domain substitution)),
      HEq
        (products.app
          (cwf.castTm (products.pi_sub domain codomain substitution)
            (cwf.tmSub left substitution)) argument)
        (products.app
          (cwf.castTm (products.pi_sub domain codomain substitution)
            (cwf.tmSub right substitution)) argument)) →
    left = right

namespace PiStructure

/-- Forget only generalized function extensionality from the historical
all-in-one dependent-product record. -/
def toBeta {modes : ModeTheory} {cwf : ModalCwF modes}
    (products : Mettapedia.TypeTheory.PiStructure modes cwf) :
    PiBetaStructure modes cwf where
  lam := products.lam
  app := products.app
  beta := products.beta
  pi_sub := products.pi_sub

/-- Extract generalized function extensionality as the independent second
capability. -/
def toApplicationExtensionality
    {modes : ModeTheory} {cwf : ModalCwF modes}
    (products : Mettapedia.TypeTheory.PiStructure modes cwf) :
    PiApplicationExtensionality modes cwf (toBeta products) where
  extensional := products.extensional

end PiStructure

namespace PiBetaStructure

/-- Recombine beta-dependent products and explicitly supplied generalized
function extensionality. -/
def withApplicationExtensionality
    {modes : ModeTheory} {cwf : ModalCwF modes}
    (products : PiBetaStructure modes cwf)
    (extensionality : PiApplicationExtensionality modes cwf products) :
    Mettapedia.TypeTheory.PiStructure modes cwf where
  lam := products.lam
  app := products.app
  beta := products.beta
  pi_sub := products.pi_sub
  extensional := extensionality.extensional

end PiBetaStructure

/-! ## Constructive independence controls -/

/-- Beta at a simple function type does not force application
extensionality. -/
theorem simple_beta_without_application_extensionality :
    Nonempty
      (DependentFunctionSpace.{0, 0, 0} PUnit (constantFamily Bool)) ∧
      ¬ simpleRouteSensitive.ApplicationExtensional :=
  ⟨⟨simpleRouteSensitive⟩,
    simpleRouteSensitive_not_applicationExtensional⟩

/-- The same independence persists for a genuinely varying result family. -/
theorem dependent_beta_without_application_extensionality :
    (¬ ∃ Constant : Type,
      ∀ argument, Nonempty ((varyingBoolFamily argument) ≃ Constant)) ∧
      Nonempty
        (DependentFunctionSpace.{0, 0, 0} Bool varyingBoolFamily) ∧
      ¬ dependentRouteSensitive.ApplicationExtensional :=
  ⟨varyingBoolFamily_not_constant, ⟨dependentRouteSensitive⟩,
    dependentRouteSensitive_not_applicationExtensional⟩

/-- Extensional dependent products are also constructively inhabited over
the same genuinely varying family. -/
theorem dependent_extensional_beta_exists :
    (¬ ∃ Constant : Type,
      ∀ argument, Nonempty ((varyingBoolFamily argument) ≃ Constant)) ∧
      dependentExtensional.ApplicationExtensional :=
  ⟨varyingBoolFamily_not_constant,
    dependentExtensional_applicationExtensional⟩

#print axioms PiStructure.toBeta
#print axioms PiStructure.toApplicationExtensionality
#print axioms PiBetaStructure.withApplicationExtensionality
#print axioms simple_beta_without_application_extensionality
#print axioms dependent_beta_without_application_extensionality
#print axioms dependent_extensional_beta_exists

end Mettapedia.TypeTheory.DependentProductCapabilities
