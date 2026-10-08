import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementEvidenceExtraction
import Mettapedia.TypeTheory.NativeLocalSumElimination
import Mettapedia.TypeTheory.NativeLocalPiEta
import Mathlib.CategoryTheory.Functor.Const

/-!
# Complete generated predicate and refinement certificates

The independent mixed dependent grammar includes ordinary propositions,
refinement introduction and forgetting, predicate assumptions, and dependent
suffix substitution. Its complete rule interpretation earns the successful
raw evaluator section. A supplied natural program interface pulls that
section to a program presheaf, retaining the entire generated derivation
and its checked native value as a coherent displayed certificate family.

The local presheaf operations supply their own substitution and computational
laws. Only independent primitive meanings and their local declaration-header
realization are supplied. Variable scopes, program-client contexts and runtime
states remain distinct; an explicit interface connects the first two.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPresheafCertificates

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafCwf ContextualLocalUniverses ContextualModelTelescopes
open ContextualTypeOperations ContextualPiEta NativeLocalTypeFormers
open Refinement (Scope)

universe u

variable {C : Type u} [Category.{u} C]
variable {S : Refinement.Symbols.{u}} {D : Refinement.Signature S}
variable {n : Nat} {context : Refinement.ContextExpr S n}
variable {term : Refinement.TermExpr S n} {type : Refinement.TypeExpr S n}
variable {P : Face.{u, u, u} C}

/-- Independent local declaration meanings and their header realization
supply the inputs to the earned full-rule interpretation. The interface
is a genuine natural map; whole-rule soundness is not supplied as a field. -/
structure Interpretation (D : Refinement.Signature S)
    (context : Refinement.ContextExpr S n) (term : Refinement.TermExpr S n)
    (type : Refinement.TypeExpr S n) (P : Face.{u, u, u} C) where
  model : Refinement.ModelData S C
  realization : Refinement.SignatureRealization model D
  semanticContext : Scope C n
  semanticType : NativeType semanticContext.1
  contextRead : model.evaluateContext context = some semanticContext
  typeRead : model.evaluateType semanticContext type = some semanticType
  interface : P ⟶ semanticContext.1

namespace Interpretation

variable (interpretation : Interpretation D context term type P)

local instance semanticCategory : Category.{u} interpretation.semanticContext.1.Elements :=
  categoryOfElements (interpretation.semanticContext.1 : Face.{u, u, u} C)

abbrev Tree := Refinement.Derivation D (.term context term type)

def decodedFamily : DisplayedFamily.{u, u, u, u}
    (interpretation.semanticContext.1 : Face.{u, u, u} C) :=
  interpretation.semanticType.decoded

def valueFamily : DisplayedFamily P :=
  reindexDisplayed interpretation.interface interpretation.decodedFamily

/-- The semantic value is obtained from the actual term evaluator, with
successful evaluation earned from all generated local rules. -/
noncomputable def nativeSection (tree : Tree (D := D) (context := context)
    (term := term) (type := type)) : interpretation.decodedFamily.sections :=
  tree.termSection interpretation.model interpretation.realization
      (NativeLocalTypeOperations.products_substitution C)
      (NativeLocalTypeOperations.products_beta C) (NativeLocalPiEta.products_eta C)
      interpretation.semanticContext
      interpretation.semanticType interpretation.contextRead interpretation.typeRead

theorem nativeSection_readout (tree : Tree (D := D) (context := context)
    (term := term) (type := type)) :
    interpretation.model.evaluateTerm interpretation.semanticContext term =
      some ⟨interpretation.semanticType, interpretation.nativeSection tree⟩ :=
  tree.termSection_readout interpretation.model interpretation.realization
    (NativeLocalTypeOperations.products_substitution C)
    (NativeLocalTypeOperations.products_beta C) (NativeLocalPiEta.products_eta C)
    interpretation.semanticContext interpretation.semanticType interpretation.contextRead
    interpretation.typeRead

noncomputable def valueSection (tree : Tree (D := D) (context := context)
    (term := term) (type := type)) : interpretation.valueFamily.sections :=
  reindexDisplayedSection interpretation.interface interpretation.decodedFamily
    (interpretation.nativeSection tree)

structure Certificate (point : P.Elements) where
  tree : Tree (D := D) (context := context) (term := term) (type := type)
  value : interpretation.valueFamily.obj point
  checked : value = (interpretation.valueSection tree).val point

@[ext] theorem Certificate.ext {point : P.Elements}
    {first second : interpretation.Certificate point} (trees : first.tree = second.tree)
    (values : first.value = second.value) : first = second := by
  cases first
  cases second
  cases trees
  cases values
  rfl

def mapCertificate {first second : P.Elements} (arrow : first ⟶ second)
    (certificate : interpretation.Certificate first) : interpretation.Certificate second where
  tree := certificate.tree
  value := interpretation.valueFamily.map arrow certificate.value
  checked := by
    rw [certificate.checked]
    exact (interpretation.valueSection certificate.tree).property arrow

def certificates : DisplayedFamily P where
  obj := interpretation.Certificate
  map arrow := TypeCat.ofHom (interpretation.mapCertificate arrow)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Certificate.ext interpretation
    · rfl
    · exact interpretation.valueFamily.map_id_apply point certificate.value
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro certificate
    apply Certificate.ext interpretation
    · rfl
    · exact interpretation.valueFamily.map_comp_apply first second certificate.value

def treeFamily : DisplayedFamily P :=
  (Functor.const P.Elements).obj
    (Tree (D := D) (context := context) (term := term) (type := type))

def treeReadout : interpretation.certificates ⟶
    treeFamily (C := C) (P := P) (D := D) (context := context) (term := term) (type := type) where
  app _ := TypeCat.ofHom Certificate.tree
  naturality := by intro first second arrow; rfl

def valueReadout : interpretation.certificates ⟶ interpretation.valueFamily where
  app _ := TypeCat.ofHom Certificate.value
  naturality := by intro first second arrow; rfl

/-- A supplied derivation gives a coherent certificate section. Its value
coordinate is the checked evaluator result under the actual interface. -/
noncomputable def certificateSection (tree : Tree (D := D) (context := context)
    (term := term) (type := type)) : interpretation.certificates.sections where
  val point := ⟨tree, (interpretation.valueSection tree).val point, rfl⟩
  property := by
    intro first second arrow
    apply Certificate.ext interpretation
    · rfl
    · exact (interpretation.valueSection tree).property arrow

theorem valueSection_readout (tree : Tree (D := D) (context := context)
    (term := term) (type := type)) (point : P.Elements) :
    (interpretation.valueSection tree).val point =
      (interpretation.nativeSection tree).val
          (interpretation.interface.mapElements.obj point) := rfl

/-- Alternate derivations have the same evaluator value, while their
certificate trees remain individually available. -/
theorem valueSection_derivation_independent
    (first second : Tree (D := D) (context := context) (term := term) (type := type)) :
    interpretation.valueSection first = interpretation.valueSection second := by
  apply congrArg (reindexDisplayedSection interpretation.interface
    interpretation.decodedFamily)
  exact Refinement.Derivation.termSection_derivation_independent interpretation.model
    interpretation.realization (NativeLocalTypeOperations.products_substitution C)
    (NativeLocalTypeOperations.products_beta C) (NativeLocalPiEta.products_eta C) first second
    interpretation.semanticContext interpretation.semanticType interpretation.contextRead
    interpretation.typeRead

theorem certificateSection_injective (point : P.Elements) :
    Function.Injective (fun tree => (interpretation.certificateSection tree).val point) := by
  intro first second same
  exact congrArg Certificate.tree same

/-- The retained value is forced by the generated tree and native
evaluation; it cannot be replaced by an arbitrary inhabitant of the type. -/
theorem certificate_value_unique (point : P.Elements)
    (certificate : interpretation.Certificate point) :
    certificate = (interpretation.certificateSection certificate.tree).val point := by
  apply Certificate.ext interpretation
  · rfl
  · exact certificate.checked

end Interpretation

end Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPresheafCertificates
