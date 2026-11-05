import Mettapedia.Logic.HOL.IndexedVectorLookupCongruence
import Mettapedia.Logic.HOL.IndexedVectorPredicateControls

/-!
# Lookup transport across actual beta equations

The positive controls move existing lookups across syntactically different
beta wrappers in their vector, position and element. An arbitrary array's
position and selected value move together, with a nonconstant natural/Boolean
interpretation. Independent inequalities refuse fabricated position and
element equations. No unproved lookup or semantic-to-syntax conversion is
used to supply the original membership.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedVectorLookupCongruenceControls
open IndexedVectorPredicate.Controls

def wrap {Γ : Ctx BaseSort} {type : Ty BaseSort} (term : Term Const Γ type) : Term Const Γ type :=
  .app (.lam (.var .vz)) term
def unwrap {Γ : Ctx BaseSort} {type : Ty BaseSort} {Δ : List (Formula Const Γ)}
    (term : Term Const Γ type) : ProofSyntax Const Δ (.eq (wrap term) term) := .beta term (.var .vz)
theorem unwrap_free {Γ : Ctx BaseSort} {type : Ty BaseSort} {Δ : List (Formula Const Γ)}
    (term : Term Const Γ type) : (unwrap (Δ := Δ) term).FunctionExtensionalityFree := by trivial

def original : ProofSyntax Const []
    (IndexedVectorPositions.lookup signature one singleton signature.zero (.const .truth)) :=
  IndexedVectorPositions.here signature signature.zero (.const .truth) signature.nil
theorem original_free : original.FunctionExtensionalityFree := IndexedVectorPositions.here_free _ _ _ _

def wrappedVector : ProofSyntax Const []
    (IndexedVectorPositions.lookup signature one (wrap singleton) signature.zero (.const .truth)) :=
  .impE (.eqPropER (IndexedVectorPositions.lookup_vec_eq signature one (wrap singleton) singleton signature.zero
    (.const .truth) (unwrap singleton))) original
theorem wrappedVector_free : wrappedVector.FunctionExtensionalityFree :=
  ⟨IndexedVectorPositions.lookup_vec_eq_free _ _ _ _ _ _ _ (unwrap_free _),original_free⟩

def wrappedPosition : ProofSyntax Const []
    (IndexedVectorPositions.lookup signature one singleton (wrap signature.zero) (.const .truth)) :=
  .impE (.eqPropER (IndexedVectorPositions.lookup_position_eq signature one singleton
    (wrap signature.zero) signature.zero (.const .truth) (unwrap signature.zero))) original
theorem wrappedPosition_free : wrappedPosition.FunctionExtensionalityFree :=
  ⟨IndexedVectorPositions.lookup_position_eq_free _ _ _ _ _ _ _ (unwrap_free _),original_free⟩

def wrappedElement : ProofSyntax Const []
    (IndexedVectorPositions.lookup signature one singleton signature.zero (wrap (.const .truth))) :=
  .impE (.eqPropER (IndexedVectorPositions.lookup_element_eq signature one singleton signature.zero
    (wrap (.const .truth)) (.const .truth) (unwrap (.const .truth)))) original
theorem wrappedElement_free : wrappedElement.FunctionExtensionalityFree :=
  ⟨IndexedVectorPositions.lookup_element_eq_free _ _ _ _ _ _ _ (unwrap_free _),original_free⟩

abbrev openContext : Ctx BaseSort := [number ⇒ element]
def array : Term Const openContext (number ⇒ element) := .var .vz
def zero : Term Const openContext number := weakenCtx _ signature.zero
def index : Term Const openContext number := .app (weakenCtx _ signature.successor) zero
def vector : Term Const openContext signature.vector :=
  signature.consValue zero (.app array zero) (weakenCtx _ signature.nil)
def originalArray : ProofSyntax Const []
    (IndexedVectorPositions.lookup signature index vector zero (.app array zero)) :=
  IndexedVectorPositions.here signature zero (.app array zero) (weakenCtx _ signature.nil)
theorem originalArray_free : originalArray.FunctionExtensionalityFree := IndexedVectorPositions.here_free _ _ _ _

def wrappedArrayObservation : ProofSyntax Const []
    (IndexedVectorPositions.lookup signature index vector (wrap zero) (.app array (wrap zero))) :=
  .impE (.eqPropER (IndexedVectorPositions.lookup_arrayAt_eq signature index vector array (wrap zero) zero
    (unwrap zero))) originalArray
theorem wrappedArrayObservation_free : wrappedArrayObservation.FunctionExtensionalityFree :=
  ⟨IndexedVectorPositions.lookup_arrayAt_eq_free _ _ _ _ _ _ _ (unwrap_free _),originalArray_free⟩

def actualModel := model (fun _ => True) 0 []
def emptyValues : actualModel.Valuation [] := fun entry => nomatch entry
def openValues : actualModel.Valuation openContext :=
  actualModel.extend (σ := number ⇒ element) emptyValues (fun n => ULift.up (n.down % 2 == 0))
theorem full : actualModel.FullDomains := HenkinModel.fullDomains_standard _ _

theorem sound {formula : ClosedFormula Const} (proof : ProofSyntax Const [] formula) :
    (actualModel.denote formula emptyValues).down :=
  Soundness.extDerivation_sound proof.erase (M := actualModel) (ρ := emptyValues)
    (actualModel.functionsRespectEqv_of_fullDomains full) (fun _ => trivial)
    (by intro claim impossible; cases impossible)

theorem all_wrapped_lookups_hold :
    (actualModel.denote (IndexedVectorPositions.lookup signature one (wrap singleton) signature.zero (.const .truth)) emptyValues).down ∧
    (actualModel.denote (IndexedVectorPositions.lookup signature one singleton (wrap signature.zero) (.const .truth)) emptyValues).down ∧
    (actualModel.denote (IndexedVectorPositions.lookup signature one singleton signature.zero (wrap (.const .truth))) emptyValues).down := by
  exact ⟨sound wrappedVector,sound wrappedPosition,sound wrappedElement⟩

theorem actual_correlated_observation_holds :
    (actualModel.denote (IndexedVectorPositions.lookup signature index vector (wrap zero)
      (.app array (wrap zero))) openValues).down :=
  Soundness.extDerivation_sound wrappedArrayObservation.erase (M := actualModel) (ρ := openValues)
    (actualModel.functionsRespectEqv_of_fullDomains full) (fun _ => trivial)
    (by intro formula impossible; cases impossible)

theorem array_is_nonconstant :
    actualModel.denote array openValues (ULift.up 0) ≠ actualModel.denote array openValues (ULift.up 1) := by
  intro same
  have impossible : true = false := congrArg ULift.down same
  cases impossible

theorem false_position_equation_refused : ¬ Nonempty (ProofSyntax Const [] (.eq signature.zero one)) := by
  rintro ⟨claimed⟩
  have same := Soundness.extTheorem_sound claimed.erase actualModel (actualModel.functionsRespectEqv_of_fullDomains full)
  have impossible : (0 : Nat) = 1 := congrArg ULift.down same
  cases impossible

theorem false_element_equation_refused : ¬ Nonempty (ProofSyntax Const (Γ := []) [] (.eq (.const .truth) (.const .falsity))) := by
  rintro ⟨claimed⟩
  have same := Soundness.extTheorem_sound claimed.erase actualModel (actualModel.functionsRespectEqv_of_fullDomains full)
  have impossible : true = false := congrArg ULift.down same
  cases impossible

#print axioms wrappedVector_free
#print axioms wrappedPosition_free
#print axioms wrappedElement_free
#print axioms wrappedArrayObservation_free
#print axioms actual_correlated_observation_holds
#print axioms false_position_equation_refused

end Mettapedia.Logic.HOL.IndexedVectorLookupCongruenceControls
