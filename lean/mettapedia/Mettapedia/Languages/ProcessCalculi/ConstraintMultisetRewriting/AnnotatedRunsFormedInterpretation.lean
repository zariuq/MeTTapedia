import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormedAppend

/-!
# Interpretation of formed evidence along a theory extension

A theory extension installs a declaration signature in the rules (`extendRules`). Formed evidence
of the base theory is interpreted in the extension (`FormedEvidence.interpret`):

* contexts, types and terms keep their codes, and their formation derivations move by the
  Flower's signature inclusion (`ContextFormation.includeSignature`, `Typing.includeSignature`);
* certificates keep their structure and re-encode their root codes (`Code.mapRoot`); the
  extension's decoder must agree with the base decoder on the re-encoded roots (`RootMap`), and
  then the re-encoded code is accepted at the same endpoints (`Code.check_mapRoot`).

## Coherence

* The interpretation keeps the number of selected steps (`interpret_stepCount`).
* **Interpretation commutes with context substitution** on the evidence's data, when the root map
  commutes with the two root actions (`interpret_reindex_data`).

The extension adds a name (`Descent.extension_adds_name`): the declared append is typed in the
extension and not in the base. That name unfolds to a base term by a checked delta step, so the
extension here is definitional, and nothing in this file shows that interpretation is one-way.

The root maps and root actions carry their laws as fields (`RootMap.roots`, the fields of
`RootAction`); every instance below proves them.

## The instance

The vector theory, extended by the declared append program (`AppendDefinitionCompletion`): the
root map is `inherited`, the extension's root action substitutes inherited codes by the vector
action (`appendRootAction`), and append's formed evidence, substituted by `a ↦ 0, b ↦ 1` and
interpreted, agrees with interpreting first and substituting after
(`append_interpretation_coherent`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation (Tm Sub subst liftClosed)
open Presentation.FormationSensitiveContextual (Context TypeOver Term TotalTerm QTerm empty)
open Presentation.StructuralConversionCode (RootDecoder Certificate Code StepCode mapEndpoints)

/-! ## Root maps commute with substitution -/

section Codes

variable {Head : Type} {Source Target : Nat → Type}
variable (substituteSource : {n m : Nat} → Sub Head n m → Source n → Source m)
  (substituteTarget : {n m : Nat} → Sub Head n m → Target n → Target m)
  (map : {n : Nat} → Source n → Target n)

theorem stepCode_substitute_mapRoot
    (natural : ∀ {n m : Nat} (σ : Sub Head n m) (code : Source n),
      map (substituteSource σ code) = substituteTarget σ (map code))
    {n m : Nat} (σ : Sub Head n m) (code : StepCode Head Source n) :
    (code.substitute substituteSource σ).mapRoot map =
      (code.mapRoot map).substitute substituteTarget σ := by
  induction code generalizing m <;>
    simp_all only [StepCode.substitute, StepCode.mapRoot]

theorem code_substitute_mapRoot
    (natural : ∀ {n m : Nat} (σ : Sub Head n m) (code : Source n),
      map (substituteSource σ code) = substituteTarget σ (map code))
    {n m : Nat} (σ : Sub Head n m) (code : Code Head Source n) :
    (code.substitute substituteSource σ).mapRoot map =
      (code.mapRoot map).substitute substituteTarget σ := by
  induction code with
  | single step =>
      simp only [Code.substitute, Code.mapRoot,
        stepCode_substitute_mapRoot substituteSource substituteTarget map natural]
  | refl term => simp only [Code.substitute, Code.mapRoot]
  | symm code ih => simp only [Code.substitute, Code.mapRoot, ih]
  | trans first second firstIH secondIH =>
      simp only [Code.substitute, Code.mapRoot, firstIH, secondIH]

theorem stepCount_mapRoot {n : Nat} (code : Code Head Source n) :
    (code.mapRoot map).stepCount = code.stepCount := by
  induction code with
  | single step => simp only [Code.mapRoot, Code.stepCount]
  | refl term => simp only [Code.mapRoot, Code.stepCount]
  | symm code ih => simpa only [Code.mapRoot, Code.stepCount] using ih
  | trans first second firstIH secondIH =>
      simp only [Code.mapRoot, Code.stepCount, firstIH, secondIH]

end Codes

/-! ## Interpretation along an extension -/

section Interpretation

variable {Head : Type} [DecidableEq Head] {R : Presentation.Rules Head} [DecidableRel R.headEq]
variable (signature : Presentation.Declaration.Signature Head)

/-- The extension keeps the base's head equality, and its decision. -/
instance extendedHeadEq : DecidableRel (Presentation.Declaration.extendRules R signature).headEq :=
  fun a b => (inferInstance : Decidable (R.headEq a b))

/-- A formed context of the base, formed in the extension. -/
def includeContext (context : Context R) : Context (Presentation.Declaration.extendRules R signature) :=
  ⟨context.arity, context.raw, context.formed.includeSignature signature⟩

def includeType {context : Context R} (type : TypeOver context) :
    TypeOver (includeContext signature context) :=
  ⟨type.code, type.level, type.universeWitness, type.formed.includeSignature signature⟩

def includeTerm {context : Context R} {type : TypeOver context} (term : Term context type) :
    Term (includeContext signature context) (includeType signature type) :=
  ⟨term.code, term.typed.includeSignature signature⟩

def includeTotal {context : Context R} (source : TotalTerm context) :
    TotalTerm (includeContext signature context) :=
  ⟨includeType signature source.1, includeTerm signature source.2⟩

/-- A formed substitution of the base, formed in the extension. -/
def includeHom {other context : Context R} (morphism : other ⟶ context) :
    includeContext signature other ⟶ includeContext signature context :=
  ⟨morphism.substitution, fun index => (morphism.typed index).includeSignature signature⟩

/-- **A re-encoding of root codes** into the extension's decoder that decodes alike. -/
structure RootMap (decoder : RootDecoder R.computation)
    (decoder' : RootDecoder (Presentation.Declaration.extendRules R signature).computation) where
  map : {n : Nat} → decoder.Code n → decoder'.Code n
  roots : ∀ {n : Nat} (code : decoder.Code n), decoder'.decode (map code) = decoder.decode code

variable {signature} {decoder : RootDecoder R.computation}
  {decoder' : RootDecoder (Presentation.Declaration.extendRules R signature).computation}

/-- A certificate re-encoded for the extension, accepted at the same endpoints. -/
def includeCertificate (rootMap : RootMap signature decoder decoder') {n : Nat} {a b : Tm Head n}
    (certificate : Certificate R.headEq decoder.decode a b) :
    Certificate (Presentation.Declaration.extendRules R signature).headEq decoder'.decode a b :=
  ⟨certificate.code.mapRoot rootMap.map,
    (Code.check_mapRoot R.headEq decoder.decode decoder'.decode rootMap.map rootMap.roots
      certificate.code a b).trans certificate.checked⟩

namespace FormedEvidence

variable {context : Context R} {source : TotalTerm context} {target : Tm Head context.arity}

/-- **Formed evidence interpreted in the extension.** -/
def interpret (rootMap : RootMap signature decoder decoder')
    (e : FormedEvidence decoder context source target) :
    FormedEvidence decoder' (includeContext signature context) (includeTotal signature source) target where
  targetType := includeType signature e.targetType
  targetTerm := includeTerm signature e.targetTerm
  target_code := e.target_code
  typeCertificate := includeCertificate rootMap e.typeCertificate
  termCertificate := includeCertificate rootMap e.termCertificate

/-- The interpretation keeps the number of selected steps. -/
theorem interpret_stepCount (rootMap : RootMap signature decoder decoder')
    (e : FormedEvidence decoder context source target) :
    (e.interpret rootMap).stepCount = e.stepCount := by
  simp only [stepCount, interpret, includeCertificate, stepCount_mapRoot]
  rfl

/-- **Interpretation commutes with context substitution**, on the evidence's data, when the root
map commutes with the two root actions. -/
theorem interpret_reindex_data (rootMap : RootMap signature decoder decoder')
    (action : RootAction decoder) (action' : RootAction decoder')
    (natural : ∀ {n m : Nat} (σ : Sub Head n m) (code : decoder.Code n),
      rootMap.map (action.substitute σ code) = action'.substitute σ (rootMap.map code))
    (e : FormedEvidence decoder context source target) {other : Context R}
    (morphism : other ⟶ context) :
    ((e.reindex action morphism).interpret rootMap).data =
      ((e.interpret rootMap).reindex action' (includeHom signature morphism)).data := by
  simp only [data, interpret, reindex, includeCertificate, reindexCertificate, includeType,
    TypeOver.reindex]
  change ((subst morphism.substitution e.targetType.code, e.targetType.level),
      (e.typeCertificate.code.substitute action.substitute morphism.substitution).mapRoot rootMap.map,
      (e.termCertificate.code.substitute action.substitute morphism.substitution).mapRoot rootMap.map) =
    ((subst morphism.substitution e.targetType.code, e.targetType.level),
      (e.typeCertificate.code.mapRoot rootMap.map).substitute action'.substitute morphism.substitution,
      (e.termCertificate.code.mapRoot rootMap.map).substitute action'.substitute morphism.substitution)
  rw [code_substitute_mapRoot action.substitute action'.substitute rootMap.map natural,
    code_substitute_mapRoot action.substitute action'.substitute rootMap.map natural]

end FormedEvidence

end Interpretation

/-! ## The instance: the vector theory extended by the declared append -/

namespace AppendInterpretation

abbrev library := AppendDefinitionCompletion.library

/-- Substitution of the extension's root codes: inherited codes by the vector action, delta codes
are closed, declared codes are empty. -/
def appendRootSubstitute {n m : Nat} (σ : Sub Presentation.Tower.Head n m) :
    AppendDefinitionCompletion.decoder.Code n → AppendDefinitionCompletion.decoder.Code m
  | .inherited code => .inherited (Append.vectorRootSubstitute σ code)
  | .delta name => .delta name
  | .declared code => nomatch code

theorem library_delta_natural {n m : Nat} (σ : Sub Presentation.Tower.Head n m)
    (name : Presentation.DeclName) :
    (library.valueOf? name).map (fun value => (Tm.const name, liftClosed (n := m) value)) =
      mapEndpoints (subst σ)
        ((library.valueOf? name).map (fun value => (Tm.const name, liftClosed (n := n) value))) := by
  cases library.valueOf? name with
  | none => rfl
  | some value => simp [mapEndpoints, subst]

/-- **The actual root action of the extension's decoder.** -/
def appendRootAction : RootAction AppendDefinitionCompletion.decoder where
  substitute := appendRootSubstitute
  natural := by
    intro n m σ code
    cases code with
    | inherited code => exact Append.vectorRootAction.natural σ code
    | delta name => exact library_delta_natural σ name
    | declared code => exact nomatch code
  substitute_ids := by
    intro n code
    cases code with
    | inherited code =>
        exact congrArg Presentation.DeclarationConversionCode.RootCode.inherited
          (Append.vectorRootAction.substitute_ids code)
    | delta name => rfl
    | declared code => exact nomatch code
  substitute_comp := by
    intro n m k σ τ code
    cases code with
    | inherited code =>
        exact congrArg Presentation.DeclarationConversionCode.RootCode.inherited
          (Append.vectorRootAction.substitute_comp σ τ code)
    | delta name => rfl
    | declared code => exact nomatch code

/-- Base roots are inherited roots of the extension. -/
def inheritedMap :
    RootMap library NativeNaturalVectorFamilies.Programs.decoder AppendDefinitionCompletion.decoder where
  map code := .inherited code
  roots _ := rfl

/-- Append's formed evidence in the theory with the declared append. -/
def interpretedEvidence := Append.appendEvidence.interpret inheritedMap

theorem interpreted_stepCount : interpretedEvidence.stepCount = Append.appendEvidence.stepCount :=
  Append.appendEvidence.interpret_stepCount inheritedMap

theorem interpreted_retyped :
    Presentation.FormationSensitive.Judgment AppendDefinitionCompletion.rules Append.ctx
      Append.sourceCode Append.valueType :=
  interpretedEvidence.retyped

/-- **Interpretation and substitution commute on append's evidence**: substituting `a ↦ 0, b ↦ 1`
and interpreting gives the data of interpreting and substituting. -/
theorem append_interpretation_coherent :
    ((Append.appendEvidence.reindex Append.vectorRootAction Append.closing).interpret inheritedMap).data =
      (interpretedEvidence.reindex appendRootAction (includeHom library Append.closing)).data :=
  Append.appendEvidence.interpret_reindex_data inheritedMap Append.vectorRootAction appendRootAction
    (fun _ _ => rfl) Append.closing

end AppendInterpretation

#print axioms stepCode_substitute_mapRoot
#print axioms code_substitute_mapRoot
#print axioms stepCount_mapRoot
#print axioms FormedEvidence.interpret
#print axioms FormedEvidence.interpret_stepCount
#print axioms FormedEvidence.interpret_reindex_data
#print axioms AppendInterpretation.appendRootAction
#print axioms AppendInterpretation.interpreted_stepCount
#print axioms AppendInterpretation.interpreted_retyped
#print axioms AppendInterpretation.append_interpretation_coherent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
