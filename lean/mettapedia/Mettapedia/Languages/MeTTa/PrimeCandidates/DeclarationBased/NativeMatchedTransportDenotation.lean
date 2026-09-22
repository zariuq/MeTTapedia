import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.MatchedIndexDependentTransport
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.OpaqueRelatorScopedComputation
import Mettapedia.TypeTheory.ContextualIdentitySubstitution

/-!
# Constructor meanings for the actual matched-index dependent transport

This is a partial interpretation of native wire constructors, Data variables,
reflexivity, and the endpoint-dependent J expression used by the checked
matched-index consumer. Constructor meanings do not use native decoding or
receipt validation. The consumer's independent validation supplies the
endpoint equality needed to interpret its reconstructed source.

An ambient valuation supplies only Data observations. A variable can use it
only with an actual Data typing derivation under the common HOL/wire/List/J/
relator declarations. No meaning for other fields of the mixed context is
inferred. Native Data also has formed terms outside this constructor fragment.

The semantic J is the existing full set-family equality eliminator. Its
substitution law is reused, not assumed. This equality model validates proof
irrelevance; this fragment theorem does not select K/UIP for native syntax or
interpret arbitrary motives, declarations, or universe heads.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeMatchedTransportDenotation

open Presentation Presentation.Declaration NativeIndexedFamilies
open Presentation.FormationSensitive (Typing Judgment)
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualIdentityTypes
open Mettapedia.TypeTheory.ContextualIdentitySubstitution
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

universe u

variable {n m : Nat} {State Source : Type u}

mutual

/-- Native constructors interpreted structurally. Only the variable case
consults the ambient observation, and it requires independent Data typing. -/
inductive DataDenotes (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire) :
    Tower.Tm n → (State → ULift.{u, 0} NativeWireData.Wire) → Prop where
  | variable (index : Fin n)
      (typed : Typing HOLNativeRelatorCompatibility.rules context
        (.var index) NativeWireData.dataType) :
      DataDenotes context environment (.var index) (environment index)
  | symbol (value : String) :
      DataDenotes context environment (.const (.str NativeWireData.symbolPrefix value))
        (fun _ => ⟨.symbol value⟩)
  | string (value : String) :
      DataDenotes context environment (.const (.str NativeWireData.stringPrefix value))
        (fun _ => ⟨.string value⟩)
  | natural (value : Nat) :
      DataDenotes context environment (.const (.num NativeWireData.naturalPrefix value))
        (fun _ => ⟨.natural value⟩)
  | application (head : String) {arguments : Tower.Tm n}
      {values : State → List (ULift.{u, 0} NativeWireData.Wire)}
      (meaning : DataListDenotes context environment arguments values) :
      DataDenotes context environment
        (.app (.app (.const NativeWireData.applicationName)
          (.const (.str NativeWireData.symbolPrefix head))) arguments)
        (fun state => ⟨.application head ((values state).map ULift.down)⟩)

/-- Ordered argument-list constructors in the same native Data type. -/
inductive DataListDenotes (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire) :
    Tower.Tm n → (State → List (ULift.{u, 0} NativeWireData.Wire)) → Prop where
  | nil : DataListDenotes context environment (.const NativeWireData.nilName) (fun _ => [])
  | cons {head tail : Tower.Tm n}
      {value : State → ULift.{u, 0} NativeWireData.Wire}
      {values : State → List (ULift.{u, 0} NativeWireData.Wire)}
      (headMeaning : DataDenotes context environment head value)
      (tailMeaning : DataListDenotes context environment tail values) :
      DataListDenotes context environment
        (.app (.app (.const NativeWireData.consName) head) tail)
        (fun state => value state :: values state)

end

mutual

theorem encode_denotes (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire)
    (wire : NativeWireData.Wire) :
    DataDenotes context environment (NativeWireData.encode wire) (fun _ => ⟨wire⟩) := by
  cases wire with
  | symbol value =>
      simpa only [NativeWireData.encode] using
        DataDenotes.symbol (context := context) (environment := environment) value
  | string value =>
      simpa only [NativeWireData.encode] using
        DataDenotes.string (context := context) (environment := environment) value
  | natural value =>
      simpa only [NativeWireData.encode] using
        DataDenotes.natural (context := context) (environment := environment) value
  | application head arguments =>
      simpa only [NativeWireData.encode, List.map_map, Function.comp_def,
        List.map_id_fun', ULift.down_up, id_eq] using
        DataDenotes.application head (encodeList_denotes context environment arguments)
termination_by sizeOf wire

theorem encodeList_denotes (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire)
    (wires : List NativeWireData.Wire) :
    DataListDenotes context environment (NativeWireData.encodeList wires)
      (fun _ => wires.map ULift.up) := by
  cases wires with
  | nil =>
      simpa only [NativeWireData.encodeList, List.map_nil] using
        DataListDenotes.nil (context := context) (environment := environment)
  | cons wire wires =>
      simpa only [NativeWireData.encodeList, List.map_cons] using
        DataListDenotes.cons (encode_denotes context environment wire)
        (encodeList_denotes context environment wires)
termination_by sizeOf wires

end

theorem nativePattern_denotes (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire) (pattern : Pattern) :
    DataDenotes context environment (MatchedIndexDependentTransport.nativePattern pattern)
      (fun _ => ⟨InferenceCettaWire.encodePattern pattern⟩) :=
  encode_denotes context environment _

private theorem binaryHead_typed (context : Tower.Ctx n) {name : Lean.Name}
    (declared : NativeWireData.rules.constantType name = some NativeWireData.binaryType) :
    Typing HOLNativeRelatorCompatibility.rules context (.const name) NativeWireData.binaryType := by
  have formed : Typing NativeWireData.rules .nil NativeWireData.binaryType
      (sortTm (.max Tower.zero (.max Tower.zero Tower.zero))) :=
    .piForm (NativeWireData.dataType_formed _) (.sort _)
      (.piForm (NativeWireData.dataType_formed _) (.sort _)
        (NativeWireData.dataType_formed _) (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _)
  exact HOLNativeRelatorCompatibility.wire_typing (.const declared formed (.sort _))

private theorem binary_typed {context : Tower.Ctx n} {name : Lean.Name}
    (declared : NativeWireData.rules.constantType name = some NativeWireData.binaryType)
    {left right : Tower.Tm n}
    (leftTyped : Typing HOLNativeRelatorCompatibility.rules context left NativeWireData.dataType)
    (rightTyped : Typing HOLNativeRelatorCompatibility.rules context right NativeWireData.dataType) :
    Typing HOLNativeRelatorCompatibility.rules context
      (.app (.app (.const name) left) right) NativeWireData.dataType := by
  have first : Typing HOLNativeRelatorCompatibility.rules context (.app (.const name) left)
      (.pi NativeWireData.dataType NativeWireData.dataType) := by
    simpa only [NativeWireData.binaryType, NativeWireData.dataType, inst0, subst] using
      Typing.appElim (binaryHead_typed context declared) leftTyped
  simpa only [NativeWireData.dataType, inst0, subst] using Typing.appElim first rightTyped

mutual

theorem DataDenotes.typed {context : Tower.Ctx n}
    {environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire}
    {term : Tower.Tm n} {value : State → ULift.{u, 0} NativeWireData.Wire}
    (meaning : DataDenotes context environment term value) :
    Typing HOLNativeRelatorCompatibility.rules context term NativeWireData.dataType := by
  cases meaning with
  | «variable» _ typed => exact typed
  | symbol value =>
      simpa only [NativeWireData.encode] using
        HOLNativeRelatorCompatibility.wire_typing (NativeWireData.encode_typing context (.symbol value))
  | string value =>
      simpa only [NativeWireData.encode] using
        HOLNativeRelatorCompatibility.wire_typing (NativeWireData.encode_typing context (.string value))
  | natural value =>
      simpa only [NativeWireData.encode] using
        HOLNativeRelatorCompatibility.wire_typing (NativeWireData.encode_typing context (.natural value))
  | application head arguments =>
      apply binary_typed (by decide : NativeWireData.rules.constantType
        NativeWireData.applicationName = some NativeWireData.binaryType)
      · simpa only [NativeWireData.encode] using
          HOLNativeRelatorCompatibility.wire_typing (NativeWireData.encode_typing context (.symbol head))
      · exact arguments.typed

theorem DataListDenotes.typed {context : Tower.Ctx n}
    {environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire}
    {term : Tower.Tm n} {values : State → List (ULift.{u, 0} NativeWireData.Wire)}
    (meaning : DataListDenotes context environment term values) :
    Typing HOLNativeRelatorCompatibility.rules context term NativeWireData.dataType := by
  cases meaning with
  | nil => exact HOLNativeRelatorCompatibility.wire_typing (NativeWireData.nil_typing context)
  | cons head tail =>
      exact binary_typed (by decide : NativeWireData.rules.constantType
        NativeWireData.consName = some NativeWireData.binaryType) head.typed tail.typed

end

/-- The actual endpoint-dependent motive, now allowing a scoped left endpoint. -/
def endpointMotive (point : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.id NativeWireData.dataType (rename wk (rename wk point)) (.var 1)))

@[simp] theorem endpointMotive_nativePattern (pattern : Pattern) :
    endpointMotive (MatchedIndexDependentTransport.nativePattern (n := n) pattern) =
      MatchedIndexDependentTransport.motive pattern := by
  simp [endpointMotive, MatchedIndexDependentTransport.motive]

@[simp] theorem subst_endpointMotive (substitution : Sub Tower.Head n m) (point : Tower.Tm n) :
    subst substitution (endpointMotive point) = endpointMotive (subst substitution point) := by
  simp only [endpointMotive, subst, NativeWireData.dataType, subst_liftSub_wk]
  rfl

/-- The equality family over both endpoints in the full identity context. -/
def pathMotive (State : Type u) :
    (familiesCwf.{u}).Ty
      (identityContext familiesCwf Families.identityFormation
        (fun _ : State => ULift.{u, 0} NativeWireData.Wire)) :=
  fun point => ULift (PLift (point.1.1.2 = point.1.2))

def pathBase (State : Type u) :
    (familiesCwf.{u}).Tm
      ((familiesCwf.{u}).ext State (fun _ => ULift.{u, 0} NativeWireData.Wire))
      ((familiesCwf.{u}).tySub (pathMotive State)
        (Families.identityElimination.reflexivitySubstitution _)) :=
  fun _ => ⟨⟨rfl⟩⟩

/-- Evaluation of the existing full-motive J at the supplied endpoints and
equality witness. No native decoder is involved. -/
def transportValue (left right : State → ULift.{u, 0} NativeWireData.Wire)
    (path : ∀ state, ULift.{u} (PLift (left state = right state))) :
    ∀ state, ULift.{u} (PLift (left state = right state)) :=
  fun state => Families.identityElimination.j (pathMotive State) (pathBase State)
    ⟨⟨⟨state, left state⟩, right state⟩, path state⟩

/-- The concrete transport square is a specialization of full-motive J
naturality in the existing set-family CwF. -/
theorem transportValue_substitution (substitution : Source → State)
    (left right : State → ULift.{u, 0} NativeWireData.Wire)
    (path : ∀ state, ULift.{u} (PLift (left state = right state))) :
    (fun state => transportValue left right path (substitution state)) =
      transportValue (left ∘ substitution) (right ∘ substitution)
        (fun state => path (substitution state)) := by
  funext state
  exact congrFun
    (j_substitution substitution (fun _ => ULift.{u, 0} NativeWireData.Wire)
      (pathMotive State) (pathBase State))
    ⟨⟨⟨state, left (substitution state)⟩, right (substitution state)⟩,
      path (substitution state)⟩

@[simp] theorem transportValue_reflexivity
    (value : State → ULift.{u, 0} NativeWireData.Wire) :
    transportValue value value (fun _ => ⟨⟨rfl⟩⟩) = (fun _ => ⟨⟨rfl⟩⟩) := rfl

/-- Constructorwise meaning of the supported native identity fragment.
The J constructor is the actual endpoint-motive spine, not a decoded source. -/
inductive IdentityDenotes (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire) :
    (left right proof : Tower.Tm n) →
    (leftValue rightValue : State → ULift.{u, 0} NativeWireData.Wire) →
    (∀ state, ULift.{u} (PLift (leftValue state = rightValue state))) → Prop where
  | reflexivity {point : Tower.Tm n} {value : State → ULift.{u, 0} NativeWireData.Wire}
      (meaning : DataDenotes context environment point value) :
      IdentityDenotes context environment point point (.refl point)
        value value (fun _ => ⟨⟨rfl⟩⟩)
  | eliminate {point endpoint equality : Tower.Tm n}
      {left right : State → ULift.{u, 0} NativeWireData.Wire}
      {path : ∀ state, ULift.{u} (PLift (left state = right state))}
      (meaning : IdentityDenotes context environment point endpoint equality left right path) :
      IdentityDenotes context environment point endpoint
        (Intrinsic.identityEliminateApp NativeWireData.dataType point
          (endpointMotive point) (.refl point) endpoint equality)
        left right (transportValue left right path)

/-- Interpretation of the two lambda binders, the endpoint variable, and
native identity formation in the consumer's motive. The proof argument is
available, though this particular family depends only on its endpoint. -/
inductive MotiveDenotes (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire) :
    Tower.Tm n → (left : State → ULift.{u, 0} NativeWireData.Wire) →
      ((state : State) → (right : ULift.{u, 0} NativeWireData.Wire) →
        ULift.{u} (PLift (left state = right)) → Type u) → Prop where
  | endpoint {point : Tower.Tm n} {value : State → ULift.{u, 0} NativeWireData.Wire}
      (meaning : DataDenotes context environment point value) :
      MotiveDenotes context environment (endpointMotive point) value
        (fun state right _ => ULift (PLift (value state = right)))

/-! ## Native substitution on the supported ambient observations -/

mutual

theorem DataDenotes.substitute
    {context : Tower.Ctx n} {target : Tower.Ctx m}
    {environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire}
    {targetEnvironment : Fin m → Source → ULift.{u, 0} NativeWireData.Wire}
    {term : Tower.Tm n} {value : State → ULift.{u, 0} NativeWireData.Wire}
    (meaning : DataDenotes context environment term value)
    (substitution : Sub Tower.Head n m) (reindex : Source → State)
    (components : ∀ index, Typing HOLNativeRelatorCompatibility.rules context
      (.var index) NativeWireData.dataType →
      DataDenotes target targetEnvironment (substitution index)
        (fun state => environment index (reindex state))) :
    DataDenotes target targetEnvironment (subst substitution term) (value ∘ reindex) := by
  cases meaning with
  | «variable» index typed => exact components index typed
  | symbol value => exact .symbol value
  | string value => exact .string value
  | natural value => exact .natural value
  | application head arguments =>
      exact .application head (arguments.substitute substitution reindex components)

theorem DataListDenotes.substitute
    {context : Tower.Ctx n} {target : Tower.Ctx m}
    {environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire}
    {targetEnvironment : Fin m → Source → ULift.{u, 0} NativeWireData.Wire}
    {term : Tower.Tm n} {values : State → List (ULift.{u, 0} NativeWireData.Wire)}
    (meaning : DataListDenotes context environment term values)
    (substitution : Sub Tower.Head n m) (reindex : Source → State)
    (components : ∀ index, Typing HOLNativeRelatorCompatibility.rules context
      (.var index) NativeWireData.dataType →
      DataDenotes target targetEnvironment (substitution index)
        (fun state => environment index (reindex state))) :
    DataListDenotes target targetEnvironment (subst substitution term) (values ∘ reindex) := by
  cases meaning with
  | nil => exact .nil
  | cons head tail =>
      exact .cons (head.substitute substitution reindex components)
        (tail.substitute substitution reindex components)

end

/-- The only substitution premises concern independently Data-typed
variables. They do not assign meanings to unrelated context fields. -/
theorem IdentityDenotes.substitute
    {context : Tower.Ctx n} {target : Tower.Ctx m}
    {environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire}
    {targetEnvironment : Fin m → Source → ULift.{u, 0} NativeWireData.Wire}
    {left right proof : Tower.Tm n}
    {leftValue rightValue : State → ULift.{u, 0} NativeWireData.Wire}
    {path : ∀ state, ULift.{u} (PLift (leftValue state = rightValue state))}
    (meaning : IdentityDenotes context environment left right proof leftValue rightValue path)
    (substitution : Sub Tower.Head n m) (reindex : Source → State)
    (components : ∀ index, Typing HOLNativeRelatorCompatibility.rules context
      (.var index) NativeWireData.dataType →
      DataDenotes target targetEnvironment (substitution index)
        (fun state => environment index (reindex state))) :
    IdentityDenotes target targetEnvironment (subst substitution left) (subst substitution right)
      (subst substitution proof) (leftValue ∘ reindex) (rightValue ∘ reindex)
      (fun state => path (reindex state)) := by
  induction meaning with
  | reflexivity value => exact .reflexivity (value.substitute substitution reindex components)
  | eliminate meaning induction =>
      simpa only [Intrinsic.subst_identityEliminateApp, subst_endpointMotive,
        NativeWireData.dataType, subst, transportValue_substitution] using
        IdentityDenotes.eliminate induction

/-! ## The actual checked consumer, in the common declaration environment -/

theorem native_reflexivity_step (point : Tower.Tm n) :
    Step HOLNativeRelatorCompatibility.rules.headEq
      (Intrinsic.identityEliminateApp NativeWireData.dataType point
        (endpointMotive point) (.refl point) point (.refl point)) (.refl point)
      HOLNativeRelatorCompatibility.rules.computation :=
  .root ((OpaqueRelatorExtension.root_iff HOLNativeRelatorCompatibility.opacity).mpr
    (.declared ⟨.list (.identity NativeWireData.dataType point (endpointMotive point) (.refl point))⟩))

/-- The consumer's constructor meanings, for any Data observation environment.
The same section denotes both the reconstructed J and its reflexive result. -/
theorem consume_denotes (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire)
    {expected : PolarizedNeedMatchedIndex.Request} {input : NativeWireData.Wire}
    {transport : MatchedIndexDependentTransport.Transport}
    (accepted : MatchedIndexDependentTransport.consume? expected input = some transport) :
    ∃ path : ∀ _ : State, ULift.{u} (PLift
        ((ULift.up (InferenceCettaWire.encodePattern transport.selected) :
            ULift.{u, 0} NativeWireData.Wire) =
          ULift.up (InferenceCettaWire.encodePattern transport.receipt.output))),
      MotiveDenotes context environment
        (MatchedIndexDependentTransport.motive transport.selected)
        (fun _ => ⟨InferenceCettaWire.encodePattern transport.selected⟩)
        (fun _ right _ => ULift (PLift
          ((ULift.up (InferenceCettaWire.encodePattern transport.selected) :
              ULift.{u, 0} NativeWireData.Wire) = right))) ∧
      IdentityDenotes context environment
        (MatchedIndexDependentTransport.nativePattern transport.selected)
        (MatchedIndexDependentTransport.nativePattern transport.receipt.output)
        (liftClosed transport.source)
        (fun _ => ⟨InferenceCettaWire.encodePattern transport.selected⟩)
        (fun _ => ⟨InferenceCettaWire.encodePattern transport.receipt.output⟩) path ∧
      IdentityDenotes context environment
        (MatchedIndexDependentTransport.nativePattern transport.selected)
        (MatchedIndexDependentTransport.nativePattern transport.receipt.output)
        (liftClosed transport.proof)
        (fun _ => ⟨InferenceCettaWire.encodePattern transport.selected⟩)
        (fun _ => ⟨InferenceCettaWire.encodePattern transport.receipt.output⟩) path := by
  have endpoint := (MatchedIndexDependentTransport.consume_selection accepted).2.2
  have fixed : liftRen (liftRen (Fin.elim0 : Ren 0 n)) (1 : Fin 2) = 1 := rfl
  rcases transport with ⟨receipt, selected⟩
  change selected = receipt.output at endpoint
  subst selected
  refine ⟨fun _ => ⟨⟨rfl⟩⟩, ?_, ?_, ?_⟩
  · simpa only [endpointMotive_nativePattern] using
      MotiveDenotes.endpoint (nativePattern_denotes context environment receipt.output)
  · simpa only [MatchedIndexDependentTransport.Transport.source,
      MatchedIndexDependentTransport.Transport.proof, liftClosed,
      Intrinsic.rename_identityEliminateApp, MatchedIndexDependentTransport.motive,
      endpointMotive, NativeWireData.dataType, rename,
      MatchedIndexDependentTransport.rename_nativePattern, transportValue_reflexivity, fixed] using
      IdentityDenotes.eliminate
        (IdentityDenotes.reflexivity (nativePattern_denotes context environment receipt.output))
  · simpa only [MatchedIndexDependentTransport.Transport.proof, liftClosed, rename,
      MatchedIndexDependentTransport.rename_nativePattern] using
      IdentityDenotes.reflexivity (nativePattern_denotes context environment receipt.output)

/-- Weakening uses the existing native renaming law and the actually formed
mixed context; it does not assert a semantic interpretation of that context. -/
theorem consume_common_judgments
    {expected : PolarizedNeedMatchedIndex.Request} {input : NativeWireData.Wire}
    {transport : MatchedIndexDependentTransport.Transport}
    (accepted : MatchedIndexDependentTransport.consume? expected input = some transport) :
    Judgment HOLNativeRelatorCompatibility.rules OpaqueRelatorScopedComputation.Common.context
        (liftClosed transport.source) (liftClosed transport.proposition) ∧
      Judgment HOLNativeRelatorCompatibility.rules OpaqueRelatorScopedComputation.Common.context
        (liftClosed transport.proof) (liftClosed transport.proposition) := by
  have source := HOLNativeRelatorCompatibility.wire_relator_judgment
    (MatchedIndexDependentTransport.consume_source_admitted accepted)
  have proof := HOLNativeRelatorCompatibility.wire_relator_judgment
    (MatchedIndexDependentTransport.consume_proof_admitted accepted)
  exact ⟨⟨OpaqueRelatorScopedComputation.Common.context_formed,
    source.typing.renameTyping (fun index => Fin.elim0 index)⟩,
    ⟨OpaqueRelatorScopedComputation.Common.context_formed,
      proof.typing.renameTyping (fun index => Fin.elim0 index)⟩⟩

theorem consume_native_step
    {expected : PolarizedNeedMatchedIndex.Request} {input : NativeWireData.Wire}
    {transport : MatchedIndexDependentTransport.Transport}
    (accepted : MatchedIndexDependentTransport.consume? expected input = some transport) :
    Step HOLNativeRelatorCompatibility.rules.headEq
      (liftClosed (n := n) transport.source) (liftClosed transport.proof)
      HOLNativeRelatorCompatibility.rules.computation := by
  have endpoint := (MatchedIndexDependentTransport.consume_selection accepted).2.2
  have fixed : liftRen (liftRen (Fin.elim0 : Ren 0 n)) (1 : Fin 2) = 1 := rfl
  simpa only [MatchedIndexDependentTransport.Transport.source,
    MatchedIndexDependentTransport.Transport.proof, liftClosed,
    Intrinsic.rename_identityEliminateApp, MatchedIndexDependentTransport.motive,
    endpointMotive, NativeWireData.dataType, rename,
    MatchedIndexDependentTransport.rename_nativePattern, ← endpoint, fixed] using
    native_reflexivity_step (MatchedIndexDependentTransport.nativePattern (n := n) transport.selected)

/-! ## A genuinely open Data parameter over the same mixed context -/

private def pointSchema (point : Tower.Tm n) : Sub Tower.Head 2 n :=
  consSub point (Intrinsic.elementSchemaSubstitution NativeWireData.dataType)

private theorem pointSchema_typed {context : Tower.Ctx n} {point : Tower.Tm n}
    (typed : Typing HOLNativeRelatorCompatibility.rules context point NativeWireData.dataType) :
    FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules Intrinsic.contextAX
      context (pointSchema point) := by
  have empty : FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules .nil context
      Intrinsic.emptySchemaSubstitution := fun index => Fin.elim0 index
  have element : FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules
      Intrinsic.contextA context (Intrinsic.elementSchemaSubstitution NativeWireData.dataType) :=
    empty.extend (.cumul (HOLNativeRelatorCompatibility.wire_typing
      (NativeWireData.dataType_formed context)) (fun _ => Nat.zero_le _))
  exact element.extend typed

theorem endpointMotive_typed {context : Tower.Ctx n} {point : Tower.Tm n}
    (typed : Typing HOLNativeRelatorCompatibility.rules context point NativeWireData.dataType) :
    Typing HOLNativeRelatorCompatibility.rules context (endpointMotive point)
      (subst (pointSchema point) Intrinsic.identityMotiveType) := by
  have formed := (HOLNativeRelatorCompatibility.relator_typing
    FormationSensitiveNativeIdentity.identityMotiveType_hasType).substitute (pointSchema_typed typed)
  obtain ⟨_, _, _, _, _, innerFormed, innerUniverse, _⟩ := formed.piFormation
  refine .lamIntro formed (.sort Intrinsic.identityMotiveLevel)
    (.lamIntro innerFormed innerUniverse (.cumul (.idForm
      (HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed _))
      (.sort Tower.zero) ?_ (.var 1)) (fun _ => Nat.zero_le _)))
  simpa only [NativeWireData.dataType, rename] using typed.weaken.weaken

theorem endpointMotive_conversion (point endpoint equality : Tower.Tm n) :
    Conv HOLNativeRelatorCompatibility.rules.headEq
      (.app (.app (endpointMotive point) endpoint) equality)
      (.id NativeWireData.dataType point endpoint)
      HOLNativeRelatorCompatibility.rules.computation := by
  have drop (term : Tower.Tm n) : subst (subst0 endpoint) (rename wk term) = term :=
    inst0_rename_wk endpoint term
  have one : liftSub (subst0 endpoint) (1 : Fin (n + 2)) = rename wk endpoint := rfl
  have first : Step HOLNativeRelatorCompatibility.rules.headEq
      (.app (.app (endpointMotive point) endpoint) equality)
      (.app (.lam (.id NativeWireData.dataType (rename wk point) (rename wk endpoint))) equality)
      HOLNativeRelatorCompatibility.rules.computation := by
    simpa only [endpointMotive, inst0, subst, NativeWireData.dataType,
      subst_liftSub_wk, drop, one] using
      (Step.congAppFun (a := equality)
        (Step.betaPi (headEq := HOLNativeRelatorCompatibility.rules.headEq)
          (root := HOLNativeRelatorCompatibility.rules.computation)
          (.lam (.id NativeWireData.dataType (rename wk (rename wk point)) (.var 1))) endpoint))
  have second : Step HOLNativeRelatorCompatibility.rules.headEq
      (.app (.lam (.id NativeWireData.dataType (rename wk point) (rename wk endpoint))) equality)
      (.id NativeWireData.dataType point endpoint)
      HOLNativeRelatorCompatibility.rules.computation := by
    have dropEquality (term : Tower.Tm n) : subst (subst0 equality) (rename wk term) = term :=
      inst0_rename_wk equality term
    simpa only [inst0, subst, NativeWireData.dataType, dropEquality] using
      (Step.betaPi (headEq := HOLNativeRelatorCompatibility.rules.headEq)
        (root := HOLNativeRelatorCompatibility.rules.computation)
        (.id NativeWireData.dataType (rename wk point) (rename wk endpoint)) equality)
  exact .trans _ _ _ (.rel _ _ first) (.rel _ _ second)

theorem native_reflexivity_typed {context : Tower.Ctx n} {point : Tower.Tm n}
    (typed : Typing HOLNativeRelatorCompatibility.rules context point NativeWireData.dataType) :
    Typing HOLNativeRelatorCompatibility.rules context
      (Intrinsic.identityEliminateApp NativeWireData.dataType point (endpointMotive point)
        (.refl point) point (.refl point)) (.id NativeWireData.dataType point point) := by
  have motive := (pointSchema_typed typed).extend (endpointMotive_typed typed)
  have resultFormed : Typing HOLNativeRelatorCompatibility.rules context
      (.app (.app (endpointMotive point) point) (.refl point)) (sortTm Intrinsic.motiveLevel) :=
    (HOLNativeRelatorCompatibility.relator_typing
      FormationSensitiveNativeIdentity.identityReflCaseType_hasType).substitute motive
  have branch : Typing HOLNativeRelatorCompatibility.rules context (.refl point)
      (.app (.app (endpointMotive point) point) (.refl point)) :=
    .conv (.reflIntro typed) resultFormed (.sort Intrinsic.motiveLevel)
      (.symm _ _ (endpointMotive_conversion point point (.refl point)))
  have arguments : FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules
      Intrinsic.contextAXPD context
      (Intrinsic.identitySchemaSubstitution NativeWireData.dataType point
        (endpointMotive point) (.refl point)) := motive.extend branch
  have source := (HOLNativeRelatorCompatibility.relator_typing
    FormationSensitiveNativeIdentity.identityIotaLeft_hasType).substitute arguments
  exact .conv source
    (.idForm (HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed context))
      (.sort Tower.zero) typed typed) (.sort Tower.zero)
    (endpointMotive_conversion point point (.refl point))

/-- An additional Data parameter over the actual three-field mixed context. -/
def parameterContext : Tower.Ctx 4 :=
  .snoc OpaqueRelatorScopedComputation.Common.context NativeWireData.dataType

theorem parameterContext_formed :
    FormationSensitive.ContextFormation HOLNativeRelatorCompatibility.rules parameterContext :=
  .snoc OpaqueRelatorScopedComputation.Common.context_formed
    (HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed _)) (.sort Tower.zero)

theorem parameter_typed : Typing HOLNativeRelatorCompatibility.rules parameterContext
    (.var 0) NativeWireData.dataType := .var 0

def parameterSource : Tower.Tm 4 :=
  Intrinsic.identityEliminateApp NativeWireData.dataType (.var 0)
    (endpointMotive (.var 0)) (.refl (.var 0)) (.var 0) (.refl (.var 0))

theorem parameterSource_judgment :
    Judgment HOLNativeRelatorCompatibility.rules parameterContext parameterSource
      (.id NativeWireData.dataType (.var 0) (.var 0)) :=
  ⟨parameterContext_formed, native_reflexivity_typed parameter_typed⟩

def fillParameter (pattern : Pattern) : Sub Tower.Head 4 3 :=
  consSub (MatchedIndexDependentTransport.nativePattern pattern) ids

theorem fillParameter_typed (pattern : Pattern) :
    FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules parameterContext
      OpaqueRelatorScopedComputation.Common.context (fillParameter pattern) := by
  have identity : FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules
      OpaqueRelatorScopedComputation.Common.context OpaqueRelatorScopedComputation.Common.context ids :=
    fun index => by simpa only [ids, subst_ids] using Typing.var index
  exact identity.extend (by
    simpa only [subst_ids, MatchedIndexDependentTransport.nativePattern] using
      HOLNativeRelatorCompatibility.wire_typing
        (NativeWireData.encode_typing OpaqueRelatorScopedComputation.Common.context
          (InferenceCettaWire.encodePattern pattern)))

/-- The new coordinate is a Data value. The old coordinates retain exactly
their prior observation functions, without interpreting their native types. -/
def parameterEnvironment
    (environment : Fin 3 → State → ULift.{u, 0} NativeWireData.Wire) :
    Fin 4 → (State × ULift.{u, 0} NativeWireData.Wire) → ULift.{u, 0} NativeWireData.Wire :=
  Fin.cases Prod.snd (fun index state => environment index state.1)

def parameterReindex (pattern : Pattern) :
    State → State × ULift.{u, 0} NativeWireData.Wire :=
  fun state => (state, ⟨InferenceCettaWire.encodePattern pattern⟩)

theorem parameterSource_denotes
    (environment : Fin 3 → State → ULift.{u, 0} NativeWireData.Wire) :
    IdentityDenotes parameterContext (parameterEnvironment environment) (.var 0) (.var 0)
      parameterSource Prod.snd Prod.snd (transportValue Prod.snd Prod.snd (fun _ => ⟨⟨rfl⟩⟩)) :=
  .eliminate (.reflexivity (.variable 0 parameter_typed))

theorem fillParameter_components
    (environment : Fin 3 → State → ULift.{u, 0} NativeWireData.Wire) (pattern : Pattern) :
    ∀ index, Typing HOLNativeRelatorCompatibility.rules parameterContext
      (.var index) NativeWireData.dataType →
      DataDenotes OpaqueRelatorScopedComputation.Common.context environment (fillParameter pattern index)
        (fun state => parameterEnvironment environment index (parameterReindex pattern state)) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · intro _
    exact nativePattern_denotes _ environment pattern
  · intro prior typed
    have substituted := typed.substitute (fillParameter_typed pattern)
    have variableTyped : Typing HOLNativeRelatorCompatibility.rules
        OpaqueRelatorScopedComputation.Common.context (.var prior) NativeWireData.dataType := by
      simpa only [subst, fillParameter, consSub_succ, ids, NativeWireData.dataType] using substituted
    exact .variable prior variableTyped

theorem fillParameter_source
    {expected : PolarizedNeedMatchedIndex.Request} {input : NativeWireData.Wire}
    {transport : MatchedIndexDependentTransport.Transport}
    (accepted : MatchedIndexDependentTransport.consume? expected input = some transport) :
    subst (fillParameter transport.selected) parameterSource = liftClosed transport.source := by
  have endpoint := (MatchedIndexDependentTransport.consume_selection accepted).2.2
  have fixed : liftRen (liftRen (Fin.elim0 : Ren 0 3)) (1 : Fin 2) = 1 := rfl
  simp only [parameterSource, Intrinsic.subst_identityEliminateApp, subst_endpointMotive,
    subst, fillParameter, consSub_zero, endpointMotive_nativePattern,
    MatchedIndexDependentTransport.Transport.source, MatchedIndexDependentTransport.Transport.proof,
    liftClosed, Intrinsic.rename_identityEliminateApp, MatchedIndexDependentTransport.motive,
    NativeWireData.dataType, rename, MatchedIndexDependentTransport.rename_nativePattern,
    fixed, ← endpoint]

/-- Filling an open variable, interpreting the resulting native term, and
reindexing the existing full J all agree at the actual consumed source. -/
theorem consumed_parameter_square
    (environment : Fin 3 → State → ULift.{u, 0} NativeWireData.Wire)
    {expected : PolarizedNeedMatchedIndex.Request} {input : NativeWireData.Wire}
    {transport : MatchedIndexDependentTransport.Transport}
    (accepted : MatchedIndexDependentTransport.consume? expected input = some transport) :
    FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules parameterContext
        OpaqueRelatorScopedComputation.Common.context (fillParameter transport.selected) ∧
      subst (fillParameter transport.selected) parameterSource = liftClosed transport.source ∧
      IdentityDenotes OpaqueRelatorScopedComputation.Common.context environment
        (MatchedIndexDependentTransport.nativePattern transport.selected)
        (MatchedIndexDependentTransport.nativePattern transport.selected)
        (liftClosed transport.source)
        (Prod.snd ∘ parameterReindex.{u} (State := State) transport.selected)
        (Prod.snd ∘ parameterReindex.{u} (State := State) transport.selected)
        (fun state => transportValue.{u} Prod.snd Prod.snd (fun _ => ⟨⟨rfl⟩⟩)
          (parameterReindex.{u} (State := State) transport.selected state)) ∧
      (fun state => transportValue.{u} Prod.snd Prod.snd (fun _ => ⟨⟨rfl⟩⟩)
          (parameterReindex.{u} (State := State) transport.selected state)) =
        transportValue.{u} (Prod.snd ∘ parameterReindex.{u} (State := State) transport.selected)
          (Prod.snd ∘ parameterReindex.{u} (State := State) transport.selected)
          (fun _ : State => ⟨⟨rfl⟩⟩) := by
  refine ⟨fillParameter_typed _, fillParameter_source accepted, ?_, ?_⟩
  · have interpreted := (parameterSource_denotes environment).substitute
      (fillParameter transport.selected) (parameterReindex transport.selected)
      (fillParameter_components environment transport.selected)
    rw [fillParameter_source accepted] at interpreted
    simpa only [subst, fillParameter, consSub_zero] using interpreted
  · exact transportValue_substitution (parameterReindex transport.selected)
      Prod.snd Prod.snd (fun _ => ⟨⟨rfl⟩⟩)

theorem fillParameter_proof (transport : MatchedIndexDependentTransport.Transport) :
    subst (fillParameter transport.selected) (.refl (.var 0)) = liftClosed transport.proof := by
  simp only [subst, fillParameter, consSub_zero, MatchedIndexDependentTransport.Transport.proof,
    liftClosed, rename, MatchedIndexDependentTransport.rename_nativePattern]

/-- The typed open derivation itself specializes to the admitted consumer
source. This is an additional route to its actual common-context judgment. -/
theorem consumed_parameter_judgment
    {expected : PolarizedNeedMatchedIndex.Request} {input : NativeWireData.Wire}
    {transport : MatchedIndexDependentTransport.Transport}
    (accepted : MatchedIndexDependentTransport.consume? expected input = some transport) :
    Judgment HOLNativeRelatorCompatibility.rules OpaqueRelatorScopedComputation.Common.context
      (liftClosed transport.source) (liftClosed transport.proposition) := by
  have admitted := parameterSource_judgment.substitute
    OpaqueRelatorScopedComputation.Common.context_formed (fillParameter_typed transport.selected)
  rw [fillParameter_source accepted] at admitted
  simpa only [subst, fillParameter, consSub_zero, NativeWireData.dataType,
    MatchedIndexDependentTransport.Transport.proposition, liftClosed, rename,
    MatchedIndexDependentTransport.rename_nativePattern,
    ← (MatchedIndexDependentTransport.consume_selection accepted).2.2] using admitted

/-- Actual native substitution preserves the open iota step, with precisely
the two returned native reconstruction alternatives as its boundary. -/
theorem consumed_parameter_iota_square
    {expected : PolarizedNeedMatchedIndex.Request} {input : NativeWireData.Wire}
    {transport : MatchedIndexDependentTransport.Transport}
    (accepted : MatchedIndexDependentTransport.consume? expected input = some transport) :
    Step HOLNativeRelatorCompatibility.rules.headEq parameterSource (.refl (.var 0))
        HOLNativeRelatorCompatibility.rules.computation ∧
      subst (fillParameter transport.selected) parameterSource = liftClosed transport.source ∧
      subst (fillParameter transport.selected) (.refl (.var 0)) = liftClosed transport.proof ∧
      Step HOLNativeRelatorCompatibility.rules.headEq
        (liftClosed (n := 3) transport.source) (liftClosed transport.proof)
        HOLNativeRelatorCompatibility.rules.computation := by
  have original := native_reflexivity_step (.var 0 : Tower.Tm 4)
  refine ⟨original, fillParameter_source accepted, fillParameter_proof transport, ?_⟩
  have specialized := original.substitute (fillParameter transport.selected)
  change Step _ (subst _ parameterSource) _ _ at specialized
  simpa only [fillParameter_source accepted, fillParameter_proof transport] using specialized

/-! ## Semantic boundaries of this fragment -/

theorem changed_endpoint_has_empty_fibre {left right : Pattern} (different : left ≠ right) :
    IsEmpty (ULift.{u} (PLift
      ((ULift.up (InferenceCettaWire.encodePattern left) : ULift.{u, 0} NativeWireData.Wire) =
        ULift.up (InferenceCettaWire.encodePattern right)))) := by
  constructor
  intro witness
  exact different (InferenceCettaWire.encodePattern_injective (congrArg ULift.down witness.down.down))

/-- The open parameter observation is genuinely variable: changing its
selected Pattern changes its value while preserving every old observation. -/
theorem parameter_observation_separates
    (environment : Fin 3 → State → ULift.{u, 0} NativeWireData.Wire) (state : State)
    {left right : Pattern} (different : left ≠ right) :
    parameterEnvironment environment 0 (parameterReindex left state) ≠
      parameterEnvironment environment 0 (parameterReindex right state) := by
  intro equal
  exact different (InferenceCettaWire.encodePattern_injective (congrArg ULift.down equal))

/-- Encoded receipt bytes cannot acquire an identity meaning merely by
sharing the native Data carrier with the encoded endpoints. -/
theorem encoded_wire_not_identity_denotes (context : Tower.Ctx n)
    (environment : Fin n → State → ULift.{u, 0} NativeWireData.Wire)
    (wire : NativeWireData.Wire) (left right : Tower.Tm n)
    (leftValue rightValue : State → ULift.{u, 0} NativeWireData.Wire)
    (path : ∀ state, ULift.{u} (PLift (leftValue state = rightValue state))) :
    ¬ IdentityDenotes context environment left right (NativeWireData.encode wire)
      leftValue rightValue path := by
  intro meaning
  cases wire <;> simp only [NativeWireData.encode] at meaning <;> cases meaning

/-- The native signature admits a natural literal in the application-head
slot, but the structural Wire interpretation requires an actual symbol. -/
theorem formed_data_outside_constructor_fragment
    (environment : Fin 3 → State → ULift.{u, 0} NativeWireData.Wire) :
    Judgment HOLNativeRelatorCompatibility.rules OpaqueRelatorScopedComputation.Common.context
        (.app (.app (.const NativeWireData.applicationName) (NativeWireData.encode (.natural 0)))
          (NativeWireData.encodeList [])) NativeWireData.dataType ∧
      ∀ value, ¬ DataDenotes OpaqueRelatorScopedComputation.Common.context environment
        (.app (.app (.const NativeWireData.applicationName) (NativeWireData.encode (.natural 0)))
          (NativeWireData.encodeList [])) value := by
  constructor
  · exact ⟨OpaqueRelatorScopedComputation.Common.context_formed,
      HOLNativeRelatorCompatibility.wire_typing (NativeWireData.application_typing
        (NativeWireData.encode_typing _ (.natural 0)) (NativeWireData.encodeList_typing _ []))⟩
  · intro value meaning
    simp only [NativeWireData.encode] at meaning
    cases meaning

/-! ## Checked request to native computation and constructor meaning -/

/-- Both existing reconstruction alternatives have one meaning at the
selected endpoints in the actually formed common context. The receipt has
Data meaning but no proof meaning. Source admission is obtained through the
nontrivial open-parameter substitution, not assumed from its interpretation. -/
theorem consumed_transport_crown
    (environment : Fin 3 → State → ULift.{u, 0} NativeWireData.Wire)
    {expected : PolarizedNeedMatchedIndex.Request} {input : NativeWireData.Wire}
    {transport : MatchedIndexDependentTransport.Transport}
    (accepted : MatchedIndexDependentTransport.consume? expected input = some transport) :
    ∃ path : ∀ _ : State, ULift.{u} (PLift
        ((ULift.up (InferenceCettaWire.encodePattern transport.selected) :
            ULift.{u, 0} NativeWireData.Wire) =
          ULift.up (InferenceCettaWire.encodePattern transport.receipt.output))),
      Judgment HOLNativeRelatorCompatibility.rules OpaqueRelatorScopedComputation.Common.context
        (liftClosed transport.source) (liftClosed transport.proposition) ∧
      Judgment HOLNativeRelatorCompatibility.rules OpaqueRelatorScopedComputation.Common.context
        (liftClosed transport.proof) (liftClosed transport.proposition) ∧
      Step HOLNativeRelatorCompatibility.rules.headEq
        (liftClosed (n := 3) transport.source) (liftClosed transport.proof)
        HOLNativeRelatorCompatibility.rules.computation ∧
      subst (fillParameter transport.selected) parameterSource = liftClosed transport.source ∧
      MotiveDenotes OpaqueRelatorScopedComputation.Common.context environment
        (MatchedIndexDependentTransport.motive transport.selected)
        (fun _ => ⟨InferenceCettaWire.encodePattern transport.selected⟩)
        (fun _ right _ => ULift (PLift
          ((ULift.up (InferenceCettaWire.encodePattern transport.selected) :
              ULift.{u, 0} NativeWireData.Wire) = right))) ∧
      IdentityDenotes OpaqueRelatorScopedComputation.Common.context environment
        (MatchedIndexDependentTransport.nativePattern transport.selected)
        (MatchedIndexDependentTransport.nativePattern transport.receipt.output)
        (liftClosed transport.source)
        (fun _ => ⟨InferenceCettaWire.encodePattern transport.selected⟩)
        (fun _ => ⟨InferenceCettaWire.encodePattern transport.receipt.output⟩) path ∧
      IdentityDenotes OpaqueRelatorScopedComputation.Common.context environment
        (MatchedIndexDependentTransport.nativePattern transport.selected)
        (MatchedIndexDependentTransport.nativePattern transport.receipt.output)
        (liftClosed transport.proof)
        (fun _ => ⟨InferenceCettaWire.encodePattern transport.selected⟩)
        (fun _ => ⟨InferenceCettaWire.encodePattern transport.receipt.output⟩) path ∧
      DataDenotes OpaqueRelatorScopedComputation.Common.context environment
        (NativeWireData.encode (PolarizedNeedMatchedIndex.admittedWire transport.receipt))
        (fun _ => ⟨PolarizedNeedMatchedIndex.admittedWire transport.receipt⟩) ∧
      ¬ IdentityDenotes OpaqueRelatorScopedComputation.Common.context environment
        (MatchedIndexDependentTransport.nativePattern transport.selected)
        (MatchedIndexDependentTransport.nativePattern transport.receipt.output)
        (NativeWireData.encode (PolarizedNeedMatchedIndex.admittedWire transport.receipt))
        (fun _ => ⟨InferenceCettaWire.encodePattern transport.selected⟩)
        (fun _ => ⟨InferenceCettaWire.encodePattern transport.receipt.output⟩) path := by
  obtain ⟨path, motive, source, proof⟩ := consume_denotes
    OpaqueRelatorScopedComputation.Common.context environment accepted
  exact ⟨path, consumed_parameter_judgment accepted, (consume_common_judgments accepted).2,
    (consumed_parameter_iota_square accepted).2.2.2, fillParameter_source accepted,
    motive, source, proof, encode_denotes _ environment _,
    encoded_wire_not_identity_denotes _ environment _ _ _ _ _ path⟩

#print axioms encode_denotes
#print axioms DataDenotes.typed
#print axioms endpointMotive_typed
#print axioms endpointMotive_conversion
#print axioms transportValue_substitution
#print axioms IdentityDenotes.substitute
#print axioms consume_denotes
#print axioms consume_common_judgments
#print axioms native_reflexivity_typed
#print axioms parameterSource_judgment
#print axioms fillParameter_typed
#print axioms consumed_parameter_square
#print axioms consumed_parameter_judgment
#print axioms consumed_parameter_iota_square
#print axioms changed_endpoint_has_empty_fibre
#print axioms parameter_observation_separates
#print axioms encoded_wire_not_identity_denotes
#print axioms formed_data_outside_constructor_fragment
#print axioms consumed_transport_crown

end NativeMatchedTransportDenotation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
