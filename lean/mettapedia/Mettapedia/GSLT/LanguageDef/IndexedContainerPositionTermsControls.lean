import Mettapedia.Logic.HOL.IndexedContainerPositionTerms

/-!
# Mixed registered-container compiler controls

List counts come from retained shapes; Vector counts come from scoped output
expressions. Interleaving both with data binders and direct children tests the
generated field order, repeated indices and zero-length segment boundaries.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedContainerPositionTermsControls

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.IndexedContainerPositionTerms
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory

def interface : Interface where
  SortCode := VectorControl.DataSort
  Value := VectorControl.value
  Index := Nat
  IndexExpr := VectorControl.LengthExpr
  evalIndex := VectorControl.evalLength

def listEntry : Entry interface := ListInstance.entry interface
def vectorEntry : Entry interface where
  Output := Nat
  OutputExpr := VectorControl.LengthExpr
  evalOutput := VectorControl.evalLength
  container := IndexedContainer.Examples.vector

def registry : Registry interface where
  lookup name := if name = "List" then some listEntry else if name = "Vector" then some vectorEntry else none

def ordered : registry.OrderedFinitary where
  containerOrdered := by
    intro name entry registered
    by_cases list : name = "List"
    · subst name
      simp only [registry, if_pos] at registered
      cases Option.some.inj registered
      exact IndexedContainer.Examples.listOrderedFinitary
    · by_cases vector : name = "Vector"
      · subst name
        simp only [registry, show ("Vector" : String) ≠ "List" by decide, if_false, if_pos] at registered
        cases Option.some.inj registered
        exact IndexedContainer.Examples.vectorOrderedFinitary
      · simp [registry, list, vector] at registered

abbrev number : Ty Unit := .base ()
inductive Symbol : Ty Unit → Type where
  | zero : Symbol number
  | successor : Symbol (number ⇒ number)

def model : HenkinModel.{0,0,0} Unit Symbol :=
  .standard (fun _ => ULift.{1} Nat) (fun symbol => match symbol with
    | .zero => .up 0
    | .successor => fun n => .up (n.down + 1))
def empty : model.Valuation [] := fun impossible => nomatch impossible
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _
def zero : ClosedTerm Symbol number := .const .zero
def successor : ClosedTerm Symbol (number ⇒ number) := .const .successor

def lengthVariable (parameters : Ctx Unit) : {context : List interface.SortCode} →
    VectorControl.LengthExpr context → Var (context.map (fun _ => number) ++ parameters) number
  | _, .here => .vz
  | _, .there prior => .vs (lengthVariable parameters prior)

def indices : IndexedConstructorTerms.Reading interface Symbol where
  sort := fun _ => number
  index := number
  parameters := []
  term expression := .var (lengthVariable [] expression)

def countTerm {context : List interface.SortCode} (name : String) (entry : Entry interface)
    (registered : registry.lookup name = some entry) (output : entry.OutputExpr context) :
    Term Symbol (context.map (fun _ => number) ++ []) (number ⇒ number) := by
  by_cases list : name = "List"
  · exact .lam (.var .vz)
  · by_cases vector : name = "Vector"
    · subst name
      have same : vectorEntry = entry := by simpa [registry] using registered
      subst entry
      exact .lam (weaken (.var (lengthVariable [] output)))
    · simp [registry, list, vector] at registered

def reading : Reading interface registry Symbol where
  indices := indices
  number := number
  one := .app successor zero
  shapeType := fun _ _ _ => number
  count := countTerm

def encodeValue : ∀ sort, interface.Value sort → Ty.denote.{0,0} model.Carrier (indices.sort sort)
  | .length, value => .up value
  | .payload, value => match (show Bool from value) with
      | false => .up 0
      | true => .up 1

def encodeShape (name : String) (entry : Entry interface) (registered : registry.lookup name = some entry)
    (output : entry.Output) (shape : entry.container.Shape output) : Ty.denote.{0,0} model.Carrier number := by
  by_cases list : name = "List"
  · subst name
    have same : listEntry = entry := by simpa [registry] using registered
    subst entry
    exact .up shape
  · by_cases vector : name = "Vector"
    · exact .up 0
    · simp [registry, list, vector] at registered

theorem length_denote {context : List interface.SortCode} (expression : VectorControl.LengthExpr context)
    (environment : Env interface.Value context) :
    model.denote (indices.term expression) (indices.valuation model encodeValue empty environment) =
      ULift.up (VectorControl.evalLength expression environment) := by
  induction expression with
  | here => rfl
  | there prior hypothesis => exact hypothesis environment.2

theorem count_correct {context : List interface.SortCode} (name : String) (entry : Entry interface)
    (registered : registry.lookup name = some entry) (output : entry.OutputExpr context)
    (environment : Env interface.Value context)
    (sourceShape : entry.container.Shape (entry.evalOutput output environment)) :
    model.denote (reading.count name entry registered output)
      (indices.valuation model encodeValue empty environment) (encodeShape name entry registered _ sourceShape) =
      ULift.up ((ordered.containerOrdered name entry registered).positions sourceShape).length := by
  by_cases list : name = "List"
  · subst name
    have same : listEntry = entry := by simpa [registry] using registered
    subst entry
    change ULift.up sourceShape = ULift.up (List.ofFn (fun i : Fin sourceShape => i)).length
    rw [List.length_ofFn]
  · by_cases vector : name = "Vector"
    · subst name
      have same : vectorEntry = entry := by simpa [registry] using registered
      subst entry
      change model.denote (indices.term output) (indices.valuation model encodeValue empty environment) =
        ULift.up (List.ofFn (fun i : Fin (VectorControl.evalLength output environment) => i)).length
      simpa only [List.length_ofFn] using length_denote output environment
    · simp [registry, list, vector] at registered

def realization : Realization reading ordered model where
  numbers := Equiv.ulift.symm
  value := encodeValue
  index := ULift.up
  shape := encodeShape
  parameterValues := empty
  index_correct := length_denote
  one_correct := by intro values; rfl
  count_correct := count_correct

def mixedCode : Code interface registry 0 [] :=
  .data .length
    (.recursive .here
      (.nested "List" listEntry (by simp [registry]) PUnit.unit .here
        (.data .length
          (.nested "Vector" vectorEntry (by simp [registry]) .here (.there .here)
            (.recursive .here (.result .here))))))

def mixedShape (outer listLength inner : Nat) :
    Code.Shape mixedCode PUnit.unit inner :=
  ⟨outer, listLength, inner, (), ⟨⟨rfl⟩⟩⟩

theorem generated_fields : reading.fields mixedCode = [number, number, number, number] := rfl

theorem mixed_segments (outer listLength inner : Nat) :
    Code.positionSegments ordered mixedCode (mixedShape outer listLength inner) =
      [(1, outer), (listLength, outer), (inner, outer), (1, inner)] := by
  change [(1, outer), ((List.ofFn (fun i : Fin listLength => i)).length, outer),
    ((List.ofFn (fun i : Fin inner => i)).length, outer), (1, inner)] = _
  simp only [List.length_ofFn]

theorem generated_plan (outer listLength inner : Nat) :
    OrderedPositionPrograms.evaluateFields model realization.numbers (reading.fields mixedCode) empty
      (realization.encodeFields mixedCode (mixedShape outer listLength inner))
      (reading.compile mixedCode Subst.id) =
      [(1, ULift.up outer), (listLength, ULift.up outer), (inner, ULift.up outer), (1, ULift.up inner)] := by
  have computed := realization.compile_evaluate mixedCode PUnit.unit (mixedShape outer listLength inner)
    Subst.id empty (fun impossible => nomatch impossible)
  rw [mixed_segments] at computed
  exact computed

theorem generated_result (outer listLength inner : Nat) :
    CurriedPredicates.applyValues model (reading.fields mixedCode)
      (model.denote (reading.resultProgram mixedCode Subst.id) empty)
      (realization.encodeFields mixedCode (mixedShape outer listLength inner)) = ULift.up inner :=
  realization.resultProgram_denote mixedCode PUnit.unit (mixedShape outer listLength inner)
    Subst.id empty (fun impossible => nomatch impossible)

def reads (outer listLength inner slot childIndex : Nat) : Prop :=
  (FiniteConstructorEncoding.apply (Ty.denote model.Carrier) (reading.fields mixedCode)
    (Mettapedia.Logic.HOL.FiniteConstructorEncoding.handlerEquivalence model _
      (model.denote (OrderedPositionPrograms.fieldGraph zero successor (reading.fields mixedCode)
        (reading.compile mixedCode Subst.id)) empty (ULift.up slot) (ULift.up childIndex)))
    (realization.encodeFields mixedCode (mixedShape outer listLength inner))).down

theorem reads_iff_lookup (outer listLength inner slot childIndex : Nat) :
    reads outer listLength inner slot childIndex ↔
      (List.replicate (1 + listLength + inner) outer ++ [inner])[slot]? = some childIndex := by
  unfold reads
  rw [OrderedPositionPrograms.fieldGraph_denote zero successor model realization.numbers full empty
    (show model.denote zero empty = realization.numbers 0 from rfl) (fun _ => rfl)]
  change (OrderedPositionSegments.flatten
    (OrderedPositionPrograms.evaluateFields model realization.numbers (reading.fields mixedCode) empty
      (realization.encodeFields mixedCode (mixedShape outer listLength inner))
      (reading.compile mixedCode Subst.id)))[slot]? = some (ULift.up childIndex) ↔ _
  rw [generated_plan]
  have same : OrderedPositionSegments.flatten
      [(1, ULift.up outer), (listLength, ULift.up outer), (inner, ULift.up outer), (1, ULift.up inner)] =
      (List.replicate (1 + listLength + inner) outer ++ [inner]).map (ULift.up : Nat → ULift.{1} Nat) := by
    simp only [OrderedPositionSegments.flatten_cons, OrderedPositionSegments.flatten_nil,
      List.replicate_one, List.append_nil, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.replicate_add, List.append_assoc]
  rw [same, List.getElem?_map]
  constructor
  · intro accepted
    obtain ⟨source, found, equal⟩ := Option.map_eq_some_iff.mp accepted
    cases ULift.up.inj equal
    exact found
  · intro found
    rw [found]
    rfl

theorem reads_source_position (outer listLength inner slot childIndex : Nat) :
    reads outer listLength inner slot childIndex ↔
      ∃ position, ((RecursiveSpaceRepresentation.codePresentation ordered mixedCode).coding
        (mixedShape outer listLength inner)).decode slot = some position ∧
          Code.next mixedCode (mixedShape outer listLength inner) position = childIndex := by
  have graph := realization.fieldGraph_exact zero successor full empty rfl (fun _ => rfl)
    mixedCode PUnit.unit (mixedShape outer listLength inner) Subst.id empty
    (fun impossible => nomatch impossible) slot (ULift.up childIndex)
  change reads outer listLength inner slot childIndex ↔
    ∃ position, ((RecursiveSpaceRepresentation.codePresentation ordered mixedCode).coding
      (mixedShape outer listLength inner)).decode slot = some position ∧
        (ULift.up (Code.next mixedCode (mixedShape outer listLength inner) position) : ULift.{1} Nat) =
          ULift.up childIndex at graph
  refine graph.trans ?_
  constructor
  · rintro ⟨position, found, same⟩
    exact ⟨position, found, congrArg ULift.down same⟩
  · rintro ⟨position, found, same⟩
    exact ⟨position, found, congrArg (ULift.up : Nat → ULift.{1} Nat) same⟩

theorem first_direct : reads 7 3 2 0 7 := (reads_iff_lookup _ _ _ _ _).mpr (by decide +kernel)
theorem list_slot : reads 7 3 2 3 7 := (reads_iff_lookup _ _ _ _ _).mpr (by decide +kernel)
theorem vector_slot : reads 7 3 2 5 7 := (reads_iff_lookup _ _ _ _ _).mpr (by decide +kernel)
theorem following_direct : reads 7 3 2 6 2 := (reads_iff_lookup _ _ _ _ _).mpr (by decide +kernel)
theorem wrong_child_refused : ¬ reads 7 3 2 5 2 :=
  fun accepted => (by decide +kernel : ¬ (List.replicate 6 7 ++ [2])[5]? = some 2)
    ((reads_iff_lookup _ _ _ _ _).mp accepted)
theorem final_bound_refused (index : Nat) : ¬ reads 7 3 2 7 index := by
  intro accepted
  have found := (reads_iff_lookup _ _ _ _ _).mp accepted
  rw [show (List.replicate 6 7 ++ [2])[7]? = none from by decide +kernel] at found
  cases found
theorem empty_list_shift : reads 7 0 2 3 2 := (reads_iff_lookup _ _ _ _ _).mpr (by decide +kernel)
theorem empty_vector_shift : reads 7 3 0 4 0 := (reads_iff_lookup _ _ _ _ _).mpr (by decide +kernel)
theorem both_empty_shift : reads 7 0 0 1 0 := (reads_iff_lookup _ _ _ _ _).mpr (by decide +kernel)
theorem changed_source_index_refused : ¬ reads 8 3 2 5 7 :=
  fun accepted => (by decide +kernel : ¬ (List.replicate 6 8 ++ [2])[5]? = some 7)
    ((reads_iff_lookup _ _ _ _ _).mp accepted)

#print axioms generated_plan
#print axioms generated_result
#print axioms reads_source_position

end Mettapedia.GSLT.LanguageDef.IndexedContainerPositionTermsControls
