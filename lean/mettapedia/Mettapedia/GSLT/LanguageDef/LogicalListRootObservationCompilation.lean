import Mettapedia.GSLT.LanguageDef.RootResolvedBindingViewCompilation

/-!
# Logical-list observation through root and tag views

The raw finite carrier has arbitrary expression fields, including a variable or
an expression at field zero, and a private cons tag distinct from every symbol.
An injective envelope encoding reuses the checked triangular binding store and
its independently implemented complete substitution and root resolver.

The eager reference substitutes the whole value before distinguishing a private
cons, an authored symbolic cons (only in authored mode), and an ordinary flat
expression. The borrowed route resolves the outer root and, only for a
three-field expression, separately resolves its tag field. Original children
remain borrowed. The theorem compares the resulting layer after child forcing;
it does not identify raw stored binding entries.

The raw carrier includes symbols, strings, integers, variables, arbitrary
expressions and the private tag; other C grounded kinds are outside its scope.
This is a finite immutable-store observation law. It is not a complete list
unifier, a mutable builder or C representation refinement, a source parser or
lane-classification theorem, or an ownership/rollback theorem. A changed store
requires a changed view. Root-work exhaustion is a physical decline and falls
back to eager forcing rather than asserting mismatch.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.LogicalListRootObservationCompilation

open CompiledPlanOpenActivationViewCompilation
open DelayedSourceBindingCompilation
open TermObservationCoalgebra

open Mettapedia.Languages.MeTTa.TermViewCompilation
open RootResolvedBindingViewCompilation
  (RootStable Store View check force force_empty force_unbound
    openTermsToList_substitute resolveRoot? resolveRoot?_exact runPrefix substitution)

mutual
inductive Value where
  | symbol (name : List UInt8)
  | string (value : List UInt8)
  | integer (value : Int64)
  | variable (name : LogicVariable)
  | privateConsTag
  | expression (fields : Fields)
  deriving DecidableEq, Repr

inductive Fields where
  | nil
  | cons (head : Value) (tail : Fields)
  deriving DecidableEq, Repr
end

def expressionCode : List UInt8 := [0]
def privateTagCode : List UInt8 := [1]
def consName : List UInt8 := [99, 111, 110, 115]

mutual
def encode : Value → OpenTerm
  | .symbol name => .symbol name
  | .string value => .string value
  | .integer value => .integer value
  | .variable name => .variable name
  | .privateConsTag => .application privateTagCode .nil
  | .expression fields => .application expressionCode (encodeFields fields)

def encodeFields : Fields → OpenTerms
  | .nil => .nil
  | .cons head tail => .cons (encode head) (encodeFields tail)
end

mutual
def decode : OpenTerm → Option Value
  | .symbol name => some (.symbol name)
  | .string value => some (.string value)
  | .integer value => some (.integer value)
  | .variable name => some (.variable name)
  | .application head children =>
      if head = expressionCode then
        (decodeFields children).map Value.expression
      else if head = privateTagCode then
        match children with
        | .nil => some .privateConsTag
        | _ => none
      else none

def decodeFields : OpenTerms → Option Fields
  | .nil => some .nil
  | .cons head tail => do
      let value ← decode head
      let values ← decodeFields tail
      pure (.cons value values)
end

mutual
@[simp] theorem decode_encode (value : Value) : decode (encode value) = some value := by
  cases value with
  | symbol name | string value | integer value | «variable» name => rfl
  | privateConsTag => decide
  | expression fields =>
      simp [encode, decode, decodeFields_encodeFields fields]

@[simp] theorem decodeFields_encodeFields (fields : Fields) :
    decodeFields (encodeFields fields) = some fields := by
  cases fields with
  | nil => rfl
  | cons head tail =>
      simp [encodeFields, decodeFields, decode_encode head, decodeFields_encodeFields tail]
end

theorem encode_injective : Function.Injective encode := by
  intro left right same
  have decoded := congrArg decode same
  simpa only [decode_encode, Option.some.injEq] using decoded

def Fields.toList : Fields → List Value
  | .nil => []
  | .cons head tail => head :: tail.toList

theorem encodeFields_toList (fields : Fields) :
    openTermsToList (encodeFields fields) = fields.toList.map encode := by
  cases fields with
  | nil => rfl
  | cons head tail =>
      simp [encodeFields, openTermsToList, Fields.toList, encodeFields_toList tail]

abbrev Substitution := LogicVariable → Option Value
abbrev RawStore := List (LogicVariable × Value)

mutual
def substitute (assignment : Substitution) : Value → Value
  | .variable name => (assignment name).getD (.variable name)
  | .expression fields => .expression (substituteFields assignment fields)
  | value => value

def substituteFields (assignment : Substitution) : Fields → Fields
  | .nil => .nil
  | .cons head tail => .cons (substitute assignment head) (substituteFields assignment tail)
end

def assignment : RawStore → Substitution
  | [] => fun _ => none
  | (key, value) :: rest => fun name =>
      if name = key then some (substitute (assignment rest) value)
      else assignment rest name

def forceRaw (store : RawStore) (value : Value) : Value := substitute (assignment store) value

def encodeStore (store : RawStore) : Store :=
  store.map fun (name, value) => (name, encode value)

mutual
theorem encode_substitute (source : Substitution) (value : Value) :
    encode (substitute source value) =
      substituteOpen (fun name => (source name).map encode) (encode value) := by
  cases value with
  | symbol name | string value | integer value | privateConsTag => rfl
  | «variable» name =>
      simp only [substitute, encode, substituteOpen]
      cases source name <;> rfl
  | expression fields =>
      simp only [substitute, encode, substituteOpen]
      exact congrArg (OpenTerm.application expressionCode) (encode_substituteFields source fields)

theorem encode_substituteFields (source : Substitution) (fields : Fields) :
    encodeFields (substituteFields source fields) =
      substituteOpenTerms (fun name => (source name).map encode) (encodeFields fields) := by
  cases fields with
  | nil => rfl
  | cons head tail =>
      simp [substituteFields, encodeFields, substituteOpenTerms,
        encode_substitute source head, encode_substituteFields source tail]
end

theorem encode_assignment (store : RawStore) :
    substitution (encodeStore store) = fun name => (assignment store name).map encode := by
  induction store with
  | nil => rfl
  | cons binding rest inductionHypothesis =>
      rcases binding with ⟨key, value⟩
      funext name
      simp only [encodeStore, List.map_cons, substitution, assignment]
      split
      · rw [show substitution (List.map (fun (name, value) => (name, encode value)) rest) =
          (fun name => (assignment rest name).map encode) from inductionHypothesis]
        simp only [Option.map_some]
        exact congrArg some (encode_substitute (assignment rest) value).symm
      · exact congrFun inductionHypothesis name

theorem encode_force (store : RawStore) (value : Value) :
    encode (forceRaw store value) = force (encodeStore store) (encode value) := by
  simp only [forceRaw, force, encode_assignment]
  exact encode_substitute (assignment store) value

universe u v w

/-- Cons recognition does not inspect or normalize its two child values.
The flat case retains every occurrence, including field zero. -/
inductive Layer (Child : Type u) where
  | symbol (name : List UInt8)
  | string (value : List UInt8)
  | integer (value : Int64)
  | variable (name : LogicVariable)
  | privateConsTag
  | cons (head tail : Child)
  | flat (fields : List Child)
  | invalidEncoding
  deriving DecidableEq, Repr

def Layer.map {Child : Type u} {Next : Type v} (function : Child → Next) :
    Layer Child → Layer Next
  | .symbol name => .symbol name
  | .string value => .string value
  | .integer value => .integer value
  | .variable name => .variable name
  | .privateConsTag => .privateConsTag
  | .cons head tail => .cons (function head) (function tail)
  | .flat fields => .flat (fields.map function)
  | .invalidEncoding => .invalidEncoding

@[simp] theorem Layer.map_id {Child : Type u} (layer : Layer Child) :
    layer.map id = layer := by
  cases layer <;> simp [Layer.map]

@[simp] theorem Layer.map_comp {Child : Type u} {Next : Type v} {Last : Type w}
    (first : Child → Next) (second : Next → Last) (layer : Layer Child) :
    (layer.map first).map second = layer.map (second ∘ first) := by
  cases layer <;> simp [Layer.map, Function.comp_def]

def isConsTag (authored : Bool) : Value → Bool
  | .privateConsTag => true
  | .symbol name => authored && (name == consName)
  | _ => false

/-- Reference observation on already substituted raw values. -/
def out (authored : Bool) : Value → Layer Value
  | .symbol name => .symbol name
  | .string value => .string value
  | .integer value => .integer value
  | .variable name => .variable name
  | .privateConsTag => .privateConsTag
  | .expression fields =>
      match fields with
      | .cons tag (.cons head (.cons tail .nil)) =>
          if isConsTag authored tag then .cons head tail else .flat fields.toList
      | _ => .flat fields.toList

def encodedIsConsTag (authored : Bool) : OpenTerm → Bool
  | .symbol name => authored && (name == consName)
  | .application name .nil => name == privateTagCode
  | _ => false

def encodedFieldsOut (authored : Bool) (fields : OpenTerms) : Layer OpenTerm :=
  match fields with
  | .cons tag (.cons head (.cons tail .nil)) =>
      if encodedIsConsTag authored tag then .cons head tail
      else .flat (openTermsToList fields)
  | _ => .flat (openTermsToList fields)

def encodedOut (authored : Bool) : OpenTerm → Layer OpenTerm
  | .symbol name => .symbol name
  | .string value => .string value
  | .integer value => .integer value
  | .variable name => .variable name
  | .application name fields =>
      if name = expressionCode then encodedFieldsOut authored fields
      else if name = privateTagCode then
        match fields with
        | .nil => .privateConsTag
        | _ => .invalidEncoding
      else .invalidEncoding

theorem encodedIsConsTag_encode (authored : Bool) (value : Value) :
    encodedIsConsTag authored (encode value) = isConsTag authored value := by
  cases value <;> simp [encode, encodedIsConsTag, isConsTag, expressionCode, privateTagCode]
  rename_i fields
  cases fields <;> rfl

theorem encodedFieldsOut_encodeFields (authored : Bool) (fields : Fields) :
    encodedFieldsOut authored (encodeFields fields) =
      (out authored (.expression fields)).map encode := by
  cases fields with
  | nil => rfl
  | cons tag rest =>
      cases rest with
      | nil => rfl
      | cons head rest =>
          cases rest with
          | nil => rfl
          | cons tail rest =>
              cases rest with
              | nil =>
                  simp only [encodeFields, encodedFieldsOut, out, encodedIsConsTag_encode]
                  cases isConsTag authored tag <;> rfl
              | cons next rest =>
                  simp [encodeFields, encodedFieldsOut, out, Layer.map,
                    openTermsToList, Fields.toList, encodeFields_toList]

theorem encodedOut_encode (authored : Bool) (value : Value) :
    encodedOut authored (encode value) = (out authored value).map encode := by
  cases value with
  | symbol name | string value | integer value | «variable» name => rfl
  | privateConsTag => rfl
  | expression fields =>
      simp only [encode, encodedOut]
      exact encodedFieldsOut_encodeFields authored fields

def peekFields? (store : Store) (authored : Bool) (tagBudget : Nat)
    (fields : OpenTerms) : Option (Layer OpenTerm) :=
  match fields with
  | .cons tag (.cons head (.cons tail .nil)) => do
      let resolved ← resolveRoot? store tagBudget tag
      pure (if encodedIsConsTag authored resolved then .cons head tail
        else .flat (openTermsToList fields))
  | _ => some (.flat (openTermsToList fields))

def peekRoot? (store : Store) (authored : Bool) (tagBudget : Nat) :
    OpenTerm → Option (Layer OpenTerm)
  | .symbol name => some (.symbol name)
  | .string value => some (.string value)
  | .integer value => some (.integer value)
  | .variable name => some (.variable name)
  | .application name fields =>
      if name = expressionCode then peekFields? store authored tagBudget fields
      else if name = privateTagCode then
        match fields with
        | .nil => some .privateConsTag
        | _ => some .invalidEncoding
      else some .invalidEncoding

def borrowed? (store : Store) (authored : Bool) (rootBudget tagBudget : Nat)
    (source : OpenTerm) : Option (Layer OpenTerm) := do
  let root ← resolveRoot? store rootBudget source
  peekRoot? store authored tagBudget root

/-! The proofs below derive demanded-tag stability from the executable store
check and root resolver, including tags obtained through variable aliases. -/

theorem stable_tag (store : Store) (authored : Bool) (value : OpenTerm)
    (stable : RootStable store value) :
    encodedIsConsTag authored (force store value) = encodedIsConsTag authored value := by
  cases value with
  | symbol name | string value | integer value => rfl
  | «variable» name => rw [force_unbound store name stable]
  | application name fields =>
      cases fields <;> rfl

theorem resolved_tag (store : Store) (admitted : check store = true)
    (authored : Bool) (budget : Nat) (source resolved : OpenTerm)
    (completed : resolveRoot? store budget source = some resolved) :
    encodedIsConsTag authored resolved = encodedIsConsTag authored (force store source) := by
  obtain ⟨same, stable⟩ := resolveRoot?_exact store admitted budget source resolved completed
  rw [← stable_tag store authored resolved stable, same]

theorem flat_map_force (store : Store) (fields : OpenTerms) :
    (Layer.flat (openTermsToList fields)).map (force store) =
      Layer.flat (openTermsToList (substituteOpenTerms (substitution store) fields)) := by
  exact congrArg Layer.flat (openTermsToList_substitute store fields).symm

theorem peekFields?_exact (store : Store) (admitted : check store = true)
    (authored : Bool) (tagBudget : Nat) (fields : OpenTerms) (layer : Layer OpenTerm)
    (completed : peekFields? store authored tagBudget fields = some layer) :
    layer.map (force store) =
      encodedFieldsOut authored (substituteOpenTerms (substitution store) fields) := by
  cases fields with
  | nil =>
      simp only [peekFields?, Option.some.injEq] at completed
      subst layer
      rfl
  | cons tag rest =>
      cases rest with
      | nil =>
          simp only [peekFields?, Option.some.injEq] at completed
          subst layer
          exact flat_map_force store _
      | cons head rest =>
          cases rest with
          | nil =>
              simp only [peekFields?, Option.some.injEq] at completed
              subst layer
              exact flat_map_force store _
          | cons tail rest =>
              cases rest with
              | nil =>
                  simp only [peekFields?] at completed
                  cases tagSeen : resolveRoot? store tagBudget tag with
                  | none => simp [tagSeen] at completed
                  | some resolved =>
                      have tagExact := resolved_tag store admitted authored tagBudget tag resolved tagSeen
                      simp only [tagSeen] at completed
                      have selected :
                          (if encodedIsConsTag authored resolved then Layer.cons head tail
                            else Layer.flat (openTermsToList (.cons tag (.cons head (.cons tail .nil))))) =
                          layer := Option.some.inj completed
                      rw [tagExact] at selected
                      by_cases isTag : encodedIsConsTag authored (force store tag) = true
                      · rw [if_pos isTag] at selected
                        subst layer
                        simp only [force] at isTag
                        simp [Layer.map, encodedFieldsOut, substituteOpenTerms, force, isTag]
                      · rw [if_neg isTag] at selected
                        subst layer
                        simp only [force] at isTag
                        simpa only [encodedFieldsOut, substituteOpenTerms, if_neg isTag]
                          using flat_map_force store (.cons tag (.cons head (.cons tail .nil)))
              | cons next rest =>
                  simp only [peekFields?, Option.some.injEq] at completed
                  subst layer
                  exact flat_map_force store _

theorem peekRoot?_exact (store : Store) (admitted : check store = true)
    (authored : Bool) (tagBudget : Nat) (root : OpenTerm) (layer : Layer OpenTerm)
    (stable : RootStable store root)
    (completed : peekRoot? store authored tagBudget root = some layer) :
    layer.map (force store) = encodedOut authored (force store root) := by
  cases root with
  | symbol name | string value | integer value =>
      simp only [peekRoot?, Option.some.injEq] at completed
      subst layer
      rfl
  | «variable» name =>
      simp only [peekRoot?, Option.some.injEq] at completed
      subst layer
      rw [force_unbound store name stable]
      rfl
  | application name fields =>
      by_cases expression : name = expressionCode
      · subst name
        change peekFields? store authored tagBudget fields = some layer at completed
        change layer.map (force store) =
          encodedFieldsOut authored
            (substituteOpenTerms (substitution store) fields)
        exact peekFields?_exact store admitted authored tagBudget fields layer completed
      · by_cases privateTag : name = privateTagCode
        · subst name
          cases fields with
          | nil =>
              have selected : Layer.privateConsTag = layer := Option.some.inj completed
              subst layer
              rfl
          | cons head tail =>
              have selected : Layer.invalidEncoding = layer := Option.some.inj completed
              subst layer
              rfl
        · simp only [peekRoot?, if_neg expression, if_neg privateTag,
            Option.some.injEq] at completed
          subst layer
          simp only [force, substituteOpen, encodedOut,
            if_neg expression, if_neg privateTag, Layer.map]

/-- Every completed borrowed observation agrees with eager substitution.
Neither a known tag nor a known non-tag is assumed: both follow from the
actual successful outer and tag-root lookups in the checked store. -/
theorem borrowed?_exact (store : Store) (admitted : check store = true)
    (authored : Bool) (rootBudget tagBudget : Nat) (source : OpenTerm)
    (layer : Layer OpenTerm)
    (completed : borrowed? store authored rootBudget tagBudget source = some layer) :
    layer.map (force store) = encodedOut authored (force store source) := by
  simp only [borrowed?] at completed
  cases rootSeen : resolveRoot? store rootBudget source with
  | none => simp [rootSeen] at completed
  | some root =>
      simp only [rootSeen] at completed
      obtain ⟨same, stable⟩ := resolveRoot?_exact store admitted rootBudget source root rootSeen
      rw [← same]
      exact peekRoot?_exact store admitted authored tagBudget root layer stable completed

/-- The scoped raw carrier supplies actual arbitrary expression heads and a
distinct private tag; its complete substitution is independent of the encoded
store interpreter. This closes the observation theorem at that carrier. -/
theorem borrowed?_raw_exact (store : RawStore)
    (admitted : check (encodeStore store) = true)
    (authored : Bool) (rootBudget tagBudget : Nat) (source : Value)
    (layer : Layer OpenTerm)
    (completed : borrowed? (encodeStore store) authored rootBudget tagBudget (encode source) = some layer) :
    layer.map (force (encodeStore store)) = (out authored (forceRaw store source)).map encode := by
  have exactLayer := borrowed?_exact (encodeStore store) admitted authored
    rootBudget tagBudget (encode source) layer completed
  rw [← encode_force store source, encodedOut_encode] at exactLayer
  exact exactLayer

/-- The fallback affects work and allocation, not the observed layer. Every
borrowed child retains the same immutable checked authority. -/
def outView (authored : Bool) (rootBudget tagBudget : Nat) (view : View) : Layer View :=
  match borrowed? view.store authored rootBudget tagBudget view.source with
  | some layer => layer.map fun child => { view with source := child }
  | none => (encodedOut authored view.force).map View.eager

theorem outView_exact (authored : Bool) (rootBudget tagBudget : Nat) (view : View) :
    (outView authored rootBudget tagBudget view).map View.force =
      encodedOut authored view.force := by
  unfold outView
  cases completed : borrowed? view.store authored rootBudget tagBudget view.source with
  | none =>
      simp only [Layer.map_comp, Function.comp_def, View.force, View.eager,
        force_empty]
      exact Layer.map_id _
  | some layer =>
      simp only [Layer.map_comp]
      exact borrowed?_exact view.store view.admitted authored rootBudget tagBudget
        view.source layer completed

/-- Total observation correspondence for a raw value and an actually checked
encoded store, at every pair of physical root allowances. No successful
lookup or pre-established tag decision is required as a premise. -/
theorem outView_raw_exact (store : RawStore)
    (admitted : check (encodeStore store) = true)
    (authored : Bool) (rootBudget tagBudget : Nat) (source : Value) :
    (outView authored rootBudget tagBudget
      ⟨encodeStore store, admitted, encode source⟩).map View.force =
        (out authored (forceRaw store source)).map encode := by
  rw [outView_exact]
  change encodedOut authored (force (encodeStore store) (encode source)) = _
  rw [← encode_force store source, encodedOut_encode]

namespace Canaries

private def op : LogicVariable := ⟨4, 0⟩
private def aliasSlot : LogicVariable := ⟨4, 1⟩
private def tailSlot : LogicVariable := ⟨4, 2⟩
private def otherOp : LogicVariable := ⟨5, 0⟩
private def unit : Value := .expression .nil
private def triple (first second third : Value) : Value :=
  .expression (.cons first (.cons second (.cons third .nil)))
private def privateCons (head tail : Value) : Value := triple .privateConsTag head tail
private def symbolicCons (head tail : Value) : Value := triple (.symbol consName) head tail
private def tagStore : RawStore := [(op, .variable aliasSlot), (aliasSlot, .privateConsTag)]
private def symbolicTagStore : RawStore := [(op, .symbol consName)]
private def tagSource : Value := triple (.variable op) (.integer 7) (.variable tailSlot)

theorem private_tag_and_symbol_have_distinct_encodings :
    encode .privateConsTag ≠ encode (.symbol privateTagCode) ∧
      encode .privateConsTag ≠ encode unit := by decide

theorem arbitrary_expression_heads_round_trip :
    decode (encode (triple (privateCons (.integer 1) unit) (.variable op) unit)) =
      some (triple (privateCons (.integer 1) unit) (.variable op) unit) :=
  decode_encode _

theorem aliases_to_private_tag_are_admitted :
    check (encodeStore tagStore) = true := by decide

/-- The alias path is demanded; neither the head value nor the open tail is
substituted to perform this observation. -/
theorem borrowed_alias_tag_preserves_open_children :
    borrowed? (encodeStore tagStore) false 1 3 (encode tagSource) =
      some (.cons (.integer 7) (.variable tailSlot)) := by decide

theorem eager_alias_tag_has_the_same_logical_layer :
    out false (forceRaw tagStore tagSource) = .cons (.integer 7) (.variable tailSlot) := by decide

theorem symbolic_cons_is_mode_scoped :
    out true (symbolicCons (.integer 7) unit) = .cons (.integer 7) unit ∧
      out false (symbolicCons (.integer 7) unit) =
        .flat [.symbol consName, .integer 7, unit] := by decide

theorem symbolic_tag_reached_through_binding_is_mode_scoped :
    borrowed? (encodeStore symbolicTagStore) true 1 2 (encode tagSource) =
      some (.cons (.integer 7) (.variable tailSlot)) ∧
      borrowed? (encodeStore symbolicTagStore) false 1 2 (encode tagSource) =
        some (.flat [.variable op, .integer 7, .variable tailSlot]) := by decide

theorem private_tag_is_recognized_in_both_modes :
    out true (privateCons (.integer 7) unit) = .cons (.integer 7) unit ∧
      out false (privateCons (.integer 7) unit) = .cons (.integer 7) unit := by decide

/-- Resolving an expression-valued head does not turn that entire expression
into its own first field. The outer value remains an ordinary flat list. -/
theorem expression_valued_head_is_not_a_tag :
    borrowed? (encodeStore tagStore) false 1 1
      (encode (triple tagSource (.integer 8) unit)) =
        some (.flat [encode tagSource, .integer 8, encode unit]) := by decide

theorem exact_arity_is_required :
    borrowed? [] false 1 0
      (encode (.expression (.cons .privateConsTag (.cons (.integer 7) .nil)))) =
        some (.flat [encode .privateConsTag, .integer 7]) := by decide

private def irrelevant : Nat → Value
  | 0 => .variable tailSlot
  | depth + 1 => .expression (.cons (.symbol [9]) (.cons (irrelevant depth) .nil))

theorem an_unrelated_subtree_is_returned_borrowed :
    borrowed? (encodeStore tagStore) false 1 3
      (encode (triple (.variable op) (irrelevant 32) (.variable tailSlot))) =
        some (.cons (encode (irrelevant 32)) (.variable tailSlot)) := by decide

theorem repeated_children_retain_one_identity :
    borrowed? [] false 1 1
      (encode (privateCons (.variable tailSlot) (.variable tailSlot))) =
        some (.cons (.variable tailSlot) (.variable tailSlot)) := by decide

theorem other_generation_is_unbound_and_not_a_tag :
    borrowed? (encodeStore tagStore) false 1 1
      (encode (triple (.variable otherOp) (.integer 7) unit)) =
        some (.flat [.variable otherOp, .integer 7, encode unit]) := by decide

theorem insufficient_outer_or_tag_allowance_declines :
    borrowed? (encodeStore tagStore) false 0 3 (encode tagSource) = none ∧
      borrowed? (encodeStore tagStore) false 1 1 (encode tagSource) = none := by decide

private def tagView : View :=
  ⟨encodeStore tagStore, aliases_to_private_tag_are_admitted, encode tagSource⟩

theorem declined_tag_observation_falls_back_exactly :
    (outView false 1 0 tagView).map View.force =
      .cons (.integer 7) (.variable tailSlot) := by
  rw [outView_exact]
  decide

/-- An unbound field zero is not a tag in the current store. That conclusion
must not be retained after an extension that binds it to the private tag. -/
theorem stale_authority_changes_cons_classification :
    borrowed? [] false 1 1 (encode tagSource) =
      some (.flat [.variable op, .integer 7, .variable tailSlot]) ∧
      borrowed? (encodeStore [(op, .privateConsTag)]) false 1 2 (encode tagSource) =
        some (.cons (.integer 7) (.variable tailSlot)) := by decide

theorem structural_and_alias_cycles_are_not_admitted :
    check
      (encodeStore [(op, privateCons (.integer 7) (.variable op))]) = false ∧
    check
      (encodeStore [(op, .variable aliasSlot), (aliasSlot, .variable op)]) = false := by decide

/-- A finite diagnostic for the complete logical list length. Exhaustion,
an unbound tail, and a non-list tail return no length. It is not a unifier. -/
private def listLength? (authored : Bool) : Nat → Value → Option Nat
  | 0, _ => none
  | fuel + 1, value =>
      match out authored value with
      | .cons _ tail => (listLength? authored fuel tail).map Nat.succ
      | .flat fields => some fields.length
      | _ => none

private def privateOne : Value := privateCons (.integer 7) unit
private def rawThree : Value := triple (.variable op) (.integer 7) unit

/-- The independent first-order unifier accepts by capturing the private tag,
yet these values have unequal logical list lengths. Structural success alone
is therefore not sufficient evidence for logical-list matching. -/
theorem raw_success_does_not_certify_logical_list_compatibility :
    (runPrefix 3 20
      [(View.eager (encode privateOne),
        View.eager (encode rawThree))]).stop = .success ∧
      listLength? false 3 privateOne = some 1 ∧
      listLength? false 3 rawThree = some 3 := by decide

end Canaries

#print axioms encode_injective
#print axioms encode_force
#print axioms resolved_tag
#print axioms borrowed?_exact
#print axioms borrowed?_raw_exact
#print axioms outView_exact
#print axioms outView_raw_exact
#print axioms Canaries.raw_success_does_not_certify_logical_list_compatibility

end Mettapedia.GSLT.LanguageDef.LogicalListRootObservationCompilation
