import Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLowering
import Mettapedia.TypeTheory.IndexedPositiveContainer

/-!
# Textual lowering for a length-indexed Vector of recursive children

This is the source-side vertical slice for the richer indexed-container
registry.  It accepts an `Answer` field, direct recursive fields, and
`Vector n VectorTree` fields whose length name resolves to an earlier `Nat`
binder.  The resolved code erases to `IndexedPositiveContainer.Code`, keeping
the Vector output expression distinct from the recursive child-family index.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering

open InductiveSyntax
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.IndexedPositiveContainer.VectorControl

abbrev I := VectorControl.interface
abbrev DataSort := VectorControl.DataSort
abbrev LengthExpr := VectorControl.LengthExpr

/-- A source scope records all data-binder names in its type.  Freshness is
part of scope formation, so named length references have a two-sided codec
rather than a shadowing-sensitive partial inverse. -/
inductive Scope : List DataSort → List String → Type where
  | nil : Scope [] []
  | bind {context names} (name : String) (sort : DataSort)
      (prior : Scope context names) (fresh : name ∉ names) :
      Scope (sort :: context) (name :: names)

def Scope.lookupLength : {context : List DataSort} → {names : List String} →
    Scope context names → String → Option (LengthExpr context)
  | _, _, .nil, _ => none
  | _, _, .bind bound .length prior _, name =>
      if name = bound then some .here
      else (prior.lookupLength name).map .there
  | _, _, .bind _ .payload prior _, name =>
      (prior.lookupLength name).map .there

def Scope.quoteLength : {context : List DataSort} → {names : List String} →
    Scope context names → LengthExpr context → String
  | _, _, .bind name .length _ _, .here => name
  | _, _, .bind _ .length prior _, .there expression => prior.quoteLength expression
  | _, _, .bind _ .payload prior _, .there expression => prior.quoteLength expression

theorem Scope.quoteLength_mem {context : List DataSort} {names : List String}
    (scope : Scope context names) (expression : LengthExpr context) :
    scope.quoteLength expression ∈ names := by
  induction scope with
  | nil => cases expression
  | @bind context names name sort prior fresh ih =>
      cases sort with
      | payload =>
          cases expression with
          | there expression => exact List.mem_cons_of_mem name (ih expression)
      | length =>
          cases expression with
          | here => exact List.mem_cons_self
          | there expression => exact List.mem_cons_of_mem name (ih expression)

@[simp] theorem Scope.lookup_quoteLength {context : List DataSort}
    {names : List String} (scope : Scope context names)
    (expression : LengthExpr context) :
    scope.lookupLength (scope.quoteLength expression) = some expression := by
  induction scope with
  | nil => cases expression
  | @bind context names name sort prior fresh ih =>
      cases sort with
      | payload =>
          cases expression with
          | there expression => simp [Scope.quoteLength, Scope.lookupLength, ih expression]
      | length =>
          cases expression with
          | here => simp [Scope.quoteLength, Scope.lookupLength]
          | there expression =>
              have different : prior.quoteLength expression ≠ name := by
                intro same
                apply fresh
                rw [← same]
                exact prior.quoteLength_mem expression
              simp [Scope.quoteLength, Scope.lookupLength, different, ih expression]

theorem Scope.quote_lookupLength {context : List DataSort} {names : List String}
    (scope : Scope context names) (name : String) (expression : LengthExpr context)
    (found : scope.lookupLength name = some expression) :
    scope.quoteLength expression = name := by
  induction scope generalizing name with
  | nil => simp [Scope.lookupLength] at found
  | @bind context names bound sort prior fresh ih =>
      cases sort with
      | payload =>
          simp only [Scope.lookupLength, Option.map_eq_some_iff] at found
          obtain ⟨priorExpression, priorFound, rfl⟩ := found
          exact ih name priorExpression priorFound
      | length =>
          by_cases sameName : name = bound
          · subst name
            simp [Scope.lookupLength] at found
            subst expression
            rfl
          · simp only [Scope.lookupLength, sameName, if_false,
              Option.map_eq_some_iff] at found
            obtain ⟨priorExpression, priorFound, rfl⟩ := found
            exact ih name priorExpression priorFound

def payloadTerm : Term := .name "Answer"
def lengthTerm : Term := .name "Nat"
def treeTerm : Term := .name "VectorTree"
def vectorTerm (lengthName : String) : Term :=
  .app (.app (.name "Vector") (.name lengthName)) treeTerm

@[simp] theorem payloadTerm_ne_lengthTerm : payloadTerm ≠ lengthTerm := by decide
@[simp] theorem payloadTerm_ne_treeTerm : payloadTerm ≠ treeTerm := by decide
@[simp] theorem lengthTerm_ne_payloadTerm : lengthTerm ≠ payloadTerm := by decide
@[simp] theorem lengthTerm_ne_treeTerm : lengthTerm ≠ treeTerm := by decide
@[simp] theorem treeTerm_ne_payloadTerm : treeTerm ≠ payloadTerm := by decide
@[simp] theorem treeTerm_ne_lengthTerm : treeTerm ≠ lengthTerm := by decide

inductive FieldMeaning (context : List DataSort) where
  | data (sort : DataSort)
  | recursive
  | vector (length : LengthExpr context)

def classify {context : List DataSort} {names : List String}
    (scope : Scope context names) (source : Term) :
    Option (FieldMeaning context) :=
  if source = payloadTerm then some (.data .payload)
  else if source = lengthTerm then some (.data .length)
  else if source = treeTerm then some .recursive
  else match source with
    | .app (.app (.name "Vector") (.name lengthName)) element =>
        if element = treeTerm then (scope.lookupLength lengthName).map .vector else none
    | _ => none

def quoteField {context : List DataSort} {names : List String}
    (scope : Scope context names) :
    FieldMeaning context → Term
  | .data .payload => payloadTerm
  | .data .length => lengthTerm
  | .recursive => treeTerm
  | .vector length => vectorTerm (scope.quoteLength length)

@[simp] theorem classify_quote {context : List DataSort} {names : List String}
    (scope : Scope context names)
    (meaning : FieldMeaning context) :
    classify scope (quoteField scope meaning) = some meaning := by
  cases meaning with
  | data sort => cases sort <;> simp [classify, quoteField]
  | recursive => simp [classify, quoteField]
  | vector length =>
      simp [classify, quoteField, vectorTerm, payloadTerm, lengthTerm, treeTerm,
        Scope.lookup_quoteLength]

@[simp] theorem classify_treeTerm {context : List DataSort} {names : List String}
    (scope : Scope context names) :
    classify scope treeTerm = some .recursive := by
  simpa [quoteField] using classify_quote scope (.recursive : FieldMeaning context)

@[simp] theorem classify_vectorTerm {context : List DataSort} {names : List String}
    (scope : Scope context names) (length : LengthExpr context) :
    classify scope (vectorTerm (scope.quoteLength length)) = some (.vector length) := by
  simpa [quoteField] using classify_quote scope (.vector length)

theorem quote_classify {context : List DataSort} {names : List String}
    (scope : Scope context names)
    (source : Term) (meaning : FieldMeaning context)
    (accepted : classify scope source = some meaning) :
    quoteField scope meaning = source := by
  by_cases payload : source = payloadTerm
  · have same : meaning = .data .payload := by
      simpa [classify, payload] using accepted.symm
    subst meaning
    exact payload.symm
  · by_cases length : source = lengthTerm
    · have same : meaning = .data .length := by
        simpa [classify, payload, length] using accepted.symm
      subst meaning
      simpa [quoteField] using length.symm
    · by_cases recursive : source = treeTerm
      · have same : meaning = .recursive := by
          simpa [classify, payload, length, recursive] using accepted.symm
        subst meaning
        simpa [quoteField] using recursive.symm
      · cases source with
        | name identifier => simp [classify, payload, length, recursive] at accepted
        | arrow domain codomain => simp [classify, payload, length, recursive] at accepted
        | pi binder domain codomain => simp [classify, payload, length, recursive] at accepted
        | project owner field record => simp [classify, payload, length, recursive] at accepted
        | app function element =>
            cases function with
            | name identifier => simp [classify, payload, length, recursive] at accepted
            | arrow domain codomain => simp [classify, payload, length, recursive] at accepted
            | pi binder domain codomain => simp [classify, payload, length, recursive] at accepted
            | project owner field record => simp [classify, payload, length, recursive] at accepted
            | app vectorHead lengthSource =>
                cases vectorHead <;> cases lengthSource <;>
                  simp [classify, payload, length, recursive] at accepted
                rename_i vectorName lengthName
                by_cases vectorEq : vectorName = "Vector"
                · subst vectorName
                  by_cases elementEq : element = treeTerm
                  · cases found : scope.lookupLength lengthName with
                    | none => simp [elementEq, found] at accepted
                    | some output =>
                        have same : meaning = .vector output := by
                          simpa [classify, payload, length, recursive,
                            elementEq, found] using accepted.symm
                        subst meaning
                        rw [quoteField, vectorTerm,
                          Scope.quote_lookupLength scope lengthName output found,
                          elementEq]
                  · simp [elementEq] at accepted
                · simp [vectorEq] at accepted

inductive Code : List DataSort → List String → Type where
  | result {context names} : Code context names
  | data {context names} (fieldName : String) (sort : DataSort)
      (fresh : fieldName ∉ names) :
      Code (sort :: context) (fieldName :: names) → Code context names
  | recursive {context names} (fieldName : String) :
      Code context names → Code context names
  | vector {context names} (fieldName : String) (length : LengthExpr context) :
      Code context names → Code context names

def Code.erase : {context : List DataSort} → {names : List String} →
    Code context names →
    IndexedPositiveContainer.Code I VectorControl.registry 0 context
  | _, _, .result => .result ()
  | _, _, .data _ sort _ rest => .data sort rest.erase
  | _, _, .recursive _ rest => .recursive () rest.erase
  | _, _, .vector _ length rest =>
      .nested "Vector" VectorControl.entry (by simp [VectorControl.registry])
        length () rest.erase

def Code.quote : {context : List DataSort} → {names : List String} →
    Scope context names → Code context names →
    List Binder × Term
  | _, _, _scope, .result => ([], treeTerm)
  | _, _, scope, .data name sort fresh rest =>
      let quoted := rest.quote (.bind name sort scope fresh)
      (⟨name, quoteField scope (.data sort)⟩ :: quoted.1, quoted.2)
  | _, _, scope, .recursive name rest =>
      let quoted := rest.quote scope
      (⟨name, treeTerm⟩ :: quoted.1, quoted.2)
  | _, _, scope, .vector name length rest =>
      let quoted := rest.quote scope
      (⟨name, vectorTerm (scope.quoteLength length)⟩ :: quoted.1, quoted.2)

def lowerCode : {context : List DataSort} → {names : List String} →
    Scope context names → Term → List Binder → Option (Code context names)
  | _, _, _, result, [] => if result = treeTerm then some .result else none
  | _, names, scope, result, field :: rest =>
      match classify scope field.type with
      | none => none
      | some (.data sort) =>
          if fresh : field.name ∉ names then
            (lowerCode (.bind field.name sort scope fresh) result rest).map
              (.data field.name sort fresh)
          else none
      | some .recursive =>
          (lowerCode scope result rest).map (.recursive field.name)
      | some (.vector length) =>
          (lowerCode scope result rest).map (.vector field.name length)

@[simp] theorem lowerCode_quote : {context : List DataSort} →
    {names : List String} → (scope : Scope context names) →
    (code : Code context names) →
      lowerCode scope (code.quote scope).2 (code.quote scope).1 = some code
  | _, _, scope, .result => by simp [Code.quote, lowerCode]
  | _, _, scope, .data name sort fresh rest => by
      simp [Code.quote, lowerCode, classify_quote, fresh, lowerCode_quote]
  | _, _, scope, .recursive name rest => by
      simp [Code.quote, lowerCode, lowerCode_quote]
  | _, _, scope, .vector name length rest => by
      simp [Code.quote, lowerCode, lowerCode_quote]

theorem quote_lowerCode {context : List DataSort} {names : List String}
    (scope : Scope context names) :
    ∀ (fields : List Binder) (result : Term) (code : Code context names),
      lowerCode scope result fields = some code → code.quote scope = (fields, result) := by
  intro fields
  induction fields generalizing context names with
  | nil =>
      intro result code accepted
      by_cases same : result = treeTerm
      · have codeEq : Code.result = code := by simpa [lowerCode, same] using accepted
        subst code
        simp [Code.quote, same]
      · simp [lowerCode, same] at accepted
  | cons field rest ih =>
      cases field with
      | mk fieldName fieldType =>
          intro result code accepted
          cases classified : classify scope fieldType with
          | none => simp [lowerCode, classified] at accepted
          | some meaning =>
              cases meaning with
              | data sort =>
                  by_cases fresh : fieldName ∉ names
                  · cases lowered : lowerCode (.bind fieldName sort scope fresh)
                        result rest with
                    | none => simp [lowerCode, classified, fresh, lowered] at accepted
                    | some tail =>
                        have same : Code.data fieldName sort fresh tail = code := by
                          simpa [lowerCode, classified, fresh, lowered] using accepted
                        subst code
                        have quoted := ih (.bind fieldName sort scope fresh)
                          result tail lowered
                        have typeQuote : quoteField scope (.data sort) = fieldType :=
                          quote_classify scope fieldType (.data sort) classified
                        simp [Code.quote, typeQuote, quoted]
                  · simp [lowerCode, classified, fresh] at accepted
              | recursive =>
                  cases lowered : lowerCode scope result rest with
                  | none => simp [lowerCode, classified, lowered] at accepted
                  | some tail =>
                      have same : Code.recursive fieldName tail = code := by
                        simpa [lowerCode, classified, lowered] using accepted
                      subst code
                      have quoted := ih scope result tail lowered
                      have typeQuote : quoteField scope .recursive = fieldType :=
                        quote_classify scope fieldType .recursive classified
                      have treeType : treeTerm = fieldType := by
                        simpa [quoteField] using typeQuote
                      simp [Code.quote, treeType, quoted]
              | vector length =>
                  cases lowered : lowerCode scope result rest with
                  | none => simp [lowerCode, classified, lowered] at accepted
                  | some tail =>
                      have same : Code.vector fieldName length tail = code := by
                        simpa [lowerCode, classified, lowered] using accepted
                      subst code
                      have quoted := ih scope result tail lowered
                      have typeQuote : quoteField scope (.vector length) = fieldType :=
                        quote_classify scope fieldType (.vector length) classified
                      have vectorType :
                          vectorTerm (scope.quoteLength length) = fieldType := by
                        simpa [quoteField] using typeQuote
                      simp [Code.quote, vectorType, quoted]

structure ResolvedConstructor where
  name : String
  body : Code [] []

def lowerConstructor (source : InductiveSyntax.Constructor) :
    Option ResolvedConstructor :=
  (lowerCode .nil source.result source.fields).map fun body => ⟨source.name, body⟩

def ResolvedConstructor.quote (constructor : ResolvedConstructor) :
    InductiveSyntax.Constructor :=
  let quoted := constructor.body.quote .nil
  ⟨constructor.name, quoted.1, quoted.2⟩

@[simp] theorem lowerConstructor_quote (constructor : ResolvedConstructor) :
    lowerConstructor constructor.quote = some constructor := by
  cases constructor
  simp [ResolvedConstructor.quote, lowerConstructor]

structure ResolvedFamily where
  constructors : List ResolvedConstructor
  uniqueNames : (constructors.map (·.name)).Nodup

def expectedHeader (source : InductiveSyntax.Family) : Bool :=
  source.name == "VectorTree" && source.parameters == [] &&
    source.indices == [] && source.sort == .name "Type"

def lowerFamily (source : InductiveSyntax.Family) : Option ResolvedFamily := do
  if !expectedHeader source then none else
    let constructors ← source.constructors.mapM lowerConstructor
    if unique : (constructors.map (·.name)).Nodup then some ⟨constructors, unique⟩
    else none

def ResolvedFamily.quote (family : ResolvedFamily) : InductiveSyntax.Family :=
  ⟨"VectorTree", [], [], .name "Type", family.constructors.map (·.quote)⟩

private theorem lowerConstructors_quote :
    ∀ (constructors : List ResolvedConstructor),
      (constructors.map (·.quote)).mapM lowerConstructor = some constructors
  | [] => rfl
  | head :: tail => by simp [lowerConstructors_quote tail]

@[simp] theorem lowerFamily_quote (family : ResolvedFamily) :
    lowerFamily family.quote = some family := by
  cases family with
  | mk constructors uniqueNames =>
      simp [ResolvedFamily.quote, lowerFamily, expectedHeader,
        lowerConstructors_quote constructors, uniqueNames]

abbrev SingleFamilySource := PositiveInductiveLowering.SingleFamilySource

structure ResolvedModule where
  moduleName : String
  theoryName : String
  family : ResolvedFamily

def ResolvedModule.quote (resolved : ResolvedModule) : Module :=
  (PositiveInductiveLowering.SingleFamilySource.mk resolved.moduleName
    resolved.theoryName resolved.family.quote).quote

def lowerModule (source : Module) : Option ResolvedModule := do
  let selected ← PositiveInductiveLowering.selectSingleFamily source
  let family ← lowerFamily selected.family
  pure ⟨selected.moduleName, selected.theoryName, family⟩

@[simp] theorem lowerModule_quote (resolved : ResolvedModule) :
    lowerModule resolved.quote = some resolved := by
  cases resolved
  simp [ResolvedModule.quote, PositiveInductiveLowering.SingleFamilySource.quote,
    PositiveInductiveLowering.selectSingleFamily, lowerModule]

/-! ## Exact VectorTree source and refusal controls -/

namespace Controls

def solved : ResolvedConstructor :=
  ⟨"solved", .data "answer" .payload (by simp) .result⟩

def branch : ResolvedConstructor :=
  ⟨"branch", .data "arity" .length (by simp)
    (.vector "children" .here .result)⟩

def family : ResolvedFamily := ⟨[solved, branch], by decide⟩

def resolvedModule : ResolvedModule := ⟨"AgentVectorSearch", "Data", family⟩
def textualModule : Module := resolvedModule.quote

theorem module_roundtrip : lowerModule textualModule = some resolvedModule := by
  exact lowerModule_quote resolvedModule

theorem branch_erases_to_indexed_vector : branch.body.erase = VectorControl.code :=
  rfl

def unknownLength : InductiveSyntax.Constructor :=
  ⟨"branch", [⟨"children", vectorTerm "missing"⟩], treeTerm⟩

theorem unknownLength_refused : lowerConstructor unknownLength = none := by
  rfl

def shadowedLength : InductiveSyntax.Constructor :=
  ⟨"branch",
    [⟨"arity", lengthTerm⟩, ⟨"arity", payloadTerm⟩,
      ⟨"children", vectorTerm "arity"⟩],
    treeTerm⟩

theorem shadowedLength_refused : lowerConstructor shadowedLength = none := by
  rfl

def negativeField : InductiveSyntax.Constructor :=
  ⟨"bad", [⟨"f", .arrow treeTerm treeTerm⟩], treeTerm⟩

theorem negativeField_refused : lowerConstructor negativeField = none := by
  rfl

def verdicts : List (String × Bool) :=
  [("indexed VectorTree module lowers", (lowerModule textualModule).isSome),
   ("unbound Vector length refuses", (lowerConstructor unknownLength).isNone),
   ("shadowed Vector length refuses", (lowerConstructor shadowedLength).isNone),
   ("negative recursive field refuses", (lowerConstructor negativeField).isNone)]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

#print axioms module_roundtrip
#print axioms branch_erases_to_indexed_vector
#print axioms unknownLength_refused
#print axioms shadowedLength_refused
#print axioms negativeField_refused
#print axioms all_verdicts

end Controls

#print axioms lowerCode_quote
#print axioms quote_lowerCode
#print axioms lowerFamily_quote
#print axioms lowerModule_quote

end Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering
