import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Typed context substitution for authored language definitions

`Pattern` uses locally nameless binders and named free variables.  The
matching substitution used by the executable rule engine is intentionally
operational: it instantiates schemas and evaluates explicit substitution
nodes.  A structural language construction needs a different operation.  It
must substitute open, typed terms for free variables while preserving every
ambient binder.

This file defines the ordinary-binder action and derives its typing laws from
the single authored `LanguageDef`.  Reflective quotation needs an additional
support-aware boundary layer because quotation resets ambient binder scope;
that layer can reuse these weakening and typing results without changing the
runtime matcher.  No second term language or notion of sorting is introduced.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

namespace ContextSubstitution

/-- A simultaneous assignment for named free variables. -/
abbrev Assignment := String → Pattern

/-- Capture-avoiding simultaneous free-variable substitution below `depth`
new binders.  A replacement is authored in the ambient bound context, so all
of its de Bruijn indices are lifted when it is inserted beneath binders.
Explicit-substitution nodes are retained as syntax: this is structural
context substitution, not evaluator substitution. -/
def substituteAt (assignment : Assignment) (depth : Nat) : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => liftBVars 0 depth (assignment name)
  | .apply constructor arguments =>
      .apply constructor (arguments.map (substituteAt assignment depth))
  | .lambda binderName body =>
      .lambda binderName (substituteAt assignment (depth + 1) body)
  | .multiLambda arity binderNames body =>
      .multiLambda arity binderNames
        (substituteAt assignment (depth + arity) body)
  | .subst body replacement =>
      .subst (substituteAt assignment (depth + 1) body)
        (substituteAt assignment depth replacement)
  | .collection collectionType elements rest =>
      .collection collectionType
        (elements.map (substituteAt assignment depth)) rest
termination_by pattern => sizeOf pattern

/-- Top-level simultaneous free-variable substitution. -/
def substitute (assignment : Assignment) (pattern : Pattern) : Pattern :=
  substituteAt assignment 0 pattern

/-- The identity assignment. -/
def identity : Assignment := Pattern.fvar

/-- Rename only the ambient portion of locally nameless bound variables.
Indices introduced by syntax below `depth` remain fixed; an ambient index is
contracted to the surrounding context, acted on by `rename`, and embedded
again below the same local prefix.  This is the common context action behind
ordinary weakening and Cost's proof-relevant insertion of foreign binders. -/
def renameAmbientBVarsAt (rename : Nat → Nat) (depth : Nat) :
    Pattern → Pattern
  | .bvar index =>
      if index < depth then .bvar index
      else .bvar (depth + rename (index - depth))
  | .fvar name => .fvar name
  | .apply constructor arguments =>
      .apply constructor (arguments.map (renameAmbientBVarsAt rename depth))
  | .lambda binderName body =>
      .lambda binderName (renameAmbientBVarsAt rename (depth + 1) body)
  | .multiLambda arity binderNames body =>
      .multiLambda arity binderNames
        (renameAmbientBVarsAt rename (depth + arity) body)
  | .subst body replacement =>
      .subst (renameAmbientBVarsAt rename (depth + 1) body)
        (renameAmbientBVarsAt rename depth replacement)
  | .collection collectionType elements rest =>
      .collection collectionType
        (elements.map (renameAmbientBVarsAt rename depth)) rest
termination_by pattern => sizeOf pattern

/-- Transport a structural one-hole context through an ambient binder
renaming.  The second component records the binder depth at the transported
hole, so the same context action can be applied to the term inserted there. -/
def renameAmbientContextAt (rename : Nat → Nat) :
    Nat → OneHoleContext → OneHoleContext × Nat
  | depth, .hole => (.hole, depth)
  | depth, .apply constructor before inner after =>
      let transported := renameAmbientContextAt rename depth inner
      (.apply constructor
          (before.map (renameAmbientBVarsAt rename depth))
          transported.1
          (after.map (renameAmbientBVarsAt rename depth)),
        transported.2)
  | depth, .lambda binder inner =>
      let transported := renameAmbientContextAt rename (depth + 1) inner
      (.lambda binder transported.1, transported.2)
  | depth, .multiLambda arity binders inner =>
      let transported := renameAmbientContextAt rename (depth + arity) inner
      (.multiLambda arity binders transported.1, transported.2)
  | depth, .substBody inner replacement =>
      let transported := renameAmbientContextAt rename (depth + 1) inner
      (.substBody transported.1
          (renameAmbientBVarsAt rename depth replacement), transported.2)
  | depth, .substReplacement body inner =>
      let transported := renameAmbientContextAt rename depth inner
      (.substReplacement
          (renameAmbientBVarsAt rename (depth + 1) body) transported.1,
        transported.2)
  | depth, .collection collectionType before inner after rest =>
      let transported := renameAmbientContextAt rename depth inner
      (.collection collectionType
          (before.map (renameAmbientBVarsAt rename depth))
          transported.1
          (after.map (renameAmbientBVarsAt rename depth)) rest,
        transported.2)

/-- Ambient binder renaming commutes exactly with filling a transported
one-hole structural context. -/
theorem renameAmbientBVarsAt_fill (rename : Nat → Nat) (depth : Nat)
    (context : OneHoleContext) (pattern : Pattern) :
    renameAmbientBVarsAt rename depth (context.fill pattern) =
      let transported := renameAmbientContextAt rename depth context
      transported.1.fill
        (renameAmbientBVarsAt rename transported.2 pattern) := by
  induction context generalizing depth with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simp only [OneHoleContext.fill, renameAmbientBVarsAt, List.map_append,
        List.map_cons, renameAmbientContextAt, inductionHypothesis]
  | lambda binder inner inductionHypothesis =>
      simp only [OneHoleContext.fill, renameAmbientBVarsAt,
        renameAmbientContextAt, inductionHypothesis]
  | multiLambda arity binders inner inductionHypothesis =>
      simp only [OneHoleContext.fill, renameAmbientBVarsAt,
        renameAmbientContextAt, inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp only [OneHoleContext.fill, renameAmbientBVarsAt,
        renameAmbientContextAt, inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp only [OneHoleContext.fill, renameAmbientBVarsAt,
        renameAmbientContextAt, inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp only [OneHoleContext.fill, renameAmbientBVarsAt, List.map_append,
        List.map_cons, renameAmbientContextAt, inductionHypothesis]

/-- The identity context map acts identically on every raw pattern. -/
@[simp]
theorem renameAmbientBVarsAt_id (depth : Nat) (pattern : Pattern) :
    renameAmbientBVarsAt id depth pattern = pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      by_cases inside : index < depth
      · simp [renameAmbientBVarsAt, inside]
      · simp only [renameAmbientBVarsAt, if_neg inside, id_eq,
          Pattern.bvar.injEq]
        omega
  | hfvar name => simp [renameAmbientBVarsAt]
  | happly constructor arguments inductionHypothesis =>
      simp only [renameAmbientBVarsAt, Pattern.apply.injEq, true_and]
      have mapped := List.map_congr_left
        (l := arguments) (f := renameAmbientBVarsAt id depth) (g := id)
        (fun argument membership =>
          inductionHypothesis argument membership depth)
      simpa only [List.map_id, id_eq] using mapped
  | hlambda binderName body inductionHypothesis =>
      simp [renameAmbientBVarsAt, inductionHypothesis]
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simp [renameAmbientBVarsAt, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [renameAmbientBVarsAt, bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [renameAmbientBVarsAt, Pattern.collection.injEq, true_and]
      have mapped := List.map_congr_left
        (l := elements) (f := renameAmbientBVarsAt id depth) (g := id)
        (fun element membership =>
          inductionHypothesis element membership depth)
      exact ⟨by simpa only [List.map_id, id_eq] using mapped, trivial⟩

/-- Ambient context actions compose in the same order as their index maps.
This law is purely structural and does not assume injectivity. -/
theorem renameAmbientBVarsAt_comp (first second : Nat → Nat)
    (depth : Nat) (pattern : Pattern) :
    renameAmbientBVarsAt second depth
        (renameAmbientBVarsAt first depth pattern) =
      renameAmbientBVarsAt (second ∘ first) depth pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      by_cases inside : index < depth
      · simp [renameAmbientBVarsAt, inside]
      · have embeddedOutside :
            ¬ depth + first (index - depth) < depth := by omega
        simp only [renameAmbientBVarsAt, if_neg inside, if_neg embeddedOutside,
          Function.comp_apply, Pattern.bvar.injEq]
        rw [Nat.add_sub_cancel_left]
  | hfvar name => simp [renameAmbientBVarsAt]
  | happly constructor arguments inductionHypothesis =>
      simp only [renameAmbientBVarsAt, List.map_map, Pattern.apply.injEq,
        true_and]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership depth
  | hlambda binderName body inductionHypothesis =>
      simp [renameAmbientBVarsAt, inductionHypothesis]
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simp [renameAmbientBVarsAt, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [renameAmbientBVarsAt, bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [renameAmbientBVarsAt, List.map_map,
        Pattern.collection.injEq, true_and]
      constructor
      · apply List.map_congr_left
        intro element membership
        exact inductionHypothesis element membership depth
      · trivial

/-- Ordinary de Bruijn weakening is the affine ambient context action. -/
theorem renameAmbientBVarsAt_add_eq_liftBVars
    (cutoff shift : Nat) (pattern : Pattern) :
    renameAmbientBVarsAt (fun index => index + shift) cutoff pattern =
      liftBVars cutoff shift pattern := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      by_cases inside : index < cutoff
      · simp [renameAmbientBVarsAt, liftBVars, inside]
      · have cutoffLe : cutoff ≤ index := Nat.le_of_not_gt inside
        simp [renameAmbientBVarsAt, liftBVars, inside, cutoffLe]
        omega
  | hfvar name => simp [renameAmbientBVarsAt, liftBVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [renameAmbientBVarsAt, liftBVars,
        Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership cutoff
  | hlambda binderName body inductionHypothesis =>
      simp [renameAmbientBVarsAt, liftBVars, inductionHypothesis]
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simp [renameAmbientBVarsAt, liftBVars, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [renameAmbientBVarsAt, liftBVars, bodyInduction,
        replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [renameAmbientBVarsAt, liftBVars,
        Pattern.collection.injEq, true_and]
      constructor
      · apply List.map_congr_left
        intro element membership
        exact inductionHypothesis element membership cutoff
      · trivial

@[simp]
theorem substituteAt_identity (depth : Nat) (pattern : Pattern) :
    substituteAt identity depth pattern = pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simp [substituteAt]
  | hfvar name => simp [substituteAt, identity, liftBVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [substituteAt, Pattern.apply.injEq, true_and]
      have mapped :
          arguments.map (substituteAt identity depth) = arguments.map id :=
        List.map_congr_left fun argument membership =>
          inductionHypothesis argument membership depth
      simpa using mapped
  | hlambda binderName body inductionHypothesis =>
      simp [substituteAt, inductionHypothesis]
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simp [substituteAt, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [substituteAt, bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [substituteAt, Pattern.collection.injEq, true_and]
      have mapped :
          elements.map (substituteAt identity depth) = elements.map id :=
        List.map_congr_left fun element membership =>
          inductionHypothesis element membership depth
      simpa using mapped

@[simp]
theorem substitute_identity (pattern : Pattern) :
    substitute identity pattern = pattern :=
  substituteAt_identity 0 pattern

/-- Quote-aware scope is preserved when a block is inserted into the ambient
de Bruijn context.  A quotation is the delicate case: its body is already
scoped from zero, so lifting above the ambient cutoff is definitionally
inert there. -/
theorem binderSafeAt_liftBVars
    (quoteConstructor : String) {ambient cutoff shift : Nat}
    {pattern : Pattern}
    (safe : binderSafeAt quoteConstructor (ambient + cutoff) pattern = true) :
    binderSafeAt quoteConstructor (ambient + cutoff + shift)
      (liftBVars cutoff shift pattern) = true := by
  induction pattern using Pattern.inductionOn generalizing ambient cutoff with
  | hbvar index =>
      simp only [binderSafeAt, decide_eq_true_eq] at safe ⊢
      simp only [liftBVars]
      split <;> simp only [binderSafeAt, decide_eq_true_eq] <;> omega
  | hfvar name => simp [liftBVars, binderSafeAt]
  | happly constructor arguments inductionHypothesis =>
      cases arguments with
      | nil => simp [liftBVars, binderSafeAt, binderSafeListAt]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              by_cases quoted : constructor = quoteConstructor
              · subst constructor
                simp only [binderSafeAt, beq_self_eq_true, if_true] at safe ⊢
                have ordinaryZero :=
                  isWellScopedAt_of_binderSafeAt quoteConstructor safe
                have ordinaryCutoff := isWellScopedAt_mono ordinaryZero
                  (Nat.zero_le cutoff)
                simp only [liftBVars, List.map, binderSafeAt,
                  beq_self_eq_true, if_true] at ⊢
                change binderSafeAt quoteConstructor 0
                  (liftBVars cutoff shift argument) = true
                rw [liftBVars_eq_self_of_isWellScopedAt ordinaryCutoff]
                exact safe
              · simp only [liftBVars, binderSafeAt, beq_iff_eq,
                  List.map, if_neg quoted, binderSafeListAt,
                  Bool.and_true] at safe ⊢
                exact inductionHypothesis argument (by simp) safe
          | cons second remainder =>
              change binderSafeListAt quoteConstructor (ambient + cutoff)
                (argument :: second :: remainder) = true at safe
              simp only [liftBVars] at ⊢
              change binderSafeListAt quoteConstructor
                (ambient + cutoff + shift)
                ((argument :: second :: remainder).map
                  (liftBVars cutoff shift)) = true
              rw [binderSafeListAt_eq_true_iff] at safe ⊢
              intro member membership
              rcases List.mem_map.mp membership with
                ⟨sourceMember, sourceMembership, rfl⟩
              exact inductionHypothesis sourceMember sourceMembership
                (safe sourceMember sourceMembership)
  | hlambda binderName body inductionHypothesis =>
      simp only [liftBVars, binderSafeAt] at safe ⊢
      have lifted := inductionHypothesis
        (ambient := ambient) (cutoff := cutoff + 1)
        (by simpa only [Nat.add_assoc] using safe)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lifted
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simp only [liftBVars, binderSafeAt] at safe ⊢
      have lifted := inductionHypothesis
        (ambient := ambient) (cutoff := cutoff + arity)
        (by simpa only [Nat.add_assoc] using safe)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lifted
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [liftBVars, binderSafeAt, Bool.and_eq_true] at safe ⊢
      constructor
      · have lifted := bodyInduction
          (ambient := ambient) (cutoff := cutoff + 1)
          (by simpa only [Nat.add_assoc] using safe.1)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lifted
      · exact replacementInduction safe.2
  | hcollection collectionType elements rest inductionHypothesis =>
      change binderSafeListAt quoteConstructor (ambient + cutoff) elements = true
        at safe
      simp only [liftBVars] at ⊢
      change binderSafeListAt quoteConstructor (ambient + cutoff + shift)
        (elements.map (liftBVars cutoff shift)) = true
      rw [binderSafeListAt_eq_true_iff] at safe ⊢
      intro element membership
      rcases List.mem_map.mp membership with
        ⟨sourceElement, sourceMembership, rfl⟩
      exact inductionHypothesis sourceElement sourceMembership
        (safe sourceElement sourceMembership)

end ContextSubstitution

namespace WellSorted

open ContextSubstitution

/-- A simultaneous free-variable assignment is well typed from `source` to
`target` in one ambient bound context when every source variable is sent to a
term of its authored type in the target context. -/
structure TypedAssignment (language : LanguageDef)
    (source target : FreeTypeContext) (bound : List TypeExpr) where
  assignment : ContextSubstitution.Assignment
  typed : ∀ {name type}, source name = some type →
    HasType language target bound (assignment name) type

/-- Lookup is preserved when a block is inserted into a de Bruijn context and
indices at or beyond the insertion point are shifted by the block length. -/
private theorem getElem?_insert
    {inner outer inserted : List TypeExpr} {index : Nat} {type : TypeExpr}
    (lookup : (inner ++ outer)[index]? = some type) :
    GetElem?.getElem? ((inner ++ inserted) ++ outer)
        (if index ≥ inner.length then index + inserted.length else index) =
      some type := by
  induction inner generalizing index with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.zero_le, ↓reduceIte]
      rw [List.getElem?_append_right]
      · simpa using lookup
      · omega
  | cons head inner inductionHypothesis =>
      cases index with
      | zero => simpa using lookup
      | succ index =>
          simp only [List.cons_append, List.getElem?_cons_succ] at lookup ⊢
          have shifted := inductionHypothesis lookup
          by_cases beyond : index ≥ inner.length
          · have beyond' : Nat.succ index ≥ (head :: inner).length := by
              simp only [List.length_cons]
              omega
            simp only [beyond, beyond', if_pos] at shifted ⊢
            simpa [Nat.succ_add] using shifted
          · have within' : ¬ Nat.succ index ≥ (head :: inner).length := by
              simp only [List.length_cons]
              omega
            simp only [beyond, within'] at shifted ⊢
            exact shifted

/-- Lifting preserves the representation form selected by an authored
constructor parameter. -/
private theorem matchesParameterRepresentation_liftBVars
    (parameter : TermParam) (pattern : Pattern) (cutoff shift : Nat) :
    MatchesParameterRepresentation parameter pattern →
      MatchesParameterRepresentation parameter
        (liftBVars cutoff shift pattern) := by
  cases parameter with
  | simple => exact fun _ => trivial
  | abstractionNamed binderName bodyName type =>
      cases pattern <;> simp [MatchesParameterRepresentation, liftBVars]
      case lambda binder body =>
        cases binder <;> simp
  | multiAbstractionNamed binderNames bodyName type =>
      cases pattern <;> simp [MatchesParameterRepresentation, liftBVars]
      case multiLambda arity binders body =>
        cases binders <;> simp

mutual
  /-- Inserting a list of binder types after an existing inner prefix
  preserves a typing derivation when the corresponding de Bruijn indices are
  lifted.  This is the weakening lemma required by open context
  substitution. -/
  theorem HasType.liftBVars_insert
      {language : LanguageDef} {free : FreeTypeContext}
      {inner outer inserted : List TypeExpr} {pattern : Pattern}
      {type : TypeExpr}
      (typed : HasType language free (inner ++ outer) pattern type) :
      HasType language free ((inner ++ inserted) ++ outer)
        (liftBVars inner.length inserted.length pattern) type := by
    cases typed with
    | @bvar _ index type lookup =>
        by_cases beyond : index ≥ inner.length
        · simpa [liftBVars, beyond] using
            (HasType.bvar (free := free)
              (getElem?_insert (inserted := inserted) lookup))
        · simpa [liftBVars, beyond] using
            (HasType.bvar (free := free)
              (getElem?_insert (inserted := inserted) lookup))
    | @fvar _ name type lookup =>
        simpa only [liftBVars] using
          (HasType.fvar (bound := (inner ++ inserted) ++ outer) lookup)
    | @constructor _ rule arguments membership notBare argumentsTyped =>
        simpa only [liftBVars] using
          (HasType.constructor membership notBare
            (argumentsTyped.liftBVars_insert
              (inner := inner) (outer := outer) (inserted := inserted)))
    | @lambda _ binder body domain codomain bodyTyped =>
        have liftedBody := bodyTyped.liftBVars_insert
          (inner := domain :: inner) (outer := outer)
          (inserted := inserted)
        have liftedBody' : HasType language free
            (domain :: ((inner ++ inserted) ++ outer))
            (liftBVars (inner.length + 1) inserted.length body) codomain := by
          simpa only [List.cons_append, List.length_cons, Nat.add_comm] using
            liftedBody
        simpa only [liftBVars] using
          HasType.lambda (binder := binder) liftedBody'
    | @multiLambda _ arity binders body domain codomain bodyTyped =>
        have bodyTyped' : HasType language free
            ((List.replicate arity domain ++ inner) ++ outer) body codomain := by
          simpa only [List.append_assoc] using bodyTyped
        have liftedBody := bodyTyped'.liftBVars_insert
          (inner := List.replicate arity domain ++ inner) (outer := outer)
          (inserted := inserted)
        have liftedBody' : HasType language free
            (List.replicate arity domain ++ ((inner ++ inserted) ++ outer))
            (liftBVars (inner.length + arity) inserted.length body) codomain := by
          simpa only [List.append_assoc, List.length_append,
            List.length_replicate, Nat.add_comm] using liftedBody
        simpa only [liftBVars] using
          HasType.multiLambda (binders := binders) liftedBody'
    | @subst _ body replacement domain codomain bodyTyped replacementTyped =>
        have liftedBody := bodyTyped.liftBVars_insert
          (inner := domain :: inner) (outer := outer)
          (inserted := inserted)
        have liftedReplacement := replacementTyped.liftBVars_insert
          (inner := inner) (outer := outer) (inserted := inserted)
        have liftedBody' : HasType language free
            (domain :: ((inner ++ inserted) ++ outer))
            (liftBVars (inner.length + 1) inserted.length body) type := by
          simpa only [List.cons_append, List.length_cons, Nat.add_comm] using
            liftedBody
        simpa only [liftBVars] using
          HasType.subst liftedBody' liftedReplacement
    | @collection _ collectionType elements rest elementType elementsTyped =>
        simpa only [liftBVars] using
          (HasType.collection (rest := rest)
            (elementsTyped.liftBVars_insert
              (inner := inner) (outer := outer) (inserted := inserted)))
    | @collectionConstructor _ rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        simpa only [liftBVars] using
          (HasType.collectionConstructor membership parameterShape
            (elementsTyped.liftBVars_insert
              (inner := inner) (outer := outer) (inserted := inserted)))

  theorem ArgumentsHaveTypes.liftBVars_insert
      {language : LanguageDef} {free : FreeTypeContext}
      {inner outer inserted : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free (inner ++ outer)
        arguments parameters) :
      ArgumentsHaveTypes language free ((inner ++ inserted) ++ outer)
        (arguments.map (liftBVars inner.length inserted.length)) parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped argumentsTyped =>
        exact .cons
          (matchesParameterRepresentation_liftBVars _ _ _ _ representation)
          parameterType
          (argumentTyped.liftBVars_insert
            (inner := inner) (outer := outer) (inserted := inserted))
          (argumentsTyped.liftBVars_insert
            (inner := inner) (outer := outer) (inserted := inserted))

  theorem ElementsHaveType.liftBVars_insert
      {language : LanguageDef} {free : FreeTypeContext}
      {inner outer inserted : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType language free (inner ++ outer)
        elements elementType) :
      ElementsHaveType language free ((inner ++ inserted) ++ outer)
        (elements.map (liftBVars inner.length inserted.length)) elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons
          (elementTyped.liftBVars_insert
            (inner := inner) (outer := outer) (inserted := inserted))
          (elementsTyped.liftBVars_insert
            (inner := inner) (outer := outer) (inserted := inserted))
end

/-- Structural context substitution preserves the representation form
selected by an authored constructor parameter. -/
theorem matchesParameterRepresentation_substituteAt
    (parameter : TermParam) (pattern : Pattern)
    (assignment : ContextSubstitution.Assignment) (depth : Nat) :
    MatchesParameterRepresentation parameter pattern →
      MatchesParameterRepresentation parameter
        (ContextSubstitution.substituteAt assignment depth pattern) := by
  cases parameter with
  | simple => exact fun _ => trivial
  | abstractionNamed binderName bodyName type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation, ContextSubstitution.substituteAt]
      case lambda binder body => cases binder <;> simp
  | multiAbstractionNamed binderNames bodyName type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation, ContextSubstitution.substituteAt]
      case multiLambda arity binders body => cases binders <;> simp

mutual
  /-- A typed simultaneous assignment acts on every sorted term while
  preserving its type and ambient binder context. -/
  theorem HasType.substituteAt
      {language : LanguageDef} {source target : FreeTypeContext}
      {outer inner : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (assignment : TypedAssignment language source target outer)
      (typed : HasType language source (inner ++ outer) pattern type) :
      HasType language target (inner ++ outer)
        (ContextSubstitution.substituteAt
          assignment.assignment inner.length pattern) type := by
    cases typed with
    | @bvar _ index type lookup =>
        simpa only [ContextSubstitution.substituteAt] using
          (HasType.bvar (free := target) lookup)
    | @fvar _ name type lookup =>
        have replacementTyped := assignment.typed lookup
        have lifted := replacementTyped.liftBVars_insert
          (inner := []) (outer := outer) (inserted := inner)
        simpa only [ContextSubstitution.substituteAt, List.nil_append,
          List.length_nil] using lifted
    | @constructor _ rule arguments membership notBare argumentsTyped =>
        simpa only [ContextSubstitution.substituteAt] using
          (HasType.constructor membership notBare
            (argumentsTyped.substituteAt assignment (inner := inner)))
    | @lambda _ binder body domain codomain bodyTyped =>
        have bodyTyped' : HasType language source
            ((domain :: inner) ++ outer) body codomain := by
          simpa only [List.cons_append] using bodyTyped
        have substitutedBody := bodyTyped'.substituteAt assignment
          (inner := domain :: inner)
        have substitutedBody' : HasType language target
            (domain :: (inner ++ outer))
            (ContextSubstitution.substituteAt assignment.assignment
              (inner.length + 1) body) codomain := by
          simpa only [List.cons_append, List.length_cons, Nat.add_comm] using
            substitutedBody
        simpa only [ContextSubstitution.substituteAt] using
          HasType.lambda (binder := binder) substitutedBody'
    | @multiLambda _ arity binders body domain codomain bodyTyped =>
        have bodyTyped' : HasType language source
            ((List.replicate arity domain ++ inner) ++ outer) body codomain := by
          simpa only [List.append_assoc] using bodyTyped
        have substitutedBody := bodyTyped'.substituteAt assignment
          (inner := List.replicate arity domain ++ inner)
        have substitutedBody' : HasType language target
            (List.replicate arity domain ++ (inner ++ outer))
            (ContextSubstitution.substituteAt assignment.assignment
              (inner.length + arity) body) codomain := by
          simpa only [List.append_assoc, List.length_append,
            List.length_replicate, Nat.add_comm] using substitutedBody
        simpa only [ContextSubstitution.substituteAt] using
          HasType.multiLambda (binders := binders) substitutedBody'
    | @subst _ body replacement domain codomain bodyTyped replacementTyped =>
        have bodyTyped' : HasType language source
            ((domain :: inner) ++ outer) body type := by
          simpa only [List.cons_append] using bodyTyped
        have substitutedBody := bodyTyped'.substituteAt assignment
          (inner := domain :: inner)
        have substitutedReplacement := replacementTyped.substituteAt assignment
          (inner := inner)
        have substitutedBody' : HasType language target
            (domain :: (inner ++ outer))
            (ContextSubstitution.substituteAt assignment.assignment
              (inner.length + 1) body) type := by
          simpa only [List.cons_append, List.length_cons, Nat.add_comm] using
            substitutedBody
        simpa only [ContextSubstitution.substituteAt] using
          HasType.subst substitutedBody' substitutedReplacement
    | @collection _ collectionType elements rest elementType elementsTyped =>
        simpa only [ContextSubstitution.substituteAt] using
          (HasType.collection (rest := rest)
            (elementsTyped.substituteAt assignment (inner := inner)))
    | @collectionConstructor _ rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        simpa only [ContextSubstitution.substituteAt] using
          (HasType.collectionConstructor membership parameterShape
            (elementsTyped.substituteAt assignment (inner := inner)))

  theorem ArgumentsHaveTypes.substituteAt
      {language : LanguageDef} {source target : FreeTypeContext}
      {outer inner : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (assignment : TypedAssignment language source target outer)
      (typed : ArgumentsHaveTypes language source (inner ++ outer)
        arguments parameters) :
      ArgumentsHaveTypes language target (inner ++ outer)
        (arguments.map (ContextSubstitution.substituteAt
          assignment.assignment inner.length)) parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped argumentsTyped =>
        exact .cons
          (matchesParameterRepresentation_substituteAt _ _ _ _ representation)
          parameterType
          (argumentTyped.substituteAt assignment (inner := inner))
          (argumentsTyped.substituteAt assignment (inner := inner))

  theorem ElementsHaveType.substituteAt
      {language : LanguageDef} {source target : FreeTypeContext}
      {outer inner : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (assignment : TypedAssignment language source target outer)
      (typed : ElementsHaveType language source (inner ++ outer)
        elements elementType) :
      ElementsHaveType language target (inner ++ outer)
        (elements.map (ContextSubstitution.substituteAt
          assignment.assignment inner.length)) elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons
          (elementTyped.substituteAt assignment (inner := inner))
          (elementsTyped.substituteAt assignment (inner := inner))
end

/-- Identity is a typed simultaneous assignment in every context. -/
def TypedAssignment.identity (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) :
    TypedAssignment language free free bound where
  assignment := ContextSubstitution.identity
  typed := fun lookup => HasType.fvar lookup

end WellSorted

end Mettapedia.GSLT.LanguageDef
