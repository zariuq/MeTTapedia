import Mettapedia.Languages.Megalodon.HenkinDeltaInterpretation

/-!
# Native typing after successful checked delta expansion

Native inference is preserved by a successful finite-fuel delta expansion of
checked plain definitions. The source intrinsic context and term are recovered
from the native checks; exact erasure supplies the intrinsic output. Output
annotation formation is proved independently from the raw evaluator, rather
than assumed from the existence of that intrinsic output.

Lookup formation is local to the source and the checked definition bodies.
Unrelated prefix-polymorphic declarations remain permitted. These results do
not assert termination, ordered document admission, or any model equation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTermInterpretation

open MathdataKernel
open Mettapedia.Logic.HOL

/-- A local lookup-formation check remains valid with more type variables. -/
theorem PlainLookups.mono {environment : Environment} {lower upper : Nat}
    {term : Tm} (lookups : PlainLookups environment lower term) (le : lower ≤ upper) :
    PlainLookups environment upper term := by
  induction term with
  | db _ => trivial
  | named name =>
      intro declaration lookup
      exact Tp.plainWellFormed_mono (lookups declaration lookup) le
  | prim index =>
      intro type lookup
      exact Tp.plainWellFormed_mono (lookups type lookup) le
  | app _ _ ihf iha | imp _ _ ihf iha =>
      exact ⟨ihf lookups.1, iha lookups.2⟩
  | lam _ _ ih | all _ _ ih => exact ih lookups
  | typeApp _ _ _ | typeLam _ _ | typeAll _ _ => exact lookups

/-- Closed binder annotations are also formed at every larger type depth. -/
theorem plainAnnotations_mono {lower upper : Nat} {term : Tm}
    (formed : plainAnnotations lower term = true) (le : lower ≤ upper) :
    plainAnnotations upper term = true := by
  induction term with
  | db _ | named _ | prim _ => rfl
  | app _ _ ihf iha | imp _ _ ihf iha =>
      simp only [plainAnnotations, Bool.and_eq_true] at formed ⊢
      exact ⟨ihf formed.1, iha formed.2⟩
  | lam _ _ ih | all _ _ ih =>
      simp only [plainAnnotations, Bool.and_eq_true] at formed ⊢
      exact ⟨Tp.plainWellFormed_mono formed.1 le, ih formed.2⟩
  | typeApp _ _ _ | typeLam _ _ | typeAll _ _ => exact formed

/-- Successful raw delta expansion preserves local lookup formation and binder
annotation formation. A named definition is eligible because its locally formed
lookup type has a plain intrinsic representation, not because the whole library
has been required to be monomorphic. -/
theorem deltaNormalize_formation {environment : Environment}
    (checked : CheckedPlainDefinitions environment) (fuel : Nat) {depth : Nat}
    {source result : Tm} (lookups : PlainLookups environment depth source)
    (annotations : plainAnnotations depth source = true)
    (expanded : deltaNormalize environment fuel source = some result) :
    PlainLookups environment depth result ∧ plainAnnotations depth result = true := by
  induction fuel using Nat.strong_induction_on generalizing depth source result with
  | h fuel ihfuel =>
      induction source generalizing result with
      | db index | prim index =>
          simp only [deltaNormalize, Option.some.injEq] at expanded
          subst result
          exact ⟨lookups, annotations⟩
      | named name =>
          cases lookup : environment.lookupTerm? name with
          | none =>
              cases fuel <;> simp only [deltaNormalize, lookup, Option.some.injEq] at expanded
              all_goals subst result; exact ⟨lookups, annotations⟩
          | some declaration =>
              rcases declaration with ⟨declarationName, declarationType, definition⟩
              cases definition with
              | none =>
                  cases fuel <;> simp only [deltaNormalize, lookup, Option.some.injEq] at expanded
                  all_goals subst result; exact ⟨lookups, annotations⟩
              | some body =>
                  obtain ⟨type, reified⟩ := exists_reifyType_of_plain (lookups _ lookup)
                  have valid := checked.body name
                    ⟨declarationName, declarationType, some body⟩ body lookup rfl ⟨type, reified⟩
                  cases fuel with
                  | zero => simp [deltaNormalize, lookup] at expanded
                  | succ fuel =>
                      simp only [deltaNormalize, lookup] at expanded
                      have formed := ihfuel fuel (Nat.lt_succ_self fuel) valid.lookups
                        valid.annotations expanded
                      exact ⟨formed.1.mono (Nat.zero_le depth),
                        plainAnnotations_mono formed.2 (Nat.zero_le depth)⟩
      | app function argument ihf iha | imp function argument ihf iha =>
          simp only [plainAnnotations, Bool.and_eq_true] at annotations
          cases functionExpanded : deltaNormalize environment fuel function with
          | none => simp [deltaNormalize, functionExpanded] at expanded
          | some functionResult =>
              cases argumentExpanded : deltaNormalize environment fuel argument with
              | none => simp [deltaNormalize, functionExpanded, argumentExpanded] at expanded
              | some argumentResult =>
                  simp [deltaNormalize, functionExpanded, argumentExpanded] at expanded
                  subst result
                  have functionFormed := ihf lookups.1 annotations.1 functionExpanded
                  have argumentFormed := iha lookups.2 annotations.2 argumentExpanded
                  exact ⟨⟨functionFormed.1, argumentFormed.1⟩,
                    by simp only [plainAnnotations, functionFormed.2, argumentFormed.2, Bool.and_self]⟩
      | lam type body ih | all type body ih =>
          simp only [plainAnnotations, Bool.and_eq_true] at annotations
          cases bodyExpanded : deltaNormalize environment fuel body with
          | none => simp [deltaNormalize, bodyExpanded] at expanded
          | some bodyResult =>
              simp [deltaNormalize, bodyExpanded] at expanded
              subst result
              have bodyFormed := ih lookups annotations.2 bodyExpanded
              exact ⟨bodyFormed.1, by simp only [plainAnnotations, annotations.1, bodyFormed.2,
                Bool.and_self]⟩
      | typeApp _ _ _ | typeLam _ _ | typeAll _ _ => simp [plainAnnotations] at annotations

/-- Native type synthesis survives successful delta expansion. All data used
to reconstruct the source intrinsic term are native formation and inference
checks. The result's annotations are established by `deltaNormalize_formation`.
No model interpretation or equality hypothesis occurs in this theorem. -/
theorem native_infer_deltaNormalize {environment : Environment}
    (checked : CheckedPlainDefinitions environment) {fuel depth : Nat}
    {context : List Tp} {source result : Tm} {type : Tp}
    (plainContext : ∀ type ∈ context, type.plainWellFormed depth = true)
    (lookups : PlainLookups environment depth source)
    (annotations : plainAnnotations depth source = true)
    (inferred : inferTerm environment depth context source = some type)
    (expanded : deltaNormalize environment fuel source = some result) :
    inferTerm environment depth context result = some type := by
  obtain ⟨intrinsicContext, intrinsicType, term, contextEqual, typeEqual, erased⟩ :=
    interpret_native plainContext lookups (supported_of_plainAnnotations annotations) inferred
  obtain ⟨output, _, outputErased⟩ :=
    (deltaNormalize_eq_some_iff checked fuel term erased).mp expanded
  have outputAnnotations := (deltaNormalize_formation checked fuel lookups annotations expanded).2
  have outputInferred := infer_of_erase output outputErased outputAnnotations
  simpa only [contextEqual, typeEqual] using outputInferred

namespace DeltaTypingExamples

def identityDeclaration : TermDecl :=
  { name := "id", type := .arr .prop .prop, definition := some (.lam .prop (.db 0)) }

def propositionDeclaration : TermDecl :=
  { name := "q", type := .prop, definition := some (.app (.named "id") (.named "p")) }

def parameterDeclaration : TermDecl :=
  { name := "p", type := .prop }

/-- A real prefix-polymorphic definition is present but unrelated to the plain
term being unfolded. It is not deleted or replaced by an opaque placeholder. -/
def prefixDeclaration : TermDecl :=
  { name := "polyId", type := .all (.arr (.var 0) (.var 0)),
    definition := some (.typeLam (.lam (.var 0) (.db 0))) }

def environment : Environment :=
  { terms := [identityDeclaration, propositionDeclaration, parameterDeclaration, prefixDeclaration] }

theorem prefix_definition_typed :
    inferTerm environment 0 [] (.typeLam (.lam (.var 0) (.db 0))) =
      some prefixDeclaration.type := by decide

theorem environment_not_plain : ¬ PlainEnvironment environment 1 := by
  intro plain
  have formed := plain.named "polyId" prefixDeclaration (by decide)
  cases formed

theorem checkedDefinitions : CheckedPlainDefinitions environment where
  body := by
    intro name declaration body lookup defined representable
    simp only [environment, Environment.lookupTerm?, lookupTermList?, identityDeclaration,
      propositionDeclaration, parameterDeclaration, prefixDeclaration] at lookup
    split at lookup
    · cases lookup
      cases defined
      exact ⟨rfl, rfl, by trivial, by decide⟩
    · split at lookup
      · cases lookup
        cases defined
        exact ⟨rfl, rfl,
          by simp [PlainLookups, environment, Environment.lookupTerm?, lookupTermList?,
            identityDeclaration, propositionDeclaration, parameterDeclaration,
            Tp.plainWellFormed], by decide⟩
      · split at lookup
        · cases lookup
          cases defined
        · split at lookup
          · cases lookup
            obtain ⟨type, typed⟩ := representable
            cases type with
            | prop | arr => cases typed
            | base index => cases index <;> cases typed
          · cases lookup

/-- The surrounding free type variable is independent of the closed global
definitions; unfolding happens underneath a native term binder. -/
def source : Tm := .lam (.var 0) (.named "q")

/-- Delta expansion does not perform beta reduction. The expanded application
of the identity remains present beneath the outer binder. -/
def result : Tm := .lam (.var 0) (.app (.lam .prop (.db 0)) (.named "p"))

theorem source_lookups : PlainLookups environment 1 source := by
  simp [source, PlainLookups, environment, Environment.lookupTerm?, lookupTermList?,
    identityDeclaration, propositionDeclaration, Tp.plainWellFormed]

theorem source_annotations : plainAnnotations 1 source = true := by decide

theorem source_inferred :
    inferTerm environment 1 [] source = some (.arr (.var 0) .prop) := by decide

theorem two_definition_depth : deltaNormalize environment 2 source = some result := by
  simp [source, result, deltaNormalize, environment, Environment.lookupTerm?, lookupTermList?,
    identityDeclaration, propositionDeclaration, parameterDeclaration]

theorem one_definition_depth_fails : deltaNormalize environment 1 source = none := by
  simp [source, deltaNormalize, environment, Environment.lookupTerm?, lookupTermList?,
    identityDeclaration, propositionDeclaration]

/-- The generic native theorem, instantiated on actual unfolding through two
definitions in a mixed plain/prefix library. -/
theorem expanded_native_type :
    inferTerm environment 1 [] result = some (.arr (.var 0) .prop) :=
  native_infer_deltaNormalize checkedDefinitions (by simp) source_lookups source_annotations
    source_inferred two_definition_depth

end DeltaTypingExamples

#print axioms deltaNormalize_formation
#print axioms native_infer_deltaNormalize
#print axioms DeltaTypingExamples.checkedDefinitions
#print axioms DeltaTypingExamples.expanded_native_type
#print axioms DeltaTypingExamples.one_definition_depth_fails

end Mettapedia.Languages.Megalodon.HenkinTermInterpretation
