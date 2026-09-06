import Mettapedia.Languages.Megalodon.MathdataKernel

/-!
# Definition typing, shadowing, and finite delta expansion

Checking a definition against the tail of a raw declaration list does not make
its body well typed after arbitrary declarations have been prepended. The
native lookup operation takes the first matching name, and delta expansion
resolves the body in the final environment. A fresh-name extension preserves
the example below; a shadowing extension changes the unfolded term's type.

Even when every definition body is checked in the final environment, a cycle
can exhaust every finite unfolding bound. Local typing and well-founded
definition dependencies are different conditions.

These are boundaries of the explicit `MathdataKernel.Environment` interface,
not counterexamples to Megalodon's OCaml document checker. In the source
checker, `DocDef` additionally checks normality and computes the declaration's
name from the body's hash; `DocParam` checks an external term/type association.
Neither that content-addressed admission process nor its complete soundness is
modeled by the tail-checking predicate used here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.DefinitionEnvironmentBoundary

open MathdataKernel

/-- Local checks for monomorphic, term-only declaration lists. Definition
bodies are checked against the remaining tail. This predicate imposes neither
name freshness nor the source document checker's hash discipline. -/
inductive TailChecked : List TermDecl → Prop where
  | nil : TailChecked []
  | parameter (name : Name) (type : Tp) (tail : List TermDecl)
      (formed : type.plainWellFormed 0 = true)
      (checked : TailChecked tail) :
      TailChecked ({ name := name, type := type } :: tail)
  | definition (name : Name) (type : Tp) (body : Tm) (tail : List TermDecl)
      (formed : type.plainWellFormed 0 = true)
      (typed : inferTerm { terms := tail } 0 [] body = some type)
      (checked : TailChecked tail) :
      TailChecked ({ name := name, type := type, definition := some body } :: tail)

/-- Every stored definition has a closed plain type, and its body is accepted
at that type with empty term and type-variable contexts in the final environment.
This is a local typing condition, not an acyclicity or admission condition. -/
def ClosedDefinitionsTyped (environment : Environment) : Prop :=
  ∀ declaration ∈ environment.terms, ∀ body,
    declaration.definition = some body →
      declaration.type.plainWellFormed 0 = true ∧
        inferTerm environment 0 [] body = some declaration.type

def propositionParameter : TermDecl :=
  { name := "p", type := .prop }

def aliasDeclaration : TermDecl :=
  { name := "q", type := .prop, definition := some (.named "p") }

def freshParameter : TermDecl :=
  { name := "r", type := .arr .prop .prop }

def shadowParameter : TermDecl :=
  { name := "p", type := .arr .prop .prop }

def parameterEnvironment : Environment :=
  { terms := [propositionParameter] }

def aliasEnvironment : Environment :=
  { terms := [aliasDeclaration, propositionParameter] }

def freshEnvironment : Environment :=
  { terms := [freshParameter, aliasDeclaration, propositionParameter] }

def shadowEnvironment : Environment :=
  { terms := [shadowParameter, aliasDeclaration, propositionParameter] }

theorem alias_body_typed_in_tail :
    inferTerm parameterEnvironment 0 [] (.named "p") = some .prop := by decide

theorem alias_tailChecked : TailChecked aliasEnvironment.terms := by
  exact .definition "q" .prop (.named "p") [propositionParameter] rfl
    alias_body_typed_in_tail (.parameter "p" .prop [] rfl .nil)

theorem fresh_tailChecked : TailChecked freshEnvironment.terms := by
  exact .parameter "r" (.arr .prop .prop) aliasEnvironment.terms rfl alias_tailChecked

theorem shadow_tailChecked : TailChecked shadowEnvironment.terms := by
  exact .parameter "p" (.arr .prop .prop) aliasEnvironment.terms rfl alias_tailChecked

theorem alias_closedDefinitionsTyped : ClosedDefinitionsTyped aliasEnvironment := by
  intro declaration member body definition
  simp only [aliasEnvironment, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · cases definition
    exact ⟨rfl, by decide⟩
  · cases definition

theorem fresh_closedDefinitionsTyped : ClosedDefinitionsTyped freshEnvironment := by
  intro declaration member body definition
  simp only [freshEnvironment, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · cases definition
  · cases definition
    exact ⟨rfl, by decide⟩
  · cases definition

theorem alias_infer :
    inferTerm aliasEnvironment 0 [] (.named "q") = some .prop := by decide

theorem fresh_infer :
    inferTerm freshEnvironment 0 [] (.named "q") = some .prop := by decide

/-- A genuinely new declaration leaves this alias's finite-fuel delta behavior
unchanged, including the zero-fuel failure. -/
theorem fresh_delta_eq (fuel : Nat) :
    deltaNormalize freshEnvironment fuel (.named "q") =
      deltaNormalize aliasEnvironment fuel (.named "q") := by
  cases fuel with
  | zero =>
      simp [deltaNormalize, freshEnvironment, aliasEnvironment, freshParameter,
        aliasDeclaration, propositionParameter, Environment.lookupTerm?, lookupTermList?]
  | succ fuel =>
      cases fuel <;>
        simp [deltaNormalize, freshEnvironment, aliasEnvironment, freshParameter,
          aliasDeclaration, propositionParameter, Environment.lookupTerm?, lookupTermList?]

theorem fresh_delta_succ (fuel : Nat) :
    deltaNormalize freshEnvironment (fuel + 1) (.named "q") = some (.named "p") := by
  cases fuel <;>
    simp [deltaNormalize, freshEnvironment, freshParameter, aliasDeclaration,
      propositionParameter, Environment.lookupTerm?, lookupTermList?]

/-- The positive comparison checks the output's native type, not just the
continued availability of the original named declaration. -/
theorem fresh_unfolded_type :
    inferTerm freshEnvironment 0 [] (.named "p") = some .prop := by decide

theorem shadow_infer :
    inferTerm shadowEnvironment 0 [] (.named "q") = some .prop := by decide

theorem shadow_delta_succ (fuel : Nat) :
    deltaNormalize shadowEnvironment (fuel + 1) (.named "q") = some (.named "p") := by
  cases fuel <;>
    simp [deltaNormalize, shadowEnvironment, shadowParameter, aliasDeclaration,
      propositionParameter, Environment.lookupTerm?, lookupTermList?]

theorem shadow_unfolded_type :
    inferTerm shadowEnvironment 0 [] (.named "p") = some (.arr .prop .prop) := by decide

theorem shadow_unfolded_not_proposition :
    inferTerm shadowEnvironment 0 [] (.named "p") ≠ some .prop := by decide

theorem shadow_not_closedDefinitionsTyped : ¬ ClosedDefinitionsTyped shadowEnvironment := by
  intro checked
  have typed := (checked aliasDeclaration (by simp [shadowEnvironment]) (.named "p") rfl).2
  exact shadow_unfolded_not_proposition typed

/-- Actual tail checks, even at closed plain types, do not imply subject
preservation for delta unfolding in the resulting raw environment. -/
theorem tailChecking_not_delta_subject_preservation :
    ¬ (∀ declarations : List TermDecl, TailChecked declarations →
      ∀ (fuel : Nat) (term result : Tm) (type : Tp),
        inferTerm { terms := declarations } 0 [] term = some type →
        deltaNormalize { terms := declarations } fuel term = some result →
        inferTerm { terms := declarations } 0 [] result = some type) := by
  intro preservation
  exact shadow_unfolded_not_proposition
    (preservation shadowEnvironment.terms shadow_tailChecked 1
      (.named "q") (.named "p") .prop shadow_infer (shadow_delta_succ 0))

def cyclicDeclaration : TermDecl :=
  { name := "p", type := .prop, definition := some (.named "p") }

def cyclicEnvironment : Environment :=
  { terms := [cyclicDeclaration] }

/-- The cycle's body passes native typing in the final environment at a closed
plain type. This does not assert that an ordered document checker accepts it. -/
theorem cyclic_closedDefinitionsTyped : ClosedDefinitionsTyped cyclicEnvironment := by
  intro declaration member body definition
  simp only [cyclicEnvironment, List.mem_singleton] at member
  subst declaration
  cases definition
  exact ⟨rfl, by decide⟩

theorem cyclic_infer :
    inferTerm cyclicEnvironment 0 [] (.named "p") = some .prop := by decide

/-- The same self-reference cannot be checked against its empty declaration
tail. Final-environment local typing is strictly different from this ordered
condition; neither is being identified with full document admission. -/
theorem cyclic_not_tailChecked : ¬ TailChecked cyclicEnvironment.terms := by
  intro checked
  change TailChecked [{ name := "p", type := .prop, definition := some (.named "p") }] at checked
  cases checked with
  | definition name type body tail formed typed checked =>
      simp [inferTerm, Environment.lookupTerm?, lookupTermList?] at typed

/-- Every unfolding merely follows the same definition again, until the finite
bound is exhausted. The native result is failure, not an invented residual term. -/
theorem cyclic_delta_none (fuel : Nat) :
    deltaNormalize cyclicEnvironment fuel (.named "p") = none := by
  induction fuel with
  | zero =>
      simp [deltaNormalize, cyclicEnvironment, cyclicDeclaration,
        Environment.lookupTerm?, lookupTermList?]
  | succ fuel ih =>
      simpa [deltaNormalize, cyclicEnvironment, cyclicDeclaration,
        Environment.lookupTerm?, lookupTermList?] using ih

theorem cyclic_no_success :
    ¬ ∃ (fuel : Nat) (result : Tm),
      deltaNormalize cyclicEnvironment fuel (.named "p") = some result := by
  rintro ⟨fuel, result, success⟩
  rw [cyclic_delta_none] at success
  cases success

/-- Final-environment definition typing alone cannot supply a successful finite
delta bound, even for a natively well-typed input. -/
theorem closedDefinitionTyping_not_deltaTermination :
    ¬ (∀ environment : Environment, ClosedDefinitionsTyped environment →
      ∀ (term : Tm) (type : Tp),
        inferTerm environment 0 [] term = some type →
        ∃ (fuel : Nat) (result : Tm), deltaNormalize environment fuel term = some result) := by
  intro termination
  exact cyclic_no_success
    (termination cyclicEnvironment cyclic_closedDefinitionsTyped (.named "p") .prop cyclic_infer)

#print axioms fresh_delta_eq
#print axioms fresh_closedDefinitionsTyped
#print axioms tailChecking_not_delta_subject_preservation
#print axioms cyclic_closedDefinitionsTyped
#print axioms cyclic_not_tailChecked
#print axioms cyclic_delta_none
#print axioms closedDefinitionTyping_not_deltaTermination

end Mettapedia.Languages.Megalodon.DefinitionEnvironmentBoundary
