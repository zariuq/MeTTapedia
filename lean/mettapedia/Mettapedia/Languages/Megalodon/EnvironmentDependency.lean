import Mettapedia.Languages.Megalodon.NativeSupport

/-!
# Native computation depends on a closed set of environment lookups

Agreement is local to a finite support and includes absent lookups. Closure
follows selected definition bodies and known propositions, so a change hidden
behind an unchanged declaration cannot invalidate the comparison. Unrelated
declarations may be added without renaming the old terms.

These are frame theorems for the existing native operations, not an additional
evaluator or an assertion that new declarations are logically sound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.EnvironmentDependency

open MathdataKernel NativeSupport

/-- Exact agreement on every environment query named by the support. -/
structure Agreement (source target : Environment) (support : Support) : Prop where
  term : ∀ {name}, Dependency.termName name ∈ support →
    target.lookupTerm? name = source.lookupTerm? name
  primitive : ∀ {index}, Dependency.primitive index ∈ support →
    target.primitives[index]? = source.primitives[index]?
  known : ∀ {name}, Dependency.knownName name ∈ support →
    target.lookupKnown? name = source.lookupKnown? name

/-- All selected declarations' bodies remain inside the same dependency set. -/
structure Closed (environment : Environment) (support : Support) : Prop where
  body : ∀ {name declaration body}, Dependency.termName name ∈ support →
    environment.lookupTerm? name = some declaration →
    declaration.definition = some body → termSupport body ⊆ support
  known : ∀ {name proposition}, Dependency.knownName name ∈ support →
    environment.lookupKnown? name = some proposition → termSupport proposition ⊆ support

variable {source target third : Environment} {support smaller : Support}

theorem Agreement.refl (environment : Environment) (support : Support) :
    Agreement environment environment support := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem Agreement.symm (agreement : Agreement source target support) :
    Agreement target source support :=
  ⟨fun member => (agreement.term member).symm,
   fun member => (agreement.primitive member).symm,
   fun member => (agreement.known member).symm⟩

theorem Agreement.trans (first : Agreement source target support)
    (second : Agreement target third support) : Agreement source third support :=
  ⟨fun member => (second.term member).trans (first.term member),
   fun member => (second.primitive member).trans (first.primitive member),
   fun member => (second.known member).trans (first.known member)⟩

theorem Agreement.mono (agreement : Agreement source target support)
    (inclusion : smaller ⊆ support) : Agreement source target smaller :=
  ⟨fun member => agreement.term (inclusion member),
   fun member => agreement.primitive (inclusion member),
   fun member => agreement.known (inclusion member)⟩

private theorem lookupTermList_append_of_fresh (added suffix : List TermDecl)
    (name : Name) (fresh : ∀ declaration ∈ added, declaration.name ≠ name) :
    lookupTermList? (added ++ suffix) name = lookupTermList? suffix name := by
  induction added with
  | nil => rfl
  | cons declaration added ih =>
      have different := fresh declaration (by simp)
      simp only [List.cons_append, lookupTermList?, beq_iff_eq, different, ↓reduceIte]
      exact ih (fun next member => fresh next (by simp [member]))

private theorem lookupKnownList_append_of_fresh (added suffix : List KnownDecl)
    (name : Name) (fresh : ∀ declaration ∈ added, declaration.name ≠ name) :
    lookupKnownList? (added ++ suffix) name = lookupKnownList? suffix name := by
  induction added with
  | nil => rfl
  | cons declaration added ih =>
      have different := fresh declaration (by simp)
      simp only [List.cons_append, lookupKnownList?, beq_iff_eq, different, ↓reduceIte]
      exact ih (fun next member => fresh next (by simp [member]))

/-- New declarations whose keys avoid the protected support preserve all its
lookups, including protected names that were absent. Freshness is relative to
the support, not merely to the previously declared names. -/
theorem agreement_prepend (source : Environment) (support : Support)
    (terms : List TermDecl) (known : List KnownDecl)
    (termsFresh : ∀ declaration ∈ terms, Dependency.termName declaration.name ∉ support)
    (knownFresh : ∀ declaration ∈ known, Dependency.knownName declaration.name ∉ support) :
    Agreement source
      { source with terms := terms ++ source.terms, known := known ++ source.known }
      support where
  term := by
    intro name member
    apply lookupTermList_append_of_fresh
    intro declaration present equal
    apply termsFresh declaration present
    simpa only [equal] using member
  primitive _ := rfl
  known := by
    intro name member
    apply lookupKnownList_append_of_fresh
    intro declaration present equal
    apply knownFresh declaration present
    simpa only [equal] using member

/-- Exact lookup agreement transports the dependency-closure condition. -/
theorem Closed.transport (closed : Closed source support)
    (agreement : Agreement source target support) : Closed target support where
  body member lookup definition :=
    closed.body member ((agreement.term member).symm.trans lookup) definition
  known member lookup := closed.known member ((agreement.known member).symm.trans lookup)

/-- Native type synthesis does not inspect declaration bodies. -/
theorem inferTerm_frame (agreement : Agreement source target support)
    {term : Tm} {typeDepth : Nat} {termContext : List Tp}
    (supported : termSupport term ⊆ support) :
    inferTerm target typeDepth termContext term =
      inferTerm source typeDepth termContext term := by
  induction term generalizing typeDepth termContext with
  | named name =>
      simpa only [inferTerm] using congrArg (Option.map TermDecl.type)
        (agreement.term (supported (by simp [termSupport])))
  | prim index => exact agreement.primitive (supported (by simp [termSupport]))
  | app function argument ihf iha =>
      simp only [termSupport, Finset.union_subset_iff] at supported
      simp only [inferTerm, ihf supported.1, iha supported.2]
  | imp domain codomain ihd ihc =>
      simp only [termSupport, Finset.union_subset_iff] at supported
      simp only [inferTerm, ihd supported.1, ihc supported.2]
  | lam type body ih => simp only [inferTerm, ih supported]
  | all type body ih => simp only [inferTerm, ih supported]
  | typeApp function type ih => simp only [inferTerm, ih supported]
  | typeLam body ih => simp only [inferTerm, ih supported]
  | db | typeAll => rfl

/-- Prefix proposition checking is stable under the same local agreement. -/
theorem checkProposition_frame (agreement : Agreement source target support)
    {term : Tm} {typeDepth : Nat} {termContext : List Tp}
    (supported : termSupport term ⊆ support) :
    checkProposition target typeDepth termContext term =
      checkProposition source typeDepth termContext term := by
  induction term generalizing typeDepth termContext with
  | typeAll body ih => exact ih supported
  | _ => simp only [checkProposition, inferTerm_frame agreement supported]

/-- Definition expansion stays inside a dependency-closed support. -/
theorem deltaNormalize_support (closed : Closed source support)
    {term result : Tm} {fuel : Nat} (supported : termSupport term ⊆ support)
    (success : deltaNormalize source fuel term = some result) :
    termSupport result ⊆ support := by
  induction fuel generalizing term result with
  | zero =>
      induction term generalizing result with
      | named name =>
          simp only [deltaNormalize] at success
          cases lookup : source.lookupTerm? name with
          | none =>
              have equal : Tm.named name = result := by simpa [lookup] using success
              subst result
              exact supported
          | some declaration =>
              rcases declaration with ⟨name', type, definition⟩
              cases definition with
              | none =>
                  have equal : Tm.named name = result := by simpa [lookup] using success
                  subst result
                  exact supported
              | some body => simp [lookup] at success
      | app function argument ihf iha | imp function argument ihf iha =>
          simp only [termSupport, Finset.union_subset_iff] at supported
          cases leftSuccess : deltaNormalize source 0 function with
          | none => simp [deltaNormalize, leftSuccess] at success
          | some left =>
              cases rightSuccess : deltaNormalize source 0 argument with
              | none => simp [deltaNormalize, leftSuccess, rightSuccess] at success
              | some right =>
                  simp [deltaNormalize, leftSuccess, rightSuccess] at success
                  subst result
                  exact Finset.union_subset (ihf supported.1 leftSuccess)
                    (iha supported.2 rightSuccess)
      | lam type body ih | all type body ih | typeApp body type ih =>
          cases bodySuccess : deltaNormalize source 0 body with
          | none => simp [deltaNormalize, bodySuccess] at success
          | some bodyResult =>
              simp [deltaNormalize, bodySuccess] at success
              subst result
              exact ih (result := bodyResult) supported bodySuccess
      | typeLam body ih | typeAll body ih =>
          cases bodySuccess : deltaNormalize source 0 body with
          | none => simp [deltaNormalize, bodySuccess] at success
          | some bodyResult =>
              simp [deltaNormalize, bodySuccess] at success
              subst result
              exact ih (result := bodyResult) supported bodySuccess
      | db | prim =>
          simp only [deltaNormalize, Option.some.injEq] at success
          subst result
          exact supported
  | succ fuel ihFuel =>
      induction term generalizing result with
      | named name =>
          cases lookup : source.lookupTerm? name with
          | none =>
              have equal : Tm.named name = result := by simpa [deltaNormalize, lookup] using success
              subst result
              exact supported
          | some declaration =>
              rcases declaration with ⟨name', type, definition⟩
              cases definition with
              | none =>
                  have equal : Tm.named name = result := by simpa [deltaNormalize, lookup] using success
                  subst result
                  exact supported
              | some body =>
                  exact ihFuel (closed.body (supported (by simp [termSupport])) lookup rfl)
                    (by simpa [deltaNormalize, lookup] using success)
      | app function argument ihf iha | imp function argument ihf iha =>
          simp only [termSupport, Finset.union_subset_iff] at supported
          cases leftSuccess : deltaNormalize source (fuel + 1) function with
          | none => simp [deltaNormalize, leftSuccess] at success
          | some left =>
              cases rightSuccess : deltaNormalize source (fuel + 1) argument with
              | none => simp [deltaNormalize, leftSuccess, rightSuccess] at success
              | some right =>
                  simp [deltaNormalize, leftSuccess, rightSuccess] at success
                  subst result
                  exact Finset.union_subset (ihf supported.1 leftSuccess)
                    (iha supported.2 rightSuccess)
      | lam type body ih | all type body ih | typeApp body type ih =>
          cases bodySuccess : deltaNormalize source (fuel + 1) body with
          | none => simp [deltaNormalize, bodySuccess] at success
          | some bodyResult =>
              simp [deltaNormalize, bodySuccess] at success
              subst result
              exact ih (result := bodyResult) supported bodySuccess
      | typeLam body ih | typeAll body ih =>
          cases bodySuccess : deltaNormalize source (fuel + 1) body with
          | none => simp [deltaNormalize, bodySuccess] at success
          | some bodyResult =>
              simp [deltaNormalize, bodySuccess] at success
              subst result
              exact ih (result := bodyResult) supported bodySuccess
      | db | prim =>
          simp only [deltaNormalize, Option.some.injEq] at success
          subst result
          exact supported

/-- Exact local framing, including fuel exhaustion, for native definition unfolding. -/
theorem deltaNormalize_frame (agreement : Agreement source target support)
    (closed : Closed source support) {term : Tm} {fuel : Nat}
    (supported : termSupport term ⊆ support) :
    deltaNormalize target fuel term = deltaNormalize source fuel term := by
  induction fuel generalizing term with
  | zero =>
      induction term with
      | named name =>
          simp only [deltaNormalize,
            agreement.term (name := name) (supported (by simp [termSupport]))]
      | app function argument ihf iha | imp function argument ihf iha =>
          simp only [termSupport, Finset.union_subset_iff] at supported
          simp only [deltaNormalize, ihf supported.1, iha supported.2]
      | lam type body ih | all type body ih | typeApp body type ih =>
          simp only [deltaNormalize, ih supported]
      | typeLam body ih | typeAll body ih => simp only [deltaNormalize, ih supported]
      | db | prim => simp only [deltaNormalize]
  | succ fuel ihFuel =>
      induction term with
      | named name =>
          simp only [deltaNormalize,
            agreement.term (name := name) (supported (by simp [termSupport]))]
          cases lookup : source.lookupTerm? name with
          | none => rfl
          | some declaration =>
              rcases declaration with ⟨name', type, definition⟩
              cases definition with
              | none => rfl
              | some body =>
                  exact ihFuel (closed.body (supported (by simp [termSupport])) lookup rfl)
      | app function argument ihf iha | imp function argument ihf iha =>
          simp only [termSupport, Finset.union_subset_iff] at supported
          simp only [deltaNormalize, ihf supported.1, iha supported.2]
      | lam type body ih | all type body ih | typeApp body type ih =>
          simp only [deltaNormalize, ih supported]
      | typeLam body ih | typeAll body ih => simp only [deltaNormalize, ih supported]
      | db | prim => simp only [deltaNormalize]

/-- Beta/eta reduction introduces no new environment query after delta expansion. -/
theorem normalize_support (closed : Closed source support)
    {term result : Tm} {fuel : Nat} (supported : termSupport term ⊆ support)
    (success : normalize source fuel term = some result) :
    termSupport result ⊆ support := by
  obtain ⟨expanded, expansion, normalized⟩ := Option.bind_eq_some_iff.mp success
  exact (termSupport_normalize_subset normalized).trans
    (deltaNormalize_support closed supported expansion)

/-- The result of the existing native normalization pipeline is unchanged. -/
theorem normalize_frame (agreement : Agreement source target support)
    (closed : Closed source support) {term : Tm} {fuel : Nat}
    (supported : termSupport term ⊆ support) :
    normalize target fuel term = normalize source fuel term := by
  simp only [normalize, deltaNormalize_frame agreement closed supported]

#print axioms Closed.transport
#print axioms agreement_prepend
#print axioms inferTerm_frame
#print axioms checkProposition_frame
#print axioms deltaNormalize_support
#print axioms deltaNormalize_frame
#print axioms normalize_support
#print axioms normalize_frame

end Mettapedia.Languages.Megalodon.EnvironmentDependency
