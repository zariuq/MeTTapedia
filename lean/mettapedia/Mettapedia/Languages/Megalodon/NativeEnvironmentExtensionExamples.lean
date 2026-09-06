import Mettapedia.Languages.Megalodon.NativeProofEnvironment

/-!
# Fresh extensions and transitive native environment dependencies

A closed four-name support protects a nested definition chain under a genuinely
fresh extension. Agreement on the names written directly in the input does not:
changing a hidden definition preserves those lookups and their types but changes
the native proof verdict. The generic comparison covers every supported proof,
context and fuel bound, not only the accepting example.

These examples concern the actual raw native environment interface. Bare aliases
are not claimed to be an OCaml document transcript: `DocDef` skips bare `TmH`
bodies. The opacity example does mirror a source admission operation: `DocParam`
checks an existing name's type and prepends an opaque declaration, while
`def_of_tmh_r` stops at the first matching declaration even when it is opaque.
Content-addressed definition naming therefore does not itself imply an exact
operational frame law. No document-checker soundness claim is made here.

The final controls use an existing prefix-polymorphic native proof, including
type and term application. Filling an absent known-proposition lookup changes
rejection to acceptance, explaining why exact agreement retains absences too.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativeEnvironmentExtensionExamples

open MathdataKernel NativeSupport EnvironmentDependency NativeProofEnvironment

def source : Environment :=
  { terms :=
      [{ name := "a", type := .prop, definition := some (.named "b") },
       { name := "b", type := .prop, definition := some (.named "p") },
       { name := "p", type := .prop, definition := some (.named "r") },
       { name := "r", type := .prop }] }

def support : Support :=
  {.termName "a", .termName "b", .termName "p", .termName "r"}

def freshDeclaration : TermDecl := { name := "fresh", type := .prop }

def fresh : Environment := { source with terms := freshDeclaration :: source.terms }

theorem fresh_name_absent : source.lookupTerm? "fresh" = none := by decide

theorem fresh_name_present : fresh.lookupTerm? "fresh" = some freshDeclaration := by decide

theorem source_closed : Closed source support where
  body := by
    intro name declaration body member lookup definition
    have names : name = "a" ∨ name = "b" ∨ name = "p" ∨ name = "r" := by
      simpa [support] using member
    rcases names with rfl | rfl | rfl | rfl <;>
      simp [source, Environment.lookupTerm?, lookupTermList?] at lookup <;>
      cases lookup <;> cases definition <;> simp [termSupport, support]
  known := by
    intro name proposition member
    simp [support] at member

theorem fresh_agreement : Agreement source fresh support :=
  agreement_prepend source support [freshDeclaration] []
    (by simp [freshDeclaration, support]) (by simp)

/-- Every supported proof retains its exact verdict under this extension. -/
theorem fresh_checkProof_eq {fuel typeDepth : Nat}
    {termContext : List Tp} {proofContext : List Tm} {proof : Pf} {goal : Tm}
    (contextSupported : ContextSupported support proofContext)
    (proofSupported : proofSupport proof ⊆ support)
    (goalSupported : termSupport goal ⊆ support) :
    checkProof fresh fuel typeDepth termContext proofContext proof goal =
      checkProof source fuel typeDepth termContext proofContext proof goal :=
  checkProof_frame fresh_agreement source_closed contextSupported proofSupported goalSupported

def proof : Pf := .proofLam (.named "a") (.hyp 0)

def goal : Tm := .imp (.named "a") (.named "r")

/-- An executable finite request check validates the reusable environment comparison. -/
theorem fresh_request_checked : proofFrameCheck source fresh support [] proof goal = true := by
  decide

theorem fresh_checked_verdict_eq (fuel typeDepth : Nat) (termContext : List Tp) :
    checkProof fresh fuel typeDepth termContext [] proof goal =
      checkProof source fuel typeDepth termContext [] proof goal :=
  checkProof_frame_of_check fresh_request_checked fuel typeDepth termContext

theorem proof_supported : proofSupport proof ⊆ support := by decide

theorem goal_supported : termSupport goal ⊆ support := by decide

theorem source_accepts : checkProof source 4 0 [] [] proof goal = true := by
  simp [source, proof, goal, checkProof, checkNormalizedProof, inferProof, inferTerm,
    normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Environment.lookupTerm?, lookupTermList?]

theorem fresh_accepts : checkProof fresh 4 0 [] [] proof goal = true := by
  rw [fresh_checkProof_eq (contextSupported_nil support) proof_supported goal_supported]
  exact source_accepts

theorem source_insufficient_fuel : checkProof source 2 0 [] [] proof goal = false := by
  simp [source, goal, checkProof, normalize, deltaNormalize,
    Environment.lookupTerm?, lookupTermList?]

theorem fresh_insufficient_fuel : checkProof fresh 2 0 [] [] proof goal = false := by
  rw [fresh_checkProof_eq (contextSupported_nil support) proof_supported goal_supported]
  exact source_insufficient_fuel

def shadowDeclaration : TermDecl :=
  { name := "p", type := .prop,
    definition := some (.imp (.named "r") (.named "r")) }

def shadow : Environment := { source with terms := shadowDeclaration :: source.terms }

def directSupport : Support := {.termName "a", .termName "r"}

/-- Even exact direct-input agreement misses the changed transitive dependency. -/
theorem shadow_direct_agreement : Agreement source shadow directSupport where
  term := by
    intro name member
    have names : name = "a" ∨ name = "r" := by simpa [directSupport] using member
    rcases names with rfl | rfl <;> rfl
  primitive := by
    intro index member
    simp [directSupport] at member
  known := by
    intro name member
    simp [directSupport] at member

theorem direct_inputs_supported :
    proofSupport proof ⊆ directSupport ∧ termSupport goal ⊆ directSupport := by decide

theorem direct_support_not_closed : ¬ Closed source directSupport := by
  intro closed
  have bodySupported := closed.body (name := "a") (by simp [directSupport]) rfl rfl
  have outside : Dependency.termName "b" ∈ directSupport :=
    bodySupported (by simp [termSupport])
  simp [directSupport] at outside

theorem shadow_preserves_input_typing :
    inferTerm shadow 0 [] (.named "a") = inferTerm source 0 [] (.named "a") ∧
    inferTerm shadow 0 [] goal = inferTerm source 0 [] goal := by decide

theorem source_delta : deltaNormalize source 3 (.named "a") = some (.named "r") := by
  simp [source, deltaNormalize, Environment.lookupTerm?, lookupTermList?]

theorem shadow_delta :
    deltaNormalize shadow 3 (.named "a") = some (.imp (.named "r") (.named "r")) := by
  simp [shadow, shadowDeclaration, source, deltaNormalize,
    Environment.lookupTerm?, lookupTermList?]

theorem shadow_rejects : checkProof shadow 4 0 [] [] proof goal = false := by
  simp [shadow, shadowDeclaration, source, proof, goal, checkProof, checkNormalizedProof,
    inferProof, inferTerm, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Environment.lookupTerm?, lookupTermList?]

theorem shadow_not_agreement : ¬ Agreement source shadow support := by
  intro agreement
  have lookup := agreement.term (name := "p") (by simp [support])
  simp [shadow, shadowDeclaration, source, Environment.lookupTerm?, lookupTermList?] at lookup

theorem shadow_request_rejected : proofFrameCheck source shadow support [] proof goal = false := by
  decide

/-- Direct-name agreement passes, but the manifest rejects its missing dependency closure. -/
theorem incomplete_request_rejected :
    proofFrameCheck source fresh directSupport [] proof goal = false := by decide

/-- This operation preserves a declared type while hiding its old definition. -/
def opaqueEnvironment : Environment :=
  { source with terms := { name := "p", type := .prop } :: source.terms }

theorem opaque_preserves_selected_type :
    inferTerm opaqueEnvironment 0 [] (.named "p") = inferTerm source 0 [] (.named "p") := by decide

theorem opaque_delta : deltaNormalize opaqueEnvironment 3 (.named "a") = some (.named "p") := by
  simp [opaqueEnvironment, source, deltaNormalize, Environment.lookupTerm?, lookupTermList?]

theorem opaque_rejects : checkProof opaqueEnvironment 4 0 [] [] proof goal = false := by
  simp [opaqueEnvironment, source, proof, goal, checkProof, checkNormalizedProof, inferProof,
    inferTerm, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Environment.lookupTerm?, lookupTermList?]

/-! ## Known propositions can hide the same transitive term dependencies -/

def knownProposition : Tm := .imp (.named "a") (.named "a")

def withKnown (environment : Environment) : Environment :=
  { environment with known := [{ name := "identity", proposition := knownProposition }] }

def knownSupport : Support := insert (.knownName "identity") support

/-- The stored proposition has an actual native proof in the source environment. -/
theorem known_proposition_proved : checkProof source 4 0 [] [] proof knownProposition = true := by
  simp [source, proof, knownProposition, checkProof, checkNormalizedProof, inferProof,
    inferTerm, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Environment.lookupTerm?, lookupTermList?]

theorem known_source_closed : Closed (withKnown source) knownSupport where
  body := by
    intro name declaration body member lookup definition
    have termMember : Dependency.termName name ∈ support := by
      simpa [knownSupport] using member
    exact (source_closed.body termMember lookup definition).trans (Finset.subset_insert _ _)
  known := by
    intro name proposition member lookup
    have nameEqual : name = "identity" := by simpa [knownSupport, support] using member
    subst name
    simp [withKnown, Environment.lookupKnown?, lookupKnownList?] at lookup
    subst proposition
    simp [knownProposition, termSupport, knownSupport, support]

theorem known_fresh_agreement : Agreement (withKnown source) (withKnown fresh) knownSupport where
  term := by
    intro name member
    exact fresh_agreement.term (by simpa [knownSupport] using member)
  primitive := by
    intro index member
    simp [knownSupport, support] at member
  known := by
    intro name _member
    rfl

theorem known_fresh_infer_eq (fuel : Nat) :
    inferProof (withKnown fresh) fuel 0 [] [] (.known "identity") =
      inferProof (withKnown source) fuel 0 [] [] (.known "identity") :=
  inferProof_frame known_fresh_agreement known_source_closed
    (contextSupported_nil knownSupport) (by simp [proofSupport, knownSupport])

/-- The unchanged known lookup is insufficient when its referenced definition changes. -/
theorem known_shadow_changes_inference :
    inferProof (withKnown source) 4 0 [] [] (.known "identity") ≠
      inferProof (withKnown shadow) 4 0 [] [] (.known "identity") := by
  simp [withKnown, knownProposition, source, shadow, shadowDeclaration, inferProof,
    normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Environment.lookupKnown?, lookupKnownList?, Environment.lookupTerm?, lookupTermList?]

/-! ## Prefix-polymorphic known proofs and exact absence -/

def polymorphicSupport : Support := {.knownName polymorphicReuseName}

def polymorphicFresh : Environment :=
  { polymorphicReuseEnvironment with terms := [freshDeclaration] }

theorem polymorphic_closed : Closed polymorphicReuseEnvironment polymorphicSupport where
  body := by
    intro name declaration body member
    simp [polymorphicSupport] at member
  known := by
    intro name proposition member lookup
    have same : name = polymorphicReuseName := by simpa [polymorphicSupport] using member
    subst name
    simp [polymorphicReuseEnvironment, Environment.lookupKnown?, lookupKnownList?] at lookup
    subst proposition
    simp [polymorphicReuseGoal, polymorphicReuseBody, termSupport]

theorem polymorphic_fresh_agreement :
    Agreement polymorphicReuseEnvironment polymorphicFresh polymorphicSupport where
  term := by
    intro name member
    simp [polymorphicSupport] at member
  primitive := by
    intro index member
    simp [polymorphicSupport] at member
  known := by
    intro name _member
    rfl

theorem polymorphic_proof_supported :
    proofSupport polymorphicReuseProof ⊆ polymorphicSupport := by
  simp [polymorphicReuseProof, proofSupport, termSupport, polymorphicSupport]

theorem polymorphic_fresh_infer_eq (fuel : Nat) :
    inferProof polymorphicFresh fuel 0 [] [] polymorphicReuseProof =
      inferProof polymorphicReuseEnvironment fuel 0 [] [] polymorphicReuseProof :=
  inferProof_frame polymorphic_fresh_agreement polymorphic_closed
    (contextSupported_nil polymorphicSupport) polymorphic_proof_supported

theorem polymorphic_fresh_accepts :
    inferProof polymorphicFresh 16 0 [] [] polymorphicReuseProof =
      some polymorphicReuseGoal := by
  rw [polymorphic_fresh_infer_eq]
  exact polymorphic_known_reuse_accepted

theorem polymorphic_request_checked :
    proofFrameCheck polymorphicReuseEnvironment polymorphicFresh polymorphicSupport []
      polymorphicReuseProof polymorphicReuseGoal = true := by decide

def filledKnown : Environment :=
  { polymorphicReuseEnvironment with known :=
      { name := "not-an-admitted-proposition", proposition := polymorphicReuseGoal } ::
        polymorphicReuseEnvironment.known }

theorem known_previously_absent :
    polymorphicReuseEnvironment.lookupKnown? "not-an-admitted-proposition" = none := by decide

theorem filled_known_accepts :
    inferProof filledKnown 16 0 [] [] polymorphicUnknownReuseProof =
      some polymorphicReuseGoal := by
  simp [inferProof, filledKnown, polymorphicUnknownReuseProof,
    polymorphicReuseGoal, polymorphicReuseBody, polymorphicReuseType,
    Environment.lookupKnown?, lookupKnownList?, inferTerm, normalize,
    deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.typeInstantiate,
    Tm.typeInstantiateAt, Tm.instantiate, Tm.instantiateAt, Tm.shift,
    Tp.instantiateAt, Tp.shift, Tp.plainWellFormed]

theorem filling_absence_changes_inference :
    inferProof filledKnown 16 0 [] [] polymorphicUnknownReuseProof ≠
      inferProof polymorphicReuseEnvironment 16 0 [] [] polymorphicUnknownReuseProof := by
  rw [filled_known_accepts, polymorphic_unknown_reuse_rejected]
  simp

theorem filled_not_agreement_on_proof :
    ¬ Agreement polymorphicReuseEnvironment filledKnown
      (proofSupport polymorphicUnknownReuseProof) := by
  intro agreement
  have lookup := agreement.known (name := "not-an-admitted-proposition")
    (by simp [polymorphicUnknownReuseProof, proofSupport, termSupport])
  rw [known_previously_absent] at lookup
  simp [filledKnown, Environment.lookupKnown?, lookupKnownList?] at lookup

theorem filled_request_rejected :
    proofFrameCheck polymorphicReuseEnvironment filledKnown
      (proofSupport polymorphicUnknownReuseProof) []
      polymorphicUnknownReuseProof polymorphicReuseGoal = false := by decide

#print axioms source_closed
#print axioms fresh_agreement
#print axioms fresh_checkProof_eq
#print axioms fresh_request_checked
#print axioms fresh_checked_verdict_eq
#print axioms fresh_accepts
#print axioms fresh_insufficient_fuel
#print axioms direct_support_not_closed
#print axioms shadow_rejects
#print axioms shadow_request_rejected
#print axioms incomplete_request_rejected
#print axioms opaque_rejects
#print axioms known_source_closed
#print axioms known_fresh_infer_eq
#print axioms known_shadow_changes_inference
#print axioms polymorphic_fresh_infer_eq
#print axioms polymorphic_fresh_accepts
#print axioms polymorphic_request_checked
#print axioms filling_absence_changes_inference
#print axioms filled_request_rejected

end Mettapedia.Languages.Megalodon.NativeEnvironmentExtensionExamples
