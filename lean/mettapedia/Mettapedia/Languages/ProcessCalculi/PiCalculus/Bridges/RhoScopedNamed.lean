import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredSemantics

/-!
# Persistent named pi receivers realized by reflective rho servers

Only the persistent-server clause is replaced: its request handler uses the
maintained restriction- and replication-free compiler. The source's authored
persistent communication releases the capture-avoiding named substitution;
two actual rho communications release the same compiled continuation while
retaining the waiting server. A separate one-step initialization installs it.

The maintained communication safety hypotheses remain explicit. These are
selected execution blocks; arbitrary target contexts can interfere with the
private stored-code channel and require a separate observer contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedNamed

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpoint
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution

open private rhoNoLiteralQuote rhoNoLiteralQuoteList encode_rf_rhoNoLiteralQuote
  rhoNoLiteralQuote_closeFVar from
  Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation

private theorem normalize_name_quoteFree
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free bound name)
    (unquoted : rhoNoLiteralQuote name = true) : semanticNormalizeName name = name := by
  cases typed with
  | bvar _ | fvar _ => rfl
  | quote _ => simp [rhoNoLiteralQuote, rhoReflectivePresentation] at unquoted

mutual
  private theorem normalize_proc_quoteFree
      {free : FreeSortContext} {bound : List String} {process : Pattern}
      (typed : ProcWellSorted rhoReflectivePresentation free bound process)
      (unquoted : rhoNoLiteralQuote process = true) :
      semanticNormalizeProc process = process := by
    cases typed with
    | bvar _ | fvar _ | unit => rfl
    | drop nameTyped =>
        rename_i name
        have nameFree : rhoNoLiteralQuote name = true := by
          simpa [rhoNoLiteralQuote, rhoNoLiteralQuoteList, rhoReflectivePresentation] using unquoted
        simp [semanticNormalizeProc, rhoReflectivePresentation,
          normalize_name_quoteFree nameTyped nameFree]
    | output channelTyped payloadTyped =>
        rename_i channel payload
        have parts : rhoNoLiteralQuote channel = true ∧ rhoNoLiteralQuote payload = true := by
          simpa [rhoNoLiteralQuote, rhoNoLiteralQuoteList, rhoReflectivePresentation] using unquoted
        simp [semanticNormalizeProc, rhoReflectivePresentation,
          normalize_name_quoteFree channelTyped parts.1,
          normalize_proc_quoteFree payloadTyped parts.2]
    | input channelTyped bodyTyped =>
        rename_i channel body
        have parts : rhoNoLiteralQuote channel = true ∧ rhoNoLiteralQuote body = true := by
          simpa [rhoNoLiteralQuote, rhoNoLiteralQuoteList, rhoReflectivePresentation] using unquoted
        simp [semanticNormalizeProc, rhoReflectivePresentation,
          normalize_name_quoteFree channelTyped parts.1,
          normalize_proc_quoteFree bodyTyped parts.2]
    | parallel processesTyped =>
        rename_i processes
        have allFree : rhoNoLiteralQuoteList processes = true := unquoted
        simp [semanticNormalizeProc, rhoReflectivePresentation,
          normalize_list_quoteFree processesTyped allFree]

  private theorem normalize_list_quoteFree
      {free : FreeSortContext} {bound : List String} {processes : List Pattern}
      (typed : ProcListWellSorted rhoReflectivePresentation free bound processes)
      (unquoted : rhoNoLiteralQuoteList processes = true) :
      semanticNormalizeProcList processes = processes := by
    cases typed with
    | nil => rfl
    | cons processTyped processesTyped =>
        simp only [rhoNoLiteralQuoteList, Bool.and_eq_true] at unquoted
        simp [semanticNormalizeProcList,
          normalize_proc_quoteFree processTyped unquoted.1,
          normalize_list_quoteFree processesTyped unquoted.2]
end

/-- Every named source channel has the authored rho name sort. -/
def atomicChannel (name : String) : Channel rhoAtomicNameContext where
  term := .fvar name
  typed := .fvar rfl
  safe := rfl
  normalized := rfl

/-- The request binder closes the actual maintained compilation of the body. -/
def namedHandler {body : Process} (free : RestrictionFree body)
    (binder namespaceName valueName : String) : Handler rhoAtomicNameContext where
  term := closeFVar 0 binder (encode body namespaceName valueName)
  typed := close_encode_procWellSorted free binder namespaceName valueName
  safe := close_encode_binderSafe free binder namespaceName valueName
  normalized := normalize_proc_quoteFree
    (close_encode_procWellSorted free binder namespaceName valueName)
    (by rw [rhoNoLiteralQuote_closeFVar]; exact encode_rf_rhoNoLiteralQuote free _ _)

/-- The installed persistent receiver uses only authored core rho syntax. -/
def namedServer {body : Process} (free : RestrictionFree body)
    (self channel binder namespaceName valueName : String) : Pattern :=
  GuardedReplication.idle (.fvar self) (.fvar channel)
    (namedHandler free binder namespaceName valueName).term

theorem namedServer_typed {body : Process} (free : RestrictionFree body)
    (self channel binder namespaceName valueName : String) :
    ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext []
      (namedServer free self channel binder namespaceName valueName) :=
  idle_typed (atomicChannel self) (atomicChannel channel)
    (namedHandler free binder namespaceName valueName)

/-- The actual second endpoint is the retained server beside the compilation
of named capture-avoiding substitution. -/
theorem named_request_reduces {body : Process} (free : RestrictionFree body)
    (self channel binder datum namespaceName valueName : String)
    (distinct : binder ≠ datum) (convention : BarendregtFor binder datum body) :
    Nonempty (ReducesN 2
      (parallel [send (.fvar channel) (.apply "PDrop" [.fvar datum]),
        namedServer free self channel binder namespaceName valueName])
      (parallel [namedServer free self channel binder namespaceName valueName,
        encode (body.substitute binder datum) namespaceName valueName])) := by
  obtain ⟨path⟩ := request_reduces (atomicChannel self) (atomicChannel channel)
    (namedHandler free binder namespaceName valueName) (.apply "PDrop" [.fvar datum])
  have continuation := contractum_equations free binder datum namespaceName valueName
    distinct convention
  have endpoint : RhoCalculus.StructuralCongruence
      (parallel [namedServer free self channel binder namespaceName valueName,
        semanticCommSubst (namedHandler free binder namespaceName valueName).term
          (.apply "PDrop" [.fvar datum])])
      (parallel [namedServer free self channel binder namespaceName valueName,
        encode (body.substitute binder datum) namespaceName valueName]) := by
    refine .par_cong _ _ rfl ?_
    intro index firstBound secondBound
    have choices : index = 0 ∨ index = 1 := by simp at firstBound; omega
    rcases choices with rfl | rfl
    · exact .refl _
    · exact continuation
  exact ⟨path.transport (.refl _) endpoint⟩

/-- The same endpoint comparison holds for the real authored matcher followed
by the canonical section, with the intermediate state explicitly retained. -/
theorem named_request_canonical {body : Process} (free : RestrictionFree body)
    (self channel binder datum namespaceName valueName : String)
    (distinct : binder ≠ datum) (convention : BarendregtFor binder datum body) :
    ∃ intermediate,
      CanonicalFiring
        (Canonical.canonicalize
          (parallel [send (.fvar channel) (.apply "PDrop" [.fvar datum]),
            namedServer free self channel binder namespaceName valueName])) intermediate ∧
      CanonicalFiring intermediate
        (Canonical.canonicalize
          (parallel [namedServer free self channel binder namespaceName valueName,
            encode (body.substitute binder datum) namespaceName valueName])) := by
  obtain ⟨middle, first, second⟩ := request_canonical
    (atomicChannel self) (atomicChannel channel) (namedHandler free binder namespaceName valueName)
    (payload := .apply "PDrop" [.fvar datum])
    (ProcWellSorted.drop (.fvar rfl)) (by rfl)
  have continuation := contractum_equations free binder datum namespaceName valueName
    distinct convention
  have activated := (namedHandler free binder namespaceName valueName).activated_typed_safe
    (payload := .apply "PDrop" [.fvar datum])
    (ProcWellSorted.drop (.fvar rfl)) (by rfl)
  have targetEquation : RhoCalculus.StructuralCongruence
      (parallel [namedServer free self channel binder namespaceName valueName,
        semanticCommSubst (namedHandler free binder namespaceName valueName).term
          (.apply "PDrop" [.fvar datum])])
      (parallel [namedServer free self channel binder namespaceName valueName,
        encode (body.substitute binder datum) namespaceName valueName]) := by
    refine .par_cong _ _ rfl ?_
    intro index firstBound secondBound
    have choices : index = 0 ∨ index = 1 := by simp at firstBound; omega
    rcases choices with rfl | rfl
    · exact .refl _
    · exact continuation
  have leftTyped : ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext []
      (parallel [namedServer free self channel binder namespaceName valueName,
        semanticCommSubst (namedHandler free binder namespaceName valueName).term
          (.apply "PDrop" [.fvar datum])]) :=
    .parallel (.cons (namedServer_typed free self channel binder namespaceName valueName)
      (.cons activated.1 .nil))
  have rightTyped : ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext []
      (parallel [namedServer free self channel binder namespaceName valueName,
        encode (body.substitute binder datum) namespaceName valueName]) :=
    .parallel (.cons (namedServer_typed free self channel binder namespaceName valueName)
      (.cons (encode_procWellSorted (rf_substitute free binder datum) namespaceName valueName) .nil))
  have canonicalEndpoint := Canonical.canonicalize_eq_of_structuralCongruence targetEquation
    (rhoProcWellSorted_hashSetFree leftTyped) (rhoProcWellSorted_hashSetFree rightTyped)
  obtain ⟨contractum, fired, endpoint⟩ := second
  exact ⟨middle, first, contractum, fired, endpoint.trans canonicalEndpoint⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedNamed
