import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Source

/-!
# Twin binders: semantic substitution as ordinary substitution

Let an input bind two things, the received name and its *process twin*, and write a drop of a bound
name as that twin (`twin`); quoted code is left as it is. Then the substitution of the reflective
calculus, which turns a dropped received name into the received process, is the ordinary
substitution of the pair (name, process twin) (`osubst`): it replaces bound names by the received
name and twins by the received process, and enters everything, quotes included.

* `twin_semanticSubstProc`: for every well-sorted, quote-sealed, canonical body, twinning commutes
  with the calculus's substitution: the twin of the semantic substitution is the ordinary
  substitution of the twins.
* `twin_contractum`: the communication contractum of canonical primes, read through twins, is an
  ordinary substitution instance. So a communication schema whose continuation is open in a name
  and a process, instantiated ordinarily, computes the calculus's contractum.
* `ordinary_without_twins`: without twins, ordinary substitution of the name alone gives the drop of
  the code instead (the separating program of `Source`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.TwinBinders

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (IsCanonical IsCanonicalList)

/-! ## Twins and their ordinary substitution -/

mutual
  /-- Write each drop of a bound name as the process twin of that name; leave quoted code alone. -/
  def twin : Pattern → Pattern
    | .apply constructor arguments =>
        if constructor = "NQuote" then .apply constructor arguments
        else if constructor = "PDrop" then
          match arguments with
          | [.bvar position] => .apply "Twin" [.bvar position]
          | _ => .apply constructor (twinList arguments)
        else .apply constructor (twinList arguments)
    | .lambda binder body => .lambda binder (twin body)
    | .collection kind elements rest => .collection kind (twinList elements) rest
    | pattern => pattern

  def twinList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => twin pattern :: twinList patterns
end

mutual
  /-- Ordinary substitution of a name for the bound name `index` and of a process for its twin. It
  enters every former, quotes included. -/
  def osubst (index : Nat) (name process : Pattern) : Pattern → Pattern
    | .bvar position => if position = index then name else .bvar position
    | .apply constructor arguments =>
        if constructor = "Twin" ∧ arguments = [.bvar index] then process
        else .apply constructor (osubstList index name process arguments)
    | .lambda binder body => .lambda binder (osubst (index + 1) name process body)
    | .collection kind elements rest =>
        .collection kind (osubstList index name process elements) rest
    | pattern => pattern

  def osubstList (index : Nat) (name process : Pattern) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => osubst index name process pattern :: osubstList index name process patterns
end

/-! ## Closed code is fixed -/

mutual
  /-- Ordinary substitution fixes every pattern whose bound indices are below its depth. -/
  theorem osubst_fixed (index : Nat) (name process : Pattern) :
      ∀ (pattern : Pattern) {depth : Nat}, binderSafeAt "NQuote" depth pattern = true →
        depth ≤ index → osubst index name process pattern = pattern
    | .bvar position, depth, safe, below => by
        have small : position < depth := by simpa [binderSafeAt] using safe
        have different : position ≠ index := by omega
        simp [osubst, different]
    | .fvar _, _, _, _ => by simp [osubst]
    | .apply constructor arguments, depth, safe, below => by
        have notTwin : ¬ (constructor = "Twin" ∧ arguments = [.bvar index]) := by
          rintro ⟨rfl, rfl⟩
          have small : index < depth := by
            simpa [binderSafeAt, binderSafeListAt] using safe
          omega
        rw [osubst, if_neg notTwin]
        congr 1
        cases arguments with
        | nil => rfl
        | cons first rest =>
            cases rest with
            | nil =>
                by_cases quote : constructor = "NQuote"
                · subst quote
                  have inner : binderSafeAt "NQuote" 0 first = true := by
                    simpa [binderSafeAt] using safe
                  simp only [osubstList, osubst_fixed index name process first inner
                    (Nat.zero_le _)]
                · have inner : binderSafeAt "NQuote" depth first = true := by
                    have listSafe : binderSafeListAt "NQuote" depth [first] = true := by
                      simpa [binderSafeAt, quote] using safe
                    simpa [binderSafeListAt] using listSafe
                  simp only [osubstList, osubst_fixed index name process first inner below]
            | cons second more =>
                have listSafe : binderSafeListAt "NQuote" depth (first :: second :: more) = true := by
                  simpa [binderSafeAt] using safe
                exact osubstList_fixed index name process _ listSafe below
    | .lambda binder body, depth, safe, below => by
        have inner : binderSafeAt "NQuote" (depth + 1) body = true := by
          simpa [binderSafeAt] using safe
        simp only [osubst, osubst_fixed (index + 1) name process body inner (by omega)]
    | .multiLambda _ _ _, _, _, _ => by simp [osubst]
    | .subst _ _, _, _, _ => by simp [osubst]
    | .collection kind elements rest, depth, safe, below => by
        have listSafe : binderSafeListAt "NQuote" depth elements = true := by
          simpa [binderSafeAt] using safe
        simp only [osubst, osubstList_fixed index name process elements listSafe below]

  theorem osubstList_fixed (index : Nat) (name process : Pattern) :
      ∀ (patterns : List Pattern) {depth : Nat}, binderSafeListAt "NQuote" depth patterns = true →
        depth ≤ index → osubstList index name process patterns = patterns
    | [], _, _, _ => rfl
    | pattern :: patterns, depth, safe, below => by
        have both : binderSafeAt "NQuote" depth pattern = true ∧
            binderSafeListAt "NQuote" depth patterns = true := by
          simpa [binderSafeListAt, Bool.and_eq_true] using safe
        simp only [osubstList, osubst_fixed index name process pattern both.1 below,
          osubstList_fixed index name process patterns both.2 below]
end

/-! ## Canonical terms are already normalized -/

mutual
  theorem normalizeName_canonical {free : FreeSortContext} {bound : List String} {name : Pattern}
      (typed : NameWellSorted rhoReflectivePresentation free bound name)
      (canonical : IsCanonical name) : semanticNormalizeName name = name := by
    cases typed with
    | bvar _ => rfl
    | fvar _ => rfl
    | quote processTyped =>
        rename_i process
        have parts : IsCanonical process ∧ ∀ inner, process ≠ .apply "PDrop" [inner] := canonical
        change semanticNormalizeName (.apply "NQuote" [process]) = .apply "NQuote" [process]
        rw [semanticNormalizeName.eq_4 process (fun inner same => parts.2 inner same),
          normalizeProc_canonical processTyped parts.1]

  theorem normalizeProc_canonical {free : FreeSortContext} {bound : List String} {process : Pattern}
      (typed : ProcWellSorted rhoReflectivePresentation free bound process)
      (canonical : IsCanonical process) : semanticNormalizeProc process = process := by
    cases typed with
    | bvar _ => rfl
    | fvar _ => rfl
    | unit => rfl
    | drop nameTyped =>
        rename_i name
        have nameCanonical : IsCanonical name := canonical.1
        change semanticNormalizeProc (.apply "PDrop" [name]) = .apply "PDrop" [name]
        simp only [semanticNormalizeProc, normalizeName_canonical nameTyped nameCanonical]
    | output channelTyped payloadTyped =>
        rename_i channel payload
        have channelCanonical : IsCanonical channel := canonical.1
        have payloadCanonical : IsCanonical payload := canonical.2.1
        change semanticNormalizeProc (.apply "POutput" [channel, payload]) =
          .apply "POutput" [channel, payload]
        simp only [semanticNormalizeProc, normalizeName_canonical channelTyped channelCanonical,
          normalizeProc_canonical payloadTyped payloadCanonical]
    | input channelTyped bodyTyped =>
        rename_i channel body
        have channelCanonical : IsCanonical channel := canonical.1
        have bodyCanonical : IsCanonical body := canonical.2.1
        change semanticNormalizeProc (.apply "PInput" [channel, .lambda none body]) =
          .apply "PInput" [channel, .lambda none body]
        simp only [semanticNormalizeProc, normalizeName_canonical channelTyped channelCanonical,
          normalizeProc_canonical bodyTyped bodyCanonical]
    | parallel processesTyped =>
        rename_i processes
        have listCanonical : IsCanonicalList processes := canonical.2.2.2
        change semanticNormalizeProc (.collection .hashBag processes none) =
          .collection .hashBag processes none
        simp only [semanticNormalizeProc, normalizeProcList_canonical processesTyped listCanonical]

  theorem normalizeProcList_canonical {free : FreeSortContext} {bound : List String}
      {processes : List Pattern}
      (typed : ProcListWellSorted rhoReflectivePresentation free bound processes)
      (canonical : IsCanonicalList processes) : semanticNormalizeProcList processes = processes := by
    cases typed with
    | nil => rfl
    | cons processTyped processesTyped =>
        simp only [semanticNormalizeProcList, normalizeProc_canonical processTyped canonical.1,
          normalizeProcList_canonical processesTyped canonical.2]
end

/-! ## Twinning commutes with the calculus's substitution -/

theorem osubst_apply {index : Nat} {name process : Pattern} {constructor : String}
    {arguments : List Pattern} (notTwin : constructor ≠ "Twin") :
    osubst index name process (.apply constructor arguments) =
      .apply constructor (osubstList index name process arguments) := by
  rw [osubst, if_neg (fun both => notTwin both.1)]

theorem osubst_lambda {index : Nat} {name process : Pattern} {binder : Option String}
    {body : Pattern} :
    osubst index name process (.lambda binder body) =
      .lambda binder (osubst (index + 1) name process body) := by
  rw [osubst]

theorem osubst_bvar {index position : Nat} {name process : Pattern} :
    osubst index name process (.bvar position) =
      if position = index then name else .bvar position := by
  rw [osubst]

theorem osubst_twin_self {index : Nat} {name process : Pattern} :
    osubst index name process (.apply "Twin" [.bvar index]) = process := by
  rw [osubst, if_pos ⟨rfl, rfl⟩]

theorem osubst_twin_other {index position : Nat} {name process : Pattern}
    (different : position ≠ index) :
    osubst index name process (.apply "Twin" [.bvar position]) = .apply "Twin" [.bvar position] := by
  rw [osubst, if_neg (fun both => different (by simpa using both.2))]
  simp [osubstList, osubst_bvar, different]

theorem osubst_collection {index : Nat} {name process : Pattern} {kind : CollType}
    {elements : List Pattern} {rest : Option String} :
    osubst index name process (.collection kind elements rest) =
      .collection kind (osubstList index name process elements) rest := by
  rw [osubst]

mutual
  theorem twin_semanticSubstName {free : FreeSortContext} {index : Nat} {name received : Pattern}
      (typed : NameWellSorted rhoReflectivePresentation free
        (List.replicate (index + 1) rhoReflectivePresentation.nameSort) name)
      (safe : binderSafeAt "NQuote" (index + 1) name = true) (canonical : IsCanonical name) :
      twin (semanticSubstName index (.apply "NQuote" [received]) name) =
        osubst index (.apply "NQuote" [received]) (twin received) (twin name) := by
    cases typed with
    | bvar lookup =>
        rename_i position
        have twinBvar : twin (.bvar position) = .bvar position := by simp [twin]
        rw [twinBvar, osubst_bvar]
        by_cases same : position = index
        · subst same
          simp [semanticSubstName, semanticSubstNameMark, twin, Canonical.canonicalize]
        · simp [semanticSubstName, semanticSubstNameMark, semanticNormalizeName, twin, same,
            Canonical.canonicalize]
    | fvar lookup =>
        rename_i atom
        have twinFvar : twin (.fvar atom) = .fvar atom := by simp [twin]
        rw [twinFvar]
        simp [semanticSubstName, semanticSubstNameMark, semanticNormalizeName, twin, osubst,
          Canonical.canonicalize]
    | quote processTyped =>
        rename_i process
        have parts : IsCanonical process ∧ ∀ inner, process ≠ .apply "PDrop" [inner] := canonical
        have closed : binderSafeAt "NQuote" 0 (.apply "NQuote" [process]) = true := by
          simpa [binderSafeAt, rhoReflectivePresentation] using safe
        have normal : semanticNormalizeName (.apply "NQuote" [process]) = .apply "NQuote" [process] :=
          normalizeName_canonical (.quote processTyped) canonical
        change twin (semanticSubstName index (.apply "NQuote" [received]) (.apply "NQuote" [process])) =
          osubst index (.apply "NQuote" [received]) (twin received)
            (twin (.apply "NQuote" [process]))
        have twinQuote : twin (.apply "NQuote" [process]) = .apply "NQuote" [process] := by
          simp [twin]
        have fixedQuote : Canonical.canonicalize (.apply "NQuote" [process]) =
            .apply "NQuote" [process] :=
          Canonical.canonicalize_eq_of_isCanonical canonical
        rw [twinQuote, osubst_fixed index _ _ _ closed (Nat.zero_le index)]
        simp [semanticSubstName, semanticSubstNameMark, normal, twin, fixedQuote]

  theorem twin_semanticSubstProc {free : FreeSortContext} {index : Nat} {process received : Pattern}
      (typed : ProcWellSorted rhoReflectivePresentation free
        (List.replicate (index + 1) rhoReflectivePresentation.nameSort) process)
      (safe : binderSafeAt "NQuote" (index + 1) process = true) (canonical : IsCanonical process) :
      twin (semanticSubstProc index (.apply "NQuote" [received]) process) =
        osubst index (.apply "NQuote" [received]) (twin received) (twin process) := by
    cases typed with
    | bvar lookup =>
        rename_i position
        have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
        have nameLookup :
            (List.replicate (index + 1) rhoReflectivePresentation.nameSort)[position]? =
              some rhoReflectivePresentation.nameSort := by
          apply List.getElem?_eq_some_iff.mpr
          exact ⟨inBounds, by simp⟩
        rw [nameLookup] at lookup
        simp [rhoReflectivePresentation] at lookup
    | fvar _ => simp [semanticSubstProc, twin, osubst]
    | unit => simp [semanticSubstProc, twin, twinList, osubst, osubstList, rhoReflectivePresentation]
    | drop nameTyped =>
        rename_i name
        cases nameTyped with
        | bvar lookup =>
            rename_i position
            change twin (semanticSubstProc index (.apply "NQuote" [received])
                (.apply "PDrop" [.bvar position])) =
              osubst index (.apply "NQuote" [received]) (twin received)
                (twin (.apply "PDrop" [.bvar position]))
            have twinDrop : twin (.apply "PDrop" [.bvar position]) = .apply "Twin" [.bvar position] := by
              simp [twin]
            rw [twinDrop]
            by_cases same : position = index
            · subst same
              rw [osubst_twin_self]
              simp [semanticSubstProc, semanticSubstNameMark, Canonical.canonicalize]
            · rw [osubst_twin_other same]
              simp [semanticSubstProc, semanticSubstNameMark, semanticNormalizeName, twin, same,
                Canonical.canonicalize]
        | fvar _ =>
            simp [semanticSubstProc, semanticSubstNameMark, semanticNormalizeName, twin, twinList,
              osubst, osubstList, rhoReflectivePresentation, Canonical.canonicalize]
        | quote processTyped =>
            rename_i quoted
            have nameCanonical : IsCanonical (.apply "NQuote" [quoted]) := canonical.1
            have parts : IsCanonical quoted ∧ ∀ inner, quoted ≠ .apply "PDrop" [inner] :=
              nameCanonical
            have normal : semanticNormalizeName (.apply "NQuote" [quoted]) =
                .apply "NQuote" [quoted] :=
              normalizeName_canonical (.quote processTyped) nameCanonical
            have closedInner : binderSafeAt "NQuote" 0 quoted = true := by
              simpa [binderSafeAt, binderSafeListAt, rhoReflectivePresentation] using safe
            have fixedInner := osubst_fixed index (.apply "NQuote" [received]) (twin received)
              quoted closedInner (Nat.zero_le index)
            change twin (semanticSubstProc index (.apply "NQuote" [received])
                (.apply "PDrop" [.apply "NQuote" [quoted]])) =
              osubst index (.apply "NQuote" [received]) (twin received)
                (twin (.apply "PDrop" [.apply "NQuote" [quoted]]))
            have twinDrop : twin (.apply "PDrop" [.apply "NQuote" [quoted]]) =
                .apply "PDrop" [.apply "NQuote" [quoted]] := by
              simp [twin, twinList]
            rw [twinDrop, osubst_apply (by decide)]
            simp only [osubstList]
            rw [osubst_apply (by decide)]
            simp only [osubstList, fixedInner]
            have fixedQuote : Canonical.canonicalize (.apply "NQuote" [quoted]) =
                .apply "NQuote" [quoted] :=
              Canonical.canonicalize_eq_of_isCanonical nameCanonical
            simp [semanticSubstProc, semanticSubstNameMark, normal, twin, twinList, fixedQuote]
    | output channelTyped payloadTyped =>
        rename_i channel payload
        have componentsSafe :
            binderSafeAt "NQuote" (index + 1) channel = true ∧
              binderSafeAt "NQuote" (index + 1) payload = true := by
          simpa [binderSafeAt, binderSafeListAt, rhoReflectivePresentation] using safe
        have channelCanonical : IsCanonical channel := canonical.1
        have payloadCanonical : IsCanonical payload := canonical.2.1
        have channelStep := twin_semanticSubstName (received := received) channelTyped
          componentsSafe.1 channelCanonical
        have payloadStep := twin_semanticSubstProc (received := received) payloadTyped
          componentsSafe.2 payloadCanonical
        change twin (semanticSubstProc index (.apply "NQuote" [received])
            (.apply "POutput" [channel, payload])) =
          osubst index (.apply "NQuote" [received]) (twin received)
            (twin (.apply "POutput" [channel, payload]))
        have twinOutput : twin (.apply "POutput" [channel, payload]) =
            .apply "POutput" [twin channel, twin payload] := by
          simp [twin, twinList]
        rw [twinOutput, osubst_apply (by decide)]
        simp only [osubstList]
        rw [← channelStep, ← payloadStep]
        simp [semanticSubstProc, twin, twinList]
    | input channelTyped bodyTyped =>
        rename_i channel body
        have componentsSafe :
            binderSafeAt "NQuote" (index + 1) channel = true ∧
              binderSafeAt "NQuote" (index + 2) body = true := by
          simpa [binderSafeAt, binderSafeListAt, rhoReflectivePresentation, Nat.add_assoc] using safe
        have bodyTyped' :
            ProcWellSorted rhoReflectivePresentation free
              (List.replicate (index + 2) rhoReflectivePresentation.nameSort) body := by
          simpa [List.replicate_succ, Nat.add_assoc] using bodyTyped
        have channelCanonical : IsCanonical channel := canonical.1
        have bodyCanonical : IsCanonical body := canonical.2.1
        have channelStep := twin_semanticSubstName (received := received) channelTyped
          componentsSafe.1 channelCanonical
        have bodyStep := twin_semanticSubstProc (received := received) bodyTyped'
          componentsSafe.2 bodyCanonical
        change twin (semanticSubstProc index (.apply "NQuote" [received])
            (.apply "PInput" [channel, .lambda none body])) =
          osubst index (.apply "NQuote" [received]) (twin received)
            (twin (.apply "PInput" [channel, .lambda none body]))
        have twinInput : twin (.apply "PInput" [channel, .lambda none body]) =
            .apply "PInput" [twin channel, .lambda none (twin body)] := by
          simp [twin, twinList]
        rw [twinInput, osubst_apply (by decide)]
        simp only [osubstList, osubst_lambda]
        rw [← channelStep, ← bodyStep]
        simp [semanticSubstProc, twin, twinList]
    | parallel processesTyped =>
        rename_i processes
        have processesSafe : binderSafeListAt "NQuote" (index + 1) processes = true := by
          simpa [binderSafeAt, rhoReflectivePresentation] using safe
        have listCanonical : IsCanonicalList processes := canonical.2.2.2
        have listStep := twin_semanticSubstProcList (received := received) processesTyped
          processesSafe listCanonical
        change twin (semanticSubstProc index (.apply "NQuote" [received])
            (.collection .hashBag processes none)) =
          osubst index (.apply "NQuote" [received]) (twin received)
            (twin (.collection .hashBag processes none))
        have twinBag : twin (.collection .hashBag processes none) =
            .collection .hashBag (twinList processes) none := by
          simp [twin]
        rw [twinBag, osubst_collection, ← listStep]
        simp [semanticSubstProc, twin]

  theorem twin_semanticSubstProcList {free : FreeSortContext} {index : Nat}
      {processes : List Pattern} {received : Pattern}
      (typed : ProcListWellSorted rhoReflectivePresentation free
        (List.replicate (index + 1) rhoReflectivePresentation.nameSort) processes)
      (safe : binderSafeListAt "NQuote" (index + 1) processes = true)
      (canonical : IsCanonicalList processes) :
      twinList (semanticSubstProcList index (.apply "NQuote" [received]) processes) =
        osubstList index (.apply "NQuote" [received]) (twin received) (twinList processes) := by
    cases typed with
    | nil => rfl
    | cons processTyped processesTyped =>
        rename_i process processes
        have componentsSafe :
            binderSafeAt "NQuote" (index + 1) process = true ∧
              binderSafeListAt "NQuote" (index + 1) processes = true := by
          simpa [binderSafeListAt, Bool.and_eq_true] using safe
        simp only [semanticSubstProcList, twinList, osubstList,
          twin_semanticSubstProc processTyped componentsSafe.1 canonical.1,
          twin_semanticSubstProcList processesTyped componentsSafe.2 canonical.2]
end

/-! ## Communication through twins -/

/-- **The contractum through twins.** For every closed communication on canonical primes, the twin of
the calculus's contractum is an ordinary substitution instance: the received code for the bound name,
the twin of the received process for its twin. -/
theorem twin_contractum (rule : CanonicalReaction.GroundComm) :
    twin rule.result.1 =
      osubst 0 (.apply "NQuote" [rule.payload]) (twin rule.payload) (twin rule.body) := by
  have payloadCanonical : IsCanonical rule.payload := rule.outputPrime.2.1.2.1
  have bodyCanonical : IsCanonical rule.body := rule.inputPrime.2.1.2.1
  have normal : semanticNormalizeProc rule.payload = rule.payload :=
    normalizeProc_canonical rule.payload_typed payloadCanonical
  have bodyTyped : ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      (List.replicate (0 + 1) rhoReflectivePresentation.nameSort) rule.body := rule.body_typed
  change twin (semanticCommSubst rule.body rule.payload) = _
  unfold semanticCommSubst
  rw [normal]
  exact twin_semanticSubstProc bodyTyped rule.body_safe bodyCanonical

open CanonicalReactionControls in
/-- **Control: without twins.** On the separating program `for(y <- @0){*y} | @0!(@0!(0))`, the same
ordinary substitution applied to the body as written gives the inert drop of the code; applied to the
twinned body it gives the received process, which is the calculus's contractum (`twin_contractum`,
`Source.semantic_and_ordinary_differ`). -/
theorem ordinary_without_twins :
    osubst 0 (.apply "NQuote" [payload]) (twin payload) body = Source.ordinaryContractum ∧
      osubst 0 (.apply "NQuote" [payload]) (twin payload) (twin body) = payload ∧
      twin rule.result.1 = payload := by
  have twinPayload : twin payload = payload := by
    simp [twin, twinList, payload, CanonicalReaction.output, channel, zero]
  have twinBody : twin body = .apply "Twin" [.bvar 0] := by
    simp [twin, body]
  refine ⟨?_, ?_, ?_⟩
  · change osubst 0 (.apply "NQuote" [payload]) (twin payload) (.apply "PDrop" [.bvar 0]) = _
    rw [osubst_apply (by decide)]
    simp [osubstList, osubst_bvar, Source.ordinaryContractum]
  · rw [twinBody, osubst_twin_self, twinPayload]
  · rw [actual_result, twinPayload]

#print axioms osubst_fixed
#print axioms normalizeProc_canonical
#print axioms twin_semanticSubstProc
#print axioms twin_contractum
#print axioms ordinary_without_twins

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.TwinBinders
