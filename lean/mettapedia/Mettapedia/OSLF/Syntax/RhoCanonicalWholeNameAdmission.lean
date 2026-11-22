import Mettapedia.OSLF.Syntax.RhoWholeNameAdmission
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParameterizedRewriteSystem

/-!
# Rho whole-name admission after structural canonicalization

Parallel-unit and quote/drop equations can expose a whole bound name from a
surface spelling such as `@(*x | 0)`. The pure rho canonicalizer selects an
equivalent representative before scope admission and translation. Literal
quoted code whose normal form is not a whole name remains sealed.

Well-sorted, canonically admitted surface firings execute in the existing
rho theory. The unrestricted raw receipt relation can still choose an
ill-sorted intermediate term. The executable surface parser is unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- Scope admission on the computed representative of the rho equations. -/
def canonicalWholeNameSafeAt (depth : Nat) (pattern : Pattern) : Bool :=
  wholeNameSafeAt depth (Canonical.canonicalize pattern)

/-- Closed admission after pure rho canonicalization. -/
def canonicalWholeNameSafe (pattern : Pattern) : Bool :=
  canonicalWholeNameSafeAt 0 pattern

private theorem wholeNameList_members {depth : Nat} (items : List Pattern) :
    wholeNameSafeListAt depth items = true ↔ ∀ item ∈ items, wholeNameSafeAt depth item = true := by
  induction items with
  | nil => simp [wholeNameSafeListAt]
  | cons first rest ih => simp [wholeNameSafeListAt,ih]

/-- The usual opaque-quotation checker implies whole-name safety. Removing a
direct quote/drop wrapper can only make the inner name's allowed depth larger. -/
theorem wholeNameSafe_of_binderSafe (pattern : Pattern) (depth : Nat)
    (safe : binderSafeAt "NQuote" depth pattern = true) :
    wholeNameSafeAt depth pattern = true := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simpa [binderSafeAt,wholeNameSafeAt] using safe
  | hfvar name => simp [wholeNameSafeAt]
  | happly head arguments ih =>
    have all (ready : binderSafeListAt "NQuote" depth arguments = true) :
        wholeNameSafeListAt depth arguments = true := by
      apply (wholeNameList_members _).mpr
      intro p member
      exact ih p member depth ((binderSafeListAt_eq_true_iff _ _ _).mp ready p member)
    cases arguments with
    | nil => simp [wholeNameSafeAt,wholeNameSafeListAt]
    | cons argument args =>
      cases args with
      | nil =>
        by_cases quote : head = "NQuote"
        · subst head
          have sealed : binderSafeAt "NQuote" 0 argument = true := by simpa [binderSafeAt] using safe
          by_cases whole : ∃ name, argument = .apply "PDrop" [name]
          · obtain ⟨name,rfl⟩ := whole
            have wholeAt := ih (.apply "PDrop" [name]) (by simp) depth
              (binderSafeAt_mono "NQuote" sealed (Nat.zero_le depth))
            simpa [wholeNameSafeAt,wholeNameSafeListAt] using wholeAt
          · have notDrop : ∀ name, argument = .apply "PDrop" [name] → False :=
              fun name same => whole ⟨name, same⟩
            rw [wholeNameSafeAt_quote notDrop]
            split
            · exact ih argument (by simp) depth (binderSafeAt_mono "NQuote" sealed (Nat.zero_le depth))
            · exact ih argument (by simp) 0 sealed
        · simpa [wholeNameSafeAt,quote] using all (by simpa [binderSafeAt,quote] using safe)
      | cons second rest =>
        simpa [wholeNameSafeAt] using all (by simpa [binderSafeAt] using safe)
  | hlambda binder body ih =>
    exact ih (depth + 1) (by simpa [binderSafeAt] using safe)
  | hmultiLambda arity binders body ih =>
    exact ih (depth + arity) (by simpa [binderSafeAt] using safe)
  | hsubst body replacement ihBody ihReplacement =>
    have both : binderSafeAt "NQuote" (depth + 1) body = true ∧
        binderSafeAt "NQuote" depth replacement = true := by simpa [binderSafeAt] using safe
    simpa [wholeNameSafeAt] using And.intro (ihBody _ both.1) (ihReplacement _ both.2)
  | hcollection col elements rest ih =>
    have ready : binderSafeListAt "NQuote" depth elements = true := by simpa [binderSafeAt] using safe
    exact (wholeNameList_members _).mpr fun entry member =>
      ih entry member depth ((binderSafeListAt_eq_true_iff _ _ _).mp ready entry member)

/-- The admitted whole-name exception disappears at the representative:
the exact `@*n` orientation exposes a name at its original depth, and
literal quoted code is still proved safe at zero. This supplies the
existing author's scope judgment, rather than replacing it. -/
theorem canonicalize_safe_of_wholeName (pattern : Pattern) (depth : Nat)
    (safe : wholeNameSafeAt depth pattern = true) :
    binderSafeAt "NQuote" depth (Canonical.canonicalize pattern) = true := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simpa [Canonical.canonicalize,binderSafeAt,wholeNameSafeAt] using safe
  | hfvar name => simp [Canonical.canonicalize,binderSafeAt]
  | happly head arguments ih =>
    have wholeList (good : wholeNameSafeListAt depth arguments = true) :
        binderSafeListAt "NQuote" depth (Canonical.canonicalizeList arguments) = true := by
      apply (binderSafeListAt_eq_true_iff _ _ _).mpr
      intro canonical member
      rw [Canonical.canonicalizeList_eq_map] at member
      obtain ⟨source,found,rfl⟩ := List.mem_map.mp member
      exact ih source found depth ((wholeNameList_members _).mp good source found)
    cases arguments with
    | nil => simp [Canonical.canonicalize,Canonical.canonicalizeList,binderSafeAt,binderSafeListAt]
    | cons argument args =>
      cases args with
      | nil =>
        by_cases quote : head = "NQuote"
        · subst head
          change binderSafeAt "NQuote" depth (Canonical.normalizeQuote (Canonical.canonicalize argument)) = true
          by_cases whole : ∃ name, argument = .apply "PDrop" [name]
          · obtain ⟨name,rfl⟩ := whole
            have admitted : wholeNameSafeAt depth (.apply "PDrop" [name]) = true := by
              simpa [wholeNameSafeAt,wholeNameSafeListAt] using safe
            have kept := ih (.apply "PDrop" [name]) (by simp) depth admitted
            simpa [Canonical.canonicalize,Canonical.canonicalizeList,Canonical.normalizeQuote,
              binderSafeAt,binderSafeListAt] using kept
          · have notDrop : ∀ name, argument = .apply "PDrop" [name] → False :=
              fun name same => whole ⟨name, same⟩
            have safeQuote := safe
            rw [wholeNameSafeAt_quote notDrop] at safe
            cases head : nameHead (.apply "NQuote" [argument]) with
            | some k =>
                have hit := (canonicalize_eq_bvar_iff_nameHead _ k).mpr head
                have quoted : Canonical.canonicalize (.apply "NQuote" [argument]) =
                    Canonical.normalizeQuote (Canonical.canonicalize argument) := by
                  simp [Canonical.canonicalize]
                rw [quoted] at hit
                rw [hit]
                simpa [binderSafeAt] using nameHead_lt_of_wholeNameSafe head safeQuote
            | none =>
                rw [head] at safe
                exact CanonicalTyping.normalizeQuote_binderSafeAt (ih argument (by simp) 0 safe)
        · have admitted : wholeNameSafeListAt depth [argument] = true := by
            simpa [wholeNameSafeAt,quote] using safe
          simpa [Canonical.canonicalize,Canonical.canonicalizeList,binderSafeAt,binderSafeListAt,quote]
            using wholeList admitted
      | cons second rest =>
        have admitted : wholeNameSafeListAt depth (argument :: second :: rest) = true := by
          simp [wholeNameSafeAt] at safe
          exact safe
        by_cases quote : head = "NQuote"
        · subst head
          change binderSafeListAt "NQuote" depth
            (Canonical.canonicalize argument :: Canonical.canonicalize second :: Canonical.canonicalizeList rest) = true
          simpa [Canonical.canonicalizeList] using wholeList admitted
        · simpa [Canonical.canonicalize,binderSafeAt,quote,Canonical.canonicalizeList] using wholeList admitted
  | hlambda binder body ih =>
    exact ih (depth + 1) (by simpa [wholeNameSafeAt] using safe)
  | hmultiLambda arity binders body ih =>
    exact ih (depth + arity) (by simpa [wholeNameSafeAt] using safe)
  | hsubst body replacement ihBody ihReplacement =>
    have both : wholeNameSafeAt (depth + 1) body = true ∧ wholeNameSafeAt depth replacement = true := by
      simpa [wholeNameSafeAt] using safe
    simpa [Canonical.canonicalize,binderSafeAt] using
      And.intro (ihBody (depth + 1) both.1) (ihReplacement depth both.2)
  | hcollection col elements rest ih =>
    have all : wholeNameSafeListAt depth elements = true := by simpa [wholeNameSafeAt] using safe
    have mapped : binderSafeListAt "NQuote" depth (Canonical.canonicalizeList elements) = true := by
      apply (binderSafeListAt_eq_true_iff _ _ _).mpr
      intro canonical member
      rw [Canonical.canonicalizeList_eq_map] at member
      obtain ⟨source,found,rfl⟩ := List.mem_map.mp member
      exact ih source found depth ((wholeNameList_members _).mp all source found)
    cases col with
    | vec => simpa [Canonical.canonicalize,binderSafeAt] using mapped
    | hashSet => simpa [Canonical.canonicalize,binderSafeAt] using mapped
    | hashBag =>
      cases rest with
      | none =>
        exact CanonicalTyping.collapseBag_binderSafeAt
          (CanonicalTyping.normalizeBagElements_binderSafeListAt mapped)
      | some guard => simpa [Canonical.canonicalize,binderSafeAt] using mapped

/-- Admission is exactly ordinary scope safety of the canonical representative. -/
theorem canonicalWholeNameSafe_iff (source : Pattern) :
    canonicalWholeNameSafe source = true ↔ binderSafeAt "NQuote" 0 (Canonical.canonicalize source) = true := by
  constructor
  · intro safe
    have admitted := canonicalize_safe_of_wholeName (Canonical.canonicalize source) 0 safe
    rwa [Canonical.canonicalize_idempotent] at admitted
  · exact wholeNameSafe_of_binderSafe _ _

/-- Compile a canonically admitted surface process into the existing
typed executor, not into a second carrier for raw substitutions. -/
def canonicalProcess {free : FreeSortContext} (source : Pattern)
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : canonicalWholeNameSafe source = true) :
    ParameterizedRewriteSystem.Process free :=
  ⟨Canonical.canonicalize source, (ParameterizedRewriteSystem.process_iff _ _).mpr
    ⟨CanonicalTyping.canonicalize_procWellSorted [] typed,(canonicalWholeNameSafe_iff source).mp safe⟩⟩

/-- An actual authored firing of a canonically admitted surface process
has the same reached equation class in the existing typed rho theory. -/
theorem canonicalProcess_step {free : FreeSortContext} {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : canonicalWholeNameSafe source = true)
    (firing : DerivedContextualStep.RhoStep source target) :
    ∃ reached : ParameterizedRewriteSystem.Process free,
      (ParameterizedRewriteSystem.theory free).Step
        (canonicalProcess source typed safe) reached ∧
      Canonical.canonicalize reached.1 = Canonical.canonicalize target := by
  obtain ⟨target', admitted, same⟩ :=
    CanonicalStepperCompleteness.canonicalStep_complete_of_rhoStep typed firing
  let reached := ParameterizedRewriteSystem.stepTarget
    (canonicalProcess source typed safe) (target := target') ⟨1, admitted⟩
  exact ⟨reached, ParameterizedRewriteSystem.of_step ⟨1, admitted⟩, same⟩

/-- On well-sorted pure rho processes, admission depends on the structural
congruence class rather than the spelling chosen for a representative. -/
theorem canonicalWholeNameSafe_congr {free : FreeSortContext}
    {source target : Pattern}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free [] source)
    (targetTyped : ProcWellSorted rhoReflectivePresentation free [] target)
    (equivalent : StructuralCongruence source target) :
    canonicalWholeNameSafe source = canonicalWholeNameSafe target := by
  have same := Canonical.canonicalize_eq_of_structuralCongruence equivalent
    (PureBoundary.rhoProcWellSorted_hashSetFree sourceTyped)
    (PureBoundary.rhoProcWellSorted_hashSetFree targetTyped)
  simp only [canonicalWholeNameSafe, canonicalWholeNameSafeAt, same]

/-- A canonically admitted source has a translation of its representative.
The original spelling and representative are structurally congruent. -/
theorem canonical_source_coverage {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : canonicalWholeNameSafe source = true) :
    StructuralCongruence source (Canonical.canonicalize source) ∧
      ∃ t, tProc (Env.empty []) (Canonical.canonicalize source) = some t := by
  constructor
  · exact Canonical.canonicalize_sound source
  · have admitted := (ParameterizedRewriteSystem.process_iff _ _).mp
      (canonicalProcess source typed safe).2
    exact closed_admitted_translates hfree admitted.1 admitted.2

private theorem canonicalize_structural_unit_bound_name :
    Canonical.canonicalize (.apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [.bvar 0], .apply "PZero" []] none]) =
        .bvar 0 := by
  simp [Canonical.canonicalize, Canonical.canonicalizeList,
    Canonical.normalizeQuote, Canonical.normalizeBagElements,
    Canonical.bagSplice, Canonical.sortPatterns, Canonical.collapseBag]

/-- The structural parallel unit exposes the same bound name as `@*x`.
This is a positive control for the mathematical admission criterion. -/
theorem structural_unit_bound_name_canonical_control :
    let wrapped : Pattern := .apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [.bvar 0], .apply "PZero" []] none]
    canonicalWholeNameSafeAt 1 wrapped = true ∧
    tName (Env.empty []).up (Canonical.canonicalize wrapped) =
      some (quoT (.var .zero)) ∧
    StructuralCongruence wrapped (Canonical.canonicalize wrapped) := by
  dsimp [canonicalWholeNameSafeAt]
  have hsc := Canonical.canonicalize_sound
    (.apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [.bvar 0], .apply "PZero" []] none])
  rw [canonicalize_structural_unit_bound_name] at hsc
  rw [canonicalize_structural_unit_bound_name]
  exact ⟨by decide, rfl, hsc⟩

/-- Canonicalization does not turn an unrelated quoted output that mentions
the outer bound variable into a whole name. It remains outside the seal. -/
theorem literal_output_quote_canonical_control :
    canonicalWholeNameSafeAt 1
      (.apply "NQuote" [.apply "POutput"
        [.bvar 0, .apply "PZero" []]]) = false := by
  decide

namespace RawBoundary

open Reduction (Reduces)
open DerivedContextualStep (RhoStep RhoStepAt)

private def zero : Pattern := .apply "PZero" []
private def wire : Pattern := .apply "NQuote" [zero]
private def payload : Pattern := .apply "POutput" [wire,zero]
private def wrapped : Pattern :=
  .apply "NQuote" [.collection .hashBag [.apply "PDrop" [.bvar 0],zero] none]
private def body (name : Pattern) : Pattern := .apply "PDrop" [name]
private def out : Pattern := .apply "POutput" [wire,payload]
private def receive (name : Pattern) : Pattern := .apply "PInput" [wire,.lambda none (body name)]
def source : Pattern := .collection .hashBag [out,receive (.bvar 0)] none
def surfaceSpelling : Pattern := .collection .hashBag [out,receive wrapped] none
private def illSortedBody : Pattern := .apply "NQuote" [.apply "PDrop" [body (.bvar 0)]]
def illSortedResidual : Pattern := .collection .hashBag [illSortedBody] none

private theorem wireTyped {bound : List String} :
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty bound wire :=
  .quote .unit

private theorem payloadTyped {bound : List String} :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty bound payload :=
  .output wireTyped .unit

theorem source_typed : ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] source :=
  .parallel (.cons (.output wireTyped payloadTyped)
    (.cons (.input wireTyped (.drop (.bvar rfl))) .nil))

private theorem spellingEq : StructuralCongruence surfaceSpelling source := by
  have whole := Canonical.canonicalize_sound wrapped
  change StructuralCongruence wrapped
    (Canonical.canonicalize (.apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [.bvar 0],.apply "PZero" []] none])) at whole
  rw [canonicalize_structural_unit_bound_name] at whole
  exact sc_second [] (sc_apply2 "PInput" (.refl wire) (.lambda_cong none _ _ (sc_apply1 "PDrop" whole)))

private theorem wrapped_receives_payload :
    semanticCommSubst (body wrapped) payload = payload := by decide +kernel

/-- The compiled step resolves the received name before substituting; the
payload runs all the same. -/
private theorem wrapped_resolved_receives_payload :
    semanticCommSubst (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation (body wrapped)) payload = payload := by decide +kernel

/-- The old syntax-only name test missed this well-sorted surface spelling.
The actual raw COMM now recognizes its bound name and executes the payload. -/
theorem raw_surface_communicates :
    semanticNormalizeName wrapped = wrapped ∧
      Nonempty (Reduces surfaceSpelling (.collection .hashBag [payload] none)) := by
  have firing : Reduces surfaceSpelling
      (.collection .hashBag [semanticCommSubst (body wrapped) payload] none) :=
    .comm (n := wire) (q := payload) (p := body wrapped) (rest := [])
  exact ⟨by decide +kernel, ⟨by simpa only [wrapped_receives_payload] using firing⟩⟩

/-- Untyped EQUIV can place a quotation in a process position. Its raw COMM
then bypasses substitution at that position. This is not a well-sorted
alternative spelling of the receiver. -/
theorem untyped_equiv_can_leave_scope :
    Nonempty (Reduces source illSortedResidual) ∧
      canonicalWholeNameSafe illSortedResidual = false := by
  have firing : Reduces
      (.collection .hashBag [out, .apply "PInput" [wire, .lambda none illSortedBody]] none)
      illSortedResidual :=
    .comm (n := wire) (q := payload) (p := illSortedBody) (rest := [])
  have equation : StructuralCongruence illSortedBody (body (.bvar 0)) :=
    .quote_drop _
  refine ⟨⟨.equiv ?_ firing (.refl _)⟩, by decide +kernel⟩
  exact sc_second [] (sc_apply2 "PInput" (.refl wire)
    (.lambda_cong none _ _ (.symm _ _ equation)))

theorem surfaceSpelling_typed :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] surfaceSpelling := by
  have quoted : NameWellSorted rhoReflectivePresentation FreeSortContext.empty
      [rhoReflectivePresentation.nameSort] wrapped :=
    .quote (.parallel (.cons (.drop (.bvar rfl)) (.cons .unit .nil)))
  exact .parallel (.cons (.output wireTyped payloadTyped) (.cons (.input wireTyped (.drop quoted)) .nil))

theorem surfaceSpelling_not_literally_safe :
    binderSafeAt "NQuote" 0 surfaceSpelling = false := by decide +kernel

/-- The leaked index cannot be repaired by choosing another spelling
of the residual. Its entire raw structural equation class misses the
existing admitted process carrier. -/
theorem ill_sorted_residual_has_no_admitted_representative
    (candidate : ParameterizedRewriteSystem.Process FreeSortContext.empty) :
    ¬ StructuralCongruence illSortedResidual candidate.1 := by
  intro equal
  have typed := (ParameterizedRewriteSystem.process_iff _ _).mp candidate.2
  have pureResidual : Canonical.HashSetFree illSortedResidual := by
    simp [illSortedResidual,illSortedBody,body,Canonical.HashSetFree,Canonical.HashSetFreeList]
  have same := Canonical.canonicalize_eq_of_structuralCongruence equal pureResidual
    (PureBoundary.rhoProcWellSorted_hashSetFree typed.1)
  have safe : canonicalWholeNameSafe illSortedResidual = true := by
    apply (canonicalWholeNameSafe_iff _).mpr
    rw [same]
    exact CanonicalTyping.canonicalize_binderSafeAt candidate.1 0 typed.2
  rw [untyped_equiv_can_leave_scope.2] at safe
  cases safe

private theorem samePresentation :
    Canonical.canonicalize source = Canonical.canonicalize surfaceSpelling :=
  (Canonical.canonicalize_eq_of_structuralCongruence spellingEq
    (PureBoundary.rhoProcWellSorted_hashSetFree surfaceSpelling_typed)
    (PureBoundary.rhoProcWellSorted_hashSetFree source_typed)).symm

/-- The same surface class really communicates after canonical admission:
it executes the received process, rather than exporting a dangling
bound name from the quote. -/
theorem canonical_surface_communicates :
    canonicalWholeNameSafe surfaceSpelling = true ∧
      ∃ target, RhoStepAt 1 (Canonical.canonicalize surfaceSpelling) target ∧
        Canonical.canonicalize target = Canonical.canonicalize payload := by
  let env := FreeSortContext.empty
  let arranged := Pattern.collection .hashBag [receive wrapped,out] none
  have bodyTyped : ProcWellSorted rhoReflectivePresentation env
      [rhoReflectivePresentation.nameSort] (body wrapped) :=
    .drop (.quote (.parallel (.cons (.drop (.bvar rfl)) (.cons .unit .nil))))
  have ready : ProcWellSorted rhoReflectivePresentation env [] arranged :=
    .parallel (.cons (.input wireTyped bodyTyped) (.cons (.output wireTyped payloadTyped) .nil))
  have atArranged : RhoStep arranged
      (.collection .hashBag [semanticCommSubst (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation (body wrapped)) payload] none) :=
    RhoStep.comm_resolved wire (body wrapped) payload [] bodyTyped payloadTyped
  obtain ⟨target,hit,read⟩ :=
    CanonicalStepperCompleteness.canonicalStep_complete_of_rhoStep ready atArranged
  have same : Canonical.canonicalize arranged = Canonical.canonicalize surfaceSpelling :=
    Canonical.canonicalize_parallel_comm (receive wrapped) out
  rw [same] at hit
  have outClass :
      Canonical.canonicalize (.collection .hashBag [semanticCommSubst (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation (body wrapped)) payload] none) =
        Canonical.canonicalize payload := by
    rw [wrapped_resolved_receives_payload, Canonical.canonicalize_parallel_singleton]
  have sealed : binderSafeAt "NQuote" 0 source = true := by decide +kernel
  refine ⟨(canonicalWholeNameSafe_iff _).mpr ?_,target,hit,read.trans outClass⟩
  rw [← samePresentation]
  exact CanonicalTyping.canonicalize_binderSafeAt source 0 sealed

end RawBoundary

/-- Raw authored strict-core steps remain paper steps when both endpoints
are moved to structural canonical representatives. This does not assert
that the exact canonical spelling is itself an authored executor step. -/
theorem raw_strict_step_canonical_paper {free : FreeSortContext}
    {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (step : Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStep
      source target) :
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (Canonical.canonicalize source) (Canonical.canonicalize target)) := by
  obtain ⟨paper⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.rhoStep_sound
      typed step
  exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.equiv
    (StructuralCongruence.symm _ _ (Canonical.canonicalize_sound source))
    paper (Canonical.canonicalize_sound target)⟩

/-- A step on the admitted canonical representative enters the existing
strict-core simulation. -/
theorem canonical_representative_strict_simulation {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : canonicalWholeNameSafe source = true)
    (step : Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStep
      (Canonical.canonicalize source) target) :
    ∃ s t, tProc (Env.empty []) (Canonical.canonicalize source) = some s ∧
      tProc (Env.empty []) target = some t ∧ Steps strictRules s t := by
  exact wholeNameSafe_strict_simulation hfree
    (CanonicalTyping.canonicalize_procWellSorted [] typed) safe step

/-- The same representative-level comparison holds in the profile whose
additional Drop rule is explicitly declared. -/
theorem canonical_representative_dropExecution_simulation {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : canonicalWholeNameSafe source = true)
    (step : RhoCombinedInterpretedStep.RhoStepWithDrop
      (Canonical.canonicalize source) target) :
    ∃ s t, tProc (Env.empty []) (Canonical.canonicalize source) = some s ∧
      tProc (Env.empty []) target = some t ∧ Steps dropExecutionRules s t := by
  exact wholeNameSafe_dropExecution_simulation hfree
    (CanonicalTyping.canonicalize_procWellSorted [] typed) safe step

/-- A strict-core step in the target is reflected by a source step after
structural rearrangement of the admitted canonical representative. -/
theorem canonical_representative_strict_reflection {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : canonicalWholeNameSafe source = true) :
    ∃ s, tProc (Env.empty []) (Canonical.canonicalize source) = some s ∧
      ∀ {u : Term sig [] Srt.pr}, Steps strictRules s u →
        ∃ source' target',
          StructuralCongruence (Canonical.canonicalize source) source' ∧
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStep
            source' target' ∧
          ∃ t, tProc (Env.empty []) target' = some t ∧ cls t = cls u := by
  exact wholeNameSafe_strict_reflection hfree
    (CanonicalTyping.canonicalize_procWellSorted [] typed) safe

/-- The separately declared Drop profile has the same representative-level
reflection property. -/
theorem canonical_representative_dropExecution_reflection {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : canonicalWholeNameSafe source = true) :
    ∃ s, tProc (Env.empty []) (Canonical.canonicalize source) = some s ∧
      ∀ {u : Term sig [] Srt.pr}, Steps dropExecutionRules s u →
        ∃ source' target',
          StructuralCongruence (Canonical.canonicalize source) source' ∧
          RhoCombinedInterpretedStep.RhoStepWithDrop source' target' ∧
          ∃ t, tProc (Env.empty []) target' = some t ∧ cls t = cls u := by
  exact wholeNameSafe_dropExecution_reflection hfree
    (CanonicalTyping.canonicalize_procWellSorted [] typed) safe

end Mettapedia.OSLF.Binding.RhoPayloadPresentation
