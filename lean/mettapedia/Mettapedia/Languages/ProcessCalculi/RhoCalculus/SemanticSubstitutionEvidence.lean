import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution
import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch

/-!
# Explicit computation evidence for rho communication

The evidence follows rho's own name normalization and COMM substitution.
Every recursive call retains its literal result. Replay checks one constructor
case and its submitted child calls; it does not execute the original recursive
normalizer or substitution as a trusted inference step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitutionEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The replay's binder test is the whole-name decision of the source meaning. -/
private theorem matchesBinder_iff (k : Nat) (name : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.matchesBinder rhoReflectivePresentation k name = true ↔
      Canonical.canonicalize name = .bvar k := by
  simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.matchesBinder, decide_eq_true_eq,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.BinderHead.ofPattern_index_iff,
    CanonicalMatch.derivedCanonicalize_eq]

inductive Task where
  | normalizeName (name : Pattern)
  | normalizeProc (process : Pattern)
  | normalizeList (processes : List Pattern)
  | substituteName (index : Nat) (replacement name : Pattern)
  | substituteProc (index : Nat) (replacement process : Pattern)
  | substituteList (index : Nat) (replacement : Pattern) (processes : List Pattern)
  | comm (body payload : Pattern)
  deriving DecidableEq, Repr

inductive Result where
  | pattern (value : Pattern)
  | patterns (values : List Pattern)
  | marked (name : Pattern) (matched : Bool)
  deriving DecidableEq, Repr

/-- Source meaning uses the independently defined rho functions. -/
def Task.meaning : Task → Result
  | .normalizeName n => .pattern (semanticNormalizeName n)
  | .normalizeProc p => .pattern (semanticNormalizeProc p)
  | .normalizeList ps => .patterns (semanticNormalizeProcList ps)
  | .substituteName k replacement name =>
      let marked := semanticSubstNameMark k replacement name
      .marked marked.1 marked.2
  | .substituteProc k replacement p => .pattern (semanticSubstProc k replacement p)
  | .substituteList k replacement ps => .patterns (semanticSubstProcList k replacement ps)
  | .comm body payload => .pattern (semanticCommSubst body payload)

/-- A literal call tree, containing no functions or proof fields. -/
inductive Certificate where
  | node (result : Result) (children : List Certificate)
  deriving Repr

def Certificate.result : Certificate → Result
  | .node result _ => result

/-- Recursive calls made by the independent source functions. This is a
specification of their call tree, not an operation used by replay. -/
def Task.calls : Task → List Task
  | .normalizeName (.apply "NQuote" [.apply "PDrop" [n]]) => [.normalizeName n]
  | .normalizeName (.apply "NQuote" [p]) => [.normalizeProc p]
  | .normalizeName _ => []
  | .normalizeProc (.apply "POutput" [n, q]) => [.normalizeName n, .normalizeProc q]
  | .normalizeProc (.apply "PInput" [n, .lambda none body]) => [.normalizeName n, .normalizeProc body]
  | .normalizeProc (.apply "PDrop" [n]) => [.normalizeName n]
  | .normalizeProc (.apply "NQuote" [p]) => [.normalizeProc p]
  | .normalizeProc (.lambda _ body) | .normalizeProc (.multiLambda _ _ body) => [.normalizeProc body]
  | .normalizeProc (.subst body replacement) => [.normalizeProc body, .normalizeProc replacement]
  | .normalizeProc (.collection _ ps _) => [.normalizeList ps]
  | .normalizeProc _ => []
  | .normalizeList [] => []
  | .normalizeList (p :: ps) => [.normalizeProc p, .normalizeList ps]
  | .substituteName _ _ name => [.normalizeName name]
  | .substituteProc _ _ (.bvar _) | .substituteProc _ _ (.fvar _)
  | .substituteProc _ _ (.apply "NQuote" [_]) => []
  | .substituteProc k replacement (.apply "PDrop" [name]) => [.substituteName k replacement name]
  | .substituteProc k replacement (.apply "POutput" [name, process]) =>
      [.substituteName k replacement name, .substituteProc k replacement process]
  | .substituteProc k replacement (.apply "PInput" [name, .lambda none process]) =>
      [.substituteName k replacement name, .substituteProc (k + 1) replacement process]
  | .substituteProc k replacement (.lambda _ body) => [.substituteProc (k + 1) replacement body]
  | .substituteProc k replacement (.multiLambda count _ body) => [.substituteProc (k + count) replacement body]
  | .substituteProc k replacement (.subst body value) =>
      [.substituteProc (k + 1) replacement body, .substituteProc k replacement value]
  | .substituteProc k replacement (.collection _ ps _) => [.substituteList k replacement ps]
  | .substituteProc _ _ _ => []
  | .substituteList _ _ [] => []
  | .substituteList k replacement (p :: ps) => [.substituteProc k replacement p, .substituteList k replacement ps]
  | .comm body payload => [.normalizeProc payload,
      .substituteProc 0 (.apply "NQuote" [semanticNormalizeProc payload]) body]

noncomputable def Task.weight : Task → Nat
  | .normalizeName p | .normalizeProc p => sizeOf p
  | .normalizeList ps => sizeOf ps
  | .substituteName _ _ p | .substituteProc _ _ p => 2 * sizeOf p + 1
  | .substituteList _ _ ps => 2 * sizeOf ps + 1
  | .comm body payload => 2 * sizeOf body + sizeOf payload + 5

theorem Task.calls_weight_lt {task child : Task} (member : child ∈ task.calls) :
    child.weight < task.weight := by
  fun_cases Task.calls task <;>
    simp only [Task.calls, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp only [Task.weight, Pattern.apply.sizeOf_spec, Pattern.lambda.sizeOf_spec,
    Pattern.multiLambda.sizeOf_spec, Pattern.subst.sizeOf_spec, Pattern.collection.sizeOf_spec,
    List.cons.sizeOf_spec]
  all_goals omega

/-- Construct the complete source call tree, including literal intermediate
results. Producers may execute the original functions; replay does not. -/
def derive (task : Task) : Certificate :=
  .node task.meaning (task.calls.attach.map fun child => derive child.1)
termination_by task.weight
decreasing_by exact Task.calls_weight_lt child.2

@[simp] theorem derive_result (task : Task) : (derive task).result = task.meaning := by
  rw [derive]
  rfl

/-- One constructor case. The child results are untrusted until replay checks
the returned tasks against the actual child certificates. -/
def unfoldCall : Task → List Result → Option (List Task × Result)
  | .normalizeName (.apply "NQuote" [.apply "PDrop" [n]]), [.pattern out] =>
      some ([.normalizeName n], .pattern out)
  | .normalizeName (.apply "NQuote" [p]), [.pattern out] =>
      some ([.normalizeProc p], .pattern (.apply "NQuote" [out]))
  | .normalizeName n, [] =>
      match n with
      | .apply "NQuote" [_] => none
      | _ => some ([], .pattern n)
  | .normalizeProc (.apply "POutput" [n, q]), [.pattern name, .pattern process] =>
      some ([.normalizeName n, .normalizeProc q], .pattern (.apply "POutput" [name, process]))
  | .normalizeProc (.apply "PInput" [n, .lambda none body]), [.pattern name, .pattern process] =>
      some ([.normalizeName n, .normalizeProc body], .pattern (.apply "PInput" [name, .lambda none process]))
  | .normalizeProc (.apply "PDrop" [n]), [.pattern name] =>
      some ([.normalizeName n], .pattern (.apply "PDrop" [name]))
  | .normalizeProc (.apply "NQuote" [p]), [.pattern process] =>
      some ([.normalizeProc p], .pattern (.apply "NQuote" [process]))
  | .normalizeProc (.lambda name body), [.pattern process] =>
      some ([.normalizeProc body], .pattern (.lambda name process))
  | .normalizeProc (.multiLambda count names body), [.pattern process] =>
      some ([.normalizeProc body], .pattern (.multiLambda count names process))
  | .normalizeProc (.subst body replacement), [.pattern process, .pattern value] =>
      some ([.normalizeProc body, .normalizeProc replacement], .pattern (.subst process value))
  | .normalizeProc (.collection kind processes rest), [.patterns values] =>
      some ([.normalizeList processes], .pattern (.collection kind values rest))
  | .normalizeProc p, [] =>
      match p with
      | .apply "POutput" [_, _] | .apply "PInput" [_, .lambda none _]
      | .apply "PDrop" [_] | .apply "NQuote" [_]
      | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ | .collection _ _ _ => none
      | _ => some ([], .pattern p)
  | .normalizeList [], [] => some ([], .patterns [])
  | .normalizeList (p :: ps), [.pattern out, .patterns outs] =>
      some ([.normalizeProc p, .normalizeList ps], .patterns (out :: outs))
  | .substituteName k replacement name, [.pattern normalized] =>
      some ([.normalizeName name],
        if Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.matchesBinder rhoReflectivePresentation k name then
          .marked replacement true
        else .marked normalized false)
  | .substituteProc k replacement (.bvar n), [] =>
      some ([], .pattern (if n == k then replacement else .bvar n))
  | .substituteProc _ _ (.fvar name), [] => some ([], .pattern (.fvar name))
  | .substituteProc _ _ (.apply "NQuote" [p]), [] =>
      some ([], .pattern (.apply "NQuote" [p]))
  | .substituteProc k replacement (.apply "PDrop" [name]), [.marked out matched] =>
      some ([.substituteName k replacement name], .pattern (match out, matched with
        | .apply "NQuote" [p], true => p
        | _, _ => .apply "PDrop" [out]))
  | .substituteProc k replacement (.apply "POutput" [name, process]), [.marked out _, .pattern body] =>
      some ([.substituteName k replacement name, .substituteProc k replacement process],
        .pattern (.apply "POutput" [out, body]))
  | .substituteProc k replacement (.apply "PInput" [name, .lambda none process]), [.marked out _, .pattern body] =>
      some ([.substituteName k replacement name, .substituteProc (k + 1) replacement process],
        .pattern (.apply "PInput" [out, .lambda none body]))
  | .substituteProc k replacement (.lambda name body), [.pattern out] =>
      some ([.substituteProc (k + 1) replacement body], .pattern (.lambda name out))
  | .substituteProc k replacement (.multiLambda count names body), [.pattern out] =>
      some ([.substituteProc (k + count) replacement body], .pattern (.multiLambda count names out))
  | .substituteProc k replacement (.subst body value), [.pattern out, .pattern outValue] =>
      some ([.substituteProc (k + 1) replacement body, .substituteProc k replacement value],
        .pattern (.subst out outValue))
  | .substituteProc k replacement (.collection kind ps rest), [.patterns outs] =>
      some ([.substituteList k replacement ps], .pattern (.collection kind outs rest))
  | .substituteProc _ _ p, [] =>
      match p with
      | .bvar _ | .fvar _ | .apply "NQuote" [_] | .apply "PDrop" [_]
      | .apply "POutput" [_, _] | .apply "PInput" [_, .lambda none _]
      | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ | .collection _ _ _ => none
      | _ => some ([], .pattern p)
  | .substituteList _ _ [], [] => some ([], .patterns [])
  | .substituteList k replacement (p :: ps), [.pattern out, .patterns outs] =>
      some ([.substituteProc k replacement p, .substituteList k replacement ps], .patterns (out :: outs))
  | .comm body payload, [.pattern normalized, .pattern out] =>
      some ([.normalizeProc payload, .substituteProc 0 (.apply "NQuote" [normalized]) body], .pattern out)
  | _, _ => none

mutual
  /-- Total replay follows the submitted finite tree, checking every child. -/
  def checkTask (task : Task) : Certificate → Bool
    | .node result children =>
        match unfoldCall task (children.map Certificate.result) with
        | none => false
        | some (requests, expected) => decide (result = expected) && checkChildren requests children

  def checkChildren : List Task → List Certificate → Bool
    | [], [] => true
    | task :: tasks, certificate :: certificates =>
        checkTask task certificate && checkChildren tasks certificates
    | _, _ => false
end

theorem unfoldCall_sound {task : Task} {results : List Result} {requests : List Task} {out : Result}
    (expanded : unfoldCall task results = some (requests, out))
    (children : List.Forall₂ (fun task result => task.meaning = result) requests results) :
    task.meaning = out := by
  fun_cases unfoldCall task results <;>
    simp_all only [unfoldCall, Option.some.injEq, Prod.mk.injEq]
  all_goals rcases expanded with ⟨rfl, rfl⟩
  all_goals
    simp_all [Task.meaning, semanticNormalizeName, semanticNormalizeProc,
      semanticNormalizeProcList, semanticSubstNameMark, semanticSubstName,
      semanticSubstProc, semanticSubstProcList, semanticCommSubst]
  case case4 name excluded =>
    cases name using semanticNormalizeName.fun_cases <;>
      simp_all [semanticNormalizeName.eq_1, semanticNormalizeName.eq_2, semanticNormalizeName.eq_5]
  case case21 process a b c d e f g h =>
    cases process using semanticNormalizeProc.fun_cases <;>
      simp_all [semanticNormalizeProc.eq_1, semanticNormalizeProc.eq_2, semanticNormalizeProc.eq_11]
  case case24 index replacement name normalized =>
    by_cases hit : Canonical.canonicalize name = .bvar index <;>
      simp [hit, (matchesBinder_iff index name).not]
  case case28 => rfl

mutual
  theorem checkTask_sound (task : Task) (evidence : Certificate)
      (accepted : checkTask task evidence = true) : task.meaning = evidence.result := by
    cases evidenceEq : evidence with
    | node result children =>
      rw [evidenceEq] at accepted
      cases expanded : unfoldCall task (children.map Certificate.result) with
      | none => simp [checkTask, expanded] at accepted
      | some pair =>
        obtain ⟨requests, expected⟩ := pair
        have checked : result = expected ∧ checkChildren requests children = true := by
          simpa only [checkTask, expanded, Bool.and_eq_true, decide_eq_true_eq] using accepted
        exact (unfoldCall_sound expanded (checkChildren_sound requests children checked.2)).trans
          checked.1.symm
  termination_by sizeOf evidence
  decreasing_by simp_all [Certificate.node.sizeOf_spec]

  theorem checkChildren_sound (tasks : List Task) (evidence : List Certificate)
      (accepted : checkChildren tasks evidence = true) :
      List.Forall₂ (fun task result => task.meaning = result) tasks (evidence.map Certificate.result) := by
    cases tasks with
    | nil => cases evidence <;> simp_all [checkChildren]
    | cons task tasks =>
      cases evidenceEq : evidence with
      | nil => simp [evidenceEq, checkChildren] at accepted
      | cons certificate certificates =>
        rw [evidenceEq] at accepted
        have checked : checkTask task certificate = true ∧ checkChildren tasks certificates = true := by
          simpa only [checkChildren, Bool.and_eq_true] using accepted
        exact .cons (checkTask_sound task certificate checked.1)
          (checkChildren_sound tasks certificates checked.2)
  termination_by sizeOf evidence
  decreasing_by all_goals simp_all [List.cons.sizeOf_spec] <;> omega
end

theorem unfoldCall_source (task : Task) :
    unfoldCall task (task.calls.map Task.meaning) = some (task.calls, task.meaning) := by
  fun_cases Task.calls task <;>
    simp_all [Task.meaning, unfoldCall,
      semanticNormalizeName, semanticNormalizeProc, semanticNormalizeProcList,
      semanticSubstNameMark, semanticSubstName, semanticSubstProc,
      semanticSubstProcList, semanticCommSubst]
  case case3 name excluded =>
    cases name using semanticNormalizeName.fun_cases <;>
      simp_all [semanticNormalizeName.eq_1, semanticNormalizeName.eq_2, semanticNormalizeName.eq_5]
  case case12 process a b c d e f g h =>
    cases process using semanticNormalizeProc.fun_cases <;>
      simp_all [semanticNormalizeProc.eq_1, semanticNormalizeProc.eq_2, semanticNormalizeProc.eq_11]
  case case15 index replacement name =>
    by_cases hit : Canonical.canonicalize name = .bvar index <;>
      simp [hit, (matchesBinder_iff index name).not]
  case case19 => rfl

theorem unfoldCall_requests {task : Task} {results : List Result} {requests : List Task} {out : Result}
    (expanded : unfoldCall task results = some (requests, out))
    (children : List.Forall₂ (fun task result => task.meaning = result) requests results) :
    requests = task.calls := by
  fun_cases unfoldCall task results <;>
    simp_all only [unfoldCall, Option.some.injEq, Prod.mk.injEq]
  all_goals rcases expanded with ⟨rfl, rfl⟩
  all_goals simp_all [Task.calls, Task.meaning]

/-- A source call tree has the original function's literal result and exactly
its recursive source calls, in their original positions. -/
inductive Certificate.Valid : Task → Certificate → Prop where
  | node {task : Task} {result : Result} {children : List Certificate}
      (result_exact : task.meaning = result)
      (children_valid : List.Forall₂ Certificate.Valid task.calls children) :
      Certificate.Valid task (.node result children)

theorem Certificate.Valid.result_exact {task : Task} {evidence : Certificate}
    (valid : evidence.Valid task) : task.meaning = evidence.result := by
  cases valid with
  | node result_exact _ => exact result_exact

private theorem validChildren_results {tasks : List Task} {evidence : List Certificate}
    (valid : List.Forall₂ Certificate.Valid tasks evidence) :
    evidence.map Certificate.result = tasks.map Task.meaning := by
  induction valid with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, ← head.result_exact, ih]

mutual
  theorem checkTask_valid (task : Task) (evidence : Certificate)
      (accepted : checkTask task evidence = true) : evidence.Valid task := by
    cases evidenceEq : evidence with
    | node result children =>
      rw [evidenceEq] at accepted
      cases expanded : unfoldCall task (children.map Certificate.result) with
      | none => simp [checkTask, expanded] at accepted
      | some pair =>
        obtain ⟨requests, expected⟩ := pair
        have checked : result = expected ∧ checkChildren requests children = true := by
          simpa only [checkTask, expanded, Bool.and_eq_true, decide_eq_true_eq] using accepted
        have sourceChildren := checkChildren_sound requests children checked.2
        have sameCalls := unfoldCall_requests expanded sourceChildren
        exact .node ((unfoldCall_sound expanded sourceChildren).trans checked.1.symm)
          (sameCalls ▸ checkChildren_valid requests children checked.2)
  termination_by sizeOf evidence
  decreasing_by simp_all [Certificate.node.sizeOf_spec]

  theorem checkChildren_valid (tasks : List Task) (evidence : List Certificate)
      (accepted : checkChildren tasks evidence = true) :
      List.Forall₂ Certificate.Valid tasks evidence := by
    cases tasks with
    | nil => cases evidence <;> simp_all [checkChildren]
    | cons task tasks =>
      cases evidenceEq : evidence with
      | nil => simp [evidenceEq, checkChildren] at accepted
      | cons certificate certificates =>
        rw [evidenceEq] at accepted
        have checked : checkTask task certificate = true ∧ checkChildren tasks certificates = true := by
          simpa only [checkChildren, Bool.and_eq_true] using accepted
        exact .cons (checkTask_valid task certificate checked.1)
          (checkChildren_valid tasks certificates checked.2)
  termination_by sizeOf evidence
  decreasing_by all_goals simp_all [List.cons.sizeOf_spec] <;> omega
end

mutual
  theorem Certificate.Valid.checked (task : Task) (evidence : Certificate)
      (valid : evidence.Valid task) : checkTask task evidence = true := by
    cases evidenceEq : evidence with
    | node result children =>
      rw [evidenceEq] at valid
      cases valid with
      | node result_exact children_valid =>
        have results := validChildren_results children_valid
        have checked := validChildren_checked task.calls children children_valid
        simp only [checkTask, results, unfoldCall_source, result_exact, decide_true, Bool.true_and]
        exact checked
  termination_by sizeOf evidence
  decreasing_by simp_all [Certificate.node.sizeOf_spec]

  theorem validChildren_checked (tasks : List Task) (evidence : List Certificate)
      (valid : List.Forall₂ Certificate.Valid tasks evidence) :
      checkChildren tasks evidence = true := by
    cases evidenceEq : evidence with
    | nil =>
      rw [evidenceEq] at valid
      cases valid
      rfl
    | cons certificate certificates =>
      rw [evidenceEq] at valid
      cases valid with
      | cons head tail =>
        simp only [checkChildren, Bool.and_eq_true]
        exact ⟨head.checked _ _, validChildren_checked _ _ tail⟩
  termination_by sizeOf evidence
  decreasing_by all_goals simp_all [List.cons.sizeOf_spec] <;> omega
end

theorem checkTask_exact (task : Task) (evidence : Certificate) :
    checkTask task evidence = true ↔ evidence.Valid task :=
  ⟨checkTask_valid task evidence, Certificate.Valid.checked task evidence⟩

theorem Task.calls_length_le_two (task : Task) : task.calls.length ≤ 2 := by
  fun_cases Task.calls task <;> simp_all

private theorem checkChildren_map (tasks : List Task) (produce : Task → Certificate)
    (accepted : ∀ task ∈ tasks, checkTask task (produce task) = true) :
    checkChildren tasks (tasks.map produce) = true := by
  induction tasks with
  | nil => rfl
  | cons task tasks ih =>
      simp only [List.map_cons, checkChildren]
      rw [accepted task (by simp)]
      simp only [Bool.true_and]
      exact ih (fun child member => accepted child (by simp [member]))

theorem checkTask_derive (task : Task) : checkTask task (derive task) = true := by
  rw [derive]
  simp only [checkTask, List.map_map, Function.comp_def, derive_result, List.attach_map_val,
    unfoldCall_source, decide_true, Bool.true_and]
  apply checkChildren_map
  intro child member
  exact checkTask_derive child
termination_by task.weight
decreasing_by exact Task.calls_weight_lt member

/-- Check explicit evidence of the literal COMM contractum. -/
def check (body payload result : Pattern) (evidence : Certificate) : Bool :=
  checkTask (.comm body payload) evidence && decide (evidence.result = .pattern result)

theorem check_exact (body payload result : Pattern) (evidence : Certificate) :
    check body payload result evidence = true ↔
      evidence.Valid (.comm body payload) ∧ evidence.result = .pattern result := by
  simp only [check, Bool.and_eq_true, checkTask_exact, decide_eq_true_eq]

theorem check_sound (body payload result : Pattern) (evidence : Certificate)
    (accepted : check body payload result evidence = true) :
    semanticCommSubst body payload = result := by
  have checked : checkTask (.comm body payload) evidence = true ∧ evidence.result = .pattern result := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using accepted
  exact Result.pattern.inj ((checkTask_sound (.comm body payload) evidence checked.1).trans checked.2)

def certificate (body payload : Pattern) : Certificate := derive (.comm body payload)

theorem check_certificate (body payload : Pattern) :
    check body payload (semanticCommSubst body payload) (certificate body payload) = true := by
  simp only [check, certificate, checkTask_derive, derive_result, Task.meaning, decide_true, Bool.true_and]

theorem check_complete (body payload result : Pattern) :
    (∃ evidence, check body payload result evidence = true) ↔ semanticCommSubst body payload = result := by
  constructor
  · rintro ⟨evidence, accepted⟩
    exact check_sound body payload result evidence accepted
  · intro source
    subst result
    exact ⟨certificate body payload, check_certificate body payload⟩

theorem bare_result_refused (body payload result : Pattern) :
    check body payload result (.node (.pattern result) []) = false := by
  simp only [check, checkTask, unfoldCall, List.map_nil, Bool.false_and]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitutionEvidence

/-!
## Retained semantic substitution

The producer below inspects one task constructor or actual child-reply frame
per request. COMM constructs its substitution task only after receiving the
normalized payload. Frames retain actual values, remaining siblings and paid
prefixes. Assembly uses the existing bounded-arity `unfoldCall`; source
meanings, call trees and certificates are absent from producer transitions.

The independent source-call weight proves completion for every finite Task.
Receipts count declared constructor/frame queries in the same representation;
the final client inspection publishes without another provider charge.
Native VarId/scope/data decoding, capture and payload hooks, memory ownership,
allocation, interning, copying and retirement prices remain service-instance
obligations. This is pure Pattern COMM, not a C-memory refinement, persistent
receive refinement or a whole retained-slot physical bound.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitutionEvidence.Retained

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ScopedDerivedPresentationSyntax
open Mettapedia.Machines
open _root_.CategoryTheory

/-- One bounded constructor inspection. COMM requests only its first child;
its second task must be formed from the actual normalized payload reply. -/
inductive Opening where
  | leaf
  | one (child : Task)
  | two (first second : Task)
  | comm (body payload : Pattern)
  deriving DecidableEq, Repr

def opening : Task → Opening
  | .normalizeName (.apply "NQuote" [.apply "PDrop" [name]]) => .one (.normalizeName name)
  | .normalizeName (.apply "NQuote" [body]) => .one (.normalizeProc body)
  | .normalizeName _ => .leaf
  | .normalizeProc (.apply "POutput" [name, body]) => .two (.normalizeName name) (.normalizeProc body)
  | .normalizeProc (.apply "PInput" [name, .lambda none body]) => .two (.normalizeName name) (.normalizeProc body)
  | .normalizeProc (.apply "PDrop" [name]) => .one (.normalizeName name)
  | .normalizeProc (.apply "NQuote" [body]) => .one (.normalizeProc body)
  | .normalizeProc (.lambda _ body) | .normalizeProc (.multiLambda _ _ body) => .one (.normalizeProc body)
  | .normalizeProc (.subst body replacement) => .two (.normalizeProc body) (.normalizeProc replacement)
  | .normalizeProc (.collection _ children _) => .one (.normalizeList children)
  | .normalizeProc _ => .leaf
  | .normalizeList [] => .leaf
  | .normalizeList (child :: children) => .two (.normalizeProc child) (.normalizeList children)
  | .substituteName _ _ name => .one (.normalizeName name)
  | .substituteProc _ _ (.bvar _) | .substituteProc _ _ (.fvar _)
  | .substituteProc _ _ (.apply "NQuote" [_]) => .leaf
  | .substituteProc k replacement (.apply "PDrop" [name]) => .one (.substituteName k replacement name)
  | .substituteProc k replacement (.apply "POutput" [name, body]) =>
      .two (.substituteName k replacement name) (.substituteProc k replacement body)
  | .substituteProc k replacement (.apply "PInput" [name, .lambda none body]) =>
      .two (.substituteName k replacement name) (.substituteProc (k + 1) replacement body)
  | .substituteProc k replacement (.lambda _ body) => .one (.substituteProc (k + 1) replacement body)
  | .substituteProc k replacement (.multiLambda count _ body) => .one (.substituteProc (k + count) replacement body)
  | .substituteProc k replacement (.subst body value) =>
      .two (.substituteProc (k + 1) replacement body) (.substituteProc k replacement value)
  | .substituteProc k replacement (.collection _ children _) => .one (.substituteList k replacement children)
  | .substituteProc _ _ _ => .leaf
  | .substituteList _ _ [] => .leaf
  | .substituteList k replacement (child :: children) =>
      .two (.substituteProc k replacement child) (.substituteList k replacement children)
  | .comm body payload => .comm body payload

/-- This law uses the independent source call tree only in the proof. -/
theorem opening_source (task : Task) :
    match opening task with
    | .leaf => task.calls = []
    | .one child => task.calls = [child]
    | .two first second => task.calls = [first, second]
    | .comm body payload => task = .comm body payload := by
  fun_cases opening task <;> simp_all [Task.calls]

/-- Exact declared constructor/glue work of the source recursion. This is a
proof reference, never consulted by the retained producer. -/
noncomputable def sourceWork (task : Task) : Nat :=
  1 + task.calls.length + (task.calls.attach.map fun child => sourceWork child.1).sum
termination_by task.weight
decreasing_by exact Task.calls_weight_lt child.2

theorem sourceWork_unfold (task : Task) :
    sourceWork task = 1 + task.calls.length + (task.calls.map sourceWork).sum := by
  rw [sourceWork]
  simp only [List.attach_map_val]

/-- An actual returned child's source, literal value and paid prefix. -/
structure Child where
  task : Task
  result : Result
  work : Nat
  deriving DecidableEq, Repr

inductive Frame where
  | one (source : Task) (started : Nat)
  | first (source sibling : Task) (started : Nat)
  | second (source : Task) (first : Child) (started : Nat)
  | commPayload (body payload : Pattern) (started : Nat)
  | commSubstitution (body payload : Pattern) (normalized : Child) (started : Nat)
  deriving DecidableEq, Repr

inductive Mode where
  | call (task : Task) (started : Nat)
  | returned (task : Task) (result : Result) (started : Nat)
  | finished (task : Task) (result : Result)
  | refused
  deriving DecidableEq, Repr

structure State where
  mode : Mode
  frames : List Frame
  paid : Nat
  deriving DecidableEq, Repr

inductive Reply where
  | pending
  | value (result : Result)
  | refused
  deriving DecidableEq, Repr

/-- Assembly is the already checked 0/1/2-child constructor case. It never
replays a task, traverses a child list or evaluates a source meaning. -/
def assembled (source : Task) (started : Nat) (results : List Result) : Mode :=
  match unfoldCall source results with
  | none => .refused
  | some (_, out) => .returned source out started

/-- The only evaluator transition: one task constructor or one reply frame.
Partially received children and sibling tasks remain in the actual stack. -/
def step (state : State) : Reply × State :=
  let paid := state.paid + 1
  match state.mode with
  | .call task started => match opening task with
    | .leaf => (.pending, ⟨assembled task started [], state.frames, paid⟩)
    | .one child => (.pending, ⟨.call child paid, .one task started :: state.frames, paid⟩)
    | .two first second =>
        (.pending, ⟨.call first paid, .first task second started :: state.frames, paid⟩)
    | .comm body payload =>
        (.pending, ⟨.call (.normalizeProc payload) paid, .commPayload body payload started :: state.frames, paid⟩)
  | .returned task result started => match state.frames with
    | [] => (.value result, ⟨.finished task result, [], paid⟩)
    | .one source parentStarted :: rest =>
        (.pending, ⟨assembled source parentStarted [result], rest, paid⟩)
    | .first source sibling parentStarted :: rest =>
        (.pending, ⟨.call sibling paid,
          .second source ⟨task, result, state.paid - started⟩ parentStarted :: rest, paid⟩)
    | .second source first parentStarted :: rest =>
        (.pending, ⟨assembled source parentStarted [first.result, result], rest, paid⟩)
    | .commPayload body payload parentStarted :: rest => match result with
      | .pattern normalized =>
          (.pending, ⟨.call (.substituteProc 0 (.apply "NQuote" [normalized]) body) paid,
            .commSubstitution body payload ⟨task, result, state.paid - started⟩ parentStarted :: rest, paid⟩)
      | _ => (.refused, ⟨.refused, rest, paid⟩)
    | .commSubstitution body payload normalized parentStarted :: rest =>
        (.pending, ⟨assembled (.comm body payload) parentStarted [normalized.result, result], rest, paid⟩)
  | .finished _ _ | .refused => (.refused, ⟨.refused, state.frames, paid⟩)

def protocol : Mettapedia.TypeTheory.IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Unit
  Position _ := Reply
  next _ _ := ()

def provider : Cursor.Provider protocol where
  State _ _ := State
  step state _ := ⟨(step state).1, (step state).2⟩

inductive Control where
  | pulling
  | returned (answer : Except Unit Result)
  deriving DecidableEq, Repr

def accept : Reply → Control
  | .pending => .pulling
  | .value result => .returned (.ok result)
  | .refused => .returned (.error ())

def client : Cursor.Client (P := protocol) (Return := fun _ _ => Except Unit Result) where
  V _ _ := Control
  str := fun _ _ => TypeCat.ofHom fun control => match control with
    | .returned answer => ⟨.inl answer, fun impossible => nomatch impossible⟩
    | .pulling => ⟨.inr (), accept⟩

abbrev Saved := Nat × Cursor.Outcome provider client ()

def packet (state : State) : Cursor.Packet provider client () := ⟨(), .pulling, state⟩

def advance (allowance : Nat) (state : State) : Saved :=
  Cursor.advance provider client (fun _ _ => 1) allowance (packet state)

def start (task : Task) : Saved := (0, .paused (packet ⟨.call task 0, [], 0⟩))

def resume (allowance : Nat) (saved : Saved) : Saved :=
  Cursor.resume provider client (fun _ _ => 1) allowance saved

def completed (saved : Saved) : Option (Except Unit Result) :=
  match saved.2 with
  | .paused _ => none
  | .done ⟨_, answer, _⟩ => some answer

theorem resume_zero (saved : Saved) : resume 0 saved = saved := Cursor.resume_zero _ _ _ _

theorem pause_composition (first second : Nat) (saved : Saved) :
    resume (first + second) saved = resume second (resume first saved) :=
  Cursor.resume_add _ _ _ first second saved

theorem paused_not_published (paid : Nat) (packet : Cursor.Packet provider client ()) :
    completed (paid, .paused packet) = none := rfl

theorem advance_pending (before after : State) (transition : step before = (.pending, after)) :
    advance 1 before = (1, .paused (packet after)) := by
  simp only [advance, Cursor.advance, packet, client, provider, transition]
  rfl

theorem advance_chain (first second : Nat) (before middle after : State)
    (left : advance first before = (first, .paused (packet middle)))
    (right : advance second middle = (second, .paused (packet after))) :
    advance (first + second) before = (first + second, .paused (packet after)) := by
  unfold advance at *
  rw [Cursor.advance_add, left]
  change (first + (Cursor.advance provider client (fun _ _ => 1) second (packet middle)).1,
    (Cursor.advance provider client (fun _ _ => 1) second (packet middle)).2) = _
  rw [right]

theorem assembled_source (task : Task) (started : Nat) :
    assembled task started (task.calls.map Task.meaning) = .returned task task.meaning started := by
  simp only [assembled, unfoldCall_source]

private theorem eval_leaf (task : Task) (frames : List Frame) (paid : Nat)
    (opened : opening task = .leaf) :
    advance (sourceWork task) ⟨.call task paid, frames, paid⟩ =
      (sourceWork task, .paused (packet ⟨.returned task task.meaning paid,
        frames, paid + sourceWork task⟩)) := by
  have calls : task.calls = [] := by simpa only [opened] using opening_source task
  have work : sourceWork task = 1 := by rw [sourceWork_unfold, calls]; rfl
  have assembledEq : assembled task paid [] = .returned task task.meaning paid := by
    simpa only [calls, List.map_nil] using assembled_source task paid
  rw [work]
  apply advance_pending
  simp only [step, opened, assembledEq]

private theorem eval_one (task child : Task) (frames : List Frame) (paid : Nat)
    (opened : opening task = .one child)
    (childExact : ∀ (frames : List Frame) (paid : Nat),
      advance (sourceWork child) ⟨.call child paid, frames, paid⟩ =
        (sourceWork child, .paused (packet ⟨.returned child child.meaning paid,
          frames, paid + sourceWork child⟩))) :
    advance (sourceWork task) ⟨.call task paid, frames, paid⟩ =
      (sourceWork task, .paused (packet ⟨.returned task task.meaning paid,
        frames, paid + sourceWork task⟩)) := by
  have calls : task.calls = [child] := by simpa only [opened] using opening_source task
  have work : sourceWork task = 1 + sourceWork child + 1 := by
    rw [sourceWork_unfold, calls]
    simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have assembledEq : assembled task paid [child.meaning] = .returned task task.meaning paid := by
    simpa only [calls, List.map_cons, List.map_nil] using assembled_source task paid
  let initial : State := ⟨.call task paid, frames, paid⟩
  let entered : State := ⟨.call child (paid + 1), .one task paid :: frames, paid + 1⟩
  let returned : State := ⟨.returned child child.meaning (paid + 1),
    .one task paid :: frames, paid + 1 + sourceWork child⟩
  let finished : State := ⟨.returned task task.meaning paid,
    frames, paid + 1 + sourceWork child + 1⟩
  have enter : advance 1 initial = (1, .paused (packet entered)) :=
    advance_pending _ _ (by simp only [initial, entered, step, opened])
  have children : advance (sourceWork child) entered =
      (sourceWork child, .paused (packet returned)) := childExact _ _
  have finish : advance 1 returned = (1, .paused (packet finished)) :=
    advance_pending _ _ (by simp only [returned, finished, step, assembledEq])
  have runPrefix := advance_chain 1 (sourceWork child) initial entered returned enter children
  have full := advance_chain (1 + sourceWork child) 1 initial returned finished runPrefix finish
  simpa only [initial, finished, work, Nat.add_assoc] using full

private theorem eval_two (task first second : Task) (frames : List Frame) (paid : Nat)
    (opened : opening task = .two first second)
    (firstExact : ∀ (frames : List Frame) (paid : Nat),
      advance (sourceWork first) ⟨.call first paid, frames, paid⟩ =
        (sourceWork first, .paused (packet ⟨.returned first first.meaning paid,
          frames, paid + sourceWork first⟩)))
    (secondExact : ∀ (frames : List Frame) (paid : Nat),
      advance (sourceWork second) ⟨.call second paid, frames, paid⟩ =
        (sourceWork second, .paused (packet ⟨.returned second second.meaning paid,
          frames, paid + sourceWork second⟩))) :
    advance (sourceWork task) ⟨.call task paid, frames, paid⟩ =
      (sourceWork task, .paused (packet ⟨.returned task task.meaning paid,
        frames, paid + sourceWork task⟩)) := by
  have calls : task.calls = [first, second] := by simpa only [opened] using opening_source task
  have work : sourceWork task = 1 + sourceWork first + 1 + sourceWork second + 1 := by
    rw [sourceWork_unfold, calls]
    simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have assembledEq : assembled task paid [first.meaning, second.meaning] =
      .returned task task.meaning paid := by
    simpa only [calls, List.map_cons, List.map_nil] using assembled_source task paid
  let initial : State := ⟨.call task paid, frames, paid⟩
  let entered : State := ⟨.call first (paid + 1), .first task second paid :: frames, paid + 1⟩
  let firstReturned : State := ⟨.returned first first.meaning (paid + 1),
    .first task second paid :: frames, paid + 1 + sourceWork first⟩
  let firstChild : Child := ⟨first, first.meaning, sourceWork first⟩
  let middle : State := ⟨.call second (paid + 1 + sourceWork first + 1),
    .second task firstChild paid :: frames, paid + 1 + sourceWork first + 1⟩
  let secondReturned : State := ⟨.returned second second.meaning (paid + 1 + sourceWork first + 1),
    .second task firstChild paid :: frames, paid + 1 + sourceWork first + 1 + sourceWork second⟩
  let finished : State := ⟨.returned task task.meaning paid,
    frames, paid + 1 + sourceWork first + 1 + sourceWork second + 1⟩
  have enter : advance 1 initial = (1, .paused (packet entered)) :=
    advance_pending _ _ (by simp only [initial, entered, step, opened])
  have firstRun : advance (sourceWork first) entered =
      (sourceWork first, .paused (packet firstReturned)) := firstExact _ _
  have nextSibling : advance 1 firstReturned = (1, .paused (packet middle)) :=
    advance_pending _ _ (by simp only [firstReturned, middle, firstChild, step, Nat.add_sub_cancel_left])
  have secondRun : advance (sourceWork second) middle =
      (sourceWork second, .paused (packet secondReturned)) := secondExact _ _
  have finish : advance 1 secondReturned = (1, .paused (packet finished)) :=
    advance_pending _ _ (by simp only [secondReturned, finished, firstChild, step, assembledEq])
  have runFirst := advance_chain 1 (sourceWork first) initial entered firstReturned enter firstRun
  have runMiddle := advance_chain (1 + sourceWork first) 1 initial firstReturned middle runFirst nextSibling
  have runSecond := advance_chain (1 + sourceWork first + 1) (sourceWork second)
    initial middle secondReturned runMiddle secondRun
  have runAll := advance_chain (1 + sourceWork first + 1 + sourceWork second) 1
    initial secondReturned finished runSecond finish
  simpa only [initial, finished, work, Nat.add_assoc] using runAll

private theorem eval_comm (body payload : Pattern) (frames : List Frame) (paid : Nat)
    (firstExact : ∀ (frames : List Frame) (paid : Nat),
      advance (sourceWork (.normalizeProc payload)) ⟨.call (.normalizeProc payload) paid, frames, paid⟩ =
        (sourceWork (.normalizeProc payload), .paused (packet
          ⟨.returned (.normalizeProc payload) (Task.normalizeProc payload).meaning paid,
            frames, paid + sourceWork (.normalizeProc payload)⟩)))
    (secondExact : ∀ (frames : List Frame) (paid : Nat),
      advance (sourceWork (.substituteProc 0 (.apply "NQuote" [semanticNormalizeProc payload]) body))
          ⟨.call (.substituteProc 0 (.apply "NQuote" [semanticNormalizeProc payload]) body) paid, frames, paid⟩ =
        (sourceWork (.substituteProc 0 (.apply "NQuote" [semanticNormalizeProc payload]) body),
          .paused (packet
            ⟨.returned (.substituteProc 0 (.apply "NQuote" [semanticNormalizeProc payload]) body)
              (Task.substituteProc 0 (.apply "NQuote" [semanticNormalizeProc payload]) body).meaning paid,
              frames, paid + sourceWork (.substituteProc 0 (.apply "NQuote" [semanticNormalizeProc payload]) body)⟩))) :
    advance (sourceWork (.comm body payload)) ⟨.call (.comm body payload) paid, frames, paid⟩ =
      (sourceWork (.comm body payload), .paused (packet ⟨.returned (.comm body payload)
        (Task.comm body payload).meaning paid, frames, paid + sourceWork (.comm body payload)⟩)) := by
  let task := Task.comm body payload
  let first := Task.normalizeProc payload
  let second := Task.substituteProc 0 (.apply "NQuote" [semanticNormalizeProc payload]) body
  have calls : task.calls = [first, second] := rfl
  have work : sourceWork task = 1 + sourceWork first + 1 + sourceWork second + 1 := by
    rw [sourceWork_unfold, calls]
    simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have assembledEq : assembled task paid [first.meaning, second.meaning] =
      .returned task task.meaning paid := by
    simpa only [calls, List.map_cons, List.map_nil] using assembled_source task paid
  change assembled (Task.comm body payload) paid [first.meaning, second.meaning] =
    .returned task task.meaning paid at assembledEq
  let initial : State := ⟨.call task paid, frames, paid⟩
  let entered : State := ⟨.call first (paid + 1), .commPayload body payload paid :: frames, paid + 1⟩
  let firstReturned : State := ⟨.returned first first.meaning (paid + 1),
    .commPayload body payload paid :: frames, paid + 1 + sourceWork first⟩
  let firstChild : Child := ⟨first, first.meaning, sourceWork first⟩
  let middle : State := ⟨.call second (paid + 1 + sourceWork first + 1),
    .commSubstitution body payload firstChild paid :: frames, paid + 1 + sourceWork first + 1⟩
  let secondReturned : State := ⟨.returned second second.meaning (paid + 1 + sourceWork first + 1),
    .commSubstitution body payload firstChild paid :: frames,
    paid + 1 + sourceWork first + 1 + sourceWork second⟩
  let finished : State := ⟨.returned task task.meaning paid,
    frames, paid + 1 + sourceWork first + 1 + sourceWork second + 1⟩
  have enter : advance 1 initial = (1, .paused (packet entered)) :=
    advance_pending _ _ (by simp only [initial, entered, task, first, step, opening])
  have firstRun : advance (sourceWork first) entered =
      (sourceWork first, .paused (packet firstReturned)) := firstExact _ _
  have nextSibling : advance 1 firstReturned = (1, .paused (packet middle)) :=
    advance_pending _ _ (by
      simp only [firstReturned, middle, firstChild, step, first, Task.meaning, Nat.add_sub_cancel_left]
      rfl)
  have secondRun : advance (sourceWork second) middle =
      (sourceWork second, .paused (packet secondReturned)) := secondExact _ _
  have finish : advance 1 secondReturned = (1, .paused (packet finished)) :=
    advance_pending _ _ (by simp only [secondReturned, finished, firstChild, step, assembledEq])
  have runFirst := advance_chain 1 (sourceWork first) initial entered firstReturned enter firstRun
  have runMiddle := advance_chain (1 + sourceWork first) 1 initial firstReturned middle runFirst nextSibling
  have runSecond := advance_chain (1 + sourceWork first + 1) (sourceWork second)
    initial middle secondReturned runMiddle secondRun
  have runAll := advance_chain (1 + sourceWork first + 1 + sourceWork second) 1
    initial secondReturned finished runSecond finish
  change advance (sourceWork task) initial =
    (sourceWork task, .paused (packet ⟨.returned task task.meaning paid, frames, paid + sourceWork task⟩))
  simpa only [initial, finished, work, Nat.add_assoc] using runAll

/-- Every finite source task reaches its actual return frame. The proof composes
real cursor prefixes; no certificate or source meaning is run by the producer. -/
theorem evaluate_exact (task : Task) (frames : List Frame) (paid : Nat) :
    advance (sourceWork task) ⟨.call task paid, frames, paid⟩ =
      (sourceWork task, .paused (packet ⟨.returned task task.meaning paid,
        frames, paid + sourceWork task⟩)) := by
  induction task using (measure Task.weight).wf.induction generalizing frames paid with
  | h task ih =>
    cases opened : opening task with
    | leaf => exact eval_leaf task frames paid opened
    | one child =>
      have calls : task.calls = [child] := by simpa only [opened] using opening_source task
      exact eval_one task child frames paid opened
        (ih child (Task.calls_weight_lt (by simp [calls])))
    | two first second =>
      have calls : task.calls = [first, second] := by simpa only [opened] using opening_source task
      exact eval_two task first second frames paid opened
        (ih first (Task.calls_weight_lt (by simp [calls])))
        (ih second (Task.calls_weight_lt (by simp [calls])))
    | comm body payload =>
      have source : task = .comm body payload := by simpa only [opened] using opening_source task
      subst task
      exact eval_comm body payload frames paid
        (ih (.normalizeProc payload) (Task.calls_weight_lt (by simp [Task.calls])))
        (ih (.substituteProc 0 (.apply "NQuote" [semanticNormalizeProc payload]) body)
          (Task.calls_weight_lt (by simp [Task.calls])))

theorem root_return (task : Task) (result : Result) (started paid : Nat) :
    advance 2 ⟨.returned task result started, [], paid⟩ =
      (1, .done ⟨(), .ok result, ⟨.finished task result, [], paid + 1⟩⟩) := by
  simp only [advance, Cursor.advance, packet, client, provider, step]
  rfl

/-- Every finite task finishes through the real client. Publication adds one
provider reply and one uncharged client inspection to the internal traversal. -/
theorem completion_exact (task : Task) :
    resume (sourceWork task + 2) (start task) =
      (sourceWork task + 1, .done ⟨(), .ok task.meaning,
        ⟨.finished task task.meaning, [], sourceWork task + 1⟩⟩) := by
  have evaluated := evaluate_exact task [] 0
  have returned := root_return task task.meaning 0 (sourceWork task)
  unfold advance at evaluated returned
  unfold resume start
  change (0 + (Cursor.advance provider client (fun _ _ => 1) (sourceWork task + 2)
    (packet ⟨.call task 0, [], 0⟩)).1,
    (Cursor.advance provider client (fun _ _ => 1) (sourceWork task + 2)
      (packet ⟨.call task 0, [], 0⟩)).2) = _
  rw [Cursor.advance_add, evaluated]
  change (0 + (sourceWork task + (Cursor.advance provider client (fun _ _ => 1) 2
    (packet ⟨.returned task task.meaning 0, [], 0 + sourceWork task⟩)).1),
    (Cursor.advance provider client (fun _ _ => 1) 2
      (packet ⟨.returned task task.meaning 0, [], 0 + sourceWork task⟩)).2) = _
  simp only [Nat.zero_add, returned]

/-- Finite completion is unconditional on a precomputed certificate. -/
theorem finite_completion (task : Task) :
    ∃ allowance, completed (resume allowance (start task)) = some (.ok task.meaning) := by
  exact ⟨sourceWork task + 2, by rw [completion_exact]; rfl⟩

theorem completed_inert (allowance : Nat) (saved : Saved) (answer : Except Unit Result)
    (published : completed saved = some answer) : resume allowance saved = saved := by
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => simp only [completed, reduceCtorEq] at published
  | done result => rfl

/-- Any completed prefix is the same actual finished packet and exact receipt,
including its provider state, as the finite run. -/
theorem completed_prefix_exact (task : Task) (allowance : Nat) (answer : Except Unit Result)
    (published : completed (resume allowance (start task)) = some answer) :
    resume allowance (start task) =
      (sourceWork task + 1, .done ⟨(), .ok task.meaning,
        ⟨.finished task task.meaning, [], sourceWork task + 1⟩⟩) := by
  calc
    resume allowance (start task) =
        resume (sourceWork task + 2) (resume allowance (start task)) :=
      (completed_inert _ _ _ published).symm
    _ = resume allowance (resume (sourceWork task + 2) (start task)) := by
      rw [← pause_composition, Nat.add_comm, pause_composition]
    _ = _ := by rw [completion_exact]; rfl

theorem completed_sound (task : Task) (allowance : Nat) (answer : Except Unit Result)
    (published : completed (resume allowance (start task)) = some answer) :
    answer = .ok task.meaning := by
  rw [completed_prefix_exact task allowance answer published] at published
  exact (Option.some.inj published).symm

theorem step_paid (state : State) : (step state).2.paid = state.paid + 1 := by
  rcases state with ⟨mode, frames, paid⟩
  cases mode with
  | call task started => simp only [step]; cases opening task <;> rfl
  | returned task result started =>
    cases frames with
    | nil => rfl
    | cons frame rest =>
      cases frame <;> try rfl
      cases result <;> rfl
  | finished task result => rfl
  | refused => rfl

def outcomePaid : Cursor.Outcome provider client () → Nat
  | .paused packet => packet.2.2.paid
  | .done result => result.2.2.paid

theorem cursor_succ (allowance : Nat) (state : State) :
    Cursor.advance provider client (fun _ _ => 1) (base := ()) (allowance + 1) ⟨(), .pulling, state⟩ =
      let next := step state
      let rest := Cursor.advance provider client (fun _ _ => 1) (base := ()) allowance
        ⟨(), accept next.1, next.2⟩
      (1 + rest.1, rest.2) := by
  simp only [Cursor.advance, client, provider]
  cases (step state).1 <;> rfl

theorem advance_paid (allowance : Nat) (control : Control) (state : State) :
    (Cursor.advance provider client (fun _ _ => 1) (base := ()) allowance ⟨(), control, state⟩).1 + state.paid =
      outcomePaid (Cursor.advance provider client (fun _ _ => 1) (base := ()) allowance ⟨(), control, state⟩).2 := by
  induction allowance generalizing control state with
  | zero => simp only [Cursor.advance, outcomePaid, Nat.zero_add]
  | succ allowance ih =>
    cases control with
    | returned answer =>
      simp only [Cursor.advance, client]
      change 0 + state.paid = state.paid
      exact Nat.zero_add _
    | pulling =>
      rw [cursor_succ]
      dsimp only
      have rest := ih (accept (step state).1) (step state).2
      rw [step_paid] at rest
      omega

/-- Non-root child results cannot publish a provider value. -/
theorem value_requires_empty_stack (state : State) (result : Result)
    (value : (step state).1 = .value result) : state.frames = [] := by
  rcases state with ⟨mode, frames, paid⟩
  cases mode with
  | call task started =>
    cases opened : opening task <;> simp [step, opened] at value
  | returned task out started =>
    cases frames with
    | nil => rfl
    | cons frame rest =>
      cases frame with
      | one source started => simp [step] at value
      | first source sibling started => simp [step] at value
      | second source first started => simp [step] at value
      | commPayload body payload started => cases out <;> simp [step] at value
      | commSubstitution body payload normalized started => simp [step] at value
  | finished task out => simp [step] at value
  | refused => simp [step] at value

/-- One actual normalized-payload reply determines the second COMM task.
Neither the source normalizer nor a predicted reply is evaluated here. -/
theorem comm_reply_schedules_actual (body payload normalized : Pattern)
    (source : Task) (started parentStarted paid : Nat) (rest : List Frame) :
    step ⟨.returned source (.pattern normalized) started,
      .commPayload body payload parentStarted :: rest, paid⟩ =
      (.pending, ⟨.call (.substituteProc 0 (.apply "NQuote" [normalized]) body) (paid + 1),
        .commSubstitution body payload ⟨source, .pattern normalized, paid - started⟩ parentStarted :: rest,
        paid + 1⟩) := rfl

/-- The first reply and its exact local bill remain in the frame while the
second sibling runs; no prefix is replayed to reconstruct them. -/
theorem first_reply_retained (source first sibling : Task) (result : Result)
    (started parentStarted paid : Nat) (rest : List Frame) :
    step ⟨.returned first result started, .first source sibling parentStarted :: rest, paid⟩ =
      (.pending, ⟨.call sibling (paid + 1),
        .second source ⟨first, result, paid - started⟩ parentStarted :: rest, paid + 1⟩) := rfl

theorem resume_paid (allowance : Nat) (saved : Saved)
    (balanced : saved.1 = outcomePaid saved.2) :
    (resume allowance saved).1 = outcomePaid (resume allowance saved).2 := by
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | done result => exact balanced
  | paused packet =>
    rcases packet with ⟨index, control, state⟩
    cases index
    have rest := advance_paid allowance control state
    change paid = state.paid at balanced
    change paid + (Cursor.advance provider client (fun _ _ => 1) allowance
        (base := ()) ⟨(), control, state⟩).1 =
      outcomePaid (Cursor.advance provider client (fun _ _ => 1) allowance
        (base := ()) ⟨(), control, state⟩).2
    omega

theorem prefix_paid (task : Task) (allowance : Nat) :
    (resume allowance (start task)).1 = outcomePaid (resume allowance (start task)).2 :=
  resume_paid allowance (start task) rfl

theorem resume_start (task : Task) (allowance : Nat) :
    resume allowance (start task) = advance allowance ⟨.call task 0, [], 0⟩ := by
  simp only [resume, start, Cursor.resume, advance, Nat.zero_add]

/-- A completed client consumes a final uncharged inspection. This bounds
scheduler inspections, not elapsed work or a native provider implementation. -/
theorem done_charge_lt (allowance : Nat) (control : Control) (state : State)
    (finished : Cursor.Finished provider (Return := fun _ _ => Except Unit Result) ())
    (done : (Cursor.advance provider client (fun _ _ => 1) allowance
      (base := ()) ⟨(), control, state⟩).2 = .done finished) :
    (Cursor.advance provider client (fun _ _ => 1) allowance
      (base := ()) ⟨(), control, state⟩).1 < allowance := by
  induction allowance generalizing control state with
  | zero => simp only [Cursor.advance, reduceCtorEq] at done
  | succ allowance ih =>
    cases control with
    | returned answer =>
      simp only [Cursor.advance, client]
      change 0 < allowance + 1
      omega
    | pulling =>
      rw [cursor_succ] at done ⊢
      dsimp only at done ⊢
      have rest := ih (accept (step state).1) (step state).2 done
      omega

theorem completed_requires_allowance (task : Task) (allowance : Nat) (answer : Except Unit Result)
    (published : completed (resume allowance (start task)) = some answer) :
    sourceWork task + 2 ≤ allowance := by
  have exactRun := completed_prefix_exact task allowance answer published
  have paidEq := congrArg Prod.fst exactRun
  rcases savedEq : resume allowance (start task) with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => simp only [savedEq, completed, reduceCtorEq] at published
  | done finished =>
    have finishedEq : (Cursor.advance provider client (fun _ _ => 1) allowance
        (packet ⟨.call task 0, [], 0⟩)).2 = .done finished := by
      change (advance allowance ⟨.call task 0, [], 0⟩).2 = _
      rw [← resume_start, savedEq]
    have strict := done_charge_lt allowance .pulling ⟨.call task 0, [], 0⟩ finished finishedEq
    change (advance allowance ⟨.call task 0, [], 0⟩).1 < allowance at strict
    rw [← resume_start, savedEq] at strict
    rw [savedEq] at paidEq
    dsimp only at paidEq strict
    omega

/-- No partial child, root reply or prefix before the final client inspection
is exposed as completed output. -/
theorem unfinished_not_published (task : Task) (allowance : Nat)
    (unfinished : allowance < sourceWork task + 2) :
    completed (resume allowance (start task)) = none := by
  cases published : completed (resume allowance (start task)) with
  | none => rfl
  | some answer =>
    have bound := completed_requires_allowance task allowance answer published
    omega

theorem completed_comm_residual (body payload result : Pattern) (allowance : Nat)
    (published : completed (resume allowance (start (.comm body payload))) = some (.ok (.pattern result))) :
    ProcResidualEquiv result (semanticCommRepresentative body payload) := by
  have sound := completed_sound (.comm body payload) allowance (.ok (.pattern result)) published
  have equal : result = semanticCommSubst body payload := Result.pattern.inj (Except.ok.inj sound)
  rw [equal]
  exact semanticCommSubst_transport_to_representative body payload

theorem completed_substitution_list_length (index : Nat) (replacement : Pattern)
    (source result : List Pattern) (allowance : Nat)
    (published : completed (resume allowance (start (.substituteList index replacement source))) =
      some (.ok (.patterns result))) : result.length = source.length := by
  have sound := completed_sound (.substituteList index replacement source) allowance (.ok (.patterns result)) published
  have equal : result = semanticSubstProcList index replacement source := Result.patterns.inj (Except.ok.inj sound)
  rw [equal]
  exact semanticSubstProcList_length index replacement source

theorem opening_input_depth (index : Nat) (replacement name body : Pattern) :
    opening (.substituteProc index replacement (.apply "PInput" [name, .lambda none body])) =
      .two (.substituteName index replacement name) (.substituteProc (index + 1) replacement body) := rfl

theorem opening_multilambda_depth (index count : Nat) (replacement body : Pattern)
    (names : List String) :
    opening (.substituteProc index replacement (.multiLambda count names body)) =
      .one (.substituteProc (index + count) replacement body) := rfl

theorem opening_subst_depth (index : Nat) (replacement body value : Pattern) :
    opening (.substituteProc index replacement (.subst body value)) =
      .two (.substituteProc (index + 1) replacement body) (.substituteProc index replacement value) := rfl

theorem opening_list_head_tail (index : Nat) (replacement child : Pattern) (tail : List Pattern) :
    opening (.substituteList index replacement (child :: tail)) =
      .two (.substituteProc index replacement child) (.substituteList index replacement tail) := rfl

/-- Quoted syntax is an opaque leaf even when its contents are arbitrarily large. -/
theorem quote_opaque_execution (index : Nat) (replacement body : Pattern) :
    resume 3 (start (.substituteProc index replacement (.apply "NQuote" [body]))) =
      (2, .done ⟨(), .ok (.pattern (.apply "NQuote" [body])),
        ⟨.finished (.substituteProc index replacement (.apply "NQuote" [body]))
          (.pattern (.apply "NQuote" [body])), [], 2⟩⟩) := by
  rfl

/-- Equal quoted values are insufficient to expose a drop: the actual child
reply must carry the match bit. -/
theorem drop_false_does_not_expose (index started : Nat) (replacement name body : Pattern) :
    assembled (.substituteProc index replacement (.apply "PDrop" [name])) started
      [.marked (.apply "NQuote" [body]) false] =
      .returned (.substituteProc index replacement (.apply "PDrop" [name]))
        (.pattern (.apply "PDrop" [.apply "NQuote" [body]])) started := rfl

theorem drop_true_exposes (index started : Nat) (replacement name body : Pattern) :
    assembled (.substituteProc index replacement (.apply "PDrop" [name])) started
      [.marked (.apply "NQuote" [body]) true] =
      .returned (.substituteProc index replacement (.apply "PDrop" [name])) (.pattern body) started := rfl

/-- Equal source children remain separate occurrences. Work is in the declared
constructor/glue currency and is exact for this same source representation. -/
theorem sourceWork_replicate (index count : Nat) (replacement : Pattern) :
    sourceWork (.substituteList index replacement (List.replicate count (.bvar index))) = 4 * count + 1 := by
  have leaf : sourceWork (.substituteProc index replacement (.bvar index)) = 1 := by
    rw [sourceWork_unfold]
    rfl
  induction count with
  | zero => rw [List.replicate_zero, sourceWork_unfold]; rfl
  | succ count ih =>
    rw [List.replicate_succ, sourceWork_unfold]
    change 1 + 2 + (sourceWork (.substituteProc index replacement (.bvar index)) +
      (sourceWork (.substituteList index replacement (List.replicate count (.bvar index))) + 0)) = _
    rw [leaf, ih]
    omega

theorem replicate_completion (index count : Nat) (replacement : Pattern) :
    resume (4 * count + 3)
      (start (.substituteList index replacement (List.replicate count (.bvar index)))) =
      (4 * count + 2, .done ⟨(), .ok (.patterns (List.replicate count replacement)),
        ⟨.finished (.substituteList index replacement (List.replicate count (.bvar index)))
          (.patterns (List.replicate count replacement)), [], 4 * count + 2⟩⟩) := by
  have values : (Task.substituteList index replacement (List.replicate count (.bvar index))).meaning =
      .patterns (List.replicate count replacement) := by
    change Result.patterns (semanticSubstProcList index replacement (List.replicate count (.bvar index))) = _
    congr 1
    induction count with
    | zero => rfl
    | succ count ih => simp only [List.replicate_succ, semanticSubstProcList, semanticSubstProc, beq_self_eq_true, ↓reduceIte, ih]
  have run := completion_exact (.substituteList index replacement (List.replicate count (.bvar index)))
  simpa only [sourceWork_replicate, values, Nat.add_assoc, Nat.reduceAdd] using run

def retainedState (saved : Saved) : State :=
  match saved.2 with
  | .paused packet => packet.2.2
  | .done result => result.2.2

/-- Scope and sort preservation uses the existing quote-aware source theorem.
The retained evaluator does not weaken source admission to obtain completion. -/
theorem completed_comm_preserves
    {free : FreeSortContext} {body payload result : Pattern} (allowance : Nat)
    (bodyTyped : ProcWellSorted rhoReflectivePresentation free
      [rhoReflectivePresentation.nameSort] body)
    (bodySafe : binderSafeAt "NQuote" 1 body = true)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free [] payload)
    (payloadSafe : binderSafeAt "NQuote" 0 payload = true)
    (published : completed (resume allowance (start (.comm body payload))) = some (.ok (.pattern result))) :
    ProcWellSorted rhoReflectivePresentation free [] result ∧
      binderSafeAt "NQuote" 0 result = true := by
  have sound := completed_sound (.comm body payload) allowance (.ok (.pattern result)) published
  have equal : result = semanticCommSubst body payload := Result.pattern.inj (Except.ok.inj sound)
  rw [equal]
  exact ScopedSemanticSubstitution.semanticCommSubst_preserves bodyTyped bodySafe payloadTyped payloadSafe

namespace Controls

private def drop (name : Pattern) : Pattern := .apply "PDrop" [name]
private def quote (body : Pattern) : Pattern := .apply "NQuote" [body]
private def replacement : Pattern := quote (.fvar "r")
private def payload : Pattern := drop (quote (drop (.fvar "x")))
private def body : Pattern := drop (.bvar 0)
private def task : Task := .comm body payload

/-- Genuine initial-open cut: only normalization has been requested. -/
theorem comm_first_request :
    retainedState (resume 1 (start task)) =
      ⟨.call (.normalizeProc payload) 1, [.commPayload body payload 0], 1⟩ := by decide

/-- The normalized reply is retained before constructing any substitution task. -/
theorem comm_normalized_reply_cut :
    retainedState (resume 6 (start task)) =
      ⟨.returned (.normalizeProc payload) (.pattern (drop (.fvar "x"))) 1,
        [.commPayload body payload 0], 6⟩ ∧
      completed (resume 6 (start task)) = none := by decide

/-- A legal continuation consumes that exact reply, including its bill. -/
theorem comm_actual_reply_continuation :
    retainedState (resume 7 (start task)) =
      ⟨.call (.substituteProc 0 (quote (drop (.fvar "x"))) body) 7,
        [.commSubstitution body payload
          ⟨.normalizeProc payload, .pattern (drop (.fvar "x")), 5⟩ 0], 7⟩ := by decide

theorem comm_normalizes_before_substitution :
    completed (resume 15 (start task)) = some (.ok (.pattern (drop (.fvar "x")))) ∧
      completed (resume 15 (start task)) ≠ some (.ok (.pattern payload)) := by decide

theorem comm_exact_receipt : (resume 15 (start task)).1 = 14 := by decide

theorem comm_reply_before_publication :
    completed (resume 14 (start task)) = none ∧
      retainedState (resume 14 (start task)) =
        ⟨.finished task (.pattern (drop (.fvar "x"))), [], 14⟩ := by decide

theorem comm_split_retains_actual_continuation :
    resume 8 (resume 7 (start task)) = resume 15 (start task) := by
  exact (pause_composition 7 8 (start task)).symm

theorem zero_retains_actual_continuation :
    resume 0 (resume 7 (start task)) = resume 7 (start task) := resume_zero _

theorem quoted_code_is_opaque :
    completed (resume 3 (start (.substituteProc 0 replacement (quote (drop (.bvar 0)))))) =
      some (.ok (.pattern (quote (drop (.bvar 0))))) ∧
    completed (resume 3 (start (.substituteProc 0 replacement (quote (drop (.bvar 0)))))) ≠
      some (.ok (.pattern (quote (.fvar "r")))) := by decide

theorem normalized_name_matches :
    completed (resume 7 (start (.substituteName 0 replacement (quote (drop (.bvar 0)))))) =
      some (.ok (.marked replacement true)) := by decide

theorem unequal_name_does_not_match :
    completed (resume 5 (start (.substituteName 0 replacement (.bvar 1)))) =
      some (.ok (.marked (.bvar 1) false)) := by decide

theorem equal_quote_without_match_not_exposed :
    completed (resume 9 (start (.substituteProc 0 replacement (drop replacement)))) =
      some (.ok (.pattern (drop replacement))) ∧
    completed (resume 9 (start (.substituteProc 0 replacement (drop replacement)))) ≠
      some (.ok (.pattern (.fvar "r"))) := by decide

theorem matched_drop_is_exposed :
    completed (resume 7 (start (.substituteProc 0 replacement (drop (.bvar 0))))) =
      some (.ok (.pattern (.fvar "r"))) := by decide

theorem input_shifts_only_body_depth :
    completed (resume 64 (start (.substituteProc 0 replacement
      (.apply "PInput" [.bvar 0, .lambda none (.collection .vec [.bvar 0, .bvar 1, .bvar 2] none)])))) =
      some (.ok (.pattern (.apply "PInput" [replacement,
        .lambda none (.collection .vec [.bvar 0, replacement, .bvar 2] none)]))) := by decide

theorem lambda_protects_inner_binder :
    completed (resume 5 (start (.substituteProc 0 replacement (.lambda none (.bvar 0))))) =
      some (.ok (.pattern (.lambda none (.bvar 0)))) ∧
    completed (resume 5 (start (.substituteProc 0 replacement (.lambda none (.bvar 1))))) =
      some (.ok (.pattern (.lambda none replacement))) := by decide

theorem multilambda_uses_declared_count :
    completed (resume 32 (start (.substituteProc 0 replacement
      (.multiLambda 2 ["a", "b"] (.collection .vec [.bvar 0, .bvar 1, .bvar 2] none))))) =
      some (.ok (.pattern (.multiLambda 2 ["a", "b"]
        (.collection .vec [.bvar 0, .bvar 1, replacement] none)))) := by decide

theorem subst_shifts_body_but_not_value :
    completed (resume 7 (start (.substituteProc 0 replacement (.subst (.bvar 1) (.bvar 0))))) =
      some (.ok (.pattern (.subst replacement replacement))) := by decide

theorem duplicates_and_list_order_preserved :
    completed (resume 15 (start (.substituteList 0 replacement [.bvar 0, .bvar 0, .fvar "z"]))) =
      some (.ok (.patterns [replacement, replacement, .fvar "z"])) ∧
    completed (resume 15 (start (.substituteList 0 replacement [.bvar 0, .bvar 0, .fvar "z"]))) ≠
      some (.ok (.patterns [replacement, .fvar "z"])) ∧
    completed (resume 15 (start (.substituteList 0 replacement [.bvar 0, .bvar 0, .fvar "z"]))) ≠
      some (.ok (.patterns [.fvar "z", replacement, replacement])) := by decide

theorem first_child_reply_and_bill_saved :
    retainedState (resume 3 (start (.substituteList 0 replacement [.bvar 0, .fvar "z"]))) =
      ⟨.call (.substituteList 0 replacement [.fvar "z"]) 3,
        [.second (.substituteList 0 replacement [.bvar 0, .fvar "z"])
          ⟨.substituteProc 0 replacement (.bvar 0), .pattern replacement, 1⟩ 0], 3⟩ ∧
    completed (resume 3 (start (.substituteList 0 replacement [.bvar 0, .fvar "z"]))) = none := by decide

theorem empty_and_single_outputs :
    completed (resume 3 (start (.substituteList 0 replacement []))) = some (.ok (.patterns [])) ∧
    completed (resume 7 (start (.substituteList 0 replacement [.bvar 0]))) =
      some (.ok (.patterns [replacement])) := by decide

theorem wide_duplicate_inventory_and_receipt :
    completed (resume 259 (start (.substituteList 0 replacement (List.replicate 64 (.bvar 0))))) =
      some (.ok (.patterns (List.replicate 64 replacement))) ∧
    (resume 259 (start (.substituteList 0 replacement (List.replicate 64 (.bvar 0))))).1 = 258 := by
  have run := replicate_completion 0 64 replacement
  constructor
  · change completed (resume (4 * 64 + 3)
      (start (.substituteList 0 replacement (List.replicate 64 (.bvar 0))))) = _
    rw [run]
    rfl
  · exact congrArg Prod.fst run

theorem unknown_constructor_remains_literal :
    completed (resume 3 (start (.substituteProc 0 replacement (.apply "Data" [.bvar 0])))) =
      some (.ok (.pattern (.apply "Data" [.bvar 0]))) := by decide

theorem closed_comm_preservation :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] (.apply "PZero" []) ∧
      binderSafeAt "NQuote" 0 (.apply "PZero" []) = true := by
  apply completed_comm_preserves (body := .apply "PDrop" [.bvar 0])
    (payload := .apply "PZero" []) 11
  · exact .drop (.bvar (by decide))
  · decide
  · exact .unit
  · decide
  · decide

/-- Raw finite-task execution does not license a source with an escaped binder. -/
theorem opaque_raw_quote_does_not_erase_scope_gate :
    binderSafeAt "NQuote" 1 (quote (drop (.bvar 0))) = false ∧
    completed (resume 3 (start (.substituteProc 0 replacement (quote (drop (.bvar 0)))))) =
      some (.ok (.pattern (quote (drop (.bvar 0))))) := by decide

end Controls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitutionEvidence.Retained
