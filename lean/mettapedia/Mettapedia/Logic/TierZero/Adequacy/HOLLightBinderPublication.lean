import Mettapedia.Logic.TierZero.Adequacy.HOLLightLocatedAdequacy
import Mettapedia.Languages.HOLLight.ProofSystem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Counting
import Mettapedia.Logic.HOL.Embedding.ConversionPrice

/-! A five-inference HOL Light proof with a free function, a declared predicate
and a bound argument. The expected sequent is built independently of replay.
Its hypothesis and conclusion both have typed images in the dependent core. -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightBinderPublication

open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.FirstOrder
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open HOL.Embedding.SimpleSliceOfDependent

private def a := Ty.var (Name.global "A")
private def predName : Const := .mk (Name.global "cross_pred") .undefined
private def x (t : Ty) : SourceVar := ⟨Name.global "x", t⟩
private def g (t : Ty) : SourceVar := ⟨Name.global "g", .function t .bool⟩
private def f (t : Ty) := CanonicalTerm.constant predName (.function t .bool)
private def right (t : Ty) := CanonicalTerm.free (g t)
private def hyp (t : Ty) := CanonicalTerm.equalityOfSameType (f t) (right t) rfl
private def lhs (t : Ty) := CanonicalTerm.applicationOfFunction (f t) (.free (x t)) .bool (by simp [f, CanonicalTerm.constant, CanonicalTerm.free, x])
private def rhs (t : Ty) := CanonicalTerm.applicationOfFunction (right t) (.free (x t)) .bool (by simp [right, g, CanonicalTerm.free, x])
private def concl (t : Ty) := CanonicalTerm.equalityOfSameType
  (.abstractFree (x t) (lhs t)) (.abstractFree (x t) (rhs t)) rfl

def claim (t : Ty) : Theorem := Theorem.emptyResult {hyp t} (concl t)

private def vx := CanonicalTerm.free (x a)
private def reflX := Theorem.emptyResult ∅ (CanonicalTerm.equalityOfSameType vx vx rfl)
private def assumed := Theorem.emptyResult {hyp a} (hyp a)
private def applied := Theorem.emptyResult {hyp a} (CanonicalTerm.equalityOfSameType (lhs a) (rhs a) rfl)

private def node (i : Nat) (out : Theorem) (request : InferenceRequest)
    (parents : List Nat) : ProofExecution.Receipt :=
  ⟨out, .inference request, parents, ("BINDER_PUBLICATION", i)⟩

def certificate : ProofSystem.Certificate := ([
  node 0 reflX (.refl vx) [],
  node 1 assumed (.assume (hyp a)) [],
  node 2 applied (.mkComb assumed reflX) [1, 0],
  node 3 (claim a) (.abs (x a) applied) [2],
  node 4 (claim .bool) (.instType [(.bool, a)] (claim a)) [3]], 4)

theorem replay : (ProofSystem.checker emptyAxiomPolicy).check (claim .bool) certificate = true := by
  decide +kernel

theorem protected_run : InferenceKernelReachability.Reaches (validatedHolCalculus [])
    (sequentJ (claim .bool).sequent) := by
  apply (HOLLightLocatedAdequacy.validated_reaches_iff_derives [] emptyAxiomPolicy
    (by simp) (fun _ h => False.elim h) _).2
  exact ⟨_, (ProofSystem.checker_authority _).sound _ _ replay, rfl⟩

theorem rejects_erasure : (ProofSystem.checker emptyAxiomPolicy).check
    (Theorem.emptyResult ∅ (concl .bool)) certificate = false := by decide +kernel

private abbrev Fn := HOL.Ty.arr (Base := AtomicTy) .prop .prop

private def leftFn {Γ : HOL.Ctx AtomicTy} : HOL.Term Symbol Γ Fn :=
  .const (.constant predName (.function .bool .bool) (by simp))
private def rightFn {Γ : HOL.Ctx AtomicTy} : HOL.Term Symbol Γ Fn :=
  .const (.variable (g .bool) (by simp [g]))

def assumptionImage : HOL.Term Symbol [] .prop := .eq leftFn rightFn
def conclusionImage : HOL.Term Symbol [] .prop :=
  .eq (.lam (.app leftFn (.var .vz))) (.lam (.app rightFn (.var .vz)))

private theorem pred_not_eq : equalityOperand? predName (.function .bool .bool) = none := by
  have h : Const.same predName Const.equality = false := by decide +kernel
  simp [equalityOperand?, h]

theorem translates_hypothesis : Translates [] (hyp .bool).term .prop assumptionImage := by
  apply Translates.equalityApp (operand := .function .bool .bool) (equalityOperand?_equality _) (by simp)
  · exact .constant pred_not_eq _
  · exact .free _

theorem translates_conclusion : Translates [] (concl .bool).term .prop conclusionImage := by
  apply Translates.equalityApp (operand := .function .bool .bool) (equalityOperand?_equality _) (by simp)
  · apply Translates.abs Ty.toHOL_bool
    have same := (sourceVarSame_eq_true_iff (x .bool) (x .bool)).2 rfl
    simp only [lhs, f, CanonicalTerm.applicationOfFunction, CanonicalTerm.constant,
      CanonicalTerm.free, DBTerm.closeFreeAt, same, if_true]
    apply Translates.app rfl
    · exact .constant pred_not_eq _
    · exact .bound .vz
  · apply Translates.abs Ty.toHOL_bool
    have same := (sourceVarSame_eq_true_iff (x .bool) (x .bool)).2 rfl
    have distinct : sourceVarSame (x .bool) (g .bool) = false := by decide +kernel
    simp only [rhs, right, CanonicalTerm.applicationOfFunction, CanonicalTerm.free,
      DBTerm.closeFreeAt, same, distinct, if_true, Bool.false_eq_true, if_false]
    apply Translates.app rfl
    · exact .free _
    · exact .bound .vz

theorem embedded_sequent :
    HasType [] (termToExpr assumptionImage) (tyToExpr .prop) ∧
    HasType [] (termToExpr conclusionImage) (tyToExpr .prop) :=
  ⟨termToExpr_typed assumptionImage, termToExpr_typed conclusionImage⟩

/-- Applying the translated left abstraction contracts to the declared
predicate applied to the same argument. The free predicate survives β. -/
theorem application_converts (argument : HOL.Term Symbol [] .prop) :
    Conv (termToExpr (.app (.lam (.app leftFn (.var .vz))) argument))
      (termToExpr (.app leftFn argument)) :=
  Conv.beta _ _ _

/-! The private publication round. The theory varies over primitive constant
extensions of the core HOL signature. Its only extra dependency is cross_pred.
The receipt carries its replay graph. The native fixture includes the five
inference requests, their parent slots, the declaration and the local event. -/
namespace Publication

open RuleSyntax RuleSyntax.OneFrame SignatureFormation
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (mem_fire)

private def schema := Ty.function a .bool
private def licensed (s : Signature) : Bool :=
  (s.constants predName).any (Ty.same schema)

inductive Row where
  | request (wanted : Theorem)
  | checked (wanted actual : Theorem) (graph : ProofSystem.Certificate) (live equal : Bool)
  | published (actual : Theorem) (graph : ProofSystem.Certificate)

abbrev action := RuleSyntax.RuleOccurrences.Closed.action Row
abbrev X := frames action

def rule (wanted : Theorem) : Rule (Terms Row) :=
  ⟨PUnit.unit, ⟨[.request wanted], [.checked wanted (claim .bool) certificate true true],
    [], [], [.published (claim .bool) certificate]⟩, []⟩

def inventory (s : Signature) (wanted : Theorem) : State (Terms Row) Nat :=
  ⟨PUnit.unit, [], {0, 1}, fun
    | 1 => .checked wanted (claim .bool) certificate (licensed s)
        ((ProofSystem.checker emptyAxiomPolicy).check wanted certificate)
    | _ => .request wanted⟩

abbrev machine := RuleSyntax.step X Nat (ext action) (Set.range rule)

def issue (s : Signature) (wanted : Theorem) :
    Firing Nat (ext action) (Set.range rule) (inventory s wanted).frame :=
  ⟨rule wanted, ⟨wanted, rfl⟩, PUnit.unit, PUnit.unit, ⟨[0], [1], [2]⟩, []⟩

theorem admits_iff (s : Signature) (wanted : Theorem) :
    machine.Admits (s := inventory s wanted) (issue s wanted) ↔
      s.constants predName = some schema ∧
      (ProofSystem.checker emptyAxiomPolicy).check wanted certificate = true := by
  have lic : licensed s = true ↔ s.constants predName = some schema := by
    unfold licensed
    cases s.constants predName with
    | none => simp
    | some t => exact (Ty.same_eq_true_iff _ _).trans (eq_comm.trans Option.some_inj.symm)
  constructor
  · intro h
    obtain ⟨_, σ, solved⟩ := h.2.2.1
    have same := (issue s wanted).read_solved (X := X) (s := inventory s wanted) solved
      (p := Row.checked wanted (claim .bool) certificate true true) (o := 1) (by simp [issue, rule, Firing.opened, RuleInstance.map]; rfl)
    change Row.checked _ _ _ true true = Row.checked _ _ _ (licensed s) _ at same
    exact ⟨lic.mp (Row.checked.inj same).2.2.2.1.symm, (Row.checked.inj same).2.2.2.2.symm⟩
  · rintro ⟨declared, checked⟩
    refine ⟨⟨?_, List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
    · intro b g h
      exact ⟨PUnit.unit, fun _ _ => rfl, fun _ _ => rfl⟩
    · constructor <;> simp [issue, inventory, Selection.commit]
    · refine ⟨PUnit.unit, PUnit.unit, fun e member => ?_⟩
      change e ∈ [(.request wanted, .request wanted),
        (.checked wanted (claim .bool) certificate true true,
         .checked wanted (claim .bool) certificate (licensed s)
          ((ProofSystem.checker emptyAxiomPolicy).check wanted certificate))] at member
      rw [lic.mpr declared, checked] at member
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · obtain rfl := List.mem_singleton.mp member
        rfl
    · intro _ σ _
      exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- The consumed request names the entire sequent at the replayed root. -/
theorem issued_claim_exact (s : Signature) (wanted : Theorem)
    (h : machine.Admits (s := inventory s wanted) (issue s wanted)) : wanted = claim .bool := by
  obtain ⟨cache, graph, root⟩ := (ProofSystem.checker_check_iff _ _ _).mp ((admits_iff _ _).1 h).2
  obtain ⟨cache', graph', root'⟩ := (ProofSystem.checker_check_iff _ _ _).mp replay
  obtain rfl := Option.some.inj (graph.symm.trans graph')
  exact Option.some.inj (root.symm.trans root')

theorem publishes (s : Signature) (wanted : Theorem)
    (h : machine.Admits (s := inventory s wanted) (issue s wanted)) :
    let after := machine.result (s := inventory s wanted) (issue s wanted) h
    0 ∉ after.present ∧ 1 ∈ after.present ∧ 2 ∈ after.present ∧
      after.label 2 = .published (claim .bool) certificate := by
  dsimp only
  rw [result_eq]
  simp [Firing.result, issue, rule, inventory, Selection.commit,
    Firing.opened, RuleInstance.map, relabel, mem_fire, X,
    Interface.Frames.ofSubstitution, action, RuleSyntax.RuleOccurrences.Closed.action]

private def base := DefinitionAdapters.ContextControls.coreContext.signature
private def good := base.addConstant predName schema

theorem admitted : machine.Admits (s := inventory good (claim .bool)) (issue good (claim .bool)) :=
  (admits_iff _ _).2 ⟨by simp [good, Signature.addConstant], replay⟩

theorem admitted_after_extension (s : Signature) (extendsWorld : good.Includes s) :
    machine.Admits (s := inventory s (claim .bool)) (issue s (claim .bool)) :=
  (admits_iff _ _).2 ⟨extendsWorld.2 _ _ ((admits_iff _ _).1 admitted).1, replay⟩

theorem refuses_changed_declaration :
    let s := base.addConstant predName Ty.bool
    ¬machine.Admits (s := inventory s (claim .bool)) (issue s (claim .bool)) := by
  dsimp only
  intro h
  have same := ((admits_iff _ _).1 h).1
  simp [Signature.addConstant, schema, Ty.bool, Ty.function] at same

end Publication

end Mettapedia.Logic.TierZero.Adequacy.HOLLightBinderPublication
