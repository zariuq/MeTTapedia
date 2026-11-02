import Mettapedia.Logic.HOL.ConstantExpansionProofsFree
import Mettapedia.Languages.HOLLight.ExactFormulaReadback
import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Languages.HOLLight.CachedHypothesisList

/-!
# Checked constant expansion from exact source-cache premises

Source formulas and defining equations are read by the existing exact reader.
The retained expansion program constructs the transported theorem, and the
ordinary primitive compiler and hypothesis-discharge operation produce its
certificate. Publication requires that all assumptions have been removed.
The source cache, declaration identities and axiom dependencies are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.CachedSourceExpansion

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Logic.DerivationGraph
open ReverseTranslation GraphExpansion

abbrev Formula := HOL.ClosedFormula Symbol

def encode (formula : Formula) : CanonicalTerm :=
  reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand formula)

theorem readable_expand {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol Γ type) (accepted : ExactFormulaReadback.readable term = true) :
    HOL.ImpredicativeConnectives.expand term = term := by
  induction term with
  | var | const => rfl
  | app function argument ihFunction ihArgument | eq function argument ihFunction ihArgument =>
      have parts : ExactFormulaReadback.readable function = true ∧
          ExactFormulaReadback.readable argument = true := by
        simpa only [ExactFormulaReadback.readable, Bool.and_eq_true] using accepted
      simp only [HOL.ImpredicativeConnectives.expand, ihFunction parts.1, ihArgument parts.2]
  | lam body ih => simp only [HOL.ImpredicativeConnectives.expand, ih accepted]
  | top | bot | and | or | imp | not | all | ex => cases accepted

theorem matches_exact {fact : Theorem} {formula : Formula}
    (accepted : ExactFormulaReadback.matchesB fact formula = true) :
    fact.sequent.hyp = ∅ ∧ fact.sequent.concl = encode formula := by
  simp only [ExactFormulaReadback.matchesB, Bool.and_eq_true, beq_iff_eq,
    Finset.card_eq_zero] at accepted
  refine ⟨accepted.2, ?_⟩
  apply CanonicalTerm.ext_term
  rw [encode, reverseCanonical_term, readable_expand formula accepted.1.1,
    reverseTerm_eq_reverseTermOpen]
  exact (DBTerm.same_eq_true_iff _ _).mp accepted.1.2

structure Source (state : ProofExecution.State) (formula : Formula) where
  root : Nat
  fact : Theorem
  found : state.cache[root]? = some fact
  closed : fact.sequent.hyp = ∅
  exactConclusion : fact.sequent.concl = encode formula
  translated : Translates [] fact.sequent.concl.term .prop formula

/-- This adapter reuses the existing source comparison and retains its actual
cache address, exact compiled conclusion and source translation. -/
def read? (state : ProofExecution.State) (root : Nat) (formula : Formula) :
    Option (Source state formula) :=
  match found : state.cache[root]? with
  | none => none
  | some fact =>
      if accepted : ExactFormulaReadback.matchesB fact formula = true then
        some ⟨root, fact, found, (matches_exact accepted).1, (matches_exact accepted).2,
          (ExactFormulaReadback.matches_sound accepted).2⟩
      else none

structure Sources (state : ProofExecution.State) (formulas : List Formula) where
  entries : List (Nat × Theorem)
  found : ∀ entry ∈ entries, state.cache[entry.1]? = some entry.2
  closed : ∀ entry ∈ entries, entry.2.sequent.hyp = ∅
  conclusions : entries.map (fun entry => entry.2.sequent.concl) = formulas.map encode

def readAll? (state : ProofExecution.State) : (formulas : List Formula) → List Nat →
    Option (Sources state formulas)
  | [], [] => some {
      entries := []
      found := by intro entry member; cases member
      closed := by intro entry member; cases member
      conclusions := rfl }
  | formula :: formulas, root :: roots => do
      let first ← read? state root formula
      let rest ← readAll? state formulas roots
      return ⟨(first.root, first.fact) :: rest.entries,
        by
          intro entry member
          rcases List.mem_cons.mp member with rfl | member
          · exact first.found
          · exact rest.found entry member,
        by
          intro entry member
          rcases List.mem_cons.mp member with rfl | member
          · exact first.closed
          · exact rest.closed entry member,
        by simp only [List.map_cons, first.exactConclusion, rest.conclusions]⟩
  | _, _ => none

theorem Sources.boolean {state : ProofExecution.State} {formulas : List Formula}
    (sources : Sources state formulas) (entry : Nat × Theorem) (present : entry ∈ sources.entries) :
    entry.2.sequent.concl.IsBool := by
  have member : entry.2.sequent.concl ∈ sources.entries.map (fun value => value.2.sequent.concl) :=
    List.mem_map.mpr ⟨entry, present, rfl⟩
  rw [sources.conclusions] at member
  obtain ⟨formula, _, same⟩ := List.mem_map.mp member
  exact same ▸ reverseCanonical_isBool Naming.empty _

/-- Only individual defining equations are supplied. The equation of the
whole source term and its transported theorem are constructed below. -/
structure Task where
  source : Formula
  target : Formula
  theory : List Formula
  replacements : {type : HOL.Ty AtomicTy} → Symbol type → Option (HOL.ClosedTerm Symbol type)
  equations : ∀ {type} (constant : Symbol type) (body : HOL.ClosedTerm Symbol type),
    replacements constant = some body → HOL.ProofSyntax Symbol theory (.eq (.const constant) body)
  equationsFree : ∀ {type} (constant : Symbol type) (body : HOL.ClosedTerm Symbol type)
    (present : replacements constant = some body),
    (equations constant body present).FunctionExtensionalityFree
  expanded : HOL.substConst? replacements source = some target

namespace Task

def equality (task : Task) : HOL.ProofSyntax Symbol task.theory (.eq task.source task.target) :=
  HOL.ProofSyntax.castIndices (by change task.theory.map id = task.theory; simp) rfl
    (HOL.ConstantExpansionProofs.expand task.theory task.replacements task.equations task.source task.expanded)

theorem equality_free (task : Task) : task.equality.FunctionExtensionalityFree := by
  unfold equality
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact HOL.ConstantExpansionProofs.expand_free task.theory task.replacements task.equations
    task.equationsFree task.source task.expanded

def proof (task : Task) : HOL.ProofSyntax Symbol (task.source :: task.theory) task.target :=
  .impE (.eqPropEL (task.equality.prepend task.source)) (.hyp ⟨0, by simp⟩)

theorem proof_free (task : Task) : task.proof.FunctionExtensionalityFree := by
  simpa only [proof, HOL.ProofSyntax.FunctionExtensionalityFree, HOL.ProofSyntax.prepend,
    HOL.ProofSyntax.functionExtensionalityFree_mono, and_true] using task.equality_free

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def compile (task : Task) (origin : ProofExecution.Origin) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy
    task.proof task.proof_free Naming.empty origin

theorem compile_axioms_empty (task : Task) (origin : ProofExecution.Origin) :
    (task.compile origin).proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _ (task.compile origin).proof.accepted))

theorem compile_covered (task : Task) (origin : ProofExecution.Origin) {state : ProofExecution.State}
    (sources : Sources state (task.source :: task.theory)) :
    (task.compile origin).proof.result.sequent.hyp =
      (sources.entries.map (fun entry => entry.2.sequent.concl)).toFinset := by
  rw [(task.compile origin).hypotheses_exact, sources.conclusions]
  simp only [reverseHypotheses, List.map_map, Function.comp_def]
  rfl

def compileAndClose? (task : Task) (origin : ProofExecution.Origin)
    (state : ProofExecution.State) (roots : List Nat) : Option (ProofExecution.State × Nat) := do
  let sources ← readAll? state (task.source :: task.theory) roots
  let (after, root) ← emitBlock emptyAxiomPolicy [] (task.compile origin).proof.certificate state
  CachedHypothesisList.closeAndRequire? emptyAxiomPolicy after (sources.entries.map Prod.fst) root origin

theorem compileAndClose_checked (task : Task) (origin : ProofExecution.Origin)
    {premises : List Theorem} {state : ProofExecution.State} (roots : List Nat)
    (sources : Sources state (task.source :: task.theory))
    (read : readAll? state (task.source :: task.theory) roots = some sources)
    (earlier : BuildChecked emptyAxiomPolicy premises state) :
    ∃ after root,
      task.compileAndClose? origin state roots = some (after, root) ∧
      BuildChecked emptyAxiomPolicy premises after ∧
      after.cache[root]? = some (CachedHypothesisList.result (sources.entries.map Prod.snd)
        (task.compile origin).proof.result) ∧
      (CachedHypothesisList.result (sources.entries.map Prod.snd)
        (task.compile origin).proof.result).sequent.hyp = ∅ ∧
      (CachedHypothesisList.result (sources.entries.map Prod.snd)
        (task.compile origin).proof.result).sequent.concl = encode task.target ∧
      (CachedHypothesisList.result (sources.entries.map Prod.snd)
        (task.compile origin).proof.result).axioms =
        CachedHypothesisList.dependencies (sources.entries.map Prod.snd) ∧
      after.receipts.size = state.receipts.size + (task.compile origin).proof.certificate.1.length +
        2 * sources.entries.length ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → after.cache[index]? = some fact := by
  let compiled := task.compile origin
  have compiledBool : compiled.proof.result.sequent.concl.IsBool := by
    rw [compiled.conclusion_exact]
    exact reverseCanonical_isBool Naming.empty _
  obtain ⟨middle, next, emitted, middleChecked, nextFound, _, firstPreserved⟩ :=
    emitBlock_checked earlier (show lookupPremises state.cache [] = some [] from rfl)
      compiled.proof.blockChecked
  obtain ⟨after, root, closed, afterChecked, rootFound, closeSize, secondPreserved⟩ :=
    CachedHypothesisList.close_checked sources.entries middleChecked nextFound
      (fun entry present => firstPreserved _ _ (sources.found entry present))
      (fun entry present => (sources.boolean entry present).trans compiledBool.symm)
      origin
  have noHypotheses : (CachedHypothesisList.result (sources.entries.map Prod.snd)
      compiled.proof.result).sequent.hyp = ∅ := by
    apply CachedHypothesisList.result_closed
    · intro source member
      obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
      exact sources.closed entry present
    · simpa only [List.map_map, Function.comp_def] using (task.compile_covered origin sources).le
  have published := (CachedHypothesisDischarge.requireClosed_iff after root).mpr
    ⟨_, rootFound, noHypotheses⟩
  refine ⟨after, root, ?_, afterChecked, rootFound, noHypotheses, ?_, ?_, ?_, ?_⟩
  · unfold compileAndClose?
    rw [read]
    change ((emitBlock emptyAxiomPolicy [] compiled.proof.certificate state).bind fun next =>
      CachedHypothesisList.closeAndRequire? emptyAxiomPolicy next.1
        (sources.entries.map Prod.fst) next.2 origin) = some (after, root)
    rw [emitted]
    change CachedHypothesisList.closeAndRequire? emptyAxiomPolicy middle
      (sources.entries.map Prod.fst) next origin = some (after, root)
    unfold CachedHypothesisList.closeAndRequire?
    rw [closed]
    exact published
  · exact (CachedHypothesisList.result_conclusion _ _).trans compiled.conclusion_exact
  · rw [CachedHypothesisList.result_axioms, task.compile_axioms_empty origin, Finset.union_empty]
  · have compileSize := (emitBlock_size emitted).2
    change after.receipts.size = state.receipts.size + compiled.proof.certificate.1.length +
      2 * sources.entries.length
    omega
  · intro index fact found
    exact secondPreserved index fact (firstPreserved index fact found)

end Task

#print axioms readable_expand
#print axioms matches_exact
#print axioms Task.equality_free
#print axioms Task.proof_free
#print axioms Task.compile_covered
#print axioms Task.compileAndClose_checked

end Mettapedia.Languages.HOLLight.CachedSourceExpansion
