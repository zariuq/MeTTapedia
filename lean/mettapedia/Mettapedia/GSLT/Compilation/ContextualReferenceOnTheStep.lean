import Mettapedia.GSLT.Compilation.OSLFReferenceOnTheStep
import Mettapedia.OSLF.MeTTaIL.ContextualStepFuel

/-!
# An executable reference for contextual rewriting

The contextual executor computes every reduct justified at a given
premise depth. The state of the reference program holds that depth as
well as the current term. A step may raise the bound silently or perform
a reduction justified at the current bound. The same finite Transform
schema interprets both alternatives.

Every finite authored path can be lifted, starting at any depth. Every
finite Transform run reflects to an authored path after the silent bound
updates are erased. The observation is positive reachability. Scheduling
only bound increases need never perform an available reduction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.ContextualReferenceOnTheStep

open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep
  (Step StepAt engineBasePremises reductsUsing mem_rewriteAt_iff_stepAt)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Machines (ReadsBag rowState)
open OSLFReferenceOnTheStep (Encoding)

abbrev SearchState := Pattern × ℕ

/-- A reference state records the term and the search depth in one row. -/
def encoding : Encoding SearchState where
  store s := .app (.sym s.2) (RootRewritesOnTheStep.encode s.1)
  read
    | .app (.sym n) row => (Uniform.RowReadback.readPattern row).map (·, n)
    | _ => none
  read_store s := by simp only [Uniform.RowReadback.readPattern_encode, Option.map_some]

/-- The executable successor list computed with finite contextual depth.
The first alternative requests a deeper search. -/
def frontier (relations : RelationEnv) (language : LanguageDef) (s : SearchState) : List SearchState :=
  (s.1, s.2 + 1) :: (reductsUsing relations language s.2 s.1).map (·, s.2)

/-- The instrumented semantics refers to independent bounded derivations. -/
def searchStep (relations : RelationEnv) (language : LanguageDef) (s t : SearchState) : Prop :=
  t = (s.1, s.2 + 1) ∨ t.2 = s.2 ∧ StepAt (engineBasePremises relations) language s.2 s.1 t.1

def searchTheory (relations : RelationEnv) (language : LanguageDef) : GSLT :=
  equalityGSLT SearchState (searchStep relations language)

theorem frontier_exact (relations : RelationEnv) (language : LanguageDef) (s t : SearchState) :
    t ∈ frontier relations language s ↔ (searchTheory relations language).Step s t := by
  change t ∈ frontier relations language s ↔ searchStep relations language s t
  simp only [frontier, List.mem_cons, List.mem_map, searchStep]
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨_, offered, rfl⟩
    exact ⟨rfl, mem_rewriteAt_iff_stepAt.mp offered⟩
  · rintro ⟨depth, moved⟩
    exact ⟨t.1, mem_rewriteAt_iff_stepAt.mpr moved, Prod.ext rfl depth.symm⟩

private theorem raise_to (relations : RelationEnv) (language : LanguageDef) (source : Pattern)
    {first last : ℕ} (enough : first ≤ last) :
    (searchTheory relations language).MultiStep (source, first) (source, last) := by
  induction enough with
  | refl => exact .refl _
  | step _ earlier =>
      exact multiStepAppend earlier (.step (Or.inl rfl) (.refl _))

/-- Increasing the search depth is unobservable. A source step has a finite
derivation, so it becomes executable after finitely many depth increases. -/
def instrument (relations : RelationEnv) (language : LanguageDef) :
    OperationalCorrespondence (RootRewritesOnTheStep.sourceSystem relations language)
      (searchTheory relations language) where
  related source target := target.1 = source
  readStep := by
    intro source before after read moved
    rcases moved with raised | ⟨_, stepped⟩
    · exact Or.inl ((congrArg Prod.fst raised).trans read)
    · exact Or.inr ⟨after.1, read ▸ ⟨_, stepped⟩, rfl⟩
  forward := by
    rintro source target ⟨before, depth⟩ read ⟨needed, proof⟩
    have starts : before = source := read
    subst before
    let bound := max depth needed
    have enough := raise_to relations language source (Nat.le_max_left depth needed)
    have moved : (searchTheory relations language).Step (source, bound) (target, bound) :=
      Or.inr ⟨rfl, proof.mono_fuel (Nat.le_max_right depth needed)⟩
    refine ⟨(target, bound), (executionPath_nonempty_iff_multiStep _ _ _).mpr ?_, rfl⟩
    exact multiStepAppend enough (.step moved (.refl _))

/-- The fixed Transform program asks only for the next finite frontier. -/
def compiled (relations : RelationEnv) (language : LanguageDef) : GSLT :=
  OSLFReferenceOnTheStep.compiledStep encoding (frontier relations language)

def correspondence (relations : RelationEnv) (language : LanguageDef) :
    OperationalCorrespondence (RootRewritesOnTheStep.sourceSystem relations language)
      (compiled relations language) :=
  (instrument relations language).comp (OSLFReferenceOnTheStep.correspondence
    (searchTheory relations language) encoding (frontier relations language) (frontier_exact relations language))

/-- Finite endpoint reachability is exact, with the final search depth
hidden by the named observation. -/
theorem reaches_iff (relations : RelationEnv) (language : LanguageDef) (first last : Pattern) (depth : ℕ) :
    (RootRewritesOnTheStep.sourceSystem relations language).MultiStep first last ↔
      ∃ final, (compiled relations language).MultiStep (rowState (encoding.store (first, depth))) final ∧
        ∃ foundDepth, ReadsBag final {encoding.store (last, foundDepth)} := by
  let lifted : OperationalCorrespondence (RootRewritesOnTheStep.sourceSystem relations language)
      (searchTheory relations language) := instrument relations language
  have begins : lifted.related first (first, depth) := rfl
  have compared (finish : SearchState) :=
    OSLFReferenceOnTheStep.reaches_iff (searchTheory relations language) encoding
      (frontier relations language) (frontier_exact relations language) (first, depth) finish
  constructor
  · intro reached
    obtain ⟨⟨read, foundDepth⟩, run, same⟩ := lifted.liftMultiStep begins reached
    have equal : read = last := same
    subst read
    obtain ⟨final, targetRun, shown⟩ := (compared (last, foundDepth)).mp run
    exact ⟨final, targetRun, foundDepth, shown⟩
  · rintro ⟨final, run, foundDepth, read⟩
    have got := (compared (last, foundDepth)).mpr ⟨final, run, read⟩
    obtain ⟨after, path, same⟩ := lifted.toOperationalReadback.reflectMultiStep begins got
    have equal : last = after := same
    rwa [equal]

/-- When there are no equation generators, primitive contextual
reachability is the canonical OSLF reachability. -/
theorem canonical_reaches_iff (relations : RelationEnv) (language : LanguageDef)
    (equationFree : language.isEquationFree = true) (first last : Pattern) (depth : ℕ) :
    (langGSLTUsing relations language).MultiStep first last ↔
      ∃ final, (compiled relations language).MultiStep (rowState (encoding.store (first, depth))) final ∧
        ∃ foundDepth, ReadsBag final {encoding.store (last, foundDepth)} := by
  have exactStep (s t : Pattern) :=
    langSemanticReducesUsing_iff_langReducesUsing_of_equation_free relations equationFree s t
  let S := RootRewritesOnTheStep.sourceSystem relations language
  let T := langGSLTUsing relations language
  have compare : T.MultiStep first last ↔ S.MultiStep first last := by
    constructor
    · intro run
      exact GSLT.MultiStep.rec (S := T) (motive := fun s t _ => S.MultiStep s t)
        (fun term => .refl (S := S) term) (fun edge _ ih => .step ((exactStep _ _).mp edge) ih) run
    · intro run
      exact GSLT.MultiStep.rec (S := S) (motive := fun s t _ => T.MultiStep s t)
        (fun term => .refl (S := T) term) (fun edge _ ih => .step ((exactStep _ _).mpr edge) ih) run
  exact compare.trans (reaches_iff relations language first last depth)

/-- Search all implementation paths up to the given number of firings.
The term component, rather than the search bound, is the observation. -/
def reportsWithin (relations : RelationEnv) (language : LanguageDef)
    (origin goal : Pattern) (depth budget : ℕ) : Bool :=
  (List.range (budget + 1)).any fun length =>
    (OSLFReferenceOnTheStep.rowsAt encoding (frontier relations language) length (encoding.store (origin, depth))).any
      fun row => (encoding.read row).any (fun s => s.1 == goal)

theorem reportsWithin_iff (relations : RelationEnv) (language : LanguageDef)
    (origin goal : Pattern) (depth budget : ℕ) :
    reportsWithin relations language origin goal depth budget = true ↔
      ∃ foundDepth, ∃ path : (searchTheory relations language).RewritePath (origin, depth) (goal, foundDepth),
        path.length ≤ budget := by
  simp only [reportsWithin, List.any_eq_true, List.mem_range]
  have readsAt := OSLFReferenceOnTheStep.mem_rowsAt (searchTheory relations language) encoding
    (frontier relations language) (frontier_exact relations language)
  constructor
  · rintro ⟨length, inBudget, row, member, observed⟩
    obtain ⟨⟨found, n⟩, rfl, path, rfl⟩ := (readsAt length (origin, depth) row).mp member
    have same : found = goal := by simpa only [encoding.read_store, Option.any_some, beq_iff_eq] using observed
    subst found
    exact ⟨n, path, Nat.le_of_lt_succ inBudget⟩
  · rintro ⟨n, path, inBudget⟩
    refine ⟨path.length, Nat.lt_succ_of_le inBudget, encoding.store (goal, n),
      (readsAt path.length (origin, depth) _).mpr ⟨(goal, n), rfl, path, rfl⟩, ?_⟩
    simp only [encoding.read_store, Option.any_some, beq_self_eq_true]

/-- Increasing the firing budget eventually reports every finite reachable
endpoint. A reported endpoint comes from an actual authored path. -/
theorem eventually_reports_iff (relations : RelationEnv) (language : LanguageDef)
    (origin goal : Pattern) (depth : ℕ) :
    (∃ budget, reportsWithin relations language origin goal depth budget = true) ↔
      (RootRewritesOnTheStep.sourceSystem relations language).MultiStep origin goal := by
  let lifted := instrument relations language
  have starts : lifted.related origin (origin, depth) := rfl
  constructor
  · rintro ⟨budget, found⟩
    obtain ⟨n, path, _⟩ := (reportsWithin_iff relations language origin goal depth budget).mp found
    obtain ⟨last, run, same⟩ := lifted.toOperationalReadback.reflectMultiStep starts
      (executionPathToMultiStep (rewritePathToExecutionPath path))
    have eq : goal = last := same
    exact eq.symm ▸ run
  · intro reachable
    obtain ⟨⟨last, n⟩, run, same⟩ := lifted.liftMultiStep starts reachable
    have eq : last = goal := same
    subst last
    obtain ⟨path⟩ := (executionPath_nonempty_iff_multiStep _ _ _).mpr run
    let history := executionPathToRewritePath path
    exact ⟨history.length, (reportsWithin_iff relations language origin goal depth history.length).mpr
      ⟨n, history, le_rfl⟩⟩


namespace Controls

def a : Pattern := .apply "A" []
def b : Pattern := .apply "B" []
def wrap (term : Pattern) : Pattern := .apply "Wrap" [term]

def nodeSort : TypeExpr := .base "Node"

def language : LanguageDef :=
  { LanguageDef.empty "Contextual" with
    types := [.plain "Node"]
    terms := [
      { label := "A", category := "Node", params := [], syntaxPattern := [] },
      { label := "B", category := "Node", params := [], syntaxPattern := [] },
      { label := "Wrap", category := "Node", params := [.simple "child" nodeSort], syntaxPattern := [] }]
    rewrites :=
      [{ name := "root", typeContext := [], premises := [], left := a, right := b },
       { name := "descend", typeContext := [("old", nodeSort), ("new", nodeSort)],
         premises := [.congruence (.fvar "old") (.fvar "new")],
         left := wrap (.fvar "old"), right := wrap (.fvar "new") }] }

theorem shallow_frontier : frontier RelationEnv.empty language (wrap a, 1) = [(wrap a, 2)] := by
  decide +kernel

theorem deep_frontier : frontier RelationEnv.empty language (wrap a, 2) =
    [(wrap a, 3), (wrap b, 2)] := by
  decide +kernel

theorem wraps_reduce_on_the_step :
    ∃ final, (compiled RelationEnv.empty language).MultiStep (rowState (encoding.store (wrap a, 0))) final ∧
      ∃ depth, ReadsBag final {encoding.store (wrap b, depth)} := by
  have step : Step (engineBasePremises RelationEnv.empty) language (wrap a) (wrap b) :=
    ⟨2, mem_rewriteAt_iff_stepAt.mp (by decide +kernel)⟩
  exact (reaches_iff RelationEnv.empty language (wrap a) (wrap b) 0).mp (.step step (.refl _))

end Controls

#print axioms frontier_exact
#print axioms canonical_reaches_iff
#print axioms eventually_reports_iff
#print axioms Controls.shallow_frontier
#print axioms Controls.wraps_reduce_on_the_step

end Mettapedia.GSLT.Compilation.ContextualReferenceOnTheStep
