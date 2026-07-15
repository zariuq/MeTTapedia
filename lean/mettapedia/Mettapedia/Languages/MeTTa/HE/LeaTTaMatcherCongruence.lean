import Mettapedia.Languages.MeTTa.HE.MatchSolutionTheory
import Mettapedia.Languages.MeTTa.HE.DeclMergeSpec

/-!
# Structural HE/LeaTTa matcher congruence

The executable matcher and merge operations already determine their complete
solution theories.  The remaining cross-engine induction therefore only has
to preserve the genuinely intensional information needed by later recursive
reconciliation: equality-class closure and class-indexed raw-value
provenance.  This file packages that smaller obligation and upgrades it to
`LeaBindingCongruence` after successful operations.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.DeclMergeSpec
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- The structural part of cross-engine binding congruence.  It deliberately
omits solution theory: successful executable operations supply that field
independently through their solution characterizations. -/
structure LeaBindingStructuralCongruence
    (b : Bindings) (lb : Metta.Bindings) : Prop where
  classes : ∀ start finish,
    finish ∈ b.eqClass start ↔
      finish ∈ Metta.Bindings.eqClass lb start
  classValues : LeaClassValueRelEquiv b lb

/-- Attach an independently established solution theory to the structural
congruence obligation. -/
theorem LeaBindingStructuralCongruence.withSolutions
    {b : Bindings} {lb : Metta.Bindings}
    (hstruct : LeaBindingStructuralCongruence b lb)
    (hsolutions : LeaBindingSolutionTheoryEquiv b lb) :
    LeaBindingCongruence b lb :=
  ⟨⟨hstruct.classes, hsolutions⟩, hstruct.classValues⟩

/-- Forget the already-solved extensional field of full congruence. -/
theorem LeaBindingCongruence.structural
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaBindingCongruence b lb) :
    LeaBindingStructuralCongruence b lb :=
  ⟨h.semantic.classes, h.classValues⟩

/-- Successful HE and repaired-LeaTTa matches in their runtime orientations
have the same solution theory.  HE receives query then pattern, whereas
LeaTTa's `queryOp` matcher receives pattern then query. -/
theorem heMatch_leaMatch_reversed_solutionTheoryEquiv
    {query pattern : Atom} {b : Bindings} {fuel : Nat}
    {lb : Metta.Bindings}
    (hHE : b ∈ matchAtoms query pattern fuel)
    (hLea : lb ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query)) :
    LeaBindingSolutionTheoryEquiv b lb := by
  intro valuation
  rw [matchAtoms_solution_iff hHE valuation,
    leaMatchAtoms_solution_iff valuation
      (toLeaTTaAtom_noFloat pattern)
      (toLeaTTaAtom_noFloat query) hLea]
  simp only [MettaEquationSatisfied]
  exact eq_comm

/-- The matcher preservation induction only needs to produce structural
congruence; successful matcher witnesses supply the solution field for free. -/
theorem matchAtoms_congruence_of_structural
    {query pattern : Atom} {b : Bindings} {fuel : Nat}
    {lb : Metta.Bindings}
    (hHE : b ∈ matchAtoms query pattern fuel)
    (hLea : lb ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hstruct : LeaBindingStructuralCongruence b lb) :
    LeaBindingCongruence b lb :=
  hstruct.withSolutions
    (heMatch_leaMatch_reversed_solutionTheoryEquiv hHE hLea)

/-- Successful merges likewise leave only equality closure and raw-value
provenance to the operational induction. -/
theorem mergeBindings_congruence_of_structural
    {heLeft heRight heOut : Bindings}
    {leaLeft leaRight leaOut : Metta.Bindings} {fuel : Nat}
    (hleft : LeaBindingCongruence heLeft leaLeft)
    (hright : LeaBindingCongruence heRight leaRight)
    (hleaLeftNoFloat : LeaBindingsNoFloat leaLeft)
    (hleaRightNoFloat : LeaBindingsNoFloat leaRight)
    (hHE : heOut ∈ mergeBindings heLeft heRight fuel)
    (hLea : leaOut ∈ Metta.Bindings.merge leaLeft leaRight)
    (hstruct : LeaBindingStructuralCongruence heOut leaOut) :
    LeaBindingCongruence heOut leaOut := by
  apply hstruct.withSolutions
  intro valuation
  rw [mergeBindings_solution_iff hHE valuation,
    hleft.semantic.solutions valuation,
    hright.semantic.solutions valuation,
    leaMerge_solution_iff valuation
      hleaLeftNoFloat hleaRightNoFloat hLea]

/-- Successful value insertion also obtains its complete solution theory
outside the structural preservation induction. -/
theorem addVarBinding_congruence_of_structural
    {b heOut : Bindings} {lb leaOut : Metta.Bindings}
    {v : String} {value : Atom} {fuel : Nat}
    (hbase : LeaBindingCongruence b lb)
    (hlbNoFloat : LeaBindingsNoFloat lb)
    (hHE : heOut ∈ addVarBinding b v value fuel)
    (hLea : leaOut ∈
      Metta.Bindings.addVarBinding lb v (toLeaTTaAtom value))
    (hstruct : LeaBindingStructuralCongruence heOut leaOut) :
    LeaBindingCongruence heOut leaOut := by
  apply hstruct.withSolutions
  intro valuation
  rw [addVarBinding_solution_iff hHE valuation,
    hbase.semantic.solutions valuation,
    leaAddVarBinding_solution_iff valuation hlbNoFloat
      (toLeaTTaAtom_noFloat value) hLea]

/-- Successful equality insertion obtains its complete solution theory
outside the structural preservation induction as well. -/
theorem addVarEquality_congruence_of_structural
    {b heOut : Bindings} {lb leaOut : Metta.Bindings}
    {left right : String} {fuel : Nat}
    (hbase : LeaBindingCongruence b lb)
    (hlbNoFloat : LeaBindingsNoFloat lb)
    (hHE : heOut ∈ addVarEquality b left right fuel)
    (hLea : leaOut ∈ Metta.Bindings.addVarEquality lb left right)
    (hstruct : LeaBindingStructuralCongruence heOut leaOut) :
    LeaBindingCongruence heOut leaOut := by
  apply hstruct.withSolutions
  intro valuation
  rw [addVarEquality_solution_iff hHE valuation,
    hbase.semantic.solutions valuation,
    leaAddVarEquality_solution_iff valuation hlbNoFloat hLea]

/-- Induction-facing matcher witness: only structural binding information is
carried recursively. -/
def LeaMatcherStructuralTransport
    (query pattern : Atom) (b : Bindings) : Prop :=
  ∃ lb,
    lb ∈ Metta.matchAtoms (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
      LeaBindingStructuralCongruence b lb

/-- Upgrade the smaller matcher witness after executable HE success. -/
theorem LeaMatcherStructuralTransport.toCongruence
    {query pattern : Atom} {b : Bindings} {fuel : Nat}
    (hHE : b ∈ matchAtoms query pattern fuel)
    (h : LeaMatcherStructuralTransport query pattern b) :
    LeaMatcherCongruenceTransport query pattern b := by
  obtain ⟨lb, hLea, hstruct⟩ := h
  exact ⟨lb, hLea,
    matchAtoms_congruence_of_structural hHE hLea hstruct⟩

/-! ## Reverse leaf realization -/

/-- Outside the expression/expression case, repaired LeaTTa's matcher has at
most one binding result.  This is an operational fact, not an MGU uniqueness
claim: every leaf branch returns either the empty list or one singleton. -/
private theorem leaMatchAtoms_leaf_subsingleton
    {query pattern : Atom} {left right : Metta.Bindings}
    (hleaf : ¬ BothExpressions query pattern)
    (hleft : left ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hright : right ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query)) :
    left = right := by
  cases query <;> cases pattern <;>
    simp_all [BothExpressions, toLeaTTaAtom, Metta.matchAtoms,
      Metta.matchAtomsWith.eq_def]
  split at hleft <;> simp_all

/-- A successful repaired-LeaTTa leaf match is either the reflexive-variable
case or its two HE inputs are structurally disjoint.  In the variable /
expression cases this is exactly the occurs check already selected by the
executable LeaTTa matcher, rather than an extra caller premise. -/
private theorem reflexiveVar_or_varsDisjoint_of_leaMatchAtoms_leaf
    {query pattern : Atom} {lb : Metta.Bindings}
    (hLea : lb ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hleaf : ¬ BothExpressions query pattern) :
    (∃ name, query = .var name ∧ pattern = .var name) ∨
      VarsDisjoint query pattern := by
  cases query with
  | symbol queryName =>
      exact Or.inr (by
        intro name hquery
        simp [toLeaTTaAtom, Metta.Atom.vars] at hquery)
  | grounded queryGround =>
      exact Or.inr (by
        intro name hquery
        simp [toLeaTTaAtom, Metta.Atom.vars] at hquery)
  | var queryName =>
      cases pattern with
      | symbol patternName =>
          exact Or.inr (by
            intro name hquery hpattern
            simp [toLeaTTaAtom, Metta.Atom.vars] at hpattern)
      | grounded patternGround =>
          exact Or.inr (by
            intro name hquery hpattern
            simp [toLeaTTaAtom, Metta.Atom.vars] at hpattern)
      | var patternName =>
          by_cases hsame : queryName = patternName
          · subst patternName
            exact Or.inl ⟨queryName, rfl, rfl⟩
          · exact Or.inr (by
              intro name hquery hpattern
              simp [toLeaTTaAtom, Metta.Atom.vars] at hquery hpattern
              exact hsame (hquery.symm.trans hpattern))
      | expression patternAtoms =>
          cases hoccurs :
              Metta.Subst.occurs queryName (.expr (toLeaTTaAtoms patternAtoms)) with
          | true =>
              simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom,
                hoccurs] at hLea
          | false =>
              have hfresh :
                  queryName ∉ (.expr (toLeaTTaAtoms patternAtoms) : Metta.Atom).vars :=
                not_mem_vars_of_occurs_eq_false queryName _ hoccurs
              exact Or.inr (by
                intro name hquery hpattern
                have hname : name = queryName := by
                  simpa [toLeaTTaAtom, Metta.Atom.vars] using hquery
                subst name
                exact hfresh hpattern)
  | expression queryAtoms =>
      cases pattern with
      | symbol patternName =>
          exact Or.inr (by
            intro name hquery hpattern
            simp [toLeaTTaAtom, Metta.Atom.vars] at hpattern)
      | grounded patternGround =>
          exact Or.inr (by
            intro name hquery hpattern
            simp [toLeaTTaAtom, Metta.Atom.vars] at hpattern)
      | var patternName =>
          cases hoccurs :
              Metta.Subst.occurs patternName (.expr (toLeaTTaAtoms queryAtoms)) with
          | true =>
              simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom,
                hoccurs] at hLea
          | false =>
              have hfresh :
                  patternName ∉ (.expr (toLeaTTaAtoms queryAtoms) : Metta.Atom).vars :=
                not_mem_vars_of_occurs_eq_false patternName _ hoccurs
              exact Or.inr (by
                intro name hquery hpattern
                have hname : name = patternName := by
                  simpa [toLeaTTaAtom, Metta.Atom.vars] using hpattern
                subst name
                exact hfresh hquery)
      | expression patternAtoms =>
          exact (hleaf ⟨queryAtoms, patternAtoms, rfl, rfl⟩).elim

/-- A successful repaired-LeaTTa leaf match determines a declarative HE leaf
match.  Standardizing apart excludes the only reflexive-variable presentation
disagreement; the expression/expression branch is intentionally left to the
mutual operational induction. -/
private theorem exists_matchRel_of_leaMatchAtoms_leaf
    {query pattern : Atom} {lb : Metta.Bindings}
    (hLea : lb ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hdisj : VarsDisjoint query pattern)
    (hleaf : ¬ BothExpressions query pattern) :
    ∃ heOut, DeclMatchSpec.MatchRel query pattern heOut := by
  cases query with
  | symbol queryName =>
      cases pattern with
      | symbol patternName =>
          by_cases heq : patternName = queryName
          · subst patternName
            exact ⟨⟨[], []⟩, .symSym queryName⟩
          · simp [Metta.matchAtoms, Metta.matchAtomsWith.eq_def,
              toLeaTTaAtom, heq] at hLea
      | var patternVar =>
          exact ⟨⟨[(patternVar, .symbol queryName)], []⟩,
            .nonVarVar (by simp [DeclMatchSpec.Atom.isVarB])⟩
      | grounded ground =>
          simp [Metta.matchAtoms, Metta.matchAtomsWith.eq_def,
            toLeaTTaAtom, Metta.Atom.equiv] at hLea
      | expression atoms =>
          simp [Metta.matchAtoms, Metta.matchAtomsWith.eq_def,
            toLeaTTaAtom, Metta.Atom.equiv] at hLea
  | var queryVar =>
      cases pattern with
      | symbol patternName =>
          exact ⟨⟨[(queryVar, .symbol patternName)], []⟩,
            .varNonVar (by simp [DeclMatchSpec.Atom.isVarB])⟩
      | var patternVar =>
          have hne : queryVar ≠ patternVar := by
            intro heq
            subst patternVar
            exact (hdisj queryVar
              (by simp [toLeaTTaAtom, Metta.Atom.vars]))
              (by simp [toLeaTTaAtom, Metta.Atom.vars])
          exact ⟨⟨[], [(queryVar, patternVar)]⟩,
            .varVar queryVar patternVar⟩
      | grounded ground =>
          exact ⟨⟨[(queryVar, .grounded ground)], []⟩,
            .varNonVar (by simp [DeclMatchSpec.Atom.isVarB])⟩
      | expression atoms =>
          exact ⟨⟨[(queryVar, .expression atoms)], []⟩,
            .varNonVar (by simp [DeclMatchSpec.Atom.isVarB])⟩
  | grounded queryGround =>
      cases pattern with
      | symbol patternName =>
          simp [Metta.matchAtoms, Metta.matchAtomsWith.eq_def,
            toLeaTTaAtom, Metta.Atom.equiv] at hLea
      | var patternVar =>
          exact ⟨⟨[(patternVar, .grounded queryGround)], []⟩,
            .nonVarVar (by simp [DeclMatchSpec.Atom.isVarB])⟩
      | grounded patternGround =>
          have hequiv :
              Metta.Ground.equiv (toLeaTTaGround patternGround)
                (toLeaTTaGround queryGround) = true := by
            by_contra hnot
            have hfalse :
                Metta.Ground.equiv (toLeaTTaGround patternGround)
                  (toLeaTTaGround queryGround) = false :=
              Bool.eq_false_of_not_eq_true hnot
            simp [Metta.matchAtoms, Metta.matchAtomsWith.eq_def,
              toLeaTTaAtom, Metta.Atom.equiv, hfalse] at hLea
          have heq : patternGround = queryGround := by
            cases patternGround <;> cases queryGround
            all_goals
              simp only [toLeaTTaGround, Metta.Ground.equiv] at hequiv
            all_goals
              change Metta.instBEqGround.beq _ _ = true at hequiv
            all_goals
              simp_all [Metta.instBEqGround.beq]
          subst patternGround
          exact ⟨⟨[], []⟩, .grounded queryGround⟩
      | expression atoms =>
          simp [Metta.matchAtoms, Metta.matchAtomsWith.eq_def,
            toLeaTTaAtom, Metta.Atom.equiv] at hLea
  | expression queryAtoms =>
      cases pattern with
      | symbol patternName =>
          simp [Metta.matchAtoms, Metta.matchAtomsWith.eq_def,
            toLeaTTaAtom, Metta.Atom.equiv] at hLea
      | var patternVar =>
          exact ⟨⟨[(patternVar, .expression queryAtoms)], []⟩,
            .nonVarVar (by simp [DeclMatchSpec.Atom.isVarB])⟩
      | grounded ground =>
          simp [Metta.matchAtoms, Metta.matchAtomsWith.eq_def,
            toLeaTTaAtom, Metta.Atom.equiv] at hLea
      | expression patternAtoms =>
          exact (hleaf ⟨queryAtoms, patternAtoms, rfl, rfl⟩).elim

/-- Translation of HE grounded payloads is injective. -/
private theorem toLeaTTaGround_injective :
    Function.Injective toLeaTTaGround := by
  intro left right heq
  cases left <;> cases right <;>
    simp [toLeaTTaGround] at heq <;> simp_all

/-- The HE-to-LeaTTa atom embedding is injective.  Consequently, extracting
an HE witness from a transformed Robinson equation cannot silently replace
an original conflicting atom by a different presentation.  This is the
constructor-level fact used by the direct strict-prefix recursion; binding
records themselves remain compared only through `LeaBindingCongruence`. -/
theorem toLeaTTaAtom_injective : Function.Injective toLeaTTaAtom := by
  let AtomGoal : Atom → Prop := fun left => ∀ right,
    toLeaTTaAtom left = toLeaTTaAtom right → left = right
  let ListGoal : List Atom → Prop := fun left => ∀ right,
    toLeaTTaAtoms left = toLeaTTaAtoms right → left = right
  have hrec : ∀ left, AtomGoal left := by
    apply Atom.rec (motive_1 := AtomGoal) (motive_2 := ListGoal)
    · intro name right heq
      cases right <;> simp_all [toLeaTTaAtom]
    · intro name right heq
      cases right <;> simp_all [toLeaTTaAtom]
    · intro value right heq
      cases right with
      | symbol | var | expression => cases heq
      | grounded other =>
          congr
          cases value <;> cases other <;>
            simp [toLeaTTaAtom, toLeaTTaGround] at heq <;> simp_all
    · intro atoms ih right heq
      cases right with
      | symbol | var | grounded => cases heq
      | expression others =>
          exact congrArg Atom.expression (ih others (by
            simpa [toLeaTTaAtom] using heq))
    · intro right heq
      cases right <;> simp_all [toLeaTTaAtoms]
    · intro atom atoms ihAtom ihAtoms right heq
      cases right with
      | nil => cases heq
      | cons other others =>
          simp only [toLeaTTaAtoms, List.cons.injEq] at heq
          exact congrArg₂ List.cons
            (ihAtom other heq.1) (ihAtoms others heq.2)
  intro left right heq
  exact hrec left right heq

/-- A semantically satisfiable HE leaf equation has a declarative matcher
witness.  Expression/expression equations are reserved for the paired list /
merge recursion. -/
private theorem exists_matchRel_of_solution_leaf
    {left right : Atom}
    (hsat : ∃ valuation : String → Metta.Atom,
      MettaEquationSatisfied valuation
        (toLeaTTaAtom left, toLeaTTaAtom right))
    (hleaf : ¬ BothExpressions left right) :
    ∃ out, DeclMatchSpec.MatchRel left right out := by
  obtain ⟨valuation, hequation⟩ := hsat
  cases left with
  | symbol leftName =>
      cases right with
      | symbol rightName =>
          have hname : leftName = rightName := by
            simpa [MettaEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation
          subst rightName
          exact ⟨Bindings.empty, .symSym leftName⟩
      | var rightName =>
          exact ⟨Bindings.empty.assign rightName (.symbol leftName),
            .nonVarVar (by simp [DeclMatchSpec.Atom.isVarB])⟩
      | grounded rightGround =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
      | expression rightAtoms =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
  | var leftName =>
      cases right with
      | symbol rightName =>
          exact ⟨Bindings.empty.assign leftName (.symbol rightName),
            .varNonVar (by simp [DeclMatchSpec.Atom.isVarB])⟩
      | var rightName =>
          exact ⟨Bindings.empty.addEquality leftName rightName,
            .varVar leftName rightName⟩
      | grounded rightGround =>
          exact ⟨Bindings.empty.assign leftName (.grounded rightGround),
            .varNonVar (by simp [DeclMatchSpec.Atom.isVarB])⟩
      | expression rightAtoms =>
          exact ⟨Bindings.empty.assign leftName (.expression rightAtoms),
            .varNonVar (by simp [DeclMatchSpec.Atom.isVarB])⟩
  | grounded leftGround =>
      cases right with
      | symbol rightName =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
      | var rightName =>
          exact ⟨Bindings.empty.assign rightName (.grounded leftGround),
            .nonVarVar (by simp [DeclMatchSpec.Atom.isVarB])⟩
      | grounded rightGround =>
          have hground : leftGround = rightGround :=
            toLeaTTaGround_injective (by
              simpa [MettaEquationSatisfied, toLeaTTaAtom,
                applyClassSolution] using hequation)
          subst rightGround
          exact ⟨Bindings.empty, .grounded leftGround⟩
      | expression rightAtoms =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
  | expression leftAtoms =>
      cases right with
      | symbol rightName =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
      | var rightName =>
          exact ⟨Bindings.empty.assign rightName (.expression leftAtoms),
            .nonVarVar (by simp [DeclMatchSpec.Atom.isVarB])⟩
      | grounded rightGround =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
      | expression rightAtoms =>
          exact (hleaf ⟨leftAtoms, rightAtoms, rfl, rfl⟩).elim

/-- The semantic leaf witness is returned by the executable HE matcher at
some finite fuel. -/
theorem exists_matchAtoms_of_solution_leaf
    {left right : Atom}
    (hsat : ∃ valuation : String → Metta.Atom,
      MettaEquationSatisfied valuation
        (toLeaTTaAtom left, toLeaTTaAtom right))
    (hleaf : ¬ BothExpressions left right) :
    ∃ out fuel, out ∈ matchAtoms left right fuel := by
  obtain ⟨out, hrel⟩ := exists_matchRel_of_solution_leaf hsat hleaf
  obtain ⟨fuel, hmem⟩ := DeclMatchSpec.matchAtoms_complete hrel
  exact ⟨out, fuel, hmem⟩

/-- A successful HE leaf match between two non-variables is necessarily
reflexive.  Thus every unequal non-variable reconciliation that succeeds must
enter the expression/list recursion. -/
theorem matchAtoms_eq_of_nonvariable_leaf
    {left right : Atom} {out : Bindings} {fuel : Nat}
    (hleft : DeclMatchSpec.Atom.isVarB left = false)
    (hright : DeclMatchSpec.Atom.isVarB right = false)
    (hleaf : ¬ BothExpressions left right)
    (hmatch : out ∈ matchAtoms left right fuel) :
    left = right := by
  have hrel := DeclMatchSpec.matchAtoms_sound hmatch
  cases hrel with
  | symSym => rfl
  | varVar => simp [DeclMatchSpec.Atom.isVarB] at hleft
  | varNonVar => simp [DeclMatchSpec.Atom.isVarB] at hleft
  | nonVarVar => simp [DeclMatchSpec.Atom.isVarB] at hright
  | grounded => rfl
  | expr => exact (hleaf (by simp [BothExpressions])).elim

/-- HE binding records produced by the matcher/merge lane never store a bare
variable as an assignment value; variable/variable relationships are equality
edges.  This excludes malformed tautological seeds such as `$x ← $x`, on
which recursive merge can diverge through repeated conflict matching. -/
def HEAssignmentsNonVariable (b : Bindings) : Prop :=
  ∀ key target, (key, .var target) ∉ b.assignments

/-- The remaining relation-level operation needed to lift semantic leaf
completeness through expression matching.  It is restricted to right inputs
that are actual declarative matcher results and to no-bare-variable seeds,
and it returns the same operational invariant for the recursive accumulator. -/
def HESatisfiedMatcherMergeRelComplete : Prop :=
  ∀ {valuation : String → Metta.Atom} {seed matched : Bindings}
      {left right : Atom},
    DeclMatchSpec.MatchRel left right matched →
    HEBindingSatisfied valuation seed →
    HEAssignmentsNonVariable seed →
    HEBindingSatisfied valuation matched →
    ∃ out, MergeRel seed matched out ∧ HEAssignmentsNonVariable out

/-- Existence-only core of satisfiable matcher-result merge-back.  The
no-bare-variable output field is a theorem of merge and need not be carried by
the paired reconciliation induction. -/
def HESatisfiedMatcherMergeRelExists : Prop :=
  ∀ {valuation : String → Metta.Atom} {seed matched : Bindings}
      {left right : Atom},
    DeclMatchSpec.MatchRel left right matched →
    HEBindingSatisfied valuation seed →
    HEAssignmentsNonVariable seed →
    HEBindingSatisfied valuation matched →
    ∃ out, MergeRel seed matched out

/-- Given satisfiable merge-back for matcher-origin records, every
semantically satisfiable HE atom equation has a declarative matcher witness.
The nested atom/list recursion is complete here; no representation comparison
or MGU uniqueness is used. -/
theorem exists_matchRel_of_solution_of_merge
    (hmerge : HESatisfiedMatcherMergeRelComplete) :
    ∀ {left right : Atom} {valuation : String → Metta.Atom},
      HEAtomEquationSatisfied valuation left right →
        ∃ out, DeclMatchSpec.MatchRel left right out := by
  let AtomGoal : Atom → Prop := fun left =>
    ∀ {right : Atom} {valuation : String → Metta.Atom},
      HEAtomEquationSatisfied valuation left right →
        ∃ out, DeclMatchSpec.MatchRel left right out
  let ListGoal : List Atom → Prop := fun lefts =>
    ∀ {rights : List Atom} {seed : Bindings}
        {valuation : String → Metta.Atom},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      MettaAtomListsSatisfied valuation
        (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) →
      ∃ out,
        DeclMatchSpec.MatchListAccRel lefts rights seed out ∧
          HEBindingSatisfied valuation out ∧
            HEAssignmentsNonVariable out
  have hrec : ∀ left, AtomGoal left := by
    apply Atom.rec (motive_1 := AtomGoal) (motive_2 := ListGoal)
    · intro symbol right valuation hequation
      exact exists_matchRel_of_solution_leaf
        ⟨valuation, hequation⟩ (by simp [BothExpressions])
    · intro name right valuation hequation
      exact exists_matchRel_of_solution_leaf
        ⟨valuation, hequation⟩ (by simp [BothExpressions])
    · intro ground right valuation hequation
      exact exists_matchRel_of_solution_leaf
        ⟨valuation, hequation⟩ (by simp [BothExpressions])
    · intro lefts hlefts right valuation hequation
      cases right with
      | symbol symbol =>
          exact exists_matchRel_of_solution_leaf
            ⟨valuation, hequation⟩ (by simp [BothExpressions])
      | var name =>
          exact exists_matchRel_of_solution_leaf
            ⟨valuation, hequation⟩ (by simp [BothExpressions])
      | grounded ground =>
          exact exists_matchRel_of_solution_leaf
            ⟨valuation, hequation⟩ (by simp [BothExpressions])
      | expression rights =>
          have hlists : MettaAtomListsSatisfied valuation
              (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) := by
            simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
              toLeaTTaAtom, applyClassSolution] using hequation
          obtain ⟨out, hlist, _hsat⟩ :=
            hlefts (seed := Bindings.empty) (valuation := valuation)
              ((hesat_empty_iff valuation).mpr trivial)
              (by simp [HEAssignmentsNonVariable, Bindings.empty]) hlists
          exact ⟨out, .expr hlist⟩
    · intro rights seed valuation hseed hseedNonvar hlists
      cases rights with
      | nil =>
          exact ⟨seed, .nil, hseed, hseedNonvar⟩
      | cons right rights =>
          simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
    · intro left lefts hleft hlefts rights seed valuation hseed
        hseedNonvar hlists
      cases rights with
      | nil =>
          simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
      | cons right rights =>
          have hequations :
              HEAtomEquationSatisfied valuation left right ∧
                MettaAtomListsSatisfied valuation
                  (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) := by
            simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
              toLeaTTaAtoms] using hlists
          obtain ⟨matched, hmatched⟩ := hleft hequations.1
          obtain ⟨matchFuel, hmatchMem⟩ :=
            DeclMatchSpec.matchAtoms_complete hmatched
          have hmatchedSat : HEBindingSatisfied valuation matched :=
            (matchAtoms_solution_iff hmatchMem valuation).mpr
              hequations.1
          obtain ⟨next, hmergeRel, hnextNonvar⟩ :=
            hmerge hmatched hseed hseedNonvar hmatchedSat
          obtain ⟨mergeFuel, hmergeMem⟩ :=
            mergeBindings_complete hmergeRel
          have hnextSat : HEBindingSatisfied valuation next :=
            (mergeBindings_solution_iff hmergeMem valuation).mpr
              ⟨hseed, hmatchedSat⟩
          obtain ⟨out, htail, houtSat, houtNonvar⟩ :=
            hlefts hnextSat hnextNonvar hequations.2
          exact ⟨out,
            .cons hmatched hmergeMem htail, houtSat, houtNonvar⟩
  intro left right valuation hequation
  exact hrec left hequation

/-- Executable form of semantic matcher completeness under the same sharply
isolated matcher-result merge-back premise. -/
theorem exists_matchAtoms_of_solution_of_merge
    (hmerge : HESatisfiedMatcherMergeRelComplete)
    {left right : Atom} {valuation : String → Metta.Atom}
    (hequation : HEAtomEquationSatisfied valuation left right) :
    ∃ out fuel, out ∈ matchAtoms left right fuel := by
  obtain ⟨out, hrel⟩ :=
    exists_matchRel_of_solution_of_merge hmerge hequation
  obtain ⟨fuel, hmem⟩ := DeclMatchSpec.matchAtoms_complete hrel
  exact ⟨out, fuel, hmem⟩

/-- Reverse operational witness for a repaired-LeaTTa matcher result. -/
def LeaMatcherCongruenceRealization
    (query pattern : Atom) (lb : Metta.Bindings) : Prop :=
  ∃ heOut fuel,
    heOut ∈ matchAtoms query pattern fuel ∧
      LeaBindingCongruence heOut lb

/-- Every successful standardized-apart LeaTTa leaf match is paired with an
actual executable HE matcher output carrying the settled congruence invariant. -/
theorem leaMatchAtoms_leaf_congruence_realization
    {query pattern : Atom} {lb : Metta.Bindings}
    (hLea : lb ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hdisj : VarsDisjoint query pattern)
    (hleaf : ¬ BothExpressions query pattern) :
    LeaMatcherCongruenceRealization query pattern lb := by
  obtain ⟨heOut, hrel⟩ :=
    exists_matchRel_of_leaMatchAtoms_leaf hLea hdisj hleaf
  obtain ⟨fuel, hHE⟩ := DeclMatchSpec.matchAtoms_complete hrel
  obtain ⟨leaOut, hLeaOut, hcongruence⟩ :=
    matchRel_leaf_congruence_transport hrel hdisj hleaf
  have hout : leaOut = lb :=
    leaMatchAtoms_leaf_subsingleton hleaf hLeaOut hLea
  subst leaOut
  exact ⟨heOut, fuel, hHE, hcongruence⟩

/-- Internal leaf realization needs no standardized-apart premise.  A
successful occurs-checked LeaTTa leaf supplies disjointness itself; matching a
variable with itself is handled by the representation-independent reflexive
singleton congruence. -/
theorem leaMatchAtoms_leaf_congruence_realization_internal
    {query pattern : Atom} {lb : Metta.Bindings}
    (hLea : lb ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hleaf : ¬ BothExpressions query pattern) :
    LeaMatcherCongruenceRealization query pattern lb := by
  rcases reflexiveVar_or_varsDisjoint_of_leaMatchAtoms_leaf hLea hleaf with
    ⟨name, hquery, hpattern⟩ | hdisj
  · subst query
    subst pattern
    have hout : lb = [] := by
      simpa [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom] using hLea
    subst lb
    obtain ⟨fuel, hHE⟩ := DeclMatchSpec.matchAtoms_complete
      (DeclMatchSpec.MatchRel.varVar name name)
    exact ⟨Bindings.empty.addEquality name name, fuel, hHE,
      LeaBindingCongruence.reflexiveSingleton name⟩
  · exact leaMatchAtoms_leaf_congruence_realization hLea hdisj hleaf

/-! ## Repaired-LeaTTa insertion determinism -/

/-- Equality insertion is operationally partial but single-valued.  This is a
shape theorem for the executable result list, independent of which unifier a
successful reconciliation returns. -/
private theorem leaAddVarEquality_subsingleton
    {bindings : Metta.Bindings} {left right : String}
    {first second : Metta.Bindings}
    (hfirst : first ∈ Metta.Bindings.addVarEquality bindings left right)
    (hsecond : second ∈ Metta.Bindings.addVarEquality bindings left right) :
    first = second := by
  simp only [Metta.Bindings.addVarEquality] at hfirst hsecond
  cases hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw bindings left right) left) with
  | none => simp [hunify] at hfirst
  | some result =>
      cases result with
      | nil => simp [hunify] at hfirst hsecond; simp_all
      | cons relation rest =>
          cases hreconcile : Metta.Bindings.reconcileAll bindings
              [(.var left, .var right)] with
          | none => simp [hunify, hreconcile] at hfirst
          | some subst =>
              simp [hunify, hreconcile] at hfirst hsecond
              simp_all

/-- Non-variable value insertion is operationally partial but single-valued,
uniformly across atom constructors. -/
private theorem leaAddVarBinding_nonvar_subsingleton
    {bindings : Metta.Bindings} {key : String} {value : Metta.Atom}
    {first second : Metta.Bindings}
    (hnonvar : ∀ target, value ≠ .var target)
    (hfirst : first ∈ Metta.Bindings.addVarBinding bindings key value)
    (hsecond : second ∈ Metta.Bindings.addVarBinding bindings key value) :
    first = second := by
  have hopen :
      Metta.Bindings.addVarBinding bindings key value =
        match Metta.Bindings.classValues bindings key with
        | [] => [Metta.Bindings.addValRaw bindings key value]
        | values =>
            match Metta.Bindings.unifyValues (values ++ [value]) with
            | none => []
            | some [] => [bindings]
            | some (_ :: _) =>
                match Metta.Bindings.reconcileAll bindings [(.var key, value)] with
                | none => []
                | some subst =>
                    [Metta.Bindings.rebuildFromReconciliation
                      bindings bindings [(.var key, value)] subst] := by
    cases value with
    | var target => exact (hnonvar target rfl).elim
    | sym name | gnd ground | expr atoms => rfl
  rw [hopen] at hfirst hsecond
  cases hvalues : Metta.Bindings.classValues bindings key with
  | nil =>
      rw [hvalues] at hfirst hsecond
      simp only [List.mem_singleton] at hfirst hsecond
      subst first
      subst second
      rfl
  | cons classHead classTail =>
      rw [hvalues] at hfirst hsecond
      simp only at hfirst hsecond
      cases hunify : Metta.Bindings.unifyValues
          ((classHead :: classTail) ++ [value]) with
      | none =>
          rw [hunify] at hfirst
          simp at hfirst
      | some result =>
          cases result with
          | nil =>
              rw [hunify] at hfirst hsecond
              simp only [List.mem_singleton] at hfirst hsecond
              subst first
              subst second
              rfl
          | cons relation rest =>
              rw [hunify] at hfirst hsecond
              cases hreconcile : Metta.Bindings.reconcileAll bindings
                  [(.var key, value)] with
              | none =>
                  rw [hreconcile] at hfirst
                  simp at hfirst
              | some subst =>
                  rw [hreconcile] at hfirst hsecond
                  simp only [List.mem_singleton] at hfirst hsecond
                  subst first
                  subst second
                  rfl

/-- Value insertion is likewise partial but single-valued on every atom
shape, including the whole-system reconciliation branch. -/
private theorem leaAddVarBinding_subsingleton
    {bindings : Metta.Bindings} {key : String} {value : Metta.Atom}
    {first second : Metta.Bindings}
    (hfirst : first ∈ Metta.Bindings.addVarBinding bindings key value)
    (hsecond : second ∈ Metta.Bindings.addVarBinding bindings key value) :
    first = second := by
  cases value with
  | var target =>
      exact leaAddVarEquality_subsingleton
        (by simpa [Metta.Bindings.addVarBinding] using hfirst)
        (by simpa [Metta.Bindings.addVarBinding] using hsecond)
  | sym name =>
      exact leaAddVarBinding_nonvar_subsingleton
        (by intro target; simp) hfirst hsecond
  | gnd ground =>
      exact leaAddVarBinding_nonvar_subsingleton
        (by intro target; simp) hfirst hsecond
  | expr atoms =>
      exact leaAddVarBinding_nonvar_subsingleton
        (by intro target; simp) hfirst hsecond

/-! ### Successful repaired-LeaTTa insertion views -/

/-- Complete branch certificate for a successful non-variable value
insertion.  Failure branches are absent because the result membership rules
them out. -/
inductive LeaAddVarBindingSuccess
    (source : Metta.Bindings) (key : String) (value : Metta.Atom)
    (out : Metta.Bindings) : Prop where
  | fresh
      (hclass : Metta.Bindings.classValues source key = [])
      (hout : out = Metta.Bindings.addValRaw source key value)
  | unchanged
      {classHead : Metta.Atom} {classTail : List Metta.Atom}
      (hclass : Metta.Bindings.classValues source key =
        classHead :: classTail)
      (hunify : Metta.Bindings.unifyValues
        ((classHead :: classTail) ++ [value]) = some [])
      (hout : out = source)
  | reconciled
      {classHead : Metta.Atom} {classTail : List Metta.Atom}
      {localHead : String × Metta.Atom}
      {localTail result : Metta.Subst}
      (hclass : Metta.Bindings.classValues source key =
        classHead :: classTail)
      (hunify : Metta.Bindings.unifyValues
        ((classHead :: classTail) ++ [value]) =
          some (localHead :: localTail))
      (hreconcile : Metta.Bindings.reconcileAll source
        [(.var key, value)] = some result)
      (hout : out = Metta.Bindings.rebuildFromReconciliation
        source source [(.var key, value)] result)

/-- Membership inversion for successful repaired-LeaTTa non-variable value
insertion. -/
theorem leaAddVarBinding_success_iff
    {source out : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hnonvar : ∀ target, value ≠ .var target) :
    out ∈ Metta.Bindings.addVarBinding source key value ↔
      LeaAddVarBindingSuccess source key value out := by
  have hopen :
      Metta.Bindings.addVarBinding source key value =
        match Metta.Bindings.classValues source key with
        | [] => [Metta.Bindings.addValRaw source key value]
        | values =>
            match Metta.Bindings.unifyValues (values ++ [value]) with
            | none => []
            | some [] => [source]
            | some (_ :: _) =>
                match Metta.Bindings.reconcileAll source [(.var key, value)] with
                | none => []
                | some subst =>
                    [Metta.Bindings.rebuildFromReconciliation
                      source source [(.var key, value)] subst] := by
    cases value with
    | var target => exact (hnonvar target rfl).elim
    | sym name | gnd ground | expr atoms => rfl
  constructor
  · intro hmem
    rw [hopen] at hmem
    cases hclass : Metta.Bindings.classValues source key with
    | nil =>
        rw [hclass] at hmem
        simp only [List.mem_singleton] at hmem
        exact .fresh hclass hmem
    | cons classHead classTail =>
        rw [hclass] at hmem
        simp only at hmem
        generalize hunify : Metta.Bindings.unifyValues
            ((classHead :: classTail) ++ [value]) = unifyResult at hmem
        cases unifyResult with
        | none =>
            simp at hmem
        | some substResult =>
            cases substResult with
            | nil =>
                simp only [List.mem_singleton] at hmem
                exact .unchanged hclass hunify hmem
            | cons localHead localTail =>
                cases hreconcile : Metta.Bindings.reconcileAll source
                    [(.var key, value)] with
                | none =>
                    rw [hreconcile] at hmem
                    simp at hmem
                | some result =>
                    rw [hreconcile] at hmem
                    simp only [List.mem_singleton] at hmem
                    exact .reconciled hclass hunify hreconcile hmem
  · intro hsuccess
    cases hsuccess with
    | fresh hclass hout =>
        subst out
        rw [hopen, hclass]
        simp
    | unchanged hclass hunify hout =>
        subst out
        rw [hopen, hclass]
        simp only
        rw [hunify]
        simp
    | reconciled hclass hunify hreconcile hout =>
        subst out
        rw [hopen, hclass]
        simp only
        rw [hunify, hreconcile]
        simp

/-- Complete branch certificate for a successful equality insertion. -/
inductive LeaAddVarEqualitySuccess
    (source : Metta.Bindings) (left right : String)
    (out : Metta.Bindings) : Prop where
  | unchanged
      (hunify : Metta.Bindings.unifyValues
        (Metta.Bindings.classValues
          (Metta.Bindings.addEqRaw source left right) left) = some [])
      (hout : out = Metta.Bindings.addEqRaw source left right)
  | reconciled
      {localHead : String × Metta.Atom}
      {localTail result : Metta.Subst}
      (hunify : Metta.Bindings.unifyValues
        (Metta.Bindings.classValues
          (Metta.Bindings.addEqRaw source left right) left) =
            some (localHead :: localTail))
      (hreconcile : Metta.Bindings.reconcileAll source
        [(.var left, .var right)] = some result)
      (hout : out = Metta.Bindings.rebuildFromReconciliation
        (Metta.Bindings.addEqRaw source left right) source
        [(.var left, .var right)] result)

/-- Membership inversion for successful repaired-LeaTTa equality insertion. -/
theorem leaAddVarEquality_success_iff
    {source out : Metta.Bindings} {left right : String} :
    out ∈ Metta.Bindings.addVarEquality source left right ↔
      LeaAddVarEqualitySuccess source left right out := by
  constructor
  · intro hmem
    simp only [Metta.Bindings.addVarEquality] at hmem
    generalize hunify : Metta.Bindings.unifyValues
        (Metta.Bindings.classValues
          (Metta.Bindings.addEqRaw source left right) left) = unifyResult at hmem
    cases unifyResult with
    | none =>
        simp at hmem
    | some substResult =>
        cases substResult with
        | nil =>
            simp only [List.mem_singleton] at hmem
            exact .unchanged hunify hmem
        | cons localHead localTail =>
            cases hreconcile : Metta.Bindings.reconcileAll source
                [(.var left, .var right)] with
            | none =>
                rw [hreconcile] at hmem
                simp at hmem
            | some result =>
                rw [hreconcile] at hmem
                simp only [List.mem_singleton] at hmem
                exact .reconciled hunify hreconcile hmem
  · intro hsuccess
    cases hsuccess with
    | unchanged hunify hout =>
        subst out
        simp only [Metta.Bindings.addVarEquality]
        rw [hunify]
        simp
    | reconciled hunify hreconcile hout =>
        subst out
        simp only [Metta.Bindings.addVarEquality]
        rw [hunify, hreconcile]
        simp

/-- Reverse fresh-value insertion: a successful LeaTTa result in a valueless
class is realized by HE's actual fresh `addVarBinding` branch. -/
theorem leaAddVarBinding_fresh_congruence_realization
    {b : Bindings} {lb leaOut : Metta.Bindings}
    {key : String} {value : Atom}
    (hbase : LeaBindingCongruence b lb)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : b.classValues key = [])
    (hLea : leaOut ∈
      Metta.Bindings.addVarBinding lb key (toLeaTTaAtom value)) :
    ∃ heOut fuel,
      heOut ∈ addVarBinding b key value fuel ∧
        LeaBindingCongruence heOut leaOut := by
  obtain ⟨canonical, hcanonical, hcongruence⟩ :=
    hbase.addVarBinding_fresh_of_heClass hnonvar hclass
  have hout : canonical = leaOut :=
    leaAddVarBinding_subsingleton hcanonical hLea
  subst canonical
  refine ⟨b.assign key value, 1, ?_, hcongruence⟩
  simp [addVarBinding, hclass]

/-- Reverse valueless alias insertion, allowing the two engines' opposite edge
orientations while preserving the equality-class invariant. -/
theorem leaAddVarEquality_valueless_congruence_realization
    {b : Bindings} {lb leaOut : Metta.Bindings}
    {queryVar patternVar : String}
    (hbase : LeaBindingCongruence b lb)
    (hne : queryVar ≠ patternVar)
    (hclass :
      (b.addEquality queryVar patternVar).classValues queryVar = [])
    (hLea : leaOut ∈
      Metta.Bindings.addVarEquality lb patternVar queryVar) :
    ∃ heOut fuel,
      heOut ∈ addVarEquality b queryVar patternVar fuel ∧
        LeaBindingCongruence heOut leaOut := by
  obtain ⟨canonical, hcanonical, hcongruence⟩ :=
    hbase.addVarEquality_valueless_of_heClass hne hclass
  have hout : canonical = leaOut :=
    leaAddVarEquality_subsingleton hcanonical hLea
  subst canonical
  have hconsistent : Bindings.valuesConsistent
      ((b.addEquality queryVar patternVar).classValues queryVar) = true := by
    simp [hclass, Bindings.valuesConsistent]
  refine ⟨b.addEquality queryVar patternVar, 1, ?_, hcongruence⟩
  simp [addVarEquality, hconsistent]

/-- Reverse unchanged-value insertion.  The two executable guards are kept
explicit: congruence does not identify either engine's ordered class-value
list, while this branch needs only the fact that both guards selected their
respective no-change cases. -/
theorem leaAddVarBinding_same_congruence_realization
    {b : Bindings} {lb leaOut : Metta.Bindings}
    {key : String} {value first : Atom} {rest : List Atom}
    {leaValues : List Metta.Atom}
    (hbase : LeaBindingCongruence b lb)
    (hnonvar : ∀ target, toLeaTTaAtom value ≠ .var target)
    (hheClass : b.classValues key = first :: rest)
    (hheConsistent : Bindings.valuesConsistent (first :: rest) = true)
    (hsame : first = value)
    (hleaClass : Metta.Bindings.classValues lb key = leaValues)
    (hleaNonempty : leaValues ≠ [])
    (hleaUnify : Metta.Bindings.unifyValues
      (leaValues ++ [toLeaTTaAtom value]) = some [])
    (hLea : leaOut ∈
      Metta.Bindings.addVarBinding lb key (toLeaTTaAtom value)) :
    ∃ heOut fuel,
      heOut ∈ addVarBinding b key value fuel ∧
        LeaBindingCongruence heOut leaOut := by
  have hcanonical : lb ∈
      Metta.Bindings.addVarBinding lb key (toLeaTTaAtom value) := by
    rw [Metta.Bindings.addVarBinding_nochange
      hnonvar hleaClass hleaNonempty hleaUnify]
    simp
  have hout : lb = leaOut :=
    leaAddVarBinding_subsingleton hcanonical hLea
  subst leaOut
  subst first
  refine ⟨b, 1, ?_, hbase⟩
  simp [addVarBinding, hheClass, hheConsistent]

/-- Reverse consistent equality insertion.  Opposite edge orientations are
absorbed by `LeaBindingCongruence.addEqRaw`; only the executable consistency
guards remain presentation-specific. -/
theorem leaAddVarEquality_consistent_congruence_realization
    {b : Bindings} {lb leaOut : Metta.Bindings}
    {queryVar patternVar : String}
    (hbase : LeaBindingCongruence b lb)
    (hne : queryVar ≠ patternVar)
    (hheConsistent : Bindings.valuesConsistent
      ((b.addEquality queryVar patternVar).classValues queryVar) = true)
    (hleaUnify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw lb patternVar queryVar) patternVar) = some [])
    (hLea : leaOut ∈
      Metta.Bindings.addVarEquality lb patternVar queryVar) :
    ∃ heOut fuel,
      heOut ∈ addVarEquality b queryVar patternVar fuel ∧
        LeaBindingCongruence heOut leaOut := by
  let candidate := Metta.Bindings.addEqRaw lb patternVar queryVar
  have hcanonical : candidate ∈
      Metta.Bindings.addVarEquality lb patternVar queryVar := by
    rw [Metta.Bindings.addVarEquality_nochange hleaUnify]
    simp [candidate]
  have hout : candidate = leaOut :=
    leaAddVarEquality_subsingleton hcanonical hLea
  subst leaOut
  refine ⟨b.addEquality queryVar patternVar, 1, ?_, ?_⟩
  · simp [addVarEquality, hheConsistent]
  · exact hbase.addEqRaw hne

/-! ## Reverse merge base and leaf steps -/

/-- Reverse operational witness for one repaired-LeaTTa merge result. -/
def LeaMergeCongruenceRealization
    (heLeft heRight : Bindings) (leaOut : Metta.Bindings) : Prop :=
  ∃ heOut fuel,
    heOut ∈ mergeBindings heLeft heRight fuel ∧
      LeaBindingCongruence heOut leaOut

/-- One selected branch through LeaTTa's left-to-right merge fold.  The
relation retains the successful insertion at each relation while discarding
unselected alternatives. -/
inductive LeaMergeBranchRel :
    Metta.Bindings → Metta.Bindings → Metta.Bindings → Prop where
  | nil {seed : Metta.Bindings} :
      LeaMergeBranchRel seed [] seed
  | value {seed next out : Metta.Bindings} {key : String}
      {value : Metta.Atom} {rest : Metta.Bindings} :
      next ∈ Metta.Bindings.addVarBinding seed key value →
      LeaMergeBranchRel next rest out →
      LeaMergeBranchRel seed
        (Metta.BindingRel.val key value :: rest) out
  | equality {seed next out : Metta.Bindings} {left right : String}
      {rest : Metta.Bindings} :
      next ∈ Metta.Bindings.addVarEquality seed left right →
      LeaMergeBranchRel next rest out →
      LeaMergeBranchRel seed
        (Metta.BindingRel.eq left right :: rest) out

/-- Recursive branch semantics equivalent to the list-accumulator `foldl`
implementation when started from one seed. -/
private def leaMergeBranchResults
    (seed : Metta.Bindings) : Metta.Bindings → List Metta.Bindings
  | [] => [seed]
  | Metta.BindingRel.val key value :: rest =>
      (Metta.Bindings.addVarBinding seed key value).flatMap
        (fun next => leaMergeBranchResults next rest)
  | Metta.BindingRel.eq left right :: rest =>
      (Metta.Bindings.addVarEquality seed left right).flatMap
        (fun next => leaMergeBranchResults next rest)

private theorem leattaMergeFold_eq_flatMap_branchResults
    (seeds : List Metta.Bindings) (relations : Metta.Bindings) :
    relations.foldl Metta.Bindings.mergeOne seeds =
      seeds.flatMap (fun seed => leaMergeBranchResults seed relations) := by
  induction relations generalizing seeds with
  | nil => simp [leaMergeBranchResults]
  | cons relation relations ih =>
      cases relation with
      | val key value =>
          simp only [List.foldl_cons, Metta.Bindings.mergeOne]
          rw [ih]
          simp [leaMergeBranchResults, List.flatMap_assoc]
      | eq left right =>
          simp only [List.foldl_cons, Metta.Bindings.mergeOne]
          rw [ih]
          simp [leaMergeBranchResults, List.flatMap_assoc]

private theorem leaMergeBranchRel_iff_mem_results
    {seed right out : Metta.Bindings} :
    LeaMergeBranchRel seed right out ↔
      out ∈ leaMergeBranchResults seed right := by
  constructor
  · intro hbranch
    induction hbranch with
    | nil => simp [leaMergeBranchResults]
    | value hadd htail ih =>
        simp only [leaMergeBranchResults, List.mem_flatMap]
        exact ⟨_, hadd, ih⟩
    | equality hadd htail ih =>
        simp only [leaMergeBranchResults, List.mem_flatMap]
        exact ⟨_, hadd, ih⟩
  · induction right generalizing seed out with
    | nil =>
        intro hmem
        simp only [leaMergeBranchResults, List.mem_singleton] at hmem
        subst out
        exact .nil
    | cons relation rest ih =>
        intro hmem
        cases relation with
        | val key value =>
            simp only [leaMergeBranchResults, List.mem_flatMap] at hmem
            obtain ⟨next, hadd, htail⟩ := hmem
            exact .value hadd (ih htail)
        | eq left right =>
            simp only [leaMergeBranchResults, List.mem_flatMap] at hmem
            obtain ⟨next, hadd, htail⟩ := hmem
            exact .equality hadd (ih htail)

/-- Membership in LeaTTa's public merge is exactly one branchwise sequence of
successful value/equality insertions. -/
theorem leaMergeBranchRel_iff_mem_merge
    {left right out : Metta.Bindings} :
    LeaMergeBranchRel left right out ↔
      out ∈ Metta.Bindings.merge left right := by
  rw [leaMergeBranchRel_iff_mem_results]
  unfold Metta.Bindings.merge
  rw [leattaMergeFold_eq_flatMap_branchResults]
  simp

private theorem assignment_mem_of_lookup_eq_some
    {assignments : List (String × Atom)} {key : String} {value : Atom}
    (hlookup : List.lookup key assignments = some value) :
    (key, value) ∈ assignments := by
  induction assignments with
  | nil => simp at hlookup
  | cons binding assignments ih =>
      rcases binding with ⟨storedKey, storedValue⟩
      by_cases hkey : key = storedKey
      · subst storedKey
        simp at hlookup
        subst storedValue
        simp
      · have hbeq : (key == storedKey) = false := by simp [hkey]
        simp only [List.lookup_cons, hbeq] at hlookup
        exact List.mem_cons_of_mem _ (ih hlookup)

private theorem heLookup_eq_some_of_assignment_mem_of_nodup
    {assignments : List (String × Atom)}
    (hkeys : (assignments.map Prod.fst).Nodup)
    {key : String} {value : Atom}
    (hmem : (key, value) ∈ assignments) :
    List.lookup key assignments = some value := by
  induction assignments with
  | nil => cases hmem
  | cons binding rest ih =>
      rcases binding with ⟨headKey, headValue⟩
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      have hkeysTail : (rest.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        simp
      · have hheadFresh : headKey ∉ rest.map Prod.fst := by
          simpa using (List.nodup_cons.mp hkeys).1
        have hne : key ≠ headKey := by
          intro heq
          subst key
          exact hheadFresh (List.mem_map_of_mem htail)
        have hbeq : (key == headKey) = false := by simp [hne]
        simpa [List.lookup_cons, hbeq] using ih hkeysTail htail

/-- Every executable HE matcher output satisfies the no-bare-variable
assignment invariant used by recursive merge-back. -/
theorem heAssignmentsNonVariable_of_matchAtoms
    {left right : Atom} {out : Bindings} {fuel : Nat}
    (hmatch : out ∈ matchAtoms left right fuel) :
    HEAssignmentsNonVariable out := by
  intro key target hassignment
  have hlookup : out.lookup key = some (.var target) := by
    unfold Bindings.lookup
    exact heLookup_eq_some_of_assignment_mem_of_nodup
      (DeclMatchSpec.matchAtoms_assignmentsNodup hmatch) hassignment
  exact DeclMatchSpec.matchAtoms_noVarAssignmentValues hmatch hlookup

/-- Declarative matcher results have the same operational invariant. -/
theorem heAssignmentsNonVariable_of_matchRel
    {left right : Atom} {out : Bindings}
    (hmatch : DeclMatchSpec.MatchRel left right out) :
    HEAssignmentsNonVariable out := by
  obtain ⟨fuel, hmem⟩ := DeclMatchSpec.matchAtoms_complete hmatch
  exact heAssignmentsNonVariable_of_matchAtoms hmem

/-- The no-bare-variable invariant reads directly at an assignment member. -/
theorem HEAssignmentsNonVariable.isVarB_eq_false_of_assignment
    {b : Bindings} (h : HEAssignmentsNonVariable b)
    {key : String} {value : Atom}
    (hvalue : (key, value) ∈ b.assignments) :
    DeclMatchSpec.Atom.isVarB value = false := by
  cases value with
  | var target => exact (h key target hvalue).elim
  | symbol name | grounded name | expression name => rfl

/-- Overwriting or extending one assignment with a non-variable atom
preserves the no-bare-variable invariant. -/
theorem HEAssignmentsNonVariable.assign
    {b : Bindings} (h : HEAssignmentsNonVariable b)
    {key : String} {value : Atom}
    (hvalue : DeclMatchSpec.Atom.isVarB value = false) :
    HEAssignmentsNonVariable (b.assign key value) := by
  intro storedKey target hmem
  by_cases hbound : b.isBound key = true
  · unfold Bindings.assign at hmem
    simp only [hbound, if_true] at hmem
    obtain ⟨binding, hbinding, hmap⟩ := List.mem_map.mp hmem
    rcases binding with ⟨oldKey, oldValue⟩
    by_cases hkey : oldKey = key
    · simp [hkey] at hmap
      rcases hmap with ⟨rfl, htarget⟩
      subst value
      simp [DeclMatchSpec.Atom.isVarB] at hvalue
    · simp [hkey] at hmap
      rcases hmap with ⟨rfl, rfl⟩
      exact h oldKey target hbinding
  · have hbound' : b.isBound key = false := by
      cases h : b.isBound key <;> simp_all
    unfold Bindings.assign at hmem
    simp only [hbound', Bool.false_eq_true, if_false] at hmem
    rcases List.mem_append.mp hmem with hold | hnew
    · exact h storedKey target hold
    · simp only [List.mem_singleton, Prod.mk.injEq] at hnew
      rcases hnew with ⟨rfl, htarget⟩
      subst value
      simp [DeclMatchSpec.Atom.isVarB] at hvalue

/-- Equality insertion leaves assignment payloads unchanged. -/
theorem HEAssignmentsNonVariable.addEquality
    {b : Bindings} (h : HEAssignmentsNonVariable b)
    (left right : String) :
    HEAssignmentsNonVariable (b.addEquality left right) := by
  intro key target hmem
  apply h key target
  simpa [Bindings.addEquality] using hmem

/-- Consequently every value selected from any equality class is a
non-variable atom. -/
theorem HEAssignmentsNonVariable.isVarB_eq_false_of_classValue
    {b : Bindings} (h : HEAssignmentsNonVariable b)
    {key : String} {value : Atom}
    (hvalue : value ∈ b.classValues key) :
    DeclMatchSpec.Atom.isVarB value = false := by
  unfold Bindings.classValues at hvalue
  rcases List.mem_filterMap.mp hvalue with ⟨storedKey, _hclass, hlookup⟩
  apply h.isVarB_eq_false_of_assignment
  exact assignment_mem_of_lookup_eq_some (by
    simpa [Bindings.lookup] using hlookup)

/-- Declarative HE merge preserves the no-bare-variable assignment invariant
from both inputs.  Recursive conflict matches satisfy the invariant because
HE represents variable/variable results as equality edges. -/
theorem mergeRel_assignmentsNonVariable
    {left right out : Bindings} (h : MergeRel left right out)
    (hleft : HEAssignmentsNonVariable left)
    (hright : HEAssignmentsNonVariable right) :
    HEAssignmentsNonVariable out := by
  apply MergeRel.rec
    (motive_1 := fun b _ value out _ =>
      HEAssignmentsNonVariable b →
      DeclMatchSpec.Atom.isVarB value = false →
      HEAssignmentsNonVariable out)
    (motive_2 := fun b _ _ out _ =>
      HEAssignmentsNonVariable b →
      HEAssignmentsNonVariable out)
    (motive_3 := fun b assignments out _ =>
      HEAssignmentsNonVariable b →
      (∀ key value, (key, value) ∈ assignments →
        DeclMatchSpec.Atom.isVarB value = false) →
      HEAssignmentsNonVariable out)
    (motive_4 := fun b _ out _ =>
      HEAssignmentsNonVariable b →
      HEAssignmentsNonVariable out)
    (motive_5 := fun first second out _ =>
      HEAssignmentsNonVariable first →
      HEAssignmentsNonVariable second →
      HEAssignmentsNonVariable out)
    (t := h)
  · intro b key value hclass hb hvalue
    exact hb.assign hvalue
  · intro b key value first rest hclass hconsistent hsame hb hvalue
    exact hb
  · intro b key value first rest matched out hclass hconsistent
      hdifferent hmatch hmerge ihmerge hb hvalue
    exact ihmerge hb (heAssignmentsNonVariable_of_matchRel hmatch)
  · intro b key value first rest matched out hclass hinconsistent
      hmatch hmerge ihmerge hb hvalue
    have hmatched : HEAssignmentsNonVariable matched := by
      intro storedKey target hmem
      have hnonvar :=
        DeclMatchSpec.matchListRel_assignmentValue_isVarB_false hmatch hmem
      simp [DeclMatchSpec.Atom.isVarB] at hnonvar
    exact ihmerge hb hmatched
  · intro b first second hconsistent hb
    exact hb.addEquality first second
  · intro b first second leftValue rightValue matched out hvalues
      hinconsistent hmatch hmerge ihmerge hb
    exact ihmerge (hb.addEquality first second)
      (heAssignmentsNonVariable_of_matchRel hmatch)
  · intro b first second leftValue rightValue thirdValue rest matched out
      hvalues hinconsistent hmatch hmerge ihmerge hb
    have hmatched : HEAssignmentsNonVariable matched := by
      intro storedKey target hmem
      have hnonvar :=
        DeclMatchSpec.matchListRel_assignmentValue_isVarB_false hmatch hmem
      simp [DeclMatchSpec.Atom.isVarB] at hnonvar
    exact ihmerge (hb.addEquality first second) hmatched
  · intro b hb hassignments
    exact hb
  · intro b key value rest next out hadd hrest ihadd ihrest
      hb hassignments
    have hvalue : DeclMatchSpec.Atom.isVarB value = false :=
      hassignments key value (by simp)
    have htail : ∀ tailKey tailValue,
        (tailKey, tailValue) ∈ rest →
          DeclMatchSpec.Atom.isVarB tailValue = false := by
      intro tailKey tailValue hmem
      exact hassignments tailKey tailValue (by simp [hmem])
    exact ihrest (ihadd hb hvalue) htail
  · intro b hb
    exact hb
  · intro b first second rest next out hadd hrest ihadd ihrest hb
    exact ihrest (ihadd hb)
  · intro first second mid out hassignments hequalities
      ihassignments ihequalities hfirst hsecond
    apply ihequalities
    apply ihassignments hfirst
    intro key value hmem
    exact hsecond.isVarB_eq_false_of_assignment hmem
  · exact hleft
  · exact hright

/-- Executable merge inherits no-bare-variable preservation from its
declarative soundness theorem. -/
theorem mergeBindings_assignmentsNonVariable
    {left right out : Bindings} {fuel : Nat}
    (h : out ∈ mergeBindings left right fuel)
    (hleft : HEAssignmentsNonVariable left)
    (hright : HEAssignmentsNonVariable right) :
    HEAssignmentsNonVariable out :=
  mergeRel_assignmentsNonVariable (mergeBindings_sound h) hleft hright

/-- The existence-only matcher merge-back premise implies the earlier packed
premise; output non-variable preservation is discharged by the general merge
theorem rather than assumed locally. -/
theorem heSatisfiedMatcherMergeRelComplete_of_exists
    (hexists : HESatisfiedMatcherMergeRelExists) :
    HESatisfiedMatcherMergeRelComplete := by
  intro valuation seed matched left right hmatch hseedSat hseedNonvar
      hmatchedSat
  obtain ⟨out, hmerge⟩ :=
    hexists hmatch hseedSat hseedNonvar hmatchedSat
  exact ⟨out, hmerge,
    mergeRel_assignmentsNonVariable hmerge hseedNonvar
      (heAssignmentsNonVariable_of_matchRel hmatch)⟩

/-- Congruence to an actual HE matcher result rules out bare-variable value
relations on the repaired-LeaTTa side.  Such relationships are represented as
explicit equality edges by both repaired matchers. -/
theorem no_leaVarValue_of_match_congruence
    {query pattern : Atom} {heOut : Bindings} {fuel : Nat}
    {leaOut : Metta.Bindings}
    (hHE : heOut ∈ matchAtoms query pattern fuel)
    (hcongruence : LeaBindingCongruence heOut leaOut)
    {key target : String} :
    Metta.BindingRel.val key (.var target) ∉ leaOut := by
  intro hlea
  obtain ⟨heKey, heValue, hassignment, _hclass, hatom⟩ :=
    hcongruence.classValues.2 key (.var target) hlea
  cases hatom with
  | @«variable» heTarget _ hvalueClass =>
      have hlookup : heOut.lookup heKey = some (.var heTarget) := by
        unfold Bindings.lookup
        exact heLookup_eq_some_of_assignment_mem_of_nodup
          (DeclMatchSpec.matchAtoms_assignmentsNodup hHE) hassignment
      exact DeclMatchSpec.matchAtoms_noVarAssignmentValues hHE hlookup

/-- Every LeaTTa value relation paired with an HE matcher output has a
non-variable payload. -/
theorem leaMatcherValue_nonvar_of_congruence
    {query pattern : Atom} {heOut : Bindings} {fuel : Nat}
    {leaOut : Metta.Bindings}
    (hHE : heOut ∈ matchAtoms query pattern fuel)
    (hcongruence : LeaBindingCongruence heOut leaOut)
    {key : String} {value : Metta.Atom}
    (hvalue : Metta.BindingRel.val key value ∈ leaOut) :
    ∀ target, value ≠ .var target := by
  intro target heq
  subst value
  exact no_leaVarValue_of_match_congruence hHE hcongruence hvalue

/-- Branchwise merge certificate with each successful insertion already
inverted to its exact fresh/unchanged/reconciled runtime view. -/
inductive LeaMergeSuccessBranchRel :
    Metta.Bindings → Metta.Bindings → Metta.Bindings → Prop where
  | nil {seed : Metta.Bindings} :
      LeaMergeSuccessBranchRel seed [] seed
  | value {seed next out : Metta.Bindings} {key : String}
      {value : Metta.Atom} {rest : Metta.Bindings} :
      LeaAddVarBindingSuccess seed key value next →
      LeaMergeSuccessBranchRel next rest out →
      LeaMergeSuccessBranchRel seed
        (Metta.BindingRel.val key value :: rest) out
  | equality {seed next out : Metta.Bindings} {left right : String}
      {rest : Metta.Bindings} :
      LeaAddVarEqualitySuccess seed left right next →
      LeaMergeSuccessBranchRel next rest out →
      LeaMergeSuccessBranchRel seed
        (Metta.BindingRel.eq left right :: rest) out

/-- A branch whose value payloads are non-variable upgrades to the exact
success-view certificate used by the paired reconciliation induction. -/
theorem LeaMergeBranchRel.toSuccessViews
    {seed right out : Metta.Bindings}
    (hbranch : LeaMergeBranchRel seed right out)
    (hnonvar : ∀ key value,
      Metta.BindingRel.val key value ∈ right →
        ∀ target, value ≠ .var target) :
    LeaMergeSuccessBranchRel seed right out := by
  induction hbranch with
  | nil => exact .nil
  | @value seed next out key value rest hadd htail ih =>
      have hvalueNonvar : ∀ target, value ≠ .var target :=
        hnonvar key value (by simp)
      have htailNonvar : ∀ tailKey tailValue,
          Metta.BindingRel.val tailKey tailValue ∈ rest →
            ∀ target, tailValue ≠ .var target := by
        intro tailKey tailValue hmem
        exact hnonvar tailKey tailValue (by simp [hmem])
      exact .value
        ((leaAddVarBinding_success_iff hvalueNonvar).mp hadd)
        (ih htailNonvar)
  | @equality seed next out left right rest hadd htail ih =>
      have htailNonvar : ∀ tailKey tailValue,
          Metta.BindingRel.val tailKey tailValue ∈ rest →
            ∀ target, tailValue ≠ .var target := by
        intro tailKey tailValue hmem
        exact hnonvar tailKey tailValue (by simp [hmem])
      exact .equality
        (leaAddVarEquality_success_iff.mp hadd)
        (ih htailNonvar)

/-- The success-view certificate recovers the actual executable branch when
its value payloads are known non-variable. -/
theorem LeaMergeSuccessBranchRel.toBranch
    {seed right out : Metta.Bindings}
    (hsuccess : LeaMergeSuccessBranchRel seed right out)
    (hnonvar : ∀ key value,
      Metta.BindingRel.val key value ∈ right →
        ∀ target, value ≠ .var target) :
    LeaMergeBranchRel seed right out := by
  induction hsuccess with
  | nil => exact .nil
  | @value seed next out key value rest hhead htail ih =>
      have hvalueNonvar : ∀ target, value ≠ .var target :=
        hnonvar key value (by simp)
      have htailNonvar : ∀ tailKey tailValue,
          Metta.BindingRel.val tailKey tailValue ∈ rest →
            ∀ target, tailValue ≠ .var target := by
        intro tailKey tailValue hmem
        exact hnonvar tailKey tailValue (by simp [hmem])
      exact .value
        ((leaAddVarBinding_success_iff hvalueNonvar).mpr hhead)
        (ih htailNonvar)
  | @equality seed next out left right rest hhead htail ih =>
      have htailNonvar : ∀ tailKey tailValue,
          Metta.BindingRel.val tailKey tailValue ∈ rest →
            ∀ target, tailValue ≠ .var target := by
        intro tailKey tailValue hmem
        exact hnonvar tailKey tailValue (by simp [hmem])
      exact .equality
        (leaAddVarEquality_success_iff.mpr hhead)
        (ih htailNonvar)

/-- Branchwise successful merge preserves the host-float-free fragment. -/
theorem LeaMergeSuccessBranchRel.resultNoFloat
    {seed right out : Metta.Bindings}
    (hsuccess : LeaMergeSuccessBranchRel seed right out)
    (hseedNoFloat : LeaBindingsNoFloat seed)
    (hrightNoFloat : LeaBindingsNoFloat right)
    (hnonvar : ∀ key value,
      Metta.BindingRel.val key value ∈ right →
        ∀ target, value ≠ .var target) :
    LeaBindingsNoFloat out := by
  induction hsuccess with
  | nil => exact hseedNoFloat
  | @value seed next out key value rest hhead htail ih =>
      have hvalueNoFloat : MettaAtomNoFloat value :=
        hrightNoFloat key value (by simp)
      have hvalueNonvar : ∀ target, value ≠ .var target :=
        hnonvar key value (by simp)
      have hadd : next ∈
          Metta.Bindings.addVarBinding seed key value :=
        (leaAddVarBinding_success_iff hvalueNonvar).mpr hhead
      have hnextNoFloat : LeaBindingsNoFloat next :=
        leaAddVarBinding_result_noFloat
          hseedNoFloat hvalueNoFloat hadd
      have hrestNoFloat : LeaBindingsNoFloat rest := by
        intro restKey restValue hmem
        exact hrightNoFloat restKey restValue (by simp [hmem])
      have hrestNonvar : ∀ restKey restValue,
          Metta.BindingRel.val restKey restValue ∈ rest →
            ∀ target, restValue ≠ .var target := by
        intro restKey restValue hmem
        exact hnonvar restKey restValue (by simp [hmem])
      exact ih hnextNoFloat hrestNoFloat hrestNonvar
  | @equality seed next out left right rest hhead htail ih =>
      have hadd : next ∈
          Metta.Bindings.addVarEquality seed left right :=
        leaAddVarEquality_success_iff.mpr hhead
      have hnextNoFloat : LeaBindingsNoFloat next :=
        leaAddVarEquality_result_noFloat hseedNoFloat hadd
      have hrestNoFloat : LeaBindingsNoFloat rest := by
        intro restKey restValue hmem
        exact hrightNoFloat restKey restValue (by simp [hmem])
      have hrestNonvar : ∀ restKey restValue,
          Metta.BindingRel.val restKey restValue ∈ rest →
            ∀ target, restValue ≠ .var target := by
        intro restKey restValue hmem
        exact hnonvar restKey restValue (by simp [hmem])
      exact ih hnextNoFloat hrestNoFloat hrestNonvar

/-- A successful Lea merge of a binding paired with an actual HE matcher
output always exposes a branchwise fresh/unchanged/reconciled certificate. -/
theorem exists_leaMergeSuccessBranch_of_match_congruence
    {query pattern : Atom} {heRight : Bindings} {fuel : Nat}
    {leaLeft leaRight leaOut : Metta.Bindings}
    (hHE : heRight ∈ matchAtoms query pattern fuel)
    (hright : LeaBindingCongruence heRight leaRight)
    (hmerge : leaOut ∈ Metta.Bindings.merge leaLeft leaRight) :
    LeaMergeSuccessBranchRel leaLeft leaRight leaOut := by
  apply (leaMergeBranchRel_iff_mem_merge.mpr hmerge).toSuccessViews
  intro key value hvalue
  exact leaMatcherValue_nonvar_of_congruence hHE hright hvalue

/-- Merging the empty right binding is the identity in both engines. -/
theorem leaMerge_empty_right_congruence_realization
    {b : Bindings} {lb leaOut : Metta.Bindings}
    (hbase : LeaBindingCongruence b lb)
    (hLea : leaOut ∈ Metta.Bindings.merge lb Metta.Bindings.empty) :
    LeaMergeCongruenceRealization b Bindings.empty leaOut := by
  have hout : leaOut = lb := by
    simpa [Metta.Bindings.merge, Metta.Bindings.empty] using hLea
  subst leaOut
  exact ⟨b, 1, by simp [mergeBindings, Bindings.empty], hbase⟩

/-- A fresh leaf assignment can be merged into an arbitrary congruent seed in
the reverse direction.  This is the first nonempty accumulator step of the
expression matcher. -/
theorem leaMerge_singleton_fresh_value_congruence_realization
    {seed : Bindings} {leaSeed leaOut : Metta.Bindings}
    {key : String} {value : Atom}
    (hbase : LeaBindingCongruence seed leaSeed)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : seed.classValues key = [])
    (hLea : leaOut ∈ Metta.Bindings.merge leaSeed
      [Metta.BindingRel.val key (toLeaTTaAtom value)]) :
    LeaMergeCongruenceRealization seed
      ⟨[(key, value)], []⟩ leaOut := by
  have hLeaAdd : leaOut ∈
      Metta.Bindings.addVarBinding leaSeed key (toLeaTTaAtom value) := by
    simpa [Metta.Bindings.merge, Metta.Bindings.mergeOne] using hLea
  obtain ⟨heOut, addFuel, hHEAdd, hcongruence⟩ :=
    leaAddVarBinding_fresh_congruence_realization
      hbase hnonvar hclass hLeaAdd
  refine ⟨heOut, addFuel + 1, ?_, hcongruence⟩
  simpa [mergeBindings] using hHEAdd

/-- A valueless leaf alias can likewise be merged into a congruent seed;
the repaired-LeaTTa edge is deliberately reversed from HE's runtime edge. -/
theorem leaMerge_singleton_valueless_equality_congruence_realization
    {seed : Bindings} {leaSeed leaOut : Metta.Bindings}
    {queryVar patternVar : String}
    (hbase : LeaBindingCongruence seed leaSeed)
    (hne : queryVar ≠ patternVar)
    (hclass :
      (seed.addEquality queryVar patternVar).classValues queryVar = [])
    (hLea : leaOut ∈ Metta.Bindings.merge leaSeed
      [Metta.BindingRel.eq patternVar queryVar]) :
    LeaMergeCongruenceRealization seed
      ⟨[], [(queryVar, patternVar)]⟩ leaOut := by
  have hLeaAdd : leaOut ∈
      Metta.Bindings.addVarEquality leaSeed patternVar queryVar := by
    simpa [Metta.Bindings.merge, Metta.Bindings.mergeOne] using hLea
  obtain ⟨heOut, addFuel, hHEAdd, hcongruence⟩ :=
    leaAddVarEquality_valueless_congruence_realization
      hbase hne hclass hLeaAdd
  refine ⟨heOut, addFuel + 1, ?_, hcongruence⟩
  simpa [mergeBindings] using hHEAdd

/-- LeaTTa's seeded list matcher distributes over a `flatMap` accumulator.
This local form is used only to expose the one predecessor seed selected by a
successful nondeterministic tail run. -/
private theorem leattaMatchAll_flatMap_acc
    (patterns queries : List Metta.Atom) {α : Type} (acc : List α)
    (f : α → List Metta.Bindings) :
    Metta.matchAll none (acc.flatMap f) patterns queries =
      acc.flatMap (fun seed =>
        Metta.matchAll none (f seed) patterns queries) := by
  induction patterns generalizing queries acc f with
  | nil =>
      cases queries <;> simp [Metta.matchAll]
  | cons pattern patterns ih =>
      cases queries with
      | nil => simp [Metta.matchAll]
      | cons query queries =>
          simp only [Metta.matchAll]
          rw [List.flatMap_assoc]
          simpa using ih queries acc
            (fun seed =>
              (f seed).flatMap fun current =>
                (Metta.matchAtomsWith none pattern query).flatMap fun matched =>
                  Metta.Bindings.merge current matched)

/-- Membership form of singleton-seed decomposition for `matchAll`. -/
private theorem leattaMem_matchAll_seedwise
    {patterns queries : List Metta.Atom}
    {seeds : List Metta.Bindings} {out : Metta.Bindings} :
    out ∈ Metta.matchAll none seeds patterns queries ↔
      ∃ seed ∈ seeds,
        out ∈ Metta.matchAll none [seed] patterns queries := by
  have hseedwise :
      Metta.matchAll none seeds patterns queries =
        seeds.flatMap (fun seed =>
          Metta.matchAll none [seed] patterns queries) := by
    simpa using
      (leattaMatchAll_flatMap_acc patterns queries seeds
        (fun seed => [seed]))
  rw [hseedwise]
  simp

/-- The one remaining operation-level obligation needed by the reverse
matcher recursion.  Its right input is explicitly a paired matcher result,
which is the only shape produced by expression matching and by HE's recursive
conflict branches; arbitrary malformed congruent records are not admitted.
Internal conflict matches need not be standardized apart. -/
def LeaMatchedMergeCongruenceComplete : Prop :=
  ∀ {query pattern : Atom} {heLeft heRight : Bindings}
      {leaLeft leaRight leaOut : Metta.Bindings} {fuel : Nat},
    HEAssignmentsNonVariable heLeft →
    heRight ∈ matchAtoms query pattern fuel →
    leaRight ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query) →
    LeaBindingCongruence heLeft leaLeft →
    LeaBindingCongruence heRight leaRight →
    leaOut ∈ Metta.Bindings.merge leaLeft leaRight →
    LeaMergeCongruenceRealization heLeft heRight leaOut

/-- Once general reverse merge realization is available, the entire repaired
LeaTTa expression matcher—its nested atom/list recursion included—constructs
an actual HE matcher result.  The list induction carries only
`LeaBindingCongruence`; solution theory is never threaded separately. -/
theorem leaMatchAtoms_congruence_realization_of_merge
    (hmerge : LeaMatchedMergeCongruenceComplete) :
    ∀ {query pattern : Atom} {leaOut : Metta.Bindings},
      leaOut ∈ Metta.matchAtoms
        (toLeaTTaAtom pattern) (toLeaTTaAtom query) →
      LeaMatcherCongruenceRealization query pattern leaOut := by
  let AtomGoal : Atom → Prop := fun query =>
    ∀ {pattern : Atom} {leaOut : Metta.Bindings},
      leaOut ∈ Metta.matchAtoms
        (toLeaTTaAtom pattern) (toLeaTTaAtom query) →
      LeaMatcherCongruenceRealization query pattern leaOut
  let ListGoal : List Atom → Prop := fun queries =>
    ∀ {patterns : List Atom} {heSeed : Bindings}
        {leaSeed leaOut : Metta.Bindings},
      LeaBindingCongruence heSeed leaSeed →
      HEAssignmentsNonVariable heSeed →
      leaOut ∈ Metta.matchAll none [leaSeed]
        (toLeaTTaAtoms patterns) (toLeaTTaAtoms queries) →
      ∃ heOut,
        DeclMatchSpec.MatchListAccRel queries patterns heSeed heOut ∧
          LeaBindingCongruence heOut leaOut ∧
            HEAssignmentsNonVariable heOut
  have hrec : ∀ query, AtomGoal query := by
    apply Atom.rec (motive_1 := AtomGoal) (motive_2 := ListGoal)
    · intro symbol pattern leaOut hLea
      exact leaMatchAtoms_leaf_congruence_realization_internal
        hLea (by simp [BothExpressions])
    · intro name pattern leaOut hLea
      exact leaMatchAtoms_leaf_congruence_realization_internal
        hLea (by simp [BothExpressions])
    · intro ground pattern leaOut hLea
      exact leaMatchAtoms_leaf_congruence_realization_internal
        hLea (by simp [BothExpressions])
    · intro queries hqueries pattern leaOut hLea
      cases pattern with
      | symbol symbol =>
          exact leaMatchAtoms_leaf_congruence_realization_internal
            hLea (by simp [BothExpressions])
      | var name =>
          exact leaMatchAtoms_leaf_congruence_realization_internal
            hLea (by simp [BothExpressions])
      | grounded ground =>
          exact leaMatchAtoms_leaf_congruence_realization_internal
            hLea (by simp [BothExpressions])
      | expression patterns =>
          change leaOut ∈ Metta.matchAll none [[]]
            (toLeaTTaAtoms patterns) (toLeaTTaAtoms queries) at hLea
          obtain ⟨heOut, hlist, hcongruence, _houtNonvar⟩ :=
            hqueries LeaBindingCongruence.empty
              (by intro key target hmem; simp [Bindings.empty] at hmem) hLea
          obtain ⟨fuel, hHE⟩ :=
            DeclMatchSpec.matchAtoms_complete
              (DeclMatchSpec.MatchRel.expr hlist)
          exact ⟨heOut, fuel, hHE, hcongruence⟩
    · intro patterns heSeed leaSeed leaOut hseed hseedNonvar hLea
      cases patterns with
      | nil =>
          have hout : leaOut = leaSeed := by
            simpa [Metta.matchAll] using hLea
          subst leaOut
          exact ⟨heSeed, .nil, hseed, hseedNonvar⟩
      | cons pattern patterns =>
          simp [Metta.matchAll] at hLea
    · intro query queries hquery hqueries patterns
        heSeed leaSeed leaOut hseed hseedNonvar hLea
      cases patterns with
      | nil => simp [Metta.matchAll] at hLea
      | cons pattern patterns =>
          simp only [toLeaTTaAtoms, Metta.matchAll,
            List.flatMap_cons, List.flatMap_nil, List.append_nil] at hLea
          obtain ⟨leaNext, hleaNext, htail⟩ :=
            leattaMem_matchAll_seedwise.mp hLea
          obtain ⟨leaHead, hleaHead, hleaMerge⟩ :=
            List.mem_flatMap.mp hleaNext
          obtain ⟨heHead, headFuel, hHEHead, hheadCongruence⟩ :=
            hquery hleaHead
          obtain ⟨heNext, mergeFuel, hHEMerge, hnextCongruence⟩ :=
            hmerge hseedNonvar hHEHead hleaHead
              hseed hheadCongruence hleaMerge
          have hheadNonvar : HEAssignmentsNonVariable heHead :=
            heAssignmentsNonVariable_of_matchAtoms hHEHead
          have hnextNonvar : HEAssignmentsNonVariable heNext :=
            mergeBindings_assignmentsNonVariable
              hHEMerge hseedNonvar hheadNonvar
          obtain ⟨heOut, htailRel, houtCongruence, houtNonvar⟩ :=
            hqueries hnextCongruence hnextNonvar htail
          exact ⟨heOut,
            .cons (DeclMatchSpec.matchAtoms_sound hHEHead)
              hHEMerge htailRel,
            houtCongruence, houtNonvar⟩
  intro query pattern leaOut hLea
  exact hrec query hLea

/-! ## Non-reconciling executable insertion branches

These are the base cases of the later paired operational induction.  They
consume `LeaBindingCongruence` directly and expose an actual repaired-LeaTTa
operation result; no relation-list presentation is compared.
-/

/-- An actual HE insertion into a valueless class is transported by the
already-proved fresh-class congruence theorem. -/
theorem addVarBinding_fresh_congruence_transport
    {b heOut : Bindings} {lb : Metta.Bindings}
    {v : String} {value : Atom} {fuel : Nat}
    (hbase : LeaBindingCongruence b lb)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : b.classValues v = [])
    (hHE : heOut ∈ addVarBinding b v value fuel) :
    ∃ leaOut,
      leaOut ∈ Metta.Bindings.addVarBinding lb v (toLeaTTaAtom value) ∧
        LeaBindingCongruence heOut leaOut := by
  have hout : heOut = b.assign v value := by
    cases fuel with
    | zero => simp [addVarBinding] at hHE
    | succ fuel => simpa [addVarBinding, hclass] using hHE
  subst heOut
  exact hbase.addVarBinding_fresh_of_heClass hnonvar hclass

/-- An actual HE equality insertion joining two valueless classes transports
without representative chronology.  The repaired LeaTTa edge is allowed the
opposite orientation because equality-class closure is the invariant. -/
theorem addVarEquality_valueless_congruence_transport
    {b heOut : Bindings} {lb : Metta.Bindings}
    {queryVar patternVar : String} {fuel : Nat}
    (hbase : LeaBindingCongruence b lb)
    (hne : queryVar ≠ patternVar)
    (hclass :
      (b.addEquality queryVar patternVar).classValues queryVar = [])
    (hHE : heOut ∈ addVarEquality b queryVar patternVar fuel) :
    ∃ leaOut,
      leaOut ∈ Metta.Bindings.addVarEquality lb patternVar queryVar ∧
        LeaBindingCongruence heOut leaOut := by
  have hconsistent : Bindings.valuesConsistent
      ((b.addEquality queryVar patternVar).classValues queryVar) = true := by
    simp [hclass, Bindings.valuesConsistent]
  have hout : heOut = b.addEquality queryVar patternVar := by
    cases fuel with
    | zero => simp [addVarEquality] at hHE
    | succ fuel => simpa [addVarEquality, hconsistent] using hHE
  subst heOut
  exact hbase.addVarEquality_valueless_of_heClass hne hclass

/-- The empty-right merge base case preserves the settled invariant exactly. -/
theorem mergeBindings_empty_right_congruence_transport
    {b heOut : Bindings} {lb : Metta.Bindings} {fuel : Nat}
    (hbase : LeaBindingCongruence b lb)
    (hHE : heOut ∈ mergeBindings b Bindings.empty fuel) :
    ∃ leaOut,
      leaOut ∈ Metta.Bindings.merge lb Metta.Bindings.empty ∧
        LeaBindingCongruence heOut leaOut := by
  cases fuel with
  | zero => simp [mergeBindings] at hHE
  | succ fuel =>
      have hout : heOut = b := by
        rw [mergeBindings_empty_right b fuel] at hHE
        simpa using hHE
      subst heOut
      refine ⟨lb, ?_, hbase⟩
      change lb ∈ Metta.Bindings.merge lb []
      simp [Metta.Bindings.merge]

/-! ## One Robinson-elimination step

The repaired LeaTTa trace distinguishes the two operational cases that matter
to HE's binding record.  A non-variable constraint contributes an assignment
whose stored atom is compared modulo the equality classes already built; a
variable constraint contributes an equality-class edge and no raw value.
These lemmas are the step cases for the later trace induction.
-/

/-- Adding an HE equality edge only enlarges equality classes. -/
private theorem eqClass_mono_addEquality
    (b : Bindings) (left right : String) :
    ∀ {start finish},
      finish ∈ b.eqClass start →
        finish ∈ (b.addEquality left right).eqClass start := by
  intro start finish hclass
  rw [EqualityClosure.mem_eqClass_iff_reachable] at hclass ⊢
  apply hclass.mono
  intro x y hadj
  rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
  rcases hadj with ⟨hne, hforward | hreverse⟩
  · exact ⟨hne, Or.inl (by
      simp [Bindings.addEquality, hforward])⟩
  · exact ⟨hne, Or.inr (by
      simp [Bindings.addEquality, hreverse])⟩

/-- A non-variable Robinson constraint is one HE assignment modulo aliases
already present in the input equality closure.  Freshness of the assignment
key is the operational fact supplied by `UnifyStateFresh` in the full trace
induction. -/
theorem eliminationStep_nonvar_preserves_classValues
    {b : Bindings} {trace : List (String × Metta.Atom)}
    {key : String} {value : Atom} {leaValue : Metta.Atom}
    (htrace : LeaEliminationTraceClassValueRel b trace)
    (hlookup : b.lookup key = none)
    (hatom : HELeaAtomClassRel b value leaValue)
    (hnonvar : ∀ target, leaValue ≠ .var target) :
    (key, value) ∈ (b.assign key value).assignments ∧
      LeaEliminationTraceClassValueRel
        (b.assign key value) ((key, leaValue) :: trace) := by
  have hbound : b.isBound key = false := by
    simp [Bindings.isBound, hlookup]
  have hclassMono : ∀ {start finish},
      finish ∈ b.eqClass start →
        finish ∈ (b.assign key value).eqClass start := by
    intro start finish hclass
    simpa [Bindings.eqClass, Bindings.assign, hbound] using hclass
  have hatom' :
      HELeaAtomClassRel (b.assign key value) value leaValue :=
    HELeaAtomClassRel.mono hclassMono hatom
  constructor
  · simp [Bindings.assign, hbound]
  · constructor
    · intro heKey heValue hmem
      simp only [Bindings.assign, hbound, Bool.false_eq_true, if_false,
        List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨leaKey, stored, hstored, hstoredNonVar,
          hkeyClass, hstoredAtom⟩ := htrace.1 heKey heValue hold
        exact ⟨leaKey, stored, List.mem_cons_of_mem _ hstored,
          hstoredNonVar, hclassMono hkeyClass,
          HELeaAtomClassRel.mono hclassMono hstoredAtom⟩
      · rcases hnew with ⟨hkey, hvalue⟩
        subst heKey
        subst heValue
        exact ⟨key, leaValue, by simp, hnonvar,
          by rw [EqualityClosure.mem_eqClass_iff_reachable], hatom'⟩
    · intro leaKey stored hmem hstoredNonVar
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with hnew | hold
      · rcases hnew with ⟨hkey, hvalue⟩
        subst leaKey
        subst stored
        exact ⟨key, value, by simp [Bindings.assign, hbound],
          by rw [EqualityClosure.mem_eqClass_iff_reachable], hatom'⟩
      · obtain ⟨heKey, heValue, hvalue, hkeyClass, hstoredAtom⟩ :=
          htrace.2 leaKey stored hold hstoredNonVar
        exact ⟨heKey, heValue,
          by simp [Bindings.assign, hbound, hvalue],
          hclassMono hkeyClass,
          HELeaAtomClassRel.mono hclassMono hstoredAtom⟩

/-- A variable Robinson constraint is one HE equality-class edge.  Since the
trace entry is an alias rather than a raw value, it only enlarges the classes
used by existing provenance witnesses. -/
theorem eliminationStep_variable_preserves_classValues
    {b : Bindings} {trace : List (String × Metta.Atom)}
    {key target : String}
    (htrace : LeaEliminationTraceClassValueRel b trace) :
    target ∈ (b.addEquality key target).eqClass key ∧
      LeaEliminationTraceClassValueRel
        (b.addEquality key target) ((key, .var target) :: trace) := by
  have hclassMono : ∀ {start finish : String},
      finish ∈ b.eqClass start →
        finish ∈ (b.addEquality key target).eqClass start :=
    eqClass_mono_addEquality b key target
  constructor
  · rw [EqualityClosure.mem_eqClass_iff_reachable]
    by_cases hsame : key = target
    · subst target
      exact .rfl
    · exact (show
        (EqualityClosure.edgeGraph
          (b.addEquality key target).equalities).Adj key target by
          rw [EqualityClosure.edgeGraph_adj_iff]
          exact ⟨hsame, Or.inl (by simp [Bindings.addEquality])⟩).reachable
  · constructor
    · intro heKey heValue hmem
      have hold : (heKey, heValue) ∈ b.assignments := by
        simpa [Bindings.addEquality] using hmem
      obtain ⟨leaKey, leaValue, hleaValue, hnonvar,
          hkeyClass, hatom⟩ := htrace.1 heKey heValue hold
      exact ⟨leaKey, leaValue, List.mem_cons_of_mem _ hleaValue,
        hnonvar, hclassMono hkeyClass,
        HELeaAtomClassRel.mono hclassMono hatom⟩
    · intro leaKey leaValue hmem hnonvar
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with hnew | hold
      · rcases hnew with ⟨hkey, hvalue⟩
        subst leaKey
        subst leaValue
        exact (hnonvar target rfl).elim
      · obtain ⟨heKey, heValue, hvalue, hkeyClass, hatom⟩ :=
          htrace.2 leaKey leaValue hold hnonvar
        exact ⟨heKey, heValue,
          by simpa [Bindings.addEquality] using hvalue,
          hclassMono hkeyClass,
          HELeaAtomClassRel.mono hclassMono hatom⟩

/-! ## Full trace replay

The class-value relation ignores variable entries by design, so we pair it
with the exact class observation needed from those entries.  The resulting
record is the structural certificate consumed by reconciliation.
-/

/-- Every variable entry selected by the solve trace is connected in the HE
output equality closure. -/
def LeaEliminationTraceAliasRel
    (b : Bindings) (trace : List (String × Metta.Atom)) : Prop :=
  ∀ key target, (key, .var target) ∈ trace →
    target ∈ b.eqClass key

/-- Structural reading of a complete elimination trace: variable entries are
class edges and non-variable entries are class-relative raw assignments. -/
structure LeaEliminationTraceStructuralRel
    (b : Bindings) (trace : List (String × Metta.Atom)) : Prop where
  aliases : LeaEliminationTraceAliasRel b trace
  classValues : LeaEliminationTraceClassValueRel b trace

/-- Soundness half of trace provenance: every direct HE assignment originates
from a non-variable entry of the selected Robinson trace, modulo the output
equality classes. -/
def LeaEliminationTraceAssignmentsSound
    (b : Bindings) (trace : List (String × Metta.Atom)) : Prop :=
  ∀ key value, (key, value) ∈ b.assignments →
    ∃ leaKey leaValue,
      (leaKey, leaValue) ∈ trace ∧
        (∀ target, leaValue ≠ .var target) ∧
          leaKey ∈ b.eqClass key ∧
            HELeaAtomClassRel b value leaValue

/-- Strong, presentation-local provenance used only at the right boundary of
an HE merge.  Every direct assignment is literally one translated Robinson
trace entry.  The merge theorem below weakens this to class-relative
`LeaEliminationTraceAssignmentsSound` after the live accumulator has added its
own equality edges. -/
def LeaEliminationTraceAssignmentsExact
    (b : Bindings) (trace : List (String × Metta.Atom)) : Prop :=
  ∀ key value, (key, value) ∈ b.assignments →
    DeclMatchSpec.Atom.isVarB value = false ∧
      (key, toLeaTTaAtom value) ∈ trace

/-- List-facing form of exact trace provenance, used by the assignment fold
inside the declarative HE merge relation. -/
def LeaEliminationTraceAssignmentListExact
    (assignments : List (String × Atom))
    (trace : List (String × Metta.Atom)) : Prop :=
  ∀ key value, (key, value) ∈ assignments →
    DeclMatchSpec.Atom.isVarB value = false ∧
      (key, toLeaTTaAtom value) ∈ trace

/-! ### Derivation-local recursive matcher provenance

The well-founded reconciliation proof must not assume that every unrelated
HE matcher output is sound for one fixed Robinson trace.  The following
five-way certificate instead follows one concrete merge derivation and asks
for trace provenance exactly at the recursive atom/list matcher calls that
occur in its conflict constructors. -/

mutual

/-- Local trace certificate for one value insertion derivation. -/
inductive AddVarBindingTraceSound (trace : List (String × Metta.Atom)) :
    ∀ {b key value out}, AddVarBindingRel b key value out → Prop where
  | fresh {b : Bindings} {key : String} {value : Atom}
      {hclass : b.classValues key = []} :
      AddVarBindingTraceSound trace
        (AddVarBindingRel.fresh (val := value) hclass)
  | same {b : Bindings} {key : String} {value first : Atom}
      {rest : List Atom}
      {hclass : b.classValues key = first :: rest}
      {hconsistent : Bindings.valuesConsistent (first :: rest) = true}
      {hsame : first = value} :
      AddVarBindingTraceSound trace
        (AddVarBindingRel.same hclass hconsistent hsame)
  | conflict {b : Bindings} {key : String} {value first : Atom}
      {rest : List Atom} {matched out : Bindings}
      {hclass : b.classValues key = first :: rest}
      {hconsistent : Bindings.valuesConsistent (first :: rest) = true}
      {hdifferent : first ≠ value}
      {hmatch : DeclMatchSpec.MatchRel first value matched}
      {hmerge : MergeRel b matched out} :
      LeaEliminationTraceAssignmentsSound matched trace →
      MergeTraceSound trace hmerge →
      AddVarBindingTraceSound trace
        (AddVarBindingRel.conflict hclass hconsistent hdifferent
          hmatch hmerge)
  | reconcile {b : Bindings} {key : String} {value first : Atom}
      {rest : List Atom} {matched out : Bindings}
      {hclass : b.classValues key = first :: rest}
      {hinconsistent : Bindings.valuesConsistent (first :: rest) = false}
      {hmatch : DeclMatchSpec.MatchListRel
        (List.replicate (rest.length + 1) first) (rest ++ [value]) matched}
      {hmerge : MergeRel b matched out} :
      LeaEliminationTraceAssignmentsSound matched trace →
      MergeTraceSound trace hmerge →
      AddVarBindingTraceSound trace
        (AddVarBindingRel.reconcile hclass hinconsistent hmatch hmerge)

/-- Local trace certificate for one equality insertion derivation. -/
inductive AddVarEqualityTraceSound (trace : List (String × Metta.Atom)) :
    ∀ {b left right out}, AddVarEqualityRel b left right out → Prop where
  | consistent {b : Bindings} {left right : String}
      {hconsistent : Bindings.valuesConsistent
        ((b.addEquality left right).classValues left) = true} :
      AddVarEqualityTraceSound trace
        (AddVarEqualityRel.consistent hconsistent)
  | pairConflict {b : Bindings} {left right : String}
      {first second : Atom} {matched out : Bindings}
      {hvalues : (b.addEquality left right).classValues left =
        [first, second]}
      {hinconsistent : Bindings.valuesConsistent [first, second] = false}
      {hmatch : DeclMatchSpec.MatchRel first second matched}
      {hmerge : MergeRel (b.addEquality left right) matched out} :
      LeaEliminationTraceAssignmentsSound matched trace →
      MergeTraceSound trace hmerge →
      AddVarEqualityTraceSound trace
        (AddVarEqualityRel.pairConflict hvalues hinconsistent
          hmatch hmerge)
  | classConflict {b : Bindings} {left right : String}
      {first second third : Atom} {rest : List Atom}
      {matched out : Bindings}
      {hvalues : (b.addEquality left right).classValues left =
        first :: second :: third :: rest}
      {hinconsistent : Bindings.valuesConsistent
        (first :: second :: third :: rest) = false}
      {hmatch : DeclMatchSpec.MatchListRel
        (List.replicate (rest.length + 2) first)
        (second :: third :: rest) matched}
      {hmerge : MergeRel (b.addEquality left right) matched out} :
      LeaEliminationTraceAssignmentsSound matched trace →
      MergeTraceSound trace hmerge →
      AddVarEqualityTraceSound trace
        (AddVarEqualityRel.classConflict hvalues hinconsistent
          hmatch hmerge)

/-- Local trace certificate for the assignment fold of one merge. -/
inductive MergeAssignsTraceSound (trace : List (String × Metta.Atom)) :
    ∀ {b assignments out}, MergeAssignsRel b assignments out → Prop where
  | nil {b : Bindings} :
      MergeAssignsTraceSound trace (MergeAssignsRel.nil (acc := b))
  | cons {b : Bindings} {key : String} {value : Atom}
      {rest : List (String × Atom)} {next out : Bindings}
      {hadd : AddVarBindingRel b key value next}
      {htail : MergeAssignsRel next rest out} :
      AddVarBindingTraceSound trace hadd →
      MergeAssignsTraceSound trace htail →
      MergeAssignsTraceSound trace (MergeAssignsRel.cons hadd htail)

/-- Local trace certificate for the equality fold of one merge. -/
inductive MergeEqsTraceSound (trace : List (String × Metta.Atom)) :
    ∀ {b equalities out}, MergeEqsRel b equalities out → Prop where
  | nil {b : Bindings} :
      MergeEqsTraceSound trace (MergeEqsRel.nil (acc := b))
  | cons {b : Bindings} {left right : String}
      {rest : List (String × String)} {next out : Bindings}
      {hadd : AddVarEqualityRel b left right next}
      {htail : MergeEqsRel next rest out} :
      AddVarEqualityTraceSound trace hadd →
      MergeEqsTraceSound trace htail →
      MergeEqsTraceSound trace (MergeEqsRel.cons hadd htail)

/-- Derivation-local trace certificate for a complete HE merge. -/
inductive MergeTraceSound (trace : List (String × Metta.Atom)) :
    ∀ {left right out}, MergeRel left right out → Prop where
  | mk {left right mid out : Bindings}
      {hassignments : MergeAssignsRel left right.assignments mid}
      {hequalities : MergeEqsRel mid right.equalities out} :
      MergeAssignsTraceSound trace hassignments →
      MergeEqsTraceSound trace hequalities →
      MergeTraceSound trace (MergeRel.mk hassignments hequalities)

end

mutual

/-- Derivation-local trace certificate for an HE atom matcher.  Leaf matches
introduce no recursive merge obligation.  The expression constructor retains
the certificate for every accumulator merge performed by pointwise matching.
This is deliberately indexed by one concrete matcher derivation rather than
by every matcher result at the same trace. -/
inductive MatchTraceSound (trace : List (String × Metta.Atom)) :
    ∀ {left right out}, DeclMatchSpec.MatchRel left right out → Prop where
  | symSym {name : String} :
      MatchTraceSound trace (DeclMatchSpec.MatchRel.symSym name)
  | varVar {left right : String} :
      MatchTraceSound trace (DeclMatchSpec.MatchRel.varVar left right)
  | varNonVar {key : String} {value : Atom}
      {hnonvar : DeclMatchSpec.Atom.isVarB value = false} :
      MatchTraceSound trace
        (DeclMatchSpec.MatchRel.varNonVar (v := key) (t := value) hnonvar)
  | nonVarVar {value : Atom} {key : String}
      {hnonvar : DeclMatchSpec.Atom.isVarB value = false} :
      MatchTraceSound trace
        (DeclMatchSpec.MatchRel.nonVarVar (s := value) (v := key) hnonvar)
  | grounded {value : OSLFCore.GroundedValue} :
      MatchTraceSound trace (DeclMatchSpec.MatchRel.grounded value)
  | expr {left right : List Atom} {out : Bindings}
      {hlist : DeclMatchSpec.MatchListAccRel
        left right Bindings.empty out} :
      MatchListTraceSound trace hlist →
      MatchTraceSound trace (DeclMatchSpec.MatchRel.expr hlist)

/-- Pointwise-list companion to `MatchTraceSound`.  Besides recursively
certifying the head and tail matchers, the `cons` constructor records the
derivation-local certificate for the exact merge selected between them. -/
inductive MatchListTraceSound (trace : List (String × Metta.Atom)) :
    ∀ {left right seed out},
      DeclMatchSpec.MatchListAccRel left right seed out → Prop where
  | nil {seed : Bindings} :
      MatchListTraceSound trace
        (DeclMatchSpec.MatchListAccRel.nil (seed := seed))
  | cons {left right : Atom} {lefts rights : List Atom}
      {seed matched next out : Bindings} {fuel : Nat}
      {hmatch : DeclMatchSpec.MatchRel left right matched}
      {hmerge : next ∈ mergeBindings seed matched fuel}
      {htail : DeclMatchSpec.MatchListAccRel lefts rights next out} :
      MatchTraceSound trace hmatch →
      MergeTraceSound trace (mergeBindings_sound hmerge) →
      MatchListTraceSound trace htail →
      MatchListTraceSound trace
        (DeclMatchSpec.MatchListAccRel.cons hmatch hmerge htail)

end

/-- Derivation-local merge certificates are monotone in the ambient
Robinson trace.  This is the certificate transport needed when a strictly
smaller prefix or residual run is embedded back into the full successful
solve trace. -/
theorem MergeTraceSound.mono
    {small large : List (String × Metta.Atom)}
    {left right out : Bindings} {hmerge : MergeRel left right out}
    (h : MergeTraceSound small hmerge)
    (hsubset : ∀ entry ∈ small, entry ∈ large) :
    MergeTraceSound large hmerge := by
  have hlift : ∀ {b : Bindings},
      LeaEliminationTraceAssignmentsSound b small →
        LeaEliminationTraceAssignmentsSound b large := by
    intro b hsound key value hmem
    obtain ⟨leaKey, leaValue, hentry, hnonvar, hclass, hatom⟩ :=
      hsound key value hmem
    exact ⟨leaKey, leaValue, hsubset _ hentry, hnonvar, hclass, hatom⟩
  let AddValueMotive := fun
      {b : Bindings} {key : String} {value : Atom} {result : Bindings}
      (hrel : AddVarBindingRel b key value result)
      (_ : AddVarBindingTraceSound small hrel) =>
    AddVarBindingTraceSound large hrel
  let AddEqualityMotive := fun
      {b : Bindings} {first second : String} {result : Bindings}
      (hrel : AddVarEqualityRel b first second result)
      (_ : AddVarEqualityTraceSound small hrel) =>
    AddVarEqualityTraceSound large hrel
  let AssignFoldMotive := fun
      {b : Bindings} {assignments : List (String × Atom)}
      {result : Bindings} (hrel : MergeAssignsRel b assignments result)
      (_ : MergeAssignsTraceSound small hrel) =>
    MergeAssignsTraceSound large hrel
  let EqualityFoldMotive := fun
      {b : Bindings} {equalities : List (String × String)}
      {result : Bindings} (hrel : MergeEqsRel b equalities result)
      (_ : MergeEqsTraceSound small hrel) =>
    MergeEqsTraceSound large hrel
  let MergeMotive := fun
      {mergeLeft mergeRight result : Bindings}
      (hrel : MergeRel mergeLeft mergeRight result)
      (_ : MergeTraceSound small hrel) =>
    MergeTraceSound large hrel
  apply MergeTraceSound.rec
    (motive_1 := AddValueMotive)
    (motive_2 := AddEqualityMotive)
    (motive_3 := AssignFoldMotive)
    (motive_4 := EqualityFoldMotive)
    (motive_5 := MergeMotive)
    (t := h)
  · intro b key value hclass
    exact AddVarBindingTraceSound.fresh (hclass := hclass)
  · intro b key value first rest hclass hconsistent hsame
    exact AddVarBindingTraceSound.same
      (hclass := hclass) (hconsistent := hconsistent) (hsame := hsame)
  · intro b key value first rest matched result hclass hconsistent
      hdifferent hmatch hrecursive hmatched _hcert ihrecursive
    exact AddVarBindingTraceSound.conflict
      (hclass := hclass) (hconsistent := hconsistent)
      (hdifferent := hdifferent) (hmatch := hmatch)
      (hmerge := hrecursive)
      (hlift hmatched) ihrecursive
  · intro b key value first rest matched result hclass hinconsistent
      hmatch hrecursive hmatched _hcert ihrecursive
    exact AddVarBindingTraceSound.reconcile
      (hclass := hclass) (hinconsistent := hinconsistent)
      (hmatch := hmatch) (hmerge := hrecursive)
      (hlift hmatched) ihrecursive
  · intro b first second hconsistent
    exact AddVarEqualityTraceSound.consistent
      (hconsistent := hconsistent)
  · intro b first second leftValue rightValue matched result hvalues
      hinconsistent hmatch hrecursive hmatched _hcert ihrecursive
    exact AddVarEqualityTraceSound.pairConflict
      (hvalues := hvalues) (hinconsistent := hinconsistent)
      (hmatch := hmatch) (hmerge := hrecursive)
      (hlift hmatched) ihrecursive
  · intro b first second leftValue rightValue thirdValue rest matched
      result hvalues hinconsistent hmatch hrecursive hmatched _hcert
      ihrecursive
    exact AddVarEqualityTraceSound.classConflict
      (hvalues := hvalues) (hinconsistent := hinconsistent)
      (hmatch := hmatch) (hmerge := hrecursive)
      (hlift hmatched) ihrecursive
  · intro b
    exact MergeAssignsTraceSound.nil
  · intro b key value rest next result hadd hrest _haddCert _hrestCert
      ihadd ihrest
    exact MergeAssignsTraceSound.cons ihadd ihrest
  · intro b
    exact MergeEqsTraceSound.nil
  · intro b first second rest next result hadd hrest _haddCert
      _hrestCert ihadd ihrest
    exact MergeEqsTraceSound.cons ihadd ihrest
  · intro mergeLeft mergeRight mid result hassignments hequalities
      _hassignmentsCert _hequalitiesCert ihassignments ihequalities
    exact MergeTraceSound.mk ihassignments ihequalities

mutual

/-- An atom-matcher trace certificate remains valid when its local Robinson
trace is embedded into a larger successful solve trace. -/
theorem MatchTraceSound.mono
    {small large : List (String × Metta.Atom)}
    {left right : Atom} {out : Bindings}
    {hmatch : DeclMatchSpec.MatchRel left right out}
    (h : MatchTraceSound small hmatch)
    (hsubset : ∀ entry ∈ small, entry ∈ large) :
    MatchTraceSound large hmatch := by
  cases h with
  | symSym => exact MatchTraceSound.symSym
  | varVar => exact MatchTraceSound.varVar
  | varNonVar =>
      exact MatchTraceSound.varNonVar (hnonvar := by assumption)
  | nonVarVar =>
      exact MatchTraceSound.nonVarVar (hnonvar := by assumption)
  | grounded => exact MatchTraceSound.grounded
  | expr hlist => exact MatchTraceSound.expr (hlist.mono hsubset)

/-- The pointwise matcher companion is monotone in the ambient Robinson
trace, including every live accumulator merge selected by the derivation. -/
theorem MatchListTraceSound.mono
    {small large : List (String × Metta.Atom)}
    {left right : List Atom} {seed out : Bindings}
    {hmatch : DeclMatchSpec.MatchListAccRel left right seed out}
    (h : MatchListTraceSound small hmatch)
    (hsubset : ∀ entry ∈ small, entry ∈ large) :
    MatchListTraceSound large hmatch := by
  cases h with
  | nil => exact MatchListTraceSound.nil
  | cons hhead hmerge htail =>
      exact MatchListTraceSound.cons (hmerge := by assumption)
        (hhead.mono hsubset) (hmerge.mono hsubset) (htail.mono hsubset)

end

/-- A global trace-soundness hypothesis is a convenient sufficient condition
for the derivation-local certificate.  The reverse implication is neither
needed nor true: a fixed Robinson trace says nothing about unrelated matcher
calls elsewhere in the runtime. -/
theorem mergeTraceSound_of_sound_matchers
    {trace : List (String × Metta.Atom)} {left right out : Bindings}
    (hmerge : MergeRel left right out)
    (hmatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace)
    (hlistMatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchListRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace) :
    MergeTraceSound trace hmerge := by
  apply MergeRel.rec
    (motive_1 := fun _ _ _ _ h => AddVarBindingTraceSound trace h)
    (motive_2 := fun _ _ _ _ h => AddVarEqualityTraceSound trace h)
    (motive_3 := fun _ _ _ h => MergeAssignsTraceSound trace h)
    (motive_4 := fun _ _ _ h => MergeEqsTraceSound trace h)
    (motive_5 := fun _ _ _ h => MergeTraceSound trace h)
    (t := hmerge)
  · intro b key value hclass
    exact AddVarBindingTraceSound.fresh
      (value := value) (hclass := hclass)
  · intro b key value first rest hclass hconsistent hsame
    exact AddVarBindingTraceSound.same
      (hclass := hclass) (hconsistent := hconsistent) (hsame := hsame)
  · intro b key value first rest matched result hclass hconsistent
      hdifferent hmatch hrecursive ihrecursive
    exact AddVarBindingTraceSound.conflict
      (hclass := hclass) (hconsistent := hconsistent)
      (hdifferent := hdifferent) (hmatch := hmatch) (hmerge := hrecursive)
      (hmatcher hmatch) ihrecursive
  · intro b key value first rest matched result hclass hinconsistent
      hmatch hrecursive ihrecursive
    exact AddVarBindingTraceSound.reconcile
      (hclass := hclass) (hinconsistent := hinconsistent)
      (hmatch := hmatch) (hmerge := hrecursive)
      (hlistMatcher hmatch) ihrecursive
  · intro b first second hconsistent
    exact AddVarEqualityTraceSound.consistent
      (hconsistent := hconsistent)
  · intro b first second leftValue rightValue matched result hvalues
      hinconsistent hmatch hrecursive ihrecursive
    exact AddVarEqualityTraceSound.pairConflict
      (hvalues := hvalues) (hinconsistent := hinconsistent)
      (hmatch := hmatch) (hmerge := hrecursive)
      (hmatcher hmatch) ihrecursive
  · intro b first second leftValue rightValue thirdValue rest matched
      result hvalues hinconsistent hmatch hrecursive ihrecursive
    exact AddVarEqualityTraceSound.classConflict
      (hvalues := hvalues) (hinconsistent := hinconsistent)
      (hmatch := hmatch) (hmerge := hrecursive)
      (hlistMatcher hmatch) ihrecursive
  · intro b
    exact MergeAssignsTraceSound.nil
  · intro b key value rest next result hadd hrest ihadd ihrest
    exact MergeAssignsTraceSound.cons ihadd ihrest
  · intro b
    exact MergeEqsTraceSound.nil
  · intro b first second rest next result hadd hrest ihadd ihrest
    exact MergeEqsTraceSound.cons ihadd ihrest
  · intro mergeLeft mergeRight mid result hassignments hequalities
      ihassignments ihequalities
    exact MergeTraceSound.mk ihassignments ihequalities

theorem LeaEliminationTraceAssignmentsExact.assignmentList
    {b : Bindings} {trace : List (String × Metta.Atom)}
    (h : LeaEliminationTraceAssignmentsExact b trace) :
    LeaEliminationTraceAssignmentListExact b.assignments trace :=
  h

/-- Literal translated provenance is stronger than the settled
class-relative assignment invariant. -/
theorem LeaEliminationTraceAssignmentsExact.toSound
    {b : Bindings} {trace : List (String × Metta.Atom)}
    (h : LeaEliminationTraceAssignmentsExact b trace) :
    LeaEliminationTraceAssignmentsSound b trace := by
  intro key value hmem
  have hexact := h key value hmem
  have hnonvar : ∀ target, toLeaTTaAtom value ≠ .var target := by
    intro target heq
    cases value with
    | var name => simp [DeclMatchSpec.Atom.isVarB] at hexact
    | symbol name | grounded name | expression name => cases heq
  exact ⟨key, toLeaTTaAtom value, hexact.2, hnonvar,
    EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl,
    HELeaAtomClassRel.translation b value⟩

/-- Virtual binding state used while HE has processed the right operand's
assignments but has not yet folded its equality list.  Only equality closure
is virtualized; direct assignments are exactly the live accumulator's. -/
def withPendingEqualities
    (b : Bindings) (pending : List (String × String)) : Bindings :=
  { assignments := b.assignments
    equalities := b.equalities ++ pending }

@[simp] theorem withPendingEqualities_assignments
    (b : Bindings) (pending : List (String × String)) :
    (withPendingEqualities b pending).assignments = b.assignments :=
  rfl

@[simp] theorem withPendingEqualities_nil (b : Bindings) :
    withPendingEqualities b [] = b := by
  cases b
  simp [withPendingEqualities]

/-- A real fresh assignment commutes with virtual pending equalities because
`Bindings.assign` consults and changes only the assignment list. -/
theorem withPendingEqualities_assign
    (b : Bindings) (pending : List (String × String))
    (key : String) (value : Atom) :
    withPendingEqualities (b.assign key value) pending =
      (withPendingEqualities b pending).assign key value := by
  unfold withPendingEqualities Bindings.assign Bindings.isBound
  rfl

/-- One equality-fold step moves the head pending edge into the real
accumulator without changing the virtual binding state. -/
theorem withPendingEqualities_addEquality
    (b : Bindings) (pending : List (String × String))
    (left right : String) :
    withPendingEqualities (b.addEquality left right) pending =
      withPendingEqualities b ((left, right) :: pending) := by
  cases b
  simp [withPendingEqualities, Bindings.addEquality, List.append_assoc]

/-- Assignment provenance interpreted under equality edges that the runtime
will fold later.  At an empty pending list this is definitionally the settled
ordinary trace-soundness predicate. -/
def LeaEliminationTraceAssignmentsSoundUnder
    (b : Bindings) (pending : List (String × String))
    (trace : List (String × Metta.Atom)) : Prop :=
  LeaEliminationTraceAssignmentsSound
    (withPendingEqualities b pending) trace

@[simp] theorem eliminationTraceAssignmentsSoundUnder_nil
    (b : Bindings) (trace : List (String × Metta.Atom)) :
    LeaEliminationTraceAssignmentsSoundUnder b [] trace ↔
      LeaEliminationTraceAssignmentsSound b trace := by
  simp [LeaEliminationTraceAssignmentsSoundUnder]

/-- Equality closure of the live accumulator embeds into its virtual future
closure. -/
theorem eqClass_mono_withPendingEqualities
    (b : Bindings) (pending : List (String × String)) :
    ∀ {start finish}, finish ∈ b.eqClass start →
      finish ∈ (withPendingEqualities b pending).eqClass start := by
  intro start finish hclass
  rw [EqualityClosure.mem_eqClass_iff_reachable] at hclass ⊢
  apply hclass.mono
  intro left right hadj
  rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
  rcases hadj with ⟨hne, hforward | hreverse⟩
  · exact ⟨hne, Or.inl (List.mem_append_left _ hforward)⟩
  · exact ⟨hne, Or.inr (List.mem_append_left _ hreverse)⟩

/-- Any binding whose raw equality edges occur in the pending suffix embeds
into the corresponding virtual future closure. -/
theorem eqClass_mono_withPendingEqualities_of_edges
    {source base : Bindings} {pending : List (String × String)}
    (hedges : ∀ edge ∈ source.equalities, edge ∈ pending) :
    ∀ {start finish}, finish ∈ source.eqClass start →
      finish ∈ (withPendingEqualities base pending).eqClass start := by
  intro start finish hclass
  rw [EqualityClosure.mem_eqClass_iff_reachable] at hclass ⊢
  apply hclass.mono
  intro left right hadj
  rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
  rcases hadj with ⟨hne, hforward | hreverse⟩
  · exact ⟨hne, Or.inl
      (List.mem_append_right _ (hedges (left, right) hforward))⟩
  · exact ⟨hne, Or.inr
      (List.mem_append_right _ (hedges (right, left) hreverse))⟩

/-- Appending more future equality edges only enlarges the virtual closure. -/
theorem eqClass_mono_withPendingEqualities_append
    (b : Bindings) (first second : List (String × String)) :
    ∀ {start finish},
      finish ∈ (withPendingEqualities b second).eqClass start →
        finish ∈
          (withPendingEqualities b (first ++ second)).eqClass start := by
  intro start finish hclass
  rw [EqualityClosure.mem_eqClass_iff_reachable] at hclass ⊢
  apply hclass.mono
  intro left right hadj
  rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
  rcases hadj with ⟨hne, hforward | hreverse⟩
  · rcases List.mem_append.mp hforward with hbase | hsecond
    · exact ⟨hne, Or.inl (List.mem_append_left _ hbase)⟩
    · exact ⟨hne, Or.inl (List.mem_append_right _
        (List.mem_append_right _ hsecond))⟩
  · rcases List.mem_append.mp hreverse with hbase | hsecond
    · exact ⟨hne, Or.inr (List.mem_append_left _ hbase)⟩
    · exact ⟨hne, Or.inr (List.mem_append_right _
        (List.mem_append_right _ hsecond))⟩

/-- Trace assignment soundness is monotone when the target keeps no new raw
assignments and only enlarges equality classes. -/
theorem LeaEliminationTraceAssignmentsSound.mono
    {before after : Bindings} {trace : List (String × Metta.Atom)}
    (h : LeaEliminationTraceAssignmentsSound before trace)
    (hassignments : ∀ key value,
      (key, value) ∈ after.assignments →
        (key, value) ∈ before.assignments)
    (hclasses : ∀ {start finish},
      finish ∈ before.eqClass start →
        finish ∈ after.eqClass start) :
    LeaEliminationTraceAssignmentsSound after trace := by
  intro key value hmem
  obtain ⟨leaKey, leaValue, hentry, hnonvar, hclass, hatom⟩ :=
    h key value (hassignments key value hmem)
  exact ⟨leaKey, leaValue, hentry, hnonvar, hclasses hclass,
    HELeaAtomClassRel.mono hclasses hatom⟩

/-- Assignment provenance is monotone in the chosen Robinson trace: adding
more trace entries cannot invalidate an existing raw-value witness. -/
theorem LeaEliminationTraceAssignmentsSound.of_trace_subset
    {b : Bindings} {small large : List (String × Metta.Atom)}
    (h : LeaEliminationTraceAssignmentsSound b small)
    (hsubset : ∀ entry ∈ small, entry ∈ large) :
    LeaEliminationTraceAssignmentsSound b large := by
  intro key value hmem
  obtain ⟨leaKey, leaValue, hentry, hnonvar, hclass, hatom⟩ :=
    h key value hmem
  exact ⟨leaKey, leaValue, hsubset (leaKey, leaValue) hentry,
    hnonvar, hclass, hatom⟩

/-- General fresh-assignment step when the new value already has a
class-relative trace witness in the input closure. -/
theorem LeaEliminationTraceAssignmentsSound.assign_of_classRelative
    {b : Bindings} {trace : List (String × Metta.Atom)}
    (h : LeaEliminationTraceAssignmentsSound b trace)
    {key : String} {value : Atom} {leaKey : String}
    {leaValue : Metta.Atom}
    (hlookup : b.lookup key = none)
    (hentry : (leaKey, leaValue) ∈ trace)
    (hnonvar : ∀ target, leaValue ≠ .var target)
    (hclass : leaKey ∈ b.eqClass key)
    (hatom : HELeaAtomClassRel b value leaValue) :
    LeaEliminationTraceAssignmentsSound (b.assign key value) trace := by
  have hbound : b.isBound key = false := by
    simp [Bindings.isBound, hlookup]
  have hclassMono : ∀ {start finish},
      finish ∈ b.eqClass start →
        finish ∈ (b.assign key value).eqClass start := by
    intro start finish hstored
    simpa [Bindings.eqClass, Bindings.assign, hbound] using hstored
  intro outKey outValue hmem
  unfold Bindings.assign at hmem
  simp only [hbound, Bool.false_eq_true, if_false] at hmem
  rcases List.mem_append.mp hmem with hold | hnew
  · obtain ⟨storedKey, storedValue, hstored, hstoredNonvar,
        hstoredClass, hstoredAtom⟩ := h outKey outValue hold
    exact ⟨storedKey, storedValue, hstored, hstoredNonvar,
      hclassMono hstoredClass,
      HELeaAtomClassRel.mono hclassMono hstoredAtom⟩
  · simp only [List.mem_singleton, Prod.mk.injEq] at hnew
    rcases hnew with ⟨rfl, rfl⟩
    exact ⟨leaKey, leaValue, hentry, hnonvar,
      hclassMono hclass,
      HELeaAtomClassRel.mono hclassMono hatom⟩

/-- Insert one assignment into a live accumulator using a trace witness from
another binding whose equality graph is already included in the accumulator's
virtual future closure. -/
theorem LeaEliminationTraceAssignmentsSoundUnder.assign_of_source
    {b source : Bindings} {pending : List (String × String)}
    {trace : List (String × Metta.Atom)}
    (hcurrent : LeaEliminationTraceAssignmentsSoundUnder b pending trace)
    (hsource : LeaEliminationTraceAssignmentsSound source trace)
    (hsourceClasses : ∀ {start finish},
      finish ∈ source.eqClass start →
        finish ∈ (withPendingEqualities b pending).eqClass start)
    {key : String} {value : Atom}
    (hlookup : b.lookup key = none)
    (hvalue : (key, value) ∈ source.assignments) :
    LeaEliminationTraceAssignmentsSoundUnder
      (b.assign key value) pending trace := by
  obtain ⟨leaKey, leaValue, hentry, hnonvar, hclass, hatom⟩ :=
    hsource key value hvalue
  have hlookupFuture :
      (withPendingEqualities b pending).lookup key = none := by
    simpa [Bindings.lookup, withPendingEqualities] using hlookup
  have hfuture := hcurrent.assign_of_classRelative hlookupFuture
    hentry hnonvar (hsourceClasses hclass)
    (HELeaAtomClassRel.mono hsourceClasses hatom)
  unfold LeaEliminationTraceAssignmentsSoundUnder at hfuture ⊢
  rw [withPendingEqualities_assign]
  exact hfuture

/-- Adding more pending equality edges preserves the ambient trace invariant. -/
theorem LeaEliminationTraceAssignmentsSoundUnder.append
    {b : Bindings} {first second : List (String × String)}
    {trace : List (String × Metta.Atom)}
    (h : LeaEliminationTraceAssignmentsSoundUnder b second trace) :
    LeaEliminationTraceAssignmentsSoundUnder
      b (first ++ second) trace := by
  apply h.mono
  · intro key value hmem
    simpa [withPendingEqualities] using hmem
  · exact eqClass_mono_withPendingEqualities_append b first second

/-- Consuming the head pending equality into the live accumulator preserves
the virtual state exactly. -/
theorem LeaEliminationTraceAssignmentsSoundUnder.consume
    {b : Bindings} {pending : List (String × String)}
    {trace : List (String × Metta.Atom)} {left right : String}
    (h : LeaEliminationTraceAssignmentsSoundUnder
      b ((left, right) :: pending) trace) :
    LeaEliminationTraceAssignmentsSoundUnder
      (b.addEquality left right) pending trace := by
  unfold LeaEliminationTraceAssignmentsSoundUnder at h ⊢
  rw [withPendingEqualities_addEquality]
  exact h

/-- One order-free trace obligation is realized when an alias endpoint is
connected or a non-variable solve entry has a class-relative HE assignment
witness. -/
def LeaEliminationTraceEntryRealized
    (b : Bindings) (entry : String × Metta.Atom) : Prop :=
  match entry.2 with
  | .var target => target ∈ b.eqClass entry.1
  | leaValue =>
      ∃ key value,
        (key, value) ∈ b.assignments ∧
          entry.1 ∈ b.eqClass key ∧
            HELeaAtomClassRel b value leaValue

/-- Any non-variable LeaTTa value relation paired by the settled congruence
is already visible as the corresponding order-free HE trace observation. -/
theorem LeaBindingCongruence.traceEntryRealized_of_value
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaBindingCongruence b lb)
    {key : String} {value : Metta.Atom}
    (hvalue : Metta.BindingRel.val key value ∈ lb)
    (hnonvar : ∀ target, value ≠ .var target) :
    LeaEliminationTraceEntryRealized b (key, value) := by
  obtain ⟨heKey, heValue, hassignment, hclass, hatom⟩ :=
    h.classValues.2 key value hvalue
  cases value with
  | var target => exact (hnonvar target rfl).elim
  | sym symbol | gnd symbol | expr symbol =>
      exact ⟨heKey, heValue, hassignment, hclass, hatom⟩

/-- If every direct LeaTTa value in a congruent presentation occurs in a
chosen solve trace, then every direct HE assignment has exact class-relative
provenance in that trace. -/
theorem LeaBindingCongruence.assignmentsSound_of_valuesInTrace
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaBindingCongruence b lb)
    {trace : List (String × Metta.Atom)}
    (htrace : ∀ key value,
      Metta.BindingRel.val key value ∈ lb →
        (key, value) ∈ trace ∧
          ∀ target, value ≠ .var target) :
    LeaEliminationTraceAssignmentsSound b trace := by
  intro heKey heValue hassignment
  obtain ⟨key, value, hvalue, hclass, hatom⟩ :=
    h.classValues.1 heKey heValue hassignment
  exact ⟨key, value, (htrace key value hvalue).1,
    (htrace key value hvalue).2, hclass, hatom⟩

/-- The two HE observations used by trace realization grow monotonically:
direct assignments remain present and equality classes only gain reachable
members.  This is deliberately weaker than record or lookup equality. -/
structure HEBindingObservationExtension
    (before after : Bindings) : Prop where
  assignments : ∀ key value,
    (key, value) ∈ before.assignments →
      (key, value) ∈ after.assignments
  classes : ∀ {start finish},
    finish ∈ before.eqClass start →
      finish ∈ after.eqClass start

theorem HEBindingObservationExtension.refl (b : Bindings) :
    HEBindingObservationExtension b b :=
  ⟨fun _ _ h => h, fun h => h⟩

theorem HEBindingObservationExtension.trans
    {first second third : Bindings}
    (h₁₂ : HEBindingObservationExtension first second)
    (h₂₃ : HEBindingObservationExtension second third) :
    HEBindingObservationExtension first third :=
  ⟨fun key value hmem => h₂₃.assignments key value
      (h₁₂.assignments key value hmem),
    fun hmem => h₂₃.classes (h₁₂.classes hmem)⟩

/-- Assigning a genuinely fresh key extends both trace observations. -/
theorem HEBindingObservationExtension.assign_of_lookup_none
    (b : Bindings) (key : String) (value : Atom)
    (hlookup : b.lookup key = none) :
    HEBindingObservationExtension b (b.assign key value) := by
  have hbound : b.isBound key = false := by
    simp [Bindings.isBound, hlookup]
  constructor
  · intro oldKey oldValue hmem
    simp [Bindings.assign, hbound, hmem]
  · intro start finish hmem
    simpa [Bindings.eqClass, Bindings.assign, hbound] using hmem

/-- Adding an equality edge extends both trace observations. -/
theorem HEBindingObservationExtension.addEquality
    (b : Bindings) (left right : String) :
    HEBindingObservationExtension b (b.addEquality left right) := by
  constructor
  · intro key value hmem
    simpa [Bindings.addEquality] using hmem
  · exact eqClass_mono_addEquality b left right

/-- An empty class-value observation means that direct assignment of the
queried variable is fresh. -/
private theorem isBound_false_of_classValues_nil
    {b : Bindings} {key : String} (hclass : b.classValues key = []) :
    b.isBound key = false := by
  by_contra hboundFalse
  have hbound : b.isBound key = true := by simpa using hboundFalse
  rw [Bindings.isBound, Option.isSome_iff_exists] at hbound
  rcases hbound with ⟨value, hlookup⟩
  have hself : key ∈ b.eqClassOrdered key :=
    EqualityClosure.mem_eqClassOrdered_iff.mpr
      (EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl)
  have hvalue : value ∈ b.classValues key := by
    unfold Bindings.classValues
    exact List.mem_filterMap.mpr ⟨key, hself, hlookup⟩
  simp [hclass] at hvalue

/-- Extending a genuinely fresh key by one trace-certified non-variable value
preserves the assignment-sound half of the order-free trace invariant. -/
theorem LeaEliminationTraceAssignmentsSound.assign_of_lookup_none
    {b : Bindings} {trace : List (String × Metta.Atom)}
    (h : LeaEliminationTraceAssignmentsSound b trace)
    {key : String} {value : Atom} {leaValue : Metta.Atom}
    (hlookup : b.lookup key = none)
    (hatom : HELeaAtomClassRel b value leaValue)
    (hentry : (key, leaValue) ∈ trace)
    (hnonvar : ∀ target, leaValue ≠ .var target) :
    LeaEliminationTraceAssignmentsSound (b.assign key value) trace := by
  have hext :=
    HEBindingObservationExtension.assign_of_lookup_none b key value hlookup
  have hbound : b.isBound key = false := by
    simp [Bindings.isBound, hlookup]
  intro outKey outValue hmem
  unfold Bindings.assign at hmem
  simp only [hbound, Bool.false_eq_true, if_false] at hmem
  rcases List.mem_append.mp hmem with hold | hnew
  · obtain ⟨leaKey, stored, hstored, hstoredNonvar,
        hclass, hstoredAtom⟩ := h outKey outValue hold
    exact ⟨leaKey, stored, hstored, hstoredNonvar,
      hext.classes hclass,
      HELeaAtomClassRel.mono hext.classes hstoredAtom⟩
  · simp only [List.mem_singleton, Prod.mk.injEq] at hnew
    rcases hnew with ⟨rfl, rfl⟩
    exact ⟨outKey, leaValue, hentry, hnonvar,
      EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl,
      HELeaAtomClassRel.mono hext.classes hatom⟩

/-- Exact translated trace provenance is the seed-independent input needed
when the assignment fold inserts a fresh right-hand value into a live
accumulator. -/
theorem LeaEliminationTraceAssignmentsSound.assign_of_exact
    {b : Bindings} {trace : List (String × Metta.Atom)}
    (h : LeaEliminationTraceAssignmentsSound b trace)
    {key : String} {value : Atom}
    (hlookup : b.lookup key = none)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hentry : (key, toLeaTTaAtom value) ∈ trace) :
    LeaEliminationTraceAssignmentsSound (b.assign key value) trace := by
  apply h.assign_of_lookup_none hlookup
    (HELeaAtomClassRel.translation b value) hentry
  intro target heq
  cases value with
  | var name => simp [DeclMatchSpec.Atom.isVarB] at hnonvar
  | symbol name | grounded name | expression name => cases heq

/-- Adding an equality edge introduces no assignments and only enlarges the
classes used by existing class-relative provenance witnesses. -/
theorem LeaEliminationTraceAssignmentsSound.addEquality
    {b : Bindings} {trace : List (String × Metta.Atom)}
    (h : LeaEliminationTraceAssignmentsSound b trace)
    (left right : String) :
    LeaEliminationTraceAssignmentsSound
      (b.addEquality left right) trace := by
  have hext := HEBindingObservationExtension.addEquality b left right
  intro key value hmem
  have hold : (key, value) ∈ b.assignments := by
    simpa [Bindings.addEquality] using hmem
  obtain ⟨leaKey, leaValue, hentry, hnonvar, hclass, hatom⟩ :=
    h key value hold
  exact ⟨leaKey, leaValue, hentry, hnonvar,
    hext.classes hclass, HELeaAtomClassRel.mono hext.classes hatom⟩

/-- Every successful declarative HE merge preserves the left seed's
assignments and equality-class reachability, including through every recursive
conflict branch and both relation folds. -/
theorem mergeRel_observationExtension
    {left right out : Bindings} (h : MergeRel left right out) :
    HEBindingObservationExtension left out := by
  apply MergeRel.rec
    (motive_1 := fun b _ _ out _ =>
      HEBindingObservationExtension b out)
    (motive_2 := fun b _ _ out _ =>
      HEBindingObservationExtension b out)
    (motive_3 := fun b _ out _ =>
      HEBindingObservationExtension b out)
    (motive_4 := fun b _ out _ =>
      HEBindingObservationExtension b out)
    (motive_5 := fun b _ out _ =>
      HEBindingObservationExtension b out)
    (t := h)
  · intro b key value hclass
    have hbound := isBound_false_of_classValues_nil hclass
    constructor
    · intro oldKey oldValue hmem
      simp [Bindings.assign, hbound, hmem]
    · intro start finish hmem
      simpa [Bindings.eqClass, Bindings.assign, hbound] using hmem
  · intro b key value first rest hclass hconsistent hsame
    exact HEBindingObservationExtension.refl b
  · intro b key value first rest matched out hclass hconsistent
      hdifferent hmatch hmerge ihmerge
    exact ihmerge
  · intro b key value first rest matched out hclass hinconsistent
      hmatch hmerge ihmerge
    exact ihmerge
  · intro b left right hconsistent
    exact HEBindingObservationExtension.addEquality b left right
  · intro b left right first second matched out hvalues hinconsistent
      hmatch hmerge ihmerge
    exact (HEBindingObservationExtension.addEquality b left right).trans
      ihmerge
  · intro b left right first second third rest matched out hvalues
      hinconsistent hmatch hmerge ihmerge
    exact (HEBindingObservationExtension.addEquality b left right).trans
      ihmerge
  · intro b
    exact HEBindingObservationExtension.refl b
  · intro b key value rest next out hadd hrest ihadd ihrest
    exact ihadd.trans ihrest
  · intro b
    exact HEBindingObservationExtension.refl b
  · intro b left right rest next out hadd hrest ihadd ihrest
    exact ihadd.trans ihrest
  · intro left right mid out hassignments hequalities ihassignments
      ihequalities
    exact ihassignments.trans ihequalities

/-- The five-way HE merge fold preserves Robinson-trace assignment
provenance.  The right record contributes literal translated trace entries;
the only additional assignments that a conflict branch can introduce come
from its recursively invoked matcher, whose exact provenance is the sole
local hypothesis.  The output is deliberately weakened to class-relative
provenance because the live accumulator may add equality edges while folding.

This theorem closes the literal-provenance sublane completely.  The general
normalized-expression lane uses the right-closure theorem below to weaken its
matcher premise from literal to class-relative provenance. -/
theorem mergeRel_assignmentsSound_of_exact_matchers
    {trace : List (String × Metta.Atom)}
    {left right out : Bindings}
    (hmerge : MergeRel left right out)
    (hleft : LeaEliminationTraceAssignmentsSound left trace)
    (hright : LeaEliminationTraceAssignmentsExact right trace)
    (hmatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsExact matched trace)
    (hlistMatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchListRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsExact matched trace) :
    LeaEliminationTraceAssignmentsSound out trace := by
  let AddValueMotive := fun
      (b : Bindings) (_key : String) (_value : Atom) (result : Bindings)
      (_ : AddVarBindingRel b _key _value result) =>
    LeaEliminationTraceAssignmentsSound b trace →
      (DeclMatchSpec.Atom.isVarB _value = false ∧
        (_key, toLeaTTaAtom _value) ∈ trace) →
      LeaEliminationTraceAssignmentsSound result trace
  let AddEqualityMotive := fun
      (b : Bindings) (_left _right : String) (result : Bindings)
      (_ : AddVarEqualityRel b _left _right result) =>
    LeaEliminationTraceAssignmentsSound b trace →
      LeaEliminationTraceAssignmentsSound result trace
  let AssignFoldMotive := fun
      (b : Bindings) (assignments : List (String × Atom))
      (result : Bindings) (_ : MergeAssignsRel b assignments result) =>
    LeaEliminationTraceAssignmentsSound b trace →
      LeaEliminationTraceAssignmentListExact assignments trace →
      LeaEliminationTraceAssignmentsSound result trace
  let EqualityFoldMotive := fun
      (b : Bindings) (_equalities : List (String × String))
      (result : Bindings) (_ : MergeEqsRel b _equalities result) =>
    LeaEliminationTraceAssignmentsSound b trace →
      LeaEliminationTraceAssignmentsSound result trace
  let MergeMotive := fun
      (mergeLeft mergeRight result : Bindings)
      (_ : MergeRel mergeLeft mergeRight result) =>
    LeaEliminationTraceAssignmentsSound mergeLeft trace →
      LeaEliminationTraceAssignmentsExact mergeRight trace →
      LeaEliminationTraceAssignmentsSound result trace
  revert hleft hright
  apply MergeRel.rec
    (motive_1 := AddValueMotive)
    (motive_2 := AddEqualityMotive)
    (motive_3 := AssignFoldMotive)
    (motive_4 := EqualityFoldMotive)
    (motive_5 := MergeMotive)
    (t := hmerge)
  · intro b key value hclass hsound hexact
    have hbound : b.isBound key = false :=
      isBound_false_of_classValues_nil hclass
    have hlookup : b.lookup key = none := by
      cases hlookup : b.lookup key with
      | none => rfl
      | some stored =>
          simp [Bindings.isBound, hlookup] at hbound
    exact hsound.assign_of_exact hlookup hexact.1 hexact.2
  · intro b key value first rest hclass hconsistent hsame
      hsound _hexact
    exact hsound
  · intro b key value first rest matched result hclass hconsistent
      hdifferent hmatch hrecursive ihrecursive hsound _hexact
    exact ihrecursive hsound (hmatcher hmatch)
  · intro b key value first rest matched result hclass hinconsistent
      hmatch hrecursive ihrecursive hsound _hexact
    exact ihrecursive hsound (hlistMatcher hmatch)
  · intro b first second hconsistent hsound
    exact hsound.addEquality first second
  · intro b first second leftValue rightValue matched result hvalues
      hinconsistent hmatch hrecursive ihrecursive hsound
    exact ihrecursive (hsound.addEquality first second) (hmatcher hmatch)
  · intro b first second leftValue rightValue thirdValue rest matched
      result hvalues hinconsistent hmatch hrecursive ihrecursive hsound
    exact ihrecursive (hsound.addEquality first second)
      (hlistMatcher hmatch)
  · intro b hsound _hexact
    exact hsound
  · intro b key value rest next result hadd hrest ihadd ihrest
      hsound hexact
    have hhead : DeclMatchSpec.Atom.isVarB value = false ∧
        (key, toLeaTTaAtom value) ∈ trace :=
      hexact key value (by simp)
    have htail : LeaEliminationTraceAssignmentListExact rest trace := by
      intro tailKey tailValue hmem
      exact hexact tailKey tailValue (by simp [hmem])
    exact ihrest (ihadd hsound hhead) htail
  · intro b hsound
    exact hsound
  · intro b first second rest next result hadd hrest ihadd ihrest
      hsound
    exact ihrest (ihadd hsound)
  · intro mergeLeft mergeRight mid result hassignments hequalities
      ihassignments ihequalities hleftSound hrightExact
    exact ihequalities
      (ihassignments hleftSound hrightExact.assignmentList)

/-- Executable form of the trace-provenance merge theorem. -/
theorem mergeBindings_assignmentsSound_of_exact_matchers
    {trace : List (String × Metta.Atom)}
    {left right out : Bindings} {fuel : Nat}
    (hmerge : out ∈ mergeBindings left right fuel)
    (hleft : LeaEliminationTraceAssignmentsSound left trace)
    (hright : LeaEliminationTraceAssignmentsExact right trace)
    (hmatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsExact matched trace)
    (hlistMatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchListRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsExact matched trace) :
    LeaEliminationTraceAssignmentsSound out trace :=
  mergeRel_assignmentsSound_of_exact_matchers
    (mergeBindings_sound hmerge) hleft hright hmatcher hlistMatcher

/-- General live-merge provenance driven by the concrete merge derivation's
local recursive-matcher certificate.  Unlike the convenience theorem below,
this theorem makes no assertion about matcher calls that do not occur inside
`hmerge`; it is the interface constructed by the well-founded Robinson
induction. -/
theorem mergeRel_assignmentsSoundUnder_of_traceSound
    {trace : List (String × Metta.Atom)}
    {left right out : Bindings} {hmerge : MergeRel left right out}
    (htraceSound : MergeTraceSound trace hmerge) :
    ∀ (pending : List (String × String)),
      LeaEliminationTraceAssignmentsSoundUnder left
          (right.equalities ++ pending) trace →
        LeaEliminationTraceAssignmentsSound right trace →
          LeaEliminationTraceAssignmentsSoundUnder out pending trace := by
  let AddValueMotive := fun
      {b : Bindings} {key : String} {value : Atom} {result : Bindings}
      (_hrel : AddVarBindingRel b key value result)
      (_hcert : AddVarBindingTraceSound trace _hrel) =>
    ∀ (pending : List (String × String)) (source : Bindings),
      LeaEliminationTraceAssignmentsSoundUnder b pending trace →
        LeaEliminationTraceAssignmentsSound source trace →
          (∀ edge ∈ source.equalities, edge ∈ pending) →
            (key, value) ∈ source.assignments →
              LeaEliminationTraceAssignmentsSoundUnder
                result pending trace
  let AddEqualityMotive := fun
      {b : Bindings} {first second : String} {result : Bindings}
      (_hrel : AddVarEqualityRel b first second result)
      (_hcert : AddVarEqualityTraceSound trace _hrel) =>
    ∀ pending : List (String × String),
      LeaEliminationTraceAssignmentsSoundUnder
          b ((first, second) :: pending) trace →
        LeaEliminationTraceAssignmentsSoundUnder result pending trace
  let AssignFoldMotive := fun
      {b : Bindings} {assignments : List (String × Atom)}
      {result : Bindings} (_hrel : MergeAssignsRel b assignments result)
      (_hcert : MergeAssignsTraceSound trace _hrel) =>
    ∀ (pending : List (String × String)) (source : Bindings),
      LeaEliminationTraceAssignmentsSoundUnder b pending trace →
        LeaEliminationTraceAssignmentsSound source trace →
          (∀ edge ∈ source.equalities, edge ∈ pending) →
            (∀ key value, (key, value) ∈ assignments →
              (key, value) ∈ source.assignments) →
              LeaEliminationTraceAssignmentsSoundUnder
                result pending trace
  let EqualityFoldMotive := fun
      {b : Bindings} {equalities : List (String × String)}
      {result : Bindings} (_hrel : MergeEqsRel b equalities result)
      (_hcert : MergeEqsTraceSound trace _hrel) =>
    ∀ pending : List (String × String),
      LeaEliminationTraceAssignmentsSoundUnder
          b (equalities ++ pending) trace →
        LeaEliminationTraceAssignmentsSoundUnder result pending trace
  let MergeMotive := fun
      {mergeLeft mergeRight result : Bindings}
      (_hrel : MergeRel mergeLeft mergeRight result)
      (_hcert : MergeTraceSound trace _hrel) =>
    ∀ pending : List (String × String),
      LeaEliminationTraceAssignmentsSoundUnder mergeLeft
          (mergeRight.equalities ++ pending) trace →
        LeaEliminationTraceAssignmentsSound mergeRight trace →
          LeaEliminationTraceAssignmentsSoundUnder result pending trace
  apply MergeTraceSound.rec
    (motive_1 := AddValueMotive)
    (motive_2 := AddEqualityMotive)
    (motive_3 := AssignFoldMotive)
    (motive_4 := EqualityFoldMotive)
    (motive_5 := MergeMotive)
    (t := htraceSound)
  · intro b key value hclass pending source hcurrent hsource
      hedges hvalue
    have hbound : b.isBound key = false :=
      isBound_false_of_classValues_nil hclass
    have hlookup : b.lookup key = none := by
      cases hlookup : b.lookup key with
      | none => rfl
      | some stored =>
          simp [Bindings.isBound, hlookup] at hbound
    exact hcurrent.assign_of_source hsource
      (eqClass_mono_withPendingEqualities_of_edges hedges)
      hlookup hvalue
  · intro b key value first rest hclass hconsistent hsame
      pending source hcurrent _hsource _hedges _hvalue
    exact hcurrent
  · intro b key value first rest matched result hclass hconsistent
      hdifferent hmatch hrecursive hmatched hcert ihrecursive
      pending source hcurrent _hsource _hedges _hvalue
    exact ihrecursive pending
      (hcurrent.append (first := matched.equalities)) hmatched
  · intro b key value first rest matched result hclass hinconsistent
      hmatch hrecursive hmatched hcert ihrecursive pending source hcurrent
      _hsource _hedges _hvalue
    exact ihrecursive pending
      (hcurrent.append (first := matched.equalities)) hmatched
  · intro b first second hconsistent pending hcurrent
    exact hcurrent.consume
  · intro b first second leftValue rightValue matched result hvalues
      hinconsistent hmatch hrecursive hmatched hcert ihrecursive pending
      hcurrent
    have hcand : LeaEliminationTraceAssignmentsSoundUnder
        (b.addEquality first second) pending trace :=
      hcurrent.consume
    exact ihrecursive pending
      (hcand.append (first := matched.equalities)) hmatched
  · intro b first second leftValue rightValue thirdValue rest matched
      result hvalues hinconsistent hmatch hrecursive hmatched hcert
      ihrecursive pending hcurrent
    have hcand : LeaEliminationTraceAssignmentsSoundUnder
        (b.addEquality first second) pending trace :=
      hcurrent.consume
    exact ihrecursive pending
      (hcand.append (first := matched.equalities)) hmatched
  · intro b pending source hcurrent _hsource _hedges _hassignments
    exact hcurrent
  · intro b key value rest next result hadd hrest haddCert hrestCert
      ihadd ihrest pending source hcurrent hsource hedges hassignments
    have hnext := ihadd pending source hcurrent hsource hedges
      (hassignments key value (by simp))
    apply ihrest pending source hnext hsource hedges
    intro tailKey tailValue hmem
    exact hassignments tailKey tailValue (by simp [hmem])
  · intro b pending hcurrent
    simpa using hcurrent
  · intro b first second rest next result hadd hrest haddCert hrestCert
      ihadd ihrest pending hcurrent
    have hnext := ihadd (rest ++ pending) (by
      simpa only [List.cons_append] using hcurrent)
    exact ihrest pending hnext
  · intro mergeLeft mergeRight mid result hassignments hequalities
      hassignmentsCert hequalitiesCert ihassignments ihequalities pending
      hleftSound hrightSound
    have hmid := ihassignments
      (mergeRight.equalities ++ pending) mergeRight hleftSound
      hrightSound
      (by
        intro edge hedge
        exact List.mem_append_left pending hedge)
      (by
        intro key value hmem
        exact hmem)
    exact ihequalities pending hmid

/-- At an empty future-equality boundary, a derivation-local recursive
matcher certificate is sufficient for ordinary class-relative assignment
provenance. -/
theorem mergeRel_assignmentsSound_of_traceSound
    {trace : List (String × Metta.Atom)}
    {left right out : Bindings} {hmerge : MergeRel left right out}
    (htraceSound : MergeTraceSound trace hmerge)
    (hleft : LeaEliminationTraceAssignmentsSound left trace)
    (hright : LeaEliminationTraceAssignmentsSound right trace) :
    LeaEliminationTraceAssignmentsSound out trace := by
  have hleftFuture : LeaEliminationTraceAssignmentsSoundUnder
      left right.equalities trace := by
    apply hleft.mono
    · intro key value hmem
      simpa [withPendingEqualities] using hmem
    · exact eqClass_mono_withPendingEqualities left right.equalities
  have hleftFuture' : LeaEliminationTraceAssignmentsSoundUnder
      left (right.equalities ++ []) trace := by
    simpa only [List.append_nil] using hleftFuture
  have hout := mergeRel_assignmentsSoundUnder_of_traceSound
    htraceSound [] hleftFuture' hright
  simpa using hout

/-- General live-merge provenance theorem under virtual future equalities.
The assignment fold retains the complete right equality list in `pending`;
the equality fold consumes it one edge at a time.  Recursive conflict merges
temporarily prepend their matcher result's equality list.  Thus normalized
class-relative matcher provenance is available exactly when needed, without
pretending that not-yet-folded edges already occur in the runtime record. -/
theorem mergeRel_assignmentsSoundUnder_of_sound_matchers
    {trace : List (String × Metta.Atom)}
    {left right out : Bindings}
    (hmerge : MergeRel left right out)
    (hmatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace)
    (hlistMatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchListRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace) :
    ∀ (pending : List (String × String)),
      LeaEliminationTraceAssignmentsSoundUnder left
          (right.equalities ++ pending) trace →
        LeaEliminationTraceAssignmentsSound right trace →
          LeaEliminationTraceAssignmentsSoundUnder out pending trace := by
  let AddValueMotive := fun
      (b : Bindings) (key : String) (value : Atom) (result : Bindings)
      (_ : AddVarBindingRel b key value result) =>
    ∀ (pending : List (String × String)) (source : Bindings),
      LeaEliminationTraceAssignmentsSoundUnder b pending trace →
        LeaEliminationTraceAssignmentsSound source trace →
          (∀ edge ∈ source.equalities, edge ∈ pending) →
            (key, value) ∈ source.assignments →
              LeaEliminationTraceAssignmentsSoundUnder
                result pending trace
  let AddEqualityMotive := fun
      (b : Bindings) (first second : String) (result : Bindings)
      (_ : AddVarEqualityRel b first second result) =>
    ∀ pending : List (String × String),
      LeaEliminationTraceAssignmentsSoundUnder
          b ((first, second) :: pending) trace →
        LeaEliminationTraceAssignmentsSoundUnder result pending trace
  let AssignFoldMotive := fun
      (b : Bindings) (assignments : List (String × Atom))
      (result : Bindings) (_ : MergeAssignsRel b assignments result) =>
    ∀ (pending : List (String × String)) (source : Bindings),
      LeaEliminationTraceAssignmentsSoundUnder b pending trace →
        LeaEliminationTraceAssignmentsSound source trace →
          (∀ edge ∈ source.equalities, edge ∈ pending) →
            (∀ key value, (key, value) ∈ assignments →
              (key, value) ∈ source.assignments) →
              LeaEliminationTraceAssignmentsSoundUnder
                result pending trace
  let EqualityFoldMotive := fun
      (b : Bindings) (equalities : List (String × String))
      (result : Bindings) (_ : MergeEqsRel b equalities result) =>
    ∀ pending : List (String × String),
      LeaEliminationTraceAssignmentsSoundUnder
          b (equalities ++ pending) trace →
        LeaEliminationTraceAssignmentsSoundUnder result pending trace
  let MergeMotive := fun
      (mergeLeft mergeRight result : Bindings)
      (_ : MergeRel mergeLeft mergeRight result) =>
    ∀ pending : List (String × String),
      LeaEliminationTraceAssignmentsSoundUnder mergeLeft
          (mergeRight.equalities ++ pending) trace →
        LeaEliminationTraceAssignmentsSound mergeRight trace →
          LeaEliminationTraceAssignmentsSoundUnder result pending trace
  apply MergeRel.rec
    (motive_1 := AddValueMotive)
    (motive_2 := AddEqualityMotive)
    (motive_3 := AssignFoldMotive)
    (motive_4 := EqualityFoldMotive)
    (motive_5 := MergeMotive)
    (t := hmerge)
  · intro b key value hclass pending source hcurrent hsource
      hedges hvalue
    have hbound : b.isBound key = false :=
      isBound_false_of_classValues_nil hclass
    have hlookup : b.lookup key = none := by
      cases hlookup : b.lookup key with
      | none => rfl
      | some stored =>
          simp [Bindings.isBound, hlookup] at hbound
    exact hcurrent.assign_of_source hsource
      (eqClass_mono_withPendingEqualities_of_edges hedges)
      hlookup hvalue
  · intro b key value first rest hclass hconsistent hsame
      pending source hcurrent _hsource _hedges _hvalue
    exact hcurrent
  · intro b key value first rest matched result hclass hconsistent
      hdifferent hmatch hrecursive ihrecursive pending source hcurrent
      _hsource _hedges _hvalue
    exact ihrecursive pending
      (hcurrent.append (first := matched.equalities))
      (hmatcher hmatch)
  · intro b key value first rest matched result hclass hinconsistent
      hmatch hrecursive ihrecursive pending source hcurrent
      _hsource _hedges _hvalue
    exact ihrecursive pending
      (hcurrent.append (first := matched.equalities))
      (hlistMatcher hmatch)
  · intro b first second hconsistent pending hcurrent
    exact hcurrent.consume
  · intro b first second leftValue rightValue matched result hvalues
      hinconsistent hmatch hrecursive ihrecursive pending hcurrent
    have hcand : LeaEliminationTraceAssignmentsSoundUnder
        (b.addEquality first second) pending trace :=
      hcurrent.consume
    exact ihrecursive pending
      (hcand.append (first := matched.equalities))
      (hmatcher hmatch)
  · intro b first second leftValue rightValue thirdValue rest matched
      result hvalues hinconsistent hmatch hrecursive ihrecursive pending
      hcurrent
    have hcand : LeaEliminationTraceAssignmentsSoundUnder
        (b.addEquality first second) pending trace :=
      hcurrent.consume
    exact ihrecursive pending
      (hcand.append (first := matched.equalities))
      (hlistMatcher hmatch)
  · intro b pending source hcurrent _hsource _hedges _hassignments
    exact hcurrent
  · intro b key value rest next result hadd hrest ihadd ihrest
      pending source hcurrent hsource hedges hassignments
    have hnext := ihadd pending source hcurrent hsource hedges
      (hassignments key value (by simp))
    apply ihrest pending source hnext hsource hedges
    intro tailKey tailValue hmem
    exact hassignments tailKey tailValue (by simp [hmem])
  · intro b pending hcurrent
    simpa using hcurrent
  · intro b first second rest next result hadd hrest ihadd ihrest
      pending hcurrent
    have hnext := ihadd (rest ++ pending) (by
      simpa only [List.cons_append] using hcurrent)
    exact ihrest pending hnext
  · intro mergeLeft mergeRight mid result hassignments hequalities
      ihassignments ihequalities pending hleftSound hrightSound
    have hmid := ihassignments
      (mergeRight.equalities ++ pending) mergeRight hleftSound
      hrightSound
      (by
        intro edge hedge
        exact List.mem_append_left pending hedge)
      (by
        intro key value hmem
        exact hmem)
    exact ihequalities pending hmid

/-- Ordinary class-relative assignment provenance is therefore preserved by
every successful HE merge of trace-sound matcher-origin records.  The future
equality index is internal and disappears at `pending = []`. -/
theorem mergeRel_assignmentsSound_of_sound_matchers
    {trace : List (String × Metta.Atom)}
    {left right out : Bindings}
    (hmerge : MergeRel left right out)
    (hleft : LeaEliminationTraceAssignmentsSound left trace)
    (hright : LeaEliminationTraceAssignmentsSound right trace)
    (hmatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace)
    (hlistMatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchListRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace) :
    LeaEliminationTraceAssignmentsSound out trace := by
  have hleftFuture : LeaEliminationTraceAssignmentsSoundUnder
      left right.equalities trace := by
    apply hleft.mono
    · intro key value hmem
      simpa [withPendingEqualities] using hmem
    · exact eqClass_mono_withPendingEqualities left right.equalities
  have hleftFuture' : LeaEliminationTraceAssignmentsSoundUnder
      left (right.equalities ++ []) trace := by
    simpa only [List.append_nil] using hleftFuture
  have hout := mergeRel_assignmentsSoundUnder_of_sound_matchers
    hmerge hmatcher hlistMatcher [] hleftFuture' hright
  simpa using hout

/-- Executable class-relative provenance preservation. -/
theorem mergeBindings_assignmentsSound_of_sound_matchers
    {trace : List (String × Metta.Atom)}
    {left right out : Bindings} {fuel : Nat}
    (hmerge : out ∈ mergeBindings left right fuel)
    (hleft : LeaEliminationTraceAssignmentsSound left trace)
    (hright : LeaEliminationTraceAssignmentsSound right trace)
    (hmatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace)
    (hlistMatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchListRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace) :
    LeaEliminationTraceAssignmentsSound out trace :=
  mergeRel_assignmentsSound_of_sound_matchers
    (mergeBindings_sound hmerge) hleft hright hmatcher hlistMatcher

/-- A concrete merge carrying the derivation-local recursive matcher
certificate cannot destroy an already complete Robinson trace certificate.
This is the structural preservation theorem consumed directly by the paired
well-founded induction. -/
theorem mergeRel_eliminationTraceStructural_of_traceSound
    {trace : List (String × Metta.Atom)}
    {left right out : Bindings} {hmerge : MergeRel left right out}
    (htraceSound : MergeTraceSound trace hmerge)
    (hleft : LeaEliminationTraceStructuralRel left trace)
    (hright : LeaEliminationTraceAssignmentsSound right trace) :
    LeaEliminationTraceStructuralRel out trace := by
  have hext : HEBindingObservationExtension left out :=
    mergeRel_observationExtension hmerge
  have hsound : LeaEliminationTraceAssignmentsSound out trace :=
    mergeRel_assignmentsSound_of_traceSound htraceSound
      hleft.classValues.1 hright
  constructor
  · intro key target hentry
    exact hext.classes (hleft.aliases key target hentry)
  · constructor
    · exact hsound
    · intro leaKey leaValue hentry hnonvar
      obtain ⟨key, value, hvalue, hclass, hatom⟩ :=
        hleft.classValues.2 leaKey leaValue hentry hnonvar
      exact ⟨key, value, hext.assignments key value hvalue,
        hext.classes hclass, HELeaAtomClassRel.mono hext.classes hatom⟩

/-- Executable structural preservation with only the recursive matcher calls
inside this concrete merge certified trace-sound. -/
theorem mergeBindings_eliminationTraceStructural_of_traceSound
    {trace : List (String × Metta.Atom)}
    {left right out : Bindings} {fuel : Nat}
    (hmerge : out ∈ mergeBindings left right fuel)
    (htraceSound : MergeTraceSound trace (mergeBindings_sound hmerge))
    (hleft : LeaEliminationTraceStructuralRel left trace)
    (hright : LeaEliminationTraceAssignmentsSound right trace) :
    LeaEliminationTraceStructuralRel out trace :=
  mergeRel_eliminationTraceStructural_of_traceSound
    htraceSound hleft hright

/-- A successful trace-sound matcher merge cannot destroy an already
complete Robinson trace certificate.  The new provenance fold supplies the
soundness direction for assignments introduced by the right operand or by
recursive conflict matching; observation extension transports every alias
and every previously realized non-variable trace entry from the left.

This is deliberately one-sided in its operational input: the left record is
already structurally complete, while the right and recursive matcher records
need only be sound relative to the same trace. -/
theorem mergeRel_eliminationTraceStructural_of_sound_matchers
    {trace : List (String × Metta.Atom)}
    {left right out : Bindings}
    (hmerge : MergeRel left right out)
    (hleft : LeaEliminationTraceStructuralRel left trace)
    (hright : LeaEliminationTraceAssignmentsSound right trace)
    (hmatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace)
    (hlistMatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchListRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace) :
    LeaEliminationTraceStructuralRel out trace := by
  apply mergeRel_eliminationTraceStructural_of_traceSound
    (mergeTraceSound_of_sound_matchers hmerge hmatcher hlistMatcher)
      hleft hright

/-- Executable form of complete trace preservation through a successful
matcher-origin merge. -/
theorem mergeBindings_eliminationTraceStructural_of_sound_matchers
    {trace : List (String × Metta.Atom)}
    {left right out : Bindings} {fuel : Nat}
    (hmerge : out ∈ mergeBindings left right fuel)
    (hleft : LeaEliminationTraceStructuralRel left trace)
    (hright : LeaEliminationTraceAssignmentsSound right trace)
    (hmatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace)
    (hlistMatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchListRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace) :
    LeaEliminationTraceStructuralRel out trace :=
  mergeRel_eliminationTraceStructural_of_sound_matchers
    (mergeBindings_sound hmerge) hleft hright hmatcher hlistMatcher

/-- One successful value insertion is the singleton-assignment instance of
the merge observation theorem. -/
theorem addVarBindingRel_observationExtension
    {b out : Bindings} {key : String} {value : Atom}
    (h : AddVarBindingRel b key value out) :
    HEBindingObservationExtension b out :=
  mergeRel_observationExtension
    (right := ({ assignments := [(key, value)], equalities := [] } : Bindings))
    (.mk (.cons h .nil) .nil)

/-- One successful equality insertion is the singleton-equality instance of
the merge observation theorem. -/
theorem addVarEqualityRel_observationExtension
    {b out : Bindings} {left right : String}
    (h : AddVarEqualityRel b left right out) :
    HEBindingObservationExtension b out :=
  mergeRel_observationExtension
    (right := ({ assignments := [], equalities := [(left, right)] } : Bindings))
    (.mk .nil (.cons h .nil))

/-- Every successful equality insertion realizes the requested edge even
when its class values force recursive matcher/merge reconciliation. -/
theorem addVarEqualityRel_right_mem_eqClass
    {b out : Bindings} {left right : String}
    (h : AddVarEqualityRel b left right out) :
    right ∈ out.eqClass left := by
  have hcand : right ∈ (b.addEquality left right).eqClass left := by
    rw [EqualityClosure.mem_eqClass_iff_reachable]
    by_cases hsame : left = right
    · subst right
      exact .rfl
    · exact (show
          (EqualityClosure.edgeGraph
            (b.addEquality left right).equalities).Adj left right by
            rw [EqualityClosure.edgeGraph_adj_iff]
            exact ⟨hsame, Or.inl (by simp [Bindings.addEquality])⟩).reachable
  cases h with
  | consistent hconsistent => exact hcand
  | pairConflict hvalues hinconsistent hmatch hmerge =>
      exact (mergeRel_observationExtension hmerge).classes hcand
  | classConflict hvalues hinconsistent hmatch hmerge =>
      exact (mergeRel_observationExtension hmerge).classes hcand

/-- Every equality relation still pending in an equality fold is connected
in the final output.  Head edges are realized by the insertion constructor
and then transported through the suffix fold. -/
theorem mergeEqsRel_edge_mem_eqClass
    {b out : Bindings} {equalities : List (String × String)}
    (h : MergeEqsRel b equalities out) :
    ∀ edge ∈ equalities, edge.2 ∈ out.eqClass edge.1 := by
  let AddValueMotive := fun
      (_b : Bindings) (_key : String) (_value : Atom) (_out : Bindings)
      (_ : AddVarBindingRel _b _key _value _out) => True
  let AddEqualityMotive := fun
      (_b : Bindings) (_left _right : String) (_out : Bindings)
      (_ : AddVarEqualityRel _b _left _right _out) => True
  let AssignFoldMotive := fun
      (_b : Bindings) (_assignments : List (String × Atom))
      (_out : Bindings) (_ : MergeAssignsRel _b _assignments _out) => True
  let EqualityFoldMotive := fun
      (_b : Bindings) (edges : List (String × String))
      (result : Bindings) (_ : MergeEqsRel _b edges result) =>
    ∀ edge ∈ edges, edge.2 ∈ result.eqClass edge.1
  let MergeMotive := fun
      (_left _right _out : Bindings) (_ : MergeRel _left _right _out) =>
    True
  apply MergeEqsRel.rec
    (motive_1 := AddValueMotive)
    (motive_2 := AddEqualityMotive)
    (motive_3 := AssignFoldMotive)
    (motive_4 := EqualityFoldMotive)
    (motive_5 := MergeMotive)
    (t := h)
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro b edge hmem
    simp at hmem
  · intro b left right rest next out hadd hrest _ihadd ihrest
      edge hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with hhead | htail
    · subst edge
      have hnext : right ∈ next.eqClass left :=
        addVarEqualityRel_right_mem_eqClass hadd
      exact (mergeRel_observationExtension
        (MergeRel.mk
          (right := ({ assignments := [], equalities := rest } : Bindings))
          (MergeAssignsRel.nil (acc := next)) hrest)).classes
          hnext
    · exact ihrest edge htail
  · intros; trivial

/-- A successful full HE merge contains the complete equality closure of its
right operand.  This is stronger than merely replaying each raw edge: paths
in the right graph are mapped edge-by-edge to paths in the live output. -/
theorem mergeRel_right_eqClass_mono
    {left right out : Bindings} (h : MergeRel left right out) :
    ∀ {start finish}, finish ∈ right.eqClass start →
      finish ∈ out.eqClass start := by
  cases h with
  | @mk left right mid out hassignments hequalities =>
      intro start finish hclass
      rw [EqualityClosure.mem_eqClass_iff_reachable] at hclass ⊢
      apply hclass.elim
      intro walk
      induction walk with
      | nil => exact .rfl
      | @cons start next finish hadj tail ih =>
          rw [EqualityClosure.edgeGraph_adj_iff] at hadj
          have hstep :
              (EqualityClosure.edgeGraph out.equalities).Reachable
                start next := by
            rcases hadj.2 with hforward | hreverse
            · rw [← EqualityClosure.mem_eqClass_iff_reachable]
              exact mergeEqsRel_edge_mem_eqClass hequalities
                (start, next) hforward
            · have hconnected :=
                mergeEqsRel_edge_mem_eqClass hequalities
                  (next, start) hreverse
              rw [EqualityClosure.mem_eqClass_iff_reachable] at hconnected
              exact hconnected.symm
          exact hstep.trans (ih tail.reachable)

/-- Executable right-closure preservation. -/
theorem mergeBindings_right_eqClass_mono
    {left right out : Bindings} {fuel : Nat}
    (h : out ∈ mergeBindings left right fuel) :
    ∀ {start finish}, finish ∈ right.eqClass start →
      finish ∈ out.eqClass start :=
  mergeRel_right_eqClass_mono (mergeBindings_sound h)

/-! ### Equality-closure upper bounds

Assignment provenance controls raw values, while final binding congruence
also needs to rule out equality components not justified by the successful
reconciliation alias graph.  The following quotient-level predicate and
merge theorem supply that independent upper-bound lane.
-/

/-- Every HE equality-class connection is justified by reachability in one
allowed undirected alias graph.  This ignores edge orientation, multiplicity,
list order, and representative chronology. -/
def HEEqualityClosureBound
    (b : Bindings) (allowed : List (String × String)) : Prop :=
  ∀ start finish, finish ∈ b.eqClass start →
    (EqualityClosure.edgeGraph allowed).Reachable start finish

/-- It is enough to bound every raw equality edge; arbitrary class paths then
compose in the allowed graph. -/
theorem HEEqualityClosureBound.of_edges
    {b : Bindings} {allowed : List (String × String)}
    (hedges : ∀ edge ∈ b.equalities,
      (EqualityClosure.edgeGraph allowed).Reachable edge.1 edge.2) :
    HEEqualityClosureBound b allowed := by
  intro start finish hclass
  rw [EqualityClosure.mem_eqClass_iff_reachable] at hclass
  apply hclass.elim
  intro walk
  induction walk with
  | nil => exact .rfl
  | @cons start next finish hadj tail ih =>
      rw [EqualityClosure.edgeGraph_adj_iff] at hadj
      have hstep :
          (EqualityClosure.edgeGraph allowed).Reachable start next := by
        rcases hadj.2 with hforward | hreverse
        · exact hedges (start, next) hforward
        · exact (hedges (next, start) hreverse).symm
      exact hstep.trans (ih tail.reachable)

/-- A bounded equality record justifies each of its raw edges. -/
theorem HEEqualityClosureBound.edge
    {b : Bindings} {allowed : List (String × String)}
    (h : HEEqualityClosureBound b allowed)
    {left right : String} (hedge : (left, right) ∈ b.equalities) :
    (EqualityClosure.edgeGraph allowed).Reachable left right := by
  apply h left right
  rw [EqualityClosure.mem_eqClass_iff_reachable]
  by_cases heq : left = right
  · subst right
    exact .rfl
  · exact (show (EqualityClosure.edgeGraph b.equalities).Adj
        left right by
      rw [EqualityClosure.edgeGraph_adj_iff]
      exact ⟨heq, Or.inl hedge⟩).reachable

/-- An upper bound becomes exact equality-class agreement once every allowed
raw edge is known to survive in the HE output. -/
theorem HEEqualityClosureBound.eqClass_iff_of_edges
    {b : Bindings} {allowed : List (String × String)}
    (hbound : HEEqualityClosureBound b allowed)
    (hedges : ∀ edge ∈ allowed, edge.2 ∈ b.eqClass edge.1)
    (start finish : String) :
    finish ∈ b.eqClass start ↔
      (EqualityClosure.edgeGraph allowed).Reachable start finish := by
  constructor
  · exact hbound start finish
  · intro hreach
    rw [EqualityClosure.mem_eqClass_iff_reachable]
    apply hreach.elim
    intro walk
    induction walk with
    | nil => exact .rfl
    | @cons start next finish hadj tail ih =>
        rw [EqualityClosure.edgeGraph_adj_iff] at hadj
        have hstep :
            (EqualityClosure.edgeGraph b.equalities).Reachable start next := by
          rcases hadj.2 with hforward | hreverse
          · exact EqualityClosure.mem_eqClass_iff_reachable.mp
              (hedges (start, next) hforward)
          · exact (EqualityClosure.mem_eqClass_iff_reachable.mp
              (hedges (next, start) hreverse)).symm
        exact hstep.trans (ih tail.reachable)

/-- Empty HE bindings introduce no unlicensed equality component. -/
theorem HEEqualityClosureBound.empty
    (allowed : List (String × String)) :
    HEEqualityClosureBound Bindings.empty allowed := by
  apply HEEqualityClosureBound.of_edges
  intro edge hmem
  simp [Bindings.empty] at hmem

/-- Assigning a value does not change the equality graph. -/
theorem HEEqualityClosureBound.assign
    {b : Bindings} {allowed : List (String × String)}
    (h : HEEqualityClosureBound b allowed)
    (key : String) (value : Atom) :
    HEEqualityClosureBound (b.assign key value) allowed := by
  apply HEEqualityClosureBound.of_edges
  intro edge hmem
  apply h.edge
  simpa [Bindings.assign] using hmem

/-- Adding an equality preserves the upper bound exactly when the requested
connection is already reachable in the allowed graph. -/
theorem HEEqualityClosureBound.addEquality
    {b : Bindings} {allowed : List (String × String)}
    (h : HEEqualityClosureBound b allowed)
    {left right : String}
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right) :
    HEEqualityClosureBound (b.addEquality left right) allowed := by
  apply HEEqualityClosureBound.of_edges
  intro edge hmem
  rcases edge with ⟨edgeLeft, edgeRight⟩
  simp only [Bindings.addEquality, List.mem_append,
    List.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with hold | hnew
  · exact h.edge hold
  · rcases hnew with ⟨rfl, rfl⟩
    exact hallowed

/-- A complete declarative merge stays inside an allowed equality graph when
both inputs do and every recursive matcher result selected by this merge does.
The proof follows all five mutually recursive HE merge relations. -/
theorem mergeRel_equalityClosureBound_of_sound_matchers
    {allowed : List (String × String)}
    {left right out : Bindings}
    (hmerge : MergeRel left right out)
    (hleft : HEEqualityClosureBound left allowed)
    (hright : HEEqualityClosureBound right allowed)
    (hmatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchRel atomLeft atomRight matched →
        HEEqualityClosureBound matched allowed)
    (hlistMatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchListRel atomLeft atomRight matched →
        HEEqualityClosureBound matched allowed) :
    HEEqualityClosureBound out allowed := by
  apply MergeRel.rec
    (motive_1 := fun b _ _ result _ =>
      HEEqualityClosureBound b allowed →
        HEEqualityClosureBound result allowed)
    (motive_2 := fun b first second result _ =>
      (EqualityClosure.edgeGraph allowed).Reachable first second →
      HEEqualityClosureBound b allowed →
        HEEqualityClosureBound result allowed)
    (motive_3 := fun b _ result _ =>
      HEEqualityClosureBound b allowed →
        HEEqualityClosureBound result allowed)
    (motive_4 := fun b equalities result _ =>
      (∀ edge ∈ equalities,
        (EqualityClosure.edgeGraph allowed).Reachable edge.1 edge.2) →
      HEEqualityClosureBound b allowed →
        HEEqualityClosureBound result allowed)
    (motive_5 := fun mergeLeft mergeRight result _ =>
      HEEqualityClosureBound mergeLeft allowed →
      HEEqualityClosureBound mergeRight allowed →
        HEEqualityClosureBound result allowed)
    (t := hmerge)
  · intro b key value hclass hb
    exact hb.assign key value
  · intro b key value first rest hclass hconsistent hsame hb
    exact hb
  · intro b key value first rest matched result hclass hconsistent
      hdifferent hmatch hrecursive ihrecursive hb
    exact ihrecursive hb (hmatcher hmatch)
  · intro b key value first rest matched result hclass hinconsistent
      hmatch hrecursive ihrecursive hb
    exact ihrecursive hb (hlistMatcher hmatch)
  · intro b first second hconsistent hallowed hb
    exact hb.addEquality hallowed
  · intro b first second leftValue rightValue matched result hvalues
      hinconsistent hmatch hrecursive ihrecursive hallowed hb
    exact ihrecursive (hb.addEquality hallowed) (hmatcher hmatch)
  · intro b first second leftValue rightValue thirdValue rest matched
      result hvalues hinconsistent hmatch hrecursive ihrecursive hallowed hb
    exact ihrecursive (hb.addEquality hallowed) (hlistMatcher hmatch)
  · intro b hb
    exact hb
  · intro b key value rest next result hadd hrest ihadd ihrest hb
    exact ihrest (ihadd hb)
  · intro b hbounds hb
    exact hb
  · intro b first second rest next result hadd hrest ihadd ihrest
      hbounds hb
    have hhead := hbounds (first, second) (by simp)
    have htail : ∀ edge ∈ rest,
        (EqualityClosure.edgeGraph allowed).Reachable edge.1 edge.2 := by
      intro edge hmem
      exact hbounds edge (by simp [hmem])
    exact ihrest htail (ihadd hhead hb)
  · intro mergeLeft mergeRight mid result hassignments hequalities
      ihassignments ihequalities hmergeLeft hmergeRight
    apply ihequalities
    · intro edge hmem
      exact hmergeRight.edge hmem
    · exact ihassignments hmergeLeft
  · exact hleft
  · exact hright

/-- Executable wrapper for the equality-closure upper-bound theorem. -/
theorem mergeBindings_equalityClosureBound_of_sound_matchers
    {allowed : List (String × String)}
    {left right out : Bindings} {fuel : Nat}
    (hmerge : out ∈ mergeBindings left right fuel)
    (hleft : HEEqualityClosureBound left allowed)
    (hright : HEEqualityClosureBound right allowed)
    (hmatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchRel atomLeft atomRight matched →
        HEEqualityClosureBound matched allowed)
    (hlistMatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchListRel atomLeft atomRight matched →
        HEEqualityClosureBound matched allowed) :
    HEEqualityClosureBound out allowed :=
  mergeRel_equalityClosureBound_of_sound_matchers
    (mergeBindings_sound hmerge) hleft hright hmatcher hlistMatcher

mutual

/-- Derivation-local equality upper-bound certificate for one value
insertion.  Only matcher results actually selected by a recursive conflict
branch are required to stay in the allowed alias graph. -/
inductive AddVarBindingEqualityClosureBoundSound
    (allowed : List (String × String)) :
    ∀ {b key value out}, AddVarBindingRel b key value out → Prop where
  | fresh {b : Bindings} {key : String} {value : Atom}
      {hclass : b.classValues key = []} :
      AddVarBindingEqualityClosureBoundSound allowed
        (AddVarBindingRel.fresh (val := value) hclass)
  | same {b : Bindings} {key : String} {value first : Atom}
      {rest : List Atom}
      {hclass : b.classValues key = first :: rest}
      {hconsistent : Bindings.valuesConsistent (first :: rest) = true}
      {hsame : first = value} :
      AddVarBindingEqualityClosureBoundSound allowed
        (AddVarBindingRel.same hclass hconsistent hsame)
  | conflict {b : Bindings} {key : String} {value first : Atom}
      {rest : List Atom} {matched out : Bindings}
      {hclass : b.classValues key = first :: rest}
      {hconsistent : Bindings.valuesConsistent (first :: rest) = true}
      {hdifferent : first ≠ value}
      {hmatch : DeclMatchSpec.MatchRel first value matched}
      {hmerge : MergeRel b matched out} :
      HEEqualityClosureBound matched allowed →
      MergeEqualityClosureBoundSound allowed hmerge →
      AddVarBindingEqualityClosureBoundSound allowed
        (AddVarBindingRel.conflict hclass hconsistent hdifferent
          hmatch hmerge)
  | reconcile {b : Bindings} {key : String} {value first : Atom}
      {rest : List Atom} {matched out : Bindings}
      {hclass : b.classValues key = first :: rest}
      {hinconsistent : Bindings.valuesConsistent (first :: rest) = false}
      {hmatch : DeclMatchSpec.MatchListRel
        (List.replicate (rest.length + 1) first) (rest ++ [value]) matched}
      {hmerge : MergeRel b matched out} :
      HEEqualityClosureBound matched allowed →
      MergeEqualityClosureBoundSound allowed hmerge →
      AddVarBindingEqualityClosureBoundSound allowed
        (AddVarBindingRel.reconcile hclass hinconsistent hmatch hmerge)

/-- Derivation-local equality upper-bound certificate for one equality
insertion.  The requested edge itself and any recursive matcher result must
already be justified by the allowed graph. -/
inductive AddVarEqualityEqualityClosureBoundSound
    (allowed : List (String × String)) :
    ∀ {b left right out}, AddVarEqualityRel b left right out → Prop where
  | consistent {b : Bindings} {left right : String}
      {hconsistent : Bindings.valuesConsistent
        ((b.addEquality left right).classValues left) = true} :
      (EqualityClosure.edgeGraph allowed).Reachable left right →
      AddVarEqualityEqualityClosureBoundSound allowed
        (AddVarEqualityRel.consistent hconsistent)
  | pairConflict {b : Bindings} {left right : String}
      {first second : Atom} {matched out : Bindings}
      {hvalues : (b.addEquality left right).classValues left =
        [first, second]}
      {hinconsistent : Bindings.valuesConsistent [first, second] = false}
      {hmatch : DeclMatchSpec.MatchRel first second matched}
      {hmerge : MergeRel (b.addEquality left right) matched out} :
      (EqualityClosure.edgeGraph allowed).Reachable left right →
      HEEqualityClosureBound matched allowed →
      MergeEqualityClosureBoundSound allowed hmerge →
      AddVarEqualityEqualityClosureBoundSound allowed
        (AddVarEqualityRel.pairConflict hvalues hinconsistent
          hmatch hmerge)
  | classConflict {b : Bindings} {left right : String}
      {first second third : Atom} {rest : List Atom}
      {matched out : Bindings}
      {hvalues : (b.addEquality left right).classValues left =
        first :: second :: third :: rest}
      {hinconsistent : Bindings.valuesConsistent
        (first :: second :: third :: rest) = false}
      {hmatch : DeclMatchSpec.MatchListRel
        (List.replicate (rest.length + 2) first)
        (second :: third :: rest) matched}
      {hmerge : MergeRel (b.addEquality left right) matched out} :
      (EqualityClosure.edgeGraph allowed).Reachable left right →
      HEEqualityClosureBound matched allowed →
      MergeEqualityClosureBoundSound allowed hmerge →
      AddVarEqualityEqualityClosureBoundSound allowed
        (AddVarEqualityRel.classConflict hvalues hinconsistent
          hmatch hmerge)

/-- Equality upper-bound certificate for the assignment fold of one merge. -/
inductive MergeAssignsEqualityClosureBoundSound
    (allowed : List (String × String)) :
    ∀ {b assignments out}, MergeAssignsRel b assignments out → Prop where
  | nil {b : Bindings} :
      MergeAssignsEqualityClosureBoundSound allowed
        (MergeAssignsRel.nil (acc := b))
  | cons {b : Bindings} {key : String} {value : Atom}
      {rest : List (String × Atom)} {next out : Bindings}
      {hadd : AddVarBindingRel b key value next}
      {htail : MergeAssignsRel next rest out} :
      AddVarBindingEqualityClosureBoundSound allowed hadd →
      MergeAssignsEqualityClosureBoundSound allowed htail →
      MergeAssignsEqualityClosureBoundSound allowed
        (MergeAssignsRel.cons hadd htail)

/-- Equality upper-bound certificate for the equality fold of one merge. -/
inductive MergeEqsEqualityClosureBoundSound
    (allowed : List (String × String)) :
    ∀ {b equalities out}, MergeEqsRel b equalities out → Prop where
  | nil {b : Bindings} :
      MergeEqsEqualityClosureBoundSound allowed
        (MergeEqsRel.nil (acc := b))
  | cons {b : Bindings} {left right : String}
      {rest : List (String × String)} {next out : Bindings}
      {hadd : AddVarEqualityRel b left right next}
      {htail : MergeEqsRel next rest out} :
      AddVarEqualityEqualityClosureBoundSound allowed hadd →
      MergeEqsEqualityClosureBoundSound allowed htail →
      MergeEqsEqualityClosureBoundSound allowed
        (MergeEqsRel.cons hadd htail)

/-- Equality upper-bound certificate for one complete concrete HE merge. -/
inductive MergeEqualityClosureBoundSound
    (allowed : List (String × String)) :
    ∀ {left right out}, MergeRel left right out → Prop where
  | mk {left right mid out : Bindings}
      {hassignments : MergeAssignsRel left right.assignments mid}
      {hequalities : MergeEqsRel mid right.equalities out} :
      MergeAssignsEqualityClosureBoundSound allowed hassignments →
      MergeEqsEqualityClosureBoundSound allowed hequalities →
      MergeEqualityClosureBoundSound allowed
        (MergeRel.mk hassignments hequalities)

end

/-- A locally certified merge preserves the equality-closure upper bound
from its live left accumulator.  The certificate already accounts for every
right edge and every recursive matcher result selected by the derivation. -/
theorem MergeEqualityClosureBoundSound.preserves
    {allowed : List (String × String)}
    {left right out : Bindings} {hmerge : MergeRel left right out}
    (h : MergeEqualityClosureBoundSound allowed hmerge)
    (hleft : HEEqualityClosureBound left allowed) :
    HEEqualityClosureBound out allowed := by
  let AddValueMotive := fun
      {b : Bindings} {key : String} {value : Atom} {result : Bindings}
      (hrel : AddVarBindingRel b key value result)
      (_ : AddVarBindingEqualityClosureBoundSound allowed hrel) =>
    HEEqualityClosureBound b allowed →
      HEEqualityClosureBound result allowed
  let AddEqualityMotive := fun
      {b : Bindings} {first second : String} {result : Bindings}
      (hrel : AddVarEqualityRel b first second result)
      (_ : AddVarEqualityEqualityClosureBoundSound allowed hrel) =>
    HEEqualityClosureBound b allowed →
      HEEqualityClosureBound result allowed
  let AssignFoldMotive := fun
      {b : Bindings} {assignments : List (String × Atom)}
      {result : Bindings} (hrel : MergeAssignsRel b assignments result)
      (_ : MergeAssignsEqualityClosureBoundSound allowed hrel) =>
    HEEqualityClosureBound b allowed →
      HEEqualityClosureBound result allowed
  let EqualityFoldMotive := fun
      {b : Bindings} {equalities : List (String × String)}
      {result : Bindings} (hrel : MergeEqsRel b equalities result)
      (_ : MergeEqsEqualityClosureBoundSound allowed hrel) =>
    HEEqualityClosureBound b allowed →
      HEEqualityClosureBound result allowed
  let MergeMotive := fun
      {mergeLeft mergeRight result : Bindings}
      (hrel : MergeRel mergeLeft mergeRight result)
      (_ : MergeEqualityClosureBoundSound allowed hrel) =>
    HEEqualityClosureBound mergeLeft allowed →
      HEEqualityClosureBound result allowed
  apply MergeEqualityClosureBoundSound.rec
    (motive_1 := AddValueMotive)
    (motive_2 := AddEqualityMotive)
    (motive_3 := AssignFoldMotive)
    (motive_4 := EqualityFoldMotive)
    (motive_5 := MergeMotive)
    (t := h)
  · intro b key value hclass hb
    exact hb.assign key value
  · intro b key value first rest hclass hconsistent hsame hb
    exact hb
  · intro b key value first rest matched result hclass hconsistent
      hdifferent hmatch hrecursive _hmatched _hcert ihrecursive hb
    exact ihrecursive hb
  · intro b key value first rest matched result hclass hinconsistent
      hmatch hrecursive _hmatched _hcert ihrecursive hb
    exact ihrecursive hb
  · intro b first second hconsistent hallowed hb
    exact hb.addEquality hallowed
  · intro b first second leftValue rightValue matched result hvalues
      hinconsistent hmatch hrecursive hallowed _hmatched _hcert
      ihrecursive hb
    exact ihrecursive (hb.addEquality hallowed)
  · intro b first second leftValue rightValue thirdValue rest matched
      result hvalues hinconsistent hmatch hrecursive hallowed _hmatched
      _hcert ihrecursive hb
    exact ihrecursive (hb.addEquality hallowed)
  · intro b hb
    exact hb
  · intro b key value rest next result hadd hrest _haddCert
      _hrestCert ihadd ihrest hb
    exact ihrest (ihadd hb)
  · intro b hb
    exact hb
  · intro b first second rest next result hadd hrest _haddCert
      _hrestCert ihadd ihrest hb
    exact ihrest (ihadd hb)
  · intro mergeLeft mergeRight mid result hassignments hequalities
      _hassignmentsCert _hequalitiesCert ihassignments ihequalities hb
    exact ihequalities (ihassignments hb)
  · exact hleft

mutual

/-- Derivation-local equality upper-bound certificate for an original HE
atom matcher.  The only leaf that can create an equality edge is variable /
variable matching, whose connection must already be reachable in the allowed
reconciliation graph. -/
inductive MatchEqualityClosureBoundSound
    (allowed : List (String × String)) :
    ∀ {left right out}, DeclMatchSpec.MatchRel left right out → Prop where
  | symSym {name : String} :
      MatchEqualityClosureBoundSound allowed
        (DeclMatchSpec.MatchRel.symSym name)
  | varVar {left right : String} :
      (EqualityClosure.edgeGraph allowed).Reachable left right →
      MatchEqualityClosureBoundSound allowed
        (DeclMatchSpec.MatchRel.varVar left right)
  | varNonVar {key : String} {value : Atom}
      {hnonvar : DeclMatchSpec.Atom.isVarB value = false} :
      MatchEqualityClosureBoundSound allowed
        (DeclMatchSpec.MatchRel.varNonVar
          (v := key) (t := value) hnonvar)
  | nonVarVar {value : Atom} {key : String}
      {hnonvar : DeclMatchSpec.Atom.isVarB value = false} :
      MatchEqualityClosureBoundSound allowed
        (DeclMatchSpec.MatchRel.nonVarVar
          (s := value) (v := key) hnonvar)
  | grounded {value : OSLFCore.GroundedValue} :
      MatchEqualityClosureBoundSound allowed
        (DeclMatchSpec.MatchRel.grounded value)
  | expr {left right : List Atom} {out : Bindings}
      {hlist : DeclMatchSpec.MatchListAccRel
        left right Bindings.empty out} :
      MatchListEqualityClosureBoundSound allowed hlist →
      MatchEqualityClosureBoundSound allowed
        (DeclMatchSpec.MatchRel.expr hlist)

/-- Accumulator-threaded companion to the matcher equality certificate.  It
retains the exact locally certified merge chosen after every head match. -/
inductive MatchListEqualityClosureBoundSound
    (allowed : List (String × String)) :
    ∀ {left right seed out},
      DeclMatchSpec.MatchListAccRel left right seed out → Prop where
  | nil {seed : Bindings} :
      MatchListEqualityClosureBoundSound allowed
        (DeclMatchSpec.MatchListAccRel.nil (seed := seed))
  | cons {left right : Atom} {lefts rights : List Atom}
      {seed matched next out : Bindings} {fuel : Nat}
      {hmatch : DeclMatchSpec.MatchRel left right matched}
      {hmerge : next ∈ mergeBindings seed matched fuel}
      {htail : DeclMatchSpec.MatchListAccRel lefts rights next out} :
      MatchEqualityClosureBoundSound allowed hmatch →
      MergeEqualityClosureBoundSound allowed
        (mergeBindings_sound hmerge) →
      MatchListEqualityClosureBoundSound allowed htail →
      MatchListEqualityClosureBoundSound allowed
        (DeclMatchSpec.MatchListAccRel.cons hmatch hmerge htail)

end

/-- A certified original atom matcher introduces no equality connection
outside its allowed alias graph. -/
theorem MatchEqualityClosureBoundSound.bound
    {allowed : List (String × String)} {left right : Atom}
    {out : Bindings} {hmatch : DeclMatchSpec.MatchRel left right out}
    (h : MatchEqualityClosureBoundSound allowed hmatch) :
    HEEqualityClosureBound out allowed := by
  let AtomMotive := fun {left right : Atom} {out : Bindings}
      (hrel : DeclMatchSpec.MatchRel left right out)
      (_ : MatchEqualityClosureBoundSound allowed hrel) =>
    HEEqualityClosureBound out allowed
  let ListMotive := fun {left right : List Atom} {seed out : Bindings}
      (hrel : DeclMatchSpec.MatchListAccRel left right seed out)
      (_ : MatchListEqualityClosureBoundSound allowed hrel) =>
    HEEqualityClosureBound seed allowed →
      HEEqualityClosureBound out allowed
  exact MatchEqualityClosureBoundSound.rec
    (motive_1 := AtomMotive) (motive_2 := ListMotive)
    (by intro name; exact HEEqualityClosureBound.empty allowed)
    (by
      intro left right hallowed
      exact (HEEqualityClosureBound.empty allowed).addEquality hallowed)
    (by
      intro key value hnonvar
      exact (HEEqualityClosureBound.empty allowed).assign key value)
    (by
      intro value key hnonvar
      exact (HEEqualityClosureBound.empty allowed).assign key value)
    (by intro value; exact HEEqualityClosureBound.empty allowed)
    (by
      intro left right out hlist hlistSound ih
      exact ih (HEEqualityClosureBound.empty allowed))
    (by intro seed hseed; exact hseed)
    (by
      intro left right lefts rights seed matched next out fuel
        hhead hmerge htail hheadSound hmergeSound htailSound
        _ihHead ihTail hseed
      exact ihTail (hmergeSound.preserves hseed))
    (t := h)

/-- The pointwise matcher certificate preserves an already bounded live
accumulator through every certified head merge. -/
theorem MatchListEqualityClosureBoundSound.preserves
    {allowed : List (String × String)}
    {left right : List Atom} {seed out : Bindings}
    {hmatch : DeclMatchSpec.MatchListAccRel left right seed out}
    (h : MatchListEqualityClosureBoundSound allowed hmatch)
    (hseed : HEEqualityClosureBound seed allowed) :
    HEEqualityClosureBound out allowed := by
  let AtomMotive := fun {left right : Atom} {out : Bindings}
      (hrel : DeclMatchSpec.MatchRel left right out)
      (_ : MatchEqualityClosureBoundSound allowed hrel) =>
    HEEqualityClosureBound out allowed
  let ListMotive := fun {left right : List Atom} {seed out : Bindings}
      (hrel : DeclMatchSpec.MatchListAccRel left right seed out)
      (_ : MatchListEqualityClosureBoundSound allowed hrel) =>
    HEEqualityClosureBound seed allowed →
      HEEqualityClosureBound out allowed
  have hrec : ListMotive hmatch h :=
    MatchListEqualityClosureBoundSound.rec
      (motive_1 := AtomMotive) (motive_2 := ListMotive)
      (by intro name; exact HEEqualityClosureBound.empty allowed)
      (by
        intro left right hallowed
        exact (HEEqualityClosureBound.empty allowed).addEquality hallowed)
      (by
        intro key value hnonvar
        exact (HEEqualityClosureBound.empty allowed).assign key value)
      (by
        intro value key hnonvar
        exact (HEEqualityClosureBound.empty allowed).assign key value)
      (by intro value; exact HEEqualityClosureBound.empty allowed)
      (by
        intro left right out hlist hlistSound ih
        exact ih (HEEqualityClosureBound.empty allowed))
      (by intro seed hseed; exact hseed)
      (by
        intro left right lefts rights seed matched next out fuel
          hhead hmerge htail hheadSound hmergeSound htailSound
          _ihHead ihTail hseed
        exact ihTail (hmergeSound.preserves hseed))
      (t := h)
  exact hrec hseed

/-- Two equality-only records whose edges are all reflexive have a fully
certified merge.  This is the nonrecursive operational kernel used while the
original expression matcher replays a common prefix: no assignment is
introduced, every requested equality is reachable by reflexivity, and both
derivation-local certificates are constructed for the exact merge proof. -/
theorem exists_reflexiveEqualityOnly_mergeRel_certified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    {left right : Bindings}
    (hleftAssignments : left.assignments = [])
    (hleftEqualities : ∀ edge ∈ left.equalities, edge.1 = edge.2)
    (hrightAssignments : right.assignments = [])
    (hrightEqualities : ∀ edge ∈ right.equalities, edge.1 = edge.2) :
    ∃ out, ∃ hmerge : MergeRel left right out,
      out.assignments = [] ∧
        (∀ edge ∈ out.equalities, edge.1 = edge.2) ∧
        MergeTraceSound trace hmerge ∧
        MergeEqualityClosureBoundSound allowed hmerge := by
  have go : ∀ (edges : List (String × String)) (seed : Bindings),
      seed.assignments = [] →
      (∀ edge ∈ seed.equalities, edge.1 = edge.2) →
      (∀ edge ∈ edges, edge.1 = edge.2) →
      ∃ out, ∃ hequalities : MergeEqsRel seed edges out,
        out.assignments = [] ∧
          (∀ edge ∈ out.equalities, edge.1 = edge.2) ∧
          MergeEqsTraceSound trace hequalities ∧
          MergeEqsEqualityClosureBoundSound allowed hequalities := by
    intro edges
    induction edges with
    | nil =>
        intro seed hseedAssignments hseedEqualities _hedges
        exact ⟨seed, MergeEqsRel.nil, hseedAssignments,
          hseedEqualities, MergeEqsTraceSound.nil,
          MergeEqsEqualityClosureBoundSound.nil⟩
    | cons edge edges ih =>
        intro seed hseedAssignments hseedEqualities hedges
        rcases edge with ⟨leftKey, rightKey⟩
        have hkey : leftKey = rightKey :=
          hedges (leftKey, rightKey) (by simp)
        subst rightKey
        have hclass :
            (seed.addEquality leftKey leftKey).classValues leftKey = [] := by
          unfold Bindings.classValues Bindings.lookup
          simp [Bindings.addEquality, hseedAssignments]
        have hconsistent : Bindings.valuesConsistent
            ((seed.addEquality leftKey leftKey).classValues leftKey) = true := by
          simp [hclass, Bindings.valuesConsistent]
        let next := seed.addEquality leftKey leftKey
        let hadd : AddVarEqualityRel seed leftKey leftKey next :=
          AddVarEqualityRel.consistent hconsistent
        have hnextAssignments : next.assignments = [] := by
          simp [next, Bindings.addEquality, hseedAssignments]
        have hnextEqualities : ∀ stored ∈ next.equalities,
            stored.1 = stored.2 := by
          intro stored hstored
          simp only [next, Bindings.addEquality, List.mem_append,
            List.mem_singleton] at hstored
          rcases hstored with hold | hnew
          · exact hseedEqualities stored hold
          · subst stored
            rfl
        have hrestEqualities : ∀ stored ∈ edges,
            stored.1 = stored.2 := by
          intro stored hstored
          exact hedges stored (by simp [hstored])
        obtain ⟨out, htail, houtAssignments, houtEqualities,
            htailTrace, htailBound⟩ :=
          ih next hnextAssignments hnextEqualities hrestEqualities
        let hequalities : MergeEqsRel seed
            ((leftKey, leftKey) :: edges) out :=
          MergeEqsRel.cons hadd htail
        have hheadTrace : AddVarEqualityTraceSound trace hadd :=
          AddVarEqualityTraceSound.consistent
            (hconsistent := hconsistent)
        have hheadBound :
            AddVarEqualityEqualityClosureBoundSound allowed hadd :=
          AddVarEqualityEqualityClosureBoundSound.consistent
            (hconsistent := hconsistent) .rfl
        exact ⟨out, hequalities, houtAssignments, houtEqualities,
          MergeEqsTraceSound.cons hheadTrace htailTrace,
          MergeEqsEqualityClosureBoundSound.cons hheadBound htailBound⟩
  rcases right with ⟨rightAssignments, rightEqualities⟩
  change rightAssignments = [] at hrightAssignments
  subst rightAssignments
  let hassignments : MergeAssignsRel left [] left :=
    MergeAssignsRel.nil
  obtain ⟨out, hequalities, houtAssignments, houtEqualities,
      hequalitiesTrace, hequalitiesBound⟩ :=
    go rightEqualities left hleftAssignments hleftEqualities
      hrightEqualities
  let hmerge : MergeRel left ⟨[], rightEqualities⟩ out :=
    MergeRel.mk hassignments hequalities
  have hassignmentsTrace : MergeAssignsTraceSound trace hassignments := by
    exact MergeAssignsTraceSound.nil
  have hassignmentsBound :
      MergeAssignsEqualityClosureBoundSound allowed hassignments := by
    exact MergeAssignsEqualityClosureBoundSound.nil
  exact ⟨out, hmerge, houtAssignments, houtEqualities,
    MergeTraceSound.mk hassignmentsTrace hequalitiesTrace,
    MergeEqualityClosureBoundSound.mk
      hassignmentsBound hequalitiesBound⟩

/-- Certified original HE match of one atom against itself.  The output is
equality-only and every edge is reflexive; nested expressions retain the
actual pointwise matcher and merge derivations. -/
structure HEReflexiveMatchCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String)) (atom : Atom) where
  out : Bindings
  matchRel : DeclMatchSpec.MatchRel atom atom out
  traceSound : MatchTraceSound trace matchRel
  equalitySound : MatchEqualityClosureBoundSound allowed matchRel
  assignments_nil : out.assignments = []
  equalities_refl : ∀ edge ∈ out.equalities, edge.1 = edge.2

/-- Accumulator-threaded list companion to `HEReflexiveMatchCertified`.
The seed and output are both equality-only with reflexive edges. -/
structure HEReflexiveMatchListAccCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (atoms : List Atom) (seed : Bindings) where
  out : Bindings
  matchRel : DeclMatchSpec.MatchListAccRel atoms atoms seed out
  traceSound : MatchListTraceSound trace matchRel
  equalitySound : MatchListEqualityClosureBoundSound allowed matchRel
  assignments_nil : out.assignments = []
  equalities_refl : ∀ edge ∈ out.equalities, edge.1 = edge.2

mutual

/-- Every original HE atom has a traversal-faithful certified reflexive
match.  The simultaneous atom/list recursion compiles each list accumulator
merge through `exists_reflexiveEqualityOnly_mergeRel_certified`, so the result
is ready to prepend the common prefix returned by the strict divergence
theorem. -/
noncomputable def reflexiveMatchCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String)) (atom : Atom) :
    HEReflexiveMatchCertified trace allowed atom := by
  cases atom with
  | symbol symbol =>
      exact {
        out := Bindings.empty
        matchRel := DeclMatchSpec.MatchRel.symSym symbol
        traceSound := MatchTraceSound.symSym
        equalitySound := MatchEqualityClosureBoundSound.symSym
        assignments_nil := rfl
        equalities_refl := by intro edge hmem; simp [Bindings.empty] at hmem
      }
  | var name =>
      exact {
        out := ⟨[], [(name, name)]⟩
        matchRel := DeclMatchSpec.MatchRel.varVar name name
        traceSound := MatchTraceSound.varVar
        equalitySound := MatchEqualityClosureBoundSound.varVar .rfl
        assignments_nil := rfl
        equalities_refl := by
          intro edge hmem
          simp only [List.mem_singleton] at hmem
          subst edge
          rfl
      }
  | grounded ground =>
      exact {
        out := Bindings.empty
        matchRel := DeclMatchSpec.MatchRel.grounded ground
        traceSound := MatchTraceSound.grounded
        equalitySound := MatchEqualityClosureBoundSound.grounded
        assignments_nil := rfl
        equalities_refl := by intro edge hmem; simp [Bindings.empty] at hmem
      }
  | expression atoms =>
      let hlist := reflexiveMatchListAccCertified trace allowed atoms
        Bindings.empty (by rfl)
        (by intro edge hmem; simp [Bindings.empty] at hmem)
      exact {
        out := hlist.out
        matchRel := DeclMatchSpec.MatchRel.expr hlist.matchRel
        traceSound := MatchTraceSound.expr hlist.traceSound
        equalitySound :=
          MatchEqualityClosureBoundSound.expr hlist.equalitySound
        assignments_nil := hlist.assignments_nil
        equalities_refl := hlist.equalities_refl
      }
termination_by 2 * sizeOf atom

/-- Accumulator-threaded simultaneous companion to
`reflexiveMatchCertified`. -/
noncomputable def reflexiveMatchListAccCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String)) (atoms : List Atom)
    (seed : Bindings) (hseedAssignments : seed.assignments = [])
    (hseedEqualities : ∀ edge ∈ seed.equalities, edge.1 = edge.2) :
    HEReflexiveMatchListAccCertified trace allowed atoms seed := by
  cases atoms with
  | nil =>
      exact {
        out := seed
        matchRel := DeclMatchSpec.MatchListAccRel.nil
        traceSound := MatchListTraceSound.nil
        equalitySound := MatchListEqualityClosureBoundSound.nil
        assignments_nil := hseedAssignments
        equalities_refl := hseedEqualities
      }
  | cons head tail =>
      let hhead := reflexiveMatchCertified trace allowed head
      let hmergeExists :=
        exists_reflexiveEqualityOnly_mergeRel_certified trace allowed
          hseedAssignments hseedEqualities
          hhead.assignments_nil hhead.equalities_refl
      let next := Classical.choose hmergeExists
      let hmergeExists' := Classical.choose_spec hmergeExists
      let hmergeRel := Classical.choose hmergeExists'
      have hmergeProperties := Classical.choose_spec hmergeExists'
      have hnextAssignments : next.assignments = [] :=
        hmergeProperties.1
      have hnextEqualities : ∀ edge ∈ next.equalities,
          edge.1 = edge.2 := hmergeProperties.2.1
      have hmergeTrace : MergeTraceSound trace hmergeRel :=
        hmergeProperties.2.2.1
      have hmergeBound : MergeEqualityClosureBoundSound allowed hmergeRel :=
        hmergeProperties.2.2.2
      let hmergeMemExists := mergeBindings_complete hmergeRel
      let mergeFuel := Classical.choose hmergeMemExists
      have hmergeMem := Classical.choose_spec hmergeMemExists
      have hmergeTraceMem : MergeTraceSound trace
          (mergeBindings_sound hmergeMem) := by
        simpa only [Subsingleton.elim
          (mergeBindings_sound hmergeMem) hmergeRel] using hmergeTrace
      have hmergeBoundMem : MergeEqualityClosureBoundSound allowed
          (mergeBindings_sound hmergeMem) := by
        simpa only [Subsingleton.elim
          (mergeBindings_sound hmergeMem) hmergeRel] using hmergeBound
      let htail := reflexiveMatchListAccCertified trace allowed tail next
        hnextAssignments hnextEqualities
      let hlist : DeclMatchSpec.MatchListAccRel
          (head :: tail) (head :: tail) seed htail.out :=
        DeclMatchSpec.MatchListAccRel.cons
          hhead.matchRel hmergeMem htail.matchRel
      exact {
        out := htail.out
        matchRel := hlist
        traceSound := MatchListTraceSound.cons (hmerge := hmergeMem)
          hhead.traceSound hmergeTraceMem htail.traceSound
        equalitySound := MatchListEqualityClosureBoundSound.cons
          (hmerge := hmergeMem)
          hhead.equalitySound hmergeBoundMem htail.equalitySound
        assignments_nil := htail.assignments_nil
        equalities_refl := htail.equalities_refl
      }
termination_by 2 * sizeOf atoms + 1
decreasing_by all_goals simp_wf <;> omega

end

/-- Common-prefix specialization starting from empty bindings, exactly as the
original expression matcher does. -/
noncomputable def reflexiveMatchListCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String)) (atoms : List Atom) :
    HEReflexiveMatchListAccCertified
      trace allowed atoms Bindings.empty :=
  reflexiveMatchListAccCertified trace allowed atoms Bindings.empty
    rfl (by intro edge hmem; simp [Bindings.empty] at hmem)

/-- Executable value insertion preserves the seed observations on every
surviving branch. -/
theorem addVarBinding_observationExtension
    {b out : Bindings} {key : String} {value : Atom} {fuel : Nat}
    (h : out ∈ addVarBinding b key value fuel) :
    HEBindingObservationExtension b out :=
  addVarBindingRel_observationExtension (addVarBinding_sound h)

/-- Executable equality insertion preserves the seed observations on every
surviving branch. -/
theorem addVarEquality_observationExtension
    {b out : Bindings} {left right : String} {fuel : Nat}
    (h : out ∈ addVarEquality b left right fuel) :
    HEBindingObservationExtension b out :=
  addVarEqualityRel_observationExtension (addVarEquality_sound h)

/-- Executable full merge preserves the left seed observations on every
surviving branch. -/
theorem mergeBindings_observationExtension
    {left right out : Bindings} {fuel : Nat}
    (h : out ∈ mergeBindings left right fuel) :
    HEBindingObservationExtension left out :=
  mergeRel_observationExtension (mergeBindings_sound h)

/-- Once a trace obligation is realized, enlarging the two relevant HE
observations cannot invalidate its witness. -/
theorem LeaEliminationTraceEntryRealized.mono
    {before after : Bindings} {entry : String × Metta.Atom}
    (hext : HEBindingObservationExtension before after)
    (hrealized : LeaEliminationTraceEntryRealized before entry) :
    LeaEliminationTraceEntryRealized after entry := by
  rcases entry with ⟨traceKey, leaValue⟩
  cases leaValue with
  | var target => exact hext.classes hrealized
  | sym symbol | gnd symbol | expr symbol =>
      rcases hrealized with ⟨key, value, hvalue, hclass, hatom⟩
      exact ⟨key, value, hext.assignments key value hvalue,
        hext.classes hclass, HELeaAtomClassRel.mono hext.classes hatom⟩

/-- The finite, presentation-independent deficit used to index paired
matcher/merge progress.  It counts selected Robinson obligations not yet
visible in the HE output's closure and class-relative assignments. -/
noncomputable def pendingEliminationTraceEntries
    (b : Bindings) (trace : List (String × Metta.Atom)) :
    Finset (String × Metta.Atom) := by
  classical
  exact trace.toFinset.filter fun entry =>
    ¬ LeaEliminationTraceEntryRealized b entry

theorem pendingEliminationTraceEntries_eq_empty_iff
    (b : Bindings) (trace : List (String × Metta.Atom)) :
    pendingEliminationTraceEntries b trace = ∅ ↔
      ∀ entry ∈ trace,
        LeaEliminationTraceEntryRealized b entry := by
  classical
  simp [pendingEliminationTraceEntries]

/-- Observation extension can only remove pending Robinson obligations. -/
theorem pendingEliminationTraceEntries_mono
    {before after : Bindings} {trace : List (String × Metta.Atom)}
    (hext : HEBindingObservationExtension before after) :
    pendingEliminationTraceEntries after trace ⊆
      pendingEliminationTraceEntries before trace := by
  classical
  intro entry hmem
  simp only [pendingEliminationTraceEntries, Finset.mem_filter,
    List.mem_toFinset] at hmem ⊢
  exact ⟨hmem.1, fun hbefore => hmem.2 (hbefore.mono hext)⟩

/-- A successful executable merge can only discharge trace obligations from
the left accumulator. -/
theorem pendingEliminationTraceEntries_mono_of_mergeBindings
    {left right out : Bindings} {trace : List (String × Metta.Atom)}
    {fuel : Nat} (hmerge : out ∈ mergeBindings left right fuel) :
    pendingEliminationTraceEntries out trace ⊆
      pendingEliminationTraceEntries left trace :=
  pendingEliminationTraceEntries_mono
    (mergeBindings_observationExtension hmerge)

/-- Realizing one formerly pending entry gives the strict decrease needed by
the paired recursive matcher/merge induction. -/
theorem pendingEliminationTraceEntries_card_lt_of_newly_realized
    {before after : Bindings} {trace : List (String × Metta.Atom)}
    {entry : String × Metta.Atom}
    (hext : HEBindingObservationExtension before after)
    (hentry : entry ∈ trace)
    (hbefore : ¬ LeaEliminationTraceEntryRealized before entry)
    (hafter : LeaEliminationTraceEntryRealized after entry) :
    (pendingEliminationTraceEntries after trace).card <
      (pendingEliminationTraceEntries before trace).card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨pendingEliminationTraceEntries_mono hext, ?_⟩
  intro heq
  have hmemBefore : entry ∈ pendingEliminationTraceEntries before trace := by
    simp [pendingEliminationTraceEntries, hentry, hbefore]
  have hmemAfter : entry ∈ pendingEliminationTraceEntries after trace := by
    simpa [heq] using hmemBefore
  simp [pendingEliminationTraceEntries, hafter] at hmemAfter

/-- The same strict decrease is available directly at the executable merge
surface used by recursive expression matching. -/
theorem pendingEliminationTraceEntries_card_lt_of_mergeBindings
    {left right out : Bindings} {trace : List (String × Metta.Atom)}
    {entry : String × Metta.Atom} {fuel : Nat}
    (hmerge : out ∈ mergeBindings left right fuel)
    (hentry : entry ∈ trace)
    (hbefore : ¬ LeaEliminationTraceEntryRealized left entry)
    (hafter : LeaEliminationTraceEntryRealized out entry) :
    (pendingEliminationTraceEntries out trace).card <
      (pendingEliminationTraceEntries left trace).card :=
  pendingEliminationTraceEntries_card_lt_of_newly_realized
    (mergeBindings_observationExtension hmerge) hentry hbefore hafter

/-- A finite sequence of actual HE matcher-result merge-backs.  This is the
operational spine followed by recursive expression reconciliation; it records
neither a preferred binding-list presentation nor a preferred matcher MGU. -/
inductive HEMatcherMergeChain : Bindings → Bindings → Prop where
  | nil (bindings : Bindings) : HEMatcherMergeChain bindings bindings
  | cons {before matched next out : Bindings} {left right : Atom}
      {matchFuel mergeFuel : Nat} :
      matched ∈ matchAtoms left right matchFuel →
      next ∈ mergeBindings before matched mergeFuel →
      HEMatcherMergeChain next out →
      HEMatcherMergeChain before out

/-- A matcher-origin merge chain monotonically extends direct-assignment and
equality-class observations. -/
theorem HEMatcherMergeChain.observationExtension
    {before after : Bindings} (h : HEMatcherMergeChain before after) :
    HEBindingObservationExtension before after := by
  induction h with
  | nil bindings => exact HEBindingObservationExtension.refl bindings
  | cons hmatch hmerge htail ih =>
      exact (mergeBindings_observationExtension hmerge).trans ih

/-- The no-bare-variable invariant propagates through every matcher-origin
merge chain. -/
theorem HEMatcherMergeChain.assignmentsNonVariable
    {before after : Bindings} (h : HEMatcherMergeChain before after)
    (hbefore : HEAssignmentsNonVariable before) :
    HEAssignmentsNonVariable after := by
  induction h with
  | nil bindings => exact hbefore
  | cons hmatch hmerge htail ih =>
      exact ih (mergeBindings_assignmentsNonVariable hmerge hbefore
        (heAssignmentsNonVariable_of_matchAtoms hmatch))

/-- A live HE match/merge derivation over an exact translated LeaTTa
equation worklist.  Each step retains the original declarative matcher and
merge witnesses together with the local Robinson-trace certificates needed
by recursive reconciliation.  No binding-list presentation or preferred MGU
is part of the index. -/
inductive HETranslatedEquationMatchMergeChain
    (trace : List (String × Metta.Atom)) :
    Bindings → List (Metta.Atom × Metta.Atom) → Bindings → Prop where
  | nil (bindings : Bindings) :
      HETranslatedEquationMatchMergeChain trace bindings [] bindings
  | cons {before matched next out : Bindings}
      {left right : Atom} {leaLeft leaRight : Metta.Atom}
      {rest : List (Metta.Atom × Metta.Atom)}
      (hmatch : DeclMatchSpec.MatchRel left right matched)
      (hmerge : MergeRel before matched next)
      (left_translation : toLeaTTaAtom left = leaLeft)
      (right_translation : toLeaTTaAtom right = leaRight)
      (match_trace : MatchTraceSound trace hmatch)
      (matched_assignments :
        LeaEliminationTraceAssignmentsSound matched trace)
      (merge_trace : MergeTraceSound trace hmerge)
      (tail : HETranslatedEquationMatchMergeChain trace next rest out) :
      HETranslatedEquationMatchMergeChain trace before
        ((leaLeft, leaRight) :: rest) out

/-- Forgetting the translated worklist and local proof certificates yields a
finite sequence of actual executable matcher-result merge-backs. -/
theorem HETranslatedEquationMatchMergeChain.toMatcherMergeChain
    {trace : List (String × Metta.Atom)} {before after : Bindings}
    {equations : List (Metta.Atom × Metta.Atom)}
    (h : HETranslatedEquationMatchMergeChain
      trace before equations after) :
    HEMatcherMergeChain before after := by
  induction h with
  | nil bindings => exact HEMatcherMergeChain.nil bindings
  | cons hmatch hmerge _ _ _ _ _ _ ih =>
      obtain ⟨matchFuel, hmatchMem⟩ :=
        DeclMatchSpec.matchAtoms_complete hmatch
      obtain ⟨mergeFuel, hmergeMem⟩ := mergeBindings_complete hmerge
      exact HEMatcherMergeChain.cons hmatchMem hmergeMem ih

/-- The paired live chain preserves class-relative Robinson provenance from
its seed through every original matcher and merge derivation. -/
theorem HETranslatedEquationMatchMergeChain.assignmentsSound
    {trace : List (String × Metta.Atom)} {before after : Bindings}
    {equations : List (Metta.Atom × Metta.Atom)}
    (h : HETranslatedEquationMatchMergeChain
      trace before equations after)
    (hbefore : LeaEliminationTraceAssignmentsSound before trace) :
    LeaEliminationTraceAssignmentsSound after trace := by
  induction h with
  | nil bindings => exact hbefore
  | cons _ hmerge _ _ _ hmatched hmergeTrace _ ih =>
      exact ih (mergeRel_assignmentsSound_of_traceSound
        hmergeTrace hbefore hmatched)

/-- The operational no-bare-variable invariant is preserved by the same
declarative matcher/merge chain. -/
theorem HETranslatedEquationMatchMergeChain.assignmentsNonVariable
    {trace : List (String × Metta.Atom)} {before after : Bindings}
    {equations : List (Metta.Atom × Metta.Atom)}
    (h : HETranslatedEquationMatchMergeChain
      trace before equations after)
    (hbefore : HEAssignmentsNonVariable before) :
    HEAssignmentsNonVariable after := by
  induction h with
  | nil bindings => exact hbefore
  | cons hmatch hmerge _ _ _ _ _ _ ih =>
      exact ih (mergeRel_assignmentsNonVariable hmerge hbefore
        (heAssignmentsNonVariable_of_matchRel hmatch))

/-- Local paired derivations embed into a larger successful Robinson trace
without changing their original matcher or merge witnesses. -/
theorem HETranslatedEquationMatchMergeChain.mono
    {small large : List (String × Metta.Atom)} {before after : Bindings}
    {equations : List (Metta.Atom × Metta.Atom)}
    (h : HETranslatedEquationMatchMergeChain
      small before equations after)
    (hsubset : ∀ entry ∈ small, entry ∈ large) :
    HETranslatedEquationMatchMergeChain large before equations after := by
  induction h with
  | nil bindings => exact HETranslatedEquationMatchMergeChain.nil bindings
  | cons hmatch hmerge hleft hright hmatchTrace hmatched hmergeTrace
      htail ih =>
      exact HETranslatedEquationMatchMergeChain.cons
        hmatch hmerge hleft hright
        (hmatchTrace.mono hsubset)
        (hmatched.of_trace_subset hsubset)
        (hmergeTrace.mono hsubset) ih

/-- Sequential paired runs compose by concatenating their translated
equation worklists. -/
theorem HETranslatedEquationMatchMergeChain.append
    {trace : List (String × Metta.Atom)}
    {before middle after : Bindings}
    {first second : List (Metta.Atom × Metta.Atom)}
    (hfirst : HETranslatedEquationMatchMergeChain
      trace before first middle)
    (hsecond : HETranslatedEquationMatchMergeChain
      trace middle second after) :
    HETranslatedEquationMatchMergeChain
      trace before (first ++ second) after := by
  induction hfirst with
  | nil bindings => exact hsecond
  | cons hmatch hmerge hleft hright hmatchTrace hmatched hmergeTrace
      htail ih =>
      exact HETranslatedEquationMatchMergeChain.cons
        hmatch hmerge hleft hright hmatchTrace hmatched hmergeTrace
        (ih hsecond)

/-- One local step required from the paired matcher/reconciliation induction:
an actual matcher result is merged back, the no-bare-variable and assignment
provenance invariants survive, and one formerly pending trace entry becomes
visible. -/
structure HEEliminationTraceProgressStep
    (trace : List (String × Metta.Atom))
    (before after : Bindings) where
  left : Atom
  right : Atom
  matched : Bindings
  matchFuel : Nat
  mergeFuel : Nat
  match_mem : matched ∈ matchAtoms left right matchFuel
  merge_mem : after ∈ mergeBindings before matched mergeFuel
  entry : String × Metta.Atom
  entry_mem : entry ∈ trace
  pending_before : ¬ LeaEliminationTraceEntryRealized before entry
  realized_after : LeaEliminationTraceEntryRealized after entry
  assignmentsSound : LeaEliminationTraceAssignmentsSound after trace
  solutionPreserving : ∀ valuation,
    HEBindingSatisfied valuation before →
    MettaConstraintsSatisfied valuation trace →
    MettaEquationSatisfied valuation
      (toLeaTTaAtom left, toLeaTTaAtom right)

/-- The full local certificate required from an original reconciliation
conflict step.  It retains the exact matcher and merge derivations already
stored by `progress`, together with both independent invariants used by the
final quotient bridge: Robinson-trace assignment provenance and an upper
bound on the live equality graph.  No equality of binding presentations is
part of this package. -/
structure HECertifiedEliminationTraceProgressStep
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (before after : Bindings) where
  progress : HEEliminationTraceProgressStep trace before after
  matchTraceSound : MatchTraceSound trace
    (DeclMatchSpec.matchAtoms_sound progress.match_mem)
  matchEqualityClosureBoundSound :
    MatchEqualityClosureBoundSound allowed
      (DeclMatchSpec.matchAtoms_sound progress.match_mem)
  mergeTraceSound : MergeTraceSound trace
    (mergeBindings_sound progress.merge_mem)
  mergeEqualityClosureBoundSound :
    MergeEqualityClosureBoundSound allowed
      (mergeBindings_sound progress.merge_mem)

/-- A finite sequence of locally certified original matcher/merge steps.
Unlike `HEMatcherMergeChain`, this judgment retains exactly the two
derivation-local certificates needed to compose recursive reconciliation.
The trace and allowed equality graph are semantic indices; matcher result
records and their traversal order remain existential operational detail. -/
inductive HECertifiedMatcherMergeChain
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String)) :
    Bindings → Bindings → Prop where
  | nil (bindings : Bindings) :
      HECertifiedMatcherMergeChain trace allowed bindings bindings
  | cons {before next out : Bindings} :
      HECertifiedEliminationTraceProgressStep
        trace allowed before next →
      HECertifiedMatcherMergeChain trace allowed next out →
      HECertifiedMatcherMergeChain trace allowed before out

/-- Forgetting the proof indices yields the ordinary executable
matcher-origin merge chain. -/
theorem HECertifiedMatcherMergeChain.toMatcherMergeChain
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {before after : Bindings}
    (h : HECertifiedMatcherMergeChain trace allowed before after) :
    HEMatcherMergeChain before after := by
  induction h with
  | nil bindings => exact .nil bindings
  | cons hstep _ ih =>
      exact .cons hstep.progress.match_mem hstep.progress.merge_mem ih

/-- The no-bare-variable operational invariant propagates through a
certified chain. -/
theorem HECertifiedMatcherMergeChain.assignmentsNonVariable
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {before after : Bindings}
    (h : HECertifiedMatcherMergeChain trace allowed before after)
    (hbefore : HEAssignmentsNonVariable before) :
    HEAssignmentsNonVariable after :=
  h.toMatcherMergeChain.assignmentsNonVariable hbefore

/-- The derivation-local equality certificates compose along the live
accumulator, so a bounded seed yields a bounded final equality graph. -/
theorem HECertifiedMatcherMergeChain.equalityClosureBound
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {before after : Bindings}
    (h : HECertifiedMatcherMergeChain trace allowed before after)
    (hbefore : HEEqualityClosureBound before allowed) :
    HEEqualityClosureBound after allowed := by
  induction h with
  | nil bindings => exact hbefore
  | cons hstep _ ih =>
      exact ih
        (hstep.mergeEqualityClosureBoundSound.preserves hbefore)

/-- A fresh non-variable Robinson constraint is one complete local progress
step: HE matches the variable against the translated value, merges the
singleton matcher record into the accumulator, and records the new assignment
with exact trace provenance. -/
theorem exists_freshNonvarProgressStep
    {trace : List (String × Metta.Atom)} {before : Bindings}
    {key : String} {value : Atom}
    (hclass : before.classValues key = [])
    (hvalue : DeclMatchSpec.Atom.isVarB value = false)
    (hentry : (key, toLeaTTaAtom value) ∈ trace)
    (hpending : ¬ LeaEliminationTraceEntryRealized before
      (key, toLeaTTaAtom value))
    (hsound : LeaEliminationTraceAssignmentsSound before trace) :
    ∃ after, Nonempty (HEEliminationTraceProgressStep trace before after) := by
  have hbound : before.isBound key = false :=
    isBound_false_of_classValues_nil hclass
  have hlookup : before.lookup key = none := by
    cases hlookup : before.lookup key with
    | none => rfl
    | some stored =>
        simp [Bindings.isBound, hlookup] at hbound
  obtain ⟨matchFuel, hmatch⟩ := DeclMatchSpec.matchAtoms_complete
    (DeclMatchSpec.MatchRel.varNonVar (v := key) (t := value) hvalue)
  have hadd : before.assign key value ∈
      addVarBinding before key value 1 := by
    simp [addVarBinding, hclass]
  have hmerge : before.assign key value ∈
      mergeBindings before (Bindings.empty.assign key value) 2 := by
    rw [mergeBindings_single_assign]
    exact hadd
  have hleaNonvar : ∀ target, toLeaTTaAtom value ≠ .var target := by
    cases value with
    | var target => simp [DeclMatchSpec.Atom.isVarB] at hvalue
    | symbol name | grounded name | expression name =>
        intro target hfalse
        cases hfalse
  have hsoundAfter : LeaEliminationTraceAssignmentsSound
      (before.assign key value) trace :=
    hsound.assign_of_lookup_none hlookup
      (HELeaAtomClassRel.translation before value) hentry hleaNonvar
  have hrealized : LeaEliminationTraceEntryRealized
      (before.assign key value) (key, toLeaTTaAtom value) := by
    cases value with
    | var target => simp [DeclMatchSpec.Atom.isVarB] at hvalue
    | symbol name | grounded name | expression name =>
        exact ⟨key, _, by simp [Bindings.assign, hbound],
          EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl,
          HELeaAtomClassRel.translation _ _⟩
  exact ⟨before.assign key value, ⟨{
    left := .var key
    right := value
    matched := Bindings.empty.assign key value
    matchFuel := matchFuel
    mergeFuel := 2
    match_mem := hmatch
    merge_mem := hmerge
    entry := (key, toLeaTTaAtom value)
    entry_mem := hentry
    pending_before := hpending
    realized_after := hrealized
    assignmentsSound := hsoundAfter
    solutionPreserving := by
      intro valuation _hbefore htrace
      have hconstraint := htrace
        (key, toLeaTTaAtom value) hentry
      simpa [MettaEquationSatisfied, applyClassSolution] using hconstraint
  }⟩⟩

/-- A consistent variable/variable constraint is the alias companion to the
fresh-value progress step.  It adds one equality edge, introduces no
assignment, and realizes the selected alias obligation. -/
theorem exists_consistentAliasProgressStep
    {trace : List (String × Metta.Atom)} {before : Bindings}
    {left right : String}
    (hconsistent : Bindings.valuesConsistent
      ((before.addEquality left right).classValues left) = true)
    (hentry : (left, .var right) ∈ trace)
    (hpending : ¬ LeaEliminationTraceEntryRealized before
      (left, .var right))
    (hsound : LeaEliminationTraceAssignmentsSound before trace) :
    ∃ after, Nonempty (HEEliminationTraceProgressStep trace before after) := by
  obtain ⟨matchFuel, hmatch⟩ := DeclMatchSpec.matchAtoms_complete
    (DeclMatchSpec.MatchRel.varVar left right)
  have hadd : before.addEquality left right ∈
      addVarEquality before left right 1 := by
    simp [addVarEquality, hconsistent]
  have hmerge : before.addEquality left right ∈
      mergeBindings before (Bindings.empty.addEquality left right) 2 := by
    simpa [mergeBindings, Bindings.addEquality, Bindings.empty] using hadd
  have hrealized : LeaEliminationTraceEntryRealized
      (before.addEquality left right) (left, .var right) := by
    change right ∈ (before.addEquality left right).eqClass left
    rw [EqualityClosure.mem_eqClass_iff_reachable]
    by_cases hsame : left = right
    · subst right
      exact .rfl
    · exact (show
          (EqualityClosure.edgeGraph
            (before.addEquality left right).equalities).Adj left right by
            rw [EqualityClosure.edgeGraph_adj_iff]
            exact ⟨hsame, Or.inl (by simp [Bindings.addEquality])⟩).reachable
  exact ⟨before.addEquality left right, ⟨{
    left := .var left
    right := .var right
    matched := Bindings.empty.addEquality left right
    matchFuel := matchFuel
    mergeFuel := 2
    match_mem := hmatch
    merge_mem := hmerge
    entry := (left, .var right)
    entry_mem := hentry
    pending_before := hpending
    realized_after := hrealized
    assignmentsSound := hsound.addEquality left right
    solutionPreserving := by
      intro valuation _hbefore htrace
      have hconstraint := htrace (left, .var right) hentry
      simpa [MettaEquationSatisfied, applyClassSolution] using hconstraint
  }⟩⟩

/-- Exact frontier exposed by a nonempty order-free trace deficit.  The two
`progressed` base cases are discharged by the real HE insertion operations;
the only residual cases are precisely the value-conflict and joined-class
conflict branches that recurse through matcher/merge reconciliation. -/
inductive HEEliminationTraceProgressFrontier
    (trace : List (String × Metta.Atom)) (before : Bindings) : Prop where
  | progressed {after : Bindings} :
      HEEliminationTraceProgressStep trace before after →
      HEEliminationTraceProgressFrontier trace before
  | valueConflict {key : String} {value : Atom} {leaValue : Metta.Atom}
      {first : Atom} {rest : List Atom} :
      toLeaTTaAtom value = leaValue →
      DeclMatchSpec.Atom.isVarB value = false →
      before.classValues key = first :: rest →
      (key, leaValue) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (key, leaValue) →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEliminationTraceProgressFrontier trace before
  | aliasConflict {left right : String} :
      Bindings.valuesConsistent
          ((before.addEquality left right).classValues left) = false →
      (left, .var right) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (left, .var right) →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEliminationTraceProgressFrontier trace before

/-- Selecting any pending translated Robinson obligation either performs one
of the two nonrecursive HE progress steps or exposes one of the two genuine
recursive conflict shapes.  No relation-list order or representative choice
is inspected. -/
theorem progressFrontier_of_pending
    {trace : List (String × Metta.Atom)} {before : Bindings}
    (himage : ∀ key term, (key, term) ∈ trace →
      ∃ atom : Atom, toLeaTTaAtom atom = term)
    (hsound : LeaEliminationTraceAssignmentsSound before trace)
    (hpending : pendingEliminationTraceEntries before trace ≠ ∅) :
    HEEliminationTraceProgressFrontier trace before := by
  classical
  obtain ⟨entry, hentryPending⟩ :=
    Finset.nonempty_iff_ne_empty.mpr hpending
  have hentryData := hentryPending
  simp only [pendingEliminationTraceEntries, Finset.mem_filter,
    List.mem_toFinset] at hentryData
  rcases entry with ⟨key, leaValue⟩
  rcases hentryData with ⟨hentry, hnotRealized⟩
  cases leaValue with
  | var target =>
      cases hconsistent : Bindings.valuesConsistent
          ((before.addEquality key target).classValues key) with
      | false =>
          exact .aliasConflict hconsistent hentry hnotRealized hsound
      | true =>
          obtain ⟨after, ⟨hstep⟩⟩ :=
            exists_consistentAliasProgressStep hconsistent hentry
              hnotRealized hsound
          exact .progressed hstep
  | sym symbol =>
      obtain ⟨value, hvalue⟩ := himage key (.sym symbol) hentry
      have hnonvar : DeclMatchSpec.Atom.isVarB value = false := by
        cases value <;> simp_all [toLeaTTaAtom,
          DeclMatchSpec.Atom.isVarB]
      cases hclass : before.classValues key with
      | nil =>
          obtain ⟨after, ⟨hstep⟩⟩ :=
            exists_freshNonvarProgressStep hclass hnonvar
              (by simpa [← hvalue] using hentry)
              (by simpa [← hvalue] using hnotRealized) hsound
          exact .progressed hstep
      | cons first rest =>
          exact .valueConflict hvalue hnonvar hclass hentry
            hnotRealized hsound
  | gnd ground =>
      obtain ⟨value, hvalue⟩ := himage key (.gnd ground) hentry
      have hnonvar : DeclMatchSpec.Atom.isVarB value = false := by
        cases value <;> simp_all [toLeaTTaAtom,
          DeclMatchSpec.Atom.isVarB]
      cases hclass : before.classValues key with
      | nil =>
          obtain ⟨after, ⟨hstep⟩⟩ :=
            exists_freshNonvarProgressStep hclass hnonvar
              (by simpa [← hvalue] using hentry)
              (by simpa [← hvalue] using hnotRealized) hsound
          exact .progressed hstep
      | cons first rest =>
          exact .valueConflict hvalue hnonvar hclass hentry
            hnotRealized hsound
  | expr atoms =>
      obtain ⟨value, hvalue⟩ := himage key (.expr atoms) hentry
      have hnonvar : DeclMatchSpec.Atom.isVarB value = false := by
        cases value <;> simp_all [toLeaTTaAtom,
          DeclMatchSpec.Atom.isVarB]
      cases hclass : before.classValues key with
      | nil =>
          obtain ⟨after, ⟨hstep⟩⟩ :=
            exists_freshNonvarProgressStep hclass hnonvar
              (by simpa [← hvalue] using hentry)
              (by simpa [← hvalue] using hnotRealized) hsound
          exact .progressed hstep
      | cons first rest =>
          exact .valueConflict hvalue hnonvar hclass hentry
            hnotRealized hsound

/-- A reachable value-conflict frontier carries a genuine solution of the
HE equation between the stored class representative and the proposed value.
This is the semantic input to the strictly smaller recursive matcher call. -/
theorem valueConflict_equationSatisfied
    {trace : List (String × Metta.Atom)} {before : Bindings}
    {valuation : String → Metta.Atom}
    {key : String} {value first : Atom} {rest : List Atom}
    {leaValue : Metta.Atom}
    (hbefore : HEBindingSatisfied valuation before)
    (htrace : MettaConstraintsSatisfied valuation trace)
    (hvalue : toLeaTTaAtom value = leaValue)
    (hclass : before.classValues key = first :: rest)
    (hentry : (key, leaValue) ∈ trace) :
    MettaEquationSatisfied valuation
      (toLeaTTaAtom first, toLeaTTaAtom value) := by
  have hfirst : first ∈ before.classValues key := by
    rw [hclass]
    simp
  have hstored :=
    hbefore.eq_applyClassSolution_of_mem_classValues hfirst
  have hproposed := htrace (key, leaValue) hentry
  rw [← hvalue] at hproposed
  exact hstored.symm.trans hproposed

/-- Any two values already carried by one satisfying HE equality class have
the same valuation image. -/
theorem classValues_equationSatisfied
    {before : Bindings} {valuation : String → Metta.Atom}
    {key : String} {first second : Atom}
    (hbefore : HEBindingSatisfied valuation before)
    (hfirst : first ∈ before.classValues key)
    (hsecond : second ∈ before.classValues key) :
    MettaEquationSatisfied valuation
      (toLeaTTaAtom first, toLeaTTaAtom second) := by
  have hfirstValue :=
    hbefore.eq_applyClassSolution_of_mem_classValues hfirst
  have hsecondValue :=
    hbefore.eq_applyClassSolution_of_mem_classValues hsecond
  exact hfirstValue.symm.trans hsecondValue

/-- Unequal values already present in one reachable, no-bare-variable class
can only require expression recursion. -/
theorem bothExpressions_of_ne_classValues_of_satisfied
    {before : Bindings} {valuation : String → Metta.Atom}
    {key : String} {first second : Atom}
    (hnonvar : HEAssignmentsNonVariable before)
    (hbefore : HEBindingSatisfied valuation before)
    (hfirst : first ∈ before.classValues key)
    (hsecond : second ∈ before.classValues key)
    (hne : first ≠ second) :
    BothExpressions first second := by
  by_contra hleaf
  obtain ⟨matched, fuel, hmatch⟩ :=
    exists_matchAtoms_of_solution_leaf
      ⟨valuation, classValues_equationSatisfied
        hbefore hfirst hsecond⟩ hleaf
  exact hne (matchAtoms_eq_of_nonvariable_leaf
    (hnonvar.isVarB_eq_false_of_classValue hfirst)
    (hnonvar.isVarB_eq_false_of_classValue hsecond)
    hleaf hmatch)

/-- A pending non-variable class conflict cannot be a leaf mismatch.  Common
satisfiability makes every leaf match executable; HE leaf soundness then
forces literal equality, which would already realize the trace entry.  Thus
the residual value-conflict case is exactly expression recursion. -/
theorem bothExpressions_of_pending_valueConflict
    {trace : List (String × Metta.Atom)} {before : Bindings}
    {valuation : String → Metta.Atom}
    {key : String} {value first : Atom} {rest : List Atom}
    {leaValue : Metta.Atom}
    (hnonvar : HEAssignmentsNonVariable before)
    (hbefore : HEBindingSatisfied valuation before)
    (htrace : MettaConstraintsSatisfied valuation trace)
    (hvalue : toLeaTTaAtom value = leaValue)
    (hvalueNonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : before.classValues key = first :: rest)
    (hentry : (key, leaValue) ∈ trace)
    (hpending : ¬ LeaEliminationTraceEntryRealized before
      (key, leaValue)) :
    BothExpressions first value := by
  have hfirst : first ∈ before.classValues key := by
    rw [hclass]
    simp
  have hfirstNonvar : DeclMatchSpec.Atom.isVarB first = false :=
    hnonvar.isVarB_eq_false_of_classValue hfirst
  by_contra hleaf
  obtain ⟨matched, fuel, hmatch⟩ :=
    exists_matchAtoms_of_solution_leaf
      ⟨valuation, valueConflict_equationSatisfied
        hbefore htrace hvalue hclass hentry⟩ hleaf
  have hequal : first = value :=
    matchAtoms_eq_of_nonvariable_leaf hfirstNonvar hvalueNonvar
      hleaf hmatch
  subst first
  unfold Bindings.classValues at hfirst
  obtain ⟨storedKey, hordered, hlookup⟩ :=
    List.mem_filterMap.mp hfirst
  have hassignment : (storedKey, value) ∈ before.assignments :=
    assignment_mem_of_lookup_eq_some (by
      simpa [Bindings.lookup] using hlookup)
  have hclassForward : storedKey ∈ before.eqClass key :=
    EqualityClosure.mem_eqClassOrdered_iff.mp hordered
  have hclassReverse : key ∈ before.eqClass storedKey := by
    apply EqualityClosure.mem_eqClass_iff_reachable.mpr
    exact (EqualityClosure.mem_eqClass_iff_reachable.mp
      hclassForward).symm
  apply hpending
  rw [← hvalue]
  cases value with
  | var target =>
      simp [DeclMatchSpec.Atom.isVarB] at hvalueNonvar
  | symbol name | grounded name | expression name =>
      exact ⟨storedKey, _, hassignment, hclassReverse,
        HELeaAtomClassRel.translation before _⟩

/-- A satisfying valuation for a pending alias constraint also satisfies the
candidate record formed by adding that equality edge. -/
theorem aliasConflict_candidateSatisfied
    {trace : List (String × Metta.Atom)} {before : Bindings}
    {valuation : String → Metta.Atom} {left right : String}
    (hbefore : HEBindingSatisfied valuation before)
    (htrace : MettaConstraintsSatisfied valuation trace)
    (hentry : (left, .var right) ∈ trace) :
    HEBindingSatisfied valuation (before.addEquality left right) := by
  apply (heBindingSatisfied_addEquality_iff
    valuation before left right).mpr
  refine ⟨hbefore, ?_⟩
  have hconstraint := htrace (left, .var right) hentry
  simpa [applyClassSolution] using hconstraint

/-- Consequently every pair of values selected from the inconsistent joined
class has a common solution.  This is the semantic input to the joined-class
recursive matcher/list-matcher branch. -/
theorem aliasConflict_classValues_equationSatisfied
    {trace : List (String × Metta.Atom)} {before : Bindings}
    {valuation : String → Metta.Atom} {left right : String}
    {first second : Atom}
    (hbefore : HEBindingSatisfied valuation before)
    (htrace : MettaConstraintsSatisfied valuation trace)
    (hentry : (left, .var right) ∈ trace)
    (hfirst : first ∈
      (before.addEquality left right).classValues left)
    (hsecond : second ∈
      (before.addEquality left right).classValues left) :
    MettaEquationSatisfied valuation
      (toLeaTTaAtom first, toLeaTTaAtom second) := by
  have hcandidate :=
    aliasConflict_candidateSatisfied hbefore htrace hentry
  have hfirstValue :=
    hcandidate.eq_applyClassSolution_of_mem_classValues hfirst
  have hsecondValue :=
    hcandidate.eq_applyClassSolution_of_mem_classValues hsecond
  exact hfirstValue.symm.trans hsecondValue

/-- Every unequal value pair selected by a reachable inconsistent alias join
is expression-shaped.  Leaf completeness plus no-bare-variable preservation
would otherwise force the two values to be literally equal. -/
theorem bothExpressions_of_ne_aliasConflict_classValues
    {trace : List (String × Metta.Atom)} {before : Bindings}
    {valuation : String → Metta.Atom} {left right : String}
    {first second : Atom}
    (hnonvar : HEAssignmentsNonVariable before)
    (hbefore : HEBindingSatisfied valuation before)
    (htrace : MettaConstraintsSatisfied valuation trace)
    (hentry : (left, .var right) ∈ trace)
    (hfirst : first ∈
      (before.addEquality left right).classValues left)
    (hsecond : second ∈
      (before.addEquality left right).classValues left)
    (hne : first ≠ second) :
    BothExpressions first second := by
  have hcandidateNonvar :
      HEAssignmentsNonVariable (before.addEquality left right) := by
    intro key target hmem
    apply hnonvar key target
    simpa [Bindings.addEquality] using hmem
  by_contra hleaf
  obtain ⟨matched, fuel, hmatch⟩ :=
    exists_matchAtoms_of_solution_leaf
      ⟨valuation, aliasConflict_classValues_equationSatisfied
        hbefore htrace hentry hfirst hsecond⟩ hleaf
  exact hne (matchAtoms_eq_of_nonvariable_leaf
    (hcandidateNonvar.isVarB_eq_false_of_classValue hfirst)
    (hcandidateNonvar.isVarB_eq_false_of_classValue hsecond)
    hleaf hmatch)

/-- Reachable form of the local frontier.  Compared with the purely
structural split, common satisfiability collapses value conflicts to
expression recursion and proves that every unequal joined-class pair is also
expression-shaped. -/
inductive HESatisfiedEliminationTraceProgressFrontier
    (valuation : String → Metta.Atom)
    (trace : List (String × Metta.Atom)) (before : Bindings) : Prop where
  | progressed {after : Bindings} :
      HEEliminationTraceProgressStep trace before after →
      HESatisfiedEliminationTraceProgressFrontier valuation trace before
  | valueExpressionConflict {key : String} {value : Atom}
      {leaValue : Metta.Atom} {first : Atom} {rest : List Atom} :
      toLeaTTaAtom value = leaValue →
      DeclMatchSpec.Atom.isVarB value = false →
      before.classValues key = first :: rest →
      (key, leaValue) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (key, leaValue) →
      LeaEliminationTraceAssignmentsSound before trace →
      BothExpressions first value →
      (∀ {stored other : Atom},
        stored ∈ before.classValues key →
        other ∈ before.classValues key →
        stored ≠ other → BothExpressions stored other) →
      HESatisfiedEliminationTraceProgressFrontier valuation trace before
  | aliasExpressionConflict {left right : String} :
      Bindings.valuesConsistent
          ((before.addEquality left right).classValues left) = false →
      (left, .var right) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (left, .var right) →
      LeaEliminationTraceAssignmentsSound before trace →
      (∀ {first second : Atom},
        first ∈ (before.addEquality left right).classValues left →
        second ∈ (before.addEquality left right).classValues left →
        first ≠ second → BothExpressions first second) →
      HESatisfiedEliminationTraceProgressFrontier valuation trace before

theorem satisfiedProgressFrontier_of_pending
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)} {before : Bindings}
    (himage : ∀ key term, (key, term) ∈ trace →
      ∃ atom : Atom, toLeaTTaAtom atom = term)
    (hnonvar : HEAssignmentsNonVariable before)
    (hsound : LeaEliminationTraceAssignmentsSound before trace)
    (hbefore : HEBindingSatisfied valuation before)
    (htrace : MettaConstraintsSatisfied valuation trace)
    (hpending : pendingEliminationTraceEntries before trace ≠ ∅) :
    HESatisfiedEliminationTraceProgressFrontier
      valuation trace before := by
  cases progressFrontier_of_pending himage hsound hpending with
  | progressed hstep => exact .progressed hstep
  | valueConflict hvalue hvalueNonvar hclass hentry hnotRealized _ =>
      exact .valueExpressionConflict hvalue hvalueNonvar hclass hentry
        hnotRealized hsound
        (bothExpressions_of_pending_valueConflict
          hnonvar hbefore htrace hvalue hvalueNonvar hclass hentry
            hnotRealized)
        (fun hstored hother hne =>
          bothExpressions_of_ne_classValues_of_satisfied
            hnonvar hbefore hstored hother hne)
  | aliasConflict hinconsistent hentry hnotRealized _ =>
      exact .aliasExpressionConflict hinconsistent hentry hnotRealized
        hsound (fun hfirst hsecond hne =>
          bothExpressions_of_ne_aliasConflict_classValues
            hnonvar hbefore htrace hentry hfirst hsecond hne)

/-- Every local progress step strictly lowers the presentation-independent
trace deficit. -/
theorem HEEliminationTraceProgressStep.card_lt
    {trace : List (String × Metta.Atom)} {before after : Bindings}
    (h : HEEliminationTraceProgressStep trace before after) :
    (pendingEliminationTraceEntries after trace).card <
      (pendingEliminationTraceEntries before trace).card :=
  pendingEliminationTraceEntries_card_lt_of_mergeBindings
    h.merge_mem h.entry_mem h.pending_before h.realized_after

/-- A progress step selected from a commonly satisfiable trace preserves that
valuation through its actual matcher result and merge-back. -/
theorem HEEliminationTraceProgressStep.afterSatisfied
    {trace : List (String × Metta.Atom)} {before after : Bindings}
    (h : HEEliminationTraceProgressStep trace before after)
    {valuation : String → Metta.Atom}
    (hbefore : HEBindingSatisfied valuation before)
    (htrace : MettaConstraintsSatisfied valuation trace) :
    HEBindingSatisfied valuation after := by
  apply (mergeBindings_solution_iff h.merge_mem valuation).mpr
  refine ⟨hbefore, ?_⟩
  exact (matchAtoms_solution_iff h.match_mem valuation).mpr
    (h.solutionPreserving valuation hbefore htrace)

/-- The settled structural trace invariant splits into a maintained
assignment-soundness condition and exhaustion of the order-free finite
obligation deficit. -/
theorem eliminationTraceStructuralRel_iff_sound_pending_empty
    {b : Bindings} {trace : List (String × Metta.Atom)} :
    LeaEliminationTraceStructuralRel b trace ↔
      LeaEliminationTraceAssignmentsSound b trace ∧
        pendingEliminationTraceEntries b trace = ∅ := by
  rw [pendingEliminationTraceEntries_eq_empty_iff]
  constructor
  · intro h
    refine ⟨h.classValues.1, ?_⟩
    intro entry hentry
    rcases entry with ⟨key, leaValue⟩
    cases leaValue with
    | var target => exact h.aliases key target hentry
    | sym symbol | gnd symbol | expr symbol =>
        exact h.classValues.2 key _ hentry (by intro target h; cases h)
  · rintro ⟨hsound, hall⟩
    constructor
    · intro key target hentry
      exact hall (key, .var target) hentry
    · constructor
      · exact hsound
      · intro leaKey leaValue hentry hnonvar
        have hrealized := hall (leaKey, leaValue) hentry
        cases leaValue with
        | var target => exact (hnonvar target rfl).elim
        | sym symbol | gnd symbol | expr symbol => exact hrealized

/-- Order-free completion for the fully certified local step judgment.  The
finite Robinson deficit supplies termination once; every recursive step then
threads both operational invariants through the exact live merge derivation.
The result simultaneously exposes the ordinary matcher chain, complete trace
provenance, and the equality-closure upper bound required by the final
congruence theorem. -/
theorem exists_completeCertifiedMatcherMergeChain_of_local_progress
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {start : Bindings}
    (hstartNonVariable : HEAssignmentsNonVariable start)
    (hstartSound : LeaEliminationTraceAssignmentsSound start trace)
    (hstartBound : HEEqualityClosureBound start allowed)
    (hprogress : ∀ before,
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEqualityClosureBound before allowed →
      pendingEliminationTraceEntries before trace ≠ ∅ →
      ∃ after, Nonempty
        (HECertifiedEliminationTraceProgressStep
          trace allowed before after)) :
    ∃ out,
      HECertifiedMatcherMergeChain trace allowed start out ∧
        HEAssignmentsNonVariable out ∧
          LeaEliminationTraceStructuralRel out trace ∧
            HEEqualityClosureBound out allowed := by
  classical
  have go : ∀ deficit before,
      (pendingEliminationTraceEntries before trace).card = deficit →
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEqualityClosureBound before allowed →
      ∃ out,
        HECertifiedMatcherMergeChain trace allowed before out ∧
          HEAssignmentsNonVariable out ∧
            LeaEliminationTraceStructuralRel out trace ∧
              HEEqualityClosureBound out allowed := by
    intro deficit
    induction deficit using Nat.strong_induction_on with
    | h deficit ih =>
        intro before hcard hnonvar hsound hbound
        by_cases hempty : pendingEliminationTraceEntries before trace = ∅
        · exact ⟨before, .nil before, hnonvar,
            eliminationTraceStructuralRel_iff_sound_pending_empty.mpr
              ⟨hsound, hempty⟩,
            hbound⟩
        · obtain ⟨after, ⟨hstep⟩⟩ :=
            hprogress before hnonvar hsound hbound hempty
          have hlt :
              (pendingEliminationTraceEntries after trace).card < deficit := by
            rw [← hcard]
            exact hstep.progress.card_lt
          have hmatchedNonvar :
              HEAssignmentsNonVariable hstep.progress.matched :=
            heAssignmentsNonVariable_of_matchAtoms
              hstep.progress.match_mem
          have hafterNonvar : HEAssignmentsNonVariable after :=
            mergeBindings_assignmentsNonVariable
              hstep.progress.merge_mem hnonvar hmatchedNonvar
          have hafterBound : HEEqualityClosureBound after allowed :=
            hstep.mergeEqualityClosureBoundSound.preserves hbound
          obtain ⟨out, hchain, houtNonvar, houtStructural,
              houtBound⟩ :=
            ih _ hlt after rfl hafterNonvar
              hstep.progress.assignmentsSound hafterBound
          exact ⟨out, .cons hstep hchain, houtNonvar,
            houtStructural, houtBound⟩
  exact go _ start rfl hstartNonVariable hstartSound hstartBound

/-- Satisfiability-indexed certified completion.  A common valuation is
threaded through the same exact matcher/merge steps, leaving the two original
expression-conflict constructors as the only local obligations. -/
theorem exists_completeSatisfiedCertifiedMatcherMergeChain_of_local_progress
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {start : Bindings}
    {valuation : String → Metta.Atom}
    (htraceSatisfied : MettaConstraintsSatisfied valuation trace)
    (hstartNonVariable : HEAssignmentsNonVariable start)
    (hstartSound : LeaEliminationTraceAssignmentsSound start trace)
    (hstartBound : HEEqualityClosureBound start allowed)
    (hstartSatisfied : HEBindingSatisfied valuation start)
    (hprogress : ∀ before,
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEqualityClosureBound before allowed →
      HEBindingSatisfied valuation before →
      pendingEliminationTraceEntries before trace ≠ ∅ →
      ∃ after, Nonempty
        (HECertifiedEliminationTraceProgressStep
          trace allowed before after)) :
    ∃ out,
      HECertifiedMatcherMergeChain trace allowed start out ∧
        HEAssignmentsNonVariable out ∧
          LeaEliminationTraceStructuralRel out trace ∧
            HEEqualityClosureBound out allowed ∧
              HEBindingSatisfied valuation out := by
  classical
  have go : ∀ deficit before,
      (pendingEliminationTraceEntries before trace).card = deficit →
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEqualityClosureBound before allowed →
      HEBindingSatisfied valuation before →
      ∃ out,
        HECertifiedMatcherMergeChain trace allowed before out ∧
          HEAssignmentsNonVariable out ∧
            LeaEliminationTraceStructuralRel out trace ∧
              HEEqualityClosureBound out allowed ∧
                HEBindingSatisfied valuation out := by
    intro deficit
    induction deficit using Nat.strong_induction_on with
    | h deficit ih =>
        intro before hcard hnonvar hsound hbound hsatisfied
        by_cases hempty : pendingEliminationTraceEntries before trace = ∅
        · exact ⟨before, .nil before, hnonvar,
            eliminationTraceStructuralRel_iff_sound_pending_empty.mpr
              ⟨hsound, hempty⟩,
            hbound, hsatisfied⟩
        · obtain ⟨after, ⟨hstep⟩⟩ :=
            hprogress before hnonvar hsound hbound hsatisfied hempty
          have hlt :
              (pendingEliminationTraceEntries after trace).card < deficit := by
            rw [← hcard]
            exact hstep.progress.card_lt
          have hmatchedNonvar :
              HEAssignmentsNonVariable hstep.progress.matched :=
            heAssignmentsNonVariable_of_matchAtoms
              hstep.progress.match_mem
          have hafterNonvar : HEAssignmentsNonVariable after :=
            mergeBindings_assignmentsNonVariable
              hstep.progress.merge_mem hnonvar hmatchedNonvar
          have hafterBound : HEEqualityClosureBound after allowed :=
            hstep.mergeEqualityClosureBoundSound.preserves hbound
          have hafterSatisfied : HEBindingSatisfied valuation after :=
            hstep.progress.afterSatisfied hsatisfied htraceSatisfied
          obtain ⟨out, hchain, houtNonvar, houtStructural,
              houtBound, houtSatisfied⟩ :=
            ih _ hlt after rfl hafterNonvar
              hstep.progress.assignmentsSound hafterBound hafterSatisfied
          exact ⟨out, .cons hstep hchain, houtNonvar,
            houtStructural, houtBound, houtSatisfied⟩
  exact go _ start rfl hstartNonVariable hstartSound hstartBound
    hstartSatisfied

/-- Order-free well-founded lifting for the remaining paired induction.  If
every nonfinal sound state can take one genuine matcher-origin merge step,
then finitely many such steps construct a complete structural trace witness.
The local progress premise is exactly where expression matching and
reconciliation provenance meet; termination and global exhaustion are proved
once here. -/
theorem exists_completeMatcherMergeChain_of_local_progress
    {trace : List (String × Metta.Atom)} {start : Bindings}
    (hstartNonVariable : HEAssignmentsNonVariable start)
    (hstartSound : LeaEliminationTraceAssignmentsSound start trace)
    (hprogress : ∀ before,
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      pendingEliminationTraceEntries before trace ≠ ∅ →
      ∃ after, Nonempty (HEEliminationTraceProgressStep trace before after)) :
    ∃ out,
      HEMatcherMergeChain start out ∧
        HEAssignmentsNonVariable out ∧
          LeaEliminationTraceStructuralRel out trace := by
  classical
  have go : ∀ deficit before,
      (pendingEliminationTraceEntries before trace).card = deficit →
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      ∃ out,
        HEMatcherMergeChain before out ∧
          HEAssignmentsNonVariable out ∧
            LeaEliminationTraceStructuralRel out trace := by
    intro deficit
    induction deficit using Nat.strong_induction_on with
    | h deficit ih =>
        intro before hcard hnonvar hsound
        by_cases hempty : pendingEliminationTraceEntries before trace = ∅
        · exact ⟨before, .nil before, hnonvar,
            eliminationTraceStructuralRel_iff_sound_pending_empty.mpr
              ⟨hsound, hempty⟩⟩
        · obtain ⟨after, ⟨hstep⟩⟩ :=
            hprogress before hnonvar hsound hempty
          have hlt :
              (pendingEliminationTraceEntries after trace).card < deficit := by
            rw [← hcard]
            exact hstep.card_lt
          have hmatchedNonvar :
              HEAssignmentsNonVariable hstep.matched :=
            heAssignmentsNonVariable_of_matchAtoms hstep.match_mem
          have hafterNonvar : HEAssignmentsNonVariable after :=
            mergeBindings_assignmentsNonVariable
              hstep.merge_mem hnonvar hmatchedNonvar
          obtain ⟨out, hchain, houtNonvar, houtStructural⟩ :=
            ih _ hlt after rfl hafterNonvar hstep.assignmentsSound
          exact ⟨out,
            .cons hstep.match_mem hstep.merge_mem hchain,
            houtNonvar, houtStructural⟩
  exact go _ start rfl hstartNonVariable hstartSound

/-- Satisfiability-indexed form of the order-free lifting.  This is the form
used by reconciliation: a fixed common valuation is carried through every
actual matcher/merge step, so local conflict progress is never requested for
an unreachable or inconsistent accumulator. -/
theorem exists_completeMatcherMergeChain_of_satisfied_local_progress
    {trace : List (String × Metta.Atom)} {start : Bindings}
    {valuation : String → Metta.Atom}
    (htraceSatisfied : MettaConstraintsSatisfied valuation trace)
    (hstartNonVariable : HEAssignmentsNonVariable start)
    (hstartSound : LeaEliminationTraceAssignmentsSound start trace)
    (hstartSatisfied : HEBindingSatisfied valuation start)
    (hprogress : ∀ before,
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEBindingSatisfied valuation before →
      pendingEliminationTraceEntries before trace ≠ ∅ →
      ∃ after, Nonempty (HEEliminationTraceProgressStep trace before after)) :
    ∃ out,
      HEMatcherMergeChain start out ∧
        HEAssignmentsNonVariable out ∧
          LeaEliminationTraceStructuralRel out trace ∧
            HEBindingSatisfied valuation out := by
  classical
  have go : ∀ deficit before,
      (pendingEliminationTraceEntries before trace).card = deficit →
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEBindingSatisfied valuation before →
      ∃ out,
        HEMatcherMergeChain before out ∧
          HEAssignmentsNonVariable out ∧
            LeaEliminationTraceStructuralRel out trace ∧
              HEBindingSatisfied valuation out := by
    intro deficit
    induction deficit using Nat.strong_induction_on with
    | h deficit ih =>
        intro before hcard hnonvar hsound hsatisfied
        by_cases hempty : pendingEliminationTraceEntries before trace = ∅
        · exact ⟨before, .nil before, hnonvar,
            eliminationTraceStructuralRel_iff_sound_pending_empty.mpr
              ⟨hsound, hempty⟩,
            hsatisfied⟩
        · obtain ⟨after, ⟨hstep⟩⟩ :=
            hprogress before hnonvar hsound hsatisfied hempty
          have hlt :
              (pendingEliminationTraceEntries after trace).card < deficit := by
            rw [← hcard]
            exact hstep.card_lt
          have hmatchedNonvar : HEAssignmentsNonVariable hstep.matched :=
            heAssignmentsNonVariable_of_matchAtoms hstep.match_mem
          have hafterNonvar : HEAssignmentsNonVariable after :=
            mergeBindings_assignmentsNonVariable
              hstep.merge_mem hnonvar hmatchedNonvar
          have hafterSatisfied : HEBindingSatisfied valuation after :=
            hstep.afterSatisfied hsatisfied htraceSatisfied
          obtain ⟨out, hchain, houtNonvar, houtStructural,
              houtSatisfied⟩ :=
            ih _ hlt after rfl hafterNonvar hstep.assignmentsSound
              hafterSatisfied
          exact ⟨out,
            .cons hstep.match_mem hstep.merge_mem hchain,
            houtNonvar, houtStructural, houtSatisfied⟩
  exact go _ start rfl hstartNonVariable hstartSound hstartSatisfied

/-- Empty bindings are satisfiable by every valuation, so successful trace
satisfaction leaves only the local reachable-conflict progress theorem. -/
theorem exists_completeSatisfiedMatcherMergeChain_from_empty
    {trace : List (String × Metta.Atom)}
    {valuation : String → Metta.Atom}
    (htraceSatisfied : MettaConstraintsSatisfied valuation trace)
    (hprogress : ∀ before,
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEBindingSatisfied valuation before →
      pendingEliminationTraceEntries before trace ≠ ∅ →
      ∃ after, Nonempty (HEEliminationTraceProgressStep trace before after)) :
    ∃ out,
      HEMatcherMergeChain Bindings.empty out ∧
        HEAssignmentsNonVariable out ∧
          LeaEliminationTraceStructuralRel out trace ∧
            HEBindingSatisfied valuation out := by
  apply exists_completeMatcherMergeChain_of_satisfied_local_progress
    htraceSatisfied
  · intro key target hmem
    simp [Bindings.empty] at hmem
  · intro key value hmem
    simp [Bindings.empty] at hmem
  · exact (hesat_empty_iff valuation).mpr trivial
  · exact hprogress

/-- Empty HE bindings discharge the two initial invariants automatically, so
the paired reconciliation proof only needs to provide its local progress
constructor. -/
theorem exists_completeMatcherMergeChain_from_empty
    {trace : List (String × Metta.Atom)}
    (hprogress : ∀ before,
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      pendingEliminationTraceEntries before trace ≠ ∅ →
      ∃ after, Nonempty (HEEliminationTraceProgressStep trace before after)) :
    ∃ out,
      HEMatcherMergeChain Bindings.empty out ∧
        HEAssignmentsNonVariable out ∧
          LeaEliminationTraceStructuralRel out trace := by
  apply exists_completeMatcherMergeChain_of_local_progress
    (start := Bindings.empty) (trace := trace)
  · intro key target hmem
    simp [Bindings.empty] at hmem
  · intro key value hmem
    simp [Bindings.empty] at hmem
  · exact hprogress

/-- The global well-founded construction now depends only on the two genuine
recursive conflict constructors.  Translation-image selection, fresh value
insertion, consistent alias insertion, deficit decrease, and termination are
all discharged here. -/
theorem exists_completeMatcherMergeChain_of_conflict_progress
    {trace : List (String × Metta.Atom)}
    (himage : ∀ key term, (key, term) ∈ trace →
      ∃ atom : Atom, toLeaTTaAtom atom = term)
    (hvalueProgress : ∀
      (before : Bindings) (key : String) (value : Atom)
      (leaValue : Metta.Atom) (first : Atom) (rest : List Atom),
      HEAssignmentsNonVariable before →
      toLeaTTaAtom value = leaValue →
      DeclMatchSpec.Atom.isVarB value = false →
      before.classValues key = first :: rest →
      (key, leaValue) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (key, leaValue) →
      LeaEliminationTraceAssignmentsSound before trace →
      ∃ after, Nonempty
        (HEEliminationTraceProgressStep trace before after))
    (haliasProgress : ∀
      (before : Bindings) (left right : String),
      HEAssignmentsNonVariable before →
      Bindings.valuesConsistent
          ((before.addEquality left right).classValues left) = false →
      (left, .var right) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (left, .var right) →
      LeaEliminationTraceAssignmentsSound before trace →
      ∃ after, Nonempty
        (HEEliminationTraceProgressStep trace before after)) :
    ∃ out,
      HEMatcherMergeChain Bindings.empty out ∧
        HEAssignmentsNonVariable out ∧
          LeaEliminationTraceStructuralRel out trace := by
  apply exists_completeMatcherMergeChain_from_empty
  intro before hnonvar hsound hpending
  cases progressFrontier_of_pending himage hsound hpending with
  | progressed hstep => exact ⟨_, ⟨hstep⟩⟩
  | valueConflict hvalue hvalueNonvar hclass hentry hnotRealized _ =>
      exact hvalueProgress before _ _ _ _ _ hnonvar hvalue
        hvalueNonvar hclass hentry hnotRealized hsound
  | aliasConflict hinconsistent hentry hnotRealized _ =>
      exact haliasProgress before _ _ hnonvar hinconsistent hentry
        hnotRealized hsound

/-- Satisfiability-indexed reduction of the global reconciliation problem to
the two reachable expression-conflict constructors.  All leaf mismatches,
fresh values, consistent aliases, deficit decrease, and valuation transport
are discharged before either callback is invoked. -/
theorem exists_completeSatisfiedMatcherMergeChain_of_conflict_progress
    {trace : List (String × Metta.Atom)}
    {valuation : String → Metta.Atom}
    (himage : ∀ key term, (key, term) ∈ trace →
      ∃ atom : Atom, toLeaTTaAtom atom = term)
    (htraceSatisfied : MettaConstraintsSatisfied valuation trace)
    (hvalueProgress : ∀
      (before : Bindings) (key : String) (value : Atom)
      (leaValue : Metta.Atom) (first : Atom) (rest : List Atom),
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEBindingSatisfied valuation before →
      toLeaTTaAtom value = leaValue →
      DeclMatchSpec.Atom.isVarB value = false →
      before.classValues key = first :: rest →
      (key, leaValue) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (key, leaValue) →
      BothExpressions first value →
      (∀ {stored other : Atom},
        stored ∈ before.classValues key →
        other ∈ before.classValues key →
        stored ≠ other → BothExpressions stored other) →
      ∃ after, Nonempty
        (HEEliminationTraceProgressStep trace before after))
    (haliasProgress : ∀
      (before : Bindings) (left right : String),
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEBindingSatisfied valuation before →
      Bindings.valuesConsistent
          ((before.addEquality left right).classValues left) = false →
      (left, .var right) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (left, .var right) →
      (∀ {first second : Atom},
        first ∈ (before.addEquality left right).classValues left →
        second ∈ (before.addEquality left right).classValues left →
        first ≠ second → BothExpressions first second) →
      ∃ after, Nonempty
        (HEEliminationTraceProgressStep trace before after)) :
    ∃ out,
      HEMatcherMergeChain Bindings.empty out ∧
        HEAssignmentsNonVariable out ∧
          LeaEliminationTraceStructuralRel out trace ∧
            HEBindingSatisfied valuation out := by
  apply exists_completeSatisfiedMatcherMergeChain_from_empty
    htraceSatisfied
  intro before hnonvar hsound hbefore hpending
  cases satisfiedProgressFrontier_of_pending
      himage hnonvar hsound hbefore htraceSatisfied hpending with
  | progressed hstep => exact ⟨_, ⟨hstep⟩⟩
  | valueExpressionConflict hvalue hvalueNonvar hclass hentry
      hnotRealized _ hexpressions hallExpressions =>
      exact hvalueProgress before _ _ _ _ _ hnonvar hsound hbefore
        hvalue hvalueNonvar hclass hentry hnotRealized
        hexpressions hallExpressions
  | aliasExpressionConflict hinconsistent hentry hnotRealized _
      hallExpressions =>
      exact haliasProgress before _ _ hnonvar hsound hbefore
        hinconsistent hentry hnotRealized hallExpressions

/-- A complete structural certificate has discharged every finite trace
obligation. -/
theorem LeaEliminationTraceStructuralRel.pending_eq_empty
    {b : Bindings} {trace : List (String × Metta.Atom)}
    (h : LeaEliminationTraceStructuralRel b trace) :
    pendingEliminationTraceEntries b trace = ∅ :=
  (eliminationTraceStructuralRel_iff_sound_pending_empty.mp h).2

/-- Empty bindings present the empty solve trace. -/
theorem LeaEliminationTraceStructuralRel.empty :
    LeaEliminationTraceStructuralRel Bindings.empty [] := by
  constructor
  · intro key target hmem
    simp at hmem
  · constructor <;> intro <;> simp_all [Bindings.empty]

/-- Lift the complete structural trace certificate through one non-variable
elimination step. -/
theorem LeaEliminationTraceStructuralRel.nonvar
    {b : Bindings} {trace : List (String × Metta.Atom)}
    {key : String} {value : Atom} {leaValue : Metta.Atom}
    (h : LeaEliminationTraceStructuralRel b trace)
    (hlookup : b.lookup key = none)
    (hatom : HELeaAtomClassRel b value leaValue)
    (hnonvar : ∀ target, leaValue ≠ .var target) :
    LeaEliminationTraceStructuralRel
      (b.assign key value) ((key, leaValue) :: trace) := by
  have hbound : b.isBound key = false := by
    simp [Bindings.isBound, hlookup]
  constructor
  · intro traceKey target hmem
    simp only [List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with hnew | hold
    · rcases hnew with ⟨hkey, hvalue⟩
      exact (hnonvar target hvalue.symm).elim
    · have hclass := h.aliases traceKey target hold
      simpa [Bindings.eqClass, Bindings.assign, hbound] using hclass
  · exact (eliminationStep_nonvar_preserves_classValues
      h.classValues hlookup hatom hnonvar).2

/-- Lift the complete structural trace certificate through one variable
elimination step. -/
theorem LeaEliminationTraceStructuralRel.variable
    {b : Bindings} {trace : List (String × Metta.Atom)}
    {key target : String}
    (h : LeaEliminationTraceStructuralRel b trace) :
    LeaEliminationTraceStructuralRel
      (b.addEquality key target) ((key, .var target) :: trace) := by
  have hstep := eliminationStep_variable_preserves_classValues
    (b := b) (trace := trace) (key := key) (target := target)
    h.classValues
  have hclassMono : ∀ {start finish : String},
      finish ∈ b.eqClass start →
        finish ∈ (b.addEquality key target).eqClass start :=
    eqClass_mono_addEquality b key target
  constructor
  · intro traceKey traceTarget hmem
    simp only [List.mem_cons, Prod.mk.injEq,
      Metta.Atom.var.injEq] at hmem
    rcases hmem with hnew | hold
    · rcases hnew with ⟨rfl, rfl⟩
      exact hstep.1
    · exact hclassMono (h.aliases traceKey traceTarget hold)
  · exact hstep.2

/-! ## Triangularity of the Robinson solve trace -/

/-- Exact one-step view of a successful repaired-LeaTTa Robinson run.  The
elimination constructor exposes the strictly smaller recursive run used by
the paired operational induction. -/
inductive UnifyRoundsSuccessView :
    (fuel : Nat) → (equations : List (Metta.Atom × Metta.Atom)) →
      (subst result : Metta.Subst) → Prop where
  | solved {fuel equations subst result} :
      Metta.Unify.decomposeAll equations = some [] →
      result = subst →
      UnifyRoundsSuccessView fuel equations subst result
  | eliminate {fuel equations subst result key term rest} :
      Metta.Unify.decomposeAll equations =
        some ((key, term) :: rest) →
      Metta.Subst.occurs key term = false →
      Metta.Unify.unifyRounds fuel
          (rest.map fun constraint =>
            (Metta.Subst.apply [(key, term)] (.var constraint.1),
              Metta.Subst.apply [(key, term)] constraint.2))
          (Metta.Subst.extend subst key term) = some result →
      UnifyRoundsSuccessView (fuel + 1) equations subst result

/-- Every successful Robinson execution is either already solved or exposes
one occurs-check-clean elimination and a smaller successful execution. -/
theorem unifyRounds_success_view
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hrun : Metta.Unify.unifyRounds fuel equations subst = some result) :
    UnifyRoundsSuccessView fuel equations subst result := by
  cases fuel with
  | zero =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              have hresult : result = subst := by
                simpa [Metta.Unify.unifyRounds, hdecompose] using hrun.symm
              exact .solved hdecompose hresult
          | cons constraint rest =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hrun
  | succ fuel =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              have hresult : result = subst := by
                simpa [Metta.Unify.unifyRounds, hdecompose] using hrun.symm
              exact .solved hdecompose hresult
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  simp [Metta.Unify.unifyRounds, hdecompose,
                    hoccurs] at hrun
              | false =>
                  apply UnifyRoundsSuccessView.eliminate
                    hdecompose hoccurs
                  simpa [Metta.Unify.unifyRounds, hdecompose,
                    hoccurs] using hrun

/-- Whole-binding reconciliation exposes the same solved/eliminate view at
its exact equation-system fuel. -/
theorem wholeBindingReconciliation_success_view
    {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    UnifyRoundsSuccessView
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations source ++ extra))
      (Metta.Bindings.equations source ++ extra) [] result := by
  apply unifyRounds_success_view
  simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll] using
    hreconcile

/-- Structural decomposition distributes over equation-list append.  In
particular, constraints from the left prefix remain before constraints from
the suffix. -/
theorem decomposeAll_append
    (left right : List (Metta.Atom × Metta.Atom)) :
    Metta.Unify.decomposeAll (left ++ right) =
      match Metta.Unify.decomposeAll left,
          Metta.Unify.decomposeAll right with
      | some leftConstraints, some rightConstraints =>
          some (leftConstraints ++ rightConstraints)
      | _, _ => none := by
  induction left with
  | nil =>
      cases hright : Metta.Unify.decomposeAll right <;>
        simp [Metta.Unify.decomposeAll, hright]
  | cons equation left ih =>
      rcases equation with ⟨first, second⟩
      simp only [List.cons_append, Metta.Unify.decomposeAll]
      rw [ih]
      cases Metta.Unify.decomposeEq first second <;>
        cases Metta.Unify.decomposeAll left <;>
          cases Metta.Unify.decomposeAll right <;> simp

/-- Once the left worklist is structurally solved, appending it is invisible
to decomposition of the remaining worklist. -/
theorem decomposeAll_append_of_left_nil
    {left : List (Metta.Atom × Metta.Atom)}
    (right : List (Metta.Atom × Metta.Atom))
    (hleft : Metta.Unify.decomposeAll left = some []) :
    Metta.Unify.decomposeAll (left ++ right) =
      Metta.Unify.decomposeAll right := by
  rw [decomposeAll_append, hleft]
  cases Metta.Unify.decomposeAll right <;> rfl

/-- Success of a left-to-right Robinson run projects to its equation prefix.
The prefix run may return a different normalized substitution; only existence
is claimed. -/
theorem exists_unifyRounds_prefix_success
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hrun : Metta.Unify.unifyRounds fuel (front ++ suffix) subst =
      some result) :
    ∃ frontResult,
      Metta.Unify.unifyRounds fuel front subst = some frontResult := by
  induction fuel generalizing front suffix subst result with
  | zero =>
      cases hfront : Metta.Unify.decomposeAll front with
      | none =>
          have happend := decomposeAll_append front suffix
          rw [hfront] at happend
          simp only at happend
          simp [Metta.Unify.unifyRounds, happend] at hrun
      | some frontConstraints =>
          cases frontConstraints with
          | nil =>
              exact ⟨subst, by
                simp [Metta.Unify.unifyRounds, hfront]⟩
          | cons constraint rest =>
              cases hsuffix : Metta.Unify.decomposeAll suffix with
              | none =>
                  have happend := decomposeAll_append front suffix
                  rw [hfront, hsuffix] at happend
                  simp only at happend
                  simp [Metta.Unify.unifyRounds, happend] at hrun
              | some suffixConstraints =>
                  have happend := decomposeAll_append front suffix
                  rw [hfront, hsuffix] at happend
                  simp only at happend
                  simp [Metta.Unify.unifyRounds, happend] at hrun
  | succ fuel ih =>
      cases hfront : Metta.Unify.decomposeAll front with
      | none =>
          have happend := decomposeAll_append front suffix
          rw [hfront] at happend
          simp only at happend
          simp [Metta.Unify.unifyRounds, happend] at hrun
      | some frontConstraints =>
          cases frontConstraints with
          | nil =>
              exact ⟨subst, by
                simp [Metta.Unify.unifyRounds, hfront]⟩
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hsuffix : Metta.Unify.decomposeAll suffix with
              | none =>
                  have happend := decomposeAll_append front suffix
                  rw [hfront, hsuffix] at happend
                  simp only at happend
                  simp [Metta.Unify.unifyRounds, happend] at hrun
              | some suffixConstraints =>
                  have happend := decomposeAll_append front suffix
                  rw [hfront, hsuffix] at happend
                  simp only at happend
                  cases hoccurs : Metta.Subst.occurs key term with
                  | true =>
                      simp [Metta.Unify.unifyRounds, happend,
                        hoccurs] at hrun
                  | false =>
                      let transform := fun constraint : String × Metta.Atom =>
                        (Metta.Subst.apply [(key, term)] (.var constraint.1),
                          Metta.Subst.apply [(key, term)] constraint.2)
                      have htail :
                          Metta.Unify.unifyRounds fuel
                              (rest.map transform ++
                                suffixConstraints.map transform)
                              (Metta.Subst.extend subst key term) =
                            some result := by
                        simpa [Metta.Unify.unifyRounds, happend, hoccurs,
                          transform, List.map_append] using hrun
                      obtain ⟨frontResult, hfrontTail⟩ :=
                        ih htail
                      refine ⟨frontResult, ?_⟩
                      simpa [Metta.Unify.unifyRounds, hfront, hoccurs,
                        transform] using hfrontTail

/-- A Robinson round depends on an equation presentation only through its
fully decomposed constraint list. -/
theorem unifyRounds_eq_of_decomposeAll_eq
    {fuel : Nat} {left right : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst}
    (hdecompose : Metta.Unify.decomposeAll left =
      Metta.Unify.decomposeAll right) :
    Metta.Unify.unifyRounds fuel left subst =
      Metta.Unify.unifyRounds fuel right subst := by
  cases fuel <;> simp only [Metta.Unify.unifyRounds] <;> rw [hdecompose]

/-- Extending the variable identity valuation homomorphically is the identity
on every repaired-LeaTTa atom. -/
theorem applyClassSolution_variable_identity (atom : Metta.Atom) :
    applyClassSolution (fun name => .var name) atom = atom := by
  induction atom with
  | sym symbol => simp [applyClassSolution]
  | var name => simp [applyClassSolution]
  | gnd ground => simp [applyClassSolution]
  | expr atoms ih =>
      simp only [applyClassSolution]
      rw [List.map_congr_left ih]
      simp

/-- On the host-float-free fragment, an equation that decomposes to no
constraints was already syntactically equal.  This derives from the existing
solution characterization rather than a second decomposition recursion. -/
theorem eq_of_decomposeEq_eq_some_nil
    {left right : Metta.Atom}
    (hleft : MettaAtomNoFloat left)
    (hright : MettaAtomNoFloat right)
    (hdecompose : Metta.Unify.decomposeEq left right = some []) :
    left = right := by
  let valuation : String → Metta.Atom := fun name => .var name
  have hsatisfied : MettaEquationSatisfied valuation (left, right) :=
    (decomposeEq_solution_iff valuation left right []
      hleft hright hdecompose).mpr (by
        simp [MettaConstraintsSatisfied])
  simpa [MettaEquationSatisfied, valuation,
    applyClassSolution_variable_identity] using hsatisfied

/-- A successful unequal singleton equation in the float-free fragment has a
nonempty decomposed constraint list. -/
theorem exists_decomposeAll_singleton_cons_of_success
    {fuel : Nat} {left right : Metta.Atom} {subst result : Metta.Subst}
    (hleft : MettaAtomNoFloat left)
    (hright : MettaAtomNoFloat right)
    (hne : left ≠ right)
    (hrun : Metta.Unify.unifyRounds fuel [(left, right)] subst =
      some result) :
    ∃ constraint rest,
      Metta.Unify.decomposeAll [(left, right)] =
        some (constraint :: rest) := by
  cases hdecompose : Metta.Unify.decomposeAll [(left, right)] with
  | none =>
      cases fuel <;>
        simp [Metta.Unify.unifyRounds, hdecompose] at hrun
  | some constraints =>
      cases constraints with
      | nil =>
          cases hequation : Metta.Unify.decomposeEq left right with
          | none =>
              simp [Metta.Unify.decomposeAll, hequation] at hdecompose
          | some equationConstraints =>
              have hempty : equationConstraints = [] := by
                simpa [Metta.Unify.decomposeAll, hequation] using hdecompose
              subst equationConstraints
              exact (hne (eq_of_decomposeEq_eq_some_nil
                hleft hright hequation)).elim
      | cons constraint rest =>
          refine ⟨constraint, rest, ?_⟩
          rfl

/-- Decomposing a pointwise equation list agrees with decomposing its zipped
equation presentation whenever neither side is truncated. -/
theorem decomposeAll_zip_eq_decomposeList
    (left right : List Metta.Atom)
    (hlength : left.length = right.length) :
    Metta.Unify.decomposeAll (List.zip left right) =
      Metta.Unify.decomposeList left right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp_all [Metta.Unify.decomposeAll,
        Metta.Unify.decomposeList]
  | cons leftHead leftTail ih =>
      cases right with
      | nil => simp at hlength
      | cons rightHead rightTail =>
          have htail : leftTail.length = rightTail.length := by
            simpa using hlength
          simp only [List.zip_cons_cons, Metta.Unify.decomposeAll,
            Metta.Unify.decomposeList]
          rw [ih rightTail htail]

/-- A singleton expression equation and its pointwise zipped equations drive
exactly the same Robinson execution. -/
theorem unifyRounds_expression_eq_zip
    {fuel : Nat} {left right : List Metta.Atom} {subst : Metta.Subst}
    (hlength : left.length = right.length) :
    Metta.Unify.unifyRounds fuel [(.expr left, .expr right)] subst =
      Metta.Unify.unifyRounds fuel (List.zip left right) subst := by
  apply unifyRounds_eq_of_decomposeAll_eq
  rw [decomposeAll_zip_eq_decomposeList left right hlength]
  cases hdecompose : Metta.Unify.decomposeList left right <;>
    simp [Metta.Unify.decomposeAll, Metta.Unify.decomposeEq, hdecompose]

/-- Successful reconciliation of two expressions supplies a successful
Robinson certificate for the equation of every corresponding head pair. -/
theorem exists_unifyRounds_expression_head_success
    {fuel : Nat} {leftHead rightHead : Metta.Atom}
    {leftTail rightTail : List Metta.Atom} {subst result : Metta.Subst}
    (hlength : leftTail.length = rightTail.length)
    (hrun : Metta.Unify.unifyRounds fuel
      [(.expr (leftHead :: leftTail), .expr (rightHead :: rightTail))]
      subst = some result) :
    ∃ headResult,
      Metta.Unify.unifyRounds fuel [(leftHead, rightHead)] subst =
        some headResult := by
  have hzipped : Metta.Unify.unifyRounds fuel
      (List.zip (leftHead :: leftTail) (rightHead :: rightTail)) subst =
        some result := by
    rw [← unifyRounds_expression_eq_zip (by simpa using hlength)]
    exact hrun
  simpa only [List.zip_cons_cons, List.singleton_append] using
    exists_unifyRounds_prefix_success hzipped

/-- Exact operational factorization of a Robinson run around a left equation
prefix.  Eliminations selected from the prefix are replayed into the suffix;
when the prefix is solved, `remainingFuel`, `suffixWork`, and `prefixSubst`
are precisely the state from which the original run continues. -/
inductive UnifyRoundsPrefixSplit :
    (fuel : Nat) →
    (front suffix : List (Metta.Atom × Metta.Atom)) →
    (subst : Metta.Subst) →
    (remainingFuel : Nat) →
    (suffixWork : List (Metta.Atom × Metta.Atom)) →
    (prefixSubst : Metta.Subst) → Prop where
  | solved {fuel front suffix subst} :
      Metta.Unify.decomposeAll front = some [] →
      UnifyRoundsPrefixSplit fuel front suffix subst fuel suffix subst
  | eliminate {fuel front suffix subst key term rest suffixConstraints}
      {remainingFuel suffixWork prefixSubst} :
      Metta.Unify.decomposeAll front = some ((key, term) :: rest) →
      Metta.Unify.decomposeAll suffix = some suffixConstraints →
      Metta.Subst.occurs key term = false →
      UnifyRoundsPrefixSplit fuel
        (rest.map fun constraint =>
          (Metta.Subst.apply [(key, term)] (.var constraint.1),
            Metta.Subst.apply [(key, term)] constraint.2))
        (suffixConstraints.map fun constraint =>
          (Metta.Subst.apply [(key, term)] (.var constraint.1),
            Metta.Subst.apply [(key, term)] constraint.2))
        (Metta.Subst.extend subst key term)
        remainingFuel suffixWork prefixSubst →
      UnifyRoundsPrefixSplit (fuel + 1) front suffix subst
        remainingFuel suffixWork prefixSubst

/-- Every successful Robinson run factors through the exact state reached
after its left equation prefix has been solved. -/
theorem unifyRounds_prefix_split_of_success
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hrun : Metta.Unify.unifyRounds fuel (front ++ suffix) subst =
      some result) :
    ∃ remainingFuel suffixWork prefixSubst,
      UnifyRoundsPrefixSplit fuel front suffix subst
          remainingFuel suffixWork prefixSubst ∧
        Metta.Unify.unifyRounds remainingFuel suffixWork prefixSubst =
          some result := by
  induction fuel generalizing front suffix subst result with
  | zero =>
      cases hfront : Metta.Unify.decomposeAll front with
      | none =>
          have hall := decomposeAll_append front suffix
          rw [hfront] at hall
          simp only at hall
          simp [Metta.Unify.unifyRounds, hall] at hrun
      | some frontConstraints =>
          cases frontConstraints with
          | nil =>
              refine ⟨0, suffix, subst, .solved hfront, ?_⟩
              have hall := decomposeAll_append_of_left_nil suffix hfront
              rw [unifyRounds_eq_of_decomposeAll_eq
                (fuel := 0) (subst := subst) hall] at hrun
              exact hrun
          | cons constraint rest =>
              cases hsuffix : Metta.Unify.decomposeAll suffix with
              | none =>
                  have hall := decomposeAll_append front suffix
                  rw [hfront, hsuffix] at hall
                  simp only at hall
                  simp [Metta.Unify.unifyRounds, hall] at hrun
              | some suffixConstraints =>
                  have hall := decomposeAll_append front suffix
                  rw [hfront, hsuffix] at hall
                  simp only at hall
                  simp [Metta.Unify.unifyRounds, hall] at hrun
  | succ fuel ih =>
      cases hfront : Metta.Unify.decomposeAll front with
      | none =>
          have hall := decomposeAll_append front suffix
          rw [hfront] at hall
          simp only at hall
          simp [Metta.Unify.unifyRounds, hall] at hrun
      | some frontConstraints =>
          cases frontConstraints with
          | nil =>
              refine ⟨fuel + 1, suffix, subst, .solved hfront, ?_⟩
              have hall := decomposeAll_append_of_left_nil suffix hfront
              rw [unifyRounds_eq_of_decomposeAll_eq
                (fuel := fuel + 1) (subst := subst) hall] at hrun
              exact hrun
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hsuffix : Metta.Unify.decomposeAll suffix with
              | none =>
                  have hall := decomposeAll_append front suffix
                  rw [hfront, hsuffix] at hall
                  simp only at hall
                  simp [Metta.Unify.unifyRounds, hall] at hrun
              | some suffixConstraints =>
                  have hall := decomposeAll_append front suffix
                  rw [hfront, hsuffix] at hall
                  simp only at hall
                  cases hoccurs : Metta.Subst.occurs key term with
                  | true =>
                      simp [Metta.Unify.unifyRounds, hall, hoccurs] at hrun
                  | false =>
                      let transform := fun constraint : String × Metta.Atom =>
                        (Metta.Subst.apply [(key, term)] (.var constraint.1),
                          Metta.Subst.apply [(key, term)] constraint.2)
                      have htail : Metta.Unify.unifyRounds fuel
                          (rest.map transform ++ suffixConstraints.map transform)
                          (Metta.Subst.extend subst key term) = some result := by
                        simpa [Metta.Unify.unifyRounds, hall, hoccurs,
                          transform, List.map_append] using hrun
                      obtain ⟨remainingFuel, suffixWork, prefixSubst,
                          hsplit, hcontinue⟩ := ih htail
                      refine ⟨remainingFuel, suffixWork, prefixSubst, ?_,
                        hcontinue⟩
                      apply UnifyRoundsPrefixSplit.eliminate
                        hfront hsuffix hoccurs
                      simpa [transform] using hsplit

/-- The substitution recorded at a prefix boundary is exactly the result of
running that equation prefix alone from the same incoming substitution. -/
theorem UnifyRoundsPrefixSplit.front_run
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst) :
    Metta.Unify.unifyRounds fuel front subst = some prefixSubst := by
  induction h with
  | @solved fuel front suffix subst hfront =>
      cases fuel <;> simp [Metta.Unify.unifyRounds, hfront]
  | @eliminate fuel front suffix subst key term rest suffixConstraints
      remainingFuel suffixWork prefixSubst hfront hsuffix hoccurs htail ih =>
      simp [Metta.Unify.unifyRounds, hfront, hoccurs]
      simpa using ih

/-- Prefix factorization preserves the complete executable continuation, not
only successful runs.  Running the original prefixed worklist from its input
substitution is exactly the same computation as running the residual worklist
from the substitution accumulated while solving the prefix.  This is an
operational state theorem; it does not identify either substitution with a
normal form or with another engine's MGU. -/
theorem UnifyRoundsPrefixSplit.run_eq
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst) :
    Metta.Unify.unifyRounds fuel (front ++ suffix) subst =
      Metta.Unify.unifyRounds remainingFuel suffixWork prefixSubst := by
  induction h with
  | @solved fuel front suffix subst hfront =>
      apply unifyRounds_eq_of_decomposeAll_eq
      exact decomposeAll_append_of_left_nil suffix hfront
  | @eliminate fuel front suffix subst key term rest suffixConstraints
      remainingFuel suffixWork prefixSubst hfront hsuffix hoccurs htail ih =>
      have hall := decomposeAll_append front suffix
      rw [hfront, hsuffix] at hall
      simp only at hall
      rw [Metta.Unify.unifyRounds, hall]
      change (if Metta.Subst.occurs key term = true then none else
        Metta.Unify.unifyRounds fuel
          ((rest ++ suffixConstraints).map fun constraint =>
            (Metta.Subst.apply [(key, term)] (.var constraint.1),
              Metta.Subst.apply [(key, term)] constraint.2))
          (Metta.Subst.extend subst key term)) =
        Metta.Unify.unifyRounds remainingFuel suffixWork prefixSubst
      simpa [hoccurs, List.map_append] using ih

/-- Solving an equation prefix preserves the Robinson freshness invariant at
the exact residual state.  The result is indexed by worklist membership, not
by the presentation order of the accumulated substitution. -/
theorem UnifyRoundsPrefixSplit.stateFresh
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst)
    (hfresh : UnifyStateFresh (front ++ suffix) subst) :
    UnifyStateFresh suffixWork prefixSubst := by
  induction h with
  | @solved fuel front suffix subst hfront =>
      intro key hkey hmem
      exact hfresh key hkey (by
        simp only [mettaEquationVars, List.flatMap_append,
          List.mem_append]
        exact Or.inr hmem)
  | @eliminate fuel front suffix subst key term rest suffixConstraints
      remainingFuel suffixWork prefixSubst hfront hsuffix hoccurs htail ih =>
      have hall := decomposeAll_append front suffix
      rw [hfront, hsuffix] at hall
      simp only at hall
      have hnext : UnifyStateFresh
          ((rest ++ suffixConstraints).map fun constraint =>
            (Metta.Subst.apply [(key, term)] (.var constraint.1),
              Metta.Subst.apply [(key, term)] constraint.2))
          (Metta.Subst.extend subst key term) :=
        unifyRound_preserves_freshness hall hoccurs hfresh
      apply ih
      simpa only [List.map_append] using hnext

/-- Solving an equation prefix never increases the remaining Robinson fuel. -/
theorem UnifyRoundsPrefixSplit.remainingFuel_le
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst) :
    remainingFuel ≤ fuel := by
  induction h with
  | solved => exact Nat.le_refl _
  | eliminate _ _ _ _ ih => omega

/-- If the prefix exposes at least one elimination constraint, factorization
strictly decreases the fuel index. -/
theorem UnifyRoundsPrefixSplit.remainingFuel_lt_of_decompose_cons
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst)
    {constraint : String × Metta.Atom}
    {rest : List (String × Metta.Atom)}
    (hfront : Metta.Unify.decomposeAll front =
      some (constraint :: rest)) :
    remainingFuel < fuel := by
  cases h with
  | solved hsolved => rw [hsolved] at hfront; cases hfront
  | eliminate _ _ _ htail =>
      exact Nat.lt_succ_of_le htail.remainingFuel_le

/-- Successful prefix factorization is strictly fuel-decreasing whenever the
prefix contributes a genuine Robinson constraint. -/
theorem unifyRounds_prefix_split_strict_of_success
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    {constraint : String × Metta.Atom}
    {rest : List (String × Metta.Atom)}
    (hrun : Metta.Unify.unifyRounds fuel (front ++ suffix) subst =
      some result)
    (hfront : Metta.Unify.decomposeAll front =
      some (constraint :: rest)) :
    ∃ remainingFuel suffixWork prefixSubst,
      UnifyRoundsPrefixSplit fuel front suffix subst
          remainingFuel suffixWork prefixSubst ∧
        Metta.Unify.unifyRounds remainingFuel suffixWork prefixSubst =
          some result ∧
        remainingFuel < fuel := by
  obtain ⟨remainingFuel, suffixWork, prefixSubst, hsplit, hcontinue⟩ :=
    unifyRounds_prefix_split_of_success hrun
  exact ⟨remainingFuel, suffixWork, prefixSubst, hsplit, hcontinue,
    hsplit.remainingFuel_lt_of_decompose_cons hfront⟩

/-- For an unequal float-free head equation, successful total execution
automatically supplies the nonempty-decomposition premise and hence a strict
prefix split. -/
theorem unifyRounds_singleton_prefix_split_strict_of_ne
    {fuel : Nat} {left right : Metta.Atom}
    {suffix : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hleft : MettaAtomNoFloat left)
    (hright : MettaAtomNoFloat right)
    (hne : left ≠ right)
    (hrun : Metta.Unify.unifyRounds fuel
      ([(left, right)] ++ suffix) subst = some result) :
    ∃ remainingFuel suffixWork prefixSubst,
      UnifyRoundsPrefixSplit fuel [(left, right)] suffix subst
          remainingFuel suffixWork prefixSubst ∧
        Metta.Unify.unifyRounds remainingFuel suffixWork prefixSubst =
          some result ∧
        remainingFuel < fuel := by
  obtain ⟨headResult, hheadRun⟩ := exists_unifyRounds_prefix_success hrun
  obtain ⟨constraint, constraints, hdecompose⟩ :=
    exists_decomposeAll_singleton_cons_of_success
      hleft hright hne hheadRun
  exact unifyRounds_prefix_split_strict_of_success hrun hdecompose

/-- Expression reconciliation factors at its first pointwise equation and
returns the exact transformed tail state from which the same successful run
continues. -/
theorem unifyRounds_expression_head_split_of_success
    {fuel : Nat} {leftHead rightHead : Metta.Atom}
    {leftTail rightTail : List Metta.Atom} {subst result : Metta.Subst}
    (hlength : leftTail.length = rightTail.length)
    (hrun : Metta.Unify.unifyRounds fuel
      [(.expr (leftHead :: leftTail), .expr (rightHead :: rightTail))]
      subst = some result) :
    ∃ remainingFuel tailWork headSubst,
      UnifyRoundsPrefixSplit fuel [(leftHead, rightHead)]
          (List.zip leftTail rightTail) subst
          remainingFuel tailWork headSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork headSubst =
          some result := by
  have hzipped : Metta.Unify.unifyRounds fuel
      (List.zip (leftHead :: leftTail) (rightHead :: rightTail)) subst =
        some result := by
    rw [← unifyRounds_expression_eq_zip (by simpa using hlength)]
    exact hrun
  simpa only [List.zip_cons_cons, List.singleton_append] using
    unifyRounds_prefix_split_of_success hzipped

/-- Successful structural decomposition of two expression argument lists
forces equal arity. -/
theorem length_eq_of_decomposeList_success
    {left right : List Metta.Atom}
    {constraints : List (String × Metta.Atom)}
    (hdecompose : Metta.Unify.decomposeList left right =
      some constraints) :
    left.length = right.length := by
  induction left generalizing right constraints with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          simp [Metta.Unify.decomposeList] at hdecompose
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          simp [Metta.Unify.decomposeList] at hdecompose
      | cons rightHead rightTail =>
          simp only [Metta.Unify.decomposeList] at hdecompose
          cases hhead : Metta.Unify.decomposeEq leftHead rightHead with
          | none => simp [hhead] at hdecompose
          | some headConstraints =>
              cases htail : Metta.Unify.decomposeList leftTail rightTail with
              | none => simp [hhead, htail] at hdecompose
              | some tailConstraints =>
                  have htailLength : leftTail.length = rightTail.length :=
                    ih htail
                  simpa using htailLength

/-- A successful Robinson run on one expression equation therefore also
recovers equal arity; callers need not assume it independently. -/
theorem length_eq_of_unifyRounds_expression_success
    {fuel : Nat} {left right : List Metta.Atom}
    {subst result : Metta.Subst}
    (hrun : Metta.Unify.unifyRounds fuel
      [(.expr left, .expr right)] subst = some result) :
    left.length = right.length := by
  cases hdecompose : Metta.Unify.decomposeList left right with
  | none =>
      cases fuel <;>
        simp [Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
          Metta.Unify.decomposeEq, hdecompose] at hrun
  | some constraints =>
      exact length_eq_of_decomposeList_success hdecompose

mutual

/-- Structural decomposition of a translated HE atom against itself emits no
Robinson constraints.  This includes nested expressions and HE grounded
payloads. -/
theorem decomposeEq_toLeaTTa_self (atom : Atom) :
    Metta.Unify.decomposeEq
      (toLeaTTaAtom atom) (toLeaTTaAtom atom) = some [] := by
  cases atom with
  | symbol name =>
      simp [toLeaTTaAtom, Metta.Unify.decomposeEq]
  | var name =>
      simp [toLeaTTaAtom, Metta.Unify.decomposeEq]
  | grounded value =>
      have hground : Metta.Ground.equiv
          (toLeaTTaGround value) (toLeaTTaGround value) = true := by
        simpa [toLeaTTaAtom, Metta.Atom.equiv] using
          toLeaTTaAtom_grounded_equiv_self value
      simp [toLeaTTaAtom, Metta.Unify.decomposeEq, hground]
  | expression atoms =>
      simp only [toLeaTTaAtom, Metta.Unify.decomposeEq]
      exact decomposeList_toLeaTTa_self atoms
termination_by 2 * sizeOf atom

/-- Pointwise-list companion to reflexive translated decomposition. -/
theorem decomposeList_toLeaTTa_self (atoms : List Atom) :
    Metta.Unify.decomposeList
      (toLeaTTaAtoms atoms) (toLeaTTaAtoms atoms) = some [] := by
  cases atoms with
  | nil => simp [toLeaTTaAtoms, Metta.Unify.decomposeList]
  | cons head tail =>
      simp only [toLeaTTaAtoms, Metta.Unify.decomposeList]
      rw [decomposeEq_toLeaTTa_self, decomposeList_toLeaTTa_self]
      rfl
termination_by 2 * sizeOf atoms + 1
decreasing_by all_goals simp_wf <;> omega

end

/-- HE-to-LeaTTa atom-list translation commutes with append. -/
theorem toLeaTTaAtoms_append (first second : List Atom) :
    toLeaTTaAtoms (first ++ second) =
      toLeaTTaAtoms first ++ toLeaTTaAtoms second := by
  induction first with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, toLeaTTaAtoms, List.cons_append,
        List.cons.injEq, true_and]
      exact ih

/-- Translation preserves list arity. -/
theorem length_toLeaTTaAtoms (atoms : List Atom) :
    (toLeaTTaAtoms atoms).length = atoms.length := by
  induction atoms with
  | nil => rfl
  | cons head tail ih =>
      simp only [toLeaTTaAtoms, List.length_cons, Nat.succ.injEq]
      exact ih

/-- A zipped translated list against itself is structurally solved before
Robinson elimination begins. -/
theorem decomposeAll_zip_toLeaTTa_self (atoms : List Atom) :
    Metta.Unify.decomposeAll
      (List.zip (toLeaTTaAtoms atoms) (toLeaTTaAtoms atoms)) = some [] := by
  induction atoms with
  | nil => simp [toLeaTTaAtoms, Metta.Unify.decomposeAll]
  | cons head tail ih =>
      simp only [toLeaTTaAtoms, List.zip_cons_cons,
        Metta.Unify.decomposeAll]
      rw [decomposeEq_toLeaTTa_self, ih]
      rfl

/-- Robinson execution ignores an identical translated list prefix.  This is
an equation-presentation fact only; the original HE matcher will still replay
those children, including reflexive variable equalities. -/
theorem unifyRounds_zip_drop_translated_common
    (common left right : List Atom) (fuel : Nat) (subst : Metta.Subst) :
    Metta.Unify.unifyRounds fuel
        (List.zip (toLeaTTaAtoms (common ++ left))
          (toLeaTTaAtoms (common ++ right))) subst =
      Metta.Unify.unifyRounds fuel
        (List.zip (toLeaTTaAtoms left) (toLeaTTaAtoms right)) subst := by
  rw [toLeaTTaAtoms_append, toLeaTTaAtoms_append]
  rw [List.zip_append (by rfl)]
  apply unifyRounds_eq_of_decomposeAll_eq
  exact decomposeAll_append_of_left_nil _
    (decomposeAll_zip_toLeaTTa_self common)

/-- Two unequal lists of equal length have a unique-shape first divergence:
some common prefix is followed by unequal heads and equally long residual
tails.  The prefix is kept explicitly because original HE matching must
replay its reflexive children before taking the strict Robinson step. -/
theorem exists_commonPrefix_unequal_heads
    {left right : List Atom}
    (hlength : left.length = right.length)
    (hne : left ≠ right) :
    ∃ common leftHead leftTail rightHead rightTail,
      left = common ++ leftHead :: leftTail ∧
        right = common ++ rightHead :: rightTail ∧
        leftHead ≠ rightHead ∧
        leftTail.length = rightTail.length := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact (hne rfl).elim
      | cons rightHead rightTail => simp at hlength
  | cons leftHead leftTail ih =>
      cases right with
      | nil => simp at hlength
      | cons rightHead rightTail =>
          have htailLength : leftTail.length = rightTail.length := by
            simpa using hlength
          by_cases hhead : leftHead = rightHead
          · subst rightHead
            have htailNe : leftTail ≠ rightTail := by
              intro htail
              exact hne (congrArg (List.cons leftHead) htail)
            obtain ⟨common, first, firstTail, second, secondTail,
                hleft, hright, hfirstNe, hrestLength⟩ :=
              ih htailLength htailNe
            exact ⟨leftHead :: common, first, firstTail, second,
              secondTail, by simp [hleft], by simp [hright],
              hfirstNe, hrestLength⟩
          · exact ⟨[], leftHead, leftTail, rightHead, rightTail,
              rfl, rfl, hhead, htailLength⟩

/-- A successful unequal translated expression equation can be presented at
its first unequal child without changing the Robinson state or fuel.  The
common prefix is returned separately for structural reflexive matching; the
reduced nonempty expression is the point at which strict fuel descent applies.
-/
theorem exists_firstDivergence_unifyRounds_expression_success
    {fuel : Nat} {left right : List Atom} {subst result : Metta.Subst}
    (hne : left ≠ right)
    (hrun : Metta.Unify.unifyRounds fuel
      [(.expr (toLeaTTaAtoms left), .expr (toLeaTTaAtoms right))]
      subst = some result) :
    ∃ common leftHead leftTail rightHead rightTail,
      left = common ++ leftHead :: leftTail ∧
        right = common ++ rightHead :: rightTail ∧
        leftHead ≠ rightHead ∧
        leftTail.length = rightTail.length ∧
        Metta.Unify.unifyRounds fuel
          [(.expr (toLeaTTaAtoms (leftHead :: leftTail)),
            .expr (toLeaTTaAtoms (rightHead :: rightTail)))]
          subst = some result := by
  have htranslatedLength :=
    length_eq_of_unifyRounds_expression_success hrun
  have hlength : left.length = right.length := by
    rw [length_toLeaTTaAtoms, length_toLeaTTaAtoms] at htranslatedLength
    exact htranslatedLength
  obtain ⟨common, leftHead, leftTail, rightHead, rightTail,
      hleft, hright, hheadNe, htailLength⟩ :=
    exists_commonPrefix_unequal_heads hlength hne
  have hzip : Metta.Unify.unifyRounds fuel
      (List.zip (toLeaTTaAtoms left) (toLeaTTaAtoms right)) subst =
        some result := by
    rw [← unifyRounds_expression_eq_zip htranslatedLength]
    exact hrun
  have hdivergenceZip : Metta.Unify.unifyRounds fuel
      (List.zip (toLeaTTaAtoms (leftHead :: leftTail))
        (toLeaTTaAtoms (rightHead :: rightTail))) subst = some result := by
    rw [← unifyRounds_zip_drop_translated_common
      common (leftHead :: leftTail) (rightHead :: rightTail) fuel subst]
    rw [← hleft, ← hright]
    exact hzip
  refine ⟨common, leftHead, leftTail, rightHead, rightTail,
    hleft, hright, hheadNe, htailLength, ?_⟩
  have htailTranslatedLength :
      (toLeaTTaAtoms leftTail).length =
        (toLeaTTaAtoms rightTail).length := by
    rw [length_toLeaTTaAtoms, length_toLeaTTaAtoms]
    exact htailLength
  have hfullTranslatedLength :
      (toLeaTTaAtoms (leftHead :: leftTail)).length =
        (toLeaTTaAtoms (rightHead :: rightTail)).length := by
    simp only [toLeaTTaAtoms, List.length_cons, Nat.succ.injEq]
    exact htailTranslatedLength
  rw [unifyRounds_expression_eq_zip hfullTranslatedLength]
  exact hdivergenceZip

/-- If the original expression's first pointwise equation is unequal, its
exact prefix factorization is strictly smaller than the successful enclosing
expression run.  This is the descent theorem consumed by the original
matcher/list-matcher induction; no canonical matcher record appears. -/
theorem unifyRounds_expression_head_split_strict_of_ne
    {fuel : Nat} {leftHead rightHead : Metta.Atom}
    {leftTail rightTail : List Metta.Atom} {subst result : Metta.Subst}
    (hleftNoFloat : MettaAtomNoFloat leftHead)
    (hrightNoFloat : MettaAtomNoFloat rightHead)
    (hne : leftHead ≠ rightHead)
    (hlength : leftTail.length = rightTail.length)
    (hrun : Metta.Unify.unifyRounds fuel
      [(.expr (leftHead :: leftTail), .expr (rightHead :: rightTail))]
      subst = some result) :
    ∃ remainingFuel tailWork headSubst,
      UnifyRoundsPrefixSplit fuel [(leftHead, rightHead)]
          (List.zip leftTail rightTail) subst
          remainingFuel tailWork headSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork headSubst =
          some result ∧
        remainingFuel < fuel := by
  have hzipped : Metta.Unify.unifyRounds fuel
      ([(leftHead, rightHead)] ++ List.zip leftTail rightTail) subst =
        some result := by
    have hexpression := hrun
    rw [unifyRounds_expression_eq_zip (by simpa using hlength)] at hexpression
    simpa only [List.zip_cons_cons, List.singleton_append] using
      hexpression
  exact unifyRounds_singleton_prefix_split_strict_of_ne
    hleftNoFloat hrightNoFloat hne hzipped

/-- The nontrivial `unifyValues` branch is exactly one Robinson run from the
first class value to every remaining value. -/
theorem unifyValues_cons_cons_success_run
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (hunify : Metta.Bindings.unifyValues
      (first :: second :: rest) = some result) :
    Metta.Unify.unifyRounds
        (first.size + ((second :: rest).map Metta.Atom.size).sum)
        ((second :: rest).map fun value => (first, value)) [] =
      some result := by
  simpa [Metta.Bindings.unifyValues] using hunify

/-- A nonempty local class unifier cannot take Robinson's solved branch.  It
exposes one occurs-clean elimination and a strictly smaller successful run,
independently of which class value happened to be listed first. -/
theorem unifyValues_nonempty_success_elimination
    {first : Metta.Atom} {rest : List Metta.Atom}
    {localHead : String × Metta.Atom} {localTail : Metta.Subst}
    (hunify : Metta.Bindings.unifyValues (first :: rest) =
      some (localHead :: localTail)) :
    ∃ (smallerFuel : Nat) (key : String) (term : Metta.Atom)
        (remaining : List (String × Metta.Atom)),
      smallerFuel < first.size + (rest.map Metta.Atom.size).sum ∧
        first.size + (rest.map Metta.Atom.size).sum = smallerFuel + 1 ∧
        Metta.Unify.decomposeAll
            (rest.map fun value => (first, value)) =
          some ((key, term) :: remaining) ∧
        Metta.Subst.occurs key term = false ∧
        Metta.Unify.unifyRounds smallerFuel
            (remaining.map fun constraint =>
              (Metta.Subst.apply [(key, term)] (.var constraint.1),
                Metta.Subst.apply [(key, term)] constraint.2))
            (Metta.Subst.extend [] key term) =
          some (localHead :: localTail) := by
  cases rest with
  | nil => simp [Metta.Bindings.unifyValues] at hunify
  | cons second rest =>
      have hrun := unifyValues_cons_cons_success_run hunify
      have hpositive :
          0 < first.size + ((second :: rest).map Metta.Atom.size).sum := by
        have hone := Metta.Atom.one_le_size first
        omega
      generalize htotal :
          first.size + ((second :: rest).map Metta.Atom.size).sum =
            totalFuel at hrun ⊢
      cases totalFuel with
      | zero => omega
      | succ totalFuel =>
          have hview := unifyRounds_success_view hrun
          cases hview with
          | solved hdecompose hresult => simp at hresult
          | eliminate hdecompose hoccurs htail =>
              exact ⟨totalFuel, _, _, _, Nat.lt_succ_self totalFuel,
                rfl, hdecompose, hoccurs, htail⟩

/-- Local class reconciliation factors at the first value conflict and
retains the transformed residual class worklist.  This is the operational
index used by recursive HE conflict matching. -/
theorem unifyValues_cons_cons_prefix_split
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (hunify : Metta.Bindings.unifyValues
      (first :: second :: rest) = some result) :
    ∃ remainingFuel tailWork headSubst,
      UnifyRoundsPrefixSplit
          (first.size + ((second :: rest).map Metta.Atom.size).sum)
          [(first, second)]
          (rest.map fun value => (first, value)) []
          remainingFuel tailWork headSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork headSubst =
          some result := by
  have hrun := unifyValues_cons_cons_success_run hunify
  simpa only [List.map_cons, List.singleton_append] using
    unifyRounds_prefix_split_of_success hrun

/-- The local class-reconciliation split is strictly decreasing as soon as
its first value pair decomposes to a real constraint. -/
theorem unifyValues_cons_cons_prefix_split_strict
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst} {constraint : String × Metta.Atom}
    {constraints : List (String × Metta.Atom)}
    (hunify : Metta.Bindings.unifyValues
      (first :: second :: rest) = some result)
    (hdecompose : Metta.Unify.decomposeAll [(first, second)] =
      some (constraint :: constraints)) :
    ∃ remainingFuel tailWork headSubst,
      UnifyRoundsPrefixSplit
          (first.size + ((second :: rest).map Metta.Atom.size).sum)
          [(first, second)]
          (rest.map fun value => (first, value)) []
          remainingFuel tailWork headSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork headSubst =
          some result ∧
        remainingFuel <
          first.size + ((second :: rest).map Metta.Atom.size).sum := by
  obtain ⟨remainingFuel, tailWork, headSubst, hsplit, hcontinue⟩ :=
    unifyValues_cons_cons_prefix_split hunify
  exact ⟨remainingFuel, tailWork, headSubst, hsplit, hcontinue,
    hsplit.remainingFuel_lt_of_decompose_cons hdecompose⟩

/-- Unequal float-free class values therefore make every successful local
reconciliation strictly decrease its Robinson fuel, with no additional
decomposition premise at the call site. -/
theorem unifyValues_cons_cons_prefix_split_strict_of_ne
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (hfirst : MettaAtomNoFloat first)
    (hsecond : MettaAtomNoFloat second)
    (hne : first ≠ second)
    (hunify : Metta.Bindings.unifyValues
      (first :: second :: rest) = some result) :
    ∃ remainingFuel tailWork headSubst,
      UnifyRoundsPrefixSplit
          (first.size + ((second :: rest).map Metta.Atom.size).sum)
          [(first, second)]
          (rest.map fun value => (first, value)) []
          remainingFuel tailWork headSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork headSubst =
          some result ∧
        remainingFuel <
          first.size + ((second :: rest).map Metta.Atom.size).sum := by
  have hrun := unifyValues_cons_cons_success_run hunify
  have hrun' : Metta.Unify.unifyRounds
      (first.size + ((second :: rest).map Metta.Atom.size).sum)
      ([(first, second)] ++ rest.map fun value => (first, value)) [] =
        some result := by
    simpa only [List.map_cons, List.singleton_append] using hrun
  exact unifyRounds_singleton_prefix_split_strict_of_ne
    hfirst hsecond hne hrun'

/-- A solved decomposition has an empty syntactic elimination trace. -/
theorem unificationEliminationTrace_eq_nil_of_decompose_nil
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    (hdecompose : Metta.Unify.decomposeAll equations = some []) :
    unificationEliminationTrace fuel equations = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [unificationEliminationTrace, hdecompose]

/-- An occurs-check-clean elimination is exactly one trace head followed by
the strictly smaller recursive trace. -/
theorem unificationEliminationTrace_succ_eq_cons
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {key : String} {term : Metta.Atom}
    {rest : List (String × Metta.Atom)}
    (hdecompose : Metta.Unify.decomposeAll equations =
      some ((key, term) :: rest))
    (hoccurs : Metta.Subst.occurs key term = false) :
    unificationEliminationTrace (fuel + 1) equations =
      (key, term) ::
        unificationEliminationTrace fuel
          (rest.map fun constraint =>
            (Metta.Subst.apply [(key, term)] (.var constraint.1),
              Metta.Subst.apply [(key, term)] constraint.2)) := by
  simp [unificationEliminationTrace, hdecompose, hoccurs]

/-- The nonempty local-unifier branch exposes the exact head of the selected
Robinson trace together with its strictly smaller successful tail run.  This
is the trace-facing recursion equation consumed by the paired HE/LeaTTa
induction. -/
theorem unifyValues_nonempty_success_trace_step
    {first : Metta.Atom} {rest : List Metta.Atom}
    {localHead : String × Metta.Atom} {localTail : Metta.Subst}
    (hunify : Metta.Bindings.unifyValues (first :: rest) =
      some (localHead :: localTail)) :
    ∃ (smallerFuel : Nat) (key : String) (term : Metta.Atom)
        (remaining : List (String × Metta.Atom)),
      smallerFuel < first.size + (rest.map Metta.Atom.size).sum ∧
        unificationEliminationTrace
            (first.size + (rest.map Metta.Atom.size).sum)
            (rest.map fun value => (first, value)) =
          (key, term) ::
            unificationEliminationTrace smallerFuel
              (remaining.map fun constraint =>
                (Metta.Subst.apply [(key, term)] (.var constraint.1),
                  Metta.Subst.apply [(key, term)] constraint.2)) ∧
        Metta.Unify.unifyRounds smallerFuel
            (remaining.map fun constraint =>
              (Metta.Subst.apply [(key, term)] (.var constraint.1),
                Metta.Subst.apply [(key, term)] constraint.2))
            (Metta.Subst.extend [] key term) =
          some (localHead :: localTail) := by
  obtain ⟨smallerFuel, key, term, remaining, hlt, htotal,
      hdecompose, hoccurs, hrun⟩ :=
    unifyValues_nonempty_success_elimination hunify
  refine ⟨smallerFuel, key, term, remaining, hlt, ?_, hrun⟩
  rw [htotal]
  exact unificationEliminationTrace_succ_eq_cons hdecompose hoccurs

/-- Like `unifyRounds`, the selected elimination trace depends on the input
equation presentation only through its fully decomposed constraints. -/
theorem unificationEliminationTrace_eq_of_decomposeAll_eq
    {fuel : Nat} {left right : List (Metta.Atom × Metta.Atom)}
    (hdecompose : Metta.Unify.decomposeAll left =
      Metta.Unify.decomposeAll right) :
    unificationEliminationTrace fuel left =
      unificationEliminationTrace fuel right := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [unificationEliminationTrace]
      rw [hdecompose]

/-- A singleton expression equation and its pointwise zipped presentation have
the same selected Robinson trace.  This is the trace counterpart of
`unifyRounds_expression_eq_zip`; it records no normalization or MGU claim. -/
theorem unificationEliminationTrace_expression_eq_zip
    {fuel : Nat} {left right : List Metta.Atom}
    (hlength : left.length = right.length) :
    unificationEliminationTrace fuel [(.expr left, .expr right)] =
      unificationEliminationTrace fuel (List.zip left right) := by
  apply unificationEliminationTrace_eq_of_decomposeAll_eq
  rw [decomposeAll_zip_eq_decomposeList left right hlength]
  cases hdecompose : Metta.Unify.decomposeList left right <;>
    simp [Metta.Unify.decomposeAll, Metta.Unify.decomposeEq, hdecompose]

/-- The selected Robinson trace ignores an identical translated list prefix,
just as the executable run does.  The common children remain available to the
original structural matcher; only their solved equation presentation vanishes
from the elimination trace. -/
theorem unificationEliminationTrace_zip_drop_translated_common
    (common left right : List Atom) (fuel : Nat) :
    unificationEliminationTrace fuel
        (List.zip (toLeaTTaAtoms (common ++ left))
          (toLeaTTaAtoms (common ++ right))) =
      unificationEliminationTrace fuel
        (List.zip (toLeaTTaAtoms left) (toLeaTTaAtoms right)) := by
  rw [toLeaTTaAtoms_append, toLeaTTaAtoms_append]
  rw [List.zip_append (by rfl)]
  apply unificationEliminationTrace_eq_of_decomposeAll_eq
  exact decomposeAll_append_of_left_nil _
    (decomposeAll_zip_toLeaTTa_self common)

/-- Dropping an identical original child prefix preserves the complete trace
of the enclosing translated expression equation. -/
theorem unificationEliminationTrace_expression_drop_translated_common
    (common left right : List Atom) (fuel : Nat)
    (hlength : left.length = right.length) :
    unificationEliminationTrace fuel
        [(.expr (toLeaTTaAtoms (common ++ left)),
          .expr (toLeaTTaAtoms (common ++ right)))] =
      unificationEliminationTrace fuel
        [(.expr (toLeaTTaAtoms left), .expr (toLeaTTaAtoms right))] := by
  rw [unificationEliminationTrace_expression_eq_zip (by
    simp only [length_toLeaTTaAtoms, List.length_append]
    omega)]
  rw [unificationEliminationTrace_expression_eq_zip (by
    simpa only [length_toLeaTTaAtoms] using hlength)]
  exact unificationEliminationTrace_zip_drop_translated_common
    common left right fuel

/-- Prefix factorization partitions the selected solve trace exactly: its
initial segment is the trace produced by running the prefix alone, and the
suffix is the trace of the transformed residual worklist. -/
theorem UnifyRoundsPrefixSplit.trace_append
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst) :
    unificationEliminationTrace fuel (front ++ suffix) =
      unificationEliminationTrace fuel front ++
        unificationEliminationTrace remainingFuel suffixWork := by
  induction h with
  | @solved fuel front suffix subst hfront =>
      have hfrontTrace : unificationEliminationTrace fuel front = [] :=
        unificationEliminationTrace_eq_nil_of_decompose_nil hfront
      rw [hfrontTrace, List.nil_append]
      apply unificationEliminationTrace_eq_of_decomposeAll_eq
      exact decomposeAll_append_of_left_nil suffix hfront
  | @eliminate fuel front suffix subst key term rest suffixConstraints
      remainingFuel suffixWork prefixSubst hfront hsuffix hoccurs htail ih =>
      have hall := decomposeAll_append front suffix
      rw [hfront, hsuffix] at hall
      simp only at hall
      rw [unificationEliminationTrace_succ_eq_cons hall hoccurs]
      rw [unificationEliminationTrace_succ_eq_cons hfront hoccurs]
      let transform := fun constraint : String × Metta.Atom =>
        (Metta.Subst.apply [(key, term)] (.var constraint.1),
          Metta.Subst.apply [(key, term)] constraint.2)
      have htrace' : unificationEliminationTrace fuel
          (rest.map transform ++ suffixConstraints.map transform) =
            unificationEliminationTrace fuel (rest.map transform) ++
              unificationEliminationTrace remainingFuel suffixWork := by
        simpa [transform] using ih
      change (key, term) :: unificationEliminationTrace fuel
          ((rest ++ suffixConstraints).map transform) = _
      rw [List.map_append, htrace']
      rfl

/-- Existential presentation retained for callers that want to abstract over
the concrete prefix trace. -/
theorem UnifyRoundsPrefixSplit.exists_trace_append
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst) :
    ∃ prefixTrace,
      unificationEliminationTrace fuel (front ++ suffix) =
        prefixTrace ++
          unificationEliminationTrace remainingFuel suffixWork :=
  ⟨unificationEliminationTrace fuel front, h.trace_append⟩

/-- If the selected prefix initially exposes a real Robinson constraint, its
trace contribution is nonempty.  The returned equation keeps the exact
transformed residual worklist from the operational prefix split; no trace
entry is paired by list position. -/
theorem UnifyRoundsPrefixSplit.exists_nonempty_trace_append
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst)
    {constraint : String × Metta.Atom}
    {rest : List (String × Metta.Atom)}
    (hfront : Metta.Unify.decomposeAll front =
      some (constraint :: rest)) :
    ∃ entry prefixTail,
      unificationEliminationTrace fuel (front ++ suffix) =
        entry :: prefixTail ++
          unificationEliminationTrace remainingFuel suffixWork := by
  cases h with
  | @solved fuel front suffix subst hsolved =>
      rw [hsolved] at hfront
      cases hfront
  | @eliminate fuel front suffix subst key term eliminatedRest
      suffixConstraints remainingFuel suffixWork prefixSubst
      hselected hsuffix hoccurs htail =>
      obtain ⟨prefixTail, htrace⟩ := htail.exists_trace_append
      refine ⟨(key, term), prefixTail, ?_⟩
      have hall := decomposeAll_append front suffix
      rw [hselected, hsuffix] at hall
      simp only at hall
      rw [unificationEliminationTrace_succ_eq_cons hall hoccurs]
      let transform := fun item : String × Metta.Atom =>
        (Metta.Subst.apply [(key, term)] (.var item.1),
          Metta.Subst.apply [(key, term)] item.2)
      have htrace' : unificationEliminationTrace fuel
          (eliminatedRest.map transform ++
            suffixConstraints.map transform) =
          prefixTail ++
            unificationEliminationTrace remainingFuel suffixWork := by
        simpa [transform] using htrace
      change (key, term) :: unificationEliminationTrace fuel
          ((eliminatedRest ++ suffixConstraints).map transform) = _
      rw [List.map_append, htrace']
      rfl

/-- An unequal float-free first class-value conflict contributes a nonempty
trace prefix and leaves a strictly smaller exact residual Robinson state.
This is the recursion interface consumed by the value-expression progress
constructor. -/
theorem unifyValues_cons_cons_nonempty_trace_split_of_ne
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (hfirst : MettaAtomNoFloat first)
    (hsecond : MettaAtomNoFloat second)
    (hne : first ≠ second)
    (hunify : Metta.Bindings.unifyValues
      (first :: second :: rest) = some result) :
    ∃ remainingFuel tailWork headSubst entry prefixTail,
      UnifyRoundsPrefixSplit
          (first.size + ((second :: rest).map Metta.Atom.size).sum)
          [(first, second)]
          (rest.map fun value => (first, value)) []
          remainingFuel tailWork headSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork headSubst =
          some result ∧
        remainingFuel <
          first.size + ((second :: rest).map Metta.Atom.size).sum ∧
        unificationEliminationTrace
            (first.size + ((second :: rest).map Metta.Atom.size).sum)
            ((second :: rest).map fun value => (first, value)) =
          entry :: prefixTail ++
            unificationEliminationTrace remainingFuel tailWork := by
  obtain ⟨remainingFuel, tailWork, headSubst, hsplit,
      hcontinue, hlt⟩ :=
    unifyValues_cons_cons_prefix_split_strict_of_ne
      hfirst hsecond hne hunify
  have hrun := unifyValues_cons_cons_success_run hunify
  have hrun' : Metta.Unify.unifyRounds
      (first.size + ((second :: rest).map Metta.Atom.size).sum)
      ([(first, second)] ++
        rest.map fun value => (first, value)) [] = some result := by
    simpa only [List.map_cons, List.singleton_append] using hrun
  obtain ⟨headResult, hheadRun⟩ :=
    exists_unifyRounds_prefix_success hrun'
  obtain ⟨constraint, constraints, hdecompose⟩ :=
    exists_decomposeAll_singleton_cons_of_success
      hfirst hsecond hne hheadRun
  obtain ⟨entry, prefixTail, htrace⟩ :=
    hsplit.exists_nonempty_trace_append hdecompose
  refine ⟨remainingFuel, tailWork, headSubst, entry, prefixTail,
    hsplit, hcontinue, hlt, ?_⟩
  simpa only [List.map_cons, List.singleton_append] using htrace

/-- Singleton substitution can only retain variables from the source atom or
introduce variables from the replacement. -/
private theorem mem_vars_apply_singleton
    {key : String} {replacement : Metta.Atom} :
    ∀ (atom : Metta.Atom) {name : String},
      name ∈ (Metta.Subst.apply [(key, replacement)] atom).vars →
        name ∈ atom.vars ∨ name ∈ replacement.vars := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro symbol name hmem
    simp [Metta.Subst.apply, Metta.Atom.vars] at hmem
  · intro sourceVar name hmem
    by_cases hvariable : sourceVar = key
    · subst sourceVar
      exact Or.inr (by
        simpa [Metta.Subst.apply, Metta.Subst.lookup] using hmem)
    · have hbeq : (sourceVar == key) = false := by simp [hvariable]
      left
      simpa [Metta.Subst.apply, Metta.Subst.lookup, hbeq,
        Metta.Atom.vars] using hmem
  · intro ground name hmem
    simp [Metta.Subst.apply, Metta.Atom.vars] at hmem
  · intro atoms ih name hmem
    simp only [Metta.Subst.apply, Metta.Atom.vars,
      List.mem_flatten] at hmem
    obtain ⟨appliedVars, happliedVars, hname⟩ := hmem
    obtain ⟨applied, happlied, rfl⟩ := List.mem_map.mp happliedVars
    obtain ⟨atom, hatom, rfl⟩ := List.mem_map.mp happlied
    rcases ih atom hatom hname with hsource | hreplacement
    · left
      simp only [Metta.Atom.vars, List.mem_flatten]
      exact ⟨atom.vars, List.mem_map.mpr ⟨atom, hatom, rfl⟩,
        hsource⟩
    · exact Or.inr hreplacement

/-- The substituted worklist of one Robinson round mentions only variables
already present in the decomposed source worklist. -/
private theorem remainingEquationVars_subset_source
    {equations : List (Metta.Atom × Metta.Atom)}
    {key : String} {term : Metta.Atom}
    {rest : List (String × Metta.Atom)}
    (hdecompose :
      Metta.Unify.decomposeAll equations = some ((key, term) :: rest)) :
    let remaining := rest.map fun constraint =>
      (Metta.Subst.apply [(key, term)] (.var constraint.1),
        Metta.Subst.apply [(key, term)] constraint.2)
    ∀ name ∈ mettaEquationVars remaining,
      name ∈ mettaEquationVars equations := by
  dsimp only
  intro name hname
  simp only [mettaEquationVars, List.mem_flatMap] at hname
  obtain ⟨equation, hequation, hname⟩ := hname
  obtain ⟨constraint, hconstraint, rfl⟩ := List.mem_map.mp hequation
  have htermSource : ∀ sourceVar ∈ term.vars,
      sourceVar ∈ mettaEquationVars equations := by
    intro sourceVar hvariable
    apply decomposeAll_constraintVars_subset hdecompose sourceVar
    simp [mettaConstraintVars, hvariable]
  have hconstraintSource :
      ∀ sourceVar ∈ constraint.1 :: constraint.2.vars,
        sourceVar ∈ mettaEquationVars equations := by
    intro sourceVar hvariable
    apply decomposeAll_constraintVars_subset hdecompose sourceVar
    unfold mettaConstraintVars
    apply List.mem_flatMap.mpr
    exact ⟨constraint, by simp [hconstraint], hvariable⟩
  simp only [List.mem_append] at hname
  rcases hname with hleft | hright
  · rcases mem_vars_apply_singleton (.var constraint.1) hleft with
      hsource | hreplacement
    · have hnameEq : name = constraint.1 := by
        simpa [Metta.Atom.vars] using hsource
      exact hconstraintSource name (by simp [hnameEq])
    · exact htermSource name hreplacement
  · rcases mem_vars_apply_singleton constraint.2 hright with
      hsource | hreplacement
    · exact hconstraintSource name (List.mem_cons.mpr (Or.inr hsource))
    · exact htermSource name hreplacement

/-- Every variable occurring in the selected solve trace came from the
worklist on which that trace started. -/
theorem unificationEliminationTrace_constraintVars_subset
    (fuel : Nat) (equations : List (Metta.Atom × Metta.Atom)) :
    ∀ name ∈ mettaConstraintVars
        (unificationEliminationTrace fuel equations),
      name ∈ mettaEquationVars equations := by
  induction fuel generalizing equations with
  | zero => simp [unificationEliminationTrace, mettaConstraintVars]
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [unificationEliminationTrace, hdecompose,
            mettaConstraintVars]
      | some constraints =>
          cases constraints with
          | nil =>
              simp [unificationEliminationTrace, hdecompose,
                mettaConstraintVars]
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  simp [unificationEliminationTrace, hdecompose, hoccurs,
                    mettaConstraintVars]
              | false =>
                  let remaining := rest.map fun constraint =>
                    (Metta.Subst.apply [(key, term)] (.var constraint.1),
                      Metta.Subst.apply [(key, term)] constraint.2)
                  simp only [unificationEliminationTrace, hdecompose,
                    hoccurs]
                  intro name hname
                  change name ∈
                    (key :: term.vars) ++
                      mettaConstraintVars
                        (unificationEliminationTrace fuel remaining) at hname
                  rw [List.mem_append] at hname
                  rcases hname with hhead | htail
                  · apply decomposeAll_constraintVars_subset hdecompose name
                    simp only [mettaConstraintVars, List.flatMap_cons,
                      List.mem_append]
                    exact Or.inl hhead
                  · apply remainingEquationVars_subset_source hdecompose name
                    exact ih remaining name htail

/-- A solve trace is triangular when each eliminated key is absent from every
later key and term.  This is an operational invariant of the successful
Robinson loop, not a representative-order convention. -/
def EliminationTraceTriangular :
    List (String × Metta.Atom) → Prop
  | [] => True
  | binding :: trace =>
      binding.1 ∉ mettaConstraintVars trace ∧
        EliminationTraceTriangular trace

/-- Triangularity is inherited by every left prefix. -/
theorem EliminationTraceTriangular.left_of_append
    {frontTrace suffix : List (String × Metta.Atom)}
    (h : EliminationTraceTriangular (frontTrace ++ suffix)) :
    EliminationTraceTriangular frontTrace := by
  induction frontTrace with
  | nil => simp [EliminationTraceTriangular]
  | cons binding frontTrace ih =>
      simp only [List.cons_append, EliminationTraceTriangular] at h ⊢
      refine ⟨?_, ih h.2⟩
      intro hmem
      apply h.1
      simpa [mettaConstraintVars] using
        (List.mem_append_left (mettaConstraintVars suffix) hmem)

/-- A triangular trace has distinct eliminated keys. -/
theorem EliminationTraceTriangular.keys_nodup
    {trace : List (String × Metta.Atom)}
    (h : EliminationTraceTriangular trace) :
    (trace.map Prod.fst).Nodup := by
  induction trace with
  | nil => simp
  | cons binding trace ih =>
      simp only [EliminationTraceTriangular] at h
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih h.2⟩
      intro hkey
      obtain ⟨tailBinding, htail, heq⟩ := List.mem_map.mp hkey
      apply h.1
      unfold mettaConstraintVars
      apply List.mem_flatMap.mpr
      exact ⟨tailBinding, htail, by simp [heq]⟩

/-- Every successful fresh-state Robinson run produces a triangular solve
trace.  In particular, replaying the trace from tail to head always introduces
an isolated key. -/
theorem unificationEliminationTrace_triangular_of_success
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hfresh : UnifyStateFresh equations subst)
    (hrun : Metta.Unify.unifyRounds fuel equations subst = some result) :
    EliminationTraceTriangular
      (unificationEliminationTrace fuel equations) := by
  induction fuel generalizing equations subst result with
  | zero =>
      simp [unificationEliminationTrace, EliminationTraceTriangular]
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              simp [unificationEliminationTrace, hdecompose,
                EliminationTraceTriangular]
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  simp [Metta.Unify.unifyRounds, hdecompose, hoccurs] at hrun
              | false =>
                  let remaining := rest.map fun constraint =>
                    (Metta.Subst.apply [(key, term)] (.var constraint.1),
                      Metta.Subst.apply [(key, term)] constraint.2)
                  have hrun' :
                      Metta.Unify.unifyRounds fuel remaining
                          (Metta.Subst.extend subst key term) = some result := by
                    simpa [Metta.Unify.unifyRounds, hdecompose, hoccurs,
                      remaining] using hrun
                  have hfresh' :
                      UnifyStateFresh remaining
                        (Metta.Subst.extend subst key term) := by
                    simpa [remaining] using
                      (unifyRound_preserves_freshness
                        hdecompose hoccurs hfresh)
                  have hkeyRecorded :
                      key ∈ mettaSubstKeys
                        (Metta.Subst.extend subst key term) := by
                    simp [Metta.Subst.extend, mettaSubstKeys]
                  have hkeyAbsent : key ∉
                      mettaConstraintVars
                        (unificationEliminationTrace fuel remaining) := by
                    intro hkey
                    exact hfresh' key hkeyRecorded
                      (unificationEliminationTrace_constraintVars_subset
                        fuel remaining key hkey)
                  have htraceEq :
                      unificationEliminationTrace (fuel + 1) equations =
                        (key, term) ::
                          unificationEliminationTrace fuel remaining := by
                    simp [unificationEliminationTrace, hdecompose, hoccurs,
                      remaining]
                  rw [htraceEq]
                  simp only [EliminationTraceTriangular]
                  exact ⟨hkeyAbsent, ih hfresh' hrun'⟩

/-- Whole-binding reconciliation inherits triangularity because it runs the
Robinson loop from the empty substitution. -/
theorem wholeBindingReconciliation_eliminationTrace_triangular
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    EliminationTraceTriangular
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra)) := by
  have hrun :
      Metta.Unify.unifyRounds
          (Metta.Bindings.equationFuel
            (Metta.Bindings.equations bindings ++ extra))
          (Metta.Bindings.equations bindings ++ extra) [] = some result := by
    simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll] using
      hreconcile
  exact unificationEliminationTrace_triangular_of_success
    (by simp [UnifyStateFresh, mettaSubstKeys]) hrun

/-- Every selected elimination key passes the occurs check against its own
term.  Unlike triangularity, this fact needs no successful final run: a failed
occurs check contributes no trace entry. -/
theorem unificationEliminationTrace_key_not_mem_value_vars
    (fuel : Nat) (equations : List (Metta.Atom × Metta.Atom)) :
    ∀ key value,
      (key, value) ∈ unificationEliminationTrace fuel equations →
        key ∉ value.vars := by
  induction fuel generalizing equations with
  | zero =>
      simp [unificationEliminationTrace]
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none => simp [unificationEliminationTrace, hdecompose]
      | some constraints =>
          cases constraints with
          | nil => simp [unificationEliminationTrace, hdecompose]
          | cons constraint rest =>
              rcases constraint with ⟨selectedKey, selectedValue⟩
              cases hoccurs : Metta.Subst.occurs selectedKey selectedValue with
              | true =>
                  simp [unificationEliminationTrace, hdecompose, hoccurs]
              | false =>
                  let remaining := rest.map fun constraint =>
                    (Metta.Subst.apply [(selectedKey, selectedValue)]
                        (.var constraint.1),
                      Metta.Subst.apply [(selectedKey, selectedValue)]
                        constraint.2)
                  have htraceEq :
                      unificationEliminationTrace (fuel + 1) equations =
                        (selectedKey, selectedValue) ::
                          unificationEliminationTrace fuel remaining := by
                    simp [unificationEliminationTrace, hdecompose, hoccurs,
                      remaining]
                  intro key value hmem
                  rw [htraceEq] at hmem
                  simp only [List.mem_cons, Prod.mk.injEq] at hmem
                  rcases hmem with hhead | htail
                  · rcases hhead with ⟨rfl, rfl⟩
                    exact not_mem_vars_of_occurs_eq_false _ _ hoccurs
                  · exact ih remaining key value htail

/-- Canonical HE replay of a repaired-LeaTTa solve trace.  The replay records
only the two binding effects certified above; it does not impose the trace's
list order as a semantic requirement on an executable matcher output. -/
inductive LeaEliminationTraceReplay
    (base : Bindings) :
    List (String × Metta.Atom) → Bindings → Prop where
  | nil : LeaEliminationTraceReplay base [] base
  | aliasStep {trace : List (String × Metta.Atom)} {b : Bindings}
      {key target : String} :
      LeaEliminationTraceReplay base trace b →
      LeaEliminationTraceReplay base
        ((key, .var target) :: trace) (b.addEquality key target)
  | valueStep {trace : List (String × Metta.Atom)} {b : Bindings}
      {key : String} {value : Atom} {leaValue : Metta.Atom} :
      LeaEliminationTraceReplay base trace b →
      b.lookup key = none →
      HELeaAtomClassRel b value leaValue →
      (∀ target, leaValue ≠ .var target) →
      LeaEliminationTraceReplay base
        ((key, leaValue) :: trace) (b.assign key value)

/-- Variable edges selected by the elimination trace. -/
def eliminationTraceAliases :
    List (String × Metta.Atom) → List (String × String)
  | [] => []
  | (key, .var target) :: trace =>
      (key, target) :: eliminationTraceAliases trace
  | _ :: trace => eliminationTraceAliases trace

@[simp] theorem eliminationTraceAliases_append
    (left right : List (String × Metta.Atom)) :
    eliminationTraceAliases (left ++ right) =
      eliminationTraceAliases left ++ eliminationTraceAliases right := by
  induction left with
  | nil => rfl
  | cons binding left ih =>
      rcases binding with ⟨key, value⟩
      cases value <;> simp [eliminationTraceAliases, ih]

@[simp] theorem eliminationTraceAliases_reverse
    (trace : List (String × Metta.Atom)) :
    eliminationTraceAliases trace.reverse =
      (eliminationTraceAliases trace).reverse := by
  induction trace with
  | nil => rfl
  | cons binding trace ih =>
      rcases binding with ⟨key, value⟩
      cases value <;> simp [eliminationTraceAliases, ih]

/-- `ofSubst` retains exactly the variable entries as explicit equality
edges.  This is a presentation equality internal to repaired LeaTTa; the
cross-engine proof subsequently quotients it to graph reachability. -/
theorem leaEqualityEdges_ofSubst_eq_eliminationTraceAliases
    (subst : Metta.Subst) :
    leaEqualityEdges (Metta.Bindings.ofSubst subst) =
      eliminationTraceAliases subst := by
  induction subst with
  | nil => rfl
  | cons binding subst ih =>
      rcases binding with ⟨key, value⟩
      change leaEqualityEdges
          ((match value with
            | .var target => Metta.BindingRel.eq key target
            | stored => Metta.BindingRel.val key stored) ::
            Metta.Bindings.ofSubst subst) =
        eliminationTraceAliases ((key, value) :: subst)
      cases value <;>
        simp [leaEqualityEdges, eliminationTraceAliases, ih]

@[simp] theorem mem_eliminationTraceAliases_iff
    {trace : List (String × Metta.Atom)} {key target : String} :
    (key, target) ∈ eliminationTraceAliases trace ↔
      (key, .var target) ∈ trace := by
  induction trace with
  | nil => simp [eliminationTraceAliases]
  | cons binding trace ih =>
      rcases binding with ⟨traceKey, value⟩
      cases value <;> simp [eliminationTraceAliases, ih]

/-- Internal replay order is the reverse solve order: each newly exposed
alias is appended after the seed equality graph.  This equality is an
operational certificate only; all cross-engine conclusions quotient it to
reachability. -/
theorem LeaEliminationTraceReplay.equalities_from_base
    {base : Bindings} {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay base trace out) :
    out.equalities =
      base.equalities ++ (eliminationTraceAliases trace).reverse := by
  induction h with
  | nil => simp [eliminationTraceAliases]
  | aliasStep h ih =>
      simp [Bindings.addEquality, eliminationTraceAliases, ih,
        List.append_assoc]
  | @valueStep trace b key value leaValue h hlookup hatom hnonvar ih =>
      cases leaValue with
      | var target => exact (hnonvar target rfl).elim
      | sym symbol | gnd symbol | expr symbol =>
          simpa [Bindings.assign, eliminationTraceAliases] using ih

/-- Empty-seed specialization of `equalities_from_base`. -/
theorem LeaEliminationTraceReplay.equalities
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out) :
    out.equalities = (eliminationTraceAliases trace).reverse := by
  simpa [Bindings.empty] using h.equalities_from_base

/-- Consequently a replay's equality classes are exactly the seed graph plus
the graph generated by its selected variable constraints, independent of the
internal edge-list order. -/
theorem LeaEliminationTraceReplay.eqClass_iff_from_base
    {base : Bindings} {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay base trace out)
    (start finish : String) :
    finish ∈ out.eqClass start ↔
      (EqualityClosure.edgeGraph
        (base.equalities ++
          (eliminationTraceAliases trace).reverse)).Reachable start finish := by
  rw [EqualityClosure.mem_eqClass_iff_reachable, h.equalities_from_base]

/-- Empty-seed specialization of `eqClass_iff_from_base`. -/
theorem LeaEliminationTraceReplay.eqClass_iff
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (start finish : String) :
    finish ∈ out.eqClass start ↔
      (EqualityClosure.edgeGraph
        (eliminationTraceAliases trace).reverse).Reachable start finish := by
  simpa [Bindings.empty] using h.eqClass_iff_from_base start finish

/-- A canonical empty-seed trace replay stays inside any alias graph that
contains every selected variable constraint. -/
theorem LeaEliminationTraceReplay.equalityClosureBound
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    {allowed : List (String × String)}
    (hsubset : ∀ edge ∈ eliminationTraceAliases trace,
      edge ∈ allowed) :
    HEEqualityClosureBound out allowed := by
  intro start finish hclass
  have hreach := (h.eqClass_iff start finish).mp hclass
  apply hreach.mono
  intro left right hadj
  rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
  rcases hadj with ⟨hne, hforward | hreverse⟩
  · exact ⟨hne, Or.inl (hsubset (left, right)
      (by simpa using (List.mem_reverse.mp hforward)))⟩
  · exact ⟨hne, Or.inr (hsubset (right, left)
      (by simpa using (List.mem_reverse.mp hreverse)))⟩

/-- The canonical replay of every complete trace from empty bindings carries
the full structural trace certificate. -/
theorem LeaEliminationTraceReplay.structural
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out) :
    LeaEliminationTraceStructuralRel out trace := by
  induction h with
  | nil => exact LeaEliminationTraceStructuralRel.empty
  | aliasStep h ih => exact ih.variable
  | valueStep h hlookup hatom hnonvar ih =>
      exact ih.nonvar hlookup hatom hnonvar

/-- Canonical replay never manufactures a bare-variable assignment.  Such a
Robinson entry is represented by an equality edge, and the class-relative
atom witness cannot change a non-variable trace payload into an HE variable. -/
theorem LeaEliminationTraceReplay.assignmentsNonVariable
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out) :
    HEAssignmentsNonVariable out := by
  intro key target hmem
  obtain ⟨leaKey, leaValue, _htrace, hnonvar, _hclass, hatom⟩ :=
    h.structural.classValues.1 key (.var target) hmem
  cases hatom
  all_goals simp_all

/-- Replay composes with an existing trace certificate.  This is the full
trace-lifting theorem used by the paired induction: each non-variable step
adds one class-relative assignment, and each variable step adds one class
edge, while the seed certificate remains valid by closure monotonicity. -/
theorem LeaEliminationTraceReplay.structural_from
    {base : Bindings} {trace seedTrace : List (String × Metta.Atom)}
    {out : Bindings}
    (h : LeaEliminationTraceReplay base trace out)
    (hbase : LeaEliminationTraceStructuralRel base seedTrace) :
    LeaEliminationTraceStructuralRel out (trace ++ seedTrace) := by
  induction h with
  | nil => simpa using hbase
  | aliasStep h ih =>
      simpa only [List.cons_append] using ih.variable
  | valueStep h hlookup hatom hnonvar ih =>
      simpa only [List.cons_append] using
        ih.nonvar hlookup hatom hnonvar

theorem LeaEliminationTraceReplay.assignmentKey_mem
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    {key : String} {value : Atom}
    (hmem : (key, value) ∈ out.assignments) :
    key ∈ trace.map Prod.fst := by
  induction h with
  | nil => simp [Bindings.empty] at hmem
  | aliasStep h ih =>
      simp only [List.map_cons, List.mem_cons]
      exact Or.inr (ih (by
        simpa [Bindings.addEquality] using hmem))
  | @valueStep trace b traceKey heValue leaValue h hlookup hatom hnonvar ih =>
      have hbound : b.isBound traceKey = false := by
        simp [Bindings.isBound, hlookup]
      simp only [Bindings.assign, hbound, Bool.false_eq_true, if_false,
        List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
      simp only [List.map_cons, List.mem_cons]
      rcases hmem with hold | hnew
      · exact Or.inr (ih hold)
      · exact Or.inl hnew.1

/-- Every HE assignment in a trace replay comes from a non-variable solve
entry with the same key. -/
theorem LeaEliminationTraceReplay.assignment_mem_trace_nonvar
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    {key : String} {value : Atom}
    (hmem : (key, value) ∈ out.assignments) :
    ∃ leaValue,
      (key, leaValue) ∈ trace ∧
        ∀ target, leaValue ≠ .var target := by
  induction h with
  | nil => simp [Bindings.empty] at hmem
  | @aliasStep trace b traceKey target h ih =>
      obtain ⟨leaValue, htrace, hnonvar⟩ := ih (by
        simpa [Bindings.addEquality] using hmem)
      exact ⟨leaValue, List.mem_cons_of_mem _ htrace, hnonvar⟩
  | @valueStep trace b traceKey heValue leaValue h hlookup hatom hnonvar ih =>
      have hbound : b.isBound traceKey = false := by
        simp [Bindings.isBound, hlookup]
      simp only [Bindings.assign, hbound, Bool.false_eq_true, if_false,
        List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨stored, htrace, hstoredNonvar⟩ := ih hold
        exact ⟨stored, List.mem_cons_of_mem _ htrace, hstoredNonvar⟩
      · rcases hnew with ⟨rfl, rfl⟩
        exact ⟨leaValue, by simp, hnonvar⟩

/-- Canonical trace replay preserves uniqueness of direct assignment keys. -/
theorem LeaEliminationTraceReplay.assignmentsNodup
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out) :
    AssignmentsNodup out := by
  induction h with
  | nil => exact AssignmentsNodup.empty
  | aliasStep h ih =>
      unfold AssignmentsNodup at ih ⊢
      simpa [Bindings.addEquality] using ih
  | valueStep h hlookup hatom hnonvar ih =>
      exact AssignmentsNodup.assign ih

private theorem traceKey_mem_constraintVars
    {trace : List (String × Metta.Atom)} {key : String}
    (hkey : key ∈ trace.map Prod.fst) :
    key ∈ mettaConstraintVars trace := by
  obtain ⟨binding, hbinding, hkey⟩ := List.mem_map.mp hkey
  unfold mettaConstraintVars
  apply List.mem_flatMap.mpr
  exact ⟨binding, hbinding, by simp [hkey]⟩

private theorem eliminationAlias_endpoints_mem_constraintVars
    {trace : List (String × Metta.Atom)} {left right : String}
    (hedge : (left, right) ∈ eliminationTraceAliases trace) :
    left ∈ mettaConstraintVars trace ∧
      right ∈ mettaConstraintVars trace := by
  have htrace : (left, Metta.Atom.var right) ∈ trace :=
    mem_eliminationTraceAliases_iff.mp hedge
  unfold mettaConstraintVars
  constructor <;> apply List.mem_flatMap.mpr
  · exact ⟨(left, Metta.Atom.var right), htrace, by simp⟩
  · exact ⟨(left, Metta.Atom.var right), htrace,
      by simp [Metta.Atom.vars]⟩

/-- Follow the directed alias forest presented by a solve trace.  Triangular
traces point only toward later keys, so this fold gives a canonical component
root without choosing an HE equality-class representative. -/
def eliminationTraceRoot :
    List (String × Metta.Atom) → String → String
  | [], name => name
  | (key, .var target) :: trace, name =>
      if name = key then eliminationTraceRoot trace target
      else eliminationTraceRoot trace name
  | _ :: trace, name => eliminationTraceRoot trace name

private theorem eliminationTraceRoot_eq_self_of_not_mem_keys
    {trace : List (String × Metta.Atom)} {name : String}
    (hname : name ∉ trace.map Prod.fst) :
    eliminationTraceRoot trace name = name := by
  induction trace with
  | nil => rfl
  | cons binding trace ih =>
      rcases binding with ⟨key, value⟩
      have hne : name ≠ key := by
        intro heq
        subst name
        exact hname (by simp)
      have htail : name ∉ trace.map Prod.fst := by
        intro hmem
        exact hname (by simp [hmem])
      cases value <;> simp [eliminationTraceRoot, hne, ih htail]

private theorem eliminationTraceRoot_eq_of_mem_alias
    {trace : List (String × Metta.Atom)}
    (htriangular : EliminationTraceTriangular trace)
    {left right : String}
    (hedge : (left, right) ∈ eliminationTraceAliases trace) :
    eliminationTraceRoot trace left =
      eliminationTraceRoot trace right := by
  induction trace generalizing left right with
  | nil => simp [eliminationTraceAliases] at hedge
  | cons binding trace ih =>
      rcases binding with ⟨key, value⟩
      rcases htriangular with ⟨hkeyFresh, htailTriangular⟩
      cases value with
      | var target =>
          simp only [eliminationTraceAliases, List.mem_cons,
            Prod.mk.injEq] at hedge
          rcases hedge with hhead | htail
          · rcases hhead with ⟨hleft, hright⟩
            subst left
            subst right
            simp [eliminationTraceRoot]
          · have hleft : left ≠ key := by
              intro heq
              subst left
              exact hkeyFresh
                (eliminationAlias_endpoints_mem_constraintVars htail).1
            have hright : right ≠ key := by
              intro heq
              subst right
              exact hkeyFresh
                (eliminationAlias_endpoints_mem_constraintVars htail).2
            simpa [eliminationTraceRoot, hleft, hright] using
              ih htailTriangular htail
      | sym symbol | gnd symbol | expr symbol =>
          simp only [eliminationTraceAliases] at hedge
          simpa [eliminationTraceRoot] using
            ih htailTriangular hedge

private theorem eliminationTraceRoot_eq_self_of_mem_nonvar
    {trace : List (String × Metta.Atom)}
    (htriangular : EliminationTraceTriangular trace)
    {key : String} {value : Metta.Atom}
    (hmem : (key, value) ∈ trace)
    (hnonvar : ∀ target, value ≠ .var target) :
    eliminationTraceRoot trace key = key := by
  induction trace generalizing key value with
  | nil => simp at hmem
  | cons binding trace ih =>
      rcases binding with ⟨headKey, headValue⟩
      rcases htriangular with ⟨hheadFresh, htailTriangular⟩
      by_cases hhead : (key, value) = (headKey, headValue)
      · have hkeyEq : key = headKey := congrArg Prod.fst hhead
        have hvalueEq : value = headValue := congrArg Prod.snd hhead
        subst headKey
        subst headValue
        have hnotTail : key ∉ trace.map Prod.fst := by
          intro hkey
          exact hheadFresh (traceKey_mem_constraintVars hkey)
        cases value with
        | var target => exact (hnonvar target rfl).elim
        | sym symbol | gnd symbol | expr symbol =>
            simpa [eliminationTraceRoot] using
              eliminationTraceRoot_eq_self_of_not_mem_keys hnotTail
      · have htail : (key, value) ∈ trace :=
          (List.mem_cons.mp hmem).resolve_left hhead
        have hne : key ≠ headKey := by
          intro heq
          subst key
          exact hheadFresh
            (traceKey_mem_constraintVars
              (List.mem_map.mpr ⟨(headKey, value), htail, rfl⟩))
        cases headValue with
        | var target =>
            simpa [eliminationTraceRoot, hne] using
              ih htailTriangular htail hnonvar
        | sym symbol | gnd symbol | expr symbol =>
            simpa [eliminationTraceRoot] using
              ih htailTriangular htail hnonvar

private theorem eliminationTraceRoot_eq_of_reachable
    {trace : List (String × Metta.Atom)}
    (htriangular : EliminationTraceTriangular trace)
    {start finish : String}
    (hreach : (EqualityClosure.edgeGraph
      (eliminationTraceAliases trace).reverse).Reachable start finish) :
    eliminationTraceRoot trace start =
      eliminationTraceRoot trace finish := by
  apply hreach.elim
  intro walk
  induction walk with
  | nil => rfl
  | @cons start next finish hadj tail ih =>
      rw [EqualityClosure.edgeGraph_adj_iff] at hadj
      have hstep : eliminationTraceRoot trace start =
          eliminationTraceRoot trace next := by
        rcases hadj.2 with hforward | hreverse
        · apply eliminationTraceRoot_eq_of_mem_alias htriangular
          exact List.mem_reverse.mp hforward
        · symm
          apply eliminationTraceRoot_eq_of_mem_alias htriangular
          exact List.mem_reverse.mp hreverse
      exact hstep.trans (ih tail.reachable)

/-- Two non-variable solve entries in one alias component are the same entry.
This is the forest property that prevents canonical replay from manufacturing
multiple raw values in one equality class. -/
private theorem nonvar_trace_keys_eq_of_reachable
    {trace : List (String × Metta.Atom)}
    (htriangular : EliminationTraceTriangular trace)
    {leftKey rightKey : String} {leftValue rightValue : Metta.Atom}
    (hleft : (leftKey, leftValue) ∈ trace)
    (hright : (rightKey, rightValue) ∈ trace)
    (hleftNonvar : ∀ target, leftValue ≠ .var target)
    (hrightNonvar : ∀ target, rightValue ≠ .var target)
    (hreach : (EqualityClosure.edgeGraph
      (eliminationTraceAliases trace).reverse).Reachable
        leftKey rightKey) :
    leftKey = rightKey := by
  have hroots := eliminationTraceRoot_eq_of_reachable
    htriangular hreach
  rw [eliminationTraceRoot_eq_self_of_mem_nonvar
      htriangular hleft hleftNonvar,
    eliminationTraceRoot_eq_self_of_mem_nonvar
      htriangular hright hrightNonvar] at hroots
  exact hroots

private def insertEqVar (names : List String) (name : String) :
    List String :=
  if names.contains name then names else names ++ [name]

private theorem insertEqVar_nodup
    {names : List String} (hnames : names.Nodup)
    (name : String) :
    (insertEqVar names name).Nodup := by
  unfold insertEqVar
  by_cases hmem : name ∈ names
  · have hcontains : names.contains name = true := by simpa
    rw [if_pos hcontains]
    exact hnames
  · have hcontains : ¬ names.contains name = true := by simpa
    rw [if_neg hcontains, List.nodup_append]
    refine ⟨hnames, by simp, ?_⟩
    intro stored hstored appended happended heq
    simp only [List.mem_singleton] at happended
    subst appended
    subst stored
    exact hmem hstored

private theorem eqVarsInOrder_nodup (b : Bindings) :
    b.eqVarsInOrder.Nodup := by
  unfold Bindings.eqVarsInOrder
  change (b.equalities.foldl (fun names edge =>
    insertEqVar (insertEqVar names edge.1) edge.2) []).Nodup
  have hfold : ∀ (edges : List (String × String)) names,
      names.Nodup →
        (edges.foldl (fun current edge =>
          insertEqVar (insertEqVar current edge.1) edge.2)
          names).Nodup := by
    intro edges
    induction edges with
    | nil => intro names hnames; exact hnames
    | cons edge edges ih =>
        intro names hnames
        rw [List.foldl_cons]
        apply ih
        exact insertEqVar_nodup
          (insertEqVar_nodup hnames edge.1) edge.2
  exact hfold b.equalities [] (by simp)

private theorem eqClassOrdered_nodup (b : Bindings) (name : String) :
    (b.eqClassOrdered name).Nodup := by
  unfold Bindings.eqClassOrdered
  generalize hfiltered :
      b.eqVarsInOrder.filter (fun other =>
        (b.eqClass name).contains other) = filtered
  have hnodup : filtered.Nodup := by
    rw [← hfiltered]
    exact (eqVarsInOrder_nodup b).filter _
  cases filtered with
  | nil => simp
  | cons first rest => exact hnodup

private theorem filterMap_length_le_one_of_unique
    {key value : Type} {items : List key} {lookup : key → Option value}
    (hitems : items.Nodup)
    (hunique : ∀ left ∈ items, ∀ right ∈ items,
      ∀ leftValue rightValue,
        lookup left = some leftValue →
          lookup right = some rightValue → left = right) :
    (items.filterMap lookup).length ≤ 1 := by
  induction items with
  | nil => simp
  | cons item items ih =>
      have hitemFresh : item ∉ items := (List.nodup_cons.mp hitems).1
      have htailNodup : items.Nodup := (List.nodup_cons.mp hitems).2
      cases hlookup : lookup item with
      | none =>
          simp only [List.filterMap_cons, hlookup]
          apply ih htailNodup
          intro left hleft right hright leftValue rightValue
            hleftLookup hrightLookup
          exact hunique left (by simp [hleft]) right (by simp [hright])
            leftValue rightValue hleftLookup hrightLookup
      | some itemValue =>
          have htailEmpty : items.filterMap lookup = [] := by
            apply List.filterMap_eq_nil_iff.mpr
            intro other hother
            cases hotherLookup : lookup other with
            | none => rfl
            | some otherValue =>
                exfalso
                apply hitemFresh
                have heq := hunique item (by simp) other (by simp [hother])
                  itemValue otherValue hlookup hotherLookup
                simpa [heq] using hother
          simp [hlookup, htailEmpty]

/-- Every class in a triangular canonical replay carries at most one direct
raw value.  The proof factors through the directed solve-trace forest rather
than the order of either engine's equality list. -/
theorem LeaEliminationTraceReplay.classValues_length_le_one
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace)
    (name : String) :
    (out.classValues name).length ≤ 1 := by
  unfold Bindings.classValues
  apply filterMap_length_le_one_of_unique
    (eqClassOrdered_nodup out name)
  intro left hleft right hright leftValue rightValue
    hleftLookup hrightLookup
  have hleftAssignment : (left, leftValue) ∈ out.assignments :=
    assignment_mem_of_lookup_eq_some (by
      simpa [Bindings.lookup] using hleftLookup)
  have hrightAssignment : (right, rightValue) ∈ out.assignments :=
    assignment_mem_of_lookup_eq_some (by
      simpa [Bindings.lookup] using hrightLookup)
  obtain ⟨leftLeaValue, hleftTrace, hleftNonvar⟩ :=
    h.assignment_mem_trace_nonvar hleftAssignment
  obtain ⟨rightLeaValue, hrightTrace, hrightNonvar⟩ :=
    h.assignment_mem_trace_nonvar hrightAssignment
  have hnameLeft :
      (EqualityClosure.edgeGraph
        (eliminationTraceAliases trace).reverse).Reachable name left :=
    (h.eqClass_iff name left).mp
      (EqualityClosure.mem_eqClassOrdered_iff.mp hleft)
  have hnameRight :
      (EqualityClosure.edgeGraph
        (eliminationTraceAliases trace).reverse).Reachable name right :=
    (h.eqClass_iff name right).mp
      (EqualityClosure.mem_eqClassOrdered_iff.mp hright)
  exact nonvar_trace_keys_eq_of_reachable htriangular
    hleftTrace hrightTrace hleftNonvar hrightNonvar
      (hnameLeft.symm.trans hnameRight)

/-- Hence all raw class values in a triangular replay are structurally
consistent. -/
theorem LeaEliminationTraceReplay.valuesConsistent
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace)
    (name : String) :
    Bindings.valuesConsistent (out.classValues name) = true := by
  have hlength := h.classValues_length_le_one htriangular name
  cases hvalues : out.classValues name with
  | nil => simp [Bindings.valuesConsistent]
  | cons first rest =>
      cases rest with
      | nil => simp [Bindings.valuesConsistent]
      | cons second rest =>
          rw [hvalues] at hlength
          simp at hlength

/-- Every subrecord of a triangular replay that retains all assignments and
only forgets equality edges still has at most one value in each class.  This
is the prefix-stability fact needed when `mergeBindings` replays assignments
before equalities. -/
theorem LeaEliminationTraceReplay.valuesConsistent_of_equality_subrecord
    {trace : List (String × Metta.Atom)} {out candidate : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace)
    (hassignments : candidate.assignments = out.assignments)
    (hequalities : ∀ edge ∈ candidate.equalities,
      edge ∈ out.equalities)
    (name : String) :
    Bindings.valuesConsistent (candidate.classValues name) = true := by
  have hlength : (candidate.classValues name).length ≤ 1 := by
    unfold Bindings.classValues
    apply filterMap_length_le_one_of_unique
      (eqClassOrdered_nodup candidate name)
    intro left hleft right hright leftValue rightValue
      hleftLookup hrightLookup
    have hleftAssignment : (left, leftValue) ∈ out.assignments := by
      rw [← hassignments]
      exact assignment_mem_of_lookup_eq_some (by
        simpa [Bindings.lookup] using hleftLookup)
    have hrightAssignment : (right, rightValue) ∈ out.assignments := by
      rw [← hassignments]
      exact assignment_mem_of_lookup_eq_some (by
        simpa [Bindings.lookup] using hrightLookup)
    obtain ⟨leftLeaValue, hleftTrace, hleftNonvar⟩ :=
      h.assignment_mem_trace_nonvar hleftAssignment
    obtain ⟨rightLeaValue, hrightTrace, hrightNonvar⟩ :=
      h.assignment_mem_trace_nonvar hrightAssignment
    have liftReachability : ∀ {start finish : String},
        (EqualityClosure.edgeGraph candidate.equalities).Reachable
            start finish →
          (EqualityClosure.edgeGraph out.equalities).Reachable
            start finish := by
      intro start finish hreach
      apply hreach.mono
      intro first second hadj
      rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
      rcases hadj with ⟨hne, hforward | hreverse⟩
      · exact ⟨hne, Or.inl (hequalities _ hforward)⟩
      · exact ⟨hne, Or.inr (hequalities _ hreverse)⟩
    have hnameLeft :
        (EqualityClosure.edgeGraph
          (eliminationTraceAliases trace).reverse).Reachable name left := by
      apply (h.eqClass_iff name left).mp
      rw [EqualityClosure.mem_eqClass_iff_reachable]
      apply liftReachability
      rw [← EqualityClosure.mem_eqClass_iff_reachable]
      exact EqualityClosure.mem_eqClassOrdered_iff.mp hleft
    have hnameRight :
        (EqualityClosure.edgeGraph
          (eliminationTraceAliases trace).reverse).Reachable name right := by
      apply (h.eqClass_iff name right).mp
      rw [EqualityClosure.mem_eqClass_iff_reachable]
      apply liftReachability
      rw [← EqualityClosure.mem_eqClass_iff_reachable]
      exact EqualityClosure.mem_eqClassOrdered_iff.mp hright
    exact nonvar_trace_keys_eq_of_reachable htriangular
      hleftTrace hrightTrace hleftNonvar hrightNonvar
        (hnameLeft.symm.trans hnameRight)
  cases hvalues : candidate.classValues name with
  | nil => simp [Bindings.valuesConsistent]
  | cons first rest =>
      cases rest with
      | nil => simp [Bindings.valuesConsistent]
      | cons second rest =>
          rw [hvalues] at hlength
          simp at hlength

/-! ## Full replay through the public merge surface -/

/-- Folding a fresh, key-disjoint assignment suffix into an equality-free
seed recreates the suffix by the declarative merge relation. -/
private theorem mergeAssignsRel_append_fresh
    (seed : Bindings) : ∀ (rest : List (String × Atom)),
    seed.equalities = [] →
    (rest.map Prod.fst).Nodup →
    (∀ key, key ∈ rest.map Prod.fst → seed.lookup key = none) →
    MergeAssignsRel seed rest
      ⟨seed.assignments ++ rest, []⟩ := by
  intro rest
  induction rest generalizing seed with
  | nil =>
      intro hequalities hkeys hfresh
      have hseed : seed = ⟨seed.assignments, []⟩ := by
        cases seed
        simp_all
      simpa only [List.append_nil, ← hseed] using
        (MergeAssignsRel.nil (acc := seed))
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      intro hequalities hkeys hfresh
      have hkeyLookup : seed.lookup key = none :=
        hfresh key (by simp)
      have hkeyClass : seed.classValues key = [] := by
        rw [Bindings.classValues_no_equalities hequalities, hkeyLookup]
        rfl
      have hbound : seed.isBound key = false := by
        simp [Bindings.isBound, hkeyLookup]
      have hkeyFresh : key ∉ rest.map Prod.fst :=
        (List.nodup_cons.mp hkeys).1
      have hrestKeys : (rest.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hkeys).2
      have hnextEqualities : (seed.assign key value).equalities = [] := by
        simpa [Bindings.assign, hbound] using hequalities
      have hnextFresh : ∀ other,
          other ∈ rest.map Prod.fst →
            (seed.assign key value).lookup other = none := by
        intro other hother
        have hotherNe : other ≠ key := by
          intro heq
          subst other
          exact hkeyFresh hother
        rw [assign_lookup_ne seed key value other hotherNe hkeyLookup]
        exact hfresh other (by simp [hother])
      apply MergeAssignsRel.cons (.fresh hkeyClass)
      simpa [Bindings.assign, hbound, List.append_assoc] using
        (ih (seed := seed.assign key value) hnextEqualities
          hrestKeys hnextFresh)

/-- The fresh-assignment fold above carries a derivation-local trace
certificate for every trace: it contains no recursive matcher calls. -/
private theorem exists_mergeAssignsTraceSound_append_fresh
    (trace : List (String × Metta.Atom))
    (seed : Bindings) : ∀ (rest : List (String × Atom)),
    seed.equalities = [] →
    (rest.map Prod.fst).Nodup →
    (∀ key, key ∈ rest.map Prod.fst → seed.lookup key = none) →
    ∃ out,
      out = ⟨seed.assignments ++ rest, []⟩ ∧
        ∃ hrel : MergeAssignsRel seed rest out,
          MergeAssignsTraceSound trace hrel := by
  intro rest
  induction rest generalizing seed with
  | nil =>
      intro hequalities hkeys hfresh
      have hseed : seed = ⟨seed.assignments, []⟩ := by
        cases seed
        simp_all
      exact ⟨seed, by simpa only [List.append_nil] using hseed,
        MergeAssignsRel.nil,
        MergeAssignsTraceSound.nil⟩
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      intro hequalities hkeys hfresh
      have hkeyLookup : seed.lookup key = none :=
        hfresh key (by simp)
      have hkeyClass : seed.classValues key = [] := by
        rw [Bindings.classValues_no_equalities hequalities, hkeyLookup]
        rfl
      have hbound : seed.isBound key = false := by
        simp [Bindings.isBound, hkeyLookup]
      have hkeyFresh : key ∉ rest.map Prod.fst :=
        (List.nodup_cons.mp hkeys).1
      have hrestKeys : (rest.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hkeys).2
      have hnextEqualities : (seed.assign key value).equalities = [] := by
        simpa [Bindings.assign, hbound] using hequalities
      have hnextFresh : ∀ other,
          other ∈ rest.map Prod.fst →
            (seed.assign key value).lookup other = none := by
        intro other hother
        have hotherNe : other ≠ key := by
          intro heq
          subst other
          exact hkeyFresh hother
        rw [assign_lookup_ne seed key value other hotherNe hkeyLookup]
        exact hfresh other (by simp [hother])
      obtain ⟨tailOut, htailOut, htail, htailSound⟩ :=
        ih (seed := seed.assign key value) hnextEqualities
          hrestKeys hnextFresh
      let hadd : AddVarBindingRel seed key value
          (seed.assign key value) := AddVarBindingRel.fresh hkeyClass
      let hrel : MergeAssignsRel seed ((key, value) :: rest) tailOut :=
        MergeAssignsRel.cons hadd htail
      have haddSound : AddVarBindingTraceSound trace hadd := by
        exact AddVarBindingTraceSound.fresh
          (value := value) (hclass := hkeyClass)
      refine ⟨tailOut, ?_, hrel, ?_⟩
      · calc
          tailOut =
              ⟨(seed.assign key value).assignments ++ rest, []⟩ :=
            htailOut
          _ = ⟨seed.assignments ++ ((key, value) :: rest), []⟩ := by
            simp [Bindings.assign, hbound, List.append_assoc]
      · exact MergeAssignsTraceSound.cons haddSound htailSound

/-- Replaying a suffix of the final equality list is declaratively valid:
every intermediate prefix is an equality subrecord of the triangular final
replay, so its class-value consistency check succeeds. -/
private theorem LeaEliminationTraceReplay.mergeEqsRel_of_suffix
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace) :
    ∀ {acc : Bindings} (rest : List (String × String)),
      acc.assignments = out.assignments →
      out.equalities = acc.equalities ++ rest →
      MergeEqsRel acc rest out := by
  intro acc rest
  induction rest generalizing acc with
  | nil =>
      intro hassignments hequalities
      have hacc : acc = out := by
        cases acc
        cases out
        simp_all
      subst acc
      exact .nil
  | cons edge rest ih =>
      rcases edge with ⟨left, right⟩
      intro hassignments hequalities
      let next := acc.addEquality left right
      have hnextAssignments : next.assignments = out.assignments := by
        simpa [next, Bindings.addEquality] using hassignments
      have hnextEqualities :
          out.equalities = next.equalities ++ rest := by
        simpa [next, Bindings.addEquality, List.append_assoc] using hequalities
      have hsubset : ∀ equality ∈ next.equalities,
          equality ∈ out.equalities := by
        intro equality hequality
        rw [hnextEqualities]
        exact List.mem_append_left rest hequality
      have hconsistent :
          Bindings.valuesConsistent (next.classValues left) = true :=
        h.valuesConsistent_of_equality_subrecord htriangular
          hnextAssignments hsubset left
      exact .cons (.consistent hconsistent)
        (ih (acc := next) hnextAssignments hnextEqualities)

/-- The consistent-equality suffix fold likewise carries a local trace
certificate for every trace, because no recursive matcher constructor occurs
in the selected derivation. -/
private theorem LeaEliminationTraceReplay.exists_mergeEqsTraceSound_of_suffix
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace)
    (certificateTrace : List (String × Metta.Atom)) :
    ∀ {acc : Bindings} (rest : List (String × String)),
      acc.assignments = out.assignments →
      out.equalities = acc.equalities ++ rest →
      ∃ result,
        result = out ∧
          ∃ hrel : MergeEqsRel acc rest result,
            MergeEqsTraceSound certificateTrace hrel := by
  intro acc rest
  induction rest generalizing acc with
  | nil =>
      intro hassignments hequalities
      have hacc : acc = out := by
        cases acc
        cases out
        simp_all
      exact ⟨acc, hacc, MergeEqsRel.nil, MergeEqsTraceSound.nil⟩
  | cons edge rest ih =>
      rcases edge with ⟨left, right⟩
      intro hassignments hequalities
      let next := acc.addEquality left right
      have hnextAssignments : next.assignments = out.assignments := by
        simpa [next, Bindings.addEquality] using hassignments
      have hnextEqualities :
          out.equalities = next.equalities ++ rest := by
        simpa [next, Bindings.addEquality, List.append_assoc] using hequalities
      have hsubset : ∀ equality ∈ next.equalities,
          equality ∈ out.equalities := by
        intro equality hequality
        rw [hnextEqualities]
        exact List.mem_append_left rest hequality
      have hconsistent :
          Bindings.valuesConsistent (next.classValues left) = true :=
        h.valuesConsistent_of_equality_subrecord htriangular
          hnextAssignments hsubset left
      obtain ⟨result, hresult, htail, htailSound⟩ :=
        ih (acc := next) hnextAssignments hnextEqualities
      let hadd : AddVarEqualityRel acc left right next :=
        AddVarEqualityRel.consistent hconsistent
      let hrel : MergeEqsRel acc ((left, right) :: rest) result :=
        MergeEqsRel.cons hadd htail
      have haddSound : AddVarEqualityTraceSound certificateTrace hadd :=
        AddVarEqualityTraceSound.consistent (hconsistent := hconsistent)
      exact ⟨result, hresult, hrel,
        MergeEqsTraceSound.cons haddSound htailSound⟩

/-- A triangular canonical trace replay is not merely assembled by successful
individual insertions: the complete record is an official declarative
`mergeBindings` result from the empty seed. -/
theorem LeaEliminationTraceReplay.mergeRel_empty_left
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace) :
    MergeRel Bindings.empty out out := by
  let mid : Bindings := ⟨out.assignments, []⟩
  have hassigns : MergeAssignsRel Bindings.empty out.assignments mid := by
    apply mergeAssignsRel_append_fresh Bindings.empty out.assignments
    · rfl
    · exact h.assignmentsNodup
    · intro key hkey
      simp [Bindings.empty, Bindings.lookup]
  have hequalities : MergeEqsRel mid out.equalities out := by
    apply h.mergeEqsRel_of_suffix htriangular out.equalities
    · rfl
    · simp [mid]
  exact .mk hassigns hequalities

/-- The canonical empty-left replay merge has a derivation-local certificate
for any ambient trace.  Its chosen relation proof uses only fresh assignment
insertions followed by consistent equality insertions, so no recursive
matcher premise is needed. -/
theorem LeaEliminationTraceReplay.exists_mergeTraceSound_empty_left
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace)
    (certificateTrace : List (String × Metta.Atom)) :
    ∃ hrel : MergeRel Bindings.empty out out,
      MergeTraceSound certificateTrace hrel := by
  obtain ⟨midOut, hmidOut, hassigns, hassignsSound⟩ :=
    exists_mergeAssignsTraceSound_append_fresh
      certificateTrace Bindings.empty out.assignments
      (by rfl) h.assignmentsNodup
      (by
        intro key hkey
        simp [Bindings.empty, Bindings.lookup])
  obtain ⟨result, hresult, hequalities, hequalitiesSound⟩ :=
    h.exists_mergeEqsTraceSound_of_suffix htriangular
      certificateTrace (acc := midOut) out.equalities
      (by
        rw [hmidOut]
        simp [Bindings.empty])
      (by
        rw [hmidOut]
        simp)
  subst result
  let hrel : MergeRel Bindings.empty out out :=
    MergeRel.mk hassigns hequalities
  exact ⟨hrel, MergeTraceSound.mk hassignsSound hequalitiesSound⟩

/-- Certificate for the previously exposed canonical relation proof.  Proof
irrelevance is used only to identify two proofs of the same declarative merge,
not to identify binding presentations or matcher MGUs. -/
theorem LeaEliminationTraceReplay.mergeTraceSound_empty_left
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace) :
    MergeTraceSound trace (h.mergeRel_empty_left htriangular) := by
  obtain ⟨hrel, hsound⟩ :=
    h.exists_mergeTraceSound_empty_left htriangular trace
  simpa only [Subsingleton.elim hrel
    (h.mergeRel_empty_left htriangular)] using hsound

/-- Consequently the full replay is returned by the executable HE merge
surface at some finite fuel. -/
theorem LeaEliminationTraceReplay.mem_mergeBindings_empty_left
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace) :
    ∃ fuel, out ∈ mergeBindings Bindings.empty out fuel :=
  mergeBindings_complete (h.mergeRel_empty_left htriangular)

/-- Executable empty-left replay witness paired with the local provenance
certificate for its exact declarative soundness derivation. -/
theorem LeaEliminationTraceReplay.exists_mem_mergeBindings_empty_left_traceSound
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace) :
    ∃ (fuel : Nat) (hmem : out ∈
        mergeBindings Bindings.empty out fuel),
      MergeTraceSound trace (mergeBindings_sound hmem) := by
  obtain ⟨fuel, hmem⟩ := h.mem_mergeBindings_empty_left htriangular
  exact ⟨fuel, hmem, by
    simpa only [Subsingleton.elim (mergeBindings_sound hmem)
      (h.mergeRel_empty_left htriangular)] using
        h.mergeTraceSound_empty_left htriangular⟩

/-- Ambient-trace generalization of the executable canonical replay.  Since
the selected derivation has no recursive matcher calls, its local certificate
is valid relative to any larger reconciliation trace in which this replay is
used as a prefix. -/
theorem LeaEliminationTraceReplay.exists_mem_mergeBindings_empty_left_traceSound_for
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace)
    (certificateTrace : List (String × Metta.Atom)) :
    ∃ (fuel : Nat) (hmem : out ∈
        mergeBindings Bindings.empty out fuel),
      MergeTraceSound certificateTrace (mergeBindings_sound hmem) := by
  obtain ⟨hrel, hsound⟩ :=
    h.exists_mergeTraceSound_empty_left htriangular certificateTrace
  obtain ⟨fuel, hmem⟩ := mergeBindings_complete hrel
  exact ⟨fuel, hmem, by
    simpa only [Subsingleton.elim (mergeBindings_sound hmem) hrel] using
      hsound⟩

private theorem not_mem_edgeNodes_eliminationTraceAliases
    {trace : List (String × Metta.Atom)} {key : String}
    (hkey : key ∉ mettaConstraintVars trace) :
    key ∉ EqualityClosure.edgeNodes
      (eliminationTraceAliases trace).reverse := by
  intro hnode
  simp only [EqualityClosure.edgeNodes, List.mem_flatMap] at hnode
  obtain ⟨edge, hedge, hendpoint⟩ := hnode
  have hedge' : edge ∈ eliminationTraceAliases trace := by
    simpa using (List.mem_reverse.mp hedge)
  rcases edge with ⟨left, right⟩
  simp at hendpoint
  rcases hendpoint with rfl | rfl
  ·
    exact hkey
      (eliminationAlias_endpoints_mem_constraintVars hedge').1
  ·
    exact hkey
      (eliminationAlias_endpoints_mem_constraintVars hedge').2

private theorem reachable_eq_of_start_not_mem_edgeNodes
    {edges : List (String × String)} {start finish : String}
    (hstart : start ∉ EqualityClosure.edgeNodes edges)
    (hreach : (EqualityClosure.edgeGraph edges).Reachable start finish) :
    finish = start := by
  apply hreach.elim
  intro walk
  cases walk with
  | nil => rfl
  | @cons start next finish hadj tail =>
      exfalso
      apply hstart
      rw [EqualityClosure.edgeGraph_adj_iff] at hadj
      rcases hadj.2 with hforward | hreverse
      · exact EqualityClosure.left_mem_edgeNodes hforward
      · exact EqualityClosure.right_mem_edgeNodes hreverse

/-- A variable absent from every key and term in a replay trace has no direct
assignment in the replay output. -/
theorem LeaEliminationTraceReplay.lookup_eq_none_of_not_mem_constraintVars
    {trace : List (String × Metta.Atom)} {out : Bindings} {key : String}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (hkey : key ∉ mettaConstraintVars trace) :
    out.lookup key = none := by
  cases hlookup : out.lookup key with
  | none => rfl
  | some value =>
      have hmem : (key, value) ∈ out.assignments :=
        assignment_mem_of_lookup_eq_some (by
          simpa [Bindings.lookup] using hlookup)
      exact (hkey
        (traceKey_mem_constraintVars (h.assignmentKey_mem hmem))).elim

/-- A variable absent from every key and term in a replay trace is an isolated,
valueless equality class in the replay output. -/
theorem LeaEliminationTraceReplay.classValues_eq_nil_of_not_mem_constraintVars
    {trace : List (String × Metta.Atom)} {out : Bindings} {key : String}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (hkey : key ∉ mettaConstraintVars trace) :
    out.classValues key = [] := by
  unfold Bindings.classValues
  apply List.filterMap_eq_nil_iff.mpr
  intro classKey hordered
  have hclass : classKey ∈ out.eqClass key :=
    EqualityClosure.mem_eqClassOrdered_iff.mp hordered
  have hreach :
      (EqualityClosure.edgeGraph
        (eliminationTraceAliases trace).reverse).Reachable key classKey :=
    (h.eqClass_iff key classKey).mp hclass
  have hclassKey : classKey = key :=
    reachable_eq_of_start_not_mem_edgeNodes
      (not_mem_edgeNodes_eliminationTraceAliases hkey) hreach
  subst classKey
  exact h.lookup_eq_none_of_not_mem_constraintVars hkey

/-- A triangular non-variable solve step is an actual HE fresh insertion at
fuel one, not merely a low-level record construction. -/
theorem LeaEliminationTraceReplay.valueStep_mem_addVarBinding
    {trace : List (String × Metta.Atom)} {b : Bindings}
    {key : String} {value : Atom} {leaValue : Metta.Atom}
    (h : LeaEliminationTraceReplay Bindings.empty trace b)
    (hkey : key ∉ mettaConstraintVars trace)
    (hatom : HELeaAtomClassRel b value leaValue)
    (hnonvar : ∀ target, leaValue ≠ .var target) :
    b.assign key value ∈ addVarBinding b key value 1 ∧
      LeaEliminationTraceReplay Bindings.empty
        ((key, leaValue) :: trace) (b.assign key value) := by
  have hvalues : b.classValues key = [] :=
    h.classValues_eq_nil_of_not_mem_constraintVars hkey
  constructor
  · simp [addVarBinding, hvalues]
  · exact .valueStep h
      (h.lookup_eq_none_of_not_mem_constraintVars hkey) hatom hnonvar

/-- Once the joined class values are structurally consistent, a triangular
variable solve step is likewise an actual HE equality insertion at fuel one.
The remaining paired induction has to establish this consistency from the
successful tail trace; no presentation equality is assumed here. -/
theorem LeaEliminationTraceReplay.aliasStep_mem_addVarEquality
    {trace : List (String × Metta.Atom)} {b : Bindings}
    {key target : String}
    (h : LeaEliminationTraceReplay Bindings.empty trace b)
    (hconsistent : Bindings.valuesConsistent
      ((b.addEquality key target).classValues key) = true) :
    b.addEquality key target ∈ addVarEquality b key target 1 ∧
      LeaEliminationTraceReplay Bindings.empty
        ((key, .var target) :: trace) (b.addEquality key target) := by
  constructor
  · simp [addVarEquality, hconsistent]
  · exact .aliasStep h

/-- A triangular variable solve step always passes HE's executable class-value
consistency check.  This removes the last side condition separating the
canonical trace replay from an actual `addVarEquality` result. -/
theorem LeaEliminationTraceReplay.aliasStep_mem_addVarEquality_of_triangular
    {trace : List (String × Metta.Atom)} {b : Bindings}
    {key target : String}
    (h : LeaEliminationTraceReplay Bindings.empty trace b)
    (htriangular : EliminationTraceTriangular
      ((key, .var target) :: trace)) :
    b.addEquality key target ∈ addVarEquality b key target 1 ∧
      LeaEliminationTraceReplay Bindings.empty
        ((key, .var target) :: trace) (b.addEquality key target) := by
  apply h.aliasStep_mem_addVarEquality
  exact (LeaEliminationTraceReplay.aliasStep h).valuesConsistent
    htriangular key

/-- A canonical elimination-trace replay whose every step is witnessed by the
corresponding executable HE insertion.  The constructors follow reverse solve
order, exactly as the replay above, while retaining membership in the real HE
operation at every intermediate binding set. -/
inductive LeaEliminationTraceExecutableReplay
    (base : Bindings) :
    List (String × Metta.Atom) → Bindings → Prop where
  | nil : LeaEliminationTraceExecutableReplay base [] base
  | aliasStep {trace : List (String × Metta.Atom)} {b : Bindings}
      {key target : String} :
      LeaEliminationTraceExecutableReplay base trace b →
      b.addEquality key target ∈ addVarEquality b key target 1 →
      LeaEliminationTraceExecutableReplay base
        ((key, .var target) :: trace) (b.addEquality key target)
  | valueStep {trace : List (String × Metta.Atom)} {b : Bindings}
      {key : String} {value : Atom} {leaValue : Metta.Atom} :
      LeaEliminationTraceExecutableReplay base trace b →
      b.lookup key = none →
      HELeaAtomClassRel b value leaValue →
      (∀ target, leaValue ≠ .var target) →
      b.assign key value ∈ addVarBinding b key value 1 →
      LeaEliminationTraceExecutableReplay base
        ((key, leaValue) :: trace) (b.assign key value)

/-- Forget executable membership and recover the underlying canonical replay. -/
theorem LeaEliminationTraceExecutableReplay.replay
    {base : Bindings} {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceExecutableReplay base trace out) :
    LeaEliminationTraceReplay base trace out := by
  induction h with
  | nil => exact .nil
  | aliasStep h hstep ih => exact .aliasStep ih
  | valueStep h hlookup hatom hnonvar hstep ih =>
      exact .valueStep ih hlookup hatom hnonvar

/-- Accumulator-threaded list matching composes at its intermediate binding.
The mutual recursor is used so that the suffix seed follows the dependent
output index of each recursive tail. -/
private theorem matchListAccRel_append
    {left right : List Atom} {seed mid : Bindings}
    (hprefix : DeclMatchSpec.MatchListAccRel left right seed mid)
    {suffixLeft suffixRight : List Atom} {out : Bindings}
    (hsuffix : DeclMatchSpec.MatchListAccRel
      suffixLeft suffixRight mid out) :
    DeclMatchSpec.MatchListAccRel
      (left ++ suffixLeft) (right ++ suffixRight) seed out := by
  let AtomMotive := fun (atomLeft atomRight : Atom) (matched : Bindings)
      (_ : DeclMatchSpec.MatchRel atomLeft atomRight matched) => True
  let ListMotive := fun
      (prefixLeft prefixRight : List Atom) (prefixSeed prefixOut : Bindings)
      (_ : DeclMatchSpec.MatchListAccRel
        prefixLeft prefixRight prefixSeed prefixOut) =>
      ∀ {tailLeft tailRight : List Atom} {final : Bindings},
        DeclMatchSpec.MatchListAccRel tailLeft tailRight prefixOut final →
        DeclMatchSpec.MatchListAccRel
          (prefixLeft ++ tailLeft) (prefixRight ++ tailRight)
          prefixSeed final
  refine DeclMatchSpec.MatchListAccRel.rec
    (motive_1 := AtomMotive) (motive_2 := ListMotive)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by
      intro prefixSeed tailLeft tailRight final htail
      simpa [ListMotive] using htail)
    (by
      intro headLeft headRight tailLeft tailRight prefixSeed headOut
        nextSeed prefixOut fuel hhead hmerge htail _ ihtail
        suffixLeft suffixRight final hsuffix
      exact .cons hhead hmerge (ihtail hsuffix))
    hprefix hsuffix

/-- Extend an accumulator-threaded declarative list match by one final atom
pair.  This is the list-control companion to reverse-order trace replay. -/
private theorem matchListAccRel_snoc
    {left right : List Atom} {seed mid : Bindings}
    (hprefix : DeclMatchSpec.MatchListAccRel left right seed mid)
    {nextLeft nextRight : Atom} {matched out : Bindings} {fuel : Nat}
    (hmatch : DeclMatchSpec.MatchRel nextLeft nextRight matched)
    (hmerge : out ∈ mergeBindings mid matched fuel) :
    DeclMatchSpec.MatchListAccRel
      (left ++ [nextLeft]) (right ++ [nextRight]) seed out := by
  exact matchListAccRel_append hprefix (.cons hmatch hmerge .nil)

/-- Derivation-local matcher certificates compose at the same dependent
accumulator boundary as their underlying list-match derivations.  The result
is existential in the proof term so proof irrelevance is never used to
identify binding presentations. -/
private theorem exists_matchListAccRel_append_traceSound
    {trace : List (String × Metta.Atom)}
    {left right : List Atom} {seed mid : Bindings}
    {hprefix : DeclMatchSpec.MatchListAccRel left right seed mid}
    (hprefixSound : MatchListTraceSound trace hprefix)
    {suffixLeft suffixRight : List Atom} {out : Bindings}
    {hsuffix : DeclMatchSpec.MatchListAccRel
      suffixLeft suffixRight mid out}
    (hsuffixSound : MatchListTraceSound trace hsuffix) :
    ∃ hrel : DeclMatchSpec.MatchListAccRel
        (left ++ suffixLeft) (right ++ suffixRight) seed out,
      MatchListTraceSound trace hrel := by
  let AtomMotive := fun {left right : Atom} {out : Bindings}
      (hrel : DeclMatchSpec.MatchRel left right out)
      (_ : MatchTraceSound trace hrel) => True
  let ListMotive := fun {left right : List Atom} {seed mid : Bindings}
      (hrel : DeclMatchSpec.MatchListAccRel left right seed mid)
      (_ : MatchListTraceSound trace hrel) =>
    ∀ {suffixLeft suffixRight : List Atom} {out : Bindings}
        {hsuffix : DeclMatchSpec.MatchListAccRel
          suffixLeft suffixRight mid out},
      MatchListTraceSound trace hsuffix →
        ∃ hcombined : DeclMatchSpec.MatchListAccRel
            (left ++ suffixLeft) (right ++ suffixRight) seed out,
          MatchListTraceSound trace hcombined
  have hrec : ListMotive hprefix hprefixSound :=
    MatchListTraceSound.rec (trace := trace)
      (motive_1 := AtomMotive) (motive_2 := ListMotive)
      (by intro name; trivial)
      (by intro left right; trivial)
      (by intro key value hnonvar; trivial)
      (by intro value key hnonvar; trivial)
      (by intro value; trivial)
      (by
        intro left right out hlist hlistSound ih
        trivial)
      (by
        intro seed suffixLeft suffixRight out hsuffix hsuffixSound
        exact ⟨hsuffix, hsuffixSound⟩)
      (by
        intro left right lefts rights seed matched next mid fuel
          hmatch hmerge htail hmatchSound hmergeSound htailSound
          _ihMatch ihTail suffixLeft suffixRight out hsuffix hsuffixSound
        obtain ⟨hrel, hrelSound⟩ := ihTail hsuffixSound
        exact ⟨DeclMatchSpec.MatchListAccRel.cons hmatch hmerge hrel,
          MatchListTraceSound.cons (hmerge := hmerge)
            hmatchSound hmergeSound hrelSound⟩)
      (t := hprefixSound)
  exact hrec hsuffixSound

/-- Equality-closure certificate companion to
`exists_matchListAccRel_append_traceSound`. -/
private theorem exists_matchListAccRel_append_equalitySound
    {allowed : List (String × String)}
    {left right : List Atom} {seed mid : Bindings}
    {hprefix : DeclMatchSpec.MatchListAccRel left right seed mid}
    (hprefixSound : MatchListEqualityClosureBoundSound allowed hprefix)
    {suffixLeft suffixRight : List Atom} {out : Bindings}
    {hsuffix : DeclMatchSpec.MatchListAccRel
      suffixLeft suffixRight mid out}
    (hsuffixSound : MatchListEqualityClosureBoundSound allowed hsuffix) :
    ∃ hrel : DeclMatchSpec.MatchListAccRel
        (left ++ suffixLeft) (right ++ suffixRight) seed out,
      MatchListEqualityClosureBoundSound allowed hrel := by
  let AtomMotive := fun {left right : Atom} {out : Bindings}
      (hrel : DeclMatchSpec.MatchRel left right out)
      (_ : MatchEqualityClosureBoundSound allowed hrel) => True
  let ListMotive := fun {left right : List Atom} {seed mid : Bindings}
      (hrel : DeclMatchSpec.MatchListAccRel left right seed mid)
      (_ : MatchListEqualityClosureBoundSound allowed hrel) =>
    ∀ {suffixLeft suffixRight : List Atom} {out : Bindings}
        {hsuffix : DeclMatchSpec.MatchListAccRel
          suffixLeft suffixRight mid out},
      MatchListEqualityClosureBoundSound allowed hsuffix →
        ∃ hcombined : DeclMatchSpec.MatchListAccRel
            (left ++ suffixLeft) (right ++ suffixRight) seed out,
          MatchListEqualityClosureBoundSound allowed hcombined
  have hrec : ListMotive hprefix hprefixSound :=
    MatchListEqualityClosureBoundSound.rec (allowed := allowed)
      (motive_1 := AtomMotive) (motive_2 := ListMotive)
      (by intro name; trivial)
      (by intro left right hreachable; trivial)
      (by intro key value hnonvar; trivial)
      (by intro value key hnonvar; trivial)
      (by intro value; trivial)
      (by
        intro left right out hlist hlistSound ih
        trivial)
      (by
        intro seed suffixLeft suffixRight out hsuffix hsuffixSound
        exact ⟨hsuffix, hsuffixSound⟩)
      (by
        intro left right lefts rights seed matched next mid fuel
          hmatch hmerge htail hmatchSound hmergeSound htailSound
          _ihMatch ihTail suffixLeft suffixRight out hsuffix hsuffixSound
        obtain ⟨hrel, hrelSound⟩ := ihTail hsuffixSound
        exact ⟨DeclMatchSpec.MatchListAccRel.cons hmatch hmerge hrel,
          MatchListEqualityClosureBoundSound.cons (hmerge := hmerge)
            hmatchSound hmergeSound hrelSound⟩)
      (t := hprefixSound)
  exact hrec hsuffixSound

/-- Both derivation-local certificates compose on one common appended list
proof.  Proof irrelevance aligns only the two proofs of the same declarative
relation; it identifies no binding presentations. -/
private theorem exists_matchListAccRel_append_certified
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : List Atom} {seed mid : Bindings}
    {hprefix : DeclMatchSpec.MatchListAccRel left right seed mid}
    (hprefixTrace : MatchListTraceSound trace hprefix)
    (hprefixBound : MatchListEqualityClosureBoundSound allowed hprefix)
    {suffixLeft suffixRight : List Atom} {out : Bindings}
    {hsuffix : DeclMatchSpec.MatchListAccRel
      suffixLeft suffixRight mid out}
    (hsuffixTrace : MatchListTraceSound trace hsuffix)
    (hsuffixBound : MatchListEqualityClosureBoundSound allowed hsuffix) :
    ∃ hrel : DeclMatchSpec.MatchListAccRel
        (left ++ suffixLeft) (right ++ suffixRight) seed out,
      MatchListTraceSound trace hrel ∧
        MatchListEqualityClosureBoundSound allowed hrel := by
  obtain ⟨hrel, hrelTrace⟩ :=
    exists_matchListAccRel_append_traceSound hprefixTrace hsuffixTrace
  obtain ⟨hrel', hrelBound⟩ :=
    exists_matchListAccRel_append_equalitySound hprefixBound hsuffixBound
  refine ⟨hrel, hrelTrace, ?_⟩
  simpa only [Subsingleton.elim hrel' hrel] using hrelBound

/-- General Type-valued package for one original accumulator-threaded list
match with both local certificates.  Unlike the reflexive-prefix package, it
places no restriction on the output assignments or equalities. -/
structure HEMatchListAccCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (left right : List Atom) (seed : Bindings) where
  out : Bindings
  matchRel : DeclMatchSpec.MatchListAccRel left right seed out
  traceSound : MatchListTraceSound trace matchRel
  equalitySound : MatchListEqualityClosureBoundSound allowed matchRel

/-- Atom-facing counterpart of `HEMatchListAccCertified`. -/
structure HEMatchCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (left right : Atom) where
  out : Bindings
  matchRel : DeclMatchSpec.MatchRel left right out
  traceSound : MatchTraceSound trace matchRel
  equalitySound : MatchEqualityClosureBoundSound allowed matchRel

/-- A certified list match from empty bindings is exactly a certified
original expression match. -/
def HEMatchListAccCertified.toExpression
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right : List Atom}
    (h : HEMatchListAccCertified
      trace allowed left right Bindings.empty) :
    HEMatchCertified trace allowed
      (.expression left) (.expression right) := {
  out := h.out
  matchRel := DeclMatchSpec.MatchRel.expr h.matchRel
  traceSound := MatchTraceSound.expr h.traceSound
  equalitySound := MatchEqualityClosureBoundSound.expr h.equalitySound
}

/-- Prepend a certified original reflexive common prefix to an arbitrary
certified suffix beginning at that prefix's live output.  This is the exact
list-level composition consumed after the first-divergence strict recursive
call returns. -/
noncomputable def prependReflexiveMatchListCertified
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {common : List Atom}
    (hprefix : HEReflexiveMatchListAccCertified
      trace allowed common Bindings.empty)
    {left right : List Atom}
    (hsuffix : HEMatchListAccCertified
      trace allowed left right hprefix.out) :
    HEMatchListAccCertified trace allowed
      (common ++ left) (common ++ right) Bindings.empty := by
  let hcombinedExists := exists_matchListAccRel_append_certified
    hprefix.traceSound hprefix.equalitySound
      hsuffix.traceSound hsuffix.equalitySound
  let hcombined := Classical.choose hcombinedExists
  have hcombinedSound := Classical.choose_spec hcombinedExists
  exact {
    out := hsuffix.out
    matchRel := hcombined
    traceSound := hcombinedSound.1
    equalitySound := hcombinedSound.2
  }

/-- One certified atom match and merge can be appended to a certified list
prefix without exposing the relation proof chosen by append associativity. -/
private theorem exists_matchListAccRel_snoc_traceSound
    {trace : List (String × Metta.Atom)}
    {left right : List Atom} {seed mid : Bindings}
    {hprefix : DeclMatchSpec.MatchListAccRel left right seed mid}
    (hprefixSound : MatchListTraceSound trace hprefix)
    {nextLeft nextRight : Atom} {matched out : Bindings} {fuel : Nat}
    {hmatch : DeclMatchSpec.MatchRel nextLeft nextRight matched}
    (hmatchSound : MatchTraceSound trace hmatch)
    {hmerge : out ∈ mergeBindings mid matched fuel}
    (hmergeSound : MergeTraceSound trace (mergeBindings_sound hmerge)) :
    ∃ hrel : DeclMatchSpec.MatchListAccRel
        (left ++ [nextLeft]) (right ++ [nextRight]) seed out,
      MatchListTraceSound trace hrel := by
  let hsuffix : DeclMatchSpec.MatchListAccRel
      [nextLeft] [nextRight] mid out :=
    DeclMatchSpec.MatchListAccRel.cons hmatch hmerge
      DeclMatchSpec.MatchListAccRel.nil
  apply exists_matchListAccRel_append_traceSound
    (hsuffix := hsuffix) hprefixSound
  exact MatchListTraceSound.cons (hmerge := hmerge)
    hmatchSound hmergeSound MatchListTraceSound.nil

/-- A singleton fresh-assignment merge has a local certificate relative to
any ambient reconciliation trace. -/
private theorem mergeBindings_freshSingleton_traceSound
    (certificateTrace : List (String × Metta.Atom))
    {b : Bindings} {key : String} {value : Atom} {fuel : Nat}
    (hclass : b.classValues key = [])
    (hmerge : b.assign key value ∈
      mergeBindings b (Bindings.empty.assign key value) fuel) :
    MergeTraceSound certificateTrace (mergeBindings_sound hmerge) := by
  have hrightRecord : Bindings.empty.assign key value =
      (⟨[(key, value)], []⟩ : Bindings) := by
    simp [Bindings.empty, Bindings.assign, Bindings.isBound,
      Bindings.lookup]
  let hadd : AddVarBindingRel b key value (b.assign key value) :=
    AddVarBindingRel.fresh hclass
  let hassignments : MergeAssignsRel b [(key, value)]
      (b.assign key value) :=
    MergeAssignsRel.cons hadd
      (MergeAssignsRel.nil (acc := b.assign key value))
  let hequalities : MergeEqsRel (b.assign key value) []
      (b.assign key value) :=
    MergeEqsRel.nil (acc := b.assign key value)
  let hrel : MergeRel b ⟨[(key, value)], []⟩
      (b.assign key value) := MergeRel.mk hassignments hequalities
  have hsound : MergeTraceSound certificateTrace hrel := by
    apply MergeTraceSound.mk
    · exact MergeAssignsTraceSound.cons
        (AddVarBindingTraceSound.fresh (hclass := hclass))
        MergeAssignsTraceSound.nil
    · exact MergeEqsTraceSound.nil
  obtain ⟨hrelActual, hsoundActual⟩ :
      ∃ hrelActual : MergeRel b (Bindings.empty.assign key value)
          (b.assign key value),
        MergeTraceSound certificateTrace hrelActual := by
    simpa only [hrightRecord] using
      (show ∃ hrelRaw : MergeRel b ⟨[(key, value)], []⟩
          (b.assign key value),
        MergeTraceSound certificateTrace hrelRaw from ⟨hrel, hsound⟩)
  simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrelActual]
    using hsoundActual

/-- A singleton consistent-equality merge likewise has a local certificate
relative to any ambient reconciliation trace. -/
private theorem mergeBindings_consistentSingleton_traceSound
    (certificateTrace : List (String × Metta.Atom))
    {b : Bindings} {left right : String} {fuel : Nat}
    (hconsistent : Bindings.valuesConsistent
      ((b.addEquality left right).classValues left) = true)
    (hmerge : b.addEquality left right ∈
      mergeBindings b (Bindings.empty.addEquality left right) fuel) :
    MergeTraceSound certificateTrace (mergeBindings_sound hmerge) := by
  have hrightRecord : Bindings.empty.addEquality left right =
      (⟨[], [(left, right)]⟩ : Bindings) := by
    simp [Bindings.empty, Bindings.addEquality]
  let hadd : AddVarEqualityRel b left right
      (b.addEquality left right) :=
    AddVarEqualityRel.consistent hconsistent
  let hassignments : MergeAssignsRel b [] b :=
    MergeAssignsRel.nil (acc := b)
  let hequalities : MergeEqsRel b [(left, right)]
      (b.addEquality left right) :=
    MergeEqsRel.cons hadd
      (MergeEqsRel.nil (acc := b.addEquality left right))
  let hrel : MergeRel b ⟨[], [(left, right)]⟩
      (b.addEquality left right) := MergeRel.mk hassignments hequalities
  have hsound : MergeTraceSound certificateTrace hrel := by
    apply MergeTraceSound.mk
    · exact MergeAssignsTraceSound.nil
    · exact MergeEqsTraceSound.cons
        (AddVarEqualityTraceSound.consistent
          (hconsistent := hconsistent))
        MergeEqsTraceSound.nil
  obtain ⟨hrelActual, hsoundActual⟩ :
      ∃ hrelActual : MergeRel b (Bindings.empty.addEquality left right)
          (b.addEquality left right),
        MergeTraceSound certificateTrace hrelActual := by
    simpa only [hrightRecord] using
      (show ∃ hrelRaw : MergeRel b ⟨[], [(left, right)]⟩
          (b.addEquality left right),
        MergeTraceSound certificateTrace hrelRaw from ⟨hrel, hsound⟩)
  simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrelActual]
    using hsoundActual

/-- The fresh singleton merge also has the equality-closure certificate for
every allowed graph: assigning a non-variable introduces no alias edge. -/
private theorem mergeBindings_freshSingleton_equalityClosureBoundSound
    (allowed : List (String × String))
    {b : Bindings} {key : String} {value : Atom} {fuel : Nat}
    (hclass : b.classValues key = [])
    (hmerge : b.assign key value ∈
      mergeBindings b (Bindings.empty.assign key value) fuel) :
    MergeEqualityClosureBoundSound allowed
      (mergeBindings_sound hmerge) := by
  have hrightRecord : Bindings.empty.assign key value =
      (⟨[(key, value)], []⟩ : Bindings) := by
    simp [Bindings.empty, Bindings.assign, Bindings.isBound,
      Bindings.lookup]
  let hadd : AddVarBindingRel b key value (b.assign key value) :=
    AddVarBindingRel.fresh hclass
  let hassignments : MergeAssignsRel b [(key, value)]
      (b.assign key value) :=
    MergeAssignsRel.cons hadd
      (MergeAssignsRel.nil (acc := b.assign key value))
  let hequalities : MergeEqsRel (b.assign key value) []
      (b.assign key value) :=
    MergeEqsRel.nil (acc := b.assign key value)
  let hrel : MergeRel b ⟨[(key, value)], []⟩
      (b.assign key value) := MergeRel.mk hassignments hequalities
  have hsound : MergeEqualityClosureBoundSound allowed hrel := by
    apply MergeEqualityClosureBoundSound.mk
    · exact MergeAssignsEqualityClosureBoundSound.cons
        (AddVarBindingEqualityClosureBoundSound.fresh
          (hclass := hclass))
        MergeAssignsEqualityClosureBoundSound.nil
    · exact MergeEqsEqualityClosureBoundSound.nil
  obtain ⟨hrelActual, hsoundActual⟩ :
      ∃ hrelActual : MergeRel b (Bindings.empty.assign key value)
          (b.assign key value),
        MergeEqualityClosureBoundSound allowed hrelActual := by
    simpa only [hrightRecord] using
      (show ∃ hrelRaw : MergeRel b ⟨[(key, value)], []⟩
          (b.assign key value),
        MergeEqualityClosureBoundSound allowed hrelRaw from
          ⟨hrel, hsound⟩)
  simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrelActual]
    using hsoundActual

/-- A consistent singleton alias merge has the corresponding local equality
certificate whenever the requested connection is already reachable in the
allowed reconciliation graph. -/
private theorem mergeBindings_consistentSingleton_equalityClosureBoundSound
    {allowed : List (String × String)}
    {b : Bindings} {left right : String} {fuel : Nat}
    (hconsistent : Bindings.valuesConsistent
      ((b.addEquality left right).classValues left) = true)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right)
    (hmerge : b.addEquality left right ∈
      mergeBindings b (Bindings.empty.addEquality left right) fuel) :
    MergeEqualityClosureBoundSound allowed
      (mergeBindings_sound hmerge) := by
  have hrightRecord : Bindings.empty.addEquality left right =
      (⟨[], [(left, right)]⟩ : Bindings) := by
    simp [Bindings.empty, Bindings.addEquality]
  let hadd : AddVarEqualityRel b left right
      (b.addEquality left right) :=
    AddVarEqualityRel.consistent hconsistent
  let hassignments : MergeAssignsRel b [] b :=
    MergeAssignsRel.nil (acc := b)
  let hequalities : MergeEqsRel b [(left, right)]
      (b.addEquality left right) :=
    MergeEqsRel.cons hadd
      (MergeEqsRel.nil (acc := b.addEquality left right))
  let hrel : MergeRel b ⟨[], [(left, right)]⟩
      (b.addEquality left right) := MergeRel.mk hassignments hequalities
  have hsound : MergeEqualityClosureBoundSound allowed hrel := by
    apply MergeEqualityClosureBoundSound.mk
    · exact MergeAssignsEqualityClosureBoundSound.nil
    · exact MergeEqsEqualityClosureBoundSound.cons
        (AddVarEqualityEqualityClosureBoundSound.consistent
          (hconsistent := hconsistent) hallowed)
        MergeEqsEqualityClosureBoundSound.nil
  obtain ⟨hrelActual, hsoundActual⟩ :
      ∃ hrelActual : MergeRel b
          (Bindings.empty.addEquality left right)
          (b.addEquality left right),
        MergeEqualityClosureBoundSound allowed hrelActual := by
    simpa only [hrightRecord] using
      (show ∃ hrelRaw : MergeRel b ⟨[], [(left, right)]⟩
          (b.addEquality left right),
        MergeEqualityClosureBoundSound allowed hrelRaw from
          ⟨hrel, hsound⟩)
  simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrelActual]
    using hsoundActual

/-- The fresh non-variable frontier case supplies the complete paired local
certificate.  Both equality judgments are vacuous because this step only
adds an assignment, while the trace judgments retain the exact runtime
matcher and merge proofs. -/
theorem freshNonvarCertifiedProgressStep
    {trace : List (String × Metta.Atom)} {before : Bindings}
    {key : String} {value : Atom}
    (hclass : before.classValues key = [])
    (hvalue : DeclMatchSpec.Atom.isVarB value = false)
    (hentry : (key, toLeaTTaAtom value) ∈ trace)
    (hpending : ¬ LeaEliminationTraceEntryRealized before
      (key, toLeaTTaAtom value))
    (hsound : LeaEliminationTraceAssignmentsSound before trace) :
    Nonempty (HECertifiedEliminationTraceProgressStep trace
      (eliminationTraceAliases trace) before
      (before.assign key value)) := by
  have hbound : before.isBound key = false :=
    isBound_false_of_classValues_nil hclass
  have hlookup : before.lookup key = none := by
    cases hlookup : before.lookup key with
    | none => rfl
    | some stored =>
        simp [Bindings.isBound, hlookup] at hbound
  obtain ⟨matchFuel, hmatch⟩ := DeclMatchSpec.matchAtoms_complete
    (DeclMatchSpec.MatchRel.varNonVar (v := key) (t := value) hvalue)
  have hadd : before.assign key value ∈
      addVarBinding before key value 1 := by
    simp [addVarBinding, hclass]
  have hmerge : before.assign key value ∈
      mergeBindings before (Bindings.empty.assign key value) 2 := by
    rw [mergeBindings_single_assign]
    exact hadd
  have hleaNonvar : ∀ target, toLeaTTaAtom value ≠ .var target := by
    cases value with
    | var target => simp [DeclMatchSpec.Atom.isVarB] at hvalue
    | symbol name | grounded name | expression name =>
        intro target hfalse
        cases hfalse
  have hsoundAfter : LeaEliminationTraceAssignmentsSound
      (before.assign key value) trace :=
    hsound.assign_of_lookup_none hlookup
      (HELeaAtomClassRel.translation before value) hentry hleaNonvar
  have hrealized : LeaEliminationTraceEntryRealized
      (before.assign key value) (key, toLeaTTaAtom value) := by
    cases value with
    | var target => simp [DeclMatchSpec.Atom.isVarB] at hvalue
    | symbol name | grounded name | expression name =>
        exact ⟨key, _, by simp [Bindings.assign, hbound],
          EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl,
          HELeaAtomClassRel.translation _ _⟩
  let hprogress : HEEliminationTraceProgressStep trace before
      (before.assign key value) := {
    left := .var key
    right := value
    matched := Bindings.empty.assign key value
    matchFuel := matchFuel
    mergeFuel := 2
    match_mem := hmatch
    merge_mem := hmerge
    entry := (key, toLeaTTaAtom value)
    entry_mem := hentry
    pending_before := hpending
    realized_after := hrealized
    assignmentsSound := hsoundAfter
    solutionPreserving := by
      intro valuation _hbefore htrace
      have hconstraint := htrace
        (key, toLeaTTaAtom value) hentry
      simpa [MettaEquationSatisfied, applyClassSolution] using hconstraint
  }
  refine ⟨{
    progress := hprogress
    matchTraceSound := ?_
    matchEqualityClosureBoundSound := ?_
    mergeTraceSound := ?_
    mergeEqualityClosureBoundSound := ?_
  }⟩
  · simpa [hprogress, Bindings.empty, Bindings.assign,
      Bindings.isBound, Bindings.lookup] using
      (MatchTraceSound.varNonVar
        (trace := trace) (hnonvar := hvalue))
  · simpa [hprogress, Bindings.empty, Bindings.assign,
      Bindings.isBound, Bindings.lookup] using
      (MatchEqualityClosureBoundSound.varNonVar
        (allowed := eliminationTraceAliases trace)
        (hnonvar := hvalue))
  · simpa [hprogress] using
      mergeBindings_freshSingleton_traceSound trace hclass hmerge
  · simpa [hprogress] using
      mergeBindings_freshSingleton_equalityClosureBoundSound
        (eliminationTraceAliases trace) hclass hmerge

/-- The consistent alias frontier case supplies the same complete local
certificate.  Its one new HE equality edge is justified directly by the
selected variable trace entry, hence lies in the trace alias graph without
depending on representative orientation. -/
theorem consistentAliasCertifiedProgressStep
    {trace : List (String × Metta.Atom)} {before : Bindings}
    {left right : String}
    (hconsistent : Bindings.valuesConsistent
      ((before.addEquality left right).classValues left) = true)
    (hentry : (left, .var right) ∈ trace)
    (hpending : ¬ LeaEliminationTraceEntryRealized before
      (left, .var right))
    (hsound : LeaEliminationTraceAssignmentsSound before trace) :
    Nonempty (HECertifiedEliminationTraceProgressStep trace
      (eliminationTraceAliases trace) before
      (before.addEquality left right)) := by
  obtain ⟨matchFuel, hmatch⟩ := DeclMatchSpec.matchAtoms_complete
    (DeclMatchSpec.MatchRel.varVar left right)
  have hadd : before.addEquality left right ∈
      addVarEquality before left right 1 := by
    simp [addVarEquality, hconsistent]
  have hmerge : before.addEquality left right ∈
      mergeBindings before (Bindings.empty.addEquality left right) 2 := by
    simpa [mergeBindings, Bindings.addEquality, Bindings.empty] using hadd
  have hrealized : LeaEliminationTraceEntryRealized
      (before.addEquality left right) (left, .var right) := by
    change right ∈ (before.addEquality left right).eqClass left
    rw [EqualityClosure.mem_eqClass_iff_reachable]
    by_cases hsame : left = right
    · subst right
      exact .rfl
    · exact (show
          (EqualityClosure.edgeGraph
            (before.addEquality left right).equalities).Adj left right by
            rw [EqualityClosure.edgeGraph_adj_iff]
            exact ⟨hsame, Or.inl (by simp [Bindings.addEquality])⟩).reachable
  have hallowed :
      (EqualityClosure.edgeGraph (eliminationTraceAliases trace)).Reachable
        left right := by
    by_cases hsame : left = right
    · subst right
      exact .rfl
    · exact (show
          (EqualityClosure.edgeGraph
            (eliminationTraceAliases trace)).Adj left right by
            rw [EqualityClosure.edgeGraph_adj_iff]
            exact ⟨hsame, Or.inl
              (mem_eliminationTraceAliases_iff.mpr hentry)⟩).reachable
  let hprogress : HEEliminationTraceProgressStep trace before
      (before.addEquality left right) := {
    left := .var left
    right := .var right
    matched := Bindings.empty.addEquality left right
    matchFuel := matchFuel
    mergeFuel := 2
    match_mem := hmatch
    merge_mem := hmerge
    entry := (left, .var right)
    entry_mem := hentry
    pending_before := hpending
    realized_after := hrealized
    assignmentsSound := hsound.addEquality left right
    solutionPreserving := by
      intro valuation _hbefore htrace
      have hconstraint := htrace (left, .var right) hentry
      simpa [MettaEquationSatisfied, applyClassSolution] using hconstraint
  }
  refine ⟨{
    progress := hprogress
    matchTraceSound := ?_
    matchEqualityClosureBoundSound := ?_
    mergeTraceSound := ?_
    mergeEqualityClosureBoundSound := ?_
  }⟩
  · simpa [hprogress, Bindings.empty, Bindings.addEquality] using
      (MatchTraceSound.varVar (trace := trace)
        (left := left) (right := right))
  · simpa [hprogress, Bindings.empty, Bindings.addEquality] using
      (MatchEqualityClosureBoundSound.varVar
        (allowed := eliminationTraceAliases trace) hallowed)
  · simpa [hprogress] using
      mergeBindings_consistentSingleton_traceSound
        trace hconsistent hmerge
  · simpa [hprogress] using
      mergeBindings_consistentSingleton_equalityClosureBoundSound
        hconsistent hallowed hmerge

/-- Certified counterpart of `HEEliminationTraceProgressFrontier`.  The two
nonrecursive cases now carry all four local certificates; only unequal
value-expression and joined-class-expression conflicts remain as recursive
obligations. -/
inductive HECertifiedEliminationTraceProgressFrontier
    (trace : List (String × Metta.Atom))
    (before : Bindings) : Prop where
  | progressed {after : Bindings} :
      Nonempty (HECertifiedEliminationTraceProgressStep trace
        (eliminationTraceAliases trace) before after) →
      HECertifiedEliminationTraceProgressFrontier trace before
  | valueConflict {key : String} {value : Atom}
      {leaValue : Metta.Atom} {first : Atom} {rest : List Atom} :
      toLeaTTaAtom value = leaValue →
      DeclMatchSpec.Atom.isVarB value = false →
      before.classValues key = first :: rest →
      (key, leaValue) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (key, leaValue) →
      LeaEliminationTraceAssignmentsSound before trace →
      HECertifiedEliminationTraceProgressFrontier trace before
  | aliasConflict {left right : String} :
      Bindings.valuesConsistent
          ((before.addEquality left right).classValues left) = false →
      (left, .var right) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (left, .var right) →
      LeaEliminationTraceAssignmentsSound before trace →
      HECertifiedEliminationTraceProgressFrontier trace before

/-- Selecting a pending translated Robinson obligation now discharges every
fresh and consistent case with the complete paired certificate.  The proof
uses the same order-free finite selection as the earlier frontier theorem;
the stronger conclusion changes no operational choice. -/
theorem certifiedProgressFrontier_of_pending
    {trace : List (String × Metta.Atom)} {before : Bindings}
    (himage : ∀ key term, (key, term) ∈ trace →
      ∃ atom : Atom, toLeaTTaAtom atom = term)
    (hsound : LeaEliminationTraceAssignmentsSound before trace)
    (hpending : pendingEliminationTraceEntries before trace ≠ ∅) :
    HECertifiedEliminationTraceProgressFrontier trace before := by
  classical
  obtain ⟨entry, hentryPending⟩ :=
    Finset.nonempty_iff_ne_empty.mpr hpending
  have hentryData := hentryPending
  simp only [pendingEliminationTraceEntries, Finset.mem_filter,
    List.mem_toFinset] at hentryData
  rcases entry with ⟨key, leaValue⟩
  rcases hentryData with ⟨hentry, hnotRealized⟩
  cases leaValue with
  | var target =>
      cases hconsistent : Bindings.valuesConsistent
          ((before.addEquality key target).classValues key) with
      | false =>
          exact .aliasConflict hconsistent hentry hnotRealized hsound
      | true =>
          exact .progressed
            (consistentAliasCertifiedProgressStep hconsistent hentry
              hnotRealized hsound)
  | sym symbol =>
      obtain ⟨value, hvalue⟩ := himage key (.sym symbol) hentry
      have hnonvar : DeclMatchSpec.Atom.isVarB value = false := by
        cases value <;> simp_all [toLeaTTaAtom,
          DeclMatchSpec.Atom.isVarB]
      cases hclass : before.classValues key with
      | nil =>
          exact .progressed
            (freshNonvarCertifiedProgressStep hclass hnonvar
              (by simpa [← hvalue] using hentry)
              (by simpa [← hvalue] using hnotRealized) hsound)
      | cons first rest =>
          exact .valueConflict hvalue hnonvar hclass hentry
            hnotRealized hsound
  | gnd ground =>
      obtain ⟨value, hvalue⟩ := himage key (.gnd ground) hentry
      have hnonvar : DeclMatchSpec.Atom.isVarB value = false := by
        cases value <;> simp_all [toLeaTTaAtom,
          DeclMatchSpec.Atom.isVarB]
      cases hclass : before.classValues key with
      | nil =>
          exact .progressed
            (freshNonvarCertifiedProgressStep hclass hnonvar
              (by simpa [← hvalue] using hentry)
              (by simpa [← hvalue] using hnotRealized) hsound)
      | cons first rest =>
          exact .valueConflict hvalue hnonvar hclass hentry
            hnotRealized hsound
  | expr atoms =>
      obtain ⟨value, hvalue⟩ := himage key (.expr atoms) hentry
      have hnonvar : DeclMatchSpec.Atom.isVarB value = false := by
        cases value <;> simp_all [toLeaTTaAtom,
          DeclMatchSpec.Atom.isVarB]
      cases hclass : before.classValues key with
      | nil =>
          exact .progressed
            (freshNonvarCertifiedProgressStep hclass hnonvar
              (by simpa [← hvalue] using hentry)
              (by simpa [← hvalue] using hnotRealized) hsound)
      | cons first rest =>
          exact .valueConflict hvalue hnonvar hclass hentry
            hnotRealized hsound

/-- Global satisfiable reconciliation reduced to its two original
expression-conflict constructors, with both trace provenance and equality
upper bounds retained.  Fresh assignments, consistent aliases, deficit
decrease, termination, solution transport, and certificate composition are
all discharged here. -/
theorem exists_completeSatisfiedCertifiedMatcherMergeChain_of_conflict_progress
    {trace : List (String × Metta.Atom)}
    {valuation : String → Metta.Atom}
    (himage : ∀ key term, (key, term) ∈ trace →
      ∃ atom : Atom, toLeaTTaAtom atom = term)
    (htraceSatisfied : MettaConstraintsSatisfied valuation trace)
    (hvalueProgress : ∀
      (before : Bindings) (key : String) (value : Atom)
      (leaValue : Metta.Atom) (first : Atom) (rest : List Atom),
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEqualityClosureBound before (eliminationTraceAliases trace) →
      HEBindingSatisfied valuation before →
      toLeaTTaAtom value = leaValue →
      DeclMatchSpec.Atom.isVarB value = false →
      before.classValues key = first :: rest →
      (key, leaValue) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (key, leaValue) →
      BothExpressions first value →
      (∀ {stored other : Atom},
        stored ∈ before.classValues key →
        other ∈ before.classValues key →
        stored ≠ other → BothExpressions stored other) →
      ∃ after, Nonempty
        (HECertifiedEliminationTraceProgressStep trace
          (eliminationTraceAliases trace) before after))
    (haliasProgress : ∀
      (before : Bindings) (left right : String),
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEqualityClosureBound before (eliminationTraceAliases trace) →
      HEBindingSatisfied valuation before →
      Bindings.valuesConsistent
          ((before.addEquality left right).classValues left) = false →
      (left, .var right) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (left, .var right) →
      (∀ {first second : Atom},
        first ∈ (before.addEquality left right).classValues left →
        second ∈ (before.addEquality left right).classValues left →
        first ≠ second → BothExpressions first second) →
      ∃ after, Nonempty
        (HECertifiedEliminationTraceProgressStep trace
          (eliminationTraceAliases trace) before after)) :
    ∃ out,
      HECertifiedMatcherMergeChain trace
          (eliminationTraceAliases trace) Bindings.empty out ∧
        HEAssignmentsNonVariable out ∧
          LeaEliminationTraceStructuralRel out trace ∧
            HEEqualityClosureBound out (eliminationTraceAliases trace) ∧
              HEBindingSatisfied valuation out := by
  apply exists_completeSatisfiedCertifiedMatcherMergeChain_of_local_progress
    htraceSatisfied
  · intro key target hmem
    simp [Bindings.empty] at hmem
  · intro key value hmem
    simp [Bindings.empty] at hmem
  · exact HEEqualityClosureBound.empty _
  · exact (hesat_empty_iff valuation).mpr trivial
  · intro before hnonvar hsound hbound hbefore hpending
    cases certifiedProgressFrontier_of_pending himage hsound hpending with
    | progressed hstep => exact ⟨_, hstep⟩
    | valueConflict hvalue hvalueNonvar hclass hentry
        hnotRealized _ =>
        exact hvalueProgress before _ _ _ _ _ hnonvar hsound hbound
          hbefore hvalue hvalueNonvar hclass hentry hnotRealized
          (bothExpressions_of_pending_valueConflict
            hnonvar hbefore htraceSatisfied hvalue hvalueNonvar hclass
              hentry hnotRealized)
          (fun hstored hother hne =>
            bothExpressions_of_ne_classValues_of_satisfied
              hnonvar hbefore hstored hother hne)
    | aliasConflict hinconsistent hentry hnotRealized _ =>
        exact haliasProgress before _ _ hnonvar hsound hbound hbefore
          hinconsistent hentry hnotRealized
          (fun hfirst hsecond hne =>
            bothExpressions_of_ne_aliasConflict_classValues
              hnonvar hbefore htraceSatisfied hentry hfirst hsecond hne)

/-- Append one related atom pair to a pointwise class-relative list
certificate. -/
private theorem heLeaAtomClassRel_forall₂_snoc
    {b : Bindings} {atoms : List Atom} {leaAtoms : List Metta.Atom}
    (hprefix : List.Forall₂ (HELeaAtomClassRel b) atoms leaAtoms)
    {atom : Atom} {leaAtom : Metta.Atom}
    (hlast : HELeaAtomClassRel b atom leaAtom) :
    List.Forall₂ (HELeaAtomClassRel b)
      (atoms ++ [atom]) (leaAtoms ++ [leaAtom]) := by
  induction hprefix with
  | nil => exact .cons hlast .nil
  | cons hhead htail ih => exact .cons hhead ih

/-- Every executable Robinson replay is genuine matcher-origin sequencing:
read in reverse solve order, each trace entry is a declarative HE leaf match
whose singleton result is merged into the prior accumulator.  The right-hand
HE atoms remain class-relative to the original trace terms in the final
closure, so representative chronology is not exposed. -/
theorem LeaEliminationTraceExecutableReplay.exists_matchListRel_reverse
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceExecutableReplay Bindings.empty trace out) :
    ∃ left right,
      left = trace.reverse.map (fun entry => Atom.var entry.1) ∧
        List.Forall₂ (HELeaAtomClassRel out) right
          (trace.reverse.map Prod.snd) ∧
        DeclMatchSpec.MatchListRel left right out := by
  induction h with
  | nil =>
      exact ⟨[], [], rfl, .nil, .nil⟩
  | @aliasStep trace b key target h hstep ih =>
      obtain ⟨left, right, hleft, hright, hlist⟩ := ih
      have hmerge : b.addEquality key target ∈
          mergeBindings b (Bindings.empty.addEquality key target) 2 := by
        simpa [mergeBindings, Bindings.empty, Bindings.addEquality] using
          hstep
      have hext := addVarEquality_observationExtension hstep
      have hright' : List.Forall₂
          (HELeaAtomClassRel (b.addEquality key target)) right
          (trace.reverse.map Prod.snd) :=
        hright.imp (fun _ _ hrel =>
          HELeaAtomClassRel.mono hext.classes hrel)
      refine ⟨left ++ [.var key], right ++ [.var target], ?_, ?_, ?_⟩
      · simp [hleft]
      · simpa [toLeaTTaAtom] using
          heLeaAtomClassRel_forall₂_snoc hright'
          (HELeaAtomClassRel.translation
            (b.addEquality key target) (.var target))
      · exact matchListAccRel_snoc hlist
          (DeclMatchSpec.MatchRel.varVar key target) hmerge
  | @valueStep trace b key value leaValue h hlookup hatom hnonvar hstep ih =>
      obtain ⟨left, right, hleft, hright, hlist⟩ := ih
      have hvalueNonvar : DeclMatchSpec.Atom.isVarB value = false := by
        cases value with
        | var target =>
            cases hatom
            all_goals simp_all
        | symbol name | grounded name | expression name => rfl
      have hmerge : b.assign key value ∈
          mergeBindings b (Bindings.empty.assign key value) 2 := by
        simpa [mergeBindings, Bindings.empty, Bindings.assign,
          Bindings.isBound, Bindings.lookup] using hstep
      have hext := addVarBinding_observationExtension hstep
      have hright' : List.Forall₂
          (HELeaAtomClassRel (b.assign key value)) right
          (trace.reverse.map Prod.snd) :=
        hright.imp (fun _ _ hrel =>
          HELeaAtomClassRel.mono hext.classes hrel)
      refine ⟨left ++ [.var key], right ++ [value], ?_, ?_, ?_⟩
      · simp [hleft]
      · simpa using heLeaAtomClassRel_forall₂_snoc hright'
          (HELeaAtomClassRel.mono hext.classes hatom)
      · exact matchListAccRel_snoc hlist
          (DeclMatchSpec.MatchRel.varNonVar hvalueNonvar) hmerge

/-- A triangular executable Robinson replay is a genuine list matcher whose
every internal accumulator merge carries a derivation-local certificate for
an arbitrary ambient reconciliation trace.  The ambient trace parameter is
what lets a strict singleton-equation prefix be reused inside its larger
successful solve without a universe-wide matcher hypothesis. -/
theorem LeaEliminationTraceExecutableReplay.exists_matchListRelTraceSound_reverse_for
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceExecutableReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace)
    (certificateTrace : List (String × Metta.Atom)) :
    ∃ left right,
      ∃ hrel : DeclMatchSpec.MatchListRel left right out,
      left = trace.reverse.map (fun entry => Atom.var entry.1) ∧
        List.Forall₂ (HELeaAtomClassRel out) right
          (trace.reverse.map Prod.snd) ∧
        MatchListTraceSound certificateTrace hrel := by
  induction h generalizing certificateTrace with
  | nil =>
      exact ⟨[], [], DeclMatchSpec.MatchListAccRel.nil,
        rfl, .nil, MatchListTraceSound.nil⟩
  | @aliasStep trace b key target h hstep ih =>
      rcases htriangular with ⟨hkeyFresh, htailTriangular⟩
      obtain ⟨left, right, hlist, hleft, hright, hlistSound⟩ :=
        ih htailTriangular certificateTrace
      have hmerge : b.addEquality key target ∈
          mergeBindings b (Bindings.empty.addEquality key target) 2 := by
        simpa [mergeBindings, Bindings.empty, Bindings.addEquality] using
          hstep
      have hconsistent : Bindings.valuesConsistent
          ((b.addEquality key target).classValues key) = true :=
        (LeaEliminationTraceReplay.aliasStep h.replay).valuesConsistent
          ⟨hkeyFresh, htailTriangular⟩ key
      have hmergeSound : MergeTraceSound certificateTrace
          (mergeBindings_sound hmerge) :=
        mergeBindings_consistentSingleton_traceSound
          certificateTrace hconsistent hmerge
      have hmergeLiteral : b.addEquality key target ∈
          mergeBindings b ⟨[], [(key, target)]⟩ 2 := by
        simpa [Bindings.empty, Bindings.addEquality] using hmerge
      have hmergeSoundLiteral : MergeTraceSound certificateTrace
          (mergeBindings_sound hmergeLiteral) := by
        simpa [Bindings.empty, Bindings.addEquality] using hmergeSound
      obtain ⟨hlist', hlistSound'⟩ :=
        exists_matchListAccRel_snoc_traceSound hlistSound
          (MatchTraceSound.varVar (trace := certificateTrace))
          (hmerge := hmergeLiteral) hmergeSoundLiteral
      have hext := addVarEquality_observationExtension hstep
      have hright' : List.Forall₂
          (HELeaAtomClassRel (b.addEquality key target)) right
          (trace.reverse.map Prod.snd) :=
        hright.imp (fun _ _ hrel =>
          HELeaAtomClassRel.mono hext.classes hrel)
      exact ⟨left ++ [.var key], right ++ [.var target], hlist',
        by simp [hleft],
        by
          simpa [toLeaTTaAtom] using
            heLeaAtomClassRel_forall₂_snoc hright'
              (HELeaAtomClassRel.translation
                (b.addEquality key target) (.var target)),
        hlistSound'⟩
  | @valueStep trace b key value leaValue h hlookup hatom hnonvar hstep ih =>
      rcases htriangular with ⟨hkeyFresh, htailTriangular⟩
      obtain ⟨left, right, hlist, hleft, hright, hlistSound⟩ :=
        ih htailTriangular certificateTrace
      have hvalueNonvar : DeclMatchSpec.Atom.isVarB value = false := by
        cases value with
        | var target =>
            cases hatom
            all_goals simp_all
        | symbol name | grounded name | expression name => rfl
      have hclass : b.classValues key = [] :=
        h.replay.classValues_eq_nil_of_not_mem_constraintVars hkeyFresh
      have hmerge : b.assign key value ∈
          mergeBindings b (Bindings.empty.assign key value) 2 := by
        simpa [mergeBindings, Bindings.empty, Bindings.assign,
          Bindings.isBound, Bindings.lookup] using hstep
      have hmergeSound : MergeTraceSound certificateTrace
          (mergeBindings_sound hmerge) :=
        mergeBindings_freshSingleton_traceSound
          certificateTrace hclass hmerge
      have hmergeLiteral : b.assign key value ∈
          mergeBindings b ⟨[(key, value)], []⟩ 2 := by
        simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
          Bindings.lookup] using hmerge
      have hmergeSoundLiteral : MergeTraceSound certificateTrace
          (mergeBindings_sound hmergeLiteral) := by
        simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
          Bindings.lookup] using hmergeSound
      obtain ⟨hlist', hlistSound'⟩ :=
        exists_matchListAccRel_snoc_traceSound hlistSound
          (MatchTraceSound.varNonVar
            (trace := certificateTrace) (hnonvar := hvalueNonvar))
          (hmerge := hmergeLiteral) hmergeSoundLiteral
      have hext := addVarBinding_observationExtension hstep
      have hright' : List.Forall₂
          (HELeaAtomClassRel (b.assign key value)) right
          (trace.reverse.map Prod.snd) :=
        hright.imp (fun _ _ hrel =>
          HELeaAtomClassRel.mono hext.classes hrel)
      exact ⟨left ++ [.var key], right ++ [value], hlist',
        by simp [hleft],
        by
          simpa using heLeaAtomClassRel_forall₂_snoc hright'
            (HELeaAtomClassRel.mono hext.classes hatom),
        hlistSound'⟩

/-- Exact-trace specialization of the certified matcher replay. -/
theorem LeaEliminationTraceExecutableReplay.exists_matchListRelTraceSound_reverse
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceExecutableReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace) :
    ∃ left right,
      ∃ hrel : DeclMatchSpec.MatchListRel left right out,
      left = trace.reverse.map (fun entry => Atom.var entry.1) ∧
        List.Forall₂ (HELeaAtomClassRel out) right
          (trace.reverse.map Prod.snd) ∧
        MatchListTraceSound trace hrel :=
  h.exists_matchListRelTraceSound_reverse_for htriangular trace

/-- Executable expression form of the certified replay, relative to any
ambient reconciliation trace.  Proof irrelevance identifies only two
declarative proofs of the same runtime matcher result. -/
theorem LeaEliminationTraceExecutableReplay.exists_mem_matchAtoms_expression_reverse_traceSound_for
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceExecutableReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace)
    (certificateTrace : List (String × Metta.Atom)) :
    ∃ left right fuel,
      ∃ hmem : out ∈
          matchAtoms (.expression left) (.expression right) fuel,
        left = trace.reverse.map (fun entry => Atom.var entry.1) ∧
          List.Forall₂ (HELeaAtomClassRel out) right
            (trace.reverse.map Prod.snd) ∧
          MatchTraceSound certificateTrace
            (DeclMatchSpec.matchAtoms_sound hmem) := by
  obtain ⟨left, right, hlist, hleft, hright, hlistSound⟩ :=
    h.exists_matchListRelTraceSound_reverse_for
      htriangular certificateTrace
  let hrel : DeclMatchSpec.MatchRel
      (.expression left) (.expression right) out :=
    DeclMatchSpec.MatchRel.expr hlist
  obtain ⟨fuel, hmem⟩ := DeclMatchSpec.matchAtoms_complete hrel
  have hrelSound : MatchTraceSound certificateTrace hrel :=
    MatchTraceSound.expr hlistSound
  have hmemSound : MatchTraceSound certificateTrace
      (DeclMatchSpec.matchAtoms_sound hmem) := by
    simpa only [Subsingleton.elim
      (DeclMatchSpec.matchAtoms_sound hmem) hrel] using
      hrelSound
  exact ⟨left, right, fuel, hmem, hleft, hright, hmemSound⟩

/-- Exact-trace executable expression specialization. -/
theorem LeaEliminationTraceExecutableReplay.exists_mem_matchAtoms_expression_reverse_traceSound
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceExecutableReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace) :
    ∃ left right fuel,
      ∃ hmem : out ∈
          matchAtoms (.expression left) (.expression right) fuel,
        left = trace.reverse.map (fun entry => Atom.var entry.1) ∧
          List.Forall₂ (HELeaAtomClassRel out) right
            (trace.reverse.map Prod.snd) ∧
          MatchTraceSound trace (DeclMatchSpec.matchAtoms_sound hmem) :=
  h.exists_mem_matchAtoms_expression_reverse_traceSound_for
    htriangular trace

/-- The same replay is emitted by the executable HE list matcher at some
finite fuel.  Thus the sequencing certificate above is not merely a custom
relation: it has an actual runtime witness. -/
theorem LeaEliminationTraceExecutableReplay.exists_mem_matchAtomsList_reverse
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceExecutableReplay Bindings.empty trace out) :
    ∃ left right fuel,
      left = trace.reverse.map (fun entry => Atom.var entry.1) ∧
        List.Forall₂ (HELeaAtomClassRel out) right
          (trace.reverse.map Prod.snd) ∧
        out ∈ matchAtomsList left right [Bindings.empty] fuel := by
  obtain ⟨left, right, hleft, hright, hrel⟩ :=
    h.exists_matchListRel_reverse
  obtain ⟨fuel, hmem⟩ := DeclMatchSpec.matchAtomsList_complete hrel
  exact ⟨left, right, fuel, hleft, hright, hmem⟩

/-- Packaging the canonical constraint lists as expressions yields a genuine
top-level HE matcher result.  The expressions encode the selected constraints;
they are not asserted to be the original equation's presentation. -/
theorem LeaEliminationTraceExecutableReplay.exists_mem_matchAtoms_expression_reverse
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceExecutableReplay Bindings.empty trace out) :
    ∃ left right fuel,
      left = trace.reverse.map (fun entry => Atom.var entry.1) ∧
        List.Forall₂ (HELeaAtomClassRel out) right
          (trace.reverse.map Prod.snd) ∧
        out ∈ matchAtoms (.expression left) (.expression right) fuel := by
  obtain ⟨left, right, hleft, hright, hrel⟩ :=
    h.exists_matchListRel_reverse
  obtain ⟨fuel, hmem⟩ :=
    DeclMatchSpec.matchAtoms_complete (DeclMatchSpec.MatchRel.expr hrel)
  exact ⟨left, right, fuel, hleft, hright, hmem⟩

/-- Triangularity upgrades the canonical replay to a step-for-step executable
HE replay. -/
theorem LeaEliminationTraceReplay.executable_of_triangular
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (htriangular : EliminationTraceTriangular trace) :
    LeaEliminationTraceExecutableReplay Bindings.empty trace out := by
  induction h with
  | nil => exact .nil
  | @aliasStep trace b key target h ih =>
      rcases htriangular with ⟨hkeyFresh, htailTriangular⟩
      exact .aliasStep (ih htailTriangular)
        (h.aliasStep_mem_addVarEquality_of_triangular
          ⟨hkeyFresh, htailTriangular⟩).1
  | @valueStep trace b key value leaValue h hlookup hatom hnonvar ih =>
      rcases htriangular with ⟨hkeyFresh, htailTriangular⟩
      exact .valueStep (ih htailTriangular) hlookup hatom hnonvar
        (h.valueStep_mem_addVarBinding hkeyFresh hatom hnonvar).1

/-- A trace whose eliminated keys are distinct and whose terms all come from
the HE atom language has a canonical HE replay.  This is constructive witness
formation for the LeaTTa-to-HE direction; it does not identify the replay's
relation-list presentation with any independently produced HE output. -/
theorem exists_eliminationTraceReplay_of_nodup_of_translation
    {trace : List (String × Metta.Atom)}
    (hkeys : (trace.map Prod.fst).Nodup)
    (htranslation : ∀ key leaValue, (key, leaValue) ∈ trace →
      ∃ value : Atom, toLeaTTaAtom value = leaValue) :
    ∃ out, LeaEliminationTraceReplay Bindings.empty trace out := by
  induction trace with
  | nil => exact ⟨Bindings.empty, .nil⟩
  | cons binding trace ih =>
      rcases binding with ⟨key, leaValue⟩
      have hkeyFresh : key ∉ trace.map Prod.fst :=
        (List.nodup_cons.mp hkeys).1
      have htailKeys : (trace.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hkeys).2
      have htailTranslation : ∀ tailKey tailValue,
          (tailKey, tailValue) ∈ trace →
          ∃ value : Atom, toLeaTTaAtom value = tailValue := by
        intro tailKey tailValue hmem
        exact htranslation tailKey tailValue (List.mem_cons_of_mem _ hmem)
      obtain ⟨out, hout⟩ := ih htailKeys htailTranslation
      cases leaValue with
      | var target =>
          exact ⟨out.addEquality key target, .aliasStep hout⟩
      | sym name =>
          refine ⟨out.assign key (.symbol name),
            .valueStep hout ?_ (.symbol name) ?_⟩
          · by_contra hne
            cases hlookup : out.lookup key with
            | none => exact hne hlookup
            | some stored =>
                have hmem : (key, stored) ∈ out.assignments :=
                  assignment_mem_of_lookup_eq_some (by
                    simpa [Bindings.lookup] using hlookup)
                exact (hkeyFresh (hout.assignmentKey_mem hmem)).elim
          · intro target h
            cases h

      | gnd ground =>
          obtain ⟨value, hvalue⟩ :=
            htranslation key (.gnd ground) (by simp)
          refine ⟨out.assign key value,
            .valueStep hout ?_ ?_ ?_⟩
          · by_contra hne
            cases hlookup : out.lookup key with
            | none => exact hne hlookup
            | some stored =>
                have hmem : (key, stored) ∈ out.assignments :=
                  assignment_mem_of_lookup_eq_some (by
                    simpa [Bindings.lookup] using hlookup)
                exact (hkeyFresh (hout.assignmentKey_mem hmem)).elim
          · simpa [hvalue] using HELeaAtomClassRel.translation out value
          · intro target h
            cases h

      | expr atoms =>
          obtain ⟨value, hvalue⟩ :=
            htranslation key (.expr atoms) (by simp)
          refine ⟨out.assign key value,
            .valueStep hout ?_ ?_ ?_⟩
          · by_contra hne
            cases hlookup : out.lookup key with
            | none => exact hne hlookup
            | some stored =>
                have hmem : (key, stored) ∈ out.assignments :=
                  assignment_mem_of_lookup_eq_some (by
                    simpa [Bindings.lookup] using hlookup)
                exact (hkeyFresh (hout.assignmentKey_mem hmem)).elim
          · simpa [hvalue] using HELeaAtomClassRel.translation out value
          · intro target h
            cases h

/-- The solve trace of a successful whole-system reconciliation has distinct
eliminated keys.  This is derived from the normalized result, then transported
back across reversal; it is not an ordering premise on HE. -/
theorem wholeBindingReconciliation_eliminationTrace_keys_nodup
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    ((unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations bindings ++ extra))
      (Metta.Bindings.equations bindings ++ extra)).map Prod.fst).Nodup := by
  have hkeys := wholeBindingReconciliation_result_keys_nodup hreconcile
  rw [wholeBindingReconciliation_result_eq_eliminationTrace_reverse
    hreconcile] at hkeys
  simpa [mettaSubstKeys] using hkeys

/-! ## Translation-image preservation through Robinson elimination -/

/-- Syntactic membership in the image of the HE-to-LeaTTa atom embedding.
This is deliberately stronger than `MettaAtomNoFloat`: host unit and error
payloads are float-free but do not belong to the HE language. -/
def LeaAtomInHEImage (leaAtom : Metta.Atom) : Prop :=
  ∃ atom : Atom, toLeaTTaAtom atom = leaAtom

/-- Every term stored in a substitution belongs to the HE atom image. -/
def LeaSubstInHEImage (subst : Metta.Subst) : Prop :=
  ∀ key term, (key, term) ∈ subst → LeaAtomInHEImage term

/-- Both endpoints of every equation belong to the HE atom image. -/
def LeaEquationsInHEImage
    (equations : List (Metta.Atom × Metta.Atom)) : Prop :=
  ∀ equation ∈ equations,
    LeaAtomInHEImage equation.1 ∧ LeaAtomInHEImage equation.2

/-- Every decomposed constraint term belongs to the HE atom image. -/
def LeaConstraintsInHEImage
    (constraints : List (String × Metta.Atom)) : Prop :=
  ∀ key term, (key, term) ∈ constraints → LeaAtomInHEImage term

/-- Exact membership in the translated HE language implies the float-free
fragment required by the Robinson solution theorem. -/
theorem LeaAtomInHEImage.noFloat
    {leaAtom : Metta.Atom} (h : LeaAtomInHEImage leaAtom) :
    MettaAtomNoFloat leaAtom := by
  obtain ⟨atom, rfl⟩ := h
  exact toLeaTTaAtom_noFloat atom

/-- Worklist companion to `LeaAtomInHEImage.noFloat`. -/
theorem LeaEquationsInHEImage.noFloat
    {equations : List (Metta.Atom × Metta.Atom)}
    (h : LeaEquationsInHEImage equations) :
    ∀ equation ∈ equations,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2 := by
  intro equation hmem
  exact ⟨(h equation hmem).1.noFloat, (h equation hmem).2.noFloat⟩

@[simp] theorem LeaAtomInHEImage.translation (atom : Atom) :
    LeaAtomInHEImage (toLeaTTaAtom atom) :=
  ⟨atom, rfl⟩

/-- Zipping two translated HE atom lists yields an equation worklist wholly
inside the exact HE image, independently of whether the two lists have equal
length. -/
theorem leaEquationsInHEImage_zip_translations
    (left right : List Atom) :
    LeaEquationsInHEImage
      (List.zip (toLeaTTaAtoms left) (toLeaTTaAtoms right)) := by
  induction left generalizing right with
  | nil => intro equation hmem; simp [toLeaTTaAtoms] at hmem
  | cons leftHead leftTail ih =>
      cases right with
      | nil => intro equation hmem; simp [toLeaTTaAtoms] at hmem
      | cons rightHead rightTail =>
          intro equation hmem
          simp only [toLeaTTaAtoms, List.zip_cons_cons,
            List.mem_cons] at hmem
          rcases hmem with rfl | htail
          · exact ⟨LeaAtomInHEImage.translation leftHead,
              LeaAtomInHEImage.translation rightHead⟩
          · exact ih rightTail equation htail

/-- Exact-image witnesses are unique.  This lets a generalized Robinson
worklist recursion recover the original HE atom at its singleton-equation
boundary without imposing any analogous uniqueness on matcher bindings. -/
theorem LeaAtomInHEImage.witness_unique
    {leaAtom : Metta.Atom} {left right : Atom}
    (hleft : toLeaTTaAtom left = leaAtom)
    (hright : toLeaTTaAtom right = leaAtom) :
    left = right :=
  toLeaTTaAtom_injective (hleft.trans hright.symm)

mutual

/-- Class-relative atom provenance still implies membership in the exact
translation image: variable representatives may change, but both endpoints
are HE variables. -/
def HELeaAtomClassRel.inHEImage
    {b : Bindings} {atom : Atom} {leaAtom : Metta.Atom}
    (h : HELeaAtomClassRel b atom leaAtom) :
    LeaAtomInHEImage leaAtom :=
  match h with
  | .symbol name => ⟨.symbol name, rfl⟩
  | .variable (left := _) (right := right) _ => ⟨.var right, rfl⟩
  | .grounded value => ⟨.grounded value, rfl⟩
  | .expression hatoms =>
      let ⟨atoms, hatoms⟩ := HELeaAtomClassRel.forall₂_inHEImage hatoms
      ⟨.expression atoms, congrArg Metta.Atom.expr hatoms⟩

/-- List companion to exact-image extraction. -/
def HELeaAtomClassRel.forall₂_inHEImage
    {b : Bindings} {atoms : List Atom} {leaAtoms : List Metta.Atom}
    (h : List.Forall₂ (HELeaAtomClassRel b) atoms leaAtoms) :
    ∃ exactAtoms : List Atom, toLeaTTaAtoms exactAtoms = leaAtoms :=
  match h with
  | .nil => ⟨[], rfl⟩
  | .cons hatom hrest =>
      let ⟨atom, hatom⟩ := hatom.inHEImage
      let ⟨rest, hrest⟩ := HELeaAtomClassRel.forall₂_inHEImage hrest
      ⟨atom :: rest, congrArg₂ List.cons hatom hrest⟩

end

private theorem leaVal_mem_of_lookupVal_eq_some
    {bindings : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hlookup : Metta.Bindings.lookupVal bindings key = some value) :
    Metta.BindingRel.val key value ∈ bindings := by
  induction bindings with
  | nil => simp [Metta.Bindings.lookupVal] at hlookup
  | cons relation bindings ih =>
      cases relation with
      | eq left right =>
          exact List.mem_cons_of_mem _
            (ih (by simpa [Metta.Bindings.lookupVal] using hlookup))
      | val storedKey storedValue =>
          by_cases hkey : key = storedKey
          · subst storedKey
            simp [Metta.Bindings.lookupVal] at hlookup
            subst storedValue
            simp
          · have hbeq : (key == storedKey) = false := by simp [hkey]
            exact List.mem_cons_of_mem _
              (ih (by simpa [Metta.Bindings.lookupVal, hbeq] using hlookup))

/-- Every repaired-LeaTTa class value paired by `LeaBindingCongruence` lies
in the exact HE translation image, even when its key and variables use a
different representative of the same class. -/
theorem leaClassValue_inHEImage_of_congruence
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaBindingCongruence b lb) {key : String} {value : Metta.Atom}
    (hvalue : value ∈ Metta.Bindings.classValues lb key) :
    LeaAtomInHEImage value := by
  unfold Metta.Bindings.classValues at hvalue
  rcases List.mem_filterMap.mp hvalue with
    ⟨storedKey, _hclass, hlookup⟩
  have hbinding : Metta.BindingRel.val storedKey value ∈ lb :=
    leaVal_mem_of_lookupVal_eq_some hlookup
  obtain ⟨heKey, heValue, _hassignment, _hkeyClass, hatom⟩ :=
    h.classValues.2 storedKey value hbinding
  exact hatom.inHEImage

mutual

/-- HE-side syntactic substitution used only to witness closure of the
translation image under LeaTTa's singleton substitution. -/
private def substituteHEAtom (key : String) (replacement : Atom) : Atom → Atom
  | .symbol name => .symbol name
  | .var name => if name == key then replacement else .var name
  | .grounded value => .grounded value
  | .expression atoms => .expression
      (substituteHEAtoms key replacement atoms)

private def substituteHEAtoms
    (key : String) (replacement : Atom) : List Atom → List Atom
  | [] => []
  | atom :: atoms =>
      substituteHEAtom key replacement atom ::
        substituteHEAtoms key replacement atoms

end


mutual

private theorem toLeaTTaAtom_substituteHEAtom
    (key : String) (replacement atom : Atom) :
    toLeaTTaAtom (substituteHEAtom key replacement atom) =
      Metta.Subst.apply [(key, toLeaTTaAtom replacement)]
        (toLeaTTaAtom atom) := by
  cases atom with
  | symbol name => simp [substituteHEAtom, toLeaTTaAtom, Metta.Subst.apply]
  | var name =>
      by_cases h : name = key
      · subst name
        simp [substituteHEAtom, toLeaTTaAtom, Metta.Subst.apply,
          Metta.Subst.lookup]
      · have hbeq : (name == key) = false := by simp [h]
        simp [substituteHEAtom, toLeaTTaAtom, Metta.Subst.apply,
          Metta.Subst.lookup, hbeq]
  | grounded value =>
      simp [substituteHEAtom, toLeaTTaAtom, Metta.Subst.apply]
  | expression atoms =>
      simp only [substituteHEAtom, toLeaTTaAtom, Metta.Subst.apply]
      rw [toLeaTTaAtoms_substituteHEAtoms]
termination_by 2 * sizeOf atom

private theorem toLeaTTaAtoms_substituteHEAtoms
    (key : String) (replacement : Atom) (atoms : List Atom) :
    toLeaTTaAtoms (substituteHEAtoms key replacement atoms) =
      (toLeaTTaAtoms atoms).map
        (Metta.Subst.apply [(key, toLeaTTaAtom replacement)]) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [substituteHEAtoms, toLeaTTaAtoms, List.map]
      exact congrArg₂ List.cons
        (toLeaTTaAtom_substituteHEAtom key replacement atom)
        (toLeaTTaAtoms_substituteHEAtoms key replacement atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by all_goals simp_wf <;> omega

end


/-- Singleton substitution preserves the exact HE translation image. -/
theorem LeaAtomInHEImage.apply_singleton
    {atom term : Metta.Atom} {key : String}
    (hatom : LeaAtomInHEImage atom)
    (hterm : LeaAtomInHEImage term) :
    LeaAtomInHEImage (Metta.Subst.apply [(key, term)] atom) := by
  obtain ⟨heAtom, rfl⟩ := hatom
  obtain ⟨heTerm, rfl⟩ := hterm
  exact ⟨substituteHEAtom key heTerm heAtom,
    toLeaTTaAtom_substituteHEAtom key heTerm heAtom⟩

/-- Extending a substitution by an image term preserves the image invariant. -/
theorem LeaSubstInHEImage.extend
    {subst : Metta.Subst} {key : String} {term : Metta.Atom}
    (hsubst : LeaSubstInHEImage subst)
    (hterm : LeaAtomInHEImage term) :
    LeaSubstInHEImage (Metta.Subst.extend subst key term) := by
  intro storedKey storedTerm hmem
  simp only [Metta.Subst.extend, List.mem_cons] at hmem
  rcases hmem with hhead | htail
  · have : storedTerm = term := congrArg Prod.snd hhead
    simpa [this] using hterm
  · exact hsubst storedKey storedTerm (List.mem_filter.mp htail).1

private theorem LeaConstraintsInHEImage.nil :
    LeaConstraintsInHEImage [] := by
  intro key term hmem
  simp at hmem

private theorem LeaConstraintsInHEImage.singleton_translation
    (key : String) (atom : Atom) :
    LeaConstraintsInHEImage [(key, toLeaTTaAtom atom)] := by
  intro storedKey term hmem
  simp only [List.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩
  exact LeaAtomInHEImage.translation atom

private theorem LeaConstraintsInHEImage.append
    {left right : List (String × Metta.Atom)}
    (hleft : LeaConstraintsInHEImage left)
    (hright : LeaConstraintsInHEImage right) :
    LeaConstraintsInHEImage (left ++ right) := by
  intro key term hmem
  exact (List.mem_append.mp hmem).elim
    (hleft key term) (hright key term)

mutual

/-- Structural decomposition of translated HE atoms cannot manufacture a
constraint term outside the HE atom image. -/
private theorem decomposeEq_toLeaTTa_inHEImage
    (left right : Atom) {constraints : List (String × Metta.Atom)}
    (hdecompose : Metta.Unify.decomposeEq
      (toLeaTTaAtom left) (toLeaTTaAtom right) = some constraints) :
    LeaConstraintsInHEImage constraints := by
  cases left with
  | symbol leftName =>
      cases right with
      | symbol rightName =>
          simp only [toLeaTTaAtom, Metta.Unify.decomposeEq] at hdecompose
          split at hdecompose
          · cases hdecompose
            exact LeaConstraintsInHEImage.nil
          · contradiction
      | var rightName =>
          simp only [toLeaTTaAtom, Metta.Unify.decomposeEq,
            Option.some.injEq] at hdecompose
          subst constraints
          exact LeaConstraintsInHEImage.singleton_translation
            rightName (.symbol leftName)
      | grounded rightValue | expression rightValue =>
          simp [toLeaTTaAtom, Metta.Unify.decomposeEq] at hdecompose
  | var leftName =>
      cases right with
      | var rightName =>
          simp only [toLeaTTaAtom, Metta.Unify.decomposeEq] at hdecompose
          split at hdecompose
          · cases hdecompose
            exact LeaConstraintsInHEImage.nil
          · simp only [Option.some.injEq] at hdecompose
            subst constraints
            exact LeaConstraintsInHEImage.singleton_translation
              leftName (.var rightName)
      | symbol rightName =>
          simp only [toLeaTTaAtom, Metta.Unify.decomposeEq,
            Option.some.injEq] at hdecompose
          subst constraints
          exact LeaConstraintsInHEImage.singleton_translation
            leftName (.symbol rightName)
      | grounded rightValue =>
          simp only [toLeaTTaAtom, Metta.Unify.decomposeEq,
            Option.some.injEq] at hdecompose
          subst constraints
          exact LeaConstraintsInHEImage.singleton_translation
            leftName (.grounded rightValue)
      | expression rightAtoms =>
          simp only [toLeaTTaAtom, Metta.Unify.decomposeEq,
            Option.some.injEq] at hdecompose
          subst constraints
          exact LeaConstraintsInHEImage.singleton_translation
            leftName (.expression rightAtoms)
  | grounded leftValue =>
      cases right with
      | var rightName =>
          simp only [toLeaTTaAtom, Metta.Unify.decomposeEq,
            Option.some.injEq] at hdecompose
          subst constraints
          exact LeaConstraintsInHEImage.singleton_translation
            rightName (.grounded leftValue)
      | grounded rightValue =>
          simp only [toLeaTTaAtom, Metta.Unify.decomposeEq] at hdecompose
          split at hdecompose
          · cases hdecompose
            exact LeaConstraintsInHEImage.nil
          · contradiction
      | symbol rightName | expression rightName =>
          simp [toLeaTTaAtom, Metta.Unify.decomposeEq] at hdecompose
  | expression leftAtoms =>
      cases right with
      | var rightName =>
          simp only [toLeaTTaAtom, Metta.Unify.decomposeEq,
            Option.some.injEq] at hdecompose
          subst constraints
          exact LeaConstraintsInHEImage.singleton_translation
            rightName (.expression leftAtoms)
      | expression rightAtoms =>
          exact decomposeList_toLeaTTa_inHEImage
            leftAtoms rightAtoms hdecompose
      | symbol rightName | grounded rightName =>
          simp [toLeaTTaAtom, Metta.Unify.decomposeEq] at hdecompose
termination_by 2 * (sizeOf left + sizeOf right)

/-- Pointwise-list companion to image preservation by decomposition. -/
private theorem decomposeList_toLeaTTa_inHEImage
    (left right : List Atom) {constraints : List (String × Metta.Atom)}
    (hdecompose : Metta.Unify.decomposeList
      (toLeaTTaAtoms left) (toLeaTTaAtoms right) = some constraints) :
    LeaConstraintsInHEImage constraints := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          simp [toLeaTTaAtoms, Metta.Unify.decomposeList] at hdecompose
          subst constraints
          exact LeaConstraintsInHEImage.nil
      | cons rightHead rightTail =>
          simp [toLeaTTaAtoms, Metta.Unify.decomposeList] at hdecompose
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          simp [toLeaTTaAtoms, Metta.Unify.decomposeList] at hdecompose
      | cons rightHead rightTail =>
          simp only [toLeaTTaAtoms, Metta.Unify.decomposeList] at hdecompose
          cases hhead : Metta.Unify.decomposeEq
              (toLeaTTaAtom leftHead) (toLeaTTaAtom rightHead) with
          | none => simp [hhead] at hdecompose
          | some headConstraints =>
              cases htail : Metta.Unify.decomposeList
                  (toLeaTTaAtoms leftTail) (toLeaTTaAtoms rightTail) with
              | none => simp [hhead, htail] at hdecompose
              | some tailConstraints =>
                  simp only [hhead, htail, Option.some.injEq] at hdecompose
                  subst constraints
                  exact LeaConstraintsInHEImage.append
                    (decomposeEq_toLeaTTa_inHEImage
                      leftHead rightHead hhead)
                    (decomposeList_toLeaTTa_inHEImage
                      leftTail rightTail htail)
termination_by 2 * (sizeOf left + sizeOf right) + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_all
  all_goals omega

end

private theorem decomposeEq_inHEImage
    {left right : Metta.Atom}
    {constraints : List (String × Metta.Atom)}
    (hleft : LeaAtomInHEImage left)
    (hright : LeaAtomInHEImage right)
    (hdecompose : Metta.Unify.decomposeEq left right = some constraints) :
    LeaConstraintsInHEImage constraints := by
  obtain ⟨heLeft, rfl⟩ := hleft
  obtain ⟨heRight, rfl⟩ := hright
  exact decomposeEq_toLeaTTa_inHEImage heLeft heRight hdecompose

/-- Whole-worklist decomposition preserves the exact HE translation image. -/
theorem decomposeAll_inHEImage
    {equations : List (Metta.Atom × Metta.Atom)}
    {constraints : List (String × Metta.Atom)}
    (hequations : LeaEquationsInHEImage equations)
    (hdecompose : Metta.Unify.decomposeAll equations = some constraints) :
    LeaConstraintsInHEImage constraints := by
  induction equations generalizing constraints with
  | nil =>
      simp [Metta.Unify.decomposeAll] at hdecompose
      subst constraints
      exact LeaConstraintsInHEImage.nil
  | cons equation equations ih =>
      rcases equation with ⟨left, right⟩
      have hheadImage :
          LeaAtomInHEImage left ∧ LeaAtomInHEImage right :=
        hequations (left, right) (by simp)
      have htailImage : LeaEquationsInHEImage equations := by
        intro tailEquation hmem
        exact hequations tailEquation (List.mem_cons_of_mem _ hmem)
      simp only [Metta.Unify.decomposeAll] at hdecompose
      cases hhead : Metta.Unify.decomposeEq left right with
      | none => simp [hhead] at hdecompose
      | some headConstraints =>
          cases htail : Metta.Unify.decomposeAll equations with
          | none => simp [hhead, htail] at hdecompose
          | some tailConstraints =>
              simp only [hhead, htail, Option.some.injEq] at hdecompose
              subst constraints
              exact LeaConstraintsInHEImage.append
                (decomposeEq_inHEImage
                  hheadImage.1 hheadImage.2 hhead)
                (ih htailImage htail)

/-- Applying one exact-image Robinson elimination to a decomposed constraint
list produces an exact-image equation worklist. -/
private theorem LeaConstraintsInHEImage.substituteAsEquations
    {constraints : List (String × Metta.Atom)}
    (hconstraints : LeaConstraintsInHEImage constraints)
    {key : String} {term : Metta.Atom}
    (hterm : LeaAtomInHEImage term) :
    LeaEquationsInHEImage
      (constraints.map fun constraint =>
        (Metta.Subst.apply [(key, term)] (.var constraint.1),
          Metta.Subst.apply [(key, term)] constraint.2)) := by
  intro equation hequation
  obtain ⟨constraint, hconstraint, rfl⟩ :=
    List.mem_map.mp hequation
  exact
    ⟨(LeaAtomInHEImage.translation
        (.var constraint.1)).apply_singleton hterm,
      (hconstraints constraint.1 constraint.2
        hconstraint).apply_singleton hterm⟩

/-- Exact HE-image provenance is retained at the recursive boundary of a
Robinson prefix split.  Both components of the smaller operational state are
proved together: transformed residual equations and the accumulated prefix
substitution.  This is the state-closure premise needed by the direct
strict-fuel original-matcher recursion. -/
theorem UnifyRoundsPrefixSplit.state_inHEImage
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst)
    (hfrontImage : LeaEquationsInHEImage front)
    (hsuffixImage : LeaEquationsInHEImage suffix)
    (hsubstImage : LeaSubstInHEImage subst) :
    LeaEquationsInHEImage suffixWork ∧
      LeaSubstInHEImage prefixSubst := by
  induction h with
  | solved => exact ⟨hsuffixImage, hsubstImage⟩
  | @eliminate fuel front suffix subst key term rest suffixConstraints
      remainingFuel suffixWork prefixSubst hfront hsuffix _hoccurs htail ih =>
      have hallFront : LeaConstraintsInHEImage ((key, term) :: rest) :=
        decomposeAll_inHEImage hfrontImage hfront
      have hterm : LeaAtomInHEImage term :=
        hallFront key term (by simp)
      have hrest : LeaConstraintsInHEImage rest := by
        intro storedKey storedTerm hmem
        exact hallFront storedKey storedTerm
          (List.mem_cons_of_mem _ hmem)
      have hallSuffix : LeaConstraintsInHEImage suffixConstraints :=
        decomposeAll_inHEImage hsuffixImage hsuffix
      exact ih (hrest.substituteAsEquations hterm)
        (hallSuffix.substituteAsEquations hterm)
        (hsubstImage.extend hterm)

/-- Residual-worklist projection of `state_inHEImage`. -/
theorem UnifyRoundsPrefixSplit.suffixWork_inHEImage
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst)
    (hfrontImage : LeaEquationsInHEImage front)
    (hsuffixImage : LeaEquationsInHEImage suffix)
    (hsubstImage : LeaSubstInHEImage subst) :
    LeaEquationsInHEImage suffixWork :=
  (h.state_inHEImage hfrontImage hsuffixImage hsubstImage).1

/-- Prefix-substitution projection of `state_inHEImage`. -/
theorem UnifyRoundsPrefixSplit.prefixSubst_inHEImage
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst)
    (hfrontImage : LeaEquationsInHEImage front)
    (hsuffixImage : LeaEquationsInHEImage suffix)
    (hsubstImage : LeaSubstInHEImage subst) :
    LeaSubstInHEImage prefixSubst :=
  (h.state_inHEImage hfrontImage hsuffixImage hsubstImage).2

/-- The exact residual state of prefix factorization has the same valuation
theory as the original prefixed state.  This is the representation-independent
continuation invariant: it compares equation solutions, not one-pass
substitution syntax, representative chronology, or a chosen MGU. -/
theorem UnifyRoundsPrefixSplit.continuation_solution_iff
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst result : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst)
    (hfrontImage : LeaEquationsInHEImage front)
    (hsuffixImage : LeaEquationsInHEImage suffix)
    (hsubstImage : LeaSubstInHEImage subst)
    (hfresh : UnifyStateFresh (front ++ suffix) subst)
    (hcontinue : Metta.Unify.unifyRounds remainingFuel suffixWork
      prefixSubst = some result)
    (valuation : String → Metta.Atom) :
    (MettaEquationsSatisfied valuation suffixWork ∧
        MettaConstraintsSatisfied valuation prefixSubst) ↔
      (MettaEquationsSatisfied valuation (front ++ suffix) ∧
        MettaConstraintsSatisfied valuation subst) := by
  have hstateImage :=
    h.state_inHEImage hfrontImage hsuffixImage hsubstImage
  have hfullNoFloat : ∀ equation ∈ front ++ suffix,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2 := by
    intro equation hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact ⟨(hfrontImage equation hmem).1.noFloat,
        (hfrontImage equation hmem).2.noFloat⟩
    · exact ⟨(hsuffixImage equation hmem).1.noFloat,
        (hsuffixImage equation hmem).2.noFloat⟩
  have hresidualNoFloat : ∀ equation ∈ suffixWork,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2 :=
    hstateImage.1.noFloat
  have hresidualFresh : UnifyStateFresh suffixWork prefixSubst :=
    h.stateFresh hfresh
  have hfullRun : Metta.Unify.unifyRounds fuel (front ++ suffix) subst =
      some result := by
    rw [h.run_eq]
    exact hcontinue
  exact
    (unifyRounds_solution_iff valuation hresidualNoFloat
      hresidualFresh hcontinue).symm.trans
        (unifyRounds_solution_iff valuation hfullNoFloat hfresh hfullRun)

/-- Live-accumulator form of the continuation invariant.  Any HE binding
record congruent to the prefix substitution may replace that substitution in
the residual state.  This is the seam required by original list matching:
the tail is interpreted under the actual accumulated matcher output, while
the right side still denotes the untouched original equation state. -/
theorem UnifyRoundsPrefixSplit.heContinuation_solution_iff
    {fuel : Nat} {front suffix : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst result : Metta.Subst} {seed : Bindings}
    (h : UnifyRoundsPrefixSplit fuel front suffix subst
      remainingFuel suffixWork prefixSubst)
    (hfrontImage : LeaEquationsInHEImage front)
    (hsuffixImage : LeaEquationsInHEImage suffix)
    (hsubstImage : LeaSubstInHEImage subst)
    (hfresh : UnifyStateFresh (front ++ suffix) subst)
    (hcontinue : Metta.Unify.unifyRounds remainingFuel suffixWork
      prefixSubst = some result)
    (hseed : LeaBindingCongruence seed
      (Metta.Bindings.ofSubst prefixSubst))
    (valuation : String → Metta.Atom) :
    (MettaEquationsSatisfied valuation suffixWork ∧
        HEBindingSatisfied valuation seed) ↔
      (MettaEquationsSatisfied valuation (front ++ suffix) ∧
        MettaConstraintsSatisfied valuation subst) := by
  calc
    (MettaEquationsSatisfied valuation suffixWork ∧
        HEBindingSatisfied valuation seed) ↔
      (MettaEquationsSatisfied valuation suffixWork ∧
        LeaBindingSatisfied valuation
          (Metta.Bindings.ofSubst prefixSubst)) :=
      and_congr Iff.rfl (hseed.semantic.solutions valuation)
    _ ↔ (MettaEquationsSatisfied valuation suffixWork ∧
        MettaConstraintsSatisfied valuation prefixSubst) :=
      and_congr Iff.rfl (leaOfSubst_solution_iff valuation prefixSubst)
    _ ↔ (MettaEquationsSatisfied valuation (front ++ suffix) ∧
        MettaConstraintsSatisfied valuation subst) :=
      h.continuation_solution_iff hfrontImage hsuffixImage hsubstImage
        hfresh hcontinue valuation

/-- A successful unequal expression-head split exposes the complete smaller
operational state needed by the original matcher induction.  Besides strict
fuel descent, the result retains the exact trace partition and proves that
both components of the transformed continuation stay inside the HE language
image.  Nothing here replaces the original expression matcher by the
canonical reverse-trace replay. -/
theorem exists_expression_head_split_strict_state_inHEImage
    {fuel : Nat} {leftHead rightHead : Metta.Atom}
    {leftTail rightTail : List Metta.Atom} {subst result : Metta.Subst}
    (hleftImage : LeaAtomInHEImage leftHead)
    (hrightImage : LeaAtomInHEImage rightHead)
    (htailImage : LeaEquationsInHEImage (List.zip leftTail rightTail))
    (hsubstImage : LeaSubstInHEImage subst)
    (hne : leftHead ≠ rightHead)
    (hlength : leftTail.length = rightTail.length)
    (hrun : Metta.Unify.unifyRounds fuel
      [(.expr (leftHead :: leftTail), .expr (rightHead :: rightTail))]
      subst = some result) :
    ∃ remainingFuel tailWork headSubst,
      UnifyRoundsPrefixSplit fuel [(leftHead, rightHead)]
          (List.zip leftTail rightTail) subst
          remainingFuel tailWork headSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork headSubst =
          some result ∧
        remainingFuel < fuel ∧
        unificationEliminationTrace fuel
            ([(leftHead, rightHead)] ++ List.zip leftTail rightTail) =
          unificationEliminationTrace fuel [(leftHead, rightHead)] ++
            unificationEliminationTrace remainingFuel tailWork ∧
        LeaEquationsInHEImage tailWork ∧
        LeaSubstInHEImage headSubst := by
  have hleftNoFloat : MettaAtomNoFloat leftHead := by
    obtain ⟨left, rfl⟩ := hleftImage
    exact toLeaTTaAtom_noFloat left
  have hrightNoFloat : MettaAtomNoFloat rightHead := by
    obtain ⟨right, rfl⟩ := hrightImage
    exact toLeaTTaAtom_noFloat right
  obtain ⟨remainingFuel, tailWork, headSubst,
      hsplit, hcontinue, hlt⟩ :=
    unifyRounds_expression_head_split_strict_of_ne
      hleftNoFloat hrightNoFloat hne hlength hrun
  have hfrontImage : LeaEquationsInHEImage [(leftHead, rightHead)] := by
    intro equation hmem
    simp only [List.mem_singleton] at hmem
    subst equation
    exact ⟨hleftImage, hrightImage⟩
  have hstateImage := hsplit.state_inHEImage
    hfrontImage htailImage hsubstImage
  exact ⟨remainingFuel, tailWork, headSubst,
    hsplit, hcontinue, hlt, hsplit.trace_append,
    hstateImage.1, hstateImage.2⟩

/-- HE-facing specialization of the strict expression-head state theorem.
The worklist is the literal translation of the original HE expression pair,
so exact-image premises for the head and zipped tail are discharged by the
embedding itself. -/
theorem exists_translated_expression_head_split_strict_state
    {fuel : Nat} {leftHead rightHead : Atom}
    {leftTail rightTail : List Atom} {subst result : Metta.Subst}
    (hsubstImage : LeaSubstInHEImage subst)
    (hne : leftHead ≠ rightHead)
    (hlength : leftTail.length = rightTail.length)
    (hrun : Metta.Unify.unifyRounds fuel
      [(.expr (toLeaTTaAtoms (leftHead :: leftTail)),
        .expr (toLeaTTaAtoms (rightHead :: rightTail)))]
      subst = some result) :
    ∃ remainingFuel tailWork headSubst,
      UnifyRoundsPrefixSplit fuel
          [(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)]
          (List.zip (toLeaTTaAtoms leftTail)
            (toLeaTTaAtoms rightTail)) subst
          remainingFuel tailWork headSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork headSubst =
          some result ∧
        remainingFuel < fuel ∧
        unificationEliminationTrace fuel
            ([(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)] ++
              List.zip (toLeaTTaAtoms leftTail)
                (toLeaTTaAtoms rightTail)) =
          unificationEliminationTrace fuel
              [(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)] ++
            unificationEliminationTrace remainingFuel tailWork ∧
        LeaEquationsInHEImage tailWork ∧
        LeaSubstInHEImage headSubst := by
  have hneTranslation :
      toLeaTTaAtom leftHead ≠ toLeaTTaAtom rightHead := by
    intro heq
    exact hne (toLeaTTaAtom_injective heq)
  have htailLength :
      (toLeaTTaAtoms leftTail).length =
        (toLeaTTaAtoms rightTail).length := by
    rw [length_toLeaTTaAtoms, length_toLeaTTaAtoms]
    exact hlength
  simpa only [toLeaTTaAtoms] using
    (exists_expression_head_split_strict_state_inHEImage
      (hleftImage := LeaAtomInHEImage.translation leftHead)
      (hrightImage := LeaAtomInHEImage.translation rightHead)
      (htailImage :=
        leaEquationsInHEImage_zip_translations leftTail rightTail)
      hsubstImage hneTranslation htailLength hrun)

/-- Complete strict-state view of any unequal successful translated
expression equation.  It separates the maximal common child prefix, returns
the first original unequal child pair, and supplies the exact smaller
Robinson continuation at that point.  Equal prefix children remain available
for structural reflexive HE matching; they are not erased from the eventual
matcher derivation. -/
theorem exists_translated_expression_firstDivergence_strict_state
    {fuel : Nat} {left right : List Atom} {subst result : Metta.Subst}
    (hsubstImage : LeaSubstInHEImage subst)
    (hne : left ≠ right)
    (hrun : Metta.Unify.unifyRounds fuel
      [(.expr (toLeaTTaAtoms left), .expr (toLeaTTaAtoms right))]
      subst = some result) :
    ∃ common leftHead leftTail rightHead rightTail
        remainingFuel tailWork childSubst,
      left = common ++ leftHead :: leftTail ∧
        right = common ++ rightHead :: rightTail ∧
        leftHead ≠ rightHead ∧
        leftTail.length = rightTail.length ∧
        UnifyRoundsPrefixSplit fuel
            [(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)]
            (List.zip (toLeaTTaAtoms leftTail)
              (toLeaTTaAtoms rightTail)) subst
            remainingFuel tailWork childSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork childSubst =
          some result ∧
        remainingFuel < fuel ∧
        unificationEliminationTrace fuel
            ([(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)] ++
              List.zip (toLeaTTaAtoms leftTail)
                (toLeaTTaAtoms rightTail)) =
          unificationEliminationTrace fuel
              [(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)] ++
            unificationEliminationTrace remainingFuel tailWork ∧
        LeaEquationsInHEImage tailWork ∧
        LeaSubstInHEImage childSubst := by
  obtain ⟨common, leftHead, leftTail, rightHead, rightTail,
      hleft, hright, hheadNe, htailLength, hdivergenceRun⟩ :=
    exists_firstDivergence_unifyRounds_expression_success hne hrun
  obtain ⟨remainingFuel, tailWork, childSubst,
      hsplit, hcontinue, hlt, htrace, htailImage, hchildImage⟩ :=
    exists_translated_expression_head_split_strict_state
      hsubstImage hheadNe htailLength hdivergenceRun
  exact ⟨common, leftHead, leftTail, rightHead, rightTail,
    remainingFuel, tailWork, childSubst,
    hleft, hright, hheadNe, htailLength,
    hsplit, hcontinue, hlt, htrace, htailImage, hchildImage⟩

/-- A nonempty local class unifier from a congruent repaired-LeaTTa binding
exposes an exact-HE-image trace head and the strictly smaller trace tail.  The
proof uses class membership only; class list order chooses the operational
Robinson run but carries no semantic meaning. -/
theorem exists_unifyValues_trace_step_inHEImage_of_classValues
    {b : Bindings} {source : Metta.Bindings} {classKey : String}
    {first : Metta.Atom} {rest : List Metta.Atom}
    {localHead : String × Metta.Atom} {localTail : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hclass : Metta.Bindings.classValues source classKey = first :: rest)
    (hunify : Metta.Bindings.unifyValues (first :: rest) =
      some (localHead :: localTail)) :
    ∃ (smallerFuel : Nat) (key : String) (term : Metta.Atom)
        (heTerm : Atom) (remaining : List (String × Metta.Atom)),
      smallerFuel < first.size + (rest.map Metta.Atom.size).sum ∧
        toLeaTTaAtom heTerm = term ∧
        unificationEliminationTrace
            (first.size + (rest.map Metta.Atom.size).sum)
            (rest.map fun value => (first, value)) =
          (key, term) ::
            unificationEliminationTrace smallerFuel
              (remaining.map fun constraint =>
                (Metta.Subst.apply [(key, term)] (.var constraint.1),
                  Metta.Subst.apply [(key, term)] constraint.2)) ∧
        Metta.Unify.unifyRounds smallerFuel
            (remaining.map fun constraint =>
              (Metta.Subst.apply [(key, term)] (.var constraint.1),
                Metta.Subst.apply [(key, term)] constraint.2))
            (Metta.Subst.extend [] key term) =
          some (localHead :: localTail) := by
  obtain ⟨smallerFuel, key, term, remaining, hlt, htotal,
      hdecompose, hoccurs, hrun⟩ :=
    unifyValues_nonempty_success_elimination hunify
  have hallImage : ∀ value ∈ first :: rest, LeaAtomInHEImage value := by
    intro value hvalue
    apply leaClassValue_inHEImage_of_congruence hbase
    rw [hclass]
    exact hvalue
  have hequations : LeaEquationsInHEImage
      (rest.map fun value => (first, value)) := by
    intro equation hequation
    obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp hequation
    exact ⟨hallImage first (by simp), hallImage value (by simp [hvalue])⟩
  have hconstraints := decomposeAll_inHEImage hequations hdecompose
  obtain ⟨heTerm, hterm⟩ :=
    hconstraints key term (by simp)
  refine ⟨smallerFuel, key, term, heTerm, remaining, hlt,
    hterm, ?_, hrun⟩
  rw [htotal]
  exact unificationEliminationTrace_succ_eq_cons hdecompose hoccurs

/-- Successful Robinson elimination preserves exact membership in the HE atom
image, not merely absence of host floats. -/
theorem unifyRounds_result_inHEImage
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hequations : LeaEquationsInHEImage equations)
    (hsubst : LeaSubstInHEImage subst)
    (hunify : Metta.Unify.unifyRounds fuel equations subst = some result) :
    LeaSubstInHEImage result := by
  induction fuel generalizing equations subst result with
  | zero =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none => simp [Metta.Unify.unifyRounds, hdecompose] at hunify
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hunify
              subst result
              exact hsubst
          | cons constraint rest =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hunify
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none => simp [Metta.Unify.unifyRounds, hdecompose] at hunify
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hunify
              subst result
              exact hsubst
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  simp [Metta.Unify.unifyRounds, hdecompose, hoccurs] at hunify
              | false =>
                  let remaining := rest.map fun item =>
                    (Metta.Subst.apply [(key, term)] (.var item.1),
                      Metta.Subst.apply [(key, term)] item.2)
                  have hunify' :
                      Metta.Unify.unifyRounds fuel remaining
                          (Metta.Subst.extend subst key term) = some result := by
                    simpa [Metta.Unify.unifyRounds, hdecompose, hoccurs,
                      remaining] using hunify
                  have hconstraints :
                      LeaConstraintsInHEImage ((key, term) :: rest) :=
                    decomposeAll_inHEImage hequations hdecompose
                  have hterm : LeaAtomInHEImage term :=
                    hconstraints key term (by simp)
                  have hequations' : LeaEquationsInHEImage remaining := by
                    intro equation hmem
                    obtain ⟨item, hitem, rfl⟩ := List.mem_map.mp hmem
                    have hitemTerm : LeaAtomInHEImage item.2 :=
                      hconstraints item.1 item.2
                        (List.mem_cons_of_mem _ hitem)
                    exact
                      ⟨LeaAtomInHEImage.apply_singleton
                          (LeaAtomInHEImage.translation (.var item.1)) hterm,
                        hitemTerm.apply_singleton hterm⟩
                  exact ih hequations'
                    (hsubst.extend hterm) hunify'

/-- A successful fresh-state Robinson trace consists entirely of terms in
the HE atom image whenever its source equations do.  This consumes the landed
reverse-trace characterization instead of re-running a second trace induction. -/
theorem unificationEliminationTrace_inHEImage_of_success
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {result : Metta.Subst}
    (hequations : LeaEquationsInHEImage equations)
    (hunify : Metta.Unify.unifyRounds fuel equations [] = some result) :
    LeaConstraintsInHEImage
      (unificationEliminationTrace fuel equations) := by
  have hresultImage : LeaSubstInHEImage result :=
    unifyRounds_result_inHEImage hequations
      (by intro key term hmem; simp at hmem) hunify
  have hresultEq : result =
      (unificationEliminationTrace fuel equations).reverse := by
    simpa using
      (unifyRounds_result_eq_eliminationTrace_reverse_append
        (by simp [UnifyStateFresh, mettaSubstKeys]) hunify)
  intro key term hmem
  apply hresultImage key term
  rw [hresultEq]
  simpa using hmem

/-- The complete local class-unification trace is HE-image-valued under the
settled class-provenance invariant. -/
theorem unifyValues_trace_inHEImage_of_classValues
    {b : Bindings} {source : Metta.Bindings} {classKey : String}
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hclass : Metta.Bindings.classValues source classKey =
      first :: second :: rest)
    (hunify : Metta.Bindings.unifyValues
      (first :: second :: rest) = some result) :
    LeaConstraintsInHEImage
      (unificationEliminationTrace
        (first.size + ((second :: rest).map Metta.Atom.size).sum)
        ((second :: rest).map fun value => (first, value))) := by
  have hallImage : ∀ value ∈ first :: second :: rest,
      LeaAtomInHEImage value := by
    intro value hvalue
    apply leaClassValue_inHEImage_of_congruence hbase
    rw [hclass]
    exact hvalue
  have hequations : LeaEquationsInHEImage
      ((second :: rest).map fun value => (first, value)) := by
    intro equation hequation
    obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp hequation
    exact ⟨hallImage first (by simp),
      hallImage value (by simp [hvalue])⟩
  exact unificationEliminationTrace_inHEImage_of_success
    hequations (unifyValues_cons_cons_success_run hunify)

/-- Class provenance upgrades the nonempty strict prefix split to an exact
HE-image prefix.  Thus every constraint assigned to the recursive head
matcher has a translation witness, while the residual state remains strictly
smaller and untouched. -/
theorem exists_unifyValues_nonempty_trace_split_inHEImage_of_classValues
    {b : Bindings} {source : Metta.Bindings} {classKey : String}
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hclass : Metta.Bindings.classValues source classKey =
      first :: second :: rest)
    (hne : first ≠ second)
    (hunify : Metta.Bindings.unifyValues
      (first :: second :: rest) = some result) :
    ∃ remainingFuel tailWork headSubst entry prefixTail,
      UnifyRoundsPrefixSplit
          (first.size + ((second :: rest).map Metta.Atom.size).sum)
          [(first, second)]
          (rest.map fun value => (first, value)) []
          remainingFuel tailWork headSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork headSubst =
          some result ∧
        remainingFuel <
          first.size + ((second :: rest).map Metta.Atom.size).sum ∧
        unificationEliminationTrace
            (first.size + ((second :: rest).map Metta.Atom.size).sum)
            ((second :: rest).map fun value => (first, value)) =
          entry :: prefixTail ++
            unificationEliminationTrace remainingFuel tailWork ∧
        LeaConstraintsInHEImage (entry :: prefixTail) := by
  have hfirstImage : LeaAtomInHEImage first :=
    leaClassValue_inHEImage_of_congruence hbase (by
      rw [hclass]
      simp)
  have hsecondImage : LeaAtomInHEImage second :=
    leaClassValue_inHEImage_of_congruence hbase (by
      rw [hclass]
      simp)
  obtain ⟨heFirst, hheFirst⟩ := hfirstImage
  obtain ⟨heSecond, hheSecond⟩ := hsecondImage
  have hfirstNoFloat : MettaAtomNoFloat first := by
    rw [← hheFirst]
    exact toLeaTTaAtom_noFloat heFirst
  have hsecondNoFloat : MettaAtomNoFloat second := by
    rw [← hheSecond]
    exact toLeaTTaAtom_noFloat heSecond
  obtain ⟨remainingFuel, tailWork, headSubst, entry, prefixTail,
      hsplit, hcontinue, hlt, htrace⟩ :=
    unifyValues_cons_cons_nonempty_trace_split_of_ne
      hfirstNoFloat hsecondNoFloat hne hunify
  have hfullImage :=
    unifyValues_trace_inHEImage_of_classValues
      hbase hclass hunify
  have hprefixImage : LeaConstraintsInHEImage
      (entry :: prefixTail) := by
    intro key term hmem
    apply hfullImage key term
    rw [htrace]
    exact List.mem_append_left _ hmem
  exact ⟨remainingFuel, tailWork, headSubst, entry, prefixTail,
    hsplit, hcontinue, hlt, htrace, hprefixImage⟩

/-- Executable head-prefix package for one unequal local class conflict.  It
combines the strict operational split, exact trace partition, HE-image
provenance, and canonical executable replay without identifying that replay's
binding presentation with any matcher MGU. -/
structure LeaUnifyValuesExecutablePrefixWitness
    (first second : Metta.Atom) (rest : List Metta.Atom)
    (result : Metta.Subst) where
  remainingFuel : Nat
  tailWork : List (Metta.Atom × Metta.Atom)
  headSubst : Metta.Subst
  entry : String × Metta.Atom
  prefixTail : List (String × Metta.Atom)
  heOut : Bindings
  first_noFloat : MettaAtomNoFloat first
  second_noFloat : MettaAtomNoFloat second
  equations_inHEImage : LeaEquationsInHEImage
    ((second :: rest).map fun value => (first, value))
  split : UnifyRoundsPrefixSplit
    (first.size + ((second :: rest).map Metta.Atom.size).sum)
    [(first, second)] (rest.map fun value => (first, value)) []
    remainingFuel tailWork headSubst
  continue_run : Metta.Unify.unifyRounds remainingFuel tailWork headSubst =
    some result
  fuel_lt : remainingFuel <
    first.size + ((second :: rest).map Metta.Atom.size).sum
  trace_eq : unificationEliminationTrace
      (first.size + ((second :: rest).map Metta.Atom.size).sum)
      ((second :: rest).map fun value => (first, value)) =
    entry :: prefixTail ++
      unificationEliminationTrace remainingFuel tailWork
  front_trace_eq : unificationEliminationTrace
      (first.size + ((second :: rest).map Metta.Atom.size).sum)
      [(first, second)] = entry :: prefixTail
  headSubst_eq : headSubst = (entry :: prefixTail).reverse
  prefix_inHEImage : LeaConstraintsInHEImage (entry :: prefixTail)
  tailWork_inHEImage : LeaEquationsInHEImage tailWork
  headSubst_inHEImage : LeaSubstInHEImage headSubst
  replay : LeaEliminationTraceExecutableReplay Bindings.empty
    (entry :: prefixTail) heOut

/-- Every unequal successful local class unifier has the executable nonempty
head-prefix package.  This is the concrete recursive input required by the
value-expression progress constructor. -/
theorem exists_unifyValues_executablePrefixWitness_of_classValues
    {b : Bindings} {source : Metta.Bindings} {classKey : String}
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hclass : Metta.Bindings.classValues source classKey =
      first :: second :: rest)
    (hne : first ≠ second)
    (hunify : Metta.Bindings.unifyValues
      (first :: second :: rest) = some result) :
    Nonempty (LeaUnifyValuesExecutablePrefixWitness
      first second rest result) := by
  obtain ⟨remainingFuel, tailWork, headSubst, entry, prefixTail,
      hsplit, hcontinue, hlt, htrace, hprefixImage⟩ :=
    exists_unifyValues_nonempty_trace_split_inHEImage_of_classValues
      hbase hclass hne hunify
  have hrun := unifyValues_cons_cons_success_run hunify
  have htriangular : EliminationTraceTriangular
      (unificationEliminationTrace
        (first.size + ((second :: rest).map Metta.Atom.size).sum)
        ((second :: rest).map fun value => (first, value))) :=
    unificationEliminationTrace_triangular_of_success
      (by simp [UnifyStateFresh, mettaSubstKeys]) hrun
  rw [htrace] at htriangular
  have hprefixTriangular : EliminationTraceTriangular
      (entry :: prefixTail) := by
    apply htriangular.left_of_append
  obtain ⟨heOut, hreplay⟩ :=
    exists_eliminationTraceReplay_of_nodup_of_translation
      hprefixTriangular.keys_nodup
      (by
        intro key term hmem
        exact hprefixImage key term hmem)
  have hexecutable : LeaEliminationTraceExecutableReplay Bindings.empty
      (entry :: prefixTail) heOut :=
    hreplay.executable_of_triangular hprefixTriangular
  have hfrontTraceEq : unificationEliminationTrace
      (first.size + ((second :: rest).map Metta.Atom.size).sum)
      [(first, second)] = entry :: prefixTail := by
    apply List.append_cancel_right
      (bs := unificationEliminationTrace remainingFuel tailWork)
    exact hsplit.trace_append.symm.trans htrace
  have hheadSubstEq : headSubst = (entry :: prefixTail).reverse := by
    have hresultEq :=
      unifyRounds_result_eq_eliminationTrace_reverse_append
        (equations := [(first, second)])
        (subst := [])
        (by simp [UnifyStateFresh, mettaSubstKeys])
        hsplit.front_run
    rw [hfrontTraceEq] at hresultEq
    simpa using hresultEq
  have hfirstNoFloat : MettaAtomNoFloat first := by
    obtain ⟨heFirst, hheFirst⟩ :=
      leaClassValue_inHEImage_of_congruence
        (key := classKey) (value := first) hbase (by
        rw [hclass]
        simp)
    rw [← hheFirst]
    exact toLeaTTaAtom_noFloat heFirst
  have hsecondNoFloat : MettaAtomNoFloat second := by
    obtain ⟨heSecond, hheSecond⟩ :=
      leaClassValue_inHEImage_of_congruence
        (key := classKey) (value := second) hbase (by
        rw [hclass]
        simp)
    rw [← hheSecond]
    exact toLeaTTaAtom_noFloat heSecond
  have hequations : LeaEquationsInHEImage
      ((second :: rest).map fun value => (first, value)) := by
    intro equation hequation
    obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp hequation
    exact
      ⟨leaClassValue_inHEImage_of_congruence
          (key := classKey) (value := first) hbase (by
            rw [hclass]
            simp),
        leaClassValue_inHEImage_of_congruence
          (key := classKey) (value := value) hbase (by
            rw [hclass]
            simp [hvalue])⟩
  have hstateImage := hsplit.state_inHEImage
    (by
      intro equation hequation
      simp only [List.mem_singleton] at hequation
      subst equation
      exact
        ⟨leaClassValue_inHEImage_of_congruence
            (key := classKey) (value := first) hbase (by
              rw [hclass]
              simp),
          leaClassValue_inHEImage_of_congruence
            (key := classKey) (value := second) hbase (by
              rw [hclass]
              simp)⟩)
    (by
      intro equation hequation
      apply hequations equation
      obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp hequation
      exact List.mem_map.mpr ⟨value, by simp [hvalue], rfl⟩)
    (by intro key term hmem; simp at hmem)
  exact ⟨{
    remainingFuel := remainingFuel
    tailWork := tailWork
    headSubst := headSubst
    entry := entry
    prefixTail := prefixTail
    heOut := heOut
    first_noFloat := hfirstNoFloat
    second_noFloat := hsecondNoFloat
    equations_inHEImage := hequations
    split := hsplit
    continue_run := hcontinue
    fuel_lt := hlt
    trace_eq := htrace
    front_trace_eq := hfrontTraceEq
    headSubst_eq := hheadSubstEq
    prefix_inHEImage := hprefixImage
    tailWork_inHEImage := hstateImage.1
    headSubst_inHEImage := hstateImage.2
    replay := hexecutable
  }⟩

/-- When the unequal class-value prefix is literally a translated pair of
nonempty HE expressions, its standalone successful run factors once more at
the original first child.  This is the direct bridge from the local
`unifyValues` witness to the strict state consumed by the original
expression/list matcher recursion. -/
theorem LeaUnifyValuesExecutablePrefixWitness.exists_originalExpressionHeadSplit
    {leftHead rightHead : Atom} {leftTail rightTail : List Atom}
    {rest : List Metta.Atom} {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      (toLeaTTaAtom (.expression (leftHead :: leftTail)))
      (toLeaTTaAtom (.expression (rightHead :: rightTail))) rest result)
    (hne : leftHead ≠ rightHead) :
    let localFuel :=
      (toLeaTTaAtom (.expression (leftHead :: leftTail))).size +
        (((toLeaTTaAtom (.expression (rightHead :: rightTail))) :: rest).map
          Metta.Atom.size).sum
    ∃ remainingFuel tailWork childSubst,
      UnifyRoundsPrefixSplit localFuel
          [(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)]
          (List.zip (toLeaTTaAtoms leftTail)
            (toLeaTTaAtoms rightTail)) []
          remainingFuel tailWork childSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork childSubst =
          some h.headSubst ∧
        remainingFuel < localFuel ∧
        unificationEliminationTrace localFuel
            ([(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)] ++
              List.zip (toLeaTTaAtoms leftTail)
                (toLeaTTaAtoms rightTail)) =
          unificationEliminationTrace localFuel
              [(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)] ++
            unificationEliminationTrace remainingFuel tailWork ∧
        LeaEquationsInHEImage tailWork ∧
        LeaSubstInHEImage childSubst := by
  dsimp only
  have hrun : Metta.Unify.unifyRounds
      ((toLeaTTaAtom (.expression (leftHead :: leftTail))).size +
        (((toLeaTTaAtom (.expression (rightHead :: rightTail))) :: rest).map
          Metta.Atom.size).sum)
      [(.expr (toLeaTTaAtoms (leftHead :: leftTail)),
        .expr (toLeaTTaAtoms (rightHead :: rightTail)))] [] =
        some h.headSubst := by
    simpa [toLeaTTaAtom] using h.split.front_run
  have hfullLength :=
    length_eq_of_unifyRounds_expression_success hrun
  have htailLength : leftTail.length = rightTail.length := by
    rw [length_toLeaTTaAtoms, length_toLeaTTaAtoms] at hfullLength
    simpa using hfullLength
  exact exists_translated_expression_head_split_strict_state
    (by intro key term hmem; simp at hmem) hne htailLength hrun

/-- Arbitrary unequal-expression form of the local class-conflict descent.
The successful standalone class prefix determines a first unequal original
child after a possibly nonempty common prefix and returns the exact smaller
continuation state.  This is the well-founded index for the value-expression
callback in its final, traversal-faithful shape. -/
theorem LeaUnifyValuesExecutablePrefixWitness.exists_originalExpressionFirstDivergence
    {left right : List Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      (toLeaTTaAtom (.expression left))
      (toLeaTTaAtom (.expression right)) rest result)
    (hne : left ≠ right) :
    let localFuel :=
      (toLeaTTaAtom (.expression left)).size +
        (((toLeaTTaAtom (.expression right)) :: rest).map
          Metta.Atom.size).sum
    ∃ common leftHead leftTail rightHead rightTail
        remainingFuel tailWork childSubst,
      left = common ++ leftHead :: leftTail ∧
        right = common ++ rightHead :: rightTail ∧
        leftHead ≠ rightHead ∧
        leftTail.length = rightTail.length ∧
        UnifyRoundsPrefixSplit localFuel
            [(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)]
            (List.zip (toLeaTTaAtoms leftTail)
              (toLeaTTaAtoms rightTail)) []
            remainingFuel tailWork childSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork childSubst =
          some h.headSubst ∧
        remainingFuel < localFuel ∧
        unificationEliminationTrace localFuel
            ([(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)] ++
              List.zip (toLeaTTaAtoms leftTail)
                (toLeaTTaAtoms rightTail)) =
          unificationEliminationTrace localFuel
              [(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)] ++
            unificationEliminationTrace remainingFuel tailWork ∧
        LeaEquationsInHEImage tailWork ∧
        LeaSubstInHEImage childSubst := by
  dsimp only
  have hrun : Metta.Unify.unifyRounds
      ((toLeaTTaAtom (.expression left)).size +
        (((toLeaTTaAtom (.expression right)) :: rest).map
          Metta.Atom.size).sum)
      [(.expr (toLeaTTaAtoms left), .expr (toLeaTTaAtoms right))] [] =
        some h.headSubst := by
    simpa [toLeaTTaAtom] using h.split.front_run
  exact exists_translated_expression_firstDivergence_strict_state
    (by intro key term hmem; simp at hmem) hne hrun

/-- Every direct value stored in a repaired-LeaTTa binding belongs to the HE
atom image. -/
def LeaBindingsInHEImage (bindings : Metta.Bindings) : Prop :=
  ∀ key term, Metta.BindingRel.val key term ∈ bindings →
    LeaAtomInHEImage term

/-- The strengthened congruence invariant supplies exact translation-image
provenance for every LeaTTa direct value. -/
theorem LeaBindingCongruence.leaBindingsInHEImage
    {b : Bindings} {bindings : Metta.Bindings}
    (h : LeaBindingCongruence b bindings) :
    LeaBindingsInHEImage bindings := by
  intro key term hmem
  obtain ⟨heKey, heValue, _hvalue, _hclass, hatom⟩ :=
    h.classValues.2 key term hmem
  exact hatom.inHEImage

/-- Presenting an image-valued binding as equations preserves the image at
both endpoints. -/
theorem leaBindingEquations_inHEImage
    {bindings : Metta.Bindings}
    (hbindings : LeaBindingsInHEImage bindings) :
    LeaEquationsInHEImage (Metta.Bindings.equations bindings) := by
  intro equation hmem
  obtain ⟨relation, hrelation, rfl⟩ := List.mem_map.mp hmem
  cases relation with
  | val key term =>
      exact ⟨LeaAtomInHEImage.translation (.var key),
        hbindings key term hrelation⟩
  | eq left right =>
      exact ⟨LeaAtomInHEImage.translation (.var left),
        LeaAtomInHEImage.translation (.var right)⟩

/-- Image-valued equation systems are closed under concatenation. -/
theorem LeaEquationsInHEImage.append
    {left right : List (Metta.Atom × Metta.Atom)}
    (hleft : LeaEquationsInHEImage left)
    (hright : LeaEquationsInHEImage right) :
    LeaEquationsInHEImage (left ++ right) := by
  intro equation hmem
  exact (List.mem_append.mp hmem).elim
    (hleft equation) (hright equation)

/-- Whole-system reconciliation of HE-image equations returns only HE-image
terms. -/
theorem wholeBindingReconciliation_result_inHEImage
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbindings : LeaBindingsInHEImage bindings)
    (hextra : LeaEquationsInHEImage extra)
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    LeaSubstInHEImage result := by
  have hrun :
      Metta.Unify.unifyRounds
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra) [] = some result := by
    simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll] using
      hreconcile
  exact unifyRounds_result_inHEImage
    ((leaBindingEquations_inHEImage hbindings).append hextra)
    (by intro key term hmem; simp at hmem) hrun

/-- Every successful reconciliation over HE-image equations has a canonical
HE replay of its entire elimination trace. -/
theorem exists_eliminationTraceReplay_of_reconciliation
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbindings : LeaBindingsInHEImage bindings)
    (hextra : LeaEquationsInHEImage extra)
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    ∃ out, LeaEliminationTraceReplay Bindings.empty
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra)) out := by
  apply exists_eliminationTraceReplay_of_nodup_of_translation
    (wholeBindingReconciliation_eliminationTrace_keys_nodup hreconcile)
  intro key term htrace
  have hresult : (key, term) ∈ result :=
    (wholeBindingReconciliation_result_mem_iff_eliminationTrace
      hreconcile).2 htrace
  exact wholeBindingReconciliation_result_inHEImage
    hbindings hextra hreconcile key term hresult

/-- Congruent HE/LeaTTa inputs and translated new equations satisfy the image
premises of the constructive reconciliation replay automatically. -/
theorem exists_eliminationTraceReplay_of_congruence
    {b : Bindings} {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b bindings)
    (hextra : LeaEquationsInHEImage extra)
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    ∃ out, LeaEliminationTraceReplay Bindings.empty
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra)) out :=
  exists_eliminationTraceReplay_of_reconciliation
    hbase.leaBindingsInHEImage hextra hreconcile

/-- Every successful whole-system reconciliation over HE-image equations has
a canonical replay whose value and equality steps are all returned by the
corresponding executable HE insertion operation. -/
theorem exists_eliminationTraceExecutableReplay_of_reconciliation
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbindings : LeaBindingsInHEImage bindings)
    (hextra : LeaEquationsInHEImage extra)
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    ∃ out, LeaEliminationTraceExecutableReplay Bindings.empty
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra)) out := by
  obtain ⟨out, hreplay⟩ :=
    exists_eliminationTraceReplay_of_reconciliation
      hbindings hextra hreconcile
  exact ⟨out, hreplay.executable_of_triangular
    (wholeBindingReconciliation_eliminationTrace_triangular hreconcile)⟩

/-- Binding congruence supplies the HE-image premise of the executable replay
crown automatically. -/
theorem exists_eliminationTraceExecutableReplay_of_congruence
    {b : Bindings} {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b bindings)
    (hextra : LeaEquationsInHEImage extra)
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    ∃ out, LeaEliminationTraceExecutableReplay Bindings.empty
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra)) out :=
  exists_eliminationTraceExecutableReplay_of_reconciliation
    hbase.leaBindingsInHEImage hextra hreconcile

/-- Step-1 crown: under cross-engine input congruence, every successful
repaired-LeaTTa reconciliation trace is realized both stepwise by HE's
executable insertion helpers and as one result of HE's public merge surface.
The proof uses only triangular solve structure, never substitution or
representative equality. -/
theorem exists_eliminationTraceExecutableMergeReplay_of_congruence
    {b : Bindings} {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b bindings)
    (hextra : LeaEquationsInHEImage extra)
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    ∃ out fuel,
      LeaEliminationTraceExecutableReplay Bindings.empty
        (unificationEliminationTrace
          (Metta.Bindings.equationFuel
            (Metta.Bindings.equations bindings ++ extra))
          (Metta.Bindings.equations bindings ++ extra)) out ∧
      out ∈ mergeBindings Bindings.empty out fuel := by
  obtain ⟨out, hreplay⟩ :=
    exists_eliminationTraceExecutableReplay_of_congruence
      hbase hextra hreconcile
  obtain ⟨fuel, hmerge⟩ :=
    hreplay.replay.mem_mergeBindings_empty_left
      (wholeBindingReconciliation_eliminationTrace_triangular hreconcile)
  exact ⟨out, fuel, hreplay, hmerge⟩

/-- A successful whole-system reconciliation turns the replay certificate for
its solve trace into the exact substitution-provenance premise used by the
rebuild theorem. -/
theorem LeaEliminationTraceReplay.substClassValues_of_reconciliation
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    {out : Bindings}
    (hreconcile : wholeBindingReconciliation bindings extra = some result)
    (hreplay : LeaEliminationTraceReplay Bindings.empty
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra)) out) :
    LeaSubstClassValueRel out result := by
  apply (leaSubstClassValueRel_iff_eliminationTrace hreconcile).mpr
  exact hreplay.structural.classValues

/-- Every selected variable constraint is retained by the stronger alias
trace of the same successful reconciliation. -/
theorem eliminationTraceAlias_mem_reconciliationAliases
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    {key target : String}
    (hreconcile : wholeBindingReconciliation bindings extra = some result)
    (hmem : (key, .var target) ∈
      unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra)) :
    (key, target) ∈
      Metta.Bindings.reconciliationAliases bindings extra result := by
  apply wholeBindingReconciliation_result_alias_mem hreconcile
  exact (wholeBindingReconciliation_result_mem_iff_eliminationTrace
    hreconcile).mpr hmem

/-- List-level form of the previous inclusion. -/
theorem eliminationTraceAliases_subset_reconciliationAliases
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    ∀ edge ∈ eliminationTraceAliases
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra)),
      edge ∈ Metta.Bindings.reconciliationAliases bindings extra result := by
  intro edge hedge
  rcases edge with ⟨key, target⟩
  exact eliminationTraceAlias_mem_reconciliationAliases hreconcile
    (mem_eliminationTraceAliases_iff.mp hedge)

/-- Adding an alias without adding a trace entry preserves the raw-value
reading of an existing elimination trace. -/
theorem LeaEliminationTraceClassValueRel.addEquality
    {b : Bindings} {trace : List (String × Metta.Atom)}
    {key target : String}
    (h : LeaEliminationTraceClassValueRel b trace) :
    LeaEliminationTraceClassValueRel
      (b.addEquality key target) trace := by
  have hclassMono : ∀ {start finish : String},
      finish ∈ b.eqClass start →
        finish ∈ (b.addEquality key target).eqClass start :=
    eqClass_mono_addEquality b key target
  constructor
  · intro heKey heValue hmem
    have hold : (heKey, heValue) ∈ b.assignments := by
      simpa [Bindings.addEquality] using hmem
    obtain ⟨leaKey, leaValue, hleaValue, hnonvar,
        hkeyClass, hatom⟩ := h.1 heKey heValue hold
    exact ⟨leaKey, leaValue, hleaValue, hnonvar,
      hclassMono hkeyClass,
      HELeaAtomClassRel.mono hclassMono hatom⟩
  · intro leaKey leaValue hmem hnonvar
    obtain ⟨heKey, heValue, hvalue, hkeyClass, hatom⟩ :=
      h.2 leaKey leaValue hmem hnonvar
    exact ⟨heKey, heValue,
      by simpa [Bindings.addEquality] using hvalue,
      hclassMono hkeyClass,
      HELeaAtomClassRel.mono hclassMono hatom⟩

/-- Replay every equality exposed by `aliasTrace` after value replay. -/
inductive LeaAliasTraceReplay
    (base : Bindings) : List (String × String) → Bindings → Prop where
  | nil : LeaAliasTraceReplay base [] base
  | cons {aliases : List (String × String)} {b : Bindings}
      {key target : String} :
      LeaAliasTraceReplay base aliases b →
      LeaAliasTraceReplay base ((key, target) :: aliases)
        (b.addEquality key target)

/-- The nonrecursive sublane of alias restoration.  Besides recording the
same raw equality edges as `LeaAliasTraceReplay`, every step certifies that
HE's public equality insertion takes its consistent branch. -/
inductive LeaAliasTraceConsistentReplay
    (base : Bindings) : List (String × String) → Bindings → Prop where
  | nil : LeaAliasTraceConsistentReplay base [] base
  | cons {aliases : List (String × String)} {b : Bindings}
      {key target : String} :
      LeaAliasTraceConsistentReplay base aliases b →
      Bindings.valuesConsistent
          ((b.addEquality key target).classValues key) = true →
      LeaAliasTraceConsistentReplay base ((key, target) :: aliases)
        (b.addEquality key target)

/-- Forgetting the executable consistency guards recovers the structural
alias replay. -/
theorem LeaAliasTraceConsistentReplay.replay
    {base out : Bindings} {aliases : List (String × String)}
    (h : LeaAliasTraceConsistentReplay base aliases out) :
    LeaAliasTraceReplay base aliases out := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons ih

/-- Append one successful equality insertion to a declarative equality fold. -/
private def mergeEqsRel_snoc
    {base mid out : Bindings} {equalities : List (String × String)}
    {key target : String}
    (hfold : MergeEqsRel base equalities mid)
    (hadd : AddVarEqualityRel mid key target out) :
    MergeEqsRel base (equalities ++ [(key, target)]) out :=
  match hfold with
  | .nil => .cons hadd .nil
  | .cons hhead htail => .cons hhead (mergeEqsRel_snoc htail hadd)

/-- Equality-upper-bound certificates compose across the same dependent
snoc boundary as their underlying declarative equality folds. -/
private def mergeEqsEqualityClosureBoundSound_snoc
    {allowed : List (String × String)}
    {base mid out : Bindings} {equalities : List (String × String)}
    {key target : String}
    {hfold : MergeEqsRel base equalities mid}
    (hfoldSound : MergeEqsEqualityClosureBoundSound allowed hfold)
    {hadd : AddVarEqualityRel mid key target out}
    (haddSound :
      AddVarEqualityEqualityClosureBoundSound allowed hadd) :
    MergeEqsEqualityClosureBoundSound allowed
      (mergeEqsRel_snoc hfold hadd) := by
  cases hfold with
  | nil =>
      cases hfoldSound
      exact MergeEqsEqualityClosureBoundSound.cons haddSound
        MergeEqsEqualityClosureBoundSound.nil
  | cons hhead htail =>
      cases hfoldSound with
      | cons hheadSound htailSound =>
          exact MergeEqsEqualityClosureBoundSound.cons hheadSound
            (mergeEqsEqualityClosureBoundSound_snoc
              htailSound haddSound)

/-- A consistent alias replay is exactly a declarative HE equality fold in
the reverse certificate order used by the raw replay representation. -/
theorem LeaAliasTraceConsistentReplay.mergeEqsRel_reverse
    {base out : Bindings} {aliases : List (String × String)}
    (h : LeaAliasTraceConsistentReplay base aliases out) :
    MergeEqsRel base aliases.reverse out := by
  induction h with
  | nil => exact .nil
  | @cons aliases b key target h hconsistent ih =>
      simpa using mergeEqsRel_snoc ih
        (AddVarEqualityRel.consistent hconsistent)

/-- The consistent alias fold also carries a local equality upper-bound
certificate for every ambient graph that contains its requested aliases. -/
theorem LeaAliasTraceConsistentReplay.mergeEqsEqualityClosureBoundSound_reverse
    {base out : Bindings} {aliases : List (String × String)}
    (h : LeaAliasTraceConsistentReplay base aliases out)
    {allowed : List (String × String)}
    (hallowed : ∀ edge ∈ aliases,
      (EqualityClosure.edgeGraph allowed).Reachable edge.1 edge.2) :
    MergeEqsEqualityClosureBoundSound allowed h.mergeEqsRel_reverse := by
  induction h generalizing allowed with
  | nil => exact .nil
  | @cons aliases b key target h hconsistent ih =>
      have htailAllowed : ∀ edge ∈ aliases,
          (EqualityClosure.edgeGraph allowed).Reachable
            edge.1 edge.2 := by
        intro edge hedge
        exact hallowed edge (List.mem_cons_of_mem _ hedge)
      have hheadAllowed :
          (EqualityClosure.edgeGraph allowed).Reachable key target :=
        hallowed (key, target) (by simp)
      let hadd : AddVarEqualityRel b key target
          (b.addEquality key target) :=
        AddVarEqualityRel.consistent hconsistent
      have haddSound :
          AddVarEqualityEqualityClosureBoundSound allowed hadd :=
        AddVarEqualityEqualityClosureBoundSound.consistent
          (hconsistent := hconsistent) hheadAllowed
      let hcombined := mergeEqsRel_snoc h.mergeEqsRel_reverse hadd
      have hcombinedSound :
          MergeEqsEqualityClosureBoundSound allowed hcombined :=
        mergeEqsEqualityClosureBoundSound_snoc
          (ih htailAllowed) haddSound
      have hcombined' : MergeEqsRel base
          ((key, target) :: aliases).reverse
          (b.addEquality key target) := by
        simpa using hcombined
      have hcombinedSound' :
          MergeEqsEqualityClosureBoundSound allowed hcombined' := by
        simpa using hcombinedSound
      simpa only [Subsingleton.elim hcombined'
        (LeaAliasTraceConsistentReplay.mergeEqsRel_reverse
          (.cons h hconsistent))] using hcombinedSound'

/-- Every finite alias certificate has a canonical HE replay from any base. -/
theorem exists_aliasTraceReplay (base : Bindings) :
    ∀ aliases : List (String × String),
      ∃ out, LeaAliasTraceReplay base aliases out := by
  intro aliases
  induction aliases with
  | nil => exact ⟨base, .nil⟩
  | cons edge aliases ih =>
      rcases edge with ⟨key, target⟩
      obtain ⟨out, hout⟩ := ih
      exact ⟨out.addEquality key target, .cons hout⟩

/-- Alias replay appends edges in reverse certificate order. -/
theorem LeaAliasTraceReplay.equalities
    {base out : Bindings} {aliases : List (String × String)}
    (h : LeaAliasTraceReplay base aliases out) :
    out.equalities = base.equalities ++ aliases.reverse := by
  induction h with
  | nil => simp
  | cons h ih =>
      simp [Bindings.addEquality, ih, List.append_assoc]

/-- Raw alias replay never creates an assignment. -/
theorem LeaAliasTraceReplay.assignments
    {base out : Bindings} {aliases : List (String × String)}
    (h : LeaAliasTraceReplay base aliases out) :
    out.assignments = base.assignments := by
  induction h with
  | nil => rfl
  | cons h ih => simpa [Bindings.addEquality] using ih

/-- An equality-only matcher record from empty bindings has no equality
connection beyond its alias certificate. -/
theorem LeaAliasTraceReplay.equalityClosureBound
    {out : Bindings} {aliases : List (String × String)}
    (h : LeaAliasTraceReplay Bindings.empty aliases out) :
    HEEqualityClosureBound out aliases := by
  apply HEEqualityClosureBound.of_edges
  intro edge hmem
  rw [h.equalities] at hmem
  simp only [Bindings.empty, List.nil_append] at hmem
  have hedge : edge ∈ aliases := by
    simpa using (List.mem_reverse.mp hmem)
  rcases edge with ⟨left, right⟩
  by_cases heq : left = right
  · subst right
    exact .rfl
  · exact (show (EqualityClosure.edgeGraph aliases).Adj left right by
      rw [EqualityClosure.edgeGraph_adj_iff]
      exact ⟨heq, Or.inl hedge⟩).reachable

/-- A locally upper-bound-certified live merge with an equality-only alias
record has exactly the alias certificate's connected components.  The upper
direction comes from the local recursive matcher certificate; the lower
direction comes from preservation of the complete right equality closure. -/
theorem mergeBindings_eqClass_iff_aliases_of_boundSound
    {aliases : List (String × String)}
    {left aliasRecord out : Bindings} {fuel : Nat}
    (hmerge : out ∈ mergeBindings left aliasRecord fuel)
    (hboundSound : MergeEqualityClosureBoundSound aliases
      (mergeBindings_sound hmerge))
    (hleft : HEEqualityClosureBound left aliases)
    (halias : LeaAliasTraceReplay Bindings.empty aliases aliasRecord)
    (start finish : String) :
    finish ∈ out.eqClass start ↔
      (EqualityClosure.edgeGraph aliases).Reachable start finish := by
  apply (hboundSound.preserves hleft).eqClass_iff_of_edges
  intro edge hedge
  rcases edge with ⟨edgeLeft, edgeRight⟩
  apply mergeBindings_right_eqClass_mono hmerge
  rw [EqualityClosure.mem_eqClass_iff_reachable]
  by_cases heq : edgeLeft = edgeRight
  · subst edgeRight
    exact .rfl
  · apply SimpleGraph.Adj.reachable
    rw [EqualityClosure.edgeGraph_adj_iff]
    refine ⟨heq, Or.inl ?_⟩
    rw [halias.equalities]
    simpa [Bindings.empty] using (List.mem_reverse.mpr hedge)

/-- A matcher-origin alias record contributes no raw assignment provenance.
Consequently, merging such a record into a complete Robinson-trace record
preserves the complete structural certificate; only recursive conflict
matcher outputs must satisfy the same trace-soundness invariant.  This is the
live alias-merge specialization consumed by reconciliation. -/
theorem mergeBindings_eliminationTraceStructural_of_aliasRecord
    {trace : List (String × Metta.Atom)}
    {aliases : List (String × String)}
    {left aliasRecord out : Bindings} {fuel : Nat}
    (hmerge : out ∈ mergeBindings left aliasRecord fuel)
    (hleft : LeaEliminationTraceStructuralRel left trace)
    (halias : LeaAliasTraceReplay Bindings.empty aliases aliasRecord)
    (hmatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace)
    (hlistMatcher : ∀ {atomLeft atomRight matched},
      DeclMatchSpec.MatchListRel atomLeft atomRight matched →
        LeaEliminationTraceAssignmentsSound matched trace) :
    LeaEliminationTraceStructuralRel out trace := by
  apply mergeBindings_eliminationTraceStructural_of_sound_matchers
    hmerge hleft
  · intro key value hmem
    rw [halias.assignments] at hmem
    simp [Bindings.empty] at hmem
  · exact hmatcher
  · exact hlistMatcher

/-- An equality-only alias replay presents exactly the conjunction of the
alias equations it records.  This statement is independent of list order and
of the concrete spanning tree used by any other binding presentation. -/
theorem LeaAliasTraceReplay.satisfaction_iff
    {out : Bindings} {aliases : List (String × String)}
    (h : LeaAliasTraceReplay Bindings.empty aliases out)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation out ↔
      ∀ edge ∈ aliases, valuation edge.1 = valuation edge.2 := by
  induction h with
  | nil =>
      simp
  | @cons aliases b key target h ih =>
      rw [heBindingSatisfied_addEquality_iff, ih]
      constructor
      · rintro ⟨htail, hedge⟩ edge hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hhead | htailMem
        · rcases hhead with ⟨rfl, rfl⟩
          exact hedge
        · exact htail edge htailMem
      · intro hall
        refine ⟨?_, ?_⟩
        · intro edge hmem
          exact hall edge (List.mem_cons_of_mem _ hmem)
        · exact hall (key, target) (by simp)

/-- Compile the entire nonrecursive alias sublane into one finite-fuel public
HE merge against an equality-only matcher-origin record. -/
theorem LeaAliasTraceConsistentReplay.exists_liveMerge
    {base out : Bindings} {aliases : List (String × String)}
    (h : LeaAliasTraceConsistentReplay base aliases out) :
    ∃ aliasRecord fuel,
      LeaAliasTraceReplay Bindings.empty aliases aliasRecord ∧
        out ∈ mergeBindings base aliasRecord fuel := by
  obtain ⟨aliasRecord, hrecord⟩ :=
    exists_aliasTraceReplay Bindings.empty aliases
  have hmergeRel : MergeRel base aliasRecord out := by
    apply MergeRel.mk
    · have hassignments : aliasRecord.assignments = [] := by
        simpa [Bindings.empty] using hrecord.assignments
      rw [hassignments]
      exact .nil
    · have hequalities : aliasRecord.equalities = aliases.reverse := by
        simpa [Bindings.empty] using hrecord.equalities
      rw [hequalities]
      exact h.mergeEqsRel_reverse
  obtain ⟨fuel, hmerge⟩ := mergeBindings_complete hmergeRel
  exact ⟨aliasRecord, fuel, hrecord, hmerge⟩

/-- The nonrecursive alias sublane emits a public live merge together with
its derivation-local equality upper-bound certificate. -/
theorem LeaAliasTraceConsistentReplay.exists_liveMerge_boundSound
    {base out : Bindings} {aliases : List (String × String)}
    (h : LeaAliasTraceConsistentReplay base aliases out) :
    ∃ aliasRecord fuel,
      ∃ hmerge : out ∈ mergeBindings base aliasRecord fuel,
        LeaAliasTraceReplay Bindings.empty aliases aliasRecord ∧
          MergeEqualityClosureBoundSound aliases
            (mergeBindings_sound hmerge) := by
  obtain ⟨aliasRecord, hrecord⟩ :=
    exists_aliasTraceReplay Bindings.empty aliases
  have hrecordEq : aliasRecord =
      (⟨[], aliases.reverse⟩ : Bindings) := by
    have hassignmentsEq : aliasRecord.assignments = [] := by
      simpa [Bindings.empty] using hrecord.assignments
    have hequalitiesEq : aliasRecord.equalities = aliases.reverse := by
      simpa [Bindings.empty] using hrecord.equalities
    cases aliasRecord
    simp_all
  subst aliasRecord
  let hassignments : MergeAssignsRel base [] base :=
    MergeAssignsRel.nil (acc := base)
  let hequalities : MergeEqsRel base aliases.reverse out :=
    h.mergeEqsRel_reverse
  let hrel : MergeRel base (⟨[], aliases.reverse⟩ : Bindings) out :=
    MergeRel.mk hassignments hequalities
  have hassignmentsSound :
      MergeAssignsEqualityClosureBoundSound aliases hassignments := by
    exact MergeAssignsEqualityClosureBoundSound.nil
  have hequalitiesSound :
      MergeEqsEqualityClosureBoundSound aliases hequalities := by
    have hallowed : ∀ edge ∈ aliases,
        (EqualityClosure.edgeGraph aliases).Reachable
          edge.1 edge.2 := by
      intro edge hedge
      rcases edge with ⟨left, right⟩
      by_cases heq : left = right
      · subst right
        exact .rfl
      · exact (show
          (EqualityClosure.edgeGraph aliases).Adj left right by
            rw [EqualityClosure.edgeGraph_adj_iff]
            exact ⟨heq, Or.inl hedge⟩).reachable
    have hsound :=
      h.mergeEqsEqualityClosureBoundSound_reverse hallowed
    simpa only [Subsingleton.elim h.mergeEqsRel_reverse hequalities] using hsound
  have hrelSound : MergeEqualityClosureBoundSound aliases hrel :=
    MergeEqualityClosureBoundSound.mk
      hassignmentsSound hequalitiesSound
  obtain ⟨fuel, hmerge⟩ := mergeBindings_complete hrel
  refine ⟨(⟨[], aliases.reverse⟩ : Bindings), fuel,
    hmerge, hrecord, ?_⟩
  simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrel] using
    hrelSound

/-- An equality-only alias replay from empty bindings is itself a genuine HE
list match.  Each variable/variable leaf is merged into an accumulator whose
assignment list remains empty, so the public equality insertion takes its
consistent branch. -/
theorem LeaAliasTraceReplay.exists_matchListRel_reverse
    {aliases : List (String × String)} {out : Bindings}
    (h : LeaAliasTraceReplay Bindings.empty aliases out) :
    ∃ left right,
      left = aliases.reverse.map (fun edge => Atom.var edge.1) ∧
        right = aliases.reverse.map (fun edge => Atom.var edge.2) ∧
        DeclMatchSpec.MatchListRel left right out := by
  induction h with
  | nil => exact ⟨[], [], rfl, rfl, .nil⟩
  | @cons aliases b key target h ih =>
      obtain ⟨left, right, hleft, hright, hlist⟩ := ih
      have hbAssignments : b.assignments = [] := by
        simpa [Bindings.empty] using h.assignments
      have hclass :
          (b.addEquality key target).classValues key = [] := by
        unfold Bindings.classValues Bindings.lookup
        simp [Bindings.addEquality, hbAssignments]
      have hconsistent : Bindings.valuesConsistent
          ((b.addEquality key target).classValues key) = true := by
        simp [hclass, Bindings.valuesConsistent]
      have hadd : b.addEquality key target ∈
          addVarEquality b key target 1 := by
        simp [addVarEquality, hconsistent]
      have hmerge : b.addEquality key target ∈
          mergeBindings b (Bindings.empty.addEquality key target) 2 := by
        simpa [mergeBindings, Bindings.empty, Bindings.addEquality] using hadd
      refine ⟨left ++ [.var key], right ++ [.var target], ?_, ?_, ?_⟩
      · simp [hleft]
      · simp [hright]
      · exact matchListAccRel_snoc hlist
          (DeclMatchSpec.MatchRel.varVar key target) hmerge

/-- Executable form of equality-only alias replay. -/
theorem LeaAliasTraceReplay.exists_mem_matchAtomsList_reverse
    {aliases : List (String × String)} {out : Bindings}
    (h : LeaAliasTraceReplay Bindings.empty aliases out) :
    ∃ left right fuel,
      left = aliases.reverse.map (fun edge => Atom.var edge.1) ∧
        right = aliases.reverse.map (fun edge => Atom.var edge.2) ∧
        out ∈ matchAtomsList left right [Bindings.empty] fuel := by
  obtain ⟨left, right, hleft, hright, hrel⟩ :=
    h.exists_matchListRel_reverse
  obtain ⟨fuel, hmem⟩ := DeclMatchSpec.matchAtomsList_complete hrel
  exact ⟨left, right, fuel, hleft, hright, hmem⟩

/-- Expression-packaged matcher witness for an equality-only alias record. -/
theorem LeaAliasTraceReplay.exists_mem_matchAtoms_expression_reverse
    {aliases : List (String × String)} {out : Bindings}
    (h : LeaAliasTraceReplay Bindings.empty aliases out) :
    ∃ left right fuel,
      left = aliases.reverse.map (fun edge => Atom.var edge.1) ∧
        right = aliases.reverse.map (fun edge => Atom.var edge.2) ∧
        out ∈ matchAtoms (.expression left) (.expression right) fuel := by
  obtain ⟨left, right, hleft, hright, hrel⟩ :=
    h.exists_matchListRel_reverse
  obtain ⟨fuel, hmem⟩ :=
    DeclMatchSpec.matchAtoms_complete (DeclMatchSpec.MatchRel.expr hrel)
  exact ⟨left, right, fuel, hleft, hright, hmem⟩

/-- Matcher-origin form of the nonrecursive alias compiler: the right record
is itself returned by `matchAtoms`, then is merged into the live seed by the
public HE merge surface. -/
theorem LeaAliasTraceConsistentReplay.exists_matcherLiveMerge
    {base out : Bindings} {aliases : List (String × String)}
    (h : LeaAliasTraceConsistentReplay base aliases out) :
    ∃ aliasRecord left right matchFuel mergeFuel,
      aliasRecord ∈
          matchAtoms (.expression left) (.expression right) matchFuel ∧
        out ∈ mergeBindings base aliasRecord mergeFuel := by
  obtain ⟨aliasRecord, mergeFuel, hrecord, hmerge⟩ :=
    h.exists_liveMerge
  obtain ⟨left, right, matchFuel, _hleft, _hright, hmatch⟩ :=
    hrecord.exists_mem_matchAtoms_expression_reverse
  exact ⟨aliasRecord, left, right, matchFuel, mergeFuel,
    hmatch, hmerge⟩

/-- Any alias restoration over a live value record factors exactly into that
record's assignments/equalities plus an equality-only matcher-origin record.
This exposes the precise right input for the remaining live merge proof. -/
theorem LeaAliasTraceReplay.exists_matcherRecord_decomposition
    {base out : Bindings} {aliases : List (String × String)}
    (h : LeaAliasTraceReplay base aliases out) :
    ∃ aliasRecord left right fuel,
      left = aliases.reverse.map (fun edge => Atom.var edge.1) ∧
        right = aliases.reverse.map (fun edge => Atom.var edge.2) ∧
        aliasRecord ∈
          matchAtoms (.expression left) (.expression right) fuel ∧
        out.assignments = base.assignments ∧
        out.equalities = base.equalities ++ aliasRecord.equalities := by
  obtain ⟨aliasRecord, hrecord⟩ :=
    exists_aliasTraceReplay Bindings.empty aliases
  obtain ⟨left, right, fuel, hleft, hright, hmatch⟩ :=
    hrecord.exists_mem_matchAtoms_expression_reverse
  have hrecordEqualities : aliasRecord.equalities = aliases.reverse := by
    simpa [Bindings.empty] using hrecord.equalities
  exact ⟨aliasRecord, left, right, fuel, hleft, hright, hmatch,
    h.assignments, by simpa [hrecordEqualities] using h.equalities⟩

/-- Alias replay monotonically preserves the elimination trace's exact raw
value provenance. -/
theorem LeaAliasTraceReplay.classValues
    {base out : Bindings} {aliases : List (String × String)}
    {trace : List (String × Metta.Atom)}
    (h : LeaAliasTraceReplay base aliases out)
    (hvalues : LeaEliminationTraceClassValueRel base trace) :
    LeaEliminationTraceClassValueRel out trace := by
  induction h with
  | nil => exact hvalues
  | cons h ih => exact ih.addEquality

/-! ## Solution theory of the canonical reconciliation replay -/

/-- Class-relative atom transport only needs valuation constancy on the HE
equality closure.  This is the non-circular form used to derive satisfaction
from structural trace provenance plus an equality upper bound. -/
theorem HELeaAtomClassRel.applyClassSolution_eq_of_eqClass
    {b : Bindings} {valuation : String → Metta.Atom}
    {atom : Atom} {leaAtom : Metta.Atom}
    (hclasses : ∀ {left right : String},
      right ∈ b.eqClass left → valuation left = valuation right)
    (hrel : HELeaAtomClassRel b atom leaAtom) :
    applyClassSolution valuation (toLeaTTaAtom atom) =
      applyClassSolution valuation leaAtom := by
  let AtomGoal := fun (atom : Atom) (leaAtom : Metta.Atom)
      (_ : HELeaAtomClassRel b atom leaAtom) =>
    applyClassSolution valuation (toLeaTTaAtom atom) =
      applyClassSolution valuation leaAtom
  let ListGoal := fun (atoms : List Atom) (leaAtoms : List Metta.Atom)
      (_ : List.Forall₂ (HELeaAtomClassRel b) atoms leaAtoms) =>
    (toLeaTTaAtoms atoms).map (applyClassSolution valuation) =
      leaAtoms.map (applyClassSolution valuation)
  have hrec : ∀ {atom leaAtom} (h : HELeaAtomClassRel b atom leaAtom),
      AtomGoal atom leaAtom h := by
    apply HELeaAtomClassRel.rec
        (motive_1 := AtomGoal) (motive_2 := ListGoal)
    · intro name
      rfl
    · intro left right hclass
      dsimp [AtomGoal]
      simpa [toLeaTTaAtom, applyClassSolution] using
        hclasses hclass
    · intro ground
      rfl
    · intro atoms leaAtoms hrels ih
      dsimp [AtomGoal]
      simpa [toLeaTTaAtom, applyClassSolution] using
        congrArg Metta.Atom.expr ih
    · rfl
    · intro atom leaAtom atoms leaAtoms hhead htail ihHead ihTail
      change
        applyClassSolution valuation (toLeaTTaAtom atom) ::
            (toLeaTTaAtoms atoms).map (applyClassSolution valuation) =
          applyClassSolution valuation leaAtom ::
            leaAtoms.map (applyClassSolution valuation)
      exact congrArg₂ List.cons ihHead ihTail
  exact hrec hrel

/-- Class-relative atom transport preserves the valuation image whenever the
HE binding record is satisfied. -/
theorem HELeaAtomClassRel.applyClassSolution_eq
    {b : Bindings} {valuation : String → Metta.Atom}
    {atom : Atom} {leaAtom : Metta.Atom}
    (hsat : HEBindingSatisfied valuation b)
    (hrel : HELeaAtomClassRel b atom leaAtom) :
    applyClassSolution valuation (toLeaTTaAtom atom) =
      applyClassSolution valuation leaAtom := by
  let AtomGoal := fun (atom : Atom) (leaAtom : Metta.Atom)
      (_ : HELeaAtomClassRel b atom leaAtom) =>
    applyClassSolution valuation (toLeaTTaAtom atom) =
      applyClassSolution valuation leaAtom
  let ListGoal := fun (atoms : List Atom) (leaAtoms : List Metta.Atom)
      (_ : List.Forall₂ (HELeaAtomClassRel b) atoms leaAtoms) =>
    (toLeaTTaAtoms atoms).map (applyClassSolution valuation) =
      leaAtoms.map (applyClassSolution valuation)
  have hrec : ∀ {atom leaAtom} (h : HELeaAtomClassRel b atom leaAtom),
      AtomGoal atom leaAtom h := by
    apply HELeaAtomClassRel.rec
        (motive_1 := AtomGoal) (motive_2 := ListGoal)
    · intro name
      rfl
    · intro left right hclass
      dsimp [AtomGoal]
      simpa [toLeaTTaAtom, applyClassSolution] using
        hsat.eq_of_mem_eqClass hclass
    · intro ground
      rfl
    · intro atoms leaAtoms hrels ih
      dsimp [AtomGoal]
      simpa [toLeaTTaAtom, applyClassSolution] using
        congrArg Metta.Atom.expr ih
    · rfl
    · intro atom leaAtom atoms leaAtoms hhead htail ihHead ihTail
      change
        applyClassSolution valuation (toLeaTTaAtom atom) ::
            (toLeaTTaAtoms atoms).map (applyClassSolution valuation) =
          applyClassSolution valuation leaAtom ::
            leaAtoms.map (applyClassSolution valuation)
      exact congrArg₂ List.cons ihHead ihTail
  exact hrec hrel

/-- A valuation satisfying a solve trace is constant along every connected
component of the trace's explicit alias graph. -/
theorem MettaConstraintsSatisfied.eq_of_aliasReachable
    {trace : List (String × Metta.Atom)}
    {valuation : String → Metta.Atom}
    (htrace : MettaConstraintsSatisfied valuation trace)
    {left right : String}
    (hreach : (EqualityClosure.edgeGraph
      (eliminationTraceAliases trace)).Reachable left right) :
    valuation left = valuation right := by
  apply hreach.elim
  intro walk
  induction walk with
  | nil => rfl
  | @cons start next finish hadj tail ih =>
      rw [EqualityClosure.edgeGraph_adj_iff] at hadj
      have hstep : valuation start = valuation next := by
        rcases hadj.2 with hforward | hreverse
        · have hconstraint := htrace (start, .var next)
            (mem_eliminationTraceAliases_iff.mp hforward)
          simpa [applyClassSolution] using hconstraint
        · have hconstraint := htrace (next, .var start)
            (mem_eliminationTraceAliases_iff.mp hreverse)
          symm
          simpa [applyClassSolution] using hconstraint
      exact hstep.trans (ih tail.reachable)

/-- Complete trace provenance plus an equality upper bound determines the
entire HE binding solution theory.  The forward direction reads every trace
entry from the live classes; the reverse direction uses the upper bound to
show that every live equality and every class-relative atom variable is
licensed by the trace alias graph. -/
theorem LeaEliminationTraceStructuralRel.satisfaction_iff_of_bound
    {b : Bindings} {trace : List (String × Metta.Atom)}
    (hstruct : LeaEliminationTraceStructuralRel b trace)
    (hbound : HEEqualityClosureBound b
      (eliminationTraceAliases trace))
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation b ↔
      MettaConstraintsSatisfied valuation trace := by
  constructor
  · intro hbinding constraint hconstraint
    rcases constraint with ⟨leaKey, leaValue⟩
    cases leaValue with
    | var target =>
        have hclass := hstruct.aliases leaKey target hconstraint
        simpa [applyClassSolution] using
          hbinding.eq_of_mem_eqClass hclass
    | sym symbol =>
        obtain ⟨key, value, hvalue, hclass, hatom⟩ :=
          hstruct.classValues.2 leaKey (.sym symbol) hconstraint
            (by intro target h; cases h)
        exact (hbinding.eq_of_mem_eqClass hclass).symm.trans
          ((hbinding.1 key value hvalue).trans
            (hatom.applyClassSolution_eq hbinding))
    | gnd ground =>
        obtain ⟨key, value, hvalue, hclass, hatom⟩ :=
          hstruct.classValues.2 leaKey (.gnd ground) hconstraint
            (by intro target h; cases h)
        exact (hbinding.eq_of_mem_eqClass hclass).symm.trans
          ((hbinding.1 key value hvalue).trans
            (hatom.applyClassSolution_eq hbinding))
    | expr atoms =>
        obtain ⟨key, value, hvalue, hclass, hatom⟩ :=
          hstruct.classValues.2 leaKey (.expr atoms) hconstraint
            (by intro target h; cases h)
        exact (hbinding.eq_of_mem_eqClass hclass).symm.trans
          ((hbinding.1 key value hvalue).trans
            (hatom.applyClassSolution_eq hbinding))
  · intro htrace
    have hclasses : ∀ {left right : String},
        right ∈ b.eqClass left → valuation left = valuation right := by
      intro left right hclass
      exact htrace.eq_of_aliasReachable (hbound left right hclass)
    constructor
    · intro key value hvalue
      obtain ⟨leaKey, leaValue, hentry, _hnonvar, hclass, hatom⟩ :=
        hstruct.classValues.1 key value hvalue
      exact (hclasses hclass).trans
        ((htrace (leaKey, leaValue) hentry).trans
          (hatom.applyClassSolution_eq_of_eqClass hclasses).symm)
    · intro left right hedge
      exact htrace.eq_of_aliasReachable (hbound.edge hedge)

/-- The same two structural certificates therefore construct full
cross-engine congruence with repaired LeaTTa's `ofSubst` presentation of the
reverse trace.  This theorem is representation-free: it compares equality
closures, complete solution theories, and class-indexed raw values only. -/
theorem LeaEliminationTraceStructuralRel.congruence_ofSubst_reverse_of_bound
    {b : Bindings} {trace : List (String × Metta.Atom)}
    (hstruct : LeaEliminationTraceStructuralRel b trace)
    (hbound : HEEqualityClosureBound b
      (eliminationTraceAliases trace)) :
    LeaBindingCongruence b
      (Metta.Bindings.ofSubst trace.reverse) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro start finish
    rw [mem_leaEqClass_iff_reachable,
      leaEqualityEdges_ofSubst_eq_eliminationTraceAliases,
      eliminationTraceAliases_reverse]
    have hgraph : EqualityClosure.edgeGraph
        (eliminationTraceAliases trace).reverse =
        EqualityClosure.edgeGraph
          (eliminationTraceAliases trace) := by
      ext left right
      simp [EqualityClosure.edgeGraph_adj_iff]
    rw [hgraph]
    exact hbound.eqClass_iff_of_edges
      (fun edge hedge => by
        rcases edge with ⟨left, right⟩
        exact hstruct.aliases left right
          (mem_eliminationTraceAliases_iff.mp hedge))
      start finish
  · intro valuation
    rw [hstruct.satisfaction_iff_of_bound hbound,
      leaOfSubst_solution_iff]
    simp [MettaConstraintsSatisfied]
  · constructor
    · intro key value hmem
      obtain ⟨leaKey, leaValue, htrace, hnonvar, hclass, hatom⟩ :=
        hstruct.classValues.1 key value hmem
      refine ⟨leaKey, leaValue, ?_, hclass, hatom⟩
      apply val_mem_ofSubst_iff.mpr
      exact ⟨by simpa using htrace, hnonvar⟩
    · intro leaKey leaValue hmem
      obtain ⟨hsubst, hnonvar⟩ := val_mem_ofSubst_iff.mp hmem
      have htrace : (leaKey, leaValue) ∈ trace := by
        simpa using hsubst
      obtain ⟨key, value, hassignment, hclass, hatom⟩ :=
        hstruct.classValues.2 leaKey leaValue htrace hnonvar
      exact ⟨key, value, hassignment, hclass, hatom⟩

@[simp] private theorem mettaConstraintsSatisfied_reverse
    (valuation : String → Metta.Atom)
    (constraints : List (String × Metta.Atom)) :
    MettaConstraintsSatisfied valuation constraints.reverse ↔
      MettaConstraintsSatisfied valuation constraints := by
  unfold MettaConstraintsSatisfied
  simp

/-- Updating a valuation outside an atom's variable support leaves that
atom's solution image unchanged. -/
private theorem applyClassSolution_update_of_not_mem_vars
    (valuation : String → Metta.Atom) (key : String)
    (replacement : Metta.Atom) :
    ∀ atom : Metta.Atom, key ∉ atom.vars →
      applyClassSolution (Function.update valuation key replacement) atom =
        applyClassSolution valuation atom := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro name hnot
    simp [applyClassSolution]
  · intro name hnot
    have hne : name ≠ key := by
      intro heq
      subst name
      exact hnot (by simp [Metta.Atom.vars])
    simp [applyClassSolution, Function.update, hne]
  · intro ground hnot
    simp [applyClassSolution]
  · intro atoms ih hnot
    simp only [applyClassSolution]
    apply congrArg Metta.Atom.expr
    apply List.map_congr_left
    intro atom hatom
    apply ih atom hatom
    intro hkey
    apply hnot
    simp only [Metta.Atom.vars, List.mem_flatten]
    exact ⟨atom.vars,
      List.mem_map.mpr ⟨atom, hatom, rfl⟩, hkey⟩

/-- A concrete valuation for a triangular elimination trace.  Tail constraints
are interpreted first; the selected key is then assigned the interpreted head
term. -/
def eliminationTraceValuation :
    List (String × Metta.Atom) → String → Metta.Atom
  | [] => fun name => .var name
  | (key, value) :: trace =>
      let tailValuation := eliminationTraceValuation trace
      Function.update tailValuation key
        (applyClassSolution tailValuation value)

private theorem not_mem_constraintVars_of_mem
    {trace : List (String × Metta.Atom)} {key : String}
    {constraint : String × Metta.Atom}
    (hfresh : key ∉ mettaConstraintVars trace)
    (hmem : constraint ∈ trace) :
    key ≠ constraint.1 ∧ key ∉ constraint.2.vars := by
  constructor
  · intro heq
    apply hfresh
    unfold mettaConstraintVars
    apply List.mem_flatMap.mpr
    exact ⟨constraint, hmem, by simp [heq]⟩
  · intro hkey
    apply hfresh
    unfold mettaConstraintVars
    apply List.mem_flatMap.mpr
    exact ⟨constraint, hmem, by simp [hkey]⟩

/-- The recursively constructed valuation satisfies every triangular,
occurs-check-clean solve trace. -/
theorem eliminationTraceValuation_satisfies
    (trace : List (String × Metta.Atom))
    (htriangular : EliminationTraceTriangular trace)
    (hoccurs : ∀ key value, (key, value) ∈ trace → key ∉ value.vars) :
    MettaConstraintsSatisfied (eliminationTraceValuation trace) trace := by
  induction trace with
  | nil =>
      simp [MettaConstraintsSatisfied]
  | cons binding trace ih =>
      rcases binding with ⟨key, value⟩
      have htriangular' :
          key ∉ mettaConstraintVars trace ∧
            EliminationTraceTriangular trace := by
        simpa [EliminationTraceTriangular] using htriangular
      have hoccursHead : key ∉ value.vars :=
        hoccurs key value (by simp)
      have hoccursTail : ∀ tailKey tailValue,
          (tailKey, tailValue) ∈ trace → tailKey ∉ tailValue.vars := by
        intro tailKey tailValue hmem
        exact hoccurs tailKey tailValue (by simp [hmem])
      have htail := ih htriangular'.2 hoccursTail
      intro constraint hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htailMem
      · subst constraint
        change
          Function.update (eliminationTraceValuation trace) key
              (applyClassSolution (eliminationTraceValuation trace) value) key =
            applyClassSolution
              (Function.update (eliminationTraceValuation trace) key
                (applyClassSolution (eliminationTraceValuation trace) value))
              value
        rw [applyClassSolution_update_of_not_mem_vars
          _ _ _ value hoccursHead]
        simp
      · obtain ⟨hkeyNe, hvalueFresh⟩ :=
          not_mem_constraintVars_of_mem htriangular'.1 htailMem
        have hkeyNe' : constraint.1 ≠ key := Ne.symm hkeyNe
        change
          Function.update (eliminationTraceValuation trace) key
              (applyClassSolution (eliminationTraceValuation trace) value)
              constraint.1 =
            applyClassSolution
              (Function.update (eliminationTraceValuation trace) key
                (applyClassSolution (eliminationTraceValuation trace) value))
              constraint.2
        rw [applyClassSolution_update_of_not_mem_vars
          _ _ _ constraint.2 hvalueFresh]
        simpa [Function.update, hkeyNe'] using htail constraint htailMem

/-- Every successful repaired-LeaTTa Robinson run from the empty
substitution has a concrete model of its input equation worklist.  The model
is built from the selected triangular trace; no MGU uniqueness or external
completeness axiom is used. -/
theorem exists_unifyRounds_equations_satisfied_empty
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {result : Metta.Subst}
    (himage : LeaEquationsInHEImage equations)
    (hrun : Metta.Unify.unifyRounds fuel equations [] = some result) :
    ∃ valuation : String → Metta.Atom,
      MettaEquationsSatisfied valuation equations := by
  let trace := unificationEliminationTrace fuel equations
  let valuation := eliminationTraceValuation trace
  have hfresh : UnifyStateFresh equations [] := by
    simp [UnifyStateFresh, mettaSubstKeys]
  have htraceSatisfied : MettaConstraintsSatisfied valuation trace :=
    eliminationTraceValuation_satisfies trace
      (by
        simpa [trace] using
          unificationEliminationTrace_triangular_of_success hfresh hrun)
      (by
        intro key value hmem
        exact unificationEliminationTrace_key_not_mem_value_vars _ _
          key value (by simpa [trace] using hmem))
  have hresultEq : result = trace.reverse := by
    simpa [trace] using
      (unifyRounds_result_eq_eliminationTrace_reverse_append hfresh hrun)
  have hresultSatisfied : MettaConstraintsSatisfied valuation result := by
    rw [hresultEq]
    exact (mettaConstraintsSatisfied_reverse valuation trace).mpr
      htraceSatisfied
  refine ⟨valuation, ?_⟩
  exact (unifyRounds_solution_iff valuation himage.noFloat hfresh hrun).mp
    hresultSatisfied |>.1

/-- A successful singleton variable equation records the corresponding alias
in its Robinson trace.  The conclusion is graph reachability, so the
reflexive case and either later edge orientation have the same meaning. -/
theorem singletonVarEquation_reachable_in_eliminationTrace
    {fuel : Nat} {left right : String} {result : Metta.Subst}
    (hrun : Metta.Unify.unifyRounds fuel
      [(.var left, .var right)] [] = some result) :
    (EqualityClosure.edgeGraph
      (eliminationTraceAliases
        (unificationEliminationTrace fuel
          [(.var left, .var right)]))).Reachable left right := by
  by_cases hsame : left = right
  · subst right
    exact .rfl
  · cases fuel with
    | zero =>
        simp [Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
          Metta.Unify.decomposeEq, hsame] at hrun
    | succ fuel =>
        apply (show
          (EqualityClosure.edgeGraph
            (eliminationTraceAliases
              (unificationEliminationTrace (fuel + 1)
                [(.var left, .var right)]))).Adj left right by
          rw [EqualityClosure.edgeGraph_adj_iff]
          refine ⟨hsame, Or.inl ?_⟩
          rw [mem_eliminationTraceAliases_iff]
          simp [unificationEliminationTrace, Metta.Unify.decomposeAll,
            Metta.Unify.decomposeEq, Metta.Subst.occurs, hsame]).reachable

/-- Every successful non-expression Robinson equation has an original HE
matcher derivation with both local certificates.  This closes the leaf side
of the strict recursion; only genuine expression/list traversal remains. -/
theorem exists_leafMatchCertified_of_unifyRounds_success
    {fuel : Nat} {left right : Atom} {result : Metta.Subst}
    (hleaf : ¬ BothExpressions left right)
    (hrun : Metta.Unify.unifyRounds fuel
      [(toLeaTTaAtom left, toLeaTTaAtom right)] [] = some result) :
    Nonempty (HEMatchCertified
      (unificationEliminationTrace fuel
        [(toLeaTTaAtom left, toLeaTTaAtom right)])
      (eliminationTraceAliases
        (unificationEliminationTrace fuel
          [(toLeaTTaAtom left, toLeaTTaAtom right)]))
      left right) := by
  obtain ⟨valuation, hequation⟩ :=
    exists_unifyRounds_equations_satisfied_empty
      (equations := [(toLeaTTaAtom left, toLeaTTaAtom right)])
      (by
        intro equation hmem
        simp only [List.mem_singleton] at hmem
        subst equation
        exact ⟨LeaAtomInHEImage.translation left,
          LeaAtomInHEImage.translation right⟩)
      hrun
  have hsingle : MettaEquationSatisfied valuation
      (toLeaTTaAtom left, toLeaTTaAtom right) :=
    hequation _ (by simp)
  obtain ⟨out, hmatch⟩ :=
    exists_matchRel_of_solution_leaf ⟨valuation, hsingle⟩ hleaf
  refine ⟨{
    out := out
    matchRel := hmatch
    traceSound := ?_
    equalitySound := ?_
  }⟩
  · cases hmatch with
    | symSym => exact .symSym
    | varVar => exact .varVar
    | varNonVar hnonvar => exact .varNonVar (hnonvar := hnonvar)
    | nonVarVar hnonvar => exact .nonVarVar (hnonvar := hnonvar)
    | grounded => exact .grounded
    | expr hlist => exact (hleaf (by simp [BothExpressions])).elim
  · cases hmatch with
    | symSym => exact .symSym
    | varVar left right =>
        apply MatchEqualityClosureBoundSound.varVar
        simpa [toLeaTTaAtom] using
          singletonVarEquation_reachable_in_eliminationTrace hrun
    | varNonVar hnonvar => exact .varNonVar (hnonvar := hnonvar)
    | nonVarVar hnonvar => exact .nonVarVar (hnonvar := hnonvar)
    | grounded => exact .grounded
    | expr hlist => exact (hleaf (by simp [BothExpressions])).elim

/-- A leaf equality-bound certificate is monotone under inclusion of its
allowed equality graph.  The expression constructor is excluded explicitly;
its recursive merges require the general mutual monotonicity theorem. -/
theorem MatchEqualityClosureBoundSound.mono_of_leaf
    {small large : List (String × String)}
    {left right : Atom} {out : Bindings}
    {hmatch : DeclMatchSpec.MatchRel left right out}
    (h : MatchEqualityClosureBoundSound small hmatch)
    (hleaf : ¬ BothExpressions left right)
    (hmono : ∀ {start finish : String},
      (EqualityClosure.edgeGraph small).Reachable start finish →
        (EqualityClosure.edgeGraph large).Reachable start finish) :
    MatchEqualityClosureBoundSound large hmatch := by
  cases h with
  | symSym => exact .symSym
  | varVar hreachable => exact .varVar (hmono hreachable)
  | varNonVar => exact .varNonVar (hnonvar := by assumption)
  | nonVarVar => exact .nonVarVar (hnonvar := by assumption)
  | grounded => exact .grounded
  | expr hlist => exact (hleaf (by simp [BothExpressions])).elim

/-- Package-level leaf monotonicity for simultaneous enlargement of the
ambient Robinson trace and allowed alias graph. -/
def HEMatchCertified.mono_of_leaf
    {smallTrace largeTrace : List (String × Metta.Atom)}
    {smallAllowed largeAllowed : List (String × String)}
    {left right : Atom}
    (h : HEMatchCertified smallTrace smallAllowed left right)
    (hleaf : ¬ BothExpressions left right)
    (htrace : ∀ entry ∈ smallTrace, entry ∈ largeTrace)
    (halias : ∀ {start finish : String},
      (EqualityClosure.edgeGraph smallAllowed).Reachable start finish →
        (EqualityClosure.edgeGraph largeAllowed).Reachable start finish) :
    HEMatchCertified largeTrace largeAllowed left right := {
  out := h.out
  matchRel := h.matchRel
  traceSound := h.traceSound.mono htrace
  equalitySound := h.equalitySound.mono_of_leaf hleaf halias
}

/-- A certified leaf match remains certified when later Robinson eliminations
are appended to its ambient trace.  The selected matcher and its bindings are
unchanged; only the provenance and permitted equality graph are enlarged. -/
def HEMatchCertified.appendTrace_of_leaf
    {trace : List (String × Metta.Atom)} {left right : Atom}
    (h : HEMatchCertified trace (eliminationTraceAliases trace) left right)
    (hleaf : ¬ BothExpressions left right)
    (extra : List (String × Metta.Atom)) :
    HEMatchCertified (trace ++ extra)
      (eliminationTraceAliases (trace ++ extra)) left right := by
  apply h.mono_of_leaf hleaf
  · intro entry hentry
    exact List.mem_append_left _ hentry
  · intro start finish hreach
    apply hreach.mono
    intro first second hadj
    rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
    rw [eliminationTraceAliases_append]
    rcases hadj with ⟨hne, hforward | hreverse⟩
    · exact ⟨hne, Or.inl (List.mem_append_left _ hforward)⟩
    · exact ⟨hne, Or.inr (List.mem_append_left _ hreverse)⟩

/-- A certified leaf matcher result merges into any assignment-free seed
without recursion.  Symbols and grounded atoms merge the empty record,
variable/non-variable leaves take the fresh-assignment branch, and a
variable/variable leaf takes the consistent-equality branch. -/
theorem exists_leafMatch_mergeRel_assignmentFreeSeed_certified
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : Atom} {matched seed : Bindings}
    {hmatch : DeclMatchSpec.MatchRel left right matched}
    (htrace : MatchTraceSound trace hmatch)
    (hbound : MatchEqualityClosureBoundSound allowed hmatch)
    (hleaf : ¬ BothExpressions left right)
    (hseedAssignments : seed.assignments = []) :
    ∃ out, ∃ hmerge : MergeRel seed matched out,
      MergeTraceSound trace hmerge ∧
        MergeEqualityClosureBoundSound allowed hmerge := by
  let AtomMotive := fun {atomLeft atomRight : Atom} {out : Bindings}
      (matchRel : DeclMatchSpec.MatchRel atomLeft atomRight out)
      (_ : MatchTraceSound trace matchRel) =>
    MatchEqualityClosureBoundSound allowed matchRel →
      ¬ BothExpressions atomLeft atomRight →
      ∃ merged, ∃ hmerge : MergeRel seed out merged,
        MergeTraceSound trace hmerge ∧
          MergeEqualityClosureBoundSound allowed hmerge
  let ListMotive := fun {atomLeft atomRight : List Atom}
      {listSeed out : Bindings}
      (matchRel : DeclMatchSpec.MatchListAccRel
        atomLeft atomRight listSeed out)
      (_ : MatchListTraceSound trace matchRel) => True
  apply MatchTraceSound.rec
      (motive_1 := AtomMotive) (motive_2 := ListMotive)
      (t := htrace)
  · intro name _hbound _hleaf
    let hassignments : MergeAssignsRel seed [] seed := .nil
    let hequalities : MergeEqsRel seed [] seed := .nil
    exact ⟨seed, MergeRel.mk hassignments hequalities,
      MergeTraceSound.mk .nil .nil,
      MergeEqualityClosureBoundSound.mk .nil .nil⟩
  · intro varLeft varRight hbound _hleaf
    cases hbound with
    | varVar hallowed =>
        have hclass :
            (seed.addEquality varLeft varRight).classValues varLeft = [] := by
          unfold Bindings.classValues Bindings.lookup
          simp [Bindings.addEquality, hseedAssignments]
        have hconsistent : Bindings.valuesConsistent
            ((seed.addEquality varLeft varRight).classValues varLeft) = true := by
          simp [hclass, Bindings.valuesConsistent]
        let hadd : AddVarEqualityRel seed varLeft varRight
            (seed.addEquality varLeft varRight) :=
          AddVarEqualityRel.consistent hconsistent
        let hassignments : MergeAssignsRel seed [] seed := .nil
        let hequalities : MergeEqsRel seed [(varLeft, varRight)]
            (seed.addEquality varLeft varRight) :=
          .cons hadd .nil
        let hmerge : MergeRel seed ⟨[], [(varLeft, varRight)]⟩
            (seed.addEquality varLeft varRight) :=
          .mk hassignments hequalities
        exact ⟨seed.addEquality varLeft varRight, hmerge,
          MergeTraceSound.mk .nil
            (.cons (.consistent (hconsistent := hconsistent)) .nil),
          MergeEqualityClosureBoundSound.mk .nil
            (.cons (.consistent (hconsistent := hconsistent) hallowed)
              .nil)⟩
  · intro key value hnonvar _hbound _hleaf
    have hclass : seed.classValues key = [] := by
      unfold Bindings.classValues Bindings.lookup
      simp [hseedAssignments]
    let hadd : AddVarBindingRel seed key value (seed.assign key value) :=
      AddVarBindingRel.fresh hclass
    let hassignments : MergeAssignsRel seed [(key, value)]
        (seed.assign key value) := .cons hadd .nil
    let hequalities : MergeEqsRel (seed.assign key value) []
        (seed.assign key value) := .nil
    let hmerge : MergeRel seed ⟨[(key, value)], []⟩
        (seed.assign key value) := .mk hassignments hequalities
    exact ⟨seed.assign key value, hmerge,
      MergeTraceSound.mk
        (.cons (.fresh (hclass := hclass)) .nil) .nil,
      MergeEqualityClosureBoundSound.mk
        (.cons (.fresh (hclass := hclass)) .nil) .nil⟩
  · intro value key hnonvar _hbound _hleaf
    have hclass : seed.classValues key = [] := by
      unfold Bindings.classValues Bindings.lookup
      simp [hseedAssignments]
    let hadd : AddVarBindingRel seed key value (seed.assign key value) :=
      AddVarBindingRel.fresh hclass
    let hassignments : MergeAssignsRel seed [(key, value)]
        (seed.assign key value) := .cons hadd .nil
    let hequalities : MergeEqsRel (seed.assign key value) []
        (seed.assign key value) := .nil
    let hmerge : MergeRel seed ⟨[(key, value)], []⟩
        (seed.assign key value) := .mk hassignments hequalities
    exact ⟨seed.assign key value, hmerge,
      MergeTraceSound.mk
        (.cons (.fresh (hclass := hclass)) .nil) .nil,
      MergeEqualityClosureBoundSound.mk
        (.cons (.fresh (hclass := hclass)) .nil) .nil⟩
  · intro ground _hbound _hleaf
    let hassignments : MergeAssignsRel seed [] seed := .nil
    let hequalities : MergeEqsRel seed [] seed := .nil
    exact ⟨seed, MergeRel.mk hassignments hequalities,
      MergeTraceSound.mk .nil .nil,
      MergeEqualityClosureBoundSound.mk .nil .nil⟩
  · intro atomLeft atomRight out hlist hlistTrace _ih _hbound hleaf
    exact (hleaf ⟨atomLeft, atomRight, rfl, rfl⟩).elim
  · intro listSeed
    trivial
  · intro atomLeft atomRight lefts rights listSeed headOut next out fuel
      hhead hmerge htail hheadTrace hmergeTrace htailTrace _ihHead _ihTail
    trivial
  · exact hbound
  · exact hleaf

/-- Executable surface of the assignment-free-seed leaf merge theorem, aligned to
the exact concrete merge proof by proof irrelevance only. -/
theorem HEMatchCertified.exists_mergeIntoAssignmentFreeSeed_of_leaf
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : Atom}
    (h : HEMatchCertified trace allowed left right)
    (hleaf : ¬ BothExpressions left right)
    {seed : Bindings}
    (hseedAssignments : seed.assignments = []) :
    ∃ out fuel, ∃ hmerge : out ∈ mergeBindings seed h.out fuel,
      MergeTraceSound trace (mergeBindings_sound hmerge) ∧
        MergeEqualityClosureBoundSound allowed
          (mergeBindings_sound hmerge) := by
  obtain ⟨out, hmerge, htrace, hbound⟩ :=
    exists_leafMatch_mergeRel_assignmentFreeSeed_certified
      h.traceSound h.equalitySound hleaf hseedAssignments
  obtain ⟨fuel, hmem⟩ := mergeBindings_complete hmerge
  refine ⟨out, fuel, hmem, ?_, ?_⟩
  · simpa only [Subsingleton.elim (mergeBindings_sound hmem) hmerge] using
      htrace
  · simpa only [Subsingleton.elim (mergeBindings_sound hmem) hmerge] using
      hbound

/-- One certified leaf match, merged into an assignment-free live seed, is a
certified singleton list match.  This is the nonrecursive first-divergence
prefix consumed before the residual expression tail. -/
theorem HEMatchCertified.exists_singletonListAcc_of_assignmentFreeSeed
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : Atom}
    (h : HEMatchCertified trace allowed left right)
    (hleaf : ¬ BothExpressions left right)
    {seed : Bindings}
    (hseedAssignments : seed.assignments = []) :
    Nonempty (HEMatchListAccCertified trace allowed
      [left] [right] seed) := by
  obtain ⟨out, fuel, hmerge, hmergeTrace, hmergeBound⟩ :=
    h.exists_mergeIntoAssignmentFreeSeed_of_leaf hleaf hseedAssignments
  let hlist : DeclMatchSpec.MatchListAccRel [left] [right] seed out :=
    .cons h.matchRel hmerge .nil
  exact ⟨{
    out := out
    matchRel := hlist
    traceSound := MatchListTraceSound.cons (hmerge := hmerge)
      h.traceSound hmergeTrace .nil
    equalitySound := MatchListEqualityClosureBoundSound.cons
      (hmerge := hmerge) h.equalitySound hmergeBound .nil
  }⟩

/-- Positive regression oracle: a leaf assignment merges into every
assignment-free seed, even when that seed already carries equality edges. -/
theorem assignmentFreeLeafMerge_positiveOracle
    (seed : Bindings) (hseed : seed.assignments = []) :
    ∃ out, MergeRel seed ⟨[("x", .symbol "a")], []⟩ out := by
  let hmatch : DeclMatchSpec.MatchRel (.var "x") (.symbol "a")
      ⟨[("x", .symbol "a")], []⟩ :=
    .varNonVar (by simp [DeclMatchSpec.Atom.isVarB])
  obtain ⟨out, hmerge, _htrace, _hbound⟩ :=
    exists_leafMatch_mergeRel_assignmentFreeSeed_certified
      (trace := []) (allowed := []) (hmatch := hmatch)
      (.varNonVar (trace := [])
        (hnonvar := by simp [DeclMatchSpec.Atom.isVarB]))
      (.varNonVar (allowed := [])
        (hnonvar := by simp [DeclMatchSpec.Atom.isVarB]))
      (by simp [BothExpressions]) hseed
  exact ⟨out, hmerge⟩

/-- Negative regression oracle: removing the assignment-free premise is not
sound; an occupied class cannot accept a different, nonmatching symbol. -/
theorem occupiedIncompatibleLeafAssignment_negativeOracle
    {out : Bindings} :
    ¬ AddVarBindingRel ⟨[("x", .symbol "a")], []⟩
      "x" (.symbol "b") out := by
  intro h
  cases h with
  | fresh hvalues =>
      simp [Bindings.classValues, Bindings.eqClassOrdered,
        Bindings.eqVarsInOrder, Bindings.eqClass, Bindings.eqClassAux,
        Bindings.lookup] at hvalues
  | same hvalues _ hsame =>
      simp [Bindings.classValues, Bindings.eqClassOrdered,
        Bindings.eqVarsInOrder, Bindings.eqClass, Bindings.eqClassAux,
        Bindings.lookup] at hvalues
      rcases hvalues with ⟨rfl, rfl⟩
      simp at hsame
  | conflict hvalues _ _ hm _ =>
      simp [Bindings.classValues, Bindings.eqClassOrdered,
        Bindings.eqVarsInOrder, Bindings.eqClass, Bindings.eqClassAux,
        Bindings.lookup] at hvalues
      rcases hvalues with ⟨rfl, rfl⟩
      exact absurd (DeclMatchSpec.matchRel_symSym_inv hm).1 (by decide)
  | reconcile hvalues hinconsistent _ _ =>
      simp [Bindings.classValues, Bindings.eqClassOrdered,
        Bindings.eqVarsInOrder, Bindings.eqClass, Bindings.eqClassAux,
        Bindings.lookup] at hvalues
      rcases hvalues with ⟨rfl, rfl⟩
      simp [Bindings.valuesConsistent] at hinconsistent

/-- A leaf match constructed from a solved prefix embeds into the complete
prefixed Robinson trace.  Both certificates are transported by graph/list
inclusion, so the residual trace may add aliases in either orientation without
changing the leaf derivation. -/
theorem exists_leafMatchCertified_of_prefixSplit
    {fuel : Nat} {left right : Atom}
    {suffix : List (Metta.Atom × Metta.Atom)}
    {remainingFuel : Nat}
    {suffixWork : List (Metta.Atom × Metta.Atom)}
    {prefixSubst : Metta.Subst}
    (h : UnifyRoundsPrefixSplit fuel
      [(toLeaTTaAtom left, toLeaTTaAtom right)] suffix []
      remainingFuel suffixWork prefixSubst)
    (hleaf : ¬ BothExpressions left right) :
    Nonempty (HEMatchCertified
      (unificationEliminationTrace fuel
        ([(toLeaTTaAtom left, toLeaTTaAtom right)] ++ suffix))
      (eliminationTraceAliases
        (unificationEliminationTrace fuel
          ([(toLeaTTaAtom left, toLeaTTaAtom right)] ++ suffix)))
      left right) := by
  let localTrace := unificationEliminationTrace fuel
    [(toLeaTTaAtom left, toLeaTTaAtom right)]
  let fullTrace := unificationEliminationTrace fuel
    ([(toLeaTTaAtom left, toLeaTTaAtom right)] ++ suffix)
  obtain ⟨hlocal⟩ :=
    exists_leafMatchCertified_of_unifyRounds_success hleaf h.front_run
  have htraceEq : fullTrace = localTrace ++
      unificationEliminationTrace remainingFuel suffixWork := by
    simpa [localTrace, fullTrace] using h.trace_append
  have htraceSubset : ∀ entry ∈ localTrace, entry ∈ fullTrace := by
    intro entry hmem
    rw [htraceEq]
    exact List.mem_append_left _ hmem
  have haliasSubset : ∀ edge ∈ eliminationTraceAliases localTrace,
      edge ∈ eliminationTraceAliases fullTrace := by
    intro edge hmem
    rw [htraceEq, eliminationTraceAliases_append]
    exact List.mem_append_left _ hmem
  have hreachMono : ∀ {start finish : String},
      (EqualityClosure.edgeGraph
        (eliminationTraceAliases localTrace)).Reachable start finish →
      (EqualityClosure.edgeGraph
        (eliminationTraceAliases fullTrace)).Reachable start finish := by
    intro start finish hreach
    apply hreach.mono
    intro first second hadj
    rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
    rcases hadj with ⟨hne, hforward | hreverse⟩
    · exact ⟨hne, Or.inl (haliasSubset _ hforward)⟩
    · exact ⟨hne, Or.inr (haliasSubset _ hreverse)⟩
  refine ⟨{
    out := hlocal.out
    matchRel := hlocal.matchRel
    traceSound := hlocal.traceSound.mono htraceSubset
    equalitySound := hlocal.equalitySound.mono_of_leaf hleaf hreachMono
  }⟩

/-- Certified first-divergence frontier for an unequal original expression
inside a successful local class reconciliation.  The first unequal child is
either a genuine expression pair with a strictly smaller executable Robinson
state, or an actual original HE match of the whole common-plus-leaf prefix,
including its live merge into the reflexive common-prefix accumulator. -/
theorem LeaUnifyValuesExecutablePrefixWitness.exists_originalExpressionFirstDivergenceCertifiedFrontier
    {left right : List Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      (toLeaTTaAtom (.expression left))
      (toLeaTTaAtom (.expression right)) rest result)
    (hne : left ≠ right) :
    let localFuel :=
      (toLeaTTaAtom (.expression left)).size +
        (((toLeaTTaAtom (.expression right)) :: rest).map
          Metta.Atom.size).sum
    let fullTrace := unificationEliminationTrace localFuel
      (((toLeaTTaAtom (.expression right)) :: rest).map
        fun value => (toLeaTTaAtom (.expression left), value))
    ∃ common leftHead leftTail rightHead rightTail
        remainingFuel tailWork childSubst,
      left = common ++ leftHead :: leftTail ∧
        right = common ++ rightHead :: rightTail ∧
        leftHead ≠ rightHead ∧
        leftTail.length = rightTail.length ∧
        UnifyRoundsPrefixSplit localFuel
            [(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)]
            (List.zip (toLeaTTaAtoms leftTail)
              (toLeaTTaAtoms rightTail)) []
            remainingFuel tailWork childSubst ∧
        Metta.Unify.unifyRounds remainingFuel tailWork childSubst =
          some h.headSubst ∧
        remainingFuel < localFuel ∧
        LeaEquationsInHEImage tailWork ∧
        LeaSubstInHEImage childSubst ∧
        (BothExpressions leftHead rightHead ∨
          Nonempty (HEMatchListAccCertified fullTrace
            (eliminationTraceAliases fullTrace)
            (common ++ [leftHead]) (common ++ [rightHead])
            Bindings.empty)) := by
  dsimp only
  obtain ⟨common, leftHead, leftTail, rightHead, rightTail,
      remainingFuel, tailWork, childSubst,
      hleft, hright, hheadNe, htailLength, hsplit, hcontinue,
      hlt, _htrace, htailImage, hchildImage⟩ :=
    h.exists_originalExpressionFirstDivergence hne
  refine ⟨common, leftHead, leftTail, rightHead, rightTail,
    remainingFuel, tailWork, childSubst,
    hleft, hright, hheadNe, htailLength, hsplit, hcontinue,
    hlt, htailImage, hchildImage, ?_⟩
  by_cases hexpressions : BothExpressions leftHead rightHead
  · exact Or.inl hexpressions
  · right
    obtain ⟨hlocal⟩ :=
      exists_leafMatchCertified_of_prefixSplit hsplit hexpressions
    let reducedTrace := unificationEliminationTrace
      ((toLeaTTaAtom (.expression left)).size +
        (((toLeaTTaAtom (.expression right)) :: rest).map
          Metta.Atom.size).sum)
      ([(toLeaTTaAtom leftHead, toLeaTTaAtom rightHead)] ++
        List.zip (toLeaTTaAtoms leftTail) (toLeaTTaAtoms rightTail))
    let outerTrace := unificationEliminationTrace
      h.remainingFuel h.tailWork
    have htranslatedTailLength :
        (toLeaTTaAtoms leftTail).length =
          (toLeaTTaAtoms rightTail).length := by
      simpa only [length_toLeaTTaAtoms] using htailLength
    have hdrop :=
      unificationEliminationTrace_expression_drop_translated_common
        common (leftHead :: leftTail) (rightHead :: rightTail)
        ((toLeaTTaAtom (.expression left)).size +
          (((toLeaTTaAtom (.expression right)) :: rest).map
            Metta.Atom.size).sum)
        (by simpa using htailLength)
    rw [← hleft, ← hright] at hdrop
    have hfrontReduced :
        unificationEliminationTrace
            ((toLeaTTaAtom (.expression left)).size +
              (((toLeaTTaAtom (.expression right)) :: rest).map
                Metta.Atom.size).sum)
            [(toLeaTTaAtom (.expression left),
              toLeaTTaAtom (.expression right))] = reducedTrace := by
      calc
        _ = unificationEliminationTrace
              ((toLeaTTaAtom (.expression left)).size +
                (((toLeaTTaAtom (.expression right)) :: rest).map
                  Metta.Atom.size).sum)
              [(.expr (toLeaTTaAtoms left),
                .expr (toLeaTTaAtoms right))] := by rfl
        _ = unificationEliminationTrace
              ((toLeaTTaAtom (.expression left)).size +
                (((toLeaTTaAtom (.expression right)) :: rest).map
                  Metta.Atom.size).sum)
              [(.expr (toLeaTTaAtoms (leftHead :: leftTail)),
                .expr (toLeaTTaAtoms (rightHead :: rightTail)))] := hdrop
        _ = reducedTrace := by
          rw [unificationEliminationTrace_expression_eq_zip (by
            simpa only [toLeaTTaAtoms, List.length_cons] using
              congrArg Nat.succ htranslatedTailLength)]
          rfl
    have hfullTraceEq :
        unificationEliminationTrace
            ((toLeaTTaAtom (.expression left)).size +
              (((toLeaTTaAtom (.expression right)) :: rest).map
                Metta.Atom.size).sum)
            (((toLeaTTaAtom (.expression right)) :: rest).map
              fun value => (toLeaTTaAtom (.expression left), value)) =
          reducedTrace ++ outerTrace := by
      calc
        _ = unificationEliminationTrace
              ((toLeaTTaAtom (.expression left)).size +
                (((toLeaTTaAtom (.expression right)) :: rest).map
                  Metta.Atom.size).sum)
              [(toLeaTTaAtom (.expression left),
                toLeaTTaAtom (.expression right))] ++ outerTrace := by
              simpa only [List.map_cons, List.singleton_append, outerTrace]
                using h.split.trace_append
        _ = reducedTrace ++ outerTrace := by rw [hfrontReduced]
    have hlocal' : HEMatchCertified reducedTrace
        (eliminationTraceAliases reducedTrace) leftHead rightHead := by
      simpa only [reducedTrace] using hlocal
    have hlifted := hlocal'.appendTrace_of_leaf hexpressions outerTrace
    let fullTrace := unificationEliminationTrace
      ((toLeaTTaAtom (.expression left)).size +
        (((toLeaTTaAtom (.expression right)) :: rest).map
          Metta.Atom.size).sum)
      (((toLeaTTaAtom (.expression right)) :: rest).map
        fun value => (toLeaTTaAtom (.expression left), value))
    have hfullTraceEq' : fullTrace = reducedTrace ++ outerTrace := by
      simpa only [fullTrace] using hfullTraceEq
    rw [← hfullTraceEq'] at hlifted
    let hcommon := reflexiveMatchListCertified fullTrace
      (eliminationTraceAliases fullTrace) common
    obtain ⟨hsingleton⟩ :=
      hlifted.exists_singletonListAcc_of_assignmentFreeSeed
        hexpressions hcommon.assignments_nil
    let hprefix := prependReflexiveMatchListCertified hcommon hsingleton
    exact ⟨by simpa only [fullTrace] using hprefix⟩

/-- A successful whole-system reconciliation result has an explicit satisfying
valuation, constructed from its triangular solve trace. -/
theorem exists_wholeBindingReconciliation_result_satisfied
    {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    ∃ valuation : String → Metta.Atom,
      MettaConstraintsSatisfied valuation result := by
  let trace := unificationEliminationTrace
    (Metta.Bindings.equationFuel
      (Metta.Bindings.equations source ++ extra))
    (Metta.Bindings.equations source ++ extra)
  refine ⟨eliminationTraceValuation trace, ?_⟩
  have htrace : MettaConstraintsSatisfied
      (eliminationTraceValuation trace) trace :=
    eliminationTraceValuation_satisfies trace
      (by
        simpa [trace] using
          wholeBindingReconciliation_eliminationTrace_triangular hreconcile)
      (by
        intro key value hmem
        exact unificationEliminationTrace_key_not_mem_value_vars _ _
          key value (by simpa [trace] using hmem))
  rw [wholeBindingReconciliation_result_eq_eliminationTrace_reverse
    hreconcile]
  exact (mettaConstraintsSatisfied_reverse
    (eliminationTraceValuation trace) trace).mpr htrace

/-- Successful reconciliation is not merely syntactically terminating: its
source constraints and requested equations have a common valuation. -/
theorem exists_wholeBindingReconciliation_input_satisfied
    {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation source ∧
        MettaEquationsSatisfied valuation extra := by
  obtain ⟨valuation, hresult⟩ :=
    exists_wholeBindingReconciliation_result_satisfied hreconcile
  exact ⟨valuation,
    (wholeBindingReconciliation_solution_iff valuation
      hsourceNoFloat hextraNoFloat hreconcile).mp hresult⟩

/-- Cross-engine congruence transports the explicit reconciliation model to
the HE input record. -/
theorem exists_heBinding_and_extra_satisfied_of_reconciliation
    {b : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation b ∧
        MettaEquationsSatisfied valuation extra := by
  obtain ⟨valuation, hsource, hextra⟩ :=
    exists_wholeBindingReconciliation_input_satisfied
      hsourceNoFloat hextraNoFloat hreconcile
  exact ⟨valuation,
    (hbase.semantic.solutions valuation).mpr hsource, hextra⟩

/-- In a successful value reconciliation, every value already carried by the
target HE class has a common solution with the proposed value.  This is the
semantic premise needed by each HE conflict matcher branch. -/
theorem exists_classValue_equation_satisfied_of_reconciliation
    {b : Bindings} {source : Metta.Bindings}
    {key : String} {stored proposed : Atom} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var key, toLeaTTaAtom proposed)] = some result)
    (hstored : stored ∈ b.classValues key) :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation b ∧
        MettaEquationSatisfied valuation
          (toLeaTTaAtom stored, toLeaTTaAtom proposed) := by
  obtain ⟨valuation, hbinding, hextra⟩ :=
    exists_heBinding_and_extra_satisfied_of_reconciliation
      hbase hsourceNoFloat
        (by
          intro equation hmem
          simp only [List.mem_singleton] at hmem
          subst equation
          exact ⟨by simp [MettaAtomNoFloat],
            toLeaTTaAtom_noFloat proposed⟩)
        hreconcile
  have hproposed : valuation key =
      applyClassSolution valuation (toLeaTTaAtom proposed) := by
    have h := hextra
      (.var key, toLeaTTaAtom proposed) (by simp)
    simpa [MettaEquationSatisfied, applyClassSolution] using h
  have hstoredValue : valuation key =
      applyClassSolution valuation (toLeaTTaAtom stored) :=
    hbinding.eq_applyClassSolution_of_mem_classValues hstored
  exact ⟨valuation, hbinding, by
    exact hstoredValue.symm.trans hproposed⟩

/-- A non-expression class conflict exposed by successful reconciliation is
an actual finite-fuel HE matcher success. -/
theorem exists_matchAtoms_classValue_of_reconciliation
    {b : Bindings} {source : Metta.Bindings}
    {key : String} {stored proposed : Atom} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var key, toLeaTTaAtom proposed)] = some result)
    (hstored : stored ∈ b.classValues key)
    (hleaf : ¬ BothExpressions stored proposed) :
    ∃ out fuel, out ∈ matchAtoms stored proposed fuel := by
  obtain ⟨valuation, _hbinding, hequation⟩ :=
    exists_classValue_equation_satisfied_of_reconciliation
      hbase hsourceNoFloat hreconcile hstored
  exact exists_matchAtoms_of_solution_leaf
    ⟨valuation, hequation⟩ hleaf

/-- Under the matcher invariant, every unequal value conflict certified by
successful repaired-LeaTTa reconciliation is necessarily expression-shaped.
This is the recursive branch selected by HE; all non-variable leaf cases
collapse to equality. -/
theorem bothExpressions_of_ne_classValue_reconciliation
    {b : Bindings} {source : Metta.Bindings}
    {key : String} {stored proposed : Atom} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var key, toLeaTTaAtom proposed)] = some result)
    (hnonvar : HEAssignmentsNonVariable b)
    (hstored : stored ∈ b.classValues key)
    (hproposed : DeclMatchSpec.Atom.isVarB proposed = false)
    (hne : stored ≠ proposed) :
    BothExpressions stored proposed := by
  by_contra hleaf
  obtain ⟨out, fuel, hmatch⟩ :=
    exists_matchAtoms_classValue_of_reconciliation
      hbase hsourceNoFloat hreconcile hstored hleaf
  exact hne (matchAtoms_eq_of_nonvariable_leaf
    (hnonvar.isVarB_eq_false_of_classValue hstored)
    hproposed hleaf hmatch)

/-- With the isolated satisfiable merge-back premise, the same reconciliation
model manufactures HE conflict matches for arbitrary atom shapes. -/
theorem exists_matchAtoms_classValue_of_reconciliation_of_merge
    (hmerge : HESatisfiedMatcherMergeRelComplete)
    {b : Bindings} {source : Metta.Bindings}
    {key : String} {stored proposed : Atom} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var key, toLeaTTaAtom proposed)] = some result)
    (hstored : stored ∈ b.classValues key) :
    ∃ out fuel, out ∈ matchAtoms stored proposed fuel := by
  obtain ⟨valuation, _hbinding, hequation⟩ :=
    exists_classValue_equation_satisfied_of_reconciliation
      hbase hsourceNoFloat hreconcile hstored
  exact exists_matchAtoms_of_solution_of_merge hmerge hequation

/-- Joining two classes under a successful repaired-LeaTTa reconciliation
gives a common solution to every pair of values in the joined HE class. -/
theorem exists_joinedClassValues_equation_satisfied_of_reconciliation
    {b : Bindings} {source : Metta.Bindings}
    {left right : String} {first second : Atom} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var left, .var right)] = some result)
    (hfirst : first ∈ (b.addEquality left right).classValues left)
    (hsecond : second ∈ (b.addEquality left right).classValues left) :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation (b.addEquality left right) ∧
        MettaEquationSatisfied valuation
          (toLeaTTaAtom first, toLeaTTaAtom second) := by
  obtain ⟨valuation, hbinding, hextra⟩ :=
    exists_heBinding_and_extra_satisfied_of_reconciliation
      hbase hsourceNoFloat
        (by
          intro equation hmem
          simp only [List.mem_singleton] at hmem
          subst equation
          simp [MettaAtomNoFloat])
        hreconcile
  have hedge : valuation left = valuation right := by
    have h := hextra (.var left, .var right) (by simp)
    simpa [MettaEquationSatisfied, applyClassSolution] using h
  have hcandidate :
      HEBindingSatisfied valuation (b.addEquality left right) := by
    constructor
    · simpa [Bindings.addEquality] using hbinding.1
    · intro x y hmem
      simp only [Bindings.addEquality, List.mem_append,
        List.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with hold | hnew
      · exact hbinding.2 x y hold
      · rcases hnew with ⟨rfl, rfl⟩
        exact hedge
  have hfirstValue : valuation left =
      applyClassSolution valuation (toLeaTTaAtom first) :=
    hcandidate.eq_applyClassSolution_of_mem_classValues hfirst
  have hsecondValue : valuation left =
      applyClassSolution valuation (toLeaTTaAtom second) :=
    hcandidate.eq_applyClassSolution_of_mem_classValues hsecond
  exact ⟨valuation, hcandidate,
    hfirstValue.symm.trans hsecondValue⟩

/-- A non-expression pair selected from a successfully reconciled joined
class is an actual finite-fuel HE matcher success. -/
theorem exists_matchAtoms_joinedClassValues_of_reconciliation
    {b : Bindings} {source : Metta.Bindings}
    {left right : String} {first second : Atom} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var left, .var right)] = some result)
    (hfirst : first ∈ (b.addEquality left right).classValues left)
    (hsecond : second ∈ (b.addEquality left right).classValues left)
    (hleaf : ¬ BothExpressions first second) :
    ∃ out fuel, out ∈ matchAtoms first second fuel := by
  obtain ⟨valuation, _hcandidate, hequation⟩ :=
    exists_joinedClassValues_equation_satisfied_of_reconciliation
      hbase hsourceNoFloat hreconcile hfirst hsecond
  exact exists_matchAtoms_of_solution_leaf
    ⟨valuation, hequation⟩ hleaf

/-- Likewise, two unequal values exposed by joining equality classes can only
reconcile through HE's expression/list branch. -/
theorem bothExpressions_of_ne_joinedClassValues_reconciliation
    {b : Bindings} {source : Metta.Bindings}
    {left right : String} {first second : Atom} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var left, .var right)] = some result)
    (hnonvar : HEAssignmentsNonVariable b)
    (hfirst : first ∈ (b.addEquality left right).classValues left)
    (hsecond : second ∈ (b.addEquality left right).classValues left)
    (hne : first ≠ second) :
    BothExpressions first second := by
  have hcandidate :
      HEAssignmentsNonVariable (b.addEquality left right) := by
    intro key target hvalue
    apply hnonvar key target
    simpa [Bindings.addEquality] using hvalue
  by_contra hleaf
  obtain ⟨out, fuel, hmatch⟩ :=
    exists_matchAtoms_joinedClassValues_of_reconciliation
      hbase hsourceNoFloat hreconcile hfirst hsecond hleaf
  exact hne (matchAtoms_eq_of_nonvariable_leaf
    (hcandidate.isVarB_eq_false_of_classValue hfirst)
    (hcandidate.isVarB_eq_false_of_classValue hsecond)
    hleaf hmatch)

/-- Arbitrary joined-class conflicts are executable HE matches once the same
isolated satisfiable matcher-merge premise is available. -/
theorem exists_matchAtoms_joinedClassValues_of_reconciliation_of_merge
    (hmerge : HESatisfiedMatcherMergeRelComplete)
    {b : Bindings} {source : Metta.Bindings}
    {left right : String} {first second : Atom} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var left, .var right)] = some result)
    (hfirst : first ∈ (b.addEquality left right).classValues left)
    (hsecond : second ∈ (b.addEquality left right).classValues left) :
    ∃ out fuel, out ∈ matchAtoms first second fuel := by
  obtain ⟨valuation, _hcandidate, hequation⟩ :=
    exists_joinedClassValues_equation_satisfied_of_reconciliation
      hbase hsourceNoFloat hreconcile hfirst hsecond
  exact exists_matchAtoms_of_solution_of_merge hmerge hequation

/-- The canonical replay of a solve trace presents exactly the constraints in
that trace.  This theorem reads the replay semantically; its list order remains
irrelevant. -/
theorem LeaEliminationTraceReplay.satisfaction_iff
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation out ↔
      MettaConstraintsSatisfied valuation trace := by
  induction h with
  | nil =>
      simp [MettaConstraintsSatisfied]
  | @aliasStep trace b key target h ih =>
      rw [heBindingSatisfied_addEquality_iff, ih]
      constructor
      · rintro ⟨htail, hedge⟩ constraint hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hhead | htailMem
        · rcases hhead with ⟨rfl, rfl⟩
          simpa [applyClassSolution] using hedge
        · exact htail constraint htailMem
      · intro hall
        refine ⟨?_, ?_⟩
        · intro constraint hmem
          exact hall constraint (by simp [hmem])
        · have hhead := hall (key, .var target) (by simp)
          simpa [applyClassSolution] using hhead
  | @valueStep trace b key value leaValue h hlookup hatom hnonvar ih =>
      rw [heBindingSatisfied_assign_fresh_iff valuation hlookup]
      constructor
      · rintro ⟨hbase, hvalue⟩ constraint hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hhead | htailMem
        · rcases hhead with ⟨rfl, rfl⟩
          exact hvalue.trans
            (hatom.applyClassSolution_eq hbase)
        · exact ih.mp hbase constraint htailMem
      · intro hall
        have htail : MettaConstraintsSatisfied valuation trace := by
          intro constraint hmem
          exact hall constraint (by simp [hmem])
        have hbase : HEBindingSatisfied valuation b := ih.mpr htail
        have hhead := hall (key, leaValue) (by simp)
        exact ⟨hbase,
          hhead.trans (hatom.applyClassSolution_eq hbase).symm⟩

/-- A canonical HE replay and repaired LeaTTa's `ofSubst` view of the reverse
solve trace carry the same equality closure, solution theory, and
class-indexed raw-value provenance.  This is the reusable quotient bridge for
the paired induction; it does not assert that either presentation is an MGU
chosen by the other engine. -/
theorem LeaEliminationTraceReplay.congruence_ofSubst_reverse
    {trace : List (String × Metta.Atom)} {out : Bindings}
    (h : LeaEliminationTraceReplay Bindings.empty trace out) :
    LeaBindingCongruence out
      (Metta.Bindings.ofSubst trace.reverse) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro start finish
    rw [h.eqClass_iff, mem_leaEqClass_iff_reachable,
      leaEqualityEdges_ofSubst_eq_eliminationTraceAliases,
      eliminationTraceAliases_reverse]
  · intro valuation
    rw [h.satisfaction_iff, leaOfSubst_solution_iff,
      mettaConstraintsSatisfied_reverse]
  · have hstruct := h.structural
    constructor
    · intro key value hmem
      obtain ⟨leaKey, leaValue, htrace, hnonvar, hclass, hatom⟩ :=
        hstruct.classValues.1 key value hmem
      refine ⟨leaKey, leaValue, ?_, hclass, hatom⟩
      apply val_mem_ofSubst_iff.mpr
      exact ⟨by simpa using htrace, hnonvar⟩
    · intro leaKey leaValue hmem
      obtain ⟨hsubst, hnonvar⟩ := val_mem_ofSubst_iff.mp hmem
      have htrace : (leaKey, leaValue) ∈ trace := by
        simpa using hsubst
      obtain ⟨key, value, hassignment, hclass, hatom⟩ :=
        hstruct.classValues.2 leaKey leaValue htrace hnonvar
      exact ⟨key, value, hassignment, hclass, hatom⟩

/-- The executable prefix witness presents exactly the equation theory of its
first class-value conflict.  This follows by composing trace replay with the
landed Robinson solution theorem; it does not assert that the replay is an HE
matcher result or that its binding presentation is an MGU. -/
theorem LeaUnifyValuesExecutablePrefixWitness.solution_iff
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      first second rest result)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation h.heOut ↔
      MettaEquationSatisfied valuation (first, second) := by
  have hrunTheory := unifyRounds_solution_iff valuation
    (equations := [(first, second)])
    (subst := [])
    (result := h.headSubst)
    (by
      intro equation hmem
      simp only [List.mem_singleton] at hmem
      subst equation
      exact ⟨h.first_noFloat, h.second_noFloat⟩)
    (by simp [UnifyStateFresh, mettaSubstKeys])
    h.split.front_run
  calc
    HEBindingSatisfied valuation h.heOut ↔
        MettaConstraintsSatisfied valuation
          (h.entry :: h.prefixTail) :=
      h.replay.replay.satisfaction_iff valuation
    _ ↔ MettaConstraintsSatisfied valuation
          (h.entry :: h.prefixTail).reverse :=
      (mettaConstraintsSatisfied_reverse valuation
        (h.entry :: h.prefixTail)).symm
    _ ↔ MettaConstraintsSatisfied valuation h.headSubst := by
      rw [h.headSubst_eq]
    _ ↔ MettaEquationSatisfied valuation (first, second) := by
      simpa [MettaEquationsSatisfied, MettaConstraintsSatisfied] using
        hrunTheory

/-- The executable head prefix is fully congruent to the repaired LeaTTa
binding presentation generated by its actual Robinson prefix substitution.
The result combines the exact reverse-trace theorem with the generic replay
quotient bridge above. -/
theorem LeaUnifyValuesExecutablePrefixWitness.congruence_ofSubst
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      first second rest result) :
    LeaBindingCongruence h.heOut
      (Metta.Bindings.ofSubst h.headSubst) := by
  rw [h.headSubst_eq]
  exact h.replay.replay.congruence_ofSubst_reverse

/-- The canonical executable head replay is the actual HE accumulator for the
strict residual state of the original class-value equation.  The residual
worklist plus that live accumulator therefore denotes exactly the untouched
first-versus-all equation block.  This is the solution component consumed by
the recursive original matcher construction; witness existence remains an
independent operational obligation. -/
theorem LeaUnifyValuesExecutablePrefixWitness.heContinuation_solution_iff
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      first second rest result)
    (valuation : String → Metta.Atom) :
    (MettaEquationsSatisfied valuation h.tailWork ∧
        HEBindingSatisfied valuation h.heOut) ↔
      MettaEquationsSatisfied valuation
        ((second :: rest).map fun value => (first, value)) := by
  have hfrontImage : LeaEquationsInHEImage [(first, second)] := by
    intro equation hmem
    simp only [List.mem_singleton] at hmem
    subst equation
    exact h.equations_inHEImage (first, second) (by simp)
  have hsuffixImage : LeaEquationsInHEImage
      (rest.map fun value => (first, value)) := by
    intro equation hmem
    apply h.equations_inHEImage equation
    obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp hmem
    exact List.mem_map.mpr ⟨value, by simp [hvalue], rfl⟩
  have htheory := h.split.heContinuation_solution_iff
    hfrontImage hsuffixImage
    (by intro key term hmem; simp at hmem)
    (by simp [UnifyStateFresh, mettaSubstKeys])
    h.continue_run h.congruence_ofSubst valuation
  simpa [MettaConstraintsSatisfied] using htheory

/-- The selected singleton-equation prefix inherits the strict triangular
solve invariant from its successful standalone Robinson run. -/
theorem LeaUnifyValuesExecutablePrefixWitness.triangular
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      first second rest result) :
    EliminationTraceTriangular (h.entry :: h.prefixTail) := by
  have htriangular := unificationEliminationTrace_triangular_of_success
    (equations := [(first, second)])
    (subst := [])
    (by simp [UnifyStateFresh, mettaSubstKeys])
    h.split.front_run
  rw [h.front_trace_eq] at htriangular
  exact htriangular

/-- The prefix record is returned by HE's public merge surface from the empty
seed.  This is an operational existence fact, separate from its quotient
congruence with `ofSubst`. -/
theorem LeaUnifyValuesExecutablePrefixWitness.mem_mergeBindings_empty_left
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      first second rest result) :
    ∃ fuel, h.heOut ∈ mergeBindings Bindings.empty h.heOut fuel :=
  h.replay.replay.mem_mergeBindings_empty_left h.triangular

/-- The executable Robinson head-prefix record is returned by empty-left HE
merge together with a derivation-local certificate relative to the *full*
local class-unification trace.  This is the certified nonrecursive base fed
to the strict smaller-fuel conflict induction. -/
theorem LeaUnifyValuesExecutablePrefixWitness.exists_mem_mergeBindings_empty_left_fullTraceSound
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      first second rest result) :
    ∃ (fuel : Nat) (hmem : h.heOut ∈
        mergeBindings Bindings.empty h.heOut fuel),
      MergeTraceSound
        (unificationEliminationTrace
          (first.size + ((second :: rest).map Metta.Atom.size).sum)
          ((second :: rest).map fun value => (first, value)))
        (mergeBindings_sound hmem) := by
  exact h.replay.replay.exists_mem_mergeBindings_empty_left_traceSound_for
    h.triangular
    (unificationEliminationTrace
      (first.size + ((second :: rest).map Metta.Atom.size).sum)
      ((second :: rest).map fun value => (first, value)))

/-- Every assignment in the executable head-prefix record has provenance in
the full local class-unification trace, by the exact prefix/tail trace split. -/
theorem LeaUnifyValuesExecutablePrefixWitness.assignmentsSound_fullTrace
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      first second rest result) :
    LeaEliminationTraceAssignmentsSound h.heOut
      (unificationEliminationTrace
        (first.size + ((second :: rest).map Metta.Atom.size).sum)
        ((second :: rest).map fun value => (first, value))) := by
  apply LeaEliminationTraceAssignmentsSound.of_trace_subset
    h.replay.replay.structural.classValues.1
  intro entry hentry
  rw [h.trace_eq]
  exact List.mem_append_left _ hentry

/-- The executable prefix also satisfies the no-bare-variable invariant
required by every recursive matcher-origin merge accumulator. -/
theorem LeaUnifyValuesExecutablePrefixWitness.assignmentsNonVariable
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      first second rest result) :
    HEAssignmentsNonVariable h.heOut :=
  h.replay.replay.assignmentsNonVariable

/-- The exact Robinson substitution produced for the unequal head conflict
has an executable HE list-matcher presentation.  Its right-hand atoms are
compared with the substitution terms only through the final equality-class
closure, so representative order remains operational detail. -/
theorem LeaUnifyValuesExecutablePrefixWitness.exists_mem_matchAtomsList
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      first second rest result) :
    ∃ left right fuel,
      left = h.headSubst.map (fun entry => Atom.var entry.1) ∧
        List.Forall₂ (HELeaAtomClassRel h.heOut) right
          (h.headSubst.map Prod.snd) ∧
        h.heOut ∈ matchAtomsList left right [Bindings.empty] fuel := by
  obtain ⟨left, right, fuel, hleft, hright, hmem⟩ :=
    h.replay.exists_mem_matchAtomsList_reverse
  refine ⟨left, right, fuel, ?_, ?_, hmem⟩
  · rw [h.headSubst_eq]
    exact hleft
  · rw [h.headSubst_eq]
    exact hright

/-- Expression-packaged form of the exact head-prefix runtime witness.  This
is an actual matcher-origin record suitable for recursive merge chains, while
remaining agnostic about the original equation matcher's chosen MGU. -/
theorem LeaUnifyValuesExecutablePrefixWitness.exists_mem_matchAtoms_expression
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      first second rest result) :
    ∃ left right fuel,
      left = h.headSubst.map (fun entry => Atom.var entry.1) ∧
        List.Forall₂ (HELeaAtomClassRel h.heOut) right
          (h.headSubst.map Prod.snd) ∧
        h.heOut ∈
          matchAtoms (.expression left) (.expression right) fuel := by
  obtain ⟨left, right, fuel, hleft, hright, hmem⟩ :=
    h.replay.exists_mem_matchAtoms_expression_reverse
  refine ⟨left, right, fuel, ?_, ?_, hmem⟩
  · rw [h.headSubst_eq]
    exact hleft
  · rw [h.headSubst_eq]
    exact hright

/-- The head-prefix matcher presentation additionally certifies every merge
inside that expression match relative to the complete local class-unification
trace.  This is the exact recursive base required by the strict-fuel paired
conflict induction. -/
theorem LeaUnifyValuesExecutablePrefixWitness.exists_mem_matchAtoms_expression_fullTraceSound
    {first second : Metta.Atom} {rest : List Metta.Atom}
    {result : Metta.Subst}
    (h : LeaUnifyValuesExecutablePrefixWitness
      first second rest result) :
    ∃ left right fuel,
      ∃ hmem : h.heOut ∈
          matchAtoms (.expression left) (.expression right) fuel,
        left = h.headSubst.map (fun entry => Atom.var entry.1) ∧
          List.Forall₂ (HELeaAtomClassRel h.heOut) right
            (h.headSubst.map Prod.snd) ∧
          MatchTraceSound
            (unificationEliminationTrace
              (first.size + ((second :: rest).map Metta.Atom.size).sum)
              ((second :: rest).map fun value => (first, value)))
            (DeclMatchSpec.matchAtoms_sound hmem) := by
  obtain ⟨left, right, fuel, hmem, hleft, hright, hsound⟩ :=
    h.replay.exists_mem_matchAtoms_expression_reverse_traceSound_for
      h.triangular
      (unificationEliminationTrace
        (first.size + ((second :: rest).map Metta.Atom.size).sum)
        ((second :: rest).map fun value => (first, value)))
  refine ⟨left, right, fuel, hmem, ?_, ?_, hsound⟩
  · rw [h.headSubst_eq]
    exact hleft
  · rw [h.headSubst_eq]
    exact hright

/-- Replaying certified reconciliation aliases changes no solutions of the
canonical trace record. -/
theorem LeaAliasTraceReplay.satisfaction_iff_of_constraints
    {base out : Bindings} {aliases : List (String × String)}
    {result : Metta.Subst} {valuation : String → Metta.Atom}
    (h : LeaAliasTraceReplay base aliases out)
    (hbase : HEBindingSatisfied valuation base ↔
      MettaConstraintsSatisfied valuation result)
    (haliases : MettaConstraintsSatisfied valuation result →
      ∀ edge ∈ aliases, valuation edge.1 = valuation edge.2) :
    HEBindingSatisfied valuation out ↔
      HEBindingSatisfied valuation base := by
  induction h with
  | nil => exact Iff.rfl
  | @cons aliases b key target h ih =>
      have htailAliases : MettaConstraintsSatisfied valuation result →
          ∀ edge ∈ aliases, valuation edge.1 = valuation edge.2 := by
        intro hresult edge hedge
        exact haliases hresult edge (by simp [hedge])
      have htail := ih htailAliases
      rw [heBindingSatisfied_addEquality_iff, htail]
      constructor
      · exact And.left
      · intro hsat
        refine ⟨hsat, ?_⟩
        exact haliases (hbase.mp hsat) (key, target) (by simp)

/-- Redundant edges do not change the connected components of an undirected
edge graph. -/
private theorem reachable_append_of_subset
    {extra edges : List (String × String)}
    (hsub : ∀ edge ∈ extra, edge ∈ edges)
    (start finish : String) :
    (EqualityClosure.edgeGraph (extra ++ edges)).Reachable start finish ↔
      (EqualityClosure.edgeGraph edges).Reachable start finish := by
  constructor
  · intro hreach
    apply hreach.mono
    intro left right hadj
    rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
    rcases hadj with ⟨hne, hforward | hreverse⟩
    · rcases List.mem_append.mp hforward with hextra | hedge
      · exact ⟨hne, Or.inl (hsub _ hextra)⟩
      · exact ⟨hne, Or.inl hedge⟩
    · rcases List.mem_append.mp hreverse with hextra | hedge
      · exact ⟨hne, Or.inr (hsub _ hextra)⟩
      · exact ⟨hne, Or.inr hedge⟩
  · intro hreach
    apply hreach.mono
    intro left right hadj
    rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
    rcases hadj with ⟨hne, hforward | hreverse⟩
    · exact ⟨hne, Or.inl (List.mem_append_right _ hforward)⟩
    · exact ⟨hne, Or.inr (List.mem_append_right _ hreverse)⟩

private theorem edgeGraph_reverse
    (edges : List (String × String)) :
    EqualityClosure.edgeGraph edges.reverse =
      EqualityClosure.edgeGraph edges := by
  ext left right
  simp [EqualityClosure.edgeGraph_adj_iff]

/-- Replaying the selected solve trace and then every exposed alias yields
exactly the alias-trace equality closure and the elimination-trace raw-value
provenance, provided the selected aliases occur in the full alias trace. -/
theorem reconciliationReplay_structural
    {trace : List (String × Metta.Atom)}
    {aliases : List (String × String)} {mid out : Bindings}
    (htrace : LeaEliminationTraceReplay Bindings.empty trace mid)
    (haliases : LeaAliasTraceReplay mid aliases out)
    (hsub : ∀ edge ∈ eliminationTraceAliases trace, edge ∈ aliases) :
    (∀ start finish,
      finish ∈ out.eqClass start ↔
        (EqualityClosure.edgeGraph aliases).Reachable start finish) ∧
      LeaEliminationTraceClassValueRel out trace := by
  constructor
  · intro start finish
    rw [EqualityClosure.mem_eqClass_iff_reachable,
      haliases.equalities, htrace.equalities]
    have hsubReverse : ∀ edge ∈ (eliminationTraceAliases trace).reverse,
        edge ∈ aliases.reverse := by
      intro edge hedge
      simpa using hsub edge (by simpa using hedge)
    rw [reachable_append_of_subset hsubReverse start finish,
      edgeGraph_reverse]
  · exact haliases.classValues htrace.structural.classValues

/-- Successful reconciliation supplies the selected-alias inclusion needed by
the two-certificate replay theorem. -/
theorem reconciliationReplay_structural_of_success
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    {mid out : Bindings}
    (hreconcile : wholeBindingReconciliation bindings extra = some result)
    (htrace : LeaEliminationTraceReplay Bindings.empty
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra)) mid)
    (haliases : LeaAliasTraceReplay mid
      (Metta.Bindings.reconciliationAliases bindings extra result) out) :
    (∀ start finish,
      finish ∈ out.eqClass start ↔
        (EqualityClosure.edgeGraph
          (Metta.Bindings.reconciliationAliases bindings extra result)).Reachable
          start finish) ∧
      LeaEliminationTraceClassValueRel out
        (unificationEliminationTrace
          (Metta.Bindings.equationFuel
            (Metta.Bindings.equations bindings ++ extra))
          (Metta.Bindings.equations bindings ++ extra)) :=
  reconciliationReplay_structural htrace haliases
    (eliminationTraceAliases_subset_reconciliationAliases hreconcile)

/-! ## Source equality edges are already in the successful alias trace -/

private theorem decomposeAll_some_of_unifyRounds_success
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hrun : Metta.Unify.unifyRounds fuel equations subst = some result) :
    ∃ constraints, Metta.Unify.decomposeAll equations = some constraints := by
  cases fuel with
  | zero =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none => simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints => exact ⟨constraints, rfl⟩
  | succ fuel =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none => simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints => exact ⟨constraints, rfl⟩

private theorem varConstraint_mem_decomposeAll
    {equations : List (Metta.Atom × Metta.Atom)}
    {constraints : List (String × Metta.Atom)} {left right : String}
    (hne : left ≠ right)
    (hequation : (.var left, .var right) ∈ equations)
    (hdecompose : Metta.Unify.decomposeAll equations = some constraints) :
    (left, .var right) ∈ constraints := by
  induction equations generalizing constraints with
  | nil => simp at hequation
  | cons equation equations ih =>
      rcases equation with ⟨a, b⟩
      simp only [List.mem_cons] at hequation
      rcases hequation with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        cases hrest : Metta.Unify.decomposeAll equations <;>
          simp [Metta.Unify.decomposeAll, Metta.Unify.decomposeEq,
            hne, hrest] at hdecompose
        subst constraints
        simp
      · cases hfirst : Metta.Unify.decomposeEq a b with
        | none =>
            simp [Metta.Unify.decomposeAll, hfirst] at hdecompose
        | some firstConstraints =>
            cases hrest : Metta.Unify.decomposeAll equations with
            | none =>
                simp [Metta.Unify.decomposeAll, hfirst, hrest] at hdecompose
            | some restConstraints =>
                simp only [Metta.Unify.decomposeAll, hfirst, hrest,
                  Option.some.injEq] at hdecompose
                subst constraints
                exact List.mem_append_right _
                  (ih htail hrest)

private theorem mem_aliasConstraints_of_mem_var
    {constraints : List (String × Metta.Atom)} {left right : String}
    (hmem : (left, .var right) ∈ constraints) :
    (left, right) ∈ Metta.Unify.aliasConstraints constraints := by
  induction constraints with
  | nil => simp at hmem
  | cons constraint constraints ih =>
      rcases constraint with ⟨key, value⟩
      cases value with
      | var target =>
          simp only [List.mem_cons, Prod.mk.injEq,
            Metta.Atom.var.injEq] at hmem
          simp only [Metta.Unify.aliasConstraints, List.mem_cons,
            Prod.mk.injEq]
          exact hmem.imp id ih
      | sym symbol | gnd symbol | expr symbol =>
          simp only [List.mem_cons, Prod.mk.injEq] at hmem
          simp only [Metta.Unify.aliasConstraints]
          rcases hmem with hhead | htail
          · cases hhead.2
          · exact ih htail

private theorem aliasConstraints_mem_aliasTrace
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {constraints : List (String × Metta.Atom)} {edge : String × String}
    (hdecompose : Metta.Unify.decomposeAll equations = some constraints)
    (hmem : edge ∈ Metta.Unify.aliasConstraints constraints) :
    edge ∈ Metta.Unify.aliasTrace fuel equations := by
  cases fuel with
  | zero => simpa [Metta.Unify.aliasTrace, hdecompose] using hmem
  | succ fuel =>
      cases constraints with
      | nil => simp [Metta.Unify.aliasConstraints] at hmem
      | cons constraint constraints =>
          rcases constraint with ⟨key, term⟩
          cases hoccurs : Metta.Subst.occurs key term <;>
            simp [Metta.Unify.aliasTrace, hdecompose, hoccurs, hmem]

/-- A non-reflexive variable equation present in the initial worklist is
recorded by the successful run's alias trace before elimination can ground
either endpoint. -/
theorem varEquation_mem_aliasTrace_of_unifyRounds_success
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : String}
    (hrun : Metta.Unify.unifyRounds fuel equations subst = some result)
    (hne : left ≠ right)
    (hequation : (.var left, .var right) ∈ equations) :
    (left, right) ∈ Metta.Unify.aliasTrace fuel equations := by
  obtain ⟨constraints, hdecompose⟩ :=
    decomposeAll_some_of_unifyRounds_success hrun
  apply aliasConstraints_mem_aliasTrace hdecompose
  apply mem_aliasConstraints_of_mem_var
  exact varConstraint_mem_decomposeAll hne hequation hdecompose

/-- Every explicit equality edge in the reconciliation source is either
reflexive (hence graph-inert) or retained by `reconciliationAliases`. -/
theorem sourceEqualityEdge_eq_or_mem_reconciliationAliases
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    {left right : String}
    (hreconcile : wholeBindingReconciliation bindings extra = some result)
    (hmem : (left, right) ∈ leaEqualityEdges bindings) :
    left = right ∨
      (left, right) ∈
        Metta.Bindings.reconciliationAliases bindings extra result := by
  by_cases heq : left = right
  · exact Or.inl heq
  · right
    let equations := Metta.Bindings.equations bindings ++ extra
    have hrun :
        Metta.Unify.unifyRounds
          (Metta.Bindings.equationFuel equations) equations [] = some result := by
      simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll,
        equations] using hreconcile
    have hequation : (.var left, .var right) ∈ equations := by
      apply List.mem_append_left
      unfold Metta.Bindings.equations
      apply List.mem_map.mpr
      exact ⟨Metta.BindingRel.eq left right,
        mem_leaEqualityEdges_iff.mp hmem, rfl⟩
    have halias := varEquation_mem_aliasTrace_of_unifyRounds_success
      hrun heq hequation
    simpa [Metta.Bindings.reconciliationAliases, equations] using halias

private theorem reachable_append_of_eq_or_mem
    {extra edges : List (String × String)}
    (hsub : ∀ edge ∈ extra,
      edge.1 = edge.2 ∨ edge ∈ edges)
    (start finish : String) :
    (EqualityClosure.edgeGraph (extra ++ edges)).Reachable start finish ↔
      (EqualityClosure.edgeGraph edges).Reachable start finish := by
  constructor
  · intro hreach
    apply hreach.mono
    intro left right hadj
    rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
    rcases hadj with ⟨hne, hforward | hreverse⟩
    · rcases List.mem_append.mp hforward with hextra | hedge
      · rcases hsub (left, right) hextra with heq | hedge
        · exact (hne heq).elim
        · exact ⟨hne, Or.inl hedge⟩
      · exact ⟨hne, Or.inl hedge⟩
    · rcases List.mem_append.mp hreverse with hextra | hedge
      · rcases hsub (right, left) hextra with heq | hedge
        · exact (hne heq.symm).elim
        · exact ⟨hne, Or.inr hedge⟩
      · exact ⟨hne, Or.inr hedge⟩
  · intro hreach
    apply hreach.mono
    intro left right hadj
    rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
    rcases hadj with ⟨hne, hforward | hreverse⟩
    · exact ⟨hne, Or.inl (List.mem_append_right _ hforward)⟩
    · exact ⟨hne, Or.inr (List.mem_append_right _ hreverse)⟩

/-- The canonical two-certificate replay has exactly the equality closure
expected by `rebuildFromReconciliation`: explicit source edges add nothing
beyond the successful alias trace, except graph-inert reflexive edges. -/
theorem reconciliationReplay_structural_with_source_of_success
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    {mid out : Bindings}
    (hreconcile : wholeBindingReconciliation bindings extra = some result)
    (htrace : LeaEliminationTraceReplay Bindings.empty
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra)) mid)
    (haliases : LeaAliasTraceReplay mid
      (Metta.Bindings.reconciliationAliases bindings extra result) out) :
    (∀ start finish,
      finish ∈ out.eqClass start ↔
        (EqualityClosure.edgeGraph
          (leaEqualityEdges bindings ++
            Metta.Bindings.reconciliationAliases bindings extra result)).Reachable
          start finish) ∧
      LeaEliminationTraceClassValueRel out
        (unificationEliminationTrace
          (Metta.Bindings.equationFuel
            (Metta.Bindings.equations bindings ++ extra))
          (Metta.Bindings.equations bindings ++ extra)) := by
  obtain ⟨hclasses, hvalues⟩ :=
    reconciliationReplay_structural_of_success hreconcile htrace haliases
  constructor
  · intro start finish
    apply (hclasses start finish).trans
    symm
    apply reachable_append_of_eq_or_mem
    intro edge hedge
    rcases edge with ⟨left, right⟩
    exact sourceEqualityEdge_eq_or_mem_reconciliationAliases
      hreconcile hedge
  · exact hvalues

/-- Once the operational matcher/merge induction realizes the selected solve
trace and the full alias trace, all reconciliation obligations collapse to the
already-landed solution and rebuild theorems. -/
theorem rebuildFromReconciliation_congruence_of_replays
    {b heOut mid : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result)
    (hheTheory : ∀ valuation,
      HEBindingSatisfied valuation heOut ↔
        HEBindingSatisfied valuation b ∧
          MettaEquationsSatisfied valuation extra)
    (htrace : LeaEliminationTraceReplay Bindings.empty
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations source ++ extra))
        (Metta.Bindings.equations source ++ extra)) mid)
    (haliases : LeaAliasTraceReplay mid
      (Metta.Bindings.reconciliationAliases source extra result) heOut) :
    LeaBindingCongruence heOut
      (Metta.Bindings.rebuildFromReconciliation
        source source extra result) := by
  obtain ⟨hclasses, hvalues⟩ :=
    reconciliationReplay_structural_with_source_of_success
      hreconcile htrace haliases
  apply rebuildFromReconciliation_congruence_of_heTheory_classes_and_values
    hbase hsourceNoFloat hextraNoFloat hreconcile hheTheory hclasses
  exact (leaSubstClassValueRel_iff_eliminationTrace hreconcile).mpr hvalues

/-- Trace-facing strengthened reconciliation interface.  The operational
induction supplies class closure and the elimination-trace certificate; the
landed reconciliation results convert the latter to normalized-substitution
provenance and assemble full binding congruence. -/
theorem rebuildFromReconciliation_congruence_of_heTheory_classes_and_trace
    {b heOut : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result)
    (hheTheory : ∀ valuation,
      HEBindingSatisfied valuation heOut ↔
        HEBindingSatisfied valuation b ∧
          MettaEquationsSatisfied valuation extra)
    (hclasses : ∀ start finish,
      finish ∈ heOut.eqClass start ↔
        (EqualityClosure.edgeGraph
          (leaEqualityEdges source ++
            Metta.Bindings.reconciliationAliases source extra result)).Reachable
          start finish)
    (htrace : LeaEliminationTraceClassValueRel heOut
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations source ++ extra))
        (Metta.Bindings.equations source ++ extra))) :
    LeaBindingCongruence heOut
      (Metta.Bindings.rebuildFromReconciliation
        source source extra result) := by
  apply rebuildFromReconciliation_congruence_of_heTheory_classes_and_values
    hbase hsourceNoFloat hextraNoFloat hreconcile hheTheory hclasses
  exact (leaSubstClassValueRel_iff_eliminationTrace hreconcile).mpr htrace

/-- Quotient-level operational target for one successful reconciliation.
It records exactly the two fields that the mutual HE add/match/merge induction
must construct; equation-solution theory is supplied independently. -/
structure HEReconciliationTraceStructuralRel
    (heOut : Bindings) (source : Metta.Bindings)
    (extra : List (Metta.Atom × Metta.Atom))
    (result : Metta.Subst) : Prop where
  classes : ∀ start finish,
    finish ∈ heOut.eqClass start ↔
      (EqualityClosure.edgeGraph
        (leaEqualityEdges source ++
          Metta.Bindings.reconciliationAliases source extra result)).Reachable
        start finish
  classValues : LeaEliminationTraceClassValueRel heOut
    (unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations source ++ extra))
      (Metta.Bindings.equations source ++ extra))

/-- Successful reconciliation over translated equations constructs the full
executable witness package.  This is deliberately existential in the HE record
presentation; the later paired induction compares an independently produced
matcher result only through `structural`. -/
theorem exists_reconciliationExecutableWitness_of_congruence
    {b : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hextra : LeaEquationsInHEImage extra)
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    ∃ mid out,
      LeaEliminationTraceExecutableReplay Bindings.empty
          (unificationEliminationTrace
            (Metta.Bindings.equationFuel
              (Metta.Bindings.equations source ++ extra))
            (Metta.Bindings.equations source ++ extra)) mid ∧
        LeaAliasTraceReplay mid
          (Metta.Bindings.reconciliationAliases source extra result) out ∧
        HEReconciliationTraceStructuralRel out source extra result := by
  obtain ⟨mid, htrace⟩ :=
    exists_eliminationTraceExecutableReplay_of_congruence
      hbase hextra hreconcile
  obtain ⟨heOut, haliases⟩ :=
    exists_aliasTraceReplay mid
      (Metta.Bindings.reconciliationAliases source extra result)
  obtain ⟨hclasses, hvalues⟩ :=
    reconciliationReplay_structural_with_source_of_success
      hreconcile htrace.replay haliases
  exact ⟨mid, heOut, htrace, haliases, ⟨hclasses, hvalues⟩⟩

/-- Every successful reconciliation over translated equations admits a
canonical HE record with exactly the required quotient-level closure and
class-value provenance.  This is the constructive LeaTTa-to-HE witness model;
the remaining operational induction identifies an executable HE result with
these observations, not with its relation-list presentation. -/
theorem exists_reconciliationTraceStructuralRel_of_congruence
    {b : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hextra : LeaEquationsInHEImage extra)
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    ∃ heOut, HEReconciliationTraceStructuralRel
      heOut source extra result := by
  obtain ⟨mid, heOut, htrace, haliases, hstructural⟩ :=
    exists_reconciliationExecutableWitness_of_congruence
      hbase hextra hreconcile
  exact ⟨heOut, hstructural⟩

/-- The quotient-level operational certificate plus equation theory is the
full strengthened binding congruence required by recursive matching. -/
theorem HEReconciliationTraceStructuralRel.toCongruence
    {b heOut : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result)
    (hheTheory : ∀ valuation,
      HEBindingSatisfied valuation heOut ↔
        HEBindingSatisfied valuation b ∧
          MettaEquationsSatisfied valuation extra)
    (hstruct : HEReconciliationTraceStructuralRel
      heOut source extra result) :
    LeaBindingCongruence heOut
      (Metta.Bindings.rebuildFromReconciliation
        source source extra result) := by
  exact rebuildFromReconciliation_congruence_of_heTheory_classes_and_trace
    hbase hsourceNoFloat hextraNoFloat hreconcile hheTheory
      hstruct.classes hstruct.classValues

/-- Every successful translated reconciliation has a canonical HE witness
with full binding congruence, not merely the structural fields.  Its Robinson
trace is executed by the public empty-left merge surface; alias restoration is
then proved solution-neutral from the successful unifier certificate.  This
still deliberately does not identify the witness with an independent runtime
`addVarBinding`/`addVarEquality` result. -/
theorem exists_reconciliationExecutableCongruenceWitness_of_congruence
    {b : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextra : LeaEquationsInHEImage extra)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    ∃ mid out fuel,
      LeaEliminationTraceExecutableReplay Bindings.empty
          (unificationEliminationTrace
            (Metta.Bindings.equationFuel
              (Metta.Bindings.equations source ++ extra))
            (Metta.Bindings.equations source ++ extra)) mid ∧
        mid ∈ mergeBindings Bindings.empty mid fuel ∧
        LeaAliasTraceReplay mid
          (Metta.Bindings.reconciliationAliases source extra result) out ∧
        LeaBindingCongruence out
          (Metta.Bindings.rebuildFromReconciliation
            source source extra result) := by
  obtain ⟨mid, out, htrace, haliases, hstruct⟩ :=
    exists_reconciliationExecutableWitness_of_congruence
      hbase hextra hreconcile
  obtain ⟨fuel, hmerge⟩ :=
    htrace.replay.mem_mergeBindings_empty_left
      (wholeBindingReconciliation_eliminationTrace_triangular hreconcile)
  refine ⟨mid, out, fuel, htrace, hmerge, haliases, ?_⟩
  apply hstruct.toCongruence hbase hsourceNoFloat hextraNoFloat hreconcile
  intro valuation
  have hmidTrace := htrace.replay.satisfaction_iff valuation
  have hresultEq :=
    wholeBindingReconciliation_result_eq_eliminationTrace_reverse hreconcile
  have hmidResult :
      HEBindingSatisfied valuation mid ↔
        MettaConstraintsSatisfied valuation result := by
    rw [hresultEq]
    exact hmidTrace.trans
      (mettaConstraintsSatisfied_reverse valuation _).symm
  have houtMid :
      HEBindingSatisfied valuation out ↔
        HEBindingSatisfied valuation mid :=
    haliases.satisfaction_iff_of_constraints hmidResult (by
      intro hresult edge hedge
      exact wholeBindingReconciliation_aliases_satisfied valuation
        hsourceNoFloat hextraNoFloat hreconcile hresult edge hedge)
  calc
    HEBindingSatisfied valuation out ↔
        HEBindingSatisfied valuation mid := houtMid
    _ ↔ MettaConstraintsSatisfied valuation result := hmidResult
    _ ↔ LeaBindingSatisfied valuation source ∧
          MettaEquationsSatisfied valuation extra :=
      wholeBindingReconciliation_solution_iff valuation
        hsourceNoFloat hextraNoFloat hreconcile
    _ ↔ HEBindingSatisfied valuation b ∧
          MettaEquationsSatisfied valuation extra :=
      and_congr (hbase.semantic.solutions valuation).symm Iff.rfl

/-- A successful repaired-LeaTTa reconciliation has one canonical HE witness
that is operational at both public surfaces used by recursive matching: its
selected solve constraints are emitted by `matchAtomsList`, and the same
binding record is emitted by empty-left `mergeBindings`.  Replaying the full
alias certificate then yields full congruence with the repaired rebuild.
Only equality-class-relative correspondence is asserted for right-hand trace
terms; no matcher MGU or representative presentation is identified. -/
theorem exists_reconciliationMatcherListCongruenceWitness_of_congruence
    {b : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextra : LeaEquationsInHEImage extra)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    ∃ left right mid out matchFuel mergeFuel,
      left =
          (unificationEliminationTrace
            (Metta.Bindings.equationFuel
              (Metta.Bindings.equations source ++ extra))
            (Metta.Bindings.equations source ++ extra)).reverse.map
              (fun entry => Atom.var entry.1) ∧
        List.Forall₂ (HELeaAtomClassRel mid) right
          ((unificationEliminationTrace
            (Metta.Bindings.equationFuel
              (Metta.Bindings.equations source ++ extra))
            (Metta.Bindings.equations source ++ extra)).reverse.map
              Prod.snd) ∧
        mid ∈ matchAtomsList left right [Bindings.empty] matchFuel ∧
        mid ∈ mergeBindings Bindings.empty mid mergeFuel ∧
        LeaAliasTraceReplay mid
          (Metta.Bindings.reconciliationAliases source extra result) out ∧
        LeaBindingCongruence out
          (Metta.Bindings.rebuildFromReconciliation
            source source extra result) := by
  obtain ⟨mid, out, mergeFuel, htrace, hmerge, haliases, hcongruence⟩ :=
    exists_reconciliationExecutableCongruenceWitness_of_congruence
      hbase hsourceNoFloat hextra hextraNoFloat hreconcile
  obtain ⟨left, right, matchFuel, hleft, hright, hmatch⟩ :=
    htrace.exists_mem_matchAtomsList_reverse
  exact ⟨left, right, mid, out, matchFuel, mergeFuel,
    hleft, hright, hmatch, hmerge, haliases, hcongruence⟩

/-- Matcher-origin package for a complete repaired-LeaTTa reconciliation.
The matcher inputs are the canonical expression presentation of the selected
Robinson constraints, not a claimed reconstruction of an independent MGU. -/
structure HEReconciliationMatcherCongruenceWitness
    (source : Metta.Bindings)
    (extra : List (Metta.Atom × Metta.Atom))
    (result : Metta.Subst) where
  left : List Atom
  right : List Atom
  mid : Bindings
  out : Bindings
  matchFuel : Nat
  mergeFuel : Nat
  left_eq : left =
    (unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations source ++ extra))
      (Metta.Bindings.equations source ++ extra)).reverse.map
        (fun entry => Atom.var entry.1)
  right_rel : List.Forall₂ (HELeaAtomClassRel mid) right
    ((unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations source ++ extra))
      (Metta.Bindings.equations source ++ extra)).reverse.map Prod.snd)
  match_mem : mid ∈
    matchAtoms (.expression left) (.expression right) matchFuel
  matchTraceSound : MatchTraceSound
    (unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations source ++ extra))
      (Metta.Bindings.equations source ++ extra))
    (DeclMatchSpec.matchAtoms_sound match_mem)
  merge_mem : mid ∈ mergeBindings Bindings.empty mid mergeFuel
  mergeTraceSound : MergeTraceSound
    (unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations source ++ extra))
      (Metta.Bindings.equations source ++ extra))
    (mergeBindings_sound merge_mem)
  chain : HEMatcherMergeChain Bindings.empty mid
  traceStructural : LeaEliminationTraceStructuralRel mid
    (unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations source ++ extra))
      (Metta.Bindings.equations source ++ extra))
  midEqualityClosureBound : HEEqualityClosureBound mid
    (Metta.Bindings.reconciliationAliases source extra result)
  midResultCongruence : LeaBindingCongruence mid
    (Metta.Bindings.ofSubst result)
  aliases : LeaAliasTraceReplay mid
    (Metta.Bindings.reconciliationAliases source extra result) out
  congruence : LeaBindingCongruence out
    (Metta.Bindings.rebuildFromReconciliation
      source source extra result)

/-- Every successful translated whole-binding reconciliation constructs the
full matcher-origin package above. -/
theorem exists_reconciliationMatcherCongruenceWitness_of_congruence
    {b : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextra : LeaEquationsInHEImage extra)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    Nonempty (HEReconciliationMatcherCongruenceWitness
      source extra result) := by
  obtain ⟨mid, out, mergeFuel, htrace, hmerge, haliases, hcongruence⟩ :=
    exists_reconciliationExecutableCongruenceWitness_of_congruence
      hbase hsourceNoFloat hextra hextraNoFloat hreconcile
  have htriangular :=
    wholeBindingReconciliation_eliminationTrace_triangular hreconcile
  obtain ⟨left, right, matchFuel, hmatch, hleft, hright,
      hmatchTraceSound⟩ :=
    htrace.exists_mem_matchAtoms_expression_reverse_traceSound_for
      htriangular
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations source ++ extra))
        (Metta.Bindings.equations source ++ extra))
  have hmidResultCongruence : LeaBindingCongruence mid
      (Metta.Bindings.ofSubst result) := by
    rw [wholeBindingReconciliation_result_eq_eliminationTrace_reverse
      hreconcile]
    exact htrace.replay.congruence_ofSubst_reverse
  have hmergeTraceSound : MergeTraceSound
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations source ++ extra))
        (Metta.Bindings.equations source ++ extra))
      (mergeBindings_sound hmerge) := by
    simpa only [Subsingleton.elim (mergeBindings_sound hmerge)
      (htrace.replay.mergeRel_empty_left
        htriangular)] using
      htrace.replay.mergeTraceSound_empty_left
        htriangular
  exact ⟨{
    left := left
    right := right
    mid := mid
    out := out
    matchFuel := matchFuel
    mergeFuel := mergeFuel
    left_eq := hleft
    right_rel := hright
    match_mem := hmatch
    matchTraceSound := hmatchTraceSound
    merge_mem := hmerge
    mergeTraceSound := hmergeTraceSound
    chain := .cons hmatch hmerge (.nil mid)
    traceStructural := htrace.replay.structural
    midEqualityClosureBound := htrace.replay.equalityClosureBound
      (eliminationTraceAliases_subset_reconciliationAliases hreconcile)
    midResultCongruence := hmidResultCongruence
    aliases := haliases
    congruence := hcongruence
  }⟩

/-- The final live alias merge is fully congruent to repaired LeaTTa once its
concrete merge derivation carries both local certificates: trace provenance
for recursive matcher assignments and an equality-closure upper bound for
recursive matcher aliases.  Solution theory remains an independent premise
and is supplied by the HE/LeaTTa solution characterizations. -/
theorem HEReconciliationMatcherCongruenceWitness.liveAliasMergeCongruence
    {b : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (w : HEReconciliationMatcherCongruenceWitness source extra result)
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result)
    {aliasRecord merged : Bindings} {mergeFuel : Nat}
    (halias : LeaAliasTraceReplay Bindings.empty
      (Metta.Bindings.reconciliationAliases source extra result)
      aliasRecord)
    (hmerge : merged ∈ mergeBindings w.mid aliasRecord mergeFuel)
    (htraceSound : MergeTraceSound
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations source ++ extra))
        (Metta.Bindings.equations source ++ extra))
      (mergeBindings_sound hmerge))
    (hboundSound : MergeEqualityClosureBoundSound
      (Metta.Bindings.reconciliationAliases source extra result)
      (mergeBindings_sound hmerge))
    (hheTheory : ∀ valuation,
      HEBindingSatisfied valuation merged ↔
        HEBindingSatisfied valuation b ∧
          MettaEquationsSatisfied valuation extra) :
    LeaBindingCongruence merged
      (Metta.Bindings.rebuildFromReconciliation
        source source extra result) := by
  let trace := unificationEliminationTrace
    (Metta.Bindings.equationFuel
      (Metta.Bindings.equations source ++ extra))
    (Metta.Bindings.equations source ++ extra)
  have haliasAssignments :
      LeaEliminationTraceAssignmentsSound aliasRecord trace := by
    intro key value hmem
    rw [halias.assignments] at hmem
    simp [Bindings.empty] at hmem
  have hmergedStructural :
      LeaEliminationTraceStructuralRel merged trace := by
    apply mergeBindings_eliminationTraceStructural_of_traceSound
      hmerge htraceSound w.traceStructural haliasAssignments
  have hclassesAliases : ∀ start finish,
      finish ∈ merged.eqClass start ↔
        (EqualityClosure.edgeGraph
          (Metta.Bindings.reconciliationAliases source extra result)).Reachable
            start finish := by
    intro start finish
    exact mergeBindings_eqClass_iff_aliases_of_boundSound
      hmerge hboundSound w.midEqualityClosureBound halias start finish
  have hclasses : ∀ start finish,
      finish ∈ merged.eqClass start ↔
        (EqualityClosure.edgeGraph
          (leaEqualityEdges source ++
            Metta.Bindings.reconciliationAliases source extra result)).Reachable
              start finish := by
    intro start finish
    apply (hclassesAliases start finish).trans
    symm
    apply reachable_append_of_eq_or_mem
    intro edge hedge
    rcases edge with ⟨left, right⟩
    exact sourceEqualityEdge_eq_or_mem_reconciliationAliases
      hreconcile hedge
  apply HEReconciliationTraceStructuralRel.toCongruence
    hbase hsourceNoFloat hextraNoFloat hreconcile hheTheory
  exact ⟨hclasses, hmergedStructural.classValues⟩

/-- The alias-restoration half of a successful reconciliation is a genuine
live HE matcher merge as soon as the isolated satisfiable matcher-result
merge theorem is available.  The returned merge has exactly the repaired
rebuild's solution theory: alias restoration adds equations already certified
by the successful Robinson run.  Thus the remaining mutual proof need not
compare normalization order or replay aliases as raw record updates. -/
theorem HEReconciliationMatcherCongruenceWitness.exists_liveAliasMerge
    (hmergeComplete : HESatisfiedMatcherMergeRelComplete)
    {b : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (w : HEReconciliationMatcherCongruenceWitness source extra result)
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    ∃ aliasRecord merged left right matchFuel mergeFuel,
      LeaAliasTraceReplay Bindings.empty
          (Metta.Bindings.reconciliationAliases source extra result)
          aliasRecord ∧
        aliasRecord ∈
          matchAtoms (.expression left) (.expression right) matchFuel ∧
        merged ∈ mergeBindings w.mid aliasRecord mergeFuel ∧
        HEMatcherMergeChain w.mid merged ∧
        HEAssignmentsNonVariable merged ∧
        LeaBindingSolutionTheoryEquiv merged
          (Metta.Bindings.rebuildFromReconciliation
            source source extra result) := by
  let aliases :=
    Metta.Bindings.reconciliationAliases source extra result
  obtain ⟨aliasRecord, hrecord⟩ :=
    exists_aliasTraceReplay Bindings.empty aliases
  obtain ⟨left, right, matchFuel, _hleft, _hright, hmatch⟩ :=
    hrecord.exists_mem_matchAtoms_expression_reverse
  obtain ⟨valuation, hresult⟩ :=
    exists_wholeBindingReconciliation_result_satisfied hreconcile
  have hmidSatisfied : HEBindingSatisfied valuation w.mid := by
    apply (w.midResultCongruence.semantic.solutions valuation).mpr
    exact (leaOfSubst_solution_iff valuation result).mpr hresult
  have haliasRecordSatisfied :
      HEBindingSatisfied valuation aliasRecord := by
    apply (hrecord.satisfaction_iff valuation).mpr
    intro edge hedge
    exact wholeBindingReconciliation_aliases_satisfied valuation
      hsourceNoFloat hextraNoFloat hreconcile hresult edge (by
        simpa [aliases] using hedge)
  obtain ⟨merged, hmergeRel, hmergedNonVariable⟩ :=
    hmergeComplete (DeclMatchSpec.matchAtoms_sound hmatch)
      hmidSatisfied
      (heAssignmentsNonVariable_of_matchAtoms w.match_mem)
      haliasRecordSatisfied
  obtain ⟨mergeFuel, hmerge⟩ :=
    mergeBindings_complete hmergeRel
  have hmergedTheory : ∀ solution,
      HEBindingSatisfied solution merged ↔
        HEBindingSatisfied solution b ∧
          MettaEquationsSatisfied solution extra := by
    intro solution
    rw [mergeBindings_solution_iff hmerge solution]
    constructor
    · rintro ⟨hmid, _haliasRecord⟩
      have hresultSolution : MettaConstraintsSatisfied solution result :=
        (leaOfSubst_solution_iff solution result).mp
          ((w.midResultCongruence.semantic.solutions solution).mp hmid)
      have hsourceExtra :=
        (wholeBindingReconciliation_solution_iff solution
          hsourceNoFloat hextraNoFloat hreconcile).mp hresultSolution
      exact ⟨(hbase.semantic.solutions solution).mpr hsourceExtra.1,
        hsourceExtra.2⟩
    · rintro ⟨hb, hextra⟩
      have hsource : LeaBindingSatisfied solution source :=
        (hbase.semantic.solutions solution).mp hb
      have hresultSolution : MettaConstraintsSatisfied solution result :=
        (wholeBindingReconciliation_solution_iff solution
          hsourceNoFloat hextraNoFloat hreconcile).mpr ⟨hsource, hextra⟩
      have hmid : HEBindingSatisfied solution w.mid :=
        (w.midResultCongruence.semantic.solutions solution).mpr
          ((leaOfSubst_solution_iff solution result).mpr hresultSolution)
      have haliasRecord : HEBindingSatisfied solution aliasRecord := by
        apply (hrecord.satisfaction_iff solution).mpr
        intro edge hedge
        exact wholeBindingReconciliation_aliases_satisfied solution
          hsourceNoFloat hextraNoFloat hreconcile hresultSolution edge (by
            simpa [aliases] using hedge)
      exact ⟨hmid, haliasRecord⟩
  have hsolutionTheory : LeaBindingSolutionTheoryEquiv merged
      (Metta.Bindings.rebuildFromReconciliation
        source source extra result) :=
    rebuildFromReconciliation_solutionTheory_of_heTheory
      hbase.semantic.solutions hsourceNoFloat hextraNoFloat
        hreconcile hmergedTheory
  exact ⟨aliasRecord, merged, left, right, matchFuel, mergeFuel,
    hrecord, hmatch, hmerge,
    .cons hmatch hmerge (.nil merged), hmergedNonVariable,
    hsolutionTheory⟩

/-- For a successful HE value insertion, the HE solution-theory module
discharges the extensional field automatically.  The reverse operational
induction therefore has only to construct `HEReconciliationTraceStructuralRel`. -/
theorem addVarBinding_reconciliation_congruence_of_structural
    {b heOut : Bindings} {source : Metta.Bindings}
    {key : String} {value : Atom} {fuel : Nat} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hHE : heOut ∈ addVarBinding b key value fuel)
    (hreconcile : wholeBindingReconciliation source
      [(.var key, toLeaTTaAtom value)] = some result)
    (hstruct : HEReconciliationTraceStructuralRel heOut source
      [(.var key, toLeaTTaAtom value)] result) :
    LeaBindingCongruence heOut
      (Metta.Bindings.rebuildFromReconciliation source source
        [(.var key, toLeaTTaAtom value)] result) := by
  apply hstruct.toCongruence hbase hsourceNoFloat
    (hreconcile := hreconcile)
  · intro equation hmem
    simp only [List.mem_singleton] at hmem
    subst equation
    exact ⟨by simp [MettaAtomNoFloat], toLeaTTaAtom_noFloat value⟩
  · intro valuation
    rw [addVarBinding_solution_iff hHE valuation]
    simp [MettaEquationsSatisfied, MettaEquationSatisfied,
      applyClassSolution]

/-! ## Replay oracles -/

/-- POSITIVE: the original expression matcher records fresh child
assignments in pointwise traversal order. -/
theorem originalExpressionMatch_readout :
    matchAtoms (.expression [.var "x", .var "y"])
        (.expression [.symbol "a", .symbol "b"]) 10 =
      [({ assignments := [("x", .symbol "a"), ("y", .symbol "b")],
           equalities := [] } : Bindings)] := by
  decide

/-- POSITIVE: the canonical reversed-constraint expression matcher records
the same solved equations in the reversed Robinson-substitution order. -/
theorem reversedConstraintExpressionMatch_readout :
    matchAtoms (.expression [.var "y", .var "x"])
        (.expression [.symbol "b", .symbol "a"]) 10 =
      [({ assignments := [("y", .symbol "b"), ("x", .symbol "a")],
           equalities := [] } : Bindings)] := by
  decide

/-- NEGATIVE: a canonical reversed-constraint matcher result cannot be
substituted for the original atom match by record equality.  Their solution
theories agree, but operational traversal orders their assignment lists
differently.  The strict-prefix proof must therefore construct the original
`MatchRel` and compare only through `LeaBindingCongruence`. -/
theorem originalExpressionMatch_ne_reversedConstraintMatch :
    matchAtoms (.expression [.var "x", .var "y"])
        (.expression [.symbol "a", .symbol "b"]) 10 ≠
      matchAtoms (.expression [.var "y", .var "x"])
        (.expression [.symbol "b", .symbol "a"]) 10 := by
  decide

/-- POSITIVE: a singleton HE alias lies inside the identical quotient-level
allowed graph. -/
theorem equalityClosureBound_single_alias :
    HEEqualityClosureBound
      (⟨[], [("x", "y")]⟩ : Bindings) [("x", "y")] := by
  apply HEEqualityClosureBound.of_edges
  intro edge hmem
  simp only [List.mem_singleton] at hmem
  subst edge
  exact (show
    (EqualityClosure.edgeGraph [("x", "y")]).Adj "x" "y" by
      rw [EqualityClosure.edgeGraph_adj_iff]
      simp).reachable

/-- NEGATIVE: a non-reflexive live alias cannot be certified against an
empty allowed graph. -/
theorem equalityClosureBound_extra_alias_rejected :
    ¬ HEEqualityClosureBound
      (⟨[], [("x", "y")]⟩ : Bindings) [] := by
  intro hbound
  have hclass : "y" ∈
      ((⟨[], [("x", "y")]⟩ : Bindings).eqClass "x") := by
    rw [EqualityClosure.mem_eqClass_iff_reachable]
    exact (show
      (EqualityClosure.edgeGraph [("x", "y")]).Adj "x" "y" by
        rw [EqualityClosure.edgeGraph_adj_iff]
        simp).reachable
  have hreach := hbound "x" "y" hclass
  have emptyReach_eq : ∀ {start finish : String},
      (EqualityClosure.edgeGraph []).Reachable start finish →
        start = finish := by
    intro start finish h
    apply h.elim
    intro walk
    induction walk with
    | nil => rfl
    | cons hadj tail ih =>
        rw [EqualityClosure.edgeGraph_adj_iff] at hadj
        simp at hadj
  have heq : "x" = "y" := emptyReach_eq hreach
  simp at heq

/-- POSITIVE: ordinary HE grounded payloads lie in the exact translation
image used by reconciliation replay. -/
theorem leaAtomInHEImage_integer :
    LeaAtomInHEImage (.gnd (.int 7)) :=
  ⟨.grounded (.int 7), rfl⟩

/-- NEGATIVE: LeaTTa's host-only unit payload is float-free but is not in the
HE atom image.  This distinguishes the exact source invariant from the older
`MettaAtomNoFloat` approximation. -/
theorem leaAtomInHEImage_unit_rejected :
    ¬ LeaAtomInHEImage (.gnd .unit) := by
  rintro ⟨atom, hatom⟩
  cases atom with
  | symbol name | var name | expression name => cases hatom
  | grounded value =>
      exact toLeaTTaGround_ne_unit value
        (Metta.Atom.gnd.inj hatom)

/-- POSITIVE: internal recursive matching accepts the reflexive-variable leaf
without requiring standardized-apart variables, while preserving congruence
between HE's reflexive edge and LeaTTa's empty presentation. -/
theorem reflexiveVariable_internalLeaf_realization :
    LeaMatcherCongruenceRealization (.var "x") (.var "x") [] := by
  apply leaMatchAtoms_leaf_congruence_realization_internal
  · simp [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom]
  · simp [BothExpressions]

/-- NEGATIVE: a seed carrying a bare variable assignment is outside the
operational invariant used by recursive matcher merge-back. -/
theorem bareVariableAssignment_rejected :
    ¬ HEAssignmentsNonVariable
      (Bindings.empty.assign "x" (.var "y")) := by
  intro h
  apply h "x" "y"
  simp [Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup]

/-- POSITIVE: one translated non-variable constraint replays as the matching
fresh HE assignment. -/
theorem eliminationTraceReplay_single_value :
    LeaEliminationTraceReplay Bindings.empty
      [("x", .sym "a")]
      (Bindings.empty.assign "x" (.symbol "a")) := by
  apply LeaEliminationTraceReplay.valueStep
    (LeaEliminationTraceReplay.nil (base := Bindings.empty))
  · rfl
  · exact .symbol "a"
  · intro target h
    cases h

/-- POSITIVE: the singleton replay quotient bridge agrees with repaired
LeaTTa's concrete `ofSubst` value presentation. -/
theorem eliminationTraceReplay_single_value_congruence :
    LeaBindingCongruence
      (Bindings.empty.assign "x" (.symbol "a"))
      [Metta.BindingRel.val "x" (.sym "a")] := by
  simpa [Metta.Bindings.ofSubst] using
    eliminationTraceReplay_single_value.congruence_ofSubst_reverse

/-- NEGATIVE: no canonical solve-trace replay can produce an HE bare-variable
assignment; variable constraints must remain equality edges. -/
theorem eliminationTraceReplay_bareVariableAssignment_rejected :
    ¬ ∃ trace, LeaEliminationTraceReplay Bindings.empty trace
      (Bindings.empty.assign "x" (.var "y")) := by
  rintro ⟨trace, hreplay⟩
  apply hreplay.assignmentsNonVariable "x" "y"
  simp [Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup]

/-- POSITIVE: replay discharges the singleton trace obligation completely. -/
theorem pendingEliminationTraceEntries_single_value_replay_empty :
    pendingEliminationTraceEntries
      (Bindings.empty.assign "x" (.symbol "a")) [("x", .sym "a")] = ∅ :=
  eliminationTraceReplay_single_value.structural.pending_eq_empty

/-- NEGATIVE: before replay, the same non-variable trace obligation remains
pending in empty HE bindings. -/
theorem pendingEliminationTraceEntries_single_value_empty_nonempty :
    pendingEliminationTraceEntries Bindings.empty [("x", .sym "a")] ≠ ∅ := by
  intro hempty
  have hrealized :=
    (pendingEliminationTraceEntries_eq_empty_iff
      Bindings.empty [("x", .sym "a")]).mp hempty
      ("x", .sym "a") (by simp)
  simp [LeaEliminationTraceEntryRealized, Bindings.empty] at hrealized

/-- POSITIVE: the singleton replay is returned by the real HE value-insertion
operation, not only by the low-level binding constructor. -/
theorem eliminationTraceExecutableReplay_single_value :
    LeaEliminationTraceExecutableReplay Bindings.empty
      [("x", .sym "a")]
      (Bindings.empty.assign "x" (.symbol "a")) := by
  apply eliminationTraceReplay_single_value.executable_of_triangular
  simp [EliminationTraceTriangular, mettaConstraintVars]

/-- NEGATIVE: a solve trace cannot replay two non-variable assignments at the
same key; `UnifyStateFresh` rules out precisely this shape. -/
theorem eliminationTraceReplay_repeated_key_rejected :
    ¬ ∃ out, LeaEliminationTraceReplay Bindings.empty
      [("x", .sym "b"), ("x", .sym "a")] out := by
  rintro ⟨out, h⟩
  cases h with
  | valueStep htail hlookup hatom hnonvar =>
      cases htail with
      | valueStep hnil _ _ _ =>
          cases hnil
          simp [Bindings.empty, Bindings.assign, Bindings.lookup,
            Bindings.isBound] at hlookup

/-- POSITIVE: a valueless alias is wholly in the nonrecursive, executable
alias-restoration lane. -/
theorem valuelessAlias_consistentReplay :
    LeaAliasTraceConsistentReplay Bindings.empty [("x", "y")]
      (Bindings.empty.addEquality "x" "y") := by
  apply LeaAliasTraceConsistentReplay.cons
    LeaAliasTraceConsistentReplay.nil
  rfl

/-- A minimal value-bearing record whose alias join genuinely requires the
recursive conflict lane. -/
def inconsistentAliasReplaySeed : Bindings :=
  ⟨[("x", .symbol "a"), ("y", .symbol "b")], []⟩

/-- NEGATIVE: unequal class values cannot be mislabeled as a consistent alias
replay; they remain obligations for recursive matching. -/
theorem inconsistentAlias_not_consistentReplay :
    ¬ ∃ out, LeaAliasTraceConsistentReplay inconsistentAliasReplaySeed
      [("x", "y")] out := by
  rintro ⟨out, h⟩
  cases h with
  | cons htail hconsistent =>
      cases htail
      simp [inconsistentAliasReplaySeed, Bindings.addEquality,
        Bindings.classValues, Bindings.eqClassOrdered,
        Bindings.eqVarsInOrder, Bindings.eqClass, Bindings.eqClassAux,
        Bindings.eqStep, Bindings.lookup, List.lookup,
        Bindings.valuesConsistent] at hconsistent

/-- POSITIVE: a fresh grounded assignment has literal translated provenance
in its singleton Robinson trace. -/
theorem eliminationTraceAssignmentsExact_single_value :
    LeaEliminationTraceAssignmentsExact
      (Bindings.empty.assign "x" (.symbol "a")) [("x", .sym "a")] := by
  intro key value hmem
  simp [Bindings.empty, Bindings.assign, Bindings.isBound,
    Bindings.lookup] at hmem
  rcases hmem with ⟨rfl, rfl⟩
  simp [DeclMatchSpec.Atom.isVarB, toLeaTTaAtom]

/-- NEGATIVE: literal trace provenance rejects the bare-variable assignment
shape that repaired matching represents as an equality edge. -/
theorem eliminationTraceAssignmentsExact_bareVariable_rejected :
    ¬ LeaEliminationTraceAssignmentsExact
      (Bindings.empty.assign "x" (.var "y")) [("x", .var "y")] := by
  intro h
  have hbad := h "x" (.var "y") (by
    simp [Bindings.empty, Bindings.assign, Bindings.isBound,
      Bindings.lookup])
  simp [DeclMatchSpec.Atom.isVarB] at hbad

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
