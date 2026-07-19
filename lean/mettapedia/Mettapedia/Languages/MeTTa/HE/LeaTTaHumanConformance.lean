import Mettapedia.Languages.MeTTa.HE.HumanMatchMergeSpec
import Mettapedia.Languages.MeTTa.HE.HumanMatchSolutionTheory
import Mettapedia.Languages.MeTTa.HE.HumanMatchModelTheory
import Mettapedia.Languages.MeTTa.HE.HumanMatchLPBridge
import Mettapedia.Languages.MeTTa.HE.HumanMatchStructuralModel
import Mettapedia.Languages.MeTTa.HE.LeaTTaMergeExistence
import Mettapedia.Languages.MeTTa.HE.LeaTTaMatcherCongruence

/-!
# Direct repaired-LeaTTa conformance to the human HE matcher/merge relation

The theorems in this file relate repaired LeaTTa directly to
`HumanMatchMergeSpec`.  Membership in the executable HE matcher or merger is
not a premise or a conclusion of the conformance statements.  Compatibility
with the older HE executable model remains a separate validation layer.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaHumanConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaMergeExistence
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Direct semantic attachment -/

/-- Once a direct structural proof supplies equality-class closure and raw
class-value provenance, successful human and repaired-LeaTTa matches supply
the complete solution field automatically.  Thus the remaining compound
induction never has to compare representative choice, list order, or MGU
presentation. -/
theorem humanMatch_leaMatch_congruence_of_structural
    {query pattern : Atom} {humanOut : Bindings}
    {leaOut : Metta.Bindings}
    (hhuman : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      query pattern humanOut)
    (hlea : leaOut ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hstruct : LeaBindingStructuralCongruence humanOut leaOut) :
    LeaBindingCongruence humanOut leaOut :=
  hstruct.withSolutions
    (HumanMatchSolutionTheory.humanMatch_leaMatch_solutionTheoryEquiv
      hhuman hlea)

/-! ## Leaf fragment: declarative completeness -/

private theorem mem_toLeaTTaAtoms_of_mem {atoms : List Atom} {atom : Atom}
    (hmem : atom ∈ atoms) :
    toLeaTTaAtom atom ∈ toLeaTTaAtoms atoms := by
  induction atoms with
  | nil => cases hmem
  | cons head tail ih =>
      simp only [toLeaTTaAtoms, List.mem_cons] at hmem ⊢
      exact hmem.elim (fun heq => Or.inl (congrArg toLeaTTaAtom heq))
        (fun htail => Or.inr (ih htail))

/-- The neutral occurrence relation agrees with variable membership after the
structural HE-to-LeaTTa atom translation. -/
theorem mem_translated_vars_of_atomOccurs {atom : Atom} {name : String}
    (hoccurs : HumanMatchMergeSpec.AtomOccurs atom name) :
    name ∈ (toLeaTTaAtom atom).vars := by
  induction hoccurs with
  | var => simp [toLeaTTaAtom, Metta.Atom.vars]
  | @expression atoms atom name hmem _ ih =>
      simp only [toLeaTTaAtom, Metta.Atom.vars, List.mem_flatten]
      refine ⟨(toLeaTTaAtom atom).vars, ?_, ih⟩
      exact List.mem_map.mpr
        ⟨toLeaTTaAtom atom, mem_toLeaTTaAtoms_of_mem hmem, rfl⟩

/-- Variable support of the translated atom is exactly the neutral occurrence
relation used by the human specification.  The reverse direction is needed
to turn the semantic loop filter into the ordinary occurs-check condition. -/
theorem atomOccurs_of_mem_translated_vars {atom : Atom} {name : String}
    (hmem : name ∈ (toLeaTTaAtom atom).vars) :
    HumanMatchMergeSpec.AtomOccurs atom name := by
  let AtomGoal : Atom → Prop := fun candidate => ∀ name',
    name' ∈ (toLeaTTaAtom candidate).vars →
      HumanMatchMergeSpec.AtomOccurs candidate name'
  let ListGoal : List Atom → Prop := fun candidates => ∀ name',
    name' ∈ ((toLeaTTaAtoms candidates).map Metta.Atom.vars).flatten →
      ∃ candidate ∈ candidates,
        HumanMatchMergeSpec.AtomOccurs candidate name'
  have hrec : ∀ candidate, AtomGoal candidate := by
    apply Atom.rec (motive_1 := AtomGoal) (motive_2 := ListGoal)
    · intro symbol name' h
      simp [toLeaTTaAtom, Metta.Atom.vars] at h
    · intro candidate name' h
      have heq : name' = candidate := by
        simpa [toLeaTTaAtom, Metta.Atom.vars] using h
      subst name'
      exact .var candidate
    · intro grounded name' h
      simp [toLeaTTaAtom, Metta.Atom.vars] at h
    · intro candidates ih name' h
      obtain ⟨candidate, hcandidate, hoccurs⟩ := ih name' (by
        simpa [toLeaTTaAtom, Metta.Atom.vars] using h)
      exact .expression hcandidate hoccurs
    · intro name' h
      simp [toLeaTTaAtoms] at h
    · intro candidate candidates ihCandidate ihCandidates name' h
      simp only [toLeaTTaAtoms, List.map_cons, List.flatten_cons,
        List.mem_append] at h
      rcases h with hhead | htail
      · exact ⟨candidate, by simp, ihCandidate name' hhead⟩
      · obtain ⟨found, hfound, hoccurs⟩ :=
          ihCandidates name' htail
        exact ⟨found, by simp [hfound], hoccurs⟩
  exact hrec atom name hmem

/-- A non-variable singleton assignment admitted by the human loop policy
cannot contain its own key.  Otherwise that assignment itself is a one-edge
cycle in the class dependency graph. -/
theorem not_atomOccurs_self_of_single_assignment_semanticLoopFree
    {key : String} {value : Atom}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree
      (Bindings.empty.assign key value)) :
    ¬HumanMatchMergeSpec.AtomOccurs value key := by
  intro hoccurs
  have hnonalias : ¬(value = .var key ∧ key ≠ key ∧
      key ∈ (Bindings.empty.assign key value).eqClass key) := by
    intro h
    exact h.2.1 rfl
  have hdepends : HumanMatchMergeSpec.ClassDepends
      (Bindings.empty.assign key value) key key := by
    refine ⟨key, value, key, ?_, ?_, hoccurs, ?_, hnonalias⟩
    · simp [Bindings.empty, Bindings.assign, Bindings.isBound,
        Bindings.lookup]
    · simp [Bindings.empty, Bindings.assign, Bindings.isBound,
        Bindings.lookup, Bindings.eqClass, Bindings.eqClassAux,
          Bindings.eqStep]
    · simp [Bindings.empty, Bindings.assign, Bindings.isBound,
        Bindings.lookup, Bindings.eqClass, Bindings.eqClassAux,
          Bindings.eqStep]
  exact hloopFree key (.single hdepends)

private theorem applyClassSolution_update_of_not_mem_vars_direct
    (valuation : String → Metta.Atom) (key : String)
    (replacement : Metta.Atom) :
    ∀ atom : Metta.Atom, key ∉ atom.vars →
      applyClassSolution (Function.update valuation key replacement) atom =
        applyClassSolution valuation atom := by
  intro atom
  induction atom with
  | sym symbol => intro _; simp [applyClassSolution]
  | var name =>
      intro hnotmem
      have hne : name ≠ key := by
        intro heq
        subst name
        exact hnotmem (by simp [Metta.Atom.vars])
      simp [applyClassSolution, Function.update, hne]
  | gnd ground => intro _; simp [applyClassSolution]
  | expr atoms ih =>
      intro hnotmem
      simp only [applyClassSolution]
      congr 1
      apply List.map_congr_left
      intro child hchild
      apply ih child hchild
      intro hkey
      apply hnotmem
      simpa [Metta.Atom.vars] using
        (List.mem_flatten.mpr
          ⟨child.vars, List.mem_map.mpr ⟨child, hchild, rfl⟩, hkey⟩)

/-- Every admitted non-expression match in the equality-grounded human
profile has a concrete model.  In the variable/compound cases the witness is
the identity valuation updated at the matched variable; semantic loop freedom
is exactly what makes that update non-self-referential. -/
theorem humanLeafMatch_has_model
    {left right : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic left right out)
    (hleaf : ¬BothExpressions left right) :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation out := by
  let identity : String → Metta.Atom := fun name => .var name
  cases hmatch with
  | symSym symbol hadmissible =>
      refine ⟨identity, (HumanMatchSolutionTheory.matchRel_solution_iff
        (.symSym symbol hadmissible) identity).2 ?_⟩
      rfl
  | varVar left right hadmissible =>
      let valuation : String → Metta.Atom := fun _ => .sym "human-model"
      refine ⟨valuation, (HumanMatchSolutionTheory.matchRel_solution_iff
        (.varVar left right hadmissible) valuation).2 ?_⟩
      simp [valuation, toLeaTTaAtom, applyClassSolution]
  | varNonVar hnonvariable hadmissible =>
      rename_i varName
      have hnotOccurs : ¬HumanMatchMergeSpec.AtomOccurs right varName :=
        not_atomOccurs_self_of_single_assignment_semanticLoopFree hadmissible
      have hnotMem : varName ∉ (toLeaTTaAtom right).vars := by
        intro hmem
        exact hnotOccurs (atomOccurs_of_mem_translated_vars hmem)
      let replacement := applyClassSolution identity (toLeaTTaAtom right)
      let valuation := Function.update identity varName replacement
      have hvalue : applyClassSolution valuation (toLeaTTaAtom right) =
          replacement := by
        exact (applyClassSolution_update_of_not_mem_vars_direct
          identity varName replacement (toLeaTTaAtom right) hnotMem).trans rfl
      refine ⟨valuation, (HumanMatchSolutionTheory.matchRel_solution_iff
        (.varNonVar hnonvariable hadmissible) valuation).2 ?_⟩
      simpa [valuation, replacement, toLeaTTaAtom, applyClassSolution]
        using hvalue.symm
  | nonVarVar hnonvariable hadmissible =>
      rename_i varName
      have hnotOccurs : ¬HumanMatchMergeSpec.AtomOccurs left varName :=
        not_atomOccurs_self_of_single_assignment_semanticLoopFree hadmissible
      have hnotMem : varName ∉ (toLeaTTaAtom left).vars := by
        intro hmem
        exact hnotOccurs (atomOccurs_of_mem_translated_vars hmem)
      let replacement := applyClassSolution identity (toLeaTTaAtom left)
      let valuation := Function.update identity varName replacement
      have hvalue : applyClassSolution valuation (toLeaTTaAtom left) =
          replacement := by
        exact (applyClassSolution_update_of_not_mem_vars_direct
          identity varName replacement (toLeaTTaAtom left) hnotMem).trans rfl
      refine ⟨valuation, (HumanMatchSolutionTheory.matchRel_solution_iff
        (.nonVarVar hnonvariable hadmissible) valuation).2 ?_⟩
      simpa [valuation, replacement, toLeaTTaAtom, applyClassSolution]
        using hvalue
  | @expression leftAtoms rightAtoms out hitems hadmissible =>
      exact (hleaf ⟨leftAtoms, rightAtoms, rfl, rfl⟩).elim
  | @groundedLeftCustom grounded right out hright hcustom hground
      hadmissible =>
      rcases hground with ⟨hrightEq, houtEq⟩
      subst right
      subst out
      exact ⟨identity, hesat_empty identity⟩
  | @groundedRightCustom left grounded out hleft hleftNoCustom hcustom
      hground hadmissible =>
      rcases hground with ⟨hleftEq, houtEq⟩
      subst left
      subst out
      exact ⟨identity, hesat_empty identity⟩
  | @groundedFallback left right hleft hright hadmissible =>
      exact (hleft (by
        simp [HumanMatchMergeSpec.equalityGroundedSemantic])).elim

/-- Model existence may equivalently be read at the matched atom equation.
This is the leaf base used by the compound consistency induction. -/
theorem humanLeafMatch_equation_satisfiable
    {left right : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic left right out)
    (hleaf : ¬BothExpressions left right) :
    ∃ valuation : String → Metta.Atom,
      MettaEquationSatisfied valuation
        (toLeaTTaAtom left, toLeaTTaAtom right) := by
  obtain ⟨valuation, hsatisfied⟩ := humanLeafMatch_has_model hmatch hleaf
  exact ⟨valuation,
    HumanMatchSolutionTheory.matchRel_solution_iff hmatch valuation |>.1
      hsatisfied⟩

/-- Any satisfiable binding record whose assignments are genuine values has
an acyclic class-dependency graph.  Along every dependency edge, the size of
the interpreted target strictly decreases; a directed cycle is therefore
impossible. -/
theorem semanticLoopFree_of_satisfied_nonvariable
    {valuation : String → Metta.Atom} {bindings : Bindings}
    (hsatisfied : HEBindingSatisfied valuation bindings)
    (hnonvariable : HEAssignmentsNonVariable bindings) :
    HumanMatchMergeSpec.SemanticLoopFree bindings := by
  apply HumanMatchModelTheory.semanticLoopFree_of_satisfied_nonvariable
    hsatisfied
  intro key value hassignment
  cases value with
  | symbol symbol => rfl
  | var target => exact (hnonvariable key target hassignment).elim
  | grounded grounded => rfl
  | expression atoms => rfl

/-- Every old declarative leaf witness selected under standardized-apart
inputs satisfies the human relation's semantic loop policy. -/
theorem declLeaf_semanticLoopFree
    {query pattern : Atom} {out : Bindings}
    (hmatch : DeclMatchSpec.MatchRel query pattern out)
    (hdisjoint : VarsDisjoint query pattern)
    (hleaf : ¬BothExpressions query pattern) :
    HumanMatchMergeSpec.SemanticLoopFree out := by
  cases hmatch with
  | symSym => exact HumanMatchMergeSpec.semanticLoopFree_empty
  | varVar => exact
      HumanMatchMergeSpec.semanticLoopFree_of_assignments_nil rfl
  | @varNonVar varName value _ =>
      apply HumanMatchMergeSpec.semanticLoopFree_single_assignment
      intro hoccurs
      exact hdisjoint varName
        (by simp [toLeaTTaAtom, Metta.Atom.vars])
        (mem_translated_vars_of_atomOccurs hoccurs)
  | @nonVarVar value varName _ =>
      apply HumanMatchMergeSpec.semanticLoopFree_single_assignment
      intro hoccurs
      exact hdisjoint varName
        (mem_translated_vars_of_atomOccurs hoccurs)
        (by simp [toLeaTTaAtom, Metta.Atom.vars])
  | grounded => exact HumanMatchMergeSpec.semanticLoopFree_empty
  | @expr left right out hitems =>
      exact (hleaf ⟨left, right, rfl, rfl⟩).elim

/-- Embed an admissible old leaf derivation into the executable-independent
human relation.  This lemma is structural and does not invoke old executable
soundness or completeness. -/
theorem declLeaf_to_humanMatchRel
    {query pattern : Atom} {out : Bindings}
    (hmatch : DeclMatchSpec.MatchRel query pattern out)
    (hadmissible : HumanMatchMergeSpec.SemanticLoopFree out)
    (hleaf : ¬BothExpressions query pattern) :
    HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out := by
  cases hmatch with
  | symSym symbol => exact .symSym symbol hadmissible
  | varVar left right => exact .varVar left right hadmissible
  | varNonVar hnonvar =>
      exact .varNonVar
        (by cases pattern <;>
          simp_all [HumanMatchMergeSpec.isVariableB,
            DeclMatchSpec.Atom.isVarB]) hadmissible
  | nonVarVar hnonvar =>
      exact .nonVarVar
        (by cases query <;>
          simp_all [HumanMatchMergeSpec.isVariableB,
            DeclMatchSpec.Atom.isVarB]) hadmissible
  | grounded grounded =>
      exact .groundedLeftCustom
        (by simp [HumanMatchMergeSpec.isVariableB])
        (by simp [HumanMatchMergeSpec.equalityGroundedSemantic])
        ⟨rfl, rfl⟩ hadmissible
  | @expr left right out hitems =>
      exact (hleaf ⟨left, right, rfl, rfl⟩).elim

/-- On the non-expression fragment, the executable-independent human relation
with equality grounded callbacks implies the older leaf relation.  This is a
compatibility lemma between two *relations*; it invokes no executable matcher
or merger. -/
theorem humanLeaf_to_declMatchRel
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out)
    (hleaf : ¬BothExpressions query pattern) :
    DeclMatchSpec.MatchRel query pattern out := by
  cases hmatch with
  | symSym symbol _ => exact .symSym symbol
  | varVar left right _ => exact .varVar left right
  | varNonVar hnonvar _ =>
      exact .varNonVar (by
        cases pattern <;>
          simp_all [HumanMatchMergeSpec.isVariableB,
            DeclMatchSpec.Atom.isVarB])
  | nonVarVar hnonvar _ =>
      exact .nonVarVar (by
        cases query <;>
          simp_all [HumanMatchMergeSpec.isVariableB,
            DeclMatchSpec.Atom.isVarB])
  | @expression left right out hitems _ =>
      exact (hleaf ⟨left, right, rfl, rfl⟩).elim
  | groundedLeftCustom _ _ hcustom _ =>
      rcases hcustom with ⟨hright, hout⟩
      subst hright
      subst hout
      exact .grounded _
  | groundedRightCustom _ hleftNoCustom _ hcustom _ =>
      rcases hcustom with ⟨hleft, _⟩
      subst hleft
      exact (hleftNoCustom (by
        simp [HumanMatchMergeSpec.Parameters.atomHasCustomMatcher,
          HumanMatchMergeSpec.equalityGroundedSemantic])).elim
  | groundedFallback hleft _ _ =>
      exact (hleft (by
        simp [HumanMatchMergeSpec.equalityGroundedSemantic])).elim

/-- Every human-spec leaf derivation in the standardized-apart fragment is
realized by repaired LeaTTa modulo the compositional binding observation:
equality-class closure, complete solution theory, and class-value provenance.
The theorem is direct—there is no HE executable membership witness. -/
theorem humanLeafMatch_complete
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out)
    (hdisjoint : VarsDisjoint query pattern)
    (hleaf : ¬BothExpressions query pattern) :
    ∃ leaOut,
      leaOut ∈ Metta.matchAtoms
        (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
      LeaBindingCongruence out leaOut := by
  exact matchRel_leaf_congruence_transport
    (humanLeaf_to_declMatchRel hmatch hleaf) hdisjoint hleaf

/-! ## Leaf fragment: direct soundness -/

/-- Every successful repaired-LeaTTa leaf match is admitted directly by the
human relation modulo the same observational binding congruence.  The proof
uses only the existing direct LeaTTa/leaf-relation lemmas; it never constructs
or assumes an HE executable matcher result. -/
theorem leaLeafMatch_sound
    {query pattern : Atom} {leaOut : Metta.Bindings}
    (hmatch : leaOut ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hleaf : ¬BothExpressions query pattern) :
    ∃ out,
      HumanMatchMergeSpec.MatchRel
        HumanMatchMergeSpec.equalityGroundedSemantic query pattern out ∧
      LeaBindingCongruence out leaOut := by
  rcases reflexiveVar_or_varsDisjoint_of_leaMatchAtoms_leaf hmatch hleaf with
    ⟨name, hquery, hpattern⟩ | hdisjoint
  · subst query
    subst pattern
    have hout : leaOut = [] := by
      simpa [Metta.matchAtoms, Metta.matchAtomsWith, toLeaTTaAtom] using hmatch
    subst leaOut
    refine ⟨Bindings.empty.addEquality name name,
      .varVar name name
        (HumanMatchMergeSpec.semanticLoopFree_of_assignments_nil rfl), ?_⟩
    simpa [Bindings.empty, Bindings.addEquality, Metta.Bindings.empty] using
      (LeaBindingCongruence.reflexiveSingleton name)
  · obtain ⟨out, hout⟩ :=
      exists_matchRel_of_leaMatchAtoms_leaf hmatch hdisjoint hleaf
    have hadmissible :=
      declLeaf_semanticLoopFree hout hdisjoint hleaf
    have hhuman := declLeaf_to_humanMatchRel hout hadmissible hleaf
    obtain ⟨other, hother, hcongruence⟩ :=
      matchRel_leaf_congruence_transport hout hdisjoint hleaf
    have heq : other = leaOut :=
      leaMatchAtoms_leaf_subsingleton hleaf hother hmatch
    subst other
    exact ⟨out, hhuman, hcongruence⟩

/-- Positive direct conformance witness: the human var/var equality is
realized by LeaTTa as an equality relation (orientation is observationally
irrelevant). -/
example : ∃ leaOut,
    leaOut ∈ Metta.matchAtoms (.var "y") (.var "x") ∧
    LeaBindingCongruence
      (Bindings.empty.addEquality "x" "y") leaOut := by
  apply humanLeafMatch_complete
    (HumanMatchMergeSpec.MatchRel.varVar "x" "y"
      (HumanMatchMergeSpec.semanticLoopFree_of_assignments_nil rfl))
  · simp [VarsDisjoint, toLeaTTaAtom, Metta.Atom.vars]
  · simp [BothExpressions]

/-- Negative direct-spec witness: a mismatching symbol pair has no human
derivation, independently of either executable. -/
example (out : Bindings) :
    ¬HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      (.symbol "a") (.symbol "b") out :=
  HumanMatchMergeSpec.symbol_mismatch_not_match (by decide) out

/-! ## Compound completeness reduced to direct declarative merge -/

/-- Structural variable disjointness for two atom lists. -/
def AtomListsVarsDisjoint (left right : List Atom) : Prop :=
  ∀ name,
    name ∈ ((toLeaTTaAtoms left).map Metta.Atom.vars).flatten →
      name ∉ ((toLeaTTaAtoms right).map Metta.Atom.vars).flatten

theorem varsDisjoint_expression_iff {left right : List Atom} :
    VarsDisjoint (.expression left) (.expression right) ↔
      AtomListsVarsDisjoint left right := by
  simp [VarsDisjoint, AtomListsVarsDisjoint, toLeaTTaAtom,
    Metta.Atom.vars]

theorem AtomListsVarsDisjoint.head
    {left right : Atom} {lefts rights : List Atom}
    (h : AtomListsVarsDisjoint (left :: lefts) (right :: rights)) :
    VarsDisjoint left right := by
  intro name hleft hright
  exact h name
    (by simp [toLeaTTaAtoms, hleft])
    (by simp [toLeaTTaAtoms, hright])

theorem AtomListsVarsDisjoint.tail
    {left right : Atom} {lefts rights : List Atom}
    (h : AtomListsVarsDisjoint (left :: lefts) (right :: rights)) :
    AtomListsVarsDisjoint lefts rights := by
  intro name hleft hright
  exact h name
    (by simp [toLeaTTaAtoms, hleft])
    (by simp [toLeaTTaAtoms, hright])

/-- LeaTTa's seeded list matcher distributes over an arbitrary accumulator.
This is an internal view of LeaTTa alone; it mentions no HE executable. -/
private theorem directMatchAll_flatMap_acc
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
                ((Metta.matchAtomsWith none pattern query).filter
                  (fun bindings => !bindings.hasLoop)).flatMap fun matched =>
                  Metta.Bindings.merge current matched)

/-- A successful singleton-seed list match remains successful when that seed
is selected from a larger accumulator. -/
theorem mem_matchAll_of_mem_seed
    {patterns queries : List Metta.Atom}
    {seeds : List Metta.Bindings} {seed out : Metta.Bindings}
    (hseed : seed ∈ seeds)
    (hout : out ∈ Metta.matchAll none [seed] patterns queries) :
    out ∈ Metta.matchAll none seeds patterns queries := by
  have hseedwise :
      Metta.matchAll none seeds patterns queries =
        seeds.flatMap (fun candidate =>
          Metta.matchAll none [candidate] patterns queries) := by
    simpa using
      (directMatchAll_flatMap_acc patterns queries seeds
        (fun candidate => [candidate]))
  rw [hseedwise]
  exact List.mem_flatMap.mpr ⟨seed, hseed, hout⟩

/-- The direct merge-completeness base case: the declarative empty-right merge
is realized by LeaTTa's empty-right merge with the settled congruence unchanged. -/
theorem humanMerge_empty_right_complete
    {humanLeft humanOut : Bindings} {leaLeft : Metta.Bindings}
    (hmerge : HumanMatchMergeSpec.MergeRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      humanLeft Bindings.empty humanOut)
    (hleft : LeaBindingCongruence humanLeft leaLeft) :
    ∃ leaOut,
      leaOut ∈ Metta.Bindings.merge leaLeft Metta.Bindings.empty ∧
        LeaBindingCongruence humanOut leaOut := by
  have hout := HumanMatchMergeSpec.mergeRel_empty_right_eq hmerge
  subst humanOut
  exact ⟨leaLeft, by simp [Metta.Bindings.merge, Metta.Bindings.empty], hleft⟩

/-- Human matcher results never store a bare variable as a value assignment;
variable/variable constraints remain equality edges throughout recursive
merge-back.  This is proved on the executable-independent mutual relation. -/
theorem humanMatch_assignmentsNonVariable
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out) :
    HEAssignmentsNonVariable out := by
  apply HumanMatchMergeSpec.MatchRel.rec
    (motive_1 := fun _ _ out _ => HEAssignmentsNonVariable out)
    (motive_2 := fun _ _ seed out _ =>
      HEAssignmentsNonVariable seed → HEAssignmentsNonVariable out)
    (motive_3 := fun seed _ value out _ =>
      HEAssignmentsNonVariable seed →
        DeclMatchSpec.Atom.isVarB value = false →
          HEAssignmentsNonVariable out)
    (motive_4 := fun seed _ _ out _ =>
      HEAssignmentsNonVariable seed → HEAssignmentsNonVariable out)
    (motive_5 := fun seed constraints out _ =>
      HEAssignmentsNonVariable seed →
        (∀ key value,
          HumanMatchMergeSpec.Constraint.value key value ∈ constraints →
            DeclMatchSpec.Atom.isVarB value = false) →
          HEAssignmentsNonVariable out)
    (motive_6 := fun left right out _ =>
      HEAssignmentsNonVariable left →
        HEAssignmentsNonVariable right →
          HEAssignmentsNonVariable out)
    (t := hmatch)
  next =>
      intro symbol hadmissible key target hmem
      simp [Bindings.empty] at hmem
  next =>
      intro left right hadmissible key target hmem
      simp [Bindings.empty, Bindings.addEquality] at hmem
  next =>
      intro varName value hnonvar hadmissible
      have hvalue : DeclMatchSpec.Atom.isVarB value = false := by
        cases value <;>
          simp_all [HumanMatchMergeSpec.isVariableB,
            DeclMatchSpec.Atom.isVarB]
      exact (show HEAssignmentsNonVariable Bindings.empty by
        intro key target hmem
        simp [Bindings.empty] at hmem).assign hvalue
  next =>
      intro value varName hnonvar hadmissible
      have hvalue : DeclMatchSpec.Atom.isVarB value = false := by
        cases value <;>
          simp_all [HumanMatchMergeSpec.isVariableB,
            DeclMatchSpec.Atom.isVarB]
      exact (show HEAssignmentsNonVariable Bindings.empty by
        intro key target hmem
        simp [Bindings.empty] at hmem).assign hvalue
  next =>
      intro queries patterns out hitems hadmissible ih
      exact ih (by
        intro key target hmem
        simp [Bindings.empty] at hmem)
  next =>
      intro grounded right out hright hcustom hground hadmissible
      rcases hground with ⟨hrightEq, hout⟩
      subst right
      subst out
      intro key target hmem
      simp [Bindings.empty] at hmem
  next =>
      intro left grounded out hleft hleftNoCustom hcustom hground hadmissible
      rcases hground with ⟨hleftEq, hout⟩
      subst left
      subst out
      intro key target hmem
      simp [Bindings.empty] at hmem
  next =>
      intro left right hleft hright hadmissible key target hmem
      simp [Bindings.empty] at hmem
  next =>
      intro seed hseed
      exact hseed
  next =>
      intro query pattern queries patterns seed matched next out
        hhead hmerge htail ihHead ihMerge ihTail hseed
      exact ihTail (ihMerge hseed ihHead)
  next =>
      intro seed varName value hvalues hseed hvalue
      exact hseed.assign hvalue
  next =>
      intro seed varName value first rest hvalues hagree hsame hseed hvalue
      exact hseed
  next =>
      intro seed varName value first rest matched out hvalues hagree hne
        hmatch hmerge ihMatch ihMerge hseed hvalue
      exact ihMerge hseed ihMatch
  next =>
      intro seed varName value first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge hseed hvalue
      have hempty : HEAssignmentsNonVariable Bindings.empty := by
        intro key target hmem
        simp [Bindings.empty] at hmem
      exact ihMerge hseed (ihList hempty)
  next =>
      intro seed left right values hvalues hagree hseed
      exact hseed.addEquality left right
  next =>
      intro seed left right first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge hseed
      have hempty : HEAssignmentsNonVariable Bindings.empty := by
        intro key target hmem
        simp [Bindings.empty] at hmem
      exact ihMerge (hseed.addEquality left right) (ihList hempty)
  next =>
      intro seed hseed hvalues
      exact hseed
  next =>
      intro seed next out key value rest hadd htail ihAdd ihTail hseed hvalues
      have hvalue := hvalues key value (by simp)
      have hrest : ∀ restKey restValue,
          HumanMatchMergeSpec.Constraint.value restKey restValue ∈ rest →
            DeclMatchSpec.Atom.isVarB restValue = false := by
        intro restKey restValue hmem
        exact hvalues restKey restValue (by simp [hmem])
      exact ihTail (ihAdd hseed hvalue) hrest
  next =>
      intro seed next out left right rest hadd htail ihAdd ihTail hseed hvalues
      have hrest : ∀ restKey restValue,
          HumanMatchMergeSpec.Constraint.value restKey restValue ∈ rest →
            DeclMatchSpec.Atom.isVarB restValue = false := by
        intro restKey restValue hmem
        exact hvalues restKey restValue (by simp [hmem])
      exact ihTail (ihAdd hseed) hrest
  next =>
      intro left right out order horder hfold ihFold hleft hright
      apply ihFold hleft
      intro key value hmem
      have hconstraint :
          HumanMatchMergeSpec.Constraint.value key value ∈
            HumanMatchMergeSpec.constraints right :=
        (List.Perm.mem_iff horder).mp hmem
      exact hright.isVarB_eq_false_of_assignment
        (HumanMatchSolutionTheory.value_mem_constraints_iff.mp hconstraint)

/-- The matcher-output invariant in the direct conformance development is the
non-variable assignment predicate consumed by the canonical human model. -/
theorem humanMatch_modelAssignmentsNonVariable
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out) :
    HumanMatchModelTheory.AssignmentsNonVariable out := by
  have hnonvariable := humanMatch_assignmentsNonVariable hmatch
  intro key value hassignment
  cases value with
  | symbol symbol => rfl
  | var target => exact (hnonvariable key target hassignment).elim
  | grounded grounded => rfl
  | expression atoms => rfl

/-- Admissibility is an explicit conclusion of every human match constructor. -/
theorem humanMatch_semanticLoopFree
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out) :
    HumanMatchMergeSpec.SemanticLoopFree out := by
  cases hmatch <;> assumption

/-- Every non-expression human match is already in the conflict-free guarded
path fragment.  This packages all leaf constructors as the base case for the
remaining recursive match/merge proof. -/
theorem humanLeafMatch_pathReconciled
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out)
    (hleaf : ¬BothExpressions query pattern) :
    HumanMatchStructuralModel.ClassAssignmentsPathReconciled out := by
  apply HumanMatchStructuralModel.pathReconciled_of_subsingleton_classAssignments
    (humanMatch_modelAssignmentsNonVariable hmatch)
  apply HumanMatchStructuralModel.classAssignments_subsingleton_of_assignments_unique
  intro left hleft right hright
  cases hmatch with
  | symSym symbol hadmissible =>
      simp [Bindings.empty] at hleft
  | varVar leftName rightName hadmissible =>
      simp [Bindings.empty, Bindings.addEquality] at hleft
  | varNonVar hnonvariable hadmissible =>
      rename_i varName
      have hleftEq : left = (varName, pattern) := by
        simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
          Bindings.lookup] using hleft
      have hrightEq : right = (varName, pattern) := by
        simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
          Bindings.lookup] using hright
      exact hleftEq.trans hrightEq.symm
  | nonVarVar hnonvariable hadmissible =>
      rename_i varName
      have hleftEq : left = (varName, query) := by
        simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
          Bindings.lookup] using hleft
      have hrightEq : right = (varName, query) := by
        simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
          Bindings.lookup] using hright
      exact hleftEq.trans hrightEq.symm
  | @expression lefts rights result hitems hadmissible =>
      exact (hleaf ⟨lefts, rights, rfl, rfl⟩).elim
  | @groundedLeftCustom grounded right out hright hcustom hground
      hadmissible =>
      rcases hground with ⟨hrightEq, houtEq⟩
      rw [houtEq] at hleft
      simp [Bindings.empty] at hleft
  | @groundedRightCustom left grounded out hleftNonvar
      hleftNoCustom hcustom hground hadmissible =>
      rcases hground with ⟨hleftEq, houtEq⟩
      rw [houtEq] at hleft
      simp [Bindings.empty] at hleft
  | @groundedFallback leftGround rightGround hleftNoCustom
      hrightNoCustom hadmissible =>
      exact (hleftNoCustom (by
        simp [HumanMatchMergeSpec.equalityGroundedSemantic])).elim

/-- General direct completeness of human matching, reduced to two genuine
operation-level obligations: realize a *declarative* human merge between two
already-congruent LeaTTa accumulators, and prove that a congruent raw LeaTTa
candidate passes the public semantic loop filter.  Neither hypothesis mentions
an HE executable matcher or merger.  They remain explicit until the direct
human-merge induction and raw-admissibility theorem are discharged. -/
theorem humanMatch_complete_of_directMerge
    (hmerge : ∀ {humanLeft humanRight humanOut : Bindings}
        {leaLeft leaRight : Metta.Bindings},
      HumanMatchMergeSpec.MergeRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          humanLeft humanRight humanOut →
        HEAssignmentsNonVariable humanLeft →
          HEAssignmentsNonVariable humanRight →
            LeaBindingCongruence humanLeft leaLeft →
              LeaBindingCongruence humanRight leaRight →
            ∃ leaOut,
              leaOut ∈ Metta.Bindings.merge leaLeft leaRight ∧
                LeaBindingCongruence humanOut leaOut ∧
                  HEAssignmentsNonVariable humanOut)
    (hrawAcyclic : ∀ {queries patterns : List Atom}
        {humanOut : Bindings}
        {leaOut : Metta.Bindings},
      HumanMatchMergeSpec.MatchListAccRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          queries patterns Bindings.empty humanOut →
        leaOut ∈ Metta.matchAll none [Metta.Bindings.empty]
          (toLeaTTaAtoms patterns) (toLeaTTaAtoms queries) →
        LeaBindingCongruence humanOut leaOut →
          leaOut.hasLoop = false) :
    ∀ {query pattern : Atom} {humanOut : Bindings},
      HumanMatchMergeSpec.MatchRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          query pattern humanOut →
        VarsDisjoint query pattern →
          ∃ leaOut,
            leaOut ∈ Metta.matchAtoms
              (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
              LeaBindingCongruence humanOut leaOut := by
  intro query pattern humanOut hmatch
  apply HumanMatchMergeSpec.MatchRel.rec
    (motive_1 := fun query pattern humanOut _ =>
      VarsDisjoint query pattern →
        ∃ leaOut,
          leaOut ∈ Metta.matchAtoms
            (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
          LeaBindingCongruence humanOut leaOut)
    (motive_2 := fun queries patterns humanSeed humanOut _ =>
      AtomListsVarsDisjoint queries patterns →
        HEAssignmentsNonVariable humanSeed →
        ∀ {leaSeed : Metta.Bindings},
          LeaBindingCongruence humanSeed leaSeed →
            ∃ leaOut,
              leaOut ∈ Metta.matchAll none [leaSeed]
                (toLeaTTaAtoms patterns) (toLeaTTaAtoms queries) ∧
              LeaBindingCongruence humanOut leaOut ∧
                HEAssignmentsNonVariable humanOut)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (t := hmatch)
  next =>
      intro symbol hadmissible hdisjoint
      exact humanLeafMatch_complete
        (.symSym symbol hadmissible) hdisjoint (by simp [BothExpressions])
  next =>
      intro left right hadmissible hdisjoint
      exact humanLeafMatch_complete
        (.varVar left right hadmissible) hdisjoint (by simp [BothExpressions])
  next =>
      intro varName value hnonvar hadmissible hdisjoint
      exact humanLeafMatch_complete
        (.varNonVar hnonvar hadmissible) hdisjoint
        (by simp [BothExpressions])
  next =>
      intro value varName hnonvar hadmissible hdisjoint
      exact humanLeafMatch_complete
        (.nonVarVar hnonvar hadmissible) hdisjoint
        (by simp [BothExpressions])
  next =>
      intro queries patterns out hitems hadmissible ih hdisjoint
      obtain ⟨leaOut, hlea, hcongruence, _hnonvar⟩ :=
        ih (varsDisjoint_expression_iff.mp hdisjoint)
          (by simp [HEAssignmentsNonVariable, Bindings.empty])
          LeaBindingCongruence.empty
      refine ⟨leaOut, ?_, hcongruence⟩
      have hraw : leaOut ∈ Metta.matchAtomsWith none
          (toLeaTTaAtom (.expression patterns))
          (toLeaTTaAtom (.expression queries)) := by
        simpa [Metta.matchAtomsWith, toLeaTTaAtom,
          Metta.Bindings.empty] using hlea
      have hloop := hrawAcyclic hitems hlea hcongruence
      simpa [Metta.matchAtoms] using And.intro hraw hloop
  next =>
      intro grounded right out hright hcustom hground hadmissible hdisjoint
      exact humanLeafMatch_complete
        (.groundedLeftCustom hright hcustom hground hadmissible)
        hdisjoint (by simp [BothExpressions])
  next =>
      intro left grounded out hleft hleftNoCustom hcustom hground
        hadmissible hdisjoint
      exact humanLeafMatch_complete
        (.groundedRightCustom hleft hleftNoCustom hcustom hground hadmissible)
        hdisjoint (by simp [BothExpressions])
  next =>
      intro left right hleft hright hadmissible hdisjoint
      exact humanLeafMatch_complete
        (.groundedFallback hleft hright hadmissible)
        hdisjoint (by simp [BothExpressions])
  next =>
      intro humanSeed hdisjoint hseedNonvar leaSeed hseed
      exact ⟨leaSeed, by simp [Metta.matchAll], hseed, hseedNonvar⟩
  next =>
      intro query pattern queries patterns humanSeed humanMatched humanNext
        humanOut hhead hmergeRel htail ihHead ihMerge ihTail
        hdisjoint hseedNonvar leaSeed hseed
      obtain ⟨leaMatched, hleaMatched, hmatchedCongruence⟩ :=
        ihHead hdisjoint.head
      have hmatchedNonvar := humanMatch_assignmentsNonVariable hhead
      obtain ⟨leaNext, hleaNext, hnextCongruence, hnextNonvar⟩ :=
        hmerge hmergeRel hseedNonvar hmatchedNonvar
          hseed hmatchedCongruence
      obtain ⟨leaOut, hleaOut, houtCongruence, houtNonvar⟩ :=
        ihTail hdisjoint.tail hnextNonvar hnextCongruence
      refine ⟨leaOut, ?_, houtCongruence, houtNonvar⟩
      have hnextAccumulator : leaNext ∈
          [leaSeed].flatMap (fun current =>
            ((Metta.matchAtomsWith none (toLeaTTaAtom pattern)
              (toLeaTTaAtom query)).filter
                (fun bindings => !bindings.hasLoop)).flatMap (fun matched =>
                Metta.Bindings.merge current matched)) := by
        simp only [List.flatMap_singleton, List.mem_flatMap]
        exact ⟨leaMatched, (by
          simpa [Metta.matchAtoms] using hleaMatched), hleaNext⟩
      have hlifted := mem_matchAll_of_mem_seed hnextAccumulator hleaOut
      simpa only [toLeaTTaAtoms, Metta.matchAll] using hlifted
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial

/-! ## Observational completeness through one common valuation -/

private theorem humanLeafMatch_complete_satisfied
    {valuation : String → Metta.Atom}
    {query pattern : Atom} {humanOut : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      query pattern humanOut)
    (hdisjoint : VarsDisjoint query pattern)
    (hleaf : ¬BothExpressions query pattern)
    (hsatisfied : MettaEquationSatisfied valuation
      (toLeaTTaAtom query, toLeaTTaAtom pattern)) :
    ∃ leaOut,
      leaOut ∈ Metta.matchAtoms
          (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
        LeaBindingSatisfied valuation leaOut ∧
          LeaBindingsNoFloat leaOut := by
  obtain ⟨leaOut, hlea, _hcongruence⟩ :=
    humanLeafMatch_complete hmatch hdisjoint hleaf
  refine ⟨leaOut, hlea, ?_,
    leaMatchAtoms_result_noFloat
      (toLeaTTaAtom_noFloat pattern)
      (toLeaTTaAtom_noFloat query) hlea⟩
  apply (leaMatchAtoms_solution_iff valuation
    (toLeaTTaAtom_noFloat pattern)
    (toLeaTTaAtom_noFloat query) hlea).mpr
  simpa [MettaEquationSatisfied] using hsatisfied.symm

/-- A satisfiable human match derivation is realized directly by repaired
LeaTTa once raw semantic admissibility is supplied.  The proof follows the
human mutual relation, but each live merge is constructed solely from the
common valuation by `merge_exists_of_satisfied`.  No executable HE matcher or
merger appears in the statement or proof.

This theorem isolates the two remaining boundary questions for full
extensional completeness: every admitted human match equation must have a
satisfying valuation, and every satisfying raw LeaTTa match candidate must
pass LeaTTa's public loop check. -/
theorem humanMatch_complete_of_satisfied
    {query pattern : Atom} {humanOut : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      query pattern humanOut)
    (hdisjoint : VarsDisjoint query pattern)
    {valuation : String → Metta.Atom}
    (hrawAcyclic : ∀ {patterns queries : List Metta.Atom}
        {out : Metta.Bindings},
      out ∈ Metta.matchAll none [Metta.Bindings.empty]
          patterns queries →
        LeaBindingSatisfied valuation out →
          out.hasLoop = false)
    (hsatisfied : MettaEquationSatisfied valuation
      (toLeaTTaAtom query, toLeaTTaAtom pattern)) :
    ∃ leaOut,
      leaOut ∈ Metta.matchAtoms
          (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
        LeaBindingSatisfied valuation leaOut ∧
          LeaBindingsNoFloat leaOut := by
  revert hdisjoint hsatisfied
  apply HumanMatchMergeSpec.MatchRel.rec
    (motive_1 := fun query pattern _ _ =>
      VarsDisjoint query pattern →
        MettaEquationSatisfied valuation
            (toLeaTTaAtom query, toLeaTTaAtom pattern) →
          ∃ leaOut,
            leaOut ∈ Metta.matchAtoms
                (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
              LeaBindingSatisfied valuation leaOut ∧
                LeaBindingsNoFloat leaOut)
    (motive_2 := fun queries patterns _ _ _ =>
      AtomListsVarsDisjoint queries patterns →
        MettaAtomListsSatisfied valuation
          (toLeaTTaAtoms queries) (toLeaTTaAtoms patterns) →
        ∀ {leaSeed : Metta.Bindings},
          LeaBindingSatisfied valuation leaSeed →
          LeaBindingsNoFloat leaSeed →
            ∃ leaOut,
              leaOut ∈ Metta.matchAll none [leaSeed]
                (toLeaTTaAtoms patterns) (toLeaTTaAtoms queries) ∧
              LeaBindingSatisfied valuation leaOut ∧
                LeaBindingsNoFloat leaOut)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (t := hmatch)
  next =>
      intro symbol hadmissible hdisjoint hsatisfied
      exact humanLeafMatch_complete_satisfied
        (.symSym symbol hadmissible) hdisjoint
        (by simp [BothExpressions]) hsatisfied
  next =>
      intro left right hadmissible hdisjoint hsatisfied
      exact humanLeafMatch_complete_satisfied
        (.varVar left right hadmissible) hdisjoint
        (by simp [BothExpressions]) hsatisfied
  next =>
      intro varName value hnonvar hadmissible hdisjoint hsatisfied
      exact humanLeafMatch_complete_satisfied
        (.varNonVar hnonvar hadmissible) hdisjoint
        (by simp [BothExpressions]) hsatisfied
  next =>
      intro value varName hnonvar hadmissible hdisjoint hsatisfied
      exact humanLeafMatch_complete_satisfied
        (.nonVarVar hnonvar hadmissible) hdisjoint
        (by simp [BothExpressions]) hsatisfied
  next =>
      intro queries patterns humanOut hitems hadmissible ih
        hdisjoint hsatisfied
      have hlists : MettaAtomListsSatisfied valuation
          (toLeaTTaAtoms queries) (toLeaTTaAtoms patterns) := by
        simpa [MettaAtomListsSatisfied, MettaEquationSatisfied,
          applyClassSolution,
          toLeaTTaAtom] using hsatisfied
      obtain ⟨leaOut, hlea, hleaSatisfied, hleaNoFloat⟩ :=
        ih (varsDisjoint_expression_iff.mp hdisjoint) hlists
          (leaSeed := Metta.Bindings.empty)
          (by simp [LeaBindingSatisfied, Metta.Bindings.empty])
          (by simp [LeaBindingsNoFloat, Metta.Bindings.empty])
      refine ⟨leaOut, ?_, hleaSatisfied, hleaNoFloat⟩
      have hraw : leaOut ∈ Metta.matchAtomsWith none
          (toLeaTTaAtom (.expression patterns))
          (toLeaTTaAtom (.expression queries)) := by
        simpa [Metta.matchAtomsWith, toLeaTTaAtom,
          Metta.Bindings.empty] using hlea
      have hloop := hrawAcyclic hlea hleaSatisfied
      simpa [Metta.matchAtoms] using And.intro hraw hloop
  next =>
      intro grounded right out hright hcustom hground hadmissible
        hdisjoint hsatisfied
      exact humanLeafMatch_complete_satisfied
        (.groundedLeftCustom hright hcustom hground hadmissible)
        hdisjoint (by simp [BothExpressions]) hsatisfied
  next =>
      intro left grounded out hleft hleftNoCustom hcustom hground
        hadmissible hdisjoint hsatisfied
      exact humanLeafMatch_complete_satisfied
        (.groundedRightCustom hleft hleftNoCustom hcustom hground hadmissible)
        hdisjoint (by simp [BothExpressions]) hsatisfied
  next =>
      intro left right hleft hright hadmissible hdisjoint hsatisfied
      exact humanLeafMatch_complete_satisfied
        (.groundedFallback hleft hright hadmissible)
        hdisjoint (by simp [BothExpressions]) hsatisfied
  next =>
      intro humanSeed hdisjoint hlists leaSeed hseedSatisfied hseedNoFloat
      exact ⟨leaSeed, by simp [Metta.matchAll],
        hseedSatisfied, hseedNoFloat⟩
  next =>
      intro query pattern queries patterns humanSeed humanMatched humanNext
        humanOut hhead hmergeRel htail ihHead ihMerge ihTail
        hdisjoint hlists leaSeed hseedSatisfied hseedNoFloat
      have hlistParts :
          MettaEquationSatisfied valuation
              (toLeaTTaAtom query, toLeaTTaAtom pattern) ∧
            MettaAtomListsSatisfied valuation
              (toLeaTTaAtoms queries) (toLeaTTaAtoms patterns) := by
        simpa [MettaAtomListsSatisfied, MettaEquationSatisfied] using hlists
      obtain ⟨leaMatched, hleaMatched, hmatchedSatisfied,
          hmatchedNoFloat⟩ :=
        ihHead hdisjoint.head hlistParts.1
      obtain ⟨leaNext, hleaNext, hnextSatisfied, hnextNoFloat⟩ :=
        merge_exists_of_satisfied hseedNoFloat hmatchedNoFloat
          hseedSatisfied hmatchedSatisfied
      obtain ⟨leaOut, hleaOut, houtSatisfied, houtNoFloat⟩ :=
        ihTail hdisjoint.tail hlistParts.2 hnextSatisfied hnextNoFloat
      refine ⟨leaOut, ?_, houtSatisfied, houtNoFloat⟩
      have hnextAccumulator : leaNext ∈
          [leaSeed].flatMap (fun current =>
            ((Metta.matchAtomsWith none (toLeaTTaAtom pattern)
              (toLeaTTaAtom query)).filter
                (fun bindings => !bindings.hasLoop)).flatMap (fun matched =>
                Metta.Bindings.merge current matched)) := by
        simp only [List.flatMap_singleton, List.mem_flatMap]
        exact ⟨leaMatched, (by
          simpa [Metta.matchAtoms] using hleaMatched), hleaNext⟩
      have hlifted := mem_matchAll_of_mem_seed hnextAccumulator hleaOut
      simpa only [toLeaTTaAtoms, Metta.matchAll] using hlifted
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial

/-- Extensional completeness of repaired LeaTTa for every satisfiable human
match derivation.  The comparison is exactly equality of binding solution
theories, so arbitrary constraint order and reconciliation chronology are not
observable in the statement.  Raw matcher candidates pass the public loop
filter by the exact structural resolver-budget theorem. -/
theorem humanMatch_observational_complete_of_satisfiable
    {query pattern : Atom} {humanOut : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      query pattern humanOut)
    (hdisjoint : VarsDisjoint query pattern)
    (hsatisfiable : ∃ valuation : String → Metta.Atom,
      MettaEquationSatisfied valuation
        (toLeaTTaAtom query, toLeaTTaAtom pattern)) :
    ∃ leaOut,
      leaOut ∈ Metta.matchAtoms
          (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
        LeaBindingSolutionTheoryEquiv humanOut leaOut := by
  obtain ⟨valuation, hsatisfied⟩ := hsatisfiable
  obtain ⟨leaOut, hlea, _hleaSatisfied, _hleaNoFloat⟩ :=
    humanMatch_complete_of_satisfied hmatch hdisjoint
      (fun hout hsolution =>
        leaMatchAll_empty_hasLoop_false_of_satisfied hout hsolution)
      hsatisfied
  exact ⟨leaOut, hlea,
    HumanMatchSolutionTheory.humanMatch_leaMatch_solutionTheoryEquiv
      hmatch hlea⟩

/-- Reconciliation coherence supplies the human-side model required for direct
completeness.  Its canonical most-general solution then feeds the LeaTTa
realization theorem. -/
theorem humanMatch_observational_complete_of_classCoherent
    {query pattern : Atom} {humanOut : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      query pattern humanOut)
    (hdisjoint : VarsDisjoint query pattern)
    (hcoherent : HumanMatchModelTheory.CanonicalClassCoherent humanOut
      (humanMatch_semanticLoopFree hmatch)
      (humanMatch_modelAssignmentsNonVariable hmatch)) :
    ∃ leaOut,
      leaOut ∈ Metta.matchAtoms
          (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
        LeaBindingSolutionTheoryEquiv humanOut leaOut := by
  let valuation := HumanMatchModelTheory.canonicalValuation humanOut
    (humanMatch_semanticLoopFree hmatch)
    (humanMatch_modelAssignmentsNonVariable hmatch)
  have hbindings : HEBindingSatisfied valuation humanOut :=
    HumanMatchModelTheory.canonicalValuation_satisfies_of_classCoherent
      (humanMatch_semanticLoopFree hmatch)
      (humanMatch_modelAssignmentsNonVariable hmatch) hcoherent
  have hequation : MettaEquationSatisfied valuation
      (toLeaTTaAtom query, toLeaTTaAtom pattern) := by
    exact (HumanMatchSolutionTheory.matchRel_solution_iff
      hmatch valuation).mp hbindings
  exact humanMatch_observational_complete_of_satisfiable
    hmatch hdisjoint ⟨valuation, hequation⟩

/-- Direct completeness of repaired LeaTTa against the executable-independent
human matcher relation.  Reconciliation provenance is discharged internally:
every successful human derivation has the canonical model constructed by
`HumanMatchStructuralModel.humanMatch_has_model`. -/
theorem humanMatch_observational_complete
    {query pattern : Atom} {humanOut : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      query pattern humanOut)
    (hdisjoint : VarsDisjoint query pattern) :
    ∃ leaOut,
      leaOut ∈ Metta.matchAtoms
          (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
        LeaBindingSolutionTheoryEquiv humanOut leaOut := by
  obtain ⟨valuation, hbindings⟩ :=
    HumanMatchStructuralModel.humanMatch_has_model hmatch
      (humanMatch_semanticLoopFree hmatch)
      (humanMatch_modelAssignmentsNonVariable hmatch)
  have hequation : MettaEquationSatisfied valuation
      (toLeaTTaAtom query, toLeaTTaAtom pattern) :=
    (HumanMatchSolutionTheory.matchRel_solution_iff
      hmatch valuation).mp hbindings
  exact humanMatch_observational_complete_of_satisfiable
    hmatch hdisjoint ⟨valuation, hequation⟩

/-- A derivation-produced rooted reconciliation certificate is the direct
syntactic premise for human-to-LeaTTa completeness.  Unlike bare
satisfiability or loop freedom, it records the common class value selected by
recursive reconciliation and therefore excludes incompatible acyclic binding
records. -/
theorem humanMatch_observational_complete_of_structurallyRooted
    {query pattern : Atom} {humanOut : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      query pattern humanOut)
    (hdisjoint : VarsDisjoint query pattern)
    (hrooted : HumanMatchStructuralModel.ClassAssignmentsStructurallyRooted
      humanOut) :
    ∃ leaOut,
      leaOut ∈ Metta.matchAtoms
          (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
        LeaBindingSolutionTheoryEquiv humanOut leaOut := by
  apply humanMatch_observational_complete_of_classCoherent hmatch hdisjoint
  exact HumanMatchStructuralModel.canonicalClassCoherent_of_structurallyRooted
    (humanMatch_semanticLoopFree hmatch)
    (humanMatch_modelAssignmentsNonVariable hmatch) hrooted

/-- The directional reconciliation certificate is the general direct
completeness boundary: it supports recursively replaced assignments while
remaining strong enough to construct the canonical human model. -/
theorem humanMatch_observational_complete_of_reconciled
    {query pattern : Atom} {humanOut : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      query pattern humanOut)
    (hdisjoint : VarsDisjoint query pattern)
    (hreconciled : HumanMatchStructuralModel.ClassAssignmentsReconciled
      humanOut) :
    ∃ leaOut,
      leaOut ∈ Metta.matchAtoms
          (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
        LeaBindingSolutionTheoryEquiv humanOut leaOut := by
  apply humanMatch_observational_complete_of_classCoherent hmatch hdisjoint
  exact HumanMatchStructuralModel.canonicalClassCoherent_of_reconciled
    (humanMatch_semanticLoopFree hmatch)
    (humanMatch_modelAssignmentsNonVariable hmatch) hreconciled

/-- Guarded reconciliation paths are the compositional direct-completeness
boundary.  Every intermediate equation is constrained to dependency classes
strictly below the ambient class, so recursive merge-back may compose paths
without admitting the current-class bridge refuted by the negative oracle. -/
theorem humanMatch_observational_complete_of_pathReconciled
    {query pattern : Atom} {humanOut : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      query pattern humanOut)
    (hdisjoint : VarsDisjoint query pattern)
    (hreconciled :
      HumanMatchStructuralModel.ClassAssignmentsPathReconciled humanOut) :
    ∃ leaOut,
      leaOut ∈ Metta.matchAtoms
          (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
        LeaBindingSolutionTheoryEquiv humanOut leaOut := by
  apply humanMatch_observational_complete_of_classCoherent hmatch hdisjoint
  exact HumanMatchStructuralModel.canonicalClassCoherent_of_pathReconciled
    (humanMatch_semanticLoopFree hmatch)
    (humanMatch_modelAssignmentsNonVariable hmatch) hreconciled

/-- Closed conflict-free human fragment: if every final equality class carries
at most one assignment, human-side model existence is unconditional. -/
theorem humanMatch_observational_complete_of_subsingleton_classAssignments
    {query pattern : Atom} {humanOut : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      query pattern humanOut)
    (hdisjoint : VarsDisjoint query pattern)
    (hsubsingleton : ∀ source :
        HumanMatchModelTheory.DependencyNode humanOut,
      Subsingleton
        (HumanMatchModelTheory.ClassAssignment humanOut source.1)) :
    ∃ leaOut,
      leaOut ∈ Metta.matchAtoms
          (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
        LeaBindingSolutionTheoryEquiv humanOut leaOut := by
  apply humanMatch_observational_complete_of_classCoherent hmatch hdisjoint
  exact HumanMatchModelTheory.canonicalClassCoherent_of_subsingleton_classAssignments
    (humanMatch_semanticLoopFree hmatch)
    (humanMatch_modelAssignmentsNonVariable hmatch) hsubsingleton

/-- Independent Robinson certificate route to human-side model existence.
Translating a successful human match derivation into `UnifyDerives` supplies
the model. -/
theorem humanMatch_observational_complete_of_unifyDerives
    {query pattern : Atom} {humanOut : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      query pattern humanOut)
    (hdisjoint : VarsDisjoint query pattern)
    (hderives : Mettapedia.Logic.LP.UnifyDerives
      (HumanMatchLPBridge.bindingEquations humanOut)) :
    ∃ leaOut,
      leaOut ∈ Metta.matchAtoms
          (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
        LeaBindingSolutionTheoryEquiv humanOut leaOut := by
  obtain ⟨valuation, hbindings⟩ :=
    HumanMatchLPBridge.has_model_of_unifyDerives hderives
  have hequation : MettaEquationSatisfied valuation
      (toLeaTTaAtom query, toLeaTTaAtom pattern) :=
    (HumanMatchSolutionTheory.matchRel_solution_iff
      hmatch valuation).mp hbindings
  exact humanMatch_observational_complete_of_satisfiable
    hmatch hdisjoint ⟨valuation, hequation⟩

end Mettapedia.Languages.MeTTa.HE.LeaTTaHumanConformance
