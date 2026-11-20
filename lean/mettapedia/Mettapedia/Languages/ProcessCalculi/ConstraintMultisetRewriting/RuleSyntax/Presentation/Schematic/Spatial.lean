import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Possibility
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Spatial

/-!
# The spatial law, for programs with unknowns

The split former and the equivalence of the generated logic depend only on constructors and equations, so the
general forms in `Presentation.Spatial` apply to `presentSchematic` unchanged:

* `split_generated_schematic`, `sat_split_iff_schematic`: **"A beside B"** is generated, and holds at a store
  exactly when its rows divide into a store of type `A` and a store of type `B`.
* `schematic_referenceProfile`: the presentation is aligned: its premises are relation queries and its right
  sides move no metavariable across a binder; so the generated logic's step is the framework's
  (`schematic_refStep_iff`), and **the generated logic's own possibility** at a store is a firing by matching
  (`sat_possibly_schematic`).
* `split_possibly_schematic`: **a firing of a part is a firing of the whole**, in the generated types:
  "(possibly A) beside B" implies "possibly (A beside B)".
* `fires_beside`: **the same law on `RuleSyntax.step` with unknowns**: an admitted firing of a ground state with
  trivial knowledge gives an admitted firing of the state beside another ground state with disjoint identities and
  trivial knowledge, whose result reads as the first result beside the other's rows.

Substitutability is not carried over here: the tree's Hennessy–Milner theorem used for ground programs
(`ProgramAdequacy.program_adequacy`) is about the step of a finite set of rule instances, and a rule with
unknowns stands for infinitely many ground instances and is not such a step (it would share its unknowns with the
caller: `RuleSyntax.OneFrame.Controls.instanceSet_captures`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
  (Formula Env referenceStructure IsState ObjectEquivalent sat_respects_equivalent GeneratedBy)
open Interface (Frames)
open NamesOnTheStep (Expr)

universe uO

/-! ## The presentation is aligned -/

theorem extraNotDeeper_unary (lhs : Pattern) (extra : List Pattern) (d : ℕ) : ∀ k : ℕ,
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper lhs extra d (Pattern.unary "Zero" "Succ" k) = true
  | 0 => by simp [Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
      Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList]
  | k + 1 => by simp [Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
      Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList, extraNotDeeper_unary lhs extra d k]

theorem extraNotDeeper_fvar_zero (lhs : Pattern) (extra : List Pattern) (n : String) :
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper lhs extra 0 (.fvar n) = true := by
  simp only [Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper]
  split <;> (try split) <;> simp

/-- **The code of a term moves no metavariable across a binder.** -/
theorem extraNotDeeper_termCode (lhs : Pattern) (extra : List Pattern) : ∀ p : Tm,
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper lhs extra 0 (termCode p) = true
  | .var _ => extraNotDeeper_fvar_zero lhs extra _
  | .const (.sym k) => by
      simp [termCode, Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
        Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList, extraNotDeeper_unary lhs extra 0 k]
  | .const (.name n) => by
      simp [termCode, Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
        Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList, extraNotDeeper_unary lhs extra 0 n]
  | .app .app ts => by
      have first := extraNotDeeper_termCode lhs extra (ts head)
      have second := extraNotDeeper_termCode lhs extra (ts tail)
      simp [termCode, Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
        Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList, first, second]
  | .app .code ts => by
      have only := extraNotDeeper_termCode lhs extra (ts body)
      simp [termCode, Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
        Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList, only]

theorem extraNotDeeperList_termCode (lhs : Pattern) (extra : List Pattern) : ∀ ps : List Tm,
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList lhs extra 0 (ps.map termCode) = true
  | [] => rfl
  | p :: ps => by
      simp only [List.map_cons, Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList,
        extraNotDeeper_termCode lhs extra p, extraNotDeeperList_termCode lhs extra ps, Bool.and_self]

/-- **Every rewrite of the presentation is aligned**: its premises are relation queries, and its right side moves
no metavariable across a binder. -/
theorem schematicRewrite_ruleAligned (index : ℕ) (r : SRule) :
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.ruleAligned (schematicRewrite index r) = true := by
  unfold Mettapedia.OSLF.MeTTaIL.ReferenceStep.ruleAligned
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.mpr fun p member => ?_, ?_⟩
  · rcases List.mem_append.mp member with read | equation
    · obtain ⟨j, -, rfl⟩ := List.mem_mapIdx.mp read
      rfl
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp equation
      rfl
  · show Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper _ _ 0
      (.collection .hashBag (r.body.produce.map termCode) (some "rest")) = true
    simp only [Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper, extraNotDeeperList_termCode, Bool.true_and]
    split <;> (try split) <;> simp

variable {relEnv : RelationEnv} {rules : List SRule}

theorem schematic_referenceProfile :
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.ReferenceProfile (presentSchematic rules) := by
  intro rule member
  obtain ⟨r, -, index, rfl⟩ := of_mem_rewrites member
  exact schematicRewrite_ruleAligned index r

/-! ## The split law and the generated possibility -/

theorem split_generated_schematic (A B : Formula 0) :
    GeneratedBy (presentSchematic rules) (.split .hashBag A B) ↔
      GeneratedBy (presentSchematic rules) A ∧ GeneratedBy (presentSchematic rules) B :=
  split_generated_in rfl A B

/-- **The split law for programs with unknowns.** -/
theorem sat_split_iff_schematic (A B : Formula 0) (rows : List Expr) :
    (referenceStructure relEnv (presentSchematic rules)).sat Env.closed (.split .hashBag A B) (storeCode rows) ↔
      ∃ left right : List Expr, (left ++ right).Perm rows ∧
        (referenceStructure relEnv (presentSchematic rules)).sat Env.closed A (storeCode left) ∧
        (referenceStructure relEnv (presentSchematic rules)).sat Env.closed B (storeCode right) :=
  sat_split_iff_in presentSchematic_equations presentSchematic_noAlgebra presentSchematic_formers
    presentSchematic_store A B rows

/-- **The generated logic's step from a store is a firing by matching.** -/
theorem schematic_refStep_iff (noEq : ∀ args, relEnv.tuples "eq" args = [])
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) {rows : List Expr} {target : Pattern} :
    (referenceStructure relEnv (presentSchematic rules)).step (storeCode rows) .any target ↔
      IsState target ∧ ∃ r ∈ rules, ∃ θ rest, MatchFires r θ rows rest ∧
        ObjectEquivalent relEnv (presentSchematic rules) .syntax (storeCode (r.body.produce.map (inst θ) ++ rest))
          target := by
  rw [refStep_storeCode_iff_in presentSchematic_equations presentSchematic_noAlgebra presentSchematic_formers
    presentSchematic_store schematic_referenceProfile (fun step => by
      obtain ⟨r, -, θ, rest, -, rfl⟩ := step_sound noEq fragment step
      exact ⟨_, rfl⟩)]
  constructor
  · rintro ⟨targetState, arranged, next, perm, step, toTarget⟩
    obtain ⟨r, member, θ, rest, fires, same⟩ := step_sound noEq fragment step
    obtain rfl := storeCode_injective same
    exact ⟨targetState, r, member, θ, rest, ⟨fires.takes.trans perm.symm, fires.reads, fires.equations⟩, toTarget⟩
  · rintro ⟨targetState, r, member, θ, rest, fires, toTarget⟩
    exact ⟨targetState, _, _, fires.takes.symm,
      step_prefix noEq member (fragment r member).2.2 fires.reads fires.equations, toTarget⟩

/-- **The generated logic's own possibility at a store** is a firing by matching to a store of the type. -/
theorem sat_possibly_schematic (noEq : ∀ args, relEnv.tuples "eq" args = [])
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) (A : Formula 0) (rows : List Expr) :
    (referenceStructure relEnv (presentSchematic rules)).sat Env.closed (.possibly .any A) (storeCode rows) ↔
      ∃ r ∈ rules, ∃ θ rest, MatchFires r θ rows rest ∧
        (referenceStructure relEnv (presentSchematic rules)).sat Env.closed A
          (storeCode (r.body.produce.map (inst θ) ++ rest)) := by
  change (∃ next, (referenceStructure relEnv (presentSchematic rules)).step (storeCode rows) .any next ∧
    (referenceStructure relEnv (presentSchematic rules)).sat Env.closed A next) ↔ _
  constructor
  · rintro ⟨next, step, holds⟩
    obtain ⟨nextState, r, member, θ, rest, fires, toNext⟩ := (schematic_refStep_iff noEq fragment).mp step
    exact ⟨r, member, θ, rest, fires,
      (sat_respects_equivalent relEnv _ A (isState_storeCode _) nextState toNext).mpr holds⟩
  · rintro ⟨r, member, θ, rest, fires, holds⟩
    exact ⟨_, (schematic_refStep_iff noEq fragment).mpr ⟨isState_storeCode _, r, member, θ, rest, fires,
      Relation.EqvGen.refl _⟩, holds⟩

/-- **A firing of a part is a firing of the whole**, in the generated types of the presentation with unknowns:
"(possibly A) beside B" implies "possibly (A beside B)". -/
theorem split_possibly_schematic (noEq : ∀ args, relEnv.tuples "eq" args = [])
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) (A B : Formula 0) (rows : List Expr)
    (holds : (referenceStructure relEnv (presentSchematic rules)).sat Env.closed
      (.split .hashBag (.possibly .any A) B) (storeCode rows)) :
    (referenceStructure relEnv (presentSchematic rules)).sat Env.closed
      (.possibly .any (.split .hashBag A B)) (storeCode rows) := by
  obtain ⟨left, right, perm, possible, holdsB⟩ := (sat_split_iff_schematic _ _ rows).mp holds
  obtain ⟨r, member, θ, rest, fires, holdsA⟩ := (sat_possibly_schematic noEq fragment A left).mp possible
  refine (sat_possibly_schematic noEq fragment _ rows).mpr ⟨r, member, θ, rest ++ right, ⟨?_,
    fun q inRead => List.mem_append_left _ (fires.reads q inRead), fires.equations⟩, ?_⟩
  · rw [← List.append_assoc]
    exact (fires.takes.append_right right).trans perm
  · refine (sat_split_iff_schematic A B _).mpr ⟨r.body.produce.map (inst θ) ++ rest, right, ?_, holdsA, holdsB⟩
    rw [List.append_assoc]

/-! ## The same law on `RuleSyntax.step` with unknowns -/

variable {O : Type uO} [DecidableEq O]

/-- **Two states side by side**: the knowledge of both, the present rows of both, each with its own label. -/
def unionStates (s t : SState O) : SState O :=
  ⟨PUnit.unit, s.knowledge ++ t.knowledge, s.present ∪ t.present,
    fun o => if o ∈ s.present then s.label o else t.label o⟩

/-- **A firing of a part is a firing of the whole, on `RuleSyntax.step` with unknowns.** -/
theorem fires_beside [Infinite O] (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) {s t : SState O}
    {rows : O → Expr} (groundS : GroundLabels s rows) (groundT : GroundLabels t rows)
    (apart : Disjoint s.present t.present) (knowledgeS : TrivialKnowledge s.knowledge)
    (knowledgeT : TrivialKnowledge t.knowledge)
    (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g) :
    ∃ (g' : Firing O E {r | r ∈ rules} (unionStates s t).frame)
      (admitted' : (schematicStep O rules).Admits (s := unionStates s t) g'),
      ∀ bag, ReadsAs ((schematicStep O rules).result g admitted) bag →
        ReadsAs ((schematicStep O rules).result g' admitted') (bag + t.present.val.map rows) := by
  obtain ⟨θ, fires, readsResult⟩ := match_of_admitted groundS fragment g admitted
  have groundU : GroundLabels (unionStates s t) rows := by
    intro o inside
    show (if o ∈ s.present then s.label o else t.label o) = _
    split_ifs with inS
    · exact groundS o inS
    · exact groundT o ((Finset.mem_union.mp inside).resolve_left inS)
  have knowledgeU : TrivialKnowledge (unionStates s t).knowledge := by
    intro e inside
    rcases List.mem_append.mp inside with inS | inT
    · exact knowledgeS e inS
    · exact knowledgeT e inT
  have takesS : (g.rule.body.take.map (inst θ) : Multiset Expr) +
      ((s.present \ g.selection.taken.toFinset).toList.map rows : List Expr) = s.present.val.map rows := by
    rw [← coe_storeRows s rows, Multiset.coe_add]
    exact Multiset.coe_eq_coe.mpr fires.takes
  have split : (g.rule.body.take.map (inst θ) : Multiset Expr) +
      ((((s.present \ g.selection.taken.toFinset).toList.map rows : List Expr) : Multiset Expr) +
        t.present.val.map rows) = (unionStates s t).present.val.map rows := by
    show _ = (s.present ∪ t.present).val.map rows
    rw [val_union_of_disjoint apart, Multiset.map_add, ← add_assoc, takesS]
  obtain ⟨g', admitted', -, readsU⟩ := admitted_of_match groundU knowledgeU g.member (fragment g.rule g.member) split
    (fun q inRead => Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr (fires.reads q inRead)))) fires.equations
  refine ⟨g', admitted', fun bag reads => ?_⟩
  obtain ⟨-, -, -, solvable, -, -⟩ := (admits_iff g).mp admitted
  have same := readsAs_unique ((Frames.ofSubstitution_solvable_iff A _).mp solvable) reads readsResult
  rw [same]
  have restCoe : ((((s.present \ g.selection.taken.toFinset).toList.map rows : List Expr)) : Multiset Expr) =
      (s.present \ g.selection.taken.toFinset).val.map rows := by
    rw [← Multiset.map_coe, Finset.coe_toList]
  rw [restCoe] at readsU
  have shape : (g.rule.body.produce.map (inst θ) : Multiset Expr) +
      ((s.present \ g.selection.taken.toFinset).val.map rows + t.present.val.map rows) =
      (s.present \ g.selection.taken.toFinset).val.map rows + (g.rule.body.produce.map (inst θ) : Multiset Expr) +
        t.present.val.map rows := by
    rw [← add_assoc, add_comm (g.rule.body.produce.map (inst θ) : Multiset Expr)]
  rw [← shape]
  exact readsU

#print axioms schematicRewrite_ruleAligned
#print axioms schematic_referenceProfile
#print axioms sat_split_iff_schematic
#print axioms schematic_refStep_iff
#print axioms sat_possibly_schematic
#print axioms split_possibly_schematic
#print axioms fires_beside

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic
