import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Matching

/-!
# The ground presentation is the instance of the presentation with unknowns at ground rules

A ground rule over rows (`Rule Rows`, the rules of `Presentation.present`) is a rule with unknowns that has none
(`liftRule`: its rows as terms). For a program of the ground positive fragment (`Positive`):

* every lifted rule is in the fragment of rules with unknowns (`liftRule_fragment`);
* a firing by matching of a lifted rule is exactly a firing of the ground rule (`matchFires_lift_iff`): its takes
  beside a rest are the store, its reads are rows of the rest, its guards hold;
* **the two presentations have the same step on stores** (`semanticStep_ground_iff`): the framework's step modulo
  equations of `present rules` relates two stores exactly when the step of `presentSchematic` of the lifted
  rules does. The ground presentation consumes and remakes each distinct read row; the presentation with unknowns
  matches reads against the rest with a premise and keeps them in the rest. On ground rules the two agree; with
  unknowns only the second is exact (`Controls.consumeReproduce_refuses`).

So the theorems of the ground presentation (`Presentation.generated_possibility_iff` and the rest) are unchanged,
and on ground programs they are statements about the same step as the theorems here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.Framework.TypeSynthesis (langSemanticReducesUsing)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open NamesOnTheStep (Expr)

/-- **A ground rule as a rule with unknowns**: its rows as terms without unknowns. -/
def liftRule (r : Rule Rows) : SRule := ⟨PUnit.unit, r.body.map toTerm, r.collect.map toTerm⟩

theorem isGuard_map (c : Check Expr) : isGuard (Check.map toTerm c) = isEquationCheck c := by
  cases c <;> rfl

theorem written_lift {r : Rule Rows} {t : Tm} (member : t ∈ written (liftRule r)) : ∃ e, t = toTerm e := by
  simp only [written, liftRule, RuleInstance.map, List.map_map, List.mem_append, List.mem_map,
    List.mem_flatMap, Function.comp_def] at member
  rcases member with (((⟨pair, -, rfl⟩ | ⟨pair, -, rfl⟩) | ⟨c, inChecks, inTerms⟩) | ⟨e, -, rfl⟩)
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · obtain ⟨c₀, -, rfl⟩ := inChecks
    cases c₀ with
    | equal l r' =>
        simp only [Check.map, checkTerms, List.mem_cons, List.not_mem_nil, or_false] at inTerms
        rcases inTerms with rfl | rfl
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    | predicate quantifier p =>
        simp only [Check.map, checkTerms, List.mem_singleton] at inTerms
        exact ⟨_, inTerms⟩
    | count p n =>
        simp only [Check.map, checkTerms, List.mem_singleton] at inTerms
        exact ⟨_, inTerms⟩
  · exact ⟨_, rfl⟩

/-- **A ground rule of the positive fragment is a rule with unknowns of the fragment.** -/
theorem liftRule_fragment {r : Rule Rows} (positive : Positive r) : RangeRestrictedPositive (liftRule r) := by
  refine ⟨by simp [liftRule, positive.1], ?_, fun t member x vars => ?_⟩
  · show (r.body.checks.map (Check.map toTerm)).all isGuard = true
    rw [List.all_map]
    have same : (isGuard ∘ Check.map toTerm) = isEquationCheck := funext isGuard_map
    rw [same]
    exact positive.2
  · obtain ⟨e, rfl⟩ := written_lift member
    exact absurd vars (vars_toTerm e x)

theorem equationsOf_lift (r : Rule Rows) :
    equationsOf (liftRule r) = r.body.tell.map (fun pair => (toTerm pair.1, toTerm pair.2)) ++
      r.body.checks.flatMap (fun c => (guardOf (Check.map toTerm c))) := by
  simp [equationsOf, liftRule, RuleInstance.map, List.flatMap_map]

/-- **A firing by matching of a lifted rule is a firing of the ground rule**: its takes beside a rest are the
store, its reads are rows of the rest, and its guards hold. -/
theorem matchFires_lift_iff (r : Rule Rows) (θ : ℕ → Expr) (rows rest : List Expr) :
    MatchFires (liftRule r) θ rows rest ↔
      (r.body.take ++ rest).Perm rows ∧ (∀ q ∈ r.body.read, q ∈ rest) ∧ guardsHold r = true := by
  have takes : (liftRule r).body.take.map (inst θ) = r.body.take := by
    simp [liftRule, RuleInstance.map, List.map_map, Function.comp_def, inst_toTerm]
  have reads : (∀ q ∈ (liftRule r).body.read, inst θ q ∈ rest) ↔ ∀ q ∈ r.body.read, q ∈ rest := by
    simp [liftRule, RuleInstance.map, inst_toTerm]
  have guards : (∀ e ∈ equationsOf (liftRule r), inst θ e.1 = inst θ e.2) ↔ guardsHold r = true := by
    rw [equationsOf_lift]
    simp only [guardsHold, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_append,
      List.mem_map, List.mem_flatMap]
    constructor
    · intro each
      refine ⟨fun pair inTell => ?_, fun c inChecks => ?_⟩
      · have equal := each _ (Or.inl ⟨pair, inTell, rfl⟩)
        simpa [inst_toTerm] using equal
      · cases c with
        | equal l r' =>
            have equal := each (toTerm l, toTerm r') (Or.inr ⟨.equal l r', inChecks, by simp [guardOf, Check.map]⟩)
            simp only [inst_toTerm] at equal
            simp [groundCheck, equal]
        | predicate quantifier _ => rfl
        | count _ _ => rfl
    · rintro ⟨tells, checks⟩ e (⟨pair, inTell, rfl⟩ | ⟨c, inChecks, inGuard⟩)
      · simp only [inst_toTerm]
        exact tells pair inTell
      · cases c with
        | equal l r' =>
            simp only [guardOf, Check.map, List.mem_singleton] at inGuard
            subst inGuard
            have holds := checks (.equal l r') inChecks
            simp only [groundCheck, decide_eq_true_eq] at holds
            simp only [inst_toTerm]
            exact holds
        | predicate quantifier _ => simp [guardOf, Check.map] at inGuard
        | count _ _ => simp [guardOf, Check.map] at inGuard
  constructor
  · rintro ⟨takesPerm, readsIn, equations⟩
    exact ⟨takes ▸ takesPerm, reads.mp readsIn, guards.mp equations⟩
  · rintro ⟨takesPerm, readsIn, holds⟩
    exact ⟨by rw [takes]; exact takesPerm, reads.mpr readsIn, guards.mpr holds⟩

theorem produce_lift (r : Rule Rows) (θ : ℕ → Expr) : (liftRule r).body.produce.map (inst θ) = r.body.produce := by
  simp [liftRule, RuleInstance.map, List.map_map, Function.comp_def, inst_toTerm]

variable {relEnv : RelationEnv} {rules : List (Rule Rows)}

/-- **The ground presentation and the presentation with unknowns have the same step on stores**, for a program of
the ground positive fragment. -/
theorem semanticStep_ground_iff (noEq : ∀ args, relEnv.tuples "eq" args = []) (positive : ∀ r ∈ rules, Positive r)
    {rows next : List Expr} :
    langSemanticReducesUsing relEnv (present rules) (storeCode rows) (storeCode next) ↔
      langSemanticReducesUsing relEnv (presentSchematic (rules.map liftRule)) (storeCode rows) (storeCode next) := by
  have fragment : ∀ r' ∈ rules.map liftRule, RangeRestrictedPositive r' := by
    intro r' member
    obtain ⟨r, inRules, rfl⟩ := List.mem_map.mp member
    exact liftRule_fragment (positive r inRules)
  have oldEquiv : ∀ a b : List Expr,
      EquationEquiv (engineBasePremises relEnv) (present rules) (storeCode a) (storeCode b) ↔ a.Perm b :=
    fun _ _ => equationEquiv_storeCode_iff presentWith_equations presentWith_noAlgebra presentWith_formers
      presentWith_store
  have newEquiv : ∀ a b : List Expr,
      EquationEquiv (engineBasePremises relEnv) (presentSchematic (rules.map liftRule)) (storeCode a) (storeCode b) ↔
        a.Perm b :=
    fun _ _ => equationEquiv_storeCode_iff presentSchematic_equations presentSchematic_noAlgebra
      presentSchematic_formers presentSchematic_store
  rw [Presentation.semanticStep_storeCode_iff, semanticStep_storeCode_iff noEq fragment]
  simp only [oldEquiv, newEquiv]
  constructor
  · rintro ⟨r, inRules, holds, rest, split, reached⟩
    refine ⟨liftRule r, List.mem_map_of_mem inRules, fun _ => .sym 0, r.body.read.dedup ++ rest,
      (matchFires_lift_iff r _ rows _).mpr ⟨?_, fun q member => List.mem_append_left _ (List.mem_dedup.mpr member),
        holds⟩, ?_⟩
    · rw [← List.append_assoc]
      exact split
    · rw [produce_lift, ← List.append_assoc]
      exact reached
  · rintro ⟨r', member, θ, rest', fires, reached⟩
    obtain ⟨r, inRules, rfl⟩ := List.mem_map.mp member
    obtain ⟨takesPerm, readsIn, holds⟩ := (matchFires_lift_iff r θ rows rest').mp fires
    rw [produce_lift] at reached
    -- the distinct reads are part of the rest
    have sub : (r.body.read.dedup : Multiset Expr) ≤ rest' :=
      (Multiset.le_iff_subset (Multiset.coe_nodup.mpr (List.nodup_dedup _))).mpr fun x inside =>
        Multiset.mem_coe.mpr (readsIn x (List.mem_dedup.mp (Multiset.mem_coe.mp inside)))
    obtain ⟨others, decomposed⟩ := Multiset.le_iff_exists_add.mp sub
    have restPerm : (r.body.read.dedup ++ others.toList).Perm rest' := by
      refine Multiset.coe_eq_coe.mp ?_
      rw [← Multiset.coe_add, Multiset.coe_toList]
      exact decomposed.symm
    refine ⟨r, inRules, holds, others.toList, ?_, ?_⟩
    · show (r.body.take ++ r.body.read.dedup ++ others.toList).Perm rows
      rw [List.append_assoc]
      exact (restPerm.append_left _).trans takesPerm
    · show (r.body.produce ++ r.body.read.dedup ++ others.toList).Perm next
      rw [List.append_assoc]
      exact (restPerm.append_left _).trans reached

#print axioms liftRule_fragment
#print axioms matchFires_lift_iff
#print axioms semanticStep_ground_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic
