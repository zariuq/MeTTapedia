import Mettapedia.Languages.ProcessCalculi.Ambient.Core
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationReference

/-!
# The laws of mobile ambients with restriction and replication

The ambient calculus declares the laws of restriction and of replication of its blocks and one more: a restriction
crosses the boundary of an ambient it does not name (`ambientBoundary`). Its signature is that of the restriction-block
theory (`coreSignature`). Each instance of the boundary law relates explicit shapes (`boundary_forward_shape`,
`boundary_reverse_shape`): the ambient `m[(νx) P]` and the restriction `(νx) m↑[P]`, the ambient's name lifted past
the binder.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Full

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc coreSignature coreReplicationSignature
  coreBagPresentation)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext parameterType? UsesBareCollection
  isObjectPattern)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (BagPresentation)
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.RuleBinding (ContextualValue recoverValue? instantiateValue? arguments?
  dependencies? occurrenceDeclared sitePattern? occurrenceAt? recoverValue?_forward recoverValue?_context)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (isWellScopedListAt_eq_true_iff)
open Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution (Orientation orientedRule exchangeBindings exchangeOccurrence
  exchangeSite)

/-! ## The boundary law's instances -/

/-- **Every forward instance of the boundary law**: an ambient over a restriction becomes the restriction over the
ambient, the ambient's name lifted past the binder. -/
theorem boundary_forward_shape {ambient : Nat} {spec : RuleBindingSpec} {captured : Assignment}
    {source target : Pattern} (bound : (orientedRule ambientBoundary .forward).bindings = some spec)
    (sourceScoped : source.isWellScopedAt ambient = true)
    (matched : captured ∈ matchRuleAt (orientedRule ambientBoundary .forward) spec ambient source)
    (applied : reduct? (orientedRule ambientBoundary .forward) spec ambient captured = some target) :
    ∃ (name : Pattern) (binder : Option String) (body : Pattern),
      source = .apply "AAmb" [name, .apply "ANu" [.lambda binder body]] ∧
      target = .apply "ANu" [.lambda none (.apply "AAmb" [liftBVars 0 1 name, body])] := by
  obtain rfl : spec = (orientedRule ambientBoundary .forward).bindings.getD { dependencies := [] } := by
    rw [bound]; rfl
  simp only [matchRuleAt, matchRuleWithAt] at matched
  rw [show (orientedRule ambientBoundary .forward).left =
      .apply "AAmb" [.fvar "m", .apply "ANu" [.lambda none (.fvar "P")]] from rfl, mem_matchAtWith_apply] at matched
  obtain ⟨arguments, rfl, matched⟩ := matched
  rw [mem_matchArgsAtWith_cons] at matched
  obtain ⟨nameValue, rest, afterName, rfl, nameMatched, matched⟩ := matched
  rw [mem_matchArgsAtWith_cons] at matched
  obtain ⟨restriction, rest', afterRestriction, rfl, restrictionMatched, matched⟩ := matched
  rw [mem_matchArgsAtWith_nil] at matched
  obtain ⟨rfl, rfl⟩ := matched
  rw [mem_matchAtWith_apply] at restrictionMatched
  obtain ⟨restrictionArguments, rfl, restrictionMatched⟩ := restrictionMatched
  rw [mem_matchArgsAtWith_cons] at restrictionMatched
  obtain ⟨abstraction, rest'', afterAbstraction, rfl, binderMatched, restrictionMatched⟩ := restrictionMatched
  rw [mem_matchArgsAtWith_nil] at restrictionMatched
  obtain ⟨rfl, rfl⟩ := restrictionMatched
  rw [mem_matchAtWith_lambda] at binderMatched
  obtain ⟨binder, body, rfl, binderMatched⟩ := binderMatched
  have argumentsScoped : Pattern.isWellScopedListAt ambient
      [nameValue, .apply "ANu" [.lambda binder body]] = true := by
    simpa [Pattern.isWellScopedAt] using sourceScoped
  have nameScoped : nameValue.isWellScopedAt ambient = true :=
    ((isWellScopedListAt_eq_true_iff _ _).mp argumentsScoped) _ List.mem_cons_self
  have bodyScoped : body.isWellScopedAt (1 + ambient) = true := by
    have restrictionScoped := ((isWellScopedListAt_eq_true_iff _ _).mp argumentsScoped) _
      (List.mem_cons_of_mem _ List.mem_cons_self)
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Nat.add_comm] using restrictionScoped
  rw [mem_matchAtWith_fvar, captureWith?_literal] at nameMatched
  simp [capture?, orientedRule, ambientBoundary, dependencies?, arguments?, occurrenceDeclared, sitePattern?,
    occurrenceAt?, recoverValue?_zero nameScoped, assign, lookup] at nameMatched
  subst nameMatched
  rw [mem_matchAtWith_fvar, captureWith?_literal] at binderMatched
  simp [capture?, orientedRule, ambientBoundary, dependencies?, arguments?, occurrenceDeclared, sitePattern?,
    occurrenceAt?, recoverValue?_one bodyScoped, assign, lookup] at binderMatched
  subst binderMatched
  simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, ambientBoundary, arguments?,
    dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?, lookup, instantiateValue?_one bodyScoped,
    instantiateValue?_shift nameScoped] at applied
  subst applied
  exact ⟨nameValue, binder, body, rfl, rfl⟩

/-- **Every reverse instance of the boundary law**: a restriction over an ambient whose name does not use the restricted
name becomes the ambient over the restriction, its name lowered past the binder. -/
theorem boundary_reverse_shape {ambient : Nat} {spec : RuleBindingSpec} {captured : Assignment}
    {source target : Pattern} (bound : (orientedRule ambientBoundary .reverse).bindings = some spec)
    (sourceScoped : source.isWellScopedAt ambient = true)
    (matched : captured ∈ matchRuleAt (orientedRule ambientBoundary .reverse) spec ambient source)
    (applied : reduct? (orientedRule ambientBoundary .reverse) spec ambient captured = some target) :
    ∃ (name : Pattern) (binder : Option String) (body : Pattern), name.isWellScopedAt ambient = true ∧
      source = .apply "ANu" [.lambda binder (.apply "AAmb" [liftBVars 0 1 name, body])] ∧
      target = .apply "AAmb" [name, .apply "ANu" [.lambda none body]] := by
  obtain rfl : spec = (orientedRule ambientBoundary .reverse).bindings.getD { dependencies := [] } := by
    rw [bound]; rfl
  simp only [matchRuleAt, matchRuleWithAt] at matched
  rw [show (orientedRule ambientBoundary .reverse).left =
      .apply "ANu" [.lambda none (.apply "AAmb" [.fvar "m", .fvar "P"])] from rfl, mem_matchAtWith_apply] at matched
  obtain ⟨arguments, rfl, matched⟩ := matched
  rw [mem_matchArgsAtWith_cons] at matched
  obtain ⟨abstraction, rest, afterAbstraction, rfl, binderMatched, matched⟩ := matched
  rw [mem_matchArgsAtWith_nil] at matched
  obtain ⟨rfl, rfl⟩ := matched
  rw [mem_matchAtWith_lambda] at binderMatched
  obtain ⟨binder, inner, rfl, binderMatched⟩ := binderMatched
  rw [mem_matchAtWith_apply] at binderMatched
  obtain ⟨ambientArguments, rfl, binderMatched⟩ := binderMatched
  rw [mem_matchArgsAtWith_cons] at binderMatched
  obtain ⟨nameValue, rest', afterName, rfl, nameMatched, binderMatched⟩ := binderMatched
  rw [mem_matchArgsAtWith_cons] at binderMatched
  obtain ⟨body, rest'', afterBody, rfl, bodyMatched, binderMatched⟩ := binderMatched
  rw [mem_matchArgsAtWith_nil] at binderMatched
  obtain ⟨rfl, rfl⟩ := binderMatched
  have argumentsScoped : Pattern.isWellScopedListAt (ambient + 1) [nameValue, body] = true := by
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using sourceScoped
  have bodyScoped : body.isWellScopedAt (1 + ambient) = true := by
    rw [Nat.add_comm]
    exact ((isWellScopedListAt_eq_true_iff _ _).mp argumentsScoped) _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [mem_matchAtWith_fvar, captureWith?_literal] at nameMatched
  simp only [capture?, orientedRule, ambientBoundary, Option.bind_eq_bind, Option.bind_eq_some_iff] at nameMatched
  obtain ⟨nameDependencies, nameDeclared, nameArguments, nameSupplied, value, nameRecovered, nameAssigned⟩ :=
    nameMatched
  simp [dependencies?, exchangeBindings, exchangeOccurrence, exchangeSite] at nameDeclared
  subst nameDeclared
  simp [dependencies?, arguments?, occurrenceDeclared, sitePattern?, occurrenceAt?, exchangeBindings,
    exchangeOccurrence, exchangeSite] at nameSupplied
  subst nameSupplied
  have nameContext := recoverValue?_context _ _ _ _ _ _ nameRecovered
  have nameForward := recoverValue?_forward _ _ _ _ _ _ nameRecovered
  obtain ⟨valueDependencies, valueAmbient, lowered⟩ := value
  simp only at nameContext
  obtain ⟨rfl, rfl⟩ := nameContext
  obtain ⟨loweredScoped, rfl⟩ := instantiateValue?_shift_inv nameForward
  simp [assign, lookup] at nameAssigned
  subst nameAssigned
  rw [mem_matchAtWith_fvar, captureWith?_literal] at bodyMatched
  simp [capture?, orientedRule, ambientBoundary, exchangeBindings, exchangeOccurrence, exchangeSite, dependencies?,
    arguments?, occurrenceDeclared, sitePattern?, occurrenceAt?, recoverValue?_one bodyScoped, assign, lookup]
    at bodyMatched
  subst bodyMatched
  simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, ambientBoundary,
    exchangeBindings, exchangeOccurrence, exchangeSite, arguments?, dependencies?, occurrenceDeclared, sitePattern?,
    occurrenceAt?, lookup, instantiateValue?_one bodyScoped, instantiateValue?_root loweredScoped] at applied
  subst applied
  exact ⟨lowered, binder, body, loweredScoped, rfl, rfl⟩

/-! ## Every instance of a law has a shape -/

open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationGenerator EquationInstanceAt DerivedInstance
  extendClosed_closedRoot readsRaw)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator PremisesAt)
open Mettapedia.OSLF.MeTTaIL.Match (applyBindings)
open Mettapedia.GSLT.LanguageDef.WellSorted (hasType_collection_inversion)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)

/-- **The laws of the ambient calculus**, one by one: those of its blocks with replication, and the boundary law. -/
theorem ambientLaws_cases {equation : Equation} (member : List.Mem equation ambientCoreCalc.equations) :
    equation = restrictionNilOf ambientBlock ∨ equation = restrictionExchangeOf ambientBlock ∨
      equation = scopeExtrusionOf ambientBlock ∨ equation = replicationUnfoldOf ambientRepBlock ∨
      equation = replicationNilOf ambientRepBlock ∨ equation = replicationTwiceOf ambientRepBlock ∨
      equation = replicationParOf ambientRepBlock ∨ equation = replicationIdempotentOf ambientRepBlock ∨
      equation = ambientBoundary := by
  have inList : equation ∈ ambientCoreCalc.equations := member
  simp only [ambientCoreCalc, replicationBlockLaws, blockLaws, replicationLaws, List.map_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at inList
  rcases inList with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr (.inl rfl))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))))

/-- **The shapes of the ambient calculus's laws**: those of its blocks with replication, and the boundary law, one
orientation each. -/
inductive AmbShape : Pattern → Pattern → Prop where
  | law {source target : Pattern} (shape : LawShape ambientRepBlock source target) : AmbShape source target
  | boundary (name : Pattern) (binder : Option String) (body : Pattern) :
      AmbShape (.apply "AAmb" [name, .apply "ANu" [.lambda binder body]])
        (.apply "ANu" [.lambda none (.apply "AAmb" [liftBVars 0 1 name, body])])
  | boundaryReverse (name : Pattern) (binder : Option String) (body : Pattern) :
      AmbShape (.apply "ANu" [.lambda binder (.apply "AAmb" [liftBVars 0 1 name, body])])
        (.apply "AAmb" [name, .apply "ANu" [.lambda none body]])

/-- **No side of a law is an abstraction.** -/
theorem AmbShape.notLambda {source target : Pattern} (shape : AmbShape source target) :
    (∀ binder body, source ≠ .lambda binder body) ∧ (∀ binder body, target ≠ .lambda binder body) := by
  cases shape with
  | law shape =>
      cases shape with
      | singleton notLambda => exact ⟨by simp, notLambda⟩
      | _ => constructor <;> simp
  | boundary => constructor <;> simp
  | boundaryReverse => constructor <;> simp

/-- **No law relates two variables**: its source is a constructor or a bag. -/
theorem AmbShape.notVariable {source target : Pattern} (shape : AmbShape source target) :
    (∀ index, source ≠ .bvar index) ∧ ∀ name, source ≠ .fvar name := by
  cases shape with
  | law shape => cases shape <;> exact ⟨by simp, by simp⟩
  | boundary => exact ⟨by simp, by simp⟩
  | boundaryReverse => exact ⟨by simp, by simp⟩

/-- **Every authored instance of a law of the ambient calculus has a shape**, one way or the other. -/
theorem ambient_instance_shape {base : BasePremiseEvaluator} {fuel : Nat} {source target : Pattern}
    (equationInstance : EquationInstanceAt base ambientCoreCalc fuel source target) :
    AmbShape source target ∨ AmbShape target source := by
  cases equationInstance with
  | forward member raw matched premises applied =>
      rcases ambientLaws_cases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨binder, rfl⟩ := restrictionNil_raw matched
        have targetIs : target = .apply "AZero" [] := by
          rw [← applied]
          simp [restrictionNilOf, applyBindings]
        subst targetIs
        exact .inl (.law (.restrictionNil binder))
      · exact absurd raw (by rw [exchange_raw]; decide)
      · exact absurd raw (by rw [extrusion_raw]; decide)
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨process, rfl, rfl⟩ := unfold_forward matched applied
        exact .inr (.law (.unfold process none))
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨rfl, rfl⟩ := nil_forward matched applied
        exact .inl (.law .replicationNil)
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨process, rfl, rfl⟩ := twice_forward matched applied
        exact .inl (.law (.twice process))
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨first, second, rest, shape, rfl⟩ := par_forward matched applied
        rcases shape with rfl | rfl
        · exact .inl (.law (.par first second rest false))
        · exact .inl (.law (.par first second rest true))
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨process, rest, rfl, rfl⟩ := idempotent_forward matched applied
        exact .inl (.law (.idempotent process rest))
      · exact absurd raw (by decide)
  | reverse member raw matched premises applied =>
      rcases ambientLaws_cases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [restrictionNil_raw_right matched]
        have targetIs : target = .apply "ANu" [.lambda none (.apply "AZero" [])] := by
          rw [← applied]
          simp [restrictionNilOf, applyBindings]
        subst targetIs
        exact .inr (.law (.restrictionNil none))
      · exact absurd raw (by rw [exchange_raw]; decide)
      · exact absurd raw (by rw [extrusion_raw]; decide)
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨process, rest, shape, rfl⟩ := unfold_reverse matched applied
        rcases shape with rfl | rfl
        · exact .inl (.law (.unfold process rest))
        · exact .inl (.law (.unfoldSwap process rest))
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨rfl, rfl⟩ := nil_reverse matched applied
        exact .inr (.law .replicationNil)
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨process, rfl, rfl⟩ := twice_reverse matched applied
        exact .inr (.law (.twice process))
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨first, second, rest, shape, rfl⟩ := par_reverse matched applied
        rcases shape with rfl | rfl
        · exact .inl (.law (.parReverse first second rest false))
        · exact .inl (.law (.parReverse first second rest true))
      · rw [final_of_premises_nil rfl premises] at applied
        obtain ⟨process, rfl, rfl⟩ := idempotent_reverse matched applied
        exact .inr (.law (.idempotent process none))
      · exact absurd raw (by decide)
  | @declared equation orientation ambient _ _ member notRaw declared =>
      obtain ⟨spec, captured, final, bound, _, sourceScoped, matched, premises, applied, _⟩ := declared
      rcases ambientLaws_cases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd notRaw (by simp [nil_raw])
      · have premisesNil : (restrictionExchangeOf ambientBlock).premises = [] := rfl
        rw [premisesNil] at premises
        cases premises
        rw [extendClosed_closedRoot] at applied
        cases orientation with
        | forward =>
            obtain ⟨outerBinder, innerBinder, body, rfl, rfl⟩ := exchange_forward_shape bound sourceScoped matched applied
            exact .inl (.law (.exchange outerBinder innerBinder body))
        | reverse =>
            obtain ⟨outerBinder, innerBinder, body, rfl, rfl⟩ := exchange_reverse_shape bound sourceScoped matched applied
            exact .inl (.law (.exchange outerBinder innerBinder body))
      · have premisesNil : (scopeExtrusionOf ambientBlock).premises = [] := rfl
        rw [premisesNil] at premises
        cases premises
        rw [extendClosed_closedRoot] at applied
        cases orientation with
        | forward =>
            obtain ⟨members, selected, binder, body, inside, chosen, rfl, rfl⟩ :=
              extrusion_forward_shape bound sourceScoped matched applied
            exact .inl (.law (.extrusion inside chosen))
        | reverse =>
            obtain ⟨binder, members, selected, originals, inside, erased, rfl, rfl⟩ :=
              extrusion_reverse_shape bound sourceScoped matched applied
            exact .inl (.law (.extrusionReverse inside erased))
      · exact absurd notRaw (by rw [Mettapedia.GSLT.LanguageDef.EquationSemantics.readsRaw_of_none rfl]; decide)
      · exact absurd notRaw (by rw [Mettapedia.GSLT.LanguageDef.EquationSemantics.readsRaw_of_none rfl]; decide)
      · exact absurd notRaw (by rw [Mettapedia.GSLT.LanguageDef.EquationSemantics.readsRaw_of_none rfl]; decide)
      · exact absurd notRaw (by rw [Mettapedia.GSLT.LanguageDef.EquationSemantics.readsRaw_of_none rfl]; decide)
      · exact absurd notRaw (by rw [Mettapedia.GSLT.LanguageDef.EquationSemantics.readsRaw_of_none rfl]; decide)
      · have premisesNil : ambientBoundary.premises = [] := rfl
        rw [premisesNil] at premises
        cases premises
        rw [extendClosed_closedRoot] at applied
        cases orientation with
        | forward =>
            obtain ⟨name, binder, body, rfl, rfl⟩ := boundary_forward_shape bound sourceScoped matched applied
            exact .inl (.boundary name binder body)
        | reverse =>
            obtain ⟨name, binder, body, -, rfl, rfl⟩ := boundary_reverse_shape bound sourceScoped matched applied
            exact .inl (.boundaryReverse name binder body)

/-- **Every law of the bag has a shape.** -/
theorem ambient_derived_shape {source target : Pattern} (derived : DerivedInstance ambientCoreCalc source target) :
    LawShape ambientRepBlock source target := by
  cases derived with
  | bagPerm _ _ permutation => exact .bagPerm permutation
  | setPerm member typed => exact absurd typed (coreSignature.no_set_rule member)
  | setDedup member typed => exact absurd typed (coreSignature.no_set_rule member)
  | @flatten rule kind algebra pre inner post algebraRule _ _ =>
      obtain ⟨rfl, _⟩ := coreSignature.algebra_shape algebraRule
      exact .flatten pre inner post
  | @singleton rule kind algebra element algebraRule _ sorted =>
      obtain ⟨rfl, _⟩ := coreSignature.algebra_shape algebraRule
      refine .singleton fun binder body equal => ?_
      subst equal
      obtain ⟨free, bound, typed⟩ := sorted
      rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
        ⟨rule', _, _, member', shape, _, elementsTyped⟩
      · cases typeIs
      · obtain ⟨_, rfl, _⟩ := coreSignature.bare_shape member' shape
        have lambdaTyped := elementsHaveType_iff.mp elementsTyped _ List.mem_cons_self
        cases lambdaTyped
  | @unitElim rule kind algebra unit pre post algebraRule unitIs _ =>
      obtain ⟨rfl, named⟩ := coreSignature.algebra_shape algebraRule
      rw [unitIs, Option.some.injEq] at named
      subst named
      exact .unitElim pre post
  | @emptyUnit rule kind algebra unit algebraRule unitIs _ =>
      obtain ⟨rfl, named⟩ := coreSignature.algebra_shape algebraRule
      rw [unitIs, Option.some.injEq] at named
      subst named
      exact .emptyBag

/-- **Every generator of the ambient calculus's static theory has a shape**, one way or the other. -/
theorem ambient_generator_shape {base : BasePremiseEvaluator} {source target : Pattern}
    (generator : EquationGenerator base ambientCoreCalc source target) :
    AmbShape source target ∨ AmbShape target source := by
  rcases generator with ⟨_, equationInstance⟩ | derived
  · exact ambient_instance_shape equationInstance
  · exact .inl (.law (ambient_derived_shape derived))

/-! ## The reference relation reads the same laws -/

open Mettapedia.OSLF.MeTTaIL.ReferenceStep (AuthoredEquation captureSitesOf notDeeper notDeeperList
  applyBindingsScoped_eq_applyBindings_of_notDeeper)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationInstance EquationContextStep readsRaw
  declaredInstanceAt_iff_applyEquationAt)
open Mettapedia.OSLF.MeTTaIL.Match (captureDepth captureDepthList)

/-- Every law of the ambient calculus has no premise. -/
theorem ambient_premises_nil {equation : Equation} (member : equation ∈ ambientCoreCalc.equations) :
    equation.premises = [] := by
  rcases ambientLaws_cases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **A raw law of the ambient calculus instantiates its other side plainly**: no metavariable sits under a binder. -/
theorem ambient_raw_notDeeper {equation : Equation} (member : equation ∈ ambientCoreCalc.equations)
    (raw : readsRaw equation = true) :
    notDeeper (captureSitesOf equation.left equation.premises) 0 equation.right = true ∧
      notDeeper (captureSitesOf equation.right equation.premises) 0 equation.left = true := by
  rcases ambientLaws_cases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · constructor <;> simp [restrictionNilOf, notDeeper, notDeeperList]
  · exact absurd raw (by rw [exchange_raw]; decide)
  · exact absurd raw (by rw [extrusion_raw]; decide)
  · constructor <;> simp [replicationUnfoldOf, notDeeper, notDeeperList, captureSitesOf, captureDepth,
      captureDepthList]
  · constructor <;> simp [replicationNilOf, notDeeper, notDeeperList, captureSitesOf]
  · constructor <;> simp [replicationTwiceOf, notDeeper, notDeeperList, captureSitesOf, captureDepth,
      captureDepthList]
  · constructor <;> simp [replicationParOf, notDeeper, notDeeperList, captureSitesOf, captureDepth, captureDepthList]
  · constructor <;> simp [replicationIdempotentOf, notDeeper, notDeeperList, captureSitesOf, captureDepth,
      captureDepthList]
  · exact absurd raw (by decide)

/-- **The laws of the ambient calculus are plain**, in any language with them: none has premises, and a raw one
instantiates its other side plainly. -/
theorem ambient_plain {language : LanguageDef} (laws : language.equations = ambientCoreCalc.equations) :
    PlainLaws language :=
  ⟨fun _ member => ambient_premises_nil (laws ▸ member),
    fun _ member raw => ambient_raw_notDeeper (laws ▸ member) raw⟩

/-! ## The laws of replication -/



end Mettapedia.Languages.ProcessCalculi.Ambient.Full
