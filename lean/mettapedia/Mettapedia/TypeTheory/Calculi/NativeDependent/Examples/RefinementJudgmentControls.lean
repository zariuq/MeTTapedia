import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementHeaderFormation

/-!
# Conditional refinements, higher-order predicates and dependent suffixes

The independently declared fibre has a scalar parameter. A transported suffix
retains that actual parameter after replacing its old variable by a forgotten
refined value. Further function variables and proposition assumptions remain
in scope. Duplicate proposition assumptions have distinct proof-tree readouts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Controls

inductive TypeSymbol where
  | scalar
  | fibre

inductive PredicateSymbol where
  | positive

def symbols : Symbols where
  TypeSymbol := TypeSymbol
  TermSymbol := Empty
  PredicateSymbol := PredicateSymbol
  typeArity
    | .scalar => 0
    | .fibre => 1
  termArity := Empty.elim
  predicateArity := fun _ => 1

def scalar (n : Nat) : TypeExpr symbols n := .family .scalar Fin.elim0

def singletonArgument {n : Nat} (value : TermExpr symbols n) : Substitution symbols 1 n :=
  extendSubstitution Fin.elim0 value

def fibre (n : Nat) : TypeExpr symbols (n + 1) :=
  .family .fibre (singletonArgument (.var 0))

def positive (n : Nat) : PropExpr symbols (n + 1) :=
  .atom .positive (singletonArgument (.var 0))

def signature : Signature symbols where
  typeRank
    | .scalar => 0
    | .fibre => 1
  termRank := Empty.elim
  predicateRank := fun _ => 2
  typeParameters
    | .scalar => .nil
    | .fibre => .snoc .nil (scalar 0)
  termParameters := fun symbol => nomatch symbol
  predicateParameters := fun _ => .snoc .nil (scalar 0)
  termResult := fun symbol => nomatch symbol
  typeParameters_before := by
    intro symbol
    cases symbol <;> simp [ContextExpr.before, TypeExpr.before, scalar, symbols]
  termParameters_before := fun symbol => Empty.elim symbol
  predicateParameters_before := by
    intro symbol
    cases symbol
    simp [ContextExpr.before, TypeExpr.before, scalar, symbols]
  termResult_before := fun symbol => Empty.elim symbol

@[simp] theorem scalar_rename {n m : Nat} (mapping : Renaming n m) :
    (scalar n).rename mapping = scalar m := by
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.scalar)
  funext position
  exact Fin.elim0 position

@[simp] theorem scalar_substitute {n m : Nat} (substitution : Substitution symbols n m) :
    (scalar n).substitute substitution = scalar m := by
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.scalar)
  funext position
  exact Fin.elim0 position

def emptyContext : Derivation signature (.context .nil) := deriveList .contextNil .nil

def extendContext {n : Nat} {context : ContextExpr symbols n} {type : TypeExpr symbols n}
    (formed : Derivation signature (.context context)) (typeTree : Derivation signature (.type context type)) :
    Derivation signature (.context (.snoc context type)) :=
  deriveList (.contextExtend context type) (.cons formed (.cons typeTree .nil))

def scalarFormed {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) : Derivation signature (.type context (scalar n)) :=
  deriveList (.typeFamily context .scalar Fin.elim0)
    (.cons formed (.cons emptyContext
      (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil)))

def scalarContext : Derivation signature (.context (.snoc .nil (scalar 0))) :=
  extendContext emptyContext (scalarFormed emptyContext)

theorem emptyContext_before (bound : Nat) : emptyContext.before bound :=
  deriveList_before .contextNil .nil bound True.intro True.intro

theorem scalarFormed_before {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) (bound : Nat)
    (ordered : formed.before bound) (scalarRank : 0 < bound) :
    (scalarFormed formed).before bound := by
  have sourceOrder := formed.before_judgment ordered
  have nilArrowOrder : (deriveList (.substitutionNil context) (.cons formed .nil)).before bound :=
    deriveList_before (.substitutionNil context) (.cons formed .nil) bound
      ⟨sourceOrder, True.intro, fun index => Fin.elim0 index⟩ ⟨ordered, True.intro⟩
  exact deriveList_before (.typeFamily context .scalar Fin.elim0) _ bound
    ⟨sourceOrder, scalarRank, fun index => Fin.elim0 index⟩
      ⟨ordered, emptyContext_before bound, nilArrowOrder, True.intro⟩

theorem scalarContext_before (bound : Nat) (scalarRank : 0 < bound) :
    scalarContext.before bound :=
  deriveList_before (.contextExtend .nil (scalar 0)) _ bound
    ⟨True.intro, scalarRank, fun index => Fin.elim0 index⟩
    ⟨emptyContext_before bound,
      scalarFormed_before emptyContext bound (emptyContext_before bound) scalarRank, True.intro⟩

def headerFormation : HeaderFormation signature where
  typeHeader
    | .scalar => emptyContext
    | .fibre => scalarContext
  typeHeader_before := by
    intro symbol
    cases symbol with
    | scalar => exact emptyContext_before 0
    | fibre => exact scalarContext_before 1 (by decide)
  termHeader := fun symbol => nomatch symbol
  termHeader_before := fun symbol => Empty.elim symbol
  termResult := fun symbol => nomatch symbol
  termResult_before := fun symbol => Empty.elim symbol
  predicateHeader := fun _ => scalarContext
  predicateHeader_before := by
    intro symbol
    cases symbol
    exact scalarContext_before 2 (by decide)

theorem scalar_cannot_be_an_earlier_rank_zero_declaration :
    ¬ (scalar 0).before signature.typeRank signature.termRank signature.predicateRank 0 :=
  TypeExpr.family_not_before_zero _ _ _ _ _

def lookupVariable {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) (index : Fin n) :
    Derivation signature (.term context (.var index) (context.lookup index)) :=
  deriveList (.variable context index) (.cons formed .nil)

def scalarArguments {n : Nat} {context : ContextExpr symbols n} {value : TermExpr symbols n}
    (formed : Derivation signature (.context context))
    (typed : Derivation signature (.term context value (scalar n))) :
    Derivation signature (.substitution context (.snoc .nil (scalar 0)) (singletonArgument value)) := by
  have valueTree : Derivation signature (.term context value ((scalar 0).substitute Fin.elim0)) := by
    simpa only [scalar_substitute] using typed
  exact deriveList (.substitutionExtend context .nil (scalar 0) Fin.elim0 value)
    (.cons (deriveList (.substitutionNil context) (.cons formed .nil))
      (.cons (scalarFormed emptyContext) (.cons valueTree .nil)))

def positiveFormed {n : Nat} {context : ContextExpr symbols n} {value : TermExpr symbols n}
    (formed : Derivation signature (.context context))
    (typed : Derivation signature (.term context value (scalar n))) :
    Derivation signature (.predicate context (.atom .positive (singletonArgument value))) :=
  deriveList (.predicatePrimitive context .positive (singletonArgument value))
    (.cons formed (.cons scalarContext (.cons (scalarArguments formed typed) .nil)))

def fibreFormed {n : Nat} {context : ContextExpr symbols n} {value : TermExpr symbols n}
    (formed : Derivation signature (.context context))
    (typed : Derivation signature (.term context value (scalar n))) :
    Derivation signature (.type context (.family .fibre (singletonArgument value))) :=
  deriveList (.typeFamily context .fibre (singletonArgument value))
    (.cons formed (.cons scalarContext (.cons (scalarArguments formed typed) .nil)))

def assumeEntails {n : Nat} {context : ContextExpr symbols n} {predicate : PropExpr symbols n}
    (formed : Derivation signature (.context context))
    (predicateTree : Derivation signature (.predicate context predicate)) :
    Derivation signature (.entails (.assume context predicate) predicate) := by
  let assumed := deriveList (.contextAssume context predicate) (.cons formed (.cons predicateTree .nil))
  let weakening := deriveList (.substitutionWeakenAssumption context predicate) (.cons predicateTree .nil)
  have newPredicate : Derivation signature (.predicate (.assume context predicate) predicate) := by
    simpa only [RuleCode.conclusion, PropExpr.substitute_identity] using
      deriveList (.substitutePredicate (.assume context predicate) context TermExpr.var predicate)
        (.cons weakening (.cons predicateTree .nil))
  exact deriveList (.hypothesis (.assume context predicate) predicate (.here context predicate))
    (.cons assumed (.cons newPredicate .nil))

def positiveVariable : Derivation signature (.predicate (.snoc .nil (scalar 0)) (positive 0)) := by
  have typed : Derivation signature (.term (.snoc .nil (scalar 0)) (.var 0) (scalar 1)) := by
    simpa only [ContextExpr.lookup_zero, scalar_rename] using lookupVariable scalarContext 0
  exact positiveFormed scalarContext typed

def conditionalContext : ContextExpr symbols 1 := .assume (.snoc .nil (scalar 0)) (positive 0)

def conditionalContextFormed : Derivation signature (.context conditionalContext) :=
  deriveList (.contextAssume (.snoc .nil (scalar 0)) (positive 0))
    (.cons scalarContext (.cons positiveVariable .nil))

def conditionalVariable : Derivation signature (.term conditionalContext (.var 0) (scalar 1)) := by
  simpa only [conditionalContext, ContextExpr.lookup_assume, ContextExpr.lookup_zero, scalar_rename] using
    lookupVariable conditionalContextFormed 0

def conditionalPredicate : Derivation signature
    (.predicate (.snoc conditionalContext (scalar 1)) (positive 1)) := by
  let formed := extendContext conditionalContextFormed (scalarFormed conditionalContextFormed)
  have typed : Derivation signature (.term (.snoc conditionalContext (scalar 1)) (.var 0) (scalar 2)) := by
    simpa only [ContextExpr.lookup_zero, scalar_rename] using lookupVariable formed 0
  exact positiveFormed formed typed

theorem positive_instantiate_variable (n : Nat) :
    (positive (n + 1)).substitute (instantiate (.var 0)) = positive n := by
  apply congrArg (PropExpr.atom (S := symbols) PredicateSymbol.positive)
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ impossible => exact Fin.elim0 impossible

def conditionalGuard : Derivation signature
    (.entails conditionalContext ((positive 1).substitute (instantiate (.var 0)))) := by
  rw [positive_instantiate_variable]
  exact assumeEntails scalarContext positiveVariable

def conditionalRefinement : Derivation signature (.term conditionalContext
    (.refine (scalar 1) (positive 1) (.var 0)) (.comprehension (scalar 1) (positive 1))) :=
  deriveList (.comprehensionIntroduction conditionalContext (scalar 1) (positive 1) (.var 0))
    (.cons (scalarFormed conditionalContextFormed) (.cons conditionalPredicate
      (.cons conditionalVariable (.cons conditionalGuard .nil))))

def conditionalBeta : Derivation signature (.termEq conditionalContext
    (.forget (scalar 1) (positive 1) (.refine (scalar 1) (positive 1) (.var 0)))
    (.var 0) (scalar 1)) :=
  deriveList (.comprehensionBeta conditionalContext (scalar 1) (positive 1) (.var 0))
    (.cons (scalarFormed conditionalContextFormed) (.cons conditionalPredicate
      (.cons conditionalVariable (.cons conditionalGuard .nil))))

def conditionalEta : Derivation signature (.termEq conditionalContext
    (.refine (scalar 1) (positive 1)
      (.forget (scalar 1) (positive 1) (.refine (scalar 1) (positive 1) (.var 0))))
    (.refine (scalar 1) (positive 1) (.var 0)) (.comprehension (scalar 1) (positive 1))) :=
  deriveList (.comprehensionEta conditionalContext (scalar 1) (positive 1)
    (.refine (scalar 1) (positive 1) (.var 0)))
      (.cons (scalarFormed conditionalContextFormed) (.cons conditionalPredicate
        (.cons conditionalRefinement .nil)))

def dependentSuffix : ContextSuffix symbols 1 1 := .snoc .nil (fibre 0)

def dependentSuffixFormed : SuffixFormation signature (.snoc .nil (scalar 0)) dependentSuffix := by
  have typed : Derivation signature (.term (.snoc .nil (scalar 0)) (.var 0) (scalar 1)) := by
    simpa only [ContextExpr.lookup_zero, scalar_rename] using lookupVariable scalarContext 0
  exact .snoc (.nil scalarContext) (fibre 0) (fibreFormed scalarContext typed)

def predicateFunction : TypeExpr symbols 2 := .pi (scalar 2) .propositions

def predicateFunctionFormed : Derivation signature
    (.type (dependentSuffix.plug (.snoc .nil (scalar 0))) predicateFunction) :=
  deriveList (.piFormation _ (scalar 2) .propositions)
    (.cons (scalarFormed dependentSuffixFormed.context)
      (.cons (deriveList (.propositionType _)
        (.cons (extendContext dependentSuffixFormed.context
          (scalarFormed dependentSuffixFormed.context)) .nil)) .nil))

def mixedSuffix : ContextSuffix symbols 1 2 :=
  .assume (.snoc dependentSuffix predicateFunction) .truth

def mixedSuffixFormed : SuffixFormation signature (.snoc .nil (scalar 0)) mixedSuffix :=
  .assume (.snoc dependentSuffixFormed predicateFunction predicateFunctionFormed) .truth
    (deriveList (.truthFormation _)
      (.cons (extendContext dependentSuffixFormed.context predicateFunctionFormed) .nil))

def finalGuard : PropExpr symbols 3 := (positive 0).rename (weakenRenaming 2)

def finalGuardFormed : Derivation signature
    (.predicate (mixedSuffix.plug (.snoc .nil (scalar 0))) finalGuard) := by
  simpa only [RuleCode.conclusion, PropExpr.substitute_variables, finalGuard] using
    deriveList (.substitutePredicate _ _ (fun index => .var (weakenRenaming 2 index)) (positive 0))
      (.cons mixedSuffixFormed.projection (.cons positiveVariable .nil))

/-- The complete raw suffix is transported by an actual generated substitution. -/
def fullSuffixGuard : Derivation signature (.entails
    ((mixedSuffix.substitute (comprehensionProjection (scalar 0) (positive 0))).plug
      (.snoc .nil (.comprehension (scalar 0) (positive 0))))
    (finalGuard.substitute (liftSubstitutionN (comprehensionProjection (scalar 0) (positive 0)) 2))) :=
  comprehensionAssumptionElimination emptyContext (scalarFormed emptyContext) positiveVariable
    mixedSuffixFormed (assumeEntails mixedSuffixFormed.context finalGuardFormed)

theorem transported_fibre_parameter :
    (fibre 0).substitute (comprehensionProjection (scalar 0) (positive 0)) =
      .family .fibre (singletonArgument
        (.forget ((scalar 0).rename Fin.succ)
          ((positive 0).rename (liftRenaming Fin.succ)) (.var 0))) := by
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.fibre)
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ impossible => exact Fin.elim0 impossible

theorem transported_parameter_is_not_old_variable :
    comprehensionProjection (scalar 0) (positive 0) 0 ≠ (.var 0 : TermExpr symbols 1) := by
  intro equal
  cases equal

def duplicateContext : ContextExpr symbols 1 := .assume conditionalContext (positive 0)

def conditionalGuardFormed : Derivation signature (.predicate conditionalContext (positive 0)) := by
  simpa only [RuleCode.conclusion, PropExpr.substitute_identity] using
    deriveList (.substitutePredicate conditionalContext (.snoc .nil (scalar 0)) TermExpr.var (positive 0))
      (.cons (deriveList (.substitutionWeakenAssumption (.snoc .nil (scalar 0)) (positive 0))
        (.cons positiveVariable .nil)) (.cons positiveVariable .nil))

def duplicateContextFormed : Derivation signature (.context duplicateContext) :=
  deriveList (.contextAssume conditionalContext (positive 0))
    (.cons conditionalContextFormed (.cons conditionalGuardFormed .nil))

def duplicateGuardFormed : Derivation signature (.predicate duplicateContext (positive 0)) := by
  simpa only [RuleCode.conclusion, PropExpr.substitute_identity] using
    deriveList (.substitutePredicate duplicateContext conditionalContext TermExpr.var (positive 0))
      (.cons (deriveList (.substitutionWeakenAssumption conditionalContext (positive 0))
        (.cons conditionalGuardFormed .nil)) (.cons conditionalGuardFormed .nil))

def newestAssumption : Derivation signature (.entails duplicateContext (positive 0)) :=
  deriveList (.hypothesis duplicateContext (positive 0) (.here conditionalContext (positive 0)))
    (.cons duplicateContextFormed (.cons duplicateGuardFormed .nil))

def olderAssumption : Derivation signature (.entails duplicateContext (positive 0)) :=
  deriveList (.hypothesis duplicateContext (positive 0)
    (.assumptionThere (.here (.snoc .nil (scalar 0)) (positive 0)) (positive 0)))
      (.cons duplicateContextFormed (.cons duplicateGuardFormed .nil))

theorem assumption_trees_retain_positions : newestAssumption ≠ olderAssumption := by
  intro equal
  have impossible := congrArg Derivation.rootAssumptionPosition equal
  cases impossible

def firstClassPredicateQuote : Derivation signature (.term (.snoc .nil (scalar 0))
    (.quote (positive 0)) .propositions) :=
  deriveList (.quote _ _) (.cons positiveVariable .nil)

def firstClassPredicateReadback : Derivation signature (.predicateEq (.snoc .nil (scalar 0))
    (.holds (.quote (positive 0))) (positive 0)) :=
  deriveList (.holdsQuote _ _) (.cons positiveVariable .nil)

def predicateSelfImplication {n : Nat} {context : ContextExpr symbols n} {predicate : PropExpr symbols n}
    (formed : Derivation signature (.context context))
    (predicateTree : Derivation signature (.predicate context predicate)) :
    Derivation signature (.entails context (.implies predicate predicate)) :=
  deriveList (.implicationIntroduction context predicate predicate)
    (.cons predicateTree (.cons predicateTree (.cons (assumeEntails formed predicateTree) .nil)))

/-- Propositions are actual quantified data, rather than an implicit semantic index. -/
def quantifiedProposition : Derivation signature (.entails .nil
    (.all .propositions (.implies (.holds (.var 0)) (.holds (.var 0))))) := by
  let omega := deriveList (.propositionType (.nil : ContextExpr symbols 0)) (.cons emptyContext .nil)
  let context := extendContext emptyContext omega
  let predicate := deriveList (.holdsFormation (.snoc .nil .propositions) (.var 0))
    (.cons (lookupVariable context 0) .nil)
  exact deriveList (.universalIntroduction .nil .propositions
      (.implies (.holds (.var 0)) (.holds (.var 0))))
    (.cons omega (.cons (deriveList (.implicationFormation _ _ _) (.cons predicate (.cons predicate .nil)))
      (.cons (predicateSelfImplication context predicate) .nil)))

def predicateFunctionAt (n : Nat) : TypeExpr symbols n := .pi (scalar n) .propositions

def predicateFunctionAtFormed {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.type context (predicateFunctionAt n)) :=
  deriveList (.piFormation context (scalar n) .propositions)
    (.cons (scalarFormed formed)
      (.cons (deriveList (.propositionType _)
        (.cons (extendContext formed (scalarFormed formed)) .nil)) .nil))

def functionScope : ContextExpr symbols 1 := .snoc .nil (predicateFunctionAt 0)

def functionArgumentScope : ContextExpr symbols 2 := .snoc functionScope (scalar 1)

def appliedPredicate : PropExpr symbols 2 :=
  .holds (.app (scalar 2) .propositions (.var 1) (.var 0))

def functionScopeFormed : Derivation signature (.context functionScope) :=
  extendContext emptyContext (predicateFunctionAtFormed emptyContext)

def functionArgumentScopeFormed : Derivation signature (.context functionArgumentScope) :=
  extendContext functionScopeFormed (scalarFormed functionScopeFormed)

def appliedPredicateFormed : Derivation signature (.predicate functionArgumentScope appliedPredicate) := by
  have function : Derivation signature (.term functionArgumentScope (.var 1) (predicateFunctionAt 2)) := by
    have position : Fin.succ (0 : Fin 1) = (1 : Fin 2) := rfl
    rw [← position]
    simpa only [functionArgumentScope, functionScope, ContextExpr.lookup_succ, ContextExpr.lookup_zero,
      predicateFunctionAt, TypeExpr.rename, scalar_rename] using
        lookupVariable functionArgumentScopeFormed (Fin.succ (0 : Fin 1))
  have argument : Derivation signature (.term functionArgumentScope (.var 0) (scalar 2)) := by
    simpa only [functionArgumentScope, ContextExpr.lookup_zero, scalar_rename] using
      lookupVariable functionArgumentScopeFormed 0
  let application := deriveList (.application functionArgumentScope (scalar 2) .propositions (.var 1) (.var 0))
    (.cons (scalarFormed functionArgumentScopeFormed)
      (.cons (deriveList (.propositionType _)
        (.cons (extendContext functionArgumentScopeFormed (scalarFormed functionArgumentScopeFormed)) .nil))
          (.cons function (.cons argument .nil))))
  exact deriveList (.holdsFormation functionArgumentScope
    (.app (scalar 2) .propositions (.var 1) (.var 0))) (.cons application .nil)

/-- A function-valued predicate is quantified and applied to a separately
bound scalar argument. Its formation comes from the generated Pi rules. -/
def quantifiedPredicateFunction : Derivation signature (.entails .nil
    (.all (predicateFunctionAt 0)
      (.all (scalar 1) (.implies appliedPredicate appliedPredicate)))) := by
  let bodyFormation := deriveList (.implicationFormation functionArgumentScope appliedPredicate appliedPredicate)
    (.cons appliedPredicateFormed (.cons appliedPredicateFormed .nil))
  let argumentUniversal := deriveList (.universalIntroduction functionScope (scalar 1)
      (.implies appliedPredicate appliedPredicate))
    (.cons (scalarFormed functionScopeFormed) (.cons bodyFormation
      (.cons (predicateSelfImplication functionArgumentScopeFormed appliedPredicateFormed) .nil)))
  let universalFormation := deriveList (.universalFormation functionScope (scalar 1)
    (.implies appliedPredicate appliedPredicate))
      (.cons (scalarFormed functionScopeFormed) (.cons bodyFormation .nil))
  exact deriveList (.universalIntroduction .nil (predicateFunctionAt 0)
    (.all (scalar 1) (.implies appliedPredicate appliedPredicate)))
      (.cons (predicateFunctionAtFormed emptyContext)
        (.cons universalFormation (.cons argumentUniversal .nil)))

def truthPredicate {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.predicate context .truth) :=
  deriveList (.truthFormation context) (.cons formed .nil)

def truthEntailment {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.entails context .truth) :=
  deriveList (.truthIntroduction context) (.cons formed .nil)

def doubleTruthPredicate {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.predicate context (.and .truth .truth)) :=
  deriveList (.conjunctionFormation context .truth .truth)
    (.cons (truthPredicate formed) (.cons (truthPredicate formed) .nil))

def doubleTruthEntailment {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.entails context (.and .truth .truth)) :=
  deriveList (.conjunctionIntroduction context .truth .truth)
    (.cons (truthEntailment formed) (.cons (truthEntailment formed) .nil))

def truthDoubleTruthEquality {n : Nat} {context : ContextExpr symbols n}
    (formed : Derivation signature (.context context)) :
    Derivation signature (.predicateEq context .truth (.and .truth .truth)) :=
  deriveList (.predicateExtensionality context .truth (.and .truth .truth))
    (.cons (truthPredicate formed) (.cons (doubleTruthPredicate formed)
      (.cons (doubleTruthEntailment
        (deriveList (.contextAssume context .truth)
          (.cons formed (.cons (truthPredicate formed) .nil))))
      (.cons (truthEntailment
        (deriveList (.contextAssume context (.and .truth .truth))
          (.cons formed (.cons (doubleTruthPredicate formed) .nil)))) .nil))))

def annotationRefinement : Derivation signature
    (.termEq (.snoc .nil (scalar 0))
      (.refine (scalar 1) .truth (.var 0))
      (.refine (scalar 1) (.and .truth .truth) (.var 0))
      (.comprehension (scalar 1) .truth)) := by
  let formedExtension := extendContext scalarContext (scalarFormed scalarContext)
  have value : Derivation signature (.term (.snoc .nil (scalar 0)) (.var 0) (scalar 1)) := by
    simpa only [ContextExpr.lookup_zero, scalar_rename] using lookupVariable scalarContext 0
  have firstGuard : Derivation signature (.entails (.snoc .nil (scalar 0))
      ((PropExpr.truth : PropExpr symbols 2).substitute (instantiate (.var 0)))) :=
    truthEntailment scalarContext
  have secondGuard : Derivation signature (.entails (.snoc .nil (scalar 0))
      ((PropExpr.and .truth .truth : PropExpr symbols 2).substitute (instantiate (.var 0)))) :=
    doubleTruthEntailment scalarContext
  exact deriveList (.refineAnnotationCongruence _ (scalar 1) (scalar 1)
    .truth (.and .truth .truth) (.var 0) (.var 0))
      (.cons (deriveList (.typeReflexivity _ (scalar 1)) (.cons (scalarFormed scalarContext) .nil))
        (.cons (truthDoubleTruthEquality formedExtension)
          (.cons (doubleTruthPredicate formedExtension)
            (.cons (deriveList (.termReflexivity _ (.var 0) (scalar 1)) (.cons value .nil))
              (.cons value (.cons firstGuard (.cons secondGuard .nil)))))))

theorem annotation_refinement_raw_subjects_differ :
    (TermExpr.refine (scalar 1) .truth (.var 0) : TermExpr symbols 1) ≠
      .refine (scalar 1) (.and .truth .truth) (.var 0) := by
  intro same
  have predicates := (TermExpr.refine.inj same).2.1
  cases predicates

/-- Separate inverse equations leave the cross-presentation reading open. -/
def inversePresentationZero : Bool → Bool := id

def inversePresentationOne : Bool → Bool := Bool.not

theorem each_refinement_presentation_has_beta_eta (value : Bool) :
    inversePresentationZero (inversePresentationZero value) = value ∧
      inversePresentationOne (inversePresentationOne value) = value := by
  cases value <;> decide

theorem separate_beta_eta_do_not_fix_annotation_readout :
    inversePresentationZero true ≠ inversePresentationOne true := by decide

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Controls
