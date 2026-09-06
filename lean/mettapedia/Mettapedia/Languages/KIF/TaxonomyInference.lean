import Mettapedia.GSLT.Core.GSLT
import Mettapedia.Languages.KIF.DeclarationDecode
import Mettapedia.Logic.Derivation

/-!
# Certified taxonomy inference for decoded SUO-KIF

This module gives the decoded `subclass` and `instance` fragment an explicit
native inference calculus.  Source assertions are leaves; subclass
transitivity and inheritance of instances are the two derived rules.  A
Boolean replay interface checks finite certificate trees, while a separate
set-theoretic interpretation proves every accepted derivation sound.

The calculus is deliberately named for the fragment it implements.  It is not
a claim to cover SUO-KIF quantifiers, functions, modal operators, or the full
SUMO rule set.  It is a first source-derived operational slice on which those
layers can be added without confusing parsing, declarations, inference, and
model theory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.KIF.TaxonomyInference

open Mettapedia.GSLT
open Mettapedia.Logic
open Mettapedia.Languages.KIF

universe uName uEntity

/-- The two source judgments admitted by the taxonomy slice. -/
inductive TaxonomyFact (Name : Type uName) : Type uName
  | subclass (child parent : Name)
  | instance (individual className : Name)
  deriving DecidableEq, Repr

/-- Extract symbol-to-symbol taxonomy facts from decoded declarations.
Class-valued function terms remain in the declaration inventory and are not
silently coerced to names. -/
def factsFromDeclarations (declarations : List SuoDeclaration) :
    List (TaxonomyFact String) :=
  declarations.filterMap fun
    | .subclass child parent =>
        parent.asSymbol?.map fun parentName =>
          .subclass child.text parentName.text
    | .instance individual className =>
        some (.instance individual.text className.text)
    | _ => none

/-- Source leaves, transitive subclass inference, and upward inheritance of
instances along a subclass edge. -/
inductive TaxonomyRule {Name : Type uName}
    (source : List (TaxonomyFact Name)) :
    List (TaxonomyFact Name) → TaxonomyFact Name → Prop
  | source {fact : TaxonomyFact Name} (member : fact ∈ source) :
      TaxonomyRule source [] fact
  | subclassTrans (child middle parent : Name) :
      TaxonomyRule source
        [.subclass child middle, .subclass middle parent]
        (.subclass child parent)
  | instanceInheritance (individual child parent : Name) :
      TaxonomyRule source
        [.instance individual child, .subclass child parent]
        (.instance individual parent)

/-- Replay data for one taxonomy rule.  Every name needed to reconstruct the
premises and conclusion is stored in the certificate. -/
inductive TaxonomyWitness (Name : Type uName) : Type uName
  | source (fact : TaxonomyFact Name)
  | subclassTrans (child middle parent : Name)
  | instanceInheritance (individual child parent : Name)
  deriving DecidableEq, Repr

namespace TaxonomyWitness

variable {Name : Type uName}

def premises : TaxonomyWitness Name → List (TaxonomyFact Name)
  | .source _ => []
  | .subclassTrans child middle parent =>
      [.subclass child middle, .subclass middle parent]
  | .instanceInheritance individual child parent =>
      [.instance individual child, .subclass child parent]

def conclusion : TaxonomyWitness Name → TaxonomyFact Name
  | .source fact => fact
  | .subclassTrans child _middle parent => .subclass child parent
  | .instanceInheritance individual _child parent => .instance individual parent

def authorized [DecidableEq Name]
    (source : List (TaxonomyFact Name)) : TaxonomyWitness Name → Bool
  | .source fact => source.contains fact
  | .subclassTrans _ _ _ => true
  | .instanceInheritance _ _ _ => true

end TaxonomyWitness

variable {Name : Type uName}

/-- Boolean replay for one displayed taxonomy rule. -/
def checkRuleInstance (source : List (TaxonomyFact Name))
    [DecidableEq Name]
    (witness : TaxonomyWitness Name)
    (premises : List (TaxonomyFact Name))
    (conclusion : TaxonomyFact Name) : Bool :=
  decide (premises = witness.premises) &&
    decide (conclusion = witness.conclusion) &&
    witness.authorized source

theorem checkRuleInstance_sound
    [DecidableEq Name]
    (source : List (TaxonomyFact Name))
    (witness : TaxonomyWitness Name)
    (premises : List (TaxonomyFact Name))
    (conclusion : TaxonomyFact Name)
    (accepted : checkRuleInstance source witness premises conclusion = true) :
    TaxonomyRule source premises conclusion := by
  simp only [checkRuleInstance, Bool.and_eq_true, decide_eq_true_eq] at accepted
  rcases accepted with ⟨⟨premisesEqual, conclusionEqual⟩, authorized⟩
  subst premises
  subst conclusion
  cases witness with
  | source fact =>
      have member : fact ∈ source := by
        simpa [TaxonomyWitness.authorized] using authorized
      simpa [TaxonomyWitness.premises, TaxonomyWitness.conclusion] using
        (TaxonomyRule.source (source := source) member)
  | subclassTrans child middle parent =>
      exact .subclassTrans child middle parent
  | instanceInheritance individual child parent =>
      exact .instanceInheritance individual child parent

theorem checkRuleInstance_complete
    [DecidableEq Name]
    (source : List (TaxonomyFact Name))
    (premises : List (TaxonomyFact Name))
    (conclusion : TaxonomyFact Name)
    (rule : TaxonomyRule source premises conclusion) :
    ∃ witness, checkRuleInstance source witness premises conclusion = true := by
  cases rule with
  | source member =>
      exact ⟨.source conclusion, by
        simp [checkRuleInstance, TaxonomyWitness.premises,
          TaxonomyWitness.conclusion, TaxonomyWitness.authorized, member]⟩
  | subclassTrans child middle parent =>
      exact ⟨.subclassTrans child middle parent, by
        simp [checkRuleInstance, TaxonomyWitness.premises,
          TaxonomyWitness.conclusion, TaxonomyWitness.authorized]⟩
  | instanceInheritance individual child parent =>
      exact ⟨.instanceInheritance individual child parent, by
        simp [checkRuleInstance, TaxonomyWitness.premises,
          TaxonomyWitness.conclusion, TaxonomyWitness.authorized]⟩

/-- Exact finite-certificate interface for the taxonomy rules. -/
def taxonomyRuleWitness [DecidableEq Name]
    (source : List (TaxonomyFact Name)) :
    RuleWitness (TaxonomyRule source) where
  W := TaxonomyWitness Name
  isInstance := checkRuleInstance source
  sound := checkRuleInstance_sound source
  complete := checkRuleInstance_complete source

/-! ## Independent set-theoretic semantics -/

/-- An interpretation of names as individuals and as class extensions. -/
structure TaxonomyInterpretation (Name : Type uName) (Entity : Type uEntity) where
  individual : Name → Entity
  classExtension : Name → Set Entity

namespace TaxonomyInterpretation

variable {Entity : Type uEntity}

/-- Standard extensional satisfaction of taxonomy facts. -/
def Satisfies (interpretation : TaxonomyInterpretation Name Entity) :
    TaxonomyFact Name → Prop
  | .subclass child parent =>
      interpretation.classExtension child ⊆ interpretation.classExtension parent
  | .instance individual className =>
      interpretation.individual individual ∈
        interpretation.classExtension className

/-- Every source fact holds in the interpretation. -/
def ModelsSource (interpretation : TaxonomyInterpretation Name Entity)
    (source : List (TaxonomyFact Name)) : Prop :=
  ∀ fact ∈ source, interpretation.Satisfies fact

/-- Every taxonomy rule preserves the standard set-theoretic semantics. -/
theorem rule_sound
    (interpretation : TaxonomyInterpretation Name Entity)
    {source : List (TaxonomyFact Name)}
    (sourceValid : interpretation.ModelsSource source)
    {premises : List (TaxonomyFact Name)}
    {conclusion : TaxonomyFact Name}
    (rule : TaxonomyRule source premises conclusion)
    (premisesValid : ∀ premise ∈ premises,
      interpretation.Satisfies premise) :
    interpretation.Satisfies conclusion := by
  cases rule with
  | source member =>
      exact sourceValid _ member
  | subclassTrans child middle parent =>
      have childMiddle := premisesValid (.subclass child middle) (by simp)
      have middleParent := premisesValid (.subclass middle parent) (by simp)
      intro entity childMember
      exact middleParent (childMiddle childMember)
  | instanceInheritance individual child parent =>
      have individualChild := premisesValid (.instance individual child) (by simp)
      have childParent := premisesValid (.subclass child parent) (by simp)
      exact childParent individualChild

/-- Every derivation from the source taxonomy is semantically sound. -/
theorem derives_sound
    (interpretation : TaxonomyInterpretation Name Entity)
    {source : List (TaxonomyFact Name)}
    (sourceValid : interpretation.ModelsSource source)
    {fact : TaxonomyFact Name}
    (derivation : Derives (TaxonomyRule source) fact) :
    interpretation.Satisfies fact := by
  exact Derives.least interpretation.Satisfies
    (fun _premises _conclusion rule premisesValid =>
      interpretation.rule_sound sourceValid rule premisesValid)
    derivation

end TaxonomyInterpretation

/-! ## Certified inference as a GSLT -/

/-- One operational inference step adds the conclusion of a successfully
replayed certificate when that fact is not already in the state. -/
inductive TaxonomyExpansion [DecidableEq Name] :
    List (TaxonomyFact Name) → List (TaxonomyFact Name) → Prop
  | add {state : List (TaxonomyFact Name)}
      (certificate : Derivation (TaxonomyFact Name) (TaxonomyWitness Name))
      (accepted : certificate.valid (taxonomyRuleWitness state) = true)
      (fresh : certificate.concl ∉ state) :
      TaxonomyExpansion state (certificate.concl :: state)

/-- The native operational calculus of certified taxonomy expansion. -/
def taxonomyGSLT [DecidableEq Name] : GSLT where
  Term := List (TaxonomyFact Name)
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := TaxonomyExpansion
  rewrites_resp_left := by
    intro left equalLeft right equal step
    subst equalLeft
    exact ⟨right, step, rfl⟩
  rewrites_resp_right := by
    intro left right equalRight step equal
    subst equalRight
    exact step

/-- An accepted certificate either names an existing fact or induces one
operational expansion step. -/
theorem accepted_realized_or_present
    [DecidableEq Name]
    (state : List (TaxonomyFact Name))
    (certificate : Derivation (TaxonomyFact Name) (TaxonomyWitness Name))
    (accepted : certificate.valid (taxonomyRuleWitness state) = true) :
    certificate.concl ∈ state ∨
      taxonomyGSLT.Step state (certificate.concl :: state) := by
  by_cases present : certificate.concl ∈ state
  · exact Or.inl present
  · exact Or.inr (.add certificate accepted present)

/-- One certified expansion preserves every model of the current state. -/
theorem expansion_preserves_models
    [DecidableEq Name]
    {Entity : Type uEntity}
    (interpretation : TaxonomyInterpretation Name Entity)
    {state next : List (TaxonomyFact Name)}
    (stateValid : interpretation.ModelsSource state)
    (step : taxonomyGSLT.Step state next) :
    interpretation.ModelsSource next := by
  cases step with
  | add certificate accepted _fresh =>
      intro fact member
      simp only [List.mem_cons] at member
      rcases member with equal | oldMember
      · subst fact
        exact interpretation.derives_sound stateValid
          (Derivation.valid_sound (taxonomyRuleWitness state)
            certificate accepted)
      · exact stateValid fact oldMember

/-- Transport model validity along a finite certified expansion path. -/
def transportModels
    [DecidableEq Name]
    {Entity : Type uEntity}
    (interpretation : TaxonomyInterpretation Name Entity)
    {state final : List (TaxonomyFact Name)}
    (steps : taxonomyGSLT.MultiStep state final) :
    interpretation.ModelsSource state → interpretation.ModelsSource final :=
  match steps with
  | .refl _ => fun stateValid => stateValid
  | .step first rest => fun stateValid =>
      transportModels interpretation rest
        (expansion_preserves_models interpretation stateValid first)

/-- Every finite path of certified expansion preserves all source models. -/
theorem multiStep_preserves_models
    [DecidableEq Name]
    {Entity : Type uEntity}
    (interpretation : TaxonomyInterpretation Name Entity)
    {state final : List (TaxonomyFact Name)}
    (steps : taxonomyGSLT.MultiStep state final)
    (stateValid : interpretation.ModelsSource state) :
    interpretation.ModelsSource final :=
  transportModels interpretation steps stateValid

/-! ## Positive and negative controls -/

inductive CanaryName : Type
  | human
  | animal
  | socrates
  deriving DecidableEq, Repr

def canarySource : List (TaxonomyFact CanaryName) :=
  [.subclass .human .animal, .instance .socrates .human]

def humanAnimalLeaf :
    Derivation (TaxonomyFact CanaryName) (TaxonomyWitness CanaryName) :=
  .node (.subclass .human .animal)
    (.source (.subclass .human .animal)) 0 Fin.elim0

def socratesHumanLeaf :
    Derivation (TaxonomyFact CanaryName) (TaxonomyWitness CanaryName) :=
  .node (.instance .socrates .human)
    (.source (.instance .socrates .human)) 0 Fin.elim0

/-- A nontrivial two-premise certificate for inherited membership. -/
def socratesAnimalCertificate :
    Derivation (TaxonomyFact CanaryName) (TaxonomyWitness CanaryName) :=
  .node (.instance .socrates .animal)
    (.instanceInheritance .socrates .human .animal) 2
    (Fin.cases socratesHumanLeaf (Fin.cases humanAnimalLeaf Fin.elim0))

theorem socratesAnimalCertificate_accepted :
    socratesAnimalCertificate.valid (taxonomyRuleWitness canarySource) = true := by
  decide

theorem socratesAnimal_derivable :
    Derives (TaxonomyRule canarySource) (.instance .socrates .animal) :=
  Derivation.valid_sound (taxonomyRuleWitness canarySource)
    socratesAnimalCertificate socratesAnimalCertificate_accepted

def canaryInterpretation : TaxonomyInterpretation CanaryName Bool where
  individual
    | .socrates => true
    | .human => false
    | .animal => false
  classExtension
    | .human => {entity | entity = true}
    | .animal => Set.univ
    | .socrates => ∅

theorem canaryInterpretation_models_source :
    canaryInterpretation.ModelsSource canarySource := by
  intro fact member
  simp only [canarySource, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · intro entity _member
    trivial
  · rfl

theorem canaryInterpretation_refutes_reverse :
    ¬ canaryInterpretation.Satisfies (.subclass .animal .human) := by
  intro reverse
  have falseIsHuman := reverse (show false ∈ (Set.univ : Set Bool) by trivial)
  exact Bool.false_ne_true falseIsHuman

/-- The reverse subclass edge has no derivation from the canary source. -/
theorem reverse_subclass_not_derivable :
    ¬ Derives (TaxonomyRule canarySource) (.subclass .animal .human) := by
  intro derivation
  exact canaryInterpretation_refutes_reverse
    (canaryInterpretation.derives_sound
      canaryInterpretation_models_source derivation)

/-! ## Axiom audit -/

#print axioms checkRuleInstance_sound
#print axioms checkRuleInstance_complete
#print axioms TaxonomyInterpretation.rule_sound
#print axioms TaxonomyInterpretation.derives_sound
#print axioms accepted_realized_or_present
#print axioms expansion_preserves_models
#print axioms multiStep_preserves_models
#print axioms socratesAnimal_derivable
#print axioms reverse_subclass_not_derivable

end Mettapedia.Languages.KIF.TaxonomyInference
