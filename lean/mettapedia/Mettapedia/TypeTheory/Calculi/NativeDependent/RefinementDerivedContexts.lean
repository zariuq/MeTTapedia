import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementJudgments

/-!
# Generated comprehension substitution through complete mixed suffixes

The constructed derivations use the actual data-variable projection, the
comprehension guard, and the generated substitution rules. Proposition
assumptions in a suffix restrict its context rather than adding data variables.
The final rule transports an authored consequence and all its dependent suffix
annotations through the complete refinement substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u

variable {S : Symbols.{u}} {D : Signature S}

/-- Ordered premise evidence retains each supplied derivation. -/
inductive PremiseEvidence (D : Signature S) : List (Judgment S) → Type u where
  | nil : PremiseEvidence D []
  | cons {judgment : Judgment S} {rest : List (Judgment S)}
      (first : Derivation D judgment) (remaining : PremiseEvidence D rest) :
      PremiseEvidence D (judgment :: rest)

def PremiseEvidence.at : {judgments : List (Judgment S)} → PremiseEvidence D judgments →
    (position : Fin judgments.length) → Derivation D (judgments.get position)
  | _, .nil, position => Fin.elim0 position
  | _, .cons first remaining, position => Fin.cases first (fun prior => remaining.at prior) position

def deriveList (rule : RuleCode D) (premises : PremiseEvidence D rule.premises) :
    Derivation D rule.conclusion := derive rule premises.at

def Derivation.rootRule {judgment : Judgment S} : Derivation D judgment → RuleCode D
  | .node rule _ => rule.val

def Derivation.rootAssumptionPosition {judgment : Judgment S}
    (tree : Derivation D judgment) : Option Nat :=
  match tree.rootRule with
  | .hypothesis _ _ member => some member.position
  | _ => none

/-- The complete projection and its guard are earned from the local rules. -/
structure ComprehensionProjectionData {n : Nat} (D : Signature S)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) where
  formed : Derivation D (.context (.snoc context (.comprehension domain predicate)))
  arrow : Derivation D (.substitution (.snoc context (.comprehension domain predicate))
    (.snoc context domain) (comprehensionProjection domain predicate))
  guard : Derivation D (.entails (.snoc context (.comprehension domain predicate))
    (predicate.substitute (comprehensionProjection domain predicate)))

def comprehensionProjectionData {n : Nat} {context : ContextExpr S n}
    {domain : TypeExpr S n} {predicate : PropExpr S (n + 1)}
    (contextTree : Derivation D (.context context)) (domainTree : Derivation D (.type context domain))
    (predicateTree : Derivation D (.predicate (.snoc context domain) predicate)) :
    ComprehensionProjectionData D context domain predicate := by
  let refined := TypeExpr.comprehension domain predicate
  let source := ContextExpr.snoc context refined
  let formation := deriveList (.comprehensionFormation context domain predicate)
    (.cons contextTree (.cons domainTree (.cons predicateTree .nil)))
  let formed := deriveList (.contextExtend context refined) (.cons contextTree (.cons formation .nil))
  let weakening : Substitution S n (n + 1) := fun index => .var index.succ
  let weaken := deriveList (.substitutionWeaken context refined) (.cons formation .nil)
  have weakenedDomain : Derivation D (.type source (domain.rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, weakening, TypeExpr.substitute_variables] using
      deriveList (.substituteType source context weakening domain) (.cons weaken (.cons domainTree .nil))
  have lifted : Derivation D (.substitution (.snoc source (domain.rename Fin.succ))
      (.snoc context domain) (fun index => .var (liftRenaming Fin.succ index))) := by
    simpa only [RuleCode.conclusion, weakening, TypeExpr.substitute_variables, liftSubstitution_variables] using
      deriveList (.substitutionLift source context domain weakening) (.cons weaken (.cons domainTree .nil))
  have weakenedPredicate : Derivation D (.predicate (.snoc source (domain.rename Fin.succ))
      (predicate.rename (liftRenaming Fin.succ))) := by
    simpa only [RuleCode.conclusion, PropExpr.substitute_variables] using
      deriveList (.substitutePredicate (.snoc source (domain.rename Fin.succ))
        (.snoc context domain) (fun index => .var (liftRenaming Fin.succ index)) predicate)
          (.cons lifted (.cons predicateTree .nil))
  have generic : Derivation D (.term source (.var 0)
      (.comprehension (domain.rename Fin.succ) (predicate.rename (liftRenaming Fin.succ)))) :=
    deriveList (.variable source 0) (.cons formed .nil)
  let value := TermExpr.forget (domain.rename Fin.succ)
    (predicate.rename (liftRenaming Fin.succ)) (.var 0)
  have forgotten : Derivation D (.term source value (domain.rename Fin.succ)) :=
    deriveList (.comprehensionElimination source (domain.rename Fin.succ)
      (predicate.rename (liftRenaming Fin.succ)) (.var 0))
        (.cons weakenedDomain (.cons weakenedPredicate (.cons generic .nil)))
  have forgottenSubstitution : Derivation D (.term source value (domain.substitute weakening)) := by
    simpa only [weakening, TypeExpr.substitute_variables] using forgotten
  have projection : Derivation D (.substitution source (.snoc context domain)
      (comprehensionProjection domain predicate)) :=
    deriveList (.substitutionExtend source context domain weakening value)
      (.cons weaken (.cons domainTree (.cons forgottenSubstitution .nil)))
  have guarded : Derivation D (.entails source
      ((predicate.rename (liftRenaming Fin.succ)).substitute (instantiate value))) :=
    deriveList (.comprehensionGuard source (domain.rename Fin.succ)
      (predicate.rename (liftRenaming Fin.succ)) (.var 0))
        (.cons weakenedDomain (.cons weakenedPredicate (.cons generic .nil)))
  have guardCode : (predicate.rename (liftRenaming Fin.succ)).substitute (instantiate value) =
      predicate.substitute (comprehensionProjection domain predicate) := by
    rw [PropExpr.substitute_rename]
    congr 1
    funext index
    cases index using Fin.cases <;> rfl
  exact ⟨formed, projection, guardCode ▸ guarded⟩

/-- A formation spine has an actual generated premise at each suffix declaration. -/
inductive SuffixFormation {n : Nat} (D : Signature S) (base : ContextExpr S n) :
    {k : Nat} → ContextSuffix S n k → Type u where
  | nil (baseTree : Derivation D (.context base)) : SuffixFormation D base .nil
  | snoc {k : Nat} {suffix : ContextSuffix S n k} (previous : SuffixFormation D base suffix)
      (type : TypeExpr S (n + k)) (tree : Derivation D (.type (suffix.plug base) type)) :
      SuffixFormation D base (.snoc suffix type)
  | assume {k : Nat} {suffix : ContextSuffix S n k} (previous : SuffixFormation D base suffix)
      (predicate : PropExpr S (n + k))
      (tree : Derivation D (.predicate (suffix.plug base) predicate)) :
      SuffixFormation D base (.assume suffix predicate)

namespace SuffixFormation

def context {n : Nat} {base : ContextExpr S n} :
    {k : Nat} → {suffix : ContextSuffix S n k} → SuffixFormation D base suffix →
      Derivation D (.context (suffix.plug base))
  | _, _, .nil tree => tree
  | _, _, .snoc previous type tree =>
      deriveList (.contextExtend _ type) (.cons previous.context (.cons tree .nil))
  | _, _, .assume previous predicate tree =>
      deriveList (.contextAssume _ predicate) (.cons previous.context (.cons tree .nil))

def projection {n : Nat} {base : ContextExpr S n} :
    {k : Nat} → {suffix : ContextSuffix S n k} → SuffixFormation D base suffix →
      Derivation D (.substitution (suffix.plug base) base
        (fun index => .var (weakenRenaming k index)))
  | _, _, .nil tree => deriveList (.substitutionIdentity _) (.cons tree .nil)
  | _, _, .snoc previous type tree =>
      deriveList (.substitutionCompose _ _ base (fun index => .var index.succ)
        (fun index => .var (weakenRenaming _ index)))
          (.cons (deriveList (.substitutionWeaken _ type) (.cons tree .nil))
            (.cons previous.projection .nil))
  | _, _, .assume previous predicate tree =>
      deriveList (.substitutionCompose _ _ base TermExpr.var
        (fun index => .var (weakenRenaming _ index)))
          (.cons (deriveList (.substitutionWeakenAssumption _ predicate) (.cons tree .nil))
            (.cons previous.projection .nil))

end SuffixFormation

structure SuffixTransport {n m k : Nat} (D : Signature S) (source : ContextExpr S n)
    (target : ContextExpr S m) (substitution : Substitution S m n) (suffix : ContextSuffix S m k) where
  formed : SuffixFormation D source (suffix.substitute substitution)
  arrow : Derivation D (.substitution ((suffix.substitute substitution).plug source)
    (suffix.plug target) (liftSubstitutionN substitution k))

def SuffixFormation.transport {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} (sourceTree : Derivation D (.context source))
    (substitutionTree : Derivation D (.substitution source target substitution)) :
    {k : Nat} → {suffix : ContextSuffix S m k} → SuffixFormation D target suffix →
      SuffixTransport D source target substitution suffix
  | _, _, .nil _ => ⟨.nil sourceTree, substitutionTree⟩
  | k + 1, .snoc suffix type, .snoc previous _ tree => by
      let preceding := previous.transport sourceTree substitutionTree
      let sourceContext := (suffix.substitute substitution).plug source
      let targetContext := suffix.plug target
      let lifted := liftSubstitutionN substitution k
      let mappedType := deriveList (.substituteType sourceContext targetContext lifted type)
        (.cons preceding.arrow (.cons tree .nil))
      exact ⟨.snoc preceding.formed (type.substitute lifted) mappedType,
        deriveList (.substitutionLift sourceContext targetContext type lifted)
          (.cons preceding.arrow (.cons tree .nil))⟩
  | k, .assume suffix predicate, .assume previous _ tree => by
      let preceding := previous.transport sourceTree substitutionTree
      let sourceContext := (suffix.substitute substitution).plug source
      let targetContext := suffix.plug target
      let lifted := liftSubstitutionN substitution k
      let mappedPredicate := deriveList (.substitutePredicate sourceContext targetContext lifted predicate)
        (.cons preceding.arrow (.cons tree .nil))
      exact ⟨.assume preceding.formed (predicate.substitute lifted) mappedPredicate,
        deriveList (.substitutionAssumptionLift sourceContext targetContext predicate lifted)
          (.cons preceding.arrow (.cons tree .nil))⟩

theorem PropExpr.substitute_weakenN {n m : Nat} (substitution : Substitution S n m)
    (predicate : PropExpr S n) (k : Nat) :
    (predicate.rename (weakenRenaming k)).substitute (liftSubstitutionN substitution k) =
      (predicate.substitute substitution).rename (weakenRenaming k) := by
  induction k with
  | zero => simp only [weakenRenaming, PropExpr.rename_identity, liftSubstitutionN_zero]
  | succ k previous =>
      change (predicate.rename (Fin.succ ∘ weakenRenaming k)).substitute
        (liftSubstitution (liftSubstitutionN substitution k)) =
          (predicate.substitute substitution).rename (Fin.succ ∘ weakenRenaming k)
      rw [← PropExpr.rename_comp, PropExpr.substitute_weaken, previous, PropExpr.rename_comp]

/-- The full c°E rule is a constructed substitution into the assumed context,
not a new rule assuming that a suffix can be transported. -/
def comprehensionAssumptionSubstitution {n k : Nat} {context : ContextExpr S n}
    {domain : TypeExpr S n} {predicate : PropExpr S (n + 1)}
    {suffix : ContextSuffix S (n + 1) k}
    (contextTree : Derivation D (.context context)) (domainTree : Derivation D (.type context domain))
    (predicateTree : Derivation D (.predicate (.snoc context domain) predicate))
    (suffixTree : SuffixFormation D (.snoc context domain) suffix) :
    Derivation D (.substitution
      ((suffix.substitute (comprehensionProjection domain predicate)).plug
        (.snoc context (.comprehension domain predicate)))
      (.assume (suffix.plug (.snoc context domain)) (predicate.rename (weakenRenaming k)))
      (liftSubstitutionN (comprehensionProjection domain predicate) k)) := by
  let base := comprehensionProjectionData contextTree domainTree predicateTree
  let projection := comprehensionProjection domain predicate
  let sourceBase := ContextExpr.snoc context (.comprehension domain predicate)
  let targetBase := ContextExpr.snoc context domain
  let transported := suffixTree.transport base.formed base.arrow
  let sourceContext := (suffix.substitute projection).plug sourceBase
  let targetContext := suffix.plug targetBase
  have targetGuard : Derivation D (.predicate targetContext (predicate.rename (weakenRenaming k))) := by
    simpa only [RuleCode.conclusion, PropExpr.substitute_variables] using
      deriveList (.substitutePredicate targetContext targetBase
        (fun index => .var (weakenRenaming k index)) predicate)
          (.cons suffixTree.projection (.cons predicateTree .nil))
  have sourceGuard : Derivation D (.entails sourceContext
      ((predicate.rename (weakenRenaming k)).substitute (liftSubstitutionN projection k))) := by
    rw [PropExpr.substitute_weakenN]
    simpa only [RuleCode.conclusion, PropExpr.substitute_variables] using
      deriveList (.substituteEntailment sourceContext sourceBase
        (fun index => .var (weakenRenaming k index)) (predicate.substitute projection))
          (.cons transported.formed.projection (.cons base.guard .nil))
  exact deriveList (.substitutionIntoAssumption sourceContext targetContext
    (predicate.rename (weakenRenaming k)) (liftSubstitutionN projection k))
      (.cons transported.arrow (.cons targetGuard (.cons sourceGuard .nil)))

def comprehensionAssumptionElimination {n k : Nat} {context : ContextExpr S n}
    {domain : TypeExpr S n} {predicate : PropExpr S (n + 1)}
    {suffix : ContextSuffix S (n + 1) k} {consequent : PropExpr S ((n + 1) + k)}
    (contextTree : Derivation D (.context context)) (domainTree : Derivation D (.type context domain))
    (predicateTree : Derivation D (.predicate (.snoc context domain) predicate))
    (suffixTree : SuffixFormation D (.snoc context domain) suffix)
    (consequenceTree : Derivation D (.entails
      (.assume (suffix.plug (.snoc context domain)) (predicate.rename (weakenRenaming k))) consequent)) :
    Derivation D (.entails
      ((suffix.substitute (comprehensionProjection domain predicate)).plug
        (.snoc context (.comprehension domain predicate)))
      (consequent.substitute (liftSubstitutionN (comprehensionProjection domain predicate) k))) :=
  deriveList (.substituteEntailment _ _ _ consequent)
    (.cons (comprehensionAssumptionSubstitution contextTree domainTree predicateTree suffixTree)
      (.cons consequenceTree .nil))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
