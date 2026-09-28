import Mettapedia.Languages.Agda.Structural.StaticConstructors

/-!
# Static rules for explicit elimination spines

Spine action describes the conditional action of an elimination list on a
proposed input type. Its empty case does not supply a term-typing derivation.
Elimination typing separately requires the typed head and the spine action.

The application and argument rules follow Cockx's Agda Core `TyAppE` and
`TyArg`. Explicit append composes two ordered spine actions through a retained
intermediate type. Input and output conversions retain their equality evidence.

The canonical eighteen rules are embedded as rule data, with every recursive
premise referring to this combined presentation. Thus canonical constructors
may use derivations supplied by the extension. This construction does not
assert subject reduction for all structural computation or typed equality of
administrative elimination nodes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.SpineStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext TypeParameter TypeBody)

inductive CombinedJudgment where
  | core (judgment : Statics.Judgment)
  | spineAction {n : Nat} (context : RawContext n) (input : RawTy n)
      (spine : Spine (scope n)) (output : RawTy n)

/-- Nonrecursive local rule parameters; recursive evidence is generated below. -/
inductive RuleShape : CombinedJudgment → Type where
  | core {j : Statics.Judgment} (shape : Statics.RuleShape j) : RuleShape (.core j)
  | nil {n : Nat} (Γ : RawContext n) (A : RawTy n) :
      RuleShape (.spineAction Γ A nil A)
  | cons {n : Nat} (Γ : RawContext n) (A : TypeParameter n) (B : TypeBody n)
      (argument : RawTm n) (rest : Spine (scope n)) (C : RawTy n) :
      RuleShape (.spineAction Γ (Statics.piType A B).code (cons (apply argument) rest) C)
  | append {n : Nat} (Γ : RawContext n) (A : RawTy n) (first : Spine (scope n))
      (B : RawTy n) (second : Spine (scope n)) (C : RawTy n) :
      RuleShape (.spineAction Γ A (append first second) C)
  | inputConversion {n : Nat} (Γ : RawContext n) (A' A : RawTy n)
      (spine : Spine (scope n)) (B : RawTy n) :
      RuleShape (.spineAction Γ A' spine B)
  | outputConversion {n : Nat} (Γ : RawContext n) (A : RawTy n)
      (spine : Spine (scope n)) (B B' : RawTy n) :
      RuleShape (.spineAction Γ A spine B')
  | elimination {n : Nat} (Γ : RawContext n) (head : RawTm n) (A : RawTy n)
      (spine : Spine (scope n)) (B : RawTy n) :
      RuleShape (.core (Statics.typed Γ (eliminate head spine) B))

def premises : {j : CombinedJudgment} → RuleShape j → List CombinedJudgment
  | _, .core shape => (Statics.premises shape).map .core
  | _, .nil _ _ => []
  | _, .cons Γ A B argument rest C =>
      [.core (Statics.typed Γ argument A.code), .spineAction Γ (B.instantiate argument).code rest C]
  | _, .append Γ A first B second C => [.spineAction Γ A first B, .spineAction Γ B second C]
  | _, .inputConversion Γ A' A spine B => [.core (Statics.typeEqual Γ A' A), .spineAction Γ A spine B]
  | _, .outputConversion Γ A spine B B' => [.spineAction Γ A spine B, .core (Statics.typeEqual Γ B B')]
  | _, .elimination Γ head A spine B => [.core (Statics.typed Γ head A), .spineAction Γ A spine B]

def presentation : FinitePresentation Unit (fun _ => CombinedJudgment) where
  Shape _ j := RuleShape j
  premises _ _ shape := premises shape

abbrev Derivation (j : CombinedJudgment) := presentation.Derivation () j
abbrev CoreDerivation (j : Statics.Judgment) := Derivation (.core j)
abbrev Action {n : Nat} (Γ : RawContext n) (A : RawTy n) (es : Spine (scope n)) (B : RawTy n) :=
  Derivation (.spineAction Γ A es B)

/-- Canonical premises retain their original positions under the new judgment tag. -/
def canonicalHom : Hom Statics.presentation.polynomial presentation.polynomial
    (fun _ j => CombinedJudgment.core j) where
  onShape _ _ shape := .core shape
  onPosition _ _ shape := finCongr (List.length_map (f := CombinedJudgment.core) (as := Statics.premises shape))
  onNext := by
    intro _ j shape position
    change ((Statics.premises shape).map CombinedJudgment.core).get position =
      CombinedJudgment.core ((Statics.premises shape).get
        (finCongr (List.length_map (f := CombinedJudgment.core) (as := Statics.premises shape)) position))
    exact List.getElem_map CombinedJudgment.core
      (l := Statics.premises shape) (i := position.val) (h := position.isLt)

/-- Include complete canonical firing histories through the cartesian rule map. -/
noncomputable def includeCanonical {j : Statics.Judgment} (tree : Statics.Derivation j) :
    CoreDerivation j := canonicalHom.mapFix () j tree

theorem canonical_position_value {j : Statics.Judgment} (shape : Statics.RuleShape j)
    (position : presentation.polynomial.Position (canonicalHom.onShape () j shape)) :
    ((canonicalHom.onPosition () j shape) position).val = position.val := rfl

private theorem transport_injective {base : Unit} {first second : CombinedJudgment} (equal : first = second) :
    Function.Injective (fun tree : presentation.polynomial.Fix base first => equal ▸ tree) := by
  cases equal
  exact fun _ _ same => same

/-- Inclusion preserves distinctions between all canonical firing histories. -/
theorem includeCanonical_injective {j : Statics.Judgment} :
    Function.Injective (includeCanonical (j := j)) := by
  intro first
  refine IndexedPolynomial.Fix.eliminate Statics.presentation.polynomial
    (fun base j first => ∀ second, canonicalHom.mapFix base j first = canonicalHom.mapFix base j second →
      first = second) ?_ () j first
  intro base j shape children ih second same
  match second with
  | .roll otherShape otherChildren =>
      have sameShape : shape = otherShape :=
        RuleShape.core.inj (IndexedPolynomial.Fix.roll.inj same).1
      cases sameShape
      have sameChildren := eq_of_heq (IndexedPolynomial.Fix.roll.inj same).2
      congr 1
      funext position
      apply ih position (otherChildren position)
      let targetPosition := (canonicalHom.onPosition base j shape).symm position
      have atPosition := congrFun sameChildren targetPosition
      have mapped := transport_injective (canonicalHom.onNext base j shape targetPosition).symm atPosition
      change canonicalHom.mapFix base _ (children ((canonicalHom.onPosition base j shape) targetPosition)) =
        canonicalHom.mapFix base _ (otherChildren ((canonicalHom.onPosition base j shape) targetPosition)) at mapped
      have inverse : (canonicalHom.onPosition base j shape) targetPosition = position :=
        (canonicalHom.onPosition base j shape).apply_symm_apply position
      exact inverse ▸ mapped

private def coreEvidence : {js : List Statics.Judgment} → Evidence CoreDerivation js →
    Evidence Derivation (js.map CombinedJudgment.core)
  | [], _ => noEvidence Derivation
  | _ :: _, children =>
      consEvidence Derivation (children 0) (coreEvidence (fun position => children position.succ))

private abbrev emptyChildren := noEvidence Derivation
private abbrev child := @consEvidence _ Derivation

namespace Derivation

/-- Canonical rules recurse into combined derivations at every listed premise. -/
def core {j : Statics.Judgment} (shape : Statics.RuleShape j)
    (children : Evidence CoreDerivation (Statics.premises shape)) : CoreDerivation j :=
  .roll (.core shape) (coreEvidence children)

def nil {n : Nat} (Γ : RawContext n) (A : RawTy n) : Action Γ A Structural.nil A :=
  .roll (.nil Γ A) emptyChildren

def cons {n : Nat} {Γ : RawContext n} {A : TypeParameter n} {B : TypeBody n}
    {argument : RawTm n} {rest : Spine (scope n)} {C : RawTy n}
    (typedArgument : CoreDerivation (Statics.typed Γ argument A.code))
    (tail : Action Γ (B.instantiate argument).code rest C) :
    Action Γ (Statics.piType A B).code (Structural.cons (apply argument) rest) C :=
  .roll (.cons Γ A B argument rest C) (child typedArgument (child tail emptyChildren))

def append {n : Nat} {Γ : RawContext n} {A B C : RawTy n}
    {first second : Spine (scope n)} (left : Action Γ A first B) (right : Action Γ B second C) :
    Action Γ A (Structural.append first second) C :=
  .roll (.append Γ A first B second C) (child left (child right emptyChildren))

def inputConversion {n : Nat} {Γ : RawContext n} {A' A B : RawTy n} {spine : Spine (scope n)}
    (equal : CoreDerivation (Statics.typeEqual Γ A' A)) (action : Action Γ A spine B) :
    Action Γ A' spine B :=
  .roll (.inputConversion Γ A' A spine B) (child equal (child action emptyChildren))

def outputConversion {n : Nat} {Γ : RawContext n} {A B B' : RawTy n} {spine : Spine (scope n)}
    (action : Action Γ A spine B) (equal : CoreDerivation (Statics.typeEqual Γ B B')) :
    Action Γ A spine B' :=
  .roll (.outputConversion Γ A spine B B') (child action (child equal emptyChildren))

def elimination {n : Nat} {Γ : RawContext n} {head : RawTm n} {A B : RawTy n}
    {spine : Spine (scope n)} (typedHead : CoreDerivation (Statics.typed Γ head A))
    (action : Action Γ A spine B) : CoreDerivation (Statics.typed Γ (eliminate head spine) B) :=
  .roll (.elimination Γ head A spine B) (child typedHead (child action emptyChildren))

end Derivation

/-- The actual two ordered premise addresses recover both supplied histories. -/
def binaryEvidenceEquiv (first second : CombinedJudgment) :
    Evidence Derivation [first, second] ≃ Derivation first × Derivation second where
  toFun children := (children 0, children 1)
  invFun pair := child pair.1 (child pair.2 emptyChildren)
  left_inv children := by
    funext position
    refine Fin.cases rfl (fun position => ?_) position
    refine Fin.cases rfl (fun impossible => Fin.elim0 impossible) position
  right_inv pair := by cases pair; rfl

abbrev eliminationEvidenceEquiv {n : Nat} (Γ : RawContext n) (head : RawTm n)
    (A : RawTy n) (spine : Spine (scope n)) (B : RawTy n) :
    Evidence Derivation (premises (.elimination Γ head A spine B)) ≃
      CoreDerivation (Statics.typed Γ head A) × Action Γ A spine B :=
  binaryEvidenceEquiv _ _

abbrev appendEvidenceEquiv {n : Nat} (Γ : RawContext n) (A : RawTy n) (first : Spine (scope n))
    (B : RawTy n) (second : Spine (scope n)) (C : RawTy n) :
    Evidence Derivation (premises (.append Γ A first B second C)) ≃
      Action Γ A first B × Action Γ B second C := binaryEvidenceEquiv _ _

/-- A fixed rule constructor cannot identify different premise functions. -/
theorem roll_children_injective {j : CombinedJudgment} (shape : RuleShape j) :
    Function.Injective (fun children : Evidence Derivation (premises shape) =>
      (IndexedPolynomial.Fix.roll shape children : Derivation j)) := by
  intro first second same
  exact eq_of_heq (IndexedPolynomial.Fix.roll.inj same).2

theorem elimination_injective {n : Nat} {Γ : RawContext n} {head : RawTm n} {A B : RawTy n}
    {spine : Spine (scope n)}
    {firstHead secondHead : CoreDerivation (Statics.typed Γ head A)}
    {firstAction secondAction : Action Γ A spine B}
    (same : Derivation.elimination firstHead firstAction = Derivation.elimination secondHead secondAction) :
    firstHead = secondHead ∧ firstAction = secondAction := by
  have children := roll_children_injective (.elimination Γ head A spine B) same
  exact ⟨congrFun children 0, congrFun children 1⟩

theorem append_injective {n : Nat} {Γ : RawContext n} {A B C : RawTy n}
    {first second : Spine (scope n)}
    {firstLeft secondLeft : Action Γ A first B} {firstRight secondRight : Action Γ B second C}
    (same : Derivation.append firstLeft firstRight = Derivation.append secondLeft secondRight) :
    firstLeft = secondLeft ∧ firstRight = secondRight := by
  have children := roll_children_injective (.append Γ A first B second C) same
  exact ⟨congrFun children 0, congrFun children 1⟩

theorem least (P : CombinedJudgment → Prop)
    (closed : presentation.RuleClosed (fun _ j => P j)) (j : CombinedJudgment) (tree : Derivation j) : P j :=
  presentation.derivation_least (fun _ j => P j) closed () j tree

/-- Whether a history actually uses a canonical rule, including below spine nodes. -/
noncomputable def usesCanonical {base : Unit} {j : CombinedJudgment}
    (tree : presentation.polynomial.Fix base j) : Bool :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial (fun _ _ _ => Bool)
    (fun _ _ shape _children ih => match shape with
      | .core _ => true
      | .nil _ _ => false
      | .cons _ _ _ _ _ _ | .append _ _ _ _ _ _
      | .inputConversion _ _ _ _ _ | .outputConversion _ _ _ _ _
      | .elimination _ _ _ _ _ =>
          ih ⟨0, by change 0 < 2; decide⟩ || ih ⟨1, by change 1 < 2; decide⟩)
    base j tree

def isTermTyping : CombinedJudgment → Bool
  | .core (.term _ _ _) => true
  | _ => false

/-- A typing history cannot be generated solely by conditional spine actions. -/
theorem usesCanonical_of_typing {j : CombinedJudgment} (tree : Derivation j)
    (typed : isTermTyping j = true) : usesCanonical tree = true := by
  refine IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j tree => isTermTyping j = true → usesCanonical tree = true) ?_ () j tree typed
  intro base j shape children ih typed
  cases shape with
  | core _ => rfl
  | nil | cons | append | inputConversion | outputConversion => cases typed
  | elimination Γ head A spine B =>
      change (usesCanonical (children ⟨0, by change 0 < 2; decide⟩) ||
        usesCanonical (children ⟨1, by change 1 < 2; decide⟩)) = true
      rw [ih ⟨0, by change 0 < 2; decide⟩ rfl]
      rfl

@[simp] theorem usesCanonical_nil {n : Nat} (Γ : RawContext n) (A : RawTy n) :
    usesCanonical (Derivation.nil Γ A) = false := rfl

@[simp] theorem usesCanonical_include {j : Statics.Judgment} (tree : Statics.Derivation j) :
    usesCanonical (includeCanonical tree) = true := by
  match tree with
  | .roll _ _ => rfl

end Mettapedia.Languages.Agda.Structural.SpineStatics
