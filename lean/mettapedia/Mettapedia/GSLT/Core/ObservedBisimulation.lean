import Mettapedia.GSLT.Core.GSLT

/-!
# Bisimulation relative to state observations

Ordinary strong bisimulation observes only transition structure. Ontological
concepts often also depend on state predicates: what an agent believes, what
is true, which authority owns a resource, or which value is affected. This
module adds those observations to an abstract GSLT without changing its
rewrite relation.

The resulting quotient is observer-relative. A predicate defines a lawful
concept on the quotient exactly when it is invariant under the observed
bisimilarity. A coarser observer can identify states across which a concept
changes; the negative theorem then prevents that concept from being treated
as a property of the coarse quotient.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe uAtom

/-- A GSLT equipped with atomic state observations. -/
structure ObservedGSLT (system : GSLT) where
  Atom : Type uAtom
  observes : Atom → system.Term → Prop

namespace ObservedGSLT

variable {system : GSLT} (observed : ObservedGSLT.{uAtom} system)

/-- A bisimulation that also preserves every declared state observation. -/
def IsBisimulation (relation : system.Term → system.Term → Prop) : Prop :=
  system.IsBisimulation relation ∧
    ∀ ⦃left right⦄, relation left right →
      ∀ atom, observed.observes atom left ↔ observed.observes atom right

/-- Strong bisimilarity relative to the declared observations. -/
def Bisimilar (left right : system.Term) : Prop :=
  ∃ relation, observed.IsBisimulation relation ∧ relation left right

theorem bisimilar_refl (term : system.Term) : observed.Bisimilar term term := by
  refine ⟨Eq, ⟨?_, ?_⟩, rfl⟩
  · constructor
    · intro left right equal next step
      subst equal
      exact ⟨next, step, rfl⟩
    · intro left right equal next step
      subst equal
      exact ⟨next, step, rfl⟩
  · intro left right equal atom
    subst equal
    exact Iff.rfl

theorem bisimilar_symm {left right : system.Term}
    (bisimilar : observed.Bisimilar left right) :
    observed.Bisimilar right left := by
  rcases bisimilar with ⟨relation, ⟨⟨forward, backward⟩, atoms⟩, related⟩
  refine ⟨fun first second => relation second first, ?_, related⟩
  exact ⟨⟨backward, forward⟩,
    fun _ _ rel atom => (atoms rel atom).symm⟩

theorem bisimilar_trans {left middle right : system.Term}
    (first : observed.Bisimilar left middle)
    (second : observed.Bisimilar middle right) :
    observed.Bisimilar left right := by
  rcases first with
    ⟨firstRelation, ⟨⟨firstForward, firstBackward⟩, firstAtoms⟩,
      leftMiddle⟩
  rcases second with
    ⟨secondRelation, ⟨⟨secondForward, secondBackward⟩, secondAtoms⟩,
      middleRight⟩
  let composite : system.Term → system.Term → Prop :=
    fun source target =>
      ∃ bridge, firstRelation source bridge ∧ secondRelation bridge target
  refine ⟨composite, ⟨⟨?_, ?_⟩, ?_⟩,
    ⟨middle, leftMiddle, middleRight⟩⟩
  · intro source target related next sourceStep
    rcases related with ⟨bridge, sourceBridge, bridgeTarget⟩
    rcases firstForward sourceBridge sourceStep with
      ⟨bridgeNext, bridgeStep, nextBridge⟩
    rcases secondForward bridgeTarget bridgeStep with
      ⟨targetNext, targetStep, bridgeNextTarget⟩
    exact ⟨targetNext, targetStep,
      ⟨bridgeNext, nextBridge, bridgeNextTarget⟩⟩
  · intro source target related next targetStep
    rcases related with ⟨bridge, sourceBridge, bridgeTarget⟩
    rcases secondBackward bridgeTarget targetStep with
      ⟨bridgeNext, bridgeStep, bridgeNextTarget⟩
    rcases firstBackward sourceBridge bridgeStep with
      ⟨sourceNext, sourceStep, sourceNextBridge⟩
    exact ⟨sourceNext, sourceStep,
      ⟨bridgeNext, sourceNextBridge, bridgeNextTarget⟩⟩
  · intro source target related atom
    rcases related with ⟨bridge, sourceBridge, bridgeTarget⟩
    exact (firstAtoms sourceBridge atom).trans
      (secondAtoms bridgeTarget atom)

/-- Observer-relative bisimilarity forms an equivalence relation. -/
def bisimSetoid : Setoid system.Term where
  r := observed.Bisimilar
  iseqv :=
    ⟨observed.bisimilar_refl,
      fun equivalent => observed.bisimilar_symm equivalent,
      fun first second => observed.bisimilar_trans first second⟩

/-- The observer-relative behavioral classes. -/
def Class : Type _ := Quotient observed.bisimSetoid

/-- The class of one system term. -/
def toClass (term : system.Term) : observed.Class :=
  Quotient.mk observed.bisimSetoid term

theorem class_eq_iff (left right : system.Term) :
    observed.toClass left = observed.toClass right ↔
      observed.Bisimilar left right :=
  Quotient.eq

/-- Observed bisimilarity is at least as discriminating as the underlying
transition-only bisimilarity. -/
theorem forgets_observations {left right : system.Term}
    (bisimilar : observed.Bisimilar left right) :
    system.Bisimilar left right := by
  rcases bisimilar with ⟨relation, ⟨steps, _atoms⟩, related⟩
  exact ⟨relation, steps, related⟩

/-- Every declared atom is invariant under observed bisimilarity. -/
theorem observation_invariant {left right : system.Term}
    (bisimilar : observed.Bisimilar left right) (atom : observed.Atom) :
    observed.observes atom left ↔ observed.observes atom right := by
  rcases bisimilar with ⟨relation, ⟨_steps, atoms⟩, related⟩
  exact atoms related atom

/-- One differing observation proves behavioral distinction. -/
theorem distinguished_of_observation {left right : system.Term}
    (atom : observed.Atom)
    (leftObserved : observed.observes atom left)
    (rightNotObserved : ¬ observed.observes atom right) :
    ¬ observed.Bisimilar left right := by
  intro bisimilar
  exact rightNotObserved
    ((observed.observation_invariant bisimilar atom).mp leftObserved)

/-- A term predicate is saturated by the observer-relative behavioral
classes when it is constant on every such class. -/
def Saturated (predicate : system.Term → Prop) : Prop :=
  ∀ ⦃left right⦄, observed.Bisimilar left right →
    (predicate left ↔ predicate right)

/-- Every saturated predicate induces a concept on the quotient. -/
def classify
    (predicate : system.Term → Prop)
    (saturated : observed.Saturated predicate) : observed.Class → Prop :=
  Quotient.lift predicate (fun _ _ equivalent =>
    propext (saturated equivalent))

@[simp] theorem classify_toClass
    (predicate : system.Term → Prop)
    (saturated : observed.Saturated predicate) (term : system.Term) :
    observed.classify predicate saturated (observed.toClass term) ↔
      predicate term :=
  Iff.rfl

/-- A quotient classifier can exist only for a saturated predicate. -/
theorem saturated_of_classifier
    (predicate : system.Term → Prop)
    (classifier : observed.Class → Prop)
    (correct : ∀ term, classifier (observed.toClass term) ↔ predicate term) :
    observed.Saturated predicate := by
  intro left right bisimilar
  have equalClasses : observed.toClass left = observed.toClass right :=
    (observed.class_eq_iff left right).2 bisimilar
  rw [← correct left, ← correct right, equalClasses]

/-! ## Axiom audit -/

#print axioms ObservedGSLT.bisimilar_refl
#print axioms ObservedGSLT.bisimilar_symm
#print axioms ObservedGSLT.bisimilar_trans
#print axioms ObservedGSLT.observation_invariant
#print axioms ObservedGSLT.distinguished_of_observation
#print axioms ObservedGSLT.classify_toClass
#print axioms ObservedGSLT.saturated_of_classifier

end ObservedGSLT

end Mettapedia.GSLT
