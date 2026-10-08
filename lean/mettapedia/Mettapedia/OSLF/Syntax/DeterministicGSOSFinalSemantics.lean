import Mettapedia.OSLF.Syntax.DeterministicGSOSCofree
import Mettapedia.OSLF.Syntax.DeterministicGSOSBisimulation

/-!
# Final deterministic semantics and its actual bisimulation kernel

The cofree coalgebra on the terminal colour family is final. Equality
of its complete tree readouts is precisely span bisimilarity: one
direction uses finality, while the other constructs the actual kernel
coalgebra by matching labelwise optional successors. Consequently the
final semantic kernel is preserved by every free constructor context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.FinalSemantics

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory

universe u

variable (S : Signature.{u}) (Actions : S.Srt → Type u)

/-- Terminal colours erase only colours; the complete enabled action tree remains. -/
abbrev terminalColours : S.Families := fun _ _ => PUnit.{u + 1}

/-- The actual final behavior coalgebra, with arbitrary action branching. -/
def finalObject : Endofunctor.Coalgebra (behaviourFunctor S Actions) :=
  (Cofree.functor S Actions).obj (terminalColours S)

/-- The unique final map is actual finite-path unfolding. -/
def observe (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    object ⟶ finalObject S Actions :=
  PartialActionTreeCofree.extend PUnit.{u + 1} (fun _ => S.Srt) (fun _ => Actions)
    object (terminalColours S) (fun _ _ => ↾(fun _ => PUnit.unit))

/-- Uniqueness is earned on the complete tree, including disabled paths. -/
theorem observe_unique (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (mapping : object ⟶ finalObject S Actions) : mapping = observe S Actions object := by
  apply PartialActionTreeCofree.extend_unique PUnit.{u + 1} (fun _ => S.Srt) (fun _ => Actions)
  intro base sort state
  exact Subsingleton.elim _ _

/-- A genuine categorical finality certificate for the constructed tree coalgebra. -/
def isFinal : Limits.IsTerminal (finalObject S Actions) :=
  Limits.IsTerminal.ofUniqueHom (observe S Actions) (observe_unique S Actions)

theorem observe_natural {first second : Endofunctor.Coalgebra (behaviourFunctor S Actions)}
    (mapping : first ⟶ second) :
    mapping ≫ observe S Actions second = observe S Actions first :=
  observe_unique S Actions first _

theorem observe_step (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (state : object.V base sort) (action : Actions sort) :
    ((observe S Actions object).f base sort state).step action =
      (object.str base sort state action).map ((observe S Actions object).f base sort) :=
  (congrArg (fun arrow => arrow base sort state action) (observe S Actions object).h).symm

/-- Match optional successors with equal observations, retaining both original successors. -/
def matchPair {X Y : Type u} (readout : X → Y) (first second : Option X)
    (agreement : first.map readout = second.map readout) :
    Option { pair : X × X // readout pair.1 = readout pair.2 } := by
  cases first with
  | none =>
    cases second with
    | none => exact none
    | some value =>
      change (none : Option Y) = some (readout value) at agreement
      cases agreement
  | some first =>
    cases second with
    | none =>
      change some (readout first) = (none : Option Y) at agreement
      cases agreement
    | some second => exact some ⟨(first, second), Option.some.inj agreement⟩

theorem matchPair_first {X Y : Type u} (readout : X → Y) (first second : Option X)
    (agreement : first.map readout = second.map readout) :
    (matchPair readout first second agreement).map (fun pair => pair.val.1) = first := by
  cases first with
  | none =>
    cases second with
    | none => rfl
    | some value =>
      change (none : Option Y) = some (readout value) at agreement
      cases agreement
  | some first =>
    cases second with
    | none =>
      change some (readout first) = (none : Option Y) at agreement
      cases agreement
    | some second => rfl

theorem matchPair_second {X Y : Type u} (readout : X → Y) (first second : Option X)
    (agreement : first.map readout = second.map readout) :
    (matchPair readout first second agreement).map (fun pair => pair.val.2) = second := by
  cases first with
  | none =>
    cases second with
    | none => rfl
    | some value =>
      change (none : Option Y) = some (readout value) at agreement
      cases agreement
  | some first =>
    cases second with
    | none =>
      change some (readout first) = (none : Option Y) at agreement
      cases agreement
    | some second => rfl

/-- The complete final-semantic kernel retains both independent original states. -/
abbrev Kernel (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) : S.Families :=
  fun base sort => { pair : object.V base sort × object.V base sort //
    (observe S Actions object).f base sort pair.1 = (observe S Actions object).f base sort pair.2 }

theorem kernel_successors (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (pair : Kernel S Actions object base sort)
    (action : Actions sort) :
    (object.str base sort pair.val.1 action).map ((observe S Actions object).f base sort) =
      (object.str base sort pair.val.2 action).map ((observe S Actions object).f base sort) := by
  have steps := congrArg (fun tree => tree.step action) pair.property
  rw [observe_step, observe_step] at steps
  exact steps

/-- Equality of complete final observations supplies an actual kernel coalgebra. -/
def kernelCoalgebra (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    Endofunctor.Coalgebra (behaviourFunctor S Actions) where
  V := Kernel S Actions object
  str base sort := ↾(fun pair action => matchPair ((observe S Actions object).f base sort)
    (object.str base sort pair.val.1 action) (object.str base sort pair.val.2 action)
      (kernel_successors S Actions object base sort pair action))

def kernelFirst (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    kernelCoalgebra S Actions object ⟶ object where
  f _ _ := ↾(fun pair => pair.val.1)
  h := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro pair
    funext action
    exact matchPair_first _ _ _ _

def kernelSecond (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    kernelCoalgebra S Actions object ⟶ object where
  f _ _ := ↾(fun pair => pair.val.2)
  h := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro pair
    funext action
    exact matchPair_second _ _ _ _

/-- No weak-pullback preservation premise is needed: the kernel span is constructed explicitly. -/
theorem kernel_iff_bisimilar
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (first second : object.V base sort) :
    (observe S Actions object).f base sort first = (observe S Actions object).f base sort second ↔
      Bisimulation.Related object base sort first second := by
  constructor
  · intro agreement
    exact ⟨⟨⟨kernelCoalgebra S Actions object, kernelFirst S Actions object,
      kernelSecond S Actions object⟩, ⟨(first, second), agreement⟩, rfl, rfl⟩⟩
  · rintro ⟨witness⟩
    have first_read := congrArg (fun arrow => arrow.f base sort witness.point)
      (observe_natural S Actions witness.span.first)
    have second_read := congrArg (fun arrow => arrow.f base sort witness.point)
      (observe_natural S Actions witness.span.second)
    change (observe S Actions object).f base sort
      (witness.span.first.f base sort witness.point) =
      (observe S Actions witness.span.carrier).f base sort witness.point at first_read
    change (observe S Actions object).f base sort
      (witness.span.second.f base sort witness.point) =
      (observe S Actions witness.span.carrier).f base sort witness.point at second_read
    rw [witness.first_read] at first_read
    rw [witness.second_read] at second_read
    exact first_read.trans second_read.symm

variable {S Actions} (law : Law S Actions)

/-- Every complete free context preserves the actual final-semantic kernel. -/
theorem context_kernel_congruent
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (context : S.polynomial.Free (Bisimulation.RelatedPairs (Operational.liftObject law object)) base sort) :
    (observe S Actions (Operational.liftObject law object)).f base sort
        (IndexedPolynomial.Free.bind S.polynomial (fun _ _ pair => pair.val.1) base sort context) =
      (observe S Actions (Operational.liftObject law object)).f base sort
        (IndexedPolynomial.Free.bind S.polynomial (fun _ _ pair => pair.val.2) base sort context) :=
  (kernel_iff_bisimilar S Actions _ base sort _ _).mpr
    (Bisimulation.context_related law object base sort context)

/-- The actual final-semantic kernel is a constructor congruence. -/
theorem constructor_kernel_congruent
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (operator : S.Operator sort)
    (first second : (position : S.Position operator) →
      (Operational.liftObject law object).V base (S.argument operator position))
    (agreement : ∀ position,
      (observe S Actions (Operational.liftObject law object)).f base _ (first position) =
        (observe S Actions (Operational.liftObject law object)).f base _ (second position)) :
    (observe S Actions (Operational.liftObject law object)).f base sort
        (IndexedPolynomial.Free.node S.polynomial operator first) =
      (observe S Actions (Operational.liftObject law object)).f base sort
        (IndexedPolynomial.Free.node S.polynomial operator second) := by
  apply (kernel_iff_bisimilar S Actions _ base sort _ _).mpr
  apply Bisimulation.constructor_congruent law object base sort operator first second
  intro position
  exact (kernel_iff_bisimilar S Actions _ base _ _ _).mp (agreement position)

end Mettapedia.OSLF.DeterministicGSOS.FinalSemantics
