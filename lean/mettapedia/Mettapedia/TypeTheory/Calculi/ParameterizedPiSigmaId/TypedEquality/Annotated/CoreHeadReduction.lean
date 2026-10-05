import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelation

/-!
# The core weak-head reduction

`CoreStep P K`: β, the projections of a pair, the declared root steps, and a step in
the function position of an application, under a projection or at the code of the
decoder. Every weak-head reduction the relation reads takes these steps
(`CoreStep.step`), so inside one they inherit determinism and the normal forms of the
canonical forms, and they form a weak-head reduction themselves (`HeadReduction.core`).
It takes no step at an argument that a computing constant inspects.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

variable {Head : Type} {R : Rules Head}

/-- The steps every weak-head reduction the relation reads takes: β, the projections of
a pair, the declared root steps, and a step in the function position of an application,
under a projection or at the code of the decoder. -/
inductive CoreStep (P : ChurchRules R) (K : RigidTypes P) :
    {n : Nat} → CTm Head n → CTm Head n → Prop
  | beta {n : Nat} (A : CTm Head n) (b : CTm Head (n + 1)) (a : CTm Head n) :
      CoreStep P K (.app (.lam A b) a) (CTm.inst0 a b)
  | appFun {n : Nat} {f f' : CTm Head n} (a : CTm Head n) :
      CoreStep P K f f' → CoreStep P K (.app f a) (.app f' a)
  | root {n : Nat} {l r : CTm Head n} : P.computation.step l r → CoreStep P K l r
  | holdsArg {n : Nat} {c c' : CTm Head n} :
      CoreStep P K c c' → CoreStep P K (.app (.const K.holds) c) (.app (.const K.holds) c')
  | fstPair {n : Nat} (a b : CTm Head n) : CoreStep P K (.fst (.pair a b)) a
  | sndPair {n : Nat} (a b : CTm Head n) : CoreStep P K (.snd (.pair a b)) b
  | fst {n : Nat} {p p' : CTm Head n} : CoreStep P K p p' → CoreStep P K (.fst p) (.fst p')
  | snd {n : Nat} {p p' : CTm Head n} : CoreStep P K p p' → CoreStep P K (.snd p) (.snd p')

variable {P : ChurchRules R} {K : RigidTypes P}

/-- Every weak-head reduction the relation reads takes the core steps. -/
theorem CoreStep.step (H : HeadReduction P K) {n : Nat} {t u : CTm Head n}
    (s : CoreStep P K t u) : H.step t u := by
  induction s with
  | beta A b a => exact H.beta A b a
  | appFun a _ ih => exact H.appFun a ih
  | root h => exact H.root h
  | holdsArg _ ih => exact H.holdsArg ih
  | fstPair a b => exact H.fstPair a b
  | sndPair a b => exact H.sndPair a b
  | fst _ ih => exact H.fst ih
  | snd _ ih => exact H.snd ih

/-- **The core weak-head reduction**: inside a weak-head reduction the relation reads,
the core steps form one. -/
def HeadReduction.core (H : HeadReduction P K) : HeadReduction P K where
  step := CoreStep P K
  beta := .beta
  appFun := fun a s => .appFun a s
  root := .root
  holdsArg := .holdsArg
  deterministic := fun s₁ s₂ => H.deterministic (s₁.step H) (s₂.step H)
  head_normal := fun h u s => H.head_normal h u (s.step H)
  pi_normal := fun A B u s => H.pi_normal A B u (s.step H)
  id_normal := fun A a b u s => H.id_normal A a b u (s.step H)
  refl_normal := fun a u s => H.refl_normal a u (s.step H)
  prop_normal := fun u s => H.prop_normal u (s.step H)
  data_normal := fun u hd s => H.data_normal u hd (s.step H)
  ctor_normal := fun u hc hl s => H.ctor_normal u hc hl (s.step H)
  fstPair := .fstPair
  sndPair := .sndPair
  fst := .fst
  snd := .snd
  sigma_normal := fun A B u s => H.sigma_normal A B u (s.step H)
  ground_normal := fun u hg s => H.ground_normal u hg (s.step H)

theorem HeadReduction.core_step (H : HeadReduction P K) {n : Nat} {t u : CTm Head n} :
    H.core.step t u ↔ CoreStep P K t u :=
  Iff.rfl

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
