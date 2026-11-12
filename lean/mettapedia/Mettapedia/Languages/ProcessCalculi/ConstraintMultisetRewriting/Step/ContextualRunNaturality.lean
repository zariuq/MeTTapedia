import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualTensorInterpretation

/-!
# Whole-run transport from local contextual morphisms

The contract contains only placement maps, candidate covariance, the framing
domain and advancement. The complete target plan and native similarity are
constructed by induction. No whole-run covariance law is a contract field.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ContextualRunInterpretation

universe uO uT uH uOcc uS uF uI uP uM

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Step X O State Firing}
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}
  (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T)

structure PlacementTransport where
  Map : {left right : State} → I.Place left right → I.Place left right → Type uM
  iso : ∀ {left right : State} {p q : I.Place left right}, Map p q → T.Iso (I.pair p).state (I.pair q).state
  candidate : ∀ {left right : State} {p q : I.Place left right} (mapping : Map p q) (f : Firing left),
    T.Alike (T.move (iso mapping) (I.candidate p f)) (I.candidate q f)
  domain : ∀ {left right : State} {p q : I.Place left right} (_mapping : Map p q) (f : Firing left),
    I.domain p f → I.domain q f
  advance : ∀ {left right : State} {p q : I.Place left right} (_mapping : Map p q) (f : Firing left)
    (allowed : P.Admits f), Map (I.advance p f allowed) (I.advance q f allowed)

variable {I} (N : PlacementTransport.{uO,uT,uH,uOcc,uS,uF,uI,uP,uM} I)

def PlacementTransport.mapPlan : ∀ {left right : State} {p q : I.Place left right}
    (_mapping : N.Map p q) (run : P.Run left) (plan : I.Plan p run),
    (other : I.Plan q run) × N.Map (plan.realize I p run).target (other.realize I q run).target
  | _, _, _, q, mapping, .nil _, .nil _ => ⟨.nil q, mapping⟩
  | _, _, p, q, mapping, .cons f allowed rest, .cons framed nativeAllowed tail => by
      let later := mapPlan (N.advance mapping f allowed) rest tail
      have targetAllowed : P.Admits (I.candidate q f) :=
        (T.admits_alike (N.candidate mapping f)).mp
          ((T.admits_move (N.iso mapping) (I.candidate p f)).mpr nativeAllowed)
      exact ⟨.cons (N.domain mapping f framed) targetAllowed later.1, later.2⟩

theorem PlacementTransport.plans_similar : ∀ {left right : State} {p q : I.Place left right}
    (_mapping : N.Map p q) (run : P.Run left) (first : I.Plan p run) (second : I.Plan q run),
    T.Similar (first.realize I p run).execution (second.realize I q run).execution
  | _, _, _, _, mapping, .nil _, .nil _, .nil _ => ⟨N.iso mapping⟩
  | _, _, p, q, mapping, .cons f allowed rest, .cons framedP nativeP tailP, .cons framedQ nativeQ tailQ => by
      let laterP := tailP.realize I (I.advance p f allowed) rest
      let laterQ := tailQ.realize I (I.advance q f allowed) rest
      let stepP := I.resultIso p f allowed framedP nativeP
      let stepQ := I.resultIso q f allowed framedQ nativeQ
      have middle := plans_similar (N.advance mapping f allowed) rest tailP tailQ
      have tails : T.Similar (T.moveRun (T.symm stepP) laterP.execution)
          (T.moveRun (T.symm stepQ) laterQ.execution) :=
        Transport.Similar.trans (Transport.Similar.symm (Transport.Similar.moveRun (T.symm stepP) laterP.execution))
          (Transport.Similar.trans middle (Transport.Similar.moveRun (T.symm stepQ) laterQ.execution))
      exact ⟨N.iso mapping, N.candidate mapping f, tails⟩

theorem PlacementTransport.checks_map {left right : State} {p q : I.Place left right}
    (mapping : N.Map p q) (run : P.Run left) (checked : I.Checks p run) : I.Checks q run := by
  let source := Plan.ofChecks I p run checked
  exact (I.plan_iff_checks q run).mp ⟨(N.mapPlan mapping run source).1⟩

def PlacementTransport.targetsMap : ∀ {left right : State} {p q : I.Place left right}
    (_mapping : N.Map p q) (run : P.Run left) (first : I.Plan p run) (second : I.Plan q run),
    N.Map (first.realize I p run).target (second.realize I q run).target
  | _, _, _, _, mapping, .nil _, .nil _, .nil _ => mapping
  | _, _, _, _, mapping, .cons f allowed rest, .cons _ _ tailP, .cons _ _ tailQ =>
      targetsMap (N.advance mapping f allowed) rest tailP tailQ

variable {N}

structure PlacementTransport.FlipCompatible (N : PlacementTransport.{uO,uT,uH,uOcc,uS,uF,uI,uP,uM} I)
    (flip : I.Flip) where
  map : ∀ {left right : State} {p q : I.Place left right}, N.Map p q → N.Map (flip.swap p) (flip.swap q)

variable (N) (flip : I.Flip) (compatible : N.FlipCompatible flip)

def PlacementTransport.mapTensorPlan {left right : State} {p q : I.Place left right}
    (mapping : N.Map p q) {first : P.Run left} {second : P.Run right}
    (plan : I.TensorPlan flip p first second) :
    (other : I.TensorPlan flip q first second) ×
      N.Map (plan.realize I flip).target (other.realize I flip).target := by
  let one := N.mapPlan mapping first plan.leftPlan
  let two := N.mapPlan (compatible.map one.2) second plan.rightPlan
  exact ⟨⟨one.1, two.1⟩, compatible.map two.2⟩

include compatible in
theorem PlacementTransport.tensors_similar {left right : State} {p q : I.Place left right}
    (mapping : N.Map p q) {first : P.Run left} {second : P.Run right}
    (planP : I.TensorPlan flip p first second) (planQ : I.TensorPlan flip q first second) :
    T.Similar (planP.realize I flip).execution (planQ.realize I flip).execution := by
  let oneP := planP.leftPlan.realize I p first
  let oneQ := planQ.leftPlan.realize I q first
  let twoP := planP.rightPlan.realize I (flip.swap oneP.target) second
  let twoQ := planQ.rightPlan.realize I (flip.swap oneQ.target) second
  let bridgeP := T.trans (flip.stateIso oneP.target) (T.symm oneP.resultIso)
  let bridgeQ := T.trans (flip.stateIso oneQ.target) (T.symm oneQ.resultIso)
  have leftSimilar := N.plans_similar mapping first planP.leftPlan planQ.leftPlan
  have targetMapping := N.targetsMap mapping first planP.leftPlan planQ.leftPlan
  have rightSimilar := N.plans_similar (compatible.map targetMapping) second planP.rightPlan planQ.rightPlan
  have moved : T.Similar (T.moveRun bridgeP twoP.execution) (T.moveRun bridgeQ twoQ.execution) :=
    Transport.Similar.trans (Transport.Similar.symm (Transport.Similar.moveRun bridgeP twoP.execution))
      (Transport.Similar.trans rightSimilar (Transport.Similar.moveRun bridgeQ twoQ.execution))
  exact Transport.Similar.append leftSimilar moved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ContextualRunInterpretation
