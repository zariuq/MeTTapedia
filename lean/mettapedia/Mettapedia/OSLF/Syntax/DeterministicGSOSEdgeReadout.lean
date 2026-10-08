import Mettapedia.OSLF.Syntax.DeterministicGSOSCoalgebraMonad
import Mettapedia.TypeTheory.PresheafEventCertificates

/-!
# Internal source-edge fibres of the actual operational span

Independent presheaves of variables supply a natural variable coalgebra.
The earned operational extension gives a presheaf of actual labeled edges,
with natural source and target maps and retained occurrence identifiers.
Its native source fibre retains the full edge and the supplied dependent
target certificate. Complete guarded rule premises produce actual edges;
selecting a single input edge alone does not supply absent-action premises.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.EdgeReadout

open _root_.CategoryTheory Mettapedia.TypeTheory
open PresheafEventCertificates

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable {C : Type u} [Category.{u} C]

/-- Evaluation at a declared sort keeps the actual indexed family carrier. -/
def sortFunctor (sort : S.Srt) : S.Families ⥤ Type u where
  obj X := X PUnit.unit sort
  map mapping := mapping PUnit.unit sort

variable (law : Law S Actions) (worlds : Cᵒᵖ ⥤ S.Families)
variable (steps : worlds ⟶ worlds ⋙ behaviourFunctor S Actions)

/-- The genuine contextual free terms, at their original output sort. -/
noncomputable abbrev terms (sort : S.Srt) : Cᵒᵖ ⥤ Type u :=
  worlds ⋙ S.termMonad.toFunctor ⋙ sortFunctor sort

/-- An actual operational event retains its supplied occurrence identifier. -/
@[ext] structure Event (Origins : Type u) (sort : S.Srt) (world : Cᵒᵖ) where
  origin : Origins
  source : S.Term (worlds.obj world) sort
  action : Actions sort
  target : S.Term (worlds.obj world) sort
  valid : Operational.coalgebra law (steps.app world) PUnit.unit sort source action = some target

/-- Natural variable coalgebras give natural actual operational edge readouts. -/
theorem step_map {first second : Cᵒᵖ} (change : first ⟶ second)
    (sort : S.Srt) (source : S.Term (worlds.obj first) sort) (action : Actions sort) :
    Operational.coalgebra law (steps.app second) PUnit.unit sort
        (S.rename (worlds.map change) source) action =
      (Operational.coalgebra law (steps.app first) PUnit.unit sort source action).map
        (S.rename (worlds.map change)) := by
  have respects : ∀ base index value,
      steps.app second base index (worlds.map change base index value) =
        fun label => (steps.app first base index value label).map (worlds.map change base index) := by
    intro base index value
    exact congrArg (fun mapping => mapping base index value) (steps.naturality change)
  exact congrFun (Operational.coalgebra_rename law (steps.app first) (steps.app second)
    (worlds.map change) respects PUnit.unit sort source) action

/-- Reindex the complete occurrence and both endpoints along the actual variable map. -/
noncomputable def mapEvent {Origins : Type u} {sort : S.Srt}
    {first second : Cᵒᵖ} (change : first ⟶ second)
    (event : Event law worlds steps Origins sort first) : Event law worlds steps Origins sort second where
  origin := event.origin
  source := S.rename (worlds.map change) event.source
  action := event.action
  target := S.rename (worlds.map change) event.target
  valid := by
    have carried := step_map law worlds steps change sort event.source event.action
    rw [event.valid] at carried
    exact carried

/-- The actual operational events form a presheaf, without erasing occurrence origins. -/
noncomputable def events (Origins : Type u) (sort : S.Srt) : Cᵒᵖ ⥤ Type u where
  obj world := Event law worlds steps Origins sort world
  map change := ↾(mapEvent law worlds steps change)
  map_id world := by
    apply ConcreteCategory.hom_ext
    intro event
    apply Event.ext
    · rfl
    · change S.rename (worlds.map (𝟙 world)) event.source = event.source
      rw [worlds.map_id]
      exact IndexedPolynomial.Free.map_id S.polynomial event.source
    · rfl
    · change S.rename (worlds.map (𝟙 world)) event.target = event.target
      rw [worlds.map_id]
      exact IndexedPolynomial.Free.map_id S.polynomial event.target
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro event
    apply Event.ext
    · rfl
    · change S.rename (worlds.map (earlier ≫ later)) event.source =
        S.rename (worlds.map later) (S.rename (worlds.map earlier) event.source)
      rw [worlds.map_comp]
      exact (IndexedPolynomial.Free.map_comp S.polynomial
        (fun base index => worlds.map earlier base index)
        (fun base index => worlds.map later base index) event.source).symm
    · rfl
    · change S.rename (worlds.map (earlier ≫ later)) event.target =
        S.rename (worlds.map later) (S.rename (worlds.map earlier) event.target)
      rw [worlds.map_comp]
      exact (IndexedPolynomial.Free.map_comp S.polynomial
        (fun base index => worlds.map earlier base index)
        (fun base index => worlds.map later base index) event.target).symm

/-- The native event span is built from the earned operational edge presheaf. -/
noncomputable def eventSpan (Origins : Type u) (sort : S.Srt) :
    EventSpan (terms worlds sort) (terms worlds sort) where
  events := events law worlds steps Origins sort
  source := { app := fun _ => ↾Event.source }
  target := { app := fun _ => ↾Event.target }

/-- A complete guarded source configuration produces its actual operational edge. -/
noncomputable def behaviorRule {Origins : Type u} (origin : Origins) (world : Cᵒᵖ)
    {sort : S.Srt} (operator : S.Operator sort)
    (children : ∀ position, S.Term (worlds.obj world) (S.argument operator position))
    (guard : Guard Actions operator) (action : Actions sort)
    (target : S.Term (ruleVariables Actions operator guard) sort)
    (matching : inputGuard Actions (fun position =>
      (children position, Operational.coalgebra law (steps.app world) PUnit.unit _ (children position))) = guard)
    (conclusion : fromLaw Actions law sort operator guard action = some target) :
    Event law worlds steps Origins sort world where
  origin := origin
  source := IndexedPolynomial.Free.node S.polynomial operator children
  action := action
  target := IndexedPolynomial.Free.join S.polynomial
    (S.rename (assignmentAt Actions guard (fun position =>
      (children position, Operational.coalgebra law (steps.app world) PUnit.unit _ (children position))) matching) target)
  valid := by
    let inputs : BehaviourArguments S Actions (S.polynomial.Free (worlds.obj world)) operator :=
      fun position => (children position, Operational.coalgebra law (steps.app world) PUnit.unit _ (children position))
    have recovered := congrArg (fun presented =>
      presented.app (S.polynomial.Free (worlds.obj world)) PUnit.unit sort ⟨operator, inputs⟩ action)
      (toLaw_fromLaw Actions law)
    have issued : law.app (S.polynomial.Free (worlds.obj world)) PUnit.unit sort
        ⟨operator, inputs⟩ action =
      some (S.rename (assignmentAt Actions guard inputs matching) target) := by
      change instantiate Actions (fromLaw Actions law) operator inputs action = _ at recovered
      rw [instantiate_eq_at Actions (fromLaw Actions law) operator guard inputs matching] at recovered
      have calculates : instantiateAt Actions (fromLaw Actions law) operator guard inputs matching action =
          some (S.rename (assignmentAt Actions guard inputs matching) target) := by
        simp only [instantiateAt, conclusion, Option.map_some]
      exact recovered.symm.trans calculates
    exact (Operational.coalgebra_node law (steps.app world) operator children action).trans
      (congrArg (Option.map (IndexedPolynomial.Free.join S.polynomial)) issued)

/-- The full guarded premise is transported by the actual operational edge action. -/
theorem constructorGuard_map {first second : Cᵒᵖ} (change : first ⟶ second)
    {sort : S.Srt} (operator : S.Operator sort)
    (children : ∀ position, S.Term (worlds.obj first) (S.argument operator position))
    (guard : Guard Actions operator)
    (matching : inputGuard Actions (fun position =>
      (children position, Operational.coalgebra law (steps.app first) PUnit.unit _ (children position))) = guard) :
    inputGuard Actions (fun position =>
      (S.rename (worlds.map change) (children position),
        Operational.coalgebra law (steps.app second) PUnit.unit _
          (S.rename (worlds.map change) (children position)))) = guard := by
  let mapping : S.polynomial.Free (worlds.obj first) ⟶ S.polynomial.Free (worlds.obj second) :=
    S.termMonad.map (worlds.map change)
  let inputs : BehaviourArguments S Actions (S.polynomial.Free (worlds.obj first)) operator :=
    fun position => (children position, Operational.coalgebra law (steps.app first) PUnit.unit _ (children position))
  have transport : (fun position =>
      (S.rename (worlds.map change) (children position),
        Operational.coalgebra law (steps.app second) PUnit.unit _
          (S.rename (worlds.map change) (children position)))) =
      mapArguments Actions mapping inputs := by
    funext position
    apply Prod.ext
    · rfl
    · funext action
      exact step_map law worlds steps change _ (children position) action
  exact (congrArg (inputGuard Actions) transport).trans
    ((inputGuard_map Actions mapping inputs).trans matching)

/-- The guarded behavior constructor itself is an actual contextual natural map. -/
theorem behaviorRule_natural {Origins : Type u} (origin : Origins)
    {first second : Cᵒᵖ} (change : first ⟶ second)
    {sort : S.Srt} (operator : S.Operator sort)
    (children : ∀ position, S.Term (worlds.obj first) (S.argument operator position))
    (guard : Guard Actions operator) (action : Actions sort)
    (target : S.Term (ruleVariables Actions operator guard) sort)
    (matching : inputGuard Actions (fun position =>
      (children position, Operational.coalgebra law (steps.app first) PUnit.unit _ (children position))) = guard)
    (conclusion : fromLaw Actions law sort operator guard action = some target) :
    mapEvent law worlds steps change
        (behaviorRule law worlds steps origin first operator children guard action target matching conclusion) =
      behaviorRule law worlds steps origin second operator
        (fun position => S.rename (worlds.map change) (children position)) guard action target
        (constructorGuard_map law worlds steps change operator children guard matching) conclusion := by
  have sources : (mapEvent law worlds steps change
        (behaviorRule law worlds steps origin first operator children guard action target matching conclusion)).source =
      (behaviorRule law worlds steps origin second operator
        (fun position => S.rename (worlds.map change) (children position)) guard action target
        (constructorGuard_map law worlds steps change operator children guard matching) conclusion).source :=
    IndexedPolynomial.Free.map_node S.polynomial (fun base index => worlds.map change base index) operator children
  apply Event.ext
  · rfl
  · exact sources
  · rfl
  · have carried := (mapEvent law worlds steps change
        (behaviorRule law worlds steps origin first operator children guard action target matching conclusion)).valid
    have issued := (behaviorRule law worlds steps origin second operator
      (fun position => S.rename (worlds.map change) (children position)) guard action target
      (constructorGuard_map law worlds steps change operator children guard matching) conclusion).valid
    rw [sources] at carried
    exact Option.some.inj (carried.symm.trans issued)

/-- A selected operational edge at one fixed source, before target evidence. -/
abbrev SourceEdgeFibre (Origins : Type u) (sort : S.Srt) (world : Cᵒᵖ)
    (source : S.Term (worlds.obj world) sort) :=
  { event : Event law worlds steps Origins sort world // event.source = source }

/-- The source-indexed edge action preserves the actual selected occurrence. -/
noncomputable def mapSourceEdge {Origins : Type u} {sort : S.Srt}
    {first second : Cᵒᵖ} (change : first ⟶ second)
    {source : S.Term (worlds.obj first) sort}
    (edge : SourceEdgeFibre law worlds steps Origins sort first source) :
    SourceEdgeFibre law worlds steps Origins sort second (S.rename (worlds.map change) source) :=
  ⟨mapEvent law worlds steps change edge.val, congrArg (S.rename (worlds.map change)) edge.property⟩

/-- A guarded application retains every separately supplied selected premise
edge as well as the derived conclusion. The complete guard is additional
data: one selected edge does not describe every absent input action. -/
@[ext] structure FibreOccurrence (PremiseOrigins ConclusionOrigins : Type u)
    (world : Cᵒᵖ) {sort : S.Srt} (operator : S.Operator sort)
    (children : ∀ position, S.Term (worlds.obj world) (S.argument operator position)) where
  premises : ∀ position,
    SourceEdgeFibre law worlds steps PremiseOrigins (S.argument operator position) world (children position)
  result : SourceEdgeFibre law worlds steps ConclusionOrigins sort world
    (IndexedPolynomial.Free.node S.polynomial operator children)

/-- The literal product of selected source fibres produces a conclusion
fibre only with the separately admitted full guard and checked schema rule. -/
noncomputable def guardedSourceFibre {PremiseOrigins ConclusionOrigins : Type u}
    (origin : ConclusionOrigins) (world : Cᵒᵖ)
    {sort : S.Srt} (operator : S.Operator sort)
    (children : ∀ position, S.Term (worlds.obj world) (S.argument operator position))
    (premises : ∀ position,
      SourceEdgeFibre law worlds steps PremiseOrigins (S.argument operator position) world (children position))
    (guard : Guard Actions operator) (action : Actions sort)
    (target : S.Term (ruleVariables Actions operator guard) sort)
    (matching : inputGuard Actions (fun position =>
      (children position, Operational.coalgebra law (steps.app world) PUnit.unit _ (children position))) = guard)
    (conclusion : fromLaw Actions law sort operator guard action = some target) :
    FibreOccurrence law worlds steps PremiseOrigins ConclusionOrigins world operator children where
  premises := premises
  result := ⟨behaviorRule law worlds steps origin world operator children guard action target matching conclusion, rfl⟩

/-- Each selected premise really supplies an available action in the
separately supplied complete guard. Its exact endpoint remains in the fibre. -/
theorem selected_premise_available {PremiseOrigins : Type u} (world : Cᵒᵖ)
    {sort : S.Srt} (operator : S.Operator sort)
    (children : ∀ position, S.Term (worlds.obj world) (S.argument operator position))
    (premises : ∀ position,
      SourceEdgeFibre law worlds steps PremiseOrigins (S.argument operator position) world (children position))
    (guard : Guard Actions operator)
    (matching : inputGuard Actions (fun position =>
      (children position, Operational.coalgebra law (steps.app world) PUnit.unit _ (children position))) = guard)
    (position : S.Position operator) :
    guard ⟨position, (premises position).val.action⟩ = true := by
  have offered := (premises position).val.valid
  rw [(premises position).property] at offered
  rw [← matching]
  change (Operational.coalgebra law (steps.app world) PUnit.unit _
    (children position) (premises position).val.action).isSome = true
  rw [offered]
  rfl

/-- The real native edge fibre retains a complete occurrence and its target evidence. -/
noncomputable def sourceFibreEquiv (Origins : Type u) (sort : S.Srt)
    (postcondition : DisplayedPresheafTransport.DisplayedFamily (terms worlds sort))
    (world : Cᵒᵖ) (source : (terms worlds sort).obj world) :=
  (eventSpan law worlds steps Origins sort).fibreEquiv postcondition world source

end Mettapedia.OSLF.DeterministicGSOS.EdgeReadout
