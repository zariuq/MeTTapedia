import Mettapedia.OSLF.Syntax.CategoricalScopedEventPremise

/-!
# Ordered conditional rule inputs in a closed target

A conditional rule may require several individual firing witnesses, each
under its own binder context. Its input object is an iterated pullback over
one shared assignment of the rule's parameters. This construction retains
each ordered witness and enforces every requested endpoint equation.

A rule action maps that complete input object to a conclusion event, with
its observed endpoints equal to the authored conclusion. This is the
target-side semantic contract for conditional operational rules; a free
classifier must generate its initial lawful instance.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalScopedRuleAction

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalScopedEventPremise

universe u v
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]
variable {X E Q : D}

/-- One premise with its own binder object, sharing the rule's parameter,
event and endpoint objects with the other premises. -/
structure Premise (X E Q : D) where
  binder : D
  request : Request binder X E Q

/-- Re-expressing the same premise under an equality of list entries does
not change its shared parameter assignment. -/
theorem premise_transport_parameters {first second : Premise X E Q}
    (same : first = second) :
    eqToHom (congrArg
        (fun premise : Premise X E Q => Witness premise.request) same) ≫
      parameters second.request = parameters first.request := by
  cases same
  simp

/-- Transporting the presentation of a premise leaves its retained event
function unchanged, apart from the same binder-object equality transport. -/
theorem premise_transport_event {first second : Premise X E Q}
    (same : first = second) :
    eqToHom (congrArg
        (fun premise : Premise X E Q => Witness premise.request) same) ≫
      event second.request =
    event first.request ≫
      eqToHom (congrArg
        (fun premise : Premise X E Q =>
          (ihom premise.binder).obj E) same) := by
  cases same
  simp

/-- Repeated pullbacks retain all ordered premise witnesses over one
parameter assignment. The empty family has exactly its parameter object. -/
noncomputable def bundleData : (premises : List (Premise X E Q)) →
    Σ object : D, object ⟶ X
  | [] => ⟨X, 𝟙 X⟩
  | first :: rest =>
      let tail := bundleData rest
      ⟨pullback (parameters first.request) tail.2,
        pullback.fst _ _ ≫ parameters first.request⟩

noncomputable abbrev Bundle (premises : List (Premise X E Q)) : D :=
  (bundleData premises).1

noncomputable def assignment (premises : List (Premise X E Q)) :
    Bundle premises ⟶ X :=
  (bundleData premises).2

/-- Read the first individual premise witness. -/
noncomputable def head (first : Premise X E Q)
    (rest : List (Premise X E Q)) :
    Bundle (first :: rest) ⟶ Witness first.request :=
  pullback.fst _ _

/-- Retain the remaining ordered premise witnesses. -/
noncomputable def tail (first : Premise X E Q)
    (rest : List (Premise X E Q)) :
    Bundle (first :: rest) ⟶ Bundle rest :=
  pullback.snd _ _

/-- The first and remaining witnesses belong to the same parameter
assignment. The equality is the pullback condition, not an assumption. -/
theorem head_tail_assignment (first : Premise X E Q)
    (rest : List (Premise X E Q)) :
    head first rest ≫ parameters first.request =
      tail first rest ≫ assignment rest := by
  exact pullback.condition

/-- Select the individual witness at its original list position. -/
noncomputable def project :
    (premises : List (Premise X E Q)) →
      (position : Fin premises.length) →
        Bundle premises ⟶ Witness (premises.get position).request
  | [], position => Fin.elim0 position
  | first :: rest, ⟨0, _⟩ => head first rest
  | first :: rest, ⟨position + 1, bound⟩ =>
      tail first rest ≫ project rest
        ⟨position, Nat.lt_of_succ_lt_succ bound⟩

/-- Every projected premise witness uses the same rule-parameter
assignment, even when two premise positions have equal endpoint pairs. -/
theorem project_assignment :
    ∀ (premises : List (Premise X E Q))
      (position : Fin premises.length),
      project premises position ≫
          parameters (premises.get position).request =
        assignment premises
  | [], position => Fin.elim0 position
  | first :: rest, ⟨0, _⟩ => rfl
  | first :: rest, ⟨position + 1, bound⟩ => by
      let tailPosition : Fin rest.length :=
        ⟨position, Nat.lt_of_succ_lt_succ bound⟩
      change (tail first rest ≫ project rest tailPosition) ≫
          parameters (rest.get tailPosition).request = assignment (first :: rest)
      rw [Category.assoc, project_assignment rest tailPosition]
      exact (head_tail_assignment first rest).symm

/-- Independent data for a family of conditional premises: one shared
parameter assignment and one individual event witness at each ordered
position, with every witness over that same assignment. -/
structure Cone (Z : D) (premises : List (Premise X E Q)) where
  parameter : Z ⟶ X
  witness : (position : Fin premises.length) →
    Z ⟶ Witness (premises.get position).request
  agrees : ∀ position, witness position ≫
    parameters (premises.get position).request = parameter

@[ext] theorem Cone.ext {Z : D} {premises : List (Premise X E Q)}
    {first second : Cone Z premises}
    (parameter : first.parameter = second.parameter)
    (witness : first.witness = second.witness) : first = second := by
  cases first with
  | mk firstParameter firstWitness firstAgrees =>
    cases second with
    | mk secondParameter secondWitness secondAgrees =>
      cases parameter
      cases witness
      rfl

/-- A map into the iterated pullback determines all its ordered premise
witnesses and their common parameter assignment. -/
noncomputable def coneOfMap {Z : D}
    (premises : List (Premise X E Q))
    (arrow : Z ⟶ Bundle premises) : Cone Z premises where
  parameter := arrow ≫ assignment premises
  witness position := arrow ≫ project premises position
  agrees position := by
    rw [Category.assoc, project_assignment premises position]

/-- Forget the first witness of a cone while retaining its assignment and
the remaining positions in their original order. -/
def Cone.rest {Z : D} {first : Premise X E Q}
    {rest : List (Premise X E Q)}
    (cone : Cone Z (first :: rest)) : Cone Z rest where
  parameter := cone.parameter
  witness position := cone.witness position.succ
  agrees position := cone.agrees position.succ

/-- Every compatible family of ordered premise witnesses assembles into a
map to the shared pullback, with its original parameter assignment. -/
noncomputable def liftConeData {Z : D} :
    (premises : List (Premise X E Q)) →
      (cone : Cone Z premises) →
        {arrow : Z ⟶ Bundle premises //
          arrow ≫ assignment premises = cone.parameter}
  | [], cone => ⟨cone.parameter, by
      change cone.parameter ≫ 𝟙 X = cone.parameter
      simp⟩
  | first :: rest, cone => by
      let tailCone := Cone.rest cone
      let tailLift := liftConeData rest tailCone
      let firstWitness : Z ⟶ Witness first.request := cone.witness 0
      have compatible :
          firstWitness ≫ parameters first.request =
            tailLift.1 ≫ assignment rest :=
        (cone.agrees 0).trans tailLift.2.symm
      let combined := pullback.lift firstWitness tailLift.1 compatible
      refine ⟨combined, ?_⟩
      change combined ≫
          (pullback.fst _ _ ≫ parameters first.request) = cone.parameter
      calc
        combined ≫ (pullback.fst _ _ ≫ parameters first.request)
            = (combined ≫ pullback.fst _ _) ≫ parameters first.request :=
                (Category.assoc _ _ _).symm
        _ = firstWitness ≫ parameters first.request := by
              rw [pullback.lift_fst]
        _ = cone.parameter := cone.agrees 0

/-- Assemble the compatible witnesses as a map into the ordered premise
object. -/
noncomputable def liftCone {Z : D}
    (premises : List (Premise X E Q)) (cone : Cone Z premises) :
    Z ⟶ Bundle premises :=
  (liftConeData premises cone).1

theorem liftCone_assignment {Z : D}
    (premises : List (Premise X E Q)) (cone : Cone Z premises) :
    liftCone premises cone ≫ assignment premises = cone.parameter :=
  (liftConeData premises cone).2

/-- The assembled map recovers each firing witness in its original premise
position. -/
theorem liftCone_project {Z : D} :
    ∀ (premises : List (Premise X E Q)) (cone : Cone Z premises)
      (position : Fin premises.length),
      liftCone premises cone ≫ project premises position =
        cone.witness position
  | [], _, position => Fin.elim0 position
  | first :: rest, cone, ⟨0, _⟩ => by
      simp only [liftCone, liftConeData, project, head]
      exact pullback.lift_fst _ _ _
  | first :: rest, cone, ⟨position + 1, bound⟩ => by
      let tailPosition : Fin rest.length :=
        ⟨position, Nat.lt_of_succ_lt_succ bound⟩
      change liftCone (first :: rest) cone ≫
          (tail first rest ≫ project rest tailPosition) =
            cone.witness tailPosition.succ
      rw [← Category.assoc]
      have tailEquation :
          liftCone (first :: rest) cone ≫ tail first rest =
            liftCone rest (Cone.rest cone) := by
        simp only [liftCone, liftConeData, tail]
        exact pullback.lift_snd _ _ _
      rw [tailEquation, liftCone_project rest (Cone.rest cone) tailPosition]
      rfl

/-- The universal map recovers the cone of shared parameters and individual
ordered witnesses. -/
theorem coneOfMap_liftCone {Z : D}
    (premises : List (Premise X E Q)) (cone : Cone Z premises) :
    coneOfMap premises (liftCone premises cone) = cone := by
  apply Cone.ext
  · exact liftCone_assignment premises cone
  · funext position
    exact liftCone_project premises cone position

/-- The shared assignment and all ordered witness projections jointly
determine a map into the premise bundle. -/
theorem bundle_hom_ext {Z : D} :
    ∀ (premises : List (Premise X E Q))
      (first second : Z ⟶ Bundle premises),
      first ≫ assignment premises = second ≫ assignment premises →
      (∀ position, first ≫ project premises position =
        second ≫ project premises position) →
      first = second
  | [], first, second, hparameter, _ => by
      change (first : Z ⟶ X) ≫ 𝟙 X =
        (second : Z ⟶ X) ≫ 𝟙 X at hparameter
      exact (Category.comp_id (first : Z ⟶ X)).symm.trans
        (hparameter.trans (Category.comp_id (second : Z ⟶ X)))
  | premise :: rest, first, second, hparameter, hwitness => by
      apply pullback.hom_ext
      · have h := hwitness
          (⟨0, by simp⟩ : Fin (premise :: rest).length)
        change first ≫ pullback.fst _ _ =
          second ≫ pullback.fst _ _ at h
        exact h
      · apply bundle_hom_ext rest
          (first ≫ tail premise rest) (second ≫ tail premise rest)
        · calc
            (first ≫ tail premise rest) ≫ assignment rest =
                first ≫ assignment (premise :: rest) := by
                  rw [Category.assoc, ← head_tail_assignment]
                  rfl
            _ = second ≫ assignment (premise :: rest) := hparameter
            _ = (second ≫ tail premise rest) ≫ assignment rest := by
                  rw [Category.assoc, ← head_tail_assignment]
                  rfl
        · intro position
          have h := hwitness position.succ
          change first ≫ (tail premise rest ≫ project rest position) =
            second ≫ (tail premise rest ≫ project rest position) at h
          simpa only [Category.assoc] using h

/-- The ordered pullback is universal for compatible assignments of
individual binder-local event witnesses. -/
theorem liftCone_coneOfMap {Z : D}
    (premises : List (Premise X E Q))
    (arrow : Z ⟶ Bundle premises) :
    liftCone premises (coneOfMap premises arrow) = arrow := by
  apply bundle_hom_ext premises
  · exact liftCone_assignment premises (coneOfMap premises arrow)
  · intro position
    exact liftCone_project premises (coneOfMap premises arrow) position

/-- Hom maps into the ordered rule-input object are exactly compatible
families of premise firings with a common parameter assignment. -/
noncomputable def bundleConeEquiv {Z : D}
    (premises : List (Premise X E Q)) :
    (Z ⟶ Bundle premises) ≃ Cone Z premises where
  toFun := coneOfMap premises
  invFun := liftCone premises
  left_inv := liftCone_coneOfMap premises
  right_inv := coneOfMap_liftCone premises

/-- Position-preserving maps of ordered conditional inputs. Each individual
premise witness maps to the witness at the same position, and its parameter
assignment is unchanged. No injectivity or event coverage is required. -/
structure BundleMapData {E' : D}
    (source : List (Premise X E Q))
    (target : List (Premise X E' Q)) where
  sameLength : source.length = target.length
  witness : (position : Fin target.length) →
    Witness (source.get (position.cast sameLength.symm)).request ⟶
      Witness (target.get position).request
  preservesParameters : ∀ position,
    witness position ≫ parameters (target.get position).request =
      parameters (source.get (position.cast sameLength.symm)).request

/-- Maps the full ordered bundle using its pullback universal property.
Individual event witnesses are transported separately; their common
parameter assignment is retained. -/
noncomputable def mapBundle {E' : D}
    {source : List (Premise X E Q)}
    {target : List (Premise X E' Q)}
    (data : BundleMapData source target) : Bundle source ⟶ Bundle target :=
  liftCone target {
    parameter := assignment source
    witness position :=
      project source (position.cast data.sameLength.symm) ≫
        data.witness position
    agrees position := by
      rw [Category.assoc, data.preservesParameters]
      exact project_assignment source (position.cast data.sameLength.symm)
  }

/-- Bundle transport leaves the shared authored parameter assignment
unchanged. -/
theorem mapBundle_assignment {E' : D}
    {source : List (Premise X E Q)}
    {target : List (Premise X E' Q)}
    (data : BundleMapData source target) :
    mapBundle data ≫ assignment target = assignment source := by
  exact liftCone_assignment target _

/-- Bundle transport maps each retained premise firing at its original
position. Equal endpoints do not cause two witnesses to be merged. -/
theorem mapBundle_project {E' : D}
    {source : List (Premise X E Q)}
    {target : List (Premise X E' Q)}
    (data : BundleMapData source target)
    (position : Fin target.length) :
    mapBundle data ≫ project target position =
      project source (position.cast data.sameLength.symm) ≫
        data.witness position := by
  exact liftCone_project target _ position

/-- The rule conclusion is itself an individual event whose endpoints are
the declared conclusion under the same parameter assignment. -/
structure RuleAction (premises : List (Premise X E Q))
    (endpoints : E ⟶ Q) (conclusion : X ⟶ Q) where
  fire : Bundle premises ⟶ E
  endpoint_law : fire ≫ endpoints = assignment premises ≫ conclusion

/-- A rule with no premises has parameter object as its full input object.
This boundary case does not erase the conclusion event or its endpoint law. -/
noncomputable def emptyBundleIso : Bundle ([] : List (Premise X E Q)) ≅ X :=
  Iso.refl X

end Mettapedia.OSLF.Binding.CategoricalScopedRuleAction

#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleAction.head_tail_assignment
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleAction.premise_transport_event
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleAction.project_assignment
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleAction.liftConeData
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleAction.bundleConeEquiv
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleAction.mapBundle
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleAction.mapBundle_assignment
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleAction.mapBundle_project
