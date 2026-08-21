import Mettapedia.GSLT.Core.GSLT

/-!
# The loose-relation equipment core

The semantic distinction needed by GSLT-IL is already visible over types:

* tight arrows are functions;
* loose arrows are proof-relevant relations;
* cells map relation witnesses along their two tight boundaries;
* horizontal composition retains the intermediate object and both witnesses.

This module proves the horizontal unit and associativity equivalences, cell
composition and interchange, and the exact criterion for a loose arrow to be
represented by the companion of a function.  It is the small algebraic core
forced by the GSLT-IL route laws, not a duplicate implementation of a general
pseudo-double-category library.

A proof-relevant loose arrow is representable precisely when every source has
one contractible target/evidence fibre.  Functionality alone is insufficient:
a partial deterministic relation is still not a companion.
-/

namespace Mettapedia.GSLT.LooseRelationEquipment

universe u

/-- A proof-relevant relation.  Its inhabitants retain occurrence and route
evidence that a proposition-valued relation would erase. -/
abbrev Loose (Source Target : Type u) := Source -> Target -> Type u

/-- Equality retained as data in the ambient universe of a loose arrow. -/
abbrev EqWitness (left right : α) : Type u :=
  ULift.{u} (PLift (left = right))

instance instSubsingletonEqWitness (left right : α) :
    Subsingleton (EqWitness.{u} left right) where
  allEq first second := by
    rcases first with ⟨⟨firstProof⟩⟩
    rcases second with ⟨⟨secondProof⟩⟩
    congr

/-- The horizontal identity loose arrow. -/
def identity {Object : Type u} : Loose Object Object :=
  fun source target => EqWitness source target

/-- Horizontal composition retains the selected intermediate object and both
relation witnesses. -/
def comp {First Middle Last : Type u}
    (earlier : Loose First Middle) (later : Loose Middle Last) :
    Loose First Last :=
  fun source target =>
    Sigma fun middle => earlier source middle × later middle target

/-- A square between loose arrows with functional left and right boundaries. -/
structure Cell {Source Target Source' Target' : Type u}
    (left : Source -> Source') (right : Target -> Target')
    (top : Loose Source Target) (bottom : Loose Source' Target') where
  map : forall {source target},
    top source target -> bottom (left source) (right target)

namespace Cell

@[ext]
theorem ext {Source Target Source' Target' : Type u}
    {left : Source -> Source'} {right : Target -> Target'}
    {top : Loose Source Target} {bottom : Loose Source' Target'}
    {first second : Cell left right top bottom}
    (same : forall source target (witness : top source target),
      first.map witness = second.map witness) :
    first = second := by
  cases first with
  | mk firstMap =>
      cases second with
      | mk secondMap =>
          congr
          funext source target witness
          exact same source target witness

/-- Identity cell on one loose arrow. -/
def id {Source Target : Type u} (relation : Loose Source Target) :
    Cell (_root_.id : Source -> Source) (_root_.id : Target -> Target)
      relation relation where
  map witness := witness

/-- Vertical composition of cells. -/
def vcomp {Source Target Source' Target' Source'' Target'' : Type u}
    {left : Source -> Source'} {right : Target -> Target'}
    {left' : Source' -> Source''} {right' : Target' -> Target''}
    {top : Loose Source Target} {middle : Loose Source' Target'}
    {bottom : Loose Source'' Target''}
    (upper : Cell left right top middle)
    (lower : Cell left' right' middle bottom) :
    Cell (left' ∘ left) (right' ∘ right) top bottom where
  map witness := lower.map (upper.map witness)

/-- Horizontal composition of cells.  The shared middle boundary maps the
retained intermediate object. -/
def hcomp {First Middle Last First' Middle' Last' : Type u}
    {left : First -> First'} {middle : Middle -> Middle'}
    {right : Last -> Last'}
    {topEarlier : Loose First Middle} {topLater : Loose Middle Last}
    {bottomEarlier : Loose First' Middle'}
    {bottomLater : Loose Middle' Last'}
    (earlier : Cell left middle topEarlier bottomEarlier)
    (later : Cell middle right topLater bottomLater) :
    Cell left right (comp topEarlier topLater)
      (comp bottomEarlier bottomLater) where
  map witness :=
    ⟨middle witness.1, earlier.map witness.2.1, later.map witness.2.2⟩

@[simp] theorem id_map {Source Target : Type u}
    (relation : Loose Source Target) {source target}
    (witness : relation source target) :
    (id relation).map witness = witness :=
  rfl

@[simp] theorem vcomp_map
    {Source Target Source' Target' Source'' Target'' : Type u}
    {left : Source -> Source'} {right : Target -> Target'}
    {left' : Source' -> Source''} {right' : Target' -> Target''}
    {top : Loose Source Target} {middle : Loose Source' Target'}
    {bottom : Loose Source'' Target''}
    (upper : Cell left right top middle)
    (lower : Cell left' right' middle bottom)
    {source target} (witness : top source target) :
    (vcomp upper lower).map witness = lower.map (upper.map witness) :=
  rfl

theorem vcomp_id_left
    {Source Target Source' Target' : Type u}
    {left : Source -> Source'} {right : Target -> Target'}
    {top : Loose Source Target} {bottom : Loose Source' Target'}
    (cell : Cell left right top bottom) :
    vcomp (id top) cell = cell := by
  ext source target witness
  rfl

theorem vcomp_id_right
    {Source Target Source' Target' : Type u}
    {left : Source -> Source'} {right : Target -> Target'}
    {top : Loose Source Target} {bottom : Loose Source' Target'}
    (cell : Cell left right top bottom) :
    vcomp cell (id bottom) = cell := by
  ext source target witness
  rfl

theorem vcomp_assoc
    {A B A' B' A'' B'' A''' B''' : Type u}
    {f : A -> A'} {g : B -> B'}
    {f' : A' -> A''} {g' : B' -> B''}
    {f'' : A'' -> A'''} {g'' : B'' -> B'''}
    {first : Loose A B} {second : Loose A' B'}
    {third : Loose A'' B''} {fourth : Loose A''' B'''}
    (top : Cell f g first second)
    (middle : Cell f' g' second third)
    (bottom : Cell f'' g'' third fourth) :
    vcomp (vcomp top middle) bottom = vcomp top (vcomp middle bottom) := by
  ext source target witness
  rfl

/-- The generating interchange law: horizontal and vertical composition of
cells agree without discarding the retained middle witness. -/
theorem interchange
    {A B C A' B' C' A'' B'' C'' : Type u}
    {fa : A -> A'} {fb : B -> B'} {fc : C -> C'}
    {ga : A' -> A''} {gb : B' -> B''} {gc : C' -> C''}
    {r : Loose A B} {s : Loose B C}
    {r' : Loose A' B'} {s' : Loose B' C'}
    {r'' : Loose A'' B''} {s'' : Loose B'' C''}
    (upperLeft : Cell fa fb r r') (upperRight : Cell fb fc s s')
    (lowerLeft : Cell ga gb r' r'') (lowerRight : Cell gb gc s' s'') :
    hcomp (vcomp upperLeft lowerLeft) (vcomp upperRight lowerRight) =
      vcomp (hcomp upperLeft upperRight) (hcomp lowerLeft lowerRight) := by
  ext source target witness
  rfl

end Cell

/-! ## Horizontal coherence, fibrewise -/

/-- Left horizontal unitor. -/
def compIdentityLeft {Source Target : Type u} (relation : Loose Source Target)
    (source : Source) (target : Target) :
    comp identity relation source target ≃ relation source target where
  toFun witness := by
    rcases witness with ⟨middle, same, related⟩
    cases same.down.down
    exact related
  invFun related := ⟨source, ⟨⟨rfl⟩⟩, related⟩
  left_inv witness := by
    rcases witness with ⟨middle, same, related⟩
    cases same.down.down
    rfl
  right_inv _ := rfl

/-- Right horizontal unitor. -/
def compIdentityRight {Source Target : Type u}
    (relation : Loose Source Target) (source : Source) (target : Target) :
    comp relation identity source target ≃ relation source target where
  toFun witness := by
    rcases witness with ⟨middle, related, same⟩
    cases same.down.down
    exact related
  invFun related := ⟨target, related, ⟨⟨rfl⟩⟩⟩
  left_inv witness := by
    rcases witness with ⟨middle, related, same⟩
    cases same.down.down
    rfl
  right_inv _ := rfl

/-- Horizontal associator.  Both sides retain exactly the same two
intermediate objects and three witnesses. -/
def compAssoc {A B C D : Type u}
    (first : Loose A B) (second : Loose B C) (third : Loose C D)
    (source : A) (target : D) :
    comp (comp first second) third source target ≃
      comp first (comp second third) source target where
  toFun witness :=
    ⟨witness.2.1.1, witness.2.1.2.1,
      ⟨witness.1, witness.2.1.2.2, witness.2.2⟩⟩
  invFun witness :=
    ⟨witness.2.2.1, ⟨witness.1, witness.2.1, witness.2.2.2.1⟩,
      witness.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## Companions and the exact representation criterion -/

/-- The companion loose arrow represented by a tight function. -/
def companion {Source Target : Type u} (map : Source -> Target) :
    Loose Source Target :=
  fun source target => EqWitness (map source) target

/-- The oppositely directed conjoint of a tight function. -/
def conjoint {Source Target : Type u} (map : Source -> Target) :
    Loose Target Source :=
  fun target source => EqWitness target (map source)

/-- A representability license identifies every proof-relevant fibre with
the companion fibre of one direct map. -/
structure Representation {Source Target : Type u}
    (relation : Loose Source Target) where
  map : Source -> Target
  exact : forall source target,
    relation source target ≃ companion map source target

namespace Representation

/-- A companion represents itself. -/
def companionSelf {Source Target : Type u} (map : Source -> Target) :
    Representation (companion map) where
  map := map
  exact _ _ := Equiv.refl _

/-- Every represented source has an inhabited total target/evidence fibre. -/
theorem total {Source Target : Type u} {relation : Loose Source Target}
    (representation : Representation relation) :
    forall source, Nonempty (Sigma fun target => relation source target) := by
  intro source
  exact ⟨representation.map source,
    (representation.exact source (representation.map source)).symm
      ⟨⟨rfl⟩⟩⟩

/-- Every represented source has at most one target together with its retained
relation witness. -/
theorem deterministic {Source Target : Type u}
    {relation : Loose Source Target}
    (representation : Representation relation) :
    forall source, Subsingleton (Sigma fun target => relation source target) := by
  intro source
  constructor
  rintro ⟨firstTarget, firstWitness⟩ ⟨secondTarget, secondWitness⟩
  have firstEq :=
    (representation.exact source firstTarget firstWitness).down.down
  have secondEq :=
    (representation.exact source secondTarget secondWitness).down.down
  have targetEq : firstTarget = secondTarget := firstEq.symm.trans secondEq
  cases targetEq
  have witnessEq : firstWitness = secondWitness :=
    (representation.exact source firstTarget).injective
      ((instSubsingletonEqWitness _ _).allEq _ _)
  cases witnessEq
  rfl

end Representation

/-- Totality of a loose arrow on its admitted source fibre. -/
def Total {Source Target : Type u} (relation : Loose Source Target) : Prop :=
  forall source, Nonempty (Sigma fun target => relation source target)

/-- Determinism includes occurrence evidence: each source has at most one
target/witness pair, not merely at most one target. -/
def Deterministic {Source Target : Type u}
    (relation : Loose Source Target) : Prop :=
  forall source, Subsingleton (Sigma fun target => relation source target)

namespace Representation

/-- Proof-relevant determinism also makes each fixed-target witness fibre a
subsingleton. -/
theorem fibreSubsingleton {Source Target : Type u}
    {relation : Loose Source Target} (deterministic : Deterministic relation)
    (source : Source) (target : Target) :
    Subsingleton (relation source target) := by
  constructor
  intro first second
  have pairEq :
      (⟨target, first⟩ : Sigma fun output => relation source output) =
        ⟨target, second⟩ :=
    (deterministic source).allEq _ _
  cases pairEq
  rfl

/-- Represented loose arrows remain proof-relevantly deterministic under
horizontal composition. -/
theorem horizontalCompDeterministic
    {First Middle Last : Type u}
    {earlier : Loose First Middle} {later : Loose Middle Last}
    (earlierRepresentation : Representation earlier)
    (laterRepresentation : Representation later) :
    Deterministic (LooseRelationEquipment.comp earlier later) := by
  intro source
  constructor
  rintro ⟨firstTarget, firstMiddle, firstEarlier, firstLater⟩
    ⟨secondTarget, secondMiddle, secondEarlier, secondLater⟩
  have middleEq :
      (⟨firstMiddle, firstEarlier⟩ :
        Sigma fun middle => earlier source middle) =
      ⟨secondMiddle, secondEarlier⟩ :=
    (earlierRepresentation.deterministic source).allEq _ _
  cases middleEq
  have targetEq :
      (⟨firstTarget, firstLater⟩ :
        Sigma fun target => later firstMiddle target) =
      ⟨secondTarget, secondLater⟩ :=
    (laterRepresentation.deterministic firstMiddle).allEq _ _
  cases targetEq
  rfl

/-- Companions compose: once both loose arrows are admitted, their retained
relational composite compiles to ordinary function composition. -/
def horizontalComp
    {First Middle Last : Type u}
    {earlier : Loose First Middle} {later : Loose Middle Last}
    (earlierRepresentation : Representation earlier)
    (laterRepresentation : Representation later) :
    Representation (LooseRelationEquipment.comp earlier later) where
  map := laterRepresentation.map ∘ earlierRepresentation.map
  exact source target :=
    { toFun := fun witness => by
        rcases witness with ⟨middle, earlierWitness, laterWitness⟩
        have earlierEq :=
          (earlierRepresentation.exact source middle earlierWitness).down.down
        have laterEq :=
          (laterRepresentation.exact middle target laterWitness).down.down
        exact ⟨⟨congrArg laterRepresentation.map earlierEq |>.trans laterEq⟩⟩
      invFun := fun same =>
        ⟨earlierRepresentation.map source,
          (earlierRepresentation.exact source
            (earlierRepresentation.map source)).symm ⟨⟨rfl⟩⟩,
          (laterRepresentation.exact (earlierRepresentation.map source)
            target).symm same⟩
      left_inv := fun witness =>
        (fibreSubsingleton
          (horizontalCompDeterministic earlierRepresentation
            laterRepresentation) source target).allEq _ witness
      right_inv := fun witness =>
        (instSubsingletonEqWitness _ _).allEq _ witness }

/-- The direct map extracted from a composite license is definitionally the
composition of the two admitted direct maps. -/
@[simp] theorem horizontalComp_map
    {First Middle Last : Type u}
    {earlier : Loose First Middle} {later : Loose Middle Last}
    (earlierRepresentation : Representation earlier)
    (laterRepresentation : Representation later) :
    (horizontalComp earlierRepresentation laterRepresentation).map =
      laterRepresentation.map ∘ earlierRepresentation.map :=
  rfl

/-- Total proof-relevant determinism constructs a direct map.  The map is
chosen once at admission; executing it performs no relational search. -/
noncomputable def ofTotalDeterministic
    {Source Target : Type u} {relation : Loose Source Target}
    (total : Total relation) (deterministic : Deterministic relation) :
    Representation relation where
  map source := (Classical.choice (total source)).1
  exact source target :=
    { toFun := fun witness => by
        let selected := Classical.choice (total source)
        have pairEq : selected = ⟨target, witness⟩ :=
          (deterministic source).allEq _ _
        exact ⟨⟨congrArg Sigma.fst pairEq⟩⟩
      invFun := fun same => by
        let selected := Classical.choice (total source)
        have selectedWitness : relation source selected.1 := selected.2
        cases same.down.down
        exact selectedWitness
      left_inv := fun witness => by
        apply (show Subsingleton (relation source target) from
          { allEq := fun first second => by
              have pairEq :
                  (⟨target, first⟩ : Sigma fun output => relation source output) =
                    ⟨target, second⟩ :=
                (deterministic source).allEq _ _
              cases pairEq
              rfl }).allEq
      right_inv := fun first =>
        (instSubsingletonEqWitness _ _).allEq _ first }

/-- Representability is exactly total, proof-relevant determinism. -/
theorem nonempty_iff_total_and_deterministic
    {Source Target : Type u} {relation : Loose Source Target} :
    Nonempty (Representation relation) ↔
      Total relation ∧ Deterministic relation := by
  constructor
  · rintro ⟨representation⟩
    exact ⟨representation.total, representation.deterministic⟩
  · rintro ⟨total, deterministic⟩
    exact ⟨ofTotalDeterministic total deterministic⟩

end Representation

/-! ## Strict positive and negative controls -/

namespace Canary

/-- Equality on booleans is the companion of the identity function. -/
def exactBool : Loose Bool Bool := identity

def exactBoolRepresentation : Representation exactBool :=
  Representation.companionSelf _root_.id

theorem exactBool_representable :
    Nonempty (Representation exactBool) :=
  ⟨exactBoolRepresentation⟩

/-- A raw relation may choose either Boolean from its sole source. -/
def choice : Loose Unit Bool := fun _ _ => Unit

theorem choice_executes_both :
    Nonempty (choice () false) ∧ Nonempty (choice () true) :=
  ⟨⟨()⟩, ⟨()⟩⟩

/-- Nondeterministic raw execution cannot be represented by one direct map. -/
theorem choice_not_representable :
    Not (Nonempty (Representation choice)) := by
  rintro ⟨representation⟩
  have falseEq := (representation.exact () false ()).down.down
  have trueEq := (representation.exact () true ()).down.down
  exact Bool.false_ne_true (falseEq.symm.trans trueEq)

/-- This relation is single-valued wherever it fires, but is undefined at
`true`. -/
def partialRelation : Loose Bool Unit
  | false, () => Unit
  | true, () => Empty

theorem partial_deterministic : Deterministic partialRelation := by
  intro source
  constructor
  rintro ⟨firstTarget, first⟩ ⟨secondTarget, second⟩
  cases source with
  | false =>
      cases firstTarget
      cases secondTarget
      rfl
  | true => exact first.elim

theorem partial_not_total : Not (Total partialRelation) := by
  intro total
  obtain ⟨target, witness⟩ := Classical.choice (total true)
  cases target
  exact witness.elim

/-- Functionality without totality does not earn a companion. -/
theorem partial_not_representable :
    Not (Nonempty (Representation partialRelation)) := by
  intro represented
  exact partial_not_total
    ((Representation.nonempty_iff_total_and_deterministic).mp represented).1

end Canary

#print axioms Cell.interchange
#print axioms compAssoc
#print axioms Representation.nonempty_iff_total_and_deterministic
#print axioms Canary.choice_not_representable
#print axioms Canary.partial_not_representable

end Mettapedia.GSLT.LooseRelationEquipment
