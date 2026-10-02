import Mettapedia.GSLT.Core.LooseRelationEquipment
import Mettapedia.GSLT.Scope.ConsumerDescent

/-!
# Gluing views: holonomy and the cocycle condition

A **view system** over an index graph has a view at every index and, along
every edge, a translation between the two views, an equivalence
(`ViewSystem`).  Walks cross edges in either direction (`ViewSystem.Walk`),
and a walk transports values between the views at its ends
(`ViewSystem.transport`).  The **holonomy** of a closed walk is its
transport, and the system has **trivial holonomy** when every closed walk
transports every value to itself (`TrivialHolonomy`); equivalently, parallel
walks transport alike (`trivialHolonomy_iff_pathIndependent`).

**Gluing.**  A gluing is one global view with an equivalence onto every view,
compatible with every translation (`Gluing`).
* A gluing forces trivial holonomy (`Gluing.trivialHolonomy`): the transport
  along any walk is the change of chart (`Gluing.transport_chart`).
* Conversely, when every index is reached from a root (connectivity as a
  truncated walk, no chosen spanning tree needed), trivial holonomy builds a
  gluing, without choice (`gluingOfTrivialHolonomy`).
* So on a connected index graph **the views glue exactly when every cycle has
  trivial holonomy** (`nonempty_gluing_iff`): this is the Čech 1-cocycle
  condition.
* The global view is canonical: on a connected index graph it is
  equivalent to the global sections, the limit of the system
  (`Gluing.sectionsEquiv`, `sectionsEquivOfTrivialHolonomy`).
* Trivial holonomy is exactly descent of the transport to the thin view of
  the index graph, where parallel walks are identified
  (`trivialHolonomy_iff_descends`).  In that thin view identity is
  proof-irrelevant; compare `all_descend_iff_uip` for identity structures.

**Controls on a three-cycle** of boolean views whose translations are the
identity, the identity and negation (`Twisted`):
* every translation is an equivalence, yet the cycle's holonomy is negation
  (`Twisted.holonomy_moves`), so there is no gluing (`Twisted.no_gluing`) and
  no global section (`Twisted.no_sections`);
* dropping the twisted edge leaves a path, which glues (`Twisted.path_glues`).

**Relational holonomy.**  For a cycle of proof-relevant relations, global
sections are exactly the fixed points of the cycle's composite relation
(`cycleSectionEquiv`); for functions, fixed points of the holonomy
(`functionalLoop_iff`).  A global section can exist without a gluing: on
three points, a cycle whose holonomy swaps two points and fixes the third has
a section and no gluing (`Swap.section_exists`, `Swap.no_gluing`).  So
sections (existence of a compatible family) and gluing (a global view) are
different obstructions.  Along equivalences, sections are fixed points of the
holonomy and gluing is its triviality; along forgetting maps, which are
surjections, existence of compatible families is the weak-pullback
(amalgamation) condition of the observer presheaf.

**Descent is gluing.**  Equivalences along the pairs of an equivalence
relation form a view system over the relation's graph (`relationSystem`).
They satisfy the cocycle condition of descent exactly when this system has
trivial holonomy (`cocycle_iff_trivialHolonomy`), and then they are descent
data (`descentDatumOfTrivialHolonomy`), so the family descends along the
quotient.  Control: twisting the transports between two of three identified
points gives non-trivial holonomy (`Incoherent.not_trivialHolonomy`), while
the same family descends with the identity transports
(`Incoherent.identityDatum`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope

universe uI uE uV u

-- The edge and view universes are independent parameters of the record.
set_option linter.checkUnivs false in
/-- **Views over an index graph**: a view at every index and, along every
edge, a translation between the two views. -/
structure ViewSystem (Index : Type uI) where
  /-- The view at an index. -/
  View : Index → Type uV
  /-- The edges of the index graph. -/
  Edge : Index → Index → Type uE
  /-- The translation along an edge. -/
  translate : ∀ {i j : Index}, Edge i j → View i ≃ View j

namespace ViewSystem

variable {Index : Type uI} (S : ViewSystem.{uI, uE, uV} Index)

/-- A walk in the index graph, crossing each edge forward or backward. -/
inductive Walk : Index → Index → Type (max uI uE)
  | nil (i : Index) : Walk i i
  | forward {i j k : Index} (edge : S.Edge i j) (rest : Walk j k) : Walk i k
  | backward {i j k : Index} (edge : S.Edge j i) (rest : Walk j k) : Walk i k

variable {S}

/-- Concatenate two walks. -/
def Walk.append : {i j k : Index} → S.Walk i j → S.Walk j k → S.Walk i k
  | _, _, _, .nil _, later => later
  | _, _, _, .forward edge rest, later => .forward edge (rest.append later)
  | _, _, _, .backward edge rest, later => .backward edge (rest.append later)

/-- Walk back. -/
def Walk.reverse : {i j : Index} → S.Walk i j → S.Walk j i
  | _, _, .nil i => .nil i
  | _, _, .forward edge rest => rest.reverse.append (.backward edge (.nil _))
  | _, _, .backward edge rest => rest.reverse.append (.forward edge (.nil _))

variable (S)

/-- **Transport along a walk.** -/
def transport : {i j : Index} → S.Walk i j → S.View i → S.View j
  | _, _, .nil _, value => value
  | _, _, .forward edge rest, value => transport rest (S.translate edge value)
  | _, _, .backward edge rest, value => transport rest ((S.translate edge).symm value)

variable {S}

theorem transport_append {i j k : Index} (first : S.Walk i j) (second : S.Walk j k)
    (value : S.View i) :
    S.transport (first.append second) value = S.transport second (S.transport first value) := by
  induction first with
  | nil => rfl
  | forward edge rest ih => exact ih second _
  | backward edge rest ih => exact ih second _

theorem transport_reverse {i j : Index} (walk : S.Walk i j) (value : S.View i) :
    S.transport walk.reverse (S.transport walk value) = value := by
  induction walk with
  | nil => rfl
  | forward edge rest ih =>
    change S.transport (rest.reverse.append (.backward edge (.nil _)))
      (S.transport rest (S.translate edge value)) = value
    rw [transport_append, ih]
    exact Equiv.symm_apply_apply _ _
  | backward edge rest ih =>
    change S.transport (rest.reverse.append (.forward edge (.nil _)))
      (S.transport rest ((S.translate edge).symm value)) = value
    rw [transport_append, ih]
    exact Equiv.apply_symm_apply _ _

theorem transport_reverse_right {i j : Index} (walk : S.Walk i j) (value : S.View j) :
    S.transport walk (S.transport walk.reverse value) = value := by
  induction walk with
  | nil => rfl
  | forward edge rest ih =>
    change S.transport rest (S.translate edge
      (S.transport (rest.reverse.append (.backward edge (.nil _))) value)) = value
    rw [transport_append]
    change S.transport rest (S.translate edge ((S.translate edge).symm
      (S.transport rest.reverse value))) = value
    rw [Equiv.apply_symm_apply, ih]
  | backward edge rest ih =>
    change S.transport rest ((S.translate edge).symm
      (S.transport (rest.reverse.append (.forward edge (.nil _))) value)) = value
    rw [transport_append]
    change S.transport rest ((S.translate edge).symm (S.translate edge
      (S.transport rest.reverse value))) = value
    rw [Equiv.symm_apply_apply, ih]

variable (S)

/-- **Trivial holonomy**: every closed walk transports every value to
itself. -/
def TrivialHolonomy : Prop :=
  ∀ {i : Index} (loop : S.Walk i i) (value : S.View i), S.transport loop value = value

/-- Parallel walks transport alike. -/
def PathIndependent : Prop :=
  ∀ {i j : Index} (first second : S.Walk i j) (value : S.View i),
    S.transport first value = S.transport second value

/-- **Trivial holonomy is path independence.** -/
theorem trivialHolonomy_iff_pathIndependent : S.TrivialHolonomy ↔ S.PathIndependent := by
  constructor
  · intro trivial i j first second value
    calc S.transport first value
        = S.transport second (S.transport second.reverse (S.transport first value)) :=
          (transport_reverse_right second _).symm
      _ = S.transport second (S.transport (first.append second.reverse) value) := by
          rw [transport_append]
      _ = S.transport second value := by rw [trivial]
  · intro independent i loop value
    exact independent loop (.nil i) value

/-! ## Gluing -/

/-- **A gluing**: one global view, with an equivalence onto every view that
commutes with every translation. -/
structure Gluing where
  /-- The global view. -/
  Global : Type uV
  /-- The chart onto the view at an index. -/
  chart : ∀ i : Index, Global ≃ S.View i
  /-- Charts commute with translations. -/
  compatible : ∀ {i j : Index} (edge : S.Edge i j) (point : Global),
    S.translate edge (chart i point) = chart j point

variable {S}

/-- **Transport along a walk is the change of chart.** -/
theorem Gluing.transport_chart (gluing : S.Gluing) {i j : Index} (walk : S.Walk i j)
    (point : gluing.Global) : S.transport walk (gluing.chart i point) = gluing.chart j point := by
  induction walk with
  | nil => rfl
  | forward edge rest ih =>
    change S.transport rest (S.translate edge (gluing.chart _ point)) = _
    rw [gluing.compatible edge point, ih]
  | backward edge rest ih =>
    change S.transport rest ((S.translate edge).symm (gluing.chart _ point)) = _
    rw [← gluing.compatible edge point, Equiv.symm_apply_apply, ih]

/-- **A gluing forces trivial holonomy.** -/
theorem Gluing.trivialHolonomy (gluing : S.Gluing) : S.TrivialHolonomy := by
  intro i loop value
  have transported := gluing.transport_chart loop ((gluing.chart i).symm value)
  rwa [Equiv.apply_symm_apply] at transported

variable {root : Index}

/-- The transport from the root along a merely given walk, well defined by
path independence. -/
def liftTransport (independent : S.PathIndependent) {j : Index}
    (walk : Trunc (S.Walk root j)) (value : S.View root) : S.View j :=
  Trunc.lift (fun w => S.transport w value) (fun first second => independent first second value)
    walk

/-- The transport back to the root along a merely given walk. -/
def liftTransportBack (independent : S.PathIndependent) {j : Index}
    (walk : Trunc (S.Walk root j)) (value : S.View j) : S.View root :=
  Trunc.lift (fun w => S.transport w.reverse value)
    (fun first second => independent first.reverse second.reverse value) walk

theorem liftTransportBack_liftTransport (independent : S.PathIndependent) {j : Index}
    (walk : Trunc (S.Walk root j)) (value : S.View root) :
    liftTransportBack independent walk (liftTransport independent walk value) = value :=
  Trunc.induction_on walk fun w => transport_reverse w value

theorem liftTransport_liftTransportBack (independent : S.PathIndependent) {j : Index}
    (walk : Trunc (S.Walk root j)) (value : S.View j) :
    liftTransport independent walk (liftTransportBack independent walk value) = value :=
  Trunc.induction_on walk fun w => transport_reverse_right w value

/-- **Trivial holonomy on a connected index graph builds a gluing**, with
the root's view as the global view.  Connectivity is a merely given walk to
every index; no spanning tree is chosen. -/
def gluingOfTrivialHolonomy (trivial : S.TrivialHolonomy)
    (connect : ∀ j : Index, Trunc (S.Walk root j)) : S.Gluing where
  Global := S.View root
  chart j :=
    { toFun := liftTransport ((trivialHolonomy_iff_pathIndependent S).mp trivial) (connect j)
      invFun := liftTransportBack ((trivialHolonomy_iff_pathIndependent S).mp trivial) (connect j)
      left_inv := liftTransportBack_liftTransport _ (connect j)
      right_inv := liftTransport_liftTransportBack _ (connect j) }
  compatible {i j} edge point := by
    have independent : S.PathIndependent := (trivialHolonomy_iff_pathIndependent S).mp trivial
    change S.translate edge (liftTransport independent (connect i) point) =
      liftTransport independent (connect j) point
    induction connect i using Trunc.induction_on with
    | h first =>
      induction connect j using Trunc.induction_on with
      | h second =>
        change S.translate edge (S.transport first point) = S.transport second point
        have extended := transport_append first (.forward edge (.nil j)) point
        change S.transport (first.append (.forward edge (.nil j))) point =
          S.translate edge (S.transport first point) at extended
        rw [← extended]
        exact independent _ second point

/-- **On a connected index graph the views glue exactly when every cycle has
trivial holonomy.** -/
theorem nonempty_gluing_iff (connect : ∀ j : Index, Trunc (S.Walk root j)) :
    Nonempty S.Gluing ↔ S.TrivialHolonomy :=
  ⟨fun ⟨gluing⟩ => gluing.trivialHolonomy,
    fun trivial => ⟨gluingOfTrivialHolonomy trivial connect⟩⟩

/-- Any two gluings of a connected system have equivalent global views. -/
def Gluing.globalEquiv (first second : S.Gluing) (i : Index) : first.Global ≃ second.Global :=
  (first.chart i).trans (second.chart i).symm

/-- **Trivial holonomy is descent to the thin view of the index graph**,
where parallel walks are identified: the transport factors through truncated
walks exactly when holonomy is trivial. -/
theorem trivialHolonomy_iff_descends :
    S.TrivialHolonomy ↔
      ∃ thin : ∀ {i j : Index}, Trunc (S.Walk i j) → S.View i → S.View j,
        ∀ {i j : Index} (walk : S.Walk i j) (value : S.View i),
          thin (Trunc.mk walk) value = S.transport walk value := by
  rw [trivialHolonomy_iff_pathIndependent]
  constructor
  · intro independent
    exact ⟨fun walk value => Trunc.lift (fun w => S.transport w value)
      (fun first second => independent first second value) walk, fun _ _ => rfl⟩
  · rintro ⟨thin, agrees⟩ i j first second value
    rw [← agrees first value, ← agrees second value,
      Subsingleton.elim (Trunc.mk first) (Trunc.mk second)]

variable (S) in
/-- The global sections of a view system: a value at every index, preserved
by every translation. -/
def Sections : Type (max uI uV) :=
  { family : ∀ i : Index, S.View i //
      ∀ {i j : Index} (edge : S.Edge i j), S.translate edge (family i) = family j }

/-- A global section is preserved by transport along every walk. -/
theorem Sections.transport (family : S.Sections) {i j : Index} (walk : S.Walk i j) :
    S.transport walk (family.1 i) = family.1 j := by
  induction walk with
  | nil => rfl
  | forward edge rest ih =>
    change S.transport rest (S.translate edge (family.1 _)) = _
    rw [family.2 edge, ih]
  | backward edge rest ih =>
    change S.transport rest ((S.translate edge).symm (family.1 _)) = _
    rw [← family.2 edge, Equiv.symm_apply_apply, ih]

/-- **The global view of a gluing is the limit**: on a connected index graph,
the global sections are equivalent to the global view of any gluing, so the
global view is unique up to equivalence and canonical. -/
def Gluing.sectionsEquiv (gluing : S.Gluing) (connect : ∀ j : Index, Trunc (S.Walk root j)) :
    S.Sections ≃ gluing.Global where
  toFun family := (gluing.chart root).symm (family.1 root)
  invFun point := ⟨fun i => gluing.chart i point, fun edge => gluing.compatible edge point⟩
  left_inv family := by
    apply Subtype.ext
    funext i
    change gluing.chart i ((gluing.chart root).symm (family.1 root)) = family.1 i
    induction connect i using Trunc.induction_on with
    | h walk =>
      rw [← gluing.transport_chart walk, Equiv.apply_symm_apply, family.transport walk]
  right_inv point := (gluing.chart root).symm_apply_apply point

/-- **With trivial holonomy on a connected index graph, the global sections
are the view at the root.** -/
def sectionsEquivOfTrivialHolonomy (trivial : S.TrivialHolonomy)
    (connect : ∀ j : Index, Trunc (S.Walk root j)) : S.Sections ≃ S.View root :=
  (gluingOfTrivialHolonomy trivial connect).sectionsEquiv connect

end ViewSystem

/-! ## Descent is gluing -/

section Descent

variable {X : Type u} (E : Setoid X) (P : X → Type uV)

/-- Transport equivalences along the pairs of an equivalence relation, as a
view system over the relation's graph. -/
def relationSystem (transport : ∀ {x y : X}, E x y → P x ≃ P y) :
    ViewSystem.{u, 0, uV} X where
  View := P
  Edge x y := PLift (E x y)
  translate edge := transport edge.down

variable {E P}

/-- The ends of a walk in the relation's graph are related. -/
theorem walk_related {transport : ∀ {x y : X}, E x y → P x ≃ P y} {x y : X} :
    (relationSystem E P transport).Walk x y → E x y
  | .nil x => E.refl' x
  | .forward edge rest => E.trans' edge.down (walk_related rest)
  | .backward edge rest => E.trans' (E.symm' edge.down) (walk_related rest)

/-- **The cocycle condition of descent is exactly trivial holonomy on the
relation's graph.** -/
theorem cocycle_iff_trivialHolonomy (transport : ∀ {x y : X}, E x y → P x ≃ P y) :
    ((∀ {x : X} (related : E x x) (value : P x), transport related value = value) ∧
      ∀ {x y z : X} (first : E x y) (second : E y z) (value : P x),
        transport second (transport first value) = transport (E.trans' first second) value) ↔
      (relationSystem E P transport).TrivialHolonomy := by
  constructor
  · rintro ⟨refl, trans⟩
    have back : ∀ {x y : X} (related : E x y) (value : P y),
        (transport related).symm value = transport (E.symm' related) value := by
      intro x y related value
      have round := trans related (E.symm' related) ((transport related).symm value)
      rw [Equiv.apply_symm_apply, refl] at round
      exact round.symm
    have along : ∀ {x y : X} (walk : (relationSystem E P transport).Walk x y) (value : P x),
        (relationSystem E P transport).transport walk value =
          transport (walk_related walk) value := by
      intro x y walk value
      induction walk with
      | nil x => exact (refl _ value).symm
      | forward edge rest ih =>
        change (relationSystem E P transport).transport rest (transport edge.down value) = _
        rw [ih, trans]
      | backward edge rest ih =>
        change (relationSystem E P transport).transport rest
          ((transport edge.down).symm value) = _
        rw [ih, back, trans]
    intro x loop value
    exact (along loop value).trans (refl _ value)
  · intro trivial
    have independent : (relationSystem E P transport).PathIndependent :=
      (ViewSystem.trivialHolonomy_iff_pathIndependent _).mp trivial
    refine ⟨fun {x} related value => trivial (.forward ⟨related⟩ (.nil x)) value, ?_⟩
    intro x y z first second value
    exact independent (.forward ⟨first⟩ (.forward ⟨second⟩ (.nil z)))
      (.forward ⟨E.trans' first second⟩ (.nil z)) value

/-- **Trivial holonomy makes the transports descent data**, so the family
descends along the quotient. -/
def descentDatumOfTrivialHolonomy (transport : ∀ {x y : X}, E x y → P x ≃ P y)
    (trivial : (relationSystem E P transport).TrivialHolonomy) : DescentDatum E P where
  transport related value := transport related value
  transport_refl related value :=
    ((cocycle_iff_trivialHolonomy transport).mpr trivial).1 related value
  transport_trans first second value :=
    ((cocycle_iff_trivialHolonomy transport).mpr trivial).2 first second value

end Descent

/-! ## Controls on a three-cycle -/

namespace Twisted

/-- Three indices. -/
inductive Vertex where
  | a
  | b
  | c
  deriving DecidableEq

/-- The edges of the cycle `a → b → c → a`. -/
inductive CycleEdge : Vertex → Vertex → Type where
  | ab : CycleEdge .a .b
  | bc : CycleEdge .b .c
  | ca : CycleEdge .c .a

/-- Negation as an equivalence. -/
def negation : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv value := Bool.not_not value
  right_inv value := Bool.not_not value

/-- **The twisted cycle**: boolean views, identity along two edges, negation
along the third. -/
def twisted : ViewSystem.{0, 0, 0} Vertex where
  View _ := Bool
  Edge := CycleEdge
  translate
    | .ab => Equiv.refl Bool
    | .bc => Equiv.refl Bool
    | .ca => negation

/-- The cycle as a closed walk. -/
def cycle : twisted.Walk Vertex.a Vertex.a :=
  .forward CycleEdge.ab (.forward CycleEdge.bc (.forward CycleEdge.ca (.nil Vertex.a)))

/-- **The holonomy of the cycle is negation.** -/
theorem holonomy_moves : twisted.transport cycle true = false :=
  rfl

/-- **No gluing**, although every translation is an equivalence. -/
theorem no_gluing : ¬ Nonempty twisted.Gluing := by
  rintro ⟨gluing⟩
  have fixed := gluing.trivialHolonomy cycle true
  rw [holonomy_moves] at fixed
  exact Bool.noConfusion fixed

/-- **No global section.** -/
theorem no_sections : IsEmpty twisted.Sections := by
  refine ⟨fun family => ?_⟩
  have first := family.2 CycleEdge.ab
  have second := family.2 CycleEdge.bc
  have third := family.2 CycleEdge.ca
  change family.1 .a = family.1 .b at first
  change family.1 .b = family.1 .c at second
  change (!family.1 .c) = family.1 .a at third
  rw [← second, ← first] at third
  revert third
  cases family.1 .a <;> decide

/-- The path `a → b → c`: the cycle without its twisted edge. -/
inductive PathEdge : Vertex → Vertex → Type where
  | ab : PathEdge .a .b
  | bc : PathEdge .b .c

/-- The untwisted path of boolean views. -/
def path : ViewSystem.{0, 0, 0} Vertex where
  View _ := Bool
  Edge := PathEdge
  translate
    | .ab => Equiv.refl Bool
    | .bc => Equiv.refl Bool

/-- **Positive**: dropping the twisted edge, the views glue. -/
def pathGluing : path.Gluing where
  Global := Bool
  chart _ := Equiv.refl Bool
  compatible edge _ := by cases edge <;> rfl

theorem path_glues : Nonempty path.Gluing :=
  ⟨pathGluing⟩

end Twisted

/-! ### Control: incoherent transports for a family that descends -/

namespace Incoherent

open Twisted

/-- The observer that identifies all three indices. -/
def total : Setoid Vertex where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

/-- Negation between `a` and `c`, the identity elsewhere. -/
def twist : Vertex → Vertex → Bool ≃ Bool
  | .a, .c => negation
  | .c, .a => negation
  | _, _ => Equiv.refl Bool

/-- The twisted transports along the identified pairs. -/
def transport {x y : Vertex} (_ : total x y) : Bool ≃ Bool :=
  twist x y

/-- The loop `a → b → c → a` in the relation's graph. -/
def loop : (relationSystem total (fun _ => Bool) transport).Walk Vertex.a Vertex.a :=
  .forward (j := Vertex.b) ⟨trivial⟩ (.forward (j := Vertex.c) ⟨trivial⟩
    (.forward (j := Vertex.a) ⟨trivial⟩ (.nil Vertex.a)))

/-- **The transports have non-trivial holonomy**, so they fail the cocycle
condition and are not descent data. -/
theorem not_trivialHolonomy :
    ¬ (relationSystem total (fun _ => Bool) transport).TrivialHolonomy := fun trivial =>
  Bool.noConfusion (trivial loop true)

/-- **Yet the family descends**, with the identity transports: coherence is a
property of the transport data, not of the family alone. -/
def identityDatum : DescentDatum total fun _ : Vertex => Bool where
  transport _ value := value
  transport_refl _ _ := rfl
  transport_trans _ _ _ := rfl

end Incoherent

/-! ## Relational holonomy on a cycle -/

section Relational

open Mettapedia.GSLT.LooseRelationEquipment

variable {A B C : Type u}

/-- A global section around a three-cycle of proof-relevant relations: a
point of each view with a witness along each edge. -/
def CycleSection (first : Loose A B) (second : Loose B C) (third : Loose C A) : Type u :=
  Σ a : A, Σ b : B, Σ c : C, first a b × second b c × third c a

/-- The holonomy relation of the cycle: the composite relation around it. -/
def loopRelation (first : Loose A B) (second : Loose B C) (third : Loose C A) : Loose A A :=
  comp (comp first second) third

/-- **Global sections are exactly the fixed points of the holonomy
relation.** -/
def cycleSectionEquiv (first : Loose A B) (second : Loose B C) (third : Loose C A) :
    CycleSection first second third ≃ Σ a : A, loopRelation first second third a a where
  toFun := fun ⟨a, b, c, witnessFirst, witnessSecond, witnessThird⟩ =>
    ⟨a, c, ⟨b, witnessFirst, witnessSecond⟩, witnessThird⟩
  invFun := fun ⟨a, c, ⟨b, witnessFirst, witnessSecond⟩, witnessThird⟩ =>
    ⟨a, b, c, witnessFirst, witnessSecond, witnessThird⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **For functions, the holonomy relation has a fixed point at `a` exactly
when the composite of the three maps fixes `a`.** -/
theorem functionalLoop_iff (f : A → B) (g : B → C) (h : C → A) (a : A) :
    Nonempty (loopRelation (companion f) (companion g) (companion h) a a) ↔ h (g (f a)) = a := by
  constructor
  · rintro ⟨c, ⟨b, ⟨⟨first⟩⟩, ⟨⟨second⟩⟩⟩, ⟨⟨third⟩⟩⟩
    rw [first, second, third]
  · intro fixed
    exact ⟨⟨g (f a), ⟨f a, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩⟩, ⟨⟨fixed⟩⟩⟩⟩

end Relational

/-! ### Sections without gluing -/

namespace Swap

/-- Swap `1` and `2`, fix `0`. -/
def swapOneTwo : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1

theorem swapOneTwo_involutive (x : Fin 3) : swapOneTwo (swapOneTwo x) = x := by
  revert x
  decide

/-- The swap as an equivalence. -/
def swap : Fin 3 ≃ Fin 3 where
  toFun := swapOneTwo
  invFun := swapOneTwo
  left_inv := swapOneTwo_involutive
  right_inv := swapOneTwo_involutive

open Twisted in
/-- The three-cycle of views on three points, twisted by the swap. -/
def swapped : ViewSystem.{0, 0, 0} Vertex where
  View _ := Fin 3
  Edge := CycleEdge
  translate
    | .ab => Equiv.refl (Fin 3)
    | .bc => Equiv.refl (Fin 3)
    | .ca => swap

open Twisted in
/-- **A global section exists**: the constant family at the fixed point. -/
def fixedSection : swapped.Sections :=
  ⟨fun _ => (0 : Fin 3), fun edge => by cases edge <;> rfl⟩

theorem section_exists : Nonempty swapped.Sections :=
  ⟨fixedSection⟩

open Twisted in
/-- The cycle as a closed walk of the swapped system. -/
def swappedCycle : swapped.Walk Vertex.a Vertex.a :=
  .forward CycleEdge.ab (.forward CycleEdge.bc (.forward CycleEdge.ca (.nil Vertex.a)))

/-- **Yet no gluing**: the holonomy moves `1`. -/
theorem no_gluing : ¬ Nonempty swapped.Gluing := by
  rintro ⟨gluing⟩
  have fixed := gluing.trivialHolonomy swappedCycle (1 : Fin 3)
  change swapOneTwo 1 = 1 at fixed
  exact absurd fixed (by decide)

end Swap

end Mettapedia.GSLT.Scope
