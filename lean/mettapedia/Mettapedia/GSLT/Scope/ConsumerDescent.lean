import Mettapedia.GSLT.Core.PolicyFamilySufficiency
import Mettapedia.TypeTheory.DependentFamilyObserverFactorization
import Mettapedia.TypeTheory.RouteTransportDiscriminator
import Mettapedia.Logic.TheoryModel.IdentityCarve

/-!
# Consumer descent along a forgetting

A forgetting is read as a view `view : X → Y`.  A **consumer** of the detailed
scope is a function or a dependent family on `X`; it *descends* when it is the
pullback of a consumer on the view.

**Transport along a forgetting.**  Families over the view transport along
agreement of views, and a family indexed by the view transports from `x` to
`y` for every such family exactly when the views agree
(`viewFamilies_transport_iff`).  Families over the detailed states transport
for every family only along equality (`rawFamilies_transport_iff_eq`).  When
distinct states share a view, the first transports and the second does not
(`transport_boundary`).  The world-model calculus theorem
`agree_iff_all_quotient_families_transport` is the instance whose view is the
class map onto its observational quotient.

**Descent is exactly respect for the forgotten distinctions.**
* A function consumer descends along a quotient exactly when it is constant on
  the identified pairs (`function_descends_iff`).
* A dependent consumer descends along a quotient, up to fibrewise
  equivalence, exactly when it carries **descent data**: transports along the
  identified pairs that are trivial on reflexivity and satisfy the cocycle
  condition (`nonempty_factorization_iff_descentDatum`).  The descended family
  is built without choice from compatible sections over each class
  (`DescentDatum.Fibre`, `DescentDatum.fibreEquiv`).  Control: a class that
  contains fibres of different sizes admits no descent data
  (`Sizes.no_descent`).

**Histories with one answer.**  In a GSLT with a diamond and a shortcut,
three histories reach one answer: two of length two through different
intermediate states, and one of length one (`Diamond`).
* The answer consumer descends to the answer view (`Diamond.answer_descends`).
* The cost consumer does not (`Diamond.cost_not_descends`).
* The provenance consumer does not, even between histories of equal cost
  (`Diamond.provenance_not_descends`, `Diamond.equal_cost`), and neither does
  the dependent consumer "the history passed through the left branch"
  (`Diamond.passesLeft_not_descends`).
* A readout of answers serves the answer family and not the family of all
  three consumers (`Diamond.answerFamily_supported`,
  `Diamond.allConsumers_not_supported`).

**Forgetting provenance double-counts evidence.**  Two derivations resting
on one source and two resting on two sources have the same bag of answers.
Counting derivations accepts the first; counting distinct sources rejects it
(`DoubleCounting.double_counting`), so the two decisions differ
(`DoubleCounting.naive_ne_aware`).  The provenance-aware decision does not
descend to the bag of answers (`DoubleCounting.decision_not_descends`).

**The post-forgetting world.**  Truncating every identity-proof type gives
the thin view of an identity structure (`thinView`).
* Constructing the view identifies: the thin view satisfies `uip`, and it is
  in the h-set fragment (`thinView_mem_hsetFragment`).
* Forgetting does not: the truncation observer cannot tell a structure from
  its thin view (`truncation_thinView`), so a two-loop structure and its thin
  view look alike while only the second satisfies `uip`
  (`forgetting_does_not_identify_constructing_does`), and the truncation
  observer sees one theory of both (`observedTheory_thinView`).  This sharpens
  `forgetting_versus_identifying`.
* A transport family descends to the thin view exactly when it transports
  parallel proofs alike (`descendsToThin_iff`); on a groupoid, every family
  descends exactly when the structure is thin (`all_descend_iff_uip`), by the
  representable discriminator.
* **The h-set carve by holonomy**: a model of the groupoid laws is in the
  h-set fragment exactly when every transport family has trivial holonomy
  around every loop (`mem_hsetFragment_iff_trivialHolonomy`); in the thin
  view every family descends (`thinView_all_descend`), and over the two-loop
  structure one does not (`xorModel_not_all_descend`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope

open Mettapedia.GSLT.Core.NonFactorization

universe u v w

/-! ## Transport along a forgetting -/

section Transport

variable {X : Type u} {Y : Type v}

/-- Transport a family over the view along agreement of views. -/
def transportAlong (view : X → Y) (P : Y → Type w) {x y : X} (same : view x = view y) :
    P (view x) → P (view y) :=
  cast (congrArg P same)

/-- **Families over the view transport exactly along view agreement.**  The
converse tests the family of witnesses that the view equals `view x`. -/
theorem viewFamilies_transport_iff (view : X → Y) (x y : X) :
    Nonempty (∀ P : Y → Type w, P (view x) → P (view y)) ↔ view x = view y := by
  constructor
  · rintro ⟨transports⟩
    exact (transports (fun c => ULift.{w} (PLift (view x = c))) ⟨⟨rfl⟩⟩).down.down
  · intro same
    exact ⟨fun P => transportAlong view P same⟩

/-- **Families over the detailed states transport only along equality.** -/
theorem rawFamilies_transport_iff_eq (x y : X) :
    Nonempty (∀ P : X → Type w, P x → P y) ↔ x = y := by
  constructor
  · rintro ⟨transports⟩
    exact (transports (fun z => ULift.{w} (PLift (x = z))) ⟨⟨rfl⟩⟩).down.down
  · rintro rfl
    exact ⟨fun _ value => value⟩

/-- **The transport boundary.**  Distinct states with one view transport every
family over the view and not every family over the states. -/
theorem transport_boundary (view : X → Y) {x y : X} (distinct : x ≠ y)
    (same : view x = view y) :
    Nonempty (∀ P : Y → Type w, P (view x) → P (view y)) ∧
      ¬ Nonempty (∀ P : X → Type w, P x → P y) :=
  ⟨(viewFamilies_transport_iff view x y).mpr same,
    fun raw => distinct ((rawFamilies_transport_iff_eq x y).mp raw)⟩

end Transport

/-! ## Descent along a quotient -/

section Descent

variable {X : Type u} (E : Setoid X)

/-- **A function consumer descends along a quotient exactly when it is
constant on the identified pairs.** -/
theorem function_descends_iff {Z : Sort w} (consumer : X → Z) :
    Factors (Quotient.mk E) consumer ↔ ∀ ⦃x y : X⦄, E x y → consumer x = consumer y := by
  constructor
  · exact fun factors x y related => factors.constantOnFibers x y (Quotient.sound related)
  · exact fun respects => ⟨Quotient.lift consumer fun _ _ related => respects related,
      fun _ => rfl⟩

/-- **Descent data** for a family along an equivalence: a transport along
every identified pair, trivial on reflexivity and satisfying the cocycle
condition.  Identified pairs are propositions, so the transport depends only
on the endpoints. -/
structure DescentDatum (P : X → Type w) where
  /-- Transport along an identified pair. -/
  transport : ∀ {x y : X}, E x y → P x → P y
  /-- Transport along reflexivity is the identity. -/
  transport_refl : ∀ {x : X} (related : E x x) (value : P x), transport related value = value
  /-- **The cocycle condition.** -/
  transport_trans : ∀ {x y z : X} (first : E x y) (second : E y z) (value : P x),
    transport second (transport first value) = transport (E.trans' first second) value

namespace DescentDatum

variable {E} {P : X → Type w} (datum : DescentDatum E P)

/-- The identified pair of two points of one class. -/
theorem related_of_mk {x y : X} {c : Quotient E} (hx : Quotient.mk E x = c)
    (hy : Quotient.mk E y = c) : E x y :=
  Quotient.exact (hx.trans hy.symm)

/-- **The descended fibre** over a class: families of values over the points
of the class, compatible with the transports.  No representative is chosen. -/
def Fibre (c : Quotient E) : Type (max u w) :=
  { family : ∀ x : X, Quotient.mk E x = c → P x //
      ∀ (x y : X) (hx : Quotient.mk E x = c) (hy : Quotient.mk E y = c),
        datum.transport (related_of_mk hx hy) (family x hx) = family y hy }

/-- **The fibre of the family is equivalent to the descended fibre over its
class**, without choice. -/
def fibreEquiv (x : X) : P x ≃ datum.Fibre (Quotient.mk E x) where
  toFun value := ⟨fun y hy => datum.transport (related_of_mk rfl hy) value,
    fun y z _ _ => datum.transport_trans _ _ value⟩
  invFun family := family.1 x rfl
  left_inv value := datum.transport_refl _ value
  right_inv family := by
    apply Subtype.ext
    funext y hy
    exact family.2 x y rfl hy

/-- Descent data make the family factor through the quotient. -/
def factorization {P : X → Type u} (datum : DescentDatum E P) :
    Mettapedia.TypeTheory.DependentFamilyObserverFactorization.FamilyFactorization
      (Quotient.mk E) P where
  targetFamily := datum.Fibre
  identify := datum.fibreEquiv

end DescentDatum

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization in
/-- A factorization through the quotient supplies descent data: transport
through the target fibre.  The transport is the pointwise form of
`FamilyFactorization.fibreEquiv`, stated without `Equiv.cast`. -/
def FamilyFactorization.descentDatum {P : X → Type w}
    (factorization : FamilyFactorization (Quotient.mk E) P) : DescentDatum E P where
  transport {x y} related value := (factorization.identify y).symm
    (cast (congrArg factorization.targetFamily (Quotient.sound related))
      (factorization.identify x value))
  transport_refl related value := by
    rw [cast_eq, Equiv.symm_apply_apply]
  transport_trans first second value := by
    rw [Equiv.apply_symm_apply, cast_cast]

/-- **A dependent consumer descends along a quotient exactly when it carries
coherent descent data.**  Both directions are constructive. -/
theorem nonempty_factorization_iff_descentDatum (P : X → Type u) :
    Nonempty (Mettapedia.TypeTheory.DependentFamilyObserverFactorization.FamilyFactorization
      (Quotient.mk E) P) ↔ Nonempty (DescentDatum E P) :=
  ⟨fun ⟨factorization⟩ => ⟨FamilyFactorization.descentDatum E factorization⟩,
    fun ⟨datum⟩ => ⟨datum.factorization⟩⟩

end Descent

/-! ### Control: fibres of different sizes in one class -/

namespace Sizes

/-- The observer that identifies the two booleans. -/
def total : Setoid Bool where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

/-- A singleton fibre over `true` and a two-point fibre over `false`. -/
def fibres : Bool → Type
  | true => Unit
  | false => Bool

/-- **No descent data**: transport would identify a singleton with a two-point
type. -/
theorem no_descent : ¬ Nonempty (DescentDatum total fibres) := by
  rintro ⟨datum⟩
  have back : ∀ value : fibres false,
      datum.transport (x := true) (y := false) trivial
        (datum.transport (x := false) (y := true) trivial value) = value := fun value =>
    (datum.transport_trans (x := false) (y := true) (z := false) trivial trivial value).trans
      (datum.transport_refl trivial value)
  have middle : datum.transport (x := false) (y := true) trivial true =
      datum.transport (x := false) (y := true) trivial false :=
    Subsingleton.elim (α := Unit) _ _
  have collapse : (true : fibres false) = false :=
    (back true).symm.trans
      ((congrArg (datum.transport (x := true) (y := false) trivial) middle).trans (back false))
  exact Bool.noConfusion collapse

/-- **Positive**: the constant family descends. -/
def constantDatum : DescentDatum total fun _ => Bool where
  transport _ value := value
  transport_refl _ _ := rfl
  transport_trans _ _ _ := rfl

end Sizes

/-! ## Histories with one answer -/

namespace Diamond

open Mettapedia.GSLT

/-- The states of a small computation. -/
inductive Node where
  | start
  | left
  | right
  | done
  deriving DecidableEq

/-- Two branches from `start` to `done`, and a shortcut. -/
inductive Move : Node → Node → Prop where
  | toLeft : Move .start .left
  | toRight : Move .start .right
  | leftDone : Move .left .done
  | rightDone : Move .right .done
  | shortcut : Move .start .done

/-- **The diamond with a shortcut**, as a GSLT with syntactic equations. -/
def diamond : GSLT where
  Term := Node
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Move
  rewrites_resp_left := fun {_ _ target} equal step => ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := fun step equal => equal ▸ step

/-- A computation history from `start`, with the answer it reached. -/
abbrev History : Type :=
  Σ answer : Node, diamond.RewritePath Node.start answer

/-- The states a history visits, in order. -/
def visits : {source target : Node} → diamond.RewritePath source target → List Node
  | _, _, .nil node => [node]
  | source, _, .cons _ rest => source :: visits rest

/-- **The forgetting**: keep the answer only. -/
def answer (history : History) : Node :=
  history.1

/-- The cost of a history: its number of steps. -/
def cost (history : History) : ℕ :=
  history.2.length

/-- The provenance of a history: the states it visited. -/
def provenance (history : History) : List Node :=
  visits history.2

/-- Through the left branch. -/
def viaLeft : History :=
  ⟨Node.done, .cons (show diamond.Step Node.start Node.left from Move.toLeft)
    (.cons (show diamond.Step Node.left Node.done from Move.leftDone)
      (GSLT.RewritePath.nil (S := diamond) Node.done))⟩

/-- Through the right branch. -/
def viaRight : History :=
  ⟨Node.done, .cons (show diamond.Step Node.start Node.right from Move.toRight)
    (.cons (show diamond.Step Node.right Node.done from Move.rightDone)
      (GSLT.RewritePath.nil (S := diamond) Node.done))⟩

/-- Along the shortcut. -/
def direct : History :=
  ⟨Node.done, .cons (show diamond.Step Node.start Node.done from Move.shortcut)
    (GSLT.RewritePath.nil (S := diamond) Node.done)⟩

theorem same_answer : answer viaLeft = answer direct ∧ answer viaLeft = answer viaRight :=
  ⟨rfl, rfl⟩

/-- **The answer consumer descends**: every consumer of the answer is a
consumer of the answer view. -/
theorem answer_descends {Z : Sort w} (consumer : Node → Z) :
    Factors answer fun history => consumer (answer history) :=
  ⟨consumer, fun _ => rfl⟩

/-- **The cost consumer does not descend.** -/
def costFiber : NonTrivialFiber answer cost where
  left := viaLeft
  right := direct
  sameShadow := rfl
  differentValue := by decide

theorem cost_not_descends : ¬ Factors answer cost :=
  costFiber.not_factors

theorem equal_cost : cost viaLeft = cost viaRight :=
  rfl

/-- **The provenance consumer does not descend**, even between histories of
equal cost. -/
def provenanceFiber : NonTrivialFiber answer provenance where
  left := viaLeft
  right := viaRight
  sameShadow := rfl
  differentValue := by decide

theorem provenance_not_descends : ¬ Factors answer provenance :=
  provenanceFiber.not_factors

/-- The dependent consumer: evidence that the history passed through the left
branch. -/
def PassesLeft (history : History) : Prop :=
  Node.left ∈ provenance history

/-- **The dependent consumer does not descend.** -/
theorem passesLeft_not_descends : ¬ Factors answer PassesLeft :=
  (NonTrivialFiber.ofProp (shadow := answer) (a := viaLeft) (b := viaRight) rfl
    (show Node.left ∈ [Node.start, Node.left, Node.done] by decide)
    (show Node.left ∉ [Node.start, Node.right, Node.done] by decide)).not_factors

/-- The three consumers of a history. -/
inductive Consumer where
  | answer
  | cost
  | provenance
  deriving DecidableEq

/-- The consumers as one policy family. -/
def consumers : Mettapedia.GSLT.Core.PolicyFamily History where
  Policy := Consumer
  Result
    | .answer => Node
    | .cost => ℕ
    | .provenance => List Node
  decide
    | .answer => answer
    | .cost => cost
    | .provenance => provenance

/-- **Positive**: the answer readout serves the family that asks for answers
only. -/
theorem answerFamily_supported :
    (consumers.reindex fun _ : Unit => Consumer.answer).SupportsReadout answer :=
  ⟨{ run := fun _ node => node
     agrees := fun _ _ => rfl }⟩

/-- **Negative**: it does not serve the family of all three consumers. -/
theorem allConsumers_not_supported : ¬ consumers.SupportsReadout answer := by
  apply consumers.not_supportsReadout_of_policy_collision answer
    (first := viaLeft) (second := direct) rfl .cost
  change (2 : ℕ) ≠ 1
  decide

end Diamond

/-! ## Forgetting provenance double-counts evidence -/

namespace DoubleCounting

/-- A derivation: the answer it supports and the source it rests on. -/
abbrev Derivation : Type :=
  Bool × ℕ

/-- **Forget provenance**: keep the bag of derived answers. -/
def answers (derivations : List Derivation) : List Bool :=
  derivations.map Prod.fst

/-- Evidence for an answer, counting derivations: the provenance-forgetting
count. -/
def derivationCount (answers : List Bool) (target : Bool) : ℕ :=
  answers.count target

/-- Evidence for an answer, counting distinct sources. -/
def sourceCount (derivations : List Derivation) (target : Bool) : ℕ :=
  ((derivations.filter fun d => d.1 == target).map Prod.snd).dedup.length

/-- A later decision: accept an answer with at least two pieces of
evidence. -/
def accept (evidence : ℕ) : Bool :=
  decide (2 ≤ evidence)

/-- Two derivations of `true` resting on one source. -/
def sharedSource : List Derivation :=
  [(true, 7), (true, 7)]

/-- Two derivations of `true` resting on two sources. -/
def twoSources : List Derivation :=
  [(true, 7), (true, 8)]

/-- The provenance-aware decision. -/
def awareDecision (derivations : List Derivation) : Bool :=
  accept (sourceCount derivations true)

/-- The provenance-forgetting decision, computed from the bag of answers. -/
def naiveDecision (answers : List Bool) : Bool :=
  accept (derivationCount answers true)

/-- **Double counting changes the decision.**  The two evidence states have
one bag of answers.  Counting derivations accepts both; counting sources
rejects the state with a shared source. -/
theorem double_counting :
    answers sharedSource = answers twoSources ∧
      naiveDecision (answers sharedSource) = true ∧
      awareDecision sharedSource = false ∧
      awareDecision twoSources = true := by
  decide

/-- **The provenance-aware decision does not descend to the bag of
answers.** -/
theorem decision_not_descends : ¬ Factors answers awareDecision := by
  apply NonTrivialFiber.not_factors
  exact ⟨sharedSource, twoSources, rfl, by decide⟩

/-- The naive decision, pulled back to evidence states, disagrees with the
provenance-aware one. -/
theorem naive_ne_aware :
    (fun derivations => naiveDecision (answers derivations)) ≠ awareDecision := by
  intro same
  have atShared := congrFun same sharedSource
  revert atShared
  decide

end DoubleCounting

/-! ## The post-forgetting world -/

section Thin

open Mettapedia.Logic.TheoryModel
open Mettapedia.Logic.TheoryModel.IdentityProofs

/-- **The thin view** of an identity structure: every type of proofs is
truncated, so parallel proofs become equal. -/
def thinView (M : IdStructure.{u}) : IdStructure.{u} where
  Pt := M.Pt
  Pf a b := Trunc (M.Pf a b)
  refl a := Trunc.mk (M.refl a)
  inv p := Trunc.map M.inv p
  comp p q := Trunc.bind p fun p' => Trunc.map (M.comp p') q

instance (M : IdStructure.{u}) (a b : (thinView M).Pt) : Subsingleton ((thinView M).Pf a b) :=
  inferInstanceAs (Subsingleton (Trunc (M.Pf a b)))

/-- Every sentence stating an equation of proofs holds in the thin view. -/
theorem thinView_sat_uip (M : IdStructure.{u}) : (thinView M).Sat .uip :=
  fun _ _ => Subsingleton.elim _ _

/-- **Constructing the view identifies**: the thin view is in the h-set
fragment. -/
theorem thinView_mem_hsetFragment (M : IdStructure.{u}) : thinView M ∈ hsetFragment := by
  refine mem_hsetFragment_iff.mpr ?_
  rintro φ (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact thinView_sat_uip M
  · exact fun _ _ _ => Subsingleton.elim _ _
  · exact fun _ => Subsingleton.elim _ _
  · exact fun _ => Subsingleton.elim _ _
  · exact fun _ => Subsingleton.elim _ _
  · exact fun _ => Subsingleton.elim _ _

/-- **Forgetting cannot tell a structure from its thin view**: they have the
same points and the same joined pairs. -/
theorem truncation_thinView (M : IdStructure.{u}) : truncation M (thinView M) :=
  ⟨Equiv.refl _, fun _ _ =>
    ⟨fun ⟨p⟩ => ⟨Trunc.mk p⟩, fun ⟨p⟩ => Trunc.induction_on p fun p' => ⟨p'⟩⟩⟩

/-- **Forgetting does not identify; constructing the view does.**  The
truncation observer relates the two-loop structure to its thin view, which
satisfies `uip`, while the two-loop structure refutes it. -/
theorem forgetting_does_not_identify_constructing_does :
    truncation xorModel.{u} (thinView xorModel) ∧ (thinView xorModel.{u}).Sat .uip ∧
      ¬ xorModel.{u}.Sat .uip :=
  ⟨truncation_thinView _, thinView_sat_uip _, xorModel_not_uip⟩

/-- The truncation observer sees the same theory of a structure and of its
thin view. -/
theorem observedTheory_thinView (M : IdStructure.{u}) :
    observedTheory IdStructure.Sat truncation {M} =
      observedTheory IdStructure.Sat truncation {thinView M} := by
  ext φ
  constructor
  · rintro ⟨holds, invariant⟩
    refine ⟨?_, invariant⟩
    rintro N rfl
    exact (invariant (truncation_thinView M)).mp (holds rfl)
  · rintro ⟨holds, invariant⟩
    refine ⟨fun N (member : N = M) => ?_, invariant⟩
    rw [member]
    exact (invariant (truncation_thinView M)).mpr (holds rfl)

/-! ### Which families transport to the thin view -/

open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.IdentityRouteCapabilities
open Mettapedia.TypeTheory.RouteTransportDiscriminator

/-- An identity structure as a route layer. -/
def idLayer (M : IdStructure.{u}) : Layer.{u, u} M.Pt where
  Route := M.Pf
  refl := M.refl
  Support a b := Nonempty (M.Pf a b)
  forget route := ⟨route⟩

/-- A model of the groupoid laws as a route groupoid. -/
def idGroupoid (M : IdStructure.{u}) (laws : M ∈ groupoidUniverse) :
    RouteGroupoid (idLayer M) where
  comp := M.comp
  inv := M.inv
  refl_comp := @laws .leftUnit (Or.inr (Or.inl rfl))
  comp_refl := @laws .rightUnit (Or.inr (Or.inr (Or.inl rfl)))
  assoc := @laws .assoc (Or.inl rfl)
  inv_comp := @laws .leftInv (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  comp_inv := @laws .rightInv (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

variable {M : IdStructure.{u}} {groupoid : RouteGroupoid (idLayer M)}

/-- A transport family **descends to the thin view** when it transports
parallel proofs alike. -/
def DescendsToThin (family : TransportFamily.{u, u, w} (idLayer M) groupoid) : Prop :=
  ∀ {a b : M.Pt} (p q : M.Pf a b) (value : family.Fibre a),
    family.transport p value = family.transport q value

/-- The transport of a descending family along a proof of the thin view. -/
def thinTransport (family : TransportFamily.{u, u, w} (idLayer M) groupoid)
    (descends : DescendsToThin family) {a b : M.Pt} (p : (thinView M).Pf a b)
    (value : family.Fibre a) : family.Fibre b :=
  Trunc.lift (fun p' => family.transport p' value) (fun p q => descends p q value) p

/-- **A family transports along the thin view, compatibly with its own
transport, exactly when it descends.** -/
theorem descendsToThin_iff (family : TransportFamily.{u, u, w} (idLayer M) groupoid) :
    DescendsToThin family ↔
      ∃ thin : ∀ {a b : M.Pt}, (thinView M).Pf a b → family.Fibre a → family.Fibre b,
        ∀ {a b : M.Pt} (p : M.Pf a b) (value : family.Fibre a),
          thin (Trunc.mk p) value = family.transport p value := by
  constructor
  · intro descends
    exact ⟨fun p value => thinTransport family descends p value, fun _ _ => rfl⟩
  · rintro ⟨thin, agrees⟩ a b p q value
    rw [← agrees p value, ← agrees q value, Subsingleton.elim (Trunc.mk p) (Trunc.mk q)]

/-- **Every family descends to the thin view exactly when the structure is
already thin.**  The forward direction uses the representable family, whose
transport of reflexivity recovers the proof. -/
theorem all_descend_iff_uip (M : IdStructure.{u}) (laws : M ∈ groupoidUniverse) :
    (∀ family : TransportFamily.{u, u, u} (idLayer M) (idGroupoid M laws),
        DescendsToThin family) ↔ M.Sat .uip := by
  constructor
  · intro all a b p q
    have same := all (covariantRepresentable (idGroupoid M laws) a) p q ((idLayer M).refl a)
    exact ((covariantRepresentable_transport_reflSource (idGroupoid M laws) p).symm.trans
      same).trans (covariantRepresentable_transport_reflSource (idGroupoid M laws) q)
  · intro uip family a b p q value
    have equal : p = q := uip p q
    rw [equal]

/-- **In the thin view every family descends**: its identity loops have
trivial transport. -/
theorem thinView_all_descend (M : IdStructure.{u}) :
    ∀ family : TransportFamily.{u, u, u} (idLayer (thinView M))
        (idGroupoid (thinView M) (hsetFragment_subset_groupoidUniverse
          (thinView_mem_hsetFragment M))),
      DescendsToThin family :=
  (all_descend_iff_uip (thinView M) _).mpr (thinView_sat_uip M)

/-- **The h-set carve by holonomy.**  A model of the groupoid laws is in the
h-set fragment exactly when every transport family has trivial holonomy
around every loop.  The converse direction reads the holonomy of the
representable family, which is the loop itself. -/
theorem mem_hsetFragment_iff_trivialHolonomy (M : IdStructure.{u})
    (laws : M ∈ groupoidUniverse) :
    M ∈ hsetFragment ↔
      ∀ (family : TransportFamily.{u, u, u} (idLayer M) (idGroupoid M laws)) {a : M.Pt}
        (loop : M.Pf a a) (value : family.Fibre a), family.transport loop value = value := by
  constructor
  · intro member family a loop value
    have thin : M.Sat .uip := hsetFragment_subset_thin member
    have equal : loop = M.refl a := thin loop (M.refl a)
    rw [equal]
    exact family.transport_refl a value
  · intro trivial
    refine ⟨laws, fun φ member => ?_⟩
    rw [show φ = IdSentence.uip from member]
    show ∀ {a b : M.Pt} (p q : M.Pf a b), p = q
    intro a b p q
    have loopRefl : ∀ {c : M.Pt} (loop : M.Pf c c), loop = M.refl c := fun {c} loop =>
      (covariantRepresentable_transport_reflSource (idGroupoid M laws) loop).symm.trans
        (trivial (covariantRepresentable (idGroupoid M laws) c) loop ((idLayer M).refl c))
    calc p = M.comp p (M.refl b) := ((idGroupoid M laws).comp_refl p).symm
      _ = M.comp p (M.comp (M.inv q) q) :=
          congrArg (M.comp p) ((idGroupoid M laws).inv_comp q).symm
      _ = M.comp (M.comp p (M.inv q)) q := ((idGroupoid M laws).assoc p (M.inv q) q).symm
      _ = M.comp (M.refl a) q := congrArg (fun r => M.comp r q) (loopRefl (M.comp p (M.inv q)))
      _ = q := (idGroupoid M laws).refl_comp q

/-- **Control**: over the two-loop structure some family does not descend. -/
theorem xorModel_not_all_descend :
    ¬ ∀ family : TransportFamily.{u, u, u} (idLayer xorModel.{u})
        (idGroupoid xorModel xorModel_mem_groupoidUniverse),
      DescendsToThin family := fun all =>
  xorModel_not_uip ((all_descend_iff_uip _ _).mp all)

end Thin

end Mettapedia.GSLT.Scope
