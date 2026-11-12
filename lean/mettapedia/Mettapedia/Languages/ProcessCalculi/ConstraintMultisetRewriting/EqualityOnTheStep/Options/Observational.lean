import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Options.Observability
import Mettapedia.TypeTheory.ContextualPredicateFamilies

/-!
# The observational option, in the predicate-family model

Observational type theory puts propositions in a proof-irrelevant universe and computes equality
from the structure of types: equality of functions is pointwise equality, and equality of
propositions is logical equivalence. Here the option is worked out in the tree's predicate-family
model (`ContextualPredicateFamilies.model`: types over a context are predicates, terms are proofs at
every point) and compared with the set-family model (`ContextualLadder.familiesCwf`: types are
families of types, terms are sections).

**Sets as predicates.** Over the context of small types, a set is a predicate (`PredSet`). The two
sets of `SetExtensionality` read there as `S X = ‖X‖ ∧ G` and `T X = G ∧ ‖X‖` (`sPred`, `tPred`),
where `‖X‖` is the inhabitation of `X`.

* **`S` and `T` become equal** (`sets_equal`), by function extensionality and propositional
  extensionality, the model's computation of equality at function types and at propositions
  (`observational_rules`).
* **Members carry no information** (`members_irrelevant`): any two terms of a type of the model are
  equal, the proof irrelevance of `ContextualPredicateFamilies.judged_readings_agree`.

**What happens to the proof-relevant encoding `Σ X Ground`.** In the set-family model, `S X` is
`X × G` and its members are pairs (`sFam`, `tFam`): with `X = Bool`, `G = Unit` there are two
different members (`setFamily_counts_two`). The predicate model sees only the inhabitation
(`truncate`), under which `S` and `T` have equal readings (`truncations_equal`) and the two members
become one (`members_irrelevant`). So the observational option keeps `Σ X Ground` only through its
truncation: the members' identity is lost, and with it every count of members. By
`Observability.proofIrrelevance_observed`, a knowledge with definitional proof irrelevance answers
the count of members differently from today's.

**The combination with evidence rows, and where it stops** (`truncate_respects`,
`transport_through_truncation`, `counting_not_respected`). Evidence in the sense of `Codes.setEq`
(maps both ways) between two proof-relevant sets gives equal truncations, so every family of
predicate-sets transports along such evidence through the truncation: evidence rows for data and
the proof-irrelevant universe for propositions combine coherently. They do not combine for a family
that reads more than inhabitation: "two different members" holds of a constant set `Bool` and fails
of `Unit`, while maps both ways exist. Evidence that is an equivalence, as the swaps of
`Computation.swap_round_trip` are, does respect counting (`Univalent.count_respected`).

**What the syntax would need.** The knowledge of the step is typed βη conversion of the tower package
(`TowerModel`), and the step's results about it use these hypotheses of the normalization framework,
each of which an observational extension must re-prove for its new package:

* the setting and its semantic laws (`Normalization.Setting`, `declarative_laws`), with semantic
  constants (`SemanticConstants`);
* the facts about weak-head forms of types (`FormFacts`, through `FormFacts.ofSemantic`): injectivity
  and discrimination of type formers (`TypeEq.pi_injective`, `TypeEq.sigma_injective`,
  `TypeEq.pi_ne_sigma`, `TypeEq.id_injective`);
* the shape of root computations (`RootShape`) and their preservation of typing (`RootPreserving`),
  with head equality preserving typing (`HeadPreserving`) and the cumulative algebra
  (`CumulativeAlgebra`);
* completeness of the conversion algorithm (`AlgorithmicComplete`, `TowerModel.complete`), on which
  η-long forms (`ContextualDependentEtaLong.long_exists`), normal supports
  (`ContextualDependentNormalSupport.equal_support`) and the unifier's completeness depend.

The observational package changes three things these hypotheses see. Its equality type computes by
the type it is taken at, which is a reduction of the built-in identity former rather than a root
computation of a declared constant. Its coercion computes by the head forms of two types, as the
existing value-side transport table does for the impredicative package
(`TypedEquality.Impredicative.ValueSide.TransportTable`). And its proof irrelevance adds an
η-like rule for proofs of propositions, so η-long forms of proofs collapse.

Results that would change: `Controls.idSets_uninhabited` and `Controls.idFamily_no_respect` hold for
the intensional identity type only; an observational identity type `Id (U0 → U0) T S` would have an
inhabitant, as its reading in the model has (`id_inhabited_in_model`). The refusal of
`SetExtensionality` (`extensionality_refused`) would not change: observational type theory, as
designed, keeps judgmental equality intensional, so `S` and `T` stay apart in the knowledge, and by
`Observability.conservative_iff` the absence and counting of rows of `S` and of `T` keep their
separate answers. Only a knowledge that reflected propositional equality into judgmental equality
would identify them (`Consequences.rowR`), and its equality would then have to decide logical
equivalence of the propositions it contains.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep.Options.Observational

open Mettapedia.TypeTheory.ContextualPredicateFamilies (model)
open Mettapedia.GSLT.Core.ContextualLadder (familiesCwf)

/-! ## Sets as predicates -/

/-- The context `X : U0`, read in the predicate-family model: the small types. -/
abbrev smallTypes : model.{1}.Ctx := Type

/-- **A set over `U0` in the predicate-family model**: a type over the context, a predicate. -/
abbrev PredSet : Type 1 := model.{1}.Ty smallTypes

/-- `S = {X | Σ (_ : X). Ground}`, read in the model, with `Ground` read as the proposition `G`. -/
def sPred (G : Prop) : PredSet := fun X => Nonempty X ∧ G

/-- `T = {X | Σ (_ : Ground). X}`, read in the model. -/
def tPred (G : Prop) : PredSet := fun X => G ∧ Nonempty X

/-- **Observational equality computes**: at function types it is pointwise equality, at
propositions it is logical equivalence. -/
theorem observational_rules :
    (∀ R R' : PredSet, R = R' ↔ ∀ X, R X = R' X) ∧ (∀ P Q : Prop, P = Q ↔ (P ↔ Q)) :=
  ⟨fun _ _ => ⟨fun same _ => congrFun same _, funext⟩,
    fun _ _ => ⟨fun same => same ▸ Iff.rfl, propext⟩⟩

/-- **In the predicate-family model, `S` and `T` are equal.** -/
theorem sets_equal (G : Prop) : sPred G = tPred G :=
  funext fun _ => propext And.comm

/-- **The identity of sets is inhabited at `T` and `S` in the model.** -/
theorem id_inhabited_in_model (G : Prop) : tPred G = sPred G := (sets_equal G).symm

/-- **Members carry no information**: any two terms of a type of the model are equal. -/
theorem members_irrelevant (G : Prop) (m m' : model.{1}.Tm smallTypes (sPred G)) : m = m' := by
  funext X
  show m X = m' X
  have same : (m X).down = (m' X).down := proof_irrel _ _
  calc m X = PLift.up (m X).down := rfl
    _ = PLift.up (m' X).down := congrArg PLift.up same
    _ = m' X := rfl

/-- A member exists wherever `X` is inhabited and `G` holds: the model's reading of `(x, g)`. -/
theorem member_exists (G : Prop) (g : G) : ∀ X : smallTypes, Nonempty X → sPred G X :=
  fun _ x => ⟨x, g⟩

/-! ## The proof-relevant encoding, in the set-family model -/

/-- `S X = X × G`, in the set-family model. -/
def sFam (G : Type) : familiesCwf.{1}.Ty Type := fun X => ULift.{1} (X × G)

/-- `T X = G × X`, in the set-family model. -/
def tFam (G : Type) : familiesCwf.{1}.Ty Type := fun X => ULift.{1} (G × X)

/-- **In the set-family model, members are counted**: `S Bool` with `G = Unit` has two different
members. -/
theorem setFamily_counts_two : ∃ a b : sFam Unit Bool, a ≠ b :=
  ⟨⟨(true, ())⟩, ⟨(false, ())⟩, fun same => absurd (congrArg (fun m : sFam Unit Bool => m.down.1) same) (by decide)⟩

/-- **The predicate model's reading of a family**: its inhabitation at each point. -/
def truncate (S : familiesCwf.{1}.Ty Type) : PredSet := fun X => Nonempty (S X)

/-- The truncation of `S` is the predicate reading of `S`. -/
theorem truncate_sFam (G : Type) : truncate (sFam G) = sPred (Nonempty G) := by
  funext X
  apply propext
  constructor
  · rintro ⟨⟨x, g⟩⟩
    exact ⟨⟨x⟩, ⟨g⟩⟩
  · rintro ⟨⟨x⟩, ⟨g⟩⟩
    exact ⟨⟨(x, g)⟩⟩

/-- **The truncations of `S` and `T` are equal.** -/
theorem truncations_equal (G : Type) : truncate (sFam G) = truncate (tFam G) := by
  funext X
  apply propext
  constructor
  · rintro ⟨⟨x, g⟩⟩
    exact ⟨⟨(g, x)⟩⟩
  · rintro ⟨⟨g, x⟩⟩
    exact ⟨⟨(x, g)⟩⟩

/-! ## Evidence rows for data, the proof-irrelevant universe for propositions -/

/-- **Evidence between two sets of the set-family model**, as `Codes.setEq` states it: maps both ways
at every point. -/
def SetEvidence (S T : familiesCwf.{1}.Ty Type) : Type 1 := ∀ X : Type, (S X → T X) × (T X → S X)

/-- The model's reading of the swaps of `SetExtensionality`. -/
def swapEvidence (G : Type) : SetEvidence (sFam G) (tFam G) :=
  fun _ => (fun p => ⟨(p.down.2, p.down.1)⟩, fun q => ⟨(q.down.2, q.down.1)⟩)

/-- **Evidence gives equal truncations.** -/
theorem truncate_respects {S T : familiesCwf.{1}.Ty Type} (e : SetEvidence S T) : truncate S = truncate T :=
  funext fun X => propext ⟨fun ⟨s⟩ => ⟨(e X).1 s⟩, fun ⟨t⟩ => ⟨(e X).2 t⟩⟩

/-- **Every family of predicate-sets transports along evidence, through the truncation.** -/
def transport_through_truncation (P : PredSet → Sort _) {S T : familiesCwf.{1}.Ty Type}
    (e : SetEvidence S T) : P (truncate S) → P (truncate T) :=
  fun p => truncate_respects e ▸ p

/-- Along the swaps, the transport is the one of `truncations_equal`. -/
theorem swap_truncation (G : Type) :
    truncate_respects (swapEvidence G) = truncations_equal G := rfl

/-- "The set has two different members at `X`." -/
def TwoMembers (X : Type) (S : familiesCwf.{1}.Ty Type) : Prop := ∃ a b : S X, a ≠ b

/-- The constant set `Bool`. -/
def boolSet : familiesCwf.{1}.Ty Type := fun _ => ULift.{1} Bool

/-- The constant set `Unit`. -/
def unitSet : familiesCwf.{1}.Ty Type := fun _ => ULift.{1} Unit

/-- **Where the combination stops**: there is evidence between `Bool` and `Unit` (maps both ways),
and "two different members" holds of the first and fails of the second. A family that reads more
than inhabitation is not transported by evidence that is only a pair of maps. -/
theorem counting_not_respected :
    Nonempty (SetEvidence boolSet unitSet) ∧ TwoMembers Bool boolSet ∧ ¬ TwoMembers Bool unitSet := by
  refine ⟨⟨fun _ => (fun _ => ⟨()⟩, fun _ => ⟨true⟩)⟩, ⟨⟨true⟩, ⟨false⟩, fun same => ?_⟩, ?_⟩
  · exact absurd (congrArg ULift.down same) (by decide)
  · rintro ⟨⟨a⟩, ⟨b⟩, different⟩
    exact different rfl

end EqualityOnTheStep.Options.Observational

#print axioms EqualityOnTheStep.Options.Observational.observational_rules
#print axioms EqualityOnTheStep.Options.Observational.sets_equal
#print axioms EqualityOnTheStep.Options.Observational.id_inhabited_in_model
#print axioms EqualityOnTheStep.Options.Observational.members_irrelevant
#print axioms EqualityOnTheStep.Options.Observational.setFamily_counts_two
#print axioms EqualityOnTheStep.Options.Observational.truncate_sFam
#print axioms EqualityOnTheStep.Options.Observational.truncations_equal
#print axioms EqualityOnTheStep.Options.Observational.truncate_respects
#print axioms EqualityOnTheStep.Options.Observational.swap_truncation
#print axioms EqualityOnTheStep.Options.Observational.counting_not_respected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
