import Mettapedia.GSLT.Core.LooseRelationEquipment

/-!
# Speech acts over proof-relevant evidence

Assertoric speech acts (Austin's constatives, Searle's assertives, Brandom's
commitments) formalized over proof-relevant evidence, integrated with the
loose-relation equipment that carries the project's relational semantics.

The load-bearing identifications:

* **Assertion is an erasure quotient.**  A speaker holding evidence asserts
  only its truth; the evidence survives privately and answers the challenge
  "how do you know?".  `Assertion.toPublic` is that erasure, and
  `not_injective_toPublic` proves it genuinely forgets: two assertions
  backed by distinct evidence have equal public form.
* **Hearsay is the quotient without the fibre.**  Re-asserting a public
  assertion carries truth but no canonical witness.
  `truthToEvidence_not_unique` shows a challenge met from truth alone has
  no preferred answer; recovering evidence from bare truth is exactly a
  choice principle, which is why hearsay is a weaker act than testimony.
* **Wh-questions are metavariable inhabitation.**  A question is a fibre of
  a proof-relevant relation; each answer is a witness, and
  `whWitness_multiplicity_exceeds_truth` separates the *bag* of witnesses
  from the *set* of true answers on a worked example whose relation is the
  equipment's horizontal composition.
* **Abstention is a speech act, never a pruning license.**  A response may
  establish, refute with an obstruction, decline as outside the responder's
  fragment, or report exhaustion; only refutation retracts a commitment
  (`retractOnRefutation_outsideFragment`), and the naive update that also
  prunes on abstention is refuted by an explicit two-frame counterexample
  (`retractOnSilence_unsound`) in which a wider authority establishes the
  very claim the narrow one declined.
* **Evidential morphemes are outcome constructors.**  Natural languages
  grammaticalize evidence source (witnessed, reported, and hedges); the
  `Evidential` readout of a response is such a morpheme, and
  `evidential_witnessed_of_decided` pins the classification.

Positive and negative examples accompany each construction.  No axioms
beyond the kernel's; audits are printed at the bottom of the file.
-/

namespace Mettapedia.Linguistics.SpeechAct

open Mettapedia.GSLT.LooseRelationEquipment

universe u v

/-! ## Frames, assertions, and the erasure quotient -/

/-- An assertoric frame: claims together with their proof-relevant backing.
`Evidence` inhabitants are what a sincere speaker holds; `Obstruction`
inhabitants are checked counterexamples, the only backing that licenses
denial. -/
structure Frame : Type (max (u + 1) (v + 1)) where
  Claim : Type u
  Evidence : Claim → Type v
  Obstruction : Claim → Type v

/-- Truth of a claim is the propositional erasure of its evidence. -/
def Frame.Holds (F : Frame.{u, v}) (claim : F.Claim) : Prop :=
  Nonempty (F.Evidence claim)

/-- Falsity of a claim is the propositional erasure of its obstructions. -/
def Frame.Fails (F : Frame.{u, v}) (claim : F.Claim) : Prop :=
  Nonempty (F.Obstruction claim)

/-- A sincere assertion: a claim together with the evidence backing it.
This is the speaker's private object. -/
structure Assertion (F : Frame.{u, v}) : Type (max u v) where
  claim : F.Claim
  evidence : F.Evidence claim

/-- A public assertion: what crosses the channel.  The evidence has been
erased to truth. -/
structure PublicAssertion (F : Frame.{u, v}) : Type u where
  claim : F.Claim
  holds : F.Holds claim

/-- The erasure quotient performed by uttering an assertion. -/
def Assertion.toPublic {F : Frame.{u, v}} (a : Assertion F) :
    PublicAssertion F :=
  ⟨a.claim, ⟨a.evidence⟩⟩

@[simp] theorem Assertion.toPublic_claim {F : Frame.{u, v}}
    (a : Assertion F) : a.toPublic.claim = a.claim := rfl

/-- Meeting the challenge "how do you know?": a sincere asserter answers
from the retained evidence.  The definition is the honesty theorem — the
response *is* the backing. -/
def Assertion.meetChallenge {F : Frame.{u, v}} (a : Assertion F) :
    F.Evidence a.claim :=
  a.evidence

/-- Re-asserting the challenged evidence reproduces the original public
assertion: challenge and response commute with utterance. -/
theorem Assertion.toPublic_meetChallenge {F : Frame.{u, v}}
    (a : Assertion F) :
    (Assertion.mk a.claim a.meetChallenge).toPublic = a.toPublic := rfl

/-- The two-sided coin frame: one claim, two distinct pieces of evidence.
The minimal witness that assertion forgets multiplicity. -/
def coinFrame : Frame where
  Claim := Unit
  Evidence := fun _ => Bool
  Obstruction := fun _ => Empty

/-- Bool readout of coin evidence (the claim type is `Unit`, so the
evidence fibre is definitionally `Bool`). -/
private def coinReadout (a : Assertion coinFrame) : Bool := a.evidence

/-- **Assertion genuinely forgets.**  The erasure quotient is not
injective: distinct evidence, identical public form.  This is the
speech-act face of "strength does not factor through truth". -/
theorem not_injective_toPublic :
    ¬ Function.Injective (Assertion.toPublic (F := coinFrame)) := by
  intro inj
  have h := inj (a₁ := ⟨(), true⟩) (a₂ := ⟨(), false⟩) rfl
  exact Bool.noConfusion (congrArg coinReadout h)

/-! ## Hearsay: truth without a canonical witness -/

/-- Hearsay: adopting a public assertion as one's own commitment.  Truth is
carried; the fibre is not. -/
def PublicAssertion.hearsay {F : Frame.{u, v}} (p : PublicAssertion F) :
    PublicAssertion F := p

@[simp] theorem PublicAssertion.hearsay_eq {F : Frame.{u, v}}
    (p : PublicAssertion F) : p.hearsay = p := rfl

/-- **Hearsay cannot canonically meet a challenge.**  Any policy producing
evidence from bare truth is one of several: on the coin frame there exist
two distinct such policies.  (Producing evidence from truth *at all* is a
choice principle; this theorem shows that even where it is possible it is
non-canonical, which is why testimony outranks hearsay.) -/
theorem truthToEvidence_not_unique :
    ∃ f g : (c : coinFrame.Claim) → coinFrame.Holds c → coinFrame.Evidence c,
      f ≠ g := by
  refine ⟨fun _ _ => true, fun _ _ => false, fun h => ?_⟩
  have := congrFun (congrFun h ()) ⟨true⟩
  exact Bool.noConfusion this

/-! ## Wh-questions as metavariable inhabitation

A wh-question fixes one argument of a proof-relevant relation and asks for
inhabitants of the resulting fibre.  Answers are witnesses; distinct
witnesses over the same individual are distinct answers in the bag even
when they collapse in the truth set. -/

/-- The wh-question "which `x` stands in `relation` to `target`?".  An
inhabitant is one complete answer: an individual with its witness. -/
def WhAnswer {Source Target : Type u} (relation : Loose Source Target)
    (target : Target) : Type u :=
  Sigma fun source => relation source target

/-- The individual named by an answer (the part a truth-level readout
keeps). -/
def WhAnswer.individual {Source Target : Type u}
    {relation : Loose Source Target} {target : Target}
    (answer : WhAnswer relation target) : Source :=
  answer.1

/-! ### Worked example: grandparenthood by relational composition

Five people; `alice` parents `bob` and `eve`; `dana` parents `eve`; `bob`
and `eve` parent `carol`.  Grandparenthood is the equipment's horizontal
composition of parenthood with itself, so every answer to "who is a
grandparent of carol?" carries its intermediate parent as part of the
witness. -/

inductive Person : Type
  | alice | bob | carol | dana | eve
  deriving DecidableEq

/-- Proof-relevant parenthood: each constructor is one act of parenting. -/
inductive ParentOf : Person → Person → Type
  | aliceBob : ParentOf .alice .bob
  | aliceEve : ParentOf .alice .eve
  | danaEve : ParentOf .dana .eve
  | bobCarol : ParentOf .bob .carol
  | eveCarol : ParentOf .eve .carol

/-- Grandparenthood as horizontal composition: the intermediate parent and
both parenting witnesses are retained. -/
def grandparentOf : Loose Person Person :=
  comp ParentOf ParentOf

/-- Alice grandparents carol through bob. -/
def aliceViaBob : WhAnswer grandparentOf .carol :=
  ⟨.alice, ⟨.bob, .aliceBob, .bobCarol⟩⟩

/-- Alice grandparents carol *again* through eve — a second act, same
individual. -/
def aliceViaEve : WhAnswer grandparentOf .carol :=
  ⟨.alice, ⟨.eve, .aliceEve, .eveCarol⟩⟩

/-- Dana grandparents carol through eve. -/
def danaViaEve : WhAnswer grandparentOf .carol :=
  ⟨.dana, ⟨.eve, .danaEve, .eveCarol⟩⟩

/-- **The answer bag is finer than the truth set.**  Three pairwise
distinct answers name only two individuals: multiplicity is semantic
content that a truth-level readout of the question forgets.  (`aliceViaBob`
and `aliceViaEve` differ in the *witness*, not the individual.) -/
theorem whWitness_multiplicity_exceeds_truth :
    aliceViaBob ≠ aliceViaEve ∧
      aliceViaBob.individual = aliceViaEve.individual ∧
        aliceViaBob.individual ≠ danaViaEve.individual := by
  refine ⟨fun h => ?_, rfl, by decide⟩
  have h₂ : aliceViaBob.2.1 = aliceViaEve.2.1 := by rw [h]
  exact Person.noConfusion h₂

/-- Negative control: nobody grandparents alice — the question with an
empty fibre.  A correct responder abstains from naming and refutes with
this emptiness. -/
theorem whAnswer_alice_empty : IsEmpty (WhAnswer grandparentOf .alice) := by
  constructor
  rintro ⟨source, mid, _, toAlice⟩
  cases toAlice

/-! ## Responses, retraction, and abstention

A response to a queried claim either decides it (with evidence or a checked
obstruction) or declines — as outside the responder's fragment, or for
exhausted resources.  Only refutation retracts a commitment. -/

/-- The four assertoric responses.  `outsideFragment` and `exhausted` are
speech acts of *competence report*, not verdicts. -/
inductive Response (F : Frame.{u, v}) (claim : F.Claim) : Type v
  | established (evidence : F.Evidence claim)
  | refuted (obstruction : F.Obstruction claim)
  | outsideFragment
  | exhausted

/-- Commitment update: retract exactly on refutation.  `commitments` is the
current list of live claims (a scoreboard in Brandom's sense). -/
def retractOnRefutation {F : Frame.{u, v}} [DecidableEq F.Claim]
    (claim : F.Claim) :
    Response F claim → List F.Claim → List F.Claim
  | .refuted _, commitments => commitments.erase claim
  | _, commitments => commitments

/-- Declining outside the fragment retracts nothing. -/
@[simp] theorem retractOnRefutation_outsideFragment {F : Frame.{u, v}}
    [DecidableEq F.Claim] (claim : F.Claim) (commitments : List F.Claim) :
    retractOnRefutation claim .outsideFragment commitments = commitments :=
  rfl

/-- Reporting exhaustion retracts nothing. -/
@[simp] theorem retractOnRefutation_exhausted {F : Frame.{u, v}}
    [DecidableEq F.Claim] (claim : F.Claim) (commitments : List F.Claim) :
    retractOnRefutation claim .exhausted commitments = commitments :=
  rfl

/-- The unsound update: treating every non-established response as a
retraction.  This is the policy the abstention laws exist to forbid. -/
def retractOnSilence {F : Frame.{u, v}} [DecidableEq F.Claim]
    (claim : F.Claim) :
    Response F claim → List F.Claim → List F.Claim
  | .established _, commitments => commitments
  | _, commitments => commitments.erase claim

/-! ### The two-frame counterexample

A narrow responder knows only direct parenthood; grandparenthood is outside
its fragment.  A wide responder decides grandparenthood.  The claim "alice
grandparents carol" is outside the narrow fragment yet established by the
wide frame — so the silence-pruning update discards a live truth. -/

/-- Claims about this family: parenthood and grandparenthood. -/
inductive FamilyClaim : Type
  | parent (child parent : Person)
  | grandparent (grandchild grandparent : Person)
  deriving DecidableEq

/-- The wide frame decides both claim forms, proof-relevantly.
(Obstructions are omitted from the showcase; refutation is exercised
abstractly above.) -/
def wideFrame : Frame where
  Claim := FamilyClaim
  Evidence
    | .parent child parent => ParentOf parent child
    | .grandparent grandchild grandparent =>
        grandparentOf grandparent grandchild
  Obstruction := fun _ => Empty

instance : DecidableEq wideFrame.Claim :=
  inferInstanceAs (DecidableEq FamilyClaim)

/-- The claim the narrow responder must decline. -/
def aliceGrandparentsCarol : wideFrame.Claim :=
  .grandparent .carol .alice

/-- The narrow responder's honest response: outside its fragment. -/
def narrowResponse : Response wideFrame aliceGrandparentsCarol :=
  .outsideFragment

/-- **Silence-pruning is unsound.**  The naive update drops a commitment
that the wide frame establishes; the lawful update keeps it.  Abstention
is a competence report, never negative evidence. -/
theorem retractOnSilence_unsound :
    wideFrame.Holds aliceGrandparentsCarol ∧
      retractOnSilence aliceGrandparentsCarol narrowResponse
          [aliceGrandparentsCarol] = [] ∧
        retractOnRefutation aliceGrandparentsCarol narrowResponse
            [aliceGrandparentsCarol] = [aliceGrandparentsCarol] := by
  refine ⟨⟨⟨.bob, .aliceBob, .bobCarol⟩⟩, ?_, rfl⟩
  simp [retractOnSilence, narrowResponse, List.erase]

/-! ## Evidential morphemes -/

/-- The evidential readout a speakable concrete syntax would grammaticalize:
how the speaker's response relates to evidence.  `witnessed` covers both
polarities of decision — evidentials mark source, not polarity;
`reported` marks hearsay; the final two mark the competence reports. -/
inductive Evidential : Type
  | witnessed | reported | outside | exhausted
  deriving DecidableEq

/-- The evidential of a first-hand response. -/
def Response.evidential {F : Frame.{u, v}} {claim : F.Claim} :
    Response F claim → Evidential
  | .established _ => .witnessed
  | .refuted _ => .witnessed
  | .outsideFragment => .outside
  | .exhausted => .exhausted

/-- Decided responses of either polarity wear the witnessed evidential:
the morpheme marks evidence source, never verdict polarity. -/
theorem evidential_witnessed_of_decided {F : Frame.{u, v}}
    {claim : F.Claim} (response : Response F claim)
    (decided : (∃ e, response = .established e) ∨
      ∃ o, response = .refuted o) :
    response.evidential = .witnessed := by
  rcases decided with ⟨e, rfl⟩ | ⟨o, rfl⟩ <;> rfl

/-- Negative control: an abstaining response never wears the witnessed
evidential — competence reports are not testimony. -/
theorem evidential_ne_witnessed_of_outsideFragment {F : Frame.{u, v}}
    {claim : F.Claim} :
    (Response.outsideFragment : Response F claim).evidential ≠
      .witnessed := by
  intro h
  exact Evidential.noConfusion h

end Mettapedia.Linguistics.SpeechAct

#print axioms Mettapedia.Linguistics.SpeechAct.not_injective_toPublic
#print axioms Mettapedia.Linguistics.SpeechAct.truthToEvidence_not_unique
#print axioms
  Mettapedia.Linguistics.SpeechAct.whWitness_multiplicity_exceeds_truth
#print axioms Mettapedia.Linguistics.SpeechAct.whAnswer_alice_empty
#print axioms Mettapedia.Linguistics.SpeechAct.retractOnSilence_unsound
#print axioms
  Mettapedia.Linguistics.SpeechAct.evidential_witnessed_of_decided
