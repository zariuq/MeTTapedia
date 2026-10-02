import Mettapedia.Logic.Propositions.ScenarioSpaces
import Mettapedia.Logic.Propositions.Totality
import Mettapedia.Logic.Propositions.EvidenceStates

/-!
# The morning star and the evening star

Frege's puzzle ("Über Sinn und Bedeutung", 1892) as a two-dimensional
interpretation.  'Phosphorus' names the body seen in the morning and 'Hesperus'
the body seen in the evening.  As things are, both are Venus.  For all one can
tell a priori, the evening body might have been something else; here, a comet.

The example is the negative control for descent along the Russellian leg and
along the possible-worlds leg.

* 'Hesperus is Phosphorus' is true and necessary but not a priori
  (`identity_trueIn`, `identity_necessary`, `identity_not_aPriori`): a
  necessary a posteriori truth (Kripke, *Naming and Necessity*, 1980).
* It expresses the same Russellian proposition and the same set of worlds as
  'Hesperus is Hesperus' (`russellian_identity_eq`, `secondary_identity_eq`),
  and a different Fregean proposition (`fregean_identity_ne`).
* So being a priori is not a feature of Russellian propositions, nor of sets of
  worlds (`aPrioriFiber`, `not_factors_russellian_aPriori`,
  `not_factors_secondary_aPriori`), and its two liftings to Russellian
  propositions disagree (`liftings_disagree`).
* 'Hesperus is a planet' and 'Phosphorus is a planet' express one Russellian
  proposition (`russellian_planet_eq`) and differ in their primary intensions
  (`primary_planet_ne`).  This is Chalmers's case of Sue, who knows that the
  morning star is a planet and believes that the evening star is not
  (*Constructing the World*, 2012, ch. 2 §2).
* "'Hesperus is a planet' is not a priori scrutable from 'Phosphorus is a
  planet', but the associated Russellian propositions are identical" (third
  excursus): `hesperusPlanet_not_scrutableFrom`.  So no relation between
  Russellian propositions under which a proposition is scrutable from itself
  agrees with scrutability of sentences
  (`no_reflexive_russellian_scrutability`).
* The identity is a truth scrutable from the base that says the evening body is
  a planet (`identity_scrutableFrom`), and that base is a scrutability base
  (`scrutabilityBase_hesperusPlanet`): in this small language one sentence
  settles which sky is actual.
* With the two-body scenario left out, the identity is a priori and the two
  names have one sense (`identity_aPriori_oneBody`,
  `fregean_identity_eq_oneBody`).
* With 'Hesperus is a planet' as the only positive sentence, the one-body sky
  extends the two-body sky.  In the two-body sky 'Hesperus is not a planet' is
  true and the positive truths do not settle it (`notPlanet_not_scrutableFrom`):
  that sky is not all there might be (`not_thatsAll_twoBodies`).  The one-body
  sky is (`thatsAll_oneBody`).
* The Russellian proposition of the identity depends on which sky is actual
  (`russellian_depends_on_actual`); its Fregean proposition takes no such
  argument.
* Observing the two-body sky counts against 'Hesperus is Phosphorus' and not
  against 'Hesperus is Hesperus', so evidence is not a function of the
  Russellian proposition (`evidence_not_factors_russellian`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions.MorningStar

open Mettapedia.GSLT.Core.NonFactorization Mettapedia.GSLT.Scope

/-- How things might turn out: the morning and the evening body are one, or
they are two. -/
inductive Sky
  | oneBody
  | twoBodies
  deriving DecidableEq

/-- The things there are to refer to. -/
inductive Body
  | venus
  | comet
  deriving DecidableEq

inductive Name
  | hesperus
  | phosphorus
  deriving DecidableEq

inductive Predicate
  | planet
  deriving DecidableEq

/-- 'Phosphorus' names Venus however things turn out; 'Hesperus' names whatever
is seen in the evening. -/
def referent : Name → Sky → Body
  | .phosphorus, _ => .venus
  | .hesperus, .oneBody => .venus
  | .hesperus, .twoBodies => .comet

/-- Scenarios and worlds coincide, and Venus is the only planet. -/
def interpretation : Interpretation Sky Sky Body Name Predicate where
  world := id
  referent := referent
  property := fun _ _ _ => {Body.venus}

/-- 'Hesperus is Phosphorus'. -/
def identity : Sentence Name Predicate :=
  .ident .hesperus .phosphorus

/-- 'Hesperus is Hesperus'. -/
def selfIdentity : Sentence Name Predicate :=
  .ident .hesperus .hesperus

/-- 'Hesperus is a planet'. -/
def hesperusPlanet : Sentence Name Predicate :=
  .pred .planet .hesperus

/-- 'Phosphorus is a planet'. -/
def phosphorusPlanet : Sentence Name Predicate :=
  .pred .planet .phosphorus

theorem identity_trueIn : interpretation.TrueIn .oneBody identity :=
  rfl

theorem identity_necessary : interpretation.Necessary .oneBody identity :=
  fun _ => rfl

theorem identity_not_aPriori : ¬ interpretation.APriori identity :=
  fun aPriori => Body.noConfusion (aPriori .twoBodies)

theorem selfIdentity_aPriori : interpretation.APriori selfIdentity :=
  interpretation.aPriori_ident_self .hesperus

/-- **One Russellian proposition**: both identities say of Venus that it is
Venus. -/
theorem russellian_identity_eq :
    interpretation.russellian .oneBody identity = interpretation.russellian .oneBody selfIdentity :=
  rfl

theorem secondary_identity_eq :
    interpretation.secondary .oneBody identity = interpretation.secondary .oneBody selfIdentity :=
  rfl

/-- **Two Fregean propositions**: the senses of the two names differ where the
evening body is a comet. -/
theorem fregean_identity_ne :
    interpretation.fregean identity ≠ interpretation.fregean selfIdentity := by
  intro same
  have senses : interpretation.nameSense .phosphorus = interpretation.nameSense .hesperus :=
    (Form.ident.inj same).2
  exact Body.noConfusion (congrFun senses .twoBodies)

/-- The witness: one Russellian proposition, expressed by an a priori sentence
and by a sentence that is not a priori. -/
def aPrioriFiber :
    NonTrivialFiber (interpretation.russellian .oneBody) interpretation.APriori :=
  .ofProp russellian_identity_eq.symm selfIdentity_aPriori identity_not_aPriori

/-- **Being a priori is not a feature of Russellian propositions.** -/
theorem not_factors_russellian_aPriori :
    ¬ Factors (interpretation.russellian .oneBody) interpretation.APriori :=
  aPrioriFiber.not_factors

/-- **Being a priori is not a feature of sets of worlds**: the obstruction
passes to the coarser view. -/
theorem not_factors_secondary_aPriori :
    ¬ Factors (interpretation.secondary .oneBody) interpretation.APriori :=
  not_factors_of_coarsening (fine := interpretation.russellian .oneBody)
    (coarsen := RussellianProposition.worlds)
    (fun sentence => (interpretation.worlds_russellian .oneBody sentence).symm)
    not_factors_russellian_aPriori

/-- The Russellian proposition that Hesperus is Phosphorus is in the image of
the a priori sentences and not in their universal image. -/
theorem liftings_disagree :
    interpretation.russellian .oneBody identity ∈
        interpretation.russellian .oneBody '' {sentence | interpretation.APriori sentence} ∧
      interpretation.russellian .oneBody identity ∉
        Set.kernImage (interpretation.russellian .oneBody)
          {sentence | interpretation.APriori sentence} :=
  ⟨⟨selfIdentity, selfIdentity_aPriori, russellian_identity_eq.symm⟩,
    fun all => identity_not_aPriori (all rfl)⟩

theorem russellian_planet_eq :
    interpretation.russellian .oneBody hesperusPlanet =
      interpretation.russellian .oneBody phosphorusPlanet :=
  rfl

theorem phosphorusPlanet_aPriori : interpretation.APriori phosphorusPlanet :=
  fun _ => rfl

theorem hesperusPlanet_not_aPriori : ¬ interpretation.APriori hesperusPlanet :=
  fun aPriori => Body.noConfusion (aPriori .twoBodies)

theorem primary_planet_ne :
    interpretation.primary hesperusPlanet ≠ interpretation.primary phosphorusPlanet :=
  fun same =>
    hesperusPlanet_not_aPriori
      ((ConstantOnFibers.iff interpretation.factors_primary_aPriori.constantOnFibers same).mpr
        phosphorusPlanet_aPriori)

/-! ## Scrutability -/

/-- **'Hesperus is a planet' is not scrutable from 'Phosphorus is a planet'**:
where the evening body is a comet, the second is true and the first false. -/
theorem hesperusPlanet_not_scrutableFrom :
    ¬ interpretation.ScrutableFrom {phosphorusPlanet} hesperusPlanet := by
  intro scrutable
  have verified : Sky.twoBodies ∈ interpretation.primary hesperusPlanet :=
    interpretation.scrutableFrom_iff.mp scrutable .twoBodies fun member inBase => by
      rw [Set.mem_singleton_iff.mp inBase]
      exact phosphorusPlanet_aPriori .twoBodies
  exact Body.noConfusion verified

/-- **No reflexive scrutability relation on Russellian propositions matches
scrutability of sentences.** -/
theorem no_reflexive_russellian_scrutability
    (propositional : Set (RussellianProposition Sky Body) → RussellianProposition Sky Body → Prop)
    (reflexive : ∀ proposition, propositional {proposition} proposition) :
    ¬ ∀ (base : Set (Sentence Name Predicate)) (sentence : Sentence Name Predicate),
        interpretation.ScrutableFrom base sentence ↔
          propositional (interpretation.russellian .oneBody '' base)
            (interpretation.russellian .oneBody sentence) := by
  intro agrees
  refine hesperusPlanet_not_scrutableFrom ((agrees _ _).mpr ?_)
  rw [Set.image_singleton, ← russellian_planet_eq]
  exact reflexive _

/-- Where the evening body is a planet, it is Venus, and so is the morning
body. -/
theorem identity_scrutableFrom : interpretation.ScrutableFrom {hesperusPlanet} identity := by
  refine interpretation.scrutableFrom_iff.mpr fun scenario verifies => ?_
  have planet : scenario ∈ interpretation.primary hesperusPlanet := verifies _ rfl
  cases scenario with
  | oneBody => rfl
  | twoBodies => exact Body.noConfusion planet

/-- **One sentence is a scrutability base here**: the only scenario verifying
'Hesperus is a planet' is the actual one. -/
theorem scrutabilityBase_hesperusPlanet :
    interpretation.ScrutabilityBase .oneBody {hesperusPlanet} := by
  refine (interpretation.scrutabilityBase_iff .oneBody _).mpr ⟨?_, ?_⟩
  · intro member inBase
    rw [Set.mem_singleton_iff.mp inBase]
    rfl
  · intro scenario verifies sentence
    have planet : scenario ∈ interpretation.primary hesperusPlanet := verifies _ rfl
    cases scenario with
    | oneBody => exact Iff.rfl
    | twoBodies => exact Body.noConfusion planet

/-! ## Leaving a scenario out -/

theorem identity_aPriori_oneBody :
    (interpretation.pullback fun _ : Unit => Sky.oneBody).APriori identity :=
  fun _ => rfl

theorem fregean_identity_eq_oneBody :
    (interpretation.pullback fun _ : Unit => Sky.oneBody).fregean identity =
      (interpretation.pullback fun _ : Unit => Sky.oneBody).fregean selfIdentity :=
  rfl

/-! ## Without a that's-all truth -/

/-- The positive sentences: 'Hesperus is a planet'. -/
def positiveSentences : Set (Sentence Name Predicate) :=
  {hesperusPlanet}

theorem oneBody_extends_twoBodies :
    interpretation.Extends positiveSentences .oneBody .twoBodies := by
  intro sentence member _
  rw [Set.mem_singleton_iff.mp member]
  rfl

theorem notPlanet_trueIn : interpretation.TrueIn .twoBodies (.neg hesperusPlanet) :=
  fun planet => Body.noConfusion planet

/-- **A negative truth that the positive truths do not settle.** -/
theorem notPlanet_not_scrutableFrom :
    ¬ interpretation.ScrutableFrom (interpretation.truthsIn .twoBodies positiveSentences)
      (.neg hesperusPlanet) :=
  interpretation.not_scrutableFrom_positiveTruths positiveSentences oneBody_extends_twoBodies
    fun notPlanet => notPlanet rfl

theorem not_thatsAll_twoBodies : ¬ interpretation.ThatsAll positiveSentences .twoBodies :=
  fun thatsAll =>
    Body.noConfusion ((thatsAll .oneBody oneBody_extends_twoBodies hesperusPlanet).mpr rfl)

theorem thatsAll_oneBody : interpretation.ThatsAll positiveSentences .oneBody := by
  intro scenario extension sentence
  have planet : scenario ∈ interpretation.primary hesperusPlanet :=
    extension hesperusPlanet rfl rfl
  cases scenario with
  | oneBody => exact Iff.rfl
  | twoBodies => exact Body.noConfusion planet

/-! ## Reference depends on which scenario is actual -/

theorem russellian_depends_on_actual :
    interpretation.russellian .oneBody identity ≠ interpretation.russellian .twoBodies identity :=
  fun same => Body.noConfusion (Form.ident.inj same).1

/-! ## Evidence attaches to senses, not to Russellian propositions -/

theorem evidence_identity_ne :
    interpretation.evidence ({Sky.twoBodies} : Multiset Sky) selfIdentity ≠
      interpretation.evidence ({Sky.twoBodies} : Multiset Sky) identity := by
  intro same
  have noneAgainst :
      (interpretation.evidence ({Sky.twoBodies} : Multiset Sky) selfIdentity).neg = 0 :=
    (interpretation.neg_evidence_eq_zero_iff _ _).mpr fun scenario _ =>
      selfIdentity_aPriori scenario
  rw [same] at noneAgainst
  exact Body.noConfusion
    ((interpretation.neg_evidence_eq_zero_iff _ _).mp noneAgainst .twoBodies
      (Multiset.mem_singleton_self _))

/-- The witness: one Russellian proposition, two bodies of evidence. -/
noncomputable def evidenceFiber :
    NonTrivialFiber (interpretation.russellian .oneBody)
      (interpretation.evidence ({Sky.twoBodies} : Multiset Sky)) where
  left := selfIdentity
  right := identity
  sameShadow := russellian_identity_eq.symm
  differentValue := evidence_identity_ne

/-- **Evidence is not a function of the Russellian proposition.** -/
theorem evidence_not_factors_russellian :
    ¬ Factors (interpretation.russellian .oneBody)
      (interpretation.evidence ({Sky.twoBodies} : Multiset Sky)) :=
  evidenceFiber.not_factors

end Mettapedia.Logic.Propositions.MorningStar
