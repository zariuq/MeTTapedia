import Mettapedia.GSLT.LanguageDef.ExtensionComposition
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Coherence between authoring and semantic native-type readouts

An extension layer has an authoring GSLT whose reductions normalize or
compile declarations.  Its elaborated payload may then denote a second GSLT,
whose reductions are the program or proof semantics.  Applying OSLF to these
two systems therefore gives two native type theories with different roles.

They are not inverses.  Exact elaboration supplies a more precise square:
authoring equations and rewrites leave the elaborated payload unchanged, so
every declared semantic readout of that payload is invariant too.  Quotation
followed by elaboration recovers the semantic readout exactly.  For product
layers, the square includes the other component's authored empty payload;
that context cannot be omitted.

The semantic denotation itself remains additional law-bearing data.  A final
fixture gives the same unit payload two denotations whose generated diamonds
differ, proving that elaboration alone cannot choose the semantic NTT.
-/

namespace Mettapedia.GSLT.LanguageDef.TwoNTTCoherence

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe uPayload uObservation

/-! ## Recovery conditioned by retained composition knowledge -/

/-- Pair a lossy semantic shadow with retained authoring or composition
context. -/
def jointObservation {Original : Type*} {Shadow : Type*} {Context : Type*}
    (shadow : Original -> Shadow) (context : Original -> Context) :
    Original -> Shadow × Context :=
  fun original => (shadow original, context original)

/-- Context separates the remaining fibres of a shadow when two originals
with the same shadow and the same context must already be equal. -/
def ContextSeparatesFibres
    {Original : Type*} {Shadow : Type*} {Context : Type*}
    (shadow : Original -> Shadow) (context : Original -> Context) : Prop :=
  forall left right, shadow left = shadow right ->
    context left = context right -> left = right

/-- Fibre separation is exactly injectivity of the joint observation. -/
theorem jointObservation_injective_iff_contextSeparates
    {Original : Type*} {Shadow : Type*} {Context : Type*}
    (shadow : Original -> Shadow) (context : Original -> Context) :
    Function.Injective (jointObservation shadow context) <->
      ContextSeparatesFibres shadow context := by
  constructor
  · intro injective left right sameShadow sameContext
    apply injective
    exact Prod.ext sameShadow sameContext
  · intro separates left right sameJoint
    exact separates left right
      (congrArg Prod.fst sameJoint) (congrArg Prod.snd sameJoint)

/-- **Conditioned recovery criterion.**  When the original carrier is
inhabited, a recovery function from shadow plus retained context exists
exactly when that context separates every observational fibre. -/
theorem conditioned_recovery_iff_contextSeparates
    {Original : Type*} {Shadow : Type*} {Context : Type*}
    [Nonempty Original]
    (shadow : Original -> Shadow) (context : Original -> Context) :
    (exists recover : Shadow × Context -> Original,
      Function.LeftInverse recover (jointObservation shadow context)) <->
      ContextSeparatesFibres shadow context := by
  rw [← jointObservation_injective_iff_contextSeparates]
  exact (Function.injective_iff_hasLeftInverse
    (f := jointObservation shadow context)).symm

/-- An explicit collision records the exact obstruction to conditioned
recovery. -/
structure ContextCollision
    {Original : Type*} {Shadow : Type*} {Context : Type*}
    (shadow : Original -> Shadow) (context : Original -> Context) where
  left : Original
  right : Original
  sameShadow : shadow left = shadow right
  sameContext : context left = context right
  different : left ≠ right

/-- A collision in the conditioned fibre refutes every proposed recovery
function. -/
theorem ContextCollision.no_recovery
    {Original : Type*} {Shadow : Type*} {Context : Type*}
    {shadow : Original -> Shadow} {context : Original -> Context}
    (collision : ContextCollision shadow context) :
    ¬ exists recover : Shadow × Context -> Original,
      Function.LeftInverse recover (jointObservation shadow context) := by
  rintro ⟨recover, leftInverse⟩
  apply collision.different
  apply leftInverse.injective
  exact Prod.ext collision.sameShadow collision.sameContext

/-- Retaining an identity key separates even a completely collapsed shadow.
This is a positive recovery witness, not a claim that such a key is minimal. -/
theorem identity_context_recovers_collapsed_bool :
    ContextSeparatesFibres (fun _ : Bool => ()) id := by
  intro left right _ sameContext
  exact sameContext

/-- Constant context does not repair the same collapsed shadow. -/
def collapsedBool_constantContextCollision :
    ContextCollision (fun _ : Bool => ()) (fun _ : Bool => ()) where
  left := false
  right := true
  sameShadow := rfl
  sameContext := rfl
  different := Bool.false_ne_true

theorem constant_context_cannot_recover_collapsed_bool :
    ¬ exists recover : Unit × Unit -> Bool,
      Function.LeftInverse recover
        (jointObservation (fun _ : Bool => ()) (fun _ : Bool => ())) :=
  collapsedBool_constantContextCollision.no_recovery

/-! ## The generic authoring-to-readout square -/

/-- Apply an arbitrary semantic readout after partial exact elaboration. -/
def semanticReadoutAt {source : GSLT} {Payload : Type uPayload}
    (elaboration : GSLT.ExactElaboration source Payload)
    {Observation : Type uObservation} (readout : Payload -> Observation) :
    source.Term -> Option Observation :=
  fun term => (elaboration.elaborate term).map readout

/-- The three coherence laws forced by exact elaboration. -/
structure ReadoutCoherence {source : GSLT} {Payload : Type uPayload}
    (elaboration : GSLT.ExactElaboration source Payload)
    {Observation : Type uObservation}
    (readout : Payload -> Observation) : Prop where
  equation : forall {left right}, source.Equiv left right ->
    semanticReadoutAt elaboration readout left =
      semanticReadoutAt elaboration readout right
  rewrite : forall {sourceTerm targetTerm},
    source.Step sourceTerm targetTerm ->
      semanticReadoutAt elaboration readout sourceTerm =
        semanticReadoutAt elaboration readout targetTerm
  quote : forall payload,
    semanticReadoutAt elaboration readout (elaboration.quote payload) =
      some (readout payload)

/-- Every exact elaboration induces the complete readout-coherence square. -/
def exactElaboration_readoutCoherence
    {source : GSLT} {Payload : Type uPayload}
    (elaboration : GSLT.ExactElaboration source Payload)
    {Observation : Type uObservation} (readout : Payload -> Observation) :
    ReadoutCoherence elaboration readout where
  equation := by
    intro left right equivalent
    unfold semanticReadoutAt
    rw [elaboration.equation equivalent]
  rewrite := by
    intro sourceTerm targetTerm step
    unfold semanticReadoutAt
    rw [elaboration.rewrite step]
  quote := by
    intro payload
    simp [semanticReadoutAt, elaboration.elaborate_quote]

/-! ## Applying the square to generated semantic NTTs -/

/-- A semantic GSLT packaged with the OSLF type system generated from it. -/
abbrev GeneratedNTT :=
  Sigma fun theory : GSLT => OSLFTypeSystem (gsltRewriteSystem theory)

/-- Generate the native type system while retaining the theory that indexes
its dependent carrier. -/
def generateNTT (theory : GSLT) : GeneratedNTT :=
  ⟨theory, gsltOSLF theory⟩

/-- Elaborate an authored term, denote the payload as a semantic GSLT, and
generate that semantic theory's NTT. -/
def semanticNTTAt {source : GSLT} {Payload : Type uPayload}
    (elaboration : GSLT.ExactElaboration source Payload)
    (denote : Payload -> GSLT) : source.Term -> Option GeneratedNTT :=
  semanticReadoutAt elaboration (generateNTT ∘ denote)

/-- The authoring/semantic NTT coherence package is an instance of the exact
elaboration square once the semantic denotation is supplied. -/
theorem semanticNTT_coherence
    {source : GSLT} {Payload : Type uPayload}
    (elaboration : GSLT.ExactElaboration source Payload)
    (denote : Payload -> GSLT) :
    ReadoutCoherence elaboration (generateNTT ∘ denote) :=
  exactElaboration_readoutCoherence elaboration (generateNTT ∘ denote)

/-- A singleton-target diamond step in the authoring NTT leaves the generated
semantic NTT readout unchanged.  Authoring computation is compilation or
normalization of one payload, not a semantic program step. -/
theorem authoringDiamond_semanticNTT_invariant
    {source : GSLT} {Payload : Type uPayload}
    (elaboration : GSLT.ExactElaboration source Payload)
    (denote : Payload -> GSLT) (sourceTerm targetTerm : source.Term)
    (diamond :
      gsltDiamond source (fun candidate => candidate = targetTerm) sourceTerm) :
    semanticNTTAt elaboration denote sourceTerm =
      semanticNTTAt elaboration denote targetTerm := by
  apply (semanticNTT_coherence elaboration denote).rewrite
  exact (gsltDiamond_singleton_iff_step source sourceTerm targetTerm).mp diamond

/-- Quoting a payload and regenerating its semantic NTT is an exact round
trip at the declared readout. -/
theorem quote_semanticNTT_roundTrip
    {source : GSLT} {Payload : Type uPayload}
    (elaboration : GSLT.ExactElaboration source Payload)
    (denote : Payload -> GSLT) (payload : Payload) :
    semanticNTTAt elaboration denote (elaboration.quote payload) =
      some (generateNTT (denote payload)) := by
  exact (semanticNTT_coherence elaboration denote).quote payload

/-! ## Composition context is retained -/

/-- A left-only document in a product layer is read semantically with the
right layer's authored empty payload. -/
theorem product_readout_left
    {Left : Type uPayload} {Right : Type uObservation}
    (left : GSLT.CompositionalElaboration Left)
    (right : GSLT.CompositionalElaboration Right)
    {Observation : Type*} (readout : Left × Right -> Observation)
    (source : left.authoring.theory.Term) :
    semanticReadoutAt (left.product right).elaboration readout [Sum.inl source] =
      (left.elaboration.elaborate source).map
        (fun value => readout (value, right.emptyPayload)) := by
  unfold semanticReadoutAt
  rw [GSLT.CompositionalElaboration.product_elaborates_left_only]
  simp [Option.map_map, Function.comp_def]

/-- Symmetrically, a right-only document retains the left layer's authored
empty payload. -/
theorem product_readout_right
    {Left : Type uPayload} {Right : Type uObservation}
    (left : GSLT.CompositionalElaboration Left)
    (right : GSLT.CompositionalElaboration Right)
    {Observation : Type*} (readout : Left × Right -> Observation)
    (source : right.authoring.theory.Term) :
    semanticReadoutAt (left.product right).elaboration readout [Sum.inr source] =
      (right.elaboration.elaborate source).map
        (fun value => readout (left.emptyPayload, value)) := by
  unfold semanticReadoutAt
  rw [GSLT.CompositionalElaboration.product_elaborates_right_only]
  simp [Option.map_map, Function.comp_def]

/-! ## Elaboration alone does not select a semantic NTT -/

/-- A one-edge Boolean theory used to separate semantic denotations. -/
def oneStepGSLT : GSLT where
  Term := Bool
  equations :=
    { r := Eq
      iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩ }
  rewrites := fun source target => source = false /\ target = true
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def noStepDenotation : Unit -> GSLT := fun _ => GSLT.discrete Bool
def oneStepDenotation : Unit -> GSLT := fun _ => oneStepGSLT

/-- The same unit payload admits two semantic denotations with observably
different generated diamonds.  A semantic denotation law is therefore
necessary data, not something recovered from exact elaboration. -/
theorem same_payload_distinct_semantic_ntt_observation :
    (¬ gsltDiamond (noStepDenotation ())
      (fun candidate => candidate = true) false) /\
    gsltDiamond (oneStepDenotation ())
      (fun candidate => candidate = true) false := by
  constructor
  · rw [gsltDiamond_spec]
    rintro ⟨target, step, _⟩
    exact step.elim
  · rw [gsltDiamond_spec]
    exact ⟨true, ⟨rfl, rfl⟩, rfl⟩

end Mettapedia.GSLT.LanguageDef.TwoNTTCoherence
