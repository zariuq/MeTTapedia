import Mettapedia.Languages.ProcessCalculi.Ambient.LocatedReacts
import Mettapedia.Languages.ProcessCalculi.Ambient.CommSteps
import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingSubstitution

/-!
# Every step with communication is a located reaction

A step of a typed object process of the calculus with communication is, in located form, a reaction of the located
calculus with communication (`located_reacts_comm`). Entering, leaving and opening react as in the pure calculus, whose
located reactions are among these (`LocatedReaches.toComm`). A communication — an input and an output on one channel,
side by side — reacts as the located input and output at the input's place (`reacts_comm`), leaving the located body
with the message received, which is the located form of the received body (`encode_instantiate`); so the located form
reached is the located form of the contractum itself (`located_comm`). Steps in a bag, under a restriction and inside
an ambient react in context, as in the pure calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc AmbCommRawStep channels comm_parts
  commStep_typed)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex rename members_of_bag BlockSignature ReplicationStepAt
  bag_perm_equivalent)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (AmbNuRawStep ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock locatedLanguage)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (NameContext nameType procType encode shiftName
  encode_typed encode_bag encode_inName encode_inCap encode_outName encode_outCap output_inv name_cases_ambient
  message_notLambda encode_instantiate)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (decode_encode isMessage cap_isMessage)

variable {free : FreeTypeContext}

/-- **A located reaction of the pure calculus is one of the calculus with communication.** -/
theorem LocatedReaches.toComm {source target : Pattern}
    (reaches : LocatedReaches locatedReactions free source target) :
    LocatedReaches locatedCommReactions free source target := by
  intro count count' relabel here isLoc inside hereBelow locVariables hereLoc namesApart fvarsApart typed object
  obtain ⟨located, locatedTyped, locatedObject, ⟨reactionCount, redex, rest, reached⟩, facts⟩ :=
    reaches inside hereBelow locVariables hereLoc namesApart fvarsApart typed object
  exact ⟨located, locatedTyped, locatedObject, ⟨reactionCount, .marker redex, rest, reached⟩, facts⟩

/-- **An input and an output on one channel, among other components, react as located atoms**: the located input
and output at the place, leaving the located body with the located message received beside the others. -/
theorem reacts_comm {bound : List TypeExpr} {relabel : Nat → Nat} {here : Pattern} {elements : List Pattern}
    {input output : String} (listed : (input, output) ∈ channels) {i j : Nat} (hi : i < elements.length)
    (hj : j < (elements.eraseIdx i).length) {body message : Pattern}
    (receiving : elements[i] = .apply input [.lambda none body])
    (sending : (elements.eraseIdx i)[j] = .apply output [message]) (isMsg : isMessage message = true)
    (hereObject : isObjectPattern here = true) (objects : ∀ element ∈ elements, isObjectPattern element = true)
    (sourceTyped : HasType locatedCalc free bound (encode relabel here (.collection .hashBag elements none))
      procType) :
    ∃ count redex rest, ReplicationStepAt locatedCommReactions free bound
      (encode relabel here (.collection .hashBag elements none))
      (encode relabel here
        (.collection .hashBag (instantiateBVar message body :: (elements.eraseIdx i).eraseIdx j) none))
      count redex rest := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  -- the channel
  obtain ⟨capability, inputIs, outputIs⟩ : ∃ capability : Bool,
      encode relabel here (.apply input [.lambda none body]) =
        LocComm.input ⟨capability, here, encode (liftIndex 1 relabel) (shiftName here) body, rename relabel message⟩ ∧
      encode relabel here (.apply output [message]) =
        LocComm.output ⟨capability, here, encode (liftIndex 1 relabel) (shiftName here) body,
          rename relabel message⟩ := by
    simp only [channels, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
    rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨false, by rw [encode_inName]; rfl, by rw [encode_outName _ _ (message_notLambda isMsg)]; rfl⟩
    · exact ⟨true, by rw [encode_inCap]; rfl, by rw [encode_outCap _ _ (message_notLambda isMsg)]; rfl⟩
  set comm : LocComm :=
    ⟨capability, here, encode (liftIndex 1 relabel) (shiftName here) body, rename relabel message⟩ with commIs
  set others := (elements.eraseIdx i).eraseIdx j with othersIs
  -- the reception, located, is the located received body
  have resultIs : comm.result = [encode relabel here (instantiateBVar message body)] := by
    rw [commIs, LocComm.result, encode_instantiate isMsg]
  -- the input and the output first
  have permutation := perm_two elements i hi j hj
  rw [receiving, sending] at permutation
  rw [encode_bag] at sourceTyped
  have sourceMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) sourceTyped
  have mappedPerm := permutation.map (encode relabel here)
  simp only [List.map_cons, inputIs, outputIs] at mappedPerm
  have fromSource : ∀ element ∈ [comm.input, comm.output] ++ others.map (encode relabel here),
      element ∈ elements.map (encode relabel here) := fun element member =>
    mappedPerm.symm.subset (by simpa using member)
  refine ⟨0, .comm comm, others.map (encode relabel here), ⟨fun element member => ?_, fun element member => ?_, ?_, ?_⟩⟩
  · simpa using sourceMembers element (fromSource element (by simpa [locatedCommReactions, LocReaction.parts,
      LocComm.parts] using member))
  · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp (fromSource element (by
      simpa [locatedCommReactions, LocReaction.parts, LocComm.parts] using member))
    exact encode_object' hereObject (objects original inOriginal)
  · rw [encode_bag]
    exact (bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) sourceMembers
      mappedPerm).toEquationEquiv
  · show EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc _
      (.collection .hashBag (comm.result ++ others.map (encode relabel here)) none)
    rw [resultIs, encode_bag, List.map_cons]
    exact .refl _

/-- **A communication reacts in the located form**: the located input and output at the place react, leaving the
located form of the received body beside the others, which reads back as the reception. -/
theorem located_comm (names : NameContext free) {elements : List Pattern} {tail : Option String}
    {input output : String} (listed : (input, output) ∈ channels) {i j : Nat} (hi : i < elements.length)
    (hj : j < (elements.eraseIdx i).length) {binder : Option String} {body message : Pattern}
    (receiving : elements[i] = .apply input [.lambda binder body])
    (sending : (elements.eraseIdx i)[j] = .apply output [message]) :
    LocatedReaches locatedCommReactions free (.collection .hashBag elements tail)
      (.collection .hashBag (instantiateBVar message body :: (elements.eraseIdx i).eraseIdx j) none) := by
  intro count count' relabel here isLoc inside hereBelow locVariables hereLoc namesApart fvarsApart typed object
  obtain ⟨contractumTyped, contractumObject⟩ :=
    commStep_typed (AmbCommRawStep.comm listed i hi j hj binder body message receiving sending) typed object
  obtain ⟨rfl, objects⟩ := bag_objects object
  -- the input and the output
  have members := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) typed
  have inputTyped := members _ (List.getElem_mem hi)
  have inputObject := objects _ (List.getElem_mem hi)
  rw [receiving] at inputTyped inputObject
  have outputTyped := members _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
  have outputObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
  rw [sending] at outputTyped outputObject
  obtain ⟨-, rfl, -, -, -, messageObject, -, -⟩ := comm_parts listed inputTyped inputObject outputTyped outputObject
  have isMsg : isMessage message = true := by
    simp only [channels, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
    rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases name_cases_ambient (output_inv (sort := "Name") (by simp) outputTyped) rfl messageObject with
        ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> rfl
    · exact cap_isMessage (output_inv (sort := "Cap") (by simp) outputTyped) messageObject
  have hereTyped : HasType locatedCalc free (List.replicate count' nameType) (.bvar here) nameType :=
    .bvar (by simp [hereBelow])
  have locatedTyped := encode_typed names _ (Nat.lt_succ_self _) inside hereTyped rfl contractumTyped
    contractumObject
  exact ⟨_, locatedTyped, encode_object' rfl contractumObject,
    reacts_comm listed hi hj receiving sending isMsg rfl objects
      (encode_typed names _ (Nat.lt_succ_self _) inside hereTyped rfl typed object),
    decode_encode names _ (Nat.lt_succ_self _) inside hereBelow locVariables hereLoc namesApart fvarsApart
      contractumTyped contractumObject⟩

/-- **Every step of a typed object process with communication is a reaction of its located form**, to a typed object
located form whose canonical block reads back, wherever the process's does, as the contractum. -/
theorem located_reacts_comm (names : NameContext free) {source target : Pattern}
    (step : AmbCommRawStep source target) : LocatedReaches locatedCommReactions free source target := by
  induction step with
  | «open» i hi j hj name process content capability boundary =>
      exact LocatedReaches.toComm (located_reacts names (.open i hi j hj name process content capability boundary))
  | enter i hi j hj name target process host k hk mover capability destination =>
      exact LocatedReaches.toComm (located_reacts names (.enter i hi j hj name target process host k hk mover
        capability destination))
  | exit i hi name parent process k hk mover capability =>
      exact LocatedReaches.toComm (located_reacts names (.exit i hi name parent process k hk mover capability))
  | comm listed i hi j hj binder body message receiving sending =>
      exact located_comm names listed hi hj receiving sending
  | @par elements tail i hi target' inner recurse =>
      exact located_par names hi (fun typed object => (commStep_typed inner typed object).1) recurse
  | @res binder source' target' inner recurse => exact located_res names recurse
  | @ambient name content target' inner recurse =>
      exact located_ambient names name (fun typed object => (commStep_typed inner typed object).1) recurse

/-! ## At the root -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BaseContext UnfoldsWithin presentationDepth isReplicated Members
  canonP)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (EncodeFacts rootForm)

/-- **A step with communication of a closed object process is a reaction of an unfolding of its root canonical
block**, within the presentation depth: the reaction's parts beside the unfolding's other components, leaving, under
the unfolding's restrictions, a located form whose canonical block reads back at the root as the contractum. -/
theorem root_reaction_comm (names : NameContext free) (context : BaseContext free [nameType])
    {source target : Pattern} (step : AmbCommRawStep source target)
    (typed : HasType ambientCoreCalc free [] source procType) (object : isObjectPattern source = true) :
    ∃ unfolded, UnfoldsWithin locatedRepBlock (presentationDepth locatedRepBlock 3 (rootForm source))
        (rootForm source) unfolded ∧
      ∃ (redex : LocReaction) (rest : List Pattern), unfolded.components.Perm (redex.parts ++ rest) ∧
        (∀ part ∈ redex.parts, isReplicated locatedRepBlock part = false) ∧
        Members locatedCalc locatedBlock free (List.replicate unfolded.count nameType ++ [nameType])
          unfolded.components ∧
        (∀ component ∈ unfolded.components, isObjectPattern component = true) ∧
        ∃ located, HasType locatedCalc free [nameType] located procType ∧ isObjectPattern located = true ∧
          EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc
            (Prenex.restricts locatedBlock unfolded.count (.collection .hashBag (redex.result ++ rest) none))
            located ∧
          EncodeFacts free (· = .bvar 0) 0 [nameType] (canonP locatedRepBlock located) (rename Nat.succ target) :=
  root_reaction_of (reactions := locatedCommReactions) rfl names context (located_reacts_comm names step) typed
    object

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
