import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingUnfold

/-!
# Presentations of an ambient process

Steps of an ambient process are listed at its **presentations** (`presentationsA`): the unfoldings of its root
canonical block within a depth, each read back at the root, the root dropped, every ambient's content a bag
(`presentBlock`). A presentation is a closed object process equivalent to the process (`presentation_facts`): an
unfolding reads back as the block, the read-back does not use the root, and padding keeps the process.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex ProcEquiv Members BaseContext rename dropIndex rename_comp
  rename_congr rename_id liftBVars_eq_rename shiftAbove drop_typed restrict_fill garbage_equivalent restricts_typed
  body_typed isObject_toPattern isObjectPattern_rename unfoldings mem_unfoldings)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (NameContext nameType procType)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (WellLocated decodeForm decode_typed decode_unread
  decode_object decode_unfolds decodeForm_settled rootForm rootForm_facts rootRead rootRead_equivalent names_base
  rename_succ_comp)

variable {free : FreeTypeContext}

/-- **Equivalent processes lifted past one name are equivalent**: the name restricted around both is garbage. -/
theorem unlift_equivalent {bound : List TypeExpr} {first second : Pattern}
    (firstTyped : HasType ambientCoreCalc free bound first procType)
    (secondTyped : HasType ambientCoreCalc free bound second procType)
    (lifted : ProcEquiv ambientCoreCalc ambientBlock free (nameType :: bound) (liftBVars 0 1 first)
      (liftBVars 0 1 second)) :
    ProcEquiv ambientCoreCalc ambientBlock free bound first second :=
  .trans _ _ _ (.symm _ _ (garbage_equivalent (language := ambientCoreCalc) (block := ambientBlock) firstTyped))
    (.trans _ _ _ (restrict_fill (language := ambientCoreCalc) (block := ambientBlock) lifted)
      (garbage_equivalent (language := ambientCoreCalc) (block := ambientBlock) secondTyped))

/-- **A block read back at the root, the root dropped**: a closed object process, which lifted past the root is the
read-back. -/
theorem lowered_facts {fuel : Nat} {form : Prenex}
    (well : WellLocated (· = Pattern.bvar 0) (.bvar 0) form)
    (members : Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ [nameType])
      form.components) :
    HasType ambientCoreCalc free []
        (rename (dropIndex 0) (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar 0) form))) procType ∧
      isObjectPattern (rename (dropIndex 0) (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar 0) form))) =
        true ∧
      liftBVars 0 1 (rename (dropIndex 0) (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar 0) form))) =
        Prenex.toPattern ambientBlock (decodeForm fuel (.bvar 0) form) := by
  set read := Prenex.toPattern ambientBlock (decodeForm fuel (.bvar 0) form) with readIs
  have readTyped : HasType ambientCoreCalc free [nameType] read procType :=
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.restricts_typed (language := ambientCoreCalc)
      (block := ambientBlock) _
      (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.body_typed
        ((decode_typed (free := free) fuel).1 (bound := [nameType]) (.bvar 0) form members))
  have unused : ¬ FreeIn 0 read := fun used => (decode_unread fuel).1 well 0 used rfl
  refine ⟨by simpa using drop_typed (language := ambientCoreCalc) (inner := []) (outer := []) readTyped unused, ?_, ?_⟩
  · rw [isObjectPattern_rename]
    exact isObject_toPattern ((decode_object fuel).1 _ _)
  · rw [liftBVars_eq_rename, rename_comp]
    conv_rhs => rw [← rename_id read]
    refine rename_congr _ fun index used => ?_
    have positive : index ≠ 0 := fun same => unused (same ▸ used)
    simp only [Function.comp, shiftAbove, dropIndex, id]
    split_ifs <;> omega

/-- **A block presented**: read back at the root, the root dropped, every ambient's content a bag. -/
def presentBlock (form : Prenex) : Pattern :=
  padA (rename (dropIndex 0) (Prenex.toPattern ambientBlock (decodeForm (3 * form.mass + 3) (.bvar 0) form)))

/-- **The presentations of a process**: the unfoldings of its root canonical block within a depth, presented. -/
def presentationsA (depth : Nat) (process : Pattern) : List Pattern :=
  (unfoldings locatedRepBlock depth (rootForm process)).map presentBlock

/-- **A presentation of a closed process is a closed object process equivalent to it.** -/
theorem presentation_facts (names : NameContext free) {process : Pattern}
    (typed : HasType ambientCoreCalc free [] process procType) (object : isObjectPattern process = true) (depth : Nat) :
    ∀ shown ∈ presentationsA depth process, HasType ambientCoreCalc free [] shown procType ∧
      isObjectPattern shown = true ∧ ProcEquiv ambientCoreCalc ambientBlock free [] process shown := by
  intro shown presented
  obtain ⟨unfolded, inUnfoldings, rfl⟩ := List.mem_map.mp presented
  have unfolds := (mem_unfoldings _ _ _).mp inUnfoldings
  have facts := rootForm_facts names typed object
  have rootWell := facts.1
  have rootMembers := facts.2.1
  obtain ⟨unfoldedWell, least, reads⟩ := decode_unfolds (names_base names 1) unfolds rootWell rootMembers
  have unfoldedMembers := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.UnfoldsWithin.members
    (language := locatedCalc) (names_base names 1) unfolds rootMembers
  obtain ⟨loweredTyped, loweredObject, lifted⟩ :=
    lowered_facts (fuel := 3 * unfolded.mass + 3) unfoldedWell unfoldedMembers
  -- the presented read-back, lifted, is the root read-back, which is the process lifted
  set fuel := max least (max (3 * unfolded.mass + 3) (3 * (rootForm process).mass + 3)) with fuelIs
  have readsSame := reads fuel (le_max_left _ _)
  rw [decodeForm_settled (.bvar 0) unfolded (first := fuel) (second := 3 * unfolded.mass + 3)
      (by omega) le_rfl,
    decodeForm_settled (.bvar 0) (rootForm process) (first := fuel) (second := 3 * (rootForm process).mass + 3)
      (by omega) le_rfl] at readsSame
  have rootSame := rootRead_equivalent facts
  have succIs : rename Nat.succ process = liftBVars 0 1 process := by
    simpa [rename_id] using rename_succ_comp id process
  rw [succIs] at rootSame
  have liftedSame : ProcEquiv ambientCoreCalc ambientBlock free (nameType :: [])
      (liftBVars 0 1 process)
      (liftBVars 0 1 (rename (dropIndex 0)
        (Prenex.toPattern ambientBlock (decodeForm (3 * unfolded.mass + 3) (.bvar 0) unfolded)))) := by
    rw [lifted]
    exact .symm _ _ (.trans _ _ _ readsSame rootSame)
  have lowered := unlift_equivalent typed loweredTyped liftedSame
  refine ⟨padA_typed loweredTyped loweredObject, padA_object _ loweredObject,
    .trans _ _ _ lowered (padA_equivalent _ (Nat.lt_succ_self _) loweredTyped loweredObject)⟩

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
