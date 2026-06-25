import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mettapedia.KR.ConceptGeometry.AbstractInheritance
import Mettapedia.PLN.Evidence.EvidenceQuantale
import Mettapedia.PLN.Comparisons.NARS.NARSEvidenceBridge

/-!
# NARS-Style Dual Inheritance

This module formalizes a small semantic core for NARS-style inheritance:

- terms carry both extensional and intensional meaning
- inheritance is simultaneously extent inclusion and reversed intent inclusion
- evidence for `S -> P` aggregates extensional and intensional witnesses into
  `BinaryEvidence`

The resulting truth-value view reuses the existing NARS/PLN bridge by mapping
that evidence into a NARS `(frequency, confidence)` pair.
-/

namespace Mettapedia.PLN.Comparisons.NARS.NARSInheritance

open Mettapedia.KR.ConceptGeometry
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Comparisons.NARS.NARSMettaTruthFunctions
open Mettapedia.PLN.Comparisons.NARS.NARSEvidenceBridge
open scoped ENNReal

universe u v w

/-- A minimal NARS term language for dual inheritance. -/
inductive Term (Atom : Type u) where
  | atom : Atom → Term Atom
  | inter : Term Atom → Term Atom → Term Atom
  | iinter : Term Atom → Term Atom → Term Atom
  | diff : Term Atom → Term Atom → Term Atom
  | idiff : Term Atom → Term Atom → Term Atom
  deriving DecidableEq, Repr

/-- A semantic frame gives each atomic term both an extension and an intension. -/
structure Frame (Atom : Type u) (Obj : Type v) (Attr : Type w) where
  atomExtension : Atom → Finset Obj
  atomIntension : Atom → Finset Attr

namespace Frame

variable {Atom : Type u} {Obj : Type v} {Attr : Type w}
variable [DecidableEq Obj] [DecidableEq Attr]

/-- Recursive extensional meaning of a term. -/
def extension (F : Frame Atom Obj Attr) : Term Atom → Finset Obj
  | .atom a => F.atomExtension a
  | .inter s t => F.extension s ∩ F.extension t
  | .iinter s t => F.extension s ∪ F.extension t
  | .diff s t => F.extension s \ F.extension t
  | .idiff s _t => F.extension s

/-- Recursive intensional meaning of a term. -/
def intension (F : Frame Atom Obj Attr) : Term Atom → Finset Attr
  | .atom a => F.atomIntension a
  | .inter s t => F.intension s ∪ F.intension t
  | .iinter s t => F.intension s ∩ F.intension t
  | .diff s _t => F.intension s
  | .idiff s t => F.intension s \ F.intension t

omit [DecidableEq Attr] in
@[simp] theorem extension_atom (F : Frame Atom Obj Attr) (a : Atom) :
    F.extension (.atom a) = F.atomExtension a := rfl

omit [DecidableEq Attr] in
@[simp] theorem extension_inter (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.extension (.inter s t) = F.extension s ∩ F.extension t := rfl

omit [DecidableEq Obj] in
@[simp] theorem intension_atom (F : Frame Atom Obj Attr) (a : Atom) :
    F.intension (.atom a) = F.atomIntension a := rfl

omit [DecidableEq Obj] in
@[simp] theorem intension_inter (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.intension (.inter s t) = F.intension s ∪ F.intension t := rfl

omit [DecidableEq Attr] in
@[simp] theorem extension_iinter (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.extension (.iinter s t) = F.extension s ∪ F.extension t := rfl

omit [DecidableEq Obj] in
@[simp] theorem intension_iinter (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.intension (.iinter s t) = F.intension s ∩ F.intension t := rfl

omit [DecidableEq Attr] in
@[simp] theorem extension_diff (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.extension (.diff s t) = F.extension s \ F.extension t := rfl

omit [DecidableEq Obj] in
@[simp] theorem intension_diff (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.intension (.diff s t) = F.intension s := rfl

omit [DecidableEq Attr] in
@[simp] theorem extension_idiff (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.extension (.idiff s t) = F.extension s := rfl

omit [DecidableEq Obj] in
@[simp] theorem intension_idiff (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.intension (.idiff s t) = F.intension s \ F.intension t := rfl

/-- Extensional inheritance is subset between extensions. -/
def ExtensionalInherits (F : Frame Atom Obj Attr) (s p : Term Atom) : Prop :=
  F.extension s ⊆ F.extension p

/-- Intensional inheritance is reversed subset between intensions. -/
def IntensionalInherits (F : Frame Atom Obj Attr) (s p : Term Atom) : Prop :=
  F.intension p ⊆ F.intension s

/-- Full NARS inheritance requires both channels. -/
def Inherits (F : Frame Atom Obj Attr) (s p : Term Atom) : Prop :=
  F.ExtensionalInherits s p ∧ F.IntensionalInherits s p

instance instDecidableExtensionalInherits
    (F : Frame Atom Obj Attr) (s p : Term Atom) :
    Decidable (F.ExtensionalInherits s p) := by
  unfold ExtensionalInherits
  infer_instance

instance instDecidableIntensionalInherits
    (F : Frame Atom Obj Attr) (s p : Term Atom) :
    Decidable (F.IntensionalInherits s p) := by
  unfold IntensionalInherits
  infer_instance

instance instDecidableInherits
    (F : Frame Atom Obj Attr) (s p : Term Atom) :
    Decidable (F.Inherits s p) := by
  unfold Inherits
  infer_instance

@[simp] theorem inherits_iff (F : Frame Atom Obj Attr) (s p : Term Atom) :
    F.Inherits s p ↔
      F.extension s ⊆ F.extension p ∧ F.intension p ⊆ F.intension s := Iff.rfl

omit [DecidableEq Attr] in
theorem extensionalInherits_refl (F : Frame Atom Obj Attr) (t : Term Atom) :
    F.ExtensionalInherits t t :=
  fun _ hx => hx

omit [DecidableEq Obj] in
theorem intensionalInherits_refl (F : Frame Atom Obj Attr) (t : Term Atom) :
    F.IntensionalInherits t t :=
  fun _ hx => hx

theorem inherits_refl (F : Frame Atom Obj Attr) (t : Term Atom) :
    F.Inherits t t :=
  ⟨F.extensionalInherits_refl t, F.intensionalInherits_refl t⟩

omit [DecidableEq Attr] in
theorem extensionalInherits_trans (F : Frame Atom Obj Attr) {r s t : Term Atom}
    (hrs : F.ExtensionalInherits r s) (hst : F.ExtensionalInherits s t) :
    F.ExtensionalInherits r t :=
  fun _ hx => hst (hrs hx)

omit [DecidableEq Obj] in
theorem intensionalInherits_trans (F : Frame Atom Obj Attr) {r s t : Term Atom}
    (hrs : F.IntensionalInherits r s) (hst : F.IntensionalInherits s t) :
    F.IntensionalInherits r t :=
  fun _ hx => hrs (hst hx)

theorem inherits_trans (F : Frame Atom Obj Attr) {r s t : Term Atom}
    (hrs : F.Inherits r s) (hst : F.Inherits s t) :
    F.Inherits r t :=
  ⟨F.extensionalInherits_trans hrs.1 hst.1, F.intensionalInherits_trans hrs.2 hst.2⟩

/-- The NARS-style dual conjunction term. -/
def inter (s t : Term Atom) : Term Atom := .inter s t

/-- Intensional intersection:
broader extension, more selective shared intension. -/
def iinter (s t : Term Atom) : Term Atom := .iinter s t

/-- Extensional difference:
remove the extension of the second term while keeping the intension of the first. -/
def diff (s t : Term Atom) : Term Atom := .diff s t

/-- Intensional difference:
remove the intension of the second term while keeping the extension of the first. -/
def idiff (s t : Term Atom) : Term Atom := .idiff s t

theorem inter_inherits_left (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.Inherits (inter s t) s := by
  constructor
  · intro x hx
    exact (Finset.mem_inter.mp hx).1
  · intro a ha
    exact Finset.mem_union.mpr (Or.inl ha)

theorem inter_inherits_right (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.Inherits (inter s t) t := by
  constructor
  · intro x hx
    exact (Finset.mem_inter.mp hx).2
  · intro a ha
    exact Finset.mem_union.mpr (Or.inr ha)

theorem inherits_inter_of_inherits
    (F : Frame Atom Obj Attr) {s p q : Term Atom}
    (hsp : F.Inherits s p) (hsq : F.Inherits s q) :
    F.Inherits s (inter p q) := by
  constructor
  · intro x hx
    exact Finset.mem_inter.mpr ⟨hsp.1 hx, hsq.1 hx⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hsp.2 ha
    · exact hsq.2 ha

theorem inherits_iinter_left (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.Inherits s (iinter s t) := by
  constructor
  · intro x hx
    exact Finset.mem_union.mpr (Or.inl hx)
  · intro a ha
    exact (Finset.mem_inter.mp ha).1

theorem inherits_iinter_right (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.Inherits t (iinter s t) := by
  constructor
  · intro x hx
    exact Finset.mem_union.mpr (Or.inr hx)
  · intro a ha
    exact (Finset.mem_inter.mp ha).2

theorem iinter_inherits_of_inherits
    (F : Frame Atom Obj Attr) {s t p : Term Atom}
    (hsp : F.Inherits s p) (htp : F.Inherits t p) :
    F.Inherits (iinter s t) p := by
  constructor
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hsp.1 hx
    · exact htp.1 hx
  · intro a ha
    exact Finset.mem_inter.mpr ⟨hsp.2 ha, htp.2 ha⟩

theorem diff_inherits_left (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.Inherits (diff s t) s := by
  constructor
  · intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  · intro a ha
    simpa [diff]

theorem inherits_idiff_left (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.Inherits s (idiff s t) := by
  constructor
  · intro x hx
    simpa [idiff]
  · intro a ha
    exact (Finset.mem_sdiff.mp ha).1

theorem diff_inherits_diff_of_inherits
    (F : Frame Atom Obj Attr) {s p m : Term Atom}
    (hsp : F.Inherits s p) :
    F.Inherits (diff s m) (diff p m) := by
  constructor
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨hsp.1 (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
  · intro a ha
    exact hsp.2 ha

theorem diff_antitone_right_of_inherits
    (F : Frame Atom Obj Attr) {s p m : Term Atom}
    (hsp : F.Inherits s p) :
    F.Inherits (diff m p) (diff m s) := by
  constructor
  · intro x hx
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, ?_⟩
    intro hxs
    exact (Finset.mem_sdiff.mp hx).2 (hsp.1 hxs)
  · intro a ha
    exact ha

theorem idiff_inherits_idiff_of_inherits
    (F : Frame Atom Obj Attr) {s p m : Term Atom}
    (hsp : F.Inherits s p) :
    F.Inherits (idiff s m) (idiff p m) := by
  constructor
  · intro x hx
    exact hsp.1 hx
  · intro a ha
    refine Finset.mem_sdiff.mpr ⟨hsp.2 (Finset.mem_sdiff.mp ha).1, ?_⟩
    exact (Finset.mem_sdiff.mp ha).2

theorem idiff_antitone_right_of_inherits
    (F : Frame Atom Obj Attr) {s p m : Term Atom}
    (hsp : F.Inherits s p) :
    F.Inherits (idiff m p) (idiff m s) := by
  constructor
  · intro x hx
    exact hx
  · intro a ha
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp ha).1, ?_⟩
    intro hap
    exact (Finset.mem_sdiff.mp ha).2 (hsp.2 hap)

/-- Positive extensional witnesses for `S -> P`: members shared by both
extensions. -/
def positiveExtensionalWitnesses
    (F : Frame Atom Obj Attr) (s p : Term Atom) : Finset Obj :=
  F.extension s ∩ F.extension p

/-- Negative extensional witnesses for `S -> P`: members of `S` outside `P`. -/
def negativeExtensionalWitnesses
    (F : Frame Atom Obj Attr) (s p : Term Atom) : Finset Obj :=
  F.extension s \ F.extension p

/-- Positive intensional witnesses for `S -> P`: properties of `P` already
present in `S`. -/
def positiveIntensionalWitnesses
    (F : Frame Atom Obj Attr) (s p : Term Atom) : Finset Attr :=
  F.intension p ∩ F.intension s

/-- Negative intensional witnesses for `S -> P`: properties of `P` missing
from `S`. -/
def negativeIntensionalWitnesses
    (F : Frame Atom Obj Attr) (s p : Term Atom) : Finset Attr :=
  F.intension p \ F.intension s

/-- Unified evidence for a NARS inheritance statement. -/
def inheritanceEvidence
    (F : Frame Atom Obj Attr) (s p : Term Atom) : BinaryEvidence where
  pos :=
    (((F.positiveExtensionalWitnesses s p).card
        + (F.positiveIntensionalWitnesses s p).card : ℕ) : ℝ≥0∞)
  neg :=
    (((F.negativeExtensionalWitnesses s p).card
        + (F.negativeIntensionalWitnesses s p).card : ℕ) : ℝ≥0∞)

/-- NARS truth-value view induced by the unified evidence. -/
noncomputable def truthValue
    (F : Frame Atom Obj Attr) (s p : Term Atom) : TV :=
  Mettapedia.PLN.Comparisons.NARS.NARSEvidenceBridge.BinaryEvidence.toNARSTV
    (F.inheritanceEvidence s p)

omit [DecidableEq Attr] in
theorem negativeExtensionalWitnesses_eq_empty_of_extensionalInherits
    (F : Frame Atom Obj Attr) {s p : Term Atom}
    (hsp : F.ExtensionalInherits s p) :
    F.negativeExtensionalWitnesses s p = ∅ := by
  unfold negativeExtensionalWitnesses
  exact Finset.sdiff_eq_empty_iff_subset.mpr hsp

omit [DecidableEq Obj] in
theorem negativeIntensionalWitnesses_eq_empty_of_intensionalInherits
    (F : Frame Atom Obj Attr) {s p : Term Atom}
    (hsp : F.IntensionalInherits s p) :
    F.negativeIntensionalWitnesses s p = ∅ := by
  unfold negativeIntensionalWitnesses
  exact Finset.sdiff_eq_empty_iff_subset.mpr hsp

theorem inheritanceEvidence_neg_eq_zero_of_inherits
    (F : Frame Atom Obj Attr) {s p : Term Atom}
    (hsp : F.Inherits s p) :
    (F.inheritanceEvidence s p).neg = 0 := by
  have hExt :
      F.negativeExtensionalWitnesses s p = ∅ :=
    F.negativeExtensionalWitnesses_eq_empty_of_extensionalInherits hsp.1
  have hInt :
      F.negativeIntensionalWitnesses s p = ∅ :=
    F.negativeIntensionalWitnesses_eq_empty_of_intensionalInherits hsp.2
  simp [inheritanceEvidence, hExt, hInt]

theorem inheritanceEvidence_pos_eq_two_of_inter_self
    (F : Frame Atom Obj Attr) (a : Atom)
    (hExtSingleton : (F.atomExtension a).card = 1)
    (hIntSingleton : (F.atomIntension a).card = 1) :
    (F.inheritanceEvidence (.atom a) (.atom a)).pos = 2 := by
  simp [inheritanceEvidence, positiveExtensionalWitnesses, positiveIntensionalWitnesses,
    Finset.inter_self]
  rw [hExtSingleton, hIntSingleton]
  norm_num

/-- The finite NARS semantics factors through the abstract dual-inheritance
core by coercing finite extents/intents to sets. -/
def interpretation (F : Frame Atom Obj Attr) :
    AbstractInheritance.Interpretation (Term Atom) Obj Attr where
  meaning t :=
    { extent := F.extension t
      intent := F.intension t }

theorem abstract_extensionalInherits_iff
    (F : Frame Atom Obj Attr) (s p : Term Atom) :
    (F.interpretation).ExtensionalInherits s p ↔ F.ExtensionalInherits s p := Iff.rfl

theorem abstract_intensionalInherits_iff
    (F : Frame Atom Obj Attr) (s p : Term Atom) :
    (F.interpretation).IntensionalInherits s p ↔ F.IntensionalInherits s p := Iff.rfl

theorem abstract_inherits_iff
    (F : Frame Atom Obj Attr) (s p : Term Atom) :
    (F.interpretation).Inherits s p ↔ F.Inherits s p := Iff.rfl

end Frame

namespace Examples

inductive ConceptAtom where
  | bird
  | penguin
  | flyer
  deriving DecidableEq, Repr

inductive Creature where
  | tweety
  | pingu
  deriving DecidableEq, Repr

inductive Feature where
  | winged
  | aquatic
  | flies
  deriving DecidableEq, Repr

def ontologyFrame : Frame ConceptAtom Creature Feature where
  atomExtension
    | .bird => {Creature.tweety, Creature.pingu}
    | .penguin => {Creature.pingu}
    | .flyer => {Creature.tweety}
  atomIntension
    | .bird => {Feature.winged}
    | .penguin => {Feature.winged, Feature.aquatic}
    | .flyer => {Feature.flies}

def bird : Term ConceptAtom := .atom .bird
def penguin : Term ConceptAtom := .atom .penguin
def flyer : Term ConceptAtom := .atom .flyer

theorem penguin_inherits_bird :
    ontologyFrame.Inherits penguin bird := by
  decide

theorem bird_does_not_inherit_flyer :
    ¬ ontologyFrame.Inherits bird flyer := by
  decide

theorem penguin_inheritance_negative_evidence_zero :
    (ontologyFrame.inheritanceEvidence penguin bird).neg = 0 :=
  ontologyFrame.inheritanceEvidence_neg_eq_zero_of_inherits penguin_inherits_bird

theorem bird_to_flyer_negative_evidence_is_two :
    (ontologyFrame.inheritanceEvidence bird flyer).neg = 2 := by
  have hExt :
      ontologyFrame.negativeExtensionalWitnesses bird flyer = {Creature.pingu} := by
    decide
  have hInt :
      ontologyFrame.negativeIntensionalWitnesses bird flyer = {Feature.flies} := by
    decide
  simp [Frame.inheritanceEvidence, hExt, hInt]

theorem bird_inherits_iinter_bird_flyer :
    ontologyFrame.Inherits bird (Frame.iinter bird flyer) := by
  exact ontologyFrame.inherits_iinter_left bird flyer

theorem not_iinter_bird_flyer_inherits_bird :
    ¬ ontologyFrame.Inherits (Frame.iinter bird flyer) bird := by
  decide

theorem bird_minus_penguin_inherits_bird :
    ontologyFrame.Inherits (Frame.diff bird penguin) bird := by
  exact ontologyFrame.diff_inherits_left bird penguin

theorem bird_inherits_bird_idiff_penguin :
    ontologyFrame.Inherits bird (Frame.idiff bird penguin) := by
  exact ontologyFrame.inherits_idiff_left bird penguin

theorem bird_does_not_inherit_bird_minus_penguin :
    ¬ ontologyFrame.Inherits bird (Frame.diff bird penguin) := by
  decide

end Examples

end Mettapedia.PLN.Comparisons.NARS.NARSInheritance
