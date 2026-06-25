import Mettapedia.PLN.Comparisons.NARS.NARSInheritance

/-!
# Witness Geometry for Abstract Inheritance

This module adds a shared witness surface to `AbstractInheritance`:

- positive/negative extensional witnesses
- positive/negative intensional witnesses
- finite witness realizations and induced `BinaryEvidence`

It then proves that the concrete NARS witness-count semantics is exactly the
finite evidence semantics of the abstract interpretation.
-/

namespace Mettapedia.KR.ConceptGeometry.AbstractInheritance

open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Comparisons.NARS.NARSInheritance
open scoped ENNReal

universe u v w

namespace DualConcept

variable {Obj : Type u} {Attr : Type v}

@[ext] theorem ext {A B : DualConcept Obj Attr}
    (hExtent : A.extent = B.extent) (hIntent : A.intent = B.intent) : A = B := by
  cases A
  cases B
  simp_all

/-- Positive extensional witnesses: objects in both extents. -/
def positiveExtensionalWitnesses (A B : DualConcept Obj Attr) : Set Obj :=
  A.extent ∩ B.extent

/-- Negative extensional witnesses: objects in the antecedent extent but not
in the consequent extent. -/
def negativeExtensionalWitnesses (A B : DualConcept Obj Attr) : Set Obj :=
  A.extent \ B.extent

/-- Positive intensional witnesses: consequent intent already present in the
antecedent intent. -/
def positiveIntensionalWitnesses (A B : DualConcept Obj Attr) : Set Attr :=
  B.intent ∩ A.intent

/-- Negative intensional witnesses: consequent intent missing from the
antecedent intent. -/
def negativeIntensionalWitnesses (A B : DualConcept Obj Attr) : Set Attr :=
  B.intent \ A.intent

theorem negativeExtensionalWitnesses_eq_empty_of_extensionalInherits
    {A B : DualConcept Obj Attr} (hAB : ExtensionalInherits A B) :
    negativeExtensionalWitnesses A B = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hx.2 (hAB hx.1)

theorem negativeIntensionalWitnesses_eq_empty_of_intensionalInherits
    {A B : DualConcept Obj Attr} (hAB : IntensionalInherits A B) :
    negativeIntensionalWitnesses A B = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact ha.2 (hAB ha.1)

theorem negativeWitnesses_eq_empty_of_inherits
    {A B : DualConcept Obj Attr} (hAB : Inherits A B) :
    negativeExtensionalWitnesses A B = ∅ ∧
      negativeIntensionalWitnesses A B = ∅ := by
  exact ⟨negativeExtensionalWitnesses_eq_empty_of_extensionalInherits hAB.1,
    negativeIntensionalWitnesses_eq_empty_of_intensionalInherits hAB.2⟩

section Finite

variable [Fintype Obj] [DecidableEq Obj] [Fintype Attr] [DecidableEq Attr]

/-- Finite realization of an extent. -/
noncomputable def finiteExtent (A : DualConcept Obj Attr) : Finset Obj := by
  classical
  exact Finset.univ.filter fun x => x ∈ A.extent

/-- Finite realization of an intent. -/
noncomputable def finiteIntent (A : DualConcept Obj Attr) : Finset Attr := by
  classical
  exact Finset.univ.filter fun a => a ∈ A.intent

omit [DecidableEq Obj] [Fintype Attr] [DecidableEq Attr] in
@[simp] theorem mem_finiteExtent_iff (A : DualConcept Obj Attr) (x : Obj) :
    x ∈ finiteExtent A ↔ x ∈ A.extent := by
  classical
  simp [finiteExtent]

omit [Fintype Obj] [DecidableEq Obj] [DecidableEq Attr] in
@[simp] theorem mem_finiteIntent_iff (A : DualConcept Obj Attr) (a : Attr) :
    a ∈ finiteIntent A ↔ a ∈ A.intent := by
  classical
  simp [finiteIntent]

/-- Finite positive extensional witnesses. -/
noncomputable def finitePositiveExtensionalWitnesses
    (A B : DualConcept Obj Attr) : Finset Obj :=
  finiteExtent A ∩ finiteExtent B

/-- Finite negative extensional witnesses. -/
noncomputable def finiteNegativeExtensionalWitnesses
    (A B : DualConcept Obj Attr) : Finset Obj :=
  finiteExtent A \ finiteExtent B

/-- Finite positive intensional witnesses. -/
noncomputable def finitePositiveIntensionalWitnesses
    (A B : DualConcept Obj Attr) : Finset Attr :=
  finiteIntent B ∩ finiteIntent A

/-- Finite negative intensional witnesses. -/
noncomputable def finiteNegativeIntensionalWitnesses
    (A B : DualConcept Obj Attr) : Finset Attr :=
  finiteIntent B \ finiteIntent A

omit [Fintype Attr] [DecidableEq Attr] in
@[simp] theorem mem_finitePositiveExtensionalWitnesses_iff
    (A B : DualConcept Obj Attr) (x : Obj) :
    x ∈ finitePositiveExtensionalWitnesses A B ↔
      x ∈ positiveExtensionalWitnesses A B := by
  classical
  simp [finitePositiveExtensionalWitnesses, positiveExtensionalWitnesses]

omit [Fintype Attr] [DecidableEq Attr] in
@[simp] theorem mem_finiteNegativeExtensionalWitnesses_iff
    (A B : DualConcept Obj Attr) (x : Obj) :
    x ∈ finiteNegativeExtensionalWitnesses A B ↔
      x ∈ negativeExtensionalWitnesses A B := by
  classical
  simp [finiteNegativeExtensionalWitnesses, negativeExtensionalWitnesses]

omit [Fintype Obj] [DecidableEq Obj] in
@[simp] theorem mem_finitePositiveIntensionalWitnesses_iff
    (A B : DualConcept Obj Attr) (a : Attr) :
    a ∈ finitePositiveIntensionalWitnesses A B ↔
      a ∈ positiveIntensionalWitnesses A B := by
  classical
  simp [finitePositiveIntensionalWitnesses, positiveIntensionalWitnesses]

omit [Fintype Obj] [DecidableEq Obj] in
@[simp] theorem mem_finiteNegativeIntensionalWitnesses_iff
    (A B : DualConcept Obj Attr) (a : Attr) :
    a ∈ finiteNegativeIntensionalWitnesses A B ↔
      a ∈ negativeIntensionalWitnesses A B := by
  classical
  simp [finiteNegativeIntensionalWitnesses, negativeIntensionalWitnesses]

/-- Finite witness counts lifted into the shared `BinaryEvidence` carrier. -/
noncomputable def finiteInheritanceEvidence
    (A B : DualConcept Obj Attr) : BinaryEvidence where
  pos :=
    (((finitePositiveExtensionalWitnesses A B).card
        + (finitePositiveIntensionalWitnesses A B).card : ℕ) : ℝ≥0∞)
  neg :=
    (((finiteNegativeExtensionalWitnesses A B).card
        + (finiteNegativeIntensionalWitnesses A B).card : ℕ) : ℝ≥0∞)

theorem finiteInheritanceEvidence_neg_eq_zero_of_inherits
    {A B : DualConcept Obj Attr} (hAB : Inherits A B) :
    (finiteInheritanceEvidence A B).neg = 0 := by
  have hExt :
      finiteNegativeExtensionalWitnesses A B = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' : x ∈ negativeExtensionalWitnesses A B := by
      simpa using hx
    exact Set.notMem_empty x <|
      (negativeExtensionalWitnesses_eq_empty_of_extensionalInherits hAB.1) ▸ hx'
  have hInt :
      finiteNegativeIntensionalWitnesses A B = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have ha' : a ∈ negativeIntensionalWitnesses A B := by
      simpa using ha
    exact Set.notMem_empty a <|
      (negativeIntensionalWitnesses_eq_empty_of_intensionalInherits hAB.2) ▸ ha'
  simp [finiteInheritanceEvidence, hExt, hInt]

end Finite

end DualConcept

namespace Interpretation

variable {Carrier : Type u} {Obj : Type v} {Attr : Type w}
variable [Fintype Obj] [DecidableEq Obj] [Fintype Attr] [DecidableEq Attr]

/-- Finite witness-evidence view of an abstract interpretation. -/
noncomputable def finiteInheritanceEvidence
    (I : Interpretation Carrier Obj Attr) (a b : Carrier) : BinaryEvidence :=
  DualConcept.finiteInheritanceEvidence (I.meaning a) (I.meaning b)

theorem finiteInheritanceEvidence_neg_eq_zero_of_inherits
    (I : Interpretation Carrier Obj Attr) {a b : Carrier}
    (hAB : I.Inherits a b) :
    (I.finiteInheritanceEvidence a b).neg = 0 := by
  exact DualConcept.finiteInheritanceEvidence_neg_eq_zero_of_inherits hAB

/-- Build a finite NARS frame from an abstract interpretation by taking finite
realizations of extents and intents. -/
noncomputable def toNARSFrame
    (I : Interpretation Carrier Obj Attr) :
    Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame Carrier Obj Attr where
  atomExtension a := DualConcept.finiteExtent (I.meaning a)
  atomIntension a := DualConcept.finiteIntent (I.meaning a)

theorem toNARSFrame_meaning_atom_eq
    (I : Interpretation Carrier Obj Attr) (a : Carrier) :
    (I.toNARSFrame.interpretation).meaning (.atom a) = I.meaning a := by
  apply DualConcept.ext
  · ext x
    simp [Interpretation.toNARSFrame, Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.interpretation,
      DualConcept.finiteExtent]
  · ext t
    simp [Interpretation.toNARSFrame, Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.interpretation,
      DualConcept.finiteIntent]

theorem toNARSFrame_extensionalInherits_atom_iff
    (I : Interpretation Carrier Obj Attr) (a b : Carrier) :
    I.toNARSFrame.ExtensionalInherits (.atom a) (.atom b) ↔ I.ExtensionalInherits a b := by
  rw [← Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.abstract_extensionalInherits_iff (F := I.toNARSFrame)
      (s := .atom a) (p := .atom b)]
  simp [Interpretation.ExtensionalInherits, toNARSFrame_meaning_atom_eq]

theorem toNARSFrame_intensionalInherits_atom_iff
    (I : Interpretation Carrier Obj Attr) (a b : Carrier) :
    I.toNARSFrame.IntensionalInherits (.atom a) (.atom b) ↔ I.IntensionalInherits a b := by
  rw [← Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.abstract_intensionalInherits_iff (F := I.toNARSFrame)
      (s := .atom a) (p := .atom b)]
  simp [Interpretation.IntensionalInherits, toNARSFrame_meaning_atom_eq]

theorem toNARSFrame_inherits_atom_iff
    (I : Interpretation Carrier Obj Attr) (a b : Carrier) :
    I.toNARSFrame.Inherits (.atom a) (.atom b) ↔ I.Inherits a b := by
  rw [← Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.abstract_inherits_iff (F := I.toNARSFrame)
      (s := .atom a) (p := .atom b)]
  simp [Interpretation.Inherits, toNARSFrame_meaning_atom_eq]

theorem toNARSFrame_inheritanceEvidence_atom_eq_finiteInheritanceEvidence
    (I : Interpretation Carrier Obj Attr) (a b : Carrier) :
    I.toNARSFrame.inheritanceEvidence (.atom a) (.atom b) =
      I.finiteInheritanceEvidence a b := by
  rfl

end Interpretation

namespace Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame

variable {Atom : Type u} {Obj : Type v} {Attr : Type w}
variable [DecidableEq Obj] [DecidableEq Attr]
variable [Fintype Obj] [Fintype Attr]

omit [Fintype Attr] in
@[simp] theorem positiveExtensionalWitnesses_eq_finite
    (F : Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame Atom Obj Attr) (s p : Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Term Atom) :
    F.positiveExtensionalWitnesses s p =
      DualConcept.finitePositiveExtensionalWitnesses
        ((F.interpretation).meaning s) ((F.interpretation).meaning p) := by
  ext x
  simp [Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.positiveExtensionalWitnesses,
    DualConcept.finitePositiveExtensionalWitnesses,
    Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.interpretation]

omit [Fintype Attr] in
@[simp] theorem negativeExtensionalWitnesses_eq_finite
    (F : Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame Atom Obj Attr) (s p : Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Term Atom) :
    F.negativeExtensionalWitnesses s p =
      DualConcept.finiteNegativeExtensionalWitnesses
        ((F.interpretation).meaning s) ((F.interpretation).meaning p) := by
  ext x
  simp [Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.negativeExtensionalWitnesses,
    DualConcept.finiteNegativeExtensionalWitnesses,
    Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.interpretation]

omit [Fintype Obj] in
@[simp] theorem positiveIntensionalWitnesses_eq_finite
    (F : Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame Atom Obj Attr) (s p : Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Term Atom) :
    F.positiveIntensionalWitnesses s p =
      DualConcept.finitePositiveIntensionalWitnesses
        ((F.interpretation).meaning s) ((F.interpretation).meaning p) := by
  ext a
  simp [Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.positiveIntensionalWitnesses,
    DualConcept.finitePositiveIntensionalWitnesses,
    Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.interpretation]

omit [Fintype Obj] in
@[simp] theorem negativeIntensionalWitnesses_eq_finite
    (F : Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame Atom Obj Attr) (s p : Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Term Atom) :
    F.negativeIntensionalWitnesses s p =
      DualConcept.finiteNegativeIntensionalWitnesses
        ((F.interpretation).meaning s) ((F.interpretation).meaning p) := by
  ext a
  simp [Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.negativeIntensionalWitnesses,
    DualConcept.finiteNegativeIntensionalWitnesses,
    Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.interpretation]

theorem inheritanceEvidence_eq_finiteInheritanceEvidence
    (F : Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame Atom Obj Attr) (s p : Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Term Atom) :
    F.inheritanceEvidence s p =
      DualConcept.finiteInheritanceEvidence
        ((F.interpretation).meaning s) ((F.interpretation).meaning p) := by
  simp [Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame.inheritanceEvidence,
    DualConcept.finiteInheritanceEvidence]

end Mettapedia.PLN.Comparisons.NARS.NARSInheritance.Frame

end Mettapedia.KR.ConceptGeometry.AbstractInheritance
