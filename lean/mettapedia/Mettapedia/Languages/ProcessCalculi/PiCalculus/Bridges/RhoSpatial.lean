import Mettapedia.GSLT.Logic.SeparationTransport
import Mettapedia.OSLF.Bridges.GSLT.RhoSeparation
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpoint
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary

/-!
# Spatial observations of the maintained pi-to-rho compiler

A flat source network consists of input and output occurrences. The existing
compiler maps each to one canonical rho component, retaining multiplicity.
Thus every partition of the compiled component bag lifts to a source
partition, and separating conjunction agrees with the equation-relative
OSLF cut of the actual compiled process.

This comparison does not preserve every magic wand: an arbitrary rho frame
can contain a dropped name, which is outside the compiler's communication
atoms. Spatial preservation also supplies no transition-locality theorem;
operational framing is established separately with complete read footprints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoSpatial

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.GSLT.RhoBagReactiveSystem
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.OSLF.StructuralModal.SeparatingConjunction

/-- Source occurrences whose continuations remain in the maintained fragment. -/
abbrev Atom := {process : Process // RhoEndpoint.Atom process}

/-- One occurrence's image under the existing compiler and canonicalizer. -/
def atomImage (namespaceName valueName : String) (atom : Atom) : Pattern :=
  canonicalize (encode atom.1 namespaceName valueName)

/-- The resource map is a map of occurrences, not a map identifying equal
occurrences or a separate operational compiler. -/
def resourceMap (namespaceName valueName : String) :
    Hom (Multiset Atom) (Multiset Pattern) := bagMap (atomImage namespaceName valueName)

theorem atom_components (atom : Atom) (namespaceName valueName : String) :
    components (encode atom.1 namespaceName valueName) =
      {atomImage namespaceName valueName atom} := by
  obtain ⟨process, shape⟩ := atom
  cases process with
  | input channel binder body =>
      simpa [atomImage, encode, rhoInput, piNameToRhoName, canonicalize_input] using
        components_input (.fvar channel)
          (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 binder
            (encode body namespaceName valueName))
  | output channel datum =>
      simpa [atomImage, encode, rhoOutput, rhoDrop, piNameToRhoName, canonicalize_output] using
        components_output (.fvar channel) (.apply "PDrop" [.fvar datum])
  | nil | par | nu | replicate => exact False.elim shape

/-- The canonical resources of the actual compiled bag are exactly the
images of its source occurrences, including repeated occurrences. -/
theorem compiledBag_components (atoms : List Atom) (namespaceName valueName : String) :
    components (RhoEndpoint.networkPattern (atoms.map Subtype.val) namespaceName valueName) =
        resourceMap namespaceName valueName (atoms : Multiset Atom) := by
  rw [RhoEndpoint.networkPattern, List.map_map, components_parallel, List.map_map]
  change (atoms.map (fun atom => components (encode atom.1 namespaceName valueName))).sum =
    (atoms : Multiset Atom).map (atomImage namespaceName valueName)
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      rw [List.map_cons, List.sum_cons, atom_components, ih]
      change {atomImage namespaceName valueName atom} +
        (rest : Multiset Atom).map (atomImage namespaceName valueName) =
          (atom ::ₘ (rest : Multiset Atom)).map (atomImage namespaceName valueName)
      rw [Multiset.map_cons, Multiset.singleton_add]

/-- Each top-level source occurrence contributes exactly one component.
Equal encoded components remain separate occurrences. -/
theorem compiledBag_card (atoms : List Atom) (namespaceName valueName : String) :
    (components (RhoEndpoint.networkPattern (atoms.map Subtype.val)
      namespaceName valueName)).card =
        atoms.length := by
  rw [compiledBag_components]
  exact (Multiset.card_map _ _).trans (Multiset.coe_card _)

theorem compiledBag_pure (atoms : List Atom) (namespaceName valueName : String) :
    HashSetFree (RhoEndpoint.networkPattern (atoms.map Subtype.val)
      namespaceName valueName) := by
  unfold RhoEndpoint.networkPattern
  rw [List.map_map]
  change HashSetFreeList (atoms.map (fun atom => encode atom.1 namespaceName valueName))
  induction atoms with
  | nil => trivial
  | cons atom rest ih =>
      exact ⟨encode_hashSetFree (RhoEndpoint.atom_restrictionFree atom.2)
        namespaceName valueName, ih⟩

theorem mapped_atoms_flat (atoms : List Atom) : RhoEndpoint.Flat (atoms.map Subtype.val) := by
  intro process member
  obtain ⟨atom, _, rfl⟩ := List.mem_map.mp member
  exact atom.2

/-- All atom-sensitive separating predicates transport along the compiler's
occurrence map; injectivity of the atom encoding is unnecessary. -/
theorem pull_sepConj (namespaceName valueName : String) (P Q : Multiset Pattern → Prop) :
    (resourceMap namespaceName valueName).pull (sepConj P Q) =
      sepConj ((resourceMap namespaceName valueName).pull P)
        ((resourceMap namespaceName valueName).pull Q) :=
  bagMap_pull_sepConj (atomImage namespaceName valueName) P Q

/-- Spatial reasoning about the source occurrences agrees with the existing
OSLF cut of their actual rho compilation, modulo rho's equations. -/
theorem compiledBag_cut_iff (atoms : List Atom) (namespaceName valueName : String)
    (P Q : Multiset Pattern → Prop) :
    SepConj Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence .hashBag
      (fun term => P (components term))
      (fun term => Q (components term))
      (RhoEndpoint.networkPattern (atoms.map Subtype.val) namespaceName valueName) ↔
    sepConj ((resourceMap namespaceName valueName).pull P)
      ((resourceMap namespaceName valueName).pull Q) (atoms : Multiset Atom) := by
  rw [Mettapedia.OSLF.Bridges.GSLT.RhoSeparation.sepConj_iff_components P Q
    (compiledBag_pure atoms namespaceName valueName),
    compiledBag_components]
  exact congrFun (pull_sepConj namespaceName valueName P Q) (atoms : Multiset Atom) |>.to_iff

/-- The spatial comparison applies to compilation of the existing source
parallel constructor, using the checked network adequacy rather than another
encoding of parallel composition. -/
theorem encode_assemble_cut_iff (atoms : List Atom) (namespaceName valueName : String)
    (P Q : Multiset Pattern → Prop) :
    SepConj Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence .hashBag
      (fun term => P (components term)) (fun term => Q (components term))
      (encode (RhoEndpoint.assemble (atoms.map Subtype.val)) namespaceName valueName) ↔
    sepConj ((resourceMap namespaceName valueName).pull P)
      ((resourceMap namespaceName valueName).pull Q) (atoms : Multiset Atom) := by
  rw [RhoEndpoint.encode_assemble (mapped_atoms_flat atoms)]
  exact compiledBag_cut_iff atoms namespaceName valueName P Q

theorem pull_emp (namespaceName valueName : String) :
    (resourceMap namespaceName valueName).pull emp = emp :=
  bagMap_pull_emp (atomImage namespaceName valueName)

/-- Canonicalization never turns a communication atom into a dropped name. -/
theorem atomImage_ne_drop (atom : Atom) (namespaceName valueName ambient : String) :
    atomImage namespaceName valueName atom ≠ .apply "PDrop" [.fvar ambient] := by
  obtain ⟨process, shape⟩ := atom
  cases process with
  | input => simp [atomImage, encode, rhoInput, canonicalize_input]
  | output => simp [atomImage, encode, rhoOutput, canonicalize_output]
  | nil | par | nu | replicate => exact False.elim shape

/-- Rho admits compatible extensions outside this compiler's component image. -/
theorem not_liftsExtensions (namespaceName valueName : String) :
    ¬ (resourceMap namespaceName valueName).LiftsExtensions := by
  intro lifts
  obtain ⟨atom, image⟩ := (bagMap_liftsExtensions_iff_surjective
    (atomImage namespaceName valueName)).mp lifts (.apply "PDrop" [.fvar "ambient"])
  exact atomImage_ne_drop atom namespaceName valueName "ambient" image

/-- Consequently, preservation of every magic wand would be false. -/
theorem not_preserves_all_wands (namespaceName valueName : String) :
    ¬ (∀ Q R : Multiset Pattern → Prop,
      (resourceMap namespaceName valueName).pull (wand Q R) =
        wand ((resourceMap namespaceName valueName).pull Q)
          ((resourceMap namespaceName valueName).pull R)) := by
  intro preserves
  exact not_liftsExtensions namespaceName valueName
    ((resourceMap namespaceName valueName).liftsExtensions_iff_pull_wand.mpr preserves)

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoSpatial
