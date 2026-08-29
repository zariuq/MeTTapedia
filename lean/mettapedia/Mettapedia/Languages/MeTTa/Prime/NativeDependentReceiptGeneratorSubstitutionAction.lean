import Mettapedia.TypeTheory.FreeWhiskeredCellTransportComposition
import Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptSubstitutionTransport
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RetainedStructuralSubstitutionCoherence

/-!
# Functorial substitution actions on dependent receipt generators

Root substitution and complete free-cell transport compose only part of the
native-fusion square.  The authored comparison-generator family must also
provide a substitution action whose identity and composition laws retain its
own proof-relevant evidence.

This module isolates that additional capability.  It is displayed over the
already-defined receipt substitution: the generator family does not redefine
terms, conversion receipts, or their substitution.  A constant tagged family
provides a positive action, while an arity-stamping family provides maps for
every substitution but refutes composition.  Thus existence of all local maps
still does not license a fused direct kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeDependentReceiptGeneratorSubstitutionAction

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.FreeWhiskeredCell
open Mettapedia.TypeTheory.JudgmentalEquality
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptComputad
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptSubstitutionTransport
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.ProofRelevantStructuralComputation

universe uEvidence uGenerator

/-- An authored comparison-generator family over every raw context arity. -/
abbrev ReceiptGeneratorFamily
    (Head : Type)
    (computation : ProofRelevantRootComputation.{uEvidence} Head)
    (headEq : Head → Head → Prop) :=
  (n : Nat) → {left right : Tm Head n} →
    StructuralConversionReceipt computation headEq left right →
    StructuralConversionReceipt computation headEq left right →
      Type uGenerator

/-- Local generator transport is available for every simultaneous
substitution.  No identity or composition law is implied by this data. -/
structure SubstitutionMap
    {Head : Type}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    (Generator : ReceiptGeneratorFamily Head computation headEq) where
  map : ∀ {n m : Nat} (substitution : Sub Head n m),
    ReceiptGeneratorNaturality substitution (Generator n) (Generator m)

namespace SubstitutionMap

/-- A generator substitution map is functorial when identity acts trivially
and sequential actions agree with the direct action of the composite
substitution.  `HEq` retains the endpoint transports supplied by term and
receipt substitution laws. -/
structure Functorial
    {Head : Type}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    {Generator : ReceiptGeneratorFamily Head computation headEq}
    (action : SubstitutionMap Generator) : Prop where
  map_ids : ∀ {n : Nat} {left right : Tm Head n}
      {first second : StructuralConversionReceipt computation headEq left right}
      (evidence : Generator n first second),
    HEq ((action.map (ids : Sub Head n n)).onGenerator evidence) evidence
  map_comp : ∀ {n m k : Nat}
      (later : Sub Head m k) (earlier : Sub Head n m)
      {left right : Tm Head n}
      {first second : StructuralConversionReceipt computation headEq left right}
      (evidence : Generator n first second),
    HEq
      ((action.map later).onGenerator
        ((action.map earlier).onGenerator evidence))
      ((action.map (fun index => subst later (earlier index))).onGenerator
        evidence)

end SubstitutionMap

/-! ## Canonical complete-cell composition -/

/-- Any pair of local generator maps composes over the complete free cell by
the canonical composite base and generator maps.  A `Functorial` witness is
needed only to identify this canonical composite with a separately supplied
direct substitution action. -/
theorem substituteCell_canonical_comp
    {Head : Type} {n m k : Nat}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    {Generator : ReceiptGeneratorFamily Head computation headEq}
    (action : SubstitutionMap Generator)
    (later : Sub Head m k) (earlier : Sub Head n m)
    {left right : Tm Head n}
    {first second : StructuralConversionReceipt computation headEq left right}
    (cell : Cell (receiptBase computation headEq n)
      (Generator n) first second) :
    mapCell (receiptSubstitutionBaseMap later) (action.map later)
        (mapCell (receiptSubstitutionBaseMap earlier) (action.map earlier)
          cell) =
      mapCell
        (BaseMap.comp (receiptSubstitutionBaseMap earlier)
          (receiptSubstitutionBaseMap later))
        (GeneratorMap.comp (action.map earlier) (action.map later)) cell :=
  mapCell_comp _ _ cell

/-! ## A fully functorial positive family -/

namespace Tagged

abbrev Generator
    {Head : Type}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} :
    ReceiptGeneratorFamily Head computation headEq :=
  fun _ {_ _} _ _ => Nat

def action
    {Head : Type}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} :
    SubstitutionMap (Generator (computation := computation) (headEq := headEq))
    where
  map := fun _ => { onGenerator := fun evidence => evidence }

def actionFunctorial
    {Head : Type}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} :
    (action (computation := computation) (headEq := headEq)).Functorial where
  map_ids := by intros; rfl
  map_comp := by intros; rfl

end Tagged

/-! ## Local maps without composition -/

namespace StampCanary

open SubstitutionCoherenceCanary

abbrev Generator : ReceiptGeneratorFamily Unit coherentComputation
    (fun _ _ => True) :=
  fun _ {_ _} _ _ => Nat

/-- Every substitution receives a total local generator map, but every
arity-changing map increments the evidence stamp. -/
def action : SubstitutionMap Generator where
  map := by
    intro n m substitution
    exact
      { onGenerator := fun evidence =>
          if n = m then evidence else evidence + 1 }

def reflexiveReceipt {n : Nat} :
    StructuralConversionReceipt coherentComputation (fun _ _ => True)
      (constantTerm : Tm Unit n) constantTerm :=
  @ConversionEvidence.refl Unit
    (rawStructuralComputation coherentComputation (fun _ _ => True) n)
    () constantTerm

/-- The same arity round trip used at the retained-root boundary. -/
def emptyToOne : Sub Unit 0 1 := fun index => Fin.elim0 index

def oneToEmpty : Sub Unit 1 0 := fun _ => constantTerm

@[simp] theorem sequential_roundTrip_stamp :
    (action.map oneToEmpty).onGenerator
        ((action.map emptyToOne).onGenerator
          (0 : Generator 0 reflexiveReceipt reflexiveReceipt)) = 2 :=
  rfl

@[simp] theorem direct_roundTrip_stamp :
    (action.map (fun index => subst oneToEmpty (emptyToOne index))).onGenerator
        (0 : Generator 0 reflexiveReceipt reflexiveReceipt) = 0 :=
  rfl

/-- Having a generator map for every substitution does not imply that those
maps compose. -/
theorem action_not_functorial : ¬ action.Functorial := by
  intro functorial
  have comparison := functorial.map_comp oneToEmpty emptyToOne
    (0 : Generator 0 reflexiveReceipt reflexiveReceipt)
  have homogeneous :
      (action.map oneToEmpty).onGenerator
          ((action.map emptyToOne).onGenerator
            (0 : Generator 0 reflexiveReceipt reflexiveReceipt)) =
        (action.map
          (fun index => subst oneToEmpty (emptyToOne index))).onGenerator
            (0 : Generator 0 reflexiveReceipt reflexiveReceipt) :=
    eq_of_heq comparison
  simp at homogeneous

end StampCanary

/-- The positive and negative controls isolate the exact generator-side
license required above retained-root substitution coherence. -/
theorem generatorSubstitutionActionBoundary :
    Nonempty
        (Tagged.action
          (computation := SubstitutionCoherenceCanary.coherentComputation)
          (headEq := fun _ _ => True)).Functorial ∧
      ¬ StampCanary.action.Functorial :=
  ⟨⟨Tagged.actionFunctorial⟩, StampCanary.action_not_functorial⟩

/-! ## Axiom audit -/

#print axioms substituteCell_canonical_comp
#print axioms Tagged.actionFunctorial
#print axioms StampCanary.action_not_functorial
#print axioms generatorSubstitutionActionBoundary

end NativeDependentReceiptGeneratorSubstitutionAction
end Mettapedia.Languages.MeTTa.Prime
