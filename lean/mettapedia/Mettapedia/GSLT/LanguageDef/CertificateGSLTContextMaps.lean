import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory

/-!
# Judgment-preserving maps of premise positions

A context map supplies each target premise position with a source position
carrying the same judgment. Its interpretation consists of the actual
assumption nodes, so contraction, weakening and premise permutations retain
their position information. Composition is actual proof substitution.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open _root_.CategoryTheory

/-- Recover the actual premise position at an assumption root. A primitive
rule node has no assumption root, even when its conclusion equals a premise. -/
def OpenDerivation.assumptionPosition
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern} {goal : Pattern} :
    OpenDerivation definition context goal → Option (Fin context.length)
  | .assumption index => some index
  | .byRule _ _ _ => none

theorem OpenDerivation.assumptionPosition_cast
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {first second : Pattern} (same : first = second)
    (proof : OpenDerivation definition context first) :
    (same ▸ proof).assumptionPosition = proof.assumptionPosition := by
  cases same
  rfl

/-- A structural context map, directed like its open-derivation arrow. -/
structure ContextMap (source target : List Pattern) where
  position : Fin target.length → Fin source.length
  judgment : ∀ index, source.get (position index) = target.get index

namespace ContextMap

variable {source middle target : List Pattern}

@[ext] theorem ext {first second : ContextMap source target}
    (same : first.position = second.position) : first = second := by
  cases first
  cases second
  cases same
  rfl

def id (context : List Pattern) : ContextMap context context := ⟨fun index => index, fun _ => rfl⟩

def comp (first : ContextMap source middle) (second : ContextMap middle target) :
    ContextMap source target where
  position index := first.position (second.position index)
  judgment index := (first.judgment (second.position index)).trans (second.judgment index)

@[simp] theorem id_comp (mapping : ContextMap source target) :
    (id source).comp mapping = mapping := rfl

@[simp] theorem comp_id (mapping : ContextMap source target) :
    mapping.comp (id target) = mapping := rfl

/-- Every supplied position becomes its own proof-relevant assumption. -/
def interpret (definition : ValidatedCalculusLanguageDef) (mapping : ContextMap source target) :
    (⟨source⟩ : ClassifyingContext definition) ⟶ ⟨target⟩ :=
  OpenDerivationList.ofFn target fun index =>
    mapping.judgment index ▸ OpenDerivation.assumption (mapping.position index)

@[simp] theorem interpret_get (definition : ValidatedCalculusLanguageDef)
    (mapping : ContextMap source target) (index : Fin target.length) :
    (mapping.interpret definition).get index =
      mapping.judgment index ▸ OpenDerivation.assumption (mapping.position index) :=
  OpenDerivationList.get_ofFn _ _

theorem interpret_position (definition : ValidatedCalculusLanguageDef)
    (mapping : ContextMap source target) (index : Fin target.length) :
    ((mapping.interpret definition).get index).assumptionPosition = some (mapping.position index) := by
  rw [interpret_get, OpenDerivation.assumptionPosition_cast]
  rfl

/-- Structural context maps retain every position in their actual proof
vectors, including distinct positions carrying equal judgments. -/
theorem interpret_injective (definition : ValidatedCalculusLanguageDef) :
    Function.Injective (interpret (source := source) (target := target) definition) := by
  intro first second same
  apply ContextMap.ext
  funext index
  have positions := congrArg (fun proofs => (proofs.get index).assumptionPosition) same
  rw [interpret_position, interpret_position] at positions
  exact Option.some.inj positions

@[simp] theorem interpret_id (definition : ValidatedCalculusLanguageDef) (context : List Pattern) :
    (id context).interpret definition = 𝟙 (⟨context⟩ : ClassifyingContext definition) := rfl

theorem cast_trans {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {first second third : Pattern} (left : first = second) (right : second = third)
    (proof : OpenDerivation definition context first) :
    left.trans right ▸ proof = right ▸ (left ▸ proof) := by
  cases left
  cases right
  rfl

/-- Structural composition preserves the actual assumption proofs. -/
theorem interpret_comp (definition : ValidatedCalculusLanguageDef)
    (first : ContextMap source middle) (second : ContextMap middle target) :
    (first.comp second).interpret definition =
      first.interpret definition ≫ second.interpret definition := by
  change _ = (second.interpret definition).bind (first.interpret definition)
  unfold interpret
  rw [OpenDerivationList.ofFn_bind]
  apply congrArg (OpenDerivationList.ofFn target)
  funext index
  rw [OpenDerivationList.cast_bind, OpenDerivation.assumption_bind,
    OpenDerivationList.get_ofFn]
  exact cast_trans _ _ _

/-- Inverse maps of actual positions give an isomorphism of premise
contexts, retaining proof terms in both inverse equations. -/
def iso (definition : ValidatedCalculusLanguageDef)
    (forward : ContextMap source target) (backward : ContextMap target source)
    (left : forward.comp backward = id source)
    (right : backward.comp forward = id target) :
    (⟨source⟩ : ClassifyingContext definition) ≅ ⟨target⟩ where
  hom := forward.interpret definition
  inv := backward.interpret definition
  hom_inv_id := by rw [← interpret_comp, left, interpret_id]
  inv_hom_id := by rw [← interpret_comp, right, interpret_id]

end ContextMap
end Mettapedia.GSLT.LanguageDef.CertificateGSLT
