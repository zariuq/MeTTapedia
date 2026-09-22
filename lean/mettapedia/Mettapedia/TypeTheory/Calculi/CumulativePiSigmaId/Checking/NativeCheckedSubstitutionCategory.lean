import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayCoherence

/-!
# Checked substitutions retaining native argument certificates

Objects are independently checked native contexts. An arrow retains both its
simultaneous substitution and the finite typing certificates of its images.
Composition computes those certificates with the existing replay action.
Identity and associativity use its checked identity/composition laws.

Forgetting certificates gives the existing formation-sensitive context
category. This comparison retains raw term substitutions, not their conversion
classes. It is not a classifying or initiality theorem for the candidate.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCheckedSubstitution

open Presentation NativeIndexedFamilies NativeJudgmentReplay
open _root_.CategoryTheory

private abbrev replay {n : Nat} := StructuralTypingReplay.check IntrinsicRelator.rules
  NativeRelatorConversionChecking.check (n := n)

structure Context where
  arity : Nat
  raw : Tower.Ctx arity
  code : ContextCode arity
  accepted : StructuralTypingReplay.checkContext IntrinsicRelator.rules
    NativeRelatorConversionChecking.check raw code = true

def Context.toFormed (context : Context) :
    FormationSensitiveContextual.Context IntrinsicRelator.rules :=
  ⟨context.arity, context.raw,
    StructuralTypingReplay.checkContext_sound IntrinsicRelator.rules
      NativeRelatorConversionChecking.check NativeRelatorConversionChecking.check_sound
      context.code context.accepted⟩

structure Hom (source target : Context) where
  substitution : Sub Tower.Head target.arity source.arity
  codes : Fin target.arity → Code source.arity
  accepted : TelescopeArgumentChecking.checkArguments (replay source.raw)
    target.raw substitution codes = true

@[ext] theorem Hom.ext {source target : Context} {first second : Hom source target}
    (substitutions : first.substitution = second.substitution)
    (certificates : first.codes = second.codes) : first = second := by
  cases first
  cases second
  cases substitutions
  cases certificates
  rfl

theorem Hom.image_checked {source target : Context} (morphism : Hom source target)
    (index : Fin target.arity) :
    check source.raw (morphism.substitution index)
      (subst morphism.substitution (Ctx.lookup target.raw index)) source.code
      (morphism.codes index) = true := by
  have component := (TelescopeArgumentChecking.checkArguments_eq_true_iff _ _ _ _).mp
    morphism.accepted index
  simp only [check, StructuralTypingReplay.checkJudgment, Bool.and_eq_true]
  exact ⟨source.accepted, component⟩

def Hom.id (context : Context) : Hom context context where
  substitution := ids
  codes := fun _ => .var
  accepted := by
    apply (TelescopeArgumentChecking.checkArguments_eq_true_iff _ _ _ _).mpr
    intro index
    simp only [replay, ids, subst_ids, StructuralTypingReplay.check, decide_true]

def Hom.comp {first middle last : Context} (earlier : Hom first middle)
    (later : Hom middle last) : Hom first last where
  substitution := subComp earlier.substitution later.substitution
  codes := composeImageCodes last.raw later.substitution later.codes
    earlier.substitution earlier.codes
  accepted := composed_arguments_checked _ _ _ _ later.accepted earlier.accepted

theorem Hom.id_comp {source target : Context} (morphism : Hom source target) :
    (Hom.id source).comp morphism = morphism := by
  apply Hom.ext (subComp_ids_left morphism.substitution)
  funext index
  exact substitute_ids (morphism.image_checked index)

theorem Hom.comp_id {source target : Context} (morphism : Hom source target) :
    morphism.comp (Hom.id target) = morphism := by
  apply Hom.ext (subComp_ids_right morphism.substitution)
  funext index
  rfl

theorem Hom.assoc {first second third last : Context}
    (f : Hom first second) (g : Hom second third) (h : Hom third last) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply Hom.ext (subComp_assoc f.substitution g.substitution h.substitution).symm
  funext index
  have coherent := substitute_comp (h.image_checked index)
    g.substitution g.codes f.substitution f.codes
  simpa only [Hom.comp, composeImageCodes, StructuralTypingReplay.composeImageCodes,
    NativeJudgmentReplay.substitute, subst_subComp, subComp] using coherent.symm

instance contextCategory : Category Context where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

def Hom.toFormed {source target : Context} (morphism : Hom source target) :
    FormationSensitiveContextual.Hom source.toFormed target.toFormed where
  substitution := morphism.substitution
  typed index := (sound (morphism.image_checked index)).typing

/-- Certificate erasure preserves the actual substitution and composition. -/
def forget : Context ⥤ FormationSensitiveContextual.Context IntrinsicRelator.rules where
  obj := Context.toFormed
  map := Hom.toFormed

/-- Every existing formed substitution between these checked contexts has
finite image certificates. This is existence, not a search algorithm. -/
theorem forget_map_surjective (source target : Context) :
    Function.Surjective (forget.map (X := source) (Y := target)) := by
  intro morphism
  have existsCode := fun index => StructuralTypingReplay.check_complete IntrinsicRelator.rules
    NativeRelatorConversionChecking.check
    (fun conversion => NativeRelatorConversionChecking.conversion_iff_checked.mp conversion)
    (morphism.typed index)
  choose codes accepted using existsCode
  exact ⟨⟨morphism.substitution, codes,
    (TelescopeArgumentChecking.checkArguments_eq_true_iff _ _ _ _).mpr accepted⟩, rfl⟩

namespace Controls

open NativeRelatorConversionChecking.Examples (ground)

def groundContext : Context :=
  ⟨1, NativeJudgmentReplay.Controls.context, NativeJudgmentReplay.Controls.contextCode,
    by decide +kernel⟩

def convertedVariable : Code 1 :=
  .convert ground (.sort Tower.zero) .var .headType (.refl ground)

def convertedIdentity : groundContext ⟶ groundContext where
  substitution := ids
  codes := fun _ => convertedVariable
  accepted := by decide +kernel

theorem distinct_certified_arrows : convertedIdentity ≠ 𝟙 groundContext := by
  intro equal
  have codes := congrArg (fun morphism : Hom groundContext groundContext =>
    morphism.codes ⟨0, by decide +kernel⟩) equal
  cases codes

theorem erased_arrows_equal : forget.map convertedIdentity = forget.map (𝟙 groundContext) := rfl

/-- Even syntax-retaining formed contexts forget finite derivation choices. -/
theorem forget_not_faithful : ¬ forget.Faithful := by
  intro faithful
  exact distinct_certified_arrows (faithful.map_injective erased_arrows_equal)

end Controls

#print axioms contextCategory
#print axioms forget
#print axioms forget_map_surjective
#print axioms Controls.distinct_certified_arrows
#print axioms Controls.erased_arrows_equal
#print axioms Controls.forget_not_faithful

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCheckedSubstitution
