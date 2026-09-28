import Mettapedia.GSLT.Core.ContextualAdmission
import Mettapedia.Logic.HOL.Embedding.ContextualStructure
import Mettapedia.Logic.HOL.Syntax.ConstMap

/-!
# Admitted HOL syntax in the image of a constant signature map

This consumer of the common admission interface uses the live, intrinsically
typed HOL syntax. A term's evidence is an actual source-signature term whose
constant map has the stated target. Substitution evidence retains a whole
source substitution. Existing `mapConst_subst` supplies structural closure;
no dependent-type encoding of HOL or duplicate substitution engine is used.

Type and context formation have their ordinary constructor derivations.
The constant map may identify distinct symbols: the supported target syntax
then forgets which source was supplied, while the retained fibre does not.
This qualifies structural signature admission, not logical theorem transport
or a raw-byte checker.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SignatureImageAdmission

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualStructure

universe u v w

/-- Formation derivations for the native simple-type grammar. -/
inductive TypeFormation (Base : Type u) : Ty Base → Type u where
  | prop : TypeFormation Base .prop
  | base (name : Base) : TypeFormation Base (.base name)
  | arr {A B : Ty Base} : TypeFormation Base A → TypeFormation Base B →
      TypeFormation Base (.arr A B)

def typeFormation {Base : Type u} : (A : Ty Base) → TypeFormation Base A
  | .prop => .prop
  | .base name => .base name
  | .arr A B => .arr (typeFormation A) (typeFormation B)

inductive ContextFormation (Base : Type u) : Ctx Base → Type u where
  | nil : ContextFormation Base []
  | cons {Γ : Ctx Base} {A : Ty Base} :
      TypeFormation Base A → ContextFormation Base Γ → ContextFormation Base (A :: Γ)

variable {Base : Type u} {Source : Ty Base → Type v} {Target : Ty Base → Type w}

def contextFormation : (Γ : Ctx Base) → ContextFormation Base Γ
  | [] => .nil
  | A :: Γ => .cons (typeFormation A) (contextFormation Γ)

variable (symbols : ∀ {A : Ty Base}, Source A → Target A)

abbrev TermEvidence {Γ : Ctx Base} {A : Ty Base} (t : Term Target Γ A) :=
  { original : Term Source Γ A // mapConst symbols original = t }

/-- One retained simultaneous substitution; no componentwise witness selection. -/
abbrev SubstitutionEvidence {Γ Δ : Ctx Base} (σ : Subst Target Δ Γ) :=
  { original : Subst Source Δ Γ //
    ∀ {A : Ty Base} (v : Var Δ A), mapConst symbols (original v) = σ v }

def evidenceSubstitution {Γ Δ : Ctx Base} {A : Ty Base}
    {t : Term Target Δ A} {σ : Subst Target Δ Γ}
    (term : TermEvidence symbols t) (substitution : SubstitutionEvidence symbols σ) :
    TermEvidence symbols (subst σ t) :=
  ⟨subst substitution.val term.val, by
    rw [mapConst_subst, term.property]
    exact subst_ext substitution.property t⟩

/-- The shared closure interface instantiated with actual native HOL syntax. -/
def derivations : CwfDerivations.{u, max u w, u, max u w, max u v}
    (holScwf Base Target).toCwf where
  context Γ := ULift.{max u v} (ContextFormation Base Γ)
  type _ A := ULift.{max u v} (TypeFormation Base A)
  term _ _ t := ULift.{max u v} (TermEvidence symbols t)
  substitution _ _ σ := ULift.{max u v} (SubstitutionEvidence symbols σ)
  identityDerivation Γ _ := ⟨⟨Subst.id, fun _ => rfl⟩⟩
  composeDerivation σ τ _ _ _ first second :=
    ⟨⟨Subst.comp second.down.val first.down.val, by
      intro A var
      exact (evidenceSubstitution symbols
        ⟨first.down.val var, first.down.property var⟩ second.down).property⟩⟩
  reindexType _ _ _ _ formed _ := formed
  reindexTerm _ _ _ _ _ term substitution :=
    ⟨evidenceSubstitution symbols term.down substitution.down⟩
  extendDerivation _ _ formed type := ⟨.cons type.down formed.down⟩
  projectionDerivation _ _ _ _ := ⟨⟨Subst.ofRename Rename.weaken, fun _ => rfl⟩⟩
  variableDerivation _ _ _ _ := ⟨⟨.var .vz, rfl⟩⟩
  pairing σ A t _ _ substitution _ term :=
    ⟨⟨extendSubst substitution.down.val term.down.val, by
      intro B var
      cases var with
      | vz => exact term.down.property
      | vs old => exact substitution.down.property old⟩⟩

/-- The resulting signature-image profile has an actual terminal context. -/
def admitted : CwfWithTerminal :=
  CwfDerivations.admittedWithTerminal (holScwfWithTerminal Base Target).toCwfWithTerminal
    (derivations symbols) ⟨.nil⟩
    (fun _ _ => ⟨⟨toEmpty _, fun var => nomatch var⟩⟩)

/-! ## Separation and exclusion controls -/

inductive SourceConstant : Ty Unit → Type where
  | first : SourceConstant .prop
  | second : SourceConstant .prop

inductive TargetConstant : Ty Unit → Type where
  | shared : TargetConstant .prop
  | excluded : TargetConstant .prop

def mergeSymbols : {A : Ty Unit} → SourceConstant A → TargetConstant A
  | _, .first | _, .second => .shared

def firstEvidence : TermEvidence mergeSymbols
    (.const .shared : Term TargetConstant [] .prop) := ⟨.const .first, rfl⟩

def secondEvidence : TermEvidence mergeSymbols
    (.const .shared : Term TargetConstant [] .prop) := ⟨.const .second, rfl⟩

theorem different_evidence : firstEvidence ≠ secondEvidence := by
  intro same
  have terms := congrArg Subtype.val same
  cases terms

theorem excluded_not_in_image :
    ¬ Nonempty (TermEvidence mergeSymbols (.const .excluded : Term TargetConstant [] .prop)) := by
  rintro ⟨⟨term, same⟩⟩
  cases term <;> simp only [mapConst] at same
  all_goals try { cases same }
  rename_i constant
  cases constant <;> cases same

def mergeDerivations := derivations (Base := Unit)
  (Source := SourceConstant) (Target := TargetConstant) (fun {A} => @mergeSymbols A)

def emptyContext : mergeDerivations.Context := ⟨[], ⟨⟨.nil⟩⟩⟩
def proposition : mergeDerivations.TypeOver emptyContext := ⟨.prop, ⟨⟨.prop⟩⟩⟩

theorem retained_evidence_distinct :
    mergeDerivations.retainTerm (Γ := emptyContext) (A := proposition)
      (ULift.up firstEvidence) ≠
    mergeDerivations.retainTerm (Γ := emptyContext) (A := proposition)
      (ULift.up secondEvidence) := by
  intro equal
  have witnesses := mergeDerivations.retainTerm_injective equal
  exact different_evidence (congrArg ULift.down witnesses)

theorem supported_terms_coincide :
    (mergeDerivations.retainTerm (Γ := emptyContext) (A := proposition)
      (ULift.up firstEvidence)).1 =
    (mergeDerivations.retainTerm (Γ := emptyContext) (A := proposition)
      (ULift.up secondEvidence)).1 := rfl

/-- Even a hypothetical selector cannot recover both originally supplied
preimages from their identical admitted target term. -/
theorem no_recovery_of_original_evidence :
    ¬ ∃ recover : mergeDerivations.Term emptyContext proposition →
        (Σ t : mergeDerivations.Term emptyContext proposition, mergeDerivations.TermEvidence t),
      recover (mergeDerivations.retainTerm (Γ := emptyContext) (A := proposition)
        (ULift.up firstEvidence)).1 =
        mergeDerivations.retainTerm (Γ := emptyContext) (A := proposition)
          (ULift.up firstEvidence) ∧
      recover (mergeDerivations.retainTerm (Γ := emptyContext) (A := proposition)
        (ULift.up secondEvidence)).1 =
        mergeDerivations.retainTerm (Γ := emptyContext) (A := proposition)
          (ULift.up secondEvidence) := by
  rintro ⟨recover, first, second⟩
  exact retained_evidence_distinct
    (first.symm.trans ((congrArg recover supported_terms_coincide).trans second))

theorem excluded_not_admitted :
    ¬ ∃ t : mergeDerivations.Term emptyContext proposition,
      t.val = .const .excluded := by
  rintro ⟨t, same⟩
  obtain ⟨evidence⟩ := t.property
  exact excluded_not_in_image ⟨same ▸ evidence.down⟩

end Mettapedia.Logic.HOL.SignatureImageAdmission
