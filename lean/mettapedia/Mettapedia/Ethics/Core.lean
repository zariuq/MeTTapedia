import Mathlib.Tactic

set_option autoImplicit false

/-!
# Ethics Core Types

Deontic and value-judgment sentence types, together with minimal semantic
infrastructure (Semantics, Theory, satisfaction).

Ported from `foet/Foet/EthicsCore.lean` with Mettapedia namespace.

## Contents

- §1 Semantic infrastructure (Semantics, Theory)
- §2 Deontic/moral-value attribute tags
- §3 Formula and modal sentence types
- §4 Deontic and value semantics structures
- §5 Sentence translations and alignment
-/

namespace Mettapedia.Ethics

universe u v

/-! ## §1 Semantic Infrastructure -/

/-- A semantics for sentences of type `S` in models of type `M`. -/
structure Semantics (S : Type u) (M : Type v) : Type (max u v) where
  Sat : M → S → Prop

/-- A `Theory S` is a set of sentences of type `S`. -/
abbrev Theory (S : Type u) : Type u := Set S

/-- A model `m` satisfies a theory `T` if it satisfies every sentence in `T`. -/
def Models {S : Type u} {M : Type v} (sem : Semantics S M) (m : M) (T : Theory S) : Prop :=
  ∀ s, s ∈ T → sem.Sat m s

/-- Semantic entailment: `T ⊨ φ` if every model of `T` satisfies `φ`. -/
def Entails {S : Type u} {M : Type v} (sem : Semantics S M) (T : Theory S) (φ : S) : Prop :=
  ∀ m, Models sem m T → sem.Sat m φ

/-! ## §2 Attribute Tags -/

/-- Deontic tags (Obligation/Prohibition/Permission). -/
inductive DeonticAttribute : Type
  | Obligation
  | Prohibition
  | Permission
  deriving DecidableEq, Repr

/-- Moral value tags (Good/Bad/Permissible). -/
inductive MoralValueAttribute : Type
  | MorallyGood
  | MorallyBad
  | MorallyPermissible
  deriving DecidableEq, Repr

/-- The "simple" mapping from deontic to moral value attributes. -/
def deonticToMoralValue : DeonticAttribute → MoralValueAttribute
  | .Obligation  => .MorallyGood
  | .Prohibition => .MorallyBad
  | .Permission  => .MorallyPermissible

/-- Inverse of `deonticToMoralValue`. -/
def moralValueToDeontic : MoralValueAttribute → DeonticAttribute
  | .MorallyGood        => .Obligation
  | .MorallyBad         => .Prohibition
  | .MorallyPermissible => .Permission

theorem moralValueToDeontic_deonticToMoralValue (d : DeonticAttribute) :
    moralValueToDeontic (deonticToMoralValue d) = d := by
  cases d <;> rfl

theorem deonticToMoralValue_moralValueToDeontic (m : MoralValueAttribute) :
    deonticToMoralValue (moralValueToDeontic m) = m := by
  cases m <;> rfl

/-! ## §3 Formula and Modal Sentence Types -/

/-- An object-language formula as a proposition about a `World`. -/
abbrev Formula (World : Type u) : Type u := World → Prop

/-- A tagged modal sentence: a tag applied to a base formula. -/
structure ModalSentence (World : Type u) (Tag : Type) : Type (max u 1) where
  tag     : Tag
  formula : Formula World

abbrev DeonticSentence (World : Type u) : Type (max u 1) :=
  ModalSentence World DeonticAttribute

abbrev ValueJudgmentSentence (World : Type u) : Type (max u 1) :=
  ModalSentence World MoralValueAttribute

/-! ## §4 Deontic and Value Semantics Structures -/

/-- A minimal semantics for value-judgment sentences:
    interpret tag + formula into a `Prop` at a world. -/
structure ValueSemantics (World : Type u) : Type (max u 1) where
  morally : MoralValueAttribute → Formula World → Formula World

structure DeonticSemantics (World : Type u) : Type (max u 1) where
  deontic : DeonticAttribute → Formula World → Formula World

def ValueSemantics.sat {World : Type u} (sem : ValueSemantics World) (w : World)
    (s : ValueJudgmentSentence World) : Prop :=
  sem.morally s.tag s.formula w

def DeonticSemantics.sat {World : Type u} (sem : DeonticSemantics World) (w : World)
    (s : DeonticSentence World) : Prop :=
  sem.deontic s.tag s.formula w

def valueJudgmentSemantics (World : Type u) (sem : ValueSemantics World) :
    Semantics (ValueJudgmentSentence World) World :=
  ⟨fun w s => ValueSemantics.sat sem w s⟩

/-- The standard `Semantics` wrapper for deontic sentences. -/
def deonticSemantics (World : Type u) (sem : DeonticSemantics World) :
    Semantics (DeonticSentence World) World :=
  ⟨fun w s => DeonticSemantics.sat sem w s⟩

/-! ## §5 Sentence Translations and Alignment -/

/-- Deontic sentence → value-judgment sentence (tag mapping only). -/
def DeonticSentence.toValue {World : Type u} (s : DeonticSentence World) :
    ValueJudgmentSentence World :=
  { tag := deonticToMoralValue s.tag, formula := s.formula }

/-- Value-judgment sentence → deontic sentence (tag mapping only). -/
def ValueJudgmentSentence.toDeontic {World : Type u} (s : ValueJudgmentSentence World) :
    DeonticSentence World :=
  { tag := moralValueToDeontic s.tag, formula := s.formula }

theorem DeonticSentence.toValue_toDeontic {World : Type u} (s : DeonticSentence World) :
    s.toValue.toDeontic = s := by
  cases s with
  | mk tag formula =>
    simp [DeonticSentence.toValue, ValueJudgmentSentence.toDeontic,
      moralValueToDeontic_deonticToMoralValue]

theorem ValueJudgmentSentence.toDeontic_toValue {World : Type u}
    (s : ValueJudgmentSentence World) : s.toDeontic.toValue = s := by
  cases s with
  | mk tag formula =>
    simp [DeonticSentence.toValue, ValueJudgmentSentence.toDeontic,
      deonticToMoralValue_moralValueToDeontic]

/-- Satisfaction commutes with `DeonticSentence.toValue` when semantics are aligned. -/
theorem DeonticSemantics.sat_iff_sat_toValue {World : Type u}
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w)
    (w : World) (s : DeonticSentence World) :
    (deonticSemantics World semD).Sat w s ↔
    (valueJudgmentSemantics World semV).Sat w s.toValue :=
  h_align s.tag s.formula w

end Mettapedia.Ethics
