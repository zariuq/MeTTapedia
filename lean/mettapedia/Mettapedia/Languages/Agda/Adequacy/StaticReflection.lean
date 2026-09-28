import Mettapedia.Languages.Agda.Adequacy.StaticReflectionRules
import Mettapedia.Languages.Agda.Structural.StaticContextRegularity

/-!
# Static reflection for the canonical structural presentation

The initial rule-tree fold interprets every canonical native derivation in the
independent finite-Set Pi calculus. It also proves successful observation of
the syntax that each derivation mentions. Together with forward translation,
this yields inhabitedness equivalences on the embedded source fragment.

The translation returns actual source proofs. It is not asserted to be an
equivalence of proof histories, an interpretation of the extended spine proof
family, a subject-reduction theorem, or a decision procedure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Reflection

open Mettapedia.OSLF.Binding
open Mettapedia.TypeTheory
open Structural.Statics

noncomputable def interpret {j : Judgment} (tree : Derivation j) : Interpretation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => Interpretation j)
    (fun _ _ shape _ ih => interpretRule shape ih) () j tree

noncomputable def contextBack {n : Nat} {Γ : StaticSpecification.RawContext n}
    (tree : Derivation (context (embedContext Γ))) : StaticSpecification.FormCtx Γ :=
  (interpret tree).at (Observation.context_embed Γ)

noncomputable def formationBack {n : Nat} {Γ : StaticSpecification.RawContext n}
    {A : StaticSpecification.Ty n} (tree : Derivation (formed (embedContext Γ) (embedTy A))) :
    StaticSpecification.FormTy Γ A :=
  (interpret tree Γ (Observation.context_embed Γ)).at (Observation.type_embed A)

noncomputable def typingBack {n : Nat} {Γ : StaticSpecification.RawContext n}
    {t : StaticSpecification.Term n} {A : StaticSpecification.Ty n}
    (tree : Derivation (typed (embedContext Γ) (embedTerm t) (embedTy A))) :
    StaticSpecification.Typing Γ t A :=
  (interpret tree Γ (Observation.context_embed Γ)).at (Observation.term_embed t) (Observation.type_embed A)

noncomputable def typeEqualityBack {n : Nat} {Γ : StaticSpecification.RawContext n}
    {A B : StaticSpecification.Ty n}
    (tree : Derivation (typeEqual (embedContext Γ) (embedTy A) (embedTy B))) :
    StaticSpecification.TypeEq Γ A B :=
  (interpret tree Γ (Observation.context_embed Γ)).at (Observation.type_embed A) (Observation.type_embed B)

noncomputable def termEqualityBack {n : Nat} {Γ : StaticSpecification.RawContext n}
    {t u : StaticSpecification.Term n} {A : StaticSpecification.Ty n}
    (tree : Derivation (termEqual (embedContext Γ) (embedTerm t) (embedTerm u) (embedTy A))) :
    StaticSpecification.TermEq Γ t u A :=
  (interpret tree Γ (Observation.context_embed Γ)).at
    (Observation.term_embed t) (Observation.term_embed u) (Observation.type_embed A)

structure ReflectedTyping {n : Nat} (Γ : RawContext n) (t : RawTm n) (A : RawTy n) where
  ambient : Context Γ
  typing : Typing ambient.value t A

/-- Total successful observation follows from a canonical typing tree. -/
noncomputable def reflectTyping {n : Nat} {Γ : RawContext n} {t : RawTm n} {A : RawTy n}
    (tree : Derivation (typed Γ t A)) : ReflectedTyping Γ t A :=
  let ambient := interpret tree.contextOfTyping
  ⟨ambient, interpret tree ambient.value ambient.observed⟩

theorem context_iff {n : Nat} (Γ : StaticSpecification.RawContext n) :
    Nonempty (Derivation (context (embedContext Γ))) ↔ Nonempty (StaticSpecification.FormCtx Γ) :=
  ⟨fun ⟨tree⟩ => ⟨contextBack tree⟩, fun ⟨tree⟩ => ⟨contextForward tree⟩⟩

theorem formation_iff {n : Nat} (Γ : StaticSpecification.RawContext n) (A : StaticSpecification.Ty n) :
    Nonempty (Derivation (formed (embedContext Γ) (embedTy A))) ↔ Nonempty (StaticSpecification.FormTy Γ A) :=
  ⟨fun ⟨tree⟩ => ⟨formationBack tree⟩, fun ⟨tree⟩ => ⟨formationForward tree⟩⟩

theorem typing_iff {n : Nat} (Γ : StaticSpecification.RawContext n)
    (t : StaticSpecification.Term n) (A : StaticSpecification.Ty n) :
    Nonempty (Derivation (typed (embedContext Γ) (embedTerm t) (embedTy A))) ↔
      Nonempty (StaticSpecification.Typing Γ t A) :=
  ⟨fun ⟨tree⟩ => ⟨typingBack tree⟩, fun ⟨tree⟩ => ⟨typingForward tree⟩⟩

theorem typeEquality_iff {n : Nat} (Γ : StaticSpecification.RawContext n) (A B : StaticSpecification.Ty n) :
    Nonempty (Derivation (typeEqual (embedContext Γ) (embedTy A) (embedTy B))) ↔
      Nonempty (StaticSpecification.TypeEq Γ A B) :=
  ⟨fun ⟨tree⟩ => ⟨typeEqualityBack tree⟩, fun ⟨tree⟩ => ⟨typeEqualityForward tree⟩⟩

theorem termEquality_iff {n : Nat} (Γ : StaticSpecification.RawContext n)
    (t u : StaticSpecification.Term n) (A : StaticSpecification.Ty n) :
    Nonempty (Derivation (termEqual (embedContext Γ) (embedTerm t) (embedTerm u) (embedTy A))) ↔
      Nonempty (StaticSpecification.TermEq Γ t u A) :=
  ⟨fun ⟨tree⟩ => ⟨termEqualityBack tree⟩, fun ⟨tree⟩ => ⟨termEqualityForward tree⟩⟩

end Mettapedia.Languages.Agda.StaticAdequacy.Reflection
