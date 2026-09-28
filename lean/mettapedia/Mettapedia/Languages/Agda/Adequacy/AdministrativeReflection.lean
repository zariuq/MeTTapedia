import Mettapedia.Languages.Agda.Adequacy.AdministrativeReflectionRules

/-!
# Reflection of every administrative static derivation

The actual fixed-point fold interprets all thirty-six rule families. Core
formation, typing and equality return successful observations and independent
source derivations. Action and spine equality retain their explicit observed
input boundary; a conditional nil judgment alone need not form a context.

On the embedded source fragment, inhabitedness is conserved in both directions
for all five core judgments. No equivalence of proof histories or computation
preservation theorem is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.AdministrativeReflection

open Mettapedia.OSLF.Binding
open Mettapedia.TypeTheory
open Structural.Statics (RawTm RawTy RawContext context formed typed typeEqual termEqual)
open Structural.AdministrativeStatics

noncomputable def interpret {j : Judgment} (tree : Derivation j) : Interpretation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => Interpretation j)
    (fun _ _ shape _ ih => interpretRule shape ih) () j tree

noncomputable def contextBack {n : Nat} {Γ : StaticSpecification.RawContext n}
    (tree : CoreDerivation (context (embedContext Γ))) : StaticSpecification.FormCtx Γ :=
  (interpret tree).at (Observation.context_embed Γ)

noncomputable def formationBack {n : Nat} {Γ : StaticSpecification.RawContext n}
    {A : StaticSpecification.Ty n} (tree : CoreDerivation (formed (embedContext Γ) (embedTy A))) :
    StaticSpecification.FormTy Γ A :=
  (interpret tree Γ (Observation.context_embed Γ)).at (Observation.type_embed A)

noncomputable def typingBack {n : Nat} {Γ : StaticSpecification.RawContext n}
    {t : StaticSpecification.Term n} {A : StaticSpecification.Ty n}
    (tree : CoreDerivation (typed (embedContext Γ) (embedTerm t) (embedTy A))) :
    StaticSpecification.Typing Γ t A :=
  (interpret tree Γ (Observation.context_embed Γ)).at (Observation.term_embed t) (Observation.type_embed A)

noncomputable def typeEqualityBack {n : Nat} {Γ : StaticSpecification.RawContext n}
    {A B : StaticSpecification.Ty n}
    (tree : CoreDerivation (typeEqual (embedContext Γ) (embedTy A) (embedTy B))) :
    StaticSpecification.TypeEq Γ A B :=
  (interpret tree Γ (Observation.context_embed Γ)).at (Observation.type_embed A) (Observation.type_embed B)

noncomputable def termEqualityBack {n : Nat} {Γ : StaticSpecification.RawContext n}
    {t u : StaticSpecification.Term n} {A : StaticSpecification.Ty n}
    (tree : CoreDerivation (termEqual (embedContext Γ) (embedTerm t) (embedTerm u) (embedTy A))) :
    StaticSpecification.TermEq Γ t u A :=
  (interpret tree Γ (Observation.context_embed Γ)).at
    (Observation.term_embed t) (Observation.term_embed u) (Observation.type_embed A)

/-- Total successful observation follows from every typing tree in the enlarged family. -/
noncomputable def reflectTyping {n : Nat} {Γ : RawContext n} {t : RawTm n} {A : RawTy n}
    (tree : CoreDerivation (typed Γ t A)) : Reflection.ReflectedTyping Γ t A :=
  let ambient := interpret tree.contextOfTyping
  ⟨ambient, interpret tree ambient.value ambient.observed⟩

noncomputable def reflectFormation {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (tree : CoreDerivation (formed Γ A)) :
    Σ ambient : Reflection.Context Γ, Reflection.Formation ambient.value A :=
  let ambient := interpret tree.contextOfFormation
  ⟨ambient, interpret tree ambient.value ambient.observed⟩

noncomputable def reflectTypeEquality {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (tree : CoreDerivation (typeEqual Γ A B)) :
    Σ ambient : Reflection.Context Γ, Reflection.TypeEquality ambient.value A B :=
  let ambient := interpret tree.contextOfTypeEquality
  ⟨ambient, interpret tree ambient.value ambient.observed⟩

noncomputable def reflectTermEquality {n : Nat} {Γ : RawContext n} {t u : RawTm n} {A : RawTy n}
    (tree : CoreDerivation (termEqual Γ t u A)) :
    Σ ambient : Reflection.Context Γ, Reflection.TermEquality ambient.value t u A :=
  let ambient := interpret tree.contextOfTermEquality
  ⟨ambient, interpret tree ambient.value ambient.observed⟩

theorem context_iff {n : Nat} (Γ : StaticSpecification.RawContext n) :
    Nonempty (CoreDerivation (context (embedContext Γ))) ↔ Nonempty (StaticSpecification.FormCtx Γ) :=
  ⟨fun ⟨tree⟩ => ⟨contextBack tree⟩, fun ⟨tree⟩ => ⟨includeCanonical (contextForward tree)⟩⟩

theorem formation_iff {n : Nat} (Γ : StaticSpecification.RawContext n) (A : StaticSpecification.Ty n) :
    Nonempty (CoreDerivation (formed (embedContext Γ) (embedTy A))) ↔ Nonempty (StaticSpecification.FormTy Γ A) :=
  ⟨fun ⟨tree⟩ => ⟨formationBack tree⟩, fun ⟨tree⟩ => ⟨includeCanonical (formationForward tree)⟩⟩

theorem typing_iff {n : Nat} (Γ : StaticSpecification.RawContext n)
    (t : StaticSpecification.Term n) (A : StaticSpecification.Ty n) :
    Nonempty (CoreDerivation (typed (embedContext Γ) (embedTerm t) (embedTy A))) ↔
      Nonempty (StaticSpecification.Typing Γ t A) :=
  ⟨fun ⟨tree⟩ => ⟨typingBack tree⟩, fun ⟨tree⟩ => ⟨includeCanonical (typingForward tree)⟩⟩

theorem typeEquality_iff {n : Nat} (Γ : StaticSpecification.RawContext n) (A B : StaticSpecification.Ty n) :
    Nonempty (CoreDerivation (typeEqual (embedContext Γ) (embedTy A) (embedTy B))) ↔
      Nonempty (StaticSpecification.TypeEq Γ A B) :=
  ⟨fun ⟨tree⟩ => ⟨typeEqualityBack tree⟩, fun ⟨tree⟩ => ⟨includeCanonical (typeEqualityForward tree)⟩⟩

theorem termEquality_iff {n : Nat} (Γ : StaticSpecification.RawContext n)
    (t u : StaticSpecification.Term n) (A : StaticSpecification.Ty n) :
    Nonempty (CoreDerivation (termEqual (embedContext Γ) (embedTerm t) (embedTerm u) (embedTy A))) ↔
      Nonempty (StaticSpecification.TermEq Γ t u A) :=
  ⟨fun ⟨tree⟩ => ⟨termEqualityBack tree⟩, fun ⟨tree⟩ => ⟨includeCanonical (termEqualityForward tree)⟩⟩

end Mettapedia.Languages.Agda.StaticAdequacy.AdministrativeReflection
