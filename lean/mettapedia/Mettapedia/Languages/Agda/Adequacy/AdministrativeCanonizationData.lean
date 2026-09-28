import Mettapedia.Languages.Agda.Structural.AdministrativeAdmission
import Mettapedia.Languages.Agda.Structural.AdministrativeSpineLinearization
import Mettapedia.Languages.Agda.Adequacy.StaticObservationViews

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Canonization

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Structural
open Structural.Statics (RawTm RawTy RawContext TypeParameter TypeBody)
open Structural.AdministrativeStatics

def applyReadback {n : Nat} (head : RawTm n) (spine : StaticSpecification.Spine n) : RawTm n :=
  spine.foldl (fun head e => eliminate head (cons (embedElim e) nil)) head

@[simp] theorem applyReadback_nil {n : Nat} (head : RawTm n) : applyReadback head [] = head := rfl

@[simp] theorem applyReadback_cons {n : Nat} (head : RawTm n) (e : StaticSpecification.Elim n)
    (tail : StaticSpecification.Spine n) :
    applyReadback head (e :: tail) = applyReadback (eliminate head (cons (embedElim e) nil)) tail := rfl

theorem applyReadback_append {n : Nat} (head : RawTm n) (first second : StaticSpecification.Spine n) :
    applyReadback head (first ++ second) = applyReadback (applyReadback head first) second :=
  List.foldl_append

theorem applyReadback_embed {n : Nat} (head : StaticSpecification.Term n) (spine : StaticSpecification.Spine n) :
    applyReadback (embedTerm head) spine = embedTerm (head.applySpine spine) :=
  (embedTerm_applySpine head spine).symm

noncomputable def termReflexivity {n : Nat} {Γ : RawContext n} {t : RawTm n} {A : RawTy n}
    (typed : CoreDerivation (Statics.typed Γ t A)) : CoreDerivation (Statics.termEqual Γ t t A) :=
  Derivation.core (.reflexivity Γ t A) (consEvidence CoreDerivation typed (noEvidence CoreDerivation))

noncomputable def termSymmetry {n : Nat} {Γ : RawContext n} {t u : RawTm n} {A : RawTy n}
    (equal : CoreDerivation (Statics.termEqual Γ t u A)) : CoreDerivation (Statics.termEqual Γ u t A) :=
  Derivation.core (.symmetry Γ t u A) (consEvidence CoreDerivation equal (noEvidence CoreDerivation))

noncomputable def termTransitivity {n : Nat} {Γ : RawContext n} {t u v : RawTm n} {A : RawTy n}
    (first : CoreDerivation (Statics.termEqual Γ t u A))
    (second : CoreDerivation (Statics.termEqual Γ u v A)) : CoreDerivation (Statics.termEqual Γ t v A) :=
  Derivation.core (.transitivity Γ t u v A)
    (consEvidence CoreDerivation first (consEvidence CoreDerivation second (noEvidence CoreDerivation)))

noncomputable def termConversion {n : Nat} {Γ : RawContext n} {t u : RawTm n} {A B : RawTy n}
    (terms : CoreDerivation (Statics.termEqual Γ t u A))
    (types : CoreDerivation (Statics.typeEqual Γ A B)) : CoreDerivation (Statics.termEqual Γ t u B) :=
  Derivation.core (.equalityConversion Γ t u A B)
    (consEvidence CoreDerivation terms (consEvidence CoreDerivation types (noEvidence CoreDerivation)))

noncomputable def applicationCongruence {n : Nat} {Γ : RawContext n} {A : TypeParameter n} {B : TypeBody n}
    {f g u v : RawTm n} (heads : CoreDerivation (Statics.termEqual Γ f g (Statics.piType A B).code))
    (arguments : CoreDerivation (Statics.termEqual Γ u v A.code)) :
    CoreDerivation (Statics.termEqual Γ (Statics.app f u) (Statics.app g v) (B.instantiate u).code) :=
  Derivation.core (.applicationCongruence Γ A B f g u v)
    (consEvidence CoreDerivation heads (consEvidence CoreDerivation arguments (noEvidence CoreDerivation)))

structure ContextResult {n : Nat} (Γ : RawContext n) where
  value : StaticSpecification.RawContext n
  observed : Observation.context Γ = some value
  equality : ContextConversion Γ (embedContext value)

structure TypeResult {n : Nat} (Γ : RawContext n) (A : RawTy n) where
  value : StaticSpecification.Ty n
  observed : Observation.type A = some value
  equality : CoreDerivation (Statics.typeEqual Γ A (embedTy value))

structure TermResult {n : Nat} (Γ : RawContext n) (t : RawTm n) (A : RawTy n) where
  value : StaticSpecification.Term n
  observed : Observation.term t = some value
  equality : CoreDerivation (Statics.termEqual Γ t (embedTerm value) A)

structure ActionResult {n : Nat} (Γ : RawContext n) (A : RawTy n) (es : Spine (scope n)) (B : RawTy n) where
  value : StaticSpecification.Spine n
  observed : Observation.spine es = some value
  transform : ∀ {f g : RawTm n}, CoreDerivation (Statics.termEqual Γ f g A) →
    CoreDerivation (Statics.termEqual Γ (eliminate f es) (applyReadback g value) B)

noncomputable def TypeResult.at {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (result : TypeResult Γ A) {a : StaticSpecification.Ty n} (observed : Observation.type A = some a) :
    CoreDerivation (Statics.typeEqual Γ A (embedTy a)) :=
  (congrArg (fun a => CoreDerivation (Statics.typeEqual Γ A (embedTy a)))
    (Option.some.inj (result.observed.symm.trans observed))).mp result.equality

noncomputable def TermResult.at {n : Nat} {Γ : RawContext n} {t : RawTm n} {A : RawTy n}
    (result : TermResult Γ t A) {term : StaticSpecification.Term n}
    (observed : Observation.term t = some term) :
    CoreDerivation (Statics.termEqual Γ t (embedTerm term) A) :=
  (congrArg (fun term => CoreDerivation (Statics.termEqual Γ t (embedTerm term) A))
    (Option.some.inj (result.observed.symm.trans observed))).mp result.equality

noncomputable def ActionResult.at {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {es : Spine (scope n)} (result : ActionResult Γ A es B) {spine : StaticSpecification.Spine n}
    (observed : Observation.spine es = some spine) {f g : RawTm n}
    (heads : CoreDerivation (Statics.termEqual Γ f g A)) :
    CoreDerivation (Statics.termEqual Γ (eliminate f es) (applyReadback g spine) B) :=
  (congrArg (fun spine => CoreDerivation (Statics.termEqual Γ (eliminate f es) (applyReadback g spine) B))
    (Option.some.inj (result.observed.symm.trans observed))).mp (result.transform heads)

def CoreMotive : Statics.Judgment → Type
  | .context ⟨_, Γ⟩ => ContextResult Γ
  | .type ⟨_, Γ⟩ A => TypeResult Γ A
  | .term ⟨_, Γ⟩ A t => TermResult Γ t.code A
  | _ => PUnit

def Motive : Judgment → Type
  | .core j => CoreMotive j
  | .spineAction Γ A es B => ActionResult Γ A es B
  | .spineEquality _ _ _ _ _ => PUnit

end Mettapedia.Languages.Agda.StaticAdequacy.Canonization
