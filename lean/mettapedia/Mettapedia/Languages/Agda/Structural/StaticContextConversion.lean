import Mettapedia.Languages.Agda.Structural.StaticEndpointRegularity

/-!
# Converting whole dependent structural contexts

Each declaration equality is stated over its source prefix. The recursive
construction transports it along the already constructed identity substitution
for that prefix, then converts the newest variable. Every variable image has
an actual typing tree; the raw substitution is identity without identifying
the source and target context syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory

inductive ContextConversion (D : Judgment → Type) : {n : Nat} → RawContext n → RawContext n → Type where
  | nil : ContextConversion D .nil .nil
  | snoc {n : Nat} {Γ Δ : RawContext n} {A B : RawTy n} :
      ContextConversion D Γ Δ → D (typeEqual Γ A B) →
      ContextConversion D (Γ.snoc A) (Δ.snoc B)

namespace ContextConversion

variable {D : Judgment → Type} (ops : EvidenceOperations D)
    (endpoints : ∀ {n : Nat} {Γ : RawContext n} {A B : RawTy n},
      D (typeEqual Γ A B) → TypeEndpoints D Γ A B)

def identitySubstitution {n : Nat} {Γ Δ : RawContext n} (conversion : ContextConversion D Γ Δ) :
    TypedSubstitution D Γ Δ (Telescope.identity (S := sig) .term n) :=
  match conversion with
  | .nil => TypedSubstitution.identity ops.algebra (ops.build .empty (noEvidence D))
  | @snoc _ n Γ Δ A B previous equal => by
      have prior := identitySubstitution previous
      have ends := endpoints equal
      have targetDomain : D (formed Δ B) :=
        (congrArg (fun T => D (formed Δ T)) (Telescope.bind_identity B)).mp
          (ops.substituteEvidence ends.right Δ (Telescope.identity (S := sig) .term n) prior)
      have targetEqual : D (typeEqual Δ A B) :=
        (congrArg₂ (fun A B => D (typeEqual Δ A B)) (Telescope.bind_identity A) (Telescope.bind_identity B)).mp
          (ops.substituteEvidence equal Δ (Telescope.identity (S := sig) .term n) prior)
      let target := ops.extend prior.target targetDomain
      refine ⟨ops.extend prior.source ends.left, target, fun v => ?_⟩
      cases v with
      | zero =>
        have newest := ops.build (.variable (Δ.snoc B) .zero) (consEvidence D target (noEvidence D))
        have converted := ops.build (.conversion (Δ.snoc B) (.var .zero) (weaken B) (weaken A))
          (consEvidence D newest
            (consEvidence D (ops.weakenTypeEquality targetDomain (ops.typeSymmetry targetEqual)) (noEvidence D)))
        exact (congrArg (fun T => D (typed (Δ.snoc B) (.var .zero) T))
          (Telescope.bind_identity (ContextGeometry.lookup (Γ.snoc A) .zero))).mpr converted
      | succ v =>
        have old : D (typed Δ (.var v) (ContextGeometry.lookup Γ v)) :=
          (congrArg (fun T => D (typed Δ (.var v) T))
            (Telescope.bind_identity (ContextGeometry.lookup Γ v))).mp (prior.image v)
        have lifted := ops.renameEvidence old (Δ.snoc B)
          (Telescope.RawRen.projection (S := sig) .term n)
          (Telescope.RawRen.respects_projection Δ B) target
        have weaker := (congrArg (fun T => D (typed (Δ.snoc B) (.var (.succ v)) T))
          (Telescope.bind_projection (S := sig) (b := .term) (ContextGeometry.lookup Γ v))).mp lifted
        exact (congrArg (fun T => D (typed (Δ.snoc B) (.var (.succ v)) T))
          (Telescope.bind_identity (ContextGeometry.lookup (Γ.snoc A) (.succ v)))).mpr weaker

def formation {n : Nat} {Γ Δ : RawContext n} (conversion : ContextConversion D Γ Δ)
    {A : RawTy n} (formed : D (Statics.formed Γ A)) : D (Statics.formed Δ A) :=
  (congrArg (fun T => D (Statics.formed Δ T)) (Telescope.bind_identity A)).mp
    (ops.substituteEvidence formed Δ (Telescope.identity (S := sig) .term n)
      (conversion.identitySubstitution ops endpoints))

def typing {n : Nat} {Γ Δ : RawContext n} (conversion : ContextConversion D Γ Δ)
    {t : RawTm n} {A : RawTy n} (typed : D (Statics.typed Γ t A)) : D (Statics.typed Δ t A) :=
  (congrArg₂ (fun t T => D (Statics.typed Δ t T)) (Telescope.bind_identity t) (Telescope.bind_identity A)).mp
    (ops.substituteEvidence typed Δ (Telescope.identity (S := sig) .term n)
      (conversion.identitySubstitution ops endpoints))

def typeEquality {n : Nat} {Γ Δ : RawContext n} (conversion : ContextConversion D Γ Δ)
    {A B : RawTy n} (equal : D (typeEqual Γ A B)) : D (typeEqual Δ A B) :=
  (congrArg₂ (fun A B => D (typeEqual Δ A B)) (Telescope.bind_identity A) (Telescope.bind_identity B)).mp
    (ops.substituteEvidence equal Δ (Telescope.identity (S := sig) .term n)
      (conversion.identitySubstitution ops endpoints))

def termEquality {n : Nat} {Γ Δ : RawContext n} (conversion : ContextConversion D Γ Δ)
    {t u : RawTm n} {A : RawTy n} (equal : D (termEqual Γ t u A)) : D (termEqual Δ t u A) := by
  have substituted := ops.substituteEvidence equal Δ (Telescope.identity (S := sig) .term n)
    (conversion.identitySubstitution ops endpoints)
  exact (congrArg₂ (fun (pair : RawTm n × RawTm n) T => D (termEqual Δ pair.1 pair.2 T))
    (congrArg₂ Prod.mk (Telescope.bind_identity t) (Telescope.bind_identity u)) (Telescope.bind_identity A)).mp substituted

def symmetry {n : Nat} {Γ Δ : RawContext n} (conversion : ContextConversion D Γ Δ) :
    ContextConversion D Δ Γ :=
  match conversion with
  | .nil => .nil
  | .snoc previous equal =>
      .snoc (symmetry previous) (ops.typeSymmetry (previous.typeEquality ops endpoints equal))

def transitivity {n : Nat} {Γ Δ Θ : RawContext n}
    (first : ContextConversion D Γ Δ) (second : ContextConversion D Δ Θ) : ContextConversion D Γ Θ :=
  match first, second with
  | .nil, .nil => .nil
  | .snoc previous equal, .snoc next nextEqual =>
      .snoc (transitivity previous next)
        (ops.typeTransitivity equal ((previous.symmetry ops endpoints).typeEquality ops endpoints nextEqual))

end ContextConversion

def ContextReflexivity (D : Judgment → Type) : Judgment → Type
  | .context ⟨_, Γ⟩ => ContextConversion D Γ Γ
  | _ => PUnit

def contextReflexivityRule {D : Judgment → Type} (ops : EvidenceOperations D)
    {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape))
    (ih : Evidence (ContextReflexivity D) (premises shape)) : ContextReflexivity D j := by
  cases shape <;> simp only [premises] at children ih
  case empty => exact .nil
  case extend => exact .snoc (ih 0) (ops.typeReflexivity (children 1))
  case formation | sort | «variable» | pi | lambda | application | conversion | typeEquality
    | reflexivity | symmetry | transitivity | equalityConversion | piCongruence | applicationCongruence | beta | eta => exact ⟨⟩

noncomputable def Derivation.contextReflexivity {n : Nat} {Γ : RawContext n}
    (tree : Derivation (context Γ)) : ContextConversion Derivation Γ Γ :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => ContextReflexivity Derivation j)
    (fun _ _ shape children ih => contextReflexivityRule canonicalOperations shape children ih)
    () (context Γ) tree

end Mettapedia.Languages.Agda.Structural.Statics
