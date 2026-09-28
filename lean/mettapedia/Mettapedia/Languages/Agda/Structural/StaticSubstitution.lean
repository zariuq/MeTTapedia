import Mettapedia.Languages.Agda.Structural.StaticSyntax

/-!
# Substitution on structural static rule parameters

The action on abstractions uses the signature's binder lift. These laws concern
the actual raw terms occurring in the static rules; they do not assume that an
arbitrary substitution preserves typing. The latter needs typed images for its
variables and a separate induction on derivations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding

@[simp] theorem TypeParameter.level_substitute {n m : Nat}
    (A : TypeParameter n) (σ : RawSub n m) : (A.substitute σ).level = A.level := rfl

@[simp] theorem TypeParameter.term_substitute {n m : Nat}
    (A : TypeParameter n) (σ : RawSub n m) : (A.substitute σ).term = bind σ A.term := rfl

@[simp] theorem TypeParameter.substitute_identity {n : Nat} (A : TypeParameter n) :
    A.substitute (Telescope.identity (S := sig) .term n) = A := by
  cases A with
  | mk level term => exact congrArg (TypeParameter.mk level) (Telescope.bind_identity term)

theorem TypeParameter.substitute_comp {n m p : Nat} (A : TypeParameter n)
    (σ : RawSub n m) (τ : RawSub m p) :
    (A.substitute σ).substitute τ = A.substitute (Telescope.comp σ τ) := by
  cases A with
  | mk level term => exact congrArg (TypeParameter.mk level) (Telescope.bind_compose σ τ term)

@[simp] theorem bind_universeTerm {n m : Nat} (σ : RawSub n m) (k : Nat) :
    bind σ (universeTerm k) = universeTerm k := rfl

@[simp] theorem substitute_universeType {n m : Nat} (σ : RawSub n m) (k : Nat) :
    (universeType n k).substitute σ = universeType m k := rfl

@[simp] theorem bind_universeCode {n m : Nat} (σ : RawSub n m) (k : Nat) :
    bind σ (universeType n k).code = (universeType m k).code := rfl

@[simp] theorem bind_app {n m : Nat} (σ : RawSub n m) (f a : RawTm n) :
    bind σ (app f a) = app (bind σ f) (bind σ a) := rfl

/-- The binder lift fixes the newest variable and reindexes older images. -/
def TermBody.substitute {n m : Nat} (σ : RawSub n m) : TermBody n → TermBody m
  | .bind body => .bind (Mettapedia.OSLF.Binding.bind (Telescope.lift σ) body)
  | .noBind body => .noBind (Mettapedia.OSLF.Binding.bind σ body)

def TypeBody.substitute {n m : Nat} (σ : RawSub n m) : TypeBody n → TypeBody m
  | .bind body => .bind (body.substitute (Telescope.lift σ))
  | .noBind body => .noBind (body.substitute σ)

@[simp] theorem TypeBody.level_substitute {n m : Nat}
    (σ : RawSub n m) (B : TypeBody n) : (B.substitute σ).level = B.level := by
  cases B <;> rfl

@[simp] theorem TermBody.lambda_substitute {n m : Nat}
    (σ : RawSub n m) (body : TermBody n) :
    (body.substitute σ).lambda = Mettapedia.OSLF.Binding.bind σ body.lambda := by
  cases body <;> rfl

@[simp] theorem TypeBody.pi_substitute {n m : Nat}
    (σ : RawSub n m) (A : TypeParameter n) (B : TypeBody n) :
    (B.substitute σ).pi (A.substitute σ) = Mettapedia.OSLF.Binding.bind σ (B.pi A) := by
  cases B <;> rfl

@[simp] theorem substitute_piType {n m : Nat}
    (σ : RawSub n m) (A : TypeParameter n) (B : TypeBody n) :
    (piType A B).substitute σ = piType (A.substitute σ) (B.substitute σ) := by
  cases B <;> rfl

/-- Opening a nonbinding abstraction weakens it, so this case uses naturality
of weakening rather than pretending the abstraction binds a variable. -/
theorem TermBody.open_substitute {n m : Nat} (σ : RawSub n m) (body : TermBody n) :
    (body.substitute σ).open = Mettapedia.OSLF.Binding.bind (Telescope.lift σ) body.open := by
  cases body with
  | bind body => rfl
  | noBind body =>
    change Mettapedia.OSLF.Binding.bind (Telescope.projection (S := sig) .term m)
      (Mettapedia.OSLF.Binding.bind σ body) =
      Mettapedia.OSLF.Binding.bind (Telescope.lift σ)
        (Mettapedia.OSLF.Binding.bind (Telescope.projection (S := sig) .term n) body)
    exact (Telescope.bind_projection (S := sig) (b := .term)
      (Mettapedia.OSLF.Binding.bind σ body)).trans
      ((Telescope.bind_lift_weaken σ body).symm.trans
        (congrArg (fun t : RawTm (n + 1) => Mettapedia.OSLF.Binding.bind (Telescope.lift σ) t)
          (Telescope.bind_projection (S := sig) (b := .term) body).symm))

theorem TypeParameter.weaken_substitute {n m : Nat} (σ : RawSub n m) (A : TypeParameter n) :
    (A.substitute σ).weaken = A.weaken.substitute (Telescope.lift σ) := by
  cases A with
  | mk level term =>
    apply congrArg (TypeParameter.mk level)
    change bind (Telescope.projection (S := sig) .term m) (bind σ term) =
      bind (Telescope.lift σ) (bind (Telescope.projection (S := sig) .term n) term)
    exact (Telescope.bind_projection (S := sig) (b := .term) (bind σ term)).trans
      ((Telescope.bind_lift_weaken σ term).symm.trans
        (congrArg (fun t : RawTm (n + 1) => bind (Telescope.lift σ) t)
          (Telescope.bind_projection (S := sig) (b := .term) term).symm))

theorem TypeBody.open_substitute {n m : Nat} (σ : RawSub n m) (B : TypeBody n) :
    (B.substitute σ).open = B.open.substitute (Telescope.lift σ) := by
  cases B with
  | bind body => rfl
  | noBind body => exact TypeParameter.weaken_substitute σ body

/-- Instantiation commutes with arbitrary ambient substitutions at every
signature sort, including the type codes used by dependent codomains. -/
theorem bind_single {n m : Nat} {s : sig.Srt} (σ : RawSub n m)
    (body : Term sig (Telescope.scope .term (n + 1)) s) (argument : RawTm n) :
    bind σ (bind (single argument) body) =
      bind (single (bind σ argument)) (bind (Telescope.lift σ) body) := by
  exact (congrArg (fun t => bind σ t) (Telescope.bind_pair_identity argument body)).trans
    ((ContextualLinearSubstitution.bind_inst σ body argument).trans
      (Telescope.bind_pair_identity (bind σ argument) (bind (Telescope.lift σ) body)).symm)

theorem TermBody.instantiate_substitute {n m : Nat} (σ : RawSub n m)
    (body : TermBody n) (argument : RawTm n) :
    (body.substitute σ).instantiate (Mettapedia.OSLF.Binding.bind σ argument) =
      Mettapedia.OSLF.Binding.bind σ (body.instantiate argument) := by
  unfold TermBody.instantiate
  rw [TermBody.open_substitute]
  exact (bind_single σ body.open argument).symm

theorem TypeBody.instantiate_substitute {n m : Nat} (σ : RawSub n m)
    (B : TypeBody n) (argument : RawTm n) :
    (B.substitute σ).instantiate (Mettapedia.OSLF.Binding.bind σ argument) =
      (B.instantiate argument).substitute σ := by
  unfold TypeBody.instantiate
  rw [TypeBody.open_substitute]
  change TypeParameter.mk B.open.level _ = TypeParameter.mk B.open.level _
  exact congrArg (TypeParameter.mk B.open.level) (bind_single σ B.open.term argument).symm

@[simp] theorem TermBody.substitute_identity {n : Nat} (body : TermBody n) :
    body.substitute (Telescope.identity (S := sig) .term n) = body := by
  cases body with
  | bind body =>
    exact congrArg TermBody.bind
      ((congrArg (fun σ => Mettapedia.OSLF.Binding.bind σ body)
        (Telescope.lift_identity (S := sig) .term n)).trans (Telescope.bind_identity body))
  | noBind body =>
    exact congrArg TermBody.noBind (Telescope.bind_identity body)

@[simp] theorem TypeBody.substitute_identity {n : Nat} (B : TypeBody n) :
    B.substitute (Telescope.identity (S := sig) .term n) = B := by
  cases B with
  | bind body =>
    exact congrArg TypeBody.bind
      ((congrArg (fun σ => body.substitute σ) (Telescope.lift_identity (S := sig) .term n)).trans
        (TypeParameter.substitute_identity body))
  | noBind body => exact congrArg TypeBody.noBind (TypeParameter.substitute_identity body)

theorem TermBody.substitute_comp {n m p : Nat} (body : TermBody n)
    (σ : RawSub n m) (τ : RawSub m p) :
    (body.substitute σ).substitute τ = body.substitute (Telescope.comp σ τ) := by
  cases body with
  | bind body =>
    exact congrArg TermBody.bind
      ((Telescope.bind_compose (Telescope.lift σ) (Telescope.lift τ) body).trans
        (congrArg (fun ρ => Mettapedia.OSLF.Binding.bind ρ body) (Telescope.lift_comp σ τ)))
  | noBind body => exact congrArg TermBody.noBind (Telescope.bind_compose σ τ body)

theorem TypeBody.substitute_comp {n m p : Nat} (B : TypeBody n)
    (σ : RawSub n m) (τ : RawSub m p) :
    (B.substitute σ).substitute τ = B.substitute (Telescope.comp σ τ) := by
  cases B with
  | bind body =>
    exact congrArg TypeBody.bind
      ((TypeParameter.substitute_comp body (Telescope.lift σ) (Telescope.lift τ)).trans
        (congrArg (fun ρ => body.substitute ρ) (Telescope.lift_comp σ τ)))
  | noBind body => exact congrArg TypeBody.noBind (TypeParameter.substitute_comp body σ τ)

/-- A free argument remains free after crossing the body's nested lambda. -/
theorem nested_capture_control :
    (TermBody.bind (lam (.var (.succ .zero))) : TermBody 1).instantiate (.var .zero) =
      lam (.var (.succ .zero)) := rfl

theorem nested_capture_negative :
    (TermBody.bind (lam (.var (.succ .zero))) : TermBody 1).instantiate (.var .zero) ≠
      lam (.var .zero) := by
  intro equality
  cases equality

/-- Dependent annotations change with their variable image; their level does not. -/
theorem dependent_annotation_control :
    (TypeParameter.mk 2 (.var .zero) : TypeParameter 1).substitute
        (single (universeTerm (n := 0) 1)) = ⟨2, universeTerm 1⟩ := rfl

end Mettapedia.Languages.Agda.Structural.Statics
