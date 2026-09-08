import Mettapedia.Logic.HOL.Syntax.Subst

/-!
# Partial renaming and typed strengthening

A partial renaming removes variables only when they are unused. Successful
renaming is inverted by any total variable map that inverts its successful
lookups. The construction acts on the existing intrinsic syntax and lifts under
every binder; it does not forget types or recover them through untyped equality.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ : Ctx Base} {τ σ : Ty Base}

/-- Type-preserving variable maps which may leave a source variable unavailable. -/
abbrev PartialRename (Base : Type u) (Γ Δ : Ctx Base) :=
  ∀ {τ}, Var Γ τ → Option (Var Δ τ)

namespace PartialRename

def lift (ρ : PartialRename Base Γ Δ) : PartialRename Base (σ :: Γ) (σ :: Δ)
  | _, .vz => some .vz
  | _, .vs v => (ρ v).map Var.vs

/-- Remove the newest context entry, failing precisely at that variable. -/
def drop : PartialRename Base (σ :: Γ) Γ
  | _, .vz => none
  | _, .vs v => some v

theorem lift_inverse {ρ : PartialRename Base Γ Δ} {ι : Rename Base Δ Γ}
    (inverse : ∀ {a} (source : Var Γ a) (target : Var Δ a),
      ρ source = some target → ι target = source) :
    ∀ {a} (source : Var (σ :: Γ) a) (target : Var (σ :: Δ) a),
      lift ρ source = some target → Rename.lift ι target = source := by
  intro a source target success
  cases source with
  | vz => cases success; rfl
  | vs v =>
      cases renamed : ρ v with
      | none => simp [lift, renamed] at success
      | some result =>
          simp only [lift, renamed, Option.map_some, Option.some.injEq] at success
          subst target
          exact congrArg Var.vs (inverse v result renamed)

theorem drop_inverse (source : Var (σ :: Γ) τ) (target : Var Γ τ)
    (success : drop source = some target) : Rename.weaken target = source := by
  cases source with
  | vz => cases success
  | vs v => cases success; rfl

end PartialRename

/-- Rename every variable, failing if an encountered variable is unavailable. -/
def rename? : {Γ Δ : Ctx Base} → PartialRename Base Γ Δ →
    {τ : Ty Base} → Term Const Γ τ → Option (Term Const Δ τ)
  | _, _, ρ, _, .var v => (ρ v).map Term.var
  | _, _, _, _, .const constant => some (.const constant)
  | _, _, ρ, _, .app function argument =>
      do return .app (← rename? ρ function) (← rename? ρ argument)
  | _, _, ρ, _, .lam body => (rename? (PartialRename.lift ρ) body).map Term.lam
  | _, _, _, _, .top => some .top
  | _, _, _, _, .bot => some .bot
  | _, _, ρ, _, .and left right => do return .and (← rename? ρ left) (← rename? ρ right)
  | _, _, ρ, _, .or left right => do return .or (← rename? ρ left) (← rename? ρ right)
  | _, _, ρ, _, .imp left right => do return .imp (← rename? ρ left) (← rename? ρ right)
  | _, _, ρ, _, .not body => (rename? ρ body).map Term.not
  | _, _, ρ, _, .eq left right => do return .eq (← rename? ρ left) (← rename? ρ right)
  | _, _, ρ, _, .all body => (rename? (PartialRename.lift ρ) body).map Term.all
  | _, _, ρ, _, .ex body => (rename? (PartialRename.lift ρ) body).map Term.ex

/-- A variable-level partial inverse lifts to a syntactic inverse on all
successful term traversals, including below binders. -/
theorem rename_of_rename?_eq_some (term : Term Const Γ τ)
    {ρ : PartialRename Base Γ Δ} {ι : Rename Base Δ Γ}
    (inverse : ∀ {a} (source : Var Γ a) (target : Var Δ a),
      ρ source = some target → ι target = source)
    {result : Term Const Δ τ} (success : rename? ρ term = some result) :
    rename ι result = term := by
  induction term generalizing Δ with
  | var v =>
      cases renamed : ρ v with
      | none => simp [rename?, renamed] at success
      | some target =>
          simp only [rename?, renamed, Option.map_some, Option.some.injEq] at success
          subst result
          exact congrArg Term.var (inverse v target renamed)
  | const constant | top | bot => cases success; rfl
  | app left right ihl ihr | and left right ihl ihr | or left right ihl ihr
  | imp left right ihl ihr | eq left right ihl ihr =>
      cases renamedLeft : rename? ρ left <;> cases renamedRight : rename? ρ right <;>
        simp_all [rename?]
      all_goals
        subst result
        simp only [rename, ihl inverse renamedLeft, ihr inverse renamedRight]
  | not body ih =>
      cases renamed : rename? ρ body <;> simp_all [rename?]
      subst result
      simp only [rename, ih inverse renamed]
  | lam body ih | all body ih | ex body ih =>
      cases renamed : rename? (PartialRename.lift ρ) body with
      | none => simp [rename?, renamed] at success
      | some lowered =>
          simp only [rename?, renamed, Option.map_some, Option.some.injEq] at success
          subst result
          simp only [rename]
          rw [ih (PartialRename.lift_inverse inverse) renamed]

/-- Successful removal of the newest variable is reversed by ordinary weakening. -/
theorem weaken_of_rename?_drop {term : Term Const (σ :: Γ) τ} {lowered : Term Const Γ τ}
    (success : rename? PartialRename.drop term = some lowered) : weaken lowered = term :=
  rename_of_rename?_eq_some term PartialRename.drop_inverse success

namespace PartialRenamingExamples

def independent : Term (fun _ : Ty Unit => Empty) [.prop, .prop] .prop :=
  .var (.vs .vz)

theorem unused_variable_removed :
    rename? PartialRename.drop independent = some (.var .vz) := rfl

theorem used_variable_rejected :
    rename? PartialRename.drop
      (.var .vz : Term (fun _ : Ty Unit => Empty) [.prop, .prop] .prop) = none := rfl

theorem bound_variable_retained :
    rename? PartialRename.drop
      (.lam (.var .vz) : Term (fun _ : Ty Unit => Empty) [.prop] (.arr .prop .prop)) =
      some (.lam (.var .vz)) := rfl

end PartialRenamingExamples

#print axioms rename_of_rename?_eq_some
#print axioms weaken_of_rename?_drop

end Mettapedia.Logic.HOL
