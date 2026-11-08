import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorage

/-!
# Space constructors over the existing binding syntax

Names and placement are rigid constructors. The original signature retains
all of its sorts, operators and binding arities. Contextual metavariables
remain the outer declaration family. Renaming space names acts through
object binders and commutes with contextual assignment and schema opening.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

inductive SpaceOperator (Name : Type) where
  | name : Name → SpaceOperator Name
  | place : SpaceOperator Name
  deriving DecidableEq

def spaceDeclaration (S : Signature) (point : S.Srt) {Name : Type} : SpaceOperator Name → MetaArity S
  | .name _ => ([],point)
  | .place => ([point,point],point)

abbrev base (S : Signature) (point : S.Srt) (Name : Type) := signature S (spaceDeclaration S point (Name := Name))

variable {S : Signature} {point : S.Srt} {Name V W : Type}
    {decl : V → MetaArity (base S point Name)} {next : W → MetaArity (base S point Name)}

def name {Γ : Ctx S} (value : Name) : Term (signature (base S point Name) decl) Γ point :=
  .op (.inl (.inr (Operator.mk (declaration := spaceDeclaration S point) (SpaceOperator.name value)))) .nil

def place {Γ : Ctx S} (address payload : Term (signature (base S point Name) decl) Γ point) :
    Term (signature (base S point Name) decl) Γ point :=
  .op (.inl (.inr (Operator.mk (declaration := spaceDeclaration S point) (SpaceOperator.place (Name := Name)))))
    (.cons address (.cons payload .nil))

mutual

def mapNames (change : Name → Name) : ∀ {Γ : Ctx S} {sort : S.Srt},
    Term (signature (base S point Name) decl) Γ sort → Term (signature (base S point Name) decl) Γ sort
  | _,_,.var position => .var position
  | _,_,.op (.inl (.inl operator)) arguments => .op (.inl (.inl operator)) (mapNamesArgs change arguments)
  | _,_,.op (.inl (.inr (.mk (SpaceOperator.name value)))) .nil => name (change value)
  | _,_,.op (.inl (.inr (.mk (SpaceOperator.place)))) (.cons address (.cons payload .nil)) =>
      place (mapNames change address) (mapNames change payload)
  | _,_,.op (.inr operator) arguments => .op (.inr operator) (mapNamesArgs change arguments)

def mapNamesArgs (change : Name → Name) : ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S},
    Args (signature (base S point Name) decl) arities Γ → Args (signature (base S point Name) decl) arities Γ
  | _,_,.nil => .nil
  | _,_,.cons head tail => .cons (mapNames change head) (mapNamesArgs change tail)

end

mutual

theorem mapNames_rename (change : Name → Name) {Γ Δ : Ctx S}
    (ren : Ren (signature (base S point Name) decl) Γ Δ) :
    ∀ {sort : S.Srt} (term : Term (signature (base S point Name) decl) Γ sort),
      mapNames change (rename ren term) = rename ren (mapNames change term)
  | _,.var _ => rfl
  | _,.op (.inl (.inl operator)) arguments => congrArg (Term.op (S := signature (base S point Name) decl) (.inl (.inl operator))) (mapNamesArgs_rename change ren arguments)
  | _,.op (.inl (.inr (.mk (SpaceOperator.name value)))) .nil => rfl
  | _,.op (.inl (.inr (.mk (SpaceOperator.place)))) (.cons address (.cons payload .nil)) => by
      exact congrArg₂ place (mapNames_rename change ren address) (mapNames_rename change ren payload)
  | _,.op (.inr operator) arguments => congrArg (Term.op (S := signature (base S point Name) decl) (.inr operator)) (mapNamesArgs_rename change ren arguments)

theorem mapNamesArgs_rename (change : Name → Name) {Γ Δ : Ctx S}
    (ren : Ren (signature (base S point Name) decl) Γ Δ) :
    ∀ {arities : List (List S.Srt × S.Srt)} (arguments : Args (signature (base S point Name) decl) arities Γ),
      mapNamesArgs change (renameArgs ren arguments) = renameArgs ren (mapNamesArgs change arguments)
  | _,.nil => rfl
  | _,.cons (bs := binders) head tail => congrArg₂ Args.cons
      (mapNames_rename change (liftRen ren binders) head) (mapNamesArgs_rename change ren tail)

end

theorem mapNames_liftSub (change : Name → Name) {Γ Δ : Ctx S}
    (environment : Sub (signature (base S point Name) decl) Γ Δ) :
    ∀ (binders : Ctx S) (sort : S.Srt) (position : Var (binders ++ Γ) sort),
      mapNames change (liftSub environment binders sort position) =
        liftSub (fun sort position => mapNames change (environment sort position)) binders sort position
  | [],_,_ => rfl
  | _ :: _,_,.zero => rfl
  | _ :: binders,sort,.succ position => by
      simp only [liftSub,weaken,mapNames_rename,mapNames_liftSub change environment binders sort position]

mutual

theorem mapNames_bind (change : Name → Name) {Γ Δ : Ctx S}
    (environment : Sub (signature (base S point Name) decl) Γ Δ) :
    ∀ {sort : S.Srt} (term : Term (signature (base S point Name) decl) Γ sort),
      mapNames change (bind environment term) =
        bind (fun sort position => mapNames change (environment sort position)) (mapNames change term)
  | _,.var _ => rfl
  | _,.op (.inl (.inl operator)) arguments => congrArg (Term.op (S := signature (base S point Name) decl) (.inl (.inl operator))) (mapNamesArgs_bind change environment arguments)
  | _,.op (.inl (.inr (.mk (SpaceOperator.name value)))) .nil => rfl
  | _,.op (.inl (.inr (.mk (SpaceOperator.place)))) (.cons address (.cons payload .nil)) =>
      congrArg₂ place (mapNames_bind change environment address) (mapNames_bind change environment payload)
  | _,.op (.inr operator) arguments => congrArg (Term.op (S := signature (base S point Name) decl) (.inr operator)) (mapNamesArgs_bind change environment arguments)

theorem mapNamesArgs_bind (change : Name → Name) {Γ Δ : Ctx S}
    (environment : Sub (signature (base S point Name) decl) Γ Δ) :
    ∀ {arities : List (List S.Srt × S.Srt)} (arguments : Args (signature (base S point Name) decl) arities Γ),
      mapNamesArgs change (bindArgs environment arguments) =
        bindArgs (fun sort position => mapNames change (environment sort position)) (mapNamesArgs change arguments)
  | _,.nil => rfl
  | _,.cons (bs := binders) head tail => by
      have lifted : (fun sort position => mapNames change (liftSub environment binders sort position)) =
          liftSub (fun sort position => mapNames change (environment sort position)) binders := by
        funext sort position
        exact mapNames_liftSub change environment binders sort position
      simp only [bindArgs,mapNamesArgs,mapNames_bind,mapNamesArgs_bind,lifted]

end

theorem mapNames_selfArgs (change : Name → Name) : ∀ (parameters : Ctx S),
    mapNamesArgs (decl := decl) change (selfArgs (T := signature (base S point Name) decl) parameters) = selfArgs (T := signature (base S point Name) decl) parameters
  | [] => rfl
  | _ :: rest => by
      simp only [selfArgs,mapNamesArgs,mapNames,mapNamesArgs_rename,mapNames_selfArgs change rest]

theorem mapNames_generator (change : Name → Name) (identity : V) :
    mapNames change (generator decl identity) = generator decl identity := by
  simp only [generator,mapNames,mapNames_selfArgs]

theorem mapNames_argsToSub (change : Name → Name) :
    ∀ (parameters : Ctx S) {Γ : Ctx S}
      (arguments : Args (signature (base S point Name) decl) (parameters.map (fun sort => ([],sort))) Γ)
      (sort : S.Srt) (position : Var parameters sort),
      mapNames change (argsToSub arguments sort position) = argsToSub (mapNamesArgs change arguments) sort position
  | [],_,_,_,position => nomatch position
  | _ :: _,_,.cons _ _,_,.zero => rfl
  | _ :: rest,_,.cons _ tail,sort,.succ position => mapNames_argsToSub change rest tail sort position

mutual

theorem mapNames_instantiate (change : Name → Name) (assignment : Assignment decl next) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature (base S point Name) decl) Γ sort),
      mapNames change (instantiate assignment term) =
        instantiate (fun identity => mapNames change (assignment identity)) (mapNames change term)
  | _,_,.var _ => rfl
  | _,_,.op (.inl (.inl operator)) arguments => congrArg (Term.op (S := signature (base S point Name) next) (.inl (.inl operator))) (mapNamesArgs_instantiate change assignment arguments)
  | _,_,.op (.inl (.inr (.mk (SpaceOperator.name value)))) .nil => rfl
  | _,_,.op (.inl (.inr (.mk (SpaceOperator.place)))) (.cons address (.cons payload .nil)) =>
      congrArg₂ place (mapNames_instantiate change assignment address) (mapNames_instantiate change assignment payload)
  | _,_,.op (.inr (.mk identity)) arguments => by
      simp only [instantiate,mapNames]
      rw [mapNames_bind]
      rw [← mapNamesArgs_instantiate]
      congr 1
      funext sort position
      exact mapNames_argsToSub (S := S) (decl := next) change (decl identity).1
        (instantiateArgs assignment arguments) sort position

theorem mapNamesArgs_instantiate (change : Name → Name) (assignment : Assignment decl next) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : Args (signature (base S point Name) decl) arities Γ),
      mapNamesArgs change (instantiateArgs assignment arguments) =
        instantiateArgs (fun identity => mapNames change (assignment identity)) (mapNamesArgs change arguments)
  | _,_,.nil => rfl
  | _,_,.cons head tail => congrArg₂ Args.cons
      (mapNames_instantiate change assignment head) (mapNamesArgs_instantiate change assignment tail)

end

def Row.mapNames {Local Shared : Type} {locals : Local → MetaArity (base S point Name)}
    {captures : Shared → MetaArity (base S point Name)} (change : Name → Name)
    {Γ : Ctx S} {sort : S.Srt} :
    ContextualStoredRows.Row locals captures Γ sort → ContextualStoredRows.Row locals captures Γ sort
  | .schema body => .schema (SchematicReach.mapNames change body)
  | .shared value => .shared (SchematicReach.mapNames change value)

theorem mapNames_view {Local Shared : Type} (locals : Local → MetaArity (base S point Name))
    (captures : Shared → MetaArity (base S point Name)) (change : Name → Name) (scope : Nat)
    {Γ : Ctx S} {sort : S.Srt} (row : ContextualStoredRows.Row locals captures Γ sort) :
    mapNames change (ContextualStoredRows.viewAt locals captures scope row) =
      ContextualStoredRows.viewAt locals captures scope (Row.mapNames change row) := by
  cases row with
  | schema body =>
      dsimp only [ContextualStoredRows.viewAt,ContextualFreshening.termAt,Row.mapNames]
      rw [mapNames_instantiate]
      congr 1
      funext identity
      cases identity <;> exact mapNames_generator change _
  | shared value =>
      dsimp only [ContextualStoredRows.viewAt,Row.mapNames]
      rw [mapNames_instantiate]
      congr 1
      funext identity
      exact mapNames_generator change _

private def readName {Γ : Ctx S} : ∀ {sort : S.Srt},
    Term (signature (base S point Name) decl) Γ sort → Option Name
  | _,.op (.inl (.inr (.mk (SpaceOperator.name value)))) .nil => some value
  | _,_ => none

theorem name_injective {Γ : Ctx S} : Function.Injective (name (decl := decl) (Γ := Γ)) :=
  fun _ _ same => Option.some.inj (congrArg readName same)

private def readPlace {Γ : Ctx S} : ∀ {sort : S.Srt},
    Term (signature (base S point Name) decl) Γ sort →
      Option (Term (signature (base S point Name) decl) Γ point ×
        Term (signature (base S point Name) decl) Γ point)
  | _,.op (.inl (.inr (.mk SpaceOperator.place))) (.cons address (.cons payload .nil)) =>
      some (address,payload)
  | _,_ => none

theorem place_injective {Γ : Ctx S}
    {a p b q : Term (signature (base S point Name) decl) Γ point} (same : place a p = place b q) :
    a = b ∧ p = q := by
  have pair := Option.some.inj (congrArg readPlace same)
  exact ⟨congrArg Prod.fst pair,congrArg Prod.snd pair⟩

theorem instantiate_name (assignment : Assignment decl next) {Γ : Ctx S} (value : Name) :
    instantiate assignment (name value : Term (signature (base S point Name) decl) Γ point) =
      name value := rfl

theorem instantiate_place (assignment : Assignment decl next) {Γ : Ctx S}
    (address payload : Term (signature (base S point Name) decl) Γ point) :
    instantiate assignment (place address payload) =
      place (instantiate assignment address) (instantiate assignment payload) := rfl

def locatedRow {Local Shared : Type} (locals : Local → MetaArity (base S point Name))
    (captures : Shared → MetaArity (base S point Name)) {Γ : Ctx S}
    (address : Term (signature (base S point Name) captures) Γ point) :
    ContextualStoredRows.Row locals captures Γ point → ContextualStoredRows.Row locals captures Γ point
  | .schema body => .schema (place (instantiate (ContextualSelectionViews.capturedSource locals captures) address) body)
  | .shared value => .shared (place address value)

theorem view_locatedRow {Local Shared : Type} (locals : Local → MetaArity (base S point Name))
    (captures : Shared → MetaArity (base S point Name)) {Γ : Ctx S} (scope : Nat)
    (address : Term (signature (base S point Name) captures) Γ point)
    (row : ContextualStoredRows.Row locals captures Γ point) :
    ContextualStoredRows.viewAt locals captures scope (locatedRow locals captures address row) =
      place (instantiate (ContextualSelectionViews.capturedTarget locals captures) address)
        (ContextualStoredRows.viewAt locals captures scope row) := by
  cases row with
  | shared value => rfl
  | schema body =>
      dsimp only [locatedRow,ContextualStoredRows.viewAt,ContextualFreshening.termAt]
      rw [instantiate_place,instantiate_comp]
      congr 1
      apply congrArg (fun assignment => instantiate assignment address)
      funext identity
      exact instantiate_generator (ContextualFreshening.assignment locals captures scope) (.inr identity)

theorem name_ren_is_nontrivial {a b : Name} (different : a ≠ b) :
    mapNames (decl := decl) (fun _ => b) (name a : Term (signature (base S point Name) decl) [] point) ≠ name a := by
  intro same
  exact different (name_injective same).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach
