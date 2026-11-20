import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics

/-!
# Primitive services for evaluating the source calculus

The solver decides source judgements. The space service presents
ordered occurrences over a bag and specifies the change to that bag
for insertion and one-copy erasure. The evaluator can use any
representation with these laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}

/-- A successful search carries a witness. Its empty case is evidence
that the requested source judgement has no witness. -/
inductive SearchAnswer {A : Type} (predicate : A → Prop) where
  | found (value : A) (valid : predicate value)
  | absent (missing : ∀ value, ¬ predicate value)

inductive FirstOccurrence {A : Type} (test : A → Bool) (items : List A) where
  | found (before : List A) (item : A) (after : List A)
      (split : items = before ++ item :: after) (accepted : test item = true)
  | absent (missing : ∀ item ∈ items, test item = false)

def findFirst {A : Type} (test : A → Bool) : (items : List A) → FirstOccurrence test items
  | [] => .absent (by simp)
  | item :: rest =>
    if good : test item = true then .found [] item rest rfl good
    else match findFirst test rest with
    | .found before matching after split yes =>
      .found (item :: before) matching after (congrArg (List.cons item) split) yes
    | .absent missing =>
      .absent (fun other member => by
        rcases List.mem_cons.mp member with rfl | later
        · exact Bool.eq_false_iff.mpr good
        · exact missing other later)


structure Solver (κ : Keys S) (Γ : Ctx S) (star : S.Srt) where
  live : (knowledge : List (Constraint κ Γ star)) → Decidable (Solvable knowledge)
  address : (knowledge : List (Constraint κ Γ star)) → (datum : Data κ Γ star) →
    SearchAnswer (Determines knowledge datum)
  principal : (knowledge : List (Constraint κ Γ star)) → SearchAnswer (Principal knowledge)
  entails : (knowledge : List (Constraint κ Γ star)) → (left right : Data κ Γ star) →
    Decidable (EntailsEq knowledge left right)

def Solver.satisfiable (solver : Solver κ Γ star) (knowledge : List (Constraint κ Γ star)) : Bool :=
  @decide (Solvable knowledge) (solver.live knowledge)

theorem Solver.satisfiable_iff (solver : Solver κ Γ star) (knowledge : List (Constraint κ Γ star)) :
    solver.satisfiable knowledge = true ↔ Solvable knowledge := by
  exact Iff.of_eq (@decide_eq_true_eq _ (solver.live knowledge))

def Solver.impliesEquality (solver : Solver κ Γ star)
    (knowledge : List (Constraint κ Γ star)) (left right : Data κ Γ star) : Bool :=
  @decide (EntailsEq knowledge left right) (solver.entails knowledge left right)

theorem Solver.impliesEquality_iff (solver : Solver κ Γ star)
    (knowledge : List (Constraint κ Γ star)) (left right : Data κ Γ star) :
    solver.impliesEquality knowledge left right = true ↔ EntailsEq knowledge left right := by
  exact Iff.of_eq (@decide_eq_true_eq _ (solver.entails knowledge left right))

structure TypeChecks (κ : Keys S) {Γ : Ctx S} {star : S.Srt} (D : Discipline S Γ star) where
  admits : (knowledge : List (Constraint κ Γ star)) → (datum : Data κ Γ star) → (kind : D.Ty) →
    Decidable (∀ term, Reads knowledge datum term → D.admits kind term)
  refuses : (knowledge : List (Constraint κ Γ star)) → (datum : Data κ Γ star) → (kind : D.Ty) →
    Decidable (∀ term, Reads knowledge datum term → ¬ D.admits kind term)

structure Spaces (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Storage : Type) where
  view : Storage → Term S Γ star → Multiset (Row κ Γ star)
  rows : Storage → Term S Γ star → List (Row κ Γ star)
  rows_exact : ∀ storage handle, (rows storage handle : Multiset _) = view storage handle
  insert : Storage → Term S Γ star → Row κ Γ star → Storage
  insert_exact : ∀ storage handle row,
    view (insert storage handle row) = setSpace (view storage) handle (view storage handle + {row})
  erase : Storage → Term S Γ star → (Row κ Γ star → Bool) → Option (Row κ Γ star × Storage)
  erase_exact : ∀ storage handle accepts,
    match erase storage handle accepts with
    | none => ∀ row ∈ view storage handle, accepts row = false
    | some (row, next) => accepts row = true ∧
        ∃ rest, view storage handle = row ::ₘ rest ∧
          view next = setSpace (view storage) handle rest

/-- Fresh source scopes and handles accompany whichever space representation
the evaluator uses. The representation of row data belongs to the service. -/
structure ExecutionWorld (Storage : Type) where
  scope : Nat
  handles : Nat
  storage : Storage

namespace ExecutionWorld

variable {Storage : Type}

def source (spaces : Spaces κ Γ star Storage) (world : ExecutionWorld Storage) : World κ Γ star :=
  ⟨world.scope, world.handles, spaces.view world.storage⟩

def fresh (world : ExecutionWorld Storage) : ExecutionWorld Storage :=
  {world with scope := world.scope + 1}

def allocate (world : ExecutionWorld Storage) : ExecutionWorld Storage :=
  {world.fresh with handles := world.handles + 1}

@[simp] theorem source_fresh (spaces : Spaces κ Γ star Storage) (world : ExecutionWorld Storage) :
    world.fresh.source spaces = (world.source spaces).fresh := rfl

end ExecutionWorld

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation
