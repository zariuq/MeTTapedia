import Mettapedia.OSLF.Syntax.BindingSignatureABT

/-! # Checked readback into an intrinsic binding signature

The reader checks object-variable sorts, constructor result sorts, field
counts and every declared binder depth. It returns an existing intrinsic
term, not an untyped term accompanied by a trusted tag. Empty context/sort
fibres need no default inhabitant.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CommonABT

open Mettapedia.GSLT.LanguageDef

variable {S : Signature} [DecidableEq S.Srt]

def readVariable : (context : Ctx S) → (sort : S.Srt) → Nat → Option (Var context sort)
  | [], _, _ => none
  | first :: _, sort, 0 =>
      if same : first = sort then some (same ▸ Var.zero) else none
  | _ :: rest, sort, index + 1 => Var.succ <$> readVariable rest sort index

theorem readVariable_index {Γ : Ctx S} {sort : S.Srt} (position : Var Γ sort) :
    readVariable Γ sort (index position) = some position := by
  induction position with
  | zero => simp [index, readVariable]
  | succ previous earlier => simp [index, readVariable, earlier]

def castSort {Γ : Ctx S} {first second : S.Srt} (same : first = second)
    (term : Term S Γ first) : Term S Γ second := same ▸ term

omit [DecidableEq S.Srt] in
theorem lower_castSort {Γ : Ctx S} {first second : S.Srt} (same : first = second)
    (term : Term S Γ first) : lower (castSort same term) = lower term := by
  cases same
  rfl

mutual
  def read : SignatureIndexedABT.Term (Head S) → (Γ : Ctx S) → (sort : S.Srt) → Option (Term S Γ sort)
    | .idx index, Γ, sort => Term.var <$> readVariable Γ sort index
    | .node ⟨actualSort, operator⟩ fields, Γ, sort =>
        if same : actualSort = sort then
          (fun arguments => castSort same (.op operator arguments)) <$> readArgs fields Γ (S.arity operator)
        else none

  def readArgs : SignatureIndexedABT.Fields (Head S) → (Γ : Ctx S) →
      (arities : List (List S.Srt × S.Srt)) → Option (Args S arities Γ)
    | .nil, _, [] => some .nil
    | .cons depth child rest, Γ, (binders, sort) :: tail =>
        if depth = binders.length then do
          return .cons (← read child (binders ++ Γ) sort) (← readArgs rest Γ tail)
        else none
    | _, _, _ => none
end

mutual
  theorem read_lower {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
      read (lower term) Γ sort = some term := by
    match term with
    | .var position => simp only [lower, read, readVariable_index]; rfl
    | .op operator arguments =>
        simp only [lower, read, ↓reduceDIte, readArgs_lower arguments]
        rfl
    termination_by structural term

  theorem readArgs_lower {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : Args S arities Γ) : readArgs (lowerArgs arguments) Γ arities = some arguments := by
    match arguments with
    | .nil => rfl
    | .cons head tail =>
        simp only [lowerArgs, readArgs, ↓reduceIte, read_lower head, readArgs_lower tail]
        rfl
    termination_by structural arguments
end

theorem readVariable_reflects (Γ : Ctx S) (sort : S.Srt) (number : Nat)
    (position : Var Γ sort) (found : readVariable Γ sort number = some position) : index position = number := by
  induction Γ generalizing number with
  | nil => simp [readVariable] at found
  | cons first rest earlier =>
      cases number with
      | zero =>
          by_cases same : first = sort
          · subst sort
            have returned : Var.zero = position := by simpa [readVariable] using found
            subst position
            rfl
          · simp [readVariable, same] at found
      | succ number =>
          cases previous : readVariable rest sort number with
          | none => simp [readVariable, previous] at found
          | some previousPosition =>
              have returned : Var.succ previousPosition = position := by simpa [readVariable, previous] using found
              subst position
              exact congrArg Nat.succ (earlier number previousPosition previous)

mutual
  theorem lower_of_read (tree : SignatureIndexedABT.Term (Head S)) (Γ : Ctx S) (sort : S.Srt)
      (value : Term S Γ sort) (found : read tree Γ sort = some value) : lower value = tree := by
    match tree with
    | .idx number =>
        cases lookup : readVariable Γ sort number with
        | none => simp [read, lookup] at found
        | some position =>
            have returned : Term.var position = value := by simpa [read, lookup] using found
            subst value
            exact congrArg SignatureIndexedABT.Term.idx (readVariable_reflects Γ sort number position lookup)
    | .node ⟨actualSort, operator⟩ fields =>
        by_cases same : actualSort = sort
        · subst sort
          cases arguments : readArgs fields Γ (S.arity operator) with
          | none => simp [read, arguments] at found
          | some values =>
              have returned : Term.op operator values = value := by
                simpa [read, arguments, castSort] using found
              subst value
              exact congrArg (SignatureIndexedABT.Term.node ⟨actualSort, operator⟩)
                (lowerArgs_of_read fields Γ (S.arity operator) values arguments)
        · simp [read, same] at found
    termination_by structural tree

  theorem lowerArgs_of_read (fields : SignatureIndexedABT.Fields (Head S)) (Γ : Ctx S)
      (arities : List (List S.Srt × S.Srt)) (values : Args S arities Γ)
      (found : readArgs fields Γ arities = some values) : lowerArgs values = fields := by
    match fields with
    | .nil =>
        cases arities with
        | nil =>
            have returned : Args.nil = values := Option.some.inj found
            subst values
            rfl
        | cons => simp [readArgs] at found
    | .cons depth child rest =>
        cases arities with
        | nil => simp [readArgs] at found
        | cons declaration tail =>
            rcases declaration with ⟨binders, sort⟩
            by_cases same : depth = binders.length
            · cases headRead : read child (binders ++ Γ) sort with
              | none => simp [readArgs, same, headRead] at found
              | some head =>
                  cases tailRead : readArgs rest Γ tail with
                  | none => simp [readArgs, same, headRead, tailRead] at found
                  | some others =>
                      have returned : Args.cons head others = values := by
                        simpa [readArgs, same, headRead, tailRead] using found
                      subst values
                      simp only [lowerArgs, lower_of_read child (binders ++ Γ) sort head headRead,
                        lowerArgs_of_read rest Γ tail others tailRead, same]
            · simp [readArgs, same] at found
    termination_by structural fields
end

theorem read_eq_some_iff (tree : SignatureIndexedABT.Term (Head S)) (Γ : Ctx S) (sort : S.Srt)
    (value : Term S Γ sort) : read tree Γ sort = some value ↔ lower value = tree := by
  refine ⟨lower_of_read tree Γ sort value, ?_⟩
  intro same
  rw [← same, read_lower]

theorem empty_fibre_refused (Γ : Ctx S) (sort : S.Srt) [IsEmpty (Term S Γ sort)]
    (tree : SignatureIndexedABT.Term (Head S)) : read tree Γ sort = none := by
  cases result : read tree Γ sort with
  | none => rfl
  | some value => exact isEmptyElim value

namespace Controls

inductive Op : Bool → Type where
  | unit : Op false
  | use : Op false
  | binder : Op false

def signature : Signature where
  Srt := Bool
  Op := Op
  arity := fun {sort} operator => match sort, operator with
    | false, .unit => []
    | false, .use => [([], true)]
    | false, .binder => [([true], false)]

instance : DecidableEq signature.Srt := inferInstanceAs (DecidableEq Bool)

def closed : Term signature [] false :=
  .op .binder (.cons (.op .use (.cons (.var .zero) .nil)) .nil)

theorem typed_binder_reads : read (lower closed) [] false = some closed := read_lower closed

theorem right_depth_wrong_sort_refused :
    read (S := signature) (.idx 0) [false] true = none := rfl

theorem wrong_constructor_sort_refused :
    read (S := signature) (.node ⟨false, .unit⟩ .nil) [] true = none := rfl

theorem wrong_binder_depth_refused :
    read (S := signature) (.node ⟨false, .binder⟩
      (.cons 0 (.node ⟨false, .unit⟩ .nil) .nil)) [] false = none := rfl

theorem extra_field_refused :
    read (S := signature) (.node ⟨false, .unit⟩
      (.cons 0 (.node ⟨false, .unit⟩ .nil) .nil)) [] false = none := rfl

instance : IsEmpty (Term signature [] true) where
  false term := by
    cases term with
    | var position => cases position
    | op operator arguments => cases operator

theorem actual_empty_fibre_refused (tree : SignatureIndexedABT.Term (Head signature)) :
    read tree [] true = none := empty_fibre_refused [] true tree

end Controls

#print axioms read_lower
#print axioms read_eq_some_iff
#print axioms Controls.actual_empty_fibre_refused

end Mettapedia.OSLF.Binding.CommonABT
