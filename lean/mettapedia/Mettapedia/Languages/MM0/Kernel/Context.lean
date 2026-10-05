import Mettapedia.Languages.MM0.Kernel.Support

/-!
# Ordered MM0 contexts

Each binder is admitted against the preceding context. Bound variables cannot
have strict sorts. A regular variable's dependencies must name preceding
bound variables. Sort purity and provability constrain declarations and
theorem judgments elsewhere; the free-sort restriction on newly introduced
dummies is likewise separate from admission of named parameters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

structure SortInfo where
  pure : Bool := false
  strict : Bool := false
  provable : Bool := false
  free : Bool := false
  deriving DecidableEq, Repr

abbrev SortSignature := Nat → Option SortInfo

namespace Context

def isBound (context : Context) (index : Nat) : Bool :=
  match context[index]? with
  | some (.bound _) => true
  | _ => false

theorem isBound_iff (context : Context) (index : Nat) :
    isBound context index = true ↔ ∃ sort, context[index]? = some (.bound sort) := by
  unfold isBound
  cases lookup : context[index]? with
  | none => simp
  | some binder => cases binder <;> simp

inductive AdmitsBinder (sorts : SortSignature) (initial : Context) : Binder → Prop where
  | bound {sort : Nat} {info : SortInfo} :
      sorts sort = some info → info.strict = false → AdmitsBinder sorts initial (.bound sort)
  | regular {sort : Nat} {info : SortInfo} {dependencies : Finset Nat} :
      sorts sort = some info →
      (∀ index ∈ dependencies, ∃ boundSort, initial[index]? = some (.bound boundSort)) →
      AdmitsBinder sorts initial (.regular sort dependencies)

def checkBinder (sorts : SortSignature) (initial : Context) : Binder → Bool
  | .bound sort =>
      match sorts sort with
      | none => false
      | some info => !info.strict
  | .regular sort dependencies =>
      match sorts sort with
      | none => false
      | some _ => decide (∀ index ∈ dependencies, isBound initial index = true)

theorem checkBinder_iff (sorts : SortSignature) (initial : Context) (binder : Binder) :
    checkBinder sorts initial binder = true ↔ AdmitsBinder sorts initial binder := by
  cases binder with
  | bound sort =>
      cases lookup : sorts sort with
      | none =>
          constructor
          · simp [checkBinder, lookup]
          · intro admitted; cases admitted with
            | bound known _ => simp [lookup] at known
      | some info =>
          constructor
          · intro checked
            exact .bound lookup (by simpa [checkBinder, lookup] using checked)
          · intro admitted
            cases admitted with
            | bound known notStrict =>
                have same := Option.some.inj (lookup.symm.trans known)
                subst same
                simpa [checkBinder, lookup] using notStrict
  | regular sort dependencies =>
      cases lookup : sorts sort with
      | none =>
          constructor
          · simp [checkBinder, lookup]
          · intro admitted; cases admitted with
            | regular known _ => simp [lookup] at known
      | some info =>
          constructor
          · intro checked
            apply AdmitsBinder.regular lookup
            simpa [checkBinder, lookup, isBound_iff] using checked
          · intro admitted
            cases admitted with
            | regular _ boundDependencies =>
                simpa [checkBinder, lookup, isBound_iff] using boundDependencies

/-- Appending binders checks each declaration in its actual preceding scope. -/
inductive Extension (sorts : SortSignature) : Context → Context → Prop where
  | nil (initial : Context) : Extension sorts initial []
  | cons {initial : Context} {binder : Binder} {remaining : Context} :
      AdmitsBinder sorts initial binder →
      Extension sorts (initial ++ [binder]) remaining →
      Extension sorts initial (binder :: remaining)

def checkFrom (sorts : SortSignature) : Context → Context → Bool
  | _, [] => true
  | initial, binder :: remaining =>
      checkBinder sorts initial binder && checkFrom sorts (initial ++ [binder]) remaining

theorem checkFrom_iff (sorts : SortSignature) (initial remaining : Context) :
    checkFrom sorts initial remaining = true ↔ Extension sorts initial remaining := by
  induction remaining generalizing initial with
  | nil => exact ⟨fun _ => .nil initial, fun _ => rfl⟩
  | cons binder remaining ih =>
      simp only [checkFrom, Bool.and_eq_true, checkBinder_iff, ih]
      constructor
      · rintro ⟨admitted, tail⟩; exact .cons admitted tail
      · intro extension; cases extension with
        | cons admitted tail => exact ⟨admitted, tail⟩

def WellFormed (sorts : SortSignature) (context : Context) : Prop := Extension sorts [] context

def check (sorts : SortSignature) (context : Context) : Bool := checkFrom sorts [] context

theorem check_iff (sorts : SortSignature) (context : Context) :
    check sorts context = true ↔ WellFormed sorts context := checkFrom_iff sorts [] context

theorem checkFrom_append (sorts : SortSignature) (initial first second : Context) :
    checkFrom sorts initial (first ++ second) =
      (checkFrom sorts initial first && checkFrom sorts (initial ++ first) second) := by
  induction first generalizing initial with
  | nil => simp [checkFrom]
  | cons binder remaining ih =>
      simp only [List.cons_append, checkFrom, ih, Bool.and_assoc]
      simp only [List.append_assoc, List.singleton_append]

/-- Independently admitted pieces compose only at the matching extended context. -/
theorem extension_append_iff (sorts : SortSignature) (initial first second : Context) :
    Extension sorts initial (first ++ second) ↔
      Extension sorts initial first ∧ Extension sorts (initial ++ first) second := by
  rw [← checkFrom_iff, checkFrom_append, Bool.and_eq_true, checkFrom_iff, checkFrom_iff]

end Context

end Mettapedia.Languages.MM0.Kernel
