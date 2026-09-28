import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# Raw telescopes over a binding signature

An ordinary object-variable scope repeats one chosen binder sort. A raw
context stores one type code over each preceding scope; lookup weakens that
code past its own variable and all later declarations. These are scoped
syntactic data. Formation and typing are separate judgment families.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.Telescope

variable {S : Signature}

/-- Object-language scopes contain only the designated variable sort. -/
def scope (b : S.Srt) (n : Nat) : Ctx S := List.replicate n b

@[simp] theorem scope_zero (b : S.Srt) : scope b 0 = [] := rfl
@[simp] theorem scope_succ (b : S.Srt) (n : Nat) : scope b (n + 1) = b :: scope b n := rfl

abbrev RawTm (S : Signature) (b : S.Srt) (n : Nat) := Term S (scope b n) b
abbrev RawTy (S : Signature) (b k : S.Srt) (n : Nat) := Term S (scope b n) k
abbrev RawSub (S : Signature) (b : S.Srt) (n m : Nat) := Sub S (scope b n) (scope b m)

/-- A telescope of scoped type codes, without a formation certificate. -/
inductive RawContext (S : Signature) (b k : S.Srt) : Nat → Type where
  | nil : RawContext S b k 0
  | snoc {n : Nat} : RawContext S b k n → RawTy S b k n → RawContext S b k (n + 1)

variable {b k : S.Srt}

/-- Look up the declaration at an actual variable occurrence, in the full scope. -/
def lookup : {n : Nat} → RawContext S b k n → Var (scope b n) b → RawTy S b k n
  | _, .snoc _ code, .zero => weaken code
  | _, .snoc prior _, .succ var => weaken (lookup prior var)

@[simp] theorem lookup_newest {n : Nat} (context : RawContext S b k n) (code : RawTy S b k n) :
    lookup (.snoc context code) .zero = weaken code := rfl

@[simp] theorem lookup_older {n : Nat} (context : RawContext S b k n) (code : RawTy S b k n)
    (var : Var (scope b n) b) :
    lookup (.snoc context code) (.succ var) = weaken (lookup context var) := rfl

/-- Every variable in the ordinary scope has the designated binder sort. -/
theorem variable_sort : {n : Nat} → {s : S.Srt} → Var (scope b n) s → s = b
  | _ + 1, _, .zero => rfl
  | _ + 1, _, .succ var => variable_sort var

/-- A raw substitution is determined by its ordinary-variable components. -/
theorem substitution_ext {n m : Nat} {first second : RawSub S b n m}
    (components : ∀ var : Var (scope b n) b, first b var = second b var) :
    first = second := by
  funext s var
  have same := variable_sort var
  cases same
  exact components var

/-- The empty raw scope has a unique substitution into any target scope. -/
def emptySub (b : S.Srt) (m : Nat) : RawSub S b 0 m := fun _ var => nomatch var

theorem emptySub_unique {m : Nat} (substitution : RawSub S b 0 m) :
    substitution = emptySub b m := by
  funext s var
  nomatch var

#print axioms lookup
#print axioms substitution_ext

end Mettapedia.OSLF.Binding.Telescope
