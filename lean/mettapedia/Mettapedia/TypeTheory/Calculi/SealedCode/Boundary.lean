import Mettapedia.TypeTheory.Calculi.SealedCode.Freshness

/-!
# Why a name waits for closed normal code

Three weaker disciplines for constructing names, each set beside the calculus
of this directory.

* **Sealing as written.** Substitution enters the code, reduction does not,
  and the code is never evaluated first. One program then has two names,
  depending on whether its argument was evaluated before or after it was
  substituted.
* **Naming before a normal form.** Closed code is named at once. One program
  again has two names, and a fixed point reduces to a term containing its own
  name.
* **Naming open code.** Code is named as soon as it is normal, before the
  enclosing binders have filled it. One program has two names, and a naming
  step does not survive substitution.

In the calculus itself the same programs have one name each, reduction is
stable under substitution, and no program reduces to its own name.

A fourth discipline is coherent but gives up that last property: filling a
sealed template with a value exactly as written. It is confluent, and it is
code substitution, so a program built from it steps to its own name.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SealedCode

open Term

/-- Two reducts that are distinct and irreducible: the relation is not
confluent. -/
def Incoherent {α : Type} (r : α → α → Prop) : Prop :=
  ∃ M N₁ N₂, Relation.ReflTransGen r M N₁ ∧ Relation.ReflTransGen r M N₂ ∧
    (∀ P, ¬ r N₁ P) ∧ (∀ P, ¬ r N₂ P) ∧ N₁ ≠ N₂

/-! ## Two programs of the calculus -/

/-- `love sarah x`. -/
def loves {n : Nat} (x : Term n) : Term n := .app (.app (.sym "love") (.sym "sarah")) x

theorem loves_normal {n : Nat} {x : Term n} (h : Normal x) : Normal (loves x) :=
  .app (.app (.sym _) (.sym _) (fun _ e => by cases e)) h (fun _ e => by cases e)

/-- `(let $x foo (lift (love sarah $x)))`: fill, then seal. -/
def letFoo : Term 0 := .app (.lam (.lift (loves (.var 0)))) (.sym "foo")

theorem letFoo_names : Steps letFoo (.quote (loves (.sym "foo"))) := by
  have sealed : Step (.lift (loves (.sym "foo")) : Term 0) (.quote (loves (.sym "foo"))) := by
    have := Step.name (n := 0) (loves (.sym "foo")) (loves_normal (.sym _))
    rwa [ofClosed_zero] at this
  exact (Relation.ReflTransGen.single (.beta _ _)).tail sealed

/-- `(λx. lift x) ((λy. y) a)`: the argument is a redex. -/
def twoPath : Term 0 := .app (.lam (.lift (.var 0))) (.app (.lam (.var 0)) (.sym "a"))

private theorem sym_names (s : String) :
    Step (.lift (.sym s) : Term 0) (.quote (.sym s)) := by
  have := Step.name (n := 0) (.sym s) (.sym s)
  rwa [ofClosed_zero] at this

/-- Substituting first, then evaluating the argument, names `a`. -/
theorem twoPath_outer_first : Steps twoPath (.quote (.sym "a")) :=
  ((Relation.ReflTransGen.single (.beta _ _)).tail (.lift (.beta _ _))).tail (sym_names "a")

/-- Evaluating the argument first names `a` as well. -/
theorem twoPath_inner_first : Steps twoPath (.quote (.sym "a")) :=
  ((Relation.ReflTransGen.single (.appR (.beta _ _))).tail (.beta _ _)).tail (sym_names "a")

/-! ## Sealing as written -/

/-- Substitution enters the code of `lift`; reduction neither enters it nor
evaluates it first. -/
inductive AsWritten : {n : Nat} → Term n → Term n → Prop where
  | beta {n : Nat} (b : Term (n + 1)) (a : Term n) : AsWritten (.app (.lam b) a) (b.inst a)
  | lam {n : Nat} {b b' : Term (n + 1)} : AsWritten b b' → AsWritten (.lam b) (.lam b')
  | appL {n : Nat} {f f' a : Term n} : AsWritten f f' → AsWritten (.app f a) (.app f' a)
  | appR {n : Nat} {f a a' : Term n} : AsWritten a a' → AsWritten (.app f a) (.app f a')

theorem asWritten_lift_irreducible {n : Nat} (M N : Term n) : ¬ AsWritten (.lift M) N := by
  intro h
  cases h

/-- **Sealing as written is incoherent**: the program of `twoPath` has the
two names `(λy. y) a` and `a`. -/
theorem asWritten_incoherent : Incoherent (@AsWritten 0) :=
  ⟨twoPath, .lift (.app (.lam (.var 0)) (.sym "a")), .lift (.sym "a"),
    .single (.beta _ _),
    (Relation.ReflTransGen.single (.appR (.beta _ _))).tail (.beta _ _),
    asWritten_lift_irreducible _, asWritten_lift_irreducible _,
    by decide⟩

/-! ## Naming before a normal form -/

/-- Closed code is named at once, whether or not it is normal. -/
inductive Unwaited : {n : Nat} → Term n → Term n → Prop where
  | beta {n : Nat} (b : Term (n + 1)) (a : Term n) : Unwaited (.app (.lam b) a) (b.inst a)
  | name {n : Nat} (M : Term 0) : Unwaited (.lift (ofClosed M) : Term n) (.quote M)
  | lam {n : Nat} {b b' : Term (n + 1)} : Unwaited b b' → Unwaited (.lam b) (.lam b')
  | appL {n : Nat} {f f' a : Term n} : Unwaited f f' → Unwaited (.app f a) (.app f' a)
  | appR {n : Nat} {f a a' : Term n} : Unwaited a a' → Unwaited (.app f a) (.app f a')
  | lift {n : Nat} {M M' : Term n} : Unwaited M M' → Unwaited (.lift M) (.lift M')

theorem unwaited_quote_irreducible {n : Nat} (M : Term 0) (N : Term n) :
    ¬ Unwaited (.quote M) N := by
  intro h
  cases h

private theorem unwaited_name₀ (M : Term 0) : Unwaited (.lift M) (.quote M) := by
  have := Unwaited.name (n := 0) M
  rwa [ofClosed_zero] at this

/-- **Naming before a normal form is incoherent.** -/
theorem unwaited_incoherent : Incoherent (@Unwaited 0) :=
  ⟨.lift (.app (.lam (.var 0)) (.sym "a")), .quote (.app (.lam (.var 0)) (.sym "a")),
    .quote (.sym "a"),
    .single (unwaited_name₀ _),
    (Relation.ReflTransGen.single (.lift (.beta _ _))).tail (unwaited_name₀ _),
    unwaited_quote_irreducible _, unwaited_quote_irreducible _,
    by decide⟩

/-- The body of Turing's fixed point combinator, `λx. λy. y (x x y)`. -/
def turingBody : Term 0 :=
  .lam (.lam (.app (.var 0) (.app (.app (.var 1) (.var 1)) (.var 0))))

/-- The program `Θ F` with `F = λm. h (lift m)`. -/
def selfLifting : Term 0 :=
  .app (.app turingBody turingBody) (.lam (.app (.sym "h") (.lift (.var 0))))

/-- `Θ F` reduces to `h (lift (Θ F))`, in the calculus and in both variants. -/
theorem selfLifting_steps : Steps selfLifting (.app (.sym "h") (.lift selfLifting)) :=
  (((Relation.ReflTransGen.single (.appL (.beta _ _))).tail (.beta _ _)).tail (.beta _ _))

theorem selfLifting_unwaited_steps :
    Relation.ReflTransGen (@Unwaited 0) selfLifting (.app (.sym "h") (.lift selfLifting)) :=
  (((Relation.ReflTransGen.single (.appL (.beta _ _))).tail (.beta _ _)).tail (.beta _ _))

/-- **Naming before a normal form lets a program reach its own name.** -/
theorem unwaited_self_code :
    Relation.ReflTransGen (@Unwaited 0) selfLifting (.app (.sym "h") (.quote selfLifting)) ∧
      NamedIn selfLifting (.app (.sym "h") (.quote selfLifting) : Term 0) :=
  ⟨selfLifting_unwaited_steps.tail (.appR (unwaited_name₀ _)), .appR .here⟩

/-- In the calculus the same program never reaches its own name. -/
theorem selfLifting_no_self_code {N : Term 0} (h : Steps selfLifting N) :
    ¬ NamedIn selfLifting N :=
  no_self_code h

/-! ## Naming open code -/

/-- Terms whose names may hold open code. Substitution enters a `frozen` name;
reduction does not. -/
inductive FTerm : Nat → Type where
  | var {n : Nat} : Fin n → FTerm n
  | sym {n : Nat} : String → FTerm n
  | lam {n : Nat} : FTerm (n + 1) → FTerm n
  | app {n : Nat} : FTerm n → FTerm n → FTerm n
  | lift {n : Nat} : FTerm n → FTerm n
  | frozen {n : Nat} : FTerm n → FTerm n
  deriving DecidableEq

namespace FTerm

def rename : {n m : Nat} → (Fin n → Fin m) → FTerm n → FTerm m
  | _, _, ρ, .var i => .var (ρ i)
  | _, _, _, .sym s => .sym s
  | _, _, ρ, .lam b => .lam (rename (Term.liftRen ρ) b)
  | _, _, ρ, .app f a => .app (rename ρ f) (rename ρ a)
  | _, _, ρ, .lift M => .lift (rename ρ M)
  | _, _, ρ, .frozen M => .frozen (rename ρ M)

def liftSub {n m : Nat} (σ : Fin n → FTerm m) : Fin (n + 1) → FTerm (m + 1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

def subst : {n m : Nat} → (Fin n → FTerm m) → FTerm n → FTerm m
  | _, _, σ, .var i => σ i
  | _, _, _, .sym s => .sym s
  | _, _, σ, .lam b => .lam (subst (liftSub σ) b)
  | _, _, σ, .app f a => .app (subst σ f) (subst σ a)
  | _, _, σ, .lift M => .lift (subst σ M)
  | _, _, σ, .frozen M => .frozen (subst σ M)

def inst {n : Nat} (b : FTerm (n + 1)) (a : FTerm n) : FTerm n :=
  subst (Fin.cases a FTerm.var) b

end FTerm

/-- Normal terms with frozen names. -/
inductive FNormal : {n : Nat} → FTerm n → Prop where
  | var {n : Nat} (i : Fin n) : FNormal (.var i)
  | sym {n : Nat} (s : String) : FNormal (.sym s : FTerm n)
  | frozen {n : Nat} (M : FTerm n) : FNormal (.frozen M)
  | lam {n : Nat} {b : FTerm (n + 1)} : FNormal b → FNormal (.lam b)
  | app {n : Nat} {f a : FTerm n} :
      FNormal f → FNormal a → (∀ b, f ≠ .lam b) → FNormal (.app f a)

/-- Code is named as soon as it is normal, open or not. -/
inductive Premature : {n : Nat} → FTerm n → FTerm n → Prop where
  | beta {n : Nat} (b : FTerm (n + 1)) (a : FTerm n) : Premature (.app (.lam b) a) (b.inst a)
  | name {n : Nat} {M : FTerm n} : FNormal M → Premature (.lift M) (.frozen M)
  | lam {n : Nat} {b b' : FTerm (n + 1)} : Premature b b' → Premature (.lam b) (.lam b')
  | appL {n : Nat} {f f' a : FTerm n} : Premature f f' → Premature (.app f a) (.app f' a)
  | appR {n : Nat} {f a a' : FTerm n} : Premature a a' → Premature (.app f a) (.app f a')
  | lift {n : Nat} {M M' : FTerm n} : Premature M M' → Premature (.lift M) (.lift M')

theorem premature_frozen_irreducible {n : Nat} (M N : FTerm n) :
    ¬ Premature (.frozen M) N := by
  intro h
  cases h

/-- `(λy. lift (y a)) (λz. z)`. -/
def openPath : FTerm 0 :=
  .app (.lam (.lift (.app (.var 0) (.sym "a")))) (.lam (.var 0))

private theorem openCode_normal : FNormal (.app (.var 0) (.sym "a") : FTerm 1) :=
  .app (.var _) (.sym _) (fun _ e => by cases e)

/-- **Naming open code is incoherent.** Naming beneath the binder freezes the
redex `(λz. z) a`; filling first names `a`. -/
theorem premature_incoherent : Incoherent (@Premature 0) :=
  ⟨openPath, .frozen (.app (.lam (.var 0)) (.sym "a")), .frozen (.sym "a"),
    (Relation.ReflTransGen.single (.appL (.lam (.name openCode_normal)))).tail (.beta _ _),
    (((Relation.ReflTransGen.single (.beta _ _)).tail (.lift (.beta _ _))).tail
      (.name (.sym _))),
    premature_frozen_irreducible _, premature_frozen_irreducible _,
    by decide⟩

/-! ## Filling sealed code as written

An operation that unpacks a sealed name, replaces a symbol of its code by a
value exactly as written, and seals the result is coherent: the template is
sealed and the value is unique. It is also code substitution, the operation of
the diagonal lemma, and a program built from it reduces in one step to its own
name. -/

/-- Code with symbols, sealed names and filling. -/
inductive DTerm : Type where
  | sym : String → DTerm
  | quote : DTerm → DTerm
  | fill : String → DTerm → DTerm → DTerm
  deriving DecidableEq

/-- Replace a symbol throughout code, as written. -/
def DTerm.replace (s : String) (v : DTerm) : DTerm → DTerm
  | .sym t => if t = s then v else .sym t
  | .quote M => .quote (replace s v M)
  | .fill t K a => .fill t (replace s v K) (replace s v a)

/-- Values: symbols and sealed names. -/
inductive DValue : DTerm → Prop where
  | sym (s : String) : DValue (.sym s)
  | quote (M : DTerm) : DValue (.quote M)

/-- `fill s @M v` seals `M` with the symbol `s` replaced by the value `v`. -/
inductive Fill : DTerm → DTerm → Prop where
  | fill (s : String) (M v : DTerm) : DValue v → Fill (.fill s (.quote M) v) (.quote (DTerm.replace s v M))
  | template {s : String} {K K' a : DTerm} : Fill K K' → Fill (.fill s K a) (.fill s K' a)
  | argument {s : String} {K a a' : DTerm} : Fill a a' → Fill (.fill s K a) (.fill s K a')

theorem DValue.no_fill {v w : DTerm} (value : DValue v) : ¬ Fill v w := by
  intro step
  cases value <;> cases step

/-- Two steps from one term are equal or meet in one step each. -/
theorem Fill.join {a b c : DTerm} (hb : Fill a b) (hc : Fill a c) :
    b = c ∨ ∃ d, Fill b d ∧ Fill c d := by
  induction hb generalizing c with
  | fill s M v value =>
      cases hc with
      | fill => exact .inl rfl
      | template inner => cases inner
      | argument inner => exact (value.no_fill inner).elim
  | @template s K K' a hK ih =>
      cases hc with
      | fill => cases hK
      | template inner =>
          rcases ih inner with rfl | ⟨d, hd, hd'⟩
          · exact .inl rfl
          · exact .inr ⟨.fill s d a, .template hd, .template hd'⟩
      | @argument _ _ _ a' inner => exact .inr ⟨.fill s K' a', .argument inner, .template hK⟩
  | @argument s K a a' hA ih =>
      cases hc with
      | fill _ _ _ value => exact (value.no_fill hA).elim
      | @template _ _ K' _ inner => exact .inr ⟨.fill s K' a', .template inner, .argument hA⟩
      | argument inner =>
          rcases ih inner with rfl | ⟨d, hd, hd'⟩
          · exact .inl rfl
          · exact .inr ⟨.fill s K d, .argument hd, .argument hd'⟩

/-- **Filling sealed code with values is confluent.** -/
theorem fill_church_rosser {a b c : DTerm} (hb : Relation.ReflTransGen Fill a b)
    (hc : Relation.ReflTransGen Fill a c) : Relation.Join (Relation.ReflTransGen Fill) b c :=
  Relation.church_rosser
    (fun _ _ _ hb hc => by
      rcases Fill.join hb hc with rfl | ⟨d, hd, hd'⟩
      · exact ⟨_, .refl, .refl⟩
      · exact ⟨d, .single hd, .single hd'⟩)
    hb hc

/-- The template `fill x x x`. -/
def diagonal : DTerm := .fill "x" (.sym "x") (.sym "x")

/-- `fill x @(fill x x x) @(fill x x x)`. -/
def quine : DTerm := .fill "x" (.quote diagonal) (.quote diagonal)

/-- **Filling as written makes a quine**: the program steps to its own name. -/
theorem fill_quine : Fill quine (.quote quine) :=
  .fill "x" diagonal (.quote diagonal) (.quote diagonal)

/-- **A premature naming step does not survive substitution.** Naming
`lift (y a)` is a step, but after `y := λz. z` the code is a redex, and
`lift ((λz. z) a)` no longer steps to its frozen name. -/
theorem premature_not_substitution_stable :
    Premature (.lift (.app (.var 0) (.sym "a")) : FTerm 1) (.frozen (.app (.var 0) (.sym "a"))) ∧
      ¬ Premature
        ((FTerm.lift (.app (.var 0) (.sym "a"))).inst (.lam (.var 0)) : FTerm 0)
        ((FTerm.frozen (.app (.var 0) (.sym "a"))).inst (.lam (.var 0))) := by
  refine ⟨.name openCode_normal, ?_⟩
  intro h
  cases h with
  | name normal =>
      cases normal with
      | app _ _ notLam => exact notLam _ rfl

end Mettapedia.TypeTheory.Calculi.SealedCode
