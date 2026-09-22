import Mettapedia.Languages.OpenTheory.DefinedConnectives

/-!
# From extensional higher-order logic back to OpenTheory terms

`ExtensionalHOLInterpretation.lean` translates canonical OpenTheory terms into
the calculus `HOL.ExtDerivation`.  This module goes the other way at the level
of terms.

## Design

* Types: `reverseTy` sends the proposition type to `bool`, an arrow to the
  OpenTheory function type, and a base type to the atomic OpenTheory type it
  is.  It inverts `Ty.toHOL` on both sides (`toHOL_reverseTy`,
  `reverseTy_toHOL`).
* Symbols: a constant symbol becomes the OpenTheory constant occurrence it
  names, with its annotation, and a variable symbol becomes the free
  OpenTheory variable it names.
* Variables of the context: the translation `reverseTermWith env` is
  parameterized by an image `env x` of every variable `x` of the context,
  given at the binder depth of that context; entering a binder lifts the
  images (`VarEnv.lift`).  Two images are used:
  - `VarEnv.loose`: variables become loose de Bruijn indices, exactly as in
    `Translates`.  This is `reverseTermOpen`, the partner of the forward
    translation in the round trips.
  - `Naming.env names`: variables become OpenTheory free variables, the
    variable `x : Var Γ τ` becoming `⟨names x, reverseTy τ⟩`.  This is
    `reverseTerm names`; it produces closed canonical terms, hence
    `reverseCanonical` and `reverseHypotheses`.
* Connectives become applications of their HOL Light definitions:
  `PrimitiveSentences.truthDB`, `ExcludedMiddle.falsityDefinitionDB`,
  `ExcludedMiddle.andDB`, `ExcludedMiddle.orDB`, `ExcludedMiddle.impAppDB`,
  `ExcludedMiddle.notDB`, `ExcludedMiddle.forallDB` and
  `DefinedConnectives.existsDB`; target equality becomes primitive equality.

## Main results

* Typing: `inferType_reverseTermWith`; closed reversals are checked
  canonical terms (`reverseCanonical`), Boolean for formulas
  (`reverseCanonical_isBool`).
* Round trip on the image (`reverseTermOpen_of_translates`): a translated
  term comes back as the source term with every occurrence of primitive
  equality that is not the head of a full application eta-expanded
  (`expandBareEquality`); on terms whose equality occurrences are all fully
  applied it comes back unchanged
  (`reverseTermOpen_of_translates_of_equalityFullyApplied`,
  `reverseCanonical_of_translates`).
* Round trip on formulas (`exists_translates_reverseTermOpen_eq`,
  `exists_translates_reverseTermOpen_derivable`,
  `exists_translates_reverseTerm_eq`): the forward translation of the reverse
  of a term that mentions no symbol `equalitySymbol a` is provably equal to it
  in `HOL.ExtDerivation`.  That symbol, primitive equality as an
  uninterpreted constant, lies outside the image of the forward translation;
  `Examples.not_extDerivation_eq_equalitySymbolFormula` shows the hypothesis
  is needed.  The defined existential quantifier and truth are provably the
  primitive ones (`exists_iff`, `truth_iff`).
* Commutation: with renaming (`reverseTermWith_rename`, `reverseTerm_weaken`),
  with simultaneous substitution (`reverseTermWith_subst`), with binder
  instantiation against `DBTerm.instantiateAt` (`reverseTerm_instantiate`,
  `betaReduce?_reverseCanonical`), with abstraction of a fresh free variable
  against `DBTerm.closeFreeAt` (`closeFreeAt_reverseTerm_cons`,
  `abstractFree_reverseCanonical_cons`), with constant substitution
  (`reverseTermWith_substConst`), and with type substitution against
  `TermSubst.applyDB` (`reverseTermWith_mapTypes`, `reverseTerm_mapTypes`).
* Hypotheses: `reverseHypotheses` is a finite set of Boolean canonical terms,
  unchanged by weakening (`reverseHypotheses_weakenHyps`).
* Freshness: a new innermost name must be avoided by the naming
  (`Naming.Avoids`) and by the variable symbols of the body and hypotheses;
  then the hypotheses do not mention it (`not_freeInHypotheses_reverseHypotheses`)
  and abstracting it is the reverse of target abstraction.  Such a name exists
  (`exists_fresh_name`), and it keeps namings injective
  (`Naming.injective_cons`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic

namespace ReverseTranslation

open ExcludedMiddle DefinedConnectives

/-! ## Types -/

/-- The OpenTheory type of a target type. -/
def reverseTy : HOL.Ty AtomicTy → Ty
  | .prop => Ty.bool
  | .base base => base.1
  | .arr σ τ => .function (reverseTy σ) (reverseTy τ)

@[simp] theorem reverseTy_prop : reverseTy .prop = Ty.bool := rfl

@[simp] theorem reverseTy_base (base : AtomicTy) : reverseTy (.base base) = base.1 := rfl

@[simp] theorem reverseTy_arr (σ τ : HOL.Ty AtomicTy) :
    reverseTy (.arr σ τ) = .function (reverseTy σ) (reverseTy τ) := rfl

theorem toHOL_reverseTy : ∀ τ : HOL.Ty AtomicTy, (reverseTy τ).toHOL = τ
  | .prop => Ty.toHOL_bool
  | .base base => Ty.toHOL_of_isAtomic base.2
  | .arr σ τ => by
      rw [reverseTy_arr, Ty.toHOL_function, toHOL_reverseTy σ, toHOL_reverseTy τ]

theorem reverseTy_toHOL (ty : Ty) : reverseTy ty.toHOL = ty :=
  Ty.toHOL_injective (toHOL_reverseTy ty.toHOL)

theorem reverseTy_injective : Function.Injective reverseTy := fun σ τ h => by
  rw [← toHOL_reverseTy σ, h, toHOL_reverseTy]

theorem reverseTy_eq_iff {τ : HOL.Ty AtomicTy} {ty : Ty} :
    reverseTy τ = ty ↔ τ = ty.toHOL := by
  constructor
  · rintro rfl
    exact (toHOL_reverseTy τ).symm
  · rintro rfl
    exact reverseTy_toHOL ty

/-- Target type substitution by an OpenTheory type substitution is OpenTheory
type substitution. -/
theorem reverseTy_substitute (substitution : TypeSubst) :
    ∀ τ : HOL.Ty AtomicTy,
      reverseTy (HOL.Ty.substitute substitution.baseInstance τ) =
        substitution.apply (reverseTy τ)
  | .prop => (TypeSubst.apply_bool substitution).symm
  | .base base => reverseTy_toHOL _
  | .arr σ τ => by
      rw [HOL.Ty.substitute_arr, reverseTy_arr, reverseTy_arr, TypeSubst.apply_function,
        reverseTy_substitute substitution σ, reverseTy_substitute substitution τ]

/-! ## Shifting loose de Bruijn indices -/

/-- Increment every loose de Bruijn index at or above `cutoff`. -/
def shiftLoose (cutoff : Nat) : DBTerm → DBTerm
  | .const constant annotation => .const constant annotation
  | .free sourceVar => .free sourceVar
  | .bound index => if index < cutoff then .bound index else .bound (index + 1)
  | .app function argument => .app (shiftLoose cutoff function) (shiftLoose cutoff argument)
  | .abs domain body => .abs domain (shiftLoose (cutoff + 1) body)

theorem shiftLoose_of_looseBelow :
    ∀ {depth cutoff : Nat} {term : DBTerm}, DBTerm.LooseBelow depth term →
      depth ≤ cutoff → shiftLoose cutoff term = term
  | _, _, .const _ _, _, _ => rfl
  | _, _, .free _, _, _ => rfl
  | depth, cutoff, .bound index, hloose, hdepth => by
      have : index < cutoff := Nat.lt_of_lt_of_le hloose hdepth
      simp [shiftLoose, this]
  | _, _, .app _ _, hloose, hdepth => by
      simp only [shiftLoose]
      rw [shiftLoose_of_looseBelow hloose.1 hdepth, shiftLoose_of_looseBelow hloose.2 hdepth]
  | _, _, .abs _ body, hloose, hdepth => by
      simp only [shiftLoose]
      rw [shiftLoose_of_looseBelow (term := body) hloose (Nat.succ_le_succ hdepth)]

theorem shiftLoose_of_closed {term : DBTerm} (closed : DBTerm.LooseBelow 0 term)
    (cutoff : Nat) : shiftLoose cutoff term = term :=
  shiftLoose_of_looseBelow closed (Nat.zero_le cutoff)

theorem shiftLoose_shiftLoose :
    ∀ {inner outer : Nat} (term : DBTerm), inner ≤ outer →
      shiftLoose (outer + 1) (shiftLoose inner term) =
        shiftLoose inner (shiftLoose outer term)
  | _, _, .const _ _, _ => rfl
  | _, _, .free _, _ => rfl
  | inner, outer, .bound index, hle => by
      simp only [shiftLoose]
      by_cases hinner : index < inner
      · have houter : index < outer := Nat.lt_of_lt_of_le hinner hle
        simp [shiftLoose, hinner, houter, Nat.lt_succ_of_lt houter]
      · by_cases houter : index < outer
        · simp [shiftLoose, hinner, houter]
        · simp [shiftLoose, hinner, houter]
          omega
  | _, _, .app function argument, hle => by
      simp only [shiftLoose]
      rw [shiftLoose_shiftLoose function hle, shiftLoose_shiftLoose argument hle]
  | _, _, .abs _ body, hle => by
      simp only [shiftLoose]
      rw [shiftLoose_shiftLoose body (Nat.succ_le_succ hle)]

theorem looseBelow_shiftLoose :
    ∀ {depth : Nat} (cutoff : Nat) {term : DBTerm}, DBTerm.LooseBelow depth term →
      DBTerm.LooseBelow (depth + 1) (shiftLoose cutoff term)
  | _, _, .const _ _, _ => trivial
  | _, _, .free _, _ => trivial
  | depth, cutoff, .bound index, hloose => by
      simp only [shiftLoose]
      split
      · exact Nat.lt_succ_of_lt hloose
      · exact Nat.succ_lt_succ hloose
  | _, cutoff, .app _ _, hloose =>
      ⟨looseBelow_shiftLoose cutoff hloose.1, looseBelow_shiftLoose cutoff hloose.2⟩
  | _, cutoff, .abs _ body, hloose => looseBelow_shiftLoose (cutoff + 1) (term := body) hloose

/-- Shifting inserts one type into the binder context at the cutoff. -/
theorem inferType_shiftLoose (inserted : Ty) :
    ∀ (term : DBTerm) (before after : List Ty),
      (shiftLoose before.length term).inferType (before ++ inserted :: after) =
        term.inferType (before ++ after)
  | .const _ _, _, _ => by simp only [shiftLoose, DBTerm.inferType.eq_1]
  | .free _, _, _ => by simp only [shiftLoose, DBTerm.inferType.eq_2]
  | .bound index, before, after => by
      simp only [shiftLoose, DBTerm.inferType.eq_3]
      split
      · rename_i hlt
        simp only [DBTerm.inferType.eq_3]
        rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
      · rename_i hge
        simp only [DBTerm.inferType.eq_3]
        have hge' : before.length ≤ index := Nat.le_of_not_lt hge
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right hge']
        rw [show index + 1 - before.length = (index - before.length) + 1 by omega]
        rfl
  | .app function argument, before, after => by
      simp only [shiftLoose, DBTerm.inferType.eq_4]
      rw [inferType_shiftLoose inserted function before after,
        inferType_shiftLoose inserted argument before after]
  | .abs domain body, before, after => by
      simp only [shiftLoose, DBTerm.inferType.eq_5]
      have := inferType_shiftLoose inserted body (domain :: before) after
      simp only [List.length_cons, List.cons_append] at this
      rw [this]

theorem inferType_shiftLoose_zero (inserted : Ty) (term : DBTerm) (context : List Ty) :
    (shiftLoose 0 term).inferType (inserted :: context) = term.inferType context :=
  inferType_shiftLoose inserted term [] context

theorem looseBelow_mono :
    ∀ {depth depth' : Nat} {term : DBTerm}, DBTerm.LooseBelow depth term →
      depth ≤ depth' → DBTerm.LooseBelow depth' term
  | _, _, .const _ _, _, _ => trivial
  | _, _, .free _, _, _ => trivial
  | _, _, .bound _, hloose, hle => Nat.lt_of_lt_of_le hloose hle
  | _, _, .app _ _, hloose, hle => ⟨looseBelow_mono hloose.1 hle, looseBelow_mono hloose.2 hle⟩
  | _, _, .abs _ body, hloose, hle =>
      looseBelow_mono (term := body) hloose (Nat.succ_le_succ hle)

/-! ## Typing of the inlined connectives -/

theorem truthDB_inferType :
    DBTerm.inferType [] PrimitiveSentences.truthDB = some Ty.bool := by
  simp [DBTerm.inferType, CanonicalTerm.equalityDB, PrimitiveSentences.truthDB,
    PrimitiveSentences.identityBool, Ty.equality, Ty.function, TypeOp.function,
    Ty.destFunction?]

theorem falsityDefinitionDB_inferType :
    DBTerm.inferType [] falsityDefinitionDB = some Ty.bool := by
  simp [falsityDefinitionDB, forallDB, DBTerm.inferType, CanonicalTerm.equalityDB,
    PrimitiveSentences.truthDB, PrimitiveSentences.identityBool, Ty.equality, Ty.function,
    TypeOp.function, Ty.destFunction?]

theorem notDB_inferType :
    DBTerm.inferType [] notDB = some (.function Ty.bool Ty.bool) := by
  simp [notDB, falsityDefinitionDB, forallDB, impDB, andDB, boolBinaryTy,
    DBTerm.inferType, CanonicalTerm.equalityDB, PrimitiveSentences.truthDB,
    PrimitiveSentences.identityBool, Ty.equality, Ty.function, TypeOp.function,
    Ty.destFunction?]

theorem orDB_inferType : DBTerm.inferType [] orDB = some boolBinaryTy := by
  simp [orDB, forallDB, impAppDB, impDB, andDB, boolBinaryTy, DBTerm.inferType,
    CanonicalTerm.equalityDB, PrimitiveSentences.truthDB, PrimitiveSentences.identityBool,
    Ty.equality, Ty.function, TypeOp.function, Ty.destFunction?]

theorem truthDB_closed : DBTerm.LooseBelow 0 PrimitiveSentences.truthDB :=
  DBTerm.looseBelow_of_inferType truthDB_inferType

theorem falsityDefinitionDB_closed : DBTerm.LooseBelow 0 falsityDefinitionDB :=
  DBTerm.looseBelow_of_inferType falsityDefinitionDB_inferType

theorem andDB_closed : DBTerm.LooseBelow 0 andDB :=
  DBTerm.looseBelow_of_inferType andDB_inferType

theorem orDB_closed : DBTerm.LooseBelow 0 orDB :=
  DBTerm.looseBelow_of_inferType orDB_inferType

theorem impDB_closed : DBTerm.LooseBelow 0 impDB :=
  DBTerm.looseBelow_of_inferType impDB_inferType

theorem notDB_closed : DBTerm.LooseBelow 0 notDB :=
  DBTerm.looseBelow_of_inferType notDB_inferType

theorem forallDB_closed (A : Ty) : DBTerm.LooseBelow 0 (forallDB A) :=
  DBTerm.looseBelow_of_inferType (forallDB_inferType A)

theorem existsDB_closed (A : Ty) : DBTerm.LooseBelow 0 (existsDB A) :=
  DBTerm.looseBelow_of_inferType (existsDB_inferType A)

/-! ## The translation -/

/-- Images of the variables of a target context, as OpenTheory terms at the
binder depth of that context. -/
abbrev VarEnv (Γ : HOL.Ctx AtomicTy) : Type :=
  ∀ {τ : HOL.Ty AtomicTy}, HOL.Var Γ τ → DBTerm

namespace VarEnv

/-- Entering a binder: the new variable is the innermost de Bruijn index and
every other image is shifted past it. -/
def lift {Γ : HOL.Ctx AtomicTy} {σ : HOL.Ty AtomicTy} (env : VarEnv Γ) :
    VarEnv (σ :: Γ)
  | _, .vz => .bound 0
  | _, .vs x => shiftLoose 0 (env x)

/-- Every variable becomes the loose de Bruijn index of its position, as in
`Translates`. -/
def loose {Γ : HOL.Ctx AtomicTy} : VarEnv Γ := fun x => .bound (deBruijnIndex x)

/-- The empty context has no variables. -/
def empty : VarEnv [] := fun x => nomatch x

theorem lift_loose {Γ : HOL.Ctx AtomicTy} {σ τ : HOL.Ty AtomicTy}
    (x : HOL.Var (σ :: Γ) τ) : VarEnv.lift (σ := σ) (loose (Γ := Γ)) x = loose x := by
  cases x with
  | vz => rfl
  | vs x => simp [lift, loose, shiftLoose, deBruijnIndex]

end VarEnv

/-- The OpenTheory term a target symbol names. -/
def reverseSymbol : {τ : HOL.Ty AtomicTy} → Symbol τ → DBTerm
  | _, .constant constant annotation _ => .const constant annotation
  | _, .variable sourceVar _ => .free sourceVar

/-- The OpenTheory term of a target term, given images of its context
variables.  Connectives become applications of their HOL Light definitions
and target equality becomes primitive equality. -/
def reverseTermWith : {Γ : HOL.Ctx AtomicTy} → VarEnv Γ → {τ : HOL.Ty AtomicTy} →
    HOL.Term Symbol Γ τ → DBTerm
  | _, env, _, .var x => env x
  | _, _, _, .const symbol => reverseSymbol symbol
  | _, env, _, .app function argument =>
      .app (reverseTermWith env function) (reverseTermWith env argument)
  | _, env, _, .lam (σ := σ) body => .abs (reverseTy σ) (reverseTermWith env.lift body)
  | _, _, _, .top => PrimitiveSentences.truthDB
  | _, _, _, .bot => falsityDefinitionDB
  | _, env, _, .and p q => .app (.app andDB (reverseTermWith env p)) (reverseTermWith env q)
  | _, env, _, .or p q => .app (.app orDB (reverseTermWith env p)) (reverseTermWith env q)
  | _, env, _, .imp p q => impAppDB (reverseTermWith env p) (reverseTermWith env q)
  | _, env, _, .not p => .app notDB (reverseTermWith env p)
  | _, env, _, .eq (τ := ρ) left right =>
      CanonicalTerm.equalityDB (reverseTy ρ) (reverseTermWith env left)
        (reverseTermWith env right)
  | _, env, _, .all (σ := σ) body =>
      .app (forallDB (reverseTy σ)) (.abs (reverseTy σ) (reverseTermWith env.lift body))
  | _, env, _, .ex (σ := σ) body =>
      .app (existsDB (reverseTy σ)) (.abs (reverseTy σ) (reverseTermWith env.lift body))

/-- The reverse translation with context variables as loose de Bruijn
indices. -/
def reverseTermOpen {Γ : HOL.Ctx AtomicTy} {τ : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol Γ τ) : DBTerm :=
  reverseTermWith VarEnv.loose term

/-- Images agreeing on every variable give the same translation. -/
theorem reverseTermWith_congr :
    ∀ {Γ : HOL.Ctx AtomicTy} {env env' : VarEnv Γ},
      (∀ {τ : HOL.Ty AtomicTy} (x : HOL.Var Γ τ), env x = env' x) →
      ∀ {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ),
        reverseTermWith env term = reverseTermWith env' term
  | _, _, _, h, _, .var x => h x
  | _, _, _, _, _, .const _ => rfl
  | _, _, _, h, _, .app function argument => by
      simp only [reverseTermWith]
      rw [reverseTermWith_congr h function, reverseTermWith_congr h argument]
  | _, env, env', h, _, .lam body => by
      simp only [reverseTermWith]
      rw [reverseTermWith_congr (env := env.lift) (env' := env'.lift)
        (fun x => by cases x <;> simp [VarEnv.lift, h]) body]
  | _, _, _, _, _, .top => rfl
  | _, _, _, _, _, .bot => rfl
  | _, _, _, h, _, .and p q => by
      simp only [reverseTermWith]
      rw [reverseTermWith_congr h p, reverseTermWith_congr h q]
  | _, _, _, h, _, .or p q => by
      simp only [reverseTermWith]
      rw [reverseTermWith_congr h p, reverseTermWith_congr h q]
  | _, _, _, h, _, .imp p q => by
      simp only [reverseTermWith]
      rw [reverseTermWith_congr h p, reverseTermWith_congr h q]
  | _, _, _, h, _, .not p => by
      simp only [reverseTermWith]
      rw [reverseTermWith_congr h p]
  | _, _, _, h, _, .eq left right => by
      simp only [reverseTermWith]
      rw [reverseTermWith_congr h left, reverseTermWith_congr h right]
  | _, env, env', h, _, .all body => by
      simp only [reverseTermWith]
      rw [reverseTermWith_congr (env := env.lift) (env' := env'.lift)
        (fun x => by cases x <;> simp [VarEnv.lift, h]) body]
  | _, env, env', h, _, .ex body => by
      simp only [reverseTermWith]
      rw [reverseTermWith_congr (env := env.lift) (env' := env'.lift)
        (fun x => by cases x <;> simp [VarEnv.lift, h]) body]

/-- A closed target term has one translation, whatever the (vacuous) images. -/
theorem reverseTermWith_eq_reverseTermWith_empty (env : VarEnv []) {τ : HOL.Ty AtomicTy}
    (term : HOL.ClosedTerm Symbol τ) :
    reverseTermWith env term = reverseTermWith VarEnv.empty term :=
  reverseTermWith_congr (fun {_} (x : HOL.Var [] _) => nomatch x) term

theorem reverseTermWith_rename :
    ∀ {Γ Γ' : HOL.Ctx AtomicTy} (env : VarEnv Γ') (ρ : HOL.Rename AtomicTy Γ Γ')
      {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ),
      reverseTermWith env (HOL.rename ρ term) = reverseTermWith (fun x => env (ρ x)) term
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, _, _, .const _ => rfl
  | _, _, env, ρ, _, .app function argument => by
      simp only [HOL.rename, reverseTermWith]
      rw [reverseTermWith_rename env ρ function, reverseTermWith_rename env ρ argument]
  | _, _, env, ρ, _, .lam body => by
      simp only [HOL.rename, reverseTermWith]
      rw [reverseTermWith_rename env.lift (HOL.Rename.lift ρ) body]
      congr 1
      exact reverseTermWith_congr (fun x => by cases x <;> rfl) body
  | _, _, _, _, _, .top => rfl
  | _, _, _, _, _, .bot => rfl
  | _, _, env, ρ, _, .and p q => by
      simp only [HOL.rename, reverseTermWith]
      rw [reverseTermWith_rename env ρ p, reverseTermWith_rename env ρ q]
  | _, _, env, ρ, _, .or p q => by
      simp only [HOL.rename, reverseTermWith]
      rw [reverseTermWith_rename env ρ p, reverseTermWith_rename env ρ q]
  | _, _, env, ρ, _, .imp p q => by
      simp only [HOL.rename, reverseTermWith]
      rw [reverseTermWith_rename env ρ p, reverseTermWith_rename env ρ q]
  | _, _, env, ρ, _, .not p => by
      simp only [HOL.rename, reverseTermWith]
      rw [reverseTermWith_rename env ρ p]
  | _, _, env, ρ, _, .eq left right => by
      simp only [HOL.rename, reverseTermWith]
      rw [reverseTermWith_rename env ρ left, reverseTermWith_rename env ρ right]
  | _, _, env, ρ, _, .all body => by
      simp only [HOL.rename, reverseTermWith]
      rw [reverseTermWith_rename env.lift (HOL.Rename.lift ρ) body]
      congr 2
      exact reverseTermWith_congr (fun x => by cases x <;> rfl) body
  | _, _, env, ρ, _, .ex body => by
      simp only [HOL.rename, reverseTermWith]
      rw [reverseTermWith_rename env.lift (HOL.Rename.lift ρ) body]
      congr 2
      exact reverseTermWith_congr (fun x => by cases x <;> rfl) body

theorem reverseSymbol_closed {τ : HOL.Ty AtomicTy} (symbol : Symbol τ) :
    DBTerm.LooseBelow 0 (reverseSymbol symbol) := by
  cases symbol <;> trivial

theorem shiftLoose_reverseSymbol (cutoff : Nat) {τ : HOL.Ty AtomicTy} (symbol : Symbol τ) :
    shiftLoose cutoff (reverseSymbol symbol) = reverseSymbol symbol :=
  shiftLoose_of_closed (reverseSymbol_closed symbol) cutoff

theorem reverseTermWith_shiftLoose :
    ∀ {Γ : HOL.Ctx AtomicTy} (env : VarEnv Γ) (cutoff : Nat) {τ : HOL.Ty AtomicTy}
      (term : HOL.Term Symbol Γ τ),
      reverseTermWith (fun x => shiftLoose cutoff (env x)) term =
        shiftLoose cutoff (reverseTermWith env term)
  | _, _, _, _, .var _ => rfl
  | _, _, cutoff, _, .const symbol => (shiftLoose_reverseSymbol cutoff symbol).symm
  | _, env, cutoff, _, .app function argument => by
      simp only [reverseTermWith, shiftLoose]
      rw [reverseTermWith_shiftLoose env cutoff function,
        reverseTermWith_shiftLoose env cutoff argument]
  | _, env, cutoff, _, .lam body => by
      simp only [reverseTermWith, shiftLoose]
      rw [← reverseTermWith_shiftLoose (VarEnv.lift env) (cutoff + 1) body]
      congr 1
      refine reverseTermWith_congr (fun x => ?_) body
      cases x with
      | vz => simp [VarEnv.lift, shiftLoose]
      | vs x => exact (shiftLoose_shiftLoose (env x) (Nat.zero_le cutoff)).symm
  | _, _, cutoff, _, .top => (shiftLoose_of_closed truthDB_closed cutoff).symm
  | _, _, cutoff, _, .bot => (shiftLoose_of_closed falsityDefinitionDB_closed cutoff).symm
  | _, env, cutoff, _, .and p q => by
      simp only [reverseTermWith, shiftLoose]
      rw [reverseTermWith_shiftLoose env cutoff p, reverseTermWith_shiftLoose env cutoff q,
        shiftLoose_of_closed andDB_closed]
  | _, env, cutoff, _, .or p q => by
      simp only [reverseTermWith, shiftLoose]
      rw [reverseTermWith_shiftLoose env cutoff p, reverseTermWith_shiftLoose env cutoff q,
        shiftLoose_of_closed orDB_closed]
  | _, env, cutoff, _, .imp p q => by
      simp only [reverseTermWith, impAppDB, shiftLoose]
      rw [reverseTermWith_shiftLoose env cutoff p, reverseTermWith_shiftLoose env cutoff q,
        shiftLoose_of_closed impDB_closed]
  | _, env, cutoff, _, .not p => by
      simp only [reverseTermWith, shiftLoose]
      rw [reverseTermWith_shiftLoose env cutoff p, shiftLoose_of_closed notDB_closed]
  | _, env, cutoff, _, .eq left right => by
      simp only [reverseTermWith, CanonicalTerm.equalityDB, shiftLoose]
      rw [reverseTermWith_shiftLoose env cutoff left,
        reverseTermWith_shiftLoose env cutoff right]
  | _, env, cutoff, _, .all body => by
      simp only [reverseTermWith, shiftLoose]
      rw [← reverseTermWith_shiftLoose (VarEnv.lift env) (cutoff + 1) body,
        shiftLoose_of_closed (forallDB_closed _)]
      congr 2
      refine reverseTermWith_congr (fun x => ?_) body
      cases x with
      | vz => simp [VarEnv.lift, shiftLoose]
      | vs x => exact (shiftLoose_shiftLoose (env x) (Nat.zero_le cutoff)).symm
  | _, env, cutoff, _, .ex body => by
      simp only [reverseTermWith, shiftLoose]
      rw [← reverseTermWith_shiftLoose (VarEnv.lift env) (cutoff + 1) body,
        shiftLoose_of_closed (existsDB_closed _)]
      congr 2
      refine reverseTermWith_congr (fun x => ?_) body
      cases x with
      | vz => simp [VarEnv.lift, shiftLoose]
      | vs x => exact (shiftLoose_shiftLoose (env x) (Nat.zero_le cutoff)).symm

/-- Weakening a term shifts its translation past the new binder. -/
theorem reverseTermWith_weaken {Γ : HOL.Ctx AtomicTy} (env : VarEnv Γ) {σ τ : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol Γ τ) :
    reverseTermWith (VarEnv.lift (σ := σ) env) (HOL.weaken term) =
      shiftLoose 0 (reverseTermWith env term) := by
  rw [HOL.weaken, reverseTermWith_rename, ← reverseTermWith_shiftLoose]
  rfl

/-- Simultaneous substitution: translating a substituted term is translating
the term with each variable's image the translation of what replaces it. -/
theorem reverseTermWith_subst :
    ∀ {Γ Γ' : HOL.Ctx AtomicTy} (env : VarEnv Γ') (substitution : HOL.Subst Symbol Γ Γ')
      {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ),
      reverseTermWith env (HOL.subst substitution term) =
        reverseTermWith (fun x => reverseTermWith env (substitution x)) term
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, _, _, .const _ => rfl
  | _, _, env, s, _, .app function argument => by
      simp only [HOL.subst, reverseTermWith]
      rw [reverseTermWith_subst env s function, reverseTermWith_subst env s argument]
  | _, _, env, s, _, .lam body => by
      simp only [HOL.subst, reverseTermWith]
      rw [reverseTermWith_subst (VarEnv.lift env) (HOL.Subst.lift s) body]
      congr 1
      refine reverseTermWith_congr (fun x => ?_) body
      cases x with
      | vz => rfl
      | vs x => exact reverseTermWith_weaken env (s x)
  | _, _, _, _, _, .top => rfl
  | _, _, _, _, _, .bot => rfl
  | _, _, env, s, _, .and p q => by
      simp only [HOL.subst, reverseTermWith]
      rw [reverseTermWith_subst env s p, reverseTermWith_subst env s q]
  | _, _, env, s, _, .or p q => by
      simp only [HOL.subst, reverseTermWith]
      rw [reverseTermWith_subst env s p, reverseTermWith_subst env s q]
  | _, _, env, s, _, .imp p q => by
      simp only [HOL.subst, reverseTermWith]
      rw [reverseTermWith_subst env s p, reverseTermWith_subst env s q]
  | _, _, env, s, _, .not p => by
      simp only [HOL.subst, reverseTermWith]
      rw [reverseTermWith_subst env s p]
  | _, _, env, s, _, .eq left right => by
      simp only [HOL.subst, reverseTermWith]
      rw [reverseTermWith_subst env s left, reverseTermWith_subst env s right]
  | _, _, env, s, _, .all body => by
      simp only [HOL.subst, reverseTermWith]
      rw [reverseTermWith_subst (VarEnv.lift env) (HOL.Subst.lift s) body]
      congr 2
      refine reverseTermWith_congr (fun x => ?_) body
      cases x with
      | vz => rfl
      | vs x => exact reverseTermWith_weaken env (s x)
  | _, _, env, s, _, .ex body => by
      simp only [HOL.subst, reverseTermWith]
      rw [reverseTermWith_subst (VarEnv.lift env) (HOL.Subst.lift s) body]
      congr 2
      refine reverseTermWith_congr (fun x => ?_) body
      cases x with
      | vz => rfl
      | vs x => exact reverseTermWith_weaken env (s x)

/-! ## Loose indices and typing -/

/-- Loose indices of a translation come only from the images of the context
variables. -/
theorem looseBelow_reverseTermWith :
    ∀ {Γ : HOL.Ctx AtomicTy} {env : VarEnv Γ} {depth : Nat},
      (∀ {ρ : HOL.Ty AtomicTy} (x : HOL.Var Γ ρ), DBTerm.LooseBelow depth (env x)) →
      ∀ {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ),
        DBTerm.LooseBelow depth (reverseTermWith env term)
  | _, _, _, h, _, .var x => h x
  | _, _, depth, _, _, .const symbol =>
      looseBelow_mono (reverseSymbol_closed symbol) (Nat.zero_le depth)
  | _, _, _, h, _, .app function argument =>
      ⟨looseBelow_reverseTermWith h function, looseBelow_reverseTermWith h argument⟩
  | _, env, depth, h, _, .lam body =>
      looseBelow_reverseTermWith (env := VarEnv.lift env) (depth := depth + 1)
        (fun x => by
          cases x with
          | vz => exact Nat.succ_pos depth
          | vs x => exact looseBelow_shiftLoose 0 (h x)) body
  | _, _, depth, _, _, .top => looseBelow_mono truthDB_closed (Nat.zero_le depth)
  | _, _, depth, _, _, .bot => looseBelow_mono falsityDefinitionDB_closed (Nat.zero_le depth)
  | _, _, depth, h, _, .and p q =>
      ⟨⟨looseBelow_mono andDB_closed (Nat.zero_le depth), looseBelow_reverseTermWith h p⟩,
        looseBelow_reverseTermWith h q⟩
  | _, _, depth, h, _, .or p q =>
      ⟨⟨looseBelow_mono orDB_closed (Nat.zero_le depth), looseBelow_reverseTermWith h p⟩,
        looseBelow_reverseTermWith h q⟩
  | _, _, depth, h, _, .imp p q =>
      ⟨⟨looseBelow_mono impDB_closed (Nat.zero_le depth), looseBelow_reverseTermWith h p⟩,
        looseBelow_reverseTermWith h q⟩
  | _, _, depth, h, _, .not p =>
      ⟨looseBelow_mono notDB_closed (Nat.zero_le depth), looseBelow_reverseTermWith h p⟩
  | _, _, _, h, _, .eq left right =>
      ⟨⟨trivial, looseBelow_reverseTermWith h left⟩, looseBelow_reverseTermWith h right⟩
  | _, env, depth, h, _, .all body =>
      ⟨looseBelow_mono (forallDB_closed _) (Nat.zero_le depth),
        looseBelow_reverseTermWith (env := VarEnv.lift env) (depth := depth + 1)
          (fun x => by
            cases x with
            | vz => exact Nat.succ_pos depth
            | vs x => exact looseBelow_shiftLoose 0 (h x)) body⟩
  | _, env, depth, h, _, .ex body =>
      ⟨looseBelow_mono (existsDB_closed _) (Nat.zero_le depth),
        looseBelow_reverseTermWith (env := VarEnv.lift env) (depth := depth + 1)
          (fun x => by
            cases x with
            | vz => exact Nat.succ_pos depth
            | vs x => exact looseBelow_shiftLoose 0 (h x)) body⟩

theorem inferType_reverseSymbol (context : List Ty) {τ : HOL.Ty AtomicTy}
    (symbol : Symbol τ) : (reverseSymbol symbol).inferType context = some (reverseTy τ) := by
  cases symbol with
  | constant constant annotation typed =>
      subst typed
      simp [reverseSymbol, reverseTy_toHOL]
  | «variable» sourceVar typed =>
      subst typed
      simp [reverseSymbol, reverseTy_toHOL]

theorem inferType_app_app {context : List Ty} {function left right : DBTerm}
    {leftTy rightTy resultTy : Ty}
    (hfunction : function.inferType context =
      some (.function leftTy (.function rightTy resultTy)))
    (hleft : left.inferType context = some leftTy)
    (hright : right.inferType context = some rightTy) :
    (DBTerm.app (.app function left) right).inferType context = some resultTy :=
  DBTerm.inferType_app_eq_some_iff.mpr
    ⟨rightTy, DBTerm.inferType_app_eq_some_iff.mpr ⟨leftTy, hfunction, hleft⟩, hright⟩

/-- A translation is well typed at the reversed type, whenever every image of
a context variable is well typed at the reversed type of that variable. -/
theorem inferType_reverseTermWith :
    ∀ {Γ : HOL.Ctx AtomicTy} {env : VarEnv Γ} {context : List Ty},
      (∀ {ρ : HOL.Ty AtomicTy} (x : HOL.Var Γ ρ),
        (env x).inferType context = some (reverseTy ρ)) →
      ∀ {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ),
        (reverseTermWith env term).inferType context = some (reverseTy τ)
  | _, _, _, h, _, .var x => h x
  | _, _, context, _, _, .const symbol => inferType_reverseSymbol context symbol
  | _, _, _, h, _, .app function argument =>
      DBTerm.inferType_app_eq_some_iff.mpr
        ⟨_, inferType_reverseTermWith h function, inferType_reverseTermWith h argument⟩
  | _, env, context, h, _, .lam (σ := σ) body =>
      DBTerm.inferType_abs_eq_some_iff.mpr
        ⟨_, inferType_reverseTermWith (env := VarEnv.lift env)
          (context := reverseTy σ :: context)
          (fun x => by
            cases x with
            | vz => simp [VarEnv.lift]
            | vs x =>
                simp only [VarEnv.lift]
                rw [inferType_shiftLoose_zero]
                exact h x) body, rfl⟩
  | _, _, context, _, _, .top => DBTerm.inferType_weaken_empty truthDB_inferType context
  | _, _, context, _, _, .bot =>
      DBTerm.inferType_weaken_empty falsityDefinitionDB_inferType context
  | _, _, context, h, _, .and p q =>
      inferType_app_app (DBTerm.inferType_weaken_empty andDB_inferType context)
        (inferType_reverseTermWith h p) (inferType_reverseTermWith h q)
  | _, _, context, h, _, .or p q =>
      inferType_app_app (DBTerm.inferType_weaken_empty orDB_inferType context)
        (inferType_reverseTermWith h p) (inferType_reverseTermWith h q)
  | _, _, context, h, _, .imp p q =>
      inferType_app_app (DBTerm.inferType_weaken_empty impDB_inferType context)
        (inferType_reverseTermWith h p) (inferType_reverseTermWith h q)
  | _, _, context, h, _, .not p =>
      DBTerm.inferType_app_eq_some_iff.mpr
        ⟨_, DBTerm.inferType_weaken_empty notDB_inferType context,
          inferType_reverseTermWith h p⟩
  | _, _, _, h, _, .eq left right =>
      inferType_app_app (by simp [Ty.equality])
        (inferType_reverseTermWith h left) (inferType_reverseTermWith h right)
  | _, env, context, h, _, .all (σ := σ) body =>
      DBTerm.inferType_app_eq_some_iff.mpr
        ⟨_, DBTerm.inferType_weaken_empty (forallDB_inferType (reverseTy σ)) context,
          DBTerm.inferType_abs_eq_some_iff.mpr
            ⟨_, inferType_reverseTermWith (env := VarEnv.lift env)
              (context := reverseTy σ :: context)
              (fun x => by
                cases x with
                | vz => simp [VarEnv.lift]
                | vs x =>
                    simp only [VarEnv.lift]
                    rw [inferType_shiftLoose_zero]
                    exact h x) body, rfl⟩⟩
  | _, env, context, h, _, .ex (σ := σ) body =>
      DBTerm.inferType_app_eq_some_iff.mpr
        ⟨_, DBTerm.inferType_weaken_empty (existsDB_inferType (reverseTy σ)) context,
          DBTerm.inferType_abs_eq_some_iff.mpr
            ⟨_, inferType_reverseTermWith (env := VarEnv.lift env)
              (context := reverseTy σ :: context)
              (fun x => by
                cases x with
                | vz => simp [VarEnv.lift]
                | vs x =>
                    simp only [VarEnv.lift]
                    rw [inferType_shiftLoose_zero]
                    exact h x) body, rfl⟩⟩

/-! ## Binder instantiation -/

theorem instantiateAt_of_looseBelow (replacement : DBTerm) :
    ∀ {depth target : Nat} {term : DBTerm}, DBTerm.LooseBelow depth term →
      depth ≤ target → DBTerm.instantiateAt replacement target term = term
  | _, _, .const _ _, _, _ => by simp only [DBTerm.instantiateAt]
  | _, _, .free _, _, _ => by simp only [DBTerm.instantiateAt]
  | _, _, .bound _, hloose, hle =>
      DBTerm.instantiateAt_other _ _ _ (Nat.ne_of_lt (Nat.lt_of_lt_of_le hloose hle))
  | _, _, .app _ _, hloose, hle => by
      simp only [DBTerm.instantiateAt]
      rw [instantiateAt_of_looseBelow replacement hloose.1 hle,
        instantiateAt_of_looseBelow replacement hloose.2 hle]
  | _, _, .abs _ body, hloose, hle => by
      simp only [DBTerm.instantiateAt]
      rw [instantiateAt_of_looseBelow replacement (term := body) hloose (Nat.succ_le_succ hle)]

theorem instantiateAt_of_closed (replacement : DBTerm) {term : DBTerm}
    (closed : DBTerm.LooseBelow 0 term) (target : Nat) :
    DBTerm.instantiateAt replacement target term = term :=
  instantiateAt_of_looseBelow replacement closed (Nat.zero_le target)

theorem shiftLoose_instantiateAt {replacement : DBTerm}
    (closed : DBTerm.LooseBelow 0 replacement) :
    ∀ {cutoff target : Nat} (term : DBTerm), cutoff ≤ target →
      shiftLoose cutoff (DBTerm.instantiateAt replacement target term) =
        DBTerm.instantiateAt replacement (target + 1) (shiftLoose cutoff term)
  | _, _, .const _ _, _ => by simp only [shiftLoose, DBTerm.instantiateAt]
  | _, _, .free _, _ => by simp only [shiftLoose, DBTerm.instantiateAt]
  | cutoff, target, .bound index, hle => by
      by_cases htarget : index = target
      · subst htarget
        rw [DBTerm.instantiateAt_target, shiftLoose_of_closed closed]
        simp only [shiftLoose, if_neg (Nat.not_lt.mpr hle)]
        rw [DBTerm.instantiateAt_target]
      · rw [DBTerm.instantiateAt_other _ _ _ htarget]
        simp only [shiftLoose]
        split
        · rename_i hlt
          exact (DBTerm.instantiateAt_other _ _ _ (by omega)).symm
        · exact (DBTerm.instantiateAt_other _ _ _ (by omega)).symm
  | _, _, .app function argument, hle => by
      simp only [shiftLoose, DBTerm.instantiateAt]
      rw [shiftLoose_instantiateAt closed function hle,
        shiftLoose_instantiateAt closed argument hle]
  | _, _, .abs _ body, hle => by
      simp only [shiftLoose, DBTerm.instantiateAt]
      rw [shiftLoose_instantiateAt closed body (Nat.succ_le_succ hle)]

theorem instantiateAt_reverseSymbol (replacement : DBTerm) (target : Nat)
    {τ : HOL.Ty AtomicTy} (symbol : Symbol τ) :
    DBTerm.instantiateAt replacement target (reverseSymbol symbol) = reverseSymbol symbol :=
  instantiateAt_of_closed replacement (reverseSymbol_closed symbol) target

/-- OpenTheory instantiation of one index by a closed term commutes with the
translation. -/
theorem instantiateAt_reverseTermWith {replacement : DBTerm}
    (closed : DBTerm.LooseBelow 0 replacement) :
    ∀ {Γ : HOL.Ctx AtomicTy} (env : VarEnv Γ) (target : Nat) {τ : HOL.Ty AtomicTy}
      (term : HOL.Term Symbol Γ τ),
      DBTerm.instantiateAt replacement target (reverseTermWith env term) =
        reverseTermWith (fun x => DBTerm.instantiateAt replacement target (env x)) term
  | _, _, _, _, .var _ => rfl
  | _, _, target, _, .const symbol => instantiateAt_reverseSymbol replacement target symbol
  | _, env, target, _, .app function argument => by
      simp only [reverseTermWith, DBTerm.instantiateAt]
      rw [instantiateAt_reverseTermWith closed env target function,
        instantiateAt_reverseTermWith closed env target argument]
  | _, env, target, _, .lam body => by
      simp only [reverseTermWith, DBTerm.instantiateAt]
      rw [instantiateAt_reverseTermWith closed (VarEnv.lift env) (target + 1) body]
      congr 1
      refine reverseTermWith_congr (fun x => ?_) body
      cases x with
      | vz => exact DBTerm.instantiateAt_other _ _ _ (Nat.succ_ne_zero target).symm
      | vs x => exact (shiftLoose_instantiateAt closed (env x) (Nat.zero_le target)).symm
  | _, _, target, _, .top => instantiateAt_of_closed replacement truthDB_closed target
  | _, _, target, _, .bot =>
      instantiateAt_of_closed replacement falsityDefinitionDB_closed target
  | _, env, target, _, .and p q => by
      simp only [reverseTermWith, DBTerm.instantiateAt]
      rw [instantiateAt_reverseTermWith closed env target p,
        instantiateAt_reverseTermWith closed env target q,
        instantiateAt_of_closed replacement andDB_closed]
  | _, env, target, _, .or p q => by
      simp only [reverseTermWith, DBTerm.instantiateAt]
      rw [instantiateAt_reverseTermWith closed env target p,
        instantiateAt_reverseTermWith closed env target q,
        instantiateAt_of_closed replacement orDB_closed]
  | _, env, target, _, .imp p q => by
      simp only [reverseTermWith, impAppDB, DBTerm.instantiateAt]
      rw [instantiateAt_reverseTermWith closed env target p,
        instantiateAt_reverseTermWith closed env target q,
        instantiateAt_of_closed replacement impDB_closed]
  | _, env, target, _, .not p => by
      simp only [reverseTermWith, DBTerm.instantiateAt]
      rw [instantiateAt_reverseTermWith closed env target p,
        instantiateAt_of_closed replacement notDB_closed]
  | _, env, target, _, .eq left right => by
      simp only [reverseTermWith, CanonicalTerm.equalityDB, DBTerm.instantiateAt]
      rw [instantiateAt_reverseTermWith closed env target left,
        instantiateAt_reverseTermWith closed env target right]
  | _, env, target, _, .all body => by
      simp only [reverseTermWith, DBTerm.instantiateAt]
      rw [instantiateAt_reverseTermWith closed (VarEnv.lift env) (target + 1) body,
        instantiateAt_of_closed replacement (forallDB_closed _)]
      congr 2
      refine reverseTermWith_congr (fun x => ?_) body
      cases x with
      | vz => exact DBTerm.instantiateAt_other _ _ _ (Nat.succ_ne_zero target).symm
      | vs x => exact (shiftLoose_instantiateAt closed (env x) (Nat.zero_le target)).symm
  | _, env, target, _, .ex body => by
      simp only [reverseTermWith, DBTerm.instantiateAt]
      rw [instantiateAt_reverseTermWith closed (VarEnv.lift env) (target + 1) body,
        instantiateAt_of_closed replacement (existsDB_closed _)]
      congr 2
      refine reverseTermWith_congr (fun x => ?_) body
      cases x with
      | vz => exact DBTerm.instantiateAt_other _ _ _ (Nat.succ_ne_zero target).symm
      | vs x => exact (shiftLoose_instantiateAt closed (env x) (Nat.zero_le target)).symm

/-- Target beta instantiation is OpenTheory instantiation of index `0`, when
every context variable has a closed image. -/
theorem reverseTermWith_instantiate {Γ : HOL.Ctx AtomicTy} {env : VarEnv Γ}
    (envClosed : ∀ {ρ : HOL.Ty AtomicTy} (x : HOL.Var Γ ρ), DBTerm.LooseBelow 0 (env x))
    {σ τ : HOL.Ty AtomicTy} (argument : HOL.Term Symbol Γ σ)
    (body : HOL.Term Symbol (σ :: Γ) τ) :
    reverseTermWith env (HOL.instantiate argument body) =
      DBTerm.instantiateAt (reverseTermWith env argument) 0
        (reverseTermWith (VarEnv.lift env) body) := by
  rw [HOL.instantiate, reverseTermWith_subst,
    instantiateAt_reverseTermWith (looseBelow_reverseTermWith envClosed argument)]
  refine reverseTermWith_congr (fun x => ?_) body
  cases x with
  | vz => exact (DBTerm.instantiateAt_target _ _).symm
  | vs x =>
      show env x = DBTerm.instantiateAt _ 0 (shiftLoose 0 (env x))
      rw [shiftLoose_of_closed (envClosed x), instantiateAt_of_closed _ (envClosed x)]

/-! ## Abstraction of a free variable -/

theorem closeFreeAt_of_not_freeOccurrence (sourceVar : SourceVar) :
    ∀ (depth : Nat) {term : DBTerm}, ¬ DBTerm.FreeOccurrence sourceVar term →
      DBTerm.closeFreeAt sourceVar depth term = term
  | _, .const _ _, _ => by simp only [DBTerm.closeFreeAt]
  | depth, .free other, absent => by
      have different : sourceVar ≠ other := by
        rintro rfl
        exact absent .here
      exact DBTerm.closeFreeAt_other _ _ _ different
  | _, .bound _, _ => by simp only [DBTerm.closeFreeAt]
  | depth, .app _ _, absent => by
      simp only [DBTerm.closeFreeAt]
      rw [closeFreeAt_of_not_freeOccurrence sourceVar depth
          (fun found => absent (.appFunction found)),
        closeFreeAt_of_not_freeOccurrence sourceVar depth
          (fun found => absent (.appArgument found))]
  | depth, .abs _ _, absent => by
      simp only [DBTerm.closeFreeAt]
      rw [closeFreeAt_of_not_freeOccurrence sourceVar (depth + 1)
        (fun found => absent (.absBody found))]

theorem not_freeOccurrence_of_hasFree {sourceVar : SourceVar} {term : DBTerm}
    (h : DBTerm.hasFree sourceVar term = false) : ¬ DBTerm.FreeOccurrence sourceVar term :=
  fun found => by
    rw [← DBTerm.hasFree_eq_true_iff] at found
    rw [h] at found
    exact Bool.false_ne_true found

theorem not_freeOccurrence_truthDB (sourceVar : SourceVar) :
    ¬ DBTerm.FreeOccurrence sourceVar PrimitiveSentences.truthDB :=
  not_freeOccurrence_of_hasFree (by
    simp [DBTerm.hasFree, PrimitiveSentences.truthDB, CanonicalTerm.equalityDB,
      PrimitiveSentences.identityBool])

theorem not_freeOccurrence_forallDB (sourceVar : SourceVar) (A : Ty) :
    ¬ DBTerm.FreeOccurrence sourceVar (forallDB A) :=
  not_freeOccurrence_of_hasFree (by
    simp [DBTerm.hasFree, forallDB, PrimitiveSentences.truthDB, CanonicalTerm.equalityDB,
      PrimitiveSentences.identityBool])

theorem not_freeOccurrence_falsityDefinitionDB (sourceVar : SourceVar) :
    ¬ DBTerm.FreeOccurrence sourceVar falsityDefinitionDB :=
  not_freeOccurrence_of_hasFree (by
    simp [DBTerm.hasFree, falsityDefinitionDB, forallDB, PrimitiveSentences.truthDB,
      CanonicalTerm.equalityDB, PrimitiveSentences.identityBool])

theorem not_freeOccurrence_andDB (sourceVar : SourceVar) :
    ¬ DBTerm.FreeOccurrence sourceVar andDB :=
  not_freeOccurrence_of_hasFree (by
    simp [DBTerm.hasFree, andDB, PrimitiveSentences.truthDB, CanonicalTerm.equalityDB,
      PrimitiveSentences.identityBool])

theorem not_freeOccurrence_impDB (sourceVar : SourceVar) :
    ¬ DBTerm.FreeOccurrence sourceVar impDB :=
  not_freeOccurrence_of_hasFree (by
    simp [DBTerm.hasFree, impDB, andDB, PrimitiveSentences.truthDB,
      CanonicalTerm.equalityDB, PrimitiveSentences.identityBool])

theorem not_freeOccurrence_notDB (sourceVar : SourceVar) :
    ¬ DBTerm.FreeOccurrence sourceVar notDB :=
  not_freeOccurrence_of_hasFree (by
    simp [DBTerm.hasFree, notDB, impDB, andDB, falsityDefinitionDB, forallDB,
      PrimitiveSentences.truthDB, CanonicalTerm.equalityDB, PrimitiveSentences.identityBool])

theorem not_freeOccurrence_orDB (sourceVar : SourceVar) :
    ¬ DBTerm.FreeOccurrence sourceVar orDB :=
  not_freeOccurrence_of_hasFree (by
    simp [DBTerm.hasFree, orDB, impAppDB, impDB, andDB, forallDB,
      PrimitiveSentences.truthDB, CanonicalTerm.equalityDB, PrimitiveSentences.identityBool])

theorem not_freeOccurrence_existsDB (sourceVar : SourceVar) (A : Ty) :
    ¬ DBTerm.FreeOccurrence sourceVar (existsDB A) :=
  not_freeOccurrence_of_hasFree (by
    simp [DBTerm.hasFree, existsDB, impAppDB, impDB, andDB, forallDB,
      PrimitiveSentences.truthDB, CanonicalTerm.equalityDB, PrimitiveSentences.identityBool])

theorem freeOccurrence_of_freeOccurrence_shiftLoose {sourceVar : SourceVar} :
    ∀ {cutoff : Nat} {term : DBTerm},
      DBTerm.FreeOccurrence sourceVar (shiftLoose cutoff term) →
        DBTerm.FreeOccurrence sourceVar term
  | _, .const _ _, found => by cases found
  | _, .free _, found => found
  | cutoff, .bound index, found => by
      simp only [shiftLoose] at found
      split at found <;> cases found
  | _, .app _ _, found => by
      cases found with
      | appFunction found =>
          exact .appFunction (freeOccurrence_of_freeOccurrence_shiftLoose found)
      | appArgument found =>
          exact .appArgument (freeOccurrence_of_freeOccurrence_shiftLoose found)
  | _, .abs _ _, found => by
      cases found with
      | absBody found => exact .absBody (freeOccurrence_of_freeOccurrence_shiftLoose found)

theorem shiftLoose_closeFreeAt (sourceVar : SourceVar) :
    ∀ {cutoff depth : Nat} (term : DBTerm), cutoff ≤ depth →
      shiftLoose cutoff (DBTerm.closeFreeAt sourceVar depth term) =
        DBTerm.closeFreeAt sourceVar (depth + 1) (shiftLoose cutoff term)
  | _, _, .const _ _, _ => by simp only [shiftLoose, DBTerm.closeFreeAt]
  | cutoff, depth, .free other, hle => by
      by_cases same : sourceVar = other
      · subst same
        simp only [DBTerm.closeFreeAt_exact, shiftLoose, if_neg (Nat.not_lt.mpr hle)]
      · rw [DBTerm.closeFreeAt_other _ _ _ same]
        simp only [shiftLoose]
        rw [DBTerm.closeFreeAt_other _ _ _ same]
  | _, _, .bound _, _ => by
      simp only [shiftLoose, DBTerm.closeFreeAt]
      split <;> simp only [DBTerm.closeFreeAt]
  | _, _, .app function argument, hle => by
      simp only [shiftLoose, DBTerm.closeFreeAt]
      rw [shiftLoose_closeFreeAt sourceVar function hle,
        shiftLoose_closeFreeAt sourceVar argument hle]
  | _, _, .abs _ body, hle => by
      simp only [shiftLoose, DBTerm.closeFreeAt]
      rw [shiftLoose_closeFreeAt sourceVar body (Nat.succ_le_succ hle)]

theorem sigma_ne_of_noConstOccurrence_const {Γ : HOL.Ctx AtomicTy} {σ τ : HOL.Ty AtomicTy}
    {target : Symbol σ} {symbol : Symbol τ}
    (absent : HOL.NoConstOccurrence target (.const symbol : HOL.Term Symbol Γ τ)) :
    (⟨τ, symbol⟩ : Sigma Symbol) ≠ ⟨σ, target⟩ := by
  cases absent with
  | const_diff_type hne => exact fun h => hne (congrArg Sigma.fst h).symm
  | const_same_ne _ hne => exact fun h => hne (eq_of_heq (Sigma.mk.inj h).2)

/-- A symbol other than the variable symbol of `sourceVar` names a term in
which `sourceVar` does not occur. -/
theorem not_freeOccurrence_reverseSymbol {sourceVar : SourceVar} {τ : HOL.Ty AtomicTy}
    {symbol : Symbol τ}
    (different : (⟨τ, symbol⟩ : Sigma Symbol) ≠ ⟨_, Symbol.ofVar sourceVar⟩) :
    ¬ DBTerm.FreeOccurrence sourceVar (reverseSymbol symbol) := by
  cases symbol with
  | constant constant annotation typed =>
      intro found
      cases found
  | «variable» other typed =>
      intro found
      cases found
      subst typed
      exact different rfl

private theorem not_freeOccurrence_reverseTermWith_aux (sourceVar : SourceVar)
    {σ : HOL.Ty AtomicTy} (target : Symbol σ)
    (htarget : (⟨σ, target⟩ : Sigma Symbol) = ⟨_, Symbol.ofVar sourceVar⟩) :
    ∀ {Γ : HOL.Ctx AtomicTy} {env : VarEnv Γ},
      (∀ {ρ : HOL.Ty AtomicTy} (x : HOL.Var Γ ρ), ¬ DBTerm.FreeOccurrence sourceVar (env x)) →
      ∀ {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ),
        HOL.NoConstOccurrence target term →
          ¬ DBTerm.FreeOccurrence sourceVar (reverseTermWith env term)
  | _, _, h, _, .var x, _ => h x
  | _, _, _, _, .const _, absent =>
      not_freeOccurrence_reverseSymbol
        (fun h => sigma_ne_of_noConstOccurrence_const absent (h.trans htarget.symm))
  | _, _, h, _, .app function argument, absent => by
      cases absent with
      | app hfunction hargument =>
          intro found
          cases found with
          | appFunction found =>
              exact not_freeOccurrence_reverseTermWith_aux sourceVar target htarget h
                function hfunction found
          | appArgument found =>
              exact not_freeOccurrence_reverseTermWith_aux sourceVar target htarget h
                argument hargument found
  | _, env, h, _, .lam body, absent => by
      cases absent with
      | lam hbody =>
          intro found
          cases found with
          | absBody found =>
              refine not_freeOccurrence_reverseTermWith_aux sourceVar target htarget
                (env := VarEnv.lift env) (fun x => ?_) body hbody found
              cases x with
              | vz => intro found; cases found
              | vs x => exact fun found => h x (freeOccurrence_of_freeOccurrence_shiftLoose found)
  | _, _, _, _, .top, _ => not_freeOccurrence_truthDB sourceVar
  | _, _, _, _, .bot, _ => not_freeOccurrence_falsityDefinitionDB sourceVar
  | _, _, h, _, .and p q, absent => by
      cases absent with
      | and hp hq =>
          intro found
          cases found with
          | appFunction found =>
              cases found with
              | appFunction found => exact not_freeOccurrence_andDB sourceVar found
              | appArgument found =>
                  exact not_freeOccurrence_reverseTermWith_aux sourceVar target htarget h
                    p hp found
          | appArgument found =>
              exact not_freeOccurrence_reverseTermWith_aux sourceVar target htarget h
                q hq found
  | _, _, h, _, .or p q, absent => by
      cases absent with
      | or hp hq =>
          intro found
          cases found with
          | appFunction found =>
              cases found with
              | appFunction found => exact not_freeOccurrence_orDB sourceVar found
              | appArgument found =>
                  exact not_freeOccurrence_reverseTermWith_aux sourceVar target htarget h
                    p hp found
          | appArgument found =>
              exact not_freeOccurrence_reverseTermWith_aux sourceVar target htarget h
                q hq found
  | _, _, h, _, .imp p q, absent => by
      cases absent with
      | imp hp hq =>
          intro found
          cases found with
          | appFunction found =>
              cases found with
              | appFunction found => exact not_freeOccurrence_impDB sourceVar found
              | appArgument found =>
                  exact not_freeOccurrence_reverseTermWith_aux sourceVar target htarget h
                    p hp found
          | appArgument found =>
              exact not_freeOccurrence_reverseTermWith_aux sourceVar target htarget h
                q hq found
  | _, _, h, _, .not p, absent => by
      cases absent with
      | not hp =>
          intro found
          cases found with
          | appFunction found => exact not_freeOccurrence_notDB sourceVar found
          | appArgument found =>
              exact not_freeOccurrence_reverseTermWith_aux sourceVar target htarget h
                p hp found
  | _, _, h, _, .eq left right, absent => by
      cases absent with
      | eq hleft hright =>
          intro found
          cases found with
          | appFunction found =>
              cases found with
              | appFunction found => cases found
              | appArgument found =>
                  exact not_freeOccurrence_reverseTermWith_aux sourceVar target htarget h
                    left hleft found
          | appArgument found =>
              exact not_freeOccurrence_reverseTermWith_aux sourceVar target htarget h
                right hright found
  | _, env, h, _, .all body, absent => by
      cases absent with
      | all hbody =>
          intro found
          cases found with
          | appFunction found => exact not_freeOccurrence_forallDB sourceVar _ found
          | appArgument found =>
              cases found with
              | absBody found =>
                  refine not_freeOccurrence_reverseTermWith_aux sourceVar target htarget
                    (env := VarEnv.lift env) (fun x => ?_) body hbody found
                  cases x with
                  | vz => intro found; cases found
                  | vs x =>
                      exact fun found => h x (freeOccurrence_of_freeOccurrence_shiftLoose found)
  | _, env, h, _, .ex body, absent => by
      cases absent with
      | ex hbody =>
          intro found
          cases found with
          | appFunction found => exact not_freeOccurrence_existsDB sourceVar _ found
          | appArgument found =>
              cases found with
              | absBody found =>
                  refine not_freeOccurrence_reverseTermWith_aux sourceVar target htarget
                    (env := VarEnv.lift env) (fun x => ?_) body hbody found
                  cases x with
                  | vz => intro found; cases found
                  | vs x =>
                      exact fun found => h x (freeOccurrence_of_freeOccurrence_shiftLoose found)

/-- The translation mentions a free variable only through the images of the
context variables or through its variable symbol. -/
theorem not_freeOccurrence_reverseTermWith {sourceVar : SourceVar} {Γ : HOL.Ctx AtomicTy}
    {env : VarEnv Γ}
    (envAbsent : ∀ {ρ : HOL.Ty AtomicTy} (x : HOL.Var Γ ρ),
      ¬ DBTerm.FreeOccurrence sourceVar (env x))
    {τ : HOL.Ty AtomicTy} {term : HOL.Term Symbol Γ τ}
    (symbolAbsent : HOL.NoConstOccurrence (Symbol.ofVar sourceVar) term) :
    ¬ DBTerm.FreeOccurrence sourceVar (reverseTermWith env term) :=
  not_freeOccurrence_reverseTermWith_aux sourceVar _ rfl envAbsent term symbolAbsent

private theorem closeFreeAt_reverseTermWith_aux (sourceVar : SourceVar)
    {σ : HOL.Ty AtomicTy} (target : Symbol σ)
    (htarget : (⟨σ, target⟩ : Sigma Symbol) = ⟨_, Symbol.ofVar sourceVar⟩) :
    ∀ {Γ : HOL.Ctx AtomicTy} (env : VarEnv Γ) (depth : Nat) {τ : HOL.Ty AtomicTy}
      (term : HOL.Term Symbol Γ τ), HOL.NoConstOccurrence target term →
        DBTerm.closeFreeAt sourceVar depth (reverseTermWith env term) =
          reverseTermWith (fun x => DBTerm.closeFreeAt sourceVar depth (env x)) term
  | _, _, _, _, .var _, _ => rfl
  | _, _, depth, _, .const _, absent =>
      closeFreeAt_of_not_freeOccurrence sourceVar depth
        (not_freeOccurrence_reverseSymbol
          (fun h => sigma_ne_of_noConstOccurrence_const absent (h.trans htarget.symm)))
  | _, env, depth, _, .app function argument, absent => by
      cases absent with
      | app hfunction hargument =>
          simp only [reverseTermWith, DBTerm.closeFreeAt]
          rw [closeFreeAt_reverseTermWith_aux sourceVar target htarget env depth function
              hfunction,
            closeFreeAt_reverseTermWith_aux sourceVar target htarget env depth argument
              hargument]
  | _, env, depth, _, .lam body, absent => by
      cases absent with
      | lam hbody =>
          simp only [reverseTermWith, DBTerm.closeFreeAt]
          rw [closeFreeAt_reverseTermWith_aux sourceVar target htarget (VarEnv.lift env)
            (depth + 1) body hbody]
          congr 1
          refine reverseTermWith_congr (fun x => ?_) body
          cases x with
          | vz => simp only [VarEnv.lift, DBTerm.closeFreeAt]
          | vs x => exact (shiftLoose_closeFreeAt sourceVar (env x) (Nat.zero_le depth)).symm
  | _, _, depth, _, .top, _ =>
      closeFreeAt_of_not_freeOccurrence sourceVar depth (not_freeOccurrence_truthDB sourceVar)
  | _, _, depth, _, .bot, _ =>
      closeFreeAt_of_not_freeOccurrence sourceVar depth
        (not_freeOccurrence_falsityDefinitionDB sourceVar)
  | _, env, depth, _, .and p q, absent => by
      cases absent with
      | and hp hq =>
          simp only [reverseTermWith, DBTerm.closeFreeAt]
          rw [closeFreeAt_reverseTermWith_aux sourceVar target htarget env depth p hp,
            closeFreeAt_reverseTermWith_aux sourceVar target htarget env depth q hq,
            closeFreeAt_of_not_freeOccurrence sourceVar depth
              (not_freeOccurrence_andDB sourceVar)]
  | _, env, depth, _, .or p q, absent => by
      cases absent with
      | or hp hq =>
          simp only [reverseTermWith, DBTerm.closeFreeAt]
          rw [closeFreeAt_reverseTermWith_aux sourceVar target htarget env depth p hp,
            closeFreeAt_reverseTermWith_aux sourceVar target htarget env depth q hq,
            closeFreeAt_of_not_freeOccurrence sourceVar depth
              (not_freeOccurrence_orDB sourceVar)]
  | _, env, depth, _, .imp p q, absent => by
      cases absent with
      | imp hp hq =>
          simp only [reverseTermWith, impAppDB, DBTerm.closeFreeAt]
          rw [closeFreeAt_reverseTermWith_aux sourceVar target htarget env depth p hp,
            closeFreeAt_reverseTermWith_aux sourceVar target htarget env depth q hq,
            closeFreeAt_of_not_freeOccurrence sourceVar depth
              (not_freeOccurrence_impDB sourceVar)]
  | _, env, depth, _, .not p, absent => by
      cases absent with
      | not hp =>
          simp only [reverseTermWith, DBTerm.closeFreeAt]
          rw [closeFreeAt_reverseTermWith_aux sourceVar target htarget env depth p hp,
            closeFreeAt_of_not_freeOccurrence sourceVar depth
              (not_freeOccurrence_notDB sourceVar)]
  | _, env, depth, _, .eq left right, absent => by
      cases absent with
      | eq hleft hright =>
          simp only [reverseTermWith, CanonicalTerm.equalityDB, DBTerm.closeFreeAt]
          rw [closeFreeAt_reverseTermWith_aux sourceVar target htarget env depth left hleft,
            closeFreeAt_reverseTermWith_aux sourceVar target htarget env depth right hright]
  | _, env, depth, _, .all body, absent => by
      cases absent with
      | all hbody =>
          simp only [reverseTermWith, DBTerm.closeFreeAt]
          rw [closeFreeAt_reverseTermWith_aux sourceVar target htarget (VarEnv.lift env)
              (depth + 1) body hbody,
            closeFreeAt_of_not_freeOccurrence sourceVar depth
              (not_freeOccurrence_forallDB sourceVar _)]
          congr 2
          refine reverseTermWith_congr (fun x => ?_) body
          cases x with
          | vz => simp only [VarEnv.lift, DBTerm.closeFreeAt]
          | vs x => exact (shiftLoose_closeFreeAt sourceVar (env x) (Nat.zero_le depth)).symm
  | _, env, depth, _, .ex body, absent => by
      cases absent with
      | ex hbody =>
          simp only [reverseTermWith, DBTerm.closeFreeAt]
          rw [closeFreeAt_reverseTermWith_aux sourceVar target htarget (VarEnv.lift env)
              (depth + 1) body hbody,
            closeFreeAt_of_not_freeOccurrence sourceVar depth
              (not_freeOccurrence_existsDB sourceVar _)]
          congr 2
          refine reverseTermWith_congr (fun x => ?_) body
          cases x with
          | vz => simp only [VarEnv.lift, DBTerm.closeFreeAt]
          | vs x => exact (shiftLoose_closeFreeAt sourceVar (env x) (Nat.zero_le depth)).symm

/-- Closing a free variable that no symbol of the term names commutes with the
translation. -/
theorem closeFreeAt_reverseTermWith {sourceVar : SourceVar} {Γ : HOL.Ctx AtomicTy}
    (env : VarEnv Γ) (depth : Nat) {τ : HOL.Ty AtomicTy} {term : HOL.Term Symbol Γ τ}
    (symbolAbsent : HOL.NoConstOccurrence (Symbol.ofVar sourceVar) term) :
    DBTerm.closeFreeAt sourceVar depth (reverseTermWith env term) =
      reverseTermWith (fun x => DBTerm.closeFreeAt sourceVar depth (env x)) term :=
  closeFreeAt_reverseTermWith_aux sourceVar _ rfl env depth term symbolAbsent

/-! ## Naming the context -/

/-- Names for the variables of a target context.  The variable `x : Var Γ τ`
becomes the OpenTheory free variable `⟨names x, reverseTy τ⟩`. -/
abbrev Naming (Γ : HOL.Ctx AtomicTy) : Type :=
  ∀ {τ : HOL.Ty AtomicTy}, HOL.Var Γ τ → Name

namespace Naming

/-- The OpenTheory free variable of a context variable. -/
def sourceVar {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) {τ : HOL.Ty AtomicTy}
    (x : HOL.Var Γ τ) : SourceVar :=
  ⟨names x, reverseTy τ⟩

/-- Context variables as OpenTheory free variables. -/
def env {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) : VarEnv Γ :=
  fun x => .free (sourceVar names x)

/-- Extend a naming by the name of a new innermost variable. -/
def cons {Γ : HOL.Ctx AtomicTy} {σ : HOL.Ty AtomicTy} (name : Name) (names : Naming Γ) :
    Naming (σ :: Γ)
  | _, .vz => name
  | _, .vs x => names x

/-- The naming of the empty context. -/
def empty : Naming [] := fun x => nomatch x

/-- The names of all context variables, innermost first. -/
def toList : {Γ : HOL.Ctx AtomicTy} → Naming Γ → List Name
  | [], _ => []
  | _ :: _, names => names .vz :: toList (fun x => names (.vs x))

theorem mem_toList : ∀ {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) {τ : HOL.Ty AtomicTy}
    (x : HOL.Var Γ τ), names x ∈ toList names
  | _ :: _, _, _, .vz => List.mem_cons_self
  | _ :: _, names, _, .vs x =>
      List.mem_cons_of_mem _ (mem_toList (fun y => names (.vs y)) x)

/-- Distinct context variables have distinct OpenTheory free variables. -/
def Injective {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) : Prop :=
  ∀ {τ τ' : HOL.Ty AtomicTy} (x : HOL.Var Γ τ) (y : HOL.Var Γ τ'),
    sourceVar names x = sourceVar names y → deBruijnIndex x = deBruijnIndex y

/-- No context variable is named by the free variable `excluded`. -/
def Avoids {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) (excluded : SourceVar) : Prop :=
  ∀ {τ : HOL.Ty AtomicTy} (x : HOL.Var Γ τ), sourceVar names x ≠ excluded

theorem avoids_of_not_mem_toList {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) {name : Name}
    (fresh : name ∉ toList names) (ty : Ty) : Avoids names ⟨name, ty⟩ := by
  intro τ x h
  have hname : names x = name := congrArg Var.name h
  exact fresh (hname ▸ mem_toList names x)

theorem injective_empty : Injective empty := fun x => nomatch x

theorem injective_cons {Γ : HOL.Ctx AtomicTy} {σ : HOL.Ty AtomicTy} {names : Naming Γ}
    {name : Name} (injective : Injective names) (fresh : Avoids names ⟨name, reverseTy σ⟩) :
    Injective (cons (σ := σ) name names) := by
  intro τ τ' x y h
  cases x with
  | vz =>
      cases y with
      | vz => rfl
      | vs y => exact absurd h.symm (fresh y)
  | vs x =>
      cases y with
      | vz => exact absurd h (fresh x)
      | vs y => simp only [deBruijnIndex, injective x y h]

theorem env_closed {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) {τ : HOL.Ty AtomicTy}
    (x : HOL.Var Γ τ) : DBTerm.LooseBelow 0 (env names x) := trivial

theorem inferType_env {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) (context : List Ty)
    {τ : HOL.Ty AtomicTy} (x : HOL.Var Γ τ) :
    (env names x).inferType context = some (reverseTy τ) := by
  simp [env, sourceVar]

/-- Lifting a naming's images under a binder leaves the named variables
free. -/
theorem lift_env_vs {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) {σ τ : HOL.Ty AtomicTy}
    (x : HOL.Var Γ τ) : VarEnv.lift (σ := σ) (env names) (.vs x) = env names x := rfl

end Naming

/-- The reverse translation with context variables named by OpenTheory free
variables.  It produces closed canonical terms. -/
def reverseTerm {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) {τ : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol Γ τ) : DBTerm :=
  reverseTermWith (Naming.env names) term

theorem looseBelow_zero_reverseTerm {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) {τ : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol Γ τ) : DBTerm.LooseBelow 0 (reverseTerm names term) :=
  looseBelow_reverseTermWith (Naming.env_closed names) term

theorem inferType_reverseTerm {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) (context : List Ty)
    {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ) :
    (reverseTerm names term).inferType context = some (reverseTy τ) :=
  inferType_reverseTermWith (Naming.inferType_env names context) term

/-- On closed terms the two variable images agree. -/
theorem reverseTerm_eq_reverseTermOpen {τ : HOL.Ty AtomicTy}
    (term : HOL.ClosedTerm Symbol τ) :
    reverseTerm Naming.empty term = reverseTermOpen term :=
  reverseTermWith_congr (fun {_} (x : HOL.Var [] _) => nomatch x) term

/-- Reversal commutes with weakening: the new innermost variable is not
mentioned. -/
theorem reverseTerm_weaken {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) {σ τ : HOL.Ty AtomicTy}
    (name : Name) (term : HOL.Term Symbol Γ τ) :
    reverseTerm (Naming.cons (σ := σ) name names) (HOL.weaken term) =
      reverseTerm names term := by
  rw [reverseTerm, HOL.weaken, reverseTermWith_rename]
  rfl

/-- Reversal commutes with renaming, the naming being pulled back along the
renaming. -/
theorem reverseTerm_rename {Γ Γ' : HOL.Ctx AtomicTy} (names : Naming Γ')
    (ρ : HOL.Rename AtomicTy Γ Γ') {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ) :
    reverseTerm names (HOL.rename ρ term) = reverseTerm (fun x => names (ρ x)) term := by
  rw [reverseTerm, reverseTermWith_rename]
  rfl

/-- Target beta instantiation is OpenTheory instantiation of the outermost
bound index of the reversed body. -/
theorem reverseTerm_instantiate {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {σ τ : HOL.Ty AtomicTy} (argument : HOL.Term Symbol Γ σ)
    (body : HOL.Term Symbol (σ :: Γ) τ) :
    reverseTerm names (HOL.instantiate argument body) =
      DBTerm.instantiateAt (reverseTerm names argument) 0
        (reverseTermWith (VarEnv.lift (Naming.env names)) body) :=
  reverseTermWith_instantiate (Naming.env_closed names) argument body

/-- Abstracting the fresh name of the innermost variable turns the reverse of
a body under the extended naming into the body of the reverse of its
abstraction. -/
theorem closeFreeAt_reverseTerm_cons {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {σ τ : HOL.Ty AtomicTy} (name : Name) (body : HOL.Term Symbol (σ :: Γ) τ)
    (fresh : Naming.Avoids names ⟨name, reverseTy σ⟩)
    (symbolAbsent : HOL.NoConstOccurrence (Symbol.ofVar ⟨name, reverseTy σ⟩) body) :
    DBTerm.closeFreeAt ⟨name, reverseTy σ⟩ 0 (reverseTerm (Naming.cons name names) body) =
      reverseTermWith (VarEnv.lift (Naming.env names)) body := by
  rw [reverseTerm, closeFreeAt_reverseTermWith _ _ symbolAbsent]
  refine reverseTermWith_congr (fun x => ?_) body
  cases x with
  | vz =>
      show DBTerm.closeFreeAt _ 0 (.free ⟨name, reverseTy σ⟩) = .bound 0
      exact DBTerm.closeFreeAt_exact _ 0
  | vs x =>
      exact DBTerm.closeFreeAt_other _ _ 0 (fresh x).symm

@[simp] theorem reverseTerm_all {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) {σ : HOL.Ty AtomicTy}
    (body : HOL.Formula Symbol (σ :: Γ)) :
    reverseTerm names (.all body) = .app (forallDB (reverseTy σ)) (reverseTerm names (.lam body)) :=
  rfl

@[simp] theorem reverseTerm_ex {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) {σ : HOL.Ty AtomicTy}
    (body : HOL.Formula Symbol (σ :: Γ)) :
    reverseTerm names (.ex body) = .app (existsDB (reverseTy σ)) (reverseTerm names (.lam body)) :=
  rfl

/-- The substitution closing a context by the variable symbols of its names. -/
def Naming.closingSubst {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) : HOL.Subst Symbol Γ [] :=
  fun {τ} x => .const (.variable (Naming.sourceVar names x) (toHOL_reverseTy τ))

/-- Naming the context variables is closing them by variable symbols and then
reversing the closed term. -/
theorem reverseTerm_eq_reverseTermOpen_closingSubst {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ) :
    reverseTerm names term = reverseTermOpen (HOL.subst (Naming.closingSubst names) term) := by
  rw [reverseTermOpen, reverseTermWith_subst]
  rfl

/-! ## Canonical terms and hypothesis sets -/

/-- The checked canonical term of a reversed term. -/
def reverseCanonical {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) {τ : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol Γ τ) : CanonicalTerm :=
  ⟨reverseTerm names term, reverseTy τ, inferType_reverseTerm names [] term⟩

@[simp] theorem reverseCanonical_term {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ) :
    (reverseCanonical names term).term = reverseTerm names term := rfl

@[simp] theorem reverseCanonical_ty {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ) :
    (reverseCanonical names term).ty = reverseTy τ := rfl

theorem reverseCanonical_isBool {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    (formula : HOL.Formula Symbol Γ) : (reverseCanonical names formula).IsBool := rfl

theorem reverseCanonical_weaken {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {σ τ : HOL.Ty AtomicTy} (name : Name) (term : HOL.Term Symbol Γ τ) :
    reverseCanonical (Naming.cons (σ := σ) name names) (HOL.weaken term) =
      reverseCanonical names term :=
  CanonicalTerm.ext_term (reverseTerm_weaken names name term)

/-- Target beta reduction is OpenTheory beta reduction of the reversed
redex. -/
theorem betaReductionSemantics_reverseCanonical {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {σ τ : HOL.Ty AtomicTy} (argument : HOL.Term Symbol Γ σ)
    (body : HOL.Term Symbol (σ :: Γ) τ) :
    CanonicalTerm.BetaReductionSemantics
      (reverseCanonical names (.app (.lam body) argument))
      (reverseCanonical names (HOL.instantiate argument body)) :=
  ⟨reverseTy σ, reverseTermWith (VarEnv.lift (Naming.env names)) body,
    reverseCanonical names argument, rfl, reverseTerm_instantiate names argument body⟩

/-- Abstracting the fresh name of the innermost variable is the reverse of the
target abstraction. -/
theorem abstractionSemantics_reverseCanonical_cons {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {σ τ : HOL.Ty AtomicTy} (name : Name) (body : HOL.Term Symbol (σ :: Γ) τ)
    (fresh : Naming.Avoids names ⟨name, reverseTy σ⟩)
    (symbolAbsent : HOL.NoConstOccurrence (Symbol.ofVar ⟨name, reverseTy σ⟩) body) :
    CanonicalTerm.AbstractionSemantics ⟨name, reverseTy σ⟩
      (reverseCanonical (Naming.cons name names) body) (reverseCanonical names (.lam body)) := by
  show DBTerm.abs (reverseTy σ) (reverseTermWith (VarEnv.lift (Naming.env names)) body) =
    DBTerm.abs (reverseTy σ) (DBTerm.closeFreeAt ⟨name, reverseTy σ⟩ 0
      (reverseTerm (Naming.cons name names) body))
  rw [closeFreeAt_reverseTerm_cons names name body fresh symbolAbsent]

theorem betaReduce?_reverseCanonical {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {σ τ : HOL.Ty AtomicTy} (argument : HOL.Term Symbol Γ σ)
    (body : HOL.Term Symbol (σ :: Γ) τ) :
    (reverseCanonical names (.app (.lam body) argument)).betaReduce? =
      some (reverseCanonical names (HOL.instantiate argument body)) :=
  (CanonicalTerm.betaReduce?_eq_some_iff _ _).mpr
    (betaReductionSemantics_reverseCanonical names argument body)

theorem abstractFree_reverseCanonical_cons {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {σ τ : HOL.Ty AtomicTy} (name : Name) (body : HOL.Term Symbol (σ :: Γ) τ)
    (fresh : Naming.Avoids names ⟨name, reverseTy σ⟩)
    (symbolAbsent : HOL.NoConstOccurrence (Symbol.ofVar ⟨name, reverseTy σ⟩) body) :
    (reverseCanonical (Naming.cons name names) body).abstractFree ⟨name, reverseTy σ⟩ =
      reverseCanonical names (.lam body) :=
  (CanonicalTerm.abstractFree_eq_iff _ _ _).mpr
    (abstractionSemantics_reverseCanonical_cons names name body fresh symbolAbsent)

/-- Instantiating the innermost context variable is, in OpenTheory,
abstracting its fresh name and instantiating the new binder: the effect of
abstraction followed by beta conversion. -/
theorem reverseTerm_instantiate_eq_instantiateAt_closeFreeAt {Γ : HOL.Ctx AtomicTy}
    (names : Naming Γ) {σ τ : HOL.Ty AtomicTy} (name : Name) (argument : HOL.Term Symbol Γ σ)
    (body : HOL.Term Symbol (σ :: Γ) τ) (fresh : Naming.Avoids names ⟨name, reverseTy σ⟩)
    (symbolAbsent : HOL.NoConstOccurrence (Symbol.ofVar ⟨name, reverseTy σ⟩) body) :
    reverseTerm names (HOL.instantiate argument body) =
      DBTerm.instantiateAt (reverseTerm names argument) 0
        (DBTerm.closeFreeAt ⟨name, reverseTy σ⟩ 0 (reverseTerm (Naming.cons name names) body)) := by
  rw [closeFreeAt_reverseTerm_cons names name body fresh symbolAbsent, reverseTerm_instantiate]

/-- The hypothesis set of reversed formulas. -/
def reverseHypotheses {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    (hypotheses : List (HOL.Formula Symbol Γ)) : Finset CanonicalTerm :=
  (hypotheses.map (reverseCanonical names)).toFinset

theorem mem_reverseHypotheses {Γ : HOL.Ctx AtomicTy} {names : Naming Γ}
    {hypotheses : List (HOL.Formula Symbol Γ)} {term : CanonicalTerm} :
    term ∈ reverseHypotheses names hypotheses ↔
      ∃ ψ ∈ hypotheses, reverseCanonical names ψ = term := by
  simp [reverseHypotheses]

@[simp] theorem reverseHypotheses_nil {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) :
    reverseHypotheses names [] = ∅ := rfl

theorem reverseHypotheses_cons {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    (φ : HOL.Formula Symbol Γ) (hypotheses : List (HOL.Formula Symbol Γ)) :
    reverseHypotheses names (φ :: hypotheses) =
      insert (reverseCanonical names φ) (reverseHypotheses names hypotheses) := by
  simp [reverseHypotheses]

theorem reverseCanonical_mem_reverseHypotheses {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {hypotheses : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (member : φ ∈ hypotheses) : reverseCanonical names φ ∈ reverseHypotheses names hypotheses :=
  mem_reverseHypotheses.mpr ⟨φ, member, rfl⟩

theorem reverseHypotheses_mono {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {hypotheses hypotheses' : List (HOL.Formula Symbol Γ)}
    (subset : ∀ ψ ∈ hypotheses, ψ ∈ hypotheses') :
    reverseHypotheses names hypotheses ⊆ reverseHypotheses names hypotheses' := by
  intro term member
  obtain ⟨ψ, hψ, rfl⟩ := mem_reverseHypotheses.mp member
  exact reverseCanonical_mem_reverseHypotheses names (subset ψ hψ)

theorem isBool_of_mem_reverseHypotheses {Γ : HOL.Ctx AtomicTy} {names : Naming Γ}
    {hypotheses : List (HOL.Formula Symbol Γ)} {term : CanonicalTerm}
    (member : term ∈ reverseHypotheses names hypotheses) : term.IsBool := by
  obtain ⟨ψ, _, rfl⟩ := mem_reverseHypotheses.mp member
  exact reverseCanonical_isBool names ψ

/-- Weakening the hypotheses under a new innermost variable does not change
their reversal. -/
theorem reverseHypotheses_weakenHyps {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {σ : HOL.Ty AtomicTy} (name : Name) (hypotheses : List (HOL.Formula Symbol Γ)) :
    reverseHypotheses (Naming.cons (σ := σ) name names) (HOL.weakenHyps hypotheses) =
      reverseHypotheses names hypotheses := by
  simp only [reverseHypotheses, HOL.weakenHyps, List.map_map]
  congr 1
  exact List.map_congr_left fun ψ _ => reverseCanonical_weaken names name ψ

/-- A free variable avoided by the naming and named by no symbol of the
hypotheses is not free in their reversal. -/
theorem not_freeInHypotheses_reverseHypotheses {Γ : HOL.Ctx AtomicTy} {names : Naming Γ}
    {sourceVar : SourceVar} (fresh : Naming.Avoids names sourceVar)
    {hypotheses : List (HOL.Formula Symbol Γ)}
    (symbolAbsent : ∀ ψ ∈ hypotheses, HOL.NoConstOccurrence (Symbol.ofVar sourceVar) ψ) :
    ¬ FreeInHypotheses sourceVar (reverseHypotheses names hypotheses) := by
  rintro ⟨term, member, found⟩
  obtain ⟨ψ, hψ, rfl⟩ := mem_reverseHypotheses.mp member
  refine not_freeOccurrence_reverseTermWith (fun x found => ?_) (symbolAbsent ψ hψ) found
  cases found
  exact fresh x rfl

/-! ## Fresh names -/

/-- The names of the free variables named by the variable symbols of a
term. -/
def variableSymbolNames : {Γ : HOL.Ctx AtomicTy} → {τ : HOL.Ty AtomicTy} →
    HOL.Term Symbol Γ τ → List Name
  | _, _, .var _ => []
  | _, _, .const (.constant ..) => []
  | _, _, .const (.variable sourceVar _) => [sourceVar.name]
  | _, _, .app function argument =>
      variableSymbolNames function ++ variableSymbolNames argument
  | _, _, .lam body => variableSymbolNames body
  | _, _, .top => []
  | _, _, .bot => []
  | _, _, .and p q => variableSymbolNames p ++ variableSymbolNames q
  | _, _, .or p q => variableSymbolNames p ++ variableSymbolNames q
  | _, _, .imp p q => variableSymbolNames p ++ variableSymbolNames q
  | _, _, .not p => variableSymbolNames p
  | _, _, .eq left right => variableSymbolNames left ++ variableSymbolNames right
  | _, _, .all body => variableSymbolNames body
  | _, _, .ex body => variableSymbolNames body

theorem noConstOccurrence_of_not_mem_variableSymbolNames {name : Name} (ty : Ty) :
    ∀ {Γ : HOL.Ctx AtomicTy} {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ),
      name ∉ variableSymbolNames term →
        HOL.NoConstOccurrence (Symbol.ofVar ⟨name, ty⟩) term
  | _, _, .var _, _ => .var
  | _, _, .const (.constant constant annotation typed), _ =>
      Symbol.noConstOccurrence_const _ _ (Symbol.sigma_constant_ne_ofVar _ _ typed _)
  | _, _, .const (.variable other typed), absent => by
      have different : other ≠ ⟨name, ty⟩ := by
        rintro rfl
        exact absent (List.mem_singleton_self _)
      exact Symbol.noConstOccurrence_const _ _ (Symbol.sigma_variable_ne_ofVar typed different)
  | _, _, .app function argument, absent => by
      simp only [variableSymbolNames, List.mem_append, not_or] at absent
      exact .app (noConstOccurrence_of_not_mem_variableSymbolNames ty function absent.1)
        (noConstOccurrence_of_not_mem_variableSymbolNames ty argument absent.2)
  | _, _, .lam body, absent =>
      .lam (noConstOccurrence_of_not_mem_variableSymbolNames ty body absent)
  | _, _, .top, _ => .top
  | _, _, .bot, _ => .bot
  | _, _, .and p q, absent => by
      simp only [variableSymbolNames, List.mem_append, not_or] at absent
      exact .and (noConstOccurrence_of_not_mem_variableSymbolNames ty p absent.1)
        (noConstOccurrence_of_not_mem_variableSymbolNames ty q absent.2)
  | _, _, .or p q, absent => by
      simp only [variableSymbolNames, List.mem_append, not_or] at absent
      exact .or (noConstOccurrence_of_not_mem_variableSymbolNames ty p absent.1)
        (noConstOccurrence_of_not_mem_variableSymbolNames ty q absent.2)
  | _, _, .imp p q, absent => by
      simp only [variableSymbolNames, List.mem_append, not_or] at absent
      exact .imp (noConstOccurrence_of_not_mem_variableSymbolNames ty p absent.1)
        (noConstOccurrence_of_not_mem_variableSymbolNames ty q absent.2)
  | _, _, .not p, absent =>
      .not (noConstOccurrence_of_not_mem_variableSymbolNames ty p absent)
  | _, _, .eq left right, absent => by
      simp only [variableSymbolNames, List.mem_append, not_or] at absent
      exact .eq (noConstOccurrence_of_not_mem_variableSymbolNames ty left absent.1)
        (noConstOccurrence_of_not_mem_variableSymbolNames ty right absent.2)
  | _, _, .all body, absent =>
      .all (noConstOccurrence_of_not_mem_variableSymbolNames ty body absent)
  | _, _, .ex body, absent =>
      .ex (noConstOccurrence_of_not_mem_variableSymbolNames ty body absent)

/-- The longest namespace among the given names. -/
def maxNamespaceLength : List Name → Nat
  | [] => 0
  | name :: names => max name.namespaceComponents.length (maxNamespaceLength names)

theorem namespaceComponents_length_le_maxNamespaceLength :
    ∀ {names : List Name} {name : Name}, name ∈ names →
      name.namespaceComponents.length ≤ maxNamespaceLength names
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ member =>
      Nat.le_trans (namespaceComponents_length_le_maxNamespaceLength member)
        (Nat.le_max_right _ _)

/-- A name whose namespace is longer than every namespace in `avoid`. -/
def freshName (avoid : List Name) : Name :=
  ⟨List.replicate (maxNamespaceLength avoid + 1) "", "x"⟩

theorem freshName_not_mem (avoid : List Name) : freshName avoid ∉ avoid := by
  intro member
  have := namespaceComponents_length_le_maxNamespaceLength member
  simp [freshName] at this

/-- A name for a new innermost variable that is avoided by the naming and by
every variable symbol of the body and of the hypotheses: the side conditions
of `abstractionSemantics_reverseCanonical_cons`,
`not_freeInHypotheses_reverseHypotheses` and `Naming.injective_cons`. -/
theorem exists_fresh_name {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) (σ : HOL.Ty AtomicTy)
    {τ : HOL.Ty AtomicTy} (body : HOL.Term Symbol (σ :: Γ) τ)
    (hypotheses : List (HOL.Formula Symbol Γ)) :
    ∃ name : Name, Naming.Avoids names ⟨name, reverseTy σ⟩ ∧
      HOL.NoConstOccurrence (Symbol.ofVar ⟨name, reverseTy σ⟩) body ∧
      ∀ ψ ∈ hypotheses, HOL.NoConstOccurrence (Symbol.ofVar ⟨name, reverseTy σ⟩) ψ := by
  let avoid := Naming.toList names ++ variableSymbolNames body ++
    hypotheses.flatMap variableSymbolNames
  have fresh := freshName_not_mem avoid
  simp only [avoid, List.mem_append, List.mem_flatMap, not_or, not_exists, not_and] at fresh
  refine ⟨freshName avoid, Naming.avoids_of_not_mem_toList names fresh.1.1 _,
    noConstOccurrence_of_not_mem_variableSymbolNames _ body fresh.1.2, fun ψ hψ => ?_⟩
  exact noConstOccurrence_of_not_mem_variableSymbolNames _ ψ (fresh.2 ψ hψ)

/-! ## The defined connectives against the primitive ones -/

section Connectives

variable {Γ : HOL.Ctx AtomicTy}

/-- Two formulas derivable from the same hypotheses are provably equal. -/
theorem extDerivation_eq_of_iff {p q : HOL.Formula Symbol Γ}
    (equivalent : ∀ Δ : List (HOL.Formula Symbol Γ),
      HOL.ExtDerivation Symbol Δ p ↔ HOL.ExtDerivation Symbol Δ q)
    (Δ : List (HOL.Formula Symbol Γ)) : HOL.ExtDerivation Symbol Δ (.eq p q) :=
  .eqPropI (.impI ((equivalent _).mp (.hyp List.mem_cons_self)))
    (.impI ((equivalent _).mpr (.hyp List.mem_cons_self)))

/-- The defined truth is provably the primitive one. -/
theorem truth_iff {Δ : List (HOL.Formula Symbol Γ)} :
    HOL.ExtDerivation Symbol Δ (truth : HOL.Formula Symbol Γ) ↔
      HOL.ExtDerivation Symbol Δ .top :=
  ⟨fun _ => .topI, fun _ => truth_provable Δ⟩

theorem rename_lift_weaken_weaken {σ ρ τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ) :
    HOL.rename (HOL.Rename.lift (σ := σ) (HOL.Rename.weaken (σ := ρ))) (HOL.weaken (σ := σ) term) =
      HOL.weaken (σ := σ) (HOL.weaken (σ := ρ) term) := by
  simp only [HOL.weaken, HOL.rename_comp]
  rfl

/-- The universal quantifier is congruent for provable equality of bodies. -/
theorem all_congr {σ : HOL.Ty AtomicTy} {φ ψ : HOL.Formula Symbol (σ :: Γ)}
    (equal : ∀ Δ : List (HOL.Formula Symbol (σ :: Γ)), HOL.ExtDerivation Symbol Δ (.eq φ ψ))
    {Δ : List (HOL.Formula Symbol Γ)} :
    HOL.ExtDerivation Symbol Δ (.all φ) ↔ HOL.ExtDerivation Symbol Δ (.all ψ) :=
  ⟨fun derivation =>
      .allI (HOL.ExtDerivation.eqProp_mp_left (equal _) (extDerivation_all_inv derivation)),
    fun derivation =>
      .allI (HOL.ExtDerivation.eqProp_mp_right (equal _) (extDerivation_all_inv derivation))⟩

/-- The existential quantifier is congruent for provable equality of
bodies. -/
theorem ex_congr {σ : HOL.Ty AtomicTy} {φ ψ : HOL.Formula Symbol (σ :: Γ)}
    (equal : ∀ Δ : List (HOL.Formula Symbol (σ :: Γ)), HOL.ExtDerivation Symbol Δ (.eq φ ψ))
    {Δ : List (HOL.Formula Symbol Γ)} :
    HOL.ExtDerivation Symbol Δ (.ex φ) ↔ HOL.ExtDerivation Symbol Δ (.ex ψ) := by
  constructor
  · intro derivation
    refine .exE derivation ?_
    change HOL.ExtDerivation Symbol _ (.ex (HOL.rename (HOL.Rename.lift HOL.Rename.weaken) ψ))
    refine .exI (.var .vz) ?_
    rw [instantiate_var_rename_lift_weaken]
    exact HOL.ExtDerivation.eqProp_mp_left (equal _) (.hyp List.mem_cons_self)
  · intro derivation
    refine .exE derivation ?_
    change HOL.ExtDerivation Symbol _ (.ex (HOL.rename (HOL.Rename.lift HOL.Rename.weaken) φ))
    refine .exI (.var .vz) ?_
    rw [instantiate_var_rename_lift_weaken]
    exact HOL.ExtDerivation.eqProp_mp_right (equal _) (.hyp List.mem_cons_self)

/-- `∃ = λ P. ∀ q. (∀ x. P x ⇒ q) ⇒ q`, the forward translation of
`DefinedConnectives.existsDB`. -/
def existsTerm (σ : HOL.Ty AtomicTy) : HOL.Term Symbol Γ (.arr (.arr σ .prop) .prop) :=
  .lam (.app (forallTerm .prop) (.lam
    (impApp
      (.app (forallTerm σ)
        (.lam (impApp (.app (.var (.vs (.vs .vz))) (.var .vz)) (.var (.vs .vz)))))
      (.var .vz))))

theorem existsDB_translates {A : Ty} {σ : HOL.Ty AtomicTy} (typed : A.toHOL = σ) :
    Translates Γ (existsDB A) (.arr (.arr σ .prop) .prop) (existsTerm σ) :=
  .abs (by rw [Ty.toHOL_function, typed, Ty.toHOL_bool])
    (.app rfl (forallDB_translates _ Ty.toHOL_bool)
      (.abs Ty.toHOL_bool
        (impAppDB_translates _
          (.app rfl (forallDB_translates _ typed)
            (.abs typed
              (impAppDB_translates _ (.app rfl (.bound (.vs (.vs .vz))) (.bound .vz))
                (.bound (.vs .vz)))))
          (.bound .vz))))

/-- The body of the defined existential after one beta step. -/
abbrev existsMatrix {σ : HOL.Ty AtomicTy} (predicate : HOL.Term Symbol Γ (.arr σ .prop)) :
    HOL.Formula Symbol (.prop :: Γ) :=
  impApp
    (.app (forallTerm σ)
      (.lam (impApp (.app (HOL.weaken (HOL.weaken predicate)) (.var .vz)) (.var (.vs .vz)))))
    (.var .vz)

theorem beta_exists {σ : HOL.Ty AtomicTy} (Δ : List (HOL.Formula Symbol Γ))
    (predicate : HOL.Term Symbol Γ (.arr σ .prop)) :
    HOL.ExtDerivation Symbol Δ
      (.eq (.app (existsTerm σ) predicate)
        (.app (forallTerm .prop) (.lam (existsMatrix predicate)))) :=
  .beta predicate _

/-- The defined existential quantifier is provably the primitive one. -/
theorem exists_iff {σ : HOL.Ty AtomicTy} {Δ : List (HOL.Formula Symbol Γ)}
    {predicate : HOL.Term Symbol Γ (.arr σ .prop)} :
    HOL.ExtDerivation Symbol Δ (.app (existsTerm σ) predicate) ↔
      HOL.ExtDerivation Symbol Δ (.ex (.app (HOL.weaken predicate) (.var .vz))) := by
  constructor
  · intro derivation
    have unfolded := forall_iff.mp
      (HOL.ExtDerivation.eqProp_mp_left (beta_exists Δ predicate) derivation)
    let goal : HOL.Formula Symbol Γ := .ex (.app (HOL.weaken predicate) (.var .vz))
    have instantiated := HOL.ExtDerivation.allE goal unfolded
    have hcompute : HOL.instantiate goal
        (.app (HOL.weaken (σ := .prop) (.lam (existsMatrix predicate))) (.var .vz)) =
          .app (.lam (existsMatrix predicate)) goal := by
      show HOL.Term.app (HOL.subst (HOL.Subst.single goal)
        (HOL.weaken (.lam (existsMatrix predicate)))) goal = _
      rw [subst_single_weaken]
    rw [hcompute] at instantiated
    have reduced := HOL.ExtDerivation.eqProp_mp_left (.beta goal _) instantiated
    have hmatrix : HOL.instantiate goal (existsMatrix predicate) =
        impApp
          (.app (forallTerm σ)
            (.lam (impApp (.app (HOL.weaken predicate) (.var .vz)) (HOL.weaken goal))))
          goal := by
      show impApp
        (.app (forallTerm σ)
          (.lam (impApp
            (.app (HOL.subst (HOL.Subst.lift (HOL.Subst.single goal))
              (HOL.weaken (HOL.weaken predicate))) (.var .vz))
            (HOL.weaken goal))))
        goal = _
      rw [HOL.subst_weaken, subst_single_weaken]
    rw [hmatrix] at reduced
    refine .impE (imp_iff.mp reduced) (forall_iff.mpr (.allI ?_))
    refine HOL.ExtDerivation.eqProp_mp_right (beta_weaken_lam_var _ _) (imp_iff.mpr (.impI ?_))
    change HOL.ExtDerivation Symbol _
      (.ex (HOL.rename (HOL.Rename.lift HOL.Rename.weaken)
        (.app (HOL.weaken predicate) (.var .vz))))
    refine .exI (.var .vz) ?_
    rw [instantiate_var_rename_lift_weaken]
    exact .hyp List.mem_cons_self
  · intro derivation
    refine HOL.ExtDerivation.eqProp_mp_right (beta_exists Δ predicate)
      (forall_iff.mpr (.allI ?_))
    refine HOL.ExtDerivation.eqProp_mp_right (beta_weaken_lam_var _ _) (imp_iff.mpr (.impI ?_))
    let matrix : HOL.Formula Symbol (σ :: .prop :: Γ) :=
      impApp (.app (HOL.weaken (HOL.weaken predicate)) (.var .vz)) (.var (.vs .vz))
    let premise : HOL.Formula Symbol (.prop :: Γ) := .app (forallTerm σ) (.lam matrix)
    have weakened := extDerivation_mono_cons (χ := premise)
      (extDerivation_weaken (σ := .prop) derivation)
    refine .exE weakened ?_
    have universal := forall_iff.mp
      (extDerivation_weaken (σ := σ) (Δ := premise :: HOL.weakenHyps (σ := .prop) Δ)
        (.hyp List.mem_cons_self))
    have instantiated := HOL.ExtDerivation.allE (.var .vz) universal
    have hcompute : HOL.instantiate (.var .vz)
        (.app (HOL.weaken (HOL.weaken (σ := σ) (.lam matrix))) (.var .vz)) =
          .app (HOL.weaken (σ := σ) (.lam matrix)) (.var .vz) := by
      show HOL.Term.app (HOL.subst (HOL.Subst.single (.var .vz))
        (HOL.weaken (HOL.weaken (σ := σ) (.lam matrix)))) (.var .vz) = _
      rw [subst_single_weaken]
    change HOL.ExtDerivation Symbol _ (HOL.instantiate (.var .vz)
      (.app (HOL.weaken (HOL.weaken (σ := σ) (.lam matrix))) (.var .vz))) at instantiated
    rw [hcompute] at instantiated
    have reduced := HOL.ExtDerivation.eqProp_mp_left (beta_weaken_lam_var _ _) instantiated
    have implication := imp_iff.mp reduced
    refine .impE (extDerivation_mono_cons implication) (.hyp ?_)
    show _ ∈ HOL.Term.app (HOL.rename (HOL.Rename.lift HOL.Rename.weaken)
      (HOL.weaken predicate)) (.var .vz) :: _
    rw [rename_lift_weaken_weaken]
    exact List.mem_cons_self

theorem extDerivation_forallTerm_lam_eq_all {σ : HOL.Ty AtomicTy} (body : HOL.Formula Symbol (σ :: Γ))
    (Δ : List (HOL.Formula Symbol Γ)) :
    HOL.ExtDerivation Symbol Δ (.eq (.app (forallTerm σ) (.lam body)) (.all body)) :=
  extDerivation_eq_of_iff (fun _ => forall_iff.trans
    (all_congr (fun _ => beta_weaken_lam_var _ body))) Δ

theorem extDerivation_existsTerm_lam_eq_ex {σ : HOL.Ty AtomicTy} (body : HOL.Formula Symbol (σ :: Γ))
    (Δ : List (HOL.Formula Symbol Γ)) :
    HOL.ExtDerivation Symbol Δ (.eq (.app (existsTerm σ) (.lam body)) (.ex body)) :=
  extDerivation_eq_of_iff (fun _ => exists_iff.trans
    (ex_congr (fun _ => beta_weaken_lam_var _ body))) Δ

end Connectives

/-! ## Inversion of constant non-occurrence -/

section Inversion

variable {B : Type} {C : HOL.Ty B → Type} {σ : HOL.Ty B} {target : C σ} {Γ : HOL.Ctx B}

theorem noConstOccurrence_app_inv {ρ τ : HOL.Ty B} {function : HOL.Term C Γ (.arr ρ τ)}
    {argument : HOL.Term C Γ ρ} (absent : HOL.NoConstOccurrence target (.app function argument)) :
    HOL.NoConstOccurrence target function ∧ HOL.NoConstOccurrence target argument := by
  cases absent with
  | app hfunction hargument => exact ⟨hfunction, hargument⟩

theorem noConstOccurrence_lam_inv {ρ τ : HOL.Ty B} {body : HOL.Term C (ρ :: Γ) τ}
    (absent : HOL.NoConstOccurrence target (.lam body)) : HOL.NoConstOccurrence target body := by
  cases absent with
  | lam hbody => exact hbody

theorem noConstOccurrence_and_inv {p q : HOL.Formula C Γ}
    (absent : HOL.NoConstOccurrence target (.and p q)) :
    HOL.NoConstOccurrence target p ∧ HOL.NoConstOccurrence target q := by
  cases absent with
  | and hp hq => exact ⟨hp, hq⟩

theorem noConstOccurrence_or_inv {p q : HOL.Formula C Γ}
    (absent : HOL.NoConstOccurrence target (.or p q)) :
    HOL.NoConstOccurrence target p ∧ HOL.NoConstOccurrence target q := by
  cases absent with
  | or hp hq => exact ⟨hp, hq⟩

theorem noConstOccurrence_imp_inv {p q : HOL.Formula C Γ}
    (absent : HOL.NoConstOccurrence target (.imp p q)) :
    HOL.NoConstOccurrence target p ∧ HOL.NoConstOccurrence target q := by
  cases absent with
  | imp hp hq => exact ⟨hp, hq⟩

theorem noConstOccurrence_not_inv {p : HOL.Formula C Γ}
    (absent : HOL.NoConstOccurrence target (.not p)) : HOL.NoConstOccurrence target p := by
  cases absent with
  | not hp => exact hp

theorem noConstOccurrence_eq_inv {ρ : HOL.Ty B} {left right : HOL.Term C Γ ρ}
    (absent : HOL.NoConstOccurrence target (.eq left right)) :
    HOL.NoConstOccurrence target left ∧ HOL.NoConstOccurrence target right := by
  cases absent with
  | eq hleft hright => exact ⟨hleft, hright⟩

theorem noConstOccurrence_all_inv {ρ : HOL.Ty B} {body : HOL.Formula C (ρ :: Γ)}
    (absent : HOL.NoConstOccurrence target (.all body)) : HOL.NoConstOccurrence target body := by
  cases absent with
  | all hbody => exact hbody

theorem noConstOccurrence_ex_inv {ρ : HOL.Ty B} {body : HOL.Formula C (ρ :: Γ)}
    (absent : HOL.NoConstOccurrence target (.ex body)) : HOL.NoConstOccurrence target body := by
  cases absent with
  | ex hbody => exact hbody

end Inversion

/-! ## Symbols outside the image of the forward translation -/

/-- The symbol `Symbol.constant Const.equality (Ty.equality operand)`, primitive
equality at an equality type as an uninterpreted constant.  The forward
translation never produces it; the reverse translation sends it to primitive
equality. -/
abbrev equalitySymbol (operand : Ty) : Symbol (Ty.equality operand).toHOL :=
  .constant Const.equality (Ty.equality operand) rfl

/-- The term mentions no symbol `equalitySymbol operand`. -/
def EqualitySymbolFree {Γ : HOL.Ctx AtomicTy} {τ : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol Γ τ) : Prop :=
  ∀ operand : Ty, HOL.NoConstOccurrence (equalitySymbol operand) term

namespace EqualitySymbolFree

variable {Γ : HOL.Ctx AtomicTy}

theorem app {ρ τ : HOL.Ty AtomicTy} {function : HOL.Term Symbol Γ (.arr ρ τ)}
    {argument : HOL.Term Symbol Γ ρ} (free : EqualitySymbolFree (.app function argument)) :
    EqualitySymbolFree function ∧ EqualitySymbolFree argument :=
  ⟨fun operand => (noConstOccurrence_app_inv (free operand)).1,
    fun operand => (noConstOccurrence_app_inv (free operand)).2⟩

theorem lam {ρ τ : HOL.Ty AtomicTy} {body : HOL.Term Symbol (ρ :: Γ) τ}
    (free : EqualitySymbolFree (.lam body)) : EqualitySymbolFree body :=
  fun operand => noConstOccurrence_lam_inv (free operand)

theorem and {p q : HOL.Formula Symbol Γ} (free : EqualitySymbolFree (.and p q)) :
    EqualitySymbolFree p ∧ EqualitySymbolFree q :=
  ⟨fun operand => (noConstOccurrence_and_inv (free operand)).1,
    fun operand => (noConstOccurrence_and_inv (free operand)).2⟩

theorem or {p q : HOL.Formula Symbol Γ} (free : EqualitySymbolFree (.or p q)) :
    EqualitySymbolFree p ∧ EqualitySymbolFree q :=
  ⟨fun operand => (noConstOccurrence_or_inv (free operand)).1,
    fun operand => (noConstOccurrence_or_inv (free operand)).2⟩

theorem imp {p q : HOL.Formula Symbol Γ} (free : EqualitySymbolFree (.imp p q)) :
    EqualitySymbolFree p ∧ EqualitySymbolFree q :=
  ⟨fun operand => (noConstOccurrence_imp_inv (free operand)).1,
    fun operand => (noConstOccurrence_imp_inv (free operand)).2⟩

theorem not {p : HOL.Formula Symbol Γ} (free : EqualitySymbolFree (.not p)) :
    EqualitySymbolFree p :=
  fun operand => noConstOccurrence_not_inv (free operand)

theorem eq {ρ : HOL.Ty AtomicTy} {left right : HOL.Term Symbol Γ ρ}
    (free : EqualitySymbolFree (.eq left right)) :
    EqualitySymbolFree left ∧ EqualitySymbolFree right :=
  ⟨fun operand => (noConstOccurrence_eq_inv (free operand)).1,
    fun operand => (noConstOccurrence_eq_inv (free operand)).2⟩

theorem all {ρ : HOL.Ty AtomicTy} {body : HOL.Formula Symbol (ρ :: Γ)}
    (free : EqualitySymbolFree (.all body)) : EqualitySymbolFree body :=
  fun operand => noConstOccurrence_all_inv (free operand)

theorem ex {ρ : HOL.Ty AtomicTy} {body : HOL.Formula Symbol (ρ :: Γ)}
    (free : EqualitySymbolFree (.ex body)) : EqualitySymbolFree body :=
  fun operand => noConstOccurrence_ex_inv (free operand)

/-- A constant symbol of an equality-symbol-free term is not primitive
equality at an equality type. -/
theorem equalityOperand?_eq_none {constant : Const} {annotation : Ty} {τ : HOL.Ty AtomicTy}
    {typed : annotation.toHOL = τ}
    (free : EqualitySymbolFree (.const (.constant constant annotation typed) :
      HOL.Term Symbol Γ τ)) :
    equalityOperand? constant annotation = none := by
  cases hrecognized : equalityOperand? constant annotation with
  | none => rfl
  | some operand =>
      exfalso
      obtain ⟨rfl, rfl⟩ := (equalityOperand?_eq_some_iff _ _ _).mp hrecognized
      subst typed
      exact sigma_ne_of_noConstOccurrence_const (free operand) rfl

end EqualitySymbolFree

theorem sigma_variable_ne_equalitySymbol {τ : HOL.Ty AtomicTy} (sourceVar : SourceVar)
    (typed : sourceVar.ty.toHOL = τ) (operand : Ty) :
    (⟨τ, .variable sourceVar typed⟩ : Sigma Symbol) ≠ ⟨_, equalitySymbol operand⟩ := by
  intro h
  have := congrArg (fun symbol : Sigma Symbol => symbol.2.sourceVar?) h
  simp [Symbol.sourceVar?] at this

theorem EqualitySymbolFree.rename {Γ Γ' : HOL.Ctx AtomicTy} (ρ : HOL.Rename AtomicTy Γ Γ')
    {τ : HOL.Ty AtomicTy} {term : HOL.Term Symbol Γ τ} (free : EqualitySymbolFree term) :
    EqualitySymbolFree (HOL.rename ρ term) :=
  fun operand => HOL.noConstOccurrence_rename ρ term (free operand)

theorem EqualitySymbolFree.subst {Γ Γ' : HOL.Ctx AtomicTy}
    {substitution : HOL.Subst Symbol Γ Γ'}
    (images : ∀ {ρ : HOL.Ty AtomicTy} (x : HOL.Var Γ ρ), EqualitySymbolFree (substitution x))
    {τ : HOL.Ty AtomicTy} {term : HOL.Term Symbol Γ τ} (free : EqualitySymbolFree term) :
    EqualitySymbolFree (HOL.subst substitution term) :=
  fun operand => HOL.noConstOccurrence_subst (fun x => images x operand) term (free operand)

theorem EqualitySymbolFree.instantiate {Γ : HOL.Ctx AtomicTy} {σ τ : HOL.Ty AtomicTy}
    {argument : HOL.Term Symbol Γ σ} {body : HOL.Term Symbol (σ :: Γ) τ}
    (freeArgument : EqualitySymbolFree argument) (freeBody : EqualitySymbolFree body) :
    EqualitySymbolFree (HOL.instantiate argument body) :=
  EqualitySymbolFree.subst (fun x => by
    cases x with
    | vz => exact freeArgument
    | vs _ => exact fun _ => .var) freeBody

/-- Closing the context by variable symbols introduces no equality symbol. -/
theorem EqualitySymbolFree.subst_closingSubst {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {τ : HOL.Ty AtomicTy} {term : HOL.Term Symbol Γ τ} (free : EqualitySymbolFree term) :
    EqualitySymbolFree (HOL.subst (Naming.closingSubst names) term) :=
  fun operand => HOL.noConstOccurrence_subst
    (fun _ => Symbol.noConstOccurrence_const _ _
      (sigma_variable_ne_equalitySymbol _ _ operand)) term (free operand)

/-! ## Round trip on formulas -/

@[simp] theorem reverseTermOpen_lam {Γ : HOL.Ctx AtomicTy} {σ τ : HOL.Ty AtomicTy}
    (body : HOL.Term Symbol (σ :: Γ) τ) :
    reverseTermOpen (.lam body) = .abs (reverseTy σ) (reverseTermOpen body) :=
  congrArg (DBTerm.abs (reverseTy σ)) (reverseTermWith_congr VarEnv.lift_loose body)

@[simp] theorem reverseTermOpen_all {Γ : HOL.Ctx AtomicTy} {σ : HOL.Ty AtomicTy}
    (body : HOL.Formula Symbol (σ :: Γ)) :
    reverseTermOpen (.all body) =
      .app (forallDB (reverseTy σ)) (.abs (reverseTy σ) (reverseTermOpen body)) :=
  congrArg (fun body' => DBTerm.app (forallDB (reverseTy σ)) (.abs (reverseTy σ) body'))
    (reverseTermWith_congr VarEnv.lift_loose body)

@[simp] theorem reverseTermOpen_ex {Γ : HOL.Ctx AtomicTy} {σ : HOL.Ty AtomicTy}
    (body : HOL.Formula Symbol (σ :: Γ)) :
    reverseTermOpen (.ex body) =
      .app (existsDB (reverseTy σ)) (.abs (reverseTy σ) (reverseTermOpen body)) :=
  congrArg (fun body' => DBTerm.app (existsDB (reverseTy σ)) (.abs (reverseTy σ) body'))
    (reverseTermWith_congr VarEnv.lift_loose body)

/-- The reverse of an equality-symbol-free term is never primitive equality
applied to one argument, so the forward translation treats its applications
as ordinary applications. -/
theorem equalityHeadOperand?_reverseTermOpen {Γ : HOL.Ctx AtomicTy} :
    ∀ {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ), EqualitySymbolFree term →
      (reverseTermOpen term).equalityHeadOperand? = none
  | _, .var _, _ => rfl
  | _, .const (.constant ..), _ => rfl
  | _, .const (.variable ..), _ => rfl
  | _, .app (.const (.constant _ _ typed)) _, free =>
      EqualitySymbolFree.equalityOperand?_eq_none (typed := typed) free.app.1
  | _, .app (.const (.variable ..)) _, _ => rfl
  | _, .app (.var _) _, _ => rfl
  | _, .app (.app _ _) _, _ => rfl
  | _, .app (.lam _) _, _ => rfl
  | _, .lam _, _ => rfl
  | _, .top, _ => rfl
  | _, .bot, _ => rfl
  | _, .and _ _, _ => rfl
  | _, .or _ _, _ => rfl
  | _, .imp _ _, _ => rfl
  | _, .not _, _ => rfl
  | _, .eq _ _, _ => rfl
  | _, .all _, _ => rfl
  | _, .ex _, _ => rfl

/-- **Round trip on formulas.**  The forward translation of the reverse of an
equality-symbol-free term is provably equal to it, from any hypotheses. -/
theorem exists_translates_reverseTermOpen_eq {Γ : HOL.Ctx AtomicTy} :
    ∀ {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ), EqualitySymbolFree term →
      ∃ target : HOL.Term Symbol Γ τ, Translates Γ (reverseTermOpen term) τ target ∧
        ∀ Δ : List (HOL.Formula Symbol Γ), HOL.ExtDerivation Symbol Δ (.eq target term)
  | _, .var x, _ => ⟨.var x, .bound x, fun _ => .eqRefl _⟩
  | _, .const (.constant constant annotation typed), free =>
      ⟨_, .constant (EqualitySymbolFree.equalityOperand?_eq_none free) typed,
        fun _ => .eqRefl _⟩
  | _, .const (.variable sourceVar typed), _ => ⟨_, .free typed, fun _ => .eqRefl _⟩
  | _, .app function argument, free => by
      obtain ⟨function', hfunction, efunction⟩ :=
        exists_translates_reverseTermOpen_eq function free.app.1
      obtain ⟨argument', hargument, eargument⟩ :=
        exists_translates_reverseTermOpen_eq argument free.app.2
      exact ⟨.app function' argument',
        .app (equalityHeadOperand?_reverseTermOpen function free.app.1) hfunction hargument,
        fun Δ => HOL.ExtDerivation.eqAppCongr (efunction Δ) (eargument Δ)⟩
  | _, .lam (σ := σ) body, free => by
      obtain ⟨body', hbody, ebody⟩ := exists_translates_reverseTermOpen_eq body free.lam
      rw [reverseTermOpen_lam]
      exact ⟨.lam body', .abs (toHOL_reverseTy σ) hbody, fun _ => .eqLam (ebody _)⟩
  | _, .top, _ =>
      ⟨truth, PrimitiveSentences.truthDB_translates Γ,
        extDerivation_eq_of_iff (fun _ => truth_iff)⟩
  | _, .bot, _ =>
      ⟨falsityDefinition, falsityDefinitionDB_translates Γ,
        extDerivation_eq_of_iff (fun _ => falsity_iff)⟩
  | _, .and p q, free => by
      obtain ⟨p', hp, ep⟩ := exists_translates_reverseTermOpen_eq p free.and.1
      obtain ⟨q', hq, eq'⟩ := exists_translates_reverseTermOpen_eq q free.and.2
      exact ⟨.app (.app andTerm p') q', .app rfl (.app rfl (andDB_translates Γ) hp) hq,
        fun Δ => .eqTrans (HOL.ExtDerivation.eqAppCongr (.eqAppArg andTerm (ep Δ)) (eq' Δ))
          (extDerivation_eq_of_iff (fun _ => and_iff) Δ)⟩
  | _, .or p q, free => by
      obtain ⟨p', hp, ep⟩ := exists_translates_reverseTermOpen_eq p free.or.1
      obtain ⟨q', hq, eq'⟩ := exists_translates_reverseTermOpen_eq q free.or.2
      exact ⟨.app (.app orTerm p') q', .app rfl (.app rfl (orDB_translates Γ) hp) hq,
        fun Δ => .eqTrans (HOL.ExtDerivation.eqAppCongr (.eqAppArg orTerm (ep Δ)) (eq' Δ))
          (extDerivation_eq_of_iff (fun _ => or_iff) Δ)⟩
  | _, .imp p q, free => by
      obtain ⟨p', hp, ep⟩ := exists_translates_reverseTermOpen_eq p free.imp.1
      obtain ⟨q', hq, eq'⟩ := exists_translates_reverseTermOpen_eq q free.imp.2
      exact ⟨impApp p' q', impAppDB_translates Γ hp hq,
        fun Δ => .eqTrans (HOL.ExtDerivation.eqAppCongr (.eqAppArg impTerm (ep Δ)) (eq' Δ))
          (extDerivation_eq_of_iff (fun _ => imp_iff) Δ)⟩
  | _, .not p, free => by
      obtain ⟨p', hp, ep⟩ := exists_translates_reverseTermOpen_eq p free.not
      exact ⟨.app notTerm p', .app rfl (notDB_translates Γ) hp,
        fun Δ => .eqTrans (.eqAppArg notTerm (ep Δ))
          (extDerivation_eq_of_iff (fun _ => not_iff) Δ)⟩
  | _, .eq (τ := ρ) left right, free => by
      obtain ⟨left', hleft, eleft⟩ := exists_translates_reverseTermOpen_eq left free.eq.1
      obtain ⟨right', hright, eright⟩ := exists_translates_reverseTermOpen_eq right free.eq.2
      exact ⟨.eq left' right',
        .equalityApp (equalityOperand?_equality (reverseTy ρ)) (toHOL_reverseTy ρ) hleft hright,
        fun Δ => extDerivation_eq_congr (eleft Δ) (eright Δ)⟩
  | _, .all (σ := σ) body, free => by
      obtain ⟨body', hbody, ebody⟩ := exists_translates_reverseTermOpen_eq body free.all
      rw [reverseTermOpen_all]
      exact ⟨.app (forallTerm σ) (.lam body'),
        .app rfl (forallDB_translates Γ (toHOL_reverseTy σ)) (.abs (toHOL_reverseTy σ) hbody),
        fun Δ => .eqTrans (.eqAppArg (forallTerm σ) (.eqLam (ebody _)))
          (extDerivation_forallTerm_lam_eq_all body Δ)⟩
  | _, .ex (σ := σ) body, free => by
      obtain ⟨body', hbody, ebody⟩ := exists_translates_reverseTermOpen_eq body free.ex
      rw [reverseTermOpen_ex]
      exact ⟨.app (existsTerm σ) (.lam body'),
        .app rfl (existsDB_translates (toHOL_reverseTy σ)) (.abs (toHOL_reverseTy σ) hbody),
        fun Δ => .eqTrans (.eqAppArg (existsTerm σ) (.eqLam (ebody _)))
          (extDerivation_existsTerm_lam_eq_ex body Δ)⟩

/-- Round trip on formulas, as mutual derivability. -/
theorem exists_translates_reverseTermOpen_derivable {Γ : HOL.Ctx AtomicTy}
    (formula : HOL.Formula Symbol Γ) (free : EqualitySymbolFree formula) :
    ∃ target : HOL.Formula Symbol Γ, Translates Γ (reverseTermOpen formula) .prop target ∧
      HOL.ExtDerivation Symbol [target] formula ∧ HOL.ExtDerivation Symbol [formula] target := by
  obtain ⟨target, htarget, equal⟩ := exists_translates_reverseTermOpen_eq formula free
  exact ⟨target, htarget,
    HOL.ExtDerivation.eqProp_mp_left (equal _) (.hyp List.mem_cons_self),
    HOL.ExtDerivation.eqProp_mp_right (equal _) (.hyp List.mem_cons_self)⟩

/-- Round trip with named context variables: the forward translation of the
closed reverse is provably equal to the term with its context closed by the
variable symbols of the names. -/
theorem exists_translates_reverseTerm_eq {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ) (free : EqualitySymbolFree term) :
    ∃ target : HOL.ClosedTerm Symbol τ, Translates [] (reverseTerm names term) τ target ∧
      ∀ Δ : List (HOL.ClosedFormula Symbol),
        HOL.ExtDerivation Symbol Δ (.eq target (HOL.subst (Naming.closingSubst names) term)) := by
  rw [reverseTerm_eq_reverseTermOpen_closingSubst]
  exact exists_translates_reverseTermOpen_eq _ (free.subst_closingSubst names)

/-! ## Round trip on the image -/

/-- `λ x y. x = y` at one operand type. -/
def equalityLambdaDB (operand : Ty) : DBTerm :=
  .abs operand (.abs operand (CanonicalTerm.equalityDB operand (.bound 1) (.bound 0)))

/-- Eta-expand every occurrence of primitive equality at an equality type that
is not the head of a full application, as the forward translation does. -/
def expandBareEquality : DBTerm → DBTerm
  | .const constant annotation =>
      match equalityOperand? constant annotation with
      | some operand => equalityLambdaDB operand
      | none => .const constant annotation
  | .free sourceVar => .free sourceVar
  | .bound index => .bound index
  | .app (.app (.const constant annotation) left) right =>
      .app (.app (.const constant annotation) (expandBareEquality left))
        (expandBareEquality right)
  | .app function argument => .app (expandBareEquality function) (expandBareEquality argument)
  | .abs domain body => .abs domain (expandBareEquality body)

theorem expandBareEquality_const_of_equalityOperand?_eq_none {constant : Const}
    {annotation : Ty} (unrecognized : equalityOperand? constant annotation = none) :
    expandBareEquality (.const constant annotation) = .const constant annotation := by
  simp only [expandBareEquality, unrecognized]

theorem expandBareEquality_app_of_equalityHeadOperand?_eq_none {function argument : DBTerm}
    (notEquality : function.equalityHeadOperand? = none) :
    expandBareEquality (.app function argument) =
      .app (expandBareEquality function) (expandBareEquality argument) := by
  match function, notEquality with
  | .const _ _, _ => rfl
  | .free _, _ => rfl
  | .bound _, _ => rfl
  | .app (.const constant annotation) left, notEquality =>
      have unrecognized : equalityOperand? constant annotation = none := notEquality
      show _ = DBTerm.app (DBTerm.app (expandBareEquality (.const constant annotation))
        (expandBareEquality left)) (expandBareEquality argument)
      rw [expandBareEquality_const_of_equalityOperand?_eq_none unrecognized]
      rfl
  | .app (.free _) _, _ => rfl
  | .app (.bound _) _, _ => rfl
  | .app (.app _ _) _, _ => rfl
  | .app (.abs _ _) _, _ => rfl
  | .abs _ _, _ => rfl

/-- **Round trip on the image.**  A translated term comes back as the source
term with every occurrence of primitive equality that is not the head of a full
application eta-expanded. -/
theorem reverseTermOpen_of_translates {Γ : HOL.Ctx AtomicTy} {term : DBTerm}
    {τ : HOL.Ty AtomicTy} {target : HOL.Term Symbol Γ τ}
    (translation : Translates Γ term τ target) :
    reverseTermOpen target = expandBareEquality term := by
  induction translation with
  | @equality Γ constant annotation operand σ recognized typed =>
      obtain ⟨rfl, rfl⟩ := (equalityOperand?_eq_some_iff _ _ _).mp recognized
      subst typed
      simp only [expandBareEquality, recognized]
      show DBTerm.abs (reverseTy operand.toHOL) (DBTerm.abs (reverseTy operand.toHOL)
        (CanonicalTerm.equalityDB (reverseTy operand.toHOL) (.bound 1) (.bound 0))) = _
      rw [reverseTy_toHOL]
      rfl
  | constant unrecognized typed =>
      exact (expandBareEquality_const_of_equalityOperand?_eq_none unrecognized).symm
  | free typed => rfl
  | bound x => rfl
  | @equalityApp Γ constant annotation operand left right σ left' right' recognized typed _ _
      leftIH rightIH =>
      obtain ⟨rfl, rfl⟩ := (equalityOperand?_eq_some_iff _ _ _).mp recognized
      subst typed
      show CanonicalTerm.equalityDB (reverseTy operand.toHOL) (reverseTermOpen left')
        (reverseTermOpen right') = _
      rw [leftIH, rightIH, reverseTy_toHOL]
      rfl
  | app notEquality _ _ functionIH argumentIH =>
      show DBTerm.app (reverseTermOpen _) (reverseTermOpen _) = _
      rw [functionIH, argumentIH,
        expandBareEquality_app_of_equalityHeadOperand?_eq_none notEquality]
  | abs typed _ bodyIH =>
      subst typed
      rw [reverseTermOpen_lam, bodyIH, reverseTy_toHOL]
      rfl

/-- Every occurrence of primitive equality at an equality type is the head of
a full application. -/
inductive EqualityFullyApplied : DBTerm → Prop
  | const {constant : Const} {annotation : Ty}
      (unrecognized : equalityOperand? constant annotation = none) :
      EqualityFullyApplied (.const constant annotation)
  | free (sourceVar : SourceVar) : EqualityFullyApplied (.free sourceVar)
  | bound (index : Nat) : EqualityFullyApplied (.bound index)
  | fullApp {constant : Const} {annotation : Ty} {left right : DBTerm} :
      EqualityFullyApplied left → EqualityFullyApplied right →
      EqualityFullyApplied (.app (.app (.const constant annotation) left) right)
  | app {function argument : DBTerm} :
      EqualityFullyApplied function → EqualityFullyApplied argument →
      EqualityFullyApplied (.app function argument)
  | abs {domain : Ty} {body : DBTerm} :
      EqualityFullyApplied body → EqualityFullyApplied (.abs domain body)

theorem EqualityFullyApplied.equalityHeadOperand?_eq_none {term : DBTerm}
    (applied : EqualityFullyApplied term) : term.equalityHeadOperand? = none := by
  cases applied with
  | const => rfl
  | free => rfl
  | bound => rfl
  | fullApp => rfl
  | app hfunction _ =>
      cases hfunction with
      | const unrecognized => exact unrecognized
      | free => rfl
      | bound => rfl
      | fullApp => rfl
      | app => rfl
      | abs => rfl
  | abs => rfl

theorem EqualityFullyApplied.expandBareEquality_eq {term : DBTerm}
    (applied : EqualityFullyApplied term) : expandBareEquality term = term := by
  induction applied with
  | const unrecognized => exact expandBareEquality_const_of_equalityOperand?_eq_none unrecognized
  | free => rfl
  | bound => rfl
  | fullApp _ _ leftIH rightIH =>
      show DBTerm.app (.app _ (expandBareEquality _)) (expandBareEquality _) = _
      rw [leftIH, rightIH]
  | app hfunction _ functionIH argumentIH =>
      rw [expandBareEquality_app_of_equalityHeadOperand?_eq_none
        hfunction.equalityHeadOperand?_eq_none, functionIH, argumentIH]
  | abs _ bodyIH =>
      show DBTerm.abs _ (expandBareEquality _) = _
      rw [bodyIH]

/-- On terms whose equality occurrences are all fully applied, reversal
inverts the forward translation exactly. -/
theorem reverseTermOpen_of_translates_of_equalityFullyApplied {Γ : HOL.Ctx AtomicTy}
    {term : DBTerm} {τ : HOL.Ty AtomicTy} {target : HOL.Term Symbol Γ τ}
    (translation : Translates Γ term τ target) (applied : EqualityFullyApplied term) :
    reverseTermOpen target = term :=
  (reverseTermOpen_of_translates translation).trans applied.expandBareEquality_eq

/-- The canonical form of the round trip on the image. -/
theorem reverseCanonical_of_translates {term : CanonicalTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.ClosedTerm Symbol τ} (translation : Translates [] term.term τ target)
    (applied : EqualityFullyApplied term.term) :
    reverseCanonical Naming.empty target = term :=
  CanonicalTerm.ext_term ((reverseTerm_eq_reverseTermOpen target).trans
    (reverseTermOpen_of_translates_of_equalityFullyApplied translation applied))

/-! ## Constant substitution -/

theorem looseBelow_zero_reverseTermOpen {τ : HOL.Ty AtomicTy} (term : HOL.ClosedTerm Symbol τ) :
    DBTerm.LooseBelow 0 (reverseTermOpen term) :=
  looseBelow_reverseTermWith (fun {_} (x : HOL.Var [] _) => nomatch x) term

/-- A closed term keeps its translation when weakened into any context. -/
theorem reverseTermWith_weakenCtx {Γ : HOL.Ctx AtomicTy} (env : VarEnv Γ)
    {τ : HOL.Ty AtomicTy} (term : HOL.ClosedTerm Symbol τ) :
    reverseTermWith env (HOL.weakenCtx Γ term) = reverseTermOpen term := by
  rw [← HOL.rename_weakenCtx (fun x => nomatch x : HOL.Rename AtomicTy [] Γ) term,
    HOL.weakenCtx_nil, reverseTermWith_rename]
  exact reverseTermWith_congr (fun {_} (x : HOL.Var [] _) => nomatch x) term

/-- Replace every free variable, and every constant occurrence other than
primitive equality at an equality type, by the image of the symbol that names
it. -/
def replaceSymbols (image : ∀ {τ : HOL.Ty AtomicTy}, Symbol τ → DBTerm) : DBTerm → DBTerm
  | .const constant annotation =>
      match equalityOperand? constant annotation with
      | some _ => .const constant annotation
      | none => image (Symbol.constant constant annotation rfl)
  | .free sourceVar => image (Symbol.ofVar sourceVar)
  | .bound index => .bound index
  | .app function argument =>
      .app (replaceSymbols image function) (replaceSymbols image argument)
  | .abs domain body => .abs domain (replaceSymbols image body)

theorem replaceSymbols_shiftLoose {image : ∀ {τ : HOL.Ty AtomicTy}, Symbol τ → DBTerm}
    (closed : ∀ {τ : HOL.Ty AtomicTy} (symbol : Symbol τ), DBTerm.LooseBelow 0 (image symbol)) :
    ∀ (cutoff : Nat) (term : DBTerm),
      replaceSymbols image (shiftLoose cutoff term) = shiftLoose cutoff (replaceSymbols image term)
  | cutoff, .const constant annotation => by
      cases hrecognized : equalityOperand? constant annotation with
      | some _ => simp [replaceSymbols, shiftLoose, hrecognized]
      | none =>
          simp only [shiftLoose, replaceSymbols, hrecognized]
          exact (shiftLoose_of_closed (closed _) cutoff).symm
  | cutoff, .free _ => (shiftLoose_of_closed (closed _) cutoff).symm
  | cutoff, .bound index => by
      by_cases hlt : index < cutoff <;> simp [replaceSymbols, shiftLoose, hlt]
  | cutoff, .app function argument => by
      simp only [shiftLoose, replaceSymbols]
      rw [replaceSymbols_shiftLoose closed cutoff function,
        replaceSymbols_shiftLoose closed cutoff argument]
  | cutoff, .abs _ body => by
      simp only [shiftLoose, replaceSymbols]
      rw [replaceSymbols_shiftLoose closed (cutoff + 1) body]

section ReplaceConnectives

variable (image : ∀ {τ : HOL.Ty AtomicTy}, Symbol τ → DBTerm)

theorem replaceSymbols_truthDB :
    replaceSymbols image PrimitiveSentences.truthDB = PrimitiveSentences.truthDB := by
  simp [replaceSymbols, PrimitiveSentences.truthDB, CanonicalTerm.equalityDB,
    PrimitiveSentences.identityBool, equalityOperand?_equality]

theorem replaceSymbols_forallDB (A : Ty) : replaceSymbols image (forallDB A) = forallDB A := by
  simp [replaceSymbols, forallDB, PrimitiveSentences.truthDB, CanonicalTerm.equalityDB,
    PrimitiveSentences.identityBool, equalityOperand?_equality]

theorem replaceSymbols_falsityDefinitionDB :
    replaceSymbols image falsityDefinitionDB = falsityDefinitionDB := by
  simp [replaceSymbols, falsityDefinitionDB, forallDB, PrimitiveSentences.truthDB,
    CanonicalTerm.equalityDB, PrimitiveSentences.identityBool, equalityOperand?_equality]

theorem replaceSymbols_andDB : replaceSymbols image andDB = andDB := by
  simp [replaceSymbols, andDB, PrimitiveSentences.truthDB, CanonicalTerm.equalityDB,
    PrimitiveSentences.identityBool, equalityOperand?_equality]

theorem replaceSymbols_impDB : replaceSymbols image impDB = impDB := by
  simp [replaceSymbols, impDB, andDB, PrimitiveSentences.truthDB, CanonicalTerm.equalityDB,
    PrimitiveSentences.identityBool, equalityOperand?_equality]

theorem replaceSymbols_notDB : replaceSymbols image notDB = notDB := by
  simp [replaceSymbols, notDB, impDB, andDB, falsityDefinitionDB, forallDB,
    PrimitiveSentences.truthDB, CanonicalTerm.equalityDB, PrimitiveSentences.identityBool,
    equalityOperand?_equality]

theorem replaceSymbols_orDB : replaceSymbols image orDB = orDB := by
  simp [replaceSymbols, orDB, impAppDB, impDB, andDB, forallDB, PrimitiveSentences.truthDB,
    CanonicalTerm.equalityDB, PrimitiveSentences.identityBool, equalityOperand?_equality]

theorem replaceSymbols_existsDB (A : Ty) : replaceSymbols image (existsDB A) = existsDB A := by
  simp [replaceSymbols, existsDB, impAppDB, impDB, andDB, forallDB, PrimitiveSentences.truthDB,
    CanonicalTerm.equalityDB, PrimitiveSentences.identityBool, equalityOperand?_equality]

end ReplaceConnectives

/-- **Constant substitution.**  Translating a term after substituting closed
terms for its symbols is replacing, in its translation, each symbol's
OpenTheory term by the translation of its substitute.  The hypotheses: the
term mentions no equality symbol (whose translation coincides with primitive
equality), and the images of the context variables are left alone. -/
theorem reverseTermWith_substConst (substitution : ∀ {τ : HOL.Ty AtomicTy}, Symbol τ →
      HOL.ClosedTerm Symbol τ) :
    ∀ {Γ : HOL.Ctx AtomicTy} (env : VarEnv Γ),
      (∀ {ρ : HOL.Ty AtomicTy} (x : HOL.Var Γ ρ),
        replaceSymbols (fun symbol => reverseTermOpen (substitution symbol)) (env x) = env x) →
      ∀ {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ), EqualitySymbolFree term →
        reverseTermWith env (HOL.substConst substitution term) =
          replaceSymbols (fun symbol => reverseTermOpen (substitution symbol))
            (reverseTermWith env term)
  | _, _, henv, _, .var x, _ => (henv x).symm
  | _, env, _, _, .const (.constant constant annotation typed), free => by
      have unrecognized := EqualitySymbolFree.equalityOperand?_eq_none free
      subst typed
      rw [HOL.substConst, reverseTermWith_weakenCtx]
      simp only [reverseTermWith, reverseSymbol, replaceSymbols, unrecognized]
  | _, env, _, _, .const (.variable sourceVar typed), _ => by
      subst typed
      rw [HOL.substConst, reverseTermWith_weakenCtx]
      rfl
  | _, env, henv, _, .app function argument, free => by
      simp only [HOL.substConst, reverseTermWith, replaceSymbols]
      rw [reverseTermWith_substConst substitution env henv function free.app.1,
        reverseTermWith_substConst substitution env henv argument free.app.2]
  | _, env, henv, _, .lam body, free => by
      simp only [HOL.substConst, reverseTermWith, replaceSymbols]
      rw [reverseTermWith_substConst substitution (VarEnv.lift env) (fun x => ?_) body free.lam]
      cases x with
      | vz => rfl
      | vs x =>
          simp only [VarEnv.lift]
          rw [replaceSymbols_shiftLoose (fun symbol => looseBelow_zero_reverseTermOpen _), henv x]
  | _, _, _, _, .top, _ => (replaceSymbols_truthDB _).symm
  | _, _, _, _, .bot, _ => (replaceSymbols_falsityDefinitionDB _).symm
  | _, env, henv, _, .and p q, free => by
      simp only [HOL.substConst, reverseTermWith, replaceSymbols]
      rw [reverseTermWith_substConst substitution env henv p free.and.1,
        reverseTermWith_substConst substitution env henv q free.and.2, replaceSymbols_andDB]
  | _, env, henv, _, .or p q, free => by
      simp only [HOL.substConst, reverseTermWith, replaceSymbols]
      rw [reverseTermWith_substConst substitution env henv p free.or.1,
        reverseTermWith_substConst substitution env henv q free.or.2, replaceSymbols_orDB]
  | _, env, henv, _, .imp p q, free => by
      simp only [HOL.substConst, reverseTermWith, impAppDB, replaceSymbols]
      rw [reverseTermWith_substConst substitution env henv p free.imp.1,
        reverseTermWith_substConst substitution env henv q free.imp.2, replaceSymbols_impDB]
  | _, env, henv, _, .not p, free => by
      simp only [HOL.substConst, reverseTermWith, replaceSymbols]
      rw [reverseTermWith_substConst substitution env henv p free.not, replaceSymbols_notDB]
  | _, env, henv, _, .eq left right, free => by
      simp only [HOL.substConst, reverseTermWith, CanonicalTerm.equalityDB, replaceSymbols,
        equalityOperand?_equality]
      rw [reverseTermWith_substConst substitution env henv left free.eq.1,
        reverseTermWith_substConst substitution env henv right free.eq.2]
  | _, env, henv, _, .all body, free => by
      simp only [HOL.substConst, reverseTermWith, replaceSymbols]
      rw [reverseTermWith_substConst substitution (VarEnv.lift env) (fun x => ?_) body free.all,
        replaceSymbols_forallDB]
      cases x with
      | vz => rfl
      | vs x =>
          simp only [VarEnv.lift]
          rw [replaceSymbols_shiftLoose (fun symbol => looseBelow_zero_reverseTermOpen _), henv x]
  | _, env, henv, _, .ex body, free => by
      simp only [HOL.substConst, reverseTermWith, replaceSymbols]
      rw [reverseTermWith_substConst substitution (VarEnv.lift env) (fun x => ?_) body free.ex,
        replaceSymbols_existsDB]
      cases x with
      | vz => rfl
      | vs x =>
          simp only [VarEnv.lift]
          rw [replaceSymbols_shiftLoose (fun symbol => looseBelow_zero_reverseTermOpen _), henv x]

/-! ## Type substitution -/

theorem applyDB_shiftLoose (substitution : TermSubst) :
    ∀ (cutoff : Nat) (term : DBTerm),
      substitution.applyDB (shiftLoose cutoff term) = shiftLoose cutoff (substitution.applyDB term)
  | _, .const _ _ => by simp [shiftLoose]
  | cutoff, .free sourceVar => by
      cases hlookup : substitution.lookup (substitution.types.applyVar sourceVar) with
      | some replacement =>
          simp only [shiftLoose]
          rw [TermSubst.applyDB_free_of_lookup_some _ _ _ hlookup,
            shiftLoose_of_closed (DBTerm.looseBelow_of_inferType replacement.canonical.checked)]
      | none =>
          simp only [shiftLoose]
          rw [TermSubst.applyDB_free_of_lookup_none _ _ hlookup]
          rfl
  | cutoff, .bound index => by
      by_cases hlt : index < cutoff <;> simp [shiftLoose, hlt]
  | cutoff, .app function argument => by
      simp only [shiftLoose, TermSubst.applyDB_app]
      rw [applyDB_shiftLoose substitution cutoff function,
        applyDB_shiftLoose substitution cutoff argument]
  | cutoff, .abs _ body => by
      simp only [shiftLoose, TermSubst.applyDB_abs]
      rw [applyDB_shiftLoose substitution (cutoff + 1) body]

section ApplyConnectives

variable (substitution : TermSubst)

theorem applyDB_truthDB :
    substitution.applyDB PrimitiveSentences.truthDB = PrimitiveSentences.truthDB := by
  simp [PrimitiveSentences.truthDB, CanonicalTerm.equalityDB, PrimitiveSentences.identityBool]

theorem applyDB_forallDB (A : Ty) :
    substitution.applyDB (forallDB A) = forallDB (substitution.types.apply A) := by
  simp [forallDB, PrimitiveSentences.truthDB, CanonicalTerm.equalityDB,
    PrimitiveSentences.identityBool]

theorem applyDB_falsityDefinitionDB :
    substitution.applyDB falsityDefinitionDB = falsityDefinitionDB := by
  simp [falsityDefinitionDB, forallDB, PrimitiveSentences.truthDB, CanonicalTerm.equalityDB,
    PrimitiveSentences.identityBool]

theorem applyDB_andDB : substitution.applyDB andDB = andDB := by
  simp [andDB, boolBinaryTy, PrimitiveSentences.truthDB, CanonicalTerm.equalityDB,
    PrimitiveSentences.identityBool]

theorem applyDB_impDB : substitution.applyDB impDB = impDB := by
  simp [impDB, andDB, boolBinaryTy, PrimitiveSentences.truthDB, CanonicalTerm.equalityDB,
    PrimitiveSentences.identityBool]

theorem applyDB_notDB : substitution.applyDB notDB = notDB := by
  simp [notDB, impDB, andDB, boolBinaryTy, falsityDefinitionDB, forallDB,
    PrimitiveSentences.truthDB, CanonicalTerm.equalityDB, PrimitiveSentences.identityBool]

theorem applyDB_orDB : substitution.applyDB orDB = orDB := by
  simp [orDB, impAppDB, impDB, andDB, boolBinaryTy, forallDB, PrimitiveSentences.truthDB,
    CanonicalTerm.equalityDB, PrimitiveSentences.identityBool]

theorem applyDB_existsDB (A : Ty) :
    substitution.applyDB (existsDB A) = existsDB (substitution.types.apply A) := by
  simp [existsDB, impAppDB, impDB, andDB, boolBinaryTy, forallDB, PrimitiveSentences.truthDB,
    CanonicalTerm.equalityDB, PrimitiveSentences.identityBool]

end ApplyConnectives

/-- The OpenTheory substitution with type component `types` and no term
entries. -/
abbrev typeOnly (types : TypeSubst) : TermSubst := ⟨types, []⟩

theorem reverseSymbol_symbolInstance (types : TypeSubst) {τ : HOL.Ty AtomicTy}
    (symbol : Symbol τ) :
    reverseSymbol (types.symbolInstance symbol) = (typeOnly types).applyDB (reverseSymbol symbol) := by
  cases symbol with
  | constant constant annotation typed => simp [TypeSubst.symbolInstance, reverseSymbol]
  | «variable» sourceVar typed =>
      simp only [TypeSubst.symbolInstance, reverseSymbol]
      rw [TermSubst.applyDB_free_of_lookup_none _ _ (by simp [TermSubst.lookup])]

/-- **Type substitution.**  Translating a retyped term is applying the type
substitution to its translation, when the images of the retyped context
variables are the retyped images. -/
theorem reverseTermWith_mapTypes (types : TypeSubst) :
    ∀ {Γ : HOL.Ctx AtomicTy} (env : VarEnv Γ)
      (env' : VarEnv (Γ.map (HOL.Ty.substitute types.baseInstance))),
      (∀ {ρ : HOL.Ty AtomicTy} (x : HOL.Var Γ ρ),
        env' (x.mapTypes types.baseInstance) = (typeOnly types).applyDB (env x)) →
      ∀ {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ),
        reverseTermWith env' (HOL.mapTypes types.baseInstance types.symbolInstance term) =
          (typeOnly types).applyDB (reverseTermWith env term)
  | _, _, _, h, _, .var x => h x
  | _, _, _, _, _, .const symbol => reverseSymbol_symbolInstance types symbol
  | _, env, env', h, _, .app function argument => by
      simp only [HOL.mapTypes, reverseTermWith, TermSubst.applyDB_app]
      exact congrArg₂ DBTerm.app (reverseTermWith_mapTypes types env env' h function)
        (reverseTermWith_mapTypes types env env' h argument)
  | _, env, env', h, _, .lam (σ := σ) body => by
      simp only [HOL.mapTypes, reverseTermWith, TermSubst.applyDB_abs]
      rw [reverseTy_substitute]
      refine congrArg (DBTerm.abs _) (reverseTermWith_mapTypes types (VarEnv.lift env)
        (VarEnv.lift env') (fun x => ?_) body)
      cases x with
      | vz => simp [VarEnv.lift, HOL.Var.mapTypes]
      | vs x =>
          simp only [VarEnv.lift, HOL.Var.mapTypes]
          rw [h x, applyDB_shiftLoose]
  | _, _, _, _, _, .top => (applyDB_truthDB _).symm
  | _, _, _, _, _, .bot => (applyDB_falsityDefinitionDB _).symm
  | _, env, env', h, _, .and p q => by
      simp only [HOL.mapTypes, reverseTermWith, TermSubst.applyDB_app]
      rw [applyDB_andDB]
      exact congrArg₂ (fun left right => DBTerm.app (.app andDB left) right)
        (reverseTermWith_mapTypes types env env' h p) (reverseTermWith_mapTypes types env env' h q)
  | _, env, env', h, _, .or p q => by
      simp only [HOL.mapTypes, reverseTermWith, TermSubst.applyDB_app]
      rw [applyDB_orDB]
      exact congrArg₂ (fun left right => DBTerm.app (.app orDB left) right)
        (reverseTermWith_mapTypes types env env' h p) (reverseTermWith_mapTypes types env env' h q)
  | _, env, env', h, _, .imp p q => by
      simp only [HOL.mapTypes, reverseTermWith, impAppDB, TermSubst.applyDB_app]
      rw [applyDB_impDB]
      exact congrArg₂ (fun left right => DBTerm.app (.app impDB left) right)
        (reverseTermWith_mapTypes types env env' h p) (reverseTermWith_mapTypes types env env' h q)
  | _, env, env', h, _, .not p => by
      simp only [HOL.mapTypes, reverseTermWith, TermSubst.applyDB_app]
      rw [applyDB_notDB]
      exact congrArg (DBTerm.app notDB) (reverseTermWith_mapTypes types env env' h p)
  | _, env, env', h, _, .eq (τ := ρ) left right => by
      simp only [HOL.mapTypes, reverseTermWith, CanonicalTerm.equalityDB, TermSubst.applyDB_app,
        TermSubst.applyDB_const, TypeSubst.apply_equality]
      rw [reverseTy_substitute]
      exact congrArg₂
        (fun left right => DBTerm.app (.app (.const Const.equality _) left) right)
        (reverseTermWith_mapTypes types env env' h left)
        (reverseTermWith_mapTypes types env env' h right)
  | _, env, env', h, _, .all (σ := σ) body => by
      simp only [HOL.mapTypes, reverseTermWith, TermSubst.applyDB_app, TermSubst.applyDB_abs]
      rw [reverseTy_substitute, applyDB_forallDB]
      refine congrArg (fun body' => DBTerm.app (forallDB _) (DBTerm.abs _ body'))
        (reverseTermWith_mapTypes types (VarEnv.lift env) (VarEnv.lift env') (fun x => ?_) body)
      cases x with
      | vz => simp [VarEnv.lift, HOL.Var.mapTypes]
      | vs x =>
          simp only [VarEnv.lift, HOL.Var.mapTypes]
          rw [h x, applyDB_shiftLoose]
  | _, env, env', h, _, .ex (σ := σ) body => by
      simp only [HOL.mapTypes, reverseTermWith, TermSubst.applyDB_app, TermSubst.applyDB_abs]
      rw [reverseTy_substitute, applyDB_existsDB]
      refine congrArg (fun body' => DBTerm.app (existsDB _) (DBTerm.abs _ body'))
        (reverseTermWith_mapTypes types (VarEnv.lift env) (VarEnv.lift env') (fun x => ?_) body)
      cases x with
      | vz => simp [VarEnv.lift, HOL.Var.mapTypes]
      | vs x =>
          simp only [VarEnv.lift, HOL.Var.mapTypes]
          rw [h x, applyDB_shiftLoose]

/-- The naming of a retyped context: each retyped variable keeps its name. -/
def Naming.mapTypes (types : TypeSubst) :
    {Γ : HOL.Ctx AtomicTy} → Naming Γ → Naming (Γ.map (HOL.Ty.substitute types.baseInstance))
  | [], _ => fun x => nomatch x
  | _ :: _, names => fun x =>
      match x with
      | .vz => names .vz
      | .vs y => Naming.mapTypes types (fun z => names (.vs z)) y

theorem Naming.mapTypes_apply (types : TypeSubst) :
    ∀ {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) {τ : HOL.Ty AtomicTy} (x : HOL.Var Γ τ),
      Naming.mapTypes types names (x.mapTypes types.baseInstance) = names x
  | _ :: _, _, _, .vz => rfl
  | _ :: _, names, _, .vs x => Naming.mapTypes_apply types (fun z => names (.vs z)) x

/-- Type substitution of the reverse under a naming: the retyped context keeps
the names. -/
theorem reverseTerm_mapTypes (types : TypeSubst) {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ) :
    reverseTerm (Naming.mapTypes types names)
        (HOL.mapTypes types.baseInstance types.symbolInstance term) =
      (typeOnly types).applyDB (reverseTerm names term) := by
  refine reverseTermWith_mapTypes types _ _ (fun x => ?_) term
  show DBTerm.free _ = (typeOnly types).applyDB (.free _)
  rw [TermSubst.applyDB_free_of_lookup_none _ _ (by simp [TermSubst.lookup])]
  simp only [Naming.sourceVar, Naming.mapTypes_apply, reverseTy_substitute]
  rfl

/-! ## Examples -/

namespace Examples

/-- The atomic type `ind`. -/
def individual : AtomicTy :=
  ⟨OpenTheory.Examples.individual, rfl, Bool.eq_false_iff.mpr fun h => by
    simp [Ty.isBool_eq_true_iff, OpenTheory.Examples.individual, Ty.bool, TypeOp.bool,
      Name.global] at h⟩

/-- The target base type `ind`. -/
abbrev ind : HOL.Ty AtomicTy := .base individual

theorem individual_toHOL : OpenTheory.Examples.individual.toHOL = ind :=
  Ty.toHOL_of_isAtomic individual.2

/-! ### Each connective becomes its inlined definition -/

theorem reverseTerm_top :
    reverseTerm Naming.empty (.top : HOL.ClosedFormula Symbol) = PrimitiveSentences.truthDB :=
  rfl

theorem reverseTerm_bot :
    reverseTerm Naming.empty (.bot : HOL.ClosedFormula Symbol) = falsityDefinitionDB :=
  rfl

theorem reverseTerm_and_top_bot :
    reverseTerm Naming.empty (.and .top .bot : HOL.ClosedFormula Symbol) =
      .app (.app andDB PrimitiveSentences.truthDB) falsityDefinitionDB :=
  rfl

theorem reverseTerm_or_top_bot :
    reverseTerm Naming.empty (.or .top .bot : HOL.ClosedFormula Symbol) =
      .app (.app orDB PrimitiveSentences.truthDB) falsityDefinitionDB :=
  rfl

theorem reverseTerm_imp_top_bot :
    reverseTerm Naming.empty (.imp .top .bot : HOL.ClosedFormula Symbol) =
      impAppDB PrimitiveSentences.truthDB falsityDefinitionDB :=
  rfl

theorem reverseTerm_not_top :
    reverseTerm Naming.empty (.not .top : HOL.ClosedFormula Symbol) =
      .app notDB PrimitiveSentences.truthDB :=
  rfl

/-- `∀ x : ind. x = x` becomes `∀ (λ x. x = x)` with the inlined `∀`. -/
theorem reverseTerm_all_eq_self :
    reverseTerm Naming.empty
        (.all (σ := ind) (.eq (.var .vz) (.var .vz)) : HOL.ClosedFormula Symbol) =
      .app (forallDB OpenTheory.Examples.individual)
        (.abs OpenTheory.Examples.individual
          (CanonicalTerm.equalityDB OpenTheory.Examples.individual (.bound 0) (.bound 0))) :=
  rfl

/-- `∃ x : ind. x = x` becomes `∃ (λ x. x = x)` with the inlined `∃`. -/
theorem reverseTerm_ex_eq_self :
    reverseTerm Naming.empty
        (.ex (σ := ind) (.eq (.var .vz) (.var .vz)) : HOL.ClosedFormula Symbol) =
      .app (existsDB OpenTheory.Examples.individual)
        (.abs OpenTheory.Examples.individual
          (CanonicalTerm.equalityDB OpenTheory.Examples.individual (.bound 0) (.bound 0))) :=
  rfl

/-- A named context variable becomes a free variable, and a bound one a de
Bruijn index. -/
theorem reverseTerm_named_context :
    reverseTerm (Naming.cons (σ := ind) (Name.global "x") Naming.empty)
        (.all (σ := ind) (.eq (.var (.vs .vz)) (.var .vz))) =
      .app (forallDB OpenTheory.Examples.individual)
        (.abs OpenTheory.Examples.individual
          (CanonicalTerm.equalityDB OpenTheory.Examples.individual
            (.free ⟨Name.global "x", OpenTheory.Examples.individual⟩) (.bound 0))) :=
  rfl

/-- The same formula with the context variable left loose. -/
theorem reverseTermOpen_loose_context :
    reverseTermOpen
        (.all (σ := ind) (.eq (.var (.vs .vz)) (.var .vz)) : HOL.Formula Symbol [ind]) =
      .app (forallDB OpenTheory.Examples.individual)
        (.abs OpenTheory.Examples.individual
          (CanonicalTerm.equalityDB OpenTheory.Examples.individual (.bound 1) (.bound 0))) :=
  rfl

/-! ### Connectives lie outside the image of the forward translation -/

/-- No canonical term translates to the primitive truth constant. -/
theorem not_translates_top (Γ : HOL.Ctx AtomicTy) (term : DBTerm) :
    ¬ Translates Γ term .prop (.top : HOL.Formula Symbol Γ) := by
  intro translation
  cases translation

/-- Reversing and translating forward turns the primitive truth constant into
the defined one. -/
theorem translates_reverseTermOpen_top (Γ : HOL.Ctx AtomicTy) :
    Translates Γ (reverseTermOpen (.top : HOL.Formula Symbol Γ)) .prop truth :=
  PrimitiveSentences.truthDB_translates Γ

theorem truth_ne_top (Γ : HOL.Ctx AtomicTy) : (truth : HOL.Formula Symbol Γ) ≠ .top :=
  fun h => by cases h

/-! ### Unapplied equality comes back eta-expanded -/

/-- The bare equality constant at `ind`. -/
def bareEquality : DBTerm := .const Const.equality (Ty.equality OpenTheory.Examples.individual)

theorem bareEquality_translates :
    Translates [] bareEquality (.arr ind (.arr ind .prop)) (equalityLambda ind) :=
  .equality (equalityOperand?_equality _) individual_toHOL

theorem reverseTermOpen_equalityLambda :
    reverseTermOpen (equalityLambda ind : HOL.ClosedTerm Symbol _) =
      equalityLambdaDB OpenTheory.Examples.individual :=
  (reverseTermOpen_of_translates bareEquality_translates).trans
    (by simp only [bareEquality, expandBareEquality, equalityOperand?_equality])

theorem equalityLambdaDB_ne_bareEquality :
    equalityLambdaDB OpenTheory.Examples.individual ≠ bareEquality :=
  fun h => by cases h

theorem not_equalityFullyApplied_bareEquality : ¬ EqualityFullyApplied bareEquality := by
  intro applied
  cases applied with
  | const unrecognized =>
      rw [equalityOperand?_equality] at unrecognized
      cases unrecognized

/-! ### An equality symbol defeats the round trip on formulas -/

/-- The free variable `x : ind`. -/
abbrev xVar : SourceVar := ⟨Name.global "x", OpenTheory.Examples.individual⟩

/-- The free variable `y : ind`. -/
abbrev yVar : SourceVar := ⟨Name.global "y", OpenTheory.Examples.individual⟩

/-- The variable symbol of `x : ind`. -/
abbrev xSymbol : Symbol ind := .variable xVar individual_toHOL

/-- The variable symbol of `y : ind`. -/
abbrev ySymbol : Symbol ind := .variable yVar individual_toHOL

/-- Primitive equality at `ind`, as an uninterpreted constant symbol. -/
abbrev equalitySymbolAtInd : Symbol (.arr ind (.arr ind .prop)) :=
  .constant Const.equality (Ty.equality OpenTheory.Examples.individual)
    (by rw [Ty.toHOL_equality, individual_toHOL])

/-- `x = y` with `=` the uninterpreted equality symbol. -/
abbrev equalitySymbolFormula : HOL.ClosedFormula Symbol :=
  .app (.app (.const equalitySymbolAtInd) (.const xSymbol)) (.const ySymbol)

theorem not_equalitySymbolFree_equalitySymbolFormula :
    ¬ EqualitySymbolFree equalitySymbolFormula := by
  intro free
  have unrecognized := EqualitySymbolFree.equalityOperand?_eq_none free.app.1.app.1
  rw [equalityOperand?_equality] at unrecognized
  cases unrecognized

/-- The reverse of `equalitySymbolFormula` translates forward to the target
equality `x = y`. -/
theorem translates_reverseTermOpen_equalitySymbolFormula :
    Translates [] (reverseTermOpen equalitySymbolFormula) .prop
      (.eq (.const xSymbol) (.const ySymbol)) :=
  show Translates [] (CanonicalTerm.equalityDB OpenTheory.Examples.individual (.free xVar)
      (.free yVar)) _ _ from
    .equalityApp (equalityOperand?_equality _) individual_toHOL (.free individual_toHOL)
      (.free individual_toHOL)

open Classical in
/-- Symbol denotations over the two-element carrier: `x` is `true`, every
other symbol is a fixed default; the equality symbol is constantly true. -/
noncomputable def separatingDen :
    {τ : HOL.Ty AtomicTy} → Symbol τ →
      HOL.Ty.denote.{0, 0} (fun _ : AtomicTy => ULift.{1} Bool) τ
  | τ, .variable sourceVar _ =>
      if h : sourceVar = xVar ∧ τ = ind then h.2 ▸ (ULift.up true : ULift.{1} Bool)
      else twoPointDefault τ
  | τ, .constant .. => twoPointDefault τ

/-- The standard model of `separatingDen`. -/
noncomputable def separatingModel : HOL.HenkinModel.{0, 0, 0} AtomicTy Symbol :=
  HOL.HenkinModel.standard (fun _ => ULift.{1} Bool) separatingDen

/-- **The round trip on formulas needs `EqualitySymbolFree`.**  The forward
translation of the reverse of `equalitySymbolFormula` is not provably equal to
it: in `separatingModel` the equality symbol holds of `x` and `y`, while `x`
and `y` differ. -/
theorem not_extDerivation_eq_equalitySymbolFormula :
    ¬ HOL.ExtDerivation Symbol ([] : List (HOL.ClosedFormula Symbol))
      (.eq (.eq (.const xSymbol) (.const ySymbol)) equalitySymbolFormula) := by
  intro derivation
  have holds : (separatingDen xSymbol = separatingDen ySymbol) ↔ True :=
    HOL.Soundness.extTheorem_sound derivation separatingModel
      (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _
        (HOL.HenkinModel.fullDomains_standard _ _))
  have hequal := holds.mpr trivial
  simp [separatingDen, xVar, yVar, Name.global, twoPointDefault] at hequal
  exact Bool.noConfusion (congrArg ULift.down hequal)

end Examples

end ReverseTranslation

end Mettapedia.Languages.OpenTheory
