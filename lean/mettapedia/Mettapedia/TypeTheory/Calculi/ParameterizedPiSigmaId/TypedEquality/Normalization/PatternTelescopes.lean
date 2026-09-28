import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Definitions

/-!
# Pattern telescopes

A definition by structural recursion on the argument at position `s` of a
telescope `x₀ ⋯ x_{s-1} (t : T) y₁ ⋯ y_d` has, for each constructor
`k : F₁ → ⋯ → Fₐ → T`, an equation whose variables are, in order,

`x₀ ⋯ x_{s-1}  v₁ ⋯ vₐ  y₁ ⋯ y_d`,

the later entries seeing `k v₁ ⋯ vₐ` in place of `t`. This module builds that
pattern context, the pattern substitution from the telescope into it, and the
matching substitution that instantiates the pattern at a given argument list
whose scrutinee is `k a₁ ⋯ aₐ`; instantiating the pattern by the match gives
back the arguments with the scrutinee replaced by the constructor form.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed)

variable {Head : Type}

/-! ## Telescopes and substitutions extended entry by entry -/

/-- Extend a context by entries, the entry at `j` living after the first `j`. -/
def extendEntries {n : Nat} (Γ : Ctx Head n) (entry : (j : Nat) → Tm Head (n + j)) :
    (d : Nat) → Ctx Head (n + d)
  | 0 => Γ
  | d + 1 => .snoc (extendEntries Γ entry d) (entry d)

/-- Lift a substitution under `j` binders. -/
def liftSubN {n m : Nat} (σ : Sub Head n m) : (j : Nat) → Sub Head (n + j) (m + j)
  | 0 => σ
  | j + 1 => liftSub (liftSubN σ j)

/-- Extend a substitution by the entries `values l` for `l < d`, the last one
innermost. -/
def extendSub {n m : Nat} (ρ : Sub Head n m) (values : Nat → Tm Head m) :
    (d : Nat) → Sub Head (n + d) m
  | 0 => ρ
  | d + 1 => consSub (values d) (extendSub ρ values d)

/-- The dependent function type over the entries after position `j`, ending
in `C`. -/
def piRange (e : (i : Nat) → Tm Head i) (j : Nat) : (d : Nat) → Tm Head (j + d) → Tm Head j
  | 0, C => C
  | d + 1, C => piRange e j d (.pi (e (j + d)) C)

theorem closeType_ofEntries_add (e : (i : Nat) → Tm Head i) (j : Nat) :
    ∀ (d : Nat) (C : Tm Head (j + d)),
      closeType (ofEntries e (j + d)) C = closeType (ofEntries e j) (piRange e j d C)
  | 0, _ => rfl
  | d + 1, C => closeType_ofEntries_add e j d (.pi (e (j + d)) C)

theorem extendSub_ge {n m : Nat} (ρ : Sub Head n m) (values : Nat → Tm Head m) :
    ∀ (d : Nat) (i : Fin n), extendSub ρ values d ⟨i.val + d, by omega⟩ = ρ i
  | 0, i => rfl
  | d + 1, i => by
      show extendSub ρ values d ⟨i.val + d, by omega⟩ = ρ i
      exact extendSub_ge ρ values d i

/-! ## The pattern of a constructor -/

/-- The variables of `a` fields, in order, in the context just after them. -/
def fieldVars (s : Nat) : (a : Nat) → List (Tm Head (s + a))
  | 0 => []
  | a + 1 => (fieldVars s a).map (Presentation.rename wk) ++ [.var 0]

/-- The pattern for the prefix and the scrutinee: the prefix variables past the
fields, and the constructor `k` applied to the fields. -/
def patSub (s a : Nat) (k : DeclName) : Sub Head (s + 1) (s + a) :=
  consSub (appSpine (.const k) (fieldVars s a)) fun i => .var ⟨i.val + a, by omega⟩

/-- The context of the prefix and the fields of a constructor of `T`. -/
def fieldCtx (T : DeclName) (e : (i : Nat) → Tm Head i) (s : Nat) (fields : List (Field Head)) :
    Ctx Head (s + fields.length) :=
  extendEntries (ofEntries e s) (fun l => liftClosed ((fields.getD l .recursive).type T))
    fields.length

/-- The context of an equation for constructor `k`: the prefix, the fields, and
the later entries with the constructor form in place of the scrutinee. -/
def patternCtx (T k : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (fields : List (Field Head)) : Ctx Head (s + fields.length + d) :=
  extendEntries (fieldCtx T e s fields)
    (fun j => Presentation.subst (liftSubN (patSub s fields.length k) j) (e (s + 1 + j))) d

/-- The substitution of the telescope by the pattern of constructor `k`. -/
def patternSub (s a d : Nat) (k : DeclName) : Sub Head (s + 1 + d) (s + a + d) :=
  liftSubN (patSub s a k) d

/-! ## Matching -/

/-- A default term, for out-of-range list access. -/
def defaultTm {m : Nat} : Tm Head m := .const .anonymous

/-- The substitution of the pattern context sending the prefix and the later
variables to the arguments `σ` and the fields to `as`. -/
def matchSub {m : Nat} (s a : Nat) (as : List (Tm Head m)) :
    (d : Nat) → Sub Head (s + 1 + d) m → Sub Head (s + a + d) m
  | 0, σ => extendSub (tailSub σ) (fun l => as.getD l defaultTm) a
  | d + 1, σ => consSub (σ 0) (matchSub s a as d (tailSub σ))

/-- The arguments `σ` with the scrutinee, at position `d` from the end,
replaced by `x`. -/
def replaceScrut {m : Nat} (s : Nat) (x : Tm Head m) :
    (d : Nat) → Sub Head (s + 1 + d) m → Sub Head (s + 1 + d) m
  | 0, σ => consSub x (tailSub σ)
  | d + 1, σ => consSub (σ 0) (replaceScrut s x d (tailSub σ))

theorem fieldVars_map_extendSub {m s : Nat} (ρ : Sub Head s m) (values : Nat → Tm Head m) :
    ∀ (a : Nat), (fieldVars s a).map (Presentation.subst (extendSub ρ values a)) =
      (List.range a).map values
  | 0 => rfl
  | a + 1 => by
      have e : ∀ t : Tm Head (s + a),
          Presentation.subst (extendSub ρ values (a + 1)) (Presentation.rename wk t) =
            Presentation.subst (extendSub ρ values a) t :=
        fun t => subst_consSub_rename_wk _ _ t
      have ih := fieldVars_map_extendSub ρ values a
      simp only [fieldVars, List.map_append, List.map_map, Function.comp_def, e, List.map_cons,
        List.map_nil, List.range_succ]
      rw [ih]
      rfl

theorem range_map_getD {m : Nat} (as : List (Tm Head m)) :
    (List.range as.length).map (fun l => as.getD l defaultTm) = as := by
  apply List.ext_getElem
  · simp
  · intro l h₁ h₂
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

/-- Instantiating the pattern by the match gives the arguments with the
scrutinee replaced by the constructor form. -/
theorem subst_matchSub_patternSub {m s a : Nat} (k : DeclName) (as : List (Tm Head m))
    (has : as.length = a) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m) (ι : Fin (s + 1 + d)),
      Presentation.subst (matchSub s a as d σ) (patternSub s a d k ι) =
        replaceScrut s (appSpine (.const k) as) d σ ι
  | 0, σ, ι => by
      refine Fin.cases ?_ (fun i => ?_) ι
      · show Presentation.subst (extendSub (tailSub σ) (fun l => as.getD l defaultTm) a)
          (appSpine (.const k) (fieldVars s a)) = appSpine (.const k) as
        rw [subst_appSpine, fieldVars_map_extendSub, ← has, range_map_getD]
        rfl
      · show extendSub (tailSub σ) (fun l => as.getD l defaultTm) a ⟨i.val + a, by omega⟩ =
          tailSub σ i
        exact extendSub_ge (tailSub σ) _ a i
  | d + 1, σ, ι => by
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · show Presentation.subst (consSub (σ 0) (matchSub s a as d (tailSub σ)))
          (liftSub (patternSub s a d k) i.succ) = replaceScrut s (appSpine (.const k) as) d (tailSub σ) i
        rw [liftSub_succ, subst_consSub_rename_wk]
        exact subst_matchSub_patternSub k as has d (tailSub σ) i

/-! ## Arguments around the scrutinee -/

/-- The arguments before the scrutinee. -/
def prefixSub {m : Nat} (s : Nat) : (d : Nat) → Sub Head (s + 1 + d) m → Sub Head s m
  | 0, σ => tailSub σ
  | d + 1, σ => prefixSub s d (tailSub σ)

/-- The scrutinee. -/
def scrutOf {m : Nat} (s : Nat) : (d : Nat) → Sub Head (s + 1 + d) m → Tm Head m
  | 0, σ => σ 0
  | d + 1, σ => scrutOf s d (tailSub σ)

/-- The arguments after the scrutinee, in order. -/
def suffixArgs {m : Nat} (s : Nat) : (d : Nat) → Sub Head (s + 1 + d) m → List (Tm Head m)
  | 0, _ => []
  | d + 1, σ => suffixArgs s d (tailSub σ) ++ [σ 0]

theorem telescopeArgs_split (e : (i : Nat) → Tm Head i) (s : Nat) {m : Nat} :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m),
      telescopeArgs (ofEntries e (s + 1 + d)) σ =
        telescopeArgs (ofEntries e s) (prefixSub s d σ) ++ [scrutOf s d σ] ++ suffixArgs s d σ
  | 0, σ => by simp [prefixSub, scrutOf, suffixArgs]; rfl
  | d + 1, σ => by
      show telescopeArgs (ofEntries e (s + 1 + d + 1)) σ = _
      rw [telescopeArgs_ofEntries_succ, telescopeArgs_split e s d (tailSub σ)]
      simp [prefixSub, scrutOf, suffixArgs]

theorem prefixSub_replaceScrut {m s : Nat} (x : Tm Head m) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m), prefixSub s d (replaceScrut s x d σ) = prefixSub s d σ
  | 0, _ => rfl
  | d + 1, σ => prefixSub_replaceScrut x d (tailSub σ)

theorem scrutOf_replaceScrut {m s : Nat} (x : Tm Head m) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m), scrutOf s d (replaceScrut s x d σ) = x
  | 0, _ => rfl
  | d + 1, σ => scrutOf_replaceScrut x d (tailSub σ)

theorem suffixArgs_replaceScrut {m s : Nat} (x : Tm Head m) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m), suffixArgs s d (replaceScrut s x d σ) = suffixArgs s d σ
  | 0, _ => rfl
  | d + 1, σ => by
      show suffixArgs s d (replaceScrut s x d (tailSub σ)) ++ [σ 0] = _
      rw [suffixArgs_replaceScrut x d (tailSub σ)]
      rfl

theorem replaceScrut_self {m s : Nat} :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m), replaceScrut s (scrutOf s d σ) d σ = σ
  | 0, σ => consSub_eta σ
  | d + 1, σ => by
      show consSub (σ 0) (replaceScrut s (scrutOf s d (tailSub σ)) d (tailSub σ)) = σ
      rw [replaceScrut_self d (tailSub σ)]
      exact consSub_eta σ

theorem prefixSub_rename {m k s : Nat} (ρ : Ren m k) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m),
      prefixSub s d (fun i => Presentation.rename ρ (σ i)) =
        fun i => Presentation.rename ρ (prefixSub s d σ i)
  | 0, _ => rfl
  | d + 1, σ => prefixSub_rename ρ d (tailSub σ)

theorem scrutOf_rename {m k s : Nat} (ρ : Ren m k) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m),
      scrutOf s d (fun i => Presentation.rename ρ (σ i)) = Presentation.rename ρ (scrutOf s d σ)
  | 0, _ => rfl
  | d + 1, σ => scrutOf_rename ρ d (tailSub σ)

/-! ## Recursive calls -/

/-- The positions of the recursive fields. -/
def recPositions : List (Field Head) → List Nat
  | [] => []
  | .recursive :: fs => 0 :: (recPositions fs).map (· + 1)
  | .closed _ :: fs => (recPositions fs).map (· + 1)

/-- Weakening past `j` new variables. -/
def wkN {n : Nat} (j : Nat) : Ren n (n + j) := fun i => ⟨i.val + j, by omega⟩

/-- The arguments of a recursive call on the field at position `l`: the prefix
variables and the field's variable, in the context of an equation. -/
def callSub (s a d l : Nat) : Sub Head (s + 1) (s + a + d) :=
  consSub (if h : l < a then .var ⟨d + (a - 1 - l), by omega⟩ else defaultTm)
    fun i => .var ⟨i.val + a + d, by omega⟩

/-- The recursive call of `f` on the field at position `l`: `f` applied to the
prefix and the field, a function of the arguments after the scrutinee. -/
def recCall (f : DeclName) (e : (i : Nat) → Tm Head i) (s a d l : Nat) : Tm Head (s + a + d) :=
  applyClosed (ofEntries e (s + 1)) (callSub s a d l) (.const f)

/-- The type of the recursive call on the field at position `l`. -/
def recCallType (e : (i : Nat) → Tm Head i) (s a d l : Nat) (C : Tm Head (s + 1 + d)) :
    Tm Head (s + a + d) :=
  Presentation.subst (callSub s a d l) (piRange e (s + 1) d C)

/-- The context of an equation extended by one hypothesis for each recursive
field, typed as the recursive call on it. -/
def hypCtx (T k : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat) (fields : List (Field Head))
    (C : Tm Head (s + 1 + d)) : Ctx Head (s + fields.length + d + (recPositions fields).length) :=
  extendEntries (patternCtx T k e s d fields)
    (fun j => Presentation.rename (wkN j)
      (recCallType e s fields.length d ((recPositions fields).getD j 0) C))
    (recPositions fields).length

/-- The substitution of the hypotheses by the recursive calls. -/
def hypSub (f : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat) (fields : List (Field Head)) :
    Sub Head (s + fields.length + d + (recPositions fields).length) (s + fields.length + d) :=
  extendSub ids (fun j => recCall f e s fields.length d ((recPositions fields).getD j 0))
    (recPositions fields).length

theorem subst_extendSub {m k : Nat} (τ : Sub Head m k) (values : Nat → Tm Head m) :
    ∀ (r : Nat), (fun ι => Presentation.subst τ (extendSub (ids : Sub Head m m) values r ι)) =
      extendSub τ (fun j => Presentation.subst τ (values j)) r
  | 0 => rfl
  | r + 1 => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · show Presentation.subst τ (extendSub ids values r i) = extendSub τ _ r i
        exact congrFun (subst_extendSub τ values r) i

/-! ## The match at the pattern's variables -/

theorem matchSub_field {m s a : Nat} (as : List (Tm Head m)) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m) (l : Nat) (hl : l < a),
      matchSub s a as d σ ⟨d + (a - 1 - l), by omega⟩ = as.getD l defaultTm
  | 0, σ, l, hl => by
      have e₀ : (⟨0 + (a - 1 - l), by omega⟩ : Fin (s + a + 0)) = ⟨a - 1 - l, by omega⟩ :=
        Fin.ext (by simp)
      rw [e₀]
      show extendSub (tailSub σ) (fun l => as.getD l defaultTm) a ⟨a - 1 - l, by omega⟩ = _
      have key : ∀ (b : Nat) (i : Nat) (hi : i < b) (hb : b ≤ a),
          extendSub (tailSub σ) (fun l => as.getD l defaultTm) b ⟨i, by omega⟩ =
            as.getD (b - 1 - i) defaultTm := by
        intro b
        induction b with
        | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
        | succ b ih =>
            intro i hi hb
            cases i with
            | zero => simp [extendSub]
            | succ i =>
                show extendSub (tailSub σ) _ b ⟨i, by omega⟩ = _
                rw [ih i (by omega) (by omega)]
                congr 1
                omega
      rw [key a (a - 1 - l) (by omega) (Nat.le_refl a)]
      congr 1
      omega
  | d + 1, σ, l, hl => by
      have e : (⟨d + 1 + (a - 1 - l), by omega⟩ : Fin (s + a + (d + 1))) =
          Fin.succ (⟨d + (a - 1 - l), by omega⟩ : Fin (s + a + d)) := Fin.ext (by simp; omega)
      rw [e]
      exact matchSub_field as d (tailSub σ) l hl

theorem matchSub_prefix {m s a : Nat} (as : List (Tm Head m)) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m) (i : Fin s),
      matchSub s a as d σ ⟨i.val + a + d, by omega⟩ = prefixSub s d σ i
  | 0, σ, i => by
      show extendSub (tailSub σ) (fun l => as.getD l defaultTm) a ⟨i.val + a, by omega⟩ = tailSub σ i
      exact extendSub_ge (tailSub σ) _ a i
  | d + 1, σ, i => by
      have e : (⟨i.val + a + (d + 1), by omega⟩ : Fin (s + a + (d + 1))) =
          Fin.succ (⟨i.val + a + d, by omega⟩ : Fin (s + a + d)) := Fin.ext rfl
      rw [e]
      exact matchSub_prefix as d (tailSub σ) i

/-- The recursive call's arguments under the match: the prefix and the field. -/
theorem callSub_matchSub {m s a : Nat} (as : List (Tm Head m)) (d : Nat)
    (σ : Sub Head (s + 1 + d) m) (l : Nat) (hl : l < a) :
    (fun ι => Presentation.subst (matchSub s a as d σ) (callSub s a d l ι)) =
      consSub (as.getD l defaultTm) (prefixSub s d σ) := by
  funext ι
  refine Fin.cases ?_ (fun i => ?_) ι
  · show Presentation.subst (matchSub s a as d σ)
      (if h : l < a then .var ⟨d + (a - 1 - l), by omega⟩ else defaultTm) = _
    rw [dif_pos hl]
    exact matchSub_field as d σ l hl
  · exact matchSub_prefix as d σ i

theorem subst_extendSub_wkN {n m : Nat} (τ : Sub Head n m) (values : Nat → Tm Head m) :
    ∀ (j : Nat) (X : Tm Head n),
      Presentation.subst (extendSub τ values j) (Presentation.rename (wkN j) X) =
        Presentation.subst τ X
  | 0, X => by
      show Presentation.subst τ (Presentation.rename (fun i => ⟨i.val + 0, by omega⟩) X) = _
      rw [show (fun i : Fin n => (⟨i.val + 0, by omega⟩ : Fin (n + 0))) = idRen from rfl,
        rename_id]
  | j + 1, X => by
      have e : (wkN (j + 1) : Ren n (n + (j + 1))) = fun i => wk (wkN j i) := rfl
      rw [e, ← rename_comp]
      show Presentation.subst (consSub (values j) (extendSub τ values j))
        (Presentation.rename wk (Presentation.rename (wkN j) X)) = _
      rw [subst_consSub_rename_wk]
      exact subst_extendSub_wkN τ values j X

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
