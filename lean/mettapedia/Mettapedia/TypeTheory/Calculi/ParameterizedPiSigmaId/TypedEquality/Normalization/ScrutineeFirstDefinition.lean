import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirst
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DefinitionConsequences

/-!
# The definition that passes its arguments to the scrutinee-first form

A definition by structural recursion whose recursive calls change an
argument before the scrutinee is admitted through its scrutinee-first form
`f'` and the definition `f x̄ y z̄ = f' y x̄ z̄`. This module builds the move
between the two argument lists, the right-hand side of that definition, and
the substitution identities that make the δ-step of `f` at a constructor
pattern a full application of `f'` with the pattern at its scrutinee, which
is where the ι-step of `f'` applies.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (applyClosed applyClosed_subst)

variable {Head : Type}

/-! ## The move between the argument lists

The authored telescope has the prefix, the scrutinee at position `s`, and
`d` later entries; the scrutinee-first telescope has the scrutinee first.
In de Bruijn indices from the end, the later entries keep theirs, the
scrutinee goes from `d` to `d + s`, and the prefix moves down by one. -/

/-- The index of an authored argument in the scrutinee-first list. -/
def teleMove (s d : Nat) : Ren (s + 1 + d) (0 + 1 + (s + d)) := fun i =>
  if h : i.val < d then ⟨i.val, by omega⟩
  else if h' : i.val = d then ⟨d + s, by omega⟩
  else ⟨i.val - 1, by omega⟩

/-- The index of a scrutinee-first argument in the authored list. -/
def teleMoveBack (s d : Nat) : Ren (0 + 1 + (s + d)) (s + 1 + d) := fun j =>
  if h : j.val < d then ⟨j.val, by omega⟩
  else if h' : j.val < d + s then ⟨j.val + 1, by omega⟩
  else ⟨d, by omega⟩

theorem teleMove_val (s d : Nat) (i : Fin (s + 1 + d)) :
    (teleMove s d i).val = if i.val < d then i.val else if i.val = d then d + s else i.val - 1 := by
  by_cases h₁ : i.val < d
  · simp [teleMove, h₁]
  · by_cases h₂ : i.val = d
    · simp [teleMove, h₂]
    · simp [teleMove, h₁, h₂]

theorem teleMoveBack_val (s d : Nat) (j : Fin (0 + 1 + (s + d))) :
    (teleMoveBack s d j).val =
      if j.val < d then j.val else if j.val < d + s then j.val + 1 else d := by
  by_cases h₁ : j.val < d
  · simp [teleMoveBack, h₁]
  · by_cases h₂ : j.val < d + s
    · simp [teleMoveBack, h₁, h₂]
    · simp [teleMoveBack, h₁, h₂]

theorem teleMoveBack_teleMove (s d : Nat) (i : Fin (s + 1 + d)) :
    teleMoveBack s d (teleMove s d i) = i := by
  apply Fin.ext
  rw [teleMoveBack_val, teleMove_val]
  have := i.isLt
  by_cases h₁ : i.val < d
  · rw [if_pos h₁, if_pos h₁]
  · rw [if_neg h₁]
    by_cases h₂ : i.val = d
    · rw [if_pos h₂, if_neg (by omega), if_neg (by omega)]
      omega
    · rw [if_neg h₂, if_neg (by omega), if_pos (by omega)]
      omega

theorem teleMove_teleMoveBack (s d : Nat) (j : Fin (0 + 1 + (s + d))) :
    teleMove s d (teleMoveBack s d j) = j := by
  apply Fin.ext
  rw [teleMove_val, teleMoveBack_val]
  have := j.isLt
  by_cases h₁ : j.val < d
  · rw [if_pos h₁, if_pos h₁]
  · rw [if_neg h₁]
    by_cases h₂ : j.val < d + s
    · rw [if_pos h₂, if_neg (by omega), if_neg (by omega)]
      omega
    · rw [if_neg h₂, if_neg (by omega), if_pos rfl]
      omega

/-! ## The scrutinee replaced, by values -/

/-- `replaceScrut` by its values: the scrutinee's index gets `x`, the others
keep `σ`. -/
theorem replaceScrut_apply {m : Nat} (s : Nat) (x : Tm Head m) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m) (i : Fin (s + 1 + d)),
      replaceScrut s x d σ i = if i.val = d then x else σ i
  | 0, σ, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (if_pos rfl).symm
      · exact (if_neg (Nat.succ_ne_zero j.val)).symm
  | d + 1, σ, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (if_neg (Nat.succ_ne_zero d).symm).symm
      · show replaceScrut s x d (tailSub σ) j = _
        rw [replaceScrut_apply s x d (tailSub σ) j]
        by_cases h : j.val = d
        · rw [if_pos h, if_pos (by rw [Fin.val_succ, h])]
        · rw [if_neg h, if_neg (by rw [Fin.val_succ]; omega)]

/-- Replacing the scrutinee and then moving the arguments is moving them and
then replacing the scrutinee at its new place. -/
theorem replaceScrut_teleMoveBack {m : Nat} (s d : Nat) (x : Tm Head m)
    (σ : Sub Head (s + 1 + d) m) :
    (fun j => replaceScrut s x d σ (teleMoveBack s d j)) =
      replaceScrut 0 x (s + d) (fun j => σ (teleMoveBack s d j)) := by
  funext j
  rw [replaceScrut_apply, replaceScrut_apply, teleMoveBack_val]
  have := j.isLt
  by_cases h₁ : j.val < d
  · rw [if_pos h₁, if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h₁]
    by_cases h₂ : j.val < d + s
    · rw [if_pos h₂, if_neg (by omega), if_neg (by omega)]
    · rw [if_neg h₂, if_pos rfl, if_pos (by omega)]

/-! ## The match, by values, and under the block move

The pattern variables of the authored equation and of its scrutinee-first
form stand for the same arguments: the match of the scrutinee-first form at
the moved index is the authored match. -/

/-- `extendSub` by its values: the last `b` indices read the values in
reverse, the others the base substitution. -/
theorem extendSub_apply {n m : Nat} (ρ : Sub Head n m) (values : Nat → Tm Head m) :
    ∀ (b : Nat) (i : Fin (n + b)),
      extendSub ρ values b i =
        if h : i.val < b then values (b - 1 - i.val)
        else ρ ⟨i.val - b, by have := i.isLt; omega⟩
  | 0, i => by
      rw [show extendSub ρ values 0 = ρ from rfl, dif_neg (Nat.not_lt_zero _)]
      exact congrArg ρ (Fin.ext rfl)
  | b + 1, ⟨0, _⟩ => by
      show values b = _
      dsimp only
      rw [dif_pos (show 0 < b + 1 by omega), show b + 1 - 1 - 0 = b by omega]
  | b + 1, ⟨k + 1, hk⟩ => by
      show extendSub ρ values b ⟨k, by omega⟩ = _
      rw [extendSub_apply ρ values b ⟨k, by omega⟩]
      dsimp only
      by_cases h : k < b
      · rw [dif_pos h, dif_pos (show k + 1 < b + 1 by omega),
          show b + 1 - 1 - (k + 1) = b - 1 - k by omega]
      · rw [dif_neg h, dif_neg (show ¬ k + 1 < b + 1 by omega)]
        exact congrArg ρ (Fin.ext (by show k - b = k + 1 - (b + 1); omega))

/-- `matchSub` by its values: the later arguments, then the fields in
reverse, then the prefix arguments, which sit past the scrutinee in `σ`. -/
theorem matchSub_apply {m : Nat} (s a : Nat) (as : List (Tm Head m)) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m) (i : Fin (s + a + d)),
      matchSub s a as d σ i =
        if h : i.val < d then σ ⟨i.val, by omega⟩
        else if h' : i.val < d + a then as.getD (a - 1 - (i.val - d)) defaultTm
        else σ ⟨i.val - a + 1, by have := i.isLt; omega⟩
  | 0, σ, i => by
      show extendSub (tailSub σ) (fun l => as.getD l defaultTm) a i = _
      rw [extendSub_apply, dif_neg (Nat.not_lt_zero _)]
      by_cases h : i.val < a
      · rw [dif_pos h, dif_pos (show i.val < 0 + a by omega),
          show a - 1 - (i.val - 0) = a - 1 - i.val by omega]
      · rw [dif_neg h, dif_neg (show ¬ i.val < 0 + a by omega)]
        exact congrArg σ (Fin.ext rfl)
  | d + 1, σ, ⟨0, _⟩ => by
      show σ 0 = _
      dsimp only
      rw [dif_pos (show 0 < d + 1 by omega)]
      exact congrArg σ (Fin.ext rfl)
  | d + 1, σ, ⟨k + 1, hk⟩ => by
      show matchSub s a as d (tailSub σ) ⟨k, by omega⟩ = _
      rw [matchSub_apply s a as d (tailSub σ) ⟨k, by omega⟩]
      dsimp only
      by_cases h₁ : k < d
      · rw [dif_pos h₁, dif_pos (show k + 1 < d + 1 by omega)]
        exact congrArg σ (Fin.ext rfl)
      · rw [dif_neg h₁, dif_neg (show ¬ k + 1 < d + 1 by omega)]
        by_cases h₂ : k < d + a
        · rw [dif_pos h₂, dif_pos (show k + 1 < d + 1 + a by omega),
            show a - 1 - (k + 1 - (d + 1)) = a - 1 - (k - d) by omega]
        · rw [dif_neg h₂, dif_neg (show ¬ k + 1 < d + 1 + a by omega)]
          exact congrArg σ (Fin.ext (by show k - a + 1 + 1 = k + 1 - a + 1; omega))

/-- The match of the scrutinee-first form at the moved index is the authored
match: the pattern variables of the two equations stand for the same
arguments. -/
theorem matchSub_blockMove {m : Nat} (s a d : Nat) (as : List (Tm Head m))
    (σ : Sub Head (s + 1 + d) m) (i : Fin (s + a + d)) :
    matchSub 0 a as (s + d) (fun j => σ (teleMoveBack s d j)) (blockMove s a d i) =
      matchSub s a as d σ i := by
  rw [matchSub_apply, matchSub_apply]
  have := i.isLt
  rcases Nat.lt_or_ge i.val d with h₁ | h₁
  · rw [show blockMove s a d i = ⟨i.val, by omega⟩ by simp [blockMove, h₁]]
    dsimp only
    rw [dif_pos (show i.val < s + d by omega), dif_pos h₁]
    exact congrArg σ (Fin.ext (by rw [teleMoveBack_val]; dsimp only; rw [if_pos h₁]))
  · rcases Nat.lt_or_ge i.val (d + a) with h₂ | h₂
    · rw [show blockMove s a d i = ⟨i.val + s, by omega⟩ by
        simp [blockMove, Nat.not_lt.mpr h₁, h₂]]
      dsimp only
      rw [dif_neg (show ¬ i.val + s < s + d by omega),
        dif_pos (show i.val + s < s + d + a by omega), dif_neg (Nat.not_lt.mpr h₁), dif_pos h₂,
        show a - 1 - (i.val + s - (s + d)) = a - 1 - (i.val - d) by omega]
    · rw [show blockMove s a d i = ⟨i.val - a, by omega⟩ by
        simp [blockMove, Nat.not_lt.mpr h₁, Nat.not_lt.mpr h₂]]
      dsimp only
      rw [dif_pos (show i.val - a < s + d by omega), dif_neg (Nat.not_lt.mpr h₁),
        dif_neg (Nat.not_lt.mpr h₂)]
      exact congrArg σ (Fin.ext (by
        rw [teleMoveBack_val]; dsimp only
        rw [if_neg (show ¬ i.val - a < d by omega), if_pos (show i.val - a < d + s by omega)]))

/-! ## The right-hand side of the definition -/

/-- The right-hand side of `f x̄ y z̄ = f' y x̄ z̄`: the scrutinee-first form
applied to the authored variables in its order. -/
def definitionBody (F : Nat → Tm Head 0) (f' : DeclName) (s d : Nat) : Tm Head (s + 1 + d) :=
  applyClosed (ofEntries (fun i => liftClosed (scrutineeFirst F s i)) (0 + 1 + (s + d)))
    (fun j => .var (teleMoveBack s d j)) (.const f')

/-- Under a substitution of the authored arguments, the right-hand side is
the scrutinee-first form applied to the moved arguments. -/
theorem subst_definitionBody {m : Nat} (F : Nat → Tm Head 0) (f' : DeclName) (s d : Nat)
    (σ : Sub Head (s + 1 + d) m) :
    Presentation.subst σ (definitionBody F f' s d) =
      applyClosed (ofEntries (fun i => liftClosed (scrutineeFirst F s i)) (0 + 1 + (s + d)))
        (fun j => σ (teleMoveBack s d j)) (.const f') := by
  unfold definitionBody
  rw [applyClosed_subst]
  rfl

/-- The δ-step of `f` at a constructor pattern, on its right: `f'` fully
applied, with the pattern at its scrutinee. -/
theorem subst_definitionBody_replaceScrut {m : Nat} (F : Nat → Tm Head 0) (f' : DeclName)
    (s d : Nat) (x : Tm Head m) (σ : Sub Head (s + 1 + d) m) :
    Presentation.subst (replaceScrut s x d σ) (definitionBody F f' s d) =
      applyClosed (ofEntries (fun i => liftClosed (scrutineeFirst F s i)) (0 + 1 + (s + d)))
        (replaceScrut 0 x (s + d) (fun j => σ (teleMoveBack s d j))) (.const f') := by
  rw [subst_definitionBody, replaceScrut_teleMoveBack]

/-! ## `piClosed` under renaming and substitution -/

theorem rename_piClosed {n m : Nat} (ρ : Ren n m) (G : Nat → Tm Head 0) :
    ∀ (d : Nat) (C : Tm Head (n + d)),
      Presentation.rename ρ (piClosed G d C) = piClosed G d (Presentation.rename (liftRenN ρ d) C)
  | 0, _ => rfl
  | d + 1, C => by
      show Presentation.rename ρ (piClosed G d (.pi (liftClosed (G d)) C)) =
        piClosed G d (.pi (liftClosed (G d)) (Presentation.rename (liftRen (liftRenN ρ d)) C))
      rw [rename_piClosed ρ G d]
      show piClosed G d (.pi (Presentation.rename (liftRenN ρ d) (liftClosed (G d)))
        (Presentation.rename (liftRen (liftRenN ρ d)) C)) = _
      rw [rename_liftClosed]

theorem subst_piClosed {n m : Nat} (τ : Sub Head n m) (G : Nat → Tm Head 0) :
    ∀ (d : Nat) (C : Tm Head (n + d)),
      Presentation.subst τ (piClosed G d C) = piClosed G d (Presentation.subst (liftSubN τ d) C)
  | 0, _ => rfl
  | d + 1, C => by
      show Presentation.subst τ (piClosed G d (.pi (liftClosed (G d)) C)) =
        piClosed G d (.pi (liftClosed (G d)) (Presentation.subst (liftSub (liftSubN τ d)) C))
      rw [subst_piClosed τ G d]
      show piClosed G d (.pi (Presentation.subst (liftSubN τ d) (liftClosed (G d)))
        (Presentation.subst (liftSub (liftSubN τ d)) C)) = _
      rw [subst_liftClosed]

/-! ## The body of the scrutinee-first form

The scrutinee-first body is the authored body under the substitution that
moves the pattern variables along `blockMove` and replaces each hypothesis,
a function of the later arguments, by the scrutinee-first hypothesis, a
function of the prefix and the later arguments, applied to the prefix
variables. -/

/-- The prefix variables of the scrutinee-first equation context, oldest
first, past `r` hypotheses: the later entries occupy the indices below `d`,
the prefix the `s` indices above them. -/
def prefixVars (s a d r : Nat) : List (Tm Head (0 + a + (s + d) + r)) :=
  List.ofFn fun p : Fin s => .var ⟨d + r + (s - 1 - p.val), by omega⟩

/-- The substitution from the authored equation context to the scrutinee-first
one. -/
def hypMove (s a d r : Nat) : Sub Head (s + a + d + r) (0 + a + (s + d) + r) :=
  extendSub (fun i => .var (wkN r (blockMove s a d i)))
    (fun j => if h : j < r then appSpine (.var ⟨r - 1 - j, by omega⟩) (prefixVars s a d r)
      else defaultTm) r

theorem hypMove_pattern (s a d r : Nat) (i : Fin (s + a + d)) :
    hypMove (Head := Head) s a d r (wkN r i) = .var (wkN r (blockMove s a d i)) :=
  extendSub_ge _ _ r i

theorem hypMove_hyp (s a d r : Nat) (k : Fin r) :
    hypMove (Head := Head) s a d r ⟨k.val, by omega⟩ =
      appSpine (.var ⟨k.val, by omega⟩) (prefixVars s a d r) := by
  show extendSub _ _ r ⟨k.val, _⟩ = _
  rw [extendSub_apply]
  dsimp only
  rw [dif_pos k.isLt, dif_pos (show r - 1 - k.val < r by omega)]
  exact congrArg (fun v => appSpine (.var v) (prefixVars s a d r))
    (Fin.ext (by show r - 1 - (r - 1 - k.val) = k.val; omega))

/-- The hypothesis substitution leaves the pattern variables alone. -/
theorem hypSub_pattern (f : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (fields : List (Field Head)) (i : Fin (s + fields.length + d)) :
    hypSub f e s d fields (wkN (recPositions fields).length i) = .var i :=
  extendSub_ge _ _ _ i

/-- The hypothesis substitution sends the hypothesis at index `k` to the
recursive call on its field. -/
theorem hypSub_hyp (f : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (fields : List (Field Head)) (k : Fin (recPositions fields).length) :
    hypSub f e s d fields ⟨k.val, by omega⟩ =
      recCall f e s fields.length d
        ((recPositions fields).getD ((recPositions fields).length - 1 - k.val) 0) := by
  show extendSub _ _ _ ⟨k.val, _⟩ = _
  rw [extendSub_apply]
  dsimp only
  rw [dif_pos k.isLt]

/-- The prefix variables past the hypotheses, under the hypothesis
substitution: the prefix variables of the pattern context. -/
theorem prefixVars_hypSub (f' : DeclName) (e' : (i : Nat) → Tm Head i) (s d : Nat)
    (fields : List (Field Head)) :
    (prefixVars s fields.length d (recPositions fields).length).map
        (Presentation.subst (hypSub f' e' 0 (s + d) fields)) =
      List.ofFn fun p : Fin s => .var ⟨d + (s - 1 - p.val), by omega⟩ := by
  unfold prefixVars
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext p
  show hypSub f' e' 0 (s + d) fields
    ⟨d + (recPositions fields).length + (s - 1 - p.val), by omega⟩ = _
  have moved : (⟨d + (recPositions fields).length + (s - 1 - p.val), by omega⟩ :
      Fin (0 + fields.length + (s + d) + (recPositions fields).length)) =
      wkN (recPositions fields).length ⟨d + (s - 1 - p.val), by omega⟩ :=
    Fin.ext (by show d + (recPositions fields).length + (s - 1 - p.val) =
      d + (s - 1 - p.val) + (recPositions fields).length; omega)
  rw [moved, hypSub_pattern]

/-! ## The prefix arguments on both sides

Under the match, the scrutinee-first hypothesis applied to the prefix
variables becomes `f'` at the field's argument and the authored prefix
arguments; the authored hypothesis becomes `f` at the prefix arguments and
the field's argument. Both prefix argument lists are the same list. -/

/-- `prefixSub` by values: the prefix argument at `i` is `σ` at `i` past the
scrutinee and the later arguments. -/
theorem prefixSub_apply {m : Nat} (s : Nat) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m) (i : Fin s),
      prefixSub s d σ i = σ ⟨i.val + 1 + d, by omega⟩
  | 0, _, _ => rfl
  | d + 1, σ, i => by
      show prefixSub s d (tailSub σ) i = _
      rw [prefixSub_apply s d (tailSub σ) i]
      exact congrArg σ (Fin.ext rfl)

/-- The arguments of a telescope of `s` entries, oldest first. -/
theorem telescopeArgs_ofEntries_ofFn (e : (i : Nat) → Tm Head i) {m : Nat} :
    ∀ (s : Nat) (τ : Sub Head s m),
      telescopeArgs (ofEntries e s) τ = List.ofFn fun p : Fin s => τ ⟨s - 1 - p.val, by omega⟩
  | 0, _ => by rw [List.ofFn_zero]; rfl
  | s + 1, τ => by
      show telescopeArgs (ofEntries e s) (tailSub τ) ++ [τ 0] = _
      rw [telescopeArgs_ofEntries_ofFn e s (tailSub τ), List.ofFn_succ_last]
      congr 1
      · apply congrArg List.ofFn
        funext p
        exact congrArg τ (Fin.ext (by show s - 1 - p.val + 1 = s + 1 - 1 - p.val; omega))
      · exact congrArg (fun x => [x]) (congrArg τ (Fin.ext (by show 0 = s + 1 - 1 - s; omega)))

/-- The authored prefix arguments, oldest first. -/
theorem prefixArgs_ofFn (e : (i : Nat) → Tm Head i) {m : Nat} (s d : Nat)
    (σ : Sub Head (s + 1 + d) m) :
    telescopeArgs (ofEntries e s) (prefixSub s d σ) =
      List.ofFn fun p : Fin s => σ ⟨s - 1 - p.val + 1 + d, by omega⟩ := by
  rw [telescopeArgs_ofEntries_ofFn]
  apply congrArg List.ofFn
  funext p
  exact prefixSub_apply s d σ ⟨s - 1 - p.val, by omega⟩

/-- The scrutinee-first prefix variables under the match: the authored prefix
arguments. -/
theorem prefixVars_matchSub {m : Nat} (s a d : Nat) (as : List (Tm Head m))
    (σ : Sub Head (s + 1 + d) m) :
    (List.ofFn fun p : Fin s =>
        (.var ⟨d + (s - 1 - p.val), by omega⟩ : Tm Head (0 + a + (s + d)))).map
        (Presentation.subst (matchSub 0 a as (s + d) (fun j => σ (teleMoveBack s d j)))) =
      List.ofFn fun p : Fin s => σ ⟨s - 1 - p.val + 1 + d, by omega⟩ := by
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext p
  show matchSub 0 a as (s + d) (fun j => σ (teleMoveBack s d j)) ⟨d + (s - 1 - p.val), _⟩ = _
  rw [matchSub_apply]
  dsimp only
  rw [dif_pos (show d + (s - 1 - p.val) < s + d by omega)]
  exact congrArg σ (Fin.ext (by
    rw [teleMoveBack_val]; dsimp only
    rw [if_neg (show ¬ d + (s - 1 - p.val) < d by omega),
      if_pos (show d + (s - 1 - p.val) < d + s by omega)]
    omega))

/-! ## The two instantiations of the authored body, by index

The scrutinee-first rule instantiates `subst hypMove body` by the
scrutinee-first hypotheses and match; the authored rule instantiates `body`
by the authored ones. At a pattern variable both give the authored match. At
a hypothesis, the scrutinee-first side gives `f'` at the field's argument and
the prefix arguments, the authored side `f` at the prefix arguments and the
field's argument. -/

theorem recPosition_lt (fields : List (Field Head)) (k : Fin (recPositions fields).length) :
    (recPositions fields).getD ((recPositions fields).length - 1 - k.val) 0 < fields.length := by
  have hj : (recPositions fields).length - 1 - k.val < (recPositions fields).length := by
    have := k.isLt
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact (recPositions_spec fields _ hj).1

section Instantiations

variable {m : Nat} (f f' : DeclName) (e e' : (i : Nat) → Tm Head i) (s d : Nat)
  (fields : List (Field Head)) (as : List (Tm Head m)) (σ : Sub Head (s + 1 + d) m)

theorem firstInst_pattern (i : Fin (s + fields.length + d)) :
    Presentation.subst (matchSub 0 fields.length as (s + d) (fun j => σ (teleMoveBack s d j)))
      (Presentation.subst (hypSub f' e' 0 (s + d) fields)
        (hypMove s fields.length d (recPositions fields).length
          (wkN (recPositions fields).length i))) =
      matchSub s fields.length as d σ i := by
  rw [hypMove_pattern]
  show Presentation.subst _
    (hypSub f' e' 0 (s + d) fields (wkN _ (blockMove s fields.length d i))) = _
  rw [hypSub_pattern]
  exact matchSub_blockMove s fields.length d as σ i

theorem authoredInst_pattern (i : Fin (s + fields.length + d)) :
    Presentation.subst (matchSub s fields.length as d σ)
      (hypSub f e s d fields (wkN (recPositions fields).length i)) =
      matchSub s fields.length as d σ i := by
  rw [hypSub_pattern]
  rfl

theorem firstInst_hyp (k : Fin (recPositions fields).length) :
    Presentation.subst (matchSub 0 fields.length as (s + d) (fun j => σ (teleMoveBack s d j)))
      (Presentation.subst (hypSub f' e' 0 (s + d) fields)
        (hypMove s fields.length d (recPositions fields).length ⟨k.val, by omega⟩)) =
      appSpine (.app (.const f')
          (as.getD ((recPositions fields).getD ((recPositions fields).length - 1 - k.val) 0)
            defaultTm))
        (List.ofFn fun p : Fin s => σ ⟨s - 1 - p.val + 1 + d, by omega⟩) := by
  rw [hypMove_hyp, subst_appSpine, prefixVars_hypSub]
  show Presentation.subst _ (appSpine (hypSub f' e' 0 (s + d) fields ⟨k.val, _⟩) _) = _
  rw [hypSub_hyp, subst_appSpine, prefixVars_matchSub,
    subst_recCall f' e' as (fun j => σ (teleMoveBack s d j)) (recPosition_lt fields k)]
  rfl

theorem authoredInst_hyp (k : Fin (recPositions fields).length) :
    Presentation.subst (matchSub s fields.length as d σ)
      (hypSub f e s d fields ⟨k.val, by omega⟩) =
      appSpine (.const f)
        ((List.ofFn fun p : Fin s => σ ⟨s - 1 - p.val + 1 + d, by omega⟩) ++
          [as.getD ((recPositions fields).getD ((recPositions fields).length - 1 - k.val) 0)
            defaultTm]) := by
  rw [hypSub_hyp, subst_recCall f e as σ (recPosition_lt fields k), applyClosed_eq_appSpine,
    telescopeArgs_ofEntries_succ, tailSub_consSub, consSub_zero, prefixArgs_ofFn]

end Instantiations

/-! ## The result type and the lifted substitutions under the move -/

/-- The scrutinee replaced and the arguments moved, on the moved result
type: the authored instantiation of `C`. -/
theorem subst_replaceScrut_teleMove {m : Nat} (s d : Nat) (x : Tm Head m)
    (σ : Sub Head (s + 1 + d) m) (C : Tm Head (s + 1 + d)) :
    Presentation.subst (replaceScrut 0 x (s + d) (fun j => σ (teleMoveBack s d j)))
        (Presentation.rename (teleMove s d) C) =
      Presentation.subst (replaceScrut s x d σ) C := by
  rw [subst_rename, ← replaceScrut_teleMoveBack]
  congr 1
  funext i
  show replaceScrut s x d σ (teleMoveBack s d (teleMove s d i)) = _
  rw [teleMoveBack_teleMove]

/-- `liftSubN` by values: the last `j` indices are the bound variables, the
others the substitution weakened past them. -/
theorem liftSubN_apply {n m : Nat} (τ : Sub Head n m) :
    ∀ (j : Nat) (i : Fin (n + j)),
      liftSubN τ j i =
        if h : i.val < j then .var ⟨i.val, by omega⟩
        else Presentation.rename (wkN j) (τ ⟨i.val - j, by have := i.isLt; omega⟩)
  | 0, i => by
      show τ i = _
      rw [dif_neg (Nat.not_lt_zero _), wkN_zero, rename_id]
      exact congrArg τ (Fin.ext rfl)
  | j + 1, ⟨0, _⟩ => by
      show Tm.var 0 = _
      dsimp only
      rw [dif_pos (show 0 < j + 1 by omega)]
      rfl
  | j + 1, ⟨k + 1, hk⟩ => by
      show Presentation.rename wk (liftSubN τ j ⟨k, by omega⟩) = _
      rw [liftSubN_apply τ j ⟨k, by omega⟩]
      dsimp only
      by_cases h : k < j
      · rw [dif_pos h, dif_pos (show k + 1 < j + 1 by omega)]
        rfl
      · rw [dif_neg h, dif_neg (show ¬ k + 1 < j + 1 by omega), rename_comp]
        exact congrArg (fun v => Presentation.rename (wkN (j + 1)) (τ v))
          (Fin.ext (by show k - j = k + 1 - (j + 1); omega))

/-! ## Splitting `piClosed` at a prefix

The scrutinee-first telescope is indexed `0 + 1 + (s + d)`; reading it as
`(0 + 1 + s) + d`, to apply a hypothesis to the prefix and then compare over
the later entries, is `Nat.add_assoc`. The recast between the two spellings
is the index-preserving renaming, so it stays a renaming and commutes with
everything renamings commute with. -/

/-- The index-preserving renaming between two spellings of one length. -/
def recast {n n' : Nat} (h : n = n') : Ren n n' := fun i => ⟨i.val, by have := i.isLt; omega⟩

theorem recast_rfl {n : Nat} : (recast (rfl : n = n)) = idRen :=
  funext fun _ => Fin.ext rfl

theorem liftRen_recast {n n' : Nat} (h : n = n') :
    liftRen (recast h) = recast (congrArg (· + 1) h) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- `piClosed` over `s + d` entries is `piClosed` over the first `s` of
`piClosed` over the last `d`, on the recast body. -/
theorem piClosed_add {n : Nat} (G : Nat → Tm Head 0) (s : Nat) :
    ∀ (d : Nat) (X : Tm Head (n + (s + d))),
      piClosed G (s + d) X =
        piClosed G s (piClosed (fun l => G (s + l)) d
          (Presentation.rename (recast (Nat.add_assoc n s d).symm) X))
  | 0, X => by
      show piClosed G s X = piClosed G s (Presentation.rename (recast _) X)
      rw [show recast (Nat.add_assoc n s 0).symm = idRen from funext fun _ => Fin.ext rfl,
        rename_id]
  | d + 1, X => by
      show piClosed G (s + d) (.pi (liftClosed (G (s + d))) X) = _
      rw [piClosed_add G s d (.pi (liftClosed (G (s + d))) X)]
      show piClosed G s (piClosed (fun l => G (s + l)) d
          (.pi (Presentation.rename (recast _) (liftClosed (G (s + d))))
            (Presentation.rename (liftRen (recast _)) X))) =
        piClosed G s (piClosed (fun l => G (s + l)) d
          (.pi (liftClosed (G (s + d))) (Presentation.rename (recast _) X)))
      rw [rename_liftClosed, liftRen_recast]

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
