import Mettapedia.OSLF.Syntax.DeclaredBindingActivation
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommutativeMatching

/-!
# Declared binders agree with `match`

A library of the Prime draft declares which argument positions of its forms hold patterns:

    (scope:binder (transform value source body))
    (scope:source transform (read value pattern))

say that in `(transform R SOURCES TEMPLATE)` the location `R` is read where the form stands, the
sources hold patterns, and the template sees the names those patterns bind; inside the sources,
`(read LOC PATTERN)` has a location and a pattern. Under the lexical-fresh rule a name written at a
pattern position is a new name of the form, as a name in a pattern of `match` is. So, with
`&t = {(holds a 1), (holds b 2)}`,

    (let $f 1 (transform &t (every (read (holds $j $f))) ($j $f)))

returns both rows, as `(let $f 1 (match &t (holds $j $f) ($j $f)))` does. The outer `$f` reaches the
pattern only through a crossing set written on the form, `(transform …){$f}`.

## Words

* A **slot** is a name together with the place that made it, its *owner* (a position; `[]` is the
  top). `let $f 1` at the top makes the slot `([], f)`; a transform at position `[0]` makes
  `([0], f)` for the `$f` of its pattern. Two slots with one spelling are two names.
* A **store** (`Subst (Slot X) T`) gives values to slots: after `let $f 1`, `([], f) ↦ 1`.
* A **role** says what an argument position of a declared form is (`Role`): `value` is read where
  the form stands; `pattern` binds the names written there; `sourceValue`, a value position of a
  source form such as the location of `(read LOC PATTERN)`, and `body` are read with the form's
  names in force and bind nothing.
* **Reading** a declared form (`readArg`) turns its spellings into slots. The names its patterns
  bind (`bound`, less a crossing set) become slots of the form's owner everywhere except at its
  value positions; every other name is the slot the scope around gives it. This is the rule of the
  draft's reader (`prime_semantics.c`, "Declared binding forms"): a value argument is read in the
  scope around, with the form's slots set aside even when it comes after a pattern.
* An **answer** of matching is a store: the store matching started from, with what the pattern
  bound added. `match` on a space (`matchSpace`) gives, for each atom of the space, each answer of
  the matcher; patterns joined on the names they share, as the sources of one transform are, give
  `joinSpace`.

## Main results

* `cmatch_renameSlots`: matching a pattern whose names are slots of the owner `o` gives exactly
  the answers of the pattern as written, matched from what the store says about `o`'s slots, each
  put back at `o`, with every other slot of the store unchanged. The matcher is the transform
  kernel's (`Commutative.cmatch`: sound, complete and minimal for every declaration of commuting
  symbols).
* `readArg_pattern`: in every declared form, a pattern position whose names avoid the crossing set
  is read with each name a slot of the form's owner.
* `declared_patterns_match` (headline): from a store that binds no slot of the form yet, the form's
  patterns give exactly the answers `match` gives on the patterns as written, from no bindings,
  renamed into the form's slots and joined to the store. No outer name refines a pattern, and every
  outer slot keeps its value (`declared_answers_keep_outer`).
* `declared_agrees_with_match`: a declared form whose one pattern is `p` and the form
  `(match value pattern body)` on `p` give the same answers up to renaming their owners.
* `kernel_reads_are_match`: the rows the transform kernel computes for read sources
  (`Sources.rows`) are those `match` answers, kept when the template can be instantiated;
  `declared_transform_rows` composes it with the headline.
* `lexicalFresh_let_reads_as_declared`: a cross-check with the existing lexical-fresh elaborator
  (`TemplateScope.elabLF`). It reads the pattern and the body of a `let` exactly as the declared
  reading of a form with that one pattern does, and its value where the `let` stands.

## Controls (`Controls`)

After `let $f 1`, on `&t = {(holds a 1), (holds b 2)}`:
* the pattern `(holds $j $f)` at a declared pattern position gives the two answers `(a, 1)` and
  `(b, 2)`, and the outer `$f` still holds `1` in each (`declared_two_answers`);
* the same pattern at a position nobody declared (an ordinary call, `(rows-of (holds $j $f))`) is
  read where the form stands; the outer `$f` refines it, and only `(a, 1)` remains
  (`undeclared_one_answer`);
* with the crossing set `{$f}` the outer `$f` is shared on purpose: again only `(a, 1)`
  (`crossing_one_answer`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.DeclaredBinders

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative
open Mettapedia.GSLT.LanguageDef.TemplateScope (Owner REnv)

/-- A slot: an owner and a spelling (`TemplateScope.Slot`). -/
local notation "Slot" => Mettapedia.GSLT.LanguageDef.TemplateScope.Slot

universe uF uX uV uW uT uO uP

/-! ## Renaming the names of a pattern -/

section Rename

variable {F : Type uF} {V : Type uV} {W : Type uW}

/-- Rename every name of a pattern. -/
def renamePat (g : V → W) : Pat V F → Pat W F
  | .var v => .var (g v)
  | .leaf a => .leaf a
  | .node f p q => .node f (renamePat g p) (renamePat g q)

/-- The names written in a pattern, left to right, with repeats. -/
def patNames : Pat V F → List V
  | .var v => [v]
  | .leaf _ => []
  | .node _ p q => patNames p ++ patNames q

/-- Renamings that agree on the names of a pattern rename it alike. -/
theorem renamePat_congr {g g' : V → W} :
    ∀ p : Pat V F, (∀ v ∈ patNames p, g v = g' v) → renamePat g p = renamePat g' p
  | .var v, same => by simp [renamePat, same v (by simp [patNames])]
  | .leaf _, _ => rfl
  | .node f p q, same => by
      simp only [renamePat]
      rw [renamePat_congr p fun v h => same v (by simp [patNames, h]),
        renamePat_congr q fun v h => same v (by simp [patNames, h])]

theorem vars_renamePat [DecidableEq F] [DecidableEq V] [DecidableEq W] (g : V → W) :
    ∀ p : Pat V F, (renamePat g p).vars = p.vars.image g
  | .var v => by simp [renamePat, Pat.vars]
  | .leaf _ => by simp [renamePat, Pat.vars]
  | .node f p q => by
      simp [renamePat, Pat.vars, vars_renamePat g p, vars_renamePat g q, Finset.image_union]

end Rename

/-! ## The slots of one owner in a store -/

section Slots

variable {X : Type uX} {T : Type uT}

/-- What a store gives the slots of the owner `o`, read by their spellings. -/
def slotsOf (σ : Subst (Slot X) T) (o : Owner) : Subst X T := fun y => σ (o, y)

/-- The store `σ` with the slots of the owner `o` given by `τ`; every other slot as in `σ`. -/
def withSlots (σ : Subst (Slot X) T) (o : Owner) (τ : Subst X T) : Subst (Slot X) T :=
  fun s => if s.1 = o then τ s.2 else σ s

theorem slotsOf_apply (σ : Subst (Slot X) T) (o : Owner) (y : X) : slotsOf σ o y = σ (o, y) := rfl

@[simp] theorem withSlots_self (σ : Subst (Slot X) T) (o : Owner) (τ : Subst X T) (y : X) :
    withSlots σ o τ (o, y) = τ y := by
  simp [withSlots]

theorem withSlots_of_ne (σ : Subst (Slot X) T) (o : Owner) (τ : Subst X T) {s : Slot X}
    (other : s.1 ≠ o) : withSlots σ o τ s = σ s := by
  simp [withSlots, other]

@[simp] theorem withSlots_slotsOf (σ : Subst (Slot X) T) (o : Owner) :
    withSlots σ o (slotsOf σ o) = σ := by
  funext s
  obtain ⟨o', y⟩ := s
  by_cases h : o' = o
  · subst h
    simp [withSlots, slotsOf]
  · simp [withSlots, h]

@[simp] theorem slotsOf_withSlots (σ : Subst (Slot X) T) (o : Owner) (τ : Subst X T) :
    slotsOf (withSlots σ o τ) o = τ := by
  funext y
  simp [slotsOf, withSlots]

@[simp] theorem withSlots_withSlots (σ : Subst (Slot X) T) (o : Owner) (τ τ' : Subst X T) :
    withSlots (withSlots σ o τ) o τ' = withSlots σ o τ' := by
  funext s
  by_cases h : s.1 = o <;> simp [withSlots, h]

/-- `withSlots_withSlots`, before the last argument is given. -/
@[simp] theorem withSlots_withSlots' (σ : Subst (Slot X) T) (o : Owner) (τ : Subst X T) :
    withSlots (withSlots σ o τ) o = withSlots σ o := by
  funext τ'
  exact withSlots_withSlots σ o τ τ'

theorem withSlots_update [DecidableEq X] (σ : Subst (Slot X) T) (o : Owner) (τ : Subst X T)
    (y : X) (t : Option T) :
    withSlots σ o (Function.update τ y t) = Function.update (withSlots σ o τ) (o, y) t := by
  funext s
  obtain ⟨o', y'⟩ := s
  by_cases h : o' = o
  · subst h
    by_cases hy : y' = y
    · subst hy
      simp
    · have ne : ((o', y') : Slot X) ≠ (o', y) := by simp [hy]
      rw [Function.update_of_ne ne]
      simp [withSlots, Function.update_of_ne hy]
  · have ne : ((o', y') : Slot X) ≠ (o, y) := by simp [h]
    rw [Function.update_of_ne ne]
    simp [withSlots, h]

/-- A store that binds no slot of `o` says nothing about `o`'s slots. -/
theorem slotsOf_eq_none {σ : Subst (Slot X) T} {o : Owner} (fresh : ∀ y, σ (o, y) = none) :
    slotsOf σ o = fun _ => none :=
  funext fresh

end Slots

/-! ## Matching is blind to the owner of the slots it binds -/

section Matching

variable {F : Type uF} [DecidableEq F] {X : Type uX} [DecidableEq X]

/-- **Raw matching under renaming into slots.** -/
theorem rawMatch_renameSlots (comm : F → Bool) (o : Owner) :
    ∀ (p : Pat X F) (σ : Subst (Slot X) (Tm F)) (t : Tm F),
      rawMatch comm (renamePat (Prod.mk o) p) σ t =
        (rawMatch comm p (slotsOf σ o) t).map (withSlots σ o)
  | .var v, σ, t => by
      simp only [renamePat, rawMatch, slotsOf_apply]
      cases σ (o, v) with
      | none => simp [withSlots_update]
      | some u => by_cases hc : ceq comm u t = true <;> simp [hc]
  | .leaf a, σ, t => by
      simp only [renamePat, rawMatch]
      split_ifs <;> simp
  | .node f p q, σ, .node g l r => by
      simp only [renamePat, rawMatch]
      split_ifs <;>
        simp [rawMatch_renameSlots comm o p, rawMatch_renameSlots comm o q, List.flatMap_map,
          List.map_flatMap]
  | .node f p q, σ, .leaf a => by
      simp [renamePat, rawMatch]

/-- Pairwise filtering by two relations that agree. -/
theorem pwFilter_congr {α : Type*} {R R' : α → α → Prop} [DecidableRel R] [DecidableRel R']
    (same : ∀ a b, R a b ↔ R' a b) (l : List α) : l.pwFilter R = l.pwFilter R' := by
  obtain rfl : R = R' := funext₂ fun a b => propext (same a b)
  congr

theorem sameOn_renameSlots (comm : F → Bool) (o : Owner) (σ : Subst (Slot X) (Tm F))
    (p : Pat X F) (τ τ' : Subst X (Tm F)) :
    SameOn comm (renamePat (Prod.mk o) p).vars (withSlots σ o τ) (withSlots σ o τ') ↔
      SameOn comm p.vars τ τ' := by
  simp [SameOn, vars_renamePat]

/-- **The kernel's matcher under renaming into slots.** Matching a pattern whose names are slots
of the owner `o` gives the answers of the pattern as written, from what the store says about `o`'s
slots, each put back at `o`; every other slot keeps its value from the store. -/
theorem cmatch_renameSlots (comm : F → Bool) (o : Owner) (p : Pat X F)
    (σ : Subst (Slot X) (Tm F)) (t : Tm F) :
    cmatch comm (renamePat (Prod.mk o) p) σ t =
      (cmatch comm p (slotsOf σ o) t).map (withSlots σ o) := by
  simp only [cmatch]
  rw [rawMatch_renameSlots, List.pwFilter_map]
  exact congrArg _ (pwFilter_congr (fun τ τ' => not_congr (sameOn_renameSlots comm o σ p τ τ')) _)

end Matching

/-! ## `match` on a space, and patterns joined on their shared names -/

section Spaces

variable {V : Type uV} {T : Type uT} {P : Type uP}

/-- **`match` on a space**: for each atom of the space, each answer of the matcher. -/
def matchSpace (m : Matcher V T P) (space : Multiset T) (p : P) (σ : Subst V T) :
    Multiset (Subst V T) :=
  space.bind fun t => (m p σ t : Multiset (Subst V T))

/-- Patterns matched in turn against a space, each from the answers of the one before: the
sources of one transform, joined on the names they share. -/
def joinSpace (m : Matcher V T P) (space : Multiset T) : List P → Subst V T → Multiset (Subst V T)
  | [], σ => {σ}
  | p :: ps, σ => (matchSpace m space p σ).bind (joinSpace m space ps)

theorem joinSpace_singleton (m : Matcher V T P) (space : Multiset T) (p : P) (σ : Subst V T) :
    joinSpace m space [p] σ = matchSpace m space p σ := by
  simp only [joinSpace]
  exact (Multiset.bind_singleton (s := matchSpace m space p σ) id).trans (Multiset.map_id _)

end Spaces

section SpaceRenaming

variable {F : Type uF} [DecidableEq F] {X : Type uX} [DecidableEq X]

theorem matchSpace_renameSlots (comm : F → Bool) (o : Owner) (space : Multiset (Tm F))
    (p : Pat X F) (σ : Subst (Slot X) (Tm F)) :
    matchSpace (cmatch comm) space (renamePat (Prod.mk o) p) σ =
      (matchSpace (cmatch comm) space p (slotsOf σ o)).map (withSlots σ o) := by
  simp only [matchSpace, cmatch_renameSlots, Multiset.map_bind, ← Multiset.map_coe]

theorem joinSpace_renameSlots (comm : F → Bool) (o : Owner) (space : Multiset (Tm F)) :
    ∀ (ps : List (Pat X F)) (σ : Subst (Slot X) (Tm F)),
      joinSpace (cmatch comm) space (ps.map (renamePat (Prod.mk o))) σ =
        (joinSpace (cmatch comm) space ps (slotsOf σ o)).map (withSlots σ o)
  | [], σ => by simp [joinSpace]
  | p :: ps, σ => by
      simp only [List.map_cons, joinSpace, matchSpace_renameSlots, Multiset.bind_map,
        Multiset.map_bind, joinSpace_renameSlots comm o space ps, slotsOf_withSlots,
        withSlots_withSlots]

end SpaceRenaming

/-! ## Declared forms and how the reader reads them -/

/-- The role of an argument position of a declared form, as `scope:binder` and `scope:source`
declarations give it. -/
inductive Role where
  /-- Read where the form stands: `R` in `(transform R SOURCES TEMPLATE)`, the space of `match`. -/
  | value
  /-- A pattern: the names written there are the form's own. -/
  | pattern
  /-- A value position of a source form, such as `LOC` in `(read LOC PATTERN)`: read with the
  form's names in force; it binds nothing. -/
  | sourceValue
  /-- Read with the form's names in force: the template of a transform, the body of `match`. -/
  | body
  deriving DecidableEq, Repr

section Forms

variable {F : Type uF} {X : Type uX} [DecidableEq X]

/-- A declared form as written: its arguments in order, each with the role its declaration gives
it. A source form at a source position contributes its own positions, in order: the source
`(read LOC PATTERN)` contributes `(.sourceValue, LOC)` and `(.pattern, PATTERN)`. -/
abbrev Form (X : Type uX) (F : Type uF) := List (Role × Pat X F)

/-- The patterns of a form, in order. -/
def patterns (args : Form X F) : List (Pat X F) :=
  args.filterMap fun a => if a.1 = .pattern then some a.2 else none

/-- **The names a form binds**: those written at its pattern positions, less the crossing set `cr`
written on the form. -/
def bound (cr : List X) (args : Form X F) : List X :=
  ((patterns args).flatMap patNames).filter fun y => y ∉ cr

/-- Read a pattern in a scope: each spelling becomes the slot the scope gives it. -/
def resolvePat (env : REnv X) (p : Pat X F) : Pat (Slot X) F :=
  renamePat (fun y => (env y, y)) p

/-- The scope inside a form at the owner `o`: the names it binds are its own slots. -/
def inner (o : Owner) (cr : List X) (env : REnv X) (args : Form X F) : REnv X :=
  env.update (bound cr args) o

theorem inner_apply (o : Owner) (cr : List X) (env : REnv X) (args : Form X F) (y : X) :
    inner o cr env args y = if y ∈ bound cr args then o else env y := rfl

/-- **Reading one argument of a declared form** at the owner `o`, with the crossing set `cr`, in
the scope `env` around it: a value position in the scope around, every other position in the
form's scope. -/
def readArg (o : Owner) (cr : List X) (env : REnv X) (args : Form X F) :
    Role × Pat X F → Pat (Slot X) F
  | (.value, t) => resolvePat env t
  | (_, t) => resolvePat (inner o cr env args) t

/-- The patterns of a form, as the reader reads them. -/
def readPatterns (o : Owner) (cr : List X) (env : REnv X) (args : Form X F) :
    List (Pat (Slot X) F) :=
  args.filterMap fun a => if a.1 = .pattern then some (readArg o cr env args a) else none

omit [DecidableEq X] in
theorem mem_patterns {args : Form X F} {p : Pat X F} :
    p ∈ patterns args ↔ (Role.pattern, p) ∈ args := by
  simp only [patterns, List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq]
  constructor
  · rintro ⟨⟨r, t⟩, member, rfl, rfl⟩
    exact member
  · intro member
    exact ⟨_, member, rfl, rfl⟩

theorem mem_bound {cr : List X} {args : Form X F} {p : Pat X F} (hp : (Role.pattern, p) ∈ args)
    {y : X} (hy : y ∈ patNames p) (hcr : y ∉ cr) : y ∈ bound cr args := by
  simp only [bound, List.mem_filter, List.mem_flatMap, decide_eq_true_eq]
  exact ⟨⟨p, mem_patterns.mpr hp, hy⟩, hcr⟩

/-- **A pattern position is read with the form's own slots.** In every declared form, a pattern
whose names avoid the crossing set is read with each of its names a slot of the form's owner. -/
theorem readArg_pattern (o : Owner) (cr : List X) (env : REnv X) {args : Form X F} {p : Pat X F}
    (hp : (Role.pattern, p) ∈ args) (apart : ∀ y ∈ patNames p, y ∉ cr) :
    readArg o cr env args (.pattern, p) = renamePat (Prod.mk o) p := by
  show resolvePat (inner o cr env args) p = _
  apply renamePat_congr
  intro y hy
  simp [inner_apply, mem_bound hp hy (apart y hy)]

/-- **A value position is read where the form stands**, whatever the form binds. -/
theorem readArg_value (o : Owner) (cr : List X) (env : REnv X) (args : Form X F) (t : Pat X F) :
    readArg o cr env args (.value, t) = resolvePat env t := rfl

/-- Without a crossing set, the form's patterns are read as their names made slots of `o`. -/
theorem readPatterns_eq (o : Owner) (env : REnv X) (args : Form X F) :
    readPatterns o [] env args = (patterns args).map (renamePat (Prod.mk o)) := by
  suffices key : ∀ l : Form X F, (∀ a ∈ l, a ∈ args) →
      l.filterMap (fun a => if a.1 = .pattern then some (readArg o [] env args a) else none) =
        (l.filterMap fun a => if a.1 = .pattern then some a.2 else none).map
          (renamePat (Prod.mk o)) from
    key args fun _ h => h
  intro l inArgs
  induction l with
  | nil => rfl
  | cons a l ih =>
      have rest := ih fun b hb => inArgs b (List.mem_cons_of_mem _ hb)
      obtain ⟨r, t⟩ := a
      by_cases hr : r = .pattern
      · subst hr
        have pat := readArg_pattern o [] env (inArgs _ List.mem_cons_self) (by simp)
        simp [pat, rest]
      · simp [hr, rest]

end Forms

/-! ## The headline: declared patterns give `match`'s answers -/

section Headline

variable {F : Type uF} [DecidableEq F] {X : Type uX} [DecidableEq X]

/-- **Declared binders agree with `match`.** From a store that binds no slot of the form's owner
yet, the patterns of a declared form, read without a crossing set, give exactly the answers that
`match` gives on the patterns as written, from no bindings, renamed into the form's slots and
joined to the store. -/
theorem declared_patterns_match (comm : F → Bool) (o : Owner) (env : REnv X) (args : Form X F)
    (σ : Subst (Slot X) (Tm F)) (fresh : ∀ y, σ (o, y) = none) (space : Multiset (Tm F)) :
    joinSpace (cmatch comm) space (readPatterns o [] env args) σ =
      (joinSpace (cmatch comm) space (patterns args) fun _ => none).map (withSlots σ o) := by
  rw [readPatterns_eq, joinSpace_renameSlots, slotsOf_eq_none fresh]

/-- **No capture, either way.** Every answer keeps each slot of the store outside the form as it
was, and its slots of the form are an answer of `match` on the patterns as written. -/
theorem declared_answers_keep_outer (comm : F → Bool) (o : Owner) (env : REnv X)
    (args : Form X F) (σ : Subst (Slot X) (Tm F)) (fresh : ∀ y, σ (o, y) = none)
    (space : Multiset (Tm F)) {τ : Subst (Slot X) (Tm F)}
    (answer : τ ∈ joinSpace (cmatch comm) space (readPatterns o [] env args) σ) :
    (∀ s : Slot X, s.1 ≠ o → τ s = σ s) ∧
      slotsOf τ o ∈ joinSpace (cmatch comm) space (patterns args) fun _ => none := by
  rw [declared_patterns_match comm o env args σ fresh space, Multiset.mem_map] at answer
  obtain ⟨τ₀, member, rfl⟩ := answer
  exact ⟨fun s other => withSlots_of_ne σ o τ₀ other, by simpa using member⟩

/-- `(match SPACE PATTERN BODY)`, read as the declared form `(match value pattern body)`. -/
def matchForm (space p body : Pat X F) : Form X F :=
  [(.value, space), (.pattern, p), (.body, body)]

omit [DecidableEq F] [DecidableEq X] in
theorem patterns_matchForm (space p body : Pat X F) : patterns (matchForm space p body) = [p] := by
  simp [matchForm, patterns]

/-- **A declared form and `match` give the same answers up to renaming.** A declared form whose
one pattern is `p`, at the owner `o`, and `match` on `p`, at the owner `o'`, both from a store
that binds no slot of `o` or `o'`: moving each answer of `match` from `o'` to `o` gives the answers
of the declared form. -/
theorem declared_agrees_with_match (comm : F → Bool) (o o' : Owner) (env : REnv X)
    (args : Form X F) (p space body : Pat X F) (one : patterns args = [p])
    (σ : Subst (Slot X) (Tm F)) (fresh : ∀ y, σ (o, y) = none) (fresh' : ∀ y, σ (o', y) = none)
    (atoms : Multiset (Tm F)) :
    joinSpace (cmatch comm) atoms (readPatterns o [] env args) σ =
      (joinSpace (cmatch comm) atoms (readPatterns o' [] env (matchForm space p body)) σ).map
        fun τ => withSlots σ o (slotsOf τ o') := by
  rw [declared_patterns_match comm o env args σ fresh, declared_patterns_match comm o' env _ σ
    fresh', Multiset.map_map, one, patterns_matchForm]
  apply Multiset.map_congr rfl
  intro τ _
  simp

end Headline

/-! ## The transform kernel's read sources are `match` -/

section Kernel

variable {O : Type uO} [DecidableEq O] {V : Type uV} {T : Type uT} {P : Type uP}

/-- Read sources `(read p₁) … (read pₙ)`, joined. -/
def reads : List P → SourceList V T P
  | [] => .done
  | p :: ps => .cons (.read p) (reads ps)

/-- **The kernel's rows of read sources are `match`'s answers.** The substitutions of the rows the
transform kernel computes for read sources are the answers of the patterns joined on the space of
the store's atoms, kept when the template can be instantiated. -/
theorem kernel_reads_are_match (L : TermLayer V T P) (m : Matcher V T P) (label : O → T)
    (S : Finset O) (template : List P) :
    ∀ (ps : List P) (σ : Subst V T),
      (rows L m label S template (reads ps) σ).map Prod.fst =
        (joinSpace m (S.val.map label) ps σ).filter
          fun τ => (instTemplate L τ template).isSome = true
  | [], σ => by
      simp only [reads, rows, joinSpace]
      cases h : instTemplate L σ template <;> simp [h, Multiset.filter_singleton]
  | p :: ps, σ => by
      simp only [reads, rows, joinSpace, matchSpace, stepRows, Multiset.map_bind, Multiset.map_map,
        Function.comp_def, Multiset.bind_map, Multiset.bind_assoc, Multiset.filter_bind,
        kernel_reads_are_match L m label S template ps]

end Kernel

section DeclaredTransform

variable {O : Type uO} [DecidableEq O] {F : Type uF} [DecidableEq F] {X : Type uX} [DecidableEq X]

/-- **A declared transform's rows are `match`'s answers.** The kernel's rows for the read sources
of a declared transform, read without a crossing set from a store that binds none of its slots,
are the answers of `match` on its patterns as written, from no bindings, renamed into its slots
and joined to the store, kept when the template can be instantiated. -/
theorem declared_transform_rows (comm : F → Bool) (label : O → Tm F) (S : Finset O)
    (template : List (Pat (Slot X) F)) (o : Owner) (env : REnv X) (args : Form X F)
    (σ : Subst (Slot X) (Tm F)) (fresh : ∀ y, σ (o, y) = none) :
    (rows (termLayer comm) (cmatch comm) label S template (reads (readPatterns o [] env args))
        σ).map Prod.fst =
      ((joinSpace (cmatch comm) (S.val.map label) (patterns args) fun _ => none).map
          (withSlots σ o)).filter
        fun τ => (instTemplate (termLayer comm) τ template).isSome = true := by
  rw [kernel_reads_are_match, declared_patterns_match comm o env args σ fresh]

end DeclaredTransform

/-! ## Cross-check with the existing lexical-fresh elaborator -/

section LexicalFresh

open Mettapedia.GSLT.LanguageDef.TemplateScope (Src elabLF lfIntro letParam crossIn)

variable {F : Type uF} {X : Type uX} [DecidableEq X]

/-- A pattern as authored text of the scope-policy model. -/
def toSrc : Pat X F → Src F X
  | .var y => .sv y
  | .leaf a => .sym a
  | .node f l r => .app (.app (.sym f) (toSrc l)) (toSrc r)

/-- A read pattern as a scope-bearing term of the scope-policy model. -/
def toTm : Pat (Slot X) F → Mettapedia.GSLT.LanguageDef.TemplateScope.Tm F (Slot X)
  | .var s => .var (.src s)
  | .leaf a => .sym a
  | .node f l r => .app (.app (.sym f) (toTm l)) (toTm r)

omit [DecidableEq X] in
theorem patNames_toSrc : ∀ p : Pat X F, Src.patNames (toSrc p) = patNames p
  | .var _ => rfl
  | .leaf _ => rfl
  | .node f l r => by
      simp [toSrc, Src.patNames, patNames, patNames_toSrc l, patNames_toSrc r]

/-- The lexical-fresh elaborator reads a pattern as `resolvePat` does. -/
theorem elabLF_toSrc (R : Owner) (env : REnv X) (cr : List X) :
    ∀ (pos : Owner) (p : Pat X F), elabLF R env cr pos (toSrc p) = toTm (resolvePat env p)
  | _, .var _ => rfl
  | _, .leaf _ => rfl
  | pos, .node f l r => by
      simp only [toSrc, elabLF, resolvePat, renamePat, toTm]
      rw [elabLF_toSrc R env cr _ l, elabLF_toSrc R env cr _ r]
      rfl

/-- `elabLF` makes slots for the names a declared form with the one pattern `p` binds. -/
theorem update_lfIntro_eq_inner (o : Owner) (cr : List X) (env : REnv X) (args : Form X F)
    (p : Pat X F) (one : patterns args = [p]) :
    env.update (lfIntro none (toSrc p) cr) o = inner o cr env args := by
  funext y
  simp [Mettapedia.GSLT.LanguageDef.TemplateScope.REnv.update, inner_apply, lfIntro,
    Mettapedia.GSLT.LanguageDef.TemplateScope.crossOwn, bound, one, patNames_toSrc]

/-- **The lexical-fresh `let` is the declared reading.** The existing elaborator `elabLF` reads a
`let` whose pattern binds a name as an activation whose pattern is the declared reading of `p`, at
the owner `pos ++ [2]` of the `let`'s body, whose body is read in the declared form's scope, and
whose value is read where the `let` stands. Here `args` is any declared form whose one pattern is
`p`, such as `(let pattern value body)`. -/
theorem lexicalFresh_let_reads_as_declared (R : Owner) (env : REnv X) (cr : List X) (pos : Owner)
    (p : Pat X F) (w b : Src F X) (args : Form X F) (one : patterns args = [p]) (y₀ : X)
    (ys : List X) (introduced : lfIntro none (toSrc p) cr = y₀ :: ys) :
    elabLF R env cr pos (.letS (toSrc p) w b none) =
      .app
        (.lam (letParam (pos ++ [2]) y₀) ((y₀ :: ys).map fun y => (pos ++ [2], y))
          (.letP (toTm (readArg (pos ++ [2]) cr env args (.pattern, p)))
            (.pvar (letParam (pos ++ [2]) y₀))
            (elabLF R (inner (pos ++ [2]) cr env args) (crossIn none (y₀ :: ys) cr) (pos ++ [2])
              b)))
        (elabLF R env cr (pos ++ [1]) w) := by
  rw [Mettapedia.OSLF.Binding.DeclaredBindingInterpretation.Activation.lexical_pattern_activation
    R env cr pos none (toSrc p) w b y₀ ys introduced, ← introduced,
    update_lfIntro_eq_inner (pos ++ [2]) cr env args p one, elabLF_toSrc]
  rfl

end LexicalFresh

/-! ## Controls -/

namespace Controls

/-- Symbols: `holds`, the atoms `a`, `b`, `1`, `2`, the space name `t`, and a pair head. -/
inductive Sym where
  | holds
  | a
  | b
  | one
  | two
  | t
  | pair
  deriving DecidableEq, Repr

/-- The spellings `$j` and `$f`. -/
inductive Name where
  | j
  | f
  deriving DecidableEq, Repr

/-- `(holds $j $f)`. -/
def holdsJF : Pat Name Sym := .node .holds (.var .j) (.var .f)

/-- `(holds x y)`. -/
def fact (x y : Sym) : Tm Sym := .node .holds (.leaf x) (.leaf y)

/-- `&t = {(holds a 1), (holds b 2)}`. -/
def spaceT : Multiset (Tm Sym) := {fact .a .one, fact .b .two}

/-- The scope around: every name at the top. -/
def top : REnv Name := fun _ => []

/-- After `let $f 1` at the top: the slot `([], f)` holds `1`. -/
def outer : Subst (Slot Name) (Tm Sym) := fun s => if s = ([], .f) then some (.leaf .one) else none

/-- The form stands at position `[0]`. -/
def here : Owner := [0]

/-- `(transform &t (read (holds $j $f)) ($j $f))`, as its declaration reads it. -/
def transformForm : Form Name Sym :=
  [(.value, .leaf .t), (.pattern, holdsJF), (.body, .node .pair (.var .j) (.var .f))]

/-- `(rows-of (holds $j $f))`: a form nobody declared, so an ordinary call; its argument is a
value, and `rows-of` matches it against `&t`. -/
def undeclaredForm : Form Name Sym := [(.value, holdsJF)]

/-- The matcher: syntactic, no symbol commutes. -/
abbrev syntactic : Sym → Bool := fun _ => false

theorem outer_fresh : ∀ y, outer (here, y) = none := by
  intro y
  simp [outer, here]

/-- **Declared: both rows.** The declared pattern gives `(a, 1)` and `(b, 2)`, and every answer
keeps the outer `$f` at `1`. -/
theorem declared_two_answers :
    (matchSpace (cmatch syntactic) spaceT (readArg here [] top transformForm (.pattern, holdsJF))
        outer).map (fun τ => (τ (here, .j), τ (here, .f), τ ([], .f))) =
      {(some (.leaf .a), some (.leaf .one), some (.leaf .one)),
        (some (.leaf .b), some (.leaf .two), some (.leaf .one))} := by
  decide

/-- **Undeclared: the outer name refines.** At a value position the pattern is read where the
form stands, so its `$f` is the outer `$f`, which holds `1`: only `(a, 1)` remains. -/
theorem undeclared_one_answer :
    (matchSpace (cmatch syntactic) spaceT (readArg here [] top undeclaredForm (.value, holdsJF))
        outer).map (fun τ => (τ ([], .j), τ ([], .f))) =
      {(some (.leaf .a), some (.leaf .one))} := by
  decide

/-- **Crossing set: shared on purpose.** With `{$f}` written on the form, its `$f` is the outer
one, and only `(a, 1)` remains. -/
theorem crossing_one_answer :
    (matchSpace (cmatch syntactic) spaceT (readArg here [.f] top transformForm (.pattern, holdsJF))
        outer).map (fun τ => (τ (here, .j), τ ([], .f))) =
      {(some (.leaf .a), some (.leaf .one))} := by
  decide

/-- The three readings differ in their number of answers: two, one, one. -/
theorem answer_counts :
    Multiset.card (matchSpace (cmatch syntactic) spaceT
        (readArg here [] top transformForm (.pattern, holdsJF)) outer) = 2 ∧
      Multiset.card (matchSpace (cmatch syntactic) spaceT
        (readArg here [] top undeclaredForm (.value, holdsJF)) outer) = 1 ∧
      Multiset.card (matchSpace (cmatch syntactic) spaceT
        (readArg here [.f] top transformForm (.pattern, holdsJF)) outer) = 1 := by
  decide

/-- The headline applies to the declared transform: its answers are `match`'s on the pattern as
written, renamed into the transform's slots. -/
theorem transform_is_match :
    joinSpace (cmatch syntactic) spaceT (readPatterns here [] top transformForm) outer =
      (matchSpace (cmatch syntactic) spaceT holdsJF fun _ => none).map (withSlots outer here) := by
  rw [declared_patterns_match syntactic here top transformForm outer outer_fresh spaceT]
  simp [transformForm, patterns, joinSpace_singleton]

end Controls

end Mettapedia.OSLF.Binding.DeclaredBinders
