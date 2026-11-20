import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Existence

/-!
# A definition as a constant of the package: its rows join conversion

The package's own definitions (addition, `vec`, `below`, the eliminator) are constants whose rows are
computation rules. A definition by rows is declared the same way: a new constant at its declared type,
its rows added to the package's table (`extendedRules`). For a vector parameter matched by `nil` and
`cons`, the rule matches the call index by `zero` and `succ k` and takes the vector apart by the
projections (`ruleOf`): `pair` is no constructor pattern of the package, and `vec A (succ k)` is
`Σ A (vec A k)`.

**What this module proves, for every development (a list of definitions, each declared as a constant)
whose rules pass the tree's own declaration-time check together with the package's fourteen rows
(`devCheck`)**:

* the extended package is a constructor system, so its conversion is **Church–Rosser**
  (`dev_churchRosser`, by `DeclarationCheck.checked_churchRosser`);
* it contains the package: every step of the package is a step of the extension (`pkg_step_dev`);
* it is **conservative over the old terms**: two terms that mention none of the new constants and
  convert in the extension already convert in the package (`dev_conservative`). A step from such a
  term is a step of the package to such a term (`dev_step_old`), and Church–Rosser does the rest.

**Instances, by kernel evaluation** (`devCheck`): addition by rows; append over that addition, its
declared type using the new constant; `head`, whose uncovered calls stay stuck; `map`; the
interpreter's literal row. **Control**: the overlapping rows fail the check (`overlap_devCheck`).

**What the check asks of a name.** No name is entered twice (`devCheck_names`), so a name's first
entry, which gives its declaration, is its only entry, which gives its rules (`devCheck_find`); the
development that enters addition twice passes every other part of the check and is refused for that
(`twice_devCheck`). A new name is none of the package's eight computing constants and occurs in none of
its fourteen rows. So it is not `zero`, `succ`, `tt`, `unit` or `void`, which occur in
the rows. A constant that the package declares without a rule and that occurs in no row, `num` or
`void-rec`, passes as a name (`declared_name_passes`); the extension then declares it at the
definition's type in place of its own. The three results above are about steps and conversion and hold
for every development that passes.

**Names not declared in the package** (`devFresh`) is a separate condition, asked only where the
declarations matter. Under it the package is a sub-package of the extension (`dev_sub`), so every typing
and every typed equality of the package holds in the extension (`typed_dev`, `equal_dev`). The condition
cannot be dropped there: the development that takes the name `num` passes the check, and the package is
no sub-package of its extension (`declared_name_control`). The developments of this module meet it
(`addAppend_fresh`, `others_fresh`).

**Not proved here**: that the extended package is qualified. Typed right sides need the row checker run
over the extended package with the function a declared constant that does not compute, and
termination needs the recursion theorem for the new constant; neither depends on anything in this
module, both need the row checker generalized from the fixed vectors package.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema
open ConversionCoherence (StepStar ChurchRosser)
open TowerVectorsModel (U0 numC zeroC succC ttC vecC addC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D)
open Vectors.Checker (Pattern Row Definition)

/-! ## The rules of a definition -/

/-- The image of a slot in a rule: over the prefix, `k` in the successor case, and the later parameters;
the vector taken apart by the projections. -/
def ruleSlotImage (p : Plan) (case : Bool) (M : Nat) : Slot → Option (Tower.Tm M)
  | .param i =>
      if i < p.j then varAt M (p.q + (if case then 1 else 0) + (p.j - 1 - i))
      else if p.j < i ∧ i ≤ p.j + p.q then varAt M (p.j + p.q - i)
      else none
  | .index => if case then (varAt M p.q).map succC else some zeroC
  | .pred => if case then varAt M p.q else none
  | .head i => if p.j < i ∧ i ≤ p.j + p.q then (varAt M (p.j + p.q - i)).map .fst else none
  | .tail i => if p.j < i ∧ i ≤ p.j + p.q then (varAt M (p.j + p.q - i)).map .snd else none

/-- The images of a row's variables in its rule; the function is the declared constant. -/
def ruleImages (p : Plan) (case : Bool) (M : Nat) (name : DeclName) (r : Row) (slots : List Slot) :
    Fin (r.vars + 1) → Option (Tower.Tm M) := fun x =>
  if x.val < r.vars then (slots[r.vars - 1 - x.val]?).bind (ruleSlotImage p case M) else some (.const name)

/-- The left side of a rule: the constant at the prefix, the constructor at the call index, and the
later parameters, the vector among them a variable. -/
def ruleLeft (p : Plan) (case : Bool) (name : DeclName) (M : Nat) : Option (Tower.Tm M) := do
  let pre ← (List.range p.j).mapM fun i => varAt M (p.q + (if case then 1 else 0) + (p.j - 1 - i))
  let idx ← if case then (varAt M p.q).map succC else some zeroC
  let suf ← (List.range p.q).mapM fun t => varAt M (p.q - 1 - t)
  pure (spine (.const name) (pre ++ [idx] ++ suf))

/-- **The rule of a row.** -/
def ruleOf (p : Plan) (name : DeclName) (r : Row) (case : Bool) (slots : List Slot) :
    Option (Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) := do
  let M := p.j + (if case then 1 else 0) + p.q
  let left ← ruleLeft p case name M
  let right ← translate (ruleImages p case M name r slots) none r.body
  pure ⟨M, (left, right)⟩

/-- The variables of a context of arity `a`, in telescope order. -/
def telescopeVars (a : Nat) : List (Tower.Tm a) := List.ofFn fun i : Fin a => .var i.rev

/-- **The rules of a definition**, declared as the constant `name`. -/
def rulesOf (name : DeclName) (d : Definition) : Option (AlgebraicSchema.SchemaTable Tower.Head) :=
  match scrutinee d with
  | some (j, kind) => do
      let p : Plan := ⟨0, j, d.arity - 1 - j, kind⟩
      let shapes ← shapesOf d
      shapes.mapM fun s => ruleOf p name s.1 s.2.1 s.2.2
  | none =>
      match d.rows with
      | [r] =>
          if r.vars = d.arity then
            (translate (fun x : Fin (r.vars + 1) => if x.val < r.vars then varAt d.arity x.val
                else some (.const name)) none r.body).map fun right =>
              [⟨d.arity, (spine (.const name) (telescopeVars d.arity), right)⟩]
          else none
      | _ => none

/-! ## A development extends the package -/

/-- A development: definitions, each declared as a constant. -/
abbrev Development := List (DeclName × Definition)

/-- The constants defined in the package extended by a development. -/
def devDefined (dev : Development) (n : DeclName) : Bool := Vectors.vectorDefined n || dev.any (·.1 == n)

/-- Their arities. -/
def devArity (dev : Development) (n : DeclName) : Nat :=
  match dev.find? (·.1 == n) with
  | some (_, d) => d.arity
  | none => Vectors.vectorArity n

/-- The rules of a development. -/
def devRules (dev : Development) : Option (AlgebraicSchema.SchemaTable Tower.Head) :=
  (dev.mapM fun e => rulesOf e.1 e.2).map List.flatten

/-- The head constant of a left side. -/
def headConst? {n : Nat} : Tower.Tm n → Option DeclName
  | .const c => some c
  | .app g _ => headConst? g
  | _ => none

/-- Whether a constant is missing from a term. -/
def constFreeB (f : DeclName) {n : Nat} : Tower.Tm n → Bool
  | .var _ => true
  | .const c => c != f
  | .head _ => true
  | .pi A B => constFreeB f A && constFreeB f B
  | .sigma A B => constFreeB f A && constFreeB f B
  | .id A a b => constFreeB f A && constFreeB f a && constFreeB f b
  | .lam b => constFreeB f b
  | .app g a => constFreeB f g && constFreeB f a
  | .pair a b => constFreeB f a && constFreeB f b
  | .fst t => constFreeB f t
  | .snd t => constFreeB f t
  | .refl t => constFreeB f t

/-- Whether no name occurs twice in a list of names. -/
def namesDistinct : List DeclName → Bool
  | [] => true
  | n :: rest => !(rest.any (· == n)) && namesDistinct rest

theorem namesDistinct_nodup : ∀ {names : List DeclName}, namesDistinct names = true → names.Nodup
  | [], _ => List.nodup_nil
  | n :: rest, ok => by
      simp only [namesDistinct, Bool.and_eq_true, Bool.not_eq_true'] at ok
      obtain ⟨missing, distinct⟩ := ok
      refine List.nodup_cons.mpr ⟨fun member => ?_, namesDistinct_nodup distinct⟩
      have present : rest.any (· == n) = true := List.any_eq_true.mpr ⟨n, member, beq_self_eq_true n⟩
      rw [present] at missing
      cases missing

/-- **The declaration-time check of a development**: the new names are none of the package's computing
constants and do not occur in its rows; every new rule is headed by a new constant; the package's rows
with the new rules pass the tree's own check (constructor patterns, linear, covered, disjoint); and no
name is entered twice, so that the declaration of a name (its first entry, read by `devBase` and
`devArity`) and its rules (every entry, read by `devRules`) come from one definition. -/
def devCheck (dev : Development) : Bool :=
  match devRules dev with
  | some rows =>
      dev.all (fun e => !Vectors.vectorDefined e.1 &&
        Vectors.vectorEquations.all fun r => constFreeB e.1 r.2.1 && constFreeB e.1 r.2.2) &&
      rows.all (fun r => (headConst? r.2.1).any fun c => dev.any (·.1 == c)) &&
      DeclarationCheck.checkTable (devDefined dev) (devArity dev) (Vectors.vectorEquations ++ rows) &&
      namesDistinct (dev.map (·.1))
  | none => false

/-- The package with the development's constants declared, and no computation of its own. -/
def devBase (dev : Development) : Rules Tower.Head :=
  { pkg with
    constantType := fun n =>
      match dev.find? (·.1 == n) with
      | some (_, d) => some d.type
      | none => pkg.constantType n
    computation := RootComputation.empty }

/-- **The package extended by a development**: its rows and the development's rules, as computation. -/
def devPackage (dev : Development) (rows : AlgebraicSchema.SchemaTable Tower.Head) : Rules Tower.Head :=
  declare (devBase dev) (SchemaFamily.computation (Vectors.vectorEquations ++ rows).family)

/-! ## Church–Rosser -/

theorem devCheck_parts {dev : Development} (ok : devCheck dev = true) :
    ∃ rows, devRules dev = some rows ∧
      (∀ e ∈ dev, Vectors.vectorDefined e.1 = false ∧
        ∀ r ∈ Vectors.vectorEquations, constFreeB e.1 r.2.1 = true ∧ constFreeB e.1 r.2.2 = true) ∧
      (∀ r ∈ rows, ∃ c, headConst? r.2.1 = some c ∧ ∃ e ∈ dev, e.1 = c) ∧
      DeclarationCheck.checkTable (devDefined dev) (devArity dev) (Vectors.vectorEquations ++ rows) = true := by
  unfold devCheck at ok
  split at ok
  · rename_i rows found
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Option.any_eq_true,
      List.any_eq_true, beq_iff_eq] at ok
    obtain ⟨⟨⟨fresh, heads⟩, table⟩, -⟩ := ok
    refine ⟨rows, found, fun e member => ⟨(fresh e member).1, fun r rm => (fresh e member).2 r rm⟩,
      fun r rm => ?_, table⟩
    obtain ⟨c, hc, e, em, same⟩ := heads r rm
    exact ⟨c, hc, e, em, same⟩
  · cases ok

/-- **A checked development enters each name once.** -/
theorem devCheck_names {dev : Development} (ok : devCheck dev = true) : (dev.map (·.1)).Nodup := by
  unfold devCheck at ok
  split at ok
  · simp only [Bool.and_eq_true] at ok
    exact namesDistinct_nodup ok.2
  · cases ok

/-- When no name is entered twice, the first entry of the name of an entry is that entry. -/
theorem find_of_nodup : ∀ {dev : Development}, (dev.map (·.1)).Nodup → ∀ {e : DeclName × Definition},
    e ∈ dev → dev.find? (·.1 == e.1) = some e
  | [], _, _, member => nomatch member
  | h :: rest, distinct, e, member => by
      rw [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with same | inRest
      · subst same
        simp
      · have differ : (h.1 == e.1) = false := by
          rw [beq_eq_false_iff_ne]
          intro equal
          exact distinct.1 (List.mem_map.mpr ⟨e, inRest, equal.symm⟩)
        rw [List.find?_cons, differ]
        exact find_of_nodup distinct.2 inRest

/-- **In a checked development the first entry of a name is its only entry**: the declaration of the
name (`devBase`, `devArity`) and its rules (`devRules`) come from the same definition. -/
theorem devCheck_find {dev : Development} (ok : devCheck dev = true) {e : DeclName × Definition}
    (member : e ∈ dev) : dev.find? (·.1 == e.1) = some e :=
  find_of_nodup (devCheck_names ok) member

/-- **The package extended by a checked development is Church–Rosser.** -/
theorem dev_churchRosser {dev : Development} {rows : AlgebraicSchema.SchemaTable Tower.Head}
    (table : DeclarationCheck.checkTable (devDefined dev) (devArity dev) (Vectors.vectorEquations ++ rows) = true) :
    ChurchRosser (devPackage dev rows) :=
  DeclarationCheck.checked_churchRosser (devBase dev) (by intro n l r impossible; exact impossible)
    LevelTower.headEq_symmetric table

/-- **The extension contains the package**: every step of the package is a step of the extension. -/
theorem pkg_step_dev (dev : Development) (rows : AlgebraicSchema.SchemaTable Tower.Head) {n : Nat}
    {l r : Tower.Tm n} (step : pkg.computation.step l r) : (devPackage dev rows).computation.step l r := by
  obtain ⟨arity, left, right, σ, rule, rfl, rfl⟩ := Vectors.vector_cover level1 step
  exact Or.inr (SchemaStep.instantiate (List.mem_append_left _ rule) σ)

/-! ## Names not declared in the package: the package is a sub-package of the extension -/

/-- **The names of a development are not declared in the package.** Asked where the declarations of the
package have to be those of the extension; the results on steps and conversion do not need it. -/
def devFresh (dev : Development) : Bool := dev.all fun e => (pkg.constantType e.1).isNone

/-- **Under that condition the package is a sub-package of the extended one**: the universe structure is
the same, every declaration of the package is a declaration of the extension, and every step of the
package is a step of the extension. -/
theorem dev_sub {dev : Development} (fresh : devFresh dev = true)
    (rows : AlgebraicSchema.SchemaTable Tower.Head) : RulesSub pkg (devPackage dev rows) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := by
    intro name type declared
    have missing : dev.find? (·.1 == name) = none := by
      rw [List.find?_eq_none]
      intro e member same
      have undeclared := List.all_eq_true.mp fresh e member
      rw [beq_iff_eq.mp same, declared] at undeclared
      simp at undeclared
    show (match dev.find? (·.1 == name) with
      | some (_, d) => some d.type
      | none => pkg.constantType name) = some type
    rw [missing]
    exact declared
  computation := fun step => pkg_step_dev dev rows step

/-- **Every typing of the package is a typing of the extension**, when the names of the development are
not declared in the package. -/
theorem typed_dev {dev : Development} (fresh : devFresh dev = true)
    (rows : AlgebraicSchema.SchemaTable Tower.Head) {n : Nat} {Γ : Ctx Tower.Head n} {t A : Tower.Tm n}
    (typed : Typed pkg Γ t A) : Typed (devPackage dev rows) Γ t A :=
  Derivable.mono (dev_sub fresh rows) typed

/-- **Every typed equality of the package is one of the extension**, under the same condition. -/
theorem equal_dev {dev : Development} (fresh : devFresh dev = true)
    (rows : AlgebraicSchema.SchemaTable Tower.Head) {n : Nat} {Γ : Ctx Tower.Head n} {a b A : Tower.Tm n}
    (equal : Equal pkg Γ a b A) : Equal (devPackage dev rows) Γ a b A :=
  Derivable.mono (dev_sub fresh rows) equal

/-! ## Old terms -/

theorem constFreeB_sound {f : DeclName} : ∀ {n : Nat} {t : Tower.Tm n}, constFreeB f t = true → ConstFree f t
  | _, .var _, _ => trivial
  | _, .const c, h => by
      simp only [constFreeB, bne_iff_ne, ne_eq] at h
      exact h
  | _, .head _, _ => trivial
  | _, .pi A B, h => by
      simp only [constFreeB, Bool.and_eq_true] at h
      exact ⟨constFreeB_sound h.1, constFreeB_sound h.2⟩
  | _, .sigma A B, h => by
      simp only [constFreeB, Bool.and_eq_true] at h
      exact ⟨constFreeB_sound h.1, constFreeB_sound h.2⟩
  | _, .id A a b, h => by
      simp only [constFreeB, Bool.and_eq_true] at h
      exact ⟨constFreeB_sound h.1.1, constFreeB_sound h.1.2, constFreeB_sound h.2⟩
  | _, .lam b, h => constFreeB_sound (f := f) (t := b) h
  | _, .app g a, h => by
      simp only [constFreeB, Bool.and_eq_true] at h
      exact ⟨constFreeB_sound h.1, constFreeB_sound h.2⟩
  | _, .pair a b, h => by
      simp only [constFreeB, Bool.and_eq_true] at h
      exact ⟨constFreeB_sound h.1, constFreeB_sound h.2⟩
  | _, .fst t, h => constFreeB_sound (f := f) (t := t) h
  | _, .snd t, h => constFreeB_sound (f := f) (t := t) h
  | _, .refl t, h => constFreeB_sound (f := f) (t := t) h

theorem ConstFree.of_rename {f : DeclName} : ∀ {n m : Nat} {ρ : Ren n m} {t : Tower.Tm n},
    ConstFree f (rename ρ t) → ConstFree f t
  | _, _, _, .var _, _ => trivial
  | _, _, _, .const _, h => h
  | _, _, _, .head _, _ => trivial
  | _, _, ρ, .pi A B, h =>
      ⟨ConstFree.of_rename (ρ := ρ) (t := A) h.1, ConstFree.of_rename (ρ := liftRen ρ) (t := B) h.2⟩
  | _, _, ρ, .sigma A B, h =>
      ⟨ConstFree.of_rename (ρ := ρ) (t := A) h.1, ConstFree.of_rename (ρ := liftRen ρ) (t := B) h.2⟩
  | _, _, ρ, .id A a b, h =>
      ⟨ConstFree.of_rename (ρ := ρ) (t := A) h.1, ConstFree.of_rename (ρ := ρ) (t := a) h.2.1,
        ConstFree.of_rename (ρ := ρ) (t := b) h.2.2⟩
  | _, _, ρ, .lam b, h => ConstFree.of_rename (ρ := liftRen ρ) (t := b) h
  | _, _, ρ, .app g a, h =>
      ⟨ConstFree.of_rename (ρ := ρ) (t := g) h.1, ConstFree.of_rename (ρ := ρ) (t := a) h.2⟩
  | _, _, ρ, .pair a b, h =>
      ⟨ConstFree.of_rename (ρ := ρ) (t := a) h.1, ConstFree.of_rename (ρ := ρ) (t := b) h.2⟩
  | _, _, ρ, .fst t, h => ConstFree.of_rename (ρ := ρ) (t := t) h
  | _, _, ρ, .snd t, h => ConstFree.of_rename (ρ := ρ) (t := t) h
  | _, _, ρ, .refl t, h => ConstFree.of_rename (ρ := ρ) (t := t) h

/-- A variable that occurs in a term is free of `f` at a substitution that leaves the term free of `f`. -/
theorem constFree_of_occurs {f : DeclName} : ∀ {n m : Nat} (t : Tower.Tm n) {σ : Sub Tower.Head n m}
    {x : Fin n}, ConstFree f (subst σ t) → 0 < variableMultiplicity x t → ConstFree f (σ x)
  | _, _, .var i, σ, x, h, occurs => by
      simp only [variableMultiplicity] at occurs
      split at occurs
      · rename_i same
        subst same
        exact h
      · cases occurs
  | _, _, .const _, _, _, _, occurs => by simp [variableMultiplicity] at occurs
  | _, _, .head _, _, _, _, occurs => by simp [variableMultiplicity] at occurs
  | _, _, .pi A B, σ, x, h, occurs => by
      simp only [variableMultiplicity] at occurs
      by_cases inA : 0 < variableMultiplicity x A
      · exact constFree_of_occurs A h.1 inA
      · exact ConstFree.of_rename (ρ := wk) (constFree_of_occurs (σ := liftSub σ) (x := x.succ) B h.2 (by omega))
  | _, _, .sigma A B, σ, x, h, occurs => by
      simp only [variableMultiplicity] at occurs
      by_cases inA : 0 < variableMultiplicity x A
      · exact constFree_of_occurs A h.1 inA
      · exact ConstFree.of_rename (ρ := wk) (constFree_of_occurs (σ := liftSub σ) (x := x.succ) B h.2 (by omega))
  | _, _, .id A a b, σ, x, h, occurs => by
      simp only [variableMultiplicity] at occurs
      by_cases inA : 0 < variableMultiplicity x A
      · exact constFree_of_occurs A h.1 inA
      · by_cases ina : 0 < variableMultiplicity x a
        · exact constFree_of_occurs a h.2.1 ina
        · exact constFree_of_occurs b h.2.2 (by omega)
  | _, _, .lam b, σ, x, h, occurs => by
      simp only [variableMultiplicity] at occurs
      exact ConstFree.of_rename (ρ := wk) (constFree_of_occurs (σ := liftSub σ) (x := x.succ) b h occurs)
  | _, _, .app g a, σ, x, h, occurs => by
      simp only [variableMultiplicity] at occurs
      by_cases ing : 0 < variableMultiplicity x g
      · exact constFree_of_occurs g h.1 ing
      · exact constFree_of_occurs a h.2 (by omega)
  | _, _, .pair a b, σ, x, h, occurs => by
      simp only [variableMultiplicity] at occurs
      by_cases ina : 0 < variableMultiplicity x a
      · exact constFree_of_occurs a h.1 ina
      · exact constFree_of_occurs b h.2 (by omega)
  | _, _, .fst t, σ, x, h, occurs => by
      simp only [variableMultiplicity] at occurs
      exact constFree_of_occurs t h occurs
  | _, _, .snd t, σ, x, h, occurs => by
      simp only [variableMultiplicity] at occurs
      exact constFree_of_occurs t h occurs
  | _, _, .refl t, σ, x, h, occurs => by
      simp only [variableMultiplicity] at occurs
      exact constFree_of_occurs t h occurs

/-- A term free of `f`, at a substitution free of `f` on the variables that occur, stays free of `f`. -/
theorem constFree_subst_of_occurs {f : DeclName} : ∀ {n m : Nat} (t : Tower.Tm n) {σ : Sub Tower.Head n m},
    ConstFree f t → (∀ x, 0 < variableMultiplicity x t → ConstFree f (σ x)) → ConstFree f (subst σ t)
  | _, _, .var i, σ, _, images => images i (by simp [variableMultiplicity])
  | _, _, .const _, _, h, _ => h
  | _, _, .head _, _, _, _ => trivial
  | _, _, .pi A B, σ, h, images =>
      ⟨constFree_subst_of_occurs A h.1 fun x hx => images x (by simp only [variableMultiplicity]; omega),
        constFree_subst_of_occurs B h.2
          (lift_images fun y hy => images y (by simp only [variableMultiplicity]; omega))⟩
  | _, _, .sigma A B, σ, h, images =>
      ⟨constFree_subst_of_occurs A h.1 fun x hx => images x (by simp only [variableMultiplicity]; omega),
        constFree_subst_of_occurs B h.2
          (lift_images fun y hy => images y (by simp only [variableMultiplicity]; omega))⟩
  | _, _, .id A a b, σ, h, images =>
      ⟨constFree_subst_of_occurs A h.1 fun x hx => images x (by simp only [variableMultiplicity]; omega),
        constFree_subst_of_occurs a h.2.1 fun x hx => images x (by simp only [variableMultiplicity]; omega),
        constFree_subst_of_occurs b h.2.2 fun x hx => images x (by simp only [variableMultiplicity]; omega)⟩
  | _, _, .lam b, σ, h, images =>
      constFree_subst_of_occurs b h (lift_images fun y hy => images y (by simpa [variableMultiplicity] using hy))
  | _, _, .app g a, σ, h, images =>
      ⟨constFree_subst_of_occurs g h.1 fun x hx => images x (by simp only [variableMultiplicity]; omega),
        constFree_subst_of_occurs a h.2 fun x hx => images x (by simp only [variableMultiplicity]; omega)⟩
  | _, _, .pair a b, σ, h, images =>
      ⟨constFree_subst_of_occurs a h.1 fun x hx => images x (by simp only [variableMultiplicity]; omega),
        constFree_subst_of_occurs b h.2 fun x hx => images x (by simp only [variableMultiplicity]; omega)⟩
  | _, _, .fst t, σ, h, images => constFree_subst_of_occurs t h fun x hx => images x (by simpa [variableMultiplicity] using hx)
  | _, _, .snd t, σ, h, images => constFree_subst_of_occurs t h fun x hx => images x (by simpa [variableMultiplicity] using hx)
  | _, _, .refl t, σ, h, images => constFree_subst_of_occurs t h fun x hx => images x (by simpa [variableMultiplicity] using hx)
where
  lift_images {n m : Nat} {B : Tower.Tm (n + 1)} {σ : Sub Tower.Head n m}
      (images : ∀ y : Fin n, 0 < variableMultiplicity y.succ B → ConstFree f (σ y)) :
      ∀ x, 0 < variableMultiplicity x B → ConstFree f (liftSub σ x) := by
    intro x
    refine Fin.cases (fun _ => trivial) (fun y hy => ?_) x
    simp only [liftSub, Fin.cases_succ]
    exact (images y hy).rename wk

/-- A term headed by `c`, at any substitution, is not free of `c`. -/
theorem not_constFree_of_head {c : DeclName} : ∀ {n m : Nat} {t : Tower.Tm n} (σ : Sub Tower.Head n m),
    headConst? t = some c → ¬ ConstFree c (subst σ t)
  | _, _, .const c', _, h, free => by
      simp only [headConst?, Option.some.injEq] at h
      subst h
      exact free rfl
  | _, _, .app g _, σ, h, free => not_constFree_of_head σ (t := g) h free.1
  | _, _, .var _, _, h, _ => by simp [headConst?] at h
  | _, _, .head _, _, h, _ => by simp [headConst?] at h
  | _, _, .pi _ _, _, h, _ => by simp [headConst?] at h
  | _, _, .sigma _ _, _, h, _ => by simp [headConst?] at h
  | _, _, .id _ _ _, _, h, _ => by simp [headConst?] at h
  | _, _, .lam _, _, h, _ => by simp [headConst?] at h
  | _, _, .pair _ _, _, h, _ => by simp [headConst?] at h
  | _, _, .fst _, _, h, _ => by simp [headConst?] at h
  | _, _, .snd _, _, h, _ => by simp [headConst?] at h
  | _, _, .refl _, _, h, _ => by simp [headConst?] at h

/-- Free of every constant of the development. -/
def OldTerm (dev : Development) {n : Nat} (t : Tower.Tm n) : Prop := ∀ e ∈ dev, ConstFree e.1 t

/-- **A step of the extension from an old term is a step of the package to an old term.** -/
theorem dev_step_old {dev : Development} (ok : devCheck dev = true) {rows : AlgebraicSchema.SchemaTable Tower.Head}
    (found : devRules dev = some rows) :
    ∀ {n : Nat} {t u : Tower.Tm n}, StepCore (devPackage dev rows).computation (devPackage dev rows).headEq t u →
      OldTerm dev t → StepCore pkg.computation pkg.headEq t u ∧ OldTerm dev u := by
  obtain ⟨rows', found', fresh, heads, table⟩ := devCheck_parts ok
  rw [found] at found'
  obtain rfl := Option.some.inj found'
  intro n t u step
  induction step with
  | betaPi body a =>
      intro old
      refine ⟨.betaPi body a, fun e member => ?_⟩
      have free := old e member
      show ConstFree e.1 (subst (subst0 a) body)
      exact ConstFree.subst (t := body) free.1 fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · exact free.2
        · trivial
  | betaSigmaFst a b => exact fun old => ⟨.betaSigmaFst a b, fun e member => (old e member).1⟩
  | betaSigmaSnd a b => exact fun old => ⟨.betaSigmaSnd a b, fun e member => (old e member).2⟩
  | head equality => exact fun _ => ⟨.head equality, fun _ _ => trivial⟩
  | root h =>
      intro old
      rcases h with impossible | h
      · exact impossible.elim
      · cases h with
        | instantiate rule σ =>
            rcases List.mem_append.mp rule with base | new
            · refine ⟨.root (Vectors.vector_sound level1 base σ), fun e member => ?_⟩
              have rightFree := constFreeB_sound ((fresh e member).2 _ base).2
              exact constFree_subst_of_occurs _ rightFree fun x hx =>
                constFree_of_occurs _ (old e member)
                  ((DeclarationCheck.checkedSystem table).covered rule x hx)
            · obtain ⟨c, hc, e, member, rfl⟩ := heads _ new
              exact (not_constFree_of_head σ hc (old e member)).elim
  | congPiDom _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => (old e member).1
      exact ⟨.congPiDom step, fun e member => ⟨newOld e member, (old e member).2⟩⟩
  | congPiCod _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => (old e member).2
      exact ⟨.congPiCod step, fun e member => ⟨(old e member).1, newOld e member⟩⟩
  | congSigmaDom _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => (old e member).1
      exact ⟨.congSigmaDom step, fun e member => ⟨newOld e member, (old e member).2⟩⟩
  | congSigmaCod _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => (old e member).2
      exact ⟨.congSigmaCod step, fun e member => ⟨(old e member).1, newOld e member⟩⟩
  | congIdTy _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => (old e member).1
      exact ⟨.congIdTy step, fun e member => ⟨newOld e member, (old e member).2⟩⟩
  | congIdLeft _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => (old e member).2.1
      exact ⟨.congIdLeft step, fun e member => ⟨(old e member).1, newOld e member, (old e member).2.2⟩⟩
  | congIdRight _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => (old e member).2.2
      exact ⟨.congIdRight step, fun e member => ⟨(old e member).1, (old e member).2.1, newOld e member⟩⟩
  | congLam _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => old e member
      exact ⟨.congLam step, newOld⟩
  | congAppFun _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => (old e member).1
      exact ⟨.congAppFun step, fun e member => ⟨newOld e member, (old e member).2⟩⟩
  | congAppArg _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => (old e member).2
      exact ⟨.congAppArg step, fun e member => ⟨(old e member).1, newOld e member⟩⟩
  | congPairFst _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => (old e member).1
      exact ⟨.congPairFst step, fun e member => ⟨newOld e member, (old e member).2⟩⟩
  | congPairSnd _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => (old e member).2
      exact ⟨.congPairSnd step, fun e member => ⟨(old e member).1, newOld e member⟩⟩
  | congFst _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => old e member
      exact ⟨.congFst step, newOld⟩
  | congSnd _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => old e member
      exact ⟨.congSnd step, newOld⟩
  | congRefl _ ih =>
      intro old
      obtain ⟨step, newOld⟩ := ih fun e member => old e member
      exact ⟨.congRefl step, newOld⟩

theorem dev_stepStar_old {dev : Development} (ok : devCheck dev = true) {rows : AlgebraicSchema.SchemaTable Tower.Head}
    (found : devRules dev = some rows) {n : Nat} {t u : Tower.Tm n} (steps : StepStar (devPackage dev rows) t u)
    (old : OldTerm dev t) : StepStar pkg t u ∧ OldTerm dev u := by
  induction steps with
  | refl => exact ⟨.refl, old⟩
  | tail _ step ih =>
      obtain ⟨prior, middleOld⟩ := ih
      obtain ⟨step', uOld⟩ := dev_step_old ok found step middleOld
      exact ⟨.tail prior step', uOld⟩

/-- **The extension is conservative over the old terms**: two terms that mention none of the new
constants and convert in the extended package already convert in the package. -/
theorem dev_conservative {dev : Development} (ok : devCheck dev = true) {rows : AlgebraicSchema.SchemaTable Tower.Head}
    (found : devRules dev = some rows) {n : Nat} {t u : Tower.Tm n} (oldT : OldTerm dev t) (oldU : OldTerm dev u)
    (conversion : Conv (devPackage dev rows).headEq t u (devPackage dev rows).computation) :
    Conv pkg.headEq t u pkg.computation := by
  obtain ⟨-, -, -, -, table⟩ := devCheck_parts ok
  obtain ⟨rows', found', -, -, table'⟩ := devCheck_parts ok
  rw [found] at found'
  obtain rfl := Option.some.inj found'
  obtain ⟨common, fromT, fromU⟩ := dev_churchRosser table' conversion
  have left := (dev_stepStar_old ok found fromT oldT).1
  have right := (dev_stepStar_old ok found fromU oldU).1
  exact .trans _ _ _ (conv_of_stepStar left) (.symm _ _ (conv_of_stepStar right))

/-! ## Instances -/

/-- The constant of addition by rows. -/
def addName : DeclName := .mkSimple "add-by-rows"

/-- The constant of append. -/
def appendName : DeclName := .mkSimple "append-by-rows"

/-- **Append over addition by rows**: its declared type `vec A (add n m)` uses the new constant. -/
def appendOnAddDef : Definition :=
  ⟨"append", 5, TowerVectorsPrograms.appendCtx,
    vecC (.var 4) (spine (.const addName) [.var 3, .var 2]), [Vectors.Checker.nilRow, Vectors.Checker.consRow]⟩

/-- **The development of addition by rows, then append over it, passes the check.** -/
theorem addAppend_devCheck : devCheck [(addName, addDef), (appendName, appendOnAddDef)] = true := by
  decide +kernel

/-- Its rules: `add zero m ⟶ m`, `add (succ k) m ⟶ succ (add k m)`, `append A zero m xs ys ⟶ ys`,
`append A (succ k) m xs ys ⟶ pair (fst xs) (append A k m (snd xs) ys)`. -/
theorem addAppend_rules : devRules [(addName, addDef), (appendName, appendOnAddDef)] =
    some [⟨1, (spine (.const addName) [zeroC, .var 0], .var 0)⟩,
      ⟨2, (spine (.const addName) [succC (.var 1), .var 0],
        succC (spine (.const addName) [.var 1, .var 0]))⟩,
      ⟨4, (spine (.const appendName) [.var 3, zeroC, .var 2, .var 1, .var 0], .var 0)⟩,
      ⟨5, (spine (.const appendName) [.var 4, succC (.var 3), .var 2, .var 1, .var 0],
        .pair (.fst (.var 1)) (spine (.const appendName) [.var 4, .var 3, .var 2, .snd (.var 1), .var 0]))⟩] := by
  decide +kernel

/-- **`head`, `map` and the literal row pass the check**, each as a development of one definition; the
uncovered calls of `head` and of the literal row have no rule. -/
theorem others_devCheck :
    devCheck [(.mkSimple "head-by-rows", Vectors.Checker.headDef)] = true ∧
    devCheck [(.mkSimple "map-by-rows", mapDef)] = true ∧
    devCheck [(.mkSimple "eval-by-rows", Vectors.Checker.evalDef)] = true := by
  decide +kernel

/-- **Control: overlapping rows fail the check.** -/
theorem overlap_devCheck : devCheck [(.mkSimple "overlap-by-rows", overlapDef)] = false := by
  decide +kernel

/-- **Control: a name entered twice is refused, and only for that.** Addition entered twice has rules;
they pass the table check together with the package's rows (the repeated rules are equal, which the
disjointness test allows); its name is new and heads every rule. The check refuses it because the name
occurs twice. -/
theorem twice_devCheck :
    devCheck [(addName, addDef), (addName, addDef)] = false ∧
      namesDistinct (([(addName, addDef), (addName, addDef)] : Development).map (·.1)) = false ∧
      (match devRules [(addName, addDef), (addName, addDef)] with
        | some rows =>
            ([(addName, addDef), (addName, addDef)] : Development).all (fun e => !Vectors.vectorDefined e.1 &&
              Vectors.vectorEquations.all fun r => constFreeB e.1 r.2.1 && constFreeB e.1 r.2.2) &&
            rows.all (fun r => (headConst? r.2.1).any fun c =>
              ([(addName, addDef), (addName, addDef)] : Development).any (·.1 == c)) &&
            DeclarationCheck.checkTable (devDefined [(addName, addDef), (addName, addDef)])
              (devArity [(addName, addDef), (addName, addDef)]) (Vectors.vectorEquations ++ rows)
        | none => false) = true := by
  decide +kernel

/-- **A constant that the package declares may pass as a new name.** `num` and `void-rec` are declared in
the package, have no rule and occur in no row: a development that takes either name passes the check.
`tt` and `zero` occur in the rows and are refused. -/
theorem declared_name_passes :
    (pkg.constantType TowerNumbersModel.num).isSome = true ∧
      devCheck [(TowerNumbersModel.num, dupDef)] = true ∧
      (pkg.constantType TowerVectorsModel.voidRec).isSome = true ∧
      devCheck [(TowerVectorsModel.voidRec, dupDef)] = true ∧
      devCheck [(TowerVectorsModel.tt, dupDef)] = false ∧
      devCheck [(TowerNumbersModel.zero, dupDef)] = false := by
  decide +kernel

/-- **The condition on declared names cannot be dropped from `dev_sub`.** The development that takes the
name `num` passes the check; its name is declared in the package; and the package is no sub-package of
its extension, whatever the rules: the extension declares `num` at another type. -/
theorem declared_name_control :
    devCheck [(TowerNumbersModel.num, dupDef)] = true ∧
      devFresh [(TowerNumbersModel.num, dupDef)] = false ∧
      ∀ rows, ¬ RulesSub pkg (devPackage [(TowerNumbersModel.num, dupDef)] rows) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro rows sub
  obtain ⟨T, declared⟩ := Option.isSome_iff_exists.mp
    (show (pkg.constantType TowerNumbersModel.num).isSome = true by decide +kernel)
  have kept : (devBase [(TowerNumbersModel.num, dupDef)]).constantType TowerNumbersModel.num = some T :=
    sub.constantType declared
  have changed : (devBase [(TowerNumbersModel.num, dupDef)]).constantType TowerNumbersModel.num =
      some dupDef.type := by decide +kernel
  have differs : pkg.constantType TowerNumbersModel.num ≠ some dupDef.type := by decide +kernel
  rw [changed] at kept
  exact differs (declared.trans kept.symm)

/-- **The names of addition and append by rows are not declared in the package.** -/
theorem addAppend_fresh : devFresh [(addName, addDef), (appendName, appendOnAddDef)] = true := by
  decide +kernel

/-- Nor are those of `head`, `map` and the literal row. -/
theorem others_fresh :
    devFresh [(.mkSimple "head-by-rows", Vectors.Checker.headDef)] = true ∧
    devFresh [(.mkSimple "map-by-rows", mapDef)] = true ∧
    devFresh [(.mkSimple "eval-by-rows", Vectors.Checker.evalDef)] = true := by
  decide +kernel

/-- **Instance of `typed_dev`**: every numeral is a number of the package extended by addition and
append by rows. -/
theorem addAppend_numeral_typed (k : Nat) {rows : AlgebraicSchema.SchemaTable Tower.Head} :
    Typed (devPackage [(addName, addDef), (appendName, appendOnAddDef)] rows) .nil (nat k) numC :=
  typed_dev addAppend_fresh rows (nat_typed k)

/-- **Church–Rosser and conservativity for addition and append by rows.** -/
theorem addAppend_extension :
    ∃ rows, devRules [(addName, addDef), (appendName, appendOnAddDef)] = some rows ∧
      ChurchRosser (devPackage [(addName, addDef), (appendName, appendOnAddDef)] rows) ∧
      ∀ {n : Nat} {t u : Tower.Tm n}, OldTerm [(addName, addDef), (appendName, appendOnAddDef)] t →
        OldTerm [(addName, addDef), (appendName, appendOnAddDef)] u →
        Conv (devPackage [(addName, addDef), (appendName, appendOnAddDef)] rows).headEq t u
          (devPackage [(addName, addDef), (appendName, appendOnAddDef)] rows).computation →
        Conv pkg.headEq t u pkg.computation := by
  obtain ⟨rows, found, -, -, table⟩ := devCheck_parts addAppend_devCheck
  exact ⟨rows, found, dev_churchRosser table, fun oldT oldU conversion =>
    dev_conservative addAppend_devCheck found oldT oldU conversion⟩

end NativeTypesOnTheStep.Computing.Definitions

#print axioms NativeTypesOnTheStep.Computing.Definitions.devCheck_parts
#print axioms NativeTypesOnTheStep.Computing.Definitions.namesDistinct_nodup
#print axioms NativeTypesOnTheStep.Computing.Definitions.devCheck_names
#print axioms NativeTypesOnTheStep.Computing.Definitions.find_of_nodup
#print axioms NativeTypesOnTheStep.Computing.Definitions.devCheck_find
#print axioms NativeTypesOnTheStep.Computing.Definitions.twice_devCheck
#print axioms NativeTypesOnTheStep.Computing.Definitions.dev_churchRosser
#print axioms NativeTypesOnTheStep.Computing.Definitions.pkg_step_dev
#print axioms NativeTypesOnTheStep.Computing.Definitions.constFree_of_occurs
#print axioms NativeTypesOnTheStep.Computing.Definitions.constFree_subst_of_occurs
#print axioms NativeTypesOnTheStep.Computing.Definitions.dev_step_old
#print axioms NativeTypesOnTheStep.Computing.Definitions.dev_conservative
#print axioms NativeTypesOnTheStep.Computing.Definitions.addAppend_devCheck
#print axioms NativeTypesOnTheStep.Computing.Definitions.addAppend_rules
#print axioms NativeTypesOnTheStep.Computing.Definitions.others_devCheck
#print axioms NativeTypesOnTheStep.Computing.Definitions.overlap_devCheck
#print axioms NativeTypesOnTheStep.Computing.Definitions.declared_name_passes
#print axioms NativeTypesOnTheStep.Computing.Definitions.dev_sub
#print axioms NativeTypesOnTheStep.Computing.Definitions.typed_dev
#print axioms NativeTypesOnTheStep.Computing.Definitions.equal_dev
#print axioms NativeTypesOnTheStep.Computing.Definitions.declared_name_control
#print axioms NativeTypesOnTheStep.Computing.Definitions.addAppend_fresh
#print axioms NativeTypesOnTheStep.Computing.Definitions.others_fresh
#print axioms NativeTypesOnTheStep.Computing.Definitions.addAppend_numeral_typed
#print axioms NativeTypesOnTheStep.Computing.Definitions.addAppend_extension

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
