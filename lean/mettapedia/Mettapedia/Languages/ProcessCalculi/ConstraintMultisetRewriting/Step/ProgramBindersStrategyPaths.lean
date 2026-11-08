import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersRaising

/-!
# Positions under binders, with their siblings left open

A **path** is the shape of a λ context: the directions taken, `left`, `right` or `under` a binder,
without the sibling terms. A pattern along a path keeps one fresh hole per sibling, so a single
pattern speaks about a position in every term, whatever its siblings are. Siblings are numbered from
the top; numbers past the last sibling are never read.

- `comp`, `plug_comp`, `raiseAt_comp`: λ contexts compose, and raising along a composite is raising
  along each part.
- `contextPath`, `contextSiblings`, `Path.toContext`: a context is a path with its siblings.
- `Path.fill` (with holes) and `Path.fillSource` (source terms); `instantiate_fill`, `fill_include`,
  `fill_recovers`: instantiating a filled path is filling the instances, and an instance of a filled
  path is a filled path.
- `raiseAlong`: raising along a path's binders, which is `raiseAt` of every context with that path.
- `length_lt_size`, `prefix_of_path`: positions of a term are shorter than its size, and closed under
  prefixes.
- `pathsOf`: the paths of each length, listed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Strategy

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt Op Context appT lamT)
open LambdaComparison (app lam app_inj lam_inj)
open ContextualPatternFragment (Pattern)
open Nested (raiseAt include_app_recovers include_lam_recovers)

/-! ## Composing λ contexts -/

/-- `outer` with `inner` in its hole. -/
def comp : {Γ Δ Θ : Ctx sig} → Context Γ Δ → Context Δ Θ → Context Γ Θ
  | _, _, _, .hole, inner => inner
  | _, _, _, .appLeft outer argument, inner => .appLeft (comp outer inner) argument
  | _, _, _, .appRight function outer, inner => .appRight function (comp outer inner)
  | _, _, _, .underLam outer, inner => .underLam (comp outer inner)

theorem plug_comp {Γ Δ Θ : Ctx sig} (outer : Context Γ Δ) (inner : Context Δ Θ) (term : Term sig Θ .term) :
    (comp outer inner).plug term = outer.plug (inner.plug term) := by
  induction outer with
  | hole => rfl
  | appLeft outer argument ih => exact congrArg (fun value => appT value argument) (ih inner)
  | appRight function outer ih => exact congrArg (appT function) (ih inner)
  | underLam outer ih => exact congrArg lamT (ih inner)

theorem raiseAt_comp {Γ Δ Θ : Ctx sig} (outer : Context Γ Δ) (inner : Context Δ Θ) (e : Equation sig Γ .term) :
    raiseAt (comp outer inner) e = raiseAt inner (raiseAt outer e) := by
  induction outer with
  | hole => rfl
  | appLeft outer _ ih => exact ih inner e
  | appRight _ outer ih => exact ih inner e
  | underLam outer ih => exact ih inner (raiseOne Srt.term e)

/-- The number of constructors above the hole. -/
def depth : {Γ Δ : Ctx sig} → Context Γ Δ → Nat
  | _, _, .hole => 0
  | _, _, .appLeft inner _ => depth inner + 1
  | _, _, .appRight _ inner => depth inner + 1
  | _, _, .underLam inner => depth inner + 1

/-! ## Paths -/

/-- The shape of a context: its directions, without siblings. -/
inductive Path : Ctx sig → Ctx sig → Type where
  | here {Δ : Ctx sig} : Path Δ Δ
  | left {Δ Θ : Ctx sig} : Path Δ Θ → Path Δ Θ
  | right {Δ Θ : Ctx sig} : Path Δ Θ → Path Δ Θ
  | under {Δ Θ : Ctx sig} : Path (.term :: Δ) Θ → Path Δ Θ

/-- Decidable equality of paths. -/
def pathDecEq : {Δ Θ : Ctx sig} → (first second : Path Δ Θ) → Decidable (first = second)
  | _, _, .here, .here => isTrue rfl
  | _, _, .left first, .left second =>
      match pathDecEq first second with
      | isTrue same => isTrue (by rw [same])
      | isFalse differ => isFalse fun same => differ (Path.left.inj same)
  | _, _, .right first, .right second =>
      match pathDecEq first second with
      | isTrue same => isTrue (by rw [same])
      | isFalse differ => isFalse fun same => differ (Path.right.inj same)
  | _, _, .under first, .under second =>
      match pathDecEq first second with
      | isTrue same => isTrue (by rw [same])
      | isFalse differ => isFalse fun same => differ (Path.under.inj same)
  | _, _, .here, .left _ => isFalse nofun
  | _, _, .here, .right _ => isFalse nofun
  | _, _, .here, .under _ => isFalse nofun
  | _, _, .left _, .here => isFalse nofun
  | _, _, .left _, .right _ => isFalse nofun
  | _, _, .left _, .under _ => isFalse nofun
  | _, _, .right _, .here => isFalse nofun
  | _, _, .right _, .left _ => isFalse nofun
  | _, _, .right _, .under _ => isFalse nofun
  | _, _, .under _, .here => isFalse nofun
  | _, _, .under _, .left _ => isFalse nofun
  | _, _, .under _, .right _ => isFalse nofun

instance (Δ Θ : Ctx sig) : DecidableEq (Path Δ Θ) := pathDecEq

namespace Path

def length : {Δ Θ : Ctx sig} → Path Δ Θ → Nat
  | _, _, .here => 0
  | _, _, .left inner => length inner + 1
  | _, _, .right inner => length inner + 1
  | _, _, .under inner => length inner + 1

/-- The context of sibling `index`: the binders in scope where it sits. -/
def siblingContext : {Δ Θ : Ctx sig} → Path Δ Θ → Nat → Ctx sig
  | Δ, _, .here, _ => Δ
  | Δ, _, .left _, 0 => Δ
  | _, _, .left inner, index + 1 => siblingContext inner index
  | Δ, _, .right _, 0 => Δ
  | _, _, .right inner, index + 1 => siblingContext inner index
  | _, _, .under inner, index => siblingContext inner index

/-- Fill a path over a signature with holes: siblings and the term at the position. -/
def fill {W : Type} (declaration : W → MetaArity sig) : {Δ Θ : Ctx sig} → (path : Path Δ Θ) →
    ((index : Nat) → Term (signature sig declaration) (path.siblingContext index) .term) →
    Term (signature sig declaration) Θ .term → Term (signature sig declaration) Δ .term
  | _, _, .here, _, term => term
  | _, _, .left inner, siblings, term =>
      app declaration (fill declaration inner (fun index => siblings (index + 1)) term) (siblings 0)
  | _, _, .right inner, siblings, term =>
      app declaration (siblings 0) (fill declaration inner (fun index => siblings (index + 1)) term)
  | _, _, .under inner, siblings, term => lam declaration (fill declaration inner siblings term)

/-- Fill a path with source terms. -/
def fillSource : {Δ Θ : Ctx sig} → (path : Path Δ Θ) →
    ((index : Nat) → Term sig (path.siblingContext index) .term) → Term sig Θ .term → Term sig Δ .term
  | _, _, .here, _, term => term
  | _, _, .left inner, siblings, term => appT (fillSource inner (fun index => siblings (index + 1)) term) (siblings 0)
  | _, _, .right inner, siblings, term => appT (siblings 0) (fillSource inner (fun index => siblings (index + 1)) term)
  | _, _, .under inner, siblings, term => lamT (fillSource inner siblings term)

/-- The context with the given siblings. -/
def toContext : {Δ Θ : Ctx sig} → (path : Path Δ Θ) → ((index : Nat) → Term sig (path.siblingContext index) .term) →
    Context Δ Θ
  | _, _, .here, _ => .hole
  | _, _, .left inner, siblings => .appLeft (toContext inner fun index => siblings (index + 1)) (siblings 0)
  | _, _, .right inner, siblings => .appRight (siblings 0) (toContext inner fun index => siblings (index + 1))
  | _, _, .under inner, siblings => .underLam (toContext inner siblings)

theorem toContext_plug {Δ Θ : Ctx sig} (path : Path Δ Θ)
    (siblings : (index : Nat) → Term sig (path.siblingContext index) .term) (term : Term sig Θ .term) :
    (path.toContext siblings).plug term = path.fillSource siblings term := by
  induction path with
  | here => rfl
  | left inner ih => exact congrArg (fun value => appT value (siblings 0)) (ih _ term)
  | right inner ih => exact congrArg (appT (siblings 0)) (ih _ term)
  | under inner ih => exact congrArg lamT (ih siblings term)

theorem toContext_depth {Δ Θ : Ctx sig} (path : Path Δ Θ)
    (siblings : (index : Nat) → Term sig (path.siblingContext index) .term) :
    depth (path.toContext siblings) = path.length := by
  induction path with
  | here => rfl
  | left inner ih => exact congrArg (· + 1) (ih _)
  | right inner ih => exact congrArg (· + 1) (ih _)
  | under inner ih => exact congrArg (· + 1) (ih siblings)

end Path

/-! ## Contexts as paths -/

/-- The path of a context. -/
def contextPath : {Δ Θ : Ctx sig} → Context Δ Θ → Path Δ Θ
  | _, _, .hole => .here
  | _, _, .appLeft inner _ => .left (contextPath inner)
  | _, _, .appRight _ inner => .right (contextPath inner)
  | _, _, .underLam inner => .under (contextPath inner)

/-- The siblings of a context, top first; past the last one, a closed term. -/
def contextSiblings : {Δ Θ : Ctx sig} → (context : Context Δ Θ) →
    (index : Nat) → Term sig ((contextPath context).siblingContext index) .term
  | Δ, _, .hole, _ => closedAt Δ .term
  | _, _, .appLeft _ argument, 0 => argument
  | _, _, .appLeft inner _, index + 1 => contextSiblings inner index
  | _, _, .appRight function _, 0 => function
  | _, _, .appRight _ inner, index + 1 => contextSiblings inner index
  | _, _, .underLam inner, index => contextSiblings inner index

theorem plug_eq_fillSource {Δ Θ : Ctx sig} (context : Context Δ Θ) (term : Term sig Θ .term) :
    context.plug term = (contextPath context).fillSource (contextSiblings context) term := by
  induction context with
  | hole => rfl
  | appLeft inner argument ih => exact congrArg (fun value => appT value argument) (ih term)
  | appRight function inner ih => exact congrArg (appT function) (ih term)
  | underLam inner ih => exact congrArg lamT (ih term)

theorem toPath_length {Δ Θ : Ctx sig} (context : Context Δ Θ) : (contextPath context).length = depth context := by
  induction context with
  | hole => rfl
  | appLeft inner _ ih => exact congrArg (· + 1) ih
  | appRight _ inner ih => exact congrArg (· + 1) ih
  | underLam inner ih => exact congrArg (· + 1) ih

/-! ## Raising along a path -/

/-- Raise an equation along every binder a path passes. -/
def raiseAlong : {Δ Θ : Ctx sig} → Path Δ Θ → Equation sig Δ .term → Equation sig Θ .term
  | _, _, .here, e => e
  | _, _, .left inner, e => raiseAlong inner e
  | _, _, .right inner, e => raiseAlong inner e
  | _, _, .under inner, e => raiseAlong inner (raiseOne Srt.term e)

theorem raiseAt_eq_raiseAlong {Δ Θ : Ctx sig} (context : Context Δ Θ) (e : Equation sig Δ .term) :
    raiseAt context e = raiseAlong (contextPath context) e := by
  induction context with
  | hole => rfl
  | appLeft inner _ ih => exact ih e
  | appRight _ inner ih => exact ih e
  | underLam inner ih => exact ih (raiseOne Srt.term e)

theorem raiseAt_toContext {Δ Θ : Ctx sig} (path : Path Δ Θ)
    (siblings : (index : Nat) → Term sig (path.siblingContext index) .term) (e : Equation sig Δ .term) :
    raiseAt (path.toContext siblings) e = raiseAlong path e := by
  induction path with
  | here => rfl
  | left inner ih => exact ih _ e
  | right inner ih => exact ih _ e
  | under inner ih => exact ih siblings (raiseOne Srt.term e)

theorem raiseAlong_pattern {Δ Θ : Ctx sig} (path : Path Δ Θ) (e : Equation sig Δ .term)
    (patterned : Pattern sig e.arity e.lhs) : Pattern sig (raiseAlong path e).arity (raiseAlong path e).lhs := by
  induction path with
  | here => exact patterned
  | left inner ih => exact ih e patterned
  | right inner ih => exact ih e patterned
  | under inner ih => exact ih _ (raiseOne_pattern Srt.term e patterned)

/-! ## Filled paths and instantiation -/

namespace Path

variable {W X : Type} {declaration : W → MetaArity sig} {next : X → MetaArity sig}

theorem instantiate_fill (change : Assignment declaration next) {Δ Θ : Ctx sig} (path : Path Δ Θ)
    (siblings : (index : Nat) → Term (signature sig declaration) (path.siblingContext index) .term)
    (term : Term (signature sig declaration) Θ .term) :
    instantiate change (path.fill declaration siblings term) =
      path.fill next (fun index => instantiate change (siblings index)) (instantiate change term) := by
  induction path with
  | here => rfl
  | left inner ih =>
      change app next (instantiate change (inner.fill declaration (fun index => siblings (index + 1)) term))
        (instantiate change (siblings 0)) = _
      rw [ih]
      rfl
  | right inner ih =>
      change app next (instantiate change (siblings 0))
        (instantiate change (inner.fill declaration (fun index => siblings (index + 1)) term)) = _
      rw [ih]
      rfl
  | under inner ih =>
      change lam next (instantiate change (inner.fill declaration siblings term)) = _
      rw [ih]
      rfl

theorem fill_include {Δ Θ : Ctx sig} (path : Path Δ Θ)
    (siblings : (index : Nat) → Term sig (path.siblingContext index) .term) (term : Term sig Θ .term) :
    path.fill declaration (fun index => Rigid.includeTerm declaration (siblings index)) (Rigid.includeTerm declaration term) =
      Rigid.includeTerm declaration (path.fillSource siblings term) := by
  induction path with
  | here => rfl
  | left inner ih =>
      change app declaration (inner.fill declaration (fun index => Rigid.includeTerm declaration (siblings (index + 1)))
        (Rigid.includeTerm declaration term)) (Rigid.includeTerm declaration (siblings 0)) = _
      rw [ih]
      rfl
  | right inner ih =>
      change app declaration (Rigid.includeTerm declaration (siblings 0))
        (inner.fill declaration (fun index => Rigid.includeTerm declaration (siblings (index + 1)))
          (Rigid.includeTerm declaration term)) = _
      rw [ih]
      rfl
  | under inner ih =>
      change lam declaration (inner.fill declaration (fun index => Rigid.includeTerm declaration (siblings index))
        (Rigid.includeTerm declaration term)) = _
      rw [ih]
      rfl

/-- **An instance of a filled path is a filled path.** -/
theorem fill_recovers {Δ Θ : Ctx sig} (path : Path Δ Θ)
    (siblings : (index : Nat) → Term (signature sig declaration) (path.siblingContext index) .term)
    (term : Term (signature sig declaration) Θ .term) (source : Term sig Δ .term)
    (same : path.fill declaration siblings term = Rigid.includeTerm declaration source) :
    ∃ (sources : (index : Nat) → Term sig (path.siblingContext index) .term) (inner : Term sig Θ .term),
      source = path.fillSource sources inner ∧ term = Rigid.includeTerm declaration inner := by
  induction path with
  | here => exact ⟨fun _ => source, source, rfl, same⟩
  | left inner ih =>
      obtain ⟨function, argument, rfl, functionSame, _⟩ := include_app_recovers source _ _ same
      obtain ⟨sources, position, rfl, termSame⟩ := ih (fun index => siblings (index + 1)) term function functionSame
      refine ⟨fun index => Nat.casesOn (motive := fun index => Term sig ((Path.left inner).siblingContext index) .term)
        index argument (fun index => sources index), position, rfl, termSame⟩
  | right inner ih =>
      obtain ⟨function, argument, rfl, _, argumentSame⟩ := include_app_recovers source _ _ same
      obtain ⟨sources, position, rfl, termSame⟩ := ih (fun index => siblings (index + 1)) term argument argumentSame
      refine ⟨fun index => Nat.casesOn (motive := fun index => Term sig ((Path.right inner).siblingContext index) .term)
        index function (fun index => sources index), position, rfl, termSame⟩
  | under inner ih =>
      obtain ⟨body, rfl, bodySame⟩ := include_lam_recovers source _ same
      obtain ⟨sources, position, rfl, termSame⟩ := ih siblings term body bodySame
      exact ⟨sources, position, rfl, termSame⟩

theorem fill_pattern {Δ Θ : Ctx sig} (path : Path Δ Θ)
    (siblings : (index : Nat) → Term (signature sig declaration) (path.siblingContext index) .term)
    (term : Term (signature sig declaration) Θ .term)
    (each : ∀ index, Pattern sig declaration (siblings index)) (patterned : Pattern sig declaration term) :
    Pattern sig declaration (path.fill declaration siblings term) := by
  induction path with
  | here => exact patterned
  | left inner ih =>
      exact .rigid (S := sig) Op.app _ (.cons _ _ (ih _ term (fun index => each (index + 1)) patterned)
        (.cons _ _ (each 0) .nil))
  | right inner ih =>
      exact .rigid (S := sig) Op.app _ (.cons _ _ (each 0)
        (.cons _ _ (ih _ term (fun index => each (index + 1)) patterned) .nil))
  | under inner ih => exact .rigid (S := sig) Op.lam _ (.cons _ _ (ih siblings term each patterned) .nil)

/-! ## Sizes and prefixes -/

theorem length_add_size {Δ Θ : Ctx sig} (path : Path Δ Θ)
    (siblings : (index : Nat) → Term sig (path.siblingContext index) .term) (term : Term sig Θ .term) :
    path.length + termSize term ≤ termSize (path.fillSource siblings term) := by
  induction path with
  | here => simp [length, fillSource]
  | left inner ih =>
      have earlier := ih (fun index => siblings (index + 1)) term
      simp only [length, fillSource, appT, termSize, argsSize]
      omega
  | right inner ih =>
      have earlier := ih (fun index => siblings (index + 1)) term
      simp only [length, fillSource, appT, termSize, argsSize]
      omega
  | under inner ih =>
      have earlier := ih siblings term
      simp only [length, fillSource, lamT, termSize, argsSize]
      omega

/-- A position of a term is shorter than the term's size. -/
theorem length_lt_size {Δ Θ : Ctx sig} (path : Path Δ Θ)
    (siblings : (index : Nat) → Term sig (path.siblingContext index) .term) (term : Term sig Θ .term) :
    path.length < termSize (path.fillSource siblings term) := by
  have bound := length_add_size path siblings term
  have positive := termSize_pos term
  omega

/-- **Positions are closed under prefixes.** -/
theorem prefix_of_path {Δ Θ : Ctx sig} (path : Path Δ Θ) :
    ∀ (siblings : (index : Nat) → Term sig (path.siblingContext index) .term) (term : Term sig Θ .term)
      (count : Nat), count ≤ path.length →
      ∃ (Θ' : Ctx sig) (shorter : Path Δ Θ') (others : (index : Nat) → Term sig (shorter.siblingContext index) .term)
        (rest : Term sig Θ' .term), shorter.length = count ∧
          path.fillSource siblings term = shorter.fillSource others rest := by
  induction path with
  | here =>
      intro siblings term count bound
      have zero : count = 0 := by simp only [length] at bound; omega
      subst zero
      exact ⟨_, .here, siblings, term, rfl, rfl⟩
  | left inner ih =>
      intro siblings term count bound
      cases count with
      | zero =>
          exact ⟨_, .here, fun _ => Path.fillSource (.left inner) siblings term,
            Path.fillSource (.left inner) siblings term, rfl, rfl⟩
      | succ count =>
          obtain ⟨Θ', shorter, others, rest, sameLength, same⟩ :=
            ih (fun index => siblings (index + 1)) term count (by simp only [length] at bound; omega)
          refine ⟨Θ', .left shorter,
            fun index => Nat.casesOn (motive := fun index => Term sig ((Path.left shorter).siblingContext index) .term)
              index (siblings 0) (fun index => others index),
            rest, by simp only [length]; omega, ?_⟩
          change appT (inner.fillSource _ term) (siblings 0) = appT (shorter.fillSource others rest) (siblings 0)
          rw [same]
  | right inner ih =>
      intro siblings term count bound
      cases count with
      | zero =>
          exact ⟨_, .here, fun _ => Path.fillSource (.right inner) siblings term,
            Path.fillSource (.right inner) siblings term, rfl, rfl⟩
      | succ count =>
          obtain ⟨Θ', shorter, others, rest, sameLength, same⟩ :=
            ih (fun index => siblings (index + 1)) term count (by simp only [length] at bound; omega)
          refine ⟨Θ', .right shorter,
            fun index => Nat.casesOn (motive := fun index => Term sig ((Path.right shorter).siblingContext index) .term)
              index (siblings 0) (fun index => others index),
            rest, by simp only [length]; omega, ?_⟩
          change appT (siblings 0) (inner.fillSource _ term) = appT (siblings 0) (shorter.fillSource others rest)
          rw [same]
  | under inner ih =>
      intro siblings term count bound
      cases count with
      | zero =>
          exact ⟨_, .here, fun _ => Path.fillSource (.under inner) siblings term,
            Path.fillSource (.under inner) siblings term, rfl, rfl⟩
      | succ count =>
          obtain ⟨Θ', shorter, others, rest, sameLength, same⟩ :=
            ih siblings term count (by simp only [length] at bound; omega)
          refine ⟨Θ', .under shorter, others, rest, by simp only [length]; omega, ?_⟩
          change lamT (inner.fillSource siblings term) = lamT (shorter.fillSource others rest)
          rw [same]

end Path

/-! ## The paths of each length -/

/-- Every path of length `count` from `Δ`. -/
def pathsOf : Nat → (Δ : Ctx sig) → List (Σ Θ : Ctx sig, Path Δ Θ)
  | 0, Δ => [⟨Δ, .here⟩]
  | count + 1, Δ =>
      (pathsOf count Δ).map (fun entry => ⟨entry.1, .left entry.2⟩) ++
        (pathsOf count Δ).map (fun entry => ⟨entry.1, .right entry.2⟩) ++
          (pathsOf count (.term :: Δ)).map (fun entry => ⟨entry.1, .under entry.2⟩)

theorem length_of_mem_pathsOf : ∀ (count : Nat) (Δ : Ctx sig) (entry : Σ Θ : Ctx sig, Path Δ Θ),
    entry ∈ pathsOf count Δ → entry.2.length = count
  | 0, _, entry, member => by
      rw [pathsOf, List.mem_singleton] at member
      subst member
      rfl
  | count + 1, Δ, entry, member => by
      simp only [pathsOf, List.mem_append, List.mem_map] at member
      rcases member with (⟨other, inner, rfl⟩ | ⟨other, inner, rfl⟩) | ⟨other, inner, rfl⟩
      · exact congrArg (· + 1) (length_of_mem_pathsOf count Δ other inner)
      · exact congrArg (· + 1) (length_of_mem_pathsOf count Δ other inner)
      · exact congrArg (· + 1) (length_of_mem_pathsOf count (.term :: Δ) other inner)

theorem mem_pathsOf {Δ Θ : Ctx sig} (path : Path Δ Θ) :
    (⟨Θ, path⟩ : Σ Θ : Ctx sig, Path Δ Θ) ∈ pathsOf path.length Δ := by
  induction path with
  | here => exact List.mem_singleton_self _
  | left inner ih =>
      simp only [Path.length, pathsOf, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨_, ih, rfl⟩)
  | right inner ih =>
      simp only [Path.length, pathsOf, List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨_, ih, rfl⟩)
  | under inner ih =>
      simp only [Path.length, pathsOf, List.mem_append, List.mem_map]
      exact Or.inr ⟨_, ih, rfl⟩

#print axioms plug_comp
#print axioms raiseAt_comp
#print axioms Path.toContext_plug
#print axioms plug_eq_fillSource
#print axioms raiseAt_eq_raiseAlong
#print axioms raiseAt_toContext
#print axioms raiseAlong_pattern
#print axioms Path.instantiate_fill
#print axioms Path.fill_include
#print axioms Path.fill_recovers
#print axioms Path.fill_pattern
#print axioms Path.length_lt_size
#print axioms Path.prefix_of_path
#print axioms length_of_mem_pathsOf
#print axioms mem_pathsOf

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Strategy
