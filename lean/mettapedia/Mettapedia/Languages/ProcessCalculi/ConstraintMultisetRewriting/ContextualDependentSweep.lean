import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentControls

/-!
# A sweep of small stores of the dynamic pattern fragment

**Problems as raw codes** (`Raw`, `Problem`). A problem names the declared types of its unknowns, oldest first, and
its equations: an annotation and two sides. `Problem.store?` scopes the codes, forms the context with the executable
type former, and checks both sides against the annotation with the executable checker; so every store it returns is
a store of typed equations of the tower, and an ill-scoped or ill-typed problem returns nothing.

**Membership in the fragment, decided** (`storeInside`). An executable test, sound for the dynamic pattern fragment
(`storeInside_sound`): equal annotation codes, a normal annotation, the binder count, and Miller occurrences at the
declared arities on the normalizer's normal form of each opened side.

**The verdict of a problem** (`Problem.verdict`): ill-typed, outside the fragment, or the ending of the compiled run
of the base family. A stuck verdict is a stuck run of the base family on a store of the fragment (`stuck_verdict`).

**The generators** (`genIn`, `gen`, `annotationsOf`, `sidesOf`): every β-normal raw code of a given size over a
given number of variables, with the universes `U0` and `U1` at every universe position (`gen`; `genIn` takes the
list of universes, and the raw codes have a third, `U2`); every formed normal annotation among them; and, for an
annotation, the typed sides among the abstractions of such codes, thinned by head form so that every head form
present is kept.

**The tally** (`sweep`): the count of every verdict, and for every stuck store of the fragment its family (the head
forms of the base type and of the two opened sides), with one witness per family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentEtaDepth
open ContextualDependentPatternSolver (lamDepth)

/-! ## Raw codes -/

/-- A code with unchecked variable indices. Index `0` is the newest variable. -/
inductive Raw where
  | var (index : Nat)
  | u0
  | pi (domain codomain : Raw)
  | sigma (first second : Raw)
  | id (type left right : Raw)
  | lam (body : Raw)
  | app (function argument : Raw)
  | pair (first second : Raw)
  | fst (inner : Raw)
  | snd (inner : Raw)
  | refl (point : Raw)
  | u1
  | u2
  deriving Repr, DecidableEq, Inhabited

namespace Raw

/-- The code over `n` variables, when every index is in scope. -/
def scope : (n : Nat) → Raw → Option (Tower.Tm n)
  | n, .var index => if inScope : index < n then some (.var ⟨index, inScope⟩) else none
  | _, .u0 => some (.head (.sort Tower.zero))
  | _, .u1 => some (.head (.sort (.succ Tower.zero)))
  | _, .u2 => some (.head (.sort (.succ (.succ Tower.zero))))
  | n, .pi domain codomain => do
      let domain ← scope n domain
      let codomain ← scope (n + 1) codomain
      pure (.pi domain codomain)
  | n, .sigma first second => do
      let first ← scope n first
      let second ← scope (n + 1) second
      pure (.sigma first second)
  | n, .id type left right => do
      let type ← scope n type
      let left ← scope n left
      let right ← scope n right
      pure (.id type left right)
  | n, .lam body => do
      let body ← scope (n + 1) body
      pure (.lam body)
  | n, .app function argument => do
      let function ← scope n function
      let argument ← scope n argument
      pure (.app function argument)
  | n, .pair first second => do
      let first ← scope n first
      let second ← scope n second
      pure (.pair first second)
  | n, .fst inner => do
      let inner ← scope n inner
      pure (.fst inner)
  | n, .snd inner => do
      let inner ← scope n inner
      pure (.snd inner)
  | n, .refl point => do
      let point ← scope n point
      pure (.refl point)

/-- The number of constructors. -/
def size : Raw → Nat
  | .var _ | .u0 | .u1 | .u2 => 1
  | .pi a b | .sigma a b | .app a b | .pair a b => size a + size b + 1
  | .id a b c => size a + size b + size c + 1
  | .lam a | .fst a | .snd a | .refl a => size a + 1

/-- A compact reading, with indices. -/
def toText : Raw → String
  | .var index => s!"{index}"
  | .u0 => "U"
  | .u1 => "U1"
  | .u2 => "U2"
  | .pi domain codomain => s!"(Π {toText domain}. {toText codomain})"
  | .sigma first second => s!"(Σ {toText first}. {toText second})"
  | .id type left right => s!"(Id {toText type} {toText left} {toText right})"
  | .lam body => s!"(λ {toText body})"
  | .app function argument => s!"({toText function} {toText argument})"
  | .pair first second => s!"<{toText first}, {toText second}>"
  | .fst inner => s!"(fst {toText inner})"
  | .snd inner => s!"(snd {toText inner})"
  | .refl point => s!"(refl {toText point})"

/-- `count` abstractions over a code. -/
def lams : Nat → Raw → Raw
  | 0, body => body
  | count + 1, body => .lam (lams count body)

/-- The number of leading Π binders. -/
def piCount : Raw → Nat
  | .pi _ codomain => piCount codomain + 1
  | _ => 0

/-- The code under its leading Π binders. -/
def piBase : Raw → Raw
  | .pi _ codomain => piBase codomain
  | other => other

/-- The number of leading abstractions. -/
def lamCount : Raw → Nat
  | .lam body => lamCount body + 1
  | _ => 0

/-- The code under its leading abstractions. -/
def lamBody : Raw → Raw
  | .lam body => lamBody body
  | other => other

/-- **The head form** of a code under `binders` bound variables: an introduction by its former, or a neutral by its
head (a bound local or an unknown) and its eliminations, innermost first. -/
def headForm (binders : Nat) : Raw → String
  | .var index => if index < binders then "local" else "unknown"
  | .u0 => "U"
  | .u1 => "U1"
  | .u2 => "U2"
  | .pi _ _ => "Π"
  | .sigma _ _ => "Σ"
  | .id _ _ _ => "Id"
  | .lam _ => "λ"
  | .pair _ _ => "pair"
  | .refl _ => "refl"
  | .app function _ => headForm binders function ++ ".app"
  | .fst inner => headForm binders inner ++ ".fst"
  | .snd inner => headForm binders inner ++ ".snd"

end Raw

/-! ## Problems -/

/-- The budget of the executable type former and checker that build a store. -/
def buildFuel : Nat := 32

/-- A formed type over a context, from a raw code. -/
def typeOf? (Γ : Context setting.R) (raw : Raw) : Option (TypeOver Γ) :=
  (raw.scope Γ.arity).bind fun code =>
    (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer buildFuel Γ code).map fun formed => formed.val

/-- A term over a context at a formed type, from a raw code. -/
def termOf? (Γ : Context setting.R) (type : TypeOver Γ) (raw : Raw) : Option (TotalTerm Γ) :=
  (raw.scope Γ.arity).bind fun code =>
    match ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer buildFuel Γ.raw code type.code with
    | some accepted =>
        some ⟨type, ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
          TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed accepted.down Γ.formed
          type.isType⟩⟩
    | none => none

/-- Extend a context by declared types, oldest first. -/
def contextFrom (Γ : Context setting.R) : List Raw → Option (Context setting.R)
  | [] => some Γ
  | raw :: rest => (typeOf? Γ raw).bind fun type => contextFrom (extend Γ type) rest

/-- **A problem**: the declared types of its unknowns, oldest first, and its equations (annotation, left, right). -/
structure Problem where
  unknowns : List Raw
  equations : List (Raw × Raw × Raw)
  deriving Repr, Inhabited

/-- A compact reading of a problem. -/
def Problem.toText (problem : Problem) : String :=
  "[" ++ ", ".intercalate (problem.unknowns.map Raw.toText) ++ "] ⊢ " ++
    " ; ".intercalate (problem.equations.map fun equation =>
      s!"{equation.2.1.toText} ≐ {equation.2.2.toText} : {equation.1.toText}")

/-- An equation over a context, from raw codes. -/
def equationOf? (Γ : Context setting.R) (equation : Raw × Raw × Raw) : Option (Equation (TotalTerm Γ)) :=
  (typeOf? Γ equation.1).bind fun type =>
    (termOf? Γ type equation.2.1).bind fun left =>
      (termOf? Γ type equation.2.2).map fun right => (left, right)

/-- The equations over a context, when every one is typed. -/
def storeOf? (Γ : Context setting.R) : List (Raw × Raw × Raw) → Option (EquationStore (TotalTerm Γ))
  | [] => some []
  | equation :: rest =>
      (equationOf? Γ equation).bind fun first => (storeOf? Γ rest).map fun others => first :: others

/-- **The typed store of a problem**, when its context is formed and its equations are typed. -/
def Problem.store? (problem : Problem) : Option (Σ Γ : Context setting.R, EquationStore (TotalTerm Γ)) :=
  (contextFrom (empty setting.R) problem.unknowns).bind fun Γ =>
    (storeOf? Γ problem.equations).map fun store => ⟨Γ, store⟩

/-! ## Membership in the fragment, decided -/

/-- The budget of the normalizer in the membership test. -/
def insideFuel : Nat := 64

/-- An opened side is in the fragment by the normalizer: it reaches a normal form with Miller occurrences at the
declared arities. -/
def sideInside {n : Nat} (context : Tower.Ctx n) (count : Nat) (code : Tower.Tm (n + count)) : Bool :=
  if finished : (ContextualDependentExecutableConversion.red (L := Nat) insideFuel code).isSome = true then
    (ExecutableReduction.step Tower.rules (fun _ => none)
        ((ContextualDependentExecutableConversion.red (L := Nat) insideFuel code).get finished).val).isNone &&
      decide (InFragmentCode context count
        ((ContextualDependentExecutableConversion.red (L := Nat) insideFuel code).get finished).val)
  else false

theorem sideInside_sound {n count : Nat} {context : Tower.Ctx n} {code : Tower.Tm (n + count)}
    (accepted : sideInside context count code = true) :
    ∀ normal, ContextualDependentExecutableJoin.Star (R := Tower.rules) code normal →
      ContextualDependentExecutableJoin.Normal Tower.rules normal → InFragmentCode context count normal := by
  unfold sideInside at accepted
  split at accepted
  · rename_i finished
    rw [Bool.and_eq_true] at accepted
    exact ContextualDependentDynamicFragment.Controls.side_by_normalizer insideFuel finished
      (Option.isNone_iff_eq_none.mp accepted.1) (of_decide_eq_true accepted.2)
  · cases accepted

/-- **The membership test of an equation.** -/
def equationInside {Γ : Context setting.R} (equation : Equation (TotalTerm Γ)) : Bool :=
  decide (equation.2.1.code = equation.1.1.code) &&
    (ExecutableReduction.step Tower.rules (fun _ => none) equation.1.1.code).isNone &&
    decide (lamDepth equation.1.2.code ≤ piCount equation.1.1.code) &&
    sideInside Γ.raw (lamDepth equation.1.2.code) (openCode (lamDepth equation.1.2.code) equation.1.2.code) &&
    sideInside Γ.raw (lamDepth equation.1.2.code) (openCode (lamDepth equation.1.2.code) equation.2.2.code)

/-- **The membership test is sound** for the dynamic pattern fragment. -/
theorem equationInside_sound {Γ : Context setting.R} {equation : Equation (TotalTerm Γ)}
    (accepted : equationInside equation = true) : InFragment equation := by
  unfold equationInside at accepted
  simp only [Bool.and_eq_true] at accepted
  obtain ⟨⟨⟨⟨same, normal⟩, depth⟩, left⟩, right⟩ := accepted
  refine ⟨?_, ?_, of_decide_eq_true depth, sideInside_sound left, sideInside_sound right⟩
  · rw [of_decide_eq_true same]
    exact IsType.refl equation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (Option.isNone_iff_eq_none.mp normal)

/-- **The membership test of a store.** -/
def storeInside {Γ : Context setting.R} (store : EquationStore (TotalTerm Γ)) : Bool :=
  store.all equationInside

theorem storeInside_sound {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (accepted : storeInside store = true) : InFragmentStore store := fun equation member =>
  equationInside_sound (List.all_eq_true.mp accepted equation member)

/-! ## Verdicts -/

/-- **The verdict of a problem.** -/
inductive Verdict where
  | illTyped
  | outside
  | ended (ending : Ending)
  deriving Repr, DecidableEq, Inhabited

/-- **Run the base family on a problem**, at a budget and a number of rounds. -/
def Problem.verdict (fuel rounds : Nat) (problem : Problem) : Verdict :=
  match problem.store? with
  | none => .illTyped
  | some ⟨Γ, store⟩ => if storeInside store then .ended (ending fuel rounds Γ store) else .outside

/-- **A stuck verdict is a stuck run of the base family on a store of the fragment.** -/
theorem stuck_verdict {fuel rounds : Nat} {problem : Problem}
    (stuck : problem.verdict fuel rounds = .ended .stuck) :
    ∃ (Γ : Context setting.R) (store : EquationStore (TotalTerm Γ)), problem.store? = some ⟨Γ, store⟩ ∧
      InFragmentStore store ∧ isStuck (run (baseTower.solver fuel) store rounds) = true := by
  unfold Problem.verdict at stuck
  cases built : problem.store? with
  | none => rw [built] at stuck; cases stuck
  | some pair =>
      obtain ⟨Γ, store⟩ := pair
      rw [built] at stuck
      by_cases inside : storeInside store = true
      · simp only [inside, if_true] at stuck
        exact ⟨Γ, store, rfl, storeInside_sound inside, stuck_of_ending (Verdict.ended.inj stuck)⟩
      · simp only [inside] at stuck
        cases stuck

/-! ## Generators -/

/-- The ways to write `total` as a sum of two positive numbers. -/
def splits (total : Nat) : List (Nat × Nat) :=
  (List.range total).filterMap fun first =>
    if 1 ≤ first ∧ first < total then some (first, total - first) else none

/-- **Every β-normal raw code of exactly `size` constructors over `vars` variables, with its universes among
`sorts`**; with `neutral`, only the neutral ones (a variable under applications and projections). The first number
bounds the recursion; `size` suffices. -/
def genIn (sorts : List Raw) : Nat → Bool → Nat → Nat → List Raw
  | 0, _, _, _ => []
  | fuel + 1, neutral, vars, size =>
      if size = 0 then []
      else
        let neutrals : List Raw :=
          (if size = 1 then (List.range vars).map Raw.var else []) ++
          ((genIn sorts fuel true vars (size - 1)).flatMap fun inner => [Raw.fst inner, Raw.snd inner]) ++
          ((splits (size - 1)).flatMap fun parts =>
            (genIn sorts fuel true vars parts.1).flatMap fun function =>
              (genIn sorts fuel false vars parts.2).map fun argument => Raw.app function argument)
        if neutral then neutrals
        else
          neutrals ++ (if size = 1 then sorts else []) ++
          ((genIn sorts fuel false (vars + 1) (size - 1)).map Raw.lam) ++
          ((genIn sorts fuel false vars (size - 1)).map Raw.refl) ++
          ((splits (size - 1)).flatMap fun parts =>
            (genIn sorts fuel false vars parts.1).flatMap fun first =>
              (genIn sorts fuel false vars parts.2).map fun second => Raw.pair first second) ++
          ((splits (size - 1)).flatMap fun parts =>
            (genIn sorts fuel false vars parts.1).flatMap fun domain =>
              (genIn sorts fuel false (vars + 1) parts.2).flatMap fun codomain =>
                [Raw.pi domain codomain, Raw.sigma domain codomain]) ++
          ((splits (size - 1)).flatMap fun parts =>
            (genIn sorts fuel false vars parts.1).flatMap fun type =>
              (splits parts.2).flatMap fun ends =>
                (genIn sorts fuel false vars ends.1).flatMap fun left =>
                  (genIn sorts fuel false vars ends.2).map fun right => Raw.id type left right)

/-- **The universes the generator writes**: `U0` and `U1`, at every position of a code. -/
def twoSorts : List Raw := [.u0, .u1]

/-- **Every β-normal raw code of exactly `size` constructors over `vars` variables**, with `U0` and `U1` at every
universe position. -/
def gen : Nat → Bool → Nat → Nat → List Raw := genIn twoSorts

/-- Every β-normal raw code of at most `size` constructors over `vars` variables, with its universes among `sorts`. -/
def genUpToIn (sorts : List Raw) (vars size : Nat) : List Raw :=
  (List.range (size + 1)).flatMap fun exact => genIn sorts exact false vars exact

/-- Every β-normal raw code of at most `size` constructors over `vars` variables, with `U0` and `U1`. -/
def genUpTo (vars size : Nat) : List Raw := genUpToIn twoSorts vars size

/-- **The formed normal annotations** among the β-normal raw codes of at most `size` constructors, with at most
`binders` leading Π binders. -/
def annotationsOf (Γ : Context setting.R) (size binders : Nat) : List Raw :=
  (genUpTo Γ.arity size).filter fun raw =>
    decide (raw.piCount ≤ binders) &&
      match typeOf? Γ raw with
      | none => false
      | some type => (ExecutableReduction.step Tower.rules (fun _ => none) type.code).isNone

/-- Keep at most `perForm` codes of each head form, and at most `cap` codes. -/
def thin (form : Raw → String) (perForm cap : Nat) (codes : List Raw) : List Raw :=
  let kept := codes.foldl (init := (([] : List Raw), ([] : List (String × Nat)))) fun state code =>
    let key := form code
    let seen := (state.2.lookup key).getD 0
    if seen < perForm then (code :: state.1, (key, seen + 1) :: state.2.filter fun entry => entry.1 != key)
    else state
  kept.1.reverse.take cap

/-- **The typed sides of an annotation**: abstractions of β-normal raw codes that check against it. Bodies under as
many abstractions as the annotation has Π binders have at most `bodySize` constructors; bodies under fewer, at most
`shortSize`. The sides are thinned by head form. -/
def sidesOf (Γ : Context setting.R) (annotation : Raw) (bodySize shortSize perForm cap : Nat) : List Raw :=
  match typeOf? Γ annotation with
  | none => []
  | some type =>
      let binders := annotation.piCount
      let candidates := (List.range (binders + 1)).reverse.flatMap fun depth =>
        (genUpTo (Γ.arity + depth) (if depth = binders then bodySize else shortSize)).filterMap fun body =>
          if body.lamCount = 0 then some (Raw.lams depth body) else none
      thin (fun side => s!"{side.lamCount}:{(side.lamBody).headForm side.lamCount}") perForm cap
        (candidates.filter fun side => (termOf? Γ type side).isSome)

/-! ## The tally -/

/-- **The family of a one-equation problem**: the head forms of the base type and of the two sides, each under its
own leading binders. -/
def equationFamily (equation : Raw × Raw × Raw) : String :=
  let annotation := equation.1
  s!"{annotation.piCount}Π {annotation.piBase.headForm annotation.piCount} | " ++
    s!"{equation.2.1.lamCount}λ {equation.2.1.lamBody.headForm equation.2.1.lamCount} | " ++
    s!"{equation.2.2.lamCount}λ {equation.2.2.lamBody.headForm equation.2.2.lamCount}"

/-- The family of a problem: the families of its equations. -/
def Problem.family (problem : Problem) : String :=
  " ; ".intercalate (problem.equations.map equationFamily)

/-- **The tally of a sweep.** -/
structure Tally where
  illTyped : Nat := 0
  outside : Nat := 0
  committed : Nat := 0
  refuted : Nat := 0
  stuck : Nat := 0
  cutoff : Nat := 0
  /-- The stuck families: the family, its count, and its first witness. -/
  families : List (String × Nat × Problem) := []
  deriving Inhabited

/-- Count one verdict. -/
def Tally.count (tally : Tally) (problem : Problem) : Verdict → Tally
  | .illTyped => { tally with illTyped := tally.illTyped + 1 }
  | .outside => { tally with outside := tally.outside + 1 }
  | .ended .committed => { tally with committed := tally.committed + 1 }
  | .ended .refuted => { tally with refuted := tally.refuted + 1 }
  | .ended .cutoff => { tally with cutoff := tally.cutoff + 1 }
  | .ended .stuck =>
      let key := problem.family
      let families := match tally.families.lookup key with
        | some (seen, witness) => (key, seen + 1, witness) :: tally.families.filter fun entry => entry.1 != key
        | none => (key, 1, problem) :: tally.families
      { tally with stuck := tally.stuck + 1, families := families }

/-- **Sweep a list of problems.** -/
def sweep (fuel rounds : Nat) (problems : List Problem) : Tally :=
  problems.foldl (init := {}) fun tally problem => tally.count problem (problem.verdict fuel rounds)

/-- A reading of a tally. -/
def Tally.toText (tally : Tally) : String :=
  s!"ill-typed {tally.illTyped}, outside {tally.outside}, committed {tally.committed}, refuted {tally.refuted}, " ++
    s!"stuck {tally.stuck}, cutoff {tally.cutoff}; stuck families {tally.families.length}\n" ++
    "\n".intercalate (tally.families.reverse.map fun entry =>
      s!"  [{entry.2.1}] {entry.1}\n      {entry.2.2.toText}")

/-- **The one-equation problems of a context**: every formed normal annotation of at most `typeSize` constructors
and `binders` Π binders, against every ordered pair of its thinned typed sides. -/
def problemsOf (unknowns : List Raw) (typeSize binders bodySize shortSize perForm cap : Nat) : List Problem :=
  match contextFrom (empty setting.R) unknowns with
  | none => []
  | some Γ =>
      (annotationsOf Γ typeSize binders).flatMap fun annotation =>
        let sides := sidesOf Γ annotation bodySize shortSize perForm cap
        sides.flatMap fun left => sides.map fun right =>
          { unknowns := unknowns, equations := [(annotation, left, right)] }

/-- The number of problems counted. -/
def Tally.total (tally : Tally) : Nat :=
  tally.illTyped + tally.outside + tally.committed + tally.refuted + tally.stuck + tally.cutoff

/-- **Sweep the one-equation problems of given annotations** against every ordered pair of their thinned typed
sides, without building the list of problems. -/
def sweepAnnotations (fuel rounds : Nat) (unknowns : List Raw) (Γ : Context setting.R) (annotations : List Raw)
    (bodySize shortSize perForm cap : Nat) (tally : Tally) : Tally :=
  annotations.foldl (init := tally) fun tally annotation =>
    let sides := sidesOf Γ annotation bodySize shortSize perForm cap
    sides.foldl (init := tally) fun tally left =>
      sides.foldl (init := tally) fun tally right =>
        let problem : Problem := { unknowns := unknowns, equations := [(annotation, left, right)] }
        tally.count problem (problem.verdict fuel rounds)

/-- The β-normal raw codes of at most `size` constructors over `vars` variables that are formed types once placed
by `place` over the context. -/
def formedTypes (Γ : Context setting.R) (place : Raw → Raw) (vars size : Nat) : List Raw :=
  (genUpTo vars size).filter fun raw => (typeOf? Γ (place raw)).isSome

/-- **Telescopic annotations** `Π (x : T₁) (y : T₂). B`: every formed choice of a first binder type of at most
`first` constructors, a second of at most `second`, and a base type of at most `base`. -/
def telescopes (Γ : Context setting.R) (first second base : Nat) : List Raw :=
  (formedTypes Γ id Γ.arity first).flatMap fun domain =>
    (formedTypes Γ (fun next => .pi domain (.pi next .u0)) (Γ.arity + 1) second).flatMap fun next =>
      (formedTypes Γ (fun result => .pi domain (.pi next result)) (Γ.arity + 2) base).map fun result =>
        .pi domain (.pi next result)

/-- Annotations with one binder `Π (x : T). B`. -/
def telescopesOne (Γ : Context setting.R) (first base : Nat) : List Raw :=
  (formedTypes Γ id Γ.arity first).flatMap fun domain =>
    (formedTypes Γ (fun result => .pi domain result) (Γ.arity + 1) base).map fun result => .pi domain result

/-! ## Elimination spines by shape -/

/-- Move every variable at or above `cutoff` up by one. -/
def Raw.shift (cutoff : Nat) : Raw → Raw
  | .var index => if index < cutoff then .var index else .var (index + 1)
  | .u0 => .u0
  | .u1 => .u1
  | .u2 => .u2
  | .pi domain codomain => .pi (shift cutoff domain) (shift (cutoff + 1) codomain)
  | .sigma first second => .sigma (shift cutoff first) (shift (cutoff + 1) second)
  | .id type left right => .id (shift cutoff type) (shift cutoff left) (shift cutoff right)
  | .lam body => .lam (shift (cutoff + 1) body)
  | .app function argument => .app (shift cutoff function) (shift cutoff argument)
  | .pair first second => .pair (shift cutoff first) (shift cutoff second)
  | .fst inner => .fst (shift cutoff inner)
  | .snd inner => .snd (shift cutoff inner)
  | .refl point => .refl (shift cutoff point)

/-- One elimination of a spine. -/
inductive Step where
  | app
  | fst
  | snd
  deriving Repr, DecidableEq, Inhabited

/-- **The type of a head** whose eliminations by `word`, innermost first, with arguments in `U`, end at `base`. -/
def spineType : List Step → Raw → Raw
  | [], base => base
  | .app :: rest, base => .pi .u0 ((spineType rest base).shift 0)
  | .fst :: rest, base => .sigma (spineType rest base) .u0
  | .snd :: rest, base => .sigma .u0 ((spineType rest base).shift 0)

/-- A head under the eliminations of `word`, innermost first, every application at `argument`. -/
def spineOf : List Step → Raw → Raw → Raw
  | [], head, _ => head
  | .app :: rest, head, argument => spineOf rest (.app head argument) argument
  | .fst :: rest, head, argument => spineOf rest (.fst head) argument
  | .snd :: rest, head, argument => spineOf rest (.snd head) argument

/-- Every word of eliminations of exactly `length` steps. -/
def words : Nat → List (List Step)
  | 0 => [[]]
  | length + 1 => (words length).flatMap fun word => [Step.app :: word, Step.fst :: word, Step.snd :: word]

/-- **The spine problems of a word and a base type.** Over the unknowns `A X` and `extra` later ones, at
`Π (G : U → U) (B : U) (g : T). base` with `T` the type that `word` eliminates to `base`: the two sides are
`λ G B g. g` under `word`, with the applications at `X` against `A`, at the local `B` against `A`, and at `X` on both
sides. `base` is given over the unknowns, `G` and `B`. -/
def spineProblems (unknowns : List Raw) (extra : Nat) (word : List Step) (base : Raw) : List Problem :=
  let annotation := Raw.pi (.pi .u0 .u0) (.pi .u0 (.pi (spineType word base) (base.shift 0)))
  let side := fun argument => Raw.lams 3 (spineOf word (.var 0) argument)
  let unknownX := Raw.var (extra + 3)
  let unknownA := Raw.var (extra + 4)
  [{ unknowns := unknowns, equations := [(annotation, side unknownX, side unknownA)] },
   { unknowns := unknowns, equations := [(annotation, side unknownA, side unknownX)] },
   { unknowns := unknowns, equations := [(annotation, side (.var 1), side unknownA)] },
   { unknowns := unknowns, equations := [(annotation, side unknownX, side unknownX)] }]

/-- A deterministic one-in-`modulus` sample of a list. -/
def sample {α : Type} (modulus seed : Nat) (items : List α) : List α :=
  (items.zipIdx.filter fun entry => ((entry.2 + seed) * 2654435761 % 4294967296) % modulus = 0).map fun entry =>
    entry.1

end ContextualDependentSweep
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
