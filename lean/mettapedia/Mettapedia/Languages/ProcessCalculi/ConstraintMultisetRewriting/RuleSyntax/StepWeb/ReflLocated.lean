import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflNameFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotientTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteHosting

/-!
# The located program, and its exact arrow at one location

REFL (`x?(P) → for(@P' <- x) 0` when `P → P'`) steps a quoted process in isolation. The hosting gives the
reflected process a **child location**: its rows are `P @ l`, a token admits one step there, its rows are then
cooled into one bag, and the bag is quoted back at the parent. This module gives the program, its exact arrow
at one location and its heating. That the token gives exactly one source step, that cooling packs the reduct,
and the REFL correspondence are not shown here.

## Locations are values

A row is `At(p, l)` (`atLoc p l`). Locations are values: the root `Root` (`rootLoc`) and, for the reflection
`x?(P)` at the location `m`, the child `Child(m, x, P)` (`childLoc m x P`). Rules mention location unknowns
`L`, `M`, which match these values. A location that were an unknown of the knowledge could be identified with
another one by a solution, so takes would merge locations and an absence at a location would see the rows of
the others (`ReflLocated.Controls.unknown_locations_merge`). The child location names its own reflection, so a
close can only put a child's result back into the reflection it came from.

## The program (`located`)

* **At the root**: the finite program of `FiniteComm` (comm, heat, clear) with every term of every rule in the
  context `At(·, Root)` (`atRule`, `rootRules`).
* **At a child** `L` of `M`, with the tokens `Pending(L, M)` (no step yet) and `Done(L, M, C)` (stepped,
  with the bag `C` cooled so far):
  * `commChild`: the comm rule at `L`, also taking `Pending(L, M)` and making `Done(L, M, 0)`: the one step;
  * `heatChild`: heating at `L`, only while `Pending(L, M)` is present (a read);
  * `cool`: takes `Done(L, M, C)` and a row `A @ L`, makes `Done(L, M, C | A)`: only after the step;
  * `closeRoot`: takes `x?(P) @ Root` and `Done(Child(Root, x, P), Root, C)`, asks that no row is at
    `Child(Root, x, P)`, makes `for(@C <- x) 0 @ Root`;
  * `closeChild`: the inner close at `L`: the same at the parent `L`, also taking `Pending(L, M)` and
    making `Done(L, M, 0)`: an inner REFL is the child's one step.
  A child whose reduct has no row closes with the accumulator `0`: that is close-empty.
* **Opening**: `openRoot` and `openChild` read `x?(P) @ M` (the latter also `Pending(M, M')`), ask that
  `Child(M, x, P)` has no token and no row, and make `P @ Child(M, x, P)` and `Pending(Child(M, x, P), M)`.

The step makes `Done(L, M, 0)` and cooling moves the rows into the token, because a check is asked against
the rows present before the firing, the taken ones included: a close that took the last row `C @ L` and asked
for no row at `L` would see `C @ L` itself (`ReflLocated.Controls.close_as_designed_refused`).

## The exact arrow at one location

For a frame action on patterns whose action is structural substitution, whose equality inverts the context
`At` and separates the heads of applications (`LocatedFrame`; instances at the syntactic frame, at `QX` and
at `QN`), and a location without variables `l`:

* **substitution**: `atMap l`, the context `At(·, l)` as a map of frame instances, reflecting the equality;
* **states**: `locate l`, the knowledge and the labels in the context;
* **steps**: `atFiring l`, the rule at the location, the same opening, selection and seen sets;
* **exact admission and results** (`atFiring_admits_iff`, `atFiring_result`): for every program, the firing at
  the location is admitted exactly when the firing is, and its result is the located result;
* **readouts** (`models_atStore`, `act_atLoc`): the same solutions, each row read in the context.

`conservative_at_root` (the obligation `ExactAtRoot`): at a state whose rows are all at the root, the located
program and the finite program correspond exactly: every firing of the finite program has its root firing,
admitted exactly when it is, with the located result (preservation); every admitted firing of the located
program other than `openRoot` is the root firing of an admitted firing of the finite program (reflection);
readouts commute. The other rules take or read a token, which no row of such a state is. `openRoot` is
excluded: it fires on a reflection at the root (`ReflLocated.Controls.open_fires_at_one_location`). On
transitions (`transitions_at_root`): the transitions of the located program without `openRoot` from such a
state are exactly the located transitions of the finite program. One location is needed
(`ReflLocated.Controls.two_locations_no_counterpart`). The location is a value: the arrow asks
`pvars l = []`.

The name frame lies strictly between the syntactic frame and `QX`, by identity maps of frame instances that do
not reflect (`syntacticToName`, `nameToBag`, `frame_maps_strict`).

## Heating at the name frame

At `QN` the spine is compared as written, so the heat rule takes exactly binary parallel compositions: every
solution of its information reads the taken row as `par a b` (`heat_takes_pair`); a row that reads at no
solution of the knowledge as such is never heated (`heat_refused`); a present row that reads so at a solution
is heated at every fresh opening with fresh made identities (`heat_admitted`); and a row that reads at every
solution as `par a b` is split into rows that read at every solution as `a` and `b`
(`heat_reads_determinately`). The same holds at the root through the arrow (`root_heat_reads_determinately`)
and at a child, where the read token is the child's `Pending` at every solution (`heatChild_takes_pair`,
`heatChild_refused`, `heatChild_admitted`, `heatChild_reads_determinately`). At `QX` no list of checks can do
this (`ReflLocated.Controls.no_check_guard_at_quotient`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocated

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar tProc pReflect)
open MeTTaOperationsComm (psubst psubst_none psubst_of_pvars_nil PSubst patternAction pvars)
open MeTTaCalculus.Corrected (psubstList_eq_map)
open FiniteProgram (commRule heatRule clearRule program mem_program program_finite heatRule_mem leftPart rightPart
  firstPattern secondPattern channelUnknown firstBody secondBody IsPar)
open Comm (Tm)
open OneFrame (embed)
open ReflQuotient (BagLaws bagAction bagLaws_iff bagCanon_apply QX)
open ReflNames (IsQuote NameLaws nameAction QN QNE nameLaws_heads nameLaws_apply_iff nameLaws_pair_left
  nameLaws_pair_iff)
open MeTTaCalculus.Corrected.BagControls (atomA atomB)
open LogicOverTheStep.StepSpan (Succ)

/-! ## Locations, rows and tokens -/

/-- **A row at a location**: `p @ l`. -/
def atLoc (p l : Pattern) : Pattern := .apply "At" [p, l]

/-- **The root location.** -/
def rootLoc : Pattern := .apply "Root" []

/-- **The child location** of the reflection `x?(P)` at the location `m`. -/
def childLoc (m x p : Pattern) : Pattern := .apply "Child" [m, x, p]

/-- The token of the child `l` of `m` before its step. -/
def pendingTok (l m : Pattern) : Pattern := .apply "Pending" [l, m]

/-- The token of the child `l` of `m` after its step, with the bag `c` cooled so far. -/
def doneTok (l m c : Pattern) : Pattern := .apply "Done" [l, m, c]

/-- The location unknowns of the rules, and the other unknowns of the child rules. -/
def locL : Pattern := .fvar "L"
def locM : Pattern := .fvar "M"
def reflP : Pattern := .fvar "P"
def accC : Pattern := .fvar "C"
def anyY : Pattern := .fvar "Y"
def anyZ : Pattern := .fvar "Z"

theorem pvars_rootLoc : pvars rootLoc = [] := rfl

theorem psubst_rootLoc (σ : PSubst) : psubst σ rootLoc = rootLoc := psubst_of_pvars_nil σ rootLoc rfl

/-! ## Rules, programs and states at a location -/

/-- Every term of an equation store in the context `At(·, l)`. -/
def atStore (l : Pattern) (K : EquationStore Pattern) : EquationStore Pattern :=
  K.map fun e => (atLoc e.1 l, atLoc e.2 l)

/-- **A rule at a location**: every term of the rule (takes, reads, tells, checks, made rows, collect query) in the
context `At(·, l)`. -/
def atRule (l : Pattern) (r : Rule Tm) : Rule Tm :=
  ⟨r.locals, r.body.map (fun t => atLoc t l), r.collect.map (fun t => atLoc t l)⟩

/-- A program at a location. -/
def atProgram (l : Pattern) (P : Program Tm) : Program Tm := atRule l '' P

/-- Labels at a location. -/
def atLabel {O : Type*} (l : Pattern) (label : O → Pattern) : O → Pattern := fun o => atLoc (label o) l

/-- A configuration at a location: its knowledge in the context. -/
def atConf {O : Type*} (l : Pattern) (C : Configuration Pattern O) : Configuration Pattern O :=
  ⟨atStore l C.equations, C.present⟩

/-- **A state at a location**: its knowledge and its labels in the context `At(·, l)`. -/
def locate {O : Type*} (l : Pattern) (s : State Tm O) : State Tm O :=
  ⟨s.frame, atStore l s.knowledge, s.present, atLabel l s.label⟩

theorem locate_embed {O : Type*} (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O) :
    locate l (embed label C) = embed (atLabel l label) (atConf l C) := rfl

/-! ## The located program -/

/-- **The root rules**: the finite program at the root. -/
def rootRules : Program Tm := atProgram rootLoc program

/-- **The step at a child**: comm at `L`, taking `Pending(L, M)` and making `Done(L, M, 0)`. -/
def commChild : Rule Tm :=
  ⟨PUnit.unit, ⟨[atLoc (pFor firstPattern channelUnknown firstBody) locL,
      atLoc (pFor secondPattern channelUnknown secondBody) locL, pendingTok locL locM], [],
    [(atLoc firstPattern locL, atLoc secondPattern locL)], [],
    [atLoc firstBody locL, atLoc secondBody locL, doneTok locL locM pZero]⟩, []⟩

/-- **Heating at a child**, only while its `Pending(L, M)` is present. -/
def heatChild : Rule Tm :=
  ⟨PUnit.unit, ⟨[atLoc (par leftPart rightPart) locL], [pendingTok locL locM], [], [],
    [atLoc leftPart locL, atLoc rightPart locL]⟩, []⟩

/-- **Cooling**, only after the step: one row of the child into the accumulator of `Done`. -/
def cool : Rule Tm :=
  ⟨PUnit.unit, ⟨[doneTok locL locM accC, atLoc leftPart locL], [], [], [],
    [doneTok locL locM (par accC leftPart)]⟩, []⟩

/-- **Close at the root**: the reflection `x?(P) @ Root` and the cooled bag of its child give
`for(@C <- x) 0 @ Root`, when no row is left at the child. -/
def closeRoot : Rule Tm :=
  ⟨PUnit.unit, ⟨[atLoc (pReflect channelUnknown reflP) rootLoc,
      doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC], [], [],
    [.predicate .none (atLoc anyY (childLoc rootLoc channelUnknown reflP))],
    [atLoc (pFor (tProc accC) channelUnknown pZero) rootLoc]⟩, []⟩

/-- **The inner close at a child** `L`: the same at the parent `L`, which is `L`'s one step. -/
def closeChild : Rule Tm :=
  ⟨PUnit.unit, ⟨[atLoc (pReflect channelUnknown reflP) locL,
      doneTok (childLoc locL channelUnknown reflP) locL accC, pendingTok locL locM], [], [],
    [.predicate .none (atLoc anyY (childLoc locL channelUnknown reflP))],
    [atLoc (pFor (tProc accC) channelUnknown pZero) locL, doneTok locL locM pZero]⟩, []⟩

/-- **Open at the root**: a child for the reflection `x?(P) @ Root`, when that child has no token and no row. -/
def openRoot : Rule Tm :=
  ⟨PUnit.unit, ⟨[], [atLoc (pReflect channelUnknown reflP) rootLoc], [],
    [.predicate .none (pendingTok (childLoc rootLoc channelUnknown reflP) rootLoc),
      .predicate .none (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc anyZ),
      .predicate .none (atLoc anyY (childLoc rootLoc channelUnknown reflP))],
    [atLoc reflP (childLoc rootLoc channelUnknown reflP), pendingTok (childLoc rootLoc channelUnknown reflP) rootLoc]⟩,
    []⟩

/-- **Open at a child** `L` before its step. -/
def openChild : Rule Tm :=
  ⟨PUnit.unit, ⟨[], [atLoc (pReflect channelUnknown reflP) locL, pendingTok locL locM], [],
    [.predicate .none (pendingTok (childLoc locL channelUnknown reflP) locL),
      .predicate .none (doneTok (childLoc locL channelUnknown reflP) locL anyZ),
      .predicate .none (atLoc anyY (childLoc locL channelUnknown reflP))],
    [atLoc reflP (childLoc locL channelUnknown reflP), pendingTok (childLoc locL channelUnknown reflP) locL]⟩, []⟩

/-- The rules at children. -/
def childRules : Program Tm := {commChild, heatChild, cool, closeRoot, closeChild}

/-- The opening rules. -/
def openRules : Program Tm := {openRoot, openChild}

/-- **The located program.** -/
def located : Program Tm := rootRules ∪ childRules ∪ openRules

theorem rootRules_sub : rootRules ⊆ located := fun _ member => .inl (.inl member)

theorem commChild_mem : commChild ∈ located := Or.inl (Or.inr (Set.mem_insert _ _))

theorem closeRoot_mem : closeRoot ∈ located :=
  Or.inl (Or.inr (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))

theorem openRoot_mem : openRoot ∈ located := Or.inr (Set.mem_insert _ _)

/-- **The located program is finite.** -/
theorem located_finite : located.Finite :=
  ((program_finite.image _).union
      (((((Set.finite_singleton closeChild).insert closeRoot).insert cool).insert heatChild).insert commChild)).union
    ((Set.finite_singleton openChild).insert openRoot)

theorem psubst_apply (σ : PSubst) (c : String) (args : List Pattern) :
    psubst σ (.apply c args) = .apply c (args.map (psubst σ)) := by
  simp only [psubst, psubstList_eq_map]

/-- Substitution acts inside the context of a location without variables. -/
theorem psubst_atLoc (σ : PSubst) (t : Pattern) {l : Pattern} (ground : pvars l = []) :
    psubst σ (atLoc t l) = atLoc (psubst σ t) l := by
  simp only [atLoc, psubst, psubstList_eq_map, List.map_cons, List.map_nil, psubst_of_pvars_nil σ l ground]

/-! ## What the arrow asks of a frame -/

/-- **A frame action for locations**: its action is structural substitution, its equality inverts the
context `At` and separates the heads of applications. -/
structure LocatedFrame (A : SubstitutionAction Pattern PSubst) : Prop where
  apply_eq : ∀ σ t, A.apply σ t = psubst σ t
  atLoc_iff : ∀ a b l l', A.E (atLoc a l) (atLoc b l') ↔ A.E a b ∧ A.E l l'
  heads : ∀ (c d : String) (xs ys : List Pattern), A.E (.apply c xs) (.apply d ys) → c = d

/-- The syntactic frame. -/
theorem locatedFrame_syntactic : LocatedFrame patternAction where
  apply_eq _ _ := rfl
  atLoc_iff a b l l' := by
    show atLoc a l = atLoc b l' ↔ a = b ∧ l = l'
    simp [atLoc]
  heads _ _ _ _ same := (Pattern.apply.inj same).1

/-- The frame modulo the bag laws, `QX`. -/
theorem locatedFrame_bag : LocatedFrame bagAction where
  apply_eq _ _ := rfl
  atLoc_iff a b l l' := by
    show BagLaws (atLoc a l) (atLoc b l') ↔ BagLaws a b ∧ BagLaws l l'
    simp only [bagLaws_iff, atLoc, bagCanon_apply, List.map_cons, List.map_nil, Pattern.apply.injEq,
      List.cons.injEq, and_true, true_and]
  heads c d xs ys same := by
    have canon := (bagLaws_iff _ _).mp same
    rw [bagCanon_apply, bagCanon_apply] at canon
    exact (Pattern.apply.inj canon).1

/-- The name frame, `QN`. -/
theorem locatedFrame_name : LocatedFrame nameAction where
  apply_eq _ _ := rfl
  atLoc_iff a b l l' := by
    show NameLaws (atLoc a l) (atLoc b l') ↔ NameLaws a b ∧ NameLaws l l'
    rw [atLoc, atLoc, nameLaws_apply_iff (by unfold IsQuote; decide)]
    simp
  heads _ _ _ _ same := nameLaws_heads same

/-! ## The name frame between the syntactic frame and `QX` -/

/-- The identity from the syntactic frame to the name frame: a map of frame instances. -/
def syntacticToName : Interface.Translation.FrameMap Comm.X QN where
  obj a := a
  tm t := t
  hom f := f
  act _ _ := ReflNames.NameLaws.refl _
  preserves same := ReflNames.nameLaws_of_eq same

/-- The identity from the name frame to the frame modulo the bag laws: a map of frame instances. -/
def nameToBag : Interface.Translation.FrameMap QN QX where
  obj a := a
  tm t := t
  hom f := f
  act _ _ := ReflQuotient.BagLaws.refl _
  preserves same := ReflNames.bagLaws_of_nameLaws same

/-- Neither map reflects: names are compared modulo the bag laws at `QN`, the spine only at `QX`. -/
theorem frame_maps_strict : ¬ syntacticToName.Reflects ∧ ¬ nameToBag.Reflects := by
  constructor
  · intro reflects
    have same : MeTTaCalculus.nQuote (par atomA atomB) = MeTTaCalculus.nQuote (par atomB atomA) :=
      reflects (a := PUnit.unit) ReflNames.names_modulo_bag_laws
    exact absurd same (by decide +kernel)
  · intro reflects
    exact ReflNames.spine_as_written (reflects (a := PUnit.unit) ReflNames.spine_related_at_bag_frame)

/-! ## The arrow at a location -/

section Arrow

variable {A : SubstitutionAction Pattern PSubst} (hA : LocatedFrame A) {O : Type*}

include hA in
/-- Substitution acts inside the context of a location without variables. -/
theorem act_atLoc (σ : PSubst) (t : Pattern) {l : Pattern} (ground : pvars l = []) :
    A.apply σ (atLoc t l) = atLoc (A.apply σ t) l := by
  rw [hA.apply_eq, hA.apply_eq]
  exact psubst_atLoc σ t ground

include hA in
/-- Equality in the context of one location is equality. -/
theorem atLoc_E_iff (a b l : Pattern) : A.E (atLoc a l) (atLoc b l) ↔ A.E a b :=
  (hA.atLoc_iff a b l l).trans ⟨fun h => h.1, fun h => ⟨h, A.equivalence.refl l⟩⟩

include hA in
/-- **Readouts**: a store at a location has the same solutions. -/
theorem models_atStore {l : Pattern} (ground : pvars l = []) (σ : PSubst) (K : EquationStore Pattern) :
    A.Models σ (atStore l K) ↔ A.Models σ K := by
  simp only [SubstitutionAction.Models, atStore, List.forall_mem_map, SubstitutionAction.Solves]
  refine forall₂_congr fun e _ => ?_
  rw [act_atLoc hA σ e.1 ground, act_atLoc hA σ e.2 ground]
  exact atLoc_E_iff hA _ _ l

/-- **The context of a location as a map of frame instances**: the same frames and substitutions, terms in
the context `At(·, l)`. -/
def atMap {l : Pattern} (ground : pvars l = []) :
    Interface.Translation.FrameMap (OneFrame.frames A) (OneFrame.frames A) where
  obj a := a
  tm t := atLoc t l
  hom f := f
  act f t := by
    show A.E (atLoc (A.apply f t) l) (A.apply f (atLoc t l))
    rw [act_atLoc hA f t ground]
    exact A.equivalence.refl _
  preserves same := (atLoc_E_iff hA _ _ l).mpr same

/-- **The map reflects the equality.** -/
theorem atMap_reflects {l : Pattern} (ground : pvars l = []) : (atMap hA ground).Reflects :=
  fun same => (atLoc_E_iff hA _ _ l).mp same

/-- **The firing at a location**: the rule at the location, the same extension, opening, selection and seen
sets. -/
def atFiring (l : Pattern) {P : Program Tm} {a : PUnit.{1}} (f : Firing O (OneFrame.ext A) P a) :
    Firing O (OneFrame.ext A) (atProgram l P) a :=
  ⟨atRule l f.rule, ⟨f.rule, f.member, rfl⟩, f.ext, f.opening, f.selection, f.seen⟩

/-- A firing of a smaller program is a firing of a larger one. -/
def widen {P Q : Program Tm} (sub : P ⊆ Q) {a : PUnit.{1}} (f : Firing O (OneFrame.ext A) P a) :
    Firing O (OneFrame.ext A) Q a :=
  ⟨f.rule, sub f.member, f.ext, f.opening, f.selection, f.seen⟩

omit hA in
theorem widen_admits_iff [DecidableEq O] {P Q : Program Tm} (sub : P ⊆ Q) {s : State Tm O}
    (f : Firing O (OneFrame.ext A) P s.frame) :
    (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) Q).Admits (s := s) (widen sub f) ↔
      (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) P).Admits (s := s) f := Iff.rfl

omit hA in
theorem widen_result [DecidableEq O] {P Q : Program Tm} (sub : P ⊆ Q) {s : State Tm O}
    (f : Firing O (OneFrame.ext A) P s.frame) :
    (widen sub f).result (OneFrame.frames A) s = f.result (OneFrame.frames A) s := rfl

omit hA in
theorem checkTerms_map (g : Pattern → Pattern) (c : Check Pattern) : checkTerms (c.map g) = (checkTerms c).map g := by
  cases c <;> rfl

omit hA in
/-- The terms of a rule at a location are its terms in the context. -/
theorem terms_atRule (l : Pattern) (r : Rule Tm) : (atRule l r).terms = r.terms.map (fun t => atLoc t l) := by
  simp only [Rule.terms, atRule, RuleInstance.map, List.map_append, List.map_map, List.map_flatMap,
    List.flatMap_map, checkTerms_map]
  rfl

omit hA in
theorem mentions_atLoc {l : Pattern} {label : O → Pattern} {C : Configuration Pattern O} {t : Pattern}
    (mentions : (embed label C).Mentions t) : (embed (atLabel l label) (atConf l C)).Mentions (atLoc t l) := by
  rcases mentions with known | known | ⟨o, present, same⟩
  · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp known
    exact .inl (List.mem_map.mpr ⟨(atLoc e.1 l, atLoc e.2 l), List.mem_map.mpr ⟨e, inside, rfl⟩, rfl⟩)
  · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp known
    exact .inr (.inl (List.mem_map.mpr ⟨(atLoc e.1 l, atLoc e.2 l), List.mem_map.mpr ⟨e, inside, rfl⟩, rfl⟩))
  · exact .inr (.inr ⟨o, present, by simp only [embed, atLabel]; rw [← same]; rfl⟩)

omit hA in
theorem mentions_of_atLoc {l : Pattern} {label : O → Pattern} {C : Configuration Pattern O} {t : Pattern}
    (mentions : (embed (atLabel l label) (atConf l C)).Mentions t) :
    ∃ t', (embed label C).Mentions t' ∧ t = atLoc t' l := by
  rcases mentions with known | known | ⟨o, present, rfl⟩
  · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp known
    obtain ⟨e₀, inside₀, rfl⟩ := List.mem_map.mp inside
    exact ⟨e₀.1, .inl (List.mem_map_of_mem inside₀), rfl⟩
  · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp known
    obtain ⟨e₀, inside₀, rfl⟩ := List.mem_map.mp inside
    exact ⟨e₀.2, .inr (.inl (List.mem_map_of_mem inside₀)), rfl⟩
  · exact ⟨label o, .inr (.inr ⟨o, present, rfl⟩), rfl⟩

include hA in
/-- **Freshness is the same at the location.** -/
theorem fresh_atFiring_iff {l : Pattern} (ground : pvars l = []) (label : O → Pattern)
    (C : Configuration Pattern O) {P : Program Tm} (f : Firing O (OneFrame.ext A) P PUnit.unit) :
    (atFiring l f).Fresh (OneFrame.frames A) (embed (atLabel l label) (atConf l C)) ↔
      f.Fresh (OneFrame.frames A) (embed label C) := by
  have unwrap : ∀ (u g : PSubst) (t : Pattern),
      A.E (A.apply u (A.apply A.identity (atLoc t l))) (A.apply g (atLoc t l)) ↔
        A.E (A.apply u (A.apply A.identity t)) (A.apply g t) := by
    intro u g t
    rw [A.apply_identity, A.apply_identity, act_atLoc hA u t ground, act_atLoc hA g t ground]
    exact atLoc_E_iff hA _ _ l
  have unwrapRule : ∀ (u h : PSubst) (t : Pattern),
      A.E (A.apply u (A.apply f.opening (atLoc t l))) (A.apply h (atLoc t l)) ↔
        A.E (A.apply u (A.apply f.opening t)) (A.apply h t) := by
    intro u h t
    rw [act_atLoc hA f.opening t ground, act_atLoc hA u _ ground, act_atLoc hA h t ground]
    exact atLoc_E_iff hA _ _ l
  constructor
  · intro fresh b g h
    obtain ⟨u, onState, onRule⟩ := fresh b g h
    refine ⟨u, fun t mentions => ?_, fun t member => ?_⟩
    · exact (unwrap u g t).mp (onState (atLoc t l) (mentions_atLoc mentions))
    · have inside : atLoc t l ∈ (atRule l f.rule).terms := by
        rw [terms_atRule]
        exact List.mem_map_of_mem member
      exact (unwrapRule u h t).mp (onRule (atLoc t l) inside)
  · intro fresh b g h
    obtain ⟨u, onState, onRule⟩ := fresh b g h
    refine ⟨u, fun t mentions => ?_, fun t member => ?_⟩
    · obtain ⟨t', mentions', rfl⟩ := mentions_of_atLoc mentions
      exact (unwrap u g t').mpr (onState t' mentions')
    · change t ∈ (atRule l f.rule).terms at member
      rw [terms_atRule] at member
      obtain ⟨t', inside, rfl⟩ := List.mem_map.mp member
      exact (unwrapRule u h t').mpr (onRule t' inside)

include hA in
/-- The opened rule at the location is the opened rule in the context. -/
theorem opened_atFiring {l : Pattern} (ground : pvars l = []) {P : Program Tm} (f : Firing O (OneFrame.ext A) P PUnit.unit) :
    (atFiring l f).opened (OneFrame.frames A) = (f.opened (OneFrame.frames A)).map (fun t => atLoc t l) := by
  have commute : ∀ t, A.apply f.opening (atLoc t l) = atLoc (A.apply f.opening t) l :=
    fun t => act_atLoc hA f.opening t ground
  have checkCommute : ∀ c : Check Pattern,
      (c.map fun t => atLoc t l).map (A.apply f.opening) = (c.map (A.apply f.opening)).map fun t => atLoc t l := by
    intro c
    cases c <;> simp [Check.map, commute]
  show (f.rule.body.map fun t => atLoc t l).map (A.apply f.opening) =
    (f.rule.body.map (A.apply f.opening)).map fun t => atLoc t l
  simp only [RuleInstance.map, List.map_map, Function.comp_def, commute, checkCommute]

omit hA in
theorem equations_atLoc (l : Pattern) (label : O → Pattern) :
    ∀ (ps : List Pattern) (os : List O),
      Selection.equations (atLabel l label) (ps.map fun t => atLoc t l) os =
        atStore l (Selection.equations label ps os)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, o :: os => by
      simp only [Selection.equations, List.map_cons, List.zipWith_cons_cons, atStore, atLabel] at *
      exact congrArg _ (equations_atLoc l label ps os)

include hA in
/-- **The information at the location is the information in the context.** -/
theorem information_atFiring {l : Pattern} (ground : pvars l = []) (label : O → Pattern)
    (C : Configuration Pattern O) {P : Program Tm} (f : Firing O (OneFrame.ext A) P PUnit.unit) :
    (atFiring l f).information (OneFrame.frames A) (embed (atLabel l label) (atConf l C)) =
      atStore l (f.information (OneFrame.frames A) (embed label C)) := by
  rw [OneFrame.information_eq, OneFrame.information_eq, opened_atFiring hA ground]
  show Selection.problem f.selection (atLabel l label) ((f.opened (OneFrame.frames A)).map fun t => atLoc t l)
      (atConf l C) = atStore l (Selection.problem f.selection label (f.opened (OneFrame.frames A)) C)
  simp only [Selection.problem, atConf, RuleInstance.map, equations_atLoc, atStore, List.map_append]

omit hA in
theorem relabel_atLoc [DecidableEq O] (l : Pattern) (old : O → Pattern) :
    ∀ (made : List O) (rows : List Pattern),
      relabel (Tm := Tm) (a := PUnit.unit) (atLabel l old) made (rows.map fun t => atLoc t l) =
        atLabel l (relabel (Tm := Tm) (a := PUnit.unit) old made rows)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | o' :: rest, t :: ts => by
      funext o
      simp only [List.map_cons, relabel, atLabel]
      split_ifs
      · rfl
      · exact congrFun (relabel_atLoc l old rest ts) o

include hA in
/-- **The result at the location is the located result.** -/
theorem atFiring_result [DecidableEq O] {l : Pattern} (ground : pvars l = []) (label : O → Pattern)
    (C : Configuration Pattern O) {P : Program Tm} (f : Firing O (OneFrame.ext A) P PUnit.unit) :
    (atFiring l f).result (OneFrame.frames A) (embed (atLabel l label) (atConf l C)) =
      locate l (f.result (OneFrame.frames A) (embed label C)) := by
  unfold Firing.result
  rw [information_atFiring hA ground, OneFrame.row_eq, OneFrame.row_eq, opened_atFiring hA ground]
  simp only [locate, RuleInstance.map]
  rw [relabel_atLoc]
  rfl

include hA in
/-- A collect query or count at the location sees the same rows. -/
theorem matchesAt_atLoc {l : Pattern} (ground : pvars l = []) {σ : PSubst} {label : O → Pattern}
    {present : Finset O} {p : Pattern} :
    matchesAt (OneFrame.frames A) (a := PUnit.unit) (b := PUnit.unit) σ (atLabel l label) present (atLoc p l) =
      matchesAt (OneFrame.frames A) (a := PUnit.unit) (b := PUnit.unit) σ label present p := by
  ext o
  rw [mem_matchesAt, mem_matchesAt]
  refine and_congr_right fun _ => ?_
  show A.E (A.apply σ (atLoc p l)) (A.apply σ (atLoc (label o) l)) ↔ A.E (A.apply σ p) (A.apply σ (label o))
  rw [act_atLoc hA σ _ ground, act_atLoc hA σ _ ground]
  exact atLoc_E_iff hA _ _ l

include hA in
/-- Checks are asked the same way at the location. -/
theorem checkHolds_atLoc {l : Pattern} (ground : pvars l = []) (σ : PSubst) (label : O → Pattern)
    (present : Finset O) (c : Check Pattern) :
    checkHolds (OneFrame.frames A) (a := PUnit.unit) (b := PUnit.unit) σ (atLabel l label) present
        (c.map fun t => atLoc t l) ↔
      checkHolds (OneFrame.frames A) (a := PUnit.unit) (b := PUnit.unit) σ label present c := by
  have unwrap : ∀ x y : Pattern, A.E (A.apply σ (atLoc x l)) (A.apply σ (atLoc y l)) ↔
      A.E (A.apply σ x) (A.apply σ y) := by
    intro x y
    rw [act_atLoc hA σ x ground, act_atLoc hA σ y ground]
    exact atLoc_E_iff hA _ _ l
  cases c with
  | equal x y => exact unwrap x y
  | predicate quantifier p =>
      show quantifier.Holds present _ ↔ quantifier.Holds present _
      exact quantifier.holds_congr fun o _ => unwrap p (label o)
  | count p n =>
      show (matchesAt (OneFrame.frames A) (a := PUnit.unit) (b := PUnit.unit) σ (atLabel l label) present
          (atLoc p l)).card = n ↔
        (matchesAt (OneFrame.frames A) (a := PUnit.unit) (b := PUnit.unit) σ label present p).card = n
      rw [matchesAt_atLoc hA ground]

include hA in
/-- **Exact admission at the location**: the firing at the location is admitted exactly when the firing is,
for every program, every state and every firing (checks and collect query included). -/
theorem atFiring_admits_iff [DecidableEq O] {l : Pattern} (ground : pvars l = []) (label : O → Pattern)
    (C : Configuration Pattern O) {P : Program Tm} (f : Firing O (OneFrame.ext A) P PUnit.unit) :
    (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) (atProgram l P)).Admits
        (s := embed (atLabel l label) (atConf l C)) (atFiring l f) ↔
      (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) P).Admits (s := embed label C) f := by
  have models : ∀ σ : PSubst, A.Models σ (atStore l (f.information (OneFrame.frames A) (embed label C))) ↔
      A.Models σ (f.information (OneFrame.frames A) (embed label C)) :=
    fun σ => models_atStore hA ground σ _
  have lengths : (atFiring l f).rule.body.take.length = f.rule.body.take.length ∧
      (atFiring l f).rule.body.read.length = f.rule.body.read.length ∧
      (atFiring l f).rule.body.produce.length = f.rule.body.produce.length ∧
      (atFiring l f).rule.collect.length = f.rule.collect.length := by
    simp [atFiring, atRule, RuleInstance.map]
  have collect : (atFiring l f).collectOpened (OneFrame.frames A) =
      (f.collectOpened (OneFrame.frames A)).map fun t => atLoc t l := by
    show (f.rule.collect.map fun t => atLoc t l).map (A.apply f.opening) =
      (f.rule.collect.map (A.apply f.opening)).map fun t => atLoc t l
    simp only [List.map_map, Function.comp_def, act_atLoc hA f.opening _ ground]
  rw [RuleSyntax.admits_iff, RuleSyntax.admits_iff, fresh_atFiring_iff hA ground, information_atFiring hA ground,
    OneFrame.row_eq, OneFrame.row_eq, opened_atFiring hA ground, collect, lengths.1, lengths.2.1, lengths.2.2.1,
    lengths.2.2.2]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ (and_congr ?_ ?_))))
  · exact ⟨fun ⟨b, σ, solved⟩ => ⟨b, σ, (models σ).mp solved⟩, fun ⟨b, σ, solved⟩ => ⟨b, σ, (models σ).mpr solved⟩⟩
  · simp only [RuleInstance.map, List.forall_mem_map]
    exact forall₂_congr fun c _ =>
      ⟨fun asked b σ solved => (checkHolds_atLoc hA ground σ label C.present c).mp (asked b σ ((models σ).mpr solved)),
        fun asked b σ solved => (checkHolds_atLoc hA ground σ label C.present c).mpr (asked b σ ((models σ).mp solved))⟩
  · rw [List.zip_map_left, List.forall_mem_map]
    refine forall₂_congr fun q _ => ⟨fun asked b σ solved => ?_, fun asked b σ solved => ?_⟩
    · have seen := asked b σ ((models σ).mpr solved)
      simp only [Prod.map_fst, Prod.map_snd, id_eq] at seen
      rw [← seen]
      exact (matchesAt_atLoc hA ground).symm
    · have seen := asked b σ ((models σ).mp solved)
      simp only [Prod.map_fst, Prod.map_snd, id_eq]
      rw [← seen]
      exact matchesAt_atLoc hA ground

end Arrow

/-! ## Conservativity at the root -/

section Root

variable {A : SubstitutionAction Pattern PSubst} (hA : LocatedFrame A) {O : Type*}

/-- A state whose rows are all at the root. -/
abbrev rootState (label : O → Pattern) (C : Configuration Pattern O) : State Tm O :=
  embed (atLabel rootLoc label) (atConf rootLoc C)

/-- **The root firing** of a firing of the finite program. -/
def rootFiring {a : PUnit.{1}} (f : Firing O (OneFrame.ext A) program a) : Firing O (OneFrame.ext A) located a :=
  widen rootRules_sub (atFiring rootLoc f)

/-- Lists of one length: every member of the first is zipped with a member of the second. -/
theorem exists_mem_zip {α β : Type*} : ∀ {xs : List α} {ys : List β}, xs.length = ys.length →
    ∀ {x : α}, x ∈ xs → ∃ y, (x, y) ∈ xs.zip ys
  | [], _, _, _, member => absurd member List.not_mem_nil
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | x' :: xs, y' :: ys, lengths, x, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨y', by simp⟩
      · obtain ⟨y, inside⟩ := exists_mem_zip (Nat.succ.inj lengths) later
        exact ⟨y, List.mem_cons_of_mem _ inside⟩

include hA in
/-- An opened application read through a solution keeps its head. -/
theorem head_of_solved {σ ρ : PSubst} {c d : String} {args args' : List Pattern}
    (equal : A.E (A.apply σ (A.apply ρ (.apply c args))) (A.apply σ (.apply d args'))) : c = d := by
  rw [hA.apply_eq, hA.apply_eq, hA.apply_eq] at equal
  simp only [psubst] at equal
  exact hA.heads _ _ _ _ equal

include hA in
/-- **A take of a token is refused at a located state**: a firing one of whose take patterns is an
application whose head is not `At` is never admitted where every row is a row at a location. -/
theorem refused_of_take [DecidableEq O] {l : Pattern} (label : O → Pattern) (C : Configuration Pattern O)
    {P : Program Tm} (g : Firing O (OneFrame.ext A) P PUnit.unit) {c : String} {args : List Pattern}
    (head : c ≠ "At") (inside : Pattern.apply c args ∈ g.rule.body.take) :
    ¬ (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) P).Admits
      (s := embed (atLabel l label) (atConf l C)) g := by
  intro admitted
  obtain ⟨_, shapes, _, ⟨_, σ, solved⟩, _, _⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨o, zipped⟩ := exists_mem_zip shapes.2.2.1 inside
  have openedZip : ((OneFrame.frames A).act (a := PUnit.unit) (b := PUnit.unit) g.opening (.apply c args), o) ∈
      (g.opened (OneFrame.frames A)).take.zip g.selection.taken := by
    show _ ∈ (g.rule.body.take.map _).zip _
    rw [List.zip_map_left]
    exact List.mem_map.mpr ⟨_, zipped, rfl⟩
  have equal := g.take_solved solved openedZip
  rw [OneFrame.row_eq] at equal
  exact head (head_of_solved hA (args' := [label o, l]) equal)

include hA in
/-- **A read of a token is refused at a located state**, in the same way. -/
theorem refused_of_read [DecidableEq O] {l : Pattern} (label : O → Pattern) (C : Configuration Pattern O)
    {P : Program Tm} (g : Firing O (OneFrame.ext A) P PUnit.unit) {c : String} {args : List Pattern}
    (head : c ≠ "At") (inside : Pattern.apply c args ∈ g.rule.body.read) :
    ¬ (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) P).Admits
      (s := embed (atLabel l label) (atConf l C)) g := by
  intro admitted
  obtain ⟨_, shapes, _, ⟨_, σ, solved⟩, _, _⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨o, zipped⟩ := exists_mem_zip shapes.2.2.2.1 inside
  have openedZip : ((OneFrame.frames A).act (a := PUnit.unit) (b := PUnit.unit) g.opening (.apply c args), o) ∈
      (g.opened (OneFrame.frames A)).read.zip g.selection.read := by
    show _ ∈ (g.rule.body.read.map _).zip _
    rw [List.zip_map_left]
    exact List.mem_map.mpr ⟨_, zipped, rfl⟩
  have equal := g.read_solved solved openedZip
  rw [OneFrame.row_eq] at equal
  exact head (head_of_solved hA (args' := [label o, l]) equal)

include hA in
/-- **Preservation at the root**: the root firing is admitted exactly when the firing of the finite program
is, and its result is the located result. -/
theorem root_preserves [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (f : Firing O (OneFrame.ext A) program PUnit.unit) :
    ((RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) located).Admits (s := rootState label C)
        (rootFiring f) ↔
      (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) program).Admits (s := embed label C) f) ∧
      (rootFiring f).result (OneFrame.frames A) (rootState label C) =
        locate rootLoc (f.result (OneFrame.frames A) (embed label C)) :=
  ⟨(widen_admits_iff rootRules_sub _).trans (atFiring_admits_iff hA pvars_rootLoc label C f),
    atFiring_result hA pvars_rootLoc label C f⟩

include hA in
/-- **Reflection at the root**: at a state whose rows are all at the root, every admitted firing of the
located program other than `openRoot` is the root firing of an admitted firing of the finite program. -/
theorem root_reflects [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (g : Firing O (OneFrame.ext A) located PUnit.unit) (notOpen : g.rule ≠ openRoot)
    (admitted : (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) located).Admits (s := rootState label C) g) :
    ∃ f : Firing O (OneFrame.ext A) program PUnit.unit, g = rootFiring f ∧
      (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) program).Admits (s := embed label C) f := by
  obtain ⟨rule, member, ext, opening, selection, seen⟩ := g
  rcases (Set.mem_union _ _ _).mp member with front | openRule
  · rcases (Set.mem_union _ _ _).mp front with root | childRule
    · obtain ⟨r, rMember, rfl⟩ := (Set.mem_image _ _ _).mp root
      let f : Firing O (OneFrame.ext A) program PUnit.unit := ⟨r, rMember, ext, opening, selection, seen⟩
      exact ⟨f, rfl, (root_preserves hA label C f).1.mp admitted⟩
    · exfalso
      simp only [childRules, Set.mem_insert_iff, Set.mem_singleton_iff] at childRule
      rcases childRule with rfl | rfl | rfl | rfl | rfl
      · exact refused_of_take hA label C _ (c := "Pending") (args := [locL, locM]) (by decide)
          (by simp [commChild, pendingTok]) admitted
      · exact refused_of_read hA label C _ (c := "Pending") (args := [locL, locM]) (by decide)
          (by simp [heatChild, pendingTok]) admitted
      · exact refused_of_take hA label C _ (c := "Done") (args := [locL, locM, accC]) (by decide)
          (by simp [cool, doneTok]) admitted
      · exact refused_of_take hA label C _ (c := "Done")
          (args := [childLoc rootLoc channelUnknown reflP, rootLoc, accC]) (by decide)
          (by simp [closeRoot, doneTok]) admitted
      · exact refused_of_take hA label C _ (c := "Done")
          (args := [childLoc locL channelUnknown reflP, locL, accC]) (by decide)
          (by simp [closeChild, doneTok]) admitted
  · exfalso
    simp only [openRules, Set.mem_insert_iff, Set.mem_singleton_iff] at openRule
    rcases openRule with rfl | rfl
    · exact notOpen rfl
    · exact refused_of_read hA label C _ (c := "Pending") (args := [locL, locM]) (by decide)
        (by simp [openChild, pendingTok]) admitted

end Root

/-- **The obligation of an exact arrow at the root.** With the maps `atLabel`/`atConf` on states,
`rootFiring` on firings and the context `At(·, Root)` on terms (`atMap`):
* preservation: every firing of the finite program has its root firing, admitted exactly when it is, with
  the located result;
* reflection: every admitted firing of the located program other than `openRoot` is the root firing of an
  admitted firing of the finite program;
* readouts: the knowledge has the same solutions, and each row reads in the context of the root. -/
def ExactAtRoot (A : SubstitutionAction Pattern PSubst) (O : Type*) [DecidableEq O] (label : O → Pattern)
    (C : Configuration Pattern O) : Prop :=
  (∀ f : Firing O (OneFrame.ext A) program PUnit.unit,
    ((RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) located).Admits (s := rootState label C)
        (rootFiring f) ↔
      (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) program).Admits (s := embed label C) f) ∧
    (rootFiring f).result (OneFrame.frames A) (rootState label C) =
      locate rootLoc (f.result (OneFrame.frames A) (embed label C))) ∧
  (∀ g : Firing O (OneFrame.ext A) located PUnit.unit, g.rule ≠ openRoot →
    (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) located).Admits (s := rootState label C) g →
      ∃ f : Firing O (OneFrame.ext A) program PUnit.unit, g = rootFiring f ∧
        (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) program).Admits (s := embed label C) f) ∧
  (∀ σ : PSubst, A.Models σ (rootState label C).knowledge ↔ A.Models σ C.equations) ∧
  ∀ (σ : PSubst) (o : O), A.apply σ ((rootState label C).label o) = atLoc (A.apply σ (label o)) rootLoc

/-- **Conservativity at one location, an exact arrow**, at every frame for locations. -/
theorem conservative_at_root {A : SubstitutionAction Pattern PSubst} (hA : LocatedFrame A) {O : Type*}
    [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) : ExactAtRoot A O label C :=
  ⟨root_preserves hA label C, root_reflects hA label C, fun σ => models_atStore hA pvars_rootLoc σ C.equations,
    fun σ o => act_atLoc hA σ (label o) pvars_rootLoc⟩

/-- **The exact arrow at `QX`.** -/
theorem conservative_at_root_QX {O : Type*} [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) :
    ExactAtRoot bagAction O label C :=
  conservative_at_root locatedFrame_bag label C

/-- **The exact arrow at `QN`.** -/
theorem conservative_at_root_QN {O : Type*} [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) :
    ExactAtRoot nameAction O label C :=
  conservative_at_root locatedFrame_name label C

/-- **The exact arrow at the syntactic frame.** -/
theorem conservative_at_root_syntactic {O : Type*} [DecidableEq O] (label : O → Pattern)
    (C : Configuration Pattern O) : ExactAtRoot patternAction O label C :=
  conservative_at_root locatedFrame_syntactic label C

/-- **`openRoot` is no root rule.** -/
theorem openRoot_not_root : openRoot ∉ rootRules := by
  rintro ⟨r, member, same⟩
  rcases mem_program.mp member with rfl | rfl | rfl <;>
    simp [atRule, openRoot, commRule, heatRule, clearRule, RuleInstance.map] at same

/-- The step of the located program without opening at the root. -/
def locatedNoOpen (A : SubstitutionAction Pattern PSubst) (O : Type*) [DecidableEq O] :
    Interface.Step (OneFrame.frames A) O (State Tm O) (fun s => Firing O (OneFrame.ext A) located s.frame) :=
  Spaces.restrict (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) located).toStep
    (fun {_} g => g.rule ≠ openRoot)

/-- **The transitions correspond at one location**: at a state whose rows are all at the root, the transitions
of the located program without opening are exactly the located transitions of the finite program. -/
theorem transitions_at_root {A : SubstitutionAction Pattern PSubst} (hA : LocatedFrame A) {O : Type*}
    [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (s' : State Tm O) :
    Succ (locatedNoOpen A O) (rootState label C) s' ↔
      ∃ s'' : State Tm O, Succ (RuleSyntax.step (OneFrame.frames A) O (OneFrame.ext A) program).toStep
        (embed label C) s'' ∧ s' = locate rootLoc s'' := by
  constructor
  · rintro ⟨g, ⟨admitted, notOpen⟩, rfl⟩
    obtain ⟨f, rfl, fAdmitted⟩ := root_reflects hA label C g notOpen admitted
    exact ⟨f.result (OneFrame.frames A) (embed label C), ⟨f, fAdmitted, rfl⟩,
      (root_preserves hA label C f).2⟩
  · rintro ⟨_, ⟨f, fAdmitted, rfl⟩, rfl⟩
    refine ⟨rootFiring f, ⟨(root_preserves hA label C f).1.mpr fAdmitted, fun same => ?_⟩,
      (root_preserves hA label C f).2⟩
    exact openRoot_not_root (same ▸ ⟨f.rule, f.member, rfl⟩)

/-! ## Heating at the name frame -/

section Heat

variable {O : Type*}

/-- The heating firing of the finite program at the name frame: take `o`, make `m₁` and `m₂`. -/
def heatN (ρ : PSubst) (o m₁ m₂ : O) : Firing O QNE program PUnit.unit :=
  ⟨heatRule, heatRule_mem, PUnit.unit, ρ, ⟨[o], [], [m₁, m₂]⟩, []⟩

theorem heatN_information (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst) (o m₁ m₂ : O) :
    (heatN ρ o m₁ m₂).information QN (embed label C) =
      C.equations ++ [(psubst ρ (par leftPart rightPart), label o)] ++ [] ++ [] := by
  rw [OneFrame.information_eq]
  rfl

theorem heatN_label₁ [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (o m₁ m₂ : O) : ((heatN ρ o m₁ m₂).result QN (embed label C)).label m₁ = psubst ρ leftPart := by
  show (if m₁ = m₁ then psubst ρ leftPart else _) = _
  rw [if_pos rfl]

theorem heatN_label₂ [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst) (o : O)
    {m₁ m₂ : O}
    (madeDistinct : m₁ ≠ m₂) : ((heatN ρ o m₁ m₂).result QN (embed label C)).label m₂ = psubst ρ rightPart := by
  show (if m₂ = m₁ then _ else if m₂ = m₂ then psubst ρ rightPart else _) = _
  rw [if_neg (Ne.symm madeDistinct), if_pos rfl]

theorem psubst_par (σ : PSubst) (a b : Pattern) : psubst σ (par a b) = par (psubst σ a) (psubst σ b) := by
  simp only [par, pPar, psubst, psubstList_eq_map, List.map_cons, List.map_nil]

/-- **At every solution of its information, heating takes a binary parallel composition**, whose members
read as the made rows' patterns. -/
theorem heat_takes_pair (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst) (o m₁ m₂ : O)
    {σ : PSubst} (solved : nameAction.Models σ ((heatN ρ o m₁ m₂).information QN (embed label C))) :
    ∃ a b : Pattern, psubst σ (label o) = par a b ∧ NameLaws (psubst σ (psubst ρ leftPart)) a ∧
      NameLaws (psubst σ (psubst ρ rightPart)) b := by
  rw [heatN_information] at solved
  have take : NameLaws (psubst σ (psubst ρ (par leftPart rightPart))) (psubst σ (label o)) :=
    solved (psubst ρ (par leftPart rightPart), label o) (by simp)
  rw [psubst_par, psubst_par] at take
  exact nameLaws_pair_left take

/-- **Heating fires only on binary parallel compositions**: an admitted heating has a solution of the
knowledge at which the taken row is `par a b`. -/
theorem heat_admitted_takes_pair [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (o m₁ m₂ : O)
    (admitted : (RuleSyntax.step QN O QNE program).Admits (s := embed label C) (heatN ρ o m₁ m₂)) :
    ∃ σ : PSubst, nameAction.Models σ C.equations ∧ IsPar (psubst σ (label o)) := by
  obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  obtain ⟨a, b, same, -, -⟩ := heat_takes_pair label C ρ o m₁ m₂ solved
  refine ⟨σ, fun e member => ?_, a, b, same⟩
  have whole := solved
  rw [heatN_information] at whole
  exact whole e (by simp [member])

/-- **A row that reads as no binary parallel composition is never heated**, at any opening. -/
theorem heat_refused [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (o m₁ m₂ : O)
    (notPar : ∀ σ : PSubst, nameAction.Models σ C.equations → ¬ IsPar (psubst σ (label o))) (ρ : PSubst) :
    ¬ (RuleSyntax.step QN O QNE program).Admits (s := embed label C) (heatN ρ o m₁ m₂) := by
  intro admitted
  obtain ⟨σ, known, pair⟩ := heat_admitted_takes_pair label C ρ o m₁ m₂ admitted
  exact notPar σ known pair

/-- **A row that reads as a binary parallel composition at a solution is heated** at every fresh opening. -/
theorem heat_admitted [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (o m₁ m₂ : O)
    (present : o ∈ C.present) (madeDistinct : m₁ ≠ m₂) (fresh₁ : m₁ ∉ C.present) (fresh₂ : m₂ ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations) {a b : Pattern}
    (pair : NameLaws (psubst σ₀ (label o)) (par a b))
    {ρ : PSubst} (opensFreshly : (heatN ρ o m₁ m₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE program).Admits (s := embed label C) (heatN ρ o m₁ m₂) := by
  let h : PSubst := fun v => if v = "A" then some a else if v = "B" then some b else none
  have split : psubst h (par leftPart rightPart) = par a b := by
    rw [psubst_par]
    rfl
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (heatN ρ o m₁ m₂) opensFreshly (b := PUnit.unit) σ₀ h known
    (fun _ member => (List.not_mem_nil member).elim)
    (fun o' member => by
      obtain rfl := List.mem_singleton.mp member
      exact present)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      obtain rfl := List.mem_singleton.mp member
      show NameLaws (psubst h (par leftPart rightPart)) (psubst σ₀ (label o))
      rw [split]
      exact pair.symm)
    (fun _ member => (List.not_mem_nil member).elim)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [heatN], by simp [heatN, madeDistinct], rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩
  · intro o' member
    simp only [heatN, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    exact present
  · intro o' member
    simp [heatN, Selection.commit] at member
  · simp [heatN, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o' member
    simp only [heatN, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact fresh₁
    · exact fresh₂

/-- **Heating reads determinately at the name frame.** If the taken row reads at every solution of the
knowledge as `par a b`, every solution of the result reads the made rows as `a` and `b`. -/
theorem heat_reads_determinately [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (o : O) {m₁ m₂ : O} (madeDistinct : m₁ ≠ m₂) (a b : Pattern)
    (reads : ∀ σ : PSubst, nameAction.Models σ C.equations → NameLaws (psubst σ (label o)) (psubst σ (par a b)))
    {σ : PSubst} (solved : nameAction.Models σ ((heatN ρ o m₁ m₂).result QN (embed label C)).knowledge) :
    NameLaws (psubst σ (((heatN ρ o m₁ m₂).result QN (embed label C)).label m₁)) (psubst σ a) ∧
      NameLaws (psubst σ (((heatN ρ o m₁ m₂).result QN (embed label C)).label m₂)) (psubst σ b) := by
  have info : ((heatN ρ o m₁ m₂).result QN (embed label C)).knowledge =
      (heatN ρ o m₁ m₂).information QN (embed label C) := rfl
  rw [info] at solved
  obtain ⟨a', b', same, left, right⟩ := heat_takes_pair label C ρ o m₁ m₂ solved
  have known : nameAction.Models σ C.equations := by
    intro e member
    have whole := solved
    rw [heatN_information] at whole
    exact whole e (by simp [member])
  have read := reads σ known
  rw [same, psubst_par] at read
  obtain ⟨readA, readB⟩ := nameLaws_pair_iff.mp read
  rw [heatN_label₁, heatN_label₂ label C ρ o madeDistinct]
  exact ⟨left.trans readA, right.trans readB⟩

/-- **The root heating reads determinately**, through the arrow: the made rows read, at every solution of the
located result, as `a @ Root` and `b @ Root`. -/
theorem root_heat_reads_determinately [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (ρ : PSubst)
    (o : O) {m₁ m₂ : O} (madeDistinct : m₁ ≠ m₂) (a b : Pattern)
    (reads : ∀ σ : PSubst, nameAction.Models σ C.equations → NameLaws (psubst σ (label o)) (psubst σ (par a b)))
    {σ : PSubst}
    (solved : nameAction.Models σ ((rootFiring (heatN ρ o m₁ m₂)).result QN (rootState label C)).knowledge) :
    NameLaws (psubst σ (((rootFiring (heatN ρ o m₁ m₂)).result QN (rootState label C)).label m₁))
        (atLoc (psubst σ a) rootLoc) ∧
      NameLaws (psubst σ (((rootFiring (heatN ρ o m₁ m₂)).result QN (rootState label C)).label m₂))
        (atLoc (psubst σ b) rootLoc) := by
  rw [(root_preserves locatedFrame_name label C (heatN ρ o m₁ m₂)).2] at solved ⊢
  have unlocated := (models_atStore locatedFrame_name pvars_rootLoc σ _).mp solved
  obtain ⟨left, right⟩ := heat_reads_determinately label C ρ o madeDistinct a b reads unlocated
  simp only [locate, atLabel]
  rw [psubst_atLoc σ _ pvars_rootLoc, psubst_atLoc σ _ pvars_rootLoc]
  exact ⟨(atLoc_E_iff locatedFrame_name _ _ rootLoc).mpr left, (atLoc_E_iff locatedFrame_name _ _ rootLoc).mpr right⟩

end Heat

/-! ## Heating at a child, at the name frame -/

section HeatChild

variable {O : Type*}

/-- Substitution acts inside the context of any location. -/
theorem psubst_atLoc_any (σ : PSubst) (t l : Pattern) : psubst σ (atLoc t l) = atLoc (psubst σ t) (psubst σ l) := by
  simp only [atLoc, psubst, psubstList_eq_map, List.map_cons, List.map_nil]

theorem psubst_pendingTok (σ : PSubst) (l m : Pattern) :
    psubst σ (pendingTok l m) = pendingTok (psubst σ l) (psubst σ m) := by
  simp only [pendingTok, psubst, psubstList_eq_map, List.map_cons, List.map_nil]

/-- **A row at a location is related only to a row at a location**, part by part, at the name frame. -/
theorem nameLaws_atLoc_left {a l q : Pattern} (h : NameLaws (atLoc a l) q) :
    ∃ b l', q = atLoc b l' ∧ NameLaws a b ∧ NameLaws l l' := by
  have notQuote : ¬ IsQuote "At" := by unfold IsQuote; decide
  have same := (ReflNames.nameCanon_eq_of_nameLaws h).symm
  rw [atLoc, ReflNames.nameCanon_apply_of_not_quote notQuote] at same
  cases q with
  | apply c args =>
      obtain ⟨args', hc⟩ := ReflNames.nameCanon_apply_head c args
      have heads : c = "At" := by
        rw [hc] at same
        exact (Pattern.apply.inj same).1
      subst heads
      rw [ReflNames.nameCanon_apply_of_not_quote notQuote] at same
      have mapped := (Pattern.apply.inj same).2
      rcases args with _ | ⟨b, _ | ⟨l', _ | ⟨e, rest⟩⟩⟩
      · simp at mapped
      · simp at mapped
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
        exact ⟨b, l', rfl, (ReflNames.nameLaws_iff a b).mpr mapped.1.symm,
          (ReflNames.nameLaws_iff l l').mpr mapped.2.symm⟩
      · simp at mapped
  | bvar n => simp [ReflNames.nameCanon] at same
  | fvar x => simp [ReflNames.nameCanon] at same
  | lambda nm body => simp [ReflNames.nameCanon] at same
  | multiLambda n nms body => simp [ReflNames.nameCanon] at same
  | subst body repl => simp [ReflNames.nameCanon] at same
  | collection ct elems rest =>
      rw [ReflNames.nameCanon_collection] at same
      cases same

theorem heatChild_mem : heatChild ∈ located := Or.inl (Or.inr (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))

/-- Heating at a child at the name frame: take `o`, read the token `p`, make `m₁` and `m₂`. -/
def heatChildN (ρ : PSubst) (o p m₁ m₂ : O) : Firing O QNE located PUnit.unit :=
  ⟨heatChild, heatChild_mem, PUnit.unit, ρ, ⟨[o], [p], [m₁, m₂]⟩, []⟩

theorem heatChildN_information (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst) (o p m₁ m₂ : O) :
    (heatChildN ρ o p m₁ m₂).information QN (embed label C) =
      C.equations ++ [(psubst ρ (atLoc (par leftPart rightPart) locL), label o)] ++
        [(psubst ρ (pendingTok locL locM), label p)] ++ [] := by
  rw [OneFrame.information_eq]
  rfl

/-- **Heating at a child takes a binary parallel composition at a location, and only while that child's
`Pending` token is present**: at every solution of its information the taken row is `par a b @ l`, whose
members read as the made rows' patterns, and the read row reads as `Pending(l', m)` with `l'` the opened
location, which reads as `l`. -/
theorem heatChild_takes_pair (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst) (o p m₁ m₂ : O)
    {σ : PSubst} (solved : nameAction.Models σ ((heatChildN ρ o p m₁ m₂).information QN (embed label C))) :
    ∃ a b l : Pattern, psubst σ (label o) = atLoc (par a b) l ∧
      NameLaws (psubst σ (psubst ρ leftPart)) a ∧ NameLaws (psubst σ (psubst ρ rightPart)) b ∧
      NameLaws (psubst σ (psubst ρ locL)) l ∧
      NameLaws (pendingTok (psubst σ (psubst ρ locL)) (psubst σ (psubst ρ locM))) (psubst σ (label p)) := by
  rw [heatChildN_information] at solved
  have take : NameLaws (psubst σ (psubst ρ (atLoc (par leftPart rightPart) locL))) (psubst σ (label o)) :=
    solved (psubst ρ (atLoc (par leftPart rightPart) locL), label o) (by simp)
  have read : NameLaws (psubst σ (psubst ρ (pendingTok locL locM))) (psubst σ (label p)) :=
    solved (psubst ρ (pendingTok locL locM), label p) (by simp)
  rw [psubst_atLoc_any, psubst_atLoc_any, psubst_par, psubst_par] at take
  rw [psubst_pendingTok, psubst_pendingTok] at read
  obtain ⟨x, l, same, pair, loc⟩ := nameLaws_atLoc_left take
  obtain ⟨a, b, rfl, left, right⟩ := nameLaws_pair_left pair
  exact ⟨a, b, l, same, left, right, loc, read⟩

/-- **A row that reads as no binary parallel composition at a location is never heated at a child.** -/
theorem heatChild_refused [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (o p m₁ m₂ : O)
    (notPair : ∀ σ : PSubst, nameAction.Models σ C.equations →
      ¬ ∃ a b l : Pattern, psubst σ (label o) = atLoc (par a b) l) (ρ : PSubst) :
    ¬ (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (heatChildN ρ o p m₁ m₂) := by
  intro admitted
  obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  obtain ⟨a, b, l, same, -⟩ := heatChild_takes_pair label C ρ o p m₁ m₂ solved
  have known : nameAction.Models σ C.equations := by
    intro e member
    have whole := solved
    rw [heatChildN_information] at whole
    exact whole e (by simp [member])
  exact notPair σ known ⟨a, b, l, same⟩

/-- **A row that reads as `par a b @ l` at a solution where the child's `Pending(l, m)` is present is heated**,
at every fresh opening. -/
theorem heatChild_admitted [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (o p m₁ m₂ : O)
    (present : o ∈ C.present) (tokenPresent : p ∈ C.present) (apart : o ≠ p) (madeDistinct : m₁ ≠ m₂)
    (fresh₁ : m₁ ∉ C.present) (fresh₂ : m₂ ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations) {a b l m : Pattern}
    (pair : NameLaws (psubst σ₀ (label o)) (atLoc (par a b) l))
    (token : NameLaws (psubst σ₀ (label p)) (pendingTok l m))
    {ρ : PSubst} (opensFreshly : (heatChildN ρ o p m₁ m₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (heatChildN ρ o p m₁ m₂) := by
  let h : PSubst := fun v =>
    if v = "A" then some a else if v = "B" then some b else if v = "L" then some l
    else if v = "M" then some m else none
  have splitTake : psubst h (atLoc (par leftPart rightPart) locL) = atLoc (par a b) l := by
    rw [psubst_atLoc_any, psubst_par]
    rfl
  have splitRead : psubst h (pendingTok locL locM) = pendingTok l m := by
    rw [psubst_pendingTok]
    rfl
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (heatChildN ρ o p m₁ m₂) opensFreshly (b := PUnit.unit) σ₀ h known
    (fun _ member => (List.not_mem_nil member).elim)
    (fun o' member => by
      obtain rfl := List.mem_singleton.mp member
      exact present)
    (fun o' member => by
      obtain rfl := List.mem_singleton.mp member
      exact tokenPresent)
    (fun q member => by
      obtain rfl := List.mem_singleton.mp member
      show NameLaws (psubst h (atLoc (par leftPart rightPart) locL)) (psubst σ₀ (label o))
      rw [splitTake]
      exact pair.symm)
    (fun q member => by
      obtain rfl := List.mem_singleton.mp member
      show NameLaws (psubst h (pendingTok locL locM)) (psubst σ₀ (label p))
      rw [splitRead]
      exact token.symm)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [heatChildN], by simp [heatChildN, madeDistinct], rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩
  · intro o' member
    simp only [heatChildN, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    exact present
  · intro o' member
    simp only [heatChildN, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    exact tokenPresent
  · simp [heatChildN, Selection.commit, apart]
  · rw [Finset.disjoint_left]
    intro o' member
    simp only [heatChildN, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact fresh₁
    · exact fresh₂

/-- **Heating at a child reads determinately**: if the taken row reads at every solution of the knowledge as
`par a b @ l`, every solution of the result reads the made rows as `a @ l` and `b @ l`. -/
theorem heatChild_reads_determinately [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (ρ : PSubst) (o p : O) {m₁ m₂ : O} (madeDistinct : m₁ ≠ m₂) (a b l : Pattern)
    (reads : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label o)) (psubst σ (atLoc (par a b) l)))
    {σ : PSubst} (solved : nameAction.Models σ ((heatChildN ρ o p m₁ m₂).result QN (embed label C)).knowledge) :
    NameLaws (psubst σ (((heatChildN ρ o p m₁ m₂).result QN (embed label C)).label m₁)) (psubst σ (atLoc a l)) ∧
      NameLaws (psubst σ (((heatChildN ρ o p m₁ m₂).result QN (embed label C)).label m₂))
        (psubst σ (atLoc b l)) := by
  have info : ((heatChildN ρ o p m₁ m₂).result QN (embed label C)).knowledge =
      (heatChildN ρ o p m₁ m₂).information QN (embed label C) := rfl
  rw [info] at solved
  obtain ⟨a', b', l', same, left, right, loc, -⟩ := heatChild_takes_pair label C ρ o p m₁ m₂ solved
  have known : nameAction.Models σ C.equations := by
    intro e member
    have whole := solved
    rw [heatChildN_information] at whole
    exact whole e (by simp [member])
  have read := reads σ known
  rw [same, psubst_atLoc_any, psubst_par] at read
  obtain ⟨pairRead, locRead⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp read
  obtain ⟨readA, readB⟩ := nameLaws_pair_iff.mp pairRead
  have label₁ : ((heatChildN ρ o p m₁ m₂).result QN (embed label C)).label m₁ = psubst ρ (atLoc leftPart locL) := by
    show (if m₁ = m₁ then psubst ρ (atLoc leftPart locL) else _) = _
    rw [if_pos rfl]
  have label₂ : ((heatChildN ρ o p m₁ m₂).result QN (embed label C)).label m₂ =
      psubst ρ (atLoc rightPart locL) := by
    show (if m₂ = m₁ then _ else if m₂ = m₂ then psubst ρ (atLoc rightPart locL) else _) = _
    rw [if_neg (Ne.symm madeDistinct), if_pos rfl]
  rw [label₁, label₂]
  simp only [psubst_atLoc_any]
  exact ⟨(locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨left.trans readA, loc.trans locRead⟩,
    (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨right.trans readB, loc.trans locRead⟩⟩

end HeatChild

#print axioms refused_of_take
#print axioms refused_of_read
#print axioms root_preserves
#print axioms root_reflects
#print axioms conservative_at_root
#print axioms conservative_at_root_QX
#print axioms conservative_at_root_QN
#print axioms conservative_at_root_syntactic
#print axioms openRoot_not_root
#print axioms transitions_at_root
#print axioms syntacticToName
#print axioms nameToBag
#print axioms frame_maps_strict
#print axioms heat_takes_pair
#print axioms heat_admitted_takes_pair
#print axioms heat_refused
#print axioms heat_admitted
#print axioms heat_reads_determinately
#print axioms root_heat_reads_determinately
#print axioms nameLaws_atLoc_left
#print axioms heatChild_takes_pair
#print axioms heatChild_refused
#print axioms heatChild_admitted
#print axioms heatChild_reads_determinately
#print axioms act_atLoc
#print axioms models_atStore
#print axioms atMap
#print axioms atMap_reflects
#print axioms fresh_atFiring_iff
#print axioms information_atFiring
#print axioms atFiring_result
#print axioms atFiring_admits_iff
#print axioms located_finite
#print axioms locatedFrame_syntactic
#print axioms locatedFrame_bag
#print axioms locatedFrame_name

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocated
