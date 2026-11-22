import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CommRuns
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedResidual

/-!
# The manuscript's COMM on the one-match step by a finite program

`MeTTaCalculus` is the calculus of the F1R3FLY manuscript. Its COMM is
`for(t <- x)P | for(u <- x)Q → P·σ̇ | Q·σ̇`: two inputs, `σ` a unifier of the patterns `t` and `u`, the dot
quoting each bound value. `CommOneFiring` shows that one COMM is one firing of the one-match step by the
rule of its redex's shape, one rule per redex shape. Here the program is finite and fixed before any
process is given.

## The step and the frame

The step is the one-match step of a program, `RuleSyntax.step`, at the one frame of structural
substitution on patterns (`OneFrame.frames patternAction`; firings move along the identity). Its five
choices:

* the store is a bag of occurrences;
* a firing is one match: one rule, one opening, one selection;
* a firing's guards are asked at every solution of its information, which includes its own tells (the
  rules here have no guard, so this choice is not exercised);
* the program is a fixed set of rules beside the store: here `program`, three rules;
* there is one store of knowledge.

## The program

* `commRule`: unknowns `T1`, `T2` (the patterns), `X` (the channel), `K1`, `K2` (the continuations). Take
  `for(T1 <- X)K1` and `for(T2 <- X)K2`, tell `T1 = T2`, make `K1` and `K2`.
* `heatRule`: take `A | B`, make `A` and `B`. `clearRule`: take `0`, make nothing.

The two input patterns are data: the take patterns match every redex, and the told equation makes the
knowledge compute the unifier. The rule carries no process structure (`program_finite`).

## Where the dot goes

A made row copies what its rule took: at every solution `σ`, the made row `K1` reads as the continuation
held by the taken row, read through `σ`, so a bound variable reads as its value. The manuscript's dot
reads it as the value's quotation. So the representation `predot` writes each continuation with its own
pattern's variables in quoted position, at every depth: the input `for(t <- x)P` is represented by
`for(t <- x')P'` with `P' = dotted (pvars t) (predot P)`. The knowledge supplies the values; the quotes
are the representation's. Patterns are kept as written, and a pattern without variables is its own
representation (`predot_ground`).

## What is shown

* `predot_psubst`: pre-dotting commutes with every substitution of variable-free values for variables
  that no inner pattern binds. So the representation of a dotted continuation is the representation, read
  through the unifier (`dotted_reads_predot`).
* `comm_one_firing`: for every redex `for(t <- x)A | for(u <- x)B` whose patterns have a ground principal
  unifier `bs`, under the variable convention (`Corrected.Apart`) and with first-order continuations: at a
  state whose two taken rows read as the represented inputs at every solution of the knowledge, and one
  of whose solutions unifies the patterns, the COMM firing of the fixed program is admitted at every fresh
  opening; the manuscript's rule relates the redex to `applyDot bs A | applyDot bs B`, as written
  (`ReflectionClosure.Step`) and in the corrected semantics (`Corrected.Step conventional`); and every
  solution of the result's knowledge unifies the patterns and reads the two made rows as
  `predot (applyDot bs A)` and `predot (applyDot bs B)`, read through it.
* `comm_one_firing_closed`: when each continuation's variables are its own pattern's, every solution reads
  the two made rows as exactly `applyDot bs A` and `applyDot bs B`.
* `comm_reads_principal`: completed principal bindings give a symbolic readback of first-order
  continuations without requiring ground values. The result is read at each residual solution.
* `comm_one_transition`: a fresh opening exists, and the transition of the step leads to a state whose
  present rows replace the inputs by the made identities, whose other labels are unchanged, whose
  knowledge has a solution, and every solution of which reads the made rows so.

## What is not shown here

PAR, the bag laws and runs are in `FiniteHosting` (parts that bind only at their own input) and in
`FiniteNested` (continuations that bind again); the computed examples and the controls of the side
conditions in `FiniteControls` and `FiniteNestedControls`; the bag presentation inside the tree's corrected
semantics in `FiniteBridge`. REFL is not hosted. Whether every finite program needs the dot in its
representation is not shown: the control `FiniteControls.undotted_misreads` shows only that this program
does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteProgram

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot SC)
open MeTTaOperationsComm (psubst pcomp psubst_comp psubst_none psubst_congr psubst_of_pvars_nil pvars
  patternAction PSubst quoteOn dotted commSelection GroundPrincipal storePVars lookup_eq_none_of_keys
  applyDot_eq psubst_nQuote psubst_pFor firstOrder)
open MeTTaCalculus.Corrected (psubst_getD_congr psubst_getD_congr_on pvars_pFor binders bindersFor Apart
  psubstList_eq_map binders_apply bindersFor_cons3 bindersFor_short mem_pvars_apply_of
  mem_pvars_collection_of mem_pvars_psubst binders_subset_pvars)
open Comm (Tm X E renameBy ruleVars)
open OneFrame (embed)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)

/-! ## The program -/

/-- The comm rule's first pattern. -/
def firstPattern : Pattern := .fvar "T1"
/-- The comm rule's second pattern. -/
def secondPattern : Pattern := .fvar "T2"
/-- The comm rule's channel. -/
def channelUnknown : Pattern := .fvar "X"
/-- The comm rule's first continuation. -/
def firstBody : Pattern := .fvar "K1"
/-- The comm rule's second continuation. -/
def secondBody : Pattern := .fvar "K2"
/-- The heating rule's left component. -/
def leftPart : Pattern := .fvar "A"
/-- The heating rule's right component. -/
def rightPart : Pattern := .fvar "B"

/-- **The comm rule**: take `for(T1 <- X)K1` and `for(T2 <- X)K2`, tell `T1 = T2`, make `K1` and `K2`. -/
def commRule : Rule Tm :=
  ⟨PUnit.unit, ⟨[pFor firstPattern channelUnknown firstBody, pFor secondPattern channelUnknown secondBody],
    [], [(firstPattern, secondPattern)], [], [firstBody, secondBody]⟩, []⟩

/-- **Heating**: take `A | B`, make `A` and `B`. -/
def heatRule : Rule Tm :=
  ⟨PUnit.unit, ⟨[par leftPart rightPart], [], [], [], [leftPart, rightPart]⟩, []⟩

/-- **Clearing**: take `0`, make nothing. -/
def clearRule : Rule Tm :=
  ⟨PUnit.unit, ⟨[pZero], [], [], [], []⟩, []⟩

/-- **The program**: three rules, fixed before any process is given. -/
def program : Program Tm := {commRule, heatRule, clearRule}

theorem mem_program {r : Rule Tm} : r ∈ program ↔ r = commRule ∨ r = heatRule ∨ r = clearRule := by
  simp [program]

theorem commRule_mem : commRule ∈ program := mem_program.mpr (.inl rfl)
theorem heatRule_mem : heatRule ∈ program := mem_program.mpr (.inr (.inl rfl))
theorem clearRule_mem : clearRule ∈ program := mem_program.mpr (.inr (.inr rfl))

/-- **The program is finite.** -/
theorem program_finite : program.Finite :=
  ((Set.finite_singleton clearRule).insert heatRule).insert commRule

/-! ## Pre-dotting -/

mutual
/-- **Pre-dotting**: every input's continuation with its own pattern's variables in quoted position, at
every depth. Patterns are kept as written. -/
def predot : Pattern → Pattern
  | .bvar n => .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply c (if c = "MFor" then predotFor args else predotList args)
  | .lambda nm body => .lambda nm (predot body)
  | .multiLambda n nms body => .multiLambda n nms (predot body)
  | .subst body repl => .subst (predot body) (predot repl)
  | .collection ct elems rest => .collection ct (predotList elems) rest
/-- Pre-dotting of a list. -/
def predotList : List Pattern → List Pattern
  | [] => []
  | p :: ps => predot p :: predotList ps
/-- The arguments of an input: the pattern as written, the channel, the continuation dotted. -/
def predotFor : List Pattern → List Pattern
  | [] => []
  | [p] => [predot p]
  | [p, q] => [predot p, predot q]
  | t :: x :: k :: rest => t :: predot x :: dotted (pvars t) (predot k) :: predotList rest
end

theorem predotList_eq_map (ps : List Pattern) : predotList ps = ps.map predot := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [predotList, ih]

theorem predot_apply (c : String) (args : List Pattern) :
    predot (.apply c args) = .apply c (if c = "MFor" then predotFor args else args.map predot) := by
  simp [predot, predotList_eq_map]

theorem predotFor_cons3 (t x k : Pattern) (rest : List Pattern) :
    predotFor (t :: x :: k :: rest) = t :: predot x :: dotted (pvars t) (predot k) :: rest.map predot := by
  simp [predotFor, predotList_eq_map]

theorem predotFor_short (ps : List Pattern) (short : ps.length < 3) : predotFor ps = ps.map predot := by
  match ps, short with
  | [], _ => rfl
  | [p], _ => simp [predotFor]
  | [p, q], _ => simp [predotFor]

theorem predot_pFor (t x k : Pattern) :
    predot (pFor t x k) = pFor t (predot x) (dotted (pvars t) (predot k)) := by
  simp [pFor, predot_apply, predotFor_cons3]

theorem predot_par (p q : Pattern) : predot (par p q) = par (predot p) (predot q) := by
  simp [par, MeTTaCalculus.pPar, predot, predotList]

theorem predot_pZero : predot pZero = pZero := by
  simp [pZero, predot, predotList]

theorem predot_nQuote (p : Pattern) : predot (nQuote p) = nQuote (predot p) := by
  simp [nQuote, predot, predotList]

/-- Dotting no variable changes nothing. -/
theorem dotted_nil (p : Pattern) : dotted [] p = p := by
  have none : quoteOn [] = fun _ => none := by
    funext x
    simp [quoteOn]
  rw [dotted, none, psubst_none]

/-- **A pattern without variables is its own representation.** -/
theorem predot_ground (p : Pattern) (closed : pvars p = []) : predot p = p := by
  revert closed
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, pvars q = [] → predot q = q) with
  | bvar n => intro _; rfl
  | fvar x => intro _; rfl
  | apply c args ih =>
      intro closed
      have each : ∀ q ∈ args, predot q = q := fun q member =>
        ih q member (List.eq_nil_iff_forall_not_mem.mpr fun y occurs =>
          List.eq_nil_iff_forall_not_mem.mp closed y (mem_pvars_apply_of member occurs))
      have mapped : args.map predot = args := by
        conv => rhs; rw [← List.map_id args]
        exact List.map_congr_left each
      rw [predot_apply]
      congr 1
      split_ifs with isFor
      · match args, each, mapped, closed with
        | t :: x :: k :: rest, each, _, closed =>
            have tClosed : pvars t = [] := List.eq_nil_iff_forall_not_mem.mpr fun y occurs =>
              List.eq_nil_iff_forall_not_mem.mp closed y (mem_pvars_apply_of (by simp) occurs)
            rw [predotFor_cons3, tClosed, dotted_nil, each x (by simp), each k (by simp)]
            have restSame : rest.map predot = rest := by
              conv => rhs; rw [← List.map_id rest]
              exact List.map_congr_left fun q member => each q (by simp [member])
            rw [restSame]
        | [], _, mapped, _ => rw [predotFor_short [] (by simp), mapped]
        | [p], _, mapped, _ => rw [predotFor_short [p] (by simp), mapped]
        | [p, q], _, mapped, _ => rw [predotFor_short [p, q] (by simp), mapped]
      · exact mapped
  | lambda nm body ih =>
      intro closed
      simp only [predot]
      rw [ih (by simpa [pvars] using closed)]
  | multiLambda n nms body ih =>
      intro closed
      simp only [predot]
      rw [ih (by simpa [pvars] using closed)]
  | subst body repl ihb ihr =>
      intro closed
      have both : pvars body = [] ∧ pvars repl = [] := by simpa [pvars] using closed
      simp only [predot]
      rw [ihb both.1, ihr both.2]
  | collection ct elems rest ih =>
      intro closed
      have each : ∀ q ∈ elems, predot q = q := fun q member =>
        ih q member (List.eq_nil_iff_forall_not_mem.mpr fun y occurs =>
          List.eq_nil_iff_forall_not_mem.mp closed y (mem_pvars_collection_of member occurs))
      simp only [predot, predotList_eq_map]
      congr 1
      conv => rhs; rw [← List.map_id elems]
      exact List.map_congr_left each
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member closedQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head closedQ
      · exact tail q later closedQ

/-- Dotting adds no variable. -/
theorem mem_pvars_dotted {vs : List String} {p : Pattern} {x : String} :
    x ∈ pvars (dotted vs p) ↔ x ∈ pvars p := by
  rw [dotted, mem_pvars_psubst]
  constructor
  · rintro ⟨w, inside, occurs⟩
    by_cases quoted : w ∈ vs
    · simp only [quoteOn, if_pos quoted, Option.getD_some] at occurs
      have same : x = w := by simpa [nQuote, pvars, MeTTaOperationsComm.pvars.pvarsList] using occurs
      exact same ▸ inside
    · simp only [quoteOn, if_neg quoted, Option.getD_none] at occurs
      have same : x = w := by simpa [pvars] using occurs
      exact same ▸ inside
  · intro inside
    refine ⟨x, inside, ?_⟩
    by_cases quoted : x ∈ vs
    · simp [quoteOn, quoted, nQuote, pvars, MeTTaOperationsComm.pvars.pvarsList]
    · simp [quoteOn, quoted, pvars]

/-- **Pre-dotting adds no variable.** -/
theorem mem_pvars_predot {p : Pattern} {x : String} (occurs : x ∈ pvars (predot p)) : x ∈ pvars p := by
  revert occurs
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, x ∈ pvars (predot q) → x ∈ pvars q) with
  | bvar n => exact id
  | fvar y => exact id
  | apply c args ih =>
      intro occurs
      rw [predot_apply] at occurs
      split_ifs at occurs with isFor
      · match args, ih, occurs with
        | t :: y :: k :: rest, ih, occurs =>
            rw [predotFor_cons3, MeTTaCalculus.Corrected.pvars_apply,
              MeTTaCalculus.Corrected.mem_pvarsList] at occurs
            obtain ⟨q, member, inQ⟩ := occurs
            simp only [List.mem_cons, List.mem_map] at member
            rcases member with rfl | rfl | rfl | ⟨r, inRest, rfl⟩
            · exact mem_pvars_apply_of (by simp) inQ
            · exact mem_pvars_apply_of (by simp) (ih y (by simp) inQ)
            · exact mem_pvars_apply_of (by simp) (ih k (by simp) (mem_pvars_dotted.mp inQ))
            · exact mem_pvars_apply_of (by simp [inRest]) (ih r (by simp [inRest]) inQ)
        | [], _, occurs => simp [predotFor, pvars, MeTTaOperationsComm.pvars.pvarsList] at occurs
        | [p], ih, occurs =>
            rw [predotFor_short [p] (by simp), MeTTaCalculus.Corrected.pvars_apply,
              MeTTaCalculus.Corrected.mem_pvarsList] at occurs
            obtain ⟨q, member, inQ⟩ := occurs
            obtain ⟨r, inArgs, rfl⟩ := List.mem_map.mp member
            exact mem_pvars_apply_of inArgs (ih r inArgs inQ)
        | [p, p'], ih, occurs =>
            rw [predotFor_short [p, p'] (by simp), MeTTaCalculus.Corrected.pvars_apply,
              MeTTaCalculus.Corrected.mem_pvarsList] at occurs
            obtain ⟨q, member, inQ⟩ := occurs
            obtain ⟨r, inArgs, rfl⟩ := List.mem_map.mp member
            exact mem_pvars_apply_of inArgs (ih r inArgs inQ)
      · rw [MeTTaCalculus.Corrected.pvars_apply, MeTTaCalculus.Corrected.mem_pvarsList] at occurs
        obtain ⟨q, member, inQ⟩ := occurs
        obtain ⟨r, inArgs, rfl⟩ := List.mem_map.mp member
        exact mem_pvars_apply_of inArgs (ih r inArgs inQ)
  | lambda nm body ih =>
      intro occurs
      simp only [predot, pvars] at occurs ⊢
      exact ih occurs
  | multiLambda n nms body ih =>
      intro occurs
      simp only [predot, pvars] at occurs ⊢
      exact ih occurs
  | subst body repl ihb ihr =>
      intro occurs
      simp only [predot, pvars, List.mem_append] at occurs ⊢
      rcases occurs with inBody | inRepl
      · exact .inl (ihb inBody)
      · exact .inr (ihr inRepl)
  | collection ct elems rest ih =>
      intro occurs
      simp only [predot, predotList_eq_map, pvars, MeTTaCalculus.Corrected.mem_pvarsList] at occurs
      obtain ⟨q, member, inQ⟩ := occurs
      obtain ⟨r, inElems, rfl⟩ := List.mem_map.mp member
      exact mem_pvars_collection_of inElems (ih r inElems inQ)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member inQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head inQ
      · exact tail q later inQ

/-! ## Pre-dotting commutes with ground substitutions -/

/-- A substitution whose values have no variables. -/
def GroundValued (τ : PSubst) : Prop := ∀ x v, τ x = some v → pvars v = []

/-- Dotting commutes when the substitution neither replaces the dotted
variables nor introduces an image changed by their dot. -/
theorem dotted_psubst_comm_of_images {τ : PSubst} (vs : List String)
    (stable : ∀ x v, τ x = some v → dotted vs v = v)
    (apart : ∀ x ∈ vs, τ x = none) (p : Pattern) :
    dotted vs (psubst τ p) = psubst τ (dotted vs p) := by
  unfold dotted
  rw [psubst_comp, psubst_comp]
  apply psubst_getD_congr
  intro x
  cases found : τ x with
  | some v =>
      have notIn : x ∉ vs := fun inside => by rw [apart x inside] at found; cases found
      have fixed : psubst (quoteOn vs) v = v := stable x v found
      simp only [pcomp, found, quoteOn, if_neg notIn, fixed]
  | none =>
      by_cases inside : x ∈ vs
      · simp only [pcomp, found, quoteOn, if_pos inside, Option.getD_some, psubst_nQuote, psubst,
          Option.getD_none]
      · simp only [pcomp, found, quoteOn, if_neg inside]

/-- The ground specialization, for which every dot fixes the images. -/
theorem dotted_psubst_comm {τ : PSubst} (ground : GroundValued τ) (vs : List String)
    (apart : ∀ x ∈ vs, τ x = none) (p : Pattern) :
    dotted vs (psubst τ p) = psubst τ (dotted vs p) :=
  dotted_psubst_comm_of_images vs (fun x v found => psubst_of_pvars_nil _ v (ground x v found)) apart p

/-- **Pre-dotting commutes with every ground substitution of variables that no inner pattern binds.** -/
theorem predot_psubst {τ : PSubst} (ground : GroundValued τ) (p : Pattern)
    (outside : ∀ x ∈ binders p, τ x = none) : predot (psubst τ p) = psubst τ (predot p) := by
  revert outside
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, (∀ x ∈ binders q, τ x = none) →
      predot (psubst τ q) = psubst τ (predot q)) with
  | bvar n => intro _; rfl
  | fvar x =>
      intro _
      show predot ((τ x).getD (.fvar x)) = (τ x).getD (.fvar x)
      cases found : τ x with
      | some v => exact predot_ground v (ground x v found)
      | none => rfl
  | apply c args ih =>
      intro outside
      have psubstApply : ∀ L : List Pattern, psubst τ (.apply c L) = .apply c (L.map (psubst τ)) := by
        intro L
        simp only [psubst, psubstList_eq_map]
      rw [psubstApply, predot_apply, predot_apply, psubstApply]
      congr 1
      by_cases isFor : c = "MFor"
      · rw [if_pos isFor, if_pos isFor]
        rw [binders_apply, if_pos isFor] at outside
        match args, ih, outside with
        | t :: x :: k :: rest, ih, outside =>
            rw [bindersFor_cons3] at outside
            have tFixed : psubst τ t = t := by
              rw [psubst_congr τ (fun _ => none) t fun y occurs =>
                outside y (by simp [occurs]), psubst_none]
            have xSame := ih x (by simp) fun y inside => outside y (by simp [inside])
            have kSame := ih k (by simp) fun y inside => outside y (by simp [inside])
            have restSame : ∀ q ∈ rest, predot (psubst τ q) = psubst τ (predot q) := fun q member =>
              ih q (by simp [member]) fun y inside =>
                outside y (by simp only [List.mem_append, List.mem_flatMap]; exact .inr ⟨q, member, inside⟩)
            have apartT : ∀ y ∈ pvars t, τ y = none := fun y occurs => outside y (by simp [occurs])
            have restMap : (rest.map (psubst τ)).map predot = (rest.map predot).map (psubst τ) := by
              rw [List.map_map, List.map_map]
              exact List.map_congr_left restSame
            rw [List.map_cons, List.map_cons, List.map_cons, predotFor_cons3, predotFor_cons3, tFixed, xSame,
              kSame, dotted_psubst_comm ground (pvars t) apartT, restMap]
            simp only [List.map_cons, tFixed]
        | [], _, _ => rfl
        | [p], ih, outside =>
            rw [bindersFor_short [p] (by simp)] at outside
            have pSame := ih p (by simp) fun y inside => outside y (by simp [inside])
            simp only [List.map_cons, List.map_nil, predotFor, pSame]
        | [p, q], ih, outside =>
            rw [bindersFor_short [p, q] (by simp)] at outside
            have pSame := ih p (by simp) fun y inside => outside y (by simp [inside])
            have qSame := ih q (by simp) fun y inside => outside y (by simp [inside])
            simp only [List.map_cons, List.map_nil, predotFor, pSame, qSame]
      · rw [binders_apply, if_neg isFor] at outside
        simp only [if_neg isFor, List.map_map]
        exact List.map_congr_left fun q member =>
          ih q member fun y inside => outside y (List.mem_flatMap.mpr ⟨q, member, inside⟩)
  | lambda nm body ih =>
      intro outside
      simp only [psubst, predot]
      rw [ih fun y inside => outside y (by simpa [binders] using inside)]
  | multiLambda n nms body ih =>
      intro outside
      simp only [psubst, predot]
      rw [ih fun y inside => outside y (by simpa [binders] using inside)]
  | subst body repl ihb ihr =>
      intro outside
      simp only [psubst, predot]
      rw [ihb fun y inside => outside y (by simp [binders, inside]),
        ihr fun y inside => outside y (by simp [binders, inside])]
  | collection ct elems rest ih =>
      intro outside
      simp only [psubst, predot, psubstList_eq_map, predotList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun q member =>
        ih q member fun y inside => outside y (by
          simp only [binders, MeTTaCalculus.Corrected.bindersList_eq_flatMap, List.mem_flatMap]
          exact ⟨q, member, inside⟩)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member outsideQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head outsideQ
      · exact tail q later outsideQ

/-- A binding list binds only its keys. -/
theorem mem_keys_of_lookup {bs : Bindings} {keys : List String} (keysOf : ∀ e ∈ bs, e.1 ∈ keys) {x : String}
    {v : Pattern} (found : bs.lookup x = some v) : x ∈ keys := by
  by_contra outside
  rw [lookup_eq_none_of_keys keysOf outside] at found
  cases found

/-- **A solution that agrees with a ground binding list reads a pre-dotted continuation as the
representation of its dot.** The binding list binds every key to a variable-free value; the solution reads
each key as its value; the dotted variables are keys, and are the continuation's keys; no inner pattern of
the continuation binds a key. -/
theorem dotted_reads_predot {bs : Bindings} {keys vs : List String} (keysOf : ∀ e ∈ bs, e.1 ∈ keys)
    (bound : ∀ x ∈ keys, ∃ v, bs.lookup x = some v ∧ pvars v = [])
    {σ : PSubst} (agrees : ∀ x ∈ keys, ∀ v, bs.lookup x = some v → psubst σ (.fvar x) = v)
    (A : Pattern) (fo : firstOrder A = true) (sub : ∀ x ∈ vs, x ∈ keys)
    (reads : ∀ x ∈ pvars A, x ∈ keys → x ∈ vs) (kept : ∀ x ∈ keys, x ∉ binders A) :
    psubst σ (dotted vs (predot A)) = psubst σ (predot (applyDot bs A)) := by
  rw [applyDot_eq bs A fo]
  have ground : GroundValued (fun x => (bs.lookup x).map nQuote) := by
    intro x v found
    change (bs.lookup x).map nQuote = some v at found
    obtain ⟨w, look, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨w', look', closed⟩ := bound x (mem_keys_of_lookup keysOf look)
    rw [look] at look'
    obtain rfl := Option.some.inj look'
    simp [nQuote, pvars, MeTTaOperationsComm.pvars.pvarsList, closed]
  have untouched : ∀ x ∈ binders A, (fun x => (bs.lookup x).map nQuote) x = Option.none := by
    intro x inside
    have outside : x ∉ keys := fun inKeys => kept x inKeys inside
    simp [lookup_eq_none_of_keys keysOf outside]
  rw [predot_psubst ground A untouched]
  unfold dotted
  rw [psubst_comp, psubst_comp]
  apply psubst_getD_congr_on
  intro x occurs
  have inA := mem_pvars_predot occurs
  by_cases inKeys : x ∈ keys
  · have inVs := reads x inA inKeys
    obtain ⟨v, found, closed⟩ := bound x inKeys
    simp only [pcomp, quoteOn, if_pos inVs, Option.getD_some, psubst_nQuote, found, Option.map_some]
    rw [agrees x inKeys v found, psubst_of_pvars_nil σ v closed]
  · have notVs : x ∉ vs := fun inVs => inKeys (sub x inVs)
    have look : bs.lookup x = none := lookup_eq_none_of_keys keysOf inKeys
    simp only [pcomp, quoteOn, if_neg notVs, look, Option.map_none]

/-! ## The COMM firing of the program -/

variable {O : Type*}

/-- **The COMM firing**: the comm rule opened by `ρ`, taking `first` and `second`, making `made₁` and
`made₂`. -/
def commAt (ρ : PSubst) (first second made₁ made₂ : O) : Firing O E program PUnit.unit :=
  ⟨commRule, commRule_mem, PUnit.unit, ρ, commSelection first second made₁ made₂, []⟩

/-- The instance of the comm rule's unknowns. -/
def commInstance (t u channel left right : Pattern) : PSubst := fun v =>
  if v = "T1" then some t else if v = "T2" then some u else if v = "X" then some channel
  else if v = "K1" then some left else if v = "K2" then some right else none

theorem commInstance_firstPattern (t u channel left right : Pattern) :
    psubst (commInstance t u channel left right) firstPattern = t := by
  simp [commInstance, firstPattern, psubst]

theorem commInstance_secondPattern (t u channel left right : Pattern) :
    psubst (commInstance t u channel left right) secondPattern = u := by
  simp [commInstance, secondPattern, psubst]

theorem commInstance_channel (t u channel left right : Pattern) :
    psubst (commInstance t u channel left right) channelUnknown = channel := by
  simp [commInstance, channelUnknown, psubst]

theorem commInstance_firstBody (t u channel left right : Pattern) :
    psubst (commInstance t u channel left right) firstBody = left := by
  simp [commInstance, firstBody, psubst]

theorem commInstance_secondBody (t u channel left right : Pattern) :
    psubst (commInstance t u channel left right) secondBody = right := by
  simp [commInstance, secondBody, psubst]

/-- The information of the COMM firing: the knowledge, the opened take patterns equated with the taken
rows, and the opened tell. -/
theorem commAt_information (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second made₁ made₂ : O) :
    (commAt ρ first second made₁ made₂).information X (embed label C) =
      C.equations ++ [(psubst ρ (pFor firstPattern channelUnknown firstBody), label first),
        (psubst ρ (pFor secondPattern channelUnknown secondBody), label second)] ++ [] ++
        [(psubst ρ firstPattern, psubst ρ secondPattern)] := by
  rw [OneFrame.information_eq]
  rfl

theorem pFor_inj {t x k t' x' k' : Pattern} (same : pFor t x k = pFor t' x' k') :
    t = t' ∧ x = x' ∧ k = k' := by
  simpa [pFor] using same

/-- The patterns' variables, with their keys. -/
theorem keys_of_apart {t A u B : Pattern} (convention : Apart t A u B) :
    (∀ x ∈ pvars t ++ pvars u, x ∉ binders A) ∧ ∀ x ∈ pvars t ++ pvars u, x ∉ binders B := by
  refine ⟨fun x inKeys inside => ?_, fun x inKeys inside => ?_⟩
  · rcases List.mem_append.mp inKeys with inT | inU
    · exact convention.leftKept x inT inside
    · exact convention.rightOutside x inU (binders_subset_pvars A x inside)
  · rcases List.mem_append.mp inKeys with inT | inU
    · exact convention.leftOutside x inT (binders_subset_pvars B x inside)
    · exact convention.rightKept x inU inside

section Step

variable [DecidableEq O]

theorem commAt_label₁ (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second made₁ made₂ : O) :
    ((commAt ρ first second made₁ made₂).result X (embed label C)).label made₁ = psubst ρ firstBody := by
  show (if made₁ = made₁ then psubst ρ firstBody else _) = _
  rw [if_pos rfl]

theorem commAt_label₂ (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second : O) {made₁ made₂ : O} (madeDistinct : made₁ ≠ made₂) :
    ((commAt ρ first second made₁ made₂).result X (embed label C)).label made₂ = psubst ρ secondBody := by
  show (if made₂ = made₁ then _ else if made₂ = made₂ then psubst ρ secondBody else _) = _
  rw [if_neg (Ne.symm madeDistinct), if_pos rfl]

omit [DecidableEq O] in
/-- **A solution of the COMM firing's information that agrees with a unifying solution of the
knowledge** on every term the state mentions, at every fresh opening, when the taken rows are present
and read as two inputs on one channel at every solution of the knowledge. -/
theorem comm_amalgamates (label : O → Pattern) (t u channel K₁ K₂ : Pattern) (C : Configuration Pattern O)
    (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (pFor t channel K₁))
    (readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (pFor u channel K₂))
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    {σ₀ : PSubst} (known : patternAction.Models σ₀ C.equations) (unifies : psubst σ₀ t = psubst σ₀ u)
    {ρ : PSubst} (opensFreshly : (commAt ρ first second made₁ made₂).Fresh X (embed label C)) :
    ∃ w : PSubst, patternAction.Models w ((commAt ρ first second made₁ made₂).information X (embed label C)) ∧
      ∀ m, (embed label C).Mentions m → psubst w (psubst (fun _ => none) m) = psubst σ₀ m := by
  let h : PSubst := commInstance (psubst σ₀ t) (psubst σ₀ u) (psubst σ₀ channel) (psubst σ₀ K₁)
    (psubst σ₀ K₂)
  obtain ⟨w, solved, state, -⟩ := Comm.information_amalgamates_matched (Y := X) (s := embed label C)
    (commAt ρ first second made₁ made₂) opensFreshly (b := PUnit.unit) σ₀ h known
    (fun e member => by
      obtain rfl := List.mem_singleton.mp member
      show psubst h firstPattern = psubst h secondPattern
      rw [commInstance_firstPattern, commInstance_secondPattern]
      exact unifies)
    (fun o member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact present₁
      · obtain rfl := List.mem_singleton.mp member
        exact present₂)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      rcases List.mem_cons.mp member with rfl | member
      · show psubst h (pFor firstPattern channelUnknown firstBody) = psubst σ₀ (label first)
        rw [readsFirst σ₀ known, psubst_pFor, psubst_pFor, commInstance_firstPattern,
          commInstance_channel, commInstance_firstBody]
      · obtain rfl := List.mem_singleton.mp member
        show psubst h (pFor secondPattern channelUnknown secondBody) = psubst σ₀ (label second)
        rw [readsSecond σ₀ known, psubst_pFor, psubst_pFor, commInstance_secondPattern,
          commInstance_channel, commInstance_secondBody])
    (fun _ member => (List.not_mem_nil member).elim)
  exact ⟨w, solved, state⟩

/-- **Admission of the COMM firing, for rows of any input shape.** At every fresh opening, when the
taken rows are distinct, present, and read as two inputs on one channel at every solution of the
knowledge, the made identities are distinct and not present, and some solution of the knowledge unifies
the patterns. Nothing is asked of the continuations. -/
theorem comm_admits_inputs (label : O → Pattern) (t u channel K₁ K₂ : Pattern) (C : Configuration Pattern O)
    (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (pFor t channel K₁))
    (readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (pFor u channel K₂))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    {σ₀ : PSubst} (known : patternAction.Models σ₀ C.equations) (unifies : psubst σ₀ t = psubst σ₀ u)
    {ρ : PSubst} (opensFreshly : (commAt ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E program).Admits (s := embed label C) (commAt ρ first second made₁ made₂) := by
  obtain ⟨w, solved, -⟩ := comm_amalgamates label t u channel K₁ K₂ C first second made₁ made₂ readsFirst
    readsSecond present₁ present₂ known unifies opensFreshly
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [commAt, commSelection, distinct], by simp [commAt, commSelection, madeDistinct],
      rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩
  · intro o member
    simp only [commAt, commSelection, Selection.commit, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact present₁
    · exact present₂
  · intro o member
    simp [commAt, commSelection, Selection.commit] at member
  · simp [commAt, commSelection, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [commAt, commSelection, Selection.commit, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact fresh₁
    · exact fresh₂

/-- **Admission of the COMM firing** at rows that read as the represented inputs. -/
theorem comm_admits (label : O → Pattern) (t u channel A B : Pattern) (C : Configuration Pattern O)
    (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (predot (pFor t channel A)))
    (readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (predot (pFor u channel B)))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    {σ₀ : PSubst} (known : patternAction.Models σ₀ C.equations) (unifies : psubst σ₀ t = psubst σ₀ u)
    {ρ : PSubst} (opensFreshly : (commAt ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E program).Admits (s := embed label C) (commAt ρ first second made₁ made₂) :=
  comm_admits_inputs label t u (predot channel) (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) C
    first second made₁ made₂ (fun σ solved => (readsFirst σ solved).trans (by rw [predot_pFor]))
    (fun σ solved => (readsSecond σ solved).trans (by rw [predot_pFor])) distinct madeDistinct present₁
    present₂ fresh₁ fresh₂ known unifies opensFreshly

/-- **What every solution after the COMM firing says, for rows of any input shape.** Every solution of the
result's knowledge solves the knowledge before, unifies the two patterns, equates the two channels, and
reads each made row as the continuation its taken row holds, read through it. -/
theorem comm_reads_inputs (label : O → Pattern) (t u channel₁ channel₂ K₁ K₂ : Pattern)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (pFor t channel₁ K₁))
    (readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (pFor u channel₂ K₂))
    (madeDistinct : made₁ ≠ made₂) (ρ : PSubst) {σ : PSubst}
    (solved : patternAction.Models σ ((commAt ρ first second made₁ made₂).result X (embed label C)).knowledge) :
    patternAction.Models σ C.equations ∧ psubst σ t = psubst σ u ∧ psubst σ channel₁ = psubst σ channel₂ ∧
      psubst σ (((commAt ρ first second made₁ made₂).result X (embed label C)).label made₁) = psubst σ K₁ ∧
      psubst σ (((commAt ρ first second made₁ made₂).result X (embed label C)).label made₂) = psubst σ K₂ := by
  have info : ((commAt ρ first second made₁ made₂).result X (embed label C)).knowledge =
      (commAt ρ first second made₁ made₂).information X (embed label C) := rfl
  rw [info, commAt_information] at solved
  have known : patternAction.Models σ C.equations := fun e member => solved e (by simp [member])
  have take₁ : psubst σ (psubst ρ (pFor firstPattern channelUnknown firstBody)) = psubst σ (label first) :=
    solved (psubst ρ (pFor firstPattern channelUnknown firstBody), label first) (by simp)
  have take₂ : psubst σ (psubst ρ (pFor secondPattern channelUnknown secondBody)) =
      psubst σ (label second) :=
    solved (psubst ρ (pFor secondPattern channelUnknown secondBody), label second) (by simp)
  have told : psubst σ (psubst ρ firstPattern) = psubst σ (psubst ρ secondPattern) :=
    solved (psubst ρ firstPattern, psubst ρ secondPattern) (by simp)
  rw [readsFirst σ known] at take₁
  rw [readsSecond σ known] at take₂
  simp only [psubst_pFor] at take₁ take₂
  obtain ⟨pattern₁, channel₁', body₁⟩ := pFor_inj take₁
  obtain ⟨pattern₂, channel₂', body₂⟩ := pFor_inj take₂
  refine ⟨known, pattern₁.symm.trans (told.trans pattern₂), channel₁'.symm.trans channel₂', ?_, ?_⟩
  · rw [commAt_label₁, body₁]
  · rw [commAt_label₂ label C ρ first second madeDistinct, body₂]

/-- Every result solution reads the completed principal dot, without a
ground-value hypothesis or a ground-unifiability condition on the store. -/
theorem comm_reads_principal
    (label : O → Pattern) (C : Configuration Pattern O)
    (t u channel P Q : Pattern) (bindings : Bindings) (principal : MeTTaCalculus.Corrected.Principal t u bindings)
    (first second madeFirst madeSecond : O) (opening : PSubst)
    (readsFirst : ∀ point : PSubst, patternAction.Models point C.equations →
      psubst point (label first) = psubst point (pFor t channel (dotted (pvars t ++ pvars u) P)))
    (readsSecond : ∀ point : PSubst, patternAction.Models point C.equations →
      psubst point (label second) = psubst point (pFor u channel (dotted (pvars t ++ pvars u) Q)))
    (distinct : madeFirst ≠ madeSecond) (point : PSubst)
    (solved : patternAction.Models point
      ((FiniteProgram.commAt opening first second madeFirst madeSecond).result X (embed label C)).knowledge)
    (firstOrderP : firstOrder P = true) (firstOrderQ : firstOrder Q = true) :
    psubst point
        (((FiniteProgram.commAt opening first second madeFirst madeSecond).result X (embed label C)).label madeFirst) =
      psubst point (applyDot (MeTTaCalculus.Corrected.completeBindings (pvars t ++ pvars u) bindings) P) ∧
    psubst point
        (((FiniteProgram.commAt opening first second madeFirst madeSecond).result X (embed label C)).label madeSecond) =
      psubst point (applyDot (MeTTaCalculus.Corrected.completeBindings (pvars t ++ pvars u) bindings) Q) := by
  obtain ⟨_, unifies, _, firstRead, secondRead⟩ := FiniteProgram.comm_reads_inputs label t u channel channel
    (dotted (pvars t ++ pvars u) P) (dotted (pvars t ++ pvars u) Q) C first second madeFirst madeSecond
    readsFirst readsSecond distinct opening solved
  rw [MeTTaCalculus.Corrected.applyDot_completeBindings principal P firstOrderP,
    MeTTaCalculus.Corrected.applyDot_completeBindings principal Q firstOrderQ]
  exact ⟨firstRead.trans (MeTTaCalculus.Corrected.firing_reads_uniform_dot principal unifies P),
    secondRead.trans (MeTTaCalculus.Corrected.firing_reads_uniform_dot principal unifies Q)⟩

/-- **What every solution after the COMM firing reads.** Every solution of the result's knowledge
solves the knowledge before, unifies the two patterns, and reads the made rows as the representations of
the dotted continuations, read through it. -/
theorem comm_reads (label : O → Pattern) (t u channel A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (predot (pFor t channel A)))
    (readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (predot (pFor u channel B)))
    (madeDistinct : made₁ ≠ made₂) (ρ : PSubst) {σ : PSubst}
    (solved : patternAction.Models σ ((commAt ρ first second made₁ made₂).result X (embed label C)).knowledge) :
    patternAction.Models σ C.equations ∧ psubst σ t = psubst σ u ∧
      psubst σ (((commAt ρ first second made₁ made₂).result X (embed label C)).label made₁) =
        psubst σ (predot (applyDot bs A)) ∧
      psubst σ (((commAt ρ first second made₁ made₂).result X (embed label C)).label made₂) =
        psubst σ (predot (applyDot bs B)) := by
  obtain ⟨known, unify, -, body₁, body₂⟩ := comm_reads_inputs label t u (predot channel) (predot channel)
    (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) C first second made₁ made₂
    (fun σ solved => (readsFirst σ solved).trans (by rw [predot_pFor]))
    (fun σ solved => (readsSecond σ solved).trans (by rw [predot_pFor])) madeDistinct ρ solved
  obtain ⟨keptA, keptB⟩ := keys_of_apart convention
  refine ⟨known, unify, ?_, ?_⟩
  · rw [body₁]
    refine dotted_reads_predot gp.keys gp.covers (gp.principal σ unify) A foA
      (fun x inside => List.mem_append_left _ inside) ?_ keptA
    intro x inA inKeys
    rcases List.mem_append.mp inKeys with inT | inU
    · exact inT
    · exact absurd inA (convention.rightOutside x inU)
  · rw [body₂]
    refine dotted_reads_predot gp.keys gp.covers (gp.principal σ unify) B foB
      (fun x inside => List.mem_append_right _ inside) ?_ keptB
    intro x inB inKeys
    rcases List.mem_append.mp inKeys with inT | inU
    · exact absurd inB (convention.leftOutside x inT)
    · exact inU

/-- **COMM as one firing of a finite program.** For every redex `for(t <- x)A | for(u <- x)B`, under its
side conditions, each named: a ground principal unifier (`gp`), the variable convention (`convention`),
first-order continuations (`foA`, `foB`); the two taken rows read as the represented inputs at every
solution of the knowledge (`readsFirst`, `readsSecond`); the made identities are distinct and not present;
some solution of the knowledge unifies the patterns (`glued`). Then at every fresh opening the COMM firing
of the fixed three-rule `program` is admitted; the manuscript's rule relates the redex to its dotted
reduct, as written and in the corrected semantics; and every solution of the result's knowledge reads
the made rows as the representations of the dotted continuations, read through it. -/
theorem comm_one_firing (label : O → Pattern) (t u channel A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (predot (pFor t channel A)))
    (readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (predot (pFor u channel B)))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (glued : ∃ σ₀ : PSubst, patternAction.Models σ₀ C.equations ∧ psubst σ₀ t = psubst σ₀ u)
    {ρ : PSubst} (opensFreshly : (commAt ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E program).Admits (s := embed label C) (commAt ρ first second made₁ made₂) ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel A) (pFor u channel B))
        (par (applyDot bs A) (applyDot bs B)) ∧
      MeTTaCalculus.Corrected.Step MeTTaCalculus.Corrected.conventional
        (par (pFor t channel A) (pFor u channel B)) (par (applyDot bs A) (applyDot bs B)) ∧
      ∀ σ : PSubst, patternAction.Models σ
          ((commAt ρ first second made₁ made₂).result X (embed label C)).knowledge →
        psubst σ (((commAt ρ first second made₁ made₂).result X (embed label C)).label made₁) =
            psubst σ (predot (applyDot bs A)) ∧
          psubst σ (((commAt ρ first second made₁ made₂).result X (embed label C)).label made₂) =
            psubst σ (predot (applyDot bs B)) := by
  obtain ⟨σ₀, known, unifies⟩ := glued
  refine ⟨comm_admits label t u channel A B C first second made₁ made₂ readsFirst readsSecond distinct
    madeDistinct present₁ present₂ fresh₁ fresh₂ known unifies opensFreshly,
    .comm t u channel A B bs gp, .comm t u channel A B bs (Comm.principal_of_groundPrincipal gp) convention,
    fun σ solved => ?_⟩
  obtain ⟨-, -, read₁, read₂⟩ := comm_reads label t u channel A B bs gp convention foA foB C first second
    made₁ made₂ readsFirst readsSecond madeDistinct ρ solved
  exact ⟨read₁, read₂⟩

/-- **Closed continuations read a fixed pattern.** Under the side conditions of `comm_one_firing`, with the
taken rows labelled by the represented inputs, the knowledge's variables apart from the patterns'
(`apart`) and the knowledge consistent (`base`), and each continuation's variables its own pattern's
(`closedA`, `closedB`): every solution of the result's knowledge reads the made rows as exactly the
manuscript's dotted continuations. -/
theorem comm_one_firing_closed (label : O → Pattern) (t u channel A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (closedA : ∀ x ∈ pvars A, x ∈ pvars t) (closedB : ∀ x ∈ pvars B, x ∈ pvars u)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (labelFirst : label first = predot (pFor t channel A))
    (labelSecond : label second = predot (pFor u channel B))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars C.equations)
    (base : patternAction.Consistent C.equations)
    {ρ : PSubst} (opensFreshly : (commAt ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E program).Admits (s := embed label C) (commAt ρ first second made₁ made₂) ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel A) (pFor u channel B))
        (par (applyDot bs A) (applyDot bs B)) ∧
      ∀ σ : PSubst, patternAction.Models σ
          ((commAt ρ first second made₁ made₂).result X (embed label C)).knowledge →
        psubst σ (((commAt ρ first second made₁ made₂).result X (embed label C)).label made₁) =
            applyDot bs A ∧
          psubst σ (((commAt ρ first second made₁ made₂).result X (embed label C)).label made₂) =
            applyDot bs B := by
  obtain ⟨admitted, manuscript, -, reads⟩ := comm_one_firing label t u channel A B bs gp convention foA foB
    C first second made₁ made₂ (fun σ _ => congrArg (psubst σ) labelFirst)
    (fun σ _ => congrArg (psubst σ) labelSecond) distinct madeDistinct present₁ present₂ fresh₁ fresh₂
    (Comm.glued_solution gp.solves apart base) opensFreshly
  have groundA : pvars (applyDot bs A) = [] :=
    Comm.applyDot_ground gp A foA fun x inside => List.mem_append_left _ (closedA x inside)
  have groundB : pvars (applyDot bs B) = [] :=
    Comm.applyDot_ground gp B foB fun x inside => List.mem_append_right _ (closedB x inside)
  refine ⟨admitted, manuscript, fun σ solved => ?_⟩
  obtain ⟨read₁, read₂⟩ := reads σ solved
  rw [predot_ground _ groundA, psubst_of_pvars_nil σ _ groundA] at read₁
  rw [predot_ground _ groundB, psubst_of_pvars_nil σ _ groundB] at read₂
  exact ⟨read₁, read₂⟩

omit [DecidableEq O] in
/-- **Every COMM firing has a fresh opening.** -/
theorem exists_fresh_opening (label : O → Pattern) (C : Configuration Pattern O) (first second made₁ made₂ : O) :
    ∃ ρ : PSubst, (commAt ρ first second made₁ made₂).Fresh X (embed label C) := by
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming (embed label C) (ruleVars commRule)
  exact ⟨renameBy g, Comm.fresh_of_renaming (embed label C) _ g rfl injective avoids⟩

/-- **The COMM transition of the finite program, with its result.** Under the side conditions of
`comm_one_firing` (no opening is assumed: a fresh one exists), the step of the fixed `program` moves the
embedded configuration to a state whose present rows are the old ones with the inputs replaced by the made
identities, whose other labels are unchanged, whose knowledge has a solution, and every solution of
whose knowledge reads the made rows as the representations of the dotted continuations. -/
theorem comm_one_transition (label : O → Pattern) (t u channel A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (predot (pFor t channel A)))
    (readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (predot (pFor u channel B)))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (glued : ∃ σ₀ : PSubst, patternAction.Models σ₀ C.equations ∧ psubst σ₀ t = psubst σ₀ u) :
    ∃ s' : State Tm O, Succ (RuleSyntax.step X O E program).toStep (embed label C) s' ∧
      s'.present = (C.present \ {first, second}) ∪ {made₁, made₂} ∧
      (∀ o, o ≠ made₁ → o ≠ made₂ → s'.label o = label o) ∧
      (∃ σ : PSubst, patternAction.Models σ s'.knowledge) ∧
      ∀ σ : PSubst, patternAction.Models σ s'.knowledge →
        psubst σ (s'.label made₁) = psubst σ (predot (applyDot bs A)) ∧
          psubst σ (s'.label made₂) = psubst σ (predot (applyDot bs B)) := by
  obtain ⟨ρ, opensFreshly⟩ := exists_fresh_opening label C first second made₁ made₂
  obtain ⟨admitted, -, -, reads⟩ := comm_one_firing label t u channel A B bs gp convention foA foB C first
    second made₁ made₂ readsFirst readsSecond distinct madeDistinct present₁ present₂ fresh₁ fresh₂ glued
    opensFreshly
  obtain ⟨_, σ, solvedσ⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  refine ⟨(commAt ρ first second made₁ made₂).result X (embed label C), ⟨_, admitted, rfl⟩, ?_,
    fun o other₁ other₂ => ?_, ⟨σ, solvedσ⟩, reads⟩
  · show fire C.present ((commSelection first second made₁ made₂).commit (T := Unit)) = _
    simp [fire, Selection.commit, commSelection]
  · have absent : o ∉ (commAt ρ first second made₁ made₂).selection.made := by
      simp [commAt, commSelection, other₁, other₂]
    exact (Firing.result_label_other (X := X) (s := embed label C) _ absent).trans (psubst_none (label o))

end Step

#print axioms program_finite
#print axioms predot_ground
#print axioms mem_pvars_predot
#print axioms dotted_psubst_comm
#print axioms predot_psubst
#print axioms dotted_reads_predot
#print axioms commAt_information
#print axioms comm_amalgamates
#print axioms comm_admits_inputs
#print axioms comm_admits
#print axioms comm_reads_inputs
#print axioms comm_reads
#print axioms comm_one_firing
#print axioms comm_one_firing_closed
#print axioms exists_fresh_opening
#print axioms comm_one_transition

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteProgram
