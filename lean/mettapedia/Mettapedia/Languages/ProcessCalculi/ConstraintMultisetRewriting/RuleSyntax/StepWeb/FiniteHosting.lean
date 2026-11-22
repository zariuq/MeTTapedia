import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteComm

/-!
# The manuscript's calculus on the one-match step by a finite program: the correspondence

The step is the one-match step of a program at the one frame of structural substitution on patterns
(firings move along the identity), with the five choices stated in `FiniteComm`: a bag store, one match,
guards asked after the firing's own tells (the rules have none), a fixed set of rules beside the store,
one store of knowledge. The program is the three-rule `program` of `FiniteComm`: comm, heating of a binary
parallel composition, clearing of `0`.

## The source

`BagComm` is the manuscript's COMM on a bag of parallel parts (`parts`: a binary parallel composition is
split, `0` is dropped): two inputs `for(t <- x)A` and `for(u <- x)B` of the bag are replaced by the parts of
`applyDot bs A` and `applyDot bs B`, where `bs` is a ground principal unifier of `t` and `u` with
first-order values, under the variable convention (`Corrected.Apart`). With the bag laws of binary
parallel composition this is the manuscript's COMM, PAR and EQUIV on the parallel structure, in the
corrected reading; REFL is not hosted.

## The fragment

A part is hosted (`Hosted`) when it is first-order and either has no variable or is an input on a channel
without variables whose continuation's variables are its own pattern's and whose continuation binds
nothing. A process is hosted (`HostedProcess`) when its parts are, and no two parts share a variable.
Binding happens at the inputs that are parts; a continuation that binds again is not in the fragment
(one COMM on it is still one firing, by `comm_one_firing`; runs through it are in `FiniteNested`).

## Representation

`RepresentsBy s M comp`: the knowledge is consistent; every present row reads, at every solution of the
knowledge, as the representation `predot` of its part; every part is hosted; a part with variables is the
row's own label, represented; its variables occur neither in the knowledge nor in another row's label;
and the parts of the rows sum to the bag `M`.

## The correspondence (`manuscript_calculus_by_a_finite_program`)

1. every hosted process is represented;
2. every transition of the step is a communication or housekeeping;
3. housekeeping keeps the represented bag;
4. at a bag whose unifiable pairs of inputs have ground principal unifiers with first-order values
   (`GroundUnifiable`), a communication is a source step;
5. every source step is matched by housekeeping firings and one communication;
6. a run of `k` housekeeping firings has `k` at most the spine weight of the parts.

The side conditions, each by name: a ground principal unifier (`GroundPrincipal`, in `BagComm` and
`GroundUnifiable`), first-order values (the same), the variable convention (`Corrected.Apart`, in
`BagComm`; derived from the representation in `RepresentsBy.convention`), first-order and closed
continuations without inner binders (`Hosted`). The program is finite (`program_finite`).

## What is not shown

Continuations that bind again (`FiniteNested`); REFL; parallel bags other than binary compositions with
`0`; renaming a process into the variable convention; the converse of `FiniteBridge`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteProgram

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot)
open MeTTaOperationsComm (psubst psubst_none psubst_of_pvars_nil pvars patternAction PSubst dotted
  commSelection GroundPrincipal storePVars applyDot_eq psubst_pFor firstOrder)
open MeTTaCalculus.Corrected (binders binders_apply bindersFor_cons3 bindersFor_short Apart
  binders_subset_pvars mem_pvars_psubst pvars_pFor)
open Comm (Tm X E renameBy ruleVars)
open OneFrame (embed)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)

/-! ## Parallel parts and the spine weight -/

/-- **The parallel parts of a process**: a binary parallel composition is split, `0` is dropped, and every
other process is one part. -/
def parts : Pattern → List Pattern
  | .collection .hashBag [a, b] none => parts a ++ parts b
  | p => if p = pZero then [] else [p]

/-- **The spine weight**: one for each binary parallel composition and each `0` along the parallel
structure. -/
def weight : Pattern → ℕ
  | .collection .hashBag [a, b] none => weight a + weight b + 1
  | p => if p = pZero then 1 else 0

/-- A binary parallel composition. -/
def IsPar (p : Pattern) : Prop := ∃ a b, p = par a b

theorem parts_par (a b : Pattern) : parts (par a b) = parts a ++ parts b := by
  simp [par, MeTTaCalculus.pPar, parts]

theorem weight_par (a b : Pattern) : weight (par a b) = weight a + weight b + 1 := by
  simp [par, MeTTaCalculus.pPar, weight]

theorem parts_of_not_par {p : Pattern} (notPar : ¬ IsPar p) : parts p = if p = pZero then [] else [p] := by
  unfold parts
  split
  · rename_i a b
    exact absurd ⟨a, b, rfl⟩ notPar
  · rfl

theorem weight_of_not_par {p : Pattern} (notPar : ¬ IsPar p) : weight p = if p = pZero then 1 else 0 := by
  unfold weight
  split
  · rename_i a b
    exact absurd ⟨a, b, rfl⟩ notPar
  · rfl

theorem not_par_pZero : ¬ IsPar pZero := by
  rintro ⟨a, b, same⟩
  simp [pZero, par, MeTTaCalculus.pPar] at same

theorem not_par_pFor (t x k : Pattern) : ¬ IsPar (pFor t x k) := by
  rintro ⟨a, b, same⟩
  simp [pFor, par, MeTTaCalculus.pPar] at same

theorem pFor_ne_pZero (t x k : Pattern) : pFor t x k ≠ pZero := by
  simp [pFor, pZero]

theorem parts_pZero : parts pZero = [] := by
  rw [parts_of_not_par not_par_pZero, if_pos rfl]

theorem weight_pZero : weight pZero = 1 := by
  rw [weight_of_not_par not_par_pZero, if_pos rfl]

theorem parts_pFor (t x k : Pattern) : parts (pFor t x k) = [pFor t x k] := by
  rw [parts_of_not_par (not_par_pFor t x k), if_neg (pFor_ne_pZero t x k)]

/-- A process of weight zero is its own only part. -/
theorem parts_of_light {p : Pattern} (light : weight p = 0) : parts p = [p] := by
  by_cases isPar : IsPar p
  · obtain ⟨a, b, rfl⟩ := isPar
    rw [weight_par] at light
    omega
  · rw [weight_of_not_par isPar] at light
    rw [parts_of_not_par isPar]
    split_ifs with zero
    · rw [if_pos zero] at light
      exact absurd light one_ne_zero
    · rfl

theorem parts_coe_of_light {p : Pattern} (light : weight p = 0) : (parts p : Multiset Pattern) = {p} := by
  rw [parts_of_light light]
  rfl

/-- A process of positive weight is `0` or a binary parallel composition. -/
theorem heavy_shape {p : Pattern} (heavy : weight p ≠ 0) : p = pZero ∨ IsPar p := by
  by_cases isPar : IsPar p
  · exact .inr isPar
  · rw [weight_of_not_par isPar] at heavy
    split_ifs at heavy with zero
    · exact .inl zero
    · exact absurd rfl heavy

/-- A part that is no parallel composition is its own only part. -/
theorem parts_self_of_not_par {p c : Pattern} (notPar : ¬ IsPar p) (member : c ∈ parts p) :
    parts c = [c] := by
  rw [parts_of_not_par notPar] at member
  split_ifs at member with zero
  · exact absurd member List.not_mem_nil
  · rw [List.mem_singleton] at member
    subst member
    rw [parts_of_not_par notPar, if_neg zero]

/-- **Every part of a process is its own only part.** -/
theorem parts_of_mem_parts (p : Pattern) : ∀ c ∈ parts p, parts c = [c] := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ c ∈ parts q, parts c = [c]) with
  | collection ct elems rest ih =>
      intro c member
      by_cases isPar : IsPar (.collection ct elems rest)
      · obtain ⟨a, b, same⟩ := isPar
        simp only [par, MeTTaCalculus.pPar, Pattern.collection.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        rw [show Pattern.collection .hashBag [a, b] none = par a b from rfl, parts_par] at member
        rcases List.mem_append.mp member with inA | inB
        · exact ih a (by simp) c inA
        · exact ih b (by simp) c inB
      · exact parts_self_of_not_par isPar member
  | bvar n => exact fun c member => parts_self_of_not_par (by rintro ⟨a, b, same⟩; cases same) member
  | fvar x => exact fun c member => parts_self_of_not_par (by rintro ⟨a, b, same⟩; cases same) member
  | apply f args ih =>
      exact fun c member => parts_self_of_not_par (by rintro ⟨a, b, same⟩; cases same) member
  | lambda nm body ih =>
      exact fun c member => parts_self_of_not_par (by rintro ⟨a, b, same⟩; cases same) member
  | multiLambda n nms body ih =>
      exact fun c member => parts_self_of_not_par (by rintro ⟨a, b, same⟩; cases same) member
  | subst body repl ihb ihr =>
      exact fun c member => parts_self_of_not_par (by rintro ⟨a, b, same⟩; cases same) member
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member c inC
      rcases List.mem_cons.mp member with rfl | later
      · exact head c inC
      · exact tail q later c inC

/-! ## The hosted fragment -/

/-- **A hosted part**: first-order, and either without variables, or an input on a channel without
variables whose continuation's variables are its own pattern's and whose continuation binds nothing. -/
def Hosted (c : Pattern) : Prop :=
  firstOrder c = true ∧ (pvars c = [] ∨
    ∃ t x A, c = pFor t x A ∧ pvars x = [] ∧ (∀ y ∈ pvars A, y ∈ pvars t) ∧ binders A = [])

theorem firstOrderList_iff (ps : List Pattern) :
    MeTTaOperationsComm.firstOrder.firstOrderList ps = true ↔ ∀ q ∈ ps, firstOrder q = true := by
  induction ps with
  | nil => simp [MeTTaOperationsComm.firstOrder.firstOrderList]
  | cons p ps ih => simp [MeTTaOperationsComm.firstOrder.firstOrderList, ih]

theorem firstOrder_pFor {t x k : Pattern} :
    firstOrder (pFor t x k) = true ↔ firstOrder t = true ∧ firstOrder x = true ∧ firstOrder k = true := by
  simp [pFor, firstOrder, MeTTaOperationsComm.firstOrder.firstOrderList]

theorem firstOrder_par {a b : Pattern} :
    firstOrder (par a b) = true ↔ firstOrder a = true ∧ firstOrder b = true := by
  simp [par, MeTTaCalculus.pPar, firstOrder, MeTTaOperationsComm.firstOrder.firstOrderList]

/-- A pattern whose inner patterns bind nothing is its own representation. -/
theorem predot_of_binders_nil (p : Pattern) (noBinders : binders p = []) : predot p = p := by
  revert noBinders
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, binders q = [] → predot q = q) with
  | bvar n => intro _; rfl
  | fvar x => intro _; rfl
  | apply c args ih =>
      intro noBinders
      rw [binders_apply] at noBinders
      rw [predot_apply]
      congr 1
      split_ifs at noBinders ⊢ with isFor
      · match args, ih, noBinders with
        | t :: x :: k :: rest, ih, noBinders =>
            rw [bindersFor_cons3] at noBinders
            simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at noBinders
            obtain ⟨⟨⟨tNone, xNone⟩, kNone⟩, restNone⟩ := noBinders
            rw [predotFor_cons3, tNone, dotted_nil, ih x (by simp) xNone, ih k (by simp) kNone]
            have restSame : rest.map predot = rest := by
              conv => rhs; rw [← List.map_id rest]
              exact List.map_congr_left fun q member => ih q (by simp [member]) (restNone q member)
            rw [restSame]
        | [], _, _ => rfl
        | [p], ih, noBinders =>
            rw [bindersFor_short [p] (by simp), List.flatMap_eq_nil_iff] at noBinders
            rw [predotFor_short [p] (by simp)]
            conv => rhs; rw [← List.map_id [p]]
            exact List.map_congr_left fun q member => ih q member (noBinders q member)
        | [p, q], ih, noBinders =>
            rw [bindersFor_short [p, q] (by simp), List.flatMap_eq_nil_iff] at noBinders
            rw [predotFor_short [p, q] (by simp)]
            conv => rhs; rw [← List.map_id [p, q]]
            exact List.map_congr_left fun r member => ih r member (noBinders r member)
      · rw [List.flatMap_eq_nil_iff] at noBinders
        conv => rhs; rw [← List.map_id args]
        exact List.map_congr_left fun q member => ih q member (noBinders q member)
  | lambda nm body ih =>
      intro noBinders
      simp only [predot]
      rw [ih (by simpa [binders] using noBinders)]
  | multiLambda n nms body ih =>
      intro noBinders
      simp only [predot]
      rw [ih (by simpa [binders] using noBinders)]
  | subst body repl ihb ihr =>
      intro noBinders
      have both : binders body = [] ∧ binders repl = [] := by simpa [binders] using noBinders
      simp only [predot]
      rw [ihb both.1, ihr both.2]
  | collection ct elems rest ih =>
      intro noBinders
      have each : ∀ q ∈ elems, binders q = [] := by
        have flat : elems.flatMap binders = [] := by
          simpa [binders, MeTTaCalculus.Corrected.bindersList_eq_flatMap] using noBinders
        exact List.flatMap_eq_nil_iff.mp flat
      simp only [predot, predotList_eq_map]
      congr 1
      conv => rhs; rw [← List.map_id elems]
      exact List.map_congr_left fun q member => ih q member (each q member)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member noQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head noQ
      · exact tail q later noQ

/-- **The facts of a hosted input.** -/
theorem Hosted.input {t x A : Pattern} (hosted : Hosted (pFor t x A)) :
    pvars x = [] ∧ (∀ y ∈ pvars A, y ∈ pvars t) ∧ binders A = [] ∧ firstOrder A = true := by
  obtain ⟨fo, ground | ⟨t', x', A', same, groundX, closed, noBinders⟩⟩ := hosted
  · rw [pvars_pFor] at ground
    have pieces : pvars t = [] ∧ pvars x = [] ∧ pvars A = [] := by simpa using ground
    refine ⟨pieces.2.1, fun y inside => by rw [pieces.2.2] at inside; exact absurd inside List.not_mem_nil,
      ?_, (firstOrder_pFor.mp fo).2.2⟩
    exact List.eq_nil_iff_forall_not_mem.mpr fun y inside => by
      have inA := binders_subset_pvars A y inside
      rw [pieces.2.2] at inA
      exact List.not_mem_nil inA
  · obtain ⟨rfl, rfl, rfl⟩ := pFor_inj same
    exact ⟨groundX, closed, noBinders, (firstOrder_pFor.mp fo).2.2⟩

/-- **A hosted input's representation**: its continuation dotted by its pattern's variables. -/
theorem Hosted.predot_input {t x A : Pattern} (hosted : Hosted (pFor t x A)) :
    predot (pFor t x A) = pFor t x (dotted (pvars t) A) := by
  obtain ⟨groundX, -, noBinders, -⟩ := hosted.input
  rw [predot_pFor, predot_ground x groundX, predot_of_binders_nil A noBinders]

/-- **Every variable of a hosted part is a variable of its representation.** -/
theorem Hosted.mem_pvars_predot {c : Pattern} (hosted : Hosted c) {y : String} (inside : y ∈ pvars c) :
    y ∈ pvars (predot c) := by
  by_cases ground : pvars c = []
  · rw [ground] at inside
    exact absurd inside List.not_mem_nil
  · obtain ⟨t, x, A, rfl, -, -, -⟩ := hosted.2.resolve_left ground
    rw [hosted.predot_input, pvars_pFor]
    rw [pvars_pFor] at inside
    simp only [List.mem_append] at inside ⊢
    rcases inside with (inT | inX) | inA
    · exact .inl (.inl inT)
    · exact .inl (.inr inX)
    · exact .inr (mem_pvars_dotted.mpr inA)

/-- A hosted part read as an input is an input. -/
theorem Hosted.input_of_instance {c : Pattern} (hosted : Hosted c) {σ : PSubst} {a b d : Pattern}
    (same : psubst σ (predot c) = pFor a b d) : ∃ t x A, c = pFor t x A := by
  obtain ⟨-, ground | ⟨t, x, A, rfl, -, -, -⟩⟩ := hosted
  · rw [predot_ground c ground, psubst_of_pvars_nil σ c ground] at same
    exact ⟨a, b, d, same⟩
  · exact ⟨t, x, A, rfl⟩

/-- A hosted part read as a binary parallel composition is one, without variables. -/
theorem Hosted.par_of_instance {c : Pattern} (hosted : Hosted c) {σ : PSubst} {a b : Pattern}
    (same : psubst σ (predot c) = par a b) : c = par a b ∧ pvars c = [] := by
  obtain ⟨-, ground | ⟨t, x, A, rfl, -, -, -⟩⟩ := hosted
  · rw [predot_ground c ground, psubst_of_pvars_nil σ c ground] at same
    exact ⟨same, ground⟩
  · rw [predot_pFor, psubst_pFor] at same
    simp [pFor, par, MeTTaCalculus.pPar] at same

/-- A hosted part read as `0` is `0`. -/
theorem Hosted.zero_of_instance {c : Pattern} (hosted : Hosted c) {σ : PSubst}
    (same : psubst σ (predot c) = pZero) : c = pZero := by
  obtain ⟨-, ground | ⟨t, x, A, rfl, -, -, -⟩⟩ := hosted
  · rw [predot_ground c ground, psubst_of_pvars_nil σ c ground] at same
    exact same
  · rw [predot_pFor, psubst_pFor] at same
    exact absurd same (pFor_ne_pZero _ _ _)

/-- The parts of a hosted binary parallel composition are hosted and have no variable. -/
theorem Hosted.parts_of_par {a b : Pattern} (hosted : Hosted (par a b)) :
    (Hosted a ∧ pvars a = []) ∧ (Hosted b ∧ pvars b = []) := by
  obtain ⟨fo, ground | ⟨t, x, A, same, -, -, -⟩⟩ := hosted
  · rw [MeTTaCalculus.Corrected.pvars_par] at ground
    have both : pvars a = [] ∧ pvars b = [] := List.append_eq_nil_iff.mp ground
    obtain ⟨foA, foB⟩ := firstOrder_par.mp fo
    exact ⟨⟨⟨foA, .inl both.1⟩, both.1⟩, ⟨⟨foB, .inl both.2⟩, both.2⟩⟩
  · simp [pFor, par, MeTTaCalculus.pPar] at same

/-! ## First-order substitution and the dotted continuations -/

theorem firstOrder_psubst {τ : PSubst} (values : ∀ x v, τ x = some v → firstOrder v = true) (p : Pattern)
    (fo : firstOrder p = true) : firstOrder (psubst τ p) = true := by
  revert fo
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, firstOrder q = true →
      firstOrder (psubst τ q) = true) with
  | bvar n => intro _; rfl
  | fvar x =>
      intro _
      show firstOrder ((τ x).getD (.fvar x)) = true
      cases found : τ x with
      | some v => exact values x v found
      | none => rfl
  | apply c args ih =>
      intro fo
      simp only [firstOrder, firstOrderList_iff] at fo
      simp only [psubst, MeTTaCalculus.Corrected.psubstList_eq_map, firstOrder, firstOrderList_iff,
        List.mem_map]
      rintro q ⟨r, inArgs, rfl⟩
      exact ih r inArgs (fo r inArgs)
  | lambda nm body ih =>
      intro fo
      simp only [psubst, firstOrder] at fo ⊢
      exact ih fo
  | multiLambda n nms body ih =>
      intro fo
      simp only [psubst, firstOrder] at fo ⊢
      exact ih fo
  | subst body repl ihb ihr => intro fo; simp [firstOrder] at fo
  | collection ct elems rest ih =>
      intro fo
      simp only [firstOrder, Bool.and_eq_true, firstOrderList_iff] at fo
      simp only [psubst, MeTTaCalculus.Corrected.psubstList_eq_map, firstOrder, Bool.and_eq_true,
        firstOrderList_iff, List.mem_map]
      refine ⟨fo.1, ?_⟩
      rintro q ⟨r, inElems, rfl⟩
      exact ih r inElems (fo.2 r inElems)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member foQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head foQ
      · exact tail q later foQ

/-- **A dotted closed first-order continuation is a hosted part without variables**, under a ground
principal unifier with first-order values. -/
theorem hosted_applyDot {t u : Pattern} {bs : Bindings} (gp : GroundPrincipal t u bs)
    (values : ∀ y v, bs.lookup y = some v → firstOrder v = true) {A : Pattern} (fo : firstOrder A = true)
    (closed : ∀ y ∈ pvars A, y ∈ pvars t ++ pvars u) :
    Hosted (applyDot bs A) ∧ pvars (applyDot bs A) = [] := by
  have ground := Comm.applyDot_ground gp A fo closed
  refine ⟨⟨?_, .inl ground⟩, ground⟩
  rw [applyDot_eq bs A fo]
  refine firstOrder_psubst ?_ A fo
  intro y v found
  change (bs.lookup y).map nQuote = some v at found
  obtain ⟨w, look, rfl⟩ := Option.map_eq_some_iff.mp found
  simp [nQuote, firstOrder, MeTTaOperationsComm.firstOrder.firstOrderList, values y w look]

/-! ## The source: the manuscript's COMM on a bag of parts -/

/-- **The manuscript's COMM on a bag of parallel parts.** Two inputs on one channel whose patterns have a
ground principal unifier with first-order values, under the variable convention, are replaced by the
parts of their dotted continuations; every other part stays. -/
inductive BagComm : Multiset Pattern → Multiset Pattern → Prop
  | comm (t u x A B : Pattern) (bs : Bindings) (rest : Multiset Pattern) (gp : GroundPrincipal t u bs)
      (convention : Apart t A u B) (values : ∀ y v, bs.lookup y = some v → firstOrder v = true) :
      BagComm (pFor t x A ::ₘ pFor u x B ::ₘ rest)
        ((parts (applyDot bs A) : Multiset Pattern) + (parts (applyDot bs B) : Multiset Pattern) + rest)

/-- **Every two inputs of a bag on one channel whose patterns unify have a ground principal unifier with
first-order values.** -/
def GroundUnifiable (M : Multiset Pattern) : Prop :=
  ∀ t x A u B, pFor t x A ∈ M → pFor u x B ∈ M.erase (pFor t x A) →
    (∃ σ : PSubst, psubst σ t = psubst σ u) →
    ∃ bs, GroundPrincipal t u bs ∧ ∀ y v, bs.lookup y = some v → firstOrder v = true

/-- **A hosted process**: its parallel parts are hosted, and no two of them share a variable. -/
structure HostedProcess (P : Pattern) : Prop where
  hosted : ∀ c ∈ parts P, Hosted c
  disjoint : (parts P).Pairwise fun c d => ∀ y ∈ pvars c, y ∉ pvars d

/-! ## States that represent a bag -/

/-- The parts of the rows. -/
def bagOf (present : Finset ℕ) (comp : ℕ → Pattern) : Multiset Pattern :=
  ∑ o ∈ present, (parts (comp o) : Multiset Pattern)

/-- The spine weight of the rows. -/
def weightOf (present : Finset ℕ) (comp : ℕ → Pattern) : ℕ := ∑ o ∈ present, weight (comp o)

/-- **A state represents a bag of parts**, through a part for each present row. -/
structure RepresentsBy (s : State Tm ℕ) (M : Multiset Pattern) (comp : ℕ → Pattern) : Prop where
  consistent : patternAction.Consistent s.knowledge
  reads : ∀ o ∈ s.present, ∀ σ : PSubst, patternAction.Models σ s.knowledge →
    psubst σ (s.label o) = psubst σ (predot (comp o))
  hosted : ∀ o ∈ s.present, Hosted (comp o)
  own : ∀ o ∈ s.present, pvars (comp o) ≠ [] → s.label o = predot (comp o)
  hidden : ∀ o ∈ s.present, ∀ y ∈ pvars (comp o), y ∉ storePVars s.knowledge ∧
    ∀ o' ∈ s.present, o' ≠ o → y ∉ pvars (s.label o')
  bag : bagOf s.present comp = M

/-- A state represents a bag. -/
def Represents (s : State Tm ℕ) (M : Multiset Pattern) : Prop := ∃ comp, RepresentsBy s M comp

section Representation

variable {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}

/-- A part's variables occur in its row's label. -/
theorem RepresentsBy.mentioned (represented : RepresentsBy s M comp) {o : ℕ} (present : o ∈ s.present)
    {y : String} (inside : y ∈ pvars (comp o)) : y ∈ pvars (s.label o) := by
  rw [represented.own o present (List.ne_nil_of_mem inside)]
  exact (represented.hosted o present).mem_pvars_predot inside

/-- Two rows' parts share no variable. -/
theorem RepresentsBy.apart_vars (represented : RepresentsBy s M comp) {o₁ o₂ : ℕ}
    (present₁ : o₁ ∈ s.present) (present₂ : o₂ ∈ s.present) (distinct : o₁ ≠ o₂) {y : String}
    (inside : y ∈ pvars (comp o₁)) : y ∉ pvars (comp o₂) := fun inSecond =>
  (represented.hidden o₁ present₁ y inside).2 o₂ present₂ (Ne.symm distinct)
    (represented.mentioned present₂ inSecond)

/-- **Two rows' inputs satisfy the variable convention.** -/
theorem RepresentsBy.convention (represented : RepresentsBy s M comp) {o₁ o₂ : ℕ}
    (present₁ : o₁ ∈ s.present) (present₂ : o₂ ∈ s.present) (distinct : o₁ ≠ o₂) {t x A u x' B : Pattern}
    (first : comp o₁ = pFor t x A) (second : comp o₂ = pFor u x' B) : Apart t A u B := by
  have hostedFirst := represented.hosted o₁ present₁
  rw [first] at hostedFirst
  have hostedSecond := represented.hosted o₂ present₂
  rw [second] at hostedSecond
  obtain ⟨-, -, noA, -⟩ := hostedFirst.input
  obtain ⟨-, -, noB, -⟩ := hostedSecond.input
  have inFirst : ∀ y, y ∈ pvars t ∨ y ∈ pvars A → y ∈ pvars (comp o₁) := by
    intro y inside
    rw [first, pvars_pFor]
    simp only [List.mem_append]
    rcases inside with inT | inA
    · exact .inl (.inl inT)
    · exact .inr inA
  have inSecond : ∀ y, y ∈ pvars u ∨ y ∈ pvars B → y ∈ pvars (comp o₂) := by
    intro y inside
    rw [second, pvars_pFor]
    simp only [List.mem_append]
    rcases inside with inU | inB
    · exact .inl (.inl inU)
    · exact .inr inB
  refine ⟨fun y inT inU => ?_, fun y inT inB => ?_, fun y inU inA => ?_, fun y _ inside => ?_,
    fun y _ inside => ?_⟩
  · exact represented.apart_vars present₁ present₂ distinct (inFirst y (.inl inT)) (inSecond y (.inl inU))
  · exact represented.apart_vars present₁ present₂ distinct (inFirst y (.inl inT)) (inSecond y (.inr inB))
  · exact represented.apart_vars present₂ present₁ (Ne.symm distinct) (inSecond y (.inl inU))
      (inFirst y (.inr inA))
  · rw [noA] at inside
    exact List.not_mem_nil inside
  · rw [noB] at inside
    exact List.not_mem_nil inside

/-- **The parts of two rows that hold inputs, beside the others'.** -/
theorem bagOf_split {present : Finset ℕ} {o₁ o₂ : ℕ} (distinct : o₁ ≠ o₂) (present₁ : o₁ ∈ present)
    (present₂ : o₂ ∈ present) {t x A u x' B : Pattern} (first : comp o₁ = pFor t x A)
    (second : comp o₂ = pFor u x' B) :
    bagOf present comp = pFor t x A ::ₘ pFor u x' B ::ₘ bagOf (present \ {o₁, o₂}) comp := by
  have takenSub : ({o₁, o₂} : Finset ℕ) ⊆ present := by
    intro o member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact present₁
    · exact present₂
  unfold bagOf
  rw [← Finset.sum_sdiff takenSub, Finset.sum_pair distinct, first, second, parts_pFor, parts_pFor]
  simp only [Multiset.coe_singleton]
  rw [← Multiset.singleton_add, ← Multiset.singleton_add]
  abel

/-- **The bag holds the parts of two rows beside the others'.** -/
theorem RepresentsBy.bag_split (represented : RepresentsBy s M comp) {o₁ o₂ : ℕ} (distinct : o₁ ≠ o₂)
    (present₁ : o₁ ∈ s.present) (present₂ : o₂ ∈ s.present) {t x A u x' B : Pattern}
    (first : comp o₁ = pFor t x A) (second : comp o₂ = pFor u x' B) :
    M = pFor t x A ::ₘ pFor u x' B ::ₘ bagOf (s.present \ {o₁, o₂}) comp := by
  rw [← represented.bag]
  exact bagOf_split distinct present₁ present₂ first second

end Representation

/-! ## A fresh opening introduces no mentioned variable -/

/-- **A fresh opening introduces no variable that the state mentions.** -/
theorem fresh_avoids {O : Type*} {Prog : Program Tm} (s : State Tm O) (f : Firing O E Prog s.frame)
    (fresh : f.Fresh X s) {m : Pattern} (mentioned : s.Mentions m) {r : Pattern} (term : r ∈ f.rule.terms)
    {y : String} (inM : y ∈ pvars m) : y ∉ pvars (psubst f.opening r) := by
  intro inR
  obtain ⟨w, state, rule⟩ := fresh PUnit.unit (fun _ => none) (fun _ => some pZero)
  have onState := state m mentioned
  change psubst w (psubst (fun _ => none) m) = psubst (fun _ => none) m at onState
  rw [psubst_none] at onState
  have fixed := Comm.agree_of_psubst_eq (onState.trans (psubst_none m).symm) y inM
  have onRule := rule r term
  change psubst w (psubst f.opening r) = psubst (fun _ => some pZero) r at onRule
  have noVars : pvars (psubst (fun _ => some pZero) r) = [] :=
    Comm.pvars_psubst_eq_nil fun _ _ => ⟨pZero, rfl, rfl⟩
  have still : y ∈ pvars (psubst w (psubst f.opening r)) :=
    (mem_pvars_psubst w _ y).mpr ⟨y, inR, by rw [fixed]; simp [pvars]⟩
  rw [onRule, noVars] at still
  exact List.not_mem_nil still

theorem mem_storePVars {K : EquationStore Pattern} {e : Equation Pattern} (member : e ∈ K) {y : String}
    (occurs : y ∈ pvars e.1 ∨ y ∈ pvars e.2) : y ∈ storePVars K :=
  List.mem_flatMap.mpr ⟨e, member, List.mem_append.mpr occurs⟩

theorem not_mem_storePVars {K : EquationStore Pattern} {y : String}
    (each : ∀ e ∈ K, y ∉ pvars e.1 ∧ y ∉ pvars e.2) : y ∉ storePVars K := by
  intro inside
  obtain ⟨e, member, occurs⟩ := List.mem_flatMap.mp inside
  rcases List.mem_append.mp occurs with one | two
  · exact (each e member).1 one
  · exact (each e member).2 two

/-! ## Transitions -/

/-- A communication firing. -/
def Communicates (s s' : State Tm ℕ) : Prop :=
  ∃ f : Firing ℕ E program s.frame, f.rule = commRule ∧ f.Admits X s ∧ f.result X s = s'

/-- A housekeeping firing: heating or clearing. -/
def Administers (s s' : State Tm ℕ) : Prop :=
  ∃ f : Firing ℕ E program s.frame, (f.rule = heatRule ∨ f.rule = clearRule) ∧ f.Admits X s ∧
    f.result X s = s'

/-- **Every transition of the step is a communication or housekeeping.** -/
theorem succ_iff (s s' : State Tm ℕ) :
    Succ (RuleSyntax.step X ℕ E program).toStep s s' ↔ Communicates s s' ∨ Administers s s' := by
  constructor
  · rintro ⟨f, admitted, rfl⟩
    rcases mem_program.mp f.member with isComm | isHeat | isClear
    · exact .inl ⟨f, isComm, admitted, rfl⟩
    · exact .inr ⟨f, .inl isHeat, admitted, rfl⟩
    · exact .inr ⟨f, .inr isClear, admitted, rfl⟩
  · rintro (⟨f, _, admitted, rfl⟩ | ⟨f, _, admitted, rfl⟩)
    · exact ⟨f, admitted, rfl⟩
    · exact ⟨f, admitted, rfl⟩

/-! ## Firings in normal form -/

/-- **The heating firing**: the heating rule opened by `ρ`, taking `o`, making `m₁` and `m₂`. -/
def heatAt (ρ : PSubst) (o m₁ m₂ : ℕ) : Firing ℕ E program PUnit.unit :=
  ⟨heatRule, heatRule_mem, PUnit.unit, ρ, ⟨[o], [], [m₁, m₂]⟩, []⟩

/-- **The clearing firing**: the clearing rule opened by `ρ`, taking `o`. -/
def clearAt (ρ : PSubst) (o : ℕ) : Firing ℕ E program PUnit.unit :=
  ⟨clearRule, clearRule_mem, PUnit.unit, ρ, ⟨[o], [], []⟩, []⟩

theorem comm_normal {s : State Tm ℕ} (f : Firing ℕ E program s.frame) (isComm : f.rule = commRule)
    (admitted : f.Admits X s) :
    ∃ o₁ o₂ m₁ m₂, f = commAt f.opening o₁ o₂ m₁ m₂ ∧ o₁ ≠ o₂ ∧ m₁ ≠ m₂ ∧ o₁ ∈ s.present ∧
      o₂ ∈ s.present ∧ m₁ ∉ s.present ∧ m₂ ∉ s.present := by
  obtain ⟨rule, member, ext, opening, ⟨taken, readSel, made⟩, seen⟩ := f
  change rule = commRule at isComm
  subst isComm
  obtain ⟨⟨-, takenNodup, madeNodup, takeLen, readLen, produceLen, collectLen⟩, enabled, -, -⟩ := admitted
  change 2 = taken.length at takeLen
  change 0 = readSel.length at readLen
  change 2 = made.length at produceLen
  change 0 = seen.length at collectLen
  obtain ⟨o₁, o₂, rfl⟩ := List.length_eq_two.mp takeLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero readLen.symm
  obtain ⟨m₁, m₂, rfl⟩ := List.length_eq_two.mp produceLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero collectLen.symm
  have freshMade : Disjoint ({m₁, m₂} : Finset ℕ) s.present := by
    simpa [Selection.commit] using enabled.fresh
  exact ⟨o₁, o₂, m₁, m₂, rfl, by simpa using takenNodup, by simpa using madeNodup,
    enabled.taken_subset (by simp [Selection.commit]), enabled.taken_subset (by simp [Selection.commit]),
    fun inside => Finset.disjoint_left.mp freshMade (by simp) inside,
    fun inside => Finset.disjoint_left.mp freshMade (by simp) inside⟩

theorem heat_normal {s : State Tm ℕ} (f : Firing ℕ E program s.frame) (isHeat : f.rule = heatRule)
    (admitted : f.Admits X s) :
    ∃ o m₁ m₂, f = heatAt f.opening o m₁ m₂ ∧ m₁ ≠ m₂ ∧ o ∈ s.present ∧ m₁ ∉ s.present ∧
      m₂ ∉ s.present := by
  obtain ⟨rule, member, ext, opening, ⟨taken, readSel, made⟩, seen⟩ := f
  change rule = heatRule at isHeat
  subst isHeat
  obtain ⟨⟨-, -, madeNodup, takeLen, readLen, produceLen, collectLen⟩, enabled, -, -⟩ := admitted
  change 1 = taken.length at takeLen
  change 0 = readSel.length at readLen
  change 2 = made.length at produceLen
  change 0 = seen.length at collectLen
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp takeLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero readLen.symm
  obtain ⟨m₁, m₂, rfl⟩ := List.length_eq_two.mp produceLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero collectLen.symm
  have freshMade : Disjoint ({m₁, m₂} : Finset ℕ) s.present := by
    simpa [Selection.commit] using enabled.fresh
  exact ⟨o, m₁, m₂, rfl, by simpa using madeNodup, enabled.taken_subset (by simp [Selection.commit]),
    fun inside => Finset.disjoint_left.mp freshMade (by simp) inside,
    fun inside => Finset.disjoint_left.mp freshMade (by simp) inside⟩

theorem clear_normal {s : State Tm ℕ} (f : Firing ℕ E program s.frame) (isClear : f.rule = clearRule)
    (admitted : f.Admits X s) : ∃ o, f = clearAt f.opening o ∧ o ∈ s.present := by
  obtain ⟨rule, member, ext, opening, ⟨taken, readSel, made⟩, seen⟩ := f
  change rule = clearRule at isClear
  subst isClear
  obtain ⟨⟨-, -, -, takeLen, readLen, produceLen, collectLen⟩, enabled, -, -⟩ := admitted
  change 1 = taken.length at takeLen
  change 0 = readSel.length at readLen
  change 0 = made.length at produceLen
  change 0 = seen.length at collectLen
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp takeLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero readLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero produceLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero collectLen.symm
  exact ⟨o, rfl, enabled.taken_subset (by simp [Selection.commit])⟩

section Information

variable (s : State Tm ℕ)

theorem commAt_info (ρ : PSubst) (o₁ o₂ m₁ m₂ : ℕ) :
    (commAt ρ o₁ o₂ m₁ m₂).information X s =
      s.knowledge ++ [(psubst ρ (pFor firstPattern channelUnknown firstBody), s.label o₁),
        (psubst ρ (pFor secondPattern channelUnknown secondBody), s.label o₂)] ++ [] ++
        [(psubst ρ firstPattern, psubst ρ secondPattern)] :=
  commAt_information s.label ⟨s.knowledge, s.present⟩ ρ o₁ o₂ m₁ m₂

theorem heatAt_info (ρ : PSubst) (o m₁ m₂ : ℕ) :
    (heatAt ρ o m₁ m₂).information X s =
      s.knowledge ++ [(psubst ρ (par leftPart rightPart), s.label o)] ++ [] ++ [] :=
  (OneFrame.information_eq (label := s.label) ⟨s.knowledge, s.present⟩ (heatAt ρ o m₁ m₂)).trans rfl

theorem clearAt_info (ρ : PSubst) (o : ℕ) :
    (clearAt ρ o).information X s = s.knowledge ++ [(psubst ρ pZero, s.label o)] ++ [] ++ [] :=
  (OneFrame.information_eq (label := s.label) ⟨s.knowledge, s.present⟩ (clearAt ρ o)).trans rfl

theorem heatAt_label₁ (ρ : PSubst) (o m₁ m₂ : ℕ) :
    ((heatAt ρ o m₁ m₂).result X s).label m₁ = psubst ρ leftPart := by
  show (if m₁ = m₁ then psubst ρ leftPart else _) = _
  rw [if_pos rfl]

theorem heatAt_label₂ (ρ : PSubst) (o : ℕ) {m₁ m₂ : ℕ} (madeDistinct : m₁ ≠ m₂) :
    ((heatAt ρ o m₁ m₂).result X s).label m₂ = psubst ρ rightPart := by
  show (if m₂ = m₁ then _ else if m₂ = m₂ then psubst ρ rightPart else _) = _
  rw [if_neg (Ne.symm madeDistinct), if_pos rfl]

theorem result_label_kept {f : Firing ℕ E program s.frame} {o : ℕ} (absent : o ∉ f.selection.made) :
    (f.result X s).label o = s.label o :=
  (Firing.result_label_other (X := X) (s := s) f absent).trans (psubst_none (s.label o))

end Information

/-! ## What each admitted firing does to a represented state -/

/-- **The parts of an admitted communication**: two inputs on one channel whose patterns some solution
unifies. -/
theorem comm_shape {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) {ρ : PSubst} {o₁ o₂ m₁ m₂ : ℕ}
    (admitted : (commAt ρ o₁ o₂ m₁ m₂).Admits X s) (madeDistinct : m₁ ≠ m₂)
    (present₁ : o₁ ∈ s.present) (present₂ : o₂ ∈ s.present) :
    ∃ t x A u B, comp o₁ = pFor t x A ∧ comp o₂ = pFor u x B ∧ ∃ σ : PSubst, psubst σ t = psubst σ u := by
  obtain ⟨-, -, ⟨_, σ₀, solved₀⟩, -⟩ := admitted
  have solvedInfo : patternAction.Models σ₀ ((commAt ρ o₁ o₂ m₁ m₂).information X s) := solved₀
  rw [commAt_info] at solvedInfo
  have known₀ : patternAction.Models σ₀ s.knowledge := fun e member => solvedInfo e (by simp [member])
  have take₁ : psubst σ₀ (psubst ρ (pFor firstPattern channelUnknown firstBody)) = psubst σ₀ (s.label o₁) :=
    solvedInfo (psubst ρ (pFor firstPattern channelUnknown firstBody), s.label o₁) (by simp)
  have take₂ : psubst σ₀ (psubst ρ (pFor secondPattern channelUnknown secondBody)) =
      psubst σ₀ (s.label o₂) :=
    solvedInfo (psubst ρ (pFor secondPattern channelUnknown secondBody), s.label o₂) (by simp)
  rw [represented.reads o₁ present₁ σ₀ known₀] at take₁
  rw [represented.reads o₂ present₂ σ₀ known₀] at take₂
  simp only [psubst_pFor] at take₁ take₂
  obtain ⟨t, x, A, first⟩ := (represented.hosted o₁ present₁).input_of_instance take₁.symm
  obtain ⟨u, x', B, second⟩ := (represented.hosted o₂ present₂).input_of_instance take₂.symm
  have hostedFirst := represented.hosted o₁ present₁
  rw [first] at hostedFirst
  have hostedSecond := represented.hosted o₂ present₂
  rw [second] at hostedSecond
  obtain ⟨groundX, -, -, -⟩ := hostedFirst.input
  obtain ⟨groundX', -, -, -⟩ := hostedSecond.input
  have resultSolved : patternAction.Models σ₀ ((commAt ρ o₁ o₂ m₁ m₂).result X s).knowledge := solved₀
  obtain ⟨-, unify₀, channel₀, -, -⟩ := comm_reads_inputs s.label t u (predot x) (predot x')
    (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) ⟨s.knowledge, s.present⟩ o₁ o₂ m₁ m₂
    (fun σ known => (represented.reads o₁ present₁ σ known).trans (by rw [first, predot_pFor]))
    (fun σ known => (represented.reads o₂ present₂ σ known).trans (by rw [second, predot_pFor]))
    madeDistinct ρ resultSolved
  rw [predot_ground x groundX, predot_ground x' groundX', psubst_of_pvars_nil σ₀ x groundX,
    psubst_of_pvars_nil σ₀ x' groundX'] at channel₀
  subst channel₀
  exact ⟨t, x, A, u, B, first, second, σ₀, unify₀⟩

/-- The parts after a communication: the dotted continuations at the made identities. -/
def afterComm (comp : ℕ → Pattern) (m₁ m₂ : ℕ) (left right : Pattern) : ℕ → Pattern :=
  fun o => if o = m₁ then left else if o = m₂ then right else comp o

/-- **What a communication firing does.** At a represented state, when the two taken rows hold the inputs
`for(t <- x)A` and `for(u <- x)B` and `bs` is a ground principal unifier of the patterns with first-order
values, the result represents the parts of the dotted continuations beside the other rows' parts. -/
theorem comm_result {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) {ρ : PSubst} {o₁ o₂ m₁ m₂ : ℕ}
    (admitted : (commAt ρ o₁ o₂ m₁ m₂).Admits X s) (distinct : o₁ ≠ o₂) (madeDistinct : m₁ ≠ m₂)
    (present₁ : o₁ ∈ s.present) (present₂ : o₂ ∈ s.present) (fresh₁ : m₁ ∉ s.present)
    (fresh₂ : m₂ ∉ s.present) {t x A u B : Pattern} {bs : Bindings}
    (first : comp o₁ = pFor t x A) (second : comp o₂ = pFor u x B) (gp : GroundPrincipal t u bs)
    (values : ∀ y v, bs.lookup y = some v → firstOrder v = true) :
    RepresentsBy ((commAt ρ o₁ o₂ m₁ m₂).result X s)
      ((parts (applyDot bs A) : Multiset Pattern) + (parts (applyDot bs B) : Multiset Pattern) +
        bagOf (s.present \ {o₁, o₂}) comp)
      (afterComm comp m₁ m₂ (applyDot bs A) (applyDot bs B)) := by
  classical
  obtain ⟨⟨fresh, -⟩, -, ⟨_, σ₀, solved₀⟩, -⟩ := admitted
  have resultSolved : patternAction.Models σ₀ ((commAt ρ o₁ o₂ m₁ m₂).result X s).knowledge := solved₀
  have hostedFirst := represented.hosted o₁ present₁
  rw [first] at hostedFirst
  have hostedSecond := represented.hosted o₂ present₂
  rw [second] at hostedSecond
  obtain ⟨-, closedA, -, foA⟩ := hostedFirst.input
  obtain ⟨-, closedB, -, foB⟩ := hostedSecond.input
  have convention : Apart t A u B := represented.convention present₁ present₂ distinct first second
  have readsFirst : ∀ σ : PSubst, patternAction.Models σ s.knowledge →
      psubst σ (s.label o₁) = psubst σ (predot (pFor t x A)) := fun σ known =>
    (represented.reads o₁ present₁ σ known).trans (by rw [first])
  have readsSecond : ∀ σ : PSubst, patternAction.Models σ s.knowledge →
      psubst σ (s.label o₂) = psubst σ (predot (pFor u x B)) := fun σ known =>
    (represented.reads o₂ present₂ σ known).trans (by rw [second])
  have reads := fun (σ : PSubst)
      (solved : patternAction.Models σ ((commAt ρ o₁ o₂ m₁ m₂).result X s).knowledge) =>
    comm_reads s.label t u x A B bs gp convention foA foB ⟨s.knowledge, s.present⟩ o₁ o₂ m₁ m₂ readsFirst
      readsSecond madeDistinct ρ solved
  obtain ⟨hostedDotA, groundDotA⟩ :=
    hosted_applyDot gp values foA fun y inside => List.mem_append_left _ (closedA y inside)
  obtain ⟨hostedDotB, groundDotB⟩ :=
    hosted_applyDot gp values foB fun y inside => List.mem_append_right _ (closedB y inside)
  have comp'₁ : afterComm comp m₁ m₂ (applyDot bs A) (applyDot bs B) m₁ = applyDot bs A := by
    simp [afterComm]
  have comp'₂ : afterComm comp m₁ m₂ (applyDot bs A) (applyDot bs B) m₂ = applyDot bs B := by
    simp [afterComm, Ne.symm madeDistinct]
  have comp'Old : ∀ o ∈ s.present, afterComm comp m₁ m₂ (applyDot bs A) (applyDot bs B) o = comp o := by
    intro o member
    have n₁ : o ≠ m₁ := fun same => fresh₁ (same ▸ member)
    have n₂ : o ≠ m₂ := fun same => fresh₂ (same ▸ member)
    simp [afterComm, n₁, n₂]
  have resultPresent : ((commAt ρ o₁ o₂ m₁ m₂).result X s).present = (s.present \ {o₁, o₂}) ∪ {m₁, m₂} := by
    show fire s.present ((commSelection o₁ o₂ m₁ m₂).commit (T := Unit)) = _
    simp [fire, Selection.commit, commSelection]
  have labelOld : ∀ o, o ≠ m₁ → o ≠ m₂ → ((commAt ρ o₁ o₂ m₁ m₂).result X s).label o = s.label o := by
    intro o n₁ n₂
    exact result_label_kept s (by simp [commAt, commSelection, n₁, n₂])
  have label₁ : ((commAt ρ o₁ o₂ m₁ m₂).result X s).label m₁ = psubst ρ firstBody :=
    commAt_label₁ s.label ⟨s.knowledge, s.present⟩ ρ o₁ o₂ m₁ m₂
  have label₂ : ((commAt ρ o₁ o₂ m₁ m₂).result X s).label m₂ = psubst ρ secondBody :=
    commAt_label₂ s.label ⟨s.knowledge, s.present⟩ ρ o₁ o₂ madeDistinct
  have oldOf : ∀ o ∈ s.present \ {o₁, o₂}, o ∈ s.present ∧ o ≠ o₁ ∧ o ≠ o₂ := by
    intro o member
    obtain ⟨inside, notTaken⟩ := Finset.mem_sdiff.mp member
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at notTaken
    exact ⟨inside, notTaken.1, notTaken.2⟩
  have mentionedFresh : ∀ o ∈ s.present, ∀ y ∈ pvars (comp o), ∀ r ∈ commRule.terms,
      y ∉ pvars (psubst ρ r) := fun o member y inside r term =>
    fresh_avoids s (commAt ρ o₁ o₂ m₁ m₂) fresh (Or.inr (Or.inr ⟨o, member, rfl⟩)) term
      (represented.mentioned member inside)
  refine ⟨⟨σ₀, resultSolved⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- readings
    intro o member σ solved
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨inside, -, -⟩ := oldOf o old
      have n₁ : o ≠ m₁ := fun same => fresh₁ (same ▸ inside)
      have n₂ : o ≠ m₂ := fun same => fresh₂ (same ▸ inside)
      rw [labelOld o n₁ n₂, comp'Old o inside]
      exact represented.reads o inside σ (reads σ solved).1
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁]
        exact (reads σ solved).2.2.1
      · rw [comp'₂]
        exact (reads σ solved).2.2.2
  · -- hosted
    intro o member
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨inside, -, -⟩ := oldOf o old
      rw [comp'Old o inside]
      exact represented.hosted o inside
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁]; exact hostedDotA
      · rw [comp'₂]; exact hostedDotB
  · -- own labels
    intro o member withVars
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨inside, -, -⟩ := oldOf o old
      have n₁ : o ≠ m₁ := fun same => fresh₁ (same ▸ inside)
      have n₂ : o ≠ m₂ := fun same => fresh₂ (same ▸ inside)
      rw [comp'Old o inside] at withVars ⊢
      rw [labelOld o n₁ n₂]
      exact represented.own o inside withVars
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁] at withVars; exact absurd groundDotA withVars
      · rw [comp'₂] at withVars; exact absurd groundDotB withVars
  · -- hidden variables
    intro o member y inside
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨oPresent, notFirst, notSecond⟩ := oldOf o old
      rw [comp'Old o oPresent] at inside
      obtain ⟨notKnown, notOther⟩ := represented.hidden o oPresent y inside
      have avoids := mentionedFresh o oPresent y inside
      refine ⟨?_, ?_⟩
      · show y ∉ storePVars ((commAt ρ o₁ o₂ m₁ m₂).information X s)
        rw [commAt_info]
        refine not_mem_storePVars fun e member => ?_
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with (known | rfl | rfl) | rfl
        · exact ⟨fun one => notKnown (mem_storePVars known (.inl one)),
            fun two => notKnown (mem_storePVars known (.inr two))⟩
        · exact ⟨avoids _ (by simp [Rule.terms, commRule]),
            notOther o₁ present₁ (Ne.symm notFirst)⟩
        · exact ⟨avoids _ (by simp [Rule.terms, commRule]),
            notOther o₂ present₂ (Ne.symm notSecond)⟩
        · exact ⟨avoids _ (by simp [Rule.terms, commRule]), avoids _ (by simp [Rule.terms, commRule])⟩
      · intro o' member' different
        rw [resultPresent] at member'
        rcases Finset.mem_union.mp member' with old' | new'
        · obtain ⟨inside', -, -⟩ := oldOf o' old'
          have n₁ : o' ≠ m₁ := fun same => fresh₁ (same ▸ inside')
          have n₂ : o' ≠ m₂ := fun same => fresh₂ (same ▸ inside')
          rw [labelOld o' n₁ n₂]
          exact notOther o' inside' different
        · simp only [Finset.mem_insert, Finset.mem_singleton] at new'
          rcases new' with rfl | rfl
          · rw [label₁]; exact avoids _ (by simp [Rule.terms, commRule])
          · rw [label₂]; exact avoids _ (by simp [Rule.terms, commRule])
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁, groundDotA] at inside; exact absurd inside List.not_mem_nil
      · rw [comp'₂, groundDotB] at inside; exact absurd inside List.not_mem_nil
  · -- the bag after
    rw [resultPresent]
    unfold bagOf
    have apart : Disjoint (s.present \ {o₁, o₂}) ({m₁, m₂} : Finset ℕ) := by
      rw [Finset.disjoint_left]
      intro o inside made
      simp only [Finset.mem_insert, Finset.mem_singleton] at made
      rcases made with rfl | rfl
      · exact fresh₁ (Finset.mem_sdiff.mp inside).1
      · exact fresh₂ (Finset.mem_sdiff.mp inside).1
    rw [Finset.sum_union apart, Finset.sum_pair madeDistinct, comp'₁, comp'₂,
      Finset.sum_congr rfl fun o member => by rw [comp'Old o (Finset.mem_sdiff.mp member).1]]
    abel

/-- **What a heating firing does**: the bag is kept, and the weight decreases. -/
theorem heat_result {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) {ρ : PSubst} {o m₁ m₂ : ℕ}
    (admitted : (heatAt ρ o m₁ m₂).Admits X s) (madeDistinct : m₁ ≠ m₂) (present : o ∈ s.present)
    (fresh₁ : m₁ ∉ s.present) (fresh₂ : m₂ ∉ s.present) :
    ∃ comp' : ℕ → Pattern, RepresentsBy ((heatAt ρ o m₁ m₂).result X s) M comp' ∧
      weightOf ((heatAt ρ o m₁ m₂).result X s).present comp' < weightOf s.present comp := by
  classical
  obtain ⟨⟨fresh, -⟩, -, ⟨_, σ₀, solved₀⟩, -⟩ := admitted
  have solvedInfo : patternAction.Models σ₀ ((heatAt ρ o m₁ m₂).information X s) := solved₀
  rw [heatAt_info] at solvedInfo
  have known₀ : patternAction.Models σ₀ s.knowledge := fun e member => solvedInfo e (by simp [member])
  have take₀ : psubst σ₀ (psubst ρ (par leftPart rightPart)) = psubst σ₀ (s.label o) :=
    solvedInfo (psubst ρ (par leftPart rightPart), s.label o) (by simp)
  rw [represented.reads o present σ₀ known₀] at take₀
  simp only [MeTTaOperationsComm.psubst_par] at take₀
  obtain ⟨shape, -⟩ := (represented.hosted o present).par_of_instance take₀.symm
  have hostedPar := represented.hosted o present
  rw [shape] at hostedPar
  obtain ⟨⟨hostedA, groundA⟩, ⟨hostedB, groundB⟩⟩ := hostedPar.parts_of_par
  set a := psubst σ₀ (psubst ρ leftPart)
  set b := psubst σ₀ (psubst ρ rightPart)
  let comp' : ℕ → Pattern := fun x => if x = m₁ then a else if x = m₂ then b else comp x
  have comp'₁ : comp' m₁ = a := by simp [comp']
  have comp'₂ : comp' m₂ = b := by simp [comp', Ne.symm madeDistinct]
  have comp'Old : ∀ x ∈ s.present, comp' x = comp x := by
    intro x member
    have n₁ : x ≠ m₁ := fun same => fresh₁ (same ▸ member)
    have n₂ : x ≠ m₂ := fun same => fresh₂ (same ▸ member)
    simp [comp', n₁, n₂]
  have resultPresent : ((heatAt ρ o m₁ m₂).result X s).present = (s.present \ {o}) ∪ {m₁, m₂} := by
    show fire s.present (Selection.commit (T := Unit) ⟨[o], [], [m₁, m₂]⟩) = _
    simp [fire, Selection.commit]
  have labelOld : ∀ x, x ≠ m₁ → x ≠ m₂ → ((heatAt ρ o m₁ m₂).result X s).label x = s.label x := by
    intro x n₁ n₂
    exact result_label_kept s (by simp [heatAt, n₁, n₂])
  have mentionedFresh : ∀ x ∈ s.present, ∀ y ∈ pvars (comp x), ∀ r ∈ heatRule.terms,
      y ∉ pvars (psubst ρ r) := fun x member y inside r term =>
    fresh_avoids s (heatAt ρ o m₁ m₂) fresh (Or.inr (Or.inr ⟨x, member, rfl⟩)) term
      (represented.mentioned member inside)
  have readsMade : ∀ σ : PSubst, patternAction.Models σ ((heatAt ρ o m₁ m₂).result X s).knowledge →
      patternAction.Models σ s.knowledge ∧ psubst σ (psubst ρ leftPart) = a ∧
        psubst σ (psubst ρ rightPart) = b := by
    intro σ solved
    have solvedσ : patternAction.Models σ ((heatAt ρ o m₁ m₂).information X s) := solved
    rw [heatAt_info] at solvedσ
    have knownσ : patternAction.Models σ s.knowledge := fun e member => solvedσ e (by simp [member])
    have takeσ : psubst σ (psubst ρ (par leftPart rightPart)) = psubst σ (s.label o) :=
      solvedσ (psubst ρ (par leftPart rightPart), s.label o) (by simp)
    rw [represented.reads o present σ knownσ, shape, predot_par] at takeσ
    simp only [MeTTaOperationsComm.psubst_par] at takeσ
    have partsSame : psubst σ (psubst ρ leftPart) = psubst σ (predot a) ∧
        psubst σ (psubst ρ rightPart) = psubst σ (predot b) := by
      simpa [par, MeTTaCalculus.pPar] using takeσ
    rw [predot_ground a groundA, psubst_of_pvars_nil σ a groundA, predot_ground b groundB,
      psubst_of_pvars_nil σ b groundB] at partsSame
    exact ⟨knownσ, partsSame.1, partsSame.2⟩
  have apart : Disjoint (s.present \ {o}) ({m₁, m₂} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro x inside made
    simp only [Finset.mem_insert, Finset.mem_singleton] at made
    rcases made with rfl | rfl
    · exact fresh₁ (Finset.mem_sdiff.mp inside).1
    · exact fresh₂ (Finset.mem_sdiff.mp inside).1
  refine ⟨comp', ⟨⟨σ₀, solved₀⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x member σ solved
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · have inside := (Finset.mem_sdiff.mp old).1
      have n₁ : x ≠ m₁ := fun same => fresh₁ (same ▸ inside)
      have n₂ : x ≠ m₂ := fun same => fresh₂ (same ▸ inside)
      rw [labelOld x n₁ n₂, comp'Old x inside]
      exact represented.reads x inside σ (readsMade σ solved).1
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁, heatAt_label₁, (readsMade σ solved).2.1, predot_ground a groundA,
          psubst_of_pvars_nil σ a groundA]
      · rw [comp'₂, heatAt_label₂ s ρ o madeDistinct, (readsMade σ solved).2.2, predot_ground b groundB,
          psubst_of_pvars_nil σ b groundB]
  · intro x member
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · have inside := (Finset.mem_sdiff.mp old).1
      rw [comp'Old x inside]
      exact represented.hosted x inside
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁]; exact hostedA
      · rw [comp'₂]; exact hostedB
  · intro x member withVars
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · have inside := (Finset.mem_sdiff.mp old).1
      have n₁ : x ≠ m₁ := fun same => fresh₁ (same ▸ inside)
      have n₂ : x ≠ m₂ := fun same => fresh₂ (same ▸ inside)
      rw [comp'Old x inside] at withVars ⊢
      rw [labelOld x n₁ n₂]
      exact represented.own x inside withVars
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁] at withVars; exact absurd groundA withVars
      · rw [comp'₂] at withVars; exact absurd groundB withVars
  · intro x member y inside
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨xPresent, notTaken⟩ := Finset.mem_sdiff.mp old
      have notO : x ≠ o := fun same => notTaken (by simp [same])
      rw [comp'Old x xPresent] at inside
      obtain ⟨notKnown, notOther⟩ := represented.hidden x xPresent y inside
      have avoids := mentionedFresh x xPresent y inside
      refine ⟨?_, ?_⟩
      · show y ∉ storePVars ((heatAt ρ o m₁ m₂).information X s)
        rw [heatAt_info]
        refine not_mem_storePVars fun e member => ?_
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with known | rfl
        · exact ⟨fun one => notKnown (mem_storePVars known (.inl one)),
            fun two => notKnown (mem_storePVars known (.inr two))⟩
        · exact ⟨avoids _ (by simp [Rule.terms, heatRule]), notOther o present (Ne.symm notO)⟩
      · intro x' member' different
        rw [resultPresent] at member'
        rcases Finset.mem_union.mp member' with old' | new'
        · have inside' := (Finset.mem_sdiff.mp old').1
          have n₁ : x' ≠ m₁ := fun same => fresh₁ (same ▸ inside')
          have n₂ : x' ≠ m₂ := fun same => fresh₂ (same ▸ inside')
          rw [labelOld x' n₁ n₂]
          exact notOther x' inside' different
        · simp only [Finset.mem_insert, Finset.mem_singleton] at new'
          rcases new' with rfl | rfl
          · rw [heatAt_label₁]; exact avoids _ (by simp [Rule.terms, heatRule])
          · rw [heatAt_label₂ s ρ o madeDistinct]; exact avoids _ (by simp [Rule.terms, heatRule])
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁, groundA] at inside; exact absurd inside List.not_mem_nil
      · rw [comp'₂, groundB] at inside; exact absurd inside List.not_mem_nil
  · rw [← represented.bag, resultPresent]
    unfold bagOf
    rw [Finset.sum_union apart, Finset.sum_pair madeDistinct, comp'₁, comp'₂,
      Finset.sum_congr rfl fun x member => by rw [comp'Old x (Finset.mem_sdiff.mp member).1],
      ← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present) (s₂ := s.present), Finset.sum_singleton,
      shape, parts_par, ← Multiset.coe_add]
  · rw [resultPresent]
    unfold weightOf
    rw [Finset.sum_union apart, Finset.sum_pair madeDistinct, comp'₁, comp'₂,
      Finset.sum_congr rfl fun x member => by rw [comp'Old x (Finset.mem_sdiff.mp member).1],
      ← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present) (s₂ := s.present)
        (f := fun x => weight (comp x)), Finset.sum_singleton, shape, weight_par]
    omega

/-- **What a clearing firing does**: the bag is kept, and the weight decreases. -/
theorem clear_result {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) {ρ : PSubst} {o : ℕ}
    (admitted : (clearAt ρ o).Admits X s) (present : o ∈ s.present) :
    RepresentsBy ((clearAt ρ o).result X s) M comp ∧
      weightOf ((clearAt ρ o).result X s).present comp < weightOf s.present comp := by
  classical
  obtain ⟨⟨fresh, -⟩, -, ⟨_, σ₀, solved₀⟩, -⟩ := admitted
  have solvedInfo : patternAction.Models σ₀ ((clearAt ρ o).information X s) := solved₀
  rw [clearAt_info] at solvedInfo
  have known₀ : patternAction.Models σ₀ s.knowledge := fun e member => solvedInfo e (by simp [member])
  have take₀ : psubst σ₀ (psubst ρ pZero) = psubst σ₀ (s.label o) :=
    solvedInfo (psubst ρ pZero, s.label o) (by simp)
  rw [represented.reads o present σ₀ known₀, MeTTaOperationsComm.psubst_pZero,
    MeTTaOperationsComm.psubst_pZero] at take₀
  have shape := (represented.hosted o present).zero_of_instance take₀.symm
  have resultPresent : ((clearAt ρ o).result X s).present = s.present \ {o} := by
    show fire s.present (Selection.commit (T := Unit) ⟨[o], [], []⟩) = _
    simp [fire, Selection.commit]
  have labelOld : ∀ x, ((clearAt ρ o).result X s).label x = s.label x := fun x =>
    result_label_kept s (by simp [clearAt])
  have mentionedFresh : ∀ x ∈ s.present, ∀ y ∈ pvars (comp x), ∀ r ∈ clearRule.terms,
      y ∉ pvars (psubst ρ r) := fun x member y inside r term =>
    fresh_avoids s (clearAt ρ o) fresh (Or.inr (Or.inr ⟨x, member, rfl⟩)) term
      (represented.mentioned member inside)
  have knownOf : ∀ σ : PSubst, patternAction.Models σ ((clearAt ρ o).result X s).knowledge →
      patternAction.Models σ s.knowledge := by
    intro σ solved
    have solvedσ : patternAction.Models σ ((clearAt ρ o).information X s) := solved
    rw [clearAt_info] at solvedσ
    exact fun e member => solvedσ e (by simp [member])
  refine ⟨⟨⟨σ₀, solved₀⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x member σ solved
    rw [resultPresent] at member
    rw [labelOld x]
    exact represented.reads x (Finset.mem_sdiff.mp member).1 σ (knownOf σ solved)
  · intro x member
    rw [resultPresent] at member
    exact represented.hosted x (Finset.mem_sdiff.mp member).1
  · intro x member withVars
    rw [resultPresent] at member
    rw [labelOld x]
    exact represented.own x (Finset.mem_sdiff.mp member).1 withVars
  · intro x member y inside
    rw [resultPresent] at member
    obtain ⟨xPresent, notTaken⟩ := Finset.mem_sdiff.mp member
    have notO : x ≠ o := fun same => notTaken (by simp [same])
    obtain ⟨notKnown, notOther⟩ := represented.hidden x xPresent y inside
    have avoids := mentionedFresh x xPresent y inside
    refine ⟨?_, fun x' member' different => ?_⟩
    · show y ∉ storePVars ((clearAt ρ o).information X s)
      rw [clearAt_info]
      refine not_mem_storePVars fun e member => ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with known | rfl
      · exact ⟨fun one => notKnown (mem_storePVars known (.inl one)),
          fun two => notKnown (mem_storePVars known (.inr two))⟩
      · exact ⟨avoids _ (by simp [Rule.terms, clearRule]), notOther o present (Ne.symm notO)⟩
    · rw [resultPresent] at member'
      rw [labelOld x']
      exact notOther x' (Finset.mem_sdiff.mp member').1 different
  · rw [← represented.bag, resultPresent]
    unfold bagOf
    rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present) (s₂ := s.present),
      Finset.sum_singleton, shape, parts_pZero]
    simp
  · rw [resultPresent]
    unfold weightOf
    rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present) (s₂ := s.present)
      (f := fun x => weight (comp x)), Finset.sum_singleton, shape, weight_pZero]
    omega

/-! ## Existence of firings -/

/-- Two identities not in a set, and different. -/
theorem two_fresh (present : Finset ℕ) : ∃ m₁ m₂ : ℕ, m₁ ∉ present ∧ m₂ ∉ present ∧ m₁ ≠ m₂ := by
  classical
  obtain ⟨m₁, fresh₁⟩ := Infinite.exists_notMem_finset present
  obtain ⟨m₂, fresh₂⟩ := Infinite.exists_notMem_finset (insert m₁ present)
  exact ⟨m₁, m₂, fresh₁, fun inside => fresh₂ (Finset.mem_insert_of_mem inside),
    fun same => fresh₂ (same ▸ Finset.mem_insert_self m₁ present)⟩

/-- **Heating fires at every row whose part is a binary parallel composition.** -/
theorem heat_exists {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) {o : ℕ} (present : o ∈ s.present) {a b : Pattern}
    (shape : comp o = par a b) :
    ∃ ρ m₁ m₂, (heatAt ρ o m₁ m₂).Admits X s ∧ m₁ ≠ m₂ ∧ m₁ ∉ s.present ∧ m₂ ∉ s.present := by
  classical
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming s (ruleVars heatRule)
  obtain ⟨m₁, m₂, fresh₁, fresh₂, madeDistinct⟩ := two_fresh s.present
  have freshAt : (heatAt (renameBy g) o m₁ m₂).Fresh X s :=
    Comm.fresh_of_renaming s (heatAt (renameBy g) o m₁ m₂) g rfl injective avoids
  obtain ⟨σ₀, known⟩ := represented.consistent
  have hostedPar := represented.hosted o present
  rw [shape] at hostedPar
  obtain ⟨⟨-, groundA⟩, ⟨-, groundB⟩⟩ := hostedPar.parts_of_par
  have groundPar : pvars (par a b) = [] := by
    rw [MeTTaCalculus.Corrected.pvars_par, groundA, groundB]
    rfl
  let h : PSubst := fun v => if v = "A" then some a else if v = "B" then some b else none
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := X) (s := s)
    (heatAt (renameBy g) o m₁ m₂) freshAt (b := PUnit.unit) σ₀ h known
    (fun _ member => (List.not_mem_nil member).elim)
    (fun x member => by
      obtain rfl := List.mem_singleton.mp member
      exact present)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      obtain rfl := List.mem_singleton.mp member
      show psubst h (par leftPart rightPart) = psubst σ₀ (s.label o)
      rw [represented.reads o present σ₀ known, shape, predot_ground (par a b) groundPar,
        psubst_of_pvars_nil σ₀ (par a b) groundPar]
      simp [h, leftPart, rightPart, par, MeTTaCalculus.pPar, psubst, MeTTaOperationsComm.psubst.psubstList])
    (fun _ member => (List.not_mem_nil member).elim)
  refine ⟨renameBy g, m₁, m₂, (RuleSyntax.admits_iff _).mpr ⟨freshAt,
    ⟨by simp [heatAt], by simp [heatAt, madeDistinct], rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩, madeDistinct, fresh₁, fresh₂⟩
  · intro x member
    simp only [heatAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    exact present
  · intro x member
    simp [heatAt, Selection.commit] at member
  · simp [heatAt, Selection.commit]
  · rw [Finset.disjoint_left]
    intro x member
    simp only [heatAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact fresh₁
    · exact fresh₂

/-- **Clearing fires at every row whose part is `0`.** -/
theorem clear_exists {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) {o : ℕ} (present : o ∈ s.present) (shape : comp o = pZero) :
    ∃ ρ, (clearAt ρ o).Admits X s := by
  classical
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming s (ruleVars clearRule)
  have freshAt : (clearAt (renameBy g) o).Fresh X s :=
    Comm.fresh_of_renaming s (clearAt (renameBy g) o) g rfl injective avoids
  obtain ⟨σ₀, known⟩ := represented.consistent
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := X) (s := s)
    (clearAt (renameBy g) o) freshAt (b := PUnit.unit) σ₀ (fun _ => none) known
    (fun _ member => (List.not_mem_nil member).elim)
    (fun x member => by
      obtain rfl := List.mem_singleton.mp member
      exact present)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      obtain rfl := List.mem_singleton.mp member
      show psubst (fun _ => none) pZero = psubst σ₀ (s.label o)
      rw [represented.reads o present σ₀ known, shape, predot_pZero]
      rfl)
    (fun _ member => (List.not_mem_nil member).elim)
  refine ⟨renameBy g, (RuleSyntax.admits_iff _).mpr ⟨freshAt,
    ⟨by simp [clearAt], by simp [clearAt], rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩⟩
  · intro x member
    simp only [clearAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    exact present
  · intro x member
    simp [clearAt, Selection.commit] at member
  · simp [clearAt, Selection.commit]
  · simp [clearAt, Selection.commit]

/-- **Communication fires between two rows holding inputs on one channel whose patterns have a ground
principal unifier.** -/
theorem comm_exists {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) {o₁ o₂ : ℕ} (present₁ : o₁ ∈ s.present)
    (present₂ : o₂ ∈ s.present) (distinct : o₁ ≠ o₂) {t x A u B : Pattern} {bs : Bindings}
    (first : comp o₁ = pFor t x A) (second : comp o₂ = pFor u x B) (gp : GroundPrincipal t u bs) :
    ∃ ρ m₁ m₂, (commAt ρ o₁ o₂ m₁ m₂).Admits X s ∧ m₁ ≠ m₂ ∧ m₁ ∉ s.present ∧ m₂ ∉ s.present := by
  obtain ⟨m₁, m₂, fresh₁, fresh₂, madeDistinct⟩ := two_fresh s.present
  obtain ⟨ρ, opensFreshly⟩ := exists_fresh_opening s.label ⟨s.knowledge, s.present⟩ o₁ o₂ m₁ m₂
  have apart : ∀ y ∈ pvars t ++ pvars u, y ∉ storePVars s.knowledge := by
    intro y inside
    rcases List.mem_append.mp inside with inT | inU
    · exact (represented.hidden o₁ present₁ y (by
        rw [first, pvars_pFor]; exact List.mem_append_left _ (List.mem_append_left _ inT))).1
    · exact (represented.hidden o₂ present₂ y (by
        rw [second, pvars_pFor]; exact List.mem_append_left _ (List.mem_append_left _ inU))).1
  obtain ⟨σ₀, known, unifies⟩ := Comm.glued_solution gp.solves apart represented.consistent
  exact ⟨ρ, m₁, m₂, comm_admits s.label t u x A B ⟨s.knowledge, s.present⟩ o₁ o₂ m₁ m₂
    (fun σ known => (represented.reads o₁ present₁ σ known).trans (by rw [first]))
    (fun σ known => (represented.reads o₂ present₂ σ known).trans (by rw [second]))
    distinct madeDistinct present₁ present₂ fresh₁ fresh₂ known unifies opensFreshly,
    madeDistinct, fresh₁, fresh₂⟩

/-! ## Housekeeping -/

/-- **Housekeeping keeps the represented bag and decreases the weight.** -/
theorem administration_decreases {s s' : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) (fires : Administers s s') :
    ∃ comp' : ℕ → Pattern, RepresentsBy s' M comp' ∧ weightOf s'.present comp' < weightOf s.present comp := by
  obtain ⟨f, kind, admitted, rfl⟩ := fires
  rcases kind with isHeat | isClear
  · obtain ⟨o, m₁, m₂, same, madeDistinct, present, fresh₁, fresh₂⟩ := heat_normal f isHeat admitted
    rw [same] at admitted ⊢
    exact heat_result represented admitted madeDistinct present fresh₁ fresh₂
  · obtain ⟨o, same, present⟩ := clear_normal f isClear admitted
    rw [same] at admitted ⊢
    exact ⟨comp, clear_result represented admitted present⟩

/-- Runs of exactly `k` housekeeping firings. -/
inductive AdministrativeRun : ℕ → State Tm ℕ → State Tm ℕ → Prop
  | refl (s : State Tm ℕ) : AdministrativeRun 0 s s
  | head {k : ℕ} {s t u : State Tm ℕ} : Administers s t → AdministrativeRun k t u →
      AdministrativeRun (k + 1) s u

/-- **Housekeeping is bounded** by the spine weight. -/
theorem administration_bounded {s e : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern} {k : ℕ}
    (represented : RepresentsBy s M comp) (run : AdministrativeRun k s e) : k ≤ weightOf s.present comp := by
  induction run generalizing comp with
  | refl => exact Nat.zero_le _
  | head fires _ earlier =>
      obtain ⟨comp', represented', lighter⟩ := administration_decreases represented fires
      have bound := earlier represented'
      omega

/-- **Heating reaches parts**: housekeeping firings reach a state representing the same bag whose rows
all have weight zero. -/
theorem heats_to_parts {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) :
    ∃ (s₁ : State Tm ℕ) (comp₁ : ℕ → Pattern), Relation.ReflTransGen Administers s s₁ ∧
      RepresentsBy s₁ M comp₁ ∧ ∀ o ∈ s₁.present, weight (comp₁ o) = 0 := by
  classical
  induction hw : weightOf s.present comp using Nat.strong_induction_on generalizing s comp with
  | _ w earlier =>
    by_cases light : ∀ o ∈ s.present, weight (comp o) = 0
    · exact ⟨s, comp, .refl, represented, light⟩
    · simp only [not_forall] at light
      obtain ⟨o, present, heavy⟩ := light
      obtain ⟨s₁, fires⟩ : ∃ s₁, Administers s s₁ := by
        rcases heavy_shape heavy with zero | ⟨a, b, shape⟩
        · obtain ⟨ρ, admitted⟩ := clear_exists represented present zero
          exact ⟨_, clearAt ρ o, .inr rfl, admitted, rfl⟩
        · obtain ⟨ρ, m₁, m₂, admitted, -⟩ := heat_exists represented present shape
          exact ⟨_, heatAt ρ o m₁ m₂, .inl rfl, admitted, rfl⟩
      obtain ⟨comp', represented', lighter⟩ := administration_decreases represented fires
      obtain ⟨s', comp'', run, represented'', light'⟩ := earlier _ (hw ▸ lighter) represented' rfl
      exact ⟨s', comp'', .head fires run, represented'', light'⟩

/-! ## Communication -/

/-- **A communication is a source step**, at a bag whose unifiable pairs of inputs have ground principal
unifiers with first-order values. -/
theorem communication_sound {s s' : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) (grounded : GroundUnifiable M) (fires : Communicates s s') :
    ∃ M', BagComm M M' ∧ Represents s' M' := by
  obtain ⟨f, isComm, admitted, rfl⟩ := fires
  obtain ⟨o₁, o₂, m₁, m₂, same, distinct, madeDistinct, present₁, present₂, fresh₁, fresh₂⟩ :=
    comm_normal f isComm admitted
  rw [same] at admitted ⊢
  obtain ⟨t, x, A, u, B, first, second, unifiable⟩ :=
    comm_shape represented admitted madeDistinct present₁ present₂
  have split := represented.bag_split distinct present₁ present₂ first second
  have inM₁ : pFor t x A ∈ M := by
    rw [split]
    exact Multiset.mem_cons_self _ _
  have inM₂ : pFor u x B ∈ M.erase (pFor t x A) := by
    rw [split, Multiset.erase_cons_head]
    exact Multiset.mem_cons_self _ _
  obtain ⟨bs, gp, values⟩ := grounded t x A u B inM₁ inM₂ unifiable
  refine ⟨_, ?_, _, comm_result represented admitted distinct madeDistinct present₁ present₂ fresh₁ fresh₂
    first second gp values⟩
  rw [split]
  exact BagComm.comm t u x A B bs _ gp (represented.convention present₁ present₂ distinct first second) values

/-- **Every source step is matched**: housekeeping firings, then one communication. -/
theorem communication_complete {s : State Tm ℕ} {M M' : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) (step : BagComm M M') :
    ∃ s₁ s₂ : State Tm ℕ, Relation.ReflTransGen Administers s s₁ ∧ Communicates s₁ s₂ ∧ Represents s₂ M' := by
  classical
  obtain ⟨s₁, comp₁, run, represented₁, light⟩ := heats_to_parts represented
  obtain ⟨t, u, x, A, B, bs, rest, gp, convention, values⟩ := step
  have heated : bagOf s₁.present comp₁ = s₁.present.val.map comp₁ := by
    unfold bagOf
    rw [Finset.sum_congr rfl fun o member => parts_coe_of_light (light o member),
      Finset.sum_eq_multiset_sum,
      show (fun o => ({comp₁ o} : Multiset Pattern)) = (fun p : Pattern => ({p} : Multiset Pattern)) ∘ comp₁
        from rfl, ← Multiset.map_map, Multiset.sum_map_singleton]
  have rows : s₁.present.val.map comp₁ = pFor t x A ::ₘ pFor u x B ::ₘ rest := by
    rw [← heated, represented₁.bag]
  obtain ⟨o₁, member₁, at₁⟩ : ∃ o₁ ∈ s₁.present, comp₁ o₁ = pFor t x A := by
    have found : pFor t x A ∈ s₁.present.val.map comp₁ := by
      rw [rows]
      exact Multiset.mem_cons_self _ _
    obtain ⟨o₁, member, same⟩ := Multiset.mem_map.mp found
    exact ⟨o₁, member, same⟩
  obtain ⟨o₂, member₂, distinct, at₂⟩ : ∃ o₂ ∈ s₁.present, o₂ ≠ o₁ ∧ comp₁ o₂ = pFor u x B := by
    have split : s₁.present.val.map comp₁ = comp₁ o₁ ::ₘ (s₁.present.erase o₁).val.map comp₁ := by
      rw [← Multiset.map_cons comp₁ o₁,
        ← Finset.insert_val_of_notMem (Finset.notMem_erase o₁ s₁.present),
        Finset.insert_erase member₁]
    rw [split, at₁] at rows
    have others := Multiset.cons_inj_right _ |>.mp rows
    have found : pFor u x B ∈ (s₁.present.erase o₁).val.map comp₁ := by
      rw [others]
      exact Multiset.mem_cons_self _ _
    obtain ⟨o₂, member, same⟩ := Multiset.mem_map.mp found
    have inErase := Finset.mem_erase.mp member
    exact ⟨o₂, inErase.2, inErase.1, same⟩
  obtain ⟨ρ, m₁, m₂, admitted, madeDistinct, fresh₁, fresh₂⟩ :=
    comm_exists represented₁ member₁ member₂ (Ne.symm distinct) at₁ at₂ gp
  have represented₂ := comm_result represented₁ admitted (Ne.symm distinct) madeDistinct member₁ member₂
    fresh₁ fresh₂ at₁ at₂ gp values
  have restSame : bagOf (s₁.present \ {o₁, o₂}) comp₁ = rest := by
    have both := (represented₁.bag_split (Ne.symm distinct) member₁ member₂ at₁ at₂).symm
    exact (Multiset.cons_inj_right _).mp ((Multiset.cons_inj_right _).mp both)
  rw [restSame] at represented₂
  exact ⟨s₁, _, run, ⟨commAt ρ o₁ o₂ m₁ m₂, rfl, admitted, rfl⟩, _, represented₂⟩

/-! ## Every hosted process is represented -/

/-- The state of a list of parts: one row per part, labelled by its representation, no knowledge. -/
def initial (L : List Pattern) : State Tm ℕ :=
  ⟨PUnit.unit, [], Finset.range L.length, fun n => predot (L.getD n pZero)⟩

theorem getD_mem {L : List Pattern} {n : ℕ} (small : n < L.length) : L.getD n pZero ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem small, Option.getD_some]
  exact List.getElem_mem small

theorem getD_eq {L : List Pattern} {n : ℕ} (small : n < L.length) : L.getD n pZero = L[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem small, Option.getD_some]

/-- **The initial state's rows carry the process's parts.** -/
theorem initial_bag (P : Pattern) :
    bagOf (Finset.range (parts P).length) (fun n => (parts P).getD n pZero) = (parts P : Multiset Pattern) := by
  set L := parts P with LDef
  have selfParts : ∀ n ∈ Finset.range L.length,
      (parts (L.getD n pZero) : Multiset Pattern) = {L.getD n pZero} := by
    intro n member
    rw [parts_of_mem_parts P _ (getD_mem (Finset.mem_range.mp member))]
    rfl
  have listSame : (List.range L.length).map (fun n => L.getD n pZero) = L := by
    apply List.ext_getElem (by simp)
    intro i small₁ small₂
    simp only [List.getElem_map, List.getElem_range]
    exact getD_eq small₂
  unfold bagOf
  rw [Finset.sum_congr rfl selfParts, Finset.sum_eq_multiset_sum,
    show (fun n => ({L.getD n pZero} : Multiset Pattern)) =
      (fun p : Pattern => ({p} : Multiset Pattern)) ∘ (fun n => L.getD n pZero) from rfl,
    ← Multiset.map_map, Multiset.sum_map_singleton, Finset.range_val, Multiset.range, Multiset.map_coe,
    listSame]

/-- **The initial state of a hosted process represents its parts.** -/
theorem initial_represents (P : Pattern) (hostedP : HostedProcess P) :
    RepresentsBy (initial (parts P)) (parts P) (fun n => (parts P).getD n pZero) := by
  classical
  set L := parts P with LDef
  have hostedL : ∀ n ∈ Finset.range L.length, Hosted (L.getD n pZero) := fun n member =>
    hostedP.hosted _ (getD_mem (Finset.mem_range.mp member))
  refine ⟨⟨fun _ => none, fun _ member => absurd member List.not_mem_nil⟩, fun _ _ _ _ => rfl, hostedL,
    fun _ _ _ => rfl, ?_, ?_⟩
  · intro i member y inside
    refine ⟨by simp [initial, storePVars], ?_⟩
    intro j member' different inLabel
    have small₁ := Finset.mem_range.mp member
    have small₂ := Finset.mem_range.mp member'
    have inJ : y ∈ pvars (L.getD j pZero) := mem_pvars_predot inLabel
    rw [getD_eq small₁] at inside
    rw [getD_eq small₂] at inJ
    have pairwise := List.pairwise_iff_getElem.mp hostedP.disjoint
    rcases Nat.lt_or_gt_of_ne different with before | after
    · exact pairwise j i small₂ small₁ before y inJ inside
    · exact pairwise i j small₁ small₂ after y inside inJ
  · exact initial_bag P

/-- **Every hosted process is represented.** -/
theorem every_hosted_process_represented (P : Pattern) (hostedP : HostedProcess P) :
    ∃ s, Represents s (parts P) :=
  ⟨initial (parts P), _, initial_represents P hostedP⟩

/-! ## The theorem -/

/-- **The F1R3FLY manuscript's calculus on the one-match step, by a finite program.**

The step is `RuleSyntax.step` of the fixed three-rule `program` at the one frame of structural
substitution on patterns. Through `Represents`, with the bag of parallel parts as the source and
`BagComm` as its COMM:

1. every hosted process is represented;
2. every transition of the step is a communication or housekeeping;
3. housekeeping keeps the represented bag;
4. at a bag whose unifiable pairs of inputs have ground principal unifiers with first-order values, a
   communication is a source step;
5. every source step is matched by housekeeping firings and one communication;
6. a run of `k` housekeeping firings from a state represented through `comp` has `k` at most the spine
   weight of its parts. -/
theorem manuscript_calculus_by_a_finite_program :
    program.Finite ∧
    (∀ P : Pattern, HostedProcess P → ∃ s, Represents s (parts P)) ∧
    (∀ s s' : State Tm ℕ,
      Succ (RuleSyntax.step X ℕ E program).toStep s s' ↔ Communicates s s' ∨ Administers s s') ∧
    (∀ {s s' : State Tm ℕ} {M : Multiset Pattern}, Represents s M → Administers s s' → Represents s' M) ∧
    (∀ {s s' : State Tm ℕ} {M : Multiset Pattern}, Represents s M → GroundUnifiable M →
      Communicates s s' → ∃ M', BagComm M M' ∧ Represents s' M') ∧
    (∀ {s : State Tm ℕ} {M M' : Multiset Pattern}, Represents s M → BagComm M M' →
      ∃ s₁ s₂ : State Tm ℕ, Relation.ReflTransGen Administers s s₁ ∧ Communicates s₁ s₂ ∧
        Represents s₂ M') ∧
    (∀ {s e : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern} {k : ℕ},
      RepresentsBy s M comp → AdministrativeRun k s e → k ≤ weightOf s.present comp) := by
  refine ⟨program_finite, every_hosted_process_represented, succ_iff, ?_, ?_, ?_,
    fun represented run => administration_bounded represented run⟩
  · intro s s' M represented fires
    obtain ⟨comp, represented⟩ := represented
    obtain ⟨comp', represented', -⟩ := administration_decreases represented fires
    exact ⟨comp', represented'⟩
  · intro s s' M represented grounded fires
    obtain ⟨comp, represented⟩ := represented
    exact communication_sound represented grounded fires
  · intro s M M' represented step
    obtain ⟨comp, represented⟩ := represented
    exact communication_complete represented step

#print axioms parts_of_mem_parts
#print axioms predot_of_binders_nil
#print axioms firstOrder_psubst
#print axioms hosted_applyDot
#print axioms fresh_avoids
#print axioms succ_iff
#print axioms comm_shape
#print axioms comm_result
#print axioms heat_result
#print axioms clear_result
#print axioms heat_exists
#print axioms clear_exists
#print axioms comm_exists
#print axioms administration_bounded
#print axioms heats_to_parts
#print axioms communication_sound
#print axioms communication_complete
#print axioms initial_represents
#print axioms manuscript_calculus_by_a_finite_program

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteProgram
