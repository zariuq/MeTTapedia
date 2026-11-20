import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotientFrame

/-!
# One representation of names: pre-dotting inside patterns

The finite hosting represents an input `for(t <- x)k` by `predot`: the continuation with its own pattern's
variables in quoted position, the pattern kept as written. A REFL listener `for((R) <- x)0` quotes a
reduct `R` in its pattern. The reflected process is represented pre-dotted (`predot` recurses into `x?(P)`),
so a hosting that steps it in place and packs its rows makes the quote `(predot R)`. When `R` has an input
whose continuation reads its pattern's variables, the two differ: `(R)` as written against `(predot R)`.

`predotU` pre-dots processes quoted inside patterns too: `for(t <- x)k` is represented by
`for(predotU t <- predotU x)k'`, `k'` the continuation pre-dotted and dotted by `t`'s variables.

## What is shown

* `predotU_injective`: the representation is injective, on every pattern (so in particular on closed
  processes); `dotted_injective`: so is each dotting.
* `pvars_predotU`: it keeps the variables, in order.
* `components_predotU`: it commutes with taking parallel components, so it preserves and reflects the bag
  laws at the top level (`perm_components_predotU_iff`).
* `bagLaws_predotU`: it preserves equality modulo the bag laws at every depth, the equality of the quotient
  frame; `bagLaws_pack`: a bag of the represented components of a process, packed in any order, is the
  represented process modulo the bag laws.
* `predotU_eq_predot_of_tame`: on tame processes (every pattern guard-free) it is `predot`. It differs from
  `predot` only on patterns that quote a guard.
* `predotU_psubst`: it commutes with every ground substitution of variables that no inner pattern binds,
  the hypothesis of `predot_psubst`.
* `comm_one_firing_uniform`: COMM is one firing of the finite program on rows represented uniformly, with
  the named hypothesis that the represented patterns have the same ground principal unifier as the written
  ones (`comm_one_firing_uniform_of_guardFree`: on guard-free patterns this is the original hypothesis). The
  manuscript's example meets every hypothesis (`Controls.example_uniform`).

## Controls

* **(e)** A reduct with a binder, `R = for(y <- @0)y`, quoted by a listener carrying the pre-dotted quote
  `(predotU R)` that packing the child's rows gives, and a partner quoting the alpha-variant `for(w <- @0)w`:
  the COMM firing is refused at
  every opening when the partner is represented as written, and admitted when it is represented uniformly
  (`as_written_partner_refused`, `uniform_partner_admitted`); the literal source and the corrected
  relational semantics meet (`source_partner_meets`).
* What does **not** hold:
  * the corrected executable refuses every COMM whose pattern quotes a guard
    (`corrected_refuses_guard_quotes`), so (e) is outside the corrected semantics' exact fragment;
  * a partner that instantiates the quoted guard's binder, `for(0 <- @0)0`, meets in the source and is
    missed by the hosting in both representations (`instantiated_partner_meets_in_source`,
    `instantiated_partner_refused`);
  * neither `predot` nor `predotU` preserves `BagEq` when a binder is shadowed
    (`shadowing_breaks_bagEq`): `BagEq` compares closed forms, and dotting a shadowed name reaches the
    inner pattern;
  * the corrected semantics' REFL quotes the closed form (`canonicalBag`), which the representation fixes
    (`predotU_closeIn`, `predotU_canonicalBag`), and which is not the made quote modulo the bag laws for any
    closed reduct with a variable (`canonicalBag_not_made_quote`; instance `closed_quote_not_made_quote`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflUniform

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot SC tProc demoChan pPar)
open MeTTaOperationsComm (psubst pcomp psubst_comp psubst_none psubst_congr psubst_of_pvars_nil pvars
  patternAction PSubst quoteOn dotted GroundPrincipal applyDot_eq psubst_nQuote psubst_pFor psubst_tProc firstOrder
  lookup_eq_none_of_keys)
open MeTTaCalculus.Corrected (psubst_getD_congr psubst_getD_congr_on binders bindersFor Apart psubstList_eq_map
  binders_apply bindersFor_cons3 bindersFor_short pvars_apply pvarsList_eq_flatMap tame tameFor_iff tameList_iff
  guardFree guardFreeList_iff components components_pZero BagEq canonicalBag)
open FiniteProgram (predot predotFor predotList predotList_eq_map predot_apply predotFor_cons3 predotFor_short
  GroundValued dotted_psubst_comm_of_images mem_keys_of_lookup commAt keys_of_apart comm_admits_inputs comm_reads_inputs
  pFor_inj program)
open FiniteProgram.Controls (fresh_at rename)
open Comm (X E renameBy)
open Comm.Controls (start)
open OneFrame (embed)
open ReflQuotient (BagLaws components_apply_of_ne components_collection_of_ne)

/-! ## The representation -/

mutual
/-- **Uniform pre-dotting**: every input's continuation with its own pattern's variables in quoted
position, at every depth, and the input's pattern represented the same way. -/
def predotU : Pattern → Pattern
  | .bvar n => .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply c (if c = "MFor" then predotUFor args else predotUList args)
  | .lambda nm body => .lambda nm (predotU body)
  | .multiLambda n nms body => .multiLambda n nms (predotU body)
  | .subst body repl => .subst (predotU body) (predotU repl)
  | .collection ct elems rest => .collection ct (predotUList elems) rest
/-- Uniform pre-dotting of a list. -/
def predotUList : List Pattern → List Pattern
  | [] => []
  | p :: ps => predotU p :: predotUList ps
/-- The arguments of an input: the pattern represented, the channel, the continuation dotted. -/
def predotUFor : List Pattern → List Pattern
  | [] => []
  | [p] => [predotU p]
  | [p, q] => [predotU p, predotU q]
  | t :: x :: k :: rest => predotU t :: predotU x :: dotted (pvars t) (predotU k) :: predotUList rest
end

theorem predotUList_eq_map (ps : List Pattern) : predotUList ps = ps.map predotU := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [predotUList, ih]

theorem predotU_apply (c : String) (args : List Pattern) :
    predotU (.apply c args) = .apply c (if c = "MFor" then predotUFor args else args.map predotU) := by
  simp [predotU, predotUList_eq_map]

theorem predotUFor_cons3 (t x k : Pattern) (rest : List Pattern) :
    predotUFor (t :: x :: k :: rest) =
      predotU t :: predotU x :: dotted (pvars t) (predotU k) :: rest.map predotU := by
  simp [predotUFor, predotUList_eq_map]

theorem predotUFor_short (ps : List Pattern) (short : ps.length < 3) : predotUFor ps = ps.map predotU := by
  match ps, short with
  | [], _ => rfl
  | [p], _ => simp [predotUFor]
  | [p, q], _ => simp [predotUFor]

theorem predotU_pFor (t x k : Pattern) :
    predotU (pFor t x k) = pFor (predotU t) (predotU x) (dotted (pvars t) (predotU k)) := by
  simp [pFor, predotU_apply, predotUFor_cons3]

theorem predotU_tProc (p : Pattern) : predotU (tProc p) = tProc (predotU p) := by
  simp [tProc, predotU_apply]

theorem predotU_nQuote (p : Pattern) : predotU (nQuote p) = nQuote (predotU p) := by
  simp [nQuote, predotU, predotUList_eq_map]

theorem predotU_pZero : predotU pZero = pZero := by
  simp [pZero, predotU_apply]

theorem predotU_pPar (xs : List Pattern) : predotU (pPar xs) = pPar (xs.map predotU) := by
  simp [pPar, predotU, predotUList_eq_map]

/-! ## Variables are kept -/

theorem flatMap_pvars_map (f : Pattern → Pattern) (l : List Pattern) (h : ∀ q ∈ l, pvars (f q) = pvars q) :
    (l.map f).flatMap pvars = l.flatMap pvars := by
  rw [List.flatMap_map]
  exact List.flatMap_congr h

/-- **Dotting keeps the variables, in order.** -/
theorem pvars_dotted (vs : List String) (p : Pattern) : pvars (dotted vs p) = pvars p := by
  unfold dotted
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, pvars (psubst (quoteOn vs) q) = pvars q) with
  | bvar n => rfl
  | fvar x =>
      by_cases inside : x ∈ vs
      · simp [psubst, quoteOn, inside, nQuote, pvars, pvars.pvarsList]
      · simp [psubst, quoteOn, inside, pvars]
  | apply c args ih =>
      simp only [psubst, pvars_apply, psubstList_eq_map, pvarsList_eq_flatMap]
      exact flatMap_pvars_map _ args ih
  | lambda nm body ih =>
      simp only [psubst, pvars]
      exact ih
  | multiLambda n nms body ih =>
      simp only [psubst, pvars]
      exact ih
  | subst body repl ihb ihr => simp only [psubst, pvars, ihb, ihr]
  | collection ct elems rest ih =>
      simp only [psubst, pvars, psubstList_eq_map, pvarsList_eq_flatMap]
      exact flatMap_pvars_map _ elems ih
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

/-- **The uniform representation keeps the variables, in order.** -/
theorem pvars_predotU (p : Pattern) : pvars (predotU p) = pvars p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, pvars (predotU q) = pvars q) with
  | bvar n => rfl
  | fvar x => rfl
  | apply c args ih =>
      rw [predotU_apply, pvars_apply, pvars_apply, pvarsList_eq_flatMap, pvarsList_eq_flatMap]
      split_ifs with isFor
      · by_cases short : args.length < 3
        · rw [predotUFor_short args short]
          exact flatMap_pvars_map predotU args ih
        · match args, ih, short with
          | t :: x :: k :: rest, ih, _ =>
              rw [predotUFor_cons3]
              simp only [List.flatMap_cons, pvars_dotted, ih t (by simp), ih x (by simp), ih k (by simp),
                flatMap_pvars_map predotU rest (fun q member => ih q (by simp [member]))]
          | [], _, short => exact absurd (by simp) short
          | [_], _, short => exact absurd (by simp) short
          | [_, _], _, short => exact absurd (by simp) short
      · exact flatMap_pvars_map predotU args ih
  | lambda nm body ih =>
      simp only [predotU, pvars]
      exact ih
  | multiLambda n nms body ih =>
      simp only [predotU, pvars]
      exact ih
  | subst body repl ihb ihr => simp only [predotU, pvars, ihb, ihr]
  | collection ct elems rest ih =>
      simp only [predotU, pvars, predotUList_eq_map, pvarsList_eq_flatMap]
      exact flatMap_pvars_map predotU elems ih
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

/-! ## Injectivity -/

theorem dotted_fvar (vs : List String) (y : String) :
    dotted vs (.fvar y) = if y ∈ vs then nQuote (.fvar y) else .fvar y := by
  by_cases inside : y ∈ vs <;> simp [dotted, psubst, quoteOn, inside]

/-- A dotted term is a variable only where the term was that variable, not dotted. -/
theorem dotted_eq_fvar {vs : List String} {a : Pattern} {x : String} (h : dotted vs a = .fvar x) :
    a = .fvar x ∧ x ∉ vs := by
  cases a with
  | fvar y =>
      rw [dotted_fvar] at h
      split_ifs at h with inside
      · simp [nQuote] at h
      · obtain rfl := Pattern.fvar.inj h
        exact ⟨rfl, inside⟩
  | _ => simp [dotted, psubst] at h

/-- A dotted term is the quote of a dotted variable only where the term was that variable. -/
theorem dotted_eq_quote {vs : List String} {a : Pattern} {x : String} (inside : x ∈ vs)
    (h : dotted vs a = nQuote (.fvar x)) : a = .fvar x := by
  cases a with
  | fvar y =>
      rw [dotted_fvar] at h
      split_ifs at h with member
      · simp only [nQuote, Pattern.apply.injEq, List.cons.injEq, Pattern.fvar.injEq, and_true, true_and] at h
        rw [h]
      · simp [nQuote] at h
  | apply c args =>
      exfalso
      simp only [dotted, psubst, nQuote, Pattern.apply.injEq, psubstList_eq_map] at h
      obtain ⟨_, lists⟩ := h
      obtain ⟨a', rfl, image⟩ := List.map_eq_singleton_iff.mp lists
      exact (dotted_eq_fvar image).2 inside
  | _ => simp [dotted, psubst, nQuote] at h

theorem dotted_eq_dotted_fvar {vs : List String} {a : Pattern} {y : String}
    (h : dotted vs a = dotted vs (.fvar y)) : a = .fvar y := by
  rw [dotted_fvar vs y] at h
  split_ifs at h with inside
  · exact dotted_eq_quote inside h
  · exact (dotted_eq_fvar h).1

theorem map_inj_of {f : Pattern → Pattern} :
    ∀ {xs ys : List Pattern}, (∀ a ∈ xs, ∀ b, f a = f b → a = b) → xs.map f = ys.map f → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: _, y :: _, inj, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [inj x List.mem_cons_self y h.1, map_inj_of (fun a m b e => inj a (List.mem_cons_of_mem _ m) b e) h.2]

/-- **Dotting is injective.** -/
theorem dotted_injective (vs : List String) : Function.Injective (dotted vs) := by
  intro p
  induction p using Pattern.rec (motive_2 := fun ps => ∀ a ∈ ps, ∀ b, dotted vs a = dotted vs b → a = b) with
  | bvar n =>
      intro q h
      cases q with
      | bvar m =>
          simp only [dotted, psubst, Pattern.bvar.injEq] at h
          rw [h]
      | fvar y => exact absurd (dotted_eq_dotted_fvar h) (by simp)
      | _ => simp [dotted, psubst] at h
  | fvar x => intro q h; exact (dotted_eq_dotted_fvar h.symm).symm
  | apply c args ih =>
      intro q h
      cases q with
      | apply c' args' =>
          simp only [dotted, psubst, Pattern.apply.injEq, psubstList_eq_map] at h
          obtain ⟨rfl, lists⟩ := h
          rw [map_inj_of ih lists]
      | fvar y => exact absurd (dotted_eq_dotted_fvar h) (by simp)
      | _ => simp [dotted, psubst] at h
  | lambda nm body ih =>
      intro q h
      cases q with
      | lambda nm' body' =>
          simp only [dotted, psubst, Pattern.lambda.injEq] at h
          rw [h.1, ih h.2]
      | fvar y => exact absurd (dotted_eq_dotted_fvar h) (by simp)
      | _ => simp [dotted, psubst] at h
  | multiLambda n nms body ih =>
      intro q h
      cases q with
      | multiLambda n' nms' body' =>
          simp only [dotted, psubst, Pattern.multiLambda.injEq] at h
          rw [h.1, h.2.1, ih h.2.2]
      | fvar y => exact absurd (dotted_eq_dotted_fvar h) (by simp)
      | _ => simp [dotted, psubst] at h
  | subst body repl ihb ihr =>
      intro q h
      cases q with
      | subst body' repl' =>
          simp only [dotted, psubst, Pattern.subst.injEq] at h
          rw [ihb h.1, ihr h.2]
      | fvar y => exact absurd (dotted_eq_dotted_fvar h) (by simp)
      | _ => simp [dotted, psubst] at h
  | collection ct elems rest ih =>
      intro q h
      cases q with
      | collection ct' elems' rest' =>
          simp only [dotted, psubst, Pattern.collection.injEq, psubstList_eq_map] at h
          obtain ⟨rfl, lists, rfl⟩ := h
          rw [map_inj_of ih lists]
      | fvar y => exact absurd (dotted_eq_dotted_fvar h) (by simp)
      | _ => simp [dotted, psubst] at h
  | nil => simp_all
  | cons p ps head tail =>
      rename_i a member b h
      rcases List.mem_cons.mp member with rfl | later
      · exact head h
      · exact tail a later b h

theorem predotUFor_length (args : List Pattern) : (predotUFor args).length = args.length := by
  match args with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: rest => simp [predotUFor, predotUList_eq_map]

theorem predotUFor_inj {args args' : List Pattern} (ih : ∀ a ∈ args, ∀ b, predotU a = predotU b → a = b)
    (same : predotUFor args = predotUFor args') : args = args' := by
  have lengths : args.length = args'.length := by
    have := congrArg List.length same
    rwa [predotUFor_length, predotUFor_length] at this
  rcases args with _ | ⟨t, _ | ⟨x, _ | ⟨k, rest⟩⟩⟩ <;> rcases args' with _ | ⟨t', _ | ⟨x', _ | ⟨k', rest'⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at lengths <;> (try omega)
  · rfl
  · simp only [predotUFor, List.cons.injEq, and_true] at same
    rw [ih t List.mem_cons_self t' same]
  · simp only [predotUFor, List.cons.injEq, and_true] at same
    rw [ih t (by simp) t' same.1, ih x (by simp) x' same.2]
  · rw [predotUFor_cons3, predotUFor_cons3] at same
    simp only [List.cons.injEq] at same
    obtain ⟨st, sx, sk, srest⟩ := same
    obtain rfl := ih t (by simp) t' st
    have kk : predotU k = predotU k' := dotted_injective (pvars t) sk
    rw [ih x (by simp) x' sx, ih k (by simp) k' kk,
      map_inj_of (fun a m b e => ih a (by simp [m]) b e) srest]

/-- **The uniform representation is injective**, on every pattern. -/
theorem predotU_injective : Function.Injective predotU := by
  intro p
  induction p using Pattern.rec (motive_2 := fun ps => ∀ a ∈ ps, ∀ b, predotU a = predotU b → a = b) with
  | bvar n =>
      intro q h
      cases q with
      | bvar m =>
          simp only [predotU, Pattern.bvar.injEq] at h
          rw [h]
      | _ => simp [predotU] at h
  | fvar x =>
      intro q h
      cases q with
      | fvar y =>
          simp only [predotU, Pattern.fvar.injEq] at h
          rw [h]
      | _ => simp [predotU] at h
  | apply c args ih =>
      intro q h
      cases q with
      | apply c' args' =>
          rw [predotU_apply, predotU_apply] at h
          simp only [Pattern.apply.injEq] at h
          obtain ⟨rfl, lists⟩ := h
          by_cases isFor : c = "MFor"
          · rw [if_pos isFor, if_pos isFor] at lists
            rw [predotUFor_inj ih lists]
          · rw [if_neg isFor, if_neg isFor] at lists
            rw [map_inj_of ih lists]
      | _ => simp [predotU] at h
  | lambda nm body ih =>
      intro q h
      cases q with
      | lambda nm' body' =>
          simp only [predotU, Pattern.lambda.injEq] at h
          rw [h.1, ih h.2]
      | _ => simp [predotU] at h
  | multiLambda n nms body ih =>
      intro q h
      cases q with
      | multiLambda n' nms' body' =>
          simp only [predotU, Pattern.multiLambda.injEq] at h
          rw [h.1, h.2.1, ih h.2.2]
      | _ => simp [predotU] at h
  | subst body repl ihb ihr =>
      intro q h
      cases q with
      | subst body' repl' =>
          simp only [predotU, Pattern.subst.injEq] at h
          rw [ihb h.1, ihr h.2]
      | _ => simp [predotU] at h
  | collection ct elems rest ih =>
      intro q h
      cases q with
      | collection ct' elems' rest' =>
          simp only [predotU, Pattern.collection.injEq, predotUList_eq_map] at h
          obtain ⟨rfl, lists, rfl⟩ := h
          rw [map_inj_of ih lists]
      | _ => simp [predotU] at h
  | nil => simp_all
  | cons p ps head tail =>
      rename_i a member b h
      rcases List.mem_cons.mp member with rfl | later
      · exact head h
      · exact tail a later b h

/-! ## Parallel components -/

theorem predotUFor_eq_nil {args : List Pattern} : predotUFor args = [] ↔ args = [] := by
  match args with
  | [] => simp [predotUFor]
  | [_] => simp [predotUFor]
  | [_, _] => simp [predotUFor]
  | _ :: _ :: _ :: _ => simp [predotUFor]

/-- **The uniform representation commutes with taking parallel components.** -/
theorem components_predotU (p : Pattern) : components (predotU p) = (components p).map predotU := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, components (predotU q) = (components q).map predotU) with
  | bvar n => simp [predotU, components]
  | fvar x => simp [predotU, components]
  | apply c args _ =>
      by_cases zero : c = "MZero" ∧ args = []
      · obtain ⟨rfl, rfl⟩ := zero
        rw [show predotU (.apply "MZero" []) = pZero from predotU_pZero,
          show components (.apply "MZero" []) = [] from components_pZero, components_pZero]
        rfl
      · rw [components_apply_of_ne zero, predotU_apply, components_apply_of_ne]
        · simp only [List.map_cons, List.map_nil, predotU_apply]
        · intro h
          apply zero
          refine ⟨h.1, ?_⟩
          have empty := h.2
          split_ifs at empty with isFor
          · exact predotUFor_eq_nil.mp empty
          · exact List.map_eq_nil_iff.mp empty
  | lambda nm body _ => simp [predotU, components]
  | multiLambda n nms body _ => simp [predotU, components]
  | subst body repl _ _ => simp [predotU, components]
  | collection ct elems rest ih =>
      by_cases bag : ct = .hashBag ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := bag
        have each : ∀ (L : List Pattern), (∀ q ∈ L, components (predotU q) = (components q).map predotU) →
            (L.map predotU).flatMap components = (L.flatMap components).map predotU := by
          intro L hL
          rw [List.flatMap_map, List.map_flatMap]
          exact List.flatMap_congr hL
        have comps : ∀ (L : List Pattern),
            components (.collection .hashBag L none) = L.flatMap components := by
          intro L
          simp only [components, MeTTaCalculus.Corrected.componentsList_eq_flatMap]
        rw [show predotU (.collection .hashBag elems none) = .collection .hashBag (elems.map predotU) none by
            simp [predotU, predotUList_eq_map], comps, comps]
        exact each elems ih
      · rw [components_collection_of_ne bag]
        rw [show predotU (.collection ct elems rest) = .collection ct (elems.map predotU) rest by
            simp [predotU, predotUList_eq_map], components_collection_of_ne bag]
        simp only [List.map_cons, List.map_nil, predotU, predotUList_eq_map]
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

/-- **The top-level bag laws are preserved and reflected**: the components of two represented processes
are permutations of each other exactly when those of the processes are. -/
theorem perm_components_predotU_iff (p q : Pattern) :
    (components (predotU p)).Perm (components (predotU q)) ↔ (components p).Perm (components q) := by
  rw [components_predotU, components_predotU]
  exact List.map_perm_map_iff predotU_injective

/-! ## The bag laws are preserved, at every depth -/

/-- One bag law keeps the variables, as a set. -/
theorem mem_pvars_of_bagRewrite {a b : Pattern} (h : ReflQuotient.BagRewrite a b) (x : String) :
    x ∈ pvars a ↔ x ∈ pvars b := by
  induction h with
  | root ax =>
      cases ax with
      | perm perm =>
          simp only [pPar, pvars, pvarsList_eq_flatMap]
          exact (perm.flatMap_right pvars).mem_iff
      | flatten xs ys zs =>
          have same : pvars (pPar (xs ++ pPar ys :: zs)) = pvars (pPar (xs ++ ys ++ zs)) := by
            simp only [pPar, pvars, pvarsList_eq_flatMap, List.flatMap_append, List.flatMap_cons,
              List.append_assoc]
          rw [same]
      | zero xs zs =>
          have same : pvars (pPar (xs ++ pZero :: zs)) = pvars (pPar (xs ++ zs)) := by
            simp only [pPar, pZero, pvars, pvarsList_eq_flatMap, List.flatMap_append, List.flatMap_cons,
              List.flatMap_nil, List.nil_append]
          rw [same]
      | single _ =>
          simp only [pPar, pvars, pvarsList_eq_flatMap, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      | empty =>
          have same : pvars (pPar []) = pvars pZero := rfl
          rw [same]
  | apply c pre post _ ih => simp [pvars_apply, pvarsList_eq_flatMap, List.flatMap_append, ih]
  | lambda nm _ ih => simp only [pvars]; exact ih
  | multiLambda n nms _ ih => simp only [pvars]; exact ih
  | substBody repl _ ih => simp [pvars, ih]
  | substRepl body _ ih => simp [pvars, ih]
  | collection ct pre post rest _ ih => simp [pvars, pvarsList_eq_flatMap, List.flatMap_append, ih]

/-- Dotting depends on the dotted variables as a set. -/
theorem dotted_congr {vs ws : List String} (same : ∀ x, x ∈ vs ↔ x ∈ ws) : dotted vs = dotted ws := by
  have quotes : quoteOn vs = quoteOn ws := by
    funext x
    simp only [quoteOn, same x]
  funext p
  simp only [dotted, quotes]

/-- One member related, the others equal. -/
theorem forall₂_middle (pre post : List Pattern) {a b : Pattern} (h : BagLaws a b) :
    List.Forall₂ BagLaws (pre ++ a :: post) (pre ++ b :: post) := by
  induction pre with
  | nil => exact .cons h (List.forall₂_same.mpr fun q _ => ReflQuotient.BagLaws.refl q)
  | cons q pre ih => exact .cons (ReflQuotient.BagLaws.refl q) ih

/-- One bag law at one position is preserved by the uniform representation. -/
theorem bagRewrite_predotU {a b : Pattern} (h : ReflQuotient.BagRewrite a b) :
    BagLaws (predotU a) (predotU b) := by
  induction h with
  | root ax =>
      cases ax with
      | perm perm =>
          rw [predotU_pPar, predotU_pPar]
          exact ReflQuotient.BagLaws.of_axiom (.perm (perm.map _))
      | flatten xs ys zs =>
          rw [predotU_pPar, predotU_pPar]
          simp only [List.map_append, List.map_cons, predotU_pPar]
          exact ReflQuotient.BagLaws.of_axiom (.flatten _ _ _)
      | zero xs zs =>
          rw [predotU_pPar, predotU_pPar]
          simp only [List.map_append, List.map_cons, predotU_pZero]
          exact ReflQuotient.BagLaws.of_axiom (.zero _ _)
      | single p =>
          rw [predotU_pPar]
          exact ReflQuotient.BagLaws.of_axiom (.single _)
      | empty =>
          rw [predotU_pPar, predotU_pZero]
          exact ReflQuotient.BagLaws.of_axiom .empty
  | @apply c pre post a b r ih =>
      rw [predotU_apply, predotU_apply]
      apply ReflQuotient.bagLaws_apply
      split_ifs with isFor
      · have sameVars := mem_pvars_of_bagRewrite r
        match pre, post with
        | [], [] =>
            simp only [List.nil_append, predotUFor]
            exact .cons ih .nil
        | [], [q] =>
            simp only [List.nil_append, predotUFor]
            exact .cons ih (.cons (ReflQuotient.BagLaws.refl _) .nil)
        | [], x :: k :: rest =>
            simp only [List.nil_append, predotUFor_cons3]
            rw [dotted_congr sameVars]
            exact .cons ih (List.forall₂_same.mpr fun q _ => ReflQuotient.BagLaws.refl q)
        | [t], [] =>
            simp only [List.singleton_append, predotUFor]
            exact .cons (ReflQuotient.BagLaws.refl _) (.cons ih .nil)
        | [t], k :: rest =>
            simp only [List.singleton_append, predotUFor_cons3]
            exact .cons (ReflQuotient.BagLaws.refl _) (.cons ih (List.forall₂_same.mpr fun q _ =>
              ReflQuotient.BagLaws.refl q))
        | [t, x], post =>
            simp only [List.cons_append, List.nil_append, predotUFor_cons3]
            exact .cons (ReflQuotient.BagLaws.refl _) (.cons (ReflQuotient.BagLaws.refl _)
              (.cons (ReflQuotient.bagLaws_psubst _ ih) (List.forall₂_same.mpr fun q _ =>
                ReflQuotient.BagLaws.refl q)))
        | t :: x :: k :: rest, post =>
            simp only [List.cons_append, predotUFor_cons3, List.map_append, List.map_cons]
            exact .cons (ReflQuotient.BagLaws.refl _) (.cons (ReflQuotient.BagLaws.refl _)
              (.cons (ReflQuotient.BagLaws.refl _) (forall₂_middle _ _ ih)))
      · simp only [List.map_append, List.map_cons]
        exact forall₂_middle _ _ ih
  | lambda nm _ ih =>
      simp only [predotU]
      exact ReflQuotient.BagLaws.map (f := .lambda nm) (fun r => .lambda nm r) ih
  | multiLambda n nms _ ih =>
      simp only [predotU]
      exact ReflQuotient.BagLaws.map (f := .multiLambda n nms) (fun r => .multiLambda n nms r) ih
  | substBody repl _ ih =>
      simp only [predotU]
      exact ReflQuotient.BagLaws.map (f := fun z => .subst z (predotU repl)) (fun r => .substBody _ r) ih
  | substRepl body _ ih =>
      simp only [predotU]
      exact ReflQuotient.BagLaws.map (f := fun z => .subst (predotU body) z) (fun r => .substRepl _ r) ih
  | collection ct pre post rest _ ih =>
      simp only [predotU, predotUList_eq_map, List.map_append, List.map_cons]
      exact ReflQuotient.bagLaws_collection ct rest (forall₂_middle _ _ ih)

/-- **The uniform representation preserves equality modulo the bag laws**, at every depth: it is a map of the
quotient frame's equality. -/
theorem bagLaws_predotU {p q : Pattern} (h : BagLaws p q) : BagLaws (predotU p) (predotU q) := by
  induction h with
  | rel a b r => exact bagRewrite_predotU r
  | refl a => exact ReflQuotient.BagLaws.refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Packing in any order represents the reduct modulo the bag laws**: a bag of the represented components of
a process, in any order, is the represented process modulo the bag laws. -/
theorem bagLaws_pack (R : Pattern) {L : List Pattern} (perm : L.Perm (components R)) :
    BagLaws (pPar (L.map predotU)) (predotU R) := by
  apply ReflQuotient.bagLaws_of_perm_components
  have leaves : ∀ c ∈ L.map predotU, components c = [c] := by
    intro c member
    obtain ⟨d, inL, rfl⟩ := List.mem_map.mp member
    have leaf : components d = [d] :=
      MeTTaCalculus.Corrected.components_of_mem_components R d (perm.subset inL)
    rw [components_predotU, leaf]
    rfl
  rw [MeTTaCalculus.Corrected.components_pPar_leaves _ leaves, components_predotU]
  exact perm.map predotU

/-! ## The quotes of the corrected REFL -/

/-- **The uniform representation fixes every closed form**: every guard of a closed form has a pattern without
variables (`pvars_closed_pattern`), so nothing is dotted. -/
theorem predotU_closeIn (p : Pattern) :
    ∀ env : List (List String), predotU (MeTTaCalculus.Corrected.closeIn env p) = MeTTaCalculus.Corrected.closeIn env p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ env : List (List String),
      predotU (MeTTaCalculus.Corrected.closeIn env q) = MeTTaCalculus.Corrected.closeIn env q) with
  | bvar n => intro env; rfl
  | fvar x =>
      intro env
      cases found : MeTTaCalculus.Corrected.lookupBound env x with
      | none => simp [MeTTaCalculus.Corrected.closeIn, found, predotU]
      | some code => simp [MeTTaCalculus.Corrected.closeIn, found, predotU, MeTTaCalculus.Corrected.boundCode]
  | apply c args ih =>
      intro env
      rw [MeTTaCalculus.Corrected.closeIn_apply, predotU_apply]
      congr 1
      split_ifs with isFor
      · rcases MeTTaCalculus.Corrected.closeFor_cases env args with ⟨short, same⟩ | ⟨t, x, k, rest, rfl, same⟩
        · have shortMap : (args.map (MeTTaCalculus.Corrected.closeIn env)).length < 3 := by
            rw [List.length_map]
            exact short
          rw [same, predotUFor_short _ shortMap, List.map_map]
          exact List.map_congr_left fun q member => ih q member env
        · rw [same, predotUFor_cons3, MeTTaCalculus.Corrected.pvars_closed_pattern, FiniteProgram.dotted_nil,
            ih t (by simp) _, ih x (by simp) env, ih k (by simp) _, List.map_map]
          simp only [List.cons.injEq, true_and]
          exact List.map_congr_left fun q member => ih q (by simp [member]) env
      · rw [List.map_map]
        exact List.map_congr_left fun q member => ih q member env
  | lambda nm body ih =>
      intro env
      simp only [MeTTaCalculus.Corrected.closeIn, predotU, ih env]
  | multiLambda n nms body ih =>
      intro env
      simp only [MeTTaCalculus.Corrected.closeIn, predotU, ih env]
  | subst body repl ihb ihr =>
      intro env
      simp only [MeTTaCalculus.Corrected.closeIn, predotU, ihb env, ihr env]
  | collection ct elems rest ih =>
      intro env
      simp only [MeTTaCalculus.Corrected.closeIn, predotU, MeTTaCalculus.Corrected.closeList_eq_map,
        predotUList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun q member => ih q member env
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member env
      rcases List.mem_cons.mp member with rfl | later
      · exact head env
      · exact tail q later env

/-- **The uniform representation fixes every quote the corrected REFL makes.** -/
theorem predotU_canonicalBag (R : Pattern) : predotU (canonicalBag R) = canonicalBag R := by
  unfold canonicalBag
  rw [predotU_pPar]
  congr 1
  conv => rhs; rw [← List.map_id (MeTTaCalculus.Corrected.codeOrder (components (MeTTaCalculus.Corrected.close R)))]
  apply List.map_congr_left
  intro c member
  have inComps := (MeTTaCalculus.Corrected.codeOrder_perm _).subset member
  unfold MeTTaCalculus.Corrected.close at inComps
  rw [MeTTaCalculus.Corrected.components_closeIn] at inComps
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp inComps
  exact predotU_closeIn d []

/-- Equality modulo the bag laws keeps the variables, as a set. -/
theorem mem_pvars_of_bagLaws {a b : Pattern} (h : BagLaws a b) (x : String) : x ∈ pvars a ↔ x ∈ pvars b := by
  induction h with
  | rel a b r => exact mem_pvars_of_bagRewrite r x
  | refl a => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **For every closed reduct with a variable, the corrected REFL's quote is not the made quote modulo the bag
laws**: the corrected quote is closed and has no variable, while the made quote keeps the reduct's variables.
A reduct is closed when each of its variables is bound by one of its guards. -/
theorem canonicalBag_not_made_quote (R : Pattern) (closed : pvars (MeTTaCalculus.Corrected.close R) = [])
    {y : String} (binds : y ∈ pvars R) : ¬ BagLaws (canonicalBag R) (predotU R) := by
  intro h
  have inMade : y ∈ pvars (predotU R) := by
    rw [pvars_predotU]
    exact binds
  have inQuote := (mem_pvars_of_bagLaws h y).mpr inMade
  unfold canonicalBag at inQuote
  simp only [pPar, pvars, pvarsList_eq_flatMap, List.mem_flatMap] at inQuote
  obtain ⟨c, member, inC⟩ := inQuote
  have inClose := MeTTaCalculus.Corrected.pvars_of_mem_components
    ((MeTTaCalculus.Corrected.codeOrder_perm _).subset member) inC
  rw [closed] at inClose
  exact List.not_mem_nil inClose

/-! ## Tame processes: the uniform representation is `predot` -/

theorem predotU_of_guardFree (p : Pattern) (free : guardFree p = true) : predotU p = p := by
  revert free
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, guardFree q = true → predotU q = q) with
  | bvar n => intro _; rfl
  | fvar x => intro _; rfl
  | apply c args ih =>
      intro free
      simp only [guardFree, Bool.and_eq_true, bne_iff_ne, ne_eq, guardFreeList_iff] at free
      rw [predotU_apply, if_neg free.1]
      congr 1
      conv => rhs; rw [← List.map_id args]
      exact List.map_congr_left fun q member => ih q member (free.2 q member)
  | lambda nm body ih =>
      intro free
      simp only [guardFree] at free
      simp only [predotU, ih free]
  | multiLambda n nms body ih =>
      intro free
      simp only [guardFree] at free
      simp only [predotU, ih free]
  | subst body repl ihb ihr =>
      intro free
      simp only [guardFree, Bool.and_eq_true] at free
      simp only [predotU, ihb free.1, ihr free.2]
  | collection ct elems rest ih =>
      intro free
      simp only [guardFree, guardFreeList_iff] at free
      simp only [predotU, predotUList_eq_map]
      congr 1
      conv => rhs; rw [← List.map_id elems]
      exact List.map_congr_left fun q member => ih q member (free q member)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member freeQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head freeQ
      · exact tail q later freeQ

/-- **On tame processes the uniform representation is `predot`.** Design fix (b) changes only patterns
that quote a guard. -/
theorem predotU_eq_predot_of_tame (p : Pattern) (tameP : tame p = true) : predotU p = predot p := by
  revert tameP
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, tame q = true → predotU q = predot q) with
  | bvar n => intro _; rfl
  | fvar x => intro _; rfl
  | apply c args ih =>
      intro tameP
      rw [predotU_apply, predot_apply]
      simp only [tame] at tameP
      split_ifs at tameP ⊢ with isFor
      · obtain ⟨t, x, k, rfl, _, freeT, tameX, tameK⟩ := (tameFor_iff _).mp tameP
        rw [predotUFor_cons3, predotFor_cons3, predotU_of_guardFree t freeT, ih x (by simp) tameX,
          ih k (by simp) tameK]
        rfl
      · rw [tameList_iff] at tameP
        exact congrArg _ (List.map_congr_left fun q member => ih q member (tameP q member))
  | lambda nm body ih => intro tameP; simp [tame] at tameP
  | multiLambda n nms body ih => intro tameP; simp [tame] at tameP
  | subst body repl ihb ihr => intro tameP; simp [tame] at tameP
  | collection ct elems rest ih =>
      intro tameP
      simp only [tame, Bool.and_eq_true, tameList_iff] at tameP
      simp only [predotU, predot, predotUList_eq_map, predotList_eq_map]
      exact congrArg (fun L => Pattern.collection ct L rest)
        (List.map_congr_left fun q member => ih q member (tameP.2 q member))
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member tameQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head tameQ
      · exact tail q later tameQ

/-! ## The representation commutes with ground substitutions -/

/-- **A pattern without variables is its own representation.** -/
theorem predotU_ground (p : Pattern) (closed : pvars p = []) : predotU p = p := by
  revert closed
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, pvars q = [] → predotU q = q) with
  | bvar n => intro _; rfl
  | fvar x => intro _; rfl
  | apply c args ih =>
      intro closed
      have each : ∀ q ∈ args, predotU q = q := fun q member =>
        ih q member (List.eq_nil_iff_forall_not_mem.mpr fun y occurs =>
          List.eq_nil_iff_forall_not_mem.mp closed y (MeTTaCalculus.Corrected.mem_pvars_apply_of member occurs))
      have mapped : args.map predotU = args := by
        conv => rhs; rw [← List.map_id args]
        exact List.map_congr_left each
      rw [predotU_apply]
      congr 1
      split_ifs with isFor
      · match args, each, mapped, closed with
        | t :: x :: k :: rest, each, _, closed =>
            have tClosed : pvars t = [] := List.eq_nil_iff_forall_not_mem.mpr fun y occurs =>
              List.eq_nil_iff_forall_not_mem.mp closed y
                (MeTTaCalculus.Corrected.mem_pvars_apply_of (by simp) occurs)
            rw [predotUFor_cons3, tClosed, FiniteProgram.dotted_nil, each t (by simp), each x (by simp),
              each k (by simp)]
            have restSame : rest.map predotU = rest := by
              conv => rhs; rw [← List.map_id rest]
              exact List.map_congr_left fun q member => each q (by simp [member])
            rw [restSame]
        | [], _, mapped, _ => rw [predotUFor_short [] (by simp), mapped]
        | [p], _, mapped, _ => rw [predotUFor_short [p] (by simp), mapped]
        | [p, q], _, mapped, _ => rw [predotUFor_short [p, q] (by simp), mapped]
      · exact mapped
  | lambda nm body ih =>
      intro closed
      simp only [predotU]
      rw [ih (by simpa [pvars] using closed)]
  | multiLambda n nms body ih =>
      intro closed
      simp only [predotU]
      rw [ih (by simpa [pvars] using closed)]
  | subst body repl ihb ihr =>
      intro closed
      have both : pvars body = [] ∧ pvars repl = [] := by simpa [pvars] using closed
      simp only [predotU]
      rw [ihb both.1, ihr both.2]
  | collection ct elems rest ih =>
      intro closed
      have each : ∀ q ∈ elems, predotU q = q := fun q member =>
        ih q member (List.eq_nil_iff_forall_not_mem.mpr fun y occurs =>
          List.eq_nil_iff_forall_not_mem.mp closed y (MeTTaCalculus.Corrected.mem_pvars_collection_of member occurs))
      simp only [predotU, predotUList_eq_map]
      congr 1
      conv => rhs; rw [← List.map_id elems]
      exact List.map_congr_left each
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member closedQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head closedQ
      · exact tail q later closedQ

/-- A ground pattern and channel leave the uniform representation of the whole
continuation intact, including its own receive binders. -/
theorem predotU_ground_guard {t ch A : Pattern} (groundT : pvars t = [])
    (groundCh : pvars ch = []) :
    predotU (pFor t ch A) = pFor t ch (predotU A) := by
  rw [predotU_pFor, predotU_ground t groundT, predotU_ground ch groundCh, groundT,
    FiniteProgram.dotted_nil]

/-- A substitution may retain open variables. Its images must already
be stable under representation, and it must neither replace a local
binder nor introduce that binder into one of its images. -/
theorem predotU_psubst_of_stable {τ : PSubst}
    (stable : ∀ x v, τ x = some v → predotU v = v) (p : Pattern)
    (outside : ∀ y ∈ binders p, τ y = none ∧ ∀ x v, τ x = some v → y ∉ pvars v) :
    predotU (psubst τ p) = psubst τ (predotU p) := by
  revert outside
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      (∀ y ∈ binders q, τ y = none ∧ ∀ x v, τ x = some v → y ∉ pvars v) →
        predotU (psubst τ q) = psubst τ (predotU q)) with
  | bvar n => intro _; rfl
  | fvar x =>
      intro _
      show predotU ((τ x).getD (.fvar x)) = (τ x).getD (.fvar x)
      cases found : τ x with
      | some v => exact stable x v found
      | none => rfl
  | apply c args ih =>
      intro outside
      have psubstApply : ∀ L : List Pattern, psubst τ (.apply c L) = .apply c (L.map (psubst τ)) := by
        intro L
        simp only [psubst, psubstList_eq_map]
      rw [psubstApply, predotU_apply, predotU_apply, psubstApply]
      congr 1
      by_cases isFor : c = "MFor"
      · rw [if_pos isFor, if_pos isFor]
        rw [binders_apply, if_pos isFor] at outside
        match args, ih, outside with
        | t :: x :: k :: rest, ih, outside =>
            rw [bindersFor_cons3] at outside
            have tFixed : psubst τ t = t := by
              rw [psubst_congr τ (fun _ => none) t fun y occurs =>
                (outside y (by simp [occurs])).1, psubst_none]
            have tFixedU : psubst τ (predotU t) = predotU t := by
              rw [psubst_congr τ (fun _ => none) (predotU t) fun y occurs =>
                (outside y (by rw [pvars_predotU] at occurs; simp [occurs])).1, psubst_none]
            have xSame := ih x (by simp) fun y inside => outside y (by simp [inside])
            have kSame := ih k (by simp) fun y inside => outside y (by simp [inside])
            have restSame : ∀ q ∈ rest, predotU (psubst τ q) = psubst τ (predotU q) := fun q member =>
              ih q (by simp [member]) fun y inside =>
                outside y (by simp only [List.mem_append, List.mem_flatMap]; exact .inr ⟨q, member, inside⟩)
            have apartT : ∀ y ∈ pvars t, τ y = none := fun y occurs => (outside y (by simp [occurs])).1
            have dotStable : ∀ z v, τ z = some v → dotted (pvars t) v = v := by
              intro z v found
              unfold dotted
              refine (psubst_congr _ (fun _ => none) v ?_).trans (psubst_none v)
              intro y occurs
              have notBound : y ∉ pvars t := fun bound =>
                (outside y (by simp [bound])).2 z v found occurs
              simp [quoteOn, notBound]
            have restMap : (rest.map (psubst τ)).map predotU = (rest.map predotU).map (psubst τ) := by
              rw [List.map_map, List.map_map]
              exact List.map_congr_left restSame
            rw [List.map_cons, List.map_cons, List.map_cons, predotUFor_cons3, predotUFor_cons3, tFixed, xSame,
              kSame, dotted_psubst_comm_of_images (pvars t) dotStable apartT, restMap]
            simp only [List.map_cons, tFixedU]
        | [], _, _ => rfl
        | [p], ih, outside =>
            rw [bindersFor_short [p] (by simp)] at outside
            have pSame := ih p (by simp) fun y inside => outside y (by simp [inside])
            simp only [List.map_cons, List.map_nil, predotUFor, pSame]
        | [p, q], ih, outside =>
            rw [bindersFor_short [p, q] (by simp)] at outside
            have pSame := ih p (by simp) fun y inside => outside y (by simp [inside])
            have qSame := ih q (by simp) fun y inside => outside y (by simp [inside])
            simp only [List.map_cons, List.map_nil, predotUFor, pSame, qSame]
      · rw [binders_apply, if_neg isFor] at outside
        simp only [if_neg isFor, List.map_map]
        exact List.map_congr_left fun q member =>
          ih q member fun y inside => outside y (List.mem_flatMap.mpr ⟨q, member, inside⟩)
  | lambda nm body ih =>
      intro outside
      simp only [psubst, predotU]
      rw [ih fun y inside => outside y (by simpa [binders] using inside)]
  | multiLambda n nms body ih =>
      intro outside
      simp only [psubst, predotU]
      rw [ih fun y inside => outside y (by simpa [binders] using inside)]
  | subst body repl ihb ihr =>
      intro outside
      simp only [psubst, predotU]
      rw [ihb fun y inside => outside y (by simp [binders, inside]),
        ihr fun y inside => outside y (by simp [binders, inside])]
  | collection ct elems rest ih =>
      intro outside
      simp only [psubst, predotU, psubstList_eq_map, predotUList_eq_map, List.map_map]
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

/-- Ground images are stable and cannot contain a surrounding binder. -/
theorem predotU_psubst {τ : PSubst} (ground : GroundValued τ) (p : Pattern)
    (outside : ∀ x ∈ binders p, τ x = none) : predotU (psubst τ p) = psubst τ (predotU p) :=
  predotU_psubst_of_stable (fun x v h => predotU_ground v (ground x v h)) p fun y h =>
    ⟨outside y h, fun x v image => by simp [ground x v image]⟩

/-- **A solution that agrees with a ground binding list reads a uniformly pre-dotted continuation as the
representation of its dot**, under the hypotheses of `dotted_reads_predot`. -/
theorem dotted_reads_predotU {bs : Bindings} {keys vs : List String} (keysOf : ∀ e ∈ bs, e.1 ∈ keys)
    (bound : ∀ x ∈ keys, ∃ v, bs.lookup x = some v ∧ pvars v = [])
    {σ : PSubst} (agrees : ∀ x ∈ keys, ∀ v, bs.lookup x = some v → psubst σ (.fvar x) = v)
    (A : Pattern) (fo : firstOrder A = true) (sub : ∀ x ∈ vs, x ∈ keys)
    (reads : ∀ x ∈ pvars A, x ∈ keys → x ∈ vs) (kept : ∀ x ∈ keys, x ∉ binders A) :
    psubst σ (dotted vs (predotU A)) = psubst σ (predotU (applyDot bs A)) := by
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
  rw [predotU_psubst ground A untouched]
  unfold dotted
  rw [psubst_comp, psubst_comp]
  apply psubst_getD_congr_on
  intro x occurs
  have inA : x ∈ pvars A := by
    rw [pvars_predotU] at occurs
    exact occurs
  by_cases inKeys : x ∈ keys
  · have inVs := reads x inA inKeys
    obtain ⟨v, found, closed⟩ := bound x inKeys
    simp only [pcomp, quoteOn, if_pos inVs, Option.getD_some, psubst_nQuote, found, Option.map_some]
    rw [agrees x inKeys v found, psubst_of_pvars_nil σ v closed]
  · have notVs : x ∉ vs := fun inVs => inKeys (sub x inVs)
    have look : bs.lookup x = none := lookup_eq_none_of_keys keysOf inKeys
    simp only [pcomp, quoteOn, if_neg notVs, look, Option.map_none]

/-! ## COMM on rows represented uniformly -/

section Step

variable {O : Type*} [DecidableEq O]

/-- **COMM as one firing of the finite program, on rows represented uniformly.** Under the side conditions
of `FiniteProgram.comm_one_firing` (a ground principal unifier `gp` of the written patterns, the variable
convention, first-order continuations, rows that read as the represented inputs, distinct made identities
that are not present, a fresh opening) and the named hypothesis `gpU` that the represented patterns have
the same ground principal unifier, the firing is admitted, the manuscript's COMM relates the redex to its
dotted reduct, and every solution of the result reads the made rows as the uniform representations of the
dotted continuations. -/
theorem comm_one_firing_uniform (label : O → Pattern) (t u channel A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (gpU : GroundPrincipal (predotU t) (predotU u) bs)
    (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (predotU (pFor t channel A)))
    (readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (predotU (pFor u channel B)))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (glued : ∃ σ₀ : PSubst, patternAction.Models σ₀ C.equations ∧
      psubst σ₀ (predotU t) = psubst σ₀ (predotU u))
    {ρ : PSubst} (opensFreshly : (commAt ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E program).Admits (s := embed label C) (commAt ρ first second made₁ made₂) ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel A) (pFor u channel B))
        (par (applyDot bs A) (applyDot bs B)) ∧
      MeTTaCalculus.Corrected.Step MeTTaCalculus.Corrected.conventional
        (par (pFor t channel A) (pFor u channel B)) (par (applyDot bs A) (applyDot bs B)) ∧
      ∀ σ : PSubst, patternAction.Models σ
          ((commAt ρ first second made₁ made₂).result X (embed label C)).knowledge →
        psubst σ (((commAt ρ first second made₁ made₂).result X (embed label C)).label made₁) =
            psubst σ (predotU (applyDot bs A)) ∧
          psubst σ (((commAt ρ first second made₁ made₂).result X (embed label C)).label made₂) =
            psubst σ (predotU (applyDot bs B)) := by
  obtain ⟨σ₀, known, unifies⟩ := glued
  have rowFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (pFor (predotU t) (predotU channel) (dotted (pvars t) (predotU A))) :=
    fun σ solved => (readsFirst σ solved).trans (by rw [predotU_pFor])
  have rowSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (pFor (predotU u) (predotU channel) (dotted (pvars u) (predotU B))) :=
    fun σ solved => (readsSecond σ solved).trans (by rw [predotU_pFor])
  refine ⟨comm_admits_inputs label (predotU t) (predotU u) (predotU channel) (dotted (pvars t) (predotU A))
      (dotted (pvars u) (predotU B)) C first second made₁ made₂ rowFirst rowSecond distinct madeDistinct
      present₁ present₂ fresh₁ fresh₂ known unifies opensFreshly,
    .comm t u channel A B bs gp,
    .comm t u channel A B bs (Comm.principal_of_groundPrincipal gp) convention, fun σ solved => ?_⟩
  obtain ⟨-, unify, -, body₁, body₂⟩ := comm_reads_inputs label (predotU t) (predotU u) (predotU channel)
    (predotU channel) (dotted (pvars t) (predotU A)) (dotted (pvars u) (predotU B)) C first second made₁ made₂
    rowFirst rowSecond madeDistinct ρ solved
  obtain ⟨keptA, keptB⟩ := keys_of_apart convention
  have keysEq : pvars (predotU t) ++ pvars (predotU u) = pvars t ++ pvars u := by
    rw [pvars_predotU, pvars_predotU]
  have keysOf : ∀ e ∈ bs, e.1 ∈ pvars t ++ pvars u := fun e member => keysEq ▸ gpU.keys e member
  have covers : ∀ x ∈ pvars t ++ pvars u, ∃ v, bs.lookup x = some v ∧ pvars v = [] :=
    fun x inside => gpU.covers x (keysEq ▸ inside)
  have agrees : ∀ x ∈ pvars t ++ pvars u, ∀ v, bs.lookup x = some v → psubst σ (.fvar x) = v :=
    fun x inside => gpU.principal σ unify x (keysEq ▸ inside)
  refine ⟨?_, ?_⟩
  · rw [body₁]
    refine dotted_reads_predotU keysOf covers agrees A foA (fun x inside => List.mem_append_left _ inside) ?_ keptA
    intro x inA inKeys
    rcases List.mem_append.mp inKeys with inT | inU
    · exact inT
    · exact absurd inA (convention.rightOutside x inU)
  · rw [body₂]
    refine dotted_reads_predotU keysOf covers agrees B foB (fun x inside => List.mem_append_right _ inside) ?_ keptB
    intro x inB inKeys
    rcases List.mem_append.mp inKeys with inT | inU
    · exact absurd inB (convention.leftOutside x inT)
    · exact inU

/-- **On guard-free patterns the named hypothesis is the original one**: the represented patterns are the
written ones. -/
theorem comm_one_firing_uniform_of_guardFree (label : O → Pattern) (t u channel A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (freeT : guardFree t = true) (freeU : guardFree u = true)
    (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (predotU (pFor t channel A)))
    (readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (predotU (pFor u channel B)))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (glued : ∃ σ₀ : PSubst, patternAction.Models σ₀ C.equations ∧ psubst σ₀ t = psubst σ₀ u)
    {ρ : PSubst} (opensFreshly : (commAt ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E program).Admits (s := embed label C) (commAt ρ first second made₁ made₂) ∧
      ∀ σ : PSubst, patternAction.Models σ
          ((commAt ρ first second made₁ made₂).result X (embed label C)).knowledge →
        psubst σ (((commAt ρ first second made₁ made₂).result X (embed label C)).label made₁) =
            psubst σ (predotU (applyDot bs A)) ∧
          psubst σ (((commAt ρ first second made₁ made₂).result X (embed label C)).label made₂) =
            psubst σ (predotU (applyDot bs B)) := by
  have sameT : predotU t = t := predotU_of_guardFree t freeT
  have sameU : predotU u = u := predotU_of_guardFree u freeU
  have gpU : GroundPrincipal (predotU t) (predotU u) bs := by
    rw [sameT, sameU]
    exact gp
  obtain ⟨admitted, -, -, reads⟩ := comm_one_firing_uniform label t u channel A B bs gp gpU convention foA foB C
    first second made₁ made₂ readsFirst readsSecond distinct madeDistinct present₁ present₂ fresh₁ fresh₂
    (by rw [sameT, sameU]; exact glued) opensFreshly
  exact ⟨admitted, reads⟩

end Step

/-! ## Controls -/

namespace Controls

/-- The variables `y` and `w`. -/
def yv : Pattern := .fvar "y"
def wv : Pattern := .fvar "w"

/-- A reduct with a binder, `for(y <- @0)y`. -/
def reductY : Pattern := pFor yv demoChan yv
/-- Its alpha-variant, `for(w <- @0)w`. -/
def reductW : Pattern := pFor wv demoChan wv
/-- The same guard with its binder instantiated, `for(0 <- @0)0`. -/
def reductZero : Pattern := pFor pZero demoChan pZero

/-- The listener of the literal REFL, quoting the reduct as written. -/
def sourceListener : Pattern := pFor (tProc reductY) demoChan pZero
/-- The listener the hosting makes: its quote is packed from pre-dotted rows. -/
def madeListener : Pattern := pFor (tProc (predotU reductY)) demoChan pZero
/-- A partner quoting the alpha-variant. -/
def partner : Pattern := pFor (tProc reductW) demoChan pZero
/-- A partner quoting the instance. -/
def instantiatedPartner : Pattern := pFor (tProc reductZero) demoChan pZero

theorem madeListener_eq : madeListener = pFor (tProc (pFor yv demoChan (nQuote yv))) demoChan pZero := by
  decide +kernel

/-- As written, the partner keeps its pattern; uniformly, the quoted guard is pre-dotted. -/
theorem partner_representations :
    predot partner = pFor (tProc reductW) demoChan pZero ∧
      predotU partner = pFor (tProc (pFor wv demoChan (nQuote wv))) demoChan pZero := by
  constructor <;> decide +kernel

/-- A quote cannot be what it quotes. -/
theorem nQuote_ne_self (p : Pattern) : nQuote p ≠ p := by
  intro h
  have size := congrArg sizeOf h
  simp [nQuote] at size
  omega

theorem tProc_inj {a b : Pattern} (h : tProc a = tProc b) : a = b := by
  simpa [tProc] using h

/-- The made quote against the alpha-variant as written: no substitution equates them. -/
theorem dot_against_plain (σ : PSubst) :
    psubst σ (tProc (pFor yv demoChan (nQuote yv))) ≠ psubst σ (tProc (pFor wv demoChan wv)) := by
  intro h
  rw [psubst_tProc, psubst_tProc, psubst_pFor, psubst_pFor, psubst_nQuote] at h
  obtain ⟨same, -, dotted⟩ := pFor_inj (tProc_inj h)
  rw [same] at dotted
  exact nQuote_ne_self _ dotted

/-- The made quote against the instance: no substitution equates them. -/
theorem dot_against_instance (σ : PSubst) :
    psubst σ (tProc (pFor yv demoChan (nQuote yv))) ≠ psubst σ (tProc (pFor pZero demoChan pZero)) := by
  intro h
  rw [psubst_tProc, psubst_tProc, psubst_pFor, psubst_pFor, psubst_nQuote] at h
  obtain ⟨-, -, dotted⟩ := pFor_inj (tProc_inj h)
  exact absurd dotted (by simp [nQuote, pZero, psubst])

/-- The rows: the made listener at `0`, the partner as written at `1`. -/
def rowsWritten : ℕ → Pattern
  | 0 => madeListener
  | 1 => predot partner
  | _ => pZero

/-- The rows: the made listener at `0`, the partner represented uniformly at `1`. -/
def rowsUniform : ℕ → Pattern
  | 0 => madeListener
  | 1 => predotU partner
  | _ => pZero

/-- The rows: the made listener at `0`, the partner quoting the instance at `1`. -/
def rowsInstance : ℕ → Pattern
  | 0 => madeListener
  | 1 => instantiatedPartner
  | _ => pZero

/-- `y` read as `w`. -/
def yToW : PSubst := fun v => if v = "y" then some wv else none

/-- **Control (e), uniform**: the partner represented uniformly meets the made listener. -/
theorem uniform_partner_admitted :
    (RuleSyntax.step X ℕ E program).Admits (s := embed rowsUniform start) (commAt (renameBy rename) 0 1 2 3) :=
  comm_admits_inputs rowsUniform (tProc (pFor yv demoChan (nQuote yv))) (tProc (pFor wv demoChan (nQuote wv)))
    demoChan pZero pZero start 0 1 2 3
    (fun σ _ => congrArg (psubst σ) (by decide +kernel :
      rowsUniform 0 = pFor (tProc (pFor yv demoChan (nQuote yv))) demoChan pZero))
    (fun σ _ => congrArg (psubst σ) (by decide +kernel :
      rowsUniform 1 = pFor (tProc (pFor wv demoChan (nQuote wv))) demoChan pZero))
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (σ₀ := yToW) (fun _ member => absurd member List.not_mem_nil) (by decide +kernel)
    (fresh_at rowsUniform (by decide +kernel) (by decide +kernel))

/-- **Control (e), as written**: the partner kept as written misses the made listener, at every opening. -/
theorem as_written_partner_refused (ρ : PSubst) :
    ¬ (RuleSyntax.step X ℕ E program).Admits (s := embed rowsWritten start) (commAt ρ 0 1 2 3) := by
  intro admitted
  obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  obtain ⟨-, unify, -⟩ := comm_reads_inputs rowsWritten (tProc (pFor yv demoChan (nQuote yv))) (tProc reductW)
    demoChan demoChan pZero pZero start 0 1 2 3
    (fun σ _ => congrArg (psubst σ) (by decide +kernel :
      rowsWritten 0 = pFor (tProc (pFor yv demoChan (nQuote yv))) demoChan pZero))
    (fun σ _ => congrArg (psubst σ) (by decide +kernel : rowsWritten 1 = pFor (tProc reductW) demoChan pZero))
    (by decide) ρ solved
  exact dot_against_plain σ unify

/-- **Control (e), the source**: the literal source and the corrected relational semantics meet. -/
theorem source_partner_meets :
    ∃ bs, MeTTaCalculus.Corrected.Principal (tProc reductY) (tProc reductW) bs ∧
      MeTTaCalculus.ReflectionClosure.Step MeTTaCalculus.Corrected.Principal SC (par sourceListener partner)
        (par (applyDot bs pZero) (applyDot bs pZero)) ∧
      MeTTaCalculus.Corrected.Step MeTTaCalculus.Corrected.conventional (par sourceListener partner)
        (par (applyDot bs pZero) (applyDot bs pZero)) := by
  have found : (MeTTaCalculus.Corrected.unify (tProc reductY) (tProc reductW)).isSome = true := by
    decide +kernel
  obtain ⟨bs, unified⟩ := Option.isSome_iff_exists.mp found
  have principal := MeTTaCalculus.Corrected.unify_principal unified
  exact ⟨bs, principal, .comm _ _ _ _ _ bs principal, .comm _ _ _ _ _ bs principal
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

/-- **What does not hold (1)**: the corrected executable refuses every COMM whose pattern quotes a guard,
the alpha-variant and the instance alike. -/
theorem corrected_refuses_guard_quotes :
    MeTTaCalculus.Corrected.cstep (par sourceListener partner) = [] ∧
      MeTTaCalculus.Corrected.cstep (par sourceListener instantiatedPartner) = [] := by
  constructor <;> decide +kernel

/-- **What does not hold (2), the source**: the partner quoting the instance meets the literal source. -/
theorem instantiated_partner_meets_in_source :
    ∃ bs, MeTTaCalculus.Corrected.Principal (tProc reductY) (tProc reductZero) bs ∧
      MeTTaCalculus.ReflectionClosure.Step MeTTaCalculus.Corrected.Principal SC
        (par sourceListener instantiatedPartner) (par (applyDot bs pZero) (applyDot bs pZero)) ∧
      MeTTaCalculus.Corrected.Step MeTTaCalculus.Corrected.conventional (par sourceListener instantiatedPartner)
        (par (applyDot bs pZero) (applyDot bs pZero)) := by
  have found : (MeTTaCalculus.Corrected.unify (tProc reductY) (tProc reductZero)).isSome = true := by
    decide +kernel
  obtain ⟨bs, unified⟩ := Option.isSome_iff_exists.mp found
  have principal := MeTTaCalculus.Corrected.unify_principal unified
  exact ⟨bs, principal, .comm _ _ _ _ _ bs principal, .comm _ _ _ _ _ bs principal
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

/-- **What does not hold (2), the hosting**: the partner quoting the instance is its own representation in
both, and misses the made listener at every opening. -/
theorem instantiated_partner_refused :
    predot instantiatedPartner = instantiatedPartner ∧ predotU instantiatedPartner = instantiatedPartner ∧
      ∀ ρ : PSubst,
        ¬ (RuleSyntax.step X ℕ E program).Admits (s := embed rowsInstance start) (commAt ρ 0 1 2 3) := by
  refine ⟨by decide +kernel, by decide +kernel, fun ρ admitted => ?_⟩
  obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  obtain ⟨-, unify, -⟩ := comm_reads_inputs rowsInstance (tProc (pFor yv demoChan (nQuote yv)))
    (tProc reductZero) demoChan demoChan pZero pZero start 0 1 2 3
    (fun σ _ => congrArg (psubst σ) (by decide +kernel :
      rowsInstance 0 = pFor (tProc (pFor yv demoChan (nQuote yv))) demoChan pZero))
    (fun σ _ => congrArg (psubst σ) (by decide +kernel :
      rowsInstance 1 = pFor (tProc reductZero) demoChan pZero))
    (by decide) ρ solved
  exact dot_against_instance σ unify

/-- A shadowed binder, and its renaming. -/
def shadowed : Pattern := pFor (.fvar "x") demoChan (pFor (.fvar "x") demoChan (.fvar "x"))
def renamedApart : Pattern := pFor (.fvar "x") demoChan (pFor (.fvar "z") demoChan (.fvar "z"))

/-- **What does not hold (3)**: under shadowing, neither `predot` nor `predotU` preserves `BagEq`. -/
theorem shadowing_breaks_bagEq :
    BagEq shadowed renamedApart ∧ ¬ BagEq (predot shadowed) (predot renamedApart) ∧
      ¬ BagEq (predotU shadowed) (predotU renamedApart) := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold BagEq <;> decide +kernel

/-- **What does not hold (4)**: the corrected REFL quotes the closed form, which the representation fixes;
modulo the bag laws it is not the quote the hosting makes from the pre-dotted reduct. -/
theorem closed_quote_not_made_quote :
    predotU (canonicalBag reductY) = canonicalBag reductY ∧
      ¬ BagLaws (canonicalBag reductY) (predotU reductY) := by
  constructor <;> decide +kernel

/-- Packing: the components of `reductY | reductW`, in the other order, represent it modulo the bag laws;
dropping a copy does not. -/
theorem pack_examples :
    BagLaws (pPar ([reductW, reductY].map predotU)) (predotU (par reductY reductW)) ∧
      ¬ BagLaws (pPar ([reductY].map predotU)) (predotU (par reductY reductY)) := by
  constructor
  · exact bagLaws_pack _ (by decide +kernel)
  · decide +kernel

/-- A positive and a negative instance of the top-level statement. -/
theorem components_examples :
    (components (predotU (par reductY reductW))).Perm (components (predotU (par reductW reductY))) ∧
      ¬ (components (predotU (par reductY reductY))).Perm (components (predotU (par reductY reductW))) := by
  constructor
  · exact (perm_components_predotU_iff _ _).mpr (by decide +kernel)
  · rw [perm_components_predotU_iff]
    decide +kernel

/-- **The uniform COMM theorem applies**: on the manuscript's example `for((0) <- @0)0 | for(y <- @0)y`, whose
patterns are guard-free, the rows represented uniformly are the finite hosting's rows; the firing is admitted
and every solution reads the receiver's made row as the uniform representation of `@((0))`. -/
theorem example_uniform :
    (RuleSyntax.step X ℕ E program).Admits (s := embed FiniteProgram.Controls.rows start)
        (commAt (renameBy rename) 0 1 2 3) ∧
      ∀ σ : PSubst, patternAction.Models σ
          ((commAt (renameBy rename) 0 1 2 3).result X (embed FiniteProgram.Controls.rows start)).knowledge →
        psubst σ (((commAt (renameBy rename) 0 1 2 3).result X (embed FiniteProgram.Controls.rows start)).label 3) =
          psubst σ (predotU (applyDot Comm.Controls.unifier Comm.Controls.y)) := by
  obtain ⟨admitted, reads⟩ := comm_one_firing_uniform_of_guardFree FiniteProgram.Controls.rows
    Comm.Controls.zeroTerm Comm.Controls.y demoChan pZero Comm.Controls.y Comm.Controls.unifier
    Comm.Controls.unifier_groundPrincipal (by decide +kernel) (by decide +kernel)
    FiniteProgram.Controls.example_apart (by decide +kernel) (by decide +kernel) start 0 1 2 3
    (fun σ _ => congrArg (psubst σ) (by decide +kernel :
      FiniteProgram.Controls.rows 0 = predotU (pFor Comm.Controls.zeroTerm demoChan pZero)))
    (fun σ _ => congrArg (psubst σ) (by decide +kernel :
      FiniteProgram.Controls.rows 1 = predotU (pFor Comm.Controls.y demoChan Comm.Controls.y)))
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨fun v => if v = "y" then some Comm.Controls.zeroTerm else none, fun _ member => absurd member List.not_mem_nil,
      by decide +kernel⟩
    (fresh_at FiniteProgram.Controls.rows (by decide +kernel) (by decide +kernel))
  exact ⟨admitted, fun σ solved => (reads σ solved).2⟩

end Controls

#print axioms predotU_injective
#print axioms dotted_injective
#print axioms pvars_predotU
#print axioms components_predotU
#print axioms perm_components_predotU_iff
#print axioms bagLaws_predotU
#print axioms bagLaws_pack
#print axioms predotU_closeIn
#print axioms predotU_canonicalBag
#print axioms canonicalBag_not_made_quote
#print axioms Controls.pack_examples
#print axioms predotU_eq_predot_of_tame
#print axioms predotU_ground
#print axioms predotU_psubst
#print axioms dotted_reads_predotU
#print axioms comm_one_firing_uniform
#print axioms comm_one_firing_uniform_of_guardFree
#print axioms Controls.uniform_partner_admitted
#print axioms Controls.as_written_partner_refused
#print axioms Controls.source_partner_meets
#print axioms Controls.corrected_refuses_guard_quotes
#print axioms Controls.instantiated_partner_meets_in_source
#print axioms Controls.instantiated_partner_refused
#print axioms Controls.shadowing_breaks_bagEq
#print axioms Controls.closed_quote_not_made_quote
#print axioms Controls.components_examples
#print axioms Controls.example_uniform

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflUniform
