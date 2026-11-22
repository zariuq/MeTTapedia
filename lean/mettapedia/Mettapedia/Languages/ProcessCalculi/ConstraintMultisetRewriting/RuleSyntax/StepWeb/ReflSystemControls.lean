import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotientControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflNameTransportControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocatedControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocatedStepControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceControls
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedControls
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Adequacy

/-!
# Complete Controls Inventory (`P6`) and the Runtime-Binder-Packing Boundary (`P7`)

This leaf controls module completes the `P6` separation inventory and proves the `P7`
runtime-binder-packing boundary theorems without touching any core module:

## 1. Design controls `(a)`, `(d)`, `(e)` at the located name frame `QN`
* **`packing_order_observable_without_quotient` (`(a)`)**: cooling child rows in `[atomA, atomB]` vs
  `[atomB, atomA]` order builds syntactically distinct quotes (`cooled 0 [a, b] ≠ cooled 0 [b, a]`).
  At `Comm.X`, a partner quoting `cooled 0 [a, b]` admits `COMM` with the first listener and refuses
  `COMM` at every opening with the second; at `QN`, both quotes are `NameLaws`-equivalent and
  `located` admits `rootCommAt` on the swapped pair.
* **`non_ground_bag_pattern_control_QN` (`(d)` & sharpness of `groundBags`)**: on `located` at `QN`,
  `inputY = for(@(Y | A) <- @0)0` (`groundBags = false`) and `inputAB = for(@(A | B) <- @0)0`
  admit `rootCommAt`, while for **every** admission predicate `admit` (including `conventional` and
  `closing`), neither `BagStep admit` nor `CanonicalBagStep admit` steps `inputY | inputAB`.
* **`binder_reduct_partner_control_QN` (`(e)`)**: for the binder reduct `R = for(y <- @0)y`, the
  hosted made listener `for(@(predotU R) <- @0)0 @ Root` on `located` at `QN` **admits** `rootCommAt`
  against the uniformly represented alpha-variant `for(@(predotU (for(w <- @0)w)) <- @0)0 @ Root`
  and **refuses at every opening** `rootCommAt` against the as-written (`predot`) partner
  `for(@(for(w <- @0)w) <- @0)0 @ Root`.

## 2. Premise-contract runtime vs single-firing `located` showcase
* **`nested_reflection_premise_vs_hosted`**: pairs `Adequacy.nested_reflection_missed`
  (`stepViaPremiseContract` returns `[]` on `nestedOpenSource`) with `Corrected.Controls.corrected_nested`
  and `instance_nested_open_refl_N` (`located` at `QN` hosts the nested reflection to `CleanRepresents`
  and `SystemInvN`).

## 3. Sharpness controls for every `P5` hypothesis
* **`unbound_fvar_narrowed_by_rootHeat`** (dropping `HostedNode`): top-level `.fvar "x"` admits
  `rootHeatAt` at `QN`, narrowing `"x"` to `par`, whereas `.fvar "x"` has zero `BagStep` steps.
* **`unclean_child_spurious_closeRoot`** (dropping `CleanChildren`): a pre-existing `Done` token at
  `Child(Root, @0, 0)` lets `closeRootAt` step `@0?(0)` to `for(@0 <- @0)0`, whereas `@0?(0)` has
  zero `BagStep` steps.
* **`rogue_root_token_admits_heatChild`** (dropping `NoRootTokens`): a rogue `Pending(Root, Root)`
  token lets the child-only rule `heatChild` consume a `Root` row.
* **`cross_reflection_capture_control`** (dropping `BackwardReadyN.noCaptureRoot`): `@0?(0)`'s
  `Done` token closes a sibling open reflection `@0?(X)` via `closeRootAt`, instantiating `"X"` to
  `0` even though `@0?(X)` has zero `BagStep` steps.
* **`apart_dropped_admits_capturing_comm`** (dropping `Apart` in `Step1PrimeComm`): on
  `demoCommSource = for(a <- @0)a | for(0 <- @0)a`, `rootCommAt` at `QN` is admitted and produces
  `@0 | @0` (`demoCommCapture`), which `capture_not_conventional_step` refutes.
* **`polluted_equations_block_comm`** (dropping `FreeOnPats` in `source_step_forward_N`/`C`): a
  pre-existing constraint `(.fvar "y", atomA)` in `C.equations` blocks `rootCommAt` at every opening
  on `for((0) <- @0)0 | for(y <- @0)y @ Root`, even though `BagStep conventional` steps.
* **`open_reduct_separates_N_from_C`** (dropping `pvars R = []` under **C**): on a reduct with a
  bound variable (`R_bound = pPar [reductY, 0]`), Interface **N**'s listener and Interface **C**'s
  canonical listener are `NameLaws`-distinct, whereas on a reduct with only a free variable
  (`R_free = pPar [@0, a]`, fixed by `close`), both agree modulo `NameLaws`.
* **`conservativity_fails_with_reflect`** (dropping `NoReflectNode` in `conservativity_refl_free`):
  from `rootState` encoding `@0?(0)`, `located` admits `openRoot` into a state with a child row,
  which lies outside `Set.range (locate rootLoc)`.

## 4. `P7` Runtime-binder-packing boundary (proving what holds; claiming nothing unproved)
* **`p7_ground_comm_with_inner_binders` (Positive fragment)**: when `bs` is ground-valued
  (`GroundPrincipal t u bs`) and `Apart t A u B` holds (`∀ x ∈ keys, x ∉ binders A`),
  `dotted (pvars t) (predotU A)` already reads as `predotU (applyDot bs A)` modulo `NameLaws` even
  when `binders A ≠ []` (instantiated on `for(x <- @0) for(y <- @0)(x | y) | for(0 <- @0)0`).
* **`p7_dynamic_binder_double_dot_boundary` (Negative boundary 1 — crossing into inner pattern)**:
  when an outer variable `"P"` crosses into an inner pattern (`"P" ∈ binders A`,
  `A = for(@P <- @0)P`), static `dotted ["P"] (predotU A)` produces `@@0` while
  `predotU (applyDot [("P", 0)] A)` produces `@0`, separated modulo `NameLaws`.
* **`p7_quoted_binder_instantiation_boundary` (Negative boundary 2 — open binder at close)**:
  packing `reductY = for(y <- @0)y` at `closeRoot` without runtime binder packing meets an
  alpha-renamed partner (`Admits`) and refuses an instantiating partner (`¬ Admits` at every opening)
  on `located` at `QN`, whereas `Corrected.Step conventional` meets in the source.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem.Controls

open LogicOverTheStep.StepSpan (Succ)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect
  applyDot demoChan)
open MeTTaCalculus.Adequacy (stepViaPremiseContract)
open MeTTaCalculus.Adequacy.EngineControls (nested_reflection_missed)
open MeTTaOperationsComm (psubst pcomp psubst_comp psubst_none PSubst pvars psubst_of_pvars_nil
  psubst_pFor psubst_tProc psubst_nQuote psubst_pZero quoteOn dotted GroundPrincipal firstOrder
  applyDot_eq lookup_eq_none_of_keys)
open MeTTaCalculus.Corrected (BagEq BagStep CanonicalBagStep conventional listener close closeIn
  components components_closeIn binders Apart psize)
open FiniteProgram (predot predot_pFor commAt keys_of_apart comm_reads_inputs program
  GroundValued mem_keys_of_lookup firstBody secondBody)
open FiniteProgram.Controls (fresh_at rename)
open Comm (X E renameBy)
open OneFrame (embed)
open ReflQuotient (BagLaws bagCanon groundBags)
open MeTTaCalculus.Corrected.BagControls (atomA atomB)
open ReflNames (NameLaws nameAction QN QNE fresh_name nameLaws_of_eq bagLaws_of_nameLaws
  nameLaws_heads nameLaws_nQuote psubst_nameLaws_congr)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok located rootState locate heatChildN
  heatChild_admitted psubst_rootLoc psubst_atLoc_any psubst_pendingTok psubst_par locatedFrame_name)
open ReflPacking (cooled psubst_doneTok)
open ReflLocatedStep (psubst_childLoc res resConf solution_of_admitted info_known)
open ReflUniform (predotU dotted_reads_predotU)
open ReflUniform.Controls (yv wv reductY reductW reductZero instantiatedPartner)
open ReflCorrespondence (Clean openRootAt closeRootAt open_fresh_exists close_fresh_exists
  heat_fresh_exists openRoot_admitted closeRoot_admitted)

/-! ## Helper lemmas refuting `BagStep` and `CanonicalBagStep` on dead / non-matching terms -/

theorem no_bagStep_of_components_nil {admit : MeTTaCalculus.Corrected.Admission} :
    ∀ {P Q : Pattern}, BagStep admit P Q → components (close P) ≠ [] := by
  intro P Q step
  induction step with
  | comm _ _ _ _ _ _ _ _ =>
      rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par]
      simp [pFor, components]
  | parallel _ _ ih =>
      rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par, List.map_append,
        ← components_closeIn, ← components_closeIn]
      intro h; exact ih (List.append_eq_nil_iff.mp h).1
  | congruence before _ _ ih =>
      intro h
      have p := (show List.Perm _ _ from before).symm
      rw [h] at p
      exact ih (List.Perm.eq_nil p)
  | reflect _ _ _ =>
      simp [close, closeIn, pReflect, components]

theorem no_bagStep_of_single_nonRef {admit : MeTTaCalculus.Corrected.Admission} {c₀ : Pattern}
    (notRef : ∀ x s, c₀ ≠ .apply "MRef" [x, s]) :
    ∀ {P Q : Pattern}, BagStep admit P Q → components (close P) ≠ [c₀] := by
  intro P Q step
  induction step with
  | comm _ _ _ _ _ _ _ _ =>
      rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par]
      intro h; have len := congrArg List.length h; simp [pFor, components] at len
  | parallel _ _ ih =>
      rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par, List.map_append,
        ← components_closeIn, ← components_closeIn]
      intro h
      rcases List.append_eq_singleton_iff.mp h with ⟨srcNil, _⟩ | ⟨srcSingle, _⟩
      · exact no_bagStep_of_components_nil ‹_› srcNil
      · exact ih srcSingle
  | congruence before _ _ ih =>
      intro h
      have p := (show List.Perm _ _ from before).symm
      rw [h] at p
      exact ih (List.perm_singleton.mp p)
  | reflect x _ _ =>
      intro h
      simp only [close, pReflect, MeTTaCalculus.Corrected.closeIn_apply,
        show ¬ ("MRef" : String) = "MFor" from by decide, ↓reduceIte, List.map_cons, List.map_nil] at h
      change [Pattern.apply "MRef" [_, _]] = [c₀] at h
      simp only [List.cons.injEq, and_true] at h
      exact notRef _ _ h.symm

theorem no_bagStep_fvar {admit : MeTTaCalculus.Corrected.Admission} (v : String) (Q : Pattern) :
    ¬ BagStep admit (.fvar v) Q :=
  fun st => no_bagStep_of_single_nonRef (fun _ _ h => by cases h) st rfl

theorem no_bagStep_reflect_dead {admit : MeTTaCalculus.Corrected.Admission} {S : Pattern}
    (dead : ∀ U T : Pattern, close U = close S → ¬ BagStep admit U T) :
    ∀ {P Q : Pattern}, BagStep admit P Q →
      components (close P) ≠ [close (pReflect demoChan S)] := by
  intro P Q step
  induction step with
  | comm _ _ _ _ _ _ _ _ =>
      rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par]
      intro h; have len := congrArg List.length h; simp [pFor, components] at len
  | parallel _ _ ih =>
      rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par, List.map_append,
        ← components_closeIn, ← components_closeIn]
      intro h
      rcases List.append_eq_singleton_iff.mp h with ⟨srcNil, _⟩ | ⟨srcSingle, _⟩
      · exact no_bagStep_of_components_nil ‹_› srcNil
      · exact ih srcSingle
  | congruence before _ _ ih =>
      intro h
      have p := (show List.Perm _ _ from before).symm
      rw [h] at p
      exact ih (List.perm_singleton.mp p)
  | reflect x sub _ =>
      intro h
      simp only [close, pReflect, MeTTaCalculus.Corrected.closeIn_apply,
        show ¬ ("MRef" : String) = "MFor" from by decide, ↓reduceIte, List.map_cons, List.map_nil] at h
      change [Pattern.apply "MRef" [_, _]] = [Pattern.apply "MRef" [_, _]] at h
      simp only [List.cons.injEq, Pattern.apply.injEq, and_true] at h
      exact dead _ _ h.2.2 sub

theorem no_bagStep_reflect_zero (Q : Pattern) :
    ¬ BagStep conventional (pReflect demoChan pZero) Q := by
  refine fun st => no_bagStep_reflect_dead (fun U T eqC sub => ?_) st rfl
  have cNil : components (close U) = [] := by rw [eqC]; rfl
  exact no_bagStep_of_components_nil sub cNil

theorem no_bagStep_reflect_fvar (v : String) (Q : Pattern) :
    ¬ BagStep conventional (pReflect demoChan (.fvar v)) Q := by
  refine fun st => no_bagStep_reflect_dead (fun U T eqC sub => ?_) st rfl
  have cFv : components (close U) = [.fvar v] := by rw [eqC]; rfl
  exact no_bagStep_of_single_nonRef (fun _ _ h => by cases h) sub cFv

private theorem eq_atom_of_closeIn {env : List (List String)} {u : Pattern} {nm : String}
    (neB : nm ≠ "MBound") (neF : nm ≠ "MFor")
    (h : closeIn env u = .apply nm []) : u = .apply nm [] := by
  cases u with
  | bvar _ => simp [closeIn] at h
  | fvar x =>
      cases lk : MeTTaCalculus.Corrected.lookupBound env x <;>
        simp [closeIn, lk, MeTTaCalculus.Corrected.boundCode] at h
  | apply c args =>
      rw [MeTTaCalculus.Corrected.closeIn_apply] at h
      simp only [Pattern.apply.injEq] at h
      obtain ⟨rfl, argsEq⟩ := h
      rw [if_neg neF, List.map_eq_nil_iff] at argsEq
      subst argsEq; rfl
  | lambda _ _ => simp [closeIn] at h
  | multiLambda _ _ _ => simp [closeIn] at h
  | subst _ _ => simp [closeIn] at h
  | collection _ _ _ => simp [closeIn] at h

private theorem eq_tProc_par_atom_of_closeIn {env : List (List String)} {t : Pattern}
    {a0 : Pattern} {nm : String} (neB : nm ≠ "MBound") (neF : nm ≠ "MFor")
    (h : closeIn env t = tProc (par a0 (.apply nm []))) :
    ∃ x0 : Pattern, t = tProc (par x0 (.apply nm [])) := by
  cases t with
  | bvar _ => simp [closeIn, tProc] at h
  | fvar x =>
      cases lk : MeTTaCalculus.Corrected.lookupBound env x <;>
        simp [closeIn, lk, MeTTaCalculus.Corrected.boundCode, tProc] at h
  | apply c args =>
      rw [MeTTaCalculus.Corrected.closeIn_apply] at h
      simp only [tProc, Pattern.apply.injEq] at h
      obtain ⟨rfl, argsEq⟩ := h
      simp only [show ¬ ("MTermProc" : String) = "MFor" from by decide, ↓reduceIte] at argsEq
      match args, argsEq with
      | [], argsEq => simp at argsEq
      | _ :: _ :: _, argsEq => simp at argsEq
      | [inner], argsEq =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at argsEq
          cases inner with
          | bvar _ => simp [closeIn, par, pPar] at argsEq
          | fvar x =>
              cases lk : MeTTaCalculus.Corrected.lookupBound env x <;>
                simp [closeIn, lk, MeTTaCalculus.Corrected.boundCode, par, pPar] at argsEq
          | apply _ _ =>
              rw [MeTTaCalculus.Corrected.closeIn_apply] at argsEq
              simp [par, pPar] at argsEq
          | lambda _ _ => simp [closeIn, par, pPar] at argsEq
          | multiLambda _ _ _ => simp [closeIn, par, pPar] at argsEq
          | subst _ _ => simp [closeIn, par, pPar] at argsEq
          | collection ct elems rest =>
              simp only [closeIn, MeTTaCalculus.Corrected.closeList_eq_map, par, pPar,
                Pattern.collection.injEq] at argsEq
              obtain ⟨rfl, elEq, rfl⟩ := argsEq
              match elems, elEq with
              | [], elEq => simp at elEq
              | [_], elEq => simp at elEq
              | _ :: _ :: _ :: _, elEq => simp at elEq
              | [x0, y0], elEq =>
                  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at elEq
                  have yEq := eq_atom_of_closeIn neB neF elEq.2
                  subst yEq; exact ⟨x0, rfl⟩
  | lambda _ _ => simp [closeIn, tProc] at h
  | multiLambda _ _ _ => simp [closeIn, tProc] at h
  | subst _ _ => simp [closeIn, tProc] at h
  | collection _ _ _ => simp [closeIn, tProc] at h

private theorem bagStep_to_canonical_of_noRef {admit : MeTTaCalculus.Corrected.Admission} :
    ∀ {P Q : Pattern}, BagStep admit P Q →
      (∀ c ∈ components (close P), ∀ x s, c ≠ .apply "MRef" [x, s]) →
      CanonicalBagStep admit P Q := by
  intro P Q step
  induction step with
  | comm t u x A B bs pr adm => intro _; exact .comm t u x A B bs pr adm
  | parallel surrounding _ ih =>
      intro noRef
      refine .parallel surrounding (ih fun c cIn => noRef c ?_)
      rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par, List.map_append,
        ← components_closeIn]
      exact List.mem_append_left _ cIn
  | congruence before _ after ih =>
      intro noRef
      exact .congruence before (ih fun c cIn =>
        noRef c ((show List.Perm _ _ from before).symm.subset cIn)) after
  | @reflect x s _ _ _ =>
      intro noRef
      exact False.elim (noRef (close (pReflect x s))
        (by simp [close, closeIn, pReflect, components]) (closeIn [] x) (closeIn [] s)
        (by simp [close, pReflect, MeTTaCalculus.Corrected.closeIn_apply]))

private theorem no_canonicalBagStep_open_bag_pair {admit : MeTTaCalculus.Corrected.Admission} :
    ∀ {P Q : Pattern}, CanonicalBagStep admit P Q →
      (components (close P)).Perm
        [close ReflQuotient.Controls.inputY, close ReflQuotient.Controls.inputAB] → False := by
  have noEmpty : ∀ {P Q : Pattern}, CanonicalBagStep admit P Q → components (close P) ≠ [] := by
    intro P Q st; induction st with
    | comm _ _ _ _ _ _ _ _ =>
        rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par]; simp [pFor, components]
    | parallel _ _ ih =>
        rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par, List.map_append,
          ← components_closeIn, ← components_closeIn]
        exact fun h => ih (List.append_eq_nil_iff.mp h).1
    | congruence before _ _ ih =>
        exact fun h => ih (List.Perm.eq_nil (h ▸ (show List.Perm _ _ from before).symm))
    | reflect _ _ _ => simp [close, closeIn, pReflect, components]
  have noSingleNonRef : ∀ {c₀ : Pattern}, (∀ x s, c₀ ≠ .apply "MRef" [x, s]) →
      ∀ {P Q : Pattern}, CanonicalBagStep admit P Q → components (close P) ≠ [c₀] := by
    intro c₀ notR P Q st; induction st with
    | comm _ _ _ _ _ _ _ _ =>
        rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par]
        intro h; have l := congrArg List.length h; simp [pFor, components] at l
    | parallel _ _ ih =>
        rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par, List.map_append,
          ← components_closeIn, ← components_closeIn]
        intro h
        rcases List.append_eq_singleton_iff.mp h with ⟨sNil, _⟩ | ⟨sSng, _⟩
        · exact noEmpty ‹_› sNil
        · exact ih sSng
    | congruence before _ _ ih =>
        exact fun h => ih (List.perm_singleton.mp (h ▸ (show List.Perm _ _ from before).symm))
    | reflect x _ _ =>
        intro h
        simp only [close, pReflect, MeTTaCalculus.Corrected.closeIn_apply,
          show ¬ ("MRef" : String) = "MFor" from by decide, ↓reduceIte, List.map_cons, List.map_nil] at h
        change [Pattern.apply "MRef" [_, _]] = [c₀] at h
        simp only [List.cons.injEq, and_true] at h
        exact notR _ _ h.symm
  intro P Q step
  induction step with
  | comm t u x A B bs pr _ =>
      intro pm
      rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par, List.map_append,
        ← components_closeIn, ← components_closeIn] at pm
      have pF : ∀ q r s : Pattern, components (closeIn [] (pFor q r s)) = [close (pFor q r s)] := by
        intro q r s; simp [pFor, close, closeIn, components]
      rw [pF, pF, List.singleton_append] at pm
      have cY : close ReflQuotient.Controls.inputY =
          .apply "MFor" [tProc (par (MeTTaCalculus.Corrected.boundCode 0 0) atomA), demoChan, pZero] := by
        decide +kernel
      have cAB : close ReflQuotient.Controls.inputAB =
          .apply "MFor" [tProc (par atomA atomB), demoChan, pZero] := by
        decide +kernel
      rw [cY, cAB] at pm
      have closeFor : ∀ q r s : Pattern,
          close (pFor q r s) =
            .apply "MFor" [closeIn [pvars (closeIn [] q)] q, closeIn [] r, closeIn [pvars (closeIn [] q)] s] :=
        fun _ _ _ => rfl
      rw [closeFor, closeFor] at pm
      rcases List.perm_pair.mp pm with eqL | eqL
      · simp only [List.cons.injEq, and_true, true_and, Pattern.apply.injEq] at eqL
        obtain ⟨e1, e2⟩ := eqL
        obtain ⟨x0, eqT⟩ := eq_tProc_par_atom_of_closeIn (by decide) (by decide) e1.1
        obtain ⟨y0, eqU⟩ := eq_tProc_par_atom_of_closeIn (by decide) (by decide) e2.1
        have unif := pr.1; rw [eqT, eqU] at unif
        simp only [tProc, par, pPar, psubst, MeTTaCalculus.Corrected.psubstList_eq_map,
          List.map_cons, List.map_nil, Pattern.apply.injEq, Pattern.collection.injEq,
          List.cons.injEq, and_true, true_and] at unif
        have aEq : atomA = atomB := by simpa [atomA, atomB, psubst] using unif.2
        exact absurd aEq (by decide +kernel)
      · simp only [List.cons.injEq, and_true, true_and, Pattern.apply.injEq] at eqL
        obtain ⟨e1, e2⟩ := eqL
        obtain ⟨x0, eqT⟩ := eq_tProc_par_atom_of_closeIn (by decide) (by decide) e1.1
        obtain ⟨y0, eqU⟩ := eq_tProc_par_atom_of_closeIn (by decide) (by decide) e2.1
        have unif := pr.1; rw [eqT, eqU] at unif
        simp only [tProc, par, pPar, psubst, MeTTaCalculus.Corrected.psubstList_eq_map,
          List.map_cons, List.map_nil, Pattern.apply.injEq, Pattern.collection.injEq,
          List.cons.injEq, and_true, true_and] at unif
        have aEq : atomB = atomA := by simpa [atomA, atomB, psubst] using unif.2
        exact absurd aEq (by decide +kernel)
  | @parallel src _ surrounding s ih =>
      intro pm
      rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par, List.map_append,
        ← components_closeIn, ← components_closeIn] at pm
      change (components (close src) ++ components (close surrounding)).Perm _ at pm
      have lenSum := pm.length_eq
      simp only [List.length_append, List.length_cons, List.length_nil] at lenSum
      match hL : (components (close src)).length with
      | 0 => exact noEmpty s (List.length_eq_zero_iff.mp hL)
      | 1 =>
          obtain ⟨c₀, eqC₀⟩ := List.length_eq_one_iff.mp hL
          have memC₀ : c₀ ∈ [close ReflQuotient.Controls.inputY, close ReflQuotient.Controls.inputAB] :=
            pm.subset (by rw [eqC₀]; simp)
          refine noSingleNonRef (fun x_r s_r eqR => ?_) s eqC₀
          subst eqR
          simp only [List.mem_cons, List.not_mem_nil, or_false] at memC₀
          rcases memC₀ with eq | eq <;>
            simp [ReflQuotient.Controls.inputY, ReflQuotient.Controls.inputAB, close, pFor,
              MeTTaCalculus.Corrected.closeIn_apply] at eq
      | 2 =>
          have surNil : components (close surrounding) = [] :=
            List.length_eq_zero_iff.mp (by omega)
          rw [surNil, List.append_nil] at pm
          exact ih pm
      | n + 3 => omega
  | congruence before _ _ ih =>
      exact fun pm => ih ((show List.Perm _ _ from before).symm.trans pm)
  | reflect _ _ _ =>
      intro pm; have l := pm.length_eq; simp [close, closeIn, pReflect, components] at l

/-! ## 1. Design controls `(a)`, `(d)`, `(e)` at the located name frame `QN` -/

def cooledListenerAB : Pattern := pFor (tProc (cooled pZero [atomA, atomB])) demoChan pZero
def cooledListenerBA : Pattern := pFor (tProc (cooled pZero [atomB, atomA])) demoChan pZero

def rowsCooledSame : ℕ → Pattern
  | 0 => cooledListenerAB
  | 1 => cooledListenerAB
  | _ => pZero

def rowsCooledSwapped : ℕ → Pattern
  | 0 => cooledListenerBA
  | 1 => cooledListenerAB
  | _ => pZero

def locatedCooledSwapped : ℕ → Pattern
  | 0 => atLoc cooledListenerBA rootLoc
  | 1 => atLoc cooledListenerAB rootLoc
  | _ => pZero

/-- **Design control `(a)`**: without `QN`, cooling/packing order is observable:
`cooled 0 [A, B] ≠ cooled 0 [B, A]`; at `Comm.X`, `cooledListenerAB` communicates with `[A, B]`
order and refuses `[B, A]` order at every opening, while at `QN` both orders are `NameLaws`-equal
and `located` admits `rootCommAt` on the swapped pair. -/
theorem packing_order_observable_without_quotient :
    cooled pZero [atomA, atomB] ≠ cooled pZero [atomB, atomA] ∧
    (RuleSyntax.step X ℕ E program).Admits
      (s := embed rowsCooledSame Comm.Controls.start) (commAt (renameBy rename) 0 1 2 3) ∧
    (∀ ρ : PSubst, ¬ (RuleSyntax.step X ℕ E program).Admits
      (s := embed rowsCooledSwapped Comm.Controls.start) (commAt ρ 0 1 2 3)) ∧
    NameLaws (tProc (cooled pZero [atomB, atomA])) (tProc (cooled pZero [atomA, atomB])) ∧
    ∃ ρ : PSubst, (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed locatedCooledSwapped Comm.Controls.start) (rootCommAt ρ 0 1 2 3) := by
  refine ⟨by decide +kernel, ?_, fun ρ adm => ?_, by decide +kernel, ?_⟩
  · exact FiniteProgram.comm_admits_inputs rowsCooledSame
      (tProc (cooled pZero [atomA, atomB])) (tProc (cooled pZero [atomA, atomB]))
      demoChan pZero pZero Comm.Controls.start 0 1 2 3
      (fun _ _ => rfl) (fun _ _ => rfl) (by decide) (by decide)
      (by simp [Comm.Controls.start]) (by simp [Comm.Controls.start])
      (by simp [Comm.Controls.start]) (by simp [Comm.Controls.start])
      (σ₀ := fun _ => none) (fun _ m => absurd m List.not_mem_nil) rfl
      (fresh_at rowsCooledSame (by decide +kernel) (by decide +kernel))
  · obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp adm).2.2.2.1
    obtain ⟨-, pats, -⟩ := comm_reads_inputs rowsCooledSwapped
      (tProc (cooled pZero [atomB, atomA])) (tProc (cooled pZero [atomA, atomB]))
      demoChan demoChan pZero pZero Comm.Controls.start 0 1 2 3
      (fun _ _ => rfl) (fun _ _ => rfl) (by decide) ρ solved
    rw [psubst_of_pvars_nil σ _ (by decide +kernel),
      psubst_of_pvars_nil σ _ (by decide +kernel)] at pats
    exact absurd pats (by decide +kernel)
  · obtain ⟨ρ, fr⟩ := rootComm_fresh_exists locatedCooledSwapped Comm.Controls.start 0 1 2 3
    exact ⟨ρ, (rootComm_ground_mixed locatedCooledSwapped Comm.Controls.start
      (tProc (cooled pZero [atomB, atomA])) (tProc (cooled pZero [atomA, atomB]))
      demoChan pZero pZero (by decide +kernel) (by decide +kernel) (by decide +kernel)
      0 1 2 3 (fun _ _ => NameLaws.refl _) (fun _ _ => NameLaws.refl _) (by decide) (by decide)
      (by simp [Comm.Controls.start]) (by simp [Comm.Controls.start])
      (by simp [Comm.Controls.start]) (by simp [Comm.Controls.start])
      (σ₀ := fun _ => none) (fun _ m => absurd m List.not_mem_nil) fr).1⟩

def locatedOpenBagRows : ℕ → Pattern
  | 0 => atLoc ReflQuotient.Controls.inputY rootLoc
  | 1 => atLoc ReflQuotient.Controls.inputAB rootLoc
  | _ => pZero

/-- **Design control `(d)` & sharpness of `groundBags` on `located` at `QN`**:
`inputY = for(@(Y | A) <- @0)0` (`groundBags = false`) and `inputAB = for(@(A | B) <- @0)0`
admit `rootCommAt` at `QN` (matching `Y ↦ B` modulo `BagLaws` inside `@(...)`), while for **every**
admission predicate `admit`, neither `BagStep admit` nor `CanonicalBagStep admit` steps
`inputY | inputAB`. -/
theorem non_ground_bag_pattern_control_QN :
    groundBags ReflQuotient.Controls.patY = false ∧
    (∃ ρ : PSubst, (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed locatedOpenBagRows Comm.Controls.start) (rootCommAt ρ 0 1 2 3)) ∧
    ∀ (admit : MeTTaCalculus.Corrected.Admission) (Q : Pattern),
      ¬ BagStep admit (par ReflQuotient.Controls.inputY ReflQuotient.Controls.inputAB) Q ∧
      ¬ CanonicalBagStep admit (par ReflQuotient.Controls.inputY ReflQuotient.Controls.inputAB) Q := by
  obtain ⟨ρ, fr⟩ := rootComm_fresh_exists locatedOpenBagRows Comm.Controls.start 0 1 2 3
  have adm := rootComm_admitted_mixed locatedOpenBagRows Comm.Controls.start
    ReflQuotient.Controls.patY ReflQuotient.Controls.patAB demoChan pZero pZero 0 1 2 3
    (fun _ _ => NameLaws.refl _) (fun _ _ => NameLaws.refl _) (by decide) (by decide)
    (by simp [Comm.Controls.start]) (by simp [Comm.Controls.start])
    (by simp [Comm.Controls.start]) (by simp [Comm.Controls.start])
    (σ₀ := ReflQuotient.Controls.yToB) (fun _ m => absurd m List.not_mem_nil)
    (by decide +kernel) fr
  refine ⟨by decide +kernel, ⟨ρ, adm⟩, fun admit Q => ⟨fun bSt => ?_, fun cSt => ?_⟩⟩
  · have cSt := bagStep_to_canonical_of_noRef bSt fun c cIn x s eqR => by
      subst eqR
      rw [close, components_closeIn, MeTTaCalculus.Corrected.components_par, List.map_append] at cIn
      have pF : ∀ q r u : Pattern,
          (components (pFor q r u)).map (closeIn []) = [close (pFor q r u)] := by
        intro q r u; simp [pFor, close, components]
      rw [ReflQuotient.Controls.inputY, ReflQuotient.Controls.inputAB, pF, pF] at cIn
      simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false, close, pFor,
        MeTTaCalculus.Corrected.closeIn_apply] at cIn
      rcases cIn with eq | eq <;> simp at eq
    exact no_canonicalBagStep_open_bag_pair cSt (List.Perm.refl _)
  · exact no_canonicalBagStep_open_bag_pair cSt (List.Perm.refl _)

def locatedBinderUniformRows : ℕ → Pattern
  | 0 => atLoc (predotU (pFor (tProc reductY) demoChan pZero)) rootLoc
  | 1 => atLoc (predotU (pFor (tProc reductW) demoChan pZero)) rootLoc
  | _ => pZero

def locatedBinderWrittenRows : ℕ → Pattern
  | 0 => atLoc (predotU (pFor (tProc reductY) demoChan pZero)) rootLoc
  | 1 => atLoc (predot (pFor (tProc reductW) demoChan pZero)) rootLoc
  | _ => pZero

/-- **Design control `(e)` on `located` at `QN`**: for the binder reduct `R = for(y <- @0)y`,
`located`'s made listener `for(@(predotU R) <- @0)0 @ Root` **admits** `rootCommAt` at `QN`
against the uniformly represented alpha-variant `predotU (for(@(for(w <- @0)w) <- @0)0) @ Root`
and **refuses at every opening** `rootCommAt` against the as-written (`predot`) partner
`predot (for(@(for(w <- @0)w) <- @0)0) @ Root`. -/
theorem binder_reduct_partner_control_QN :
    (∃ ρ : PSubst, (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed locatedBinderUniformRows Comm.Controls.start) (rootCommAt ρ 0 1 2 3)) ∧
    (∀ ρ : PSubst, ¬ (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed locatedBinderWrittenRows Comm.Controls.start) (rootCommAt ρ 0 1 2 3)) := by
  obtain ⟨ρ, fr⟩ := rootComm_fresh_exists locatedBinderUniformRows Comm.Controls.start 0 1 2 3
  have admU := rootComm_admitted_mixed locatedBinderUniformRows Comm.Controls.start
    (tProc (predotU reductY)) (tProc (predotU reductW)) demoChan pZero pZero 0 1 2 3
    (fun _ _ => NameLaws.refl _) (fun _ _ => NameLaws.refl _) (by decide) (by decide)
    (by simp [Comm.Controls.start]) (by simp [Comm.Controls.start])
    (by simp [Comm.Controls.start]) (by simp [Comm.Controls.start])
    (σ₀ := ReflUniform.Controls.yToW) (fun _ m => absurd m List.not_mem_nil)
    (by decide +kernel) fr
  refine ⟨⟨ρ, admU⟩, fun ρ' admW => ?_⟩
  obtain ⟨σ, solved⟩ := solution_of_admitted admW
  have r0 : ∀ τ : PSubst, nameAction.Models τ Comm.Controls.start.equations →
      NameLaws (psubst τ (locatedBinderWrittenRows 0))
        (psubst τ (atLoc (pFor (tProc (pFor yv demoChan (nQuote yv))) demoChan pZero) rootLoc)) :=
    fun τ _ => nameLaws_of_eq (congrArg (psubst τ) (by decide +kernel))
  have r1 : ∀ τ : PSubst, nameAction.Models τ Comm.Controls.start.equations →
      NameLaws (psubst τ (locatedBinderWrittenRows 1))
        (psubst τ (atLoc (pFor (tProc reductW) demoChan pZero) rootLoc)) :=
    fun τ _ => nameLaws_of_eq (congrArg (psubst τ) (by decide +kernel))
  obtain ⟨-, unify, -⟩ := rootComm_reads_raw locatedBinderWrittenRows Comm.Controls.start
    (tProc (pFor yv demoChan (nQuote yv))) (tProc reductW) demoChan demoChan pZero pZero
    0 1 2 3 r0 r1 (by decide) ρ' solved
  have bag := bagLaws_of_nameLaws unify
  rw [psubst_tProc, psubst_tProc] at bag
  have inner := ReflCorrespondence.Controls.bagLaws_of_tProc bag
  simp only [reductW, yv, wv, psubst_pFor, psubst_nQuote] at inner
  have patEq : BagLaws (psubst σ (.fvar "y")) (psubst σ (.fvar "w")) := by
    rw [ReflQuotient.bagLaws_iff] at inner ⊢
    simp [pFor, ReflQuotient.bagCanon_apply] at inner; exact inner.1
  have bodyEq : BagLaws (nQuote (psubst σ (.fvar "y"))) (psubst σ (.fvar "w")) :=
    ReflCorrespondence.Controls.bagLaws_pFor_body inner
  have cycle : BagLaws (nQuote (psubst σ (.fvar "w"))) (psubst σ (.fvar "w")) :=
    (ReflQuotient.bagLaws_quote patEq.symm).trans bodyEq
  have canonSz : BagLaws (nQuote (bagCanon (psubst σ (.fvar "w")))) (bagCanon (psubst σ (.fvar "w"))) :=
    (ReflQuotient.bagLaws_quote (ReflQuotient.bagLaws_bagCanon _).symm).trans
      (cycle.trans (ReflQuotient.bagLaws_bagCanon _))
  rw [ReflQuotient.bagLaws_iff] at canonSz
  unfold nQuote at canonSz
  rw [ReflQuotient.bagCanon_apply] at canonSz
  simp only [List.map_cons, List.map_nil] at canonSz
  have bad := congrArg psize canonSz
  simp [psize, MeTTaCalculus.Corrected.psizeList] at bad

/-! ## 2. Showcase bridge: premise-contract runtime vs hosted `located` program -/

/-- **Nested reflection showcase bridge**: both `Corrected.Controls.nestedSource` and its
alpha-renamed counterpart `nestedOpenSource` (`@0?(@0?(for(a1 <- @0)a1 | for(0 <- @0)a))`) are
**missed** (`= []`) by `stepViaPremiseContract`, stepped by `Corrected.cstep`, and **hosted** by
`RuleSyntax.step QN ℕ QNE located` (`instance_nested_open_refl_N`). -/
theorem nested_reflection_premise_vs_hosted :
    stepViaPremiseContract MeTTaCalculus.Corrected.Controls.nestedSource = [] ∧
    stepViaPremiseContract nestedOpenSource = [] ∧
    MeTTaCalculus.Corrected.cstep nestedOpenSource ≠ [] ∧
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ),
      ReflCorrespondence.LocatedRun (encodeLabel nestedOpenSource) encodeConf label' C' ∧
      CleanRepresents label' C' nestedOpenTargetN ∧
      SystemInvN label' C' nestedOpenTargetN ∧
      BagStep conventional nestedOpenSource nestedOpenTargetN :=
  ⟨nested_reflection_missed.1,
   by decide +kernel,
   by decide +kernel,
   instance_nested_open_refl_N.2.2⟩

/-! ## 3. Sharpness controls for every `P5` hypothesis -/

/-- **Sharpness of `HostedNode` (`H1`)**: top-level unbound `.fvar "x"` (`¬ HostedNode (.fvar "x")`)
admits `rootHeatAt` at `QN` (narrowing `"x"` to `par`), whereas `.fvar "x"` has zero `BagStep`
transitions and is not `BagEq` to any 2-branch `par` of fresh variables. -/
theorem unbound_fvar_narrowed_by_rootHeat :
    ¬ HostedNode (.fvar "x") ∧
    (∃ ρ : PSubst, (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed (encodeLabel (.fvar "x")) encodeConf) (rootHeatAt ρ 0 1 2)) ∧
    (∀ Q : Pattern, ¬ BagStep conventional (.fvar "x") Q) ∧
    ¬ BagEq (.fvar "x") (par (.fvar "a") (.fvar "b")) := by
  refine ⟨fun h => by
      generalize eq : (Pattern.fvar "x") = P at h
      cases h <;> simp [pZero, nQuote, par, pPar, pFor, pReflect] at eq,
    ?_, no_bagStep_fvar "x", by unfold BagEq; decide +kernel⟩
  obtain ⟨ρ, fr⟩ := rootHeat_fresh_exists (encodeLabel (.fvar "x")) encodeConf 0 1 2
  let σ₀ : PSubst := fun v => if v = "x" then some (par pZero pZero) else none
  have pair₀ : NameLaws (psubst σ₀ ((encodeLabel (.fvar "x")) 0))
      (atLoc (par pZero pZero) rootLoc) := by decide +kernel
  exact ⟨ρ, rootHeat_admitted (encodeLabel (.fvar "x")) encodeConf 0 1 2
    (by simp [encodeConf]) (by decide) (by simp [encodeConf]) (by simp [encodeConf])
    (fun _ m => absurd m List.not_mem_nil) pair₀ fr⟩

def uncleanChildRows : ℕ → Pattern
  | 0 => atLoc (pReflect demoChan pZero) rootLoc
  | 1 => doneTok (childLoc rootLoc demoChan pZero) rootLoc pZero
  | _ => pZero

def uncleanChildConf : Configuration Pattern ℕ := ⟨[], {0, 1}⟩

/-- **Sharpness of `CleanChildren` (`H2`)**: with a pre-existing rogue `Done` token at
`Child(Root, @0, 0)` (`¬ CleanChildren`), `closeRootAt` is admitted on `@0?(0)` and produces a
listener `for(@0 <- @0)0 @ Root`, even though `@0?(0)` has zero `BagStep` steps and is not `BagEq`
to `for(@0 <- @0)0`. -/
theorem unclean_child_spurious_closeRoot :
    ¬ CleanChildren uncleanChildRows uncleanChildConf ∧
    (∃ ρ : PSubst, (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed uncleanChildRows uncleanChildConf) (closeRootAt ρ 0 1 2)) ∧
    (∀ Q : Pattern, ¬ BagStep conventional (pReflect demoChan pZero) Q) ∧
    ¬ BagEq (pReflect demoChan pZero) (pFor (tProc pZero) demoChan pZero) := by
  refine ⟨fun cl => ?_, ?_, no_bagStep_reflect_zero, by unfold BagEq; decide +kernel⟩
  · have h := cl rootLoc demoChan pZero IsLocSpine.root le_rfl 1 (by simp [uncleanChildConf])
      (fun _ => none) (fun _ m => absurd m List.not_mem_nil)
    exact h.2.1 rootLoc pZero (NameLaws.refl _)
  · obtain ⟨ρ, fr⟩ := close_fresh_exists uncleanChildRows uncleanChildConf 0 1 2
    refine ⟨ρ, closeRoot_admitted uncleanChildRows uncleanChildConf demoChan pZero pZero 0 1 2
      (fun _ _ => NameLaws.refl _) (fun _ _ => NameLaws.refl _) ?_ (by decide)
      ⟨by simp [uncleanChildConf], by simp [uncleanChildConf]⟩ (by simp [uncleanChildConf])
      (σ₀ := fun _ => none) (fun _ m => absurd m List.not_mem_nil) fr⟩
    intro o oIn σ _ y sm
    have oC : o = 0 ∨ o = 1 := by simpa [uncleanChildConf] using oIn
    rcases oC with rfl | rfl
    · simp only [uncleanChildRows, psubst_atLoc_any, psubst_rootLoc] at sm
      exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp sm).2.symm
    · simp only [uncleanChildRows, psubst_doneTok] at sm
      exact absurd (nameLaws_heads sm) (by decide)

def rogueRootTokRows : ℕ → Pattern
  | 0 => atLoc (par pZero pZero) rootLoc
  | 1 => pendingTok rootLoc rootLoc
  | _ => pZero

def rogueRootTokConf : Configuration Pattern ℕ := ⟨[], {0, 1}⟩

/-- **Sharpness of `NoRootTokens` (`H3`)**: if `Pending(Root, Root)` is present (`¬ NoRootTokens`),
the child-only rule `heatChildN` fires directly on a `Root` row `0`, consuming it. -/
theorem rogue_root_token_admits_heatChild :
    ¬ NoRootTokens rogueRootTokRows rogueRootTokConf ∧
    ∃ ρ : PSubst, (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed rogueRootTokRows rogueRootTokConf) (heatChildN ρ 0 1 2 3) := by
  refine ⟨fun nTok => (nTok 1 (by simp [rogueRootTokConf]) (fun _ => none)
    (fun _ m => absurd m List.not_mem_nil)).1 rootLoc (NameLaws.refl _), ?_⟩
  obtain ⟨ρ, fr⟩ := heat_fresh_exists rogueRootTokRows rogueRootTokConf 0 1 2 3
  exact ⟨ρ, heatChild_admitted rogueRootTokRows rogueRootTokConf 0 1 2 3
    (by simp [rogueRootTokConf]) (by simp [rogueRootTokConf]) (by decide) (by decide)
    (by simp [rogueRootTokConf]) (by simp [rogueRootTokConf])
    (σ₀ := fun _ => none) (a := pZero) (b := pZero) (l := rootLoc) (m := rootLoc)
    (fun _ m => absurd m List.not_mem_nil) (NameLaws.refl _) (NameLaws.refl _) fr⟩

def crossCaptureRows : ℕ → Pattern
  | 0 => atLoc (pReflect demoChan pZero) rootLoc
  | 1 => atLoc (pReflect demoChan (.fvar "X")) rootLoc
  | 2 => doneTok (childLoc rootLoc demoChan pZero) rootLoc pZero
  | _ => pZero

def crossCaptureConf : Configuration Pattern ℕ := ⟨[], {0, 1, 2}⟩

/-- **Sharpness of `BackwardReadyN.noCaptureRoot` (`H4`)**: when `@0?(0)`'s child reaches
`Done(Child(Root, @0, 0), Root, 0)` at `2`, a sibling open reflection `1 : @0?(X)` (`X` free)
admits `closeRootAt ρ 1 2 3` at `QN`, closing `1` by instantiating `"X" = 0` even though `@0?(X)`
has zero `BagStep` transitions! -/
theorem cross_reflection_capture_control :
    (∃ ρ : PSubst, (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed crossCaptureRows crossCaptureConf) (closeRootAt ρ 1 2 3)) ∧
    ∀ Q : Pattern, ¬ BagStep conventional (pReflect demoChan (.fvar "X")) Q := by
  obtain ⟨ρ, fr⟩ := close_fresh_exists crossCaptureRows crossCaptureConf 1 2 3
  let σX : PSubst := fun v => if v = "X" then some pZero else none
  have r1 : NameLaws (psubst σX (crossCaptureRows 1))
      (psubst σX (atLoc (pReflect demoChan pZero) rootLoc)) := by decide +kernel
  -- Construct admission directly via `closeRoot_admitted`? Note `closeRoot_admitted` asks `readsRefl`
  -- at ALL solutions; here `σX` solves `1` against `2`'s child `0`, so use `ReflLocatedStep.closeRoot_admitted_at`
  -- or prove `Admits` directly via `admits_iff`!
  refine ⟨⟨ρ, ?_⟩, no_bagStep_reflect_fvar "X"⟩
  have h1 : psubst σX (crossCaptureRows 1) = atLoc (pReflect demoChan pZero) rootLoc := by decide +kernel
  have h2 : psubst σX (crossCaptureRows 2) = doneTok (childLoc rootLoc demoChan pZero) rootLoc pZero := by
    decide +kernel
  let hRule : PSubst := fun v =>
    if v = "X" then some demoChan else if v = "P" then some pZero else if v = "C" then some pZero else none
  obtain ⟨w, solvedW, _, _⟩ := Comm.information_amalgamates_matched (Y := QN)
    (s := embed crossCaptureRows crossCaptureConf) (closeRootAt ρ 1 2 3) fr (b := PUnit.unit) σX hRule
    (fun _ m => absurd m List.not_mem_nil)
    (fun _ m => absurd m List.not_mem_nil)
    (fun o m => by
      have m' : o = 1 ∨ o = 2 := by simpa [closeRootAt] using m
      rcases m' with rfl | rfl <;> simp [embed, crossCaptureConf])
    (fun o m => by simp [closeRootAt] at m)
    (fun q m => by
      have m' : q = (atLoc (pReflect FiniteProgram.channelUnknown ReflLocated.reflP) rootLoc, 1) ∨
          q = (doneTok (childLoc rootLoc FiniteProgram.channelUnknown ReflLocated.reflP) rootLoc ReflLocated.accC, 2) := by
        simpa [closeRootAt, ReflLocated.closeRoot] using m
      rcases m' with rfl | rfl
      · show NameLaws (psubst hRule (atLoc (pReflect FiniteProgram.channelUnknown ReflLocated.reflP) rootLoc))
            (psubst σX (crossCaptureRows 1))
        rw [h1]; decide +kernel
      · show NameLaws (psubst hRule (doneTok (childLoc rootLoc FiniteProgram.channelUnknown ReflLocated.reflP) rootLoc ReflLocated.accC))
            (psubst σX (crossCaptureRows 2))
        rw [h2]; decide +kernel)
    (fun _ m => absurd m List.not_mem_nil)
  refine (RuleSyntax.admits_iff _).mpr ⟨fr,
    ⟨by show [1, 2].Nodup; decide, by show [3].Nodup; decide, rfl, rfl, rfl, rfl⟩,
    ⟨fun o m => by
       simp only [closeRootAt, Selection.commit, List.toFinset_cons, List.toFinset_nil,
         Finset.insert_empty, Finset.mem_insert, Finset.mem_singleton] at m
       rcases m with rfl | rfl <;> simp [embed, crossCaptureConf],
     fun o m => by simp [closeRootAt, Selection.commit] at m,
     by simp [closeRootAt, Selection.commit],
     by rw [Finset.disjoint_left]; intro o m
        simp only [closeRootAt, Selection.commit, List.toFinset_cons, List.toFinset_nil,
          Finset.insert_empty, Finset.mem_singleton] at m
        subst m; simp [embed, crossCaptureConf],
     fun _ m => by simp [Selection.commit] at m⟩,
    ⟨PUnit.unit, w, solvedW⟩, ?_, fun q m => by simp [Firing.collectOpened, closeRootAt, ReflLocated.closeRoot] at m⟩
  intro c cMem _ τ sol
  have only : ((closeRootAt ρ 1 2 3).opened QN).checks =
      [.predicate .none (psubst ρ (atLoc ReflLocated.anyY
        (childLoc rootLoc FiniteProgram.channelUnknown ReflLocated.reflP)))] := rfl
  rw [only, List.mem_singleton] at cMem
  subst cMem
  intro o oPres sm
  rw [OneFrame.row_eq] at sm
  have zD : (doneTok (childLoc rootLoc FiniteProgram.channelUnknown ReflLocated.reflP) rootLoc ReflLocated.accC, 2) ∈
      (closeRootAt ρ 1 2 3).rule.body.take.zip (closeRootAt ρ 1 2 3).selection.taken := by
    simp [closeRootAt, ReflLocated.closeRoot]
  have rD := ReflLocatedStep.take_reads (closeRootAt ρ 1 2 3) sol zD
  have d2 : psubst τ (crossCaptureRows 2) = doneTok (childLoc rootLoc demoChan pZero) rootLoc pZero :=
    psubst_of_pvars_nil τ _ (by decide +kernel)
  rw [d2, psubst_doneTok] at rD
  have chLoc := (ReflPacking.nameLaws_doneTok_iff.mp rD).1
  have oC : o = 0 ∨ o = 1 ∨ o = 2 := by simpa [embed, crossCaptureConf, or_assoc] using oPres
  rcases oC with rfl | rfl | rfl
  · simp only [embed, crossCaptureRows, psubst_atLoc_any] at sm
    have eqR := ((locatedFrame_name.atLoc_iff _ _ _ _).mp sm).2.symm.trans chLoc
    rw [psubst_rootLoc] at eqR
    exact not_nameLaws_childLoc_rootLoc _ _ _ eqR.symm
  · simp only [embed, crossCaptureRows, psubst_atLoc_any] at sm
    have eqR := ((locatedFrame_name.atLoc_iff _ _ _ _).mp sm).2.symm.trans chLoc
    rw [psubst_rootLoc] at eqR
    exact not_nameLaws_childLoc_rootLoc _ _ _ eqR.symm
  · simp only [embed, crossCaptureRows] at sm
    change NameLaws (psubst τ (atLoc _ _)) (psubst τ (doneTok _ _ _)) at sm
    rw [psubst_atLoc_any, psubst_doneTok] at sm
    exact absurd (nameLaws_heads sm) (by decide)

def capturingCommRows : ℕ → Pattern
  | 0 => atLoc (predotU (pFor (.fvar "a") demoChan (.fvar "a"))) rootLoc
  | 1 => atLoc (predotU (pFor pZero demoChan (.fvar "a"))) rootLoc
  | _ => pZero

/-- **Sharpness of `Apart` (`H6`)**: on `demoCommSource = for(a <- @0)a | for(0 <- @0)a` (where
`"a"` occurs both as pattern binder of `0` and free in `1`'s continuation, violating `Apart`),
`rootCommAt` at `QN` IS admitted and forces row `1`'s free `"a"` to read as `pZero` (`0`) at every
solution (`made₂` reads as `0 @ Root` instead of `a @ Root`), whereas `Corrected.cstep` steps
`demoCommSource` exclusively to `[par (@0) a]` (`Corrected.Controls.corrected_canary`) and
`par (@0) 0` is not `BagEq` to `par (@0) a`! -/
theorem apart_dropped_admits_capturing_comm :
    ¬ Apart (.fvar "a") (.fvar "a") pZero (.fvar "a") ∧
    (∃ ρ : PSubst, (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed capturingCommRows Comm.Controls.start) (rootCommAt ρ 0 1 2 3) ∧
      ∀ σ : PSubst, nameAction.Models σ
          (res capturingCommRows Comm.Controls.start (rootCommAt ρ 0 1 2 3)).knowledge →
        NameLaws (psubst σ ((res capturingCommRows Comm.Controls.start (rootCommAt ρ 0 1 2 3)).label 2))
          (atLoc (nQuote pZero) rootLoc) ∧
        NameLaws (psubst σ ((res capturingCommRows Comm.Controls.start (rootCommAt ρ 0 1 2 3)).label 3))
          (atLoc pZero rootLoc)) ∧
    MeTTaCalculus.Corrected.cstep MeTTaCalculus.demoCommSource =
      [par (nQuote pZero) (.fvar "a")] ∧
    ¬ BagEq (par (nQuote pZero) pZero) (par (nQuote pZero) (.fvar "a")) ∧
    ¬ MeTTaCalculus.Corrected.Step conventional
        MeTTaCalculus.demoCommSource MeTTaCalculus.demoCommCapture := by
  refine ⟨fun ⟨_, hOut, _, _, _⟩ => hOut "a" (by decide +kernel) (by decide +kernel), ?_,
    MeTTaCalculus.Corrected.Controls.corrected_canary,
    by unfold BagEq; decide +kernel,
    MeTTaCalculus.Corrected.Controls.capture_not_conventional_step⟩
  obtain ⟨ρ, fr⟩ := rootComm_fresh_exists capturingCommRows Comm.Controls.start 0 1 2 3
  let σA : PSubst := fun v => if v = "a" then some pZero else none
  have r0 : ∀ τ : PSubst, nameAction.Models τ Comm.Controls.start.equations →
      NameLaws (psubst τ (capturingCommRows 0))
        (psubst τ (atLoc (pFor (.fvar "a") demoChan (nQuote (.fvar "a"))) rootLoc)) :=
    fun τ _ => NameLaws.refl _
  have r1 : ∀ τ : PSubst, nameAction.Models τ Comm.Controls.start.equations →
      NameLaws (psubst τ (capturingCommRows 1))
        (psubst τ (atLoc (pFor pZero demoChan (.fvar "a")) rootLoc)) :=
    fun τ _ => NameLaws.refl _
  have adm := rootComm_admitted_mixed capturingCommRows Comm.Controls.start
    (.fvar "a") pZero demoChan (nQuote (.fvar "a")) (.fvar "a") 0 1 2 3 r0 r1
    (by decide) (by decide) (by simp [Comm.Controls.start]) (by simp [Comm.Controls.start])
    (by simp [Comm.Controls.start]) (by simp [Comm.Controls.start])
    (σ₀ := σA) (fun _ m => absurd m List.not_mem_nil) (by decide +kernel) fr
  refine ⟨ρ, adm, fun σ solved => ?_⟩
  obtain ⟨_, unif, _, b1, b2⟩ := rootComm_reads_raw capturingCommRows Comm.Controls.start
    (.fvar "a") pZero demoChan demoChan (nQuote (.fvar "a")) (.fvar "a") 0 1 2 3 r0 r1
    (by decide) ρ solved
  rw [psubst_pZero] at unif
  simp only [psubst_atLoc_any, psubst_nQuote, psubst_rootLoc] at b1 b2
  have qEq : NameLaws (nQuote (psubst σ (.fvar "a"))) (nQuote pZero) :=
    ReflNames.nameLaws_nQuote (bagLaws_of_nameLaws unif)
  exact ⟨b1.trans ((locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨qEq, NameLaws.refl _⟩),
    b2.trans ((locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨unif, NameLaws.refl _⟩)⟩

def canaryCommRows : ℕ → Pattern
  | 0 => atLoc (predotU (pFor nestedZeroTerm demoChan pZero)) rootLoc
  | 1 => atLoc (predotU (pFor nestedVarY demoChan nestedVarY)) rootLoc
  | _ => pZero

def pollutedCanaryConf : Configuration Pattern ℕ := ⟨[(.fvar "y", atomA)], {0, 1}⟩

/-- **Sharpness of `FreeOnPats` (`H7`)**: when `C.equations` already constrains `"y"` to `atomA`
(`¬ FreeOnPats [nestedVarY] pollutedCanaryConf.equations`), `nestedCanaryInner` steps in the source
(`BagStep conventional`), yet `rootCommAt` is **refused at every opening** on `located` at `QN`! -/
theorem polluted_equations_block_comm :
    ¬ FreeOnPats [nestedVarY] pollutedCanaryConf.equations ∧
    BagStep conventional nestedCanaryInner canaryReduct ∧
    ∀ ρ : PSubst, ¬ (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed canaryCommRows pollutedCanaryConf) (rootCommAt ρ 0 1 2 3) := by
  have stepSrc : BagStep conventional nestedCanaryInner canaryReduct := by
    have split₀ : ReflCorrespondence.Splits nestedCanaryInner
        ([] ++ pFor nestedZeroTerm demoChan pZero :: ([] ++ pFor nestedVarY demoChan nestedVarY :: [])) :=
      show ReflCorrespondence.Splits (par _ _) ([_] ++ [_]) from
        .split (.leaf _) (.leaf _)
    have plainA : PlainPatterns (applyDot nestedCanaryUnifier pZero) := by
      simp [PlainPatterns, PlainPatternsList, applyDot, pZero,
        Mettapedia.OSLF.MeTTaIL.Match.applyBindings]
    have plainB : PlainPatterns (applyDot nestedCanaryUnifier nestedVarY) := by
      simp [PlainPatterns, PlainPatternsList, applyDot, nestedCanaryUnifier, nestedVarY,
        nestedZeroTerm, tProc, pZero, nQuote, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
        Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.dotBindings]
    exact (HostedSubStepN.comm [] [] [] nestedZeroTerm nestedVarY demoChan pZero nestedVarY
      nestedCanaryUnifier split₀ (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) plainA plainB nestedCanaryUnifier_gp
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).toBagStep
  refine ⟨fun fr => ?_, stepSrc, fun ρ adm => ?_⟩
  · obtain ⟨w, wMod, wAg⟩ := fr (fun v => if v = "y" then some nestedZeroTerm else none)
    have eqA : NameLaws (psubst w (.fvar "y")) (psubst w atomA) :=
      wMod (.fvar "y", atomA) (by simp [pollutedCanaryConf])
    have eqZ : NameLaws (psubst w nestedVarY) nestedZeroTerm := wAg nestedVarY (by simp)
    rw [psubst_of_pvars_nil w atomA (by decide +kernel)] at eqA
    exact absurd (eqA.symm.trans eqZ) (by decide +kernel)
  · obtain ⟨σ, solved⟩ := solution_of_admitted adm
    have kn := info_known _ solved
    have eqA : NameLaws (psubst σ (.fvar "y")) (psubst σ atomA) :=
      kn (.fvar "y", atomA) (by simp [pollutedCanaryConf])
    rw [psubst_of_pvars_nil σ atomA (by decide +kernel)] at eqA
    have r0 : ∀ τ : PSubst, nameAction.Models τ pollutedCanaryConf.equations →
        NameLaws (psubst τ (canaryCommRows 0))
          (psubst τ (atLoc (pFor nestedZeroTerm demoChan pZero) rootLoc)) :=
      fun _ _ => NameLaws.refl _
    have r1 : ∀ τ : PSubst, nameAction.Models τ pollutedCanaryConf.equations →
        NameLaws (psubst τ (canaryCommRows 1))
          (psubst τ (atLoc (pFor nestedVarY demoChan (nQuote nestedVarY)) rootLoc)) :=
      fun _ _ => NameLaws.refl _
    obtain ⟨_, unif, -⟩ := rootComm_reads_raw canaryCommRows pollutedCanaryConf
      nestedZeroTerm nestedVarY demoChan demoChan pZero (nQuote nestedVarY) 0 1 2 3 r0 r1
      (by decide) ρ solved
    rw [psubst_of_pvars_nil σ nestedZeroTerm (by decide +kernel)] at unif
    exact absurd (unif.trans eqA) (by decide +kernel)

/-- **Sharpness of `pvars R = []` under Interface C (`H8`)**:
1. On `for(0 <- @0)(for(y <- @0)y) | for(0 <- @0)0`, one `COMM` steps to `R_bound = pPar [reductY, 0]`
   (`"y" ∈ pvars R_bound` bound, `pvars (close R_bound) = []`), where Interface **N**'s listener
   and Interface **C**'s canonical listener are `NameLaws`-distinct (`¬ NameLaws ...`)!
2. Conversely, on `nestedOpenInner = for(a1 <- @0)a1 | for(0 <- @0)a`, the reduct
   `R_free = pPar [@0, a]` has `"a"` **free** (`close` fixes free variables), where both listeners
   agree modulo `NameLaws` — pinpointing bound variables (`binders R ≠ []`) as the exact separator! -/
theorem open_reduct_separates_N_from_C :
    let R_bound := pPar [reductY, pZero]
    let R_free := pPar [applyDot nestedOpenUnifier (.fvar "a1"), applyDot nestedOpenUnifier (.fvar "a")]
    "y" ∈ pvars R_bound ∧
    pvars (close R_bound) = [] ∧
    BagStep conventional (par (pFor pZero demoChan reductY) (pFor pZero demoChan pZero)) R_bound ∧
    ¬ NameLaws (predotU (pFor (tProc R_bound) demoChan pZero))
        (predotU (listener demoChan R_bound)) ∧
    "a" ∈ pvars R_free ∧
    NameLaws (predotU (pFor (tProc R_free) demoChan pZero))
      (predotU (listener demoChan R_free)) := by
  intro R_bound R_free
  have stepBound : BagStep conventional
      (par (pFor pZero demoChan reductY) (pFor pZero demoChan pZero)) R_bound := by
    have st := BagStep.comm (admit := conventional) pZero pZero demoChan reductY pZero []
      MeTTaCalculus.Corrected.BagControls.principal_empty
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    have eq1 : applyDot [] reductY = reductY := by decide +kernel
    have eq2 : applyDot [] pZero = pZero := by decide +kernel
    rw [eq1, eq2] at st
    exact st
  have eqFree : R_free = pPar [nQuote pZero, .fvar "a"] := by
    simp [R_free, nestedOpenUnifier, applyDot, pZero, nQuote,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.dotBindings]
  exact ⟨by decide +kernel, by decide +kernel, stepBound, by decide +kernel,
    by rw [eqFree]; decide +kernel, by rw [eqFree]; decide +kernel⟩

def reflectOnlyLabel : ℕ → Pattern := fun _ => pReflect demoChan pZero

/-- **Sharpness of `NoReflectNode` in `conservativity_refl_free` (`H9`)**: on `rootState` encoding
`@0?(0)` (`HostedNode`, `¬ NoReflectNode`), `RuleSyntax.step QN ℕ QNE located` has an admitted
`openRoot` successor `s'` that is **not** `locate rootLoc s''` for any `s''`! -/
theorem conservativity_fails_with_reflect :
    HostedNode (pReflect demoChan pZero) ∧
    ¬ NoReflectNode (pReflect demoChan pZero) ∧
    ∃ s' : RuleSyntax.State Comm.Tm ℕ,
      Succ (RuleSyntax.step QN ℕ QNE located).toStep (rootState reflectOnlyLabel encodeConf) s' ∧
      ∀ s'' : RuleSyntax.State Comm.Tm ℕ, s' ≠ locate rootLoc s'' := by
  have eqEmb : rootState reflectOnlyLabel encodeConf =
      embed (rootState reflectOnlyLabel encodeConf).label encodeConf := rfl
  have clean₀ : Clean (childLoc rootLoc demoChan pZero)
      (rootState reflectOnlyLabel encodeConf).label encodeConf := by
    intro o oIn σ _
    have oZero : o = 0 := by simpa [encodeConf] using oIn
    subst oZero
    have l0 : (rootState reflectOnlyLabel encodeConf).label 0 =
        atLoc (pReflect demoChan pZero) rootLoc := rfl
    refine ⟨fun _ sm => ?_, fun _ _ sm => ?_, fun _ sm => ?_⟩
    · rw [l0, psubst_atLoc_any] at sm
      exact absurd (nameLaws_heads sm) (by decide)
    · rw [l0, psubst_atLoc_any] at sm
      exact absurd (nameLaws_heads sm) (by decide)
    · rw [l0, psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at sm
      exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp sm).2.symm
  obtain ⟨ρ, fr⟩ := open_fresh_exists (rootState reflectOnlyLabel encodeConf).label encodeConf 0 1 2
  have adm := openRoot_admitted (rootState reflectOnlyLabel encodeConf).label encodeConf
    demoChan pZero 0 1 2 (fun _ _ => NameLaws.refl _) clean₀ (by simp [encodeConf]) (by decide)
    ⟨by simp [encodeConf], by simp [encodeConf]⟩
    (σ₀ := fun _ => none) (fun _ m => absurd m List.not_mem_nil) fr
  refine ⟨.reflect ⟨by decide +kernel, by decide +kernel⟩ .zero,
    fun h => by
      generalize eq : pReflect demoChan pZero = P at h
      cases h <;> simp [pZero, nQuote, par, pPar, pFor, pReflect] at eq,
    (openRootAt ρ 0 1 2).result QN (rootState reflectOnlyLabel encodeConf),
    ⟨openRootAt ρ 0 1 2, by rwa [eqEmb], rfl⟩,
    fun s'' eqLoc => ?_⟩
  obtain ⟨σ, solved⟩ := solution_of_admitted adm
  have rMade := (ReflCorrespondence.openRoot_reads (rootState reflectOnlyLabel encodeConf).label
    encodeConf demoChan pZero 0 1 2 ρ (fun _ _ => NameLaws.refl _) (by decide) solved).2.1
  have lblEq : ((openRootAt ρ 0 1 2).result QN (rootState reflectOnlyLabel encodeConf)).label 1 =
      (locate rootLoc s'').label 1 := congrFun (congrArg RuleSyntax.State.label eqLoc) 1
  change (res (rootState reflectOnlyLabel encodeConf).label encodeConf (openRootAt ρ 0 1 2)).label 1 =
      atLoc (s''.label 1) rootLoc at lblEq
  rw [lblEq, psubst_atLoc_any, psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at rMade
  exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp rMade).2.symm

/-! ## 4. `P7` Runtime-binder-packing boundary theorems -/

/-- **`P7` Positive Fragment Theorem**: when `bs` is ground-valued (`GroundPrincipal t u bs`) and
`Apart t A u B` holds (`∀ x ∈ keys, x ∉ binders A`), `dotted (pvars t) (predotU A)` reads as
`predotU (applyDot bs A)` modulo `NameLaws` **even when `binders A ≠ []`**!
Instantiated on `A_nested := for(y <- @0)(x | y)` (`binders A_nested = ["y"] ≠ []`). -/
theorem p7_ground_comm_with_inner_binders :
    (∀ {t u A B : Pattern} {bs : Bindings} {σ : PSubst},
      GroundPrincipal t u bs → Apart t A u B → firstOrder A = true →
      groundBags (predotU t) = true → groundBags (predotU u) = true →
      bagCanon (predotU t) = predotU t → bagCanon (predotU u) = predotU u →
      GroundPrincipal (predotU t) (predotU u) bs →
      NameLaws (psubst σ (predotU t)) (psubst σ (predotU u)) →
      NameLaws (psubst σ (dotted (pvars t) (predotU A))) (psubst σ (predotU (applyDot bs A)))) ∧
    (let A_nested := pFor (.fvar "y") demoChan (par (.fvar "x") (.fvar "y"))
     binders A_nested = ["y"] ∧
     ∀ σ : PSubst, psubst σ (.fvar "x") = pZero →
       NameLaws (psubst σ (dotted ["x"] (predotU A_nested)))
         (psubst σ (predotU (applyDot [("x", pZero)] A_nested)))) := by
  refine ⟨fun {t u A B bs σ} gp conv foA gT gU cT cU gpU unif => ?_, ?_⟩
  · obtain ⟨keptA, -⟩ := keys_of_apart conv
    obtain ⟨keysOf, bound, _, _⟩ := gp
    have agrees : ∀ x ∈ pvars t ++ pvars u, ∀ v, bs.lookup x = some v →
        BagLaws (psubst σ (.fvar x)) v := by
      have agU := ReflQuotient.agrees_of_groundPrincipal gpU gT gU cT cU
        (bagLaws_of_nameLaws unif)
      intro x mem v lk
      exact agU x (by rwa [ReflUniform.pvars_predotU, ReflUniform.pvars_predotU]) v lk
    rw [applyDot_eq bs A foA]
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
      exact by simp [lookup_eq_none_of_keys keysOf (fun inK => keptA x inK inside)]
    rw [ReflUniform.predotU_psubst ground A untouched]
    unfold dotted
    rw [psubst_comp, psubst_comp]
    apply psubst_nameLaws_congr
    intro x occurs
    have inA : x ∈ pvars A := by rwa [ReflUniform.pvars_predotU] at occurs
    by_cases inKeys : x ∈ pvars t ++ pvars u
    · have inT : x ∈ pvars t := by
        rcases List.mem_append.mp inKeys with h | h
        · exact h
        · exact absurd inA (conv.rightOutside x h)
      obtain ⟨v, found, closed⟩ := bound x inKeys
      simp only [pcomp, quoteOn, if_pos inT, Option.getD_some, psubst_nQuote, found, Option.map_some]
      rw [psubst_of_pvars_nil σ v closed]
      exact nameLaws_nQuote (agrees x inKeys v found)
    · have notT : x ∉ pvars t := fun h => inKeys (List.mem_append_left _ h)
      have look : bs.lookup x = none := lookup_eq_none_of_keys keysOf inKeys
      simp only [pcomp, quoteOn, if_neg notT, look, Option.map_none]
      exact NameLaws.refl _
  · dsimp only
    refine ⟨by decide +kernel, fun σ hx => ?_⟩
    have gpX : GroundPrincipal (.fvar "x") pZero [("x", pZero)] := by
      refine ⟨by decide +kernel, ?_, by decide +kernel, ?_⟩
      · intro z m
        have zEq : z = "x" := by simpa [pZero, pvars, MeTTaOperationsComm.pvars.pvarsList] using m
        subst zEq; exact ⟨pZero, rfl, by decide +kernel⟩
      · intro τ s z m v lk
        have zEq : z = "x" := by simpa [pZero, pvars, MeTTaOperationsComm.pvars.pvarsList] using m
        subst zEq
        have vEq : v = pZero :=
          (by simpa [Bindings.lookup] using lk : pZero = v).symm
        subst vEq; exact s.trans (psubst_pZero τ)
    obtain ⟨keysOf, bound, _, _⟩ := gpX
    exact nameLaws_of_eq (dotted_reads_predotU keysOf bound
      (fun z _ v lk => by
        have zEq : z = "x" := by
          cases z == "x" <;> simp_all [Bindings.lookup]
        subst zEq
        have vEq : v = pZero := (by simpa [Bindings.lookup] using lk : pZero = v).symm
        subst vEq; exact hx)
      (pFor (.fvar "y") demoChan (par (.fvar "x") (.fvar "y")))
      (by decide +kernel) (fun z m => List.mem_append_left _ m)
      (fun z _ inK => by simpa [pZero, pvars, MeTTaOperationsComm.pvars.pvarsList] using inK)
      (by decide +kernel))

/-- **`P7` Negative Boundary Theorem 1 (Dynamic Binder / Crossing into Inner Pattern)**:
when an outer pattern variable `"P"` crosses into an inner input's pattern
(`A_cross := for(@P <- @0)P`, `"P" ∈ binders A_cross`), static `dotted ["P"] (predotU A_cross)`
double-quotes `"P"` (`@@0`) under `"P" ↦ 0`, whereas `predotU (applyDot [("P", 0)] A_cross)`
single-quotes it (`@0`), separated modulo `NameLaws`! -/
theorem p7_dynamic_binder_double_dot_boundary :
    let A_cross := pFor (tProc (.fvar "P")) demoChan (.fvar "P")
    let σP : PSubst := fun v => if v = "P" then some pZero else none
    "P" ∈ binders A_cross ∧
    psubst σP (dotted ["P"] (predotU A_cross)) =
      pFor (tProc (nQuote pZero)) demoChan (nQuote (nQuote pZero)) ∧
    psubst σP (predotU (applyDot [("P", pZero)] A_cross)) =
      pFor (tProc (nQuote pZero)) demoChan (nQuote pZero) ∧
    ¬ NameLaws (psubst σP (dotted ["P"] (predotU A_cross)))
        (psubst σP (predotU (applyDot [("P", pZero)] A_cross))) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def locatedBinderInstantiatedRows : ℕ → Pattern
  | 0 => atLoc (predotU (pFor (tProc reductY) demoChan pZero)) rootLoc
  | 1 => atLoc (predotU instantiatedPartner) rootLoc
  | _ => pZero

/-- **`P7` Negative Boundary Theorem 2 (Open Binder Instantiation at Close)**:
packing `reductY = for(y <- @0)y` at `closeRoot` without runtime binder packing produces
`predotU (for(@reductY <- @0)0) @ Root`, which on `located` at `QN` **admits** `rootCommAt`
against the alpha-renamed partner `predotU (for(@reductW <- @0)0) @ Root`, yet **refuses at every
opening** `rootCommAt` against the binder-instantiating partner `for(@(for(0 <- @0)0) <- @0)0`,
whereas `Corrected.Step conventional` meets in the source! -/
theorem p7_quoted_binder_instantiation_boundary :
    (∃ bs, MeTTaCalculus.Corrected.Step conventional
      (par ReflUniform.Controls.sourceListener instantiatedPartner)
      (par (applyDot bs pZero) (applyDot bs pZero))) ∧
    (∃ ρ : PSubst, (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed locatedBinderUniformRows Comm.Controls.start) (rootCommAt ρ 0 1 2 3)) ∧
    (∀ ρ : PSubst, ¬ (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed locatedBinderInstantiatedRows Comm.Controls.start) (rootCommAt ρ 0 1 2 3)) := by
  obtain ⟨bs, _, _, stSrc⟩ := ReflUniform.Controls.instantiated_partner_meets_in_source
  refine ⟨⟨bs, stSrc⟩, binder_reduct_partner_control_QN.1, fun ρ adm => ?_⟩
  obtain ⟨σ, solved⟩ := solution_of_admitted adm
  have r0 : ∀ τ : PSubst, nameAction.Models τ Comm.Controls.start.equations →
      NameLaws (psubst τ (locatedBinderInstantiatedRows 0))
        (psubst τ (atLoc (pFor (tProc (pFor yv demoChan (nQuote yv))) demoChan pZero) rootLoc)) :=
    fun τ _ => nameLaws_of_eq (congrArg (psubst τ) (by decide +kernel))
  have r1 : ∀ τ : PSubst, nameAction.Models τ Comm.Controls.start.equations →
      NameLaws (psubst τ (locatedBinderInstantiatedRows 1))
        (psubst τ (atLoc (pFor (tProc reductZero) demoChan pZero) rootLoc)) :=
    fun τ _ => nameLaws_of_eq (congrArg (psubst τ) (by decide +kernel))
  obtain ⟨_, unify, -⟩ := rootComm_reads_raw locatedBinderInstantiatedRows Comm.Controls.start
    (tProc (pFor yv demoChan (nQuote yv))) (tProc reductZero) demoChan demoChan pZero pZero
    0 1 2 3 r0 r1 (by decide) ρ solved
  have bag := bagLaws_of_nameLaws unify
  rw [psubst_tProc, psubst_tProc] at bag
  have inner := ReflCorrespondence.Controls.bagLaws_of_tProc bag
  rw [psubst_pFor, reductZero, psubst_pFor] at inner
  have body := ReflCorrespondence.Controls.bagLaws_pFor_body inner
  rw [psubst_nQuote, psubst_pZero] at body
  exact ReflCorrespondence.Controls.nQuote_not_zero _ body

#print axioms packing_order_observable_without_quotient
#print axioms non_ground_bag_pattern_control_QN
#print axioms binder_reduct_partner_control_QN
#print axioms nested_reflection_premise_vs_hosted
#print axioms unbound_fvar_narrowed_by_rootHeat
#print axioms unclean_child_spurious_closeRoot
#print axioms rogue_root_token_admits_heatChild
#print axioms cross_reflection_capture_control
#print axioms apart_dropped_admits_capturing_comm
#print axioms polluted_equations_block_comm
#print axioms open_reduct_separates_N_from_C
#print axioms conservativity_fails_with_reflect
#print axioms p7_ground_comm_with_inner_binders
#print axioms p7_dynamic_binder_double_dot_boundary
#print axioms p7_quoted_binder_instantiation_boundary

/-! ## Reachable readiness and source-coverage controls -/

namespace Readiness

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open MeTTaCalculus.Corrected (binders)
open MeTTaCalculus.Corrected.ResidualControls (X Y principal_XY)
open ReflSystem
open ReflNames (QN QNE NameLaws nameAction)
open ReflLocated (located atLoc rootLoc)
open ReflLocatedStep (res resConf)
open MeTTaOperationsComm (PSubst psubst psubst_none)

theorem two_free_patterns_not_admissible (x z : String) (ch A ch' B : Pattern) :
    ¬ CommAdmissibleN (.fvar x) ch A (.fvar z) ch' B := by
  rintro (ordinary | exactGround)
  · obtain ⟨bs, gp, _⟩ := ordinary.unifiable ⟨fun _ => some pZero, rfl⟩
    have member : x ∈ pvars (.fvar x) ++ pvars (.fvar z) := by simp [pvars]
    obtain ⟨value, found, _⟩ := gp.covers x member
    have zero : pZero = value :=
      gp.principal (fun _ => some pZero) rfl x member value found
    have quoted : nQuote pZero = value :=
      gp.principal (fun _ => some (nQuote pZero)) rfl x member value found
    exact (by decide +kernel : pZero ≠ nQuote pZero) (zero.trans quoted.symm)
  · have closed := exactGround.groundT
    simp [pvars] at closed

def inner : Pattern := pFor (.fvar "y") demoChan pZero
def left : Pattern := pFor X demoChan inner
def right : Pattern := pFor Y demoChan pZero
def source : Pattern := par left right

theorem nested_continuation_has_binder : binders inner = ["y"] := rfl

/-- The source heating control is a real symbolic COMM, not an unsatisfiable pair. -/
theorem open_pair_has_symbolic_source_step :
    BagStep conventional source (par inner pZero) := by
  have apart : Apart X inner Y pZero := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
  have h := BagStep.comm (admit := conventional) X Y demoChan inner pZero
    [("X", Y)] principal_XY apart
  have same : par (applyDot [("X", Y)] inner) (applyDot [("X", Y)] pZero) =
      par inner pZero := by decide +kernel
  rw [same] at h
  exact h

theorem split_not_readyN (C : Configuration Pattern Nat) (active : List (ActiveEntry Nat)) :
    ¬ BackwardReadyN C [(1, left), (2, right)] active := by
  intro ready
  exact two_free_patterns_not_admissible _ _ _ _ _ _
    (ready.rootCommReady (1, left) (by simp) (2, right) (by simp)
      X demoChan inner Y demoChan pZero (by decide) rfl rfl)

theorem split_not_readyC (C : Configuration Pattern Nat) (active : List (ActiveEntry Nat)) :
    ¬ BackwardReadyC C [(1, left), (2, right)] active := by
  intro ready
  exact two_free_patterns_not_admissible _ _ _ _ _ _
    (ready.rootCommReady (1, left) (by simp) (2, right) (by simp)
      X demoChan inner Y demoChan pZero (by decide) rfl rfl)

theorem source_is_hosted : HostedNode source :=
  .par (.guard ⟨by decide +kernel, by decide +kernel⟩)
    (.guard ⟨by decide +kernel, by decide +kernel⟩)

/-- Starting from a single encoded parallel term, heat and commit two ground
guards. The backward rule reads the nested receiving continuation intact. -/
theorem ground_patterns_with_nested_continuation :
    let l := pFor pZero demoChan inner
    let r := pFor pZero demoChan pZero
    let src := par l r
    ∃ heat : PSubst,
      let h := rootHeatAt heat (0 : Nat) 1 2
      let label := (res (encodeLabel src) encodeConf h).label
      let C := resConf (encodeLabel src) encodeConf h
      (RuleSyntax.step QN Nat QNE located).Admits (s := embed (encodeLabel src) encodeConf) h ∧
      ∃ comm : PSubst,
        let f := rootCommAt comm (1 : Nat) 2 3 4
        (RuleSyntax.step QN Nat QNE located).Admits (s := embed label C) f ∧
        RootCells (res label C f).label (resConf label C f) [(3, inner), (4, pZero)] ∧
        BagStep conventional (rootBagProcess (O := Nat) [(1, l), (2, r)])
          (rootBagProcess (O := Nat) [(3, inner), (4, pZero)]) := by
  dsimp only
  let l := pFor pZero demoChan inner
  let r := pFor pZero demoChan pZero
  let src := par l r
  obtain ⟨heat, heatFresh⟩ := rootHeat_fresh_exists (encodeLabel src) encodeConf 0 1 2
  have known : nameAction.Models (fun _ => none) encodeConf.equations :=
    fun _ m => absurd m List.not_mem_nil
  have pair : NameLaws (psubst (fun _ => none) (encodeLabel src 0))
      (atLoc (par (predotU l) (predotU r)) rootLoc) := by
    rw [psubst_none]
    change NameLaws (atLoc (predotU (par l r)) rootLoc) _
    rw [predotU_par]
    exact NameLaws.refl _
  have heatAdm := rootHeat_admitted (encodeLabel src) encodeConf 0 1 2
    (by decide) (by decide) (by decide) (by decide) known pair heatFresh
  let h := rootHeatAt heat (0 : Nat) 1 2
  let label := (res (encodeLabel src) encodeConf h).label
  let C := resConf (encodeLabel src) encodeConf h
  have rows : RootCells label C [(1, l), (2, r)] :=
    (rootCells_heat (pre := []) (post := []) (single_root_init src []).2.1 heatAdm).1
  obtain ⟨σ, solved⟩ := solution_of_admitted heatAdm
  obtain ⟨comm, commFresh⟩ := rootComm_fresh_exists label C 1 2 3 4
  have ground : pvars pZero = [] := rfl
  have channel : HostedChan demoChan := ⟨by decide +kernel, by decide +kernel⟩
  have stillFresh (o : Nat) (old : o ∉ encodeConf.present) (new : o ∉ [1, 2]) :
      o ∉ C.present := by
    change o ∉ (res (encodeLabel src) encodeConf h).present
    rw [ReflLocatedStep.result_present]
    rintro (⟨m, _⟩ | m)
    · exact old m
    · exact new m
  obtain ⟨commAdm, -⟩ := rootCells_comm_ground_forward
    (pre := []) (mid := []) (post := []) rows ground ground (NameLaws.refl _)
    channel.1 (by decide) (stillFresh 3 (by decide) (by decide))
    (stillFresh 4 (by decide) (by decide)) solved commFresh
  have admissible : ExactGroundComm pZero demoChan inner pZero demoChan pZero :=
    ⟨ground, ground, fun _ => rfl, channel, channel, by decide +kernel, by decide +kernel,
      .guard channel, .zero⟩
  have hosted : ∀ q ∈ ([(1, l), (2, r)] : List (Nat × Pattern)), HostedNode q.2 := by
    intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .guard channel
  obtain ⟨_, bs, principal, rows', _, sourceStep, _⟩ :=
    rootCells_comm_admissible (rest := []) rows hosted (.inr admissible) commAdm
  have empty : bs = [] := List.eq_nil_iff_forall_not_mem.mpr fun e member => by
    simpa only [ground, List.append_nil, List.not_mem_nil] using principal.keys e member
  subst bs
  have keepInner : applyDot [] inner = inner :=
    (applyDot_eq [] inner (by decide +kernel)).trans (psubst_none inner)
  have keepZero : applyDot [] pZero = pZero :=
    (applyDot_eq [] pZero (by decide +kernel)).trans (psubst_none pZero)
  rw [keepInner, keepZero] at rows' sourceStep
  exact ⟨heat, heatAdm, comm, commAdm, rows', sourceStep⟩

/-- A genuinely admitted root-heating firing reaches a root representation
whose two-input rows satisfy neither readiness predicate. -/
theorem admitted_heating_loses_readiness :
    BackwardReadyN encodeConf [(0, source)] [] ∧
      BackwardReadyC encodeConf [(0, source)] [] ∧
      SystemInvN (encodeLabel source) encodeConf source ∧
      ∃ opening : PSubst,
        (RuleSyntax.step QN Nat QNE located).Admits
          (s := OneFrame.embed (encodeLabel source) encodeConf) (rootHeatAt opening 0 1 2) ∧
        RootCells (res (encodeLabel source) encodeConf (rootHeatAt opening 0 1 2)).label
          (resConf (encodeLabel source) encodeConf (rootHeatAt opening 0 1 2))
          [(1, left), (2, right)] ∧
        ¬ BackwardReadyN (resConf (encodeLabel source) encodeConf (rootHeatAt opening 0 1 2))
          [(1, left), (2, right)] [] ∧
        ¬ BackwardReadyC (resConf (encodeLabel source) encodeConf (rootHeatAt opening 0 1 2))
          [(1, left), (2, right)] [] := by
  obtain ⟨opening, fresh⟩ := rootHeat_fresh_exists (encodeLabel source) encodeConf 0 1 2
  have known : nameAction.Models (fun _ => none) encodeConf.equations := by
    intro equation impossible
    cases impossible
  have pair : NameLaws (psubst (fun _ => none) (encodeLabel source 0))
      (atLoc (par (ReflUniform.predotU left) (ReflUniform.predotU right)) rootLoc) := by
    rw [psubst_none]
    change NameLaws (atLoc (ReflUniform.predotU (par left right)) rootLoc) _
    rw [predotU_par]
    exact NameLaws.refl _
  have admitted := rootHeat_admitted (encodeLabel source) encodeConf 0 1 2
    (by decide) (by decide) (by decide) (by decide) known pair fresh
  have initial := (single_root_init source []).2.1
  have rows := (rootCells_heat (pre := []) (post := []) initial admitted).1
  exact ⟨(encode_backwardReady source).1, (encode_backwardReady source).2,
    (encode_in_relation source_is_hosted).2.1, opening, admitted, rows,
    split_not_readyN _ [], split_not_readyC _ []⟩

/-- The conditional run relation is inhabited by a nonidentity run. Its
terminal constructor does not assert readiness at the final state. -/
theorem a_nontrivial_ready_run_can_end_unready :
    ∃ opening : PSubst,
      ReadyLocatedRunN (encodeLabel source) encodeConf source
        (res (encodeLabel source) encodeConf (rootHeatAt opening 0 1 2)).label
        (resConf (encodeLabel source) encodeConf (rootHeatAt opening 0 1 2)) ∧
      resConf (encodeLabel source) encodeConf (rootHeatAt opening 0 1 2) ≠ encodeConf ∧
      ¬ BackwardReadyN (resConf (encodeLabel source) encodeConf (rootHeatAt opening 0 1 2))
        [(1, left), (2, right)] [] := by
  obtain ⟨_, _, _, opening, admitted, rows, notReady, _⟩ := admitted_heating_loses_readiness
  have initial : SystemInvBy StepRelN (encodeLabel source) encodeConf source [(0, source)] [] :=
    (encode_cleanRepresentsBy source_is_hosted (pats := [])
      (fun _ impossible => nomatch impossible)).toSystemInvBy
  refine ⟨opening, .step initial (encode_backwardReady source).1
    (rootHeatAt opening 0 1 2) admitted (fun _ invariant => .refl invariant), ?_, notReady⟩
  intro same
  have present : 1 ∈ (resConf (encodeLabel source) encodeConf (rootHeatAt opening 0 1 2)).present :=
    (rows.rows (1, left) (by simp)).1
  rw [same] at present
  simp [encodeConf] at present

#print axioms two_free_patterns_not_admissible
#print axioms open_pair_has_symbolic_source_step
#print axioms ground_patterns_with_nested_continuation
#print axioms split_not_readyN
#print axioms source_is_hosted
#print axioms admitted_heating_loses_readiness
#print axioms a_nontrivial_ready_run_can_end_unready

end Readiness

namespace Ownership

open ReflSystem
open ReflQuotient.Controls (inputAB inputY patAB patY yToB)
open ReflLocated (psubst_par heatChild_reads_determinately)
open ReflLocatedStep (psubst_pReflect nameLaws_pReflect_iff commChildAt closeChildAt result_label_old)
open ReflNames (nameLaws_pFor_iff nameLaws_tProc nameLaws_psubst)
open ReflPacking (coolAt cool_reads bagLaws_cooled_zero)
open ReflCorrespondence (closeRoot_admitted_at_solution close_present cool_fresh_exists cool_admitted)
open ReflLocatedStep.Ownership (Store Candidate routes open_root_plan start_unreserved routed_result
  append_update ScopeLinks routes_eq_of_footprint usePhysicalGuards usePhysicalGuards_last
  LabelForms start_labelForms run_labelForms result_labelForms withWrittenComm
  written_comm_admits_iff writtenBinding_root writtenComm writtenTells
  readWrittenPair_root writtenPairTells writtenPairTells_at admits_with_tells
  startAuthored withAuthored AuthoredReads reachable_authored authored_admits_of_models authored_routed_result)
open LocatedSubstitution.Authority (Ledger)

private def liveBody : Pattern := par inputAB inputAB
private def dormantBody : Pattern := par inputY inputAB
private def ownerRow : Pattern := pReflect demoChan liveBody
private def siblingRow : Pattern := pReflect demoChan dormantBody
private def twoReflections : Pattern := par ownerRow siblingRow

private abbrev routedStep := ReflLocatedStep.Ownership.step (O := ℕ)
private abbrev physicalStep := ReflLocatedStep.Ownership.step (O := ℕ) .physical

private def rootWrittenRows (rows : List (ℕ × Pattern)) (_ : Store ℕ) (place : Option ℕ) :
    List (ℕ × Pattern) :=
  match place with
  | none => rows
  | some _ => []

/-- The routing annotation of the packed checkpoint: the completed token
carries the opening key and source row; all other live rows are at root. -/
private def packedStore (label : ℕ → Pattern) (C : Configuration Pattern ℕ)
    (key token : ℕ) : Store ℕ :=
  Store.plain (embed label C)
    ⟨fun o => if o ∈ C.present then
      if o = token then some (.control ⟨key, 1, none⟩ .done) else some (.cell none)
      else none, insert key C.present⟩

private def packedClose (label : ℕ → Pattern) (C : Configuration Pattern ℕ)
    (key token : ℕ) (opening : PSubst) (owner made : ℕ) : Candidate (packedStore label C key token) :=
  ⟨closeRootAt opening owner token made, .closeRoot, rfl⟩

private theorem packed_route_empty (label : ℕ → Pattern) (C : Configuration Pattern ℕ)
    (key token : ℕ) : (packedStore label C key token).childRows key = ∅ := by
  ext o
  by_cases live : o ∈ C.present <;> by_cases isTok : o = token <;>
    simp [packedStore, Store.childRows, Store.route, embed, live, isTok]

private theorem packed_nested_empty (label : ℕ → Pattern) (C : Configuration Pattern ℕ)
    (key token : ℕ) : (packedStore label C key token).nested key = ∅ := by
  ext o
  by_cases isTok : o = token
  · subst o
    by_cases live : token ∈ C.present <;>
      simp [packedStore, Store.nested, Store.route, embed, live, LocatedSubstitution.Authority.Mark.ticket]
  · by_cases live : o ∈ C.present <;>
      simp [packedStore, Store.nested, Store.route, embed, live, isTok, LocatedSubstitution.Authority.Mark.ticket]

private theorem packed_reserved_owner (label : ℕ → Pattern) (C : Configuration Pattern ℕ)
    (key token : ℕ) (present : token ∈ C.present) :
    (packedStore label C key token).reserved 1 = {token} := by
  ext o
  by_cases isTok : o = token
  · subst o
    simp [packedStore, Store.reserved, Store.route, embed, present, LocatedSubstitution.Authority.Mark.ticket]
  · by_cases live : o ∈ C.present <;>
      simp [packedStore, Store.reserved, Store.route, embed, live, isTok, LocatedSubstitution.Authority.Mark.ticket]

/-- The routed transform firing, not a separately postulated ticket,
gives the child row and pending token the key of its actual birth. -/
theorem routed_open_installs_the_birth_key :
    let initial := ReflLocatedStep.Ownership.start (embed (encodeLabel ownerRow) encodeConf)
    ∃ opening : PSubst,
      let fireOpen : Candidate initial := ⟨openRootAt opening 0 1 2, .openRoot, rfl⟩
      ∃ admitted : routedStep.Admits (s := initial) fireOpen,
        let after := routedStep.toStep.result fireOpen admitted
        after.route 0 = some (.cell none) ∧
        after.route 1 = some (.cell (some 2)) ∧
        after.route 2 = some (.control ⟨2, 0, none⟩ .pending) ∧
        2 ∈ after.issued := by
  dsimp only
  let initial := ReflLocatedStep.Ownership.start (embed (encodeLabel ownerRow) encodeConf)
  obtain ⟨_, _, clean, _⟩ := single_root_init ownerRow []
  obtain ⟨opening, fresh⟩ := open_fresh_exists (encodeLabel ownerRow) encodeConf 0 1 2
  let openIt : Candidate initial := ⟨openRootAt opening 0 1 2, .openRoot, rfl⟩
  have known : nameAction.Models (fun _ => none) encodeConf.equations :=
    fun _ impossible => nomatch impossible
  have rawOpen := openRoot_admitted (encodeLabel ownerRow) encodeConf demoChan (predotU liveBody) 0 1 2
    (fun _ _ => NameLaws.refl _) (clean rootLoc _ _ .root (Nat.zero_le _))
    (by decide) (by decide) (by decide) known fresh
  let marks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 2 :=
    #v[.cell (some 2), .control ⟨2, 0, none⟩ .pending]
  have planned : openIt.plan = some marks :=
    open_root_plan initial 0 1 2 (by decide +kernel) (start_unreserved _ _)
  have admitted : routedStep.Admits (s := initial) openIt := by
    refine ⟨rawOpen, ?_, ?_⟩
    · rw [planned]
      rfl
    · change Disjoint ({1, 2} : Finset ℕ) {0}
      decide +kernel
  refine ⟨opening, admitted, ?_⟩
  change (routedStep.toStep.result openIt admitted).route 0 = _ ∧ _ ∧ _ ∧ _
  rw [routed_result (policy := .whole) admitted planned]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have kept : 0 ∈ MeTTaCalculus.OccurrenceCommits.fire initial.raw.present
        (openIt.raw.selection.commit (T := Unit)) := by
      change 0 ∈ ({0} : Finset ℕ) ∪ {1, 2}
      decide +kernel
    exact (Ledger.mark_retained initial.ledger _ kept (by change 0 ∉ ([1, 2] : List ℕ); decide +kernel)).trans
      (by decide +kernel)
  · apply Ledger.mark_installed
    · change ([1, 2] : List ℕ).Nodup
      decide +kernel
    · change _ ∈ ([1, 2].zip marks.toList)
      decide +kernel
  · apply Ledger.mark_installed
    · change ([1, 2] : List ℕ).Nodup
      decide +kernel
    · change _ ∈ ([1, 2].zip marks.toList)
      decide +kernel
  · change 2 ∈ ({0} : Finset ℕ) ∪ {1, 2}
    decide +kernel

/-- The two opened regions retain distinct owners and cannot be cleared
or reheated while they have outstanding children. -/
def nestedOpeningCheckpoint (s : Store ℕ) : Prop :=
  s.route 2 = some (.control ⟨2, 0, none⟩ .pending) ∧
  s.route 4 = some (.control ⟨4, 1, some 2⟩ .pending) ∧
  s.route 1 = some (.cell (some 2)) ∧ s.route 3 = some (.cell (some 4)) ∧
  s.nested 2 = {4} ∧ (routes s .rootClear [0] [] []).isNone ∧
  (routes s .childHeat [1] [2] [5, 6]).isNone

private def Reads (label : ℕ → Pattern) (C : Configuration Pattern ℕ) (row : ℕ)
    (meaning : Pattern) : Prop :=
  ∀ σ : PSubst, nameAction.Models σ C.equations →
    NameLaws (psubst σ (label row)) (psubst σ meaning)

private theorem reads_retained {label : ℕ → Pattern} {C : Configuration Pattern ℕ}
    {row : ℕ} {meaning : Pattern} (reads : Reads label C row meaning)
    (f : Firing ℕ QNE located PUnit.unit) (old : row ∉ f.selection.made) :
    Reads (res label C f).label (resConf label C f) row meaning := by
  intro σ solved
  rw [result_label_old f old]
  exact reads σ (info_known f solved)

private theorem cool_owned {initial : Store ℕ} (earlier : routedStep.toStep.Run initial)
    {label : ℕ → Pattern} {C : Configuration Pattern ℕ} {book : Ledger ℕ ReflLocatedStep.Ownership.Phase}
    (endpoint : earlier.last = (Store.plain (embed label C) book)) (l m acc body : Pattern)
    (token row made : ℕ) (stamp : LocatedSubstitution.Authority.Ticket ℕ)
    (readsToken : Reads label C token (doneTok l m acc))
    (readsRow : Reads label C row (atLoc body l))
    (distinct : token ≠ row) (liveToken : token ∈ C.present) (liveRow : row ∈ C.present)
    (fresh : made ∉ C.present) (neverIssued : Disjoint {made} book.issued)
    (plan : routes (Store.plain (embed label C) book) .cool [token, row] [] [made] = some #v[.control stamp .done])
    (solvable : ∃ σ : PSubst, nameAction.Models σ C.equations) :
    ∃ ρ : PSubst, let f : Candidate (Store.plain (embed label C) book) := ⟨coolAt ρ token row made, .cool, rfl⟩
      let C' := resConf label C f.raw
      (∃ run : routedStep.toStep.Run initial, run.last = ReflLocatedStep.Ownership.update f #v[.control stamp .done]) ∧
      (∃ σ : PSubst, nameAction.Models σ C'.equations) ∧
      Reads (res label C f.raw).label C' made (doneTok l m (par acc body)) := by
  obtain ⟨σ, known⟩ := solvable
  obtain ⟨ρ, opens⟩ := cool_fresh_exists label C token row made
  have raw := cool_admitted label C l m acc body token row made readsToken readsRow distinct
    liveToken liveRow fresh known opens
  exact ⟨ρ, append_update (policy := .whole) earlier endpoint raw plan neverIssued, solution_of_admitted raw,
    fun _ solved => cool_reads label C ρ token row made l m acc body readsToken readsRow solved⟩

private theorem no_row_at_other_depth {σ : PSubst} {row body atSite target : Pattern}
    (spine : IsLocSpine atSite) (targetSpine : IsLocSpine target)
    (depth : locDepth atSite ≠ locDepth target)
    (read : NameLaws (psubst σ row) (psubst σ (atLoc body atSite))) (p : Pattern) :
    ¬ NameLaws (psubst σ row) (atLoc p (psubst σ target)) := by
  intro wrong
  rw [psubst_atLoc_any] at read
  have sites := ((locatedFrame_name.atLoc_iff _ _ _ _).mp (read.symm.trans wrong)).2
  exact depth ((locDepth_psubst_spine spine σ).symm.trans
    ((locDepth_nameLaws sites).trans (locDepth_psubst_spine targetSpine σ)))

private def canaryCommittedView : Store ℕ :=
  let opening : PSubst := fun _ => none
  let root := ReflLocatedStep.Ownership.start (embed (encodeLabel nestedCanarySource) encodeConf)
  let opened := ReflLocatedStep.Ownership.update
    (⟨openRootAt opening 0 1 2, .openRoot, rfl⟩ : Candidate root)
    #v[.cell (some 2), .control ⟨2, 0, none⟩ .pending]
  let nested := ReflLocatedStep.Ownership.update
    (⟨openChildAt opening 1 2 3 4, .openChild, rfl⟩ : Candidate opened)
    #v[.cell (some 4), .control ⟨4, 1, some 2⟩ .pending]
  let heated := ReflLocatedStep.Ownership.update
    (⟨heatChildN opening 3 4 5 6, .childHeat, rfl⟩ : Candidate nested)
    #v[.cell (some 4), .cell (some 4)]
  ReflLocatedStep.Ownership.update
    (⟨commChildAt opening 5 6 4 7 8 9, .childComm, rfl⟩ : Candidate heated)
    #v[.cell (some 4), .cell (some 4), .control ⟨4, 1, some 2⟩ .done]

private abbrev canaryConfig (knowledge : List (Pattern × Pattern)) : Configuration Pattern ℕ :=
  ⟨knowledge, canaryCommittedView.raw.present⟩

private abbrev canaryStore (label : ℕ → Pattern) (knowledge : List (Pattern × Pattern)) : Store ℕ :=
  Store.plain (embed label (canaryConfig knowledge)) canaryCommittedView.ledger

/-- The terminal return leaves exactly one listener and no outstanding
tickets. The symbolic result must be solvable and agree at every solution. -/
def NestedCanaryReturn (s : Store ℕ) (policy : ReflLocatedStep.Ownership.GuardPolicy := .whole) : Prop :=
  ∃ returned : (ReflLocatedStep.Ownership.step (O := ℕ) policy).toStep.Run s,
    returned.last.raw.present = {15} ∧
    returned.last.issued = Finset.range 16 ∧
    (∀ o, returned.last.route o = if o = 15 then some (.cell none) else none) ∧
    (∃ σ : PSubst, nameAction.Models σ returned.last.raw.knowledge) ∧
    (∀ σ : PSubst, nameAction.Models σ returned.last.raw.knowledge →
      NameLaws (psubst σ (returned.last.raw.label 15))
        (psubst σ (atLoc (predotU nestedCanaryTargetN) rootLoc))) ∧
    BagStep conventional nestedCanarySource nestedCanaryTargetN

private theorem finish_canary_root {initial : Store ℕ} (earlier : routedStep.toStep.Run initial)
    (label : ℕ → Pattern) (C : Configuration Pattern ℕ) (book : Ledger ℕ ReflLocatedStep.Ownership.Phase)
    (endpoint : earlier.last = (Store.plain (embed label C) book))
    (covers : initial.ledger.Covers initial.raw.present) (forms : LabelForms initial) (live : C.present = {0, 14})
    (issued : book.issued = Finset.range 15)
    (plan : routes (Store.plain (embed label C) book) .closeRoot [0, 14] [] [15] = some #v[.cell none])
    (known : ∃ σ : PSubst, nameAction.Models σ C.equations) :
    let inside := pReflect demoChan (predotU nestedCanaryInner)
    let region := childLoc rootLoc demoChan inside
    Reads label C 0 (atLoc (pReflect demoChan inside) rootLoc) →
    Reads label C 14 (doneTok region rootLoc (par pZero canaryTargetN)) →
    NestedCanaryReturn initial := by
  intro inside region rootRead tokenRead
  have spine : IsLocSpine region := .child demoChan inside .root
  have packed : ∀ o ∈ C.present, ∀ σ : PSubst, nameAction.Models σ C.equations →
      ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ region)) := by
    intro o member σ solved y
    rw [live] at member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact no_row_at_other_depth .root spine (by decide +kernel) (rootRead σ solved) y
    · intro wrong
      have token := tokenRead σ solved
      rw [psubst_doneTok] at token
      exact absurd (nameLaws_heads (token.symm.trans wrong)) (by decide)
  obtain ⟨opening, freshOpening⟩ := close_fresh_exists label C 0 14 15
  obtain ⟨σ₀, solved₀⟩ := known
  have raw := closeRoot_admitted label C demoChan inside (par pZero canaryTargetN)
    0 14 15 rootRead tokenRead packed (by decide)
    (by rw [live]; decide) (by rw [live]; decide) solved₀ freshOpening
  let close : Candidate (Store.plain (embed label C) book) := ⟨closeRootAt opening 0 14 15, .closeRoot, rfl⟩
  let marks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 1 := #v[.cell none]
  have fresh : book.Fresh close.raw.selection := by
    change Disjoint ({15} : Finset ℕ) book.issued
    rw [issued]
    decide +kernel
  have admitted : routedStep.Admits close :=
    ⟨raw, Option.isSome_iff_exists.mpr ⟨marks, plan⟩, fresh⟩
  have sourceBody : predotU canarySource = inside := by decide +kernel
  have rootShape : predotU nestedCanarySource = pReflect demoChan inside := by decide +kernel
  have rootRows : RootCells label C [(0, nestedCanarySource)] := by
    refine ⟨by simp, ?_, ?_⟩
    · intro row member
      rw [List.mem_singleton] at member
      subst row
      exact ⟨by rw [live]; decide, by rw [rootShape]; exact rootRead⟩
    · intro slot member other σ known y same
      rw [live] at member
      rcases (show slot = 0 ∨ slot = 14 by simpa only [Finset.mem_insert, Finset.mem_singleton] using member)
        with rfl | rfl
      · exact other (by simp)
      · have stamp := tokenRead σ known
        rw [psubst_doneTok] at stamp
        exact absurd (nameLaws_heads (stamp.symm.trans same)) (by decide)
  have packedQuote : BagLaws (par pZero canaryTargetN) (predotU (pPar [canaryTargetN])) := by
    rw [ReflUniform.predotU_ground _ (by decide +kernel)]
    exact bagLaws_cooled_zero [canaryTargetN]
  obtain ⟨_, _, _, _, _, _, _, child⟩ := instance_canary_N
  have childReact : BagStep conventional canarySource (pPar [canaryTargetN]) :=
    .congruence (BagEq.refl _) child.2 (bagEq_pPar_singleton _).symm
  have formed : LabelForms ((Store.plain (embed label C) book) : Store ℕ) :=
    (congrArg LabelForms endpoint).mp (run_labelForms (policy := .whole) earlier covers forms)
  obtain ⟨_, _, _, _, rows, reaction⟩ := rootCells_owned_closeRoot_N
    (policy := .whole) book (pre := []) (post := []) (owner := 0) (d := 14) (made := 15)
    (x := demoChan) (P := canarySource) (R := pPar [canaryTargetN]) (ρ := opening)
    rootRows (by decide +kernel) (by rw [sourceBody]; exact tokenRead) packedQuote childReact formed admitted
  have sameResult : routedStep.toStep.result close admitted = ReflLocatedStep.Ownership.update close marks :=
    routed_result (policy := .whole) admitted plan
  rw [sameResult] at rows
  obtain ⟨returned, after⟩ :=
    append_update (policy := .whole) earlier endpoint (f := close) (out := marks) raw plan fresh
  let result := ReflLocatedStep.Ownership.update close marks
  have resultLive : result.raw.present = {15} := by
    change ((C.present \ ({0, 14} : Finset ℕ)) ∪ {15}) = {15}
    rw [live]
    decide
  have resultIssued : result.issued = Finset.range 16 := by
    change book.issued ∪ ({15} : Finset ℕ) = Finset.range 16
    rw [issued]
    decide +kernel
  have onlyResult : returned.last.raw.present = {15} :=
    (congrArg (fun s : Store ℕ => s.raw.present) after).trans resultLive
  refine ⟨returned, onlyResult, (congrArg Store.issued after).trans resultIssued, ?_, ?_, ?_, ?_⟩
  · intro o
    split
    · rename_i isMade
      subst o
      have mark : result.route 15 = some (.cell none) := by
        apply Ledger.mark_installed
        · change ([15] : List ℕ).Nodup
          decide
        · change (15, .cell none) ∈ ([15].zip marks.toList)
          decide
      exact (congrArg (fun s : Store ℕ => s.route 15) after).trans mark
    · rename_i other
      have covered := ReflLocatedStep.Ownership.run_covers returned covers
      by_contra marked
      have member := (covered.2 o).mpr (Option.isSome_iff_ne_none.mpr marked)
      rw [onlyResult, Finset.mem_singleton] at member
      exact other member
  · rw [after]
    exact solution_of_admitted raw
  · rw [after]
    exact (rows.rows (15, nestedCanaryTargetN) (by simp [nestedCanaryTargetN])).2
  · exact .congruence (bagEq_pPar_singleton nestedCanarySource).symm reaction
      (bagEq_pPar_singleton nestedCanaryTargetN)

set_option maxHeartbeats 6500000 in
private theorem return_nested_canary (commLabel : ℕ → Pattern) (knowledge : List (Pattern × Pattern))
    (covers : canaryCommittedView.ledger.Covers canaryCommittedView.raw.present)
    (forms : LabelForms (canaryStore commLabel knowledge))
    (solvable : ∃ σ : PSubst, nameAction.Models σ knowledge) :
    let commC := canaryConfig knowledge
    let inner := predotU nestedCanaryInner
    let inside := pReflect demoChan inner
    let region := childLoc rootLoc demoChan inside
    let grand := childLoc region demoChan inner
    let leftReduct := predot (applyDot nestedCanaryUnifier pZero)
    let reduct := predot (applyDot nestedCanaryUnifier nestedVarY)
    Reads commLabel commC 0 (atLoc (pReflect demoChan inside) rootLoc) →
    Reads commLabel commC 1 (atLoc (pReflect demoChan inner) region) →
    Reads commLabel commC 2 (pendingTok region rootLoc) →
    Reads commLabel commC 7 (atLoc leftReduct grand) →
    Reads commLabel commC 8 (atLoc reduct grand) →
    Reads commLabel commC 9 (doneTok grand region pZero) →
    NestedCanaryReturn (canaryStore commLabel knowledge) := by
  intro commC inner inside region grand leftReduct reduct readRoot readInner readParent readsSeven readsEight readsNine
  let committed := canaryStore commLabel knowledge
  let view₄ := canaryCommittedView
  let emptyOpen : PSubst := fun _ => none
  have spine : IsLocSpine region := .child demoChan inside .root
  obtain ⟨cool₁, ⟨cooledRun₁, afterCool₁⟩, knownCool₁, readsTen⟩ :=
    cool_owned (.nil committed) (label := commLabel) (C := commC) (book := committed.ledger)
      rfl grand region pZero leftReduct 9 7 10 ⟨4, 1, some 2⟩ readsNine readsSeven
      (by decide) (by change 9 ∈ view₄.raw.present; decide +kernel)
      (by change 7 ∈ view₄.raw.present; decide +kernel) (by change 10 ∉ view₄.raw.present; decide +kernel)
      (by change Disjoint ({10} : Finset ℕ) view₄.issued; decide +kernel)
      (by change routes view₄ .cool [9, 7] [] [10] = _; decide +kernel)
      solvable
  let coolRaw₁ := coolAt cool₁ (9 : ℕ) 7 10
  let packed₁ := ReflLocatedStep.Ownership.update
    (⟨coolRaw₁, .cool, rfl⟩ : Candidate committed) #v[.control ⟨4, 1, some 2⟩ .done]
  let view₅ := ReflLocatedStep.Ownership.update
    (⟨coolAt emptyOpen 9 7 10, .cool, rfl⟩ : Candidate view₄) #v[.control ⟨4, 1, some 2⟩ .done]
  let coolLabel₁ := (res commLabel commC coolRaw₁).label
  let coolC₁ := resConf commLabel commC coolRaw₁
  obtain ⟨cool₂, ⟨cooledRun₂, afterCool₂⟩, knownCool₂, readsEleven⟩ :=
    cool_owned cooledRun₁ (label := coolLabel₁) (C := coolC₁) (book := packed₁.ledger)
      afterCool₁ grand region (par pZero leftReduct) reduct 10 8 11 ⟨4, 1, some 2⟩
      readsTen (reads_retained readsEight coolRaw₁ (by change 8 ∉ [10]; decide))
      (by decide) (by change 10 ∈ view₅.raw.present; decide +kernel)
      (by change 8 ∈ view₅.raw.present; decide +kernel) (by change 11 ∉ view₅.raw.present; decide +kernel)
      (by change Disjoint ({11} : Finset ℕ) view₅.issued; decide +kernel)
      (by change routes view₅ .cool [10, 8] [] [11] = _; decide +kernel) knownCool₁
  let coolRaw₂ := coolAt cool₂ (10 : ℕ) 8 11
  let packed₂ := ReflLocatedStep.Ownership.update
    (⟨coolRaw₂, .cool, rfl⟩ : Candidate packed₁) #v[.control ⟨4, 1, some 2⟩ .done]
  let view₆ := ReflLocatedStep.Ownership.update
    (⟨coolAt emptyOpen 10 8 11, .cool, rfl⟩ : Candidate view₅) #v[.control ⟨4, 1, some 2⟩ .done]
  let coolLabel₂ := (res coolLabel₁ coolC₁ coolRaw₂).label
  let coolC₂ := resConf coolLabel₁ coolC₁ coolRaw₂
  let acc := par (par pZero leftReduct) reduct
  have keepBoth {row : ℕ} {body : Pattern} (reading : Reads commLabel commC row body)
      (older : row < 3) : Reads coolLabel₂ coolC₂ row body := by
    have no10 : row ∉ coolRaw₁.selection.made := by change row ∉ [10]; simp; omega
    have no11 : row ∉ coolRaw₂.selection.made := by change row ∉ [11]; simp; omega
    exact reads_retained (reads_retained reading coolRaw₁ no10) coolRaw₂ no11
  have keepRoot := keepBoth readRoot (by decide)
  have keepInner := keepBoth readInner (by decide)
  have keepPending := keepBoth readParent (by decide)
  have grandSpine : IsLocSpine grand := .child demoChan inner spine
  have allPacked : ∀ o ∈ coolC₂.present, ∀ σ : PSubst, nameAction.Models σ coolC₂.equations →
      ∀ y : Pattern, ¬ NameLaws (psubst σ (coolLabel₂ o)) (atLoc y (psubst σ grand)) := by
    intro o live σ solved y
    change o ∈ view₆.raw.present at live
    rw [show view₆.raw.present = ({0, 1, 2, 11} : Finset ℕ) by decide +kernel] at live
    simp only [Finset.mem_insert, Finset.mem_singleton] at live
    rcases live with rfl | rfl | rfl | rfl
    · exact no_row_at_other_depth .root grandSpine (by decide +kernel) (keepRoot σ solved) y
    · exact no_row_at_other_depth spine grandSpine (by decide +kernel) (keepInner σ solved) y
    · intro wrong
      have token := keepPending σ solved
      rw [psubst_pendingTok] at token
      exact absurd (nameLaws_heads (token.symm.trans wrong)) (by decide)
    · intro wrong
      have token := readsEleven σ solved
      rw [psubst_doneTok] at token
      exact absurd (nameLaws_heads (token.symm.trans wrong)) (by decide)
  obtain ⟨closeInner, closeInnerFresh⟩ := closeChild_fresh_exists coolLabel₂ coolC₂ 1 11 2 12 13
  obtain ⟨σ₁, solved₁⟩ := knownCool₂
  have rawCloseInner := ReflLocatedStep.child_close_admitted coolLabel₂ coolC₂
    demoChan inner acc region rootLoc 1 11 2 12 13 keepInner readsEleven keepPending allPacked
    (by decide) (by decide)
    (by change 1 ∈ view₆.raw.present ∧ 11 ∈ view₆.raw.present ∧ 2 ∈ view₆.raw.present; decide +kernel)
    (by change 12 ∉ view₆.raw.present ∧ 13 ∉ view₆.raw.present; decide +kernel)
    solved₁ closeInnerFresh
  let innerClose : Candidate packed₂ := ⟨closeChildAt closeInner 1 11 2 12 13, .closeChild, rfl⟩
  let innerMarks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 2 :=
    #v[.cell (some 2), .control ⟨2, 0, none⟩ .done]
  have innerPlan : innerClose.plan = some innerMarks := by
    change routes view₆ .closeChild [1, 11, 2] [] [12, 13] = some innerMarks
    decide +kernel
  have innerFresh : packed₂.ledger.Fresh innerClose.raw.selection := by
    change Disjoint ({12, 13} : Finset ℕ) view₆.issued
    decide +kernel
  obtain ⟨afterInner, innerEndpoint⟩ :=
    append_update (policy := .whole) cooledRun₂ afterCool₂ (f := innerClose) rawCloseInner innerPlan innerFresh
  let packedInner := ReflLocatedStep.Ownership.update innerClose innerMarks
  let view₇ := ReflLocatedStep.Ownership.update
    (⟨closeChildAt emptyOpen 1 11 2 12 13, .closeChild, rfl⟩ : Candidate view₆) innerMarks
  let innerLabel := (res coolLabel₂ coolC₂ innerClose.raw).label
  let innerC := resConf coolLabel₂ coolC₂ innerClose.raw
  have readOuterToken : Reads innerLabel innerC 13 (doneTok region rootLoc pZero) :=
    fun σ m => (closeChild_reads coolLabel₂ coolC₂ demoChan inner acc region rootLoc
      1 11 2 12 13 closeInner keepInner readsEleven keepPending (by decide) m).2.2
  have readInnerResult : Reads innerLabel innerC 12 (atLoc canaryTargetN region) := by
    intro σ m
    have observed := (closeChild_reads coolLabel₂ coolC₂ demoChan inner acc region rootLoc
      1 11 2 12 13 closeInner keepInner readsEleven keepPending (by decide) m).2.1
    have same : pPar [leftReduct, reduct] = canaryReduct := by decide +kernel
    have packed : BagLaws acc canaryReduct :=
      (bagLaws_cooled_zero [leftReduct, reduct]).trans (ReflQuotient.bagLaws_of_eq same)
    exact observed.trans (nameLaws_psubst σ ((locatedFrame_name.atLoc_iff _ _ _ _).mpr
      ⟨nameLaws_pFor_iff.mpr ⟨nameLaws_tProc packed, NameLaws.refl _, NameLaws.refl _⟩,
        NameLaws.refl _⟩))
  obtain ⟨cool₃, ⟨afterPack, packEndpoint⟩, knownPack, readOuter⟩ :=
    cool_owned afterInner (label := innerLabel) (C := innerC) (book := packedInner.ledger)
      innerEndpoint region rootLoc pZero canaryTargetN 13 12 14 ⟨2, 0, none⟩ readOuterToken readInnerResult
      (by decide) (by change 13 ∈ view₇.raw.present; decide +kernel)
      (by change 12 ∈ view₇.raw.present; decide +kernel) (by change 14 ∉ view₇.raw.present; decide +kernel)
      (by change Disjoint ({14} : Finset ℕ) view₇.issued; decide +kernel)
      (by change routes view₇ .cool [13, 12] [] [14] = _; decide +kernel)
      (solution_of_admitted rawCloseInner)
  let coolRaw₃ := coolAt cool₃ (13 : ℕ) 12 14
  let packed₃ := ReflLocatedStep.Ownership.update
    (⟨coolRaw₃, .cool, rfl⟩ : Candidate packedInner) #v[.control ⟨2, 0, none⟩ .done]
  let view₈ := ReflLocatedStep.Ownership.update
    (⟨coolAt emptyOpen 13 12 14, .cool, rfl⟩ : Candidate view₇) #v[.control ⟨2, 0, none⟩ .done]
  let outerLabel := (res innerLabel innerC coolRaw₃).label
  let outerC := resConf innerLabel innerC coolRaw₃
  have rootRead : Reads outerLabel outerC 0 (atLoc (pReflect demoChan inside) rootLoc) :=
    reads_retained (reads_retained keepRoot innerClose.raw (by change 0 ∉ [12, 13]; decide))
      coolRaw₃ (by change 0 ∉ [14]; decide)
  have live : view₈.raw.present = {0, 14} := by decide +kernel
  have issued : view₈.issued = Finset.range 15 := by decide +kernel
  have plan : routes view₈ .closeRoot [0, 14] [] [15] = some #v[.cell none] := by decide +kernel
  exact finish_canary_root afterPack outerLabel outerC packed₃.ledger packEndpoint covers forms live issued
    ((routes_eq_of_footprint (s := packed₃) (t := view₈) rfl rfl .closeRoot [0, 14] [] [15]).trans plan)
    knownPack rootRead readOuter

set_option maxHeartbeats 5000000 in
/-- A nested reflection runs from its encoded source to the source
listener on the routed step. The intermediate COMM keeps the inner
owner and parent; only return to the actual owners consumes the tickets.
All reads in the observations are at every solution, and the final
knowledge has a solution. -/
theorem routed_nested_canary_returns_to_source :
    let initial := ReflLocatedStep.Ownership.start (embed (encodeLabel nestedCanarySource) encodeConf)
    let inner := predotU nestedCanaryInner
    let l := childLoc rootLoc demoChan (pReflect demoChan inner)
    let g := childLoc l demoChan inner
    ∃ openedRun : routedStep.toStep.Run initial,
      nestedOpeningCheckpoint openedRun.last ∧ ScopeLinks openedRun.last ∧
      ∃ run : routedStep.toStep.Run openedRun.last,
        run.last.route 2 = some (.control ⟨2, 0, none⟩ .pending) ∧
        run.last.route 4 = none ∧
        run.last.route 9 = some (.control ⟨4, 1, some 2⟩ .done) ∧
        run.last.childRows 4 = {7, 8} ∧
        ScopeLinks run.last ∧
        (∀ σ : PSubst, nameAction.Models σ run.last.raw.knowledge →
          NameLaws (psubst σ (run.last.raw.label 7))
            (psubst σ (atLoc (predot (applyDot nestedCanaryUnifier pZero)) g)) ∧
          NameLaws (psubst σ (run.last.raw.label 8))
            (psubst σ (atLoc (predot (applyDot nestedCanaryUnifier nestedVarY)) g)) ∧
          NameLaws (psubst σ (run.last.raw.label 9)) (psubst σ (doneTok g l pZero))) ∧
        NestedCanaryReturn run.last := by
  intro initial inner region grand
  let label := encodeLabel nestedCanarySource
  let inside := predotU (pReflect demoChan nestedCanaryInner)
  let l := childLoc rootLoc demoChan inside
  have spine : IsLocSpine l := .child demoChan inside .root
  obtain ⟨_, _, clean, _⟩ := single_root_init nestedCanarySource []
  have readsRoot (σ : PSubst) (_ : nameAction.Models σ encodeConf.equations) :
      NameLaws (psubst σ (label 0)) (psubst σ (atLoc (pReflect demoChan inside) rootLoc)) := by
    have same : label 0 = atLoc (pReflect demoChan inside) rootLoc := by decide +kernel
    rw [same]
    exact NameLaws.refl _
  have rootSolved : nameAction.Models (fun _ => none) encodeConf.equations :=
    fun _ impossible => nomatch impossible
  obtain ⟨opening, freshOpen⟩ := open_fresh_exists label encodeConf 0 1 2
  have rawOpen := openRoot_admitted label encodeConf demoChan inside 0 1 2 readsRoot
    (clean rootLoc demoChan inside .root (Nat.zero_le _)) (by decide) (by decide) (by decide)
    rootSolved freshOpen
  let first : Candidate initial := ⟨openRootAt opening 0 1 2, .openRoot, rfl⟩
  let firstMarks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 2 :=
    #v[.cell (some 2), .control ⟨2, 0, none⟩ .pending]
  have firstPlan : first.plan = some firstMarks :=
    open_root_plan initial 0 1 2 (by decide +kernel) (start_unreserved _ _)
  have firstGood : routedStep.Admits first := by
    refine ⟨rawOpen, ?_, ?_⟩
    · rw [firstPlan]; rfl
    · change Disjoint ({1, 2} : Finset ℕ) {0}
      decide +kernel
  let middle := routedStep.toStep.result first firstGood
  have firstResult : middle = ReflLocatedStep.Ownership.update first firstMarks :=
    routed_result (policy := .whole) firstGood firstPlan
  -- Only the selected occurrence IDs are used in these two finite
  -- observations. Erase the symbolic openings in the observation,
  -- not in the admitted executions above and below.
  let emptyOpen : PSubst := fun _ => none
  let view₁ := ReflLocatedStep.Ownership.update
    (⟨openRootAt emptyOpen 0 1 2, .openRoot, rfl⟩ : Candidate initial) firstMarks
  let childLabel := (res label encodeConf (openRootAt opening 0 1 2)).label
  let childC := resConf label encodeConf (openRootAt opening 0 1 2)
  have readR (σ : PSubst) (solved : nameAction.Models σ childC.equations) :
      NameLaws (psubst σ (childLabel 1)) (psubst σ (atLoc inside l)) :=
    (ReflCorrespondence.openRoot_reads label encodeConf demoChan inside 0 1 2 opening
      readsRoot (by decide) solved).2.1
  have readT (σ : PSubst) (solved : nameAction.Models σ childC.equations) :
      NameLaws (psubst σ (childLabel 2)) (psubst σ (pendingTok l rootLoc)) :=
    (ReflCorrespondence.openRoot_reads label encodeConf demoChan inside 0 1 2 opening
      readsRoot (by decide) solved).2.2
  have readChild (σ : PSubst) (solved : nameAction.Models σ childC.equations) :
      NameLaws (psubst σ (childLabel 1))
        (psubst σ (atLoc (pReflect demoChan (predotU nestedCanaryInner)) l)) := by
    have same : inside = pReflect demoChan (predotU nestedCanaryInner) := by decide +kernel
    simpa only [← same] using readR σ solved
  have cleanBelow : CleanAboveDepth (locDepth l) childLabel childC := by
    apply cleanAboveDepth_of_subset (cleanAboveDepth_mono (Nat.zero_le _) clean) (fun _ h => info_known _ h)
    intro o live
    rcases (ReflCorrespondence.open_present label encodeConf opening 0 1 2 o).mp live with old | rfl | rfl
    · refine .inl ⟨old, ReflCorrespondence.open_label_old label encodeConf opening 0 1 2 ?_ ?_⟩
      · intro impossible
        rw [impossible] at old
        exact (by decide : (1 : ℕ) ∉ encodeConf.present) old
      · intro impossible
        rw [impossible] at old
        exact (by decide : (2 : ℕ) ∉ encodeConf.present) old
    · exact .inr ⟨l, spine, le_rfl, fun σ h => .inl ⟨_, by
        simpa only [ReflLocated.psubst_atLoc_any] using readR σ h⟩⟩
    · exact .inr ⟨l, spine, le_rfl, fun σ h => .inr (.inl ⟨_, by
        simpa only [ReflLocated.psubst_pendingTok] using readT σ h⟩)⟩
  let unifier : PSubst := fun v => if v = "y" then some nestedZeroTerm else none
  have knownUnifier : nameAction.Models unifier encodeConf.equations :=
    fun _ impossible => nomatch impossible
  obtain ⟨w, solved, agrees₁⟩ := ReflCorrespondence.openRoot_extends label encodeConf demoChan inside 0 1 2
    readsRoot (by decide) freshOpen knownUnifier
  obtain ⟨ρ, freshChild⟩ := openChild_fresh_exists childLabel childC 1 2 3 4
  have opened := openChild_admitted childLabel childC demoChan (predotU nestedCanaryInner) l rootLoc
    1 2 3 4 readChild readT (cleanBelow l _ _ spine le_rfl)
    (by change 1 ∈ ({0} ∪ {1, 2} : Finset ℕ); decide +kernel)
    (by change 2 ∈ ({0} ∪ {1, 2} : Finset ℕ); decide +kernel)
    (by decide)
    (by change 3 ∉ ({0} ∪ {1, 2} : Finset ℕ) ∧ 4 ∉ ({0} ∪ {1, 2} : Finset ℕ); decide +kernel)
    solved freshChild
  let second : Candidate middle := ⟨openChildAt ρ 1 2 3 4, .openChild, rfl⟩
  let secondMarks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 2 :=
    #v[.cell (some 4), .control ⟨4, 1, some 2⟩ .pending]
  have secondPlan : second.plan = some secondMarks := by
    change routes middle .openChild [] [1, 2] [3, 4] = some secondMarks
    rw [firstResult]
    change routes view₁ .openChild [] [1, 2] [3, 4] = some secondMarks
    exact ReflLocatedStep.Ownership.open_child_plan view₁ 1 2 3 4 ⟨2, 0, none⟩
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have secondGood : routedStep.Admits second := by
    refine ⟨opened, ?_, ?_⟩
    · rw [secondPlan]; rfl
    · change Disjoint ({3, 4} : Finset ℕ) middle.issued
      rw [firstResult]
      change Disjoint ({3, 4} : Finset ℕ) view₁.issued
      decide +kernel
  let view₂ := ReflLocatedStep.Ownership.update
    (⟨openChildAt emptyOpen 1 2 3 4, .openChild, rfl⟩ : Candidate view₁) secondMarks
  let openedRun : routedStep.toStep.Run initial := .cons first firstGood (.cons second secondGood (.nil _))
  have after₂ : openedRun.last = ReflLocatedStep.Ownership.update second secondMarks :=
    routed_result (policy := .whole) secondGood secondPlan
  refine ⟨openedRun, ?_, ReflLocatedStep.Ownership.reachable_scopeLinks _ openedRun, ?_⟩
  · rw [after₂]
    change nestedOpeningCheckpoint view₂
    unfold nestedOpeningCheckpoint
    decide +kernel
  let secondRaw := openChildAt ρ (1 : ℕ) 2 3 4
  let bodyLabel := (res childLabel childC secondRaw).label
  let bodyC := resConf childLabel childC secondRaw
  let a := predot (pFor nestedZeroTerm demoChan pZero)
  let b := predot (pFor nestedVarY demoChan nestedVarY)
  have readB (σ : PSubst) (m : nameAction.Models σ bodyC.equations) :
      NameLaws (psubst σ (bodyLabel 3)) (psubst σ (atLoc (par a b) grand)) :=
    (openChild_reads childLabel childC demoChan inner region rootLoc 1 2 3 4 ρ
      readChild readT (by decide) m).2.1
  have readP (σ : PSubst) (m : nameAction.Models σ bodyC.equations) :
      NameLaws (psubst σ (bodyLabel 4)) (psubst σ (pendingTok grand region)) :=
    (openChild_reads childLabel childC demoChan inner region rootLoc 1 2 3 4 ρ
      readChild readT (by decide) m).2.2
  have inBody₃ : 3 ∈ bodyC.present := by
    change 3 ∈ view₂.raw.present
    decide +kernel
  have inBody₄ : 4 ∈ bodyC.present := by
    change 4 ∈ view₂.raw.present
    decide +kernel
  obtain ⟨v, knownBody, agrees₂⟩ := openChild_extends childLabel childC
    demoChan inner region rootLoc 1 2 3 4 readChild readT
    (by change 1 ∈ view₁.raw.present; decide +kernel)
    (by change 2 ∈ view₁.raw.present; decide +kernel) freshChild solved
  obtain ⟨h, heatFresh⟩ := heat_fresh_exists bodyLabel bodyC 3 4 5 6
  have noFive : 5 ∉ bodyC.present := by change 5 ∉ view₂.raw.present; decide +kernel
  have noSix : 6 ∉ bodyC.present := by change 6 ∉ view₂.raw.present; decide +kernel
  have rawHeat := heatChild_admitted bodyLabel bodyC 3 4 5 6 inBody₃ inBody₄ (by decide)
    (by decide) noFive noSix knownBody
    (by simpa only [psubst_atLoc_any, psubst_par] using readB v knownBody)
    (by simpa only [psubst_pendingTok] using readP v knownBody) heatFresh
  let hot := ReflLocatedStep.Ownership.update second secondMarks
  let heat : Candidate hot := ⟨heatChildN h 3 4 5 6, .childHeat, rfl⟩
  let heatMarks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 2 := #v[.cell (some 4), .cell (some 4)]
  have heatPlan : heat.plan = some heatMarks := by
    change routes view₂ .childHeat [3] [4] [5, 6] = some heatMarks
    decide +kernel
  have heatLedgerFresh : hot.ledger.Fresh heat.raw.selection := by
    change Disjoint ({5, 6} : Finset ℕ) view₂.issued
    decide +kernel
  obtain ⟨heating, afterHeat⟩ :=
    append_update (policy := .whole) (.nil openedRun.last) after₂ (f := heat) rawHeat heatPlan heatLedgerFresh
  let hot' := ReflLocatedStep.Ownership.update heat heatMarks
  let view₃ := ReflLocatedStep.Ownership.update
    (⟨heatChildN emptyOpen 3 4 5 6, .childHeat, rfl⟩ : Candidate view₂) heatMarks
  let hotLabel := (res bodyLabel bodyC heat.raw).label
  let hotC := resConf bodyLabel bodyC heat.raw
  obtain ⟨u, knownHot, agrees₃⟩ := ReflCorrespondence.heat_extends bodyLabel bodyC 3 4 5 6
    inBody₃ inBody₄ grand region a b readB readP heatFresh knownBody
  have rootLiveBody : 0 ∈ bodyC.present := by change 0 ∈ view₂.raw.present; decide +kernel
  have rootLiveChild : 0 ∈ childC.present := by change 0 ∈ view₁.raw.present; decide +kernel
  have rootStable₂ : bodyLabel 0 = childLabel 0 :=
    openChild_label_old childLabel childC ρ 1 2 3 4 (by decide) (by decide)
  have rootStable₁ : childLabel 0 = label 0 :=
    ReflCorrespondence.open_label_old label encodeConf opening 0 1 2 (by decide) (by decide)
  have firstAgreement : NameLaws (psubst w (childLabel 0)) (psubst unifier (childLabel 0)) := by
    rw [rootStable₁]
    exact agrees₁ 0 (by decide)
  have secondAgreement : NameLaws (psubst v (bodyLabel 0)) (psubst unifier (bodyLabel 0)) := by
    rw [rootStable₂]
    exact (agrees₂ 0 rootLiveChild).trans firstAgreement
  have agrees := (agrees₃ 0 rootLiveBody).trans secondAgreement
  rw [rootStable₂, rootStable₁] at agrees
  have rawLabel : label 0 = atLoc (predotU nestedCanarySource) rootLoc := by decide +kernel
  rw [rawLabel, psubst_atLoc_any, psubst_atLoc_any] at agrees
  have below := ((locatedFrame_name.atLoc_iff _ _ _ _).mp agrees).1
  have leftSpine : SpineHasPattern nestedZeroTerm (predotU nestedCanarySource) :=
    .reflect _ (.reflect _ (.parLeft _ (.guard _ _)))
  have rightSpine : SpineHasPattern nestedVarY (predotU nestedCanarySource) :=
    .reflect _ (.reflect _ (.parRight _ (.guard _ _)))
  have substEqual : psubst unifier nestedZeroTerm = psubst unifier nestedVarY := rfl
  have unifies : NameLaws (psubst u nestedZeroTerm) (psubst u nestedVarY) :=
    (spineHasPattern_nameLaws leftSpine below).trans
      ((nameLaws_of_eq substEqual).trans (spineHasPattern_nameLaws rightSpine below).symm)
  have leftRow (σ : PSubst) (m : nameAction.Models σ hotC.equations) :
      NameLaws (psubst σ (hotLabel 5)) (psubst σ (atLoc a grand)) :=
    (heatChild_reads_determinately bodyLabel bodyC h 3 4 (by decide) a b grand readB m).1
  have rightRow (σ : PSubst) (m : nameAction.Models σ hotC.equations) :
      NameLaws (psubst σ (hotLabel 6)) (psubst σ (atLoc b grand)) :=
    (heatChild_reads_determinately bodyLabel bodyC h 3 4 (by decide) a b grand readB m).2
  have stillPending (σ : PSubst) (m : nameAction.Models σ hotC.equations) :
      NameLaws (psubst σ (hotLabel 4)) (psubst σ (pendingTok grand region)) := by
    change NameLaws (psubst σ ((res bodyLabel bodyC (heatChildN h 3 4 5 6)).label 4)) _
    rw [ReflCorrespondence.heat_label_old bodyLabel bodyC h 3 4 5 6 (by decide) (by decide)]
    exact readP σ (info_known (heatChildN h 3 4 5 6) m)
  obtain ⟨c, commFresh⟩ := ReflCorrespondence.commit_fresh_exists hotLabel hotC 5 6 4 7 8 9
  have apart : Apart nestedZeroTerm pZero nestedVarY nestedVarY := by
    constructor <;> intro v present <;>
      simp [nestedZeroTerm, nestedVarY, tProc, pZero, pvars, binders,
        MeTTaOperationsComm.pvars.pvarsList] at present ⊢
  obtain ⟨rawComm, readsComm⟩ :=
    ReflCorrespondence.child_commit hotLabel hotC nestedZeroTerm nestedVarY demoChan pZero
      nestedVarY grand region nestedCanaryUnifier nestedCanaryUnifier_gp
      apart (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      5 6 4 7 8 9 leftRow rightRow stillPending (by decide) (by decide)
      (by change 5 ∈ view₃.raw.present ∧ 6 ∈ view₃.raw.present ∧ 4 ∈ view₃.raw.present; decide +kernel)
      (by change 7 ∉ view₃.raw.present ∧ 8 ∉ view₃.raw.present ∧ 9 ∉ view₃.raw.present; decide +kernel)
      knownHot unifies commFresh
  let comm : Candidate hot' := ⟨commChildAt c 5 6 4 7 8 9, .childComm, rfl⟩
  let commMarks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 3 :=
    #v[.cell (some 4), .cell (some 4), .control ⟨4, 1, some 2⟩ .done]
  have commPlan : comm.plan = some commMarks := by
    change routes view₃ .childComm [5, 6, 4] [] [7, 8, 9] = some commMarks
    decide +kernel
  have commLedgerFresh : hot'.ledger.Fresh comm.raw.selection := by
    change Disjoint ({7, 8, 9} : Finset ℕ) view₃.issued
    decide +kernel
  obtain ⟨run, afterComm⟩ :=
    append_update (policy := .whole) heating afterHeat (f := comm) rawComm commPlan commLedgerFresh
  let view₄ := canaryCommittedView
  refine ⟨run, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [afterComm]; change view₄.route 2 = _; decide +kernel
  · rw [afterComm]; change view₄.route 4 = _; decide +kernel
  · rw [afterComm]; change view₄.route 9 = _; decide +kernel
  · rw [afterComm]; change view₄.childRows 4 = _; decide +kernel
  · have linked := ReflLocatedStep.Ownership.reachable_scopeLinks _ (openedRun.append run)
    rw [openedRun.last_append run] at linked
    exact linked
  · rw [afterComm]
    intro σ solvedResult
    obtain ⟨_, left, right, token⟩ := readsComm σ solvedResult
    exact ⟨left, right, token⟩
  let commLabel := (res hotLabel hotC comm.raw).label
  let commC := resConf hotLabel hotC comm.raw
  have cut : run.last = canaryStore commLabel commC.equations := afterComm
  have covered := ReflLocatedStep.Ownership.run_covers (openedRun.append run) (Ledger.root_covers _)
  rw [openedRun.last_append run, cut] at covered
  have formed := run_labelForms (policy := .whole) (openedRun.append run) (Ledger.root_covers _)
    (start_labelForms _ (fun _ _ => ⟨predotU nestedCanarySource, rfl⟩))
  rw [openedRun.last_append run, cut] at formed
  rw [cut]
  have keepBeforePack {row : ℕ} {shape : Pattern} (reading : Reads childLabel childC row shape)
      (older : row < 3) : Reads commLabel commC row shape := by
    have no34 : row ∉ secondRaw.selection.made := by change row ∉ [3, 4]; simp; omega
    have no56 : row ∉ heat.raw.selection.made := by change row ∉ [5, 6]; simp; omega
    have no789 : row ∉ comm.raw.selection.made := by change row ∉ [7, 8, 9]; simp; omega
    exact reads_retained (reads_retained (reads_retained reading secondRaw no34) heat.raw no56) comm.raw no789
  exact return_nested_canary commLabel commC.equations covered formed (solution_of_admitted rawComm)
    (keepBeforePack (reads_retained readsRoot first.raw (by change 0 ∉ [1, 2]; decide)) (by decide))
    (keepBeforePack readChild (by decide)) (keepBeforePack readT (by decide))
    (fun σ m => (readsComm σ m).2.1) (fun σ m => (readsComm σ m).2.2.1)
    (fun σ m => (readsComm σ m).2.2.2)

/-- An authored source opening retains its owner and supplies the selected
child's text without exposing the child row in a different region. The
pending token itself is not a process row. -/
theorem authored_opening_sets_the_child_view (body : Pattern) :
    let source := pReflect demoChan body
    let initial := startAuthored (embed (encodeLabel source) encodeConf) (fun _ => source)
    ∃ run : (withAuthored .physical).Run initial,
      run.word.length = 1 ∧
      run.last.authoredRow none 0 = some source ∧
      run.last.authoredRow (some 2) 1 = some body ∧
      run.last.authoredRow none 1 = none ∧
      run.last.authoredRow (some 2) 2 = none ∧
      run.last.route 2 = some (.control ⟨2, 0, none⟩ .pending) ∧
      AuthoredReads run.last ∧ ScopeLinks run.last ∧
      ∃ loc, ∀ σ : PSubst, nameAction.Models σ run.last.raw.knowledge →
        NameLaws (psubst σ (run.last.raw.label 1)) (psubst σ (atLoc (predotU body) loc)) := by
  dsimp only
  let source := pReflect demoChan body
  let label := encodeLabel source
  let initial := startAuthored (embed label encodeConf) (fun _ => source)
  have reads : Reads label encodeConf 0 (atLoc (pReflect demoChan (predotU body)) rootLoc) := by
    intro σ _
    change NameLaws (psubst σ (atLoc (predotU source) rootLoc)) _
    rw [show predotU source = pReflect demoChan (predotU body) from predotU_pReflect _ _]
    exact NameLaws.refl _
  let ι : PSubst := fun _ => none
  have known : nameAction.Models ι encodeConf.equations := nameAction.models_nil _
  obtain ⟨ρ, fresh⟩ := open_fresh_exists label encodeConf 0 1 2
  have raw := ReflCorrespondence.openRoot_admitted label encodeConf demoChan (predotU body) 0 1 2 reads
    ((single_root_init source []).2.2.1 rootLoc demoChan (predotU body) .root (Nat.zero_le _))
    (by decide) (by decide) (by decide) known fresh
  let f : Candidate initial := ⟨openRootAt ρ 0 1 2, .openRoot, rfl⟩
  let tags : Vector (ReflLocatedStep.Ownership.Mark ℕ) 2 := #v[.cell (some 2), .control ⟨2, 0, none⟩ .pending]
  have route : f.plan = some tags := by
    apply open_root_plan
    · rfl
    · exact start_unreserved (embed label encodeConf) 0
  have freshSlots : initial.ledger.Fresh f.raw.selection := by
    change Disjoint ({1, 2} : Finset ℕ) {0}
    decide
  have base : physicalStep.Admits f :=
    ReflLocatedStep.Ownership.physical_admits_of_whole ⟨raw, route ▸ rfl, freshSlots⟩
  let texts : Vector (Option Pattern) 2 := #v[some body, none]
  let equations := [(psubst ρ ReflLocated.reflP, predotU body)]
  have record : f.authoredPlan = some (texts, equations) := rfl
  obtain ⟨σ, solves⟩ := solution_of_admitted raw
  have symbol := (ReflCorrespondence.open_reading label encodeConf demoChan (predotU body) 0 1 2 ρ reads solves).2
  have tells : nameAction.Models σ equations := by
    intro e member
    obtain rfl := List.mem_singleton.mp member
    exact symbol
  have admitted := authored_admits_of_models .physical base record solves tells
  let run : (withAuthored .physical).Run initial := .cons f admitted (.nil _)
  have endAt : run.last = ReflLocatedStep.Ownership.update f tags (some equations) (some texts) :=
    authored_routed_result .physical admitted route record
  have views := reachable_authored (policy := .physical) (embed label encodeConf) (fun _ => source)
    (fun _ _ => rfl) run
  have childText : run.last.authoredRow (some 2) 1 = some body := by rw [endAt]; rfl
  obtain ⟨loc, _, readBody⟩ := Store.authoredRow_readback childText views.1 views.2.2.2
  refine ⟨run, rfl, ?_, childText, ?_, ?_, ?_, views.1, views.2.2.1, loc, readBody⟩ <;> rw [endAt] <;> rfl

/-- Both actual openings reserve their own source rows. -/
theorem routed_nested_openings_retain_both_owners :
    let initial := ReflLocatedStep.Ownership.start (embed (encodeLabel nestedCanarySource) encodeConf)
    ∃ run : routedStep.toStep.Run initial, nestedOpeningCheckpoint run.last ∧ ScopeLinks run.last := by
  obtain ⟨run, physical, linked, _⟩ := routed_nested_canary_returns_to_source
  exact ⟨run, physical, linked⟩

/-- The existing nested source reaction still runs to its packed
listener on the physical view, with its exact return readback. -/
theorem physical_nested_canary_returns_to_source :
    NestedCanaryReturn
      (ReflLocatedStep.Ownership.start (embed (encodeLabel nestedCanarySource) encodeConf)) .physical := by
  obtain ⟨opened, _, _, committed, _, _, _, _, _, _, returned, checks⟩ :=
    routed_nested_canary_returns_to_source
  let whole := opened.append (committed.append returned)
  have same : (usePhysicalGuards whole).last = returned.last :=
    (usePhysicalGuards_last whole).trans
      ((opened.last_append (committed.append returned)).trans (committed.last_append returned))
  refine ⟨usePhysicalGuards whole, ?_⟩
  rw [same]
  exact checks

/-- Two identical root reflections still have different owners.
The second one is blocked at every opening by the global guard, but
the same reached prefix really can open it under the physical guard
policy. The new live tickets share a symbolic description, not a key. -/
theorem equal_descriptions_block_separate_open_owners :
    let source := par ownerRow ownerRow
    let initial := ReflLocatedStep.Ownership.start (embed (encodeLabel source) encodeConf)
    ∃ (label : ℕ → Pattern) (C : Configuration Pattern ℕ)
        (ledger : Ledger ℕ ReflLocatedStep.Ownership.Phase) (run : routedStep.toStep.Run initial),
      let reached : Store ℕ := (Store.plain (embed label C) ledger)
      run.last = reached ∧ reached.route 4 = some (.control ⟨4, 1, none⟩ .pending) ∧
      reached.reserved 1 = {4} ∧ reached.reserved 2 = ∅ ∧
      routes reached .openRoot [] [2] [5, 6] =
        some #v[.cell (some 6), .control ⟨6, 2, none⟩ .pending] ∧
      Disjoint ({5, 6} : Finset ℕ) reached.issued ∧
      (∀ ρ : PSubst, ¬ routedStep.Admits
        (⟨openRootAt ρ 2 5 6, .openRoot, rfl⟩ : Candidate reached)) ∧
      ∃ extra : physicalStep.toStep.Run (usePhysicalGuards run).last,
        let both := extra.last
        both.route 4 = some (.control ⟨4, 1, none⟩ .pending) ∧
        both.route 6 = some (.control ⟨6, 2, none⟩ .pending) ∧
        ScopeLinks both ∧
        (∃ σ : PSubst, nameAction.Models σ both.raw.knowledge) ∧
        ∀ σ : PSubst, nameAction.Models σ both.raw.knowledge →
          NameLaws (psubst σ (both.raw.label 4)) (psubst σ (both.raw.label 6)) := by
  intro source initial
  let label := encodeLabel source
  let inside := predotU liveBody
  let noOpening : PSubst := fun _ => none
  have solved : nameAction.Models noOpening encodeConf.equations :=
    fun _ impossible => nomatch impossible
  obtain ⟨_, root, clean, _⟩ := single_root_init source []
  obtain ⟨ρ, fresh⟩ := rootHeat_fresh_exists label encodeConf 0 1 2
  have pair : NameLaws (psubst noOpening (label 0))
      (atLoc (par (predotU ownerRow) (predotU ownerRow)) rootLoc) := by
    rw [psubst_none]
    exact NameLaws.refl _
  have rawHeat := rootHeat_admitted label encodeConf 0 1 2
    (by decide) (by decide) (by decide) (by decide) solved pair fresh
  let heat : Candidate initial := ⟨rootHeatAt ρ 0 1 2, .rootHeat, rfl⟩
  let heatMarks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 2 := #v[.cell none, .cell none]
  have heatPlan : heat.plan = some heatMarks := by
    change routes initial .rootHeat [0] [] [1, 2] = some heatMarks
    decide +kernel
  have heatFresh : initial.ledger.Fresh heat.raw.selection := by
    change Disjoint ({1, 2} : Finset ℕ) {0}
    decide +kernel
  obtain ⟨heatedRun, heatedAt⟩ :=
    append_update (policy := .whole) (.nil initial) rfl (f := heat) rawHeat heatPlan heatFresh
  let heated := ReflLocatedStep.Ownership.update heat heatMarks
  let view := ReflLocatedStep.Ownership.update
    (⟨rootHeatAt noOpening 0 1 2, .rootHeat, rfl⟩ : Candidate initial) heatMarks
  let rootsLabel := (res label encodeConf heat.raw).label
  let rootsC := resConf label encodeConf heat.raw
  have roots : RootCells rootsLabel rootsC [(1, ownerRow), (2, ownerRow)] :=
    (rootCells_heat (pre := []) (post := []) root rawHeat).1
  have emptyChildren : CleanChildren rootsLabel rootsC :=
    cleanChildren_of_rootRule clean rawHeat (r := FiniteProgram.heatRule) rfl
  have reads (o : ℕ) (member : (o, ownerRow) ∈ ([(1, ownerRow), (2, ownerRow)] : List (ℕ × Pattern))) :
      Reads rootsLabel rootsC o (atLoc (pReflect demoChan inside) rootLoc) := by
    have shape : predotU ownerRow = pReflect demoChan inside := by decide +kernel
    simpa only [Reads, ← shape] using (roots.rows (o, ownerRow) member).2
  obtain ⟨σ, known⟩ := solution_of_admitted rawHeat
  obtain ⟨opening, opener⟩ := open_fresh_exists rootsLabel rootsC 1 3 4
  have rawOpen :=
    openRoot_admitted rootsLabel rootsC demoChan inside 1 3 4 (reads 1 (by simp))
      (emptyChildren rootLoc demoChan inside .root (Nat.zero_le _))
      (by change 1 ∈ view.raw.present; decide +kernel) (by decide)
      (by change 3 ∉ view.raw.present ∧ 4 ∉ view.raw.present; decide +kernel) known opener
  let birth : Candidate heated := ⟨openRootAt opening 1 3 4, .openRoot, rfl⟩
  let birthMarks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 2 :=
    #v[.cell (some 4), .control ⟨4, 1, none⟩ .pending]
  have birthPlan : birth.plan = some birthMarks := by
    change routes view .openRoot [] [1] [3, 4] = some birthMarks
    decide +kernel
  have birthFresh : heated.ledger.Fresh birth.raw.selection := by
    change Disjoint ({3, 4} : Finset ℕ) view.issued
    decide +kernel
  obtain ⟨run, endpoint⟩ :=
    append_update (policy := .whole) heatedRun heatedAt (f := birth) rawOpen birthPlan birthFresh
  let reached := ReflLocatedStep.Ownership.update birth birthMarks
  let cut := ReflLocatedStep.Ownership.update
    (⟨openRootAt noOpening 1 3 4, .openRoot, rfl⟩ : Candidate view) birthMarks
  let resultLabel := (res rootsLabel rootsC birth.raw).label
  let resultC := resConf rootsLabel rootsC birth.raw
  have pending : reached.route 4 = some (.control ⟨4, 1, none⟩ .pending) := by
    change cut.route 4 = _
    decide +kernel
  have covers : reached.ledger.Covers reached.raw.present :=
    (congrArg (fun s : Store ℕ => s.ledger.Covers s.raw.present) endpoint).mp
      (ReflLocatedStep.Ownership.run_covers run (Ledger.root_covers _))
  have invariant : ScopeLinks reached :=
    (congrArg ScopeLinks endpoint).mp (ReflLocatedStep.Ownership.reachable_scopeLinks _ run)
  have available : reached.available none 2 := by
    change cut.available none 2
    decide +kernel
  have unused : Disjoint ({5, 6} : Finset ℕ) reached.issued := by
    change Disjoint _ cut.issued
    decide +kernel
  let newMarks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 2 :=
    #v[.cell (some 6), .control ⟨6, 2, none⟩ .pending]
  have newPlan : routes reached .openRoot [] [2] [5, 6] = some newMarks :=
    open_root_plan reached 2 5 6 available.1 available.2
  have secondRow : Reads resultLabel resultC 2 (atLoc (pReflect demoChan inside) rootLoc) :=
    reads_retained (reads 2 (by simp)) birth.raw (by change 2 ∉ [3, 4]; decide)
  have firstToken : Reads resultLabel resultC 4 (pendingTok (childLoc rootLoc demoChan inside) rootLoc) :=
    fun w models => (ReflCorrespondence.openRoot_reads rootsLabel rootsC demoChan inside 1 3 4 opening
      (reads 1 (by simp)) (by decide) (σ := w) models).2.2
  refine ⟨resultLabel, resultC, reached.ledger, run, endpoint, pending,
    ReflLocatedStep.Ownership.reserved_eq_singleton covers invariant pending, available.2, newPlan, unused, ?_, ?_⟩
  · intro otherOpening rejected
    exact ReflCorrespondence.openRoot_refused_by_pending resultLabel resultC demoChan inside 2 4 5 6
      otherOpening (by change 4 ∈ cut.raw.present; decide +kernel) secondRow firstToken rejected.1
  · obtain ⟨nextOpening, freshOpening⟩ := open_fresh_exists resultLabel resultC 2 5 6
    let second : Candidate reached := ⟨openRootAt nextOpening 2 5 6, .openRoot, rfl⟩
    have admitted : physicalStep.Admits second :=
      ReflCorrespondence.openRoot_physical_admitted resultLabel resultC reached.ledger
        demoChan inside 2 5 6 nextOpening invariant covers available (by decide) unused
        secondRow (solution_of_admitted rawOpen) freshOpening
    let localPrefix := usePhysicalGuards run
    have sameCut : localPrefix.last = reached := (usePhysicalGuards_last run).trans endpoint
    obtain ⟨extra, after⟩ := append_update (policy := .physical) (.nil localPrefix.last) sameCut
      (f := second) admitted.1 newPlan admitted.2.2
    let viewAfter := ReflLocatedStep.Ownership.update
      (⟨openRootAt noOpening 2 5 6, .openRoot, rfl⟩ : Candidate cut) newMarks
    refine ⟨extra, ?_, ?_, ?_, ?_, ?_⟩
    · rw [after]
      change viewAfter.route 4 = _
      decide +kernel
    · rw [after]
      change viewAfter.route 6 = _
      decide +kernel
    · have full := ReflLocatedStep.Ownership.reachable_scopeLinks _ (localPrefix.append extra)
      rw [localPrefix.last_append extra] at full
      exact full
    · obtain ⟨_, w, solves⟩ := admitted.1.2.2.1
      rw [after]
      exact ⟨w, solves⟩
    · rw [after]
      intro w solves
      have earlier := reads_retained firstToken second.raw (by change 4 ∉ [5, 6]; decide) w solves
      have later := (ReflCorrespondence.openRoot_reads resultLabel resultC demoChan inside 2 5 6
        nextOpening secondRow (by decide) (σ := w) solves).2.2
      exact earlier.trans later.symm

/-- The actual one-row source encoding heats to two inputs whose
open bags match at `QN`, but not in conventional COMM. The written
policy rejects exactly that selected pair, not the heating. -/
theorem reachable_scoped_comm_exceeds_conventional :
    let source := par inputY inputAB
    let initial := ReflLocatedStep.Ownership.start (embed (encodeLabel source) encodeConf)
    (∀ output, ¬ BagStep conventional source output) ∧
      ∃ (cut : Store ℕ) (warm : physicalStep.toStep.Run initial),
        warm.last = cut ∧
        ∃ f : Candidate cut, f.op = .rootComm ∧ f.raw.selection.taken = [1, 2] ∧
          f.raw.selection.made = [3, 4] ∧
          ∃ admitted : physicalStep.Admits f,
            let after := physicalStep.toStep.result f admitted
            ¬ (withWrittenComm .physical (rootWrittenRows [(1, inputY), (2, inputAB)])).Admits f ∧
            after.raw.present = {3, 4} ∧ LabelForms after ∧
            (∃ σ : PSubst, nameAction.Models σ after.raw.knowledge) ∧
            ∀ σ : PSubst, nameAction.Models σ after.raw.knowledge →
              NameLaws (psubst σ (after.raw.label 3)) (atLoc pZero rootLoc) ∧
              NameLaws (psubst σ (after.raw.label 4)) (atLoc pZero rootLoc) := by
  intro source initial
  refine ⟨fun output => (non_ground_bag_pattern_control_QN.2.2 conventional output).1, ?_⟩
  let label := encodeLabel source
  let noOpening : PSubst := fun _ => none
  have authored : label 0 = atLoc (par inputY inputAB) rootLoc := by decide +kernel
  have inputs : Reads label encodeConf 0 (atLoc (par inputY inputAB) rootLoc) :=
    fun σ _ => nameLaws_of_eq (congrArg (psubst σ) authored)
  have known : nameAction.Models yToB encodeConf.equations :=
    fun _ impossible => nomatch impossible
  obtain ⟨opening, freshHeat⟩ := rootHeat_fresh_exists label encodeConf 0 1 2
  have pair : NameLaws (psubst yToB (label 0))
      (atLoc (par (psubst yToB inputY) (psubst yToB inputAB)) rootLoc) := by
    simpa only [psubst_atLoc_any, psubst_par, psubst_rootLoc] using inputs yToB known
  have rawHeat := rootHeat_admitted label encodeConf 0 1 2
    (by decide) (by decide) (by decide) (by decide) known pair freshHeat
  let heat : Candidate initial := ⟨rootHeatAt opening 0 1 2, .rootHeat, rfl⟩
  let heatMarks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 2 := #v[.cell none, .cell none]
  have heatPlan : heat.plan = some heatMarks := by
    change routes initial .rootHeat [0] [] [1, 2] = some heatMarks
    decide +kernel
  have heatUnused : initial.ledger.Fresh heat.raw.selection := by
    change Disjoint ({1, 2} : Finset ℕ) {0}
    decide +kernel
  obtain ⟨warm, warmed⟩ := append_update (policy := .physical) (.nil initial) rfl
    (f := heat) rawHeat heatPlan heatUnused
  let heated := ReflLocatedStep.Ownership.update heat heatMarks
  let dry := ReflLocatedStep.Ownership.update
    (⟨rootHeatAt noOpening 0 1 2, .rootHeat, rfl⟩ : Candidate initial) heatMarks
  let heatedLabel := (res label encodeConf heat.raw).label
  let heatedC := resConf label encodeConf heat.raw
  have readsLeft : Reads heatedLabel heatedC 1 (atLoc inputY rootLoc) :=
    fun σ models => (rootHeat_reads_mixed label encodeConf opening 0 (by decide)
      inputY inputAB inputs (σ := σ) models).1
  have readsRight : Reads heatedLabel heatedC 2 (atLoc inputAB rootLoc) :=
    fun σ models => (rootHeat_reads_mixed label encodeConf opening 0 (by decide)
      inputY inputAB inputs (σ := σ) models).2
  obtain ⟨w, solvesHeated, agrees⟩ := rootHeat_extends label encodeConf 0 1 2
    (by decide) inputY inputAB inputs freshHeat known
  have active := agrees 0 (by decide)
  rw [authored, psubst_atLoc_any, psubst_atLoc_any] at active
  have sameInputs := ((locatedFrame_name.atLoc_iff _ _ _ _).mp active).1
  have leftSpine : SpineHasPattern patY (par inputY inputAB) := .parLeft _ (.guard _ _)
  have rightSpine : SpineHasPattern patAB (par inputY inputAB) := .parRight _ (.guard _ _)
  have modulo : NameLaws (psubst w patY) (psubst w patAB) :=
    (spineHasPattern_nameLaws leftSpine sameInputs).trans
      ((by decide +kernel : NameLaws (psubst yToB patY) (psubst yToB patAB)).trans
        (spineHasPattern_nameLaws rightSpine sameInputs).symm)
  obtain ⟨ρ, freshComm⟩ := rootComm_fresh_exists heatedLabel heatedC 1 2 3 4
  have rawComm := rootComm_admitted_mixed heatedLabel heatedC patY patAB demoChan pZero pZero 1 2 3 4
    readsLeft readsRight (by decide) (by decide)
    (by change 1 ∈ dry.raw.present; decide +kernel) (by change 2 ∈ dry.raw.present; decide +kernel)
    (by change 3 ∉ dry.raw.present; decide +kernel) (by change 4 ∉ dry.raw.present; decide +kernel)
    solvesHeated modulo freshComm
  let f : Candidate heated := ⟨rootCommAt ρ 1 2 3 4, .rootComm, rfl⟩
  let marks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 2 := #v[.cell none, .cell none]
  have plan : f.plan = some marks := by
    change routes dry .rootComm [1, 2] [] [3, 4] = some marks
    decide +kernel
  have unused : heated.ledger.Fresh f.raw.selection := by
    change Disjoint ({3, 4} : Finset ℕ) dry.issued
    decide +kernel
  have admitted : physicalStep.Admits f :=
    ⟨rawComm, Option.isSome_iff_exists.mpr ⟨marks, plan⟩, unused⟩
  have initialForms : LabelForms initial := start_labelForms _ (fun _ _ => ⟨predotU source, rfl⟩)
  have heatedForms : LabelForms heated :=
    (congrArg LabelForms warmed).mp
      (run_labelForms (policy := .physical) warm (Ledger.root_covers _) initialForms)
  have covered : heated.ledger.Covers heated.raw.present :=
    (congrArg (fun s : Store ℕ => s.ledger.Covers s.raw.present) warmed).mp
      (ReflLocatedStep.Ownership.run_covers (policy := .physical) warm (Ledger.root_covers _))
  refine ⟨heated, warm, warmed, f, rfl, rfl, rfl, admitted, ?_, ?_,
    result_labelForms (policy := .physical) admitted covered heatedForms, ?_, ?_⟩
  · intro licensed
    have permit := (written_comm_admits_iff .physical _ f).mp licensed |>.2
    change (ReflLocatedStep.Ownership.writtenBinding
      (rootWrittenRows [(1, inputY), (2, inputAB)] heated) f).isSome = true at permit
    rw [writtenBinding_root _ (f := f) (left := inputY) (right := inputAB) rfl rfl rfl rfl] at permit
    exact (by decide +kernel : ¬ (writtenComm inputY inputAB).isSome = true) permit
  · rw [routed_result (policy := .physical) admitted plan]
    change (ReflLocatedStep.Ownership.update
      (⟨rootCommAt noOpening 1 2 3 4, .rootComm, rfl⟩ : Candidate dry) marks).raw.present = _
    decide +kernel
  · rw [routed_result (policy := .physical) admitted plan]
    exact solution_of_admitted rawComm
  · rw [routed_result (policy := .physical) admitted plan]
    intro σ solves
    obtain ⟨_, _, _, left, right⟩ := rootComm_reads_raw heatedLabel heatedC patY patAB
      demoChan demoChan pZero pZero 1 2 3 4 readsLeft readsRight (by decide) ρ (σ := σ) solves
    simpa only [psubst_atLoc_any, psubst_pZero, psubst_rootLoc] using ⟨left, right⟩

/-- The written policy does not require grounding. It executes heating and
an open COMM, publishes one residual name in both continuations, and
preserves the nested guard inside the first continuation. -/
theorem reachable_written_comm_reads_residual :
    let X := MeTTaCalculus.Corrected.ResidualControls.X
    let Y := MeTTaCalculus.Corrected.ResidualControls.Y
    let left := pFor X demoChan (par X Readiness.inner)
    let right := pFor Y demoChan Y
    let source := par left right
    let init := ReflLocatedStep.Ownership.start (embed (encodeLabel source) encodeConf)
    let rows := [(1, left), (2, right)]
    let newRows := [(3, par (nQuote Y) Readiness.inner), (4, nQuote Y)]
    ∃ run : (withWrittenComm .physical (rootWrittenRows rows)).Run init,
      run.word.length = 2 ∧
      RootCells run.last.raw.label ⟨run.last.raw.knowledge, run.last.raw.present⟩ newRows ∧
      BagStep conventional (rootBagProcess rows) (rootBagProcess newRows) := by
  dsimp only
  let X := MeTTaCalculus.Corrected.ResidualControls.X
  let Y := MeTTaCalculus.Corrected.ResidualControls.Y
  let A := par X Readiness.inner
  let l := pFor X demoChan A
  let r := pFor Y demoChan Y
  let src := par l r
  let label := encodeLabel src
  let init := ReflLocatedStep.Ownership.start (embed label encodeConf)
  let rows := [(1, l), (2, r)]
  let view := rootWrittenRows rows
  let τ : PSubst := fun v => if v = "X" then some Y else none
  have solvedInit (σ : PSubst) : nameAction.Models σ encodeConf.equations :=
    fun _ m => absurd m List.not_mem_nil
  have original : Reads label encodeConf 0 (atLoc (par (predotU l) (predotU r)) rootLoc) := by
    intro σ _
    change NameLaws (psubst σ (atLoc (predotU (par l r)) rootLoc)) _
    rw [predotU_par]
    exact NameLaws.refl _
  have heating : NameLaws (psubst (fun _ => none) (label 0))
      (atLoc (par (predotU l) (predotU r)) rootLoc) :=
    (original _ (solvedInit _)).trans (nameLaws_of_eq (psubst_none _))
  obtain ⟨openHeat, heatFresh⟩ := rootHeat_fresh_exists label encodeConf 0 1 2
  let heat : Candidate init := ⟨rootHeatAt openHeat 0 1 2, .rootHeat, rfl⟩
  let heatMarks : Vector (ReflLocatedStep.Ownership.Mark ℕ) 2 := #v[.cell none, .cell none]
  have rawHeat := rootHeat_admitted label encodeConf 0 1 2
    (by decide) (by decide) (by decide) (by decide) (solvedInit _) heating heatFresh
  have heatPlan : heat.plan = some heatMarks := by
    change routes init .rootHeat [0] [] [1, 2] = some heatMarks
    decide +kernel
  have heatUnused : init.ledger.Fresh heat.raw.selection := by
    change Disjoint ({1, 2} : Finset ℕ) {0}
    decide +kernel
  have warm : physicalStep.Admits heat := ⟨rawHeat, heatPlan ▸ rfl, heatUnused⟩
  let cut := physicalStep.toStep.result heat warm
  let dry := ReflLocatedStep.Ownership.update
    (⟨rootHeatAt (fun _ => none) 0 1 2, .rootHeat, rfl⟩ : Candidate init) heatMarks
  let L := (res label encodeConf heat.raw).label
  let C := resConf label encodeConf heat.raw
  have inv : RootCells L C rows :=
    (rootCells_heat (pre := []) (post := []) (single_root_init src []).2.1 rawHeat).1
  obtain ⟨σ, solved, agrees⟩ := rootHeat_extends label encodeConf 0 1 2 (by decide)
    (predotU l) (predotU r) original heatFresh (solvedInit τ)
  have same := (original σ (solvedInit σ)).symm.trans
    ((agrees 0 (by decide)).trans (original τ (solvedInit τ)))
  rw [psubst_atLoc_any, psubst_atLoc_any] at same
  have processEq := ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).1
  have firstSpine : SpineHasPattern X (par (predotU l) (predotU r)) := by
    rw [show predotU l = pFor X demoChan (dotted (pvars X) (predotU A)) from by decide +kernel]
    exact .parLeft _ (.guard _ _)
  have secondSpine : SpineHasPattern Y (par (predotU l) (predotU r)) := by
    rw [show predotU r = pFor Y demoChan (dotted (pvars Y) (predotU Y)) from by decide +kernel]
    exact .parRight _ (.guard _ _)
  have modulo : NameLaws (psubst σ X) (psubst σ Y) :=
    (spineHasPattern_nameLaws firstSpine processEq).trans
      ((by decide +kernel : NameLaws (psubst τ X) (psubst τ Y)).trans
        (spineHasPattern_nameLaws secondSpine processEq).symm)
  obtain ⟨openComm, commFresh⟩ := rootComm_fresh_exists L C 1 2 3 4
  have readsLeft := (inv.rows (1, l) (by decide +kernel)).2
  have readsRight := (inv.rows (2, r) (by decide +kernel)).2
  have rawComm := rootComm_admitted_mixed L C X Y demoChan
    (dotted (pvars X) (predotU A)) (dotted (pvars Y) (predotU Y)) 1 2 3 4
    readsLeft readsRight (by decide) (by decide)
    (by change 1 ∈ dry.raw.present; decide +kernel) (by change 2 ∈ dry.raw.present; decide +kernel)
    (by change 3 ∉ dry.raw.present; decide +kernel) (by change 4 ∉ dry.raw.present; decide +kernel)
    solved modulo commFresh
  let f : Candidate cut := ⟨rootCommAt openComm 1 2 3 4, .rootComm, rfl⟩
  have cutRoutes : cut = ReflLocatedStep.Ownership.update heat heatMarks :=
    routed_result (policy := .physical) warm heatPlan
  have dryLedger : cut.ledger = dry.ledger := (congrArg Store.ledger cutRoutes).trans rfl
  have plan : f.plan.isSome := by
    change (routes cut .rootComm [1, 2] [] [3, 4]).isSome = true
    rw [cutRoutes]
    change (routes dry .rootComm [1, 2] [] [3, 4]).isSome = true
    decide +kernel
  have unused : cut.ledger.Fresh f.raw.selection := by
    rw [dryLedger]
    change Disjoint ({3, 4} : Finset ℕ) dry.issued
    decide +kernel
  have checked : writtenComm l r = some [("X", Y)] := by decide +kernel
  have receipt := (writtenBinding_root (view cut) (f := f) rfl rfl
    (rfl : (view cut none).lookup 1 = some l) (rfl : (view cut none).lookup 2 = some r)).trans checked
  let completed := MeTTaCalculus.Corrected.completeBindings (pvars X ++ pvars Y) [("X", Y)]
  have told : writtenTells (view cut) f =
      some [(psubst openComm firstBody, predotU (applyDot completed A)),
        (psubst openComm secondBody, predotU (applyDot completed Y))] :=
    (readWrittenPair_root (view cut) (f := f) (writtenPairTells f.raw.opening) rfl rfl
      (rfl : (view cut none).lookup 1 = some l) (rfl : (view cut none).lookup 2 = some r)).trans
      (writtenPairTells_at openComm checked)
  obtain ⟨σ', solved'⟩ := solution_of_admitted rawComm
  obtain ⟨_, samePatterns, _, left, right⟩ := rootComm_reads_raw L C X Y demoChan demoChan
    (dotted (pvars X) (predotU A)) (dotted (pvars Y) (predotU Y)) 1 2 3 4
    readsLeft readsRight (by decide) openComm solved'
  have found : MeTTaCalculus.Corrected.unify X Y = some [("X", Y)] := by decide +kernel
  have apart : Apart X A Y Y := (ReflLocatedStep.Ownership.writtenComm_pFor_iff _ _ _ _ _ _ _).mp checked |>.2.1
  have stable : ∀ e ∈ ([("X", Y)] : Bindings), predotU e.2 = e.2 := by
    intro e member
    obtain rfl := List.mem_singleton.mp member
    rfl
  obtain ⟨srcA, srcB⟩ := ReflNames.written_principal_reads found apart (by decide +kernel)
    (by decide +kernel) stable (by decide +kernel) (by decide +kernel) rfl rfl samePatterns
  obtain ⟨labelA, labelB⟩ := rootComm_result_labels L C openComm (1 : ℕ) 2 3 4 (by decide)
  rw [labelA] at left
  rw [labelB] at right
  simp only [psubst_atLoc_any, psubst_rootLoc] at left right
  have tellsModel : nameAction.Models σ' ((writtenTells (view cut) f).getD []) := by
    rw [told]
    change nameAction.Models σ' [_, _]
    simp only [SubstitutionAction.models_cons, SubstitutionAction.models_nil, and_true]
    exact ⟨((locatedFrame_name.atLoc_iff _ _ _ _).mp left).1.trans srcA,
      ((locatedFrame_name.atLoc_iff _ _ _ _).mp right).1.trans srcB⟩
  have permit : (withWrittenComm .physical view).Admits f := by
    refine (written_comm_admits_iff .physical view f).mpr
      ⟨admits_with_tells .physical _ ⟨rawComm, plan, unused⟩
        ⟨PUnit.unit, σ', (f.models_information _).mpr ⟨solved', tellsModel⟩⟩, ?_⟩
    change (ReflLocatedStep.Ownership.writtenBinding (view cut) f).isSome = true
    rw [receipt]
    rfl
  obtain ⟨bs, seen, inv', reacted⟩ := rootCells_written_comm .physical view cut.ledger
    (pre := []) (mid := []) (post := []) inv rfl permit
  change ReflLocatedStep.Ownership.writtenBinding (view cut) f = some bs at seen
  rw [receipt] at seen
  cases seen
  let run : (withWrittenComm .physical view).Run init :=
    .cons heat ⟨warm, trivial⟩ (.cons f permit (.nil _))
  have leftOut : applyDot (MeTTaCalculus.Corrected.completeBindings (pvars X ++ pvars Y) [("X", Y)])
      A = par (nQuote Y) Readiness.inner := by decide +kernel
  have rightOut : applyDot (MeTTaCalculus.Corrected.completeBindings (pvars X ++ pvars Y) [("X", Y)])
      Y = nQuote Y := by decide +kernel
  rw [leftOut, rightOut] at inv' reacted
  exact ⟨run, rfl, inv', reacted⟩

/-- Both policies commit on this represented pair of quoted open bags.
The quotient commit has an extra solution that publishes the wrong
continuation; the written publication equations exclude that solution. -/
theorem written_commit_excludes_spurious_bag_solution :
    let x : Pattern := .fvar "X"
    let y : Pattern := .fvar "Y"
    let left := pFor (tProc (par x atomA)) demoChan x
    let right := pFor (tProc (par atomB y)) demoChan y
    let rows := [(1, left), (2, right)]
    let label := fun o : ℕ => atLoc (predotU (if o = 1 then left else right)) rootLoc
    let c : Configuration Pattern ℕ := ⟨[], {1, 2}⟩
    let s := ReflLocatedStep.Ownership.start (embed label c)
    ∃ (f : Candidate s) (quotient : physicalStep.Admits f)
        (written : (withWrittenComm .physical (rootWrittenRows rows)).Admits f),
      let wide := physicalStep.toStep.result f quotient
      let precise := (withWrittenComm .physical (rootWrittenRows rows)).result f written
      (∃ σ : PSubst,
        nameAction.Models σ wide.raw.knowledge ∧
        ¬ nameAction.Models σ precise.raw.knowledge ∧
        ¬ NameLaws (psubst σ (wide.raw.label 3)) (atLoc (nQuote atomB) rootLoc)) ∧
      ∀ σ : PSubst, nameAction.Models σ precise.raw.knowledge →
        NameLaws (psubst σ (precise.raw.label 3)) (atLoc (nQuote atomB) rootLoc) := by
  dsimp only
  let x : Pattern := .fvar "X"
  let y : Pattern := .fvar "Y"
  let t := tProc (par x atomA)
  let u := tProc (par atomB y)
  let l := pFor t demoChan x
  let r := pFor u demoChan y
  let label := fun o : ℕ => atLoc (predotU (if o = 1 then l else r)) rootLoc
  let c : Configuration Pattern ℕ := ⟨[], {1, 2}⟩
  let s := ReflLocatedStep.Ownership.start (embed label c)
  let rows := [(1, l), (2, r)]
  let view := rootWrittenRows rows
  let assign (extra : Bool) : PSubst := fun v =>
    if v = "X" then some (if extra then par atomB atomB else atomB)
    else if v = "Y" then some (if extra then par atomA atomB else atomA) else none
  have left : Reads label c 1 (atLoc (pFor t demoChan (nQuote x)) rootLoc) :=
    fun σ _ => NameLaws.refl _
  have right : Reads label c 2 (atLoc (pFor u demoChan (nQuote y)) rootLoc) :=
    fun σ _ => NameLaws.refl _
  have unifiesAt (extra : Bool) : NameLaws (psubst (assign extra) t) (psubst (assign extra) u) := by
    cases extra <;> decide +kernel
  have models (σ : PSubst) : nameAction.Models σ c.equations := nameAction.models_nil σ
  obtain ⟨ρ, fresh⟩ := rootComm_fresh_exists label c 1 2 3 4
  let f : Candidate s := ⟨rootCommAt ρ 1 2 3 4, .rootComm, rfl⟩
  have raw := rootComm_admitted_mixed label c t u demoChan (nQuote x) (nQuote y) 1 2 3 4
    left right (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (models (assign false)) (unifiesAt false) fresh
  have plan : f.plan.isSome := by
    change (routes s .rootComm [1, 2] [] [3, 4]).isSome = true
    decide +kernel
  have unused : s.ledger.Fresh f.raw.selection := by
    change Disjoint ({3, 4} : Finset ℕ) {1, 2}
    decide
  have quotient : physicalStep.Admits f := ⟨raw, plan, unused⟩
  have solvedAt (extra : Bool) :=
    rootComm_extends_with_publications label c t u demoChan (nQuote x) (nQuote y) 1 2 3 4
      left right (by decide) (by decide) fresh (models (assign extra)) (unifiesAt extra)
  have checked : writtenComm l r = some [("X", atomB), ("Y", atomA)] := by decide +kernel
  let binding := MeTTaCalculus.Corrected.completeBindings (pvars t ++ pvars u)
    [("X", atomB), ("Y", atomA)]
  have leftValue : predotU (applyDot binding x) = nQuote atomB := by decide +kernel
  have rightValue : predotU (applyDot binding y) = nQuote atomA := by decide +kernel
  have told : writtenTells (view s) f =
      some [(psubst ρ firstBody, nQuote atomB), (psubst ρ secondBody, nQuote atomA)] := by
    have seq := writtenPairTells_at ρ checked
    change writtenPairTells ρ l r =
      some [(psubst ρ firstBody, predotU (applyDot binding x)),
        (psubst ρ secondBody, predotU (applyDot binding y))] at seq
    rw [leftValue, rightValue] at seq
    exact (readWrittenPair_root (view s) (f := f) (writtenPairTells f.raw.opening)
      (left := l) (right := r) rfl rfl rfl rfl).trans seq
  let equations := [(psubst ρ firstBody, nQuote atomB), (psubst ρ secondBody, nQuote atomA)]
  have closedB (w : PSubst) : psubst w (nQuote atomB) = nQuote atomB :=
    psubst_of_pvars_nil w _ rfl
  have closedA (w : PSubst) : psubst w (nQuote atomA) = nQuote atomA :=
    psubst_of_pvars_nil w _ rfl
  obtain ⟨good, agrees, _, goodL, goodR⟩ := solvedAt false
  have goodTells : nameAction.Models good ((writtenTells (view s) f).getD []) := by
    rw [told]
    change nameAction.Models good equations
    simp only [equations, SubstitutionAction.models_cons, SubstitutionAction.models_nil, and_true]
    change NameLaws (psubst good (psubst ρ firstBody)) (psubst good (nQuote atomB)) ∧
      NameLaws (psubst good (psubst ρ secondBody)) (psubst good (nQuote atomA))
    rw [closedA, closedB]
    exact ⟨goodL, goodR⟩
  have admitted : (withWrittenComm .physical view).Admits f := by
    refine (written_comm_admits_iff .physical view f).mpr
      ⟨admits_with_tells .physical _ quotient
        ⟨PUnit.unit, good, (f.models_information _).mpr ⟨agrees, goodTells⟩⟩, ?_⟩
    change (ReflLocatedStep.Ownership.writtenBinding (view s) f).isSome = true
    rw [writtenBinding_root (view s) (left := l) (right := r) rfl rfl rfl rfl, checked]
    rfl
  obtain ⟨wide, wideModel, _, wideL, _⟩ := solvedAt true
  have mismatch : ¬ NameLaws (psubst wide (psubst ρ firstBody)) (nQuote atomB) := fun same =>
    (by decide +kernel : ¬ NameLaws (nQuote (par atomB atomB)) (nQuote atomB)) (wideL.symm.trans same)
  obtain ⟨labelL, labelR⟩ := rootComm_result_labels label c ρ (1 : ℕ) 2 3 4 (by decide)
  refine ⟨f, quotient, admitted, ⟨wide, wideModel, ?_, ?_⟩, ?_⟩
  · intro survives
    have meant := (ReflLocatedStep.Ownership.written_result_models .physical view admitted survives).2
    rw [told] at meant
    have value : NameLaws (psubst wide (psubst ρ firstBody)) (psubst wide (nQuote atomB)) :=
      meant (psubst ρ firstBody, nQuote atomB) (by simp)
    exact mismatch ((closedB wide) ▸ value)
  · intro same
    change NameLaws (psubst wide ((res label c (rootCommAt ρ 1 2 3 4)).label 3)) _ at same
    rw [labelL] at same
    simp only [psubst_atLoc_any, psubst_rootLoc] at same
    exact mismatch ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).1
  · intro σ accepted
    have publishing := (ReflLocatedStep.Ownership.written_result_publications .physical view admitted
      told labelL labelR accepted).1
    simpa only [psubst_rootLoc, closedB] using publishing

private theorem sibling_is_dormant (result : Pattern) : ¬ BagStep conventional siblingRow result := by
  intro step
  refine no_bagStep_reflect_dead (S := dormantBody) ?_ step rfl
  intro p out same st
  have bag : BagEq dormantBody p := by
    unfold BagEq
    rw [same]
  exact ((non_ground_bag_pattern_control_QN.2.2 conventional out).1
    (.congruence bag st (BagEq.refl _)))

/-- A completed child opened from row 1 can be taken by a raw close on
row 2. The run starts at the canonical one-row encoding. Row 2 has no
source step: the QN instance can make its open pattern agree modulo
the quoted bag equations, but the source principal matcher cannot.
This separates ownership even with the actual opening absence guards. -/
theorem admitted_run_can_close_an_unopened_sibling :
    HostedNode twoReflections ∧ (∀ p, ¬ BagStep conventional siblingRow p) ∧
    ∃ (heating opening : PSubst) (pr tk : ℕ),
      let heat := rootHeatAt heating 0 1 2
      let rootLabel := (res (encodeLabel twoReflections) encodeConf heat).label
      let rootC := resConf (encodeLabel twoReflections) encodeConf heat
      let birth := openRootAt opening 1 pr tk
      (RuleSyntax.step QN ℕ QNE located).Admits (s := embed (encodeLabel twoReflections) encodeConf) heat ∧
      (RuleSyntax.step QN ℕ QNE located).Admits (s := embed rootLabel rootC) birth ∧
      ∃ (readyLabel : ℕ → Pattern) (readyC : Configuration Pattern ℕ) (token made : ℕ)
        (closing : PSubst),
        let closeWrong := closeRootAt closing 2 token made
        LocatedRunNoRoot (res rootLabel rootC birth).label (resConf rootLabel rootC birth) readyLabel readyC false ∧
        (RuleSyntax.step QN ℕ QNE located).Admits (s := embed readyLabel readyC) closeWrong ∧
        1 ∈ (resConf readyLabel readyC closeWrong).present ∧ 2 ∉ (resConf readyLabel readyC closeWrong).present ∧
        ∃ rightClosing : PSubst,
          let closeRight := closeRootAt rightClosing 1 token made
          (RuleSyntax.step QN ℕ QNE located).Admits (s := embed readyLabel readyC) closeRight ∧
          2 ∈ (resConf readyLabel readyC closeRight).present ∧ 1 ∉ (resConf readyLabel readyC closeRight).present ∧
          routedStep.Admits (packedClose readyLabel readyC tk token rightClosing 1 made) ∧
          ¬ routedStep.Admits (packedClose readyLabel readyC tk token closing 2 made) := by
  have channel : HostedChan demoChan := ⟨by decide +kernel, by decide +kernel⟩
  refine ⟨.par (.reflect channel (.par (.guard channel) (.guard channel)))
    (.reflect channel (.par (.guard channel) (.guard channel))), sibling_is_dormant, ?_⟩
  have groundAB : pvars patAB = [] := by decide +kernel
  have gp : GroundPrincipal patAB patAB [] := by
    refine ⟨(fun _ h => nomatch h), ?_, rfl, ?_⟩
    · intro v h
      simp [groundAB] at h
    · intro _ _ v h
      simp [groundAB] at h
  have conv : Apart patAB pZero patAB pZero := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro v h <;> simp [groundAB] at h
  have split : ReflCorrespondence.Splits liveBody ([inputAB] ++ [inputAB]) :=
    .split (.leaf inputAB) (.leaf inputAB)
  have packedStep : HostedPackStep 0 liveBody
      (pPar [applyDot [] pZero, applyDot [] pZero]) (patAB, patAB) [] := by
    refine HostedPackStep.comm [] [] [] patAB patAB demoChan pZero pZero []
      split (by decide +kernel) (by decide +kernel)
      channel.1 (by decide +kernel) (by decide +kernel) ?_ ?_ gp conv
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) <;>
      simp [PlainPatterns, PlainPatternsList, applyDot, pZero, Mettapedia.OSLF.MeTTaIL.Match.applyBindings]
  let wants := [patAB, patAB, patY]
  have originPattern : SpineHasPattern patAB (predotU ownerRow) :=
    .reflect _ (.parLeft inputAB (.guard demoChan pZero))
  have siblingPattern : SpineHasPattern patY (predotU siblingRow) :=
    .reflect _ (.parLeft inputAB (.guard demoChan pZero))
  obtain ⟨_, initial, clean, free⟩ := single_root_init twoReflections wants
  obtain ⟨heat, freshHeat⟩ := rootHeat_fresh_exists (encodeLabel twoReflections) encodeConf 0 1 2
  have solveInitial : nameAction.Models (fun _ => none) encodeConf.equations :=
    fun _ member => absurd member List.not_mem_nil
  have pair : NameLaws (psubst (fun _ => none) (encodeLabel twoReflections 0))
      (atLoc (par (predotU ownerRow) (predotU siblingRow)) rootLoc) := by
    rw [psubst_none]
    exact NameLaws.refl _
  have heated := rootHeat_admitted (encodeLabel twoReflections) encodeConf 0 1 2
    (by decide) (by decide) (by decide) (by decide) solveInitial pair freshHeat
  let h := rootHeatAt heat (0 : ℕ) 1 2
  let rootLabel := (res (encodeLabel twoReflections) encodeConf h).label
  let rootC := resConf (encodeLabel twoReflections) encodeConf h
  have roots : RootCells rootLabel rootC [(1, ownerRow), (2, siblingRow)] :=
    (rootCells_heat (pre := []) (post := []) initial heated).1
  have cleanRoots : CleanChildren rootLabel rootC := cleanChildren_of_rootRule clean heated
    (r := FiniteProgram.heatRule) rfl
  have anchors : ∀ q ∈ wants, ∃ cell ∈ ([(0, twoReflections)] : List (ℕ × Pattern)),
      SpineHasPattern q (predotU cell.2) := by
    intro q member
    refine ⟨(0, twoReflections), by simp, ?_⟩
    simp only [wants, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .parLeft _ originPattern
    · exact .parLeft _ originPattern
    · exact .parRight _ siblingPattern
  have freeRoots := (freeOnPats_rootHeat (pre := []) (post := []) initial freshHeat free anchors).1
  obtain ⟨pr, tk, opening, opened, readyLabel, readyC, token, acc, ran, done, readsToken, _, packed, _,
    kept, knownEarlier, freeReady⟩ :=
    refl_depth_root_ready (pre := []) (post := [(2, siblingRow)]) (reflOcc := 1) (x := demoChan)
      (extPats := [patY]) packedStep roots channel.1 cleanRoots
      (fun _ _ v _ => by
        change v ∉ pvars patAB ++ pvars patAB
        simp [groundAB]) freeRoots
      (fun q m => by
        obtain rfl := List.mem_singleton.mp m
        exact ⟨(2, siblingRow), by simp, siblingPattern⟩)
  have old₁ := (roots.rows (1, ownerRow) (by simp)).1
  have row₂ := roots.rows (2, siblingRow) (by simp)
  obtain ⟨σ, known, agrees⟩ := freeReady yToB
  have old₂ := kept 2 row₂.1
  have tRead := readsToken σ known
  have tokenNew : token ∉ rootC.present := by
    intro member
    rw [(kept token member).2, psubst_doneTok] at tRead
    exact (cleanRoots rootLoc demoChan (predotU liveBody) .root (Nat.zero_le _) token member
      σ (knownEarlier σ known)).2.1 _ _ tRead
  have patSame : NameLaws (psubst σ patY) (psubst σ patAB) := by
    rw [psubst_of_pvars_nil σ patAB groundAB]
    exact (agrees patY (by simp)).trans (by decide +kernel)
  have bodySame : NameLaws (psubst σ (predotU dormantBody)) (psubst σ (predotU liveBody)) := by
    change NameLaws (psubst σ (par inputY inputAB)) (psubst σ (par inputAB inputAB))
    rw [psubst_par, psubst_par]
    apply ReflPacking.nameLaws_par _ (NameLaws.refl _)
    rw [inputY, inputAB, psubst_pFor, psubst_pFor]
    exact nameLaws_pFor_iff.mpr ⟨patSame, NameLaws.refl _, NameLaws.refl _⟩
  have readsSibling : NameLaws (psubst σ (readyLabel 2))
      (psubst σ (atLoc (pReflect demoChan (predotU liveBody)) rootLoc)) := by
    rw [old₂.2]
    refine (row₂.2 σ (knownEarlier σ known)).trans ?_
    change NameLaws (psubst σ (atLoc (pReflect demoChan (predotU dormantBody)) rootLoc)) _
    simp only [psubst_atLoc_any, psubst_pReflect, psubst_rootLoc]
    exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr
      ⟨nameLaws_pReflect_iff.mpr ⟨NameLaws.refl _, bodySame⟩, NameLaws.refl _⟩
  obtain ⟨made, unused⟩ := Infinite.exists_notMem_finset (insert tk readyC.present)
  have freshMade : made ∉ readyC.present := fun present => unused (Finset.mem_insert.mpr (.inr present))
  obtain ⟨closing, freshClose⟩ := close_fresh_exists readyLabel readyC 2 token made
  have wrong := closeRoot_admitted_at_solution readyLabel readyC demoChan (predotU liveBody) acc 2 token made
    readsSibling readsToken packed (fun e => tokenNew (e ▸ row₂.1)) ⟨old₂.1, done.present⟩
    freshMade known freshClose
  have neq1 : (1 : ℕ) ≠ token := fun e => tokenNew (e ▸ old₁)
  have neq2 : (2 : ℕ) ≠ made := fun e => freshMade (e ▸ old₂.1)
  obtain ⟨rightClosing, freshRight⟩ := close_fresh_exists readyLabel readyC 1 token made
  have oldRight := kept 1 old₁
  have readsRight : ∀ τ : PSubst, nameAction.Models τ readyC.equations →
      NameLaws (psubst τ (readyLabel 1)) (psubst τ (atLoc (pReflect demoChan (predotU liveBody)) rootLoc)) := by
    intro τ solved
    rw [oldRight.2]
    exact (roots.rows (1, ownerRow) (by simp)).2 τ (knownEarlier τ solved)
  have right := closeRoot_admitted readyLabel readyC demoChan (predotU liveBody) acc 1 token made
    readsRight readsToken packed neq1 ⟨oldRight.1, done.present⟩ freshMade known freshRight
  have ownerNotMade : (1 : ℕ) ≠ made := fun e => freshMade (e ▸ oldRight.1)
  have stamp : (packedStore readyLabel readyC tk token).route token =
      some (.control ⟨tk, 1, none⟩ .done) := by simp [packedStore, Store.route, done.present]
  have markOwner : (packedStore readyLabel readyC tk token).route 1 = some (.cell none) := by
    simp [packedStore, Store.route, oldRight.1, neq1]
  have consumesOwner : routedStep.Admits (packedClose readyLabel readyC tk token rightClosing 1 made) := by
    refine ⟨right, ?_, ?_⟩
    · exact (ReflLocatedStep.Ownership.close_root_plan_iff _ 1 token made).mpr
        ⟨_, stamp, rfl, rfl, markOwner, packed_reserved_owner _ _ _ _ done.present,
          packed_route_empty .., packed_nested_empty ..⟩
    · apply Finset.disjoint_left.mpr
      intro o produced prior
      have same : o = made := by simpa [packedClose, closeRootAt] using produced
      exact unused (same ▸ prior)
  have refusesSibling : ¬ routedStep.Admits (packedClose readyLabel readyC tk token closing 2 made) := by
    intro admitted
    obtain ⟨t, read, owns, _⟩ :=
      (ReflLocatedStep.Ownership.close_root_plan_iff _ 2 token made).mp admitted.2.1
    rw [stamp] at read
    simp only [Option.some.injEq, LocatedSubstitution.Authority.Mark.control.injEq] at read
    rw [← read.1] at owns
    exact (by decide : (1 : ℕ) ≠ 2) owns
  exact ⟨heat, opening, pr, tk, heated, opened,
    readyLabel, readyC, token, made, closing, ran, wrong,
    (close_present readyLabel readyC closing 2 token made 1).mpr (.inl ⟨oldRight.1, by decide, neq1⟩),
    (fun present => ((close_present readyLabel readyC closing 2 token made 2).mp present).elim
      (fun h => h.2.1 rfl) neq2), rightClosing, right,
    (close_present readyLabel readyC rightClosing 1 token made 2).mpr
      (.inl ⟨old₂.1, by decide, fun e => tokenNew (e ▸ row₂.1)⟩),
    (fun present => ((close_present readyLabel readyC rightClosing 1 token made 1).mp present).elim
      (fun h => h.2.1 rfl) ownerNotMade), consumesOwner, refusesSibling⟩

end Ownership

namespace Coverage

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open MeTTaCalculus.Corrected
open MeTTaOperationsComm (pvars)

/-- The hosted forward relation includes structural stuttering even at zero.
It therefore is not a subrelation of the computational source step. -/
theorem hosted_structural_stutter_is_not_a_source_step :
    ReflSystem.HostedRootStepN (O := Nat) [(0, pZero)] [] [] pZero pZero ∧
      ReflSystem.HostedRootStepC (O := Nat) [(0, pZero)] [] [] pZero pZero ∧
      ¬ BagStep conventional pZero pZero :=
  ⟨.equiv (BagEq.refl _), .equiv (BagEq.refl _), BagStep.not_from_zero _ _⟩

theorem computational_source_steps_are_inhabited :
    ∃ source target, BagStep conventional source target :=
  ⟨BagControls.twoParties, par BagControls.atomA BagControls.atomB, BagControls.parties_step⟩

def continuation : Pattern := pFor (.fvar "y") demoChan pZero
def premise : Pattern := par (pFor pZero demoChan continuation) (pFor pZero demoChan pZero)
def reduct : Pattern := par continuation pZero
def reflected : Pattern := pReflect demoChan premise
def listener : Pattern := pFor (tProc reduct) demoChan pZero

theorem the_premise_has_a_step : BagStep conventional premise reduct := by
  have step := BagStep.comm (admit := conventional) pZero pZero demoChan continuation pZero []
    BagControls.principal_empty
    ⟨by simp [pZero, pvars, MeTTaOperationsComm.pvars.pvarsList],
     by simp [pZero, pvars, MeTTaOperationsComm.pvars.pvarsList],
     by simp [pZero, pvars, MeTTaOperationsComm.pvars.pvarsList],
     by simp [pZero, pvars, MeTTaOperationsComm.pvars.pvarsList],
     by simp [pZero, pvars, MeTTaOperationsComm.pvars.pvarsList]⟩
  simpa [premise, reduct, continuation, applyDot, dotBindings,
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings, pFor, demoChan, nQuote, pZero] using step

theorem reflection_has_a_step : BagStep conventional reflected listener :=
  .reflect demoChan the_premise_has_a_step

theorem reflected_source_is_tame : tame reflected = true := by decide +kernel
theorem reflected_listener_is_not_tame : tame listener = false := by decide +kernel

/-- The actual bag-step relation does not preserve tameness through REFL. -/
theorem reflection_does_not_preserve_tameness :
    ¬ ∀ source target, tame source = true → BagStep conventional source target → tame target = true := by
  intro preserves
  have impossible := preserves reflected listener reflected_source_is_tame reflection_has_a_step
  rw [reflected_listener_is_not_tame] at impossible
  cases impossible

#print axioms hosted_structural_stutter_is_not_a_source_step
#print axioms computational_source_steps_are_inhabited
#print axioms reflection_has_a_step
#print axioms reflection_does_not_preserve_tameness

end Coverage

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem.Controls
