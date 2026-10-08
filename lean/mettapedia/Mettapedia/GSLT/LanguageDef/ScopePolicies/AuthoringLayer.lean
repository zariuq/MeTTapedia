import Mettapedia.GSLT.LanguageDef.Extension
import Mettapedia.GSLT.LanguageDef.ScopePolicies.Explication

/-!
# Is a scope policy a `CoGSLTLayer`?

A `CoGSLTLayer` is an exact elaboration from an authoring theory: an
elaborator that respects the equations and the rewrites of the authoring
theory, and a `quote` back that elaboration inverts.  For the elaboration of a
scope policy the answer has three parts.

* **Onto its image, with writing out as the authored step**
  (`policyLayer`).  The layer is indexed by the configuration.  Over a
  configuration:
  * the authoring theory (`authoringGSLT`) is authored forms compared as
    written, and its step is *writing out* (`WritesOut`): an empty `new` block
    around a symbol is dropped, under every policy; a form is replaced by its
    explicit form, under explicit capture on every text, and under the
    query-wide policy and lexical fresh on text whose lambdas carry no crossing
    set;
  * the law that elaboration does not see a step is `writesOut_elabCfg`: the
    policy elaborates a form and what it is written out to alike, at every
    root, lifetime and readout;
  * the fibre is the core terms that the policy elaborates some text to
    (`Elaborated`), and `quote` is a chosen text.  It is a chosen preimage, not
    a decompiler: no function from core terms back to text is built here, and
    the law that elaboration inverts `quote` holds because the fibre is the
    image.
  Rule M has the first step only.  Its explicit form is not elaborated alike
  (`mercury_explicit_form_differs`, from `ownList_order_witness`), so it could
  not be a step of any layer whose elaborator is rule M's.
* **Onto the core, no** (`no_exact_elaboration_onto_core`).  No `quote` from
  all core terms exists: contextual code is the elaboration of no text.
* **From the policy's running theory, no**
  (`no_elaboration_of_running_theory`).  The authoring theory of a layer has
  rewrites that elaboration must not see; the reduction of the policy's own
  theory is evaluation, and a program and its observation are different terms
  of the core.

The readout is not seen by the layer: the fibres over two configurations that
differ in the readout only are the same type (`elaborated_readout`).  A readout
changes the reduction the core runs under, and that is not authoring data.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

universe u v

variable {S : Type u} {X : Type v} [DecidableEq X]

/-- **Writing out, as a step of authored text.**  A step replaces a form by a
different form that the policy elaborates alike (`writesOut_elabCfg`).

* Under every policy, an empty `new` block around a symbol is dropped.
* Under explicit capture, a form is replaced by its explicit form.
* Under the query-wide policy and under lexical fresh, the same, for a form
  whose lambdas carry no crossing set.

Rule M has only the first step: its explicit form is not elaborated alike
(`mercury_explicit_form_differs`). -/
inductive WritesOut (c : Config) : Src S X → Src S X → Prop
  | emptyBlock (s : S) : WritesOut c (.new [] (.sym s)) (.sym s)
  | explicitCapture (t : Src S X) (policy : c.ownership = .explicitCapture)
      (changed : explicateEC t ≠ t) : WritesOut c t (explicateEC t)
  | queryWide (t : Src S X) (policy : c.ownership = .queryWide) (plain : lamPlain t = true)
      (changed : explicateQ t ≠ t) : WritesOut c t (explicateQ t)
  | lexicalFresh (t : Src S X) (policy : c.ownership = .lexicalFresh) (plain : lamPlain t = true)
      (changed : explicateLF [] t ≠ t) : WritesOut c t (explicateLF [] t)

/-- A step is not seen by the ownership policy, at any root. -/
theorem writesOut_elabForm {c : Config} {first second : Src S X} (step : WritesOut c first second)
    (root : Owner) : elabForm c.ownership root second = elabForm c.ownership root first := by
  cases step with
  | emptyBlock s => cases c.ownership <;> rfl
  | explicitCapture _ policy _ =>
      rw [policy]
      exact elabEC_explicateEC first (fun _ => root) root
  | queryWide _ policy plain _ =>
      rw [policy]
      exact elabQ_explicateQ first (fun _ => root) root plain
  | lexicalFresh _ policy plain _ =>
      rw [policy]
      exact elabLF_explicateLF first (fun _ => root) [] [] root plain

/-- **Elaboration does not see a step**: a policy elaborates a form and what it
is written out to alike, at every root, under every lifetime and readout. -/
theorem writesOut_elabCfg {c : Config} {first second : Src S X} (step : WritesOut c first second)
    (root : Owner) : elabCfg c root second = elabCfg c root first := by
  obtain ⟨ownership, lifetime, readout⟩ := c
  have forms : elabForm ownership root second = elabForm ownership root first :=
    writesOut_elabForm step root
  cases lifetime <;> simp only [elabCfg, elabCfgX, forms]

/-- Under rule M the only step drops an empty block around a symbol. -/
theorem writesOut_mercury {c : Config} (policy : c.ownership = .mercury) {first second : Src S X}
    (step : WritesOut c first second) : ∃ s, first = .new [] (.sym s) ∧ second = .sym s := by
  cases step with
  | emptyBlock s => exact ⟨s, rfl, rfl⟩
  | explicitCapture _ other _ =>
      rw [policy] at other
      cases other
  | queryWide _ other _ _ =>
      rw [policy] at other
      cases other
  | lexicalFresh _ other _ _ =>
      rw [policy] at other
      cases other

/-- **The authoring theory of a policy**: authored forms, compared as written,
with writing out as the step. -/
def authoringGSLT (S : Type u) (X : Type v) [DecidableEq X] (c : Config) : GSLT.{max u v} where
  Term := Src S X
  equations := ⟨Eq, ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩⟩
  rewrites := WritesOut c
  rewrites_resp_left := by
    rintro first _ second rfl step
    exact ⟨second, step, rfl⟩
  rewrites_resp_right := by
    rintro first second _ step rfl
    exact step

/-- **The core terms that a policy elaborates some text to.** -/
def Elaborated (S : Type u) (X : Type v) [DecidableEq X] (c : Config) (root : Owner) :
    Type (max u v) :=
  {term : Tm S (Slot X) // ∃ t : Src S X, elabCfg c root t = term}

/-- **The scope policies as one layer over the configurations**: an exact
elaboration onto its image from the authoring theory whose step is writing
out, with a chosen text as `quote`. -/
noncomputable def policyLayer (S : Type u) (X : Type v) [DecidableEq X] (root : Owner) :
    CoGSLTLayer.{0, max u v, max u v} Config where
  Fiber := fun c => Elaborated S X c root
  sourceGSLT := fun c => authoringGSLT S X c
  elaborate := fun c t => some ⟨elabCfg c root t, t, rfl⟩
  quote := fun _ term => Classical.choose term.2
  elaborate_quote := fun _ term =>
    congrArg some (Subtype.ext (Classical.choose_spec term.2))
  elaborate_equation := fun _ {first second} equivalent => by
    obtain rfl : first = second := equivalent
    rfl
  elaborate_rewrite := fun _ {_ _} step =>
    congrArg some (Subtype.ext (writesOut_elabCfg step root).symm)

/-- Positive: the layer elaborates a text to its elaboration. -/
theorem policyLayer_elaborate (root : Owner) (c : Config) (t : Src S X) :
    ((policyLayer S X root).elaborate c t).map Subtype.val = some (elabCfg c root t) :=
  rfl

/-- Positive: quoting an elaboration gives a text with that elaboration. -/
theorem policyLayer_quote (root : Owner) (c : Config) (t : Src S X) :
    elabCfg c root ((policyLayer S X root).quote c ⟨elabCfg c root t, t, rfl⟩) =
      elabCfg c root t :=
  Classical.choose_spec (⟨t, rfl⟩ : ∃ source : Src S X, elabCfg c root source = elabCfg c root t)

/-- Positive: the authoring theory has a step under every configuration, so
the layer's law about steps is about something at every base. -/
theorem authoring_steps (c : Config) (s : S) :
    (authoringGSLT S X c).rewrites (.new [] (.sym s)) (.sym s) :=
  .emptyBlock s

/-- Positive: under explicit capture `(lam z (($a $b) (lam w $a)))` steps to
its explicit form, which is a different text. -/
theorem explicitCapture_writes_out (lifetime : Lifetime) (readout : Readout) :
    (authoringGSLT Unit ℕ ⟨.explicitCapture, lifetime, readout⟩).rewrites orderSource
        (explicateEC orderSource) ∧
      explicateEC orderSource ≠ orderSource := by
  have changed : explicateEC orderSource ≠ orderSource :=
    fun same => absurd (congrArg explicit same) (by decide)
  exact ⟨.explicitCapture orderSource rfl changed, changed⟩

/-- Negative: under rule M the same text has no step. -/
theorem mercury_no_writing_out (second : Src Unit ℕ) :
    ¬ (authoringGSLT Unit ℕ cfgM).rewrites orderSource second := by
  intro step
  obtain ⟨s, source, -⟩ := writesOut_mercury (c := cfgM) rfl step
  simp [orderSource] at source

/-- Negative, and the reason: rule M does not elaborate that text and its
explicit form alike, so the explicit form could not be a step of a layer whose
elaborator is rule M's. -/
theorem mercury_explicit_form_differs :
    elabCfg cfgM [] orderExplicit ≠ elabCfg cfgM [] orderSource :=
  fun same => ownList_order_witness.2.2.2 same.symm

/-- The readout is not seen by the layer. -/
theorem elaborated_readout (ownership : Ownership) (lifetime : Lifetime)
    (readout readout' : Readout) (root : Owner) :
    Elaborated S X ⟨ownership, lifetime, readout⟩ root =
      Elaborated S X ⟨ownership, lifetime, readout'⟩ root :=
  rfl

/-- The fibre is not all of the core: contextual code is not in it. -/
theorem ctx_not_elaborated (c : Config) (root : Owner) (ks : List (Nm (Slot X)))
    (body : Tm S (Slot X)) : ¬ ∃ t : Src S X, elabCfg c root t = .ctx ks body :=
  fun ⟨t, same⟩ => elabCfg_ne_ctx c root t ks body same

/-- **No exact elaboration onto the core.**  An exact elaboration out of the
authoring theory whose elaborator is the policy's has no `quote` for contextual
code. -/
theorem no_exact_elaboration_onto_core (c : Config) (root : Owner) (s : S) :
    ¬ ∃ exact : GSLT.ExactElaboration (authoringGSLT S X c) (Tm S (Slot X)),
      ∀ t : Src S X, exact.elaborate t = some (elabCfg c root t) := by
  rintro ⟨exact, agrees⟩
  have quoted := exact.elaborate_quote (.ctx [] (.sym s))
  have same := (agrees (exact.quote (.ctx [] (.sym s)))).symm.trans quoted
  exact elabCfg_ne_ctx c root _ [] (.sym s) (Option.some.inj same)

variable [DecidableEq S]

/-- **No elaboration out of the policy's running theory.**  An elaboration
identifies a term with every term it rewrites to; a program and its observation
are different terms of the core. -/
theorem no_elaboration_of_running_theory (c : Config) (u : X) (unit : S) (s : S) :
    ¬ ∃ elaboration : GSLT.Elaboration (policyGSLT c u unit) (Core S X),
      ∀ term : Authored S X, elaboration.elaborate term = some (elabState c u unit term) := by
  rintro ⟨elaboration, agrees⟩
  have same := elaboration.rewrite (bareProgram_steps c u unit s)
  rw [agrees, agrees] at same
  have states := Option.some.inj same
  simp only [elabState] at states
  cases states

#print axioms writesOut_elabCfg
#print axioms policyLayer
#print axioms explicitCapture_writes_out
#print axioms mercury_no_writing_out
#print axioms mercury_explicit_form_differs
#print axioms no_exact_elaboration_onto_core
#print axioms no_elaboration_of_running_theory

end Mettapedia.GSLT.LanguageDef.ScopePolicies
