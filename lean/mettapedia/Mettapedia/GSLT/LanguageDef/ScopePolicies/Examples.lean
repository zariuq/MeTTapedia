import Mettapedia.GSLT.LanguageDef.ScopePolicies.Composition
import Mettapedia.GSLT.LanguageDef.ScopePolicies.LifetimeReadout

/-!
# Further examples, positive and negative

* **Static equivalence that is not equality** (`translation_differs`,
  `translation_equivalent`): on row H1 of the corpus the translation under
  lexical fresh and the source under rule M elaborate to two different
  judgments of the core, and the two are statically equivalent.
* **Admissible programs** (`rowH1_admissible`, `freeParameter_not_admissible`).
* **Readings** (`ctx_not_read`): a judgment whose query is contextual code is
  read by no judgment of the identity model.
* **Explicit and plain text** (`explicit_examples`).
* **Where writing out is not exact** (`explicateQ_needs_plain`): under the
  query-wide policy, a lambda with a crossing set around a lambda without one.
* **Separation** (`not_separated_self`).
* **Realizing a file** (`empty_not_realizes`).
* **Images** (`explicitCapture_image_subset`, `explicit_image_eq`): every
  judgment that explicit capture elaborates a program to is one that every
  ownership policy elaborates a program to; on explicit programs all ownership
  policies have one image.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot
open Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus

/-! ## Static equivalence that is not equality -/

/-- The equations of the corpus are admissible text. -/
theorem corpus_clauses_admissible :
    ∀ F body, clauses F = some body → body.Admissible := by
  intro F body found
  cases F <;> first
    | (cases found; decide)
    | cases found

/-- Row H1, `(let $f (lam z $hole) (Pair ($f 1) ($f 2)))`, is an admissible
program. -/
theorem rowH1_admissible : (rowProgram rowH1).Admissible :=
  ⟨corpus_clauses_admissible, by decide⟩

set_option maxRecDepth 100000 in
/-- **The translation is not exact in the slot model.**  Rule M gives the
lambda of row H1 an own list; lexical fresh on the translation gives it none
and runs a `new` block as an activation.  The two queries are different
terms. -/
theorem translation_differs :
    elabCfg cfgLF [] (toLexProgram (rowProgram rowH1)).query ≠
      elabCfg cfgM [] (rowProgram rowH1).query := by
  decide +kernel

/-- So the two judgments of the core are different. -/
theorem translation_differs_state :
    elabState cfgLF Sp.u Sy.unit (.program (toLexProgram (rowProgram rowH1))) ≠
      elabState cfgM Sp.u Sy.unit (.program (rowProgram rowH1)) := by
  intro same
  simp only [elabState, Core.run.injEq] at same
  exact translation_differs same.2.2

/-- **And they are statically equivalent**: one judgment of the identity model
reads both. -/
theorem translation_equivalent :
    CoreEquiv (elabState cfgLF Sp.u Sy.unit (.program (toLexProgram (rowProgram rowH1))))
      (elabState cfgM Sp.u Sy.unit (.program (rowProgram rowH1))) :=
  toLexical_core_equiv Sp.u Sy.unit rowH1_admissible

/-! ## Admissible programs, readings -/

/-- Negative: a program whose query is a parameter that no lambda binds is not
admissible. -/
theorem freeParameter_not_admissible :
    ¬ (⟨fun _ => none, .par Sp.z⟩ : Program Sy Sp).Admissible := by
  rintro ⟨-, query⟩
  exact absurd query (by decide)

/-- Negative: a judgment whose query is contextual code is read by no judgment
of the identity model. -/
theorem ctx_not_read {S X : Type} [DecidableEq X] (prog : S → Option (Tm S (Slot X)))
    (ks : List (Nm (Slot X))) (body : Tm S (Slot X)) (prog₂ : S → Option (Tm S (BId X)))
    (t₂ : Tm S (BId X)) : ¬ Reads prog (.ctx ks body) prog₂ t₂ := by
  rintro ⟨_, _, reading, program, -, -, same, -, -⟩
  exact elabCfg_ne_ctx reading.config [] program.query ks body same.symm

/-! ## Explicit and plain text -/

/-- The text of `ownList_order_witness`: the source is plain and not explicit;
its explicit form is explicit and not plain. -/
theorem explicit_examples :
    explicit orderSource = false ∧ lamPlain orderSource = true ∧
      explicit orderExplicit = true ∧ lamPlain orderExplicit = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `(lam z (($a $b) (lam w $a))){}`: a lambda with a crossing set around a
lambda without one. -/
def mixedLambdas : Src Unit ℕ :=
  .lam 2 (some []) (.app (.app (.sv 0) (.sv 1)) (.lam 3 none (.sv 0)))

/-- **Negative: outside plain text, writing out what the query-wide policy
inferred is not exact.**  The inner lambda now shares `$a`, and the own list of
the outer lambda changes its order. -/
theorem explicateQ_needs_plain :
    lamPlain mixedLambdas = false ∧
      elabQ (fun _ => []) [] (explicateQ mixedLambdas) ≠ elabQ (fun _ => []) [] mixedLambdas := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Positive, on the same text: writing out what explicit capture inferred is
exact. -/
theorem explicateEC_mixedLambdas :
    elabEC (fun _ => []) [] (explicateEC mixedLambdas) = elabEC (fun _ => []) [] mixedLambdas :=
  elabEC_explicateEC mixedLambdas _ _

/-- `(form z (let $a z $a))`: a lambda formed at run time around a `let` that
carries no crossing set. -/
def formedPlainLet : Src Unit ℕ :=
  .form 2 (.letS (.sv 0) (.par 2) (.sv 0) none)

/-- The same text with the crossing set `{}` written on the `let`. -/
def formedExplicitLet : Src Unit ℕ :=
  .form 2 (.letS (.sv 0) (.par 2) (.sv 0) (some []))

/-- **A lambda formed at run time is explicit exactly when its body is.**
Negative: around a plain `let` the text is not explicit, and rule M and lexical
fresh elaborate it to two terms.  Positive: with the crossing set written the
text is explicit, and the two elaborations are one. -/
theorem formed_explicit_examples :
    explicit formedPlainLet = false ∧
      elabForm .mercury [] formedPlainLet ≠ elabForm .lexicalFresh [] formedPlainLet ∧
        explicit formedExplicitLet = true ∧
          elabForm .mercury [] formedExplicitLet =
            elabForm .lexicalFresh [] formedExplicitLet := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Separation, realization -/

/-- Negative: a configuration is not separated from itself. -/
theorem not_separated_self (c : Config) : ¬ Separated c c :=
  fun separated => separated.1 (Translates.id c Sp.u Sy.unit _)

/-- Negative: the program with no equation does not realize a region that
declares one. -/
theorem empty_not_realizes : ¬ Realizes Sp.u Sy.unit mercuryRegion fun _ => none := by
  intro realizes
  have found := realizes.1 mercuryEntry (Finset.mem_singleton.mpr rfl)
  cases found

/-! ## Images -/

section Images

universe u v

variable {S : Type u} {X : Type v} [DecidableEq X]

/-- **The image of explicit capture is contained in the image of every
ownership policy**, at one lifetime and readout. -/
theorem explicitCapture_image_subset (ownership : Ownership) (lifetime : Lifetime)
    (readout : Readout) (u : X) (unit : S) (text : Program S X) :
    ∃ text' : Program S X,
      elabState ⟨ownership, lifetime, readout⟩ u unit (.program text') =
        elabState ⟨.explicitCapture, lifetime, readout⟩ u unit (.program text) :=
  ⟨text.map explicateEC, elabState_explicateEC ownership lifetime readout u unit text⟩

/-- **On explicit programs every ownership policy has the same image.** -/
theorem explicit_image_eq (ownership ownership' : Ownership) (lifetime : Lifetime)
    (readout : Readout) (u : X) (unit : S) (judgment : Core S X) :
    (∃ text : Program S X, text.Explicit ∧
        elabState ⟨ownership, lifetime, readout⟩ u unit (.program text) = judgment) ↔
      ∃ text : Program S X, text.Explicit ∧
        elabState ⟨ownership', lifetime, readout⟩ u unit (.program text) = judgment := by
  constructor
  · rintro ⟨text, written, same⟩
    exact ⟨text, written, (elabState_explicit ownership' ownership lifetime readout u unit
      written).trans same⟩
  · rintro ⟨text, written, same⟩
    exact ⟨text, written, (elabState_explicit ownership ownership' lifetime readout u unit
      written).trans same⟩

/-- On programs whose lambdas carry no crossing set, the image of the
query-wide policy and of lexical fresh is contained in the image of every
ownership policy. -/
theorem plain_image_subset (ownership : Ownership) (lifetime : Lifetime) (readout : Readout)
    (u : X) (unit : S) {text : Program S X} (plain : text.All fun t => lamPlain t = true) :
    (∃ text' : Program S X,
      elabState ⟨ownership, lifetime, readout⟩ u unit (.program text') =
        elabState ⟨.queryWide, lifetime, readout⟩ u unit (.program text)) ∧
    ∃ text' : Program S X,
      elabState ⟨ownership, lifetime, readout⟩ u unit (.program text') =
        elabState ⟨.lexicalFresh, lifetime, readout⟩ u unit (.program text) :=
  ⟨⟨text.map explicateQ, elabState_explicateQ ownership lifetime readout u unit plain⟩,
    ⟨text.map (explicateLF []), elabState_explicateLF ownership lifetime readout u unit plain⟩⟩

end Images

#print axioms translation_differs
#print axioms translation_equivalent
#print axioms explicateQ_needs_plain
#print axioms explicitCapture_image_subset
#print axioms explicit_image_eq

end Mettapedia.GSLT.LanguageDef.ScopePolicies
