import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Encoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Contextual

/-!
# The translation: one schema per equation and six control rules

The target is `RuleSyntax.step` at the contextual frames of the data signature
(`Interface.Frames.contextual S`: declaration frames, contextual assignments, and syntactic equality
of terms, so matching is the solving of equations between terms with second-order unknowns, modulo
nothing; for left sides in the pattern class that is second-order pattern unification), with firings
extending the frame by declarations (`RuleSyntax.Contextual.declarations S`) and occurrences numbered
by `ℕ`.

**The control rules**, the same for every program (`controlRules`), each over five unknowns in the
ambient context (`Unknown`): a datum `T`, a pattern `P`, computations `C` and `D`, a stack `FS`.
* `retRule`: `alt(eval(ret T), FS)` ⟶ `alt(value T, FS)`;
* `unmatchedRule`: `alt(eval(apply T), FS)` ⟶ `alt(value T, FS)` when no equation row matches:
  the check `absent eqn(T)`;
* `choiceLeftRule`, `choiceRightRule`: `alt(eval(choice C D), FS)` ⟶ `alt(eval C, FS)`, resp.
  `alt(eval D, FS)`;
* `bindStartRule`: `alt(eval(bind P C D), FS)` ⟶ `alt(eval C, push(P, D, FS))`;
* `bindValueRule`: `alt(value T, push(P, D, FS))` ⟶ `alt(eval D, FS)`, telling `P ≐ T`.
There is no rule for `fail`: an alternative that fails has no continuation.

**The schema of an equation** (`schema`): its unknowns are the source's names and a stack; it takes
`alt(eval(apply lhs), FS)` and makes `alt(eval rhs, FS)`. The left side is matched against the call by
the take equation, two ways, in the knowledge; the right side is the encoded computation with the
equation's names opened by the firing (fresh at every use).

**The translation** (`translate`) is the control rules and one schema per equation, so it sends the
union of programs to the union of rule sets (`translate_union`). That is a statement about rules. A
hosted program is its rules and its rows: the program's left sides are also present as rows
`eqn(lhs)` with private names (`start`), which the negative test of an unmatched call reads, and the
correspondence theorems are about the rules run from those rows. The rows of a union, and what a
hosted program survives beside rows and rules that are not its own, are in `Hosting.Composition`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Interface.Frames (Frame)

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)

/-! ## Named nodes -/

section Named

variable {V : Type} {D : V → MetaArity S}

abbrev altN (x y : Term (signature S D) Γ star) : Term (signature S D) Γ star := N.node .alt ![x, y]
abbrev evalN (x : Term (signature S D) Γ star) : Term (signature S D) Γ star := N.node .eval ![x]
abbrev valueN (x : Term (signature S D) Γ star) : Term (signature S D) Γ star := N.node .value ![x]
abbrev retN (x : Term (signature S D) Γ star) : Term (signature S D) Γ star := N.node .ret ![x]
abbrev applyN (x : Term (signature S D) Γ star) : Term (signature S D) Γ star := N.node .apply ![x]
abbrev choiceN (x y : Term (signature S D) Γ star) : Term (signature S D) Γ star := N.node .choice ![x, y]
abbrev bindN (x y z : Term (signature S D) Γ star) : Term (signature S D) Γ star := N.node .bind ![x, y, z]
abbrev emptyN : Term (signature S D) Γ star := N.node .empty ![]
abbrev pushN (x y z : Term (signature S D) Γ star) : Term (signature S D) Γ star := N.node .push ![x, y, z]
abbrev eqnN (x : Term (signature S D) Γ star) : Term (signature S D) Γ star := N.node .eqn ![x]

end Named

/-! ## The control rules -/

/-- The unknowns of a control rule. -/
inductive Unknown where
  | datum
  | pattern
  | first
  | second
  | stack
  deriving DecidableEq

variable (Γ star) in
/-- Every unknown of a control rule is a term in the ambient context at the top sort. -/
def unknownArity : Unknown → MetaArity S := fun _ => (Γ, star)

variable (Γ star) in
/-- The frame of a control rule's unknowns. -/
abbrev controlFrame : Frame S := ⟨Unknown, unknownArity Γ star⟩

/-- An unknown of a control rule, as a term. -/
def unk (x : Unknown) : Term (signature S (unknownArity Γ star)) Γ star :=
  generator (unknownArity Γ star) x

/-- `alt(eval(ret T), FS)` ⟶ `alt(value T, FS)`. -/
def retRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S) where
  locals := controlFrame Γ star
  body := { take := [observe (altN N (evalN N (retN N (unk .datum))) (unk .stack))], read := [], tell := [],
            checks := [], produce := [observe (altN N (valueN N (unk .datum)) (unk .stack))] }
  collect := []

/-- `alt(eval(apply T), FS)` ⟶ `alt(value T, FS)`, when no row `eqn(T)` matches. -/
def unmatchedRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S) where
  locals := controlFrame Γ star
  body := { take := [observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack))], read := [], tell := [],
            checks := [.predicate .none (observe (eqnN N (unk .datum)))],
            produce := [observe (altN N (valueN N (unk .datum)) (unk .stack))] }
  collect := []

/-- `alt(eval(choice C D), FS)` ⟶ `alt(eval C, FS)`. -/
def choiceLeftRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S) where
  locals := controlFrame Γ star
  body := { take := [observe (altN N (evalN N (choiceN N (unk .first) (unk .second))) (unk .stack))],
            read := [], tell := [], checks := [],
            produce := [observe (altN N (evalN N (unk .first)) (unk .stack))] }
  collect := []

/-- `alt(eval(choice C D), FS)` ⟶ `alt(eval D, FS)`. -/
def choiceRightRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S) where
  locals := controlFrame Γ star
  body := { take := [observe (altN N (evalN N (choiceN N (unk .first) (unk .second))) (unk .stack))],
            read := [], tell := [], checks := [],
            produce := [observe (altN N (evalN N (unk .second)) (unk .stack))] }
  collect := []

/-- `alt(eval(bind P C D), FS)` ⟶ `alt(eval C, push(P, D, FS))`. -/
def bindStartRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S) where
  locals := controlFrame Γ star
  body := { take := [observe (altN N (evalN N (bindN N (unk .pattern) (unk .first) (unk .second)))
                (unk .stack))],
            read := [], tell := [], checks := [],
            produce := [observe (altN N (evalN N (unk .first))
              (pushN N (unk .pattern) (unk .second) (unk .stack)))] }
  collect := []

/-- `alt(value T, push(P, D, FS))` ⟶ `alt(eval D, FS)`, telling `P ≐ T`. -/
def bindValueRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S) where
  locals := controlFrame Γ star
  body := { take := [observe (altN N (valueN N (unk .datum))
                (pushN N (unk .pattern) (unk .second) (unk .stack)))],
            read := [], tell := [(observe (unk .pattern), observe (unk .datum))], checks := [],
            produce := [observe (altN N (evalN N (unk .second)) (unk .stack))] }
  collect := []

/-- **The control rules**: six, the same for every program. -/
def controlRules : Set (RuleSyntax.Rule (RuleSyntax.Contextual.Terms S)) :=
  {retRule N, unmatchedRule N, choiceLeftRule N, choiceRightRule N, bindStartRule N, bindValueRule N}

/-! ## The schema of an equation -/

section Schema

variable {κ : Keys S} {Ty : Type}

variable (Γ star κ) in
/-- The unknowns of a schema: every name of the source, and the stack. -/
abbrev schemaArity : Name κ ⊕ Unit → MetaArity S := Sum.elim (fam κ) (fun _ => (Γ, star))

variable (Γ star κ) in
/-- The frame of a schema's unknowns. -/
abbrev schemaFrame : Frame S := ⟨Name κ ⊕ Unit, schemaArity Γ star κ⟩

/-- The source's names as the schema's unknowns. -/
def asUnknowns : Assignment (fam κ) (schemaArity Γ star κ) :=
  fun x => generator (schemaArity Γ star κ) (.inl x)

/-- The schema's stack. -/
def schemaStack : Term (signature S (schemaArity Γ star κ)) Γ star :=
  generator (schemaArity Γ star κ) (.inr ())

/-- **The schema of an equation**: take `alt(eval(apply lhs), FS)`, make `alt(eval rhs, FS)`. -/
def schema (e : SourceLanguage.Equation κ Γ star Ty) : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S) where
  locals := schemaFrame Γ star κ
  body := { take := [observe (altN N (evalN N (applyN N (instantiate asUnknowns e.lhs))) schemaStack)],
            read := [], tell := [], checks := [],
            produce := [observe (altN N (evalN N (encComp N (instantiate asUnknowns) e.rhs)) schemaStack)] }
  collect := []

/-! ## The translation -/

/-- **The translation of a program**: the control rules and one schema per equation. Programs that
read text as code (`run`) are outside the fragment; the reading `reflect` is not used. -/
def translate (P : SourceLanguage.Program κ Γ star Ty) : RuleSyntax.Program (RuleSyntax.Contextual.Terms S) :=
  controlRules N ∪ {r | ∃ e ∈ P.equations, r = schema N e}

theorem mem_translate {P : SourceLanguage.Program κ Γ star Ty} {r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S)} :
    r ∈ translate N P ↔ r ∈ controlRules N ∨ ∃ e ∈ P.equations, r = schema N e :=
  Iff.rfl

theorem mem_controlRules {r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S)} :
    r ∈ controlRules N ↔ r = retRule N ∨ r = unmatchedRule N ∨ r = choiceLeftRule N ∨
      r = choiceRightRule N ∨ r = bindStartRule N ∨ r = bindValueRule N := by
  simp [controlRules]

/-- **The rules of a union**: the translation of a union of programs is the union of the translations;
the control rules are shared. This is about the sets of rules; the equation rows of a union are
`Composition.equationRows_union`, and rules and rows together `Composition.hosted_union`. -/
theorem translate_union (P Q : SourceLanguage.Program κ Γ star Ty) :
    translate N (P.union Q) = translate N P ∪ translate N Q := by
  ext r
  constructor
  · rintro (control | ⟨e, member, rfl⟩)
    · exact .inl (.inl control)
    · rcases List.mem_append.mp member with left | right
      · exact .inl (.inr ⟨e, left, rfl⟩)
      · exact .inr (.inr ⟨e, right, rfl⟩)
  · rintro ((control | ⟨e, member, rfl⟩) | (control | ⟨e, member, rfl⟩))
    · exact .inl control
    · exact .inr ⟨e, List.mem_append.mpr (.inl member), rfl⟩
    · exact .inl control
    · exact .inr ⟨e, List.mem_append.mpr (.inr member), rfl⟩

/-- **No rule per term**: every rule of a translation is a control rule or the schema of one of the
program's equations; this is the definition of `translate` read as an inclusion. The query being run
is not an argument of `translate`: it contributes a row of the start, and no rule. -/
theorem translate_rules (P : SourceLanguage.Program κ Γ star Ty) :
    translate N P ⊆ controlRules N ∪ {r | ∃ e ∈ P.equations, r = schema N e} :=
  fun _ member => member

/-! ## The start of a run -/

variable (κ) in
/-- The names at the start: the source's names, and a private copy of them for each equation row. -/
abbrev startArity : Name κ ⊕ (ℕ × Name κ) → MetaArity S := Sum.elim (fam κ) (fun p => fam κ p.2)

variable (κ) in
/-- The frame at the start. -/
abbrev startFrame : Frame S := ⟨Name κ ⊕ (ℕ × Name κ), startArity κ⟩

/-- The source's names at the start. -/
def queryNames : Assignment (fam κ) (startArity κ) :=
  fun x => generator (startArity κ) (.inl x)

/-- The private copy of the names for the row of equation `i`. -/
def rowNames (i : ℕ) : Assignment (fam κ) (startArity κ) :=
  fun x => generator (startArity κ) (.inr (i, x))

/-- The rows at the start: equation `i`'s left side at its private names for `i` below the number of
equations, and the query's alternative at that number. -/
def startLabel (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) (o : ℕ) :
    Observation S (startArity κ) :=
  if h : o < P.equations.length then
    observe (eqnN N (instantiate (rowNames o) (P.equations.get ⟨o, h⟩).lhs))
  else observe (encAlt N (instantiate queryNames) (.eval q) [])

/-- **The start of a run** of query `q`: no knowledge, the equation rows `0, …, m - 1` and the
alternative `m`, for `m` equations. -/
def start (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) :
    RuleSyntax.State (RuleSyntax.Contextual.Terms S) ℕ :=
  ⟨startFrame κ, [], insert P.equations.length (Finset.range P.equations.length), startLabel N P q⟩

/-- The start's caller embedding can be read back without changing the
identity or parameter context of any caller name. -/
theorem instantiate_queryNames_injective :
    Function.Injective (instantiate (queryNames (κ := κ)) : Data κ Γ star → _) := by
  let forget : Assignment (startArity κ) (fam κ) :=
    fun
    | .inl name => generator (fam κ) name
    | .inr (_, name) => generator (fam κ) name
  have restores (t : Data κ Γ star) : instantiate forget (instantiate queryNames t) = t := by
    rw [instantiate_comp]
    have composed : (fun name => instantiate forget (queryNames name)) = generator (fam κ) := by
      funext name
      rw [queryNames, instantiate_generator]
    rw [composed, instantiate_identity]
  intro t u same
  exact (restores t).symm.trans ((congrArg (instantiate forget) same).trans (restores u))

/-- In the initial alternative, a held query retains its addressed space,
pattern, and template at their original caller names. -/
theorem start_held_query_components (P : SourceLanguage.Program κ Γ star Ty)
    {space pattern template otherSpace otherPattern otherTemplate : Data κ Γ star}
    (same : start N P (.query space pattern (.ret template)) =
      start N P (.query otherSpace otherPattern (.ret otherTemplate))) :
    space = otherSpace ∧ pattern = otherPattern ∧ template = otherTemplate := by
  let entry (s : RuleSyntax.State (RuleSyntax.Contextual.Terms S) ℕ) :
      Σ frame, RuleSyntax.Contextual.Terms S frame := ⟨s.frame, s.label P.equations.length⟩
  have images := congrArg entry same
  have labels : startLabel N P (.query space pattern (.ret template)) P.equations.length =
      startLabel N P (.query otherSpace otherPattern (.ret otherTemplate)) P.equations.length :=
    eq_of_heq (Sigma.mk.inj_iff.mp images).2
  simp only [startLabel, lt_irrefl, encAlt, encFocus, encComp] at labels
  have focus := (vec2_inj (N.args_eq (observe_injective labels))).1
  have query := vec1_inj (N.args_eq focus)
  obtain ⟨onSpace, onPattern, onBody⟩ := vec3_inj (N.args_eq query)
  exact ⟨instantiate_queryNames_injective onSpace, instantiate_queryNames_injective onPattern,
    instantiate_queryNames_injective (vec1_inj (N.args_eq onBody))⟩

end Schema

/-! ## The step of a translated program -/

/-- **The step of the translated program**: `RuleSyntax.step` at the contextual frames with
extensions by declarations. -/
abbrev hostStep {κ : Keys S} {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) :=
  RuleSyntax.step (Interface.Frames.contextual S) ℕ (RuleSyntax.Contextual.declarations S) (translate N P)

/-- **The frames match modulo syntax only**: the equality of the contextual frames is equality of
terms. No equation of the source is part of it; equations are rules. -/
theorem contextual_equality {F : Frame S} (a b : Observation S F.arity) :
    (Interface.Frames.contextual S).E a b ↔ a = b :=
  Iff.rfl

#print axioms translate_union
#print axioms mem_controlRules
#print axioms contextual_equality

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
