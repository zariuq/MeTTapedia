import Mettapedia.GSLT.Parsing.EbnfHelperNameSource
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

/-!
# The authored EBNF width scan bounds occupied names

This is an observation of existing source S-expressions, not another grammar
representation or executable compiler. Selected source equations preserve the
width observation. Their composed paths therefore bound names at the relevant
positions of the original structured document and authority.

The string provider is an explicit boundary: freshness only requires that it
returns a structured text, not that a guessed string decoder is correct. The
theorems concern completed source paths, not native termination, the complete
lowering traversal, or correctness of the C evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.EbnfWidthSource

open Algorithms.MeTTa.Simple.Parser (SExpr)
open EbnfRepetitionSource (app loweringSyntax equation? closeEquation?)
open EbnfHelperNameSource (text unary helperText)
open SourceSExprPatternInstantiation (Env instantiate? instantiateList?)

/-- Maximum occupied-name width, extended to the scan's intermediate calls.
Literal contents, comments, spans and other metadata are not grammar names.
String payloads have lower bound zero until the external codec returns text. -/
def width : SExpr → Nat
  | .list [.atom "bnf-v1:text-cons", _, tail] => width tail + 1
  | .list [.atom "ebnf-v1:s", tail] => width tail + 1
  | .list [.atom "ebnf-v1:max", left, right] => max (width left) (width right)
  | .list [.atom "bnf-v1:entries-cons", left, right]
  | .list [.atom "bnf-v1:alternatives-cons", left, right]
  | .list [.atom "bnf-v1:elements-cons", left, right]
  | .list [.atom "bnf-v1:lexical-declarations-cons", left, right] =>
      max (width left) (width right)
  | .list [.atom "bnf-v1:rule", name, expression, _] =>
      max (width name) (width expression)
  | .list [.atom "bnf-v1:lexical-declaration", name, _, _, _, _] => width name
  | .list [.atom "bnf-v1:expression", body, _]
  | .list [.atom "bnf-v1:alternative", body, _]
  | .list [.atom "bnf-v1:reference", body, _]
  | .list [.atom "ebnf-v1:group", body, _]
  | .list [.atom "ebnf-v1:optional", body, _]
  | .list [.atom "ebnf-v1:zero-or-more", body, _]
  | .list [.atom "ebnf-v1:one-or-more", body, _]
  | .list [.atom "ebnf-v1:text-width", body]
  | .list [.atom "ebnf-v1:width-entries", body]
  | .list [.atom "ebnf-v1:width-entry", body]
  | .list [.atom "ebnf-v1:width-alternatives", body]
  | .list [.atom "ebnf-v1:width-alternative", body]
  | .list [.atom "ebnf-v1:width-elements", body]
  | .list [.atom "ebnf-v1:width-element", body]
  | .list [.atom "ebnf-v1:width-expression", body]
  | .list [.atom "ebnf-v1:width-lexicals", body]
  | .list [.atom "ebnf-v1:width-lexical", body] => width body
  | _ => 0

@[simp] theorem width_text (word : List Nat) : width (text word) = word.length := by
  induction word with
  | nil => rfl
  | cons cp tail ih => simpa [text, app, width] using ih

@[simp] theorem width_unary (n : Nat) : width (unary n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [unary, app, width] using ih

/-- An explicit view used only to reduce the finite selected source inventory.
Every row below is checked against its authored occurrence, not used as a
replacement program. -/
private def observedEquation (row : Fin 25) : SExpr × SExpr :=
  let v := SExpr.atom
  let a := app
  match row.val with
  | 0 => (a "ebnf-v1:text-width" [a "bnf-v1:text-nil" []], unary 0)
  | 1 => (a "ebnf-v1:text-width" [a "bnf-v1:text-cons" [v "?cp", v "?tail"]],
      a "ebnf-v1:s" [a "ebnf-v1:text-width" [v "?tail"]])
  | 2 => (a "ebnf-v1:max" [unary 0, v "?right"], v "?right")
  | 3 => (a "ebnf-v1:max" [a "ebnf-v1:s" [v "?left"], unary 0],
      a "ebnf-v1:s" [v "?left"])
  | 4 => (a "ebnf-v1:max" [a "ebnf-v1:s" [v "?left"], a "ebnf-v1:s" [v "?right"]],
      a "ebnf-v1:s" [a "ebnf-v1:max" [v "?left", v "?right"]])
  | 5 => (a "ebnf-v1:width-entries" [a "bnf-v1:entries-nil" []], unary 0)
  | 6 => (a "ebnf-v1:width-entries" [a "bnf-v1:entries-cons" [v "?head", v "?tail"]],
      a "ebnf-v1:max" [a "ebnf-v1:width-entry" [v "?head"], a "ebnf-v1:width-entries" [v "?tail"]])
  | 7 => (a "ebnf-v1:width-alternatives" [a "bnf-v1:alternatives-nil" []], unary 0)
  | 8 => (a "ebnf-v1:width-alternatives" [a "bnf-v1:alternatives-cons" [v "?head", v "?tail"]],
      a "ebnf-v1:max" [a "ebnf-v1:width-alternative" [v "?head"], a "ebnf-v1:width-alternatives" [v "?tail"]])
  | 9 => (a "ebnf-v1:width-elements" [a "bnf-v1:elements-nil" []], unary 0)
  | 10 => (a "ebnf-v1:width-elements" [a "bnf-v1:elements-cons" [v "?head", v "?tail"]],
      a "ebnf-v1:max" [a "ebnf-v1:width-element" [v "?head"], a "ebnf-v1:width-elements" [v "?tail"]])
  | 11 => (a "ebnf-v1:width-lexicals" [a "bnf-v1:lexical-declarations-nil" []], unary 0)
  | 12 => (a "ebnf-v1:width-lexicals" [a "bnf-v1:lexical-declarations-cons" [v "?head", v "?tail"]],
      a "ebnf-v1:max" [a "ebnf-v1:width-lexical" [v "?head"], a "ebnf-v1:width-lexicals" [v "?tail"]])
  | 13 => (a "ebnf-v1:width-entry" [a "bnf-v1:rule" [v "?name", v "?expr", v "?span"]],
      a "ebnf-v1:max" [a "ebnf-v1:text-width" [v "?name"], a "ebnf-v1:width-expression" [v "?expr"]])
  | 14 => (a "ebnf-v1:width-entry" [a "bnf-v1:comment" [v "?text", v "?span"]], unary 0)
  | 15 => (a "ebnf-v1:width-entry" [a "bnf-v1:blank" [v "?span"]], unary 0)
  | 16 => (a "ebnf-v1:width-expression" [a "bnf-v1:expression" [v "?alts", v "?span"]],
      a "ebnf-v1:width-alternatives" [v "?alts"])
  | 17 => (a "ebnf-v1:width-alternative" [a "bnf-v1:alternative" [v "?elems", v "?span"]],
      a "ebnf-v1:width-elements" [v "?elems"])
  | 18 => (a "ebnf-v1:width-element" [a "bnf-v1:reference" [v "?name", v "?span"]],
      a "ebnf-v1:text-width" [v "?name"])
  | 19 => (a "ebnf-v1:width-element" [a "bnf-v1:literal" [v "?text", v "?span"]], unary 0)
  | 20 => (a "ebnf-v1:width-element" [a "ebnf-v1:group" [v "?expr", v "?span"]],
      a "ebnf-v1:width-expression" [v "?expr"])
  | 21 => (a "ebnf-v1:width-element" [a "ebnf-v1:optional" [v "?body", v "?span"]],
      a "ebnf-v1:width-element" [v "?body"])
  | 22 => (a "ebnf-v1:width-element" [a "ebnf-v1:zero-or-more" [v "?body", v "?span"]],
      a "ebnf-v1:width-element" [v "?body"])
  | 23 => (a "ebnf-v1:width-element" [a "ebnf-v1:one-or-more" [v "?body", v "?span"]],
      a "ebnf-v1:width-element" [v "?body"])
  | _ => (a "ebnf-v1:width-lexical"
      [a "bnf-v1:lexical-declaration" [v "?name", v "?klass", v "?matcher", v "?label", v "?origin"]],
      a "ebnf-v1:max" [a "ebnf-v1:text-width" [v "?name"],
        a "ebnf-v1:max" [a "ebnf-v1:text-width" [a "bnf-v1:string->text" [v "?klass"]],
          a "ebnf-v1:text-width" [a "bnf-v1:string->text" [v "?label"]]]])

def occurrence (row : Fin 25) : Nat := if row.val < 5 then row.val else row.val + 5

private theorem source_inventory (row : Fin 25) :
    equation? loweringSyntax (occurrence row) = some (observedEquation row) := by
  fin_cases row <;> rfl

theorem source_width_preserved (row : Fin 25) (env : Env) (before after : SExpr)
    (closed : closeEquation? loweringSyntax (occurrence row) env = some (before, after)) :
    width before = width after := by
  unfold closeEquation? at closed
  rw [source_inventory] at closed
  fin_cases row <;>
    simp [observedEquation, unary, app, instantiate?, instantiateList?,
      SourceIntegerProvider.sourceVariableToken,
      Option.bind_eq_some_iff, Option.map_eq_some_iff] at closed
  all_goals grind [width]

/-- Only the scan's active argument positions are closed under steps. Source
payloads and arbitrary constructor fields are not made reduction-active. -/
inductive Step (Codec : SExpr → List Nat → Prop) : SExpr → SExpr → Prop where
  | source (row : Fin 25) (env : Env) {before after : SExpr} :
      closeEquation? loweringSyntax (occurrence row) env = some (before, after) →
      Step Codec before after
  | successor {before after : SExpr} : Step Codec before after →
      Step Codec (app "ebnf-v1:s" [before]) (app "ebnf-v1:s" [after])
  | maximumLeft {before after right : SExpr} : Step Codec before after →
      Step Codec (app "ebnf-v1:max" [before, right]) (app "ebnf-v1:max" [after, right])
  | maximumRight {before after left : SExpr} : Step Codec before after →
      Step Codec (app "ebnf-v1:max" [left, before]) (app "ebnf-v1:max" [left, after])
  | textArgument {before after : SExpr} : Step Codec before after →
      Step Codec (app "ebnf-v1:text-width" [before]) (app "ebnf-v1:text-width" [after])
  | codec {input : SExpr} {word : List Nat} : Codec input word →
      Step Codec (app "bnf-v1:string->text" [input]) (text word)

abbrev Path (Codec : SExpr → List Nat → Prop) := Relation.ReflTransGen (Step Codec)

theorem step_width_le {Codec : SExpr → List Nat → Prop} {before after : SExpr}
    (step : Step Codec before after) : width before ≤ width after := by
  induction step with
  | source row env closed => exact (source_width_preserved row env _ _ closed).le
  | successor _ ih => simpa [app, width] using Nat.add_le_add_right ih 1
  | maximumLeft _ ih => exact max_le_max_right _ ih
  | maximumRight _ ih => exact max_le_max_left _ ih
  | textArgument _ ih => exact ih
  | codec _ => exact Nat.zero_le _

theorem path_width_le {Codec : SExpr → List Nat → Prop} {before after : SExpr}
    (path : Path Codec before after) : width before ≤ width after := by
  induction path with
  | refl => exact Nat.le_refl _
  | tail _ step ih => exact ih.trans (step_width_le step)

/-- Name-occurrence existence in the existing grammar wire. This predicate
does not count occurrences or claim preservation of derivation multiplicity. -/
inductive NameAt (name : List Nat) : SExpr → Prop where
  | reference (span : SExpr) : NameAt name (app "bnf-v1:reference" [text name, span])
  | declaration (body span : SExpr) : NameAt name (app "bnf-v1:rule" [text name, body, span])
  | lexical (klass matcher label origin : SExpr) :
      NameAt name (app "bnf-v1:lexical-declaration" [text name, klass, matcher, label, origin])
  | ruleBody {body : SExpr} (declaredName span : SExpr) : NameAt name body →
      NameAt name (app "bnf-v1:rule" [declaredName, body, span])
  | expression {body : SExpr} (span : SExpr) : NameAt name body →
      NameAt name (app "bnf-v1:expression" [body, span])
  | alternative {body : SExpr} (span : SExpr) : NameAt name body →
      NameAt name (app "bnf-v1:alternative" [body, span])
  | group {body : SExpr} (span : SExpr) : NameAt name body →
      NameAt name (app "ebnf-v1:group" [body, span])
  | optional {body : SExpr} (span : SExpr) : NameAt name body →
      NameAt name (app "ebnf-v1:optional" [body, span])
  | star {body : SExpr} (span : SExpr) : NameAt name body →
      NameAt name (app "ebnf-v1:zero-or-more" [body, span])
  | plus {body : SExpr} (span : SExpr) : NameAt name body →
      NameAt name (app "ebnf-v1:one-or-more" [body, span])
  | head (tag : String) {head : SExpr} (tail : SExpr) :
      tag ∈ ["bnf-v1:entries-cons", "bnf-v1:alternatives-cons",
        "bnf-v1:elements-cons", "bnf-v1:lexical-declarations-cons"] →
      NameAt name head → NameAt name (app tag [head, tail])
  | tail (tag : String) (head : SExpr) {tail : SExpr} :
      tag ∈ ["bnf-v1:entries-cons", "bnf-v1:alternatives-cons",
        "bnf-v1:elements-cons", "bnf-v1:lexical-declarations-cons"] →
      NameAt name tail → NameAt name (app tag [head, tail])

theorem name_width_le {name : List Nat} {value : SExpr} (found : NameAt name value) :
    name.length ≤ width value := by
  induction found with
  | reference span => simp [app, width]
  | declaration body span => simp [app, width]
  | lexical klass matcher label origin => simp [app, width]
  | ruleBody declaredName span _ ih => exact ih.trans (Nat.le_max_right _ _)
  | expression span _ ih | alternative span _ ih | group span _ ih
    | optional span _ ih | star span _ ih | plus span _ ih => exact ih
  | head tag tail member _ ih =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact ih.trans (Nat.le_max_left _ _)
  | tail tag head member _ ih =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact ih.trans (Nat.le_max_right _ _)

def scan (start : List Nat) (entries lexicals : SExpr) : SExpr :=
  app "ebnf-v1:max" [app "ebnf-v1:text-width" [text start],
    app "ebnf-v1:max" [app "ebnf-v1:width-entries" [entries],
      app "ebnf-v1:width-lexicals" [lexicals]]]

/-- The lower-document rule actually installs this scan beneath prefix,
before the helper traversal starts. The arbitrary payloads are unchanged. -/
theorem lower_document_uses_scan (start : List Nat) (entries lexicals span : SExpr) :
    closeEquation? loweringSyntax 30
      [("?entries", entries), ("?span", span), ("?start", text start), ("?lexicals", lexicals)] =
    some (app "ebnf-v1:lower" [app "bnf-v1:document" [entries, span],
      app "bnf-v1:grammar-authority" [app "bnf-v1:start" [text start],
        app "bnf-v1:lexical-environment" [lexicals]]],
      app "ebnf-v1:finish" [app "ebnf-v1:lower-entries" [entries,
        EbnfHelperNameSource.state (app "ebnf-v1:prefix" [scan start entries lexicals])
          (text [48]) (app "bnf-v1:entries-nil" []) (app "ebnf-v1:origins-nil" [])
          (.atom "ebnf-v1:outside-rule")], span]) := by
  have selected : equation? loweringSyntax 30 = some
      (app "ebnf-v1:lower" [app "bnf-v1:document" [.atom "?entries", .atom "?span"],
        app "bnf-v1:grammar-authority" [app "bnf-v1:start" [.atom "?start"],
          app "bnf-v1:lexical-environment" [.atom "?lexicals"]]],
        app "ebnf-v1:finish" [app "ebnf-v1:lower-entries" [.atom "?entries",
          EbnfHelperNameSource.state (app "ebnf-v1:prefix"
            [app "ebnf-v1:max" [app "ebnf-v1:text-width" [.atom "?start"],
              app "ebnf-v1:max" [app "ebnf-v1:width-entries" [.atom "?entries"],
                app "ebnf-v1:width-lexicals" [.atom "?lexicals"]]]])
            (text [48]) (app "bnf-v1:entries-nil" []) (app "ebnf-v1:origins-nil" [])
            (.atom "ebnf-v1:outside-rule")], .atom "?span"]) := rfl
  simp [closeEquation?, selected, EbnfHelperNameSource.state, scan, text, app,
    instantiate?, instantiateList?, SourceIntegerProvider.sourceVariableToken]

/-- The bound is obtained from a completed authored source path, not assumed
as a separate precondition of the freshness theorem. -/
theorem scan_bounds {Codec : SExpr → List Nat → Prop} (start : List Nat)
    (entries lexicals : SExpr) (result : Nat)
    (completed : Path Codec (scan start entries lexicals) (unary result)) :
    start.length ≤ result ∧
      (∀ name, NameAt name entries → name.length ≤ result) ∧
      (∀ name, NameAt name lexicals → name.length ≤ result) := by
  have bound : max start.length (max (width entries) (width lexicals)) ≤ result := by
    simpa [scan, app, width] using path_width_le completed
  refine ⟨(Nat.le_max_left _ _).trans bound, ?_, ?_⟩
  · intro name found
    exact (name_width_le found).trans
      ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans bound))
  · intro name found
    exact (name_width_le found).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans bound))

theorem helper_fresh_after_scan {Codec : SExpr → List Nat → Prop} (start : List Nat)
    (entries lexicals : SExpr) (result : Nat)
    (completed : Path Codec (scan start entries lexicals) (unary result))
    (initial : List Bool) (allocation : Nat) :
    helperText result initial allocation ≠ text start ∧
      (∀ name, NameAt name entries → helperText result initial allocation ≠ text name) ∧
      (∀ name, NameAt name lexicals → helperText result initial allocation ≠ text name) := by
  obtain ⟨startBound, entryBound, lexicalBound⟩ := scan_bounds start entries lexicals result completed
  exact ⟨EbnfHelperNameSource.helperText_not_existing result initial allocation start startBound,
    fun name found => EbnfHelperNameSource.helperText_not_existing result initial allocation name
      (entryBound name found),
    fun name found => EbnfHelperNameSource.helperText_not_existing result initial allocation name
      (lexicalBound name found)⟩

private theorem lift_path {Codec : SExpr → List Nat → Prop} (f : SExpr → SExpr)
    (compatible : ∀ {a b}, Step Codec a b → Step Codec (f a) (f b))
    {a b : SExpr} (path : Path Codec a b) : Path Codec (f a) (f b) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (compatible step)

/-- Positive all-length witness: the actual two text-width rules terminate
at the independently counted length. This is not a sampled computation. -/
theorem text_width_path (Codec : SExpr → List Nat → Prop) (word : List Nat) :
    Path Codec (app "ebnf-v1:text-width" [text word]) (unary word.length) := by
  induction word with
  | nil =>
      apply Relation.ReflTransGen.single (Step.source 0 [] ?_)
      unfold closeEquation?
      rw [source_inventory]
      simp [observedEquation, app, text, unary, instantiate?, instantiateList?,
        SourceIntegerProvider.sourceVariableToken]
  | cons cp tail ih =>
      have first : Step Codec (app "ebnf-v1:text-width" [text (cp :: tail)])
          (app "ebnf-v1:s" [app "ebnf-v1:text-width" [text tail]]) := by
        apply Step.source 1 [("?cp", .atom (toString cp)), ("?tail", text tail)]
        unfold closeEquation?
        rw [source_inventory]
        simp [observedEquation, app, text, instantiate?, instantiateList?,
          SourceIntegerProvider.sourceVariableToken]
      exact (Relation.ReflTransGen.single first).trans
        (lift_path (fun x => app "ebnf-v1:s" [x]) Step.successor ih)

theorem max_path (Codec : SExpr → List Nat → Prop) (left right : Nat) :
    Path Codec (app "ebnf-v1:max" [unary left, unary right]) (unary (max left right)) := by
  induction left generalizing right with
  | zero =>
      apply Relation.ReflTransGen.single (Step.source 2 [("?right", unary right)] ?_)
      unfold closeEquation?
      rw [source_inventory]
      simp [observedEquation, app, unary, instantiate?, instantiateList?,
        SourceIntegerProvider.sourceVariableToken]
  | succ left ih =>
      cases right with
      | zero =>
          apply Relation.ReflTransGen.single (Step.source 3 [("?left", unary left)] ?_)
          unfold closeEquation?
          rw [source_inventory]
          simp [observedEquation, app, unary, instantiate?, instantiateList?,
            SourceIntegerProvider.sourceVariableToken]
      | succ right =>
          have first : Step Codec (app "ebnf-v1:max" [unary (left + 1), unary (right + 1)])
              (app "ebnf-v1:s" [app "ebnf-v1:max" [unary left, unary right]]) := by
            apply Step.source 4 [("?left", unary left), ("?right", unary right)]
            unfold closeEquation?
            rw [source_inventory]
            simp [observedEquation, app, unary, instantiate?, instantiateList?,
              SourceIntegerProvider.sourceVariableToken]
          simpa [Nat.add_max_add_right, unary] using (Relation.ReflTransGen.single first).trans
            (lift_path (fun x => app "ebnf-v1:s" [x]) Step.successor (ih right))

/-- Composition executes the source maximum, rather than merely comparing
the input and output width observations. -/
theorem maximum_paths {Codec : SExpr → List Nat → Prop} {a b : SExpr} {m n : Nat}
    (left : Path Codec a (unary m)) (right : Path Codec b (unary n)) :
    Path Codec (app "ebnf-v1:max" [a, b]) (unary (max m n)) :=
  (lift_path (fun x => app "ebnf-v1:max" [x, b]) Step.maximumLeft left).trans
    ((lift_path (fun x => app "ebnf-v1:max" [unary m, x]) Step.maximumRight right).trans
      (max_path Codec m n))

theorem scan_components_path {Codec : SExpr → List Nat → Prop} (start : List Nat)
    {entries lexicals : SExpr} {entryWidth lexicalWidth : Nat}
    (entryPath : Path Codec (app "ebnf-v1:width-entries" [entries]) (unary entryWidth))
    (lexicalPath : Path Codec (app "ebnf-v1:width-lexicals" [lexicals]) (unary lexicalWidth)) :
    Path Codec (scan start entries lexicals)
      (unary (max start.length (max entryWidth lexicalWidth))) :=
  maximum_paths (text_width_path Codec start) (maximum_paths entryPath lexicalPath)

/-- The complete top scan has non-vacuous executions for arbitrary start
words, without an external codec or assumed width bound. -/
theorem empty_scan_path (Codec : SExpr → List Nat → Prop) (start : List Nat) :
    Path Codec (scan start (app "bnf-v1:entries-nil" [])
      (app "bnf-v1:lexical-declarations-nil" [])) (unary start.length) := by
  have entry : Path Codec (app "ebnf-v1:width-entries" [app "bnf-v1:entries-nil" []])
      (unary 0) := by
    apply Relation.ReflTransGen.single (Step.source 5 [] ?_)
    unfold closeEquation?
    rw [source_inventory]
    simp [observedEquation, app, unary, instantiate?, instantiateList?,
      SourceIntegerProvider.sourceVariableToken]
  have lexical : Path Codec
      (app "ebnf-v1:width-lexicals" [app "bnf-v1:lexical-declarations-nil" []]) (unary 0) := by
    apply Relation.ReflTransGen.single (Step.source 11 [] ?_)
    unfold closeEquation?
    rw [source_inventory]
    simp [observedEquation, app, unary, instantiate?, instantiateList?,
      SourceIntegerProvider.sourceVariableToken]
  simpa using scan_components_path start entry lexical

/-- An unbounded nested-wire specimen, not a second grammar datatype. -/
def nestedReference (word : List Nat) (span : SExpr) : Nat → SExpr
  | 0 => app "bnf-v1:reference" [text word, span]
  | depth + 1 => app "ebnf-v1:optional" [nestedReference word span depth, span]

theorem nested_reference_name (word : List Nat) (span : SExpr) (depth : Nat) :
    NameAt word (nestedReference word span depth) := by
  induction depth with
  | zero => exact .reference span
  | succ depth ih => exact .optional span ih

/-- Actual source executions for every word and every nesting depth. In
particular the completed-path premise is not limited to empty grammars. -/
theorem nested_reference_path (Codec : SExpr → List Nat → Prop) (word : List Nat)
    (span : SExpr) (depth : Nat) :
    Path Codec (app "ebnf-v1:width-element" [nestedReference word span depth])
      (unary word.length) := by
  induction depth with
  | zero =>
      have first : Step Codec
          (app "ebnf-v1:width-element" [nestedReference word span 0])
          (app "ebnf-v1:text-width" [text word]) := by
        apply Step.source 18 [("?name", text word), ("?span", span)]
        unfold closeEquation?
        rw [source_inventory]
        simp [observedEquation, nestedReference, app, instantiate?, instantiateList?,
          SourceIntegerProvider.sourceVariableToken]
      exact (Relation.ReflTransGen.single first).trans (text_width_path Codec word)
  | succ depth ih =>
      have first : Step Codec
          (app "ebnf-v1:width-element" [nestedReference word span (depth + 1)])
          (app "ebnf-v1:width-element" [nestedReference word span depth]) := by
        apply Step.source 21 [("?body", nestedReference word span depth), ("?span", span)]
        unfold closeEquation?
        rw [source_inventory]
        simp [observedEquation, nestedReference, app, instantiate?, instantiateList?,
          SourceIntegerProvider.sourceVariableToken]
      exact (Relation.ReflTransGen.single first).trans ih

/-- Dropping a nested reference from the scan cannot be licensed as a valid
completed source path when that reference is longer than the claimed bound. -/
theorem cannot_return_short_width {Codec : SExpr → List Nat → Prop}
    (start name : List Nat) (entries lexicals : SExpr) (result : Nat)
    (found : NameAt name entries) (tooShort : result < name.length) :
    ¬ Path Codec (scan start entries lexicals) (unary result) := by
  intro completed
  exact (Nat.not_le_of_lt tooShort) ((scan_bounds start entries lexicals result completed).2.1 name found)

/-- A control distinguishing references from literal contents. -/
theorem literal_contents_are_not_names (word : List Nat) (span : SExpr) :
    width (app "bnf-v1:literal" [text word, span]) = 0 := rfl

end Mettapedia.GSLT.Parsing.EbnfWidthSource
