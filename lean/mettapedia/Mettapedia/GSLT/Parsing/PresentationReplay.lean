import Mettapedia.GSLT.Parsing.PresentationExprSemantics

/-!
# Checking finite derivations of presentation expressions

The certificate records only choices and reference occurrences. Token values,
classes, referenced definitions, source positions and CST output are checked
or reconstructed from the supplied presentation and immutable source. The
returned witness inhabits the pre-existing presentation semantics.

Fuel bounds certificate checking, not source rejection. Failure of this
checker must not be reported as evidence that the grammar rejects the input.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PresentationReplay

open LanguageDefSyntaxCompiler PresentationExprSemantics

inductive Certificate where
  | leaf
  | unary (child : Certificate)
  | pair (first second : Certificate)
  | choice (right : Bool) (child : Certificate)
  | reference (occurrence : Nat) (child : Certificate)
  deriving DecidableEq, Repr

abbrev ClassTest := String → Nat → Bool

abbrev Result (classes : ClassTest) (presentation : Presentation) (input : List Nat)
    (expression : Expr) (start : Nat) :=
  Σ stop, RecognizesAtUsing (fun name cp => classes name cp = true) presentation input expression start stop

def replay (classes : ClassTest) (presentation : Presentation) (input : List Nat) :
    (fuel : Nat) → (expression : Expr) → Certificate → (start : Nat) →
      Option (Result classes presentation input expression start)
  | 0, _, _, _ => none
  | _ + 1, .epsilon, .leaf, start => some ⟨start, .epsilon start⟩
  | _ + 1, .char cp, .leaf, start =>
      if found : input[start]? = some cp then some ⟨start + 1, .char found⟩ else none
  | _ + 1, .class name, .leaf, start =>
      match found : input[start]? with
      | none => none
      | some cp =>
          if recognized : classes name cp = true then some ⟨start + 1, .classMember found recognized⟩ else none
  | _ + 1, .literal codepoints, .leaf, start =>
      if matched : input.extract start (start + codepoints.length) = codepoints then
        some ⟨start + codepoints.length, .literal matched⟩ else none
  | fuel + 1, .alt first _, .choice false child, start => do
      let ⟨stop, run⟩ ← replay classes presentation input fuel first child start
      return ⟨stop, .altLeft run⟩
  | fuel + 1, .alt _ second, .choice true child, start => do
      let ⟨stop, run⟩ ← replay classes presentation input fuel second child start
      return ⟨stop, .altRight run⟩
  | fuel + 1, .seq first second, .pair left right, start => do
      let ⟨middle, leftRun⟩ ← replay classes presentation input fuel first left start
      let ⟨stop, rightRun⟩ ← replay classes presentation input fuel second right middle
      return ⟨stop, .seq leftRun rightRun⟩
  | fuel + 1, .left first second, .pair left right, start => do
      let ⟨middle, leftRun⟩ ← replay classes presentation input fuel first left start
      let ⟨stop, rightRun⟩ ← replay classes presentation input fuel second right middle
      return ⟨stop, .left leftRun rightRun⟩
  | fuel + 1, .right first second, .pair left right, start => do
      let ⟨middle, leftRun⟩ ← replay classes presentation input fuel first left start
      let ⟨stop, rightRun⟩ ← replay classes presentation input fuel second right middle
      return ⟨stop, .right leftRun rightRun⟩
  | fuel + 1, .node _ body, .unary child, start => do
      let ⟨stop, run⟩ ← replay classes presentation input fuel body child start
      return ⟨stop, .node run⟩
  | fuel + 1, .ref name, .reference occurrence child, start => do
      if bounded : occurrence < presentation.definitions.length then
        let definition := presentation.definitions.get ⟨occurrence, bounded⟩
        if named : definition.name = name then
          let ⟨stop, run⟩ ← replay classes presentation input fuel definition.body child start
          return ⟨stop, .ref definition (List.get_mem presentation.definitions ⟨occurrence, bounded⟩) named run⟩
        else none
      else none
  | _ + 1, .star _, .leaf, start => some ⟨start, .starZero start⟩
  | fuel + 1, .star body, .pair head tail, start => do
      let ⟨middle, headRun⟩ ← replay classes presentation input fuel body head start
      if advances : start < middle then
        let ⟨stop, tailRun⟩ ← replay classes presentation input fuel (.star body) tail middle
        return ⟨stop, .starMore headRun advances tailRun⟩
      else none
  | fuel + 1, .plus body, .pair head tail, start => do
      let ⟨middle, headRun⟩ ← replay classes presentation input fuel body head start
      if advances : start < middle then
        let ⟨stop, tailRun⟩ ← replay classes presentation input fuel (.star body) tail middle
        return ⟨stop, .plus headRun advances tailRun⟩
      else none
  | _ + 1, .eof, .leaf, start =>
      if ended : start = input.length then some ⟨start, .eof ended⟩ else none
  | _ + 1, _, _, _ => none

/-- Certificate height supplies a checking budget without guessing from the
number of input tokens. Every recursive check descends to a child certificate. -/
def Certificate.height : Certificate → Nat
  | .leaf => 1
  | .unary child | .choice _ child | .reference _ child => child.height + 1
  | .pair first second => max first.height second.height + 1

def check (classes : ClassTest) (presentation : Presentation) (input : List Nat)
    (expression : Expr) (certificate : Certificate) (start : Nat) :
    Option (Result classes presentation input expression start) :=
  replay classes presentation input certificate.height expression certificate start

def observe (classes : ClassTest) (presentation : Presentation) (input : List Nat)
    (expression : Expr) (certificate : Certificate) (start : Nat) : Option (Nat × List CST) :=
  (check classes presentation input expression certificate start).map fun ⟨stop, run⟩ => (stop, run.cst)

theorem observe_sound {classes : ClassTest} {presentation : Presentation} {input : List Nat}
    {expression : Expr} {certificate : Certificate} {start stop : Nat} {output : List CST}
    (accepted : observe classes presentation input expression certificate start = some (stop, output)) :
    Nonempty (CSTRecognizesAtUsing (fun name cp => classes name cp = true)
      presentation input expression start stop output) := by
  unfold observe at accepted
  cases checked : check classes presentation input expression certificate start with
  | none => simp [checked] at accepted
  | some result =>
      rcases result with ⟨last, run⟩
      simp only [checked, Option.map_some, Option.some.injEq, Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact ⟨⟨run, rfl⟩⟩

namespace Controls

def noClasses : ClassTest := fun _ _ => false
def emptyPresentation : Presentation := ⟨"controls", [], []⟩

theorem matching_character :
    observe noClasses emptyPresentation [97] (.char 97) .leaf 0 =
      some (1, [.terminal [97] 0 1]) := by decide

theorem changed_character_refused :
    observe noClasses emptyPresentation [98] (.char 97) .leaf 0 = none := by decide

theorem wrong_reference_refused :
    observe noClasses ⟨"references", [⟨"different", .char 97⟩], []⟩ [97]
      (.ref "wanted") (.reference 0 .leaf) 0 = none := by decide

theorem zero_width_repeat_refused :
    observe noClasses emptyPresentation [] (.star .epsilon) (.pair .leaf .leaf) 0 = none := by decide

end Controls

end Mettapedia.GSLT.Parsing.PresentationReplay
