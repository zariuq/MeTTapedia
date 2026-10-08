import Mettapedia.Logic.HostingStyles.Catamorphisms
import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCorpus
import Mettapedia.GSLT.LanguageDef.ScopePolicies.Explication

/-!
# Which translators are folds

A translation is a fold where the source syntax is free and each term former
becomes one fixed operation on translations
(`Mettapedia.Logic.HostingStyles.Catamorphisms`: `RuleSignature.fold_unique`).

Authored text is free syntax: `Src S X` is the derivations of the rule
signature of its term formers (`srcSignature`, `ofSrc`, `toSrc`,
`toSrc_ofSrc`).  A quotation is a constant of that signature: the code it
holds is data, no policy elaborates it, and it is not a part.  A map of text is a fold when it is the fold of an algebra of
that signature on text (`IsFold`).

* `isFold_of_compositional` — a map that sends each term former to one
  operation on the translations of the parts is a fold; this is
  `RuleSignature.fold_unique`.
* `IsFold.app_left`, `IsFold.let_body` — a fold sends an application, and a
  `let`, of parts with equal translations to equal translations.

So:

* `explicateEC_isFold`, `explicateQ_isFold` — writing out what explicit
  capture, and what the query-wide policy, inferred is a fold.  Each crossing
  set is computed from the translated parts alone.
* `toLexical_not_fold` — the translator from rule M to lexical fresh is not a
  fold.  `(lam z $hole)` and `(lam z (new ($hole) $hole))` have one
  translation; next to an outsider `$hole` their translations differ, because
  rule M's ownership of a name depends on the names written around the lambda.
* `explicateLF_not_fold` — writing out what lexical fresh inferred, from the
  root, is not a fold either: what a `let` introduces depends on the names in
  force around it.

The last two are defined by recursion on the text with a context passed down
(the names quantified outside, the names in force, the environment, the
position), and they read the untranslated part as well as its translation.
That is primitive recursion on free syntax into context-indexed translations,
which is not a fold into text.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.Logic.HostingStyles
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus

/-! ## Authored text as free syntax -/

/-- The term formers of authored text, with what each carries beside its
parts. -/
inductive SrcFormer (S X : Type) where
  | sym (s : S)
  | fn (F : S)
  | sv (y : X)
  | par (z : X)
  | lam (z : X) (crossing : Option (List X))
  | form (z : X)
  | app
  | quote (code : Src S X)
  | pquote (code : Src S X)
  | letS (crossing : Option (List X))
  | unify
  | alt
  | new (names : List X)

variable {S X : Type}

/-- The number of parts. -/
def SrcFormer.arity : SrcFormer S X → Nat
  | .sym _ => 0
  | .fn _ => 0
  | .sv _ => 0
  | .par _ => 0
  | .lam _ _ => 1
  | .form _ => 1
  | .app => 2
  | .quote _ => 0
  | .pquote _ => 0
  | .letS _ => 3
  | .unify => 3
  | .alt => 2
  | .new _ => 1

/-- **The formation rules of authored text**: one judgment, one rule for each
term former. -/
def srcSignature (S X : Type) : RuleSignature Unit where
  Shape := fun _ _ => SrcFormer S X
  Position := fun former => Fin former.arity
  next := fun _ _ => ()

/-- Build a text from a term former and its parts. -/
def SrcFormer.build : (former : SrcFormer S X) → (Fin former.arity → Src S X) → Src S X
  | .sym s, _ => .sym s
  | .fn F, _ => .fn F
  | .sv y, _ => .sv y
  | .par z, _ => .par z
  | .lam z xs, parts => .lam z xs (parts ⟨0, Nat.zero_lt_one⟩)
  | .form z, parts => .form z (parts ⟨0, Nat.zero_lt_one⟩)
  | .app, parts => .app (parts ⟨0, Nat.zero_lt_two⟩) (parts ⟨1, Nat.one_lt_two⟩)
  | .quote c, _ => .quote c
  | .pquote c, _ => .pquote c
  | .letS xs, parts =>
      .letS (parts ⟨0, Nat.succ_pos 2⟩) (parts ⟨1, Nat.one_lt_succ_succ 1⟩) (parts ⟨2, Nat.lt_succ_self 2⟩) xs
  | .unify, parts => .unify (parts ⟨0, Nat.succ_pos 2⟩) (parts ⟨1, Nat.one_lt_succ_succ 1⟩) (parts ⟨2, Nat.lt_succ_self 2⟩)
  | .alt, parts => .alt (parts ⟨0, Nat.zero_lt_two⟩) (parts ⟨1, Nat.one_lt_two⟩)
  | .new ys, parts => .new ys (parts ⟨0, Nat.zero_lt_one⟩)

/-- A text, as a derivation of the formation rules. -/
def ofSrc : Src S X → (srcSignature S X).Proof ()
  | .sym s => (srcSignature S X).node (.sym s) fun position => position.elim0
  | .fn F => (srcSignature S X).node (.fn F) fun position => position.elim0
  | .sv y => (srcSignature S X).node (.sv y) fun position => position.elim0
  | .par z => (srcSignature S X).node (.par z) fun position => position.elim0
  | .lam z xs b => (srcSignature S X).node (.lam z xs) fun _ => ofSrc b
  | .form z b => (srcSignature S X).node (.form z) fun _ => ofSrc b
  | .app f a => (srcSignature S X).node .app ![ofSrc f, ofSrc a]
  | .quote c => (srcSignature S X).node (.quote c) fun position => position.elim0
  | .pquote c => (srcSignature S X).node (.pquote c) fun position => position.elim0
  | .letS p w b xs => (srcSignature S X).node (.letS xs) ![ofSrc p, ofSrc w, ofSrc b]
  | .unify p w b => (srcSignature S X).node .unify ![ofSrc p, ofSrc w, ofSrc b]
  | .alt t₁ t₂ => (srcSignature S X).node .alt ![ofSrc t₁, ofSrc t₂]
  | .new ys b => (srcSignature S X).node (.new ys) fun _ => ofSrc b

/-- A derivation of the formation rules, as a text. -/
noncomputable def toSrc {judgment : Unit} (formed : (srcSignature S X).Proof judgment) :
    Src S X :=
  Fix.fold (srcSignature S X) (carrier := fun _ _ => Src S X)
    (fun _ _ layer => SrcFormer.build layer.1 layer.2) PUnit.unit judgment formed

/-- Reading a rule application is building from the readings of its
premises. -/
theorem toSrc_node (former : SrcFormer S X)
    (children : Fin former.arity → (srcSignature S X).Proof ()) :
    toSrc ((srcSignature S X).node (j := ()) former children) =
      former.build fun position => toSrc (children position) :=
  rfl

/-- **Authored text is the derivations of its formation rules.** -/
theorem toSrc_ofSrc : ∀ t : Src S X, toSrc (ofSrc t) = t
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv _ => rfl
  | .par _ => rfl
  | .lam z xs b => by
      show Src.lam z xs (toSrc (ofSrc b)) = _
      rw [toSrc_ofSrc b]
  | .form z b => by
      show Src.form z (toSrc (ofSrc b)) = _
      rw [toSrc_ofSrc b]
  | .app f a => by
      show Src.app (toSrc (ofSrc f)) (toSrc (ofSrc a)) = _
      rw [toSrc_ofSrc f, toSrc_ofSrc a]
  | .quote _ => rfl
  | .pquote _ => rfl
  | .letS p w b xs => by
      show Src.letS (toSrc (ofSrc p)) (toSrc (ofSrc w)) (toSrc (ofSrc b)) xs = _
      rw [toSrc_ofSrc p, toSrc_ofSrc w, toSrc_ofSrc b]
  | .unify p w b => by
      show Src.unify (toSrc (ofSrc p)) (toSrc (ofSrc w)) (toSrc (ofSrc b)) = _
      rw [toSrc_ofSrc p, toSrc_ofSrc w, toSrc_ofSrc b]
  | .alt t₁ t₂ => by
      show Src.alt (toSrc (ofSrc t₁)) (toSrc (ofSrc t₂)) = _
      rw [toSrc_ofSrc t₁, toSrc_ofSrc t₂]
  | .new ys b => by
      show Src.new ys (toSrc (ofSrc b)) = _
      rw [toSrc_ofSrc b]

/-! ## Folds -/

/-- **A map of text is a fold**: the fold of an algebra of the formation rules
on text. -/
def IsFold (translate : Src S X → Src S X) : Prop :=
  ∃ algebra : (srcSignature S X).Algebra (fun _ _ => Src S X),
    ∀ t, translate t = Fix.fold (srcSignature S X) algebra.act PUnit.unit () (ofSrc t)

/-- **A map that sends each term former to one operation on the translations
of the parts is a fold** (`RuleSignature.fold_unique`). -/
theorem isFold_of_compositional (translate : Src S X → Src S X)
    (operation : (former : SrcFormer S X) → (Fin former.arity → Src S X) → Src S X)
    (commutes : ∀ (former : SrcFormer S X) (parts : Fin former.arity → Src S X),
      translate (former.build parts) = operation former fun position => translate (parts position)) :
    IsFold translate := by
  refine ⟨{ act := fun _ _ layer => operation layer.1 layer.2 }, fun t => ?_⟩
  have folded := (srcSignature S X).fold_unique
    { act := fun _ _ layer => operation layer.1 layer.2 }
    (fun _ formed => translate (toSrc formed))
    (fun shape children => commutes shape fun position => toSrc (children position))
    (ofSrc t)
  rw [← folded, toSrc_ofSrc]

/-- A fold sends applications of functions with one translation to one
translation. -/
theorem IsFold.app_left {translate : Src S X → Src S X} (fold : IsFold translate)
    {first second : Src S X} (same : translate first = translate second) (argument : Src S X) :
    translate (.app first argument) = translate (.app second argument) := by
  obtain ⟨algebra, isFold⟩ := fold
  have unfolded : ∀ function : Src S X, translate (.app function argument) =
      algebra.act PUnit.unit () ⟨.app, ![translate function, translate argument]⟩ := by
    intro function
    rw [isFold, isFold function, isFold argument]
    show algebra.act PUnit.unit () ⟨.app, _⟩ = _
    congr 2
    funext position
    refine Fin.cases rfl (fun rest => ?_) position
    refine Fin.cases rfl (fun impossible => impossible.elim0) rest
  rw [unfolded first, unfolded second, same]

/-- A fold sends `let`s of bodies with one translation to one translation. -/
theorem IsFold.let_body {translate : Src S X → Src S X} (fold : IsFold translate)
    {first second : Src S X} (same : translate first = translate second) (pattern value : Src S X)
    (crossing : Option (List X)) :
    translate (.letS pattern value first crossing) =
      translate (.letS pattern value second crossing) := by
  obtain ⟨algebra, isFold⟩ := fold
  have unfolded : ∀ body : Src S X, translate (.letS pattern value body crossing) =
      algebra.act PUnit.unit ()
        ⟨.letS crossing, ![translate pattern, translate value, translate body]⟩ := by
    intro body
    rw [isFold, isFold pattern, isFold value, isFold body]
    show algebra.act PUnit.unit () ⟨.letS crossing, _⟩ = _
    congr 2
    funext position
    refine Fin.cases rfl (fun rest => ?_) position
    refine Fin.cases rfl (fun rest => ?_) rest
    refine Fin.cases rfl (fun impossible => impossible.elim0) rest
  rw [unfolded first, unfolded second, same]

/-! ## The explications that are folds -/

/-- What each term former becomes under `explicateEC`. -/
def explicateECOperation : (former : SrcFormer S X) → (Fin former.arity → Src S X) → Src S X
  | .lam z none, parts => .lam z (some []) (parts ⟨0, Nat.zero_lt_one⟩)
  | .letS none, parts =>
      .letS (parts ⟨0, Nat.succ_pos 2⟩) (parts ⟨1, Nat.one_lt_succ_succ 1⟩) (parts ⟨2, Nat.lt_succ_self 2⟩)
        (some (Src.patNames (parts ⟨0, Nat.succ_pos 2⟩)))
  | former, parts => former.build parts

/-- **Writing out what explicit capture inferred is a fold.** -/
theorem explicateEC_isFold : IsFold (explicateEC (S := S) (X := X)) := by
  refine isFold_of_compositional _ explicateECOperation fun former parts => ?_
  cases former with
  | lam z crossing => cases crossing <;> rfl
  | letS crossing =>
      cases crossing with
      | none =>
          show Src.letS _ _ _ (some (Src.patNames (parts ⟨0, Nat.succ_pos 2⟩))) =
            Src.letS _ _ _ (some (Src.patNames (explicateEC (parts ⟨0, Nat.succ_pos 2⟩))))
          rw [patNames_explicateEC]
      | some _ => rfl
  | _ => rfl

/-- What each term former becomes under `explicateQ`. -/
def explicateQOperation : (former : SrcFormer S X) → (Fin former.arity → Src S X) → Src S X
  | .lam z none, parts =>
      .lam z (some (Src.uses (parts ⟨0, Nat.zero_lt_one⟩))) (parts ⟨0, Nat.zero_lt_one⟩)
  | .letS none, parts =>
      .letS (parts ⟨0, Nat.succ_pos 2⟩) (parts ⟨1, Nat.one_lt_succ_succ 1⟩) (parts ⟨2, Nat.lt_succ_self 2⟩)
        (some (Src.patNames (parts ⟨0, Nat.succ_pos 2⟩)))
  | former, parts => former.build parts

/-- **Writing out what the query-wide policy inferred is a fold.** -/
theorem explicateQ_isFold : IsFold (explicateQ (S := S) (X := X)) := by
  refine isFold_of_compositional _ explicateQOperation fun former parts => ?_
  cases former with
  | lam z crossing => cases crossing <;> rfl
  | letS crossing =>
      cases crossing with
      | none =>
          show Src.letS _ _ _ (some (Src.patNames (parts ⟨0, Nat.succ_pos 2⟩))) =
            Src.letS _ _ _ (some (Src.patNames (explicateQ (parts ⟨0, Nat.succ_pos 2⟩))))
          rw [patNames_explicateQ]
      | some _ => rfl
  | _ => rfl

/-! ## The translators that are not folds -/

/-- `(lam z $hole)`. -/
def bareHole : A := lm .z (sv .hole)

/-- `(lam z (new ($hole) $hole))`. -/
def declaredHole : A := lm .z (.new [.hole] (sv .hole))

/-- The two have one translation; next to an outsider `$hole` they do not. -/
theorem toLexical_hole :
    toLexical bareHole = toLexical declaredHole ∧
      toLexical (.app bareHole (sv .hole)) ≠ toLexical (.app declaredHole (sv .hole)) := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **The translator from rule M to lexical fresh is not a fold.** -/
theorem toLexical_not_fold : ¬ IsFold (toLexical (S := Sy) (X := Sp)) :=
  fun fold => toLexical_hole.2 (fold.app_left toLexical_hole.1 (sv .hole))

/-- `(let $y n1 ok)`, and the same with the crossing set `{}`. -/
def plainLet : A := .letS (sv .y) (k .n1) (k .ok) none
def freshLet : A := .letS (sv .y) (k .n1) (k .ok) (some [])

/-- From the root the two have one explicit form; inside a `let` that shares
`$y` they do not. -/
theorem explicateLF_let :
    explicateLF [] plainLet = explicateLF [] freshLet ∧
      explicateLF [] (.letS (sv .y) (k .n2) plainLet (some [.y])) ≠
        explicateLF [] (.letS (sv .y) (k .n2) freshLet (some [.y])) := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **Writing out what lexical fresh inferred, from the root, is not a
fold.** -/
theorem explicateLF_not_fold : ¬ IsFold (explicateLF (S := Sy) ([] : List Sp)) :=
  fun fold => explicateLF_let.2 (fold.let_body explicateLF_let.1 (sv .y) (k .n2) (some [.y]))

#print axioms toSrc_ofSrc
#print axioms isFold_of_compositional
#print axioms explicateEC_isFold
#print axioms explicateQ_isFold
#print axioms toLexical_not_fold
#print axioms explicateLF_not_fold

end Mettapedia.GSLT.LanguageDef.ScopePolicies
