import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotRenaming
import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCorpus

/-!
# Template scope: the renaming theorem on examples

Kernel-checked computations on the scope corpus and on four small programs.

* `rows_admissible`, `rows_hyp` — every row of the corpus (80 queries with
  their equations) is admissible, so `renaming_M`, `renaming_LF` and
  `transfer` apply to every row.
* `rows_per_result` — on all 80 rows, printing each result with its own naming
  gives the same bag in both models, under rule M and under lexical fresh: what
  a renaming per result predicts.
* `code_identity_not_spelling`, `code_match_identity`, `pqLam_agrees` — a binder
  inside code is its position. `(lam w w)` and `(lam z z)` are the same code
  in both models, and the first matches the second; `(lam w z)` does not,
  because one `z` is free. The written names still differ as terms. The
  program `pqLam` answers `ok` in both models, under both profiles.
* `copy_binder_stays_binder`, `copy_hole_stays_hole` — an activation copy keeps
  the hole bit. A copied code binder stays a binder and does not capture; a
  copied query-root hole stays a hole and does.
* `gotCtx_view`, `gotCtx_fill`, `gotCtx_resist` — contextual quotation, on a
  local symbol table so the corpus export is untouched.
  `(let (quote (lam z $b)) (quote (lam z (f z))) (Got $b))` answers
  `(Got (quote (f z) (z)))` in both models, under both profiles, and lexical
  fresh answers the same on its translation. Filling that code with `7` and
  running answers `(f 7)`. Filling a different name leaves the quotation.
* `gotCtx_run_toLexical`, `gotCtx_transfer` — `run_toLexical` and `transfer`
  on that program.
* `pvar_var_no_capture`, `leak_code_no_capture`, `leak_answers`, `leak_not_bare`
  — a code binder does not capture a store name. The leak
  `(let (quote (lam w w)) (quote (lam z $hole)) (Got escaped $hole))` answers
  nothing in both models, under both profiles, so it does not answer
  `(Got escaped z)`.
* `open_is_activation`, `activation_fresh` — an opening is the shipped static
  activation. Two paths copy one owned name to two store names.
* `quote_own`, `quote_open` — the body `(let $u k (Pair $u $u))` owns `u`,
  and opening it renames that store name to the activation path.
* `template_map_one`, `template_map_two`, `template_map_shared` — one opening
  answers `(Pair n1 n1)`. Two openings, with the store threaded, answer
  `(List2 (Pair n1 n1) (Pair n2 n2))` at two activation paths. The same
  template with `$u` written outside owns nothing, and the two openings
  answer nothing.
* `newPat_needed`, `freePar_needed` — each remaining admissibility condition
  is needed: a program violating it, on which the two models' bags are not
  related.
* `alias_per_result` — the renaming is per result, not per bag: on an
  admissible program, two results of one bag share a frame-allocated name in the
  identity model where the slot model makes two names; the bag printed with one
  naming for the whole bag differs, the bag printed result by result agrees.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotExamples

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus
open Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCorpus
open Mettapedia.GSLT.LanguageDef.TemplateScope.Bridge
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

/-! ## The corpus -/

/-- **Every row of the corpus is admissible**: the query and every equation. -/
theorem rows_admissible :
    rows.all (fun r => decide r.src.Admissible &&
      allSy.all fun F => match r.clauseSet.cl F with
        | some b => decide b.Admissible
        | none => true) = true := by
  decide +kernel

theorem mem_allSy (F : Sy) : F ∈ allSy := by
  cases F <;> decide

/-- The hypotheses of the renaming theorems, on every row. -/
theorem rows_hyp : ∀ r ∈ rows, r.src.Admissible ∧
    ∀ F body, r.clauseSet.cl F = some body → body.Admissible := by
  intro r hr
  have h := List.all_eq_true.1 rows_admissible r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1, fun F body hb => ?_⟩
  have := h.2 F (mem_allSy F)
  rw [hb] at this
  simpa using this

/-- Every result printed with its own naming (slot model). -/
def perS (bag : Option (List T)) : Option (List (SExp (SAtom Sy Sp))) :=
  bag.map fun b => b.map fun r => printAns (bagNaming (allocated [r])) Bridge.parName r

/-- Every result printed with its own naming (identity model). -/
def perI (bag : Option (List TI)) : Option (List (SExp (SAtom Sy Sp))) :=
  bag.map fun b => b.map fun r => printAns (bagNamingI (allocatedI [r])) parNameI r

/-- **Result by result, the two models print alike on the whole corpus.** -/
theorem rows_per_result :
    rows.all (fun r =>
      decide (perS (SpectrumCorpus.ans cfgM r.clauseSet.cl r.src) = perI (ansMI r.clauseSet.cl r.src)) &&
      decide (perS (SpectrumCorpus.ans cfgLF r.clauseSet.cl r.src) =
        perI (ansLFI r.clauseSet.cl r.src))) = true := by
  decide +kernel

/-! ## Binders inside code -/

/-- No equations. -/
def noCl : Sy → Option A := fun _ => none

/-- **Written names are not identities.**  `(lam w w)` and `(lam z z)` are
different terms, because the spellings differ, and the same code in both
models: equality of code compares binder positions. -/
theorem code_identity_not_spelling :
    (codeOf (lm .w (pr .w)) ≠ codeOf (lm .z (pr .z))) ∧
      codeEq (codeOf (lm .w (pr .w))) (codeOf (lm .z (pr .z))) = true ∧
    (codeI (lm .w (pr .w)) ≠ codeI (lm .z (pr .z))) ∧
      codeEq (codeI (lm .w (pr .w))) (codeI (lm .z (pr .z))) = true ∧
      codeEq (codeOf (lm .w (pr .z))) (codeOf (lm .z (pr .z))) = false ∧
      codeEq (codeI (lm .w (pr .z))) (codeI (lm .z (pr .z))) = false := by
  decide +kernel

/-- **Matching uses those identities.**  The pattern `(lam z z)` matches the
code `(lam w w)` in both models.  It does not match `(lam w z)`: the pattern's
`z` is bound and the code's `z` is free. -/
theorem code_match_identity :
    (matchCode (Store.empty : GStore Sy (Slot Sp)) (codeOf (lm .z (pr .z)))
        (codeOf (lm .w (pr .w)))).isSome = true ∧
      (matchCode (Store.empty : GStore Sy (Slot Sp)) (codeOf (lm .z (pr .z)))
        (codeOf (lm .w (pr .z)))).isNone = true ∧
    (matchCode (Store.empty : GStore Sy (BId Sp)) (codeI (lm .z (pr .z)))
        (codeI (lm .w (pr .w)))).isSome = true ∧
      (matchCode (Store.empty : GStore Sy (BId Sp)) (codeI (lm .z (pr .z)))
        (codeI (lm .w (pr .z)))).isNone = true := by
  decide +kernel

/-- **An activation copy of a binder stays a binder.** `CodeId.hole` and
`holeRec` agree on the copy, in both models, and `matchCode` does not capture
through it. -/
theorem copy_binder_stays_binder :
    (CodeId.hole ((.inst [0] (.src (codeBinder [], .z))) : Nm (Slot Sp)) = false) ∧
      (holeRecS ((.inst [0] (.src (codeBinder [], .z))) : Nm (Slot Sp)) = false) ∧
    (CodeId.hole ((.inst [0] (.src (.code .z (codeBinder [])))) : Nm (BId Sp)) = false) ∧
      (holeRecI ((.inst [0] (.src (.code .z (codeBinder [])))) : Nm (BId Sp)) = false) ∧
    (matchCode (Store.empty : GStore Sy (Slot Sp))
      (.var (.inst [0] (.src (codeBinder [], .z)))) (.sym .ok)).isNone = true ∧
    (matchCode (Store.empty : GStore Sy (BId Sp))
      (.var (.inst [0] (.src (.code .z (codeBinder []))))) (.sym .ok)).isNone = true := by
  decide +kernel

/-- **An activation copy of a hole stays a hole.** `CodeId.hole` and `holeRec`
agree on the copy, in both models, and `matchCode` captures through it. -/
theorem copy_hole_stays_hole :
    (CodeId.hole ((.inst [0] (.src (([] : Owner), .z))) : Nm (Slot Sp)) = true) ∧
      (holeRecS ((.inst [0] (.src (([] : Owner), .z))) : Nm (Slot Sp)) = true) ∧
    (CodeId.hole ((.inst [0] (.src (.slot ⟨.z, [], [], .head⟩))) : Nm (BId Sp)) = true) ∧
      (holeRecI ((.inst [0] (.src (.slot ⟨.z, [], [], .head⟩))) : Nm (BId Sp)) = true) ∧
    (matchCode (Store.empty : GStore Sy (Slot Sp))
      (.var (.inst [0] (.src (([] : Owner), .z)))) (.sym .ok)).isSome = true ∧
    (matchCode (Store.empty : GStore Sy (BId Sp))
      (.var (.inst [0] (.src (.slot ⟨.z, [], [], .head⟩)))) (.sym .ok)).isSome = true := by
  decide +kernel

/-- A quotation in pattern position: a lambda in the pattern, against code. -/
def pqLam : A := .letS (.pquote (lm .z (pr .z))) (.quote (lm .z (pr .z))) (k .ok) none

/-- **The same answer in both models.**  `pqLam` returns `ok` under rule M and
under lexical fresh, in the slot model and in the identity model. -/
theorem pqLam_agrees :
    (run .static (progSlot cfgM .u .unit noCl) 80 [] Store.empty (elabCfg cfgM [] pqLam)).map
        (List.map Prod.fst) = some [.sym .ok] ∧
      (run .static (progM .u .unit noCl) 80 [] Store.empty (elabMFormAt [] pqLam)).map
        (List.map Prod.fst) = some [.sym .ok] ∧
    (run .static (progSlot cfgLF .u .unit noCl) 80 [] Store.empty (elabCfg cfgLF [] pqLam)).map
        (List.map Prod.fst) = some [.sym .ok] ∧
      (run .static (progLF .u .unit noCl) 80 [] Store.empty (elabLFFormAt [] pqLam)).map
        (List.map Prod.fst) = some [.sym .ok] := by
  decide +kernel

/-! ## Contextual quotation

The symbols are local. `Sy` is the corpus's symbol table, and these rows are
not part of the export. -/

/-- Symbols of the contextual-quotation program: `f`, `Got`, `7`, and the
clause wrapper's `unit`. -/
inductive QuoteSym where
  | f | Got | n7 | unit
  deriving DecidableEq, Repr

/-- Spellings of that program: the code binder `z`, the store name `b`, and
the clause wrapper's `u`. -/
inductive QuoteSp where
  | z | b | u
  deriving DecidableEq, Repr

/-- No equations. -/
def noQuote : QuoteSym → Option (Src QuoteSym QuoteSp) := fun _ => none

/-- `(let (quote (lam z $b)) (quote (lam z (f z))) (Got $b))`. -/
def gotCtx : Src QuoteSym QuoteSp :=
  .letS (.pquote (.lam .z none (.sv .b)))
    (.quote (.lam .z none (.app (.sym .f) (.par .z))))
    (.app (.sym .Got) (.sv .b)) none

def quoteSymText : QuoteSym → String
  | .f => "f" | .Got => "Got" | .n7 => "7" | .unit => "unit"

def quoteSpText : QuoteSp → String
  | .z => "z" | .b => "b" | .u => "u"

def quoteAtom : SAtom QuoteSym QuoteSp → String
  | .sym c => quoteSymText c
  | .kw k => kwText k
  | .var v => "$" ++ quoteSpText v
  | .fresh v n => "$" ++ quoteSpText v ++ "#" ++ toString n
  | .par v => quoteSpText v

/-- `(Got (quote (f z) (z)))`, as the answer printer writes it. -/
def gotSExp : SExp (SAtom QuoteSym QuoteSp) :=
  .list [.atom (.sym .Got),
    .list [.atom (.kw .quote),
      .list [.atom (.sym .f), .atom (.par .z)],
      .list [.atom (.par .z)]]]

/-- `(f 7)`. -/
def f7SExp : SExp (SAtom QuoteSym QuoteSp) :=
  .list [.atom (.sym .f), .atom (.sym .n7)]

/-- `(quote (f z) (z))`. -/
def quoteSExp : SExp (SAtom QuoteSym QuoteSp) :=
  .list [.atom (.kw .quote),
    .list [.atom (.sym .f), .atom (.par .z)],
    .list [.atom (.par .z)]]

/-- `(Got (f z))`, the ground term a capture would return. -/
def bareSExp : SExp (SAtom QuoteSym QuoteSp) :=
  .list [.atom (.sym .Got), .list [.atom (.sym .f), .atom (.par .z)]]

/-- `(Got (quote (f z)))`, a quotation that has dropped its binder list. -/
def droppedSExp : SExp (SAtom QuoteSym QuoteSp) :=
  .list [.atom (.sym .Got),
    .list [.atom (.kw .quote), .list [.atom (.sym .f), .atom (.par .z)]]]

/-- **The shipped renderer spells the contextual answer as the C text.** -/
theorem gotSExp_text :
    (gotSExp.render quoteAtom (fun _ => false)).toList =
      "(Got (quote (f z) (z)))".toList := by
  simp [gotSExp, SExp.render, SExp.renderList, SExp.renderSeq, quoteAtom, quoteSymText,
    quoteSpText, kwText]

/-- **The shipped renderer spells the filled term as the C text.** -/
theorem f7SExp_text :
    (f7SExp.render quoteAtom (fun _ => false)).toList = "(f 7)".toList := by
  simp [f7SExp, SExp.render, SExp.renderList, SExp.renderSeq, quoteAtom, quoteSymText]

/-- **The shipped renderer spells the unfilled code as the C text.** -/
theorem quoteSExp_text :
    (quoteSExp.render quoteAtom (fun _ => false)).toList =
      "(quote (f z) (z))".toList := by
  simp [quoteSExp, SExp.render, SExp.renderList, SExp.renderSeq, quoteAtom, quoteSymText,
    quoteSpText, kwText]

/-- The answer is `(Got (quote (f z) (…)))`: one code binder around `(f z)`. -/
def isGotCtx {Y : Type} : Tm QuoteSym Y → Bool
  | .app (.sym .Got) (.ctx [_] (.app (.sym .f) (.pvar _))) => true
  | _ => false

def slotPar (n : Nm (Slot QuoteSp)) : SAtom QuoteSym QuoteSp := .par n.spelling

def idPar (n : Nm (BId QuoteSp)) : SAtom QuoteSym QuoteSp := .par (IdSlot.spellI n)

def printed {Y : Type} (π : Nm Y → SAtom QuoteSym QuoteSp) (t : Tm QuoteSym Y) :
    SExp (SAtom QuoteSym QuoteSp) :=
  printAns (fun _ => .var .b) π t

def viewBag {Y : Type} (π : Nm Y → SAtom QuoteSym QuoteSp)
    (bag : Option (List (Tm QuoteSym Y))) :
    Option (List (SExp (SAtom QuoteSym QuoteSp)) × Bool) :=
  bag.map fun ts => (ts.map (printed π), ts.all isGotCtx)

def ansSlotM : Option (List (Tm QuoteSym (Slot QuoteSp))) :=
  answers .static (progSlot cfgM .u .unit noQuote) 80 (elabCfg cfgM [] gotCtx)

def ansSlotLF : Option (List (Tm QuoteSym (Slot QuoteSp))) :=
  answers .static (progSlot cfgLF .u .unit noQuote) 80 (elabCfg cfgLF [] gotCtx)

def ansIdM : Option (List (Tm QuoteSym (BId QuoteSp))) :=
  answers .static (progM .u .unit noQuote) 80 (elabMFormAt [] gotCtx)

def ansIdLF : Option (List (Tm QuoteSym (BId QuoteSp))) :=
  answers .static (progLF .u .unit noQuote) 80 (elabLFFormAt [] gotCtx)

/-- Lexical fresh on the translation of `gotCtx`. -/
def ansTranslated : Option (List (Tm QuoteSym (BId QuoteSp))) :=
  answers .static (progLF .u .unit (toLexicalProg noQuote)) 80
    (elabLFFormAt [] (toLexical gotCtx))

/-- **The contextual answer.**  Both models, both profiles, and lexical fresh
on the translation: one result, the text `(Got (quote (f z) (z)))`, and that
result is contextual code. `(lam w w)` matches `(lam z z)` and `(lam w z)`
does not: `code_match_identity`. -/
theorem gotCtx_view :
    viewBag slotPar ansSlotM = some ([gotSExp], true) ∧
      viewBag slotPar ansSlotLF = some ([gotSExp], true) ∧
    viewBag idPar ansIdM = some ([gotSExp], true) ∧
      viewBag idPar ansIdLF = some ([gotSExp], true) ∧
      viewBag idPar ansTranslated = some ([gotSExp], true) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Not a ground term.**  The answer is not the bare `(Got (f z))`, and not
a quotation that has dropped its binder list. -/
theorem gotCtx_not_bare :
    (viewBag slotPar ansSlotM).map Prod.fst ≠ some [bareSExp] ∧
      (viewBag slotPar ansSlotM).map Prod.fst ≠ some [droppedSExp] ∧
    (viewBag idPar ansIdM).map Prod.fst ≠ some [bareSExp] ∧
      (viewBag idPar ansIdM).map Prod.fst ≠ some [droppedSExp] := by
  have h := gotCtx_view
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    exact absurd ((congrArg (Option.map Prod.fst) h.1).symm.trans e) (by decide)
  · intro e
    exact absurd ((congrArg (Option.map Prod.fst) h.1).symm.trans e) (by decide)
  · intro e
    exact absurd ((congrArg (Option.map Prod.fst) h.2.2.1).symm.trans e) (by decide)
  · intro e
    exact absurd ((congrArg (Option.map Prod.fst) h.2.2.1).symm.trans e) (by decide)

/-- The code under `Got`, filled at its single binder and then run. -/
def fillOf {Y : Type} [DecidableEq Y] [CodeId Y] (π : Nm Y → SAtom QuoteSym QuoteSp)
    (bag : Option (List (Tm QuoteSym Y))) :
    Option (SExp (SAtom QuoteSym QuoteSp) × List (SExp (SAtom QuoteSym QuoteSp))) :=
  match bag with
  | some [t] =>
      match t with
      | .app (.sym .Got) (.ctx [k] body) =>
          let filled := liftLet k (.sym .n7) (.ctx [k] body)
          some (printed π filled,
            ((answers .static (fun _ : QuoteSym => none) 40 filled).map
              (List.map (printed π))).getD [])
      | _ => none
  | _ => none

/-- **Filling and running.**  `liftLet` of the code's own binder with `7`
yields `(f 7)`, and running that term yields `(f 7)`. -/
theorem gotCtx_fill :
    fillOf slotPar ansSlotM = some (f7SExp, [f7SExp]) ∧
      fillOf slotPar ansSlotLF = some (f7SExp, [f7SExp]) ∧
    fillOf idPar ansIdM = some (f7SExp, [f7SExp]) ∧
      fillOf idPar ansIdLF = some (f7SExp, [f7SExp]) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `liftLet` at a name that is not the code binder. -/
def resistFill {Y : Type} [CodeId Y] (π : Nm Y → SAtom QuoteSym QuoteSp) (k₀ : Nm Y)
    (bag : Option (List (Tm QuoteSym Y))) : Option (SExp (SAtom QuoteSym QuoteSp)) :=
  match bag with
  | some [.app _ (.ctx ks body)] =>
      some (printed π (liftLet k₀ (.sym .n7) (.ctx ks body)))
  | _ => none

/-- **A different name does not instantiate the code.**  The query's `$b` is
not the binder `z`. `liftLet` there leaves `(quote (f z) (z))`. -/
theorem gotCtx_resist :
    resistFill slotPar (.src ([], .b)) ansSlotM = some quoteSExp ∧
      resistFill slotPar (.src ([], .b)) ansSlotLF = some quoteSExp ∧
    resistFill idPar (.src (.par .b [])) ansIdM = some quoteSExp ∧
      resistFill idPar (.src (.par .b [])) ansIdLF = some quoteSExp :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem gotCtx_admissible : gotCtx.Admissible := by
  decide +kernel

/-- **`run_toLexical` on contextual code.**  Lexical fresh runs the translation
to the same results rule M runs on `gotCtx`, whose answer is the contextual
quotation above. -/
theorem gotCtx_run_toLexical :
    run .static (progLF .u .unit (toLexicalProg noQuote)) 80 [] Store.empty
        (elabLFFormAt [] (toLexical gotCtx)) =
      run .static (progM .u .unit noQuote) 80 [] Store.empty
        (elabMFormAt [] gotCtx) :=
  run_toLexical .u .unit noQuote gotCtx .static 80 [] Store.empty

/-- Slot-model lexical fresh on the translation of `gotCtx`, at fuel 80. -/
def runLFTrans : Option (Result QuoteSym (Slot QuoteSp)) :=
  run .static (progSlot cfgLF .u .unit (toLexicalProg noQuote)) 80 [] Store.empty
    (elabCfg cfgLF [] (toLexical gotCtx))

/-- Slot-model rule M on `gotCtx`, at fuel 80. -/
def runSlotM : Option (Result QuoteSym (Slot QuoteSp)) :=
  run .static (progSlot cfgM .u .unit noQuote) 80 [] Store.empty
    (elabCfg cfgM [] gotCtx)

/-- Identity-model rule M on `gotCtx`, at fuel `k`. -/
def runIdM (k : ℕ) : Option (Result QuoteSym (BId QuoteSp)) :=
  run .static (progM .u .unit noQuote) k [] Store.empty (elabMFormAt [] gotCtx)

theorem option_of_isSome {α : Type} {o : Option α} (h : o.isSome = true) : ∃ a, o = some a := by
  cases o with
  | some a => exact ⟨a, rfl⟩
  | none => exact absurd h Bool.false_ne_true

/-- **`transfer` on contextual code.**  At fuel 80 the slot model's lexical
fresh run of the translation and its rule-M run of `gotCtx` are both defined,
and each is related by `Renamed` to the identity model's rule-M run. -/
theorem gotCtx_transfer :
    ∃ bagLF bagM k bagId,
      runLFTrans = some bagLF ∧ runSlotM = some bagM ∧ runIdM k = some bagId ∧
        List.Forall₂ Renamed bagLF bagId ∧ List.Forall₂ Renamed bagM bagId := by
  have hT := transfer .u .unit noQuote gotCtx
    (fun _ _ h => by unfold noQuote at h; cases h) gotCtx_admissible
  have hLF : runLFTrans.isSome = true := by decide +kernel
  have hM : runSlotM.isSome = true := by decide +kernel
  obtain ⟨bagLF, hBagLF⟩ := option_of_isSome hLF
  obtain ⟨bagM, hBagM⟩ := option_of_isSome hM
  obtain ⟨k, bagId, hk, hR, hR'⟩ := hT.2 hBagLF hBagM
  exact ⟨bagLF, bagM, k, bagId, hBagLF, hBagM, hk, hR, hR'⟩

/-! ## Each remaining condition is needed -/

theorem unrelated_of_length {o₁ : Option (Result Sy (Slot Sp))} {o₂ : Option (Result Sy (BId Sp))}
    {a b : ℕ} (h₁ : o₁.map List.length = some a) (h₂ : o₂.map List.length = some b) (hab : a ≠ b) :
    ∃ L₁ L₂, o₁ = some L₁ ∧ o₂ = some L₂ ∧ ¬ List.Forall₂ Renamed L₁ L₂ := by
  obtain ⟨L₁, rfl, rfl⟩ := Option.map_eq_some_iff.1 h₁
  obtain ⟨L₂, rfl, rfl⟩ := Option.map_eq_some_iff.1 h₂
  exact ⟨L₁, L₂, rfl, rfl, fun hf => hab hf.length_eq⟩

theorem unrelated_of_sym_pvar {o₁ : Option (Result Sy (Slot Sp))} {o₂ : Option (Result Sy (BId Sp))}
    {s : Sy} {x : Nm (BId Sp)} (h₁ : o₁.map (List.map Prod.fst) = some [.sym s])
    (h₂ : o₂.map (List.map Prod.fst) = some [.pvar x]) :
    ∃ L₁ L₂, o₁ = some L₁ ∧ o₂ = some L₂ ∧ ¬ List.Forall₂ Renamed L₁ L₂ := by
  obtain ⟨L₁, rfl, e₁⟩ := Option.map_eq_some_iff.1 h₁
  obtain ⟨L₂, rfl, e₂⟩ := Option.map_eq_some_iff.1 h₂
  refine ⟨L₁, L₂, rfl, rfl, fun hf => ?_⟩
  cases hf with
  | nil => simp at e₁
  | cons hr _ =>
      obtain ⟨ν, μ, D, -, -, hrel, -⟩ := hr
      simp only [List.map_cons, List.cons.injEq] at e₁ e₂
      rw [e₁.1, e₂.1] at hrel
      have hsym : ∀ {R : List (Nm (BId Sp))} {ok : Bool} {t₂ : Tm Sy (BId Sp)},
          Rel SC ν μ .val R ok (.sym s : Tm Sy (Slot Sp)) t₂ → t₂ = .sym s := by
        intro R ok t₂ h
        cases h
        rfl
      cases hsym hrel

/-- A `new` block on the spine of a pattern. -/
def newPat : A := .letS (.new [.hole] (sv .hole)) (k .n5) (k .ok) none

/-- **A `new` block on the spine of a pattern**: the slot model's pattern is an
activation, which matches nothing; the identity model's is the bare name. -/
theorem newPat_needed : ¬ newPat.Admissible ∧
    (∃ L₁ L₂, run .static (progSlot cfgM .u .unit noCl) 80 [] Store.empty (elabCfg cfgM [] newPat) =
      some L₁ ∧ run .static (progM .u .unit noCl) 80 [] Store.empty (elabMFormAt [] newPat) = some L₂ ∧
      ¬ List.Forall₂ Renamed L₁ L₂) ∧
    (∃ L₁ L₂, run .static (progSlot cfgLF .u .unit noCl) 80 [] Store.empty (elabCfg cfgLF [] newPat) =
      some L₁ ∧ run .static (progLF .u .unit noCl) 80 [] Store.empty (elabLFFormAt [] newPat) = some L₂ ∧
      ¬ List.Forall₂ Renamed L₁ L₂) :=
  ⟨by decide +kernel, unrelated_of_length (a := 0) (b := 1) (by decide +kernel) (by decide +kernel)
      (by decide),
    unrelated_of_length (a := 0) (b := 1) (by decide +kernel) (by decide +kernel) (by decide)⟩

/-- A free parameter, substituted under a lambda binding the same spelling. -/
def freePar : A := ap (ap (lm .w (lm .z (pr .w))) (pr .z)) (k .n7)

/-- **A free parameter**: the slot model names parameters by spelling, so the
free `z` is captured and the answer is `7`; the identity model names them by
binder, and the answer is the free `z`. -/
theorem freePar_needed : ¬ freePar.Admissible ∧
    (∃ L₁ L₂, run .static (progSlot cfgM .u .unit noCl) 80 [] Store.empty (elabCfg cfgM [] freePar) =
      some L₁ ∧ run .static (progM .u .unit noCl) 80 [] Store.empty (elabMFormAt [] freePar) = some L₂ ∧
      ¬ List.Forall₂ Renamed L₁ L₂) ∧
    (∃ L₁ L₂, run .static (progSlot cfgLF .u .unit noCl) 80 [] Store.empty (elabCfg cfgLF [] freePar) =
      some L₁ ∧ run .static (progLF .u .unit noCl) 80 [] Store.empty (elabLFFormAt [] freePar) = some L₂ ∧
      ¬ List.Forall₂ Renamed L₁ L₂) :=
  ⟨by decide +kernel,
    unrelated_of_sym_pvar (s := .n7) (x := .src (.par .z [])) (by decide +kernel) (by decide +kernel),
    unrelated_of_sym_pvar (s := .n7) (x := .src (.par .z [])) (by decide +kernel) (by decide +kernel)⟩

/-! ## The renaming is per result -/

/-- Two results, each with a private name made inside the `let` body. -/
def aliasLF : A := .letS (sv .f) (.alt (lm .z (pr .z)) (k .n5)) (.new [.hole] (sv .hole)) none

/-- The same under rule M, with a crossing set making the `let` introduce `$f`. -/
def aliasM : A := .letS (sv .f) (.alt (lm .z (pr .z)) (k .n5)) (.new [.hole] (sv .hole)) (some [])

/-- **Per result, not per bag.**  On admissible programs, the identity model
allocates the `new` block's `$hole` in the frame, once for the bag, and the
slot model at each run of the block: printed with one naming for the whole bag
the two models differ (`[$hole#1, $hole#2]` against `[$hole#1, $hole#1]`);
printed result by result they agree, as `renaming_LF` and `renaming_M`
predict. -/
theorem alias_per_result :
    aliasLF.Admissible ∧
      printedS (SpectrumCorpus.ans cfgLF noCl aliasLF) ≠ printedI (ansLFI noCl aliasLF) ∧
      perS (SpectrumCorpus.ans cfgLF noCl aliasLF) = perI (ansLFI noCl aliasLF) ∧
    aliasM.Admissible ∧
      printedS (SpectrumCorpus.ans cfgM noCl aliasM) ≠ printedI (ansMI noCl aliasM) ∧
      perS (SpectrumCorpus.ans cfgM noCl aliasM) = perI (ansMI noCl aliasM) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## Per-opening freshness -/

/-- Symbols of the template:map example: `Pair`, `List2`, and the elements. -/
inductive FS where
  | Pair | List2 | n1 | n2
  deriving DecidableEq, Repr

/-- Spellings of that example: the template name, its parameter, its local. -/
inductive FX where
  | tm | k | u
  deriving DecidableEq, Repr

namespace Fresh

def pair (a b : Tm FS FX) : Tm FS FX := .app (.app (.sym .Pair) a) b

/-- A lambda whose body is `(let $u k (Pair $u $u))`. Elaboration owns `u`. -/
def tmpl : Tm FS FX :=
  .lam (.src .k) []
    (.letP (.var (.src .u)) (.pvar (.src .k)) (pair (.var (.src .u)) (.var (.src .u))))

def call (arg : Tm FS FX) : Tm FS FX := .app (.var (.src .tm)) arg

/-- One opening, on `n1`. -/
def one : Tm FS FX := .letP (.var (.src .tm)) tmpl (call (.sym .n1))

/-- Two openings. The outer application threads the store from the first to
the second. -/
def two : Tm FS FX :=
  .letP (.var (.src .tm)) tmpl
    (.app (.app (.sym .List2) (call (.sym .n1))) (call (.sym .n2)))

/-- The same two openings, with `$u` written outside the lambda, so the
lambda does not own it. -/
def twoShared : Tm FS FX :=
  .letP (.var (.src .tm)) tmpl
    (.app (.app (.sym .List2) (.app (.app (.sym .List2) (call (.sym .n1))) (call (.sym .n2))))
      (.var (.src .u)))

/-- The quotation body: `(let $u k (Pair $u $u))`. -/
def quoteBody : Tm FS FX :=
  .letP (.var (.src .u)) (.pvar (.src .k)) (pair (.var (.src .u)) (.var (.src .u)))

end Fresh

/-- **An opening is an activation.** Static activation is the shipped renaming
of the lambda's own names at the activation path, then the parameter
substitution. The store is not consulted. -/
theorem open_is_activation {S : Type} {X : Type} [DecidableEq S] [DecidableEq X]
    (ρ : Path) (key : Nm X) (own : List X) (body arg : Tm S X) :
    activate .static (Store.empty : GStore S X) ρ key own body arg =
      subst (renameOwn ρ own) (Sub.single key arg) body := rfl

/-- **Two openings, two store names.** The same owned spelling, copied at two
paths, is two `.inst` names. -/
theorem activation_fresh {S : Type} {X : Type} [DecidableEq X] {ρ₁ ρ₂ : Path} {y : X}
    (h : ρ₁ ≠ ρ₂) :
    renameOwn (S := S) ρ₁ [y] (.src y) = some (.var (.inst ρ₁ (.src y))) ∧
      renameOwn (S := S) ρ₂ [y] (.src y) = some (.var (.inst ρ₂ (.src y))) ∧
        (.inst ρ₁ (.src y) : Nm X) ≠ .inst ρ₂ (.src y) := by
  have hkey : ownKey [y] (.src y) = true := by simp [ownKey]
  refine ⟨?_, ?_, ?_⟩
  · simp [renameOwn, hkey]
  · simp [renameOwn, hkey]
  · intro e
    injection e with e
    exact h e

/-- **The quotation body owns its local.** `(let $u k (Pair $u $u))` writes
`$u` at this level. -/
theorem quote_own : (direct Fresh.quoteBody).dedup = [FX.u] := rfl

/-- **Opening that body renames the local.** The copy is tagged by the
activation path, and the parameter is the element. -/
theorem quote_open (ρ : Path) :
    activate .static (Store.empty : GStore FS FX) ρ (.src .k) ((direct Fresh.quoteBody).dedup)
        Fresh.quoteBody (.sym .n1) =
      .letP (.var (.inst ρ (.src .u))) (.sym .n1)
        (Fresh.pair (.var (.inst ρ (.src .u))) (.var (.inst ρ (.src .u)))) := rfl

/-- **Elaboration records the local on the two-element query.** -/
theorem template_owns :
    (match elabTopM Fresh.two with
      | .letP _ (.lam _ own _) _ => own
      | _ => []) = [FX.u] := rfl

/-- The one-element answer, `(Pair n1 n1)`. -/
def oneAns : Tm FS FX := Fresh.pair (.sym .n1) (.sym .n1)

/-- The two-element result before the store is applied: one pair at each
activation path. -/
def twoTerm : Tm FS FX :=
  .app (.app (.sym .List2)
      (Fresh.pair (.var (.inst [0, 1, 2] (.src .u))) (.var (.inst [0, 1, 2] (.src .u)))))
    (Fresh.pair (.var (.inst [1, 2] (.src .u))) (.var (.inst [1, 2] (.src .u))))

/-- The two-element answer, `(List2 (Pair n1 n1) (Pair n2 n2))`. -/
def twoAns : Tm FS FX :=
  .app (.app (.sym .List2) (Fresh.pair (.sym .n1) (.sym .n1)))
    (Fresh.pair (.sym .n2) (.sym .n2))

/-- **One opening answers.** -/
theorem template_map_one :
    answers .static (fun _ : FS => none) 40 (elabTopM Fresh.one) = some [oneAns] := rfl

/-- **Two openings do not share a store name.** The pre-answer term carries
`.inst [0, 1, 2]` and `.inst [1, 2]`. The answer is
`(List2 (Pair n1 n1) (Pair n2 n2))`. -/
theorem template_map_two :
    (run .static (fun _ : FS => none) 40 [] Store.empty (elabTopM Fresh.two)).map
        (List.map Prod.fst) = some [twoTerm] ∧
      answers .static (fun _ : FS => none) 40 (elabTopM Fresh.two) = some [twoAns] ∧
        (.inst [0, 1, 2] (.src FX.u) : Nm FX) ≠ .inst [1, 2] (.src .u) := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- **A local written outside the template is not owned.** Both openings
refine the same `$u`, and the bag is empty. -/
theorem template_map_shared :
    answers .static (fun _ : FS => none) 40 (elabTopM Fresh.twoShared) = some [] := rfl

/-! ## Hygiene: a store name inside code does not take a binder's spelling

The capture arm that would bind `$hole` to contextual code is not part of
`matchCode`. What the shipped matcher does is refuse: a pattern `.pvar` against
a value `.var` returns no store. The leak therefore has no answer, and in
particular does not answer `(Got escaped z)`. -/

/-- **A code binder does not capture a store name.** For every store, every
binder list, and every pair of names, `matchCode` and its step list return
nothing. No spelling of the binder is written into the store. -/
theorem pvar_var_no_capture {S : Type} {Y : Type} [DecidableEq S] [DecidableEq Y]
    [CodeId Y] (σ : GStore S Y) (bound : List (Nm Y)) (x n : Nm Y) :
    matchCodeIn σ bound (.pvar x) (.var n) = none ∧
      matchCodeStepsIn bound ((.pvar x : Tm S Y)) (.var n) = none ∧
      matchCode σ (.pvar x) (.var n) = none := by
  exact ⟨rfl, rfl, rfl⟩

/-- Symbols of the leak: `Got`, `escaped`, and the clause wrapper's `unit`. -/
inductive LeakSym where
  | Got | escaped | unit
  deriving DecidableEq, Repr

/-- Spellings of the leak: binders `w` and `z`, the store name `hole`, and
the clause wrapper's `u`. -/
inductive LeakSp where
  | w | z | hole | u
  deriving DecidableEq, Repr

/-- No equations. -/
def noLeak : LeakSym → Option (Src LeakSym LeakSp) := fun _ => none

/-- `(lam w w)`, the pattern's code. -/
def lamWW : Src LeakSym LeakSp := .lam .w none (.par .w)

/-- `(lam z $hole)`, the value's code. -/
def lamZH : Src LeakSym LeakSp := .lam .z none (.sv .hole)

/-- **The code match refuses.** Both sealed forms of `(lam w w)` against
`(lam z $hole)` return no store. -/
theorem leak_code_no_capture :
    matchCode (Store.empty : GStore LeakSym (Slot LeakSp)) (codeOf lamWW) (codeOf lamZH) = none ∧
      matchCode (Store.empty : GStore LeakSym (BId LeakSp)) (codeI lamWW) (codeI lamZH) = none := by
  exact ⟨rfl, rfl⟩

/-- `(let (quote (lam w w)) (quote (lam z $hole)) (Got escaped $hole))`. -/
def leak : Src LeakSym LeakSp :=
  .letS (.pquote lamWW) (.quote lamZH)
    (.app (.app (.sym .Got) (.sym .escaped)) (.sv .hole)) none

def leakSymText : LeakSym → String
  | .Got => "Got" | .escaped => "escaped" | .unit => "unit"

def leakSpText : LeakSp → String
  | .w => "w" | .z => "z" | .hole => "hole" | .u => "u"

def leakAtom : SAtom LeakSym LeakSp → String
  | .sym c => leakSymText c
  | .kw k => kwText k
  | .var v => "$" ++ leakSpText v
  | .fresh v n => "$" ++ leakSpText v ++ "#" ++ toString n
  | .par v => leakSpText v

/-- `(Got escaped z)`, the bare-name capture the leak must not return. -/
def leakBare : SExp (SAtom LeakSym LeakSp) :=
  .list [.atom (.sym .Got), .atom (.sym .escaped), .atom (.par .z)]

/-- **The shipped renderer spells that capture as the C text.** -/
theorem leakBare_text :
    (leakBare.render leakAtom (fun _ => false)).toList = "(Got escaped z)".toList := by
  simp [leakBare, SExp.render, SExp.renderList, SExp.renderSeq, leakAtom, leakSymText,
    leakSpText]

def leakSlotM : Option (List (Tm LeakSym (Slot LeakSp))) :=
  answers .static (progSlot cfgM .u .unit noLeak) 80 (elabCfg cfgM [] leak)

def leakSlotLF : Option (List (Tm LeakSym (Slot LeakSp))) :=
  answers .static (progSlot cfgLF .u .unit noLeak) 80 (elabCfg cfgLF [] leak)

def leakIdM : Option (List (Tm LeakSym (BId LeakSp))) :=
  answers .static (progM .u .unit noLeak) 80 (elabMFormAt [] leak)

def leakIdLF : Option (List (Tm LeakSym (BId LeakSp))) :=
  answers .static (progLF .u .unit noLeak) 80 (elabLFFormAt [] leak)

/-- **The leak answers nothing.** Both models and both profiles return the
empty bag, which is the match refusing `(lam w w)` against `(lam z $hole)`. -/
theorem leak_answers :
    leakSlotM = some [] ∧ leakSlotLF = some [] ∧ leakIdM = some [] ∧ leakIdLF = some [] :=
  ⟨rfl, rfl, rfl, rfl⟩

def leakPrintSlot (t : Tm LeakSym (Slot LeakSp)) : SExp (SAtom LeakSym LeakSp) :=
  printAns (fun _ => .var .hole) (fun n => .par n.spelling) t

def leakPrintId (t : Tm LeakSym (BId LeakSp)) : SExp (SAtom LeakSym LeakSp) :=
  printAns (fun _ => .var .hole) (fun n => .par (IdSlot.spellI n)) t

/-- **Not the bare name.** Printing those bags does not yield
`(Got escaped z)`. -/
theorem leak_not_bare :
    (leakSlotM.map (List.map leakPrintSlot) ≠ some [leakBare]) ∧
      (leakSlotLF.map (List.map leakPrintSlot) ≠ some [leakBare]) ∧
    (leakIdM.map (List.map leakPrintId) ≠ some [leakBare]) ∧
      (leakIdLF.map (List.map leakPrintId) ≠ some [leakBare]) := by
  have h := leak_answers
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    rw [h.1] at e
    exact absurd e (by decide)
  · intro e
    rw [h.2.1] at e
    exact absurd e (by decide)
  · intro e
    rw [h.2.2.1] at e
    exact absurd e (by decide)
  · intro e
    rw [h.2.2.2] at e
    exact absurd e (by decide)

end Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotExamples
