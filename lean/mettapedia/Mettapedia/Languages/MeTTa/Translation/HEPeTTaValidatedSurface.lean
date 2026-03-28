import Mettapedia.Languages.MeTTa.OSLFCore.Bridge

/-!
# Validated HE↔PeTTa Shared Surface

Executable validators and shared atomspace surface predicates used by
`HEPeTTaTranslate.lean`. This module isolates the stable/common fragment and
its default/shared atomspace bridge surface so those checks can be verified
separately from the larger roundtrip theorem file.
-/

namespace Mettapedia.Languages.MeTTa.Translation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def isHEBinderAtom : Atom → Bool
  | .var _ => true
  | .symbol "_" => true
  | _ => false

set_option maxHeartbeats 800000

mutual
/-- A recursive common fragment that neither translator rewrites.
    Positive example: shared `let`/`match` terms whose subterms are also stable.
    Negative example: any nested `chain`, `progn`, or `@<` headed expression. -/
def isStableCommonForm : Atom → Bool
  | .expression (.symbol "chain" :: _) => false
  | .expression (.symbol "collapse-bind" :: _) => false
  | .expression (.symbol "superpose-bind" :: _) => false
  | .expression (.symbol "switch" :: _) => false
  | .expression (.symbol "switch-minimal" :: _) => false
  | .expression (.symbol "atom-subst" :: _) => false
  | .expression (.symbol "nop" :: _) => false
  | .expression (.symbol "function" :: _) => false
  | .expression (.symbol "progn" :: _) => false
  | .expression (.symbol "prog1" :: _) => false
  | .expression (.symbol "foldall" :: _) => false
  | .expression (.symbol "@<" :: _) => false
  | .expression (.symbol "@>" :: _) => false
  | .expression es => isStableCommonExpr es
  | _ => true

/-- Raw symbols that would trigger a rewrite when used as expression heads. -/
def isForbiddenHeadSymbol : Atom → Bool
  | .symbol "chain" => true
  | .symbol "collapse-bind" => true
  | .symbol "superpose-bind" => true
  | .symbol "switch" => true
  | .symbol "switch-minimal" => true
  | .symbol "atom-subst" => true
  | .symbol "nop" => true
  | .symbol "function" => true
  | .symbol "progn" => true
  | .symbol "prog1" => true
  | .symbol "foldall" => true
  | .symbol "@<" => true
  | .symbol "@>" => true
  | _ => false

/-- Stability required specifically in expression-head position. -/
def isStableCommonHead (a : Atom) : Bool :=
  !isForbiddenHeadSymbol a && isStableCommonForm a

/-- Stability of a translated expression node: the head is stricter than args. -/
def isStableCommonExpr : List Atom → Bool
  | [] => true
  | hd :: args => isStableCommonHead hd && isStableCommonList args

/-- List helper for ordinary subterms. -/
def isStableCommonList : List Atom → Bool
  | [] => true
  | x :: xs => isStableCommonForm x && isStableCommonList xs
end

mutual
/-- Executable validator for the HE source fragment on which the roundtrip
    fixed-point theorem is actually true.

    It enforces two semantic side conditions:
    1. HE binder slots contain only variables or `_`.
    2. PeTTa-only heads (`progn`, `prog1`, `@<`, `@>`) do not already appear in
       the source tree.

    Positive example: `(chain e $x body)` with recursively validated subterms.
    Negative example: a `chain` whose binder slot itself contains another
    expression. -/
def isValidatedHESource : Atom → Bool
  | .expression [.symbol "chain", e, v, body] =>
      isValidatedHESource e && isHEBinderAtom v && isValidatedHESource body
  | .expression [.symbol "collapse-bind", inner] =>
      isValidatedHESource inner
  | .expression [.symbol "superpose-bind", inner] =>
      isValidatedHESource inner
  | .expression (.symbol "switch" :: scrut :: branches) =>
      isValidatedHESource scrut && isValidatedHEList branches
  | .expression (.symbol "switch-minimal" :: scrut :: branches) =>
      isValidatedHESource scrut && isValidatedHEList branches
  | .expression [.symbol "atom-subst", atom, v, tmpl] =>
      isValidatedHESource atom && isHEBinderAtom v && isValidatedHESource tmpl
  | .expression [.symbol "nop", x] =>
      isValidatedHESource x
  | .expression [.symbol "function", .expression [.symbol "return", x]] =>
      isValidatedHESource x
  | .expression (.symbol "chain" :: _) => false
  | .expression (.symbol "collapse-bind" :: _) => false
  | .expression (.symbol "superpose-bind" :: _) => false
  | .expression (.symbol "switch" :: _) => false
  | .expression (.symbol "switch-minimal" :: _) => false
  | .expression (.symbol "atom-subst" :: _) => false
  | .expression (.symbol "nop" :: _) => false
  | .expression (.symbol "function" :: _) => false
  | .expression (.symbol "progn" :: _) => false
  | .expression (.symbol "prog1" :: _) => false
  | .expression (.symbol "foldall" :: _) => false
  | .expression (.symbol "@<" :: _) => false
  | .expression (.symbol "@>" :: _) => false
  | .expression [] => true
  | .expression (hd :: args) => isValidatedHEHeadSource hd && isValidatedHEList args
  | _ => true

/-- Validator for terms that are safe in operator position after `translateHE`. -/
def isValidatedHEHeadSource : Atom → Bool
  | .symbol "chain" => false
  | .symbol "collapse-bind" => false
  | .symbol "superpose-bind" => false
  | .symbol "switch" => false
  | .symbol "switch-minimal" => false
  | .symbol "atom-subst" => false
  | .symbol "nop" => false
  | .symbol "function" => false
  | .symbol "progn" => false
  | .symbol "prog1" => false
  | .symbol "foldall" => false
  | .symbol "@<" => false
  | .symbol "@>" => false
  | .expression [.symbol "function", .expression [.symbol "return", x]] =>
      isValidatedHEHeadSource x
  | a => isValidatedHESource a

/-- List helper for `isValidatedHESource`. -/
def isValidatedHEList : List Atom → Bool
  | [] => true
  | x :: xs => isValidatedHESource x && isValidatedHEList xs
end

example : isStableCommonForm (.expression [.symbol "let", .var "$x", .symbol "a", .symbol "b"]) = true := by
  native_decide

example : isStableCommonForm (.expression [.symbol "progn", .symbol "a", .symbol "b"]) = false := by
  native_decide

example : isStableCommonForm (.expression [.symbol "foldall",
    .symbol "merge", .symbol "goal", .symbol "0"]) = false := by
  native_decide

example : isValidatedHESource (.expression [.symbol "chain",
    .symbol "e", .var "$x", .symbol "b"]) = true := by
  native_decide

example : isValidatedHESource (.expression [.symbol "chain",
    .symbol "e",
    .expression [.symbol "chain", .symbol "x", .var "$y", .symbol "z"],
    .symbol "b"]) = false := by
  native_decide

example : isValidatedHESource (.expression
    [.expression [.symbol "function", .expression [.symbol "return", .symbol "chain"]],
     .symbol "arg"]) = false := by
  native_decide

/-- PeTTa `foldall` reducers that remain first-order callable after lowering to
    HE's ordinary application surface. -/
def isFirstOrderReducerAtom : Atom → Bool
  | .symbol name => !isForbiddenHeadSymbol (.symbol name)
  | _ => false

mutual
/-- Executable validator for the PeTTa source fragment on which the new
    `foldall` lowering stays inside the common stable form.

    The key extra side condition is that `foldall` reducers must be first-order
    symbols, so the lowered HE application `(Agg acc item)` stays symbol-headed.
-/
def isValidatedPeTTaSource : Atom → Bool
  | .expression (.symbol "progn" :: args) => isValidatedPeTTaList args
  | .expression (.symbol "prog1" :: args) => isValidatedPeTTaList args
  | .expression [.symbol "foldall", agg, goal, init] =>
      isFirstOrderReducerAtom agg && isValidatedPeTTaSource goal && isValidatedPeTTaSource init
  | .expression [.symbol "@<", a, b] =>
      isValidatedPeTTaSource a && isValidatedPeTTaSource b
  | .expression [.symbol "@>", a, b] =>
      isValidatedPeTTaSource a && isValidatedPeTTaSource b
  | .expression (.symbol "chain" :: _) => false
  | .expression (.symbol "collapse-bind" :: _) => false
  | .expression (.symbol "superpose-bind" :: _) => false
  | .expression (.symbol "switch" :: _) => false
  | .expression (.symbol "switch-minimal" :: _) => false
  | .expression (.symbol "atom-subst" :: _) => false
  | .expression (.symbol "nop" :: _) => false
  | .expression (.symbol "function" :: _) => false
  | .expression (.symbol "foldall" :: _) => false
  | .expression (.symbol "@<" :: _) => false
  | .expression (.symbol "@>" :: _) => false
  | .expression [] => true
  | .expression (hd :: args) => isValidatedPeTTaHeadSource hd && isValidatedPeTTaList args
  | _ => true

/-- `progn` in operator position returns its final argument, so every earlier
    term need only be source-valid while the final term must itself be head-safe. -/
def isValidatedPeTTaPrognHeadArgs : List Atom → Bool
  | [] => true
  | [last] => isValidatedPeTTaHeadSource last
  | x :: xs => isValidatedPeTTaSource x && isValidatedPeTTaPrognHeadArgs xs

/-- `prog1` in operator position returns its first argument, so only that first
    term must be head-safe; the rest are evaluated for side effects. -/
def isValidatedPeTTaProg1HeadArgs : List Atom → Bool
  | [] => true
  | [first] => isValidatedPeTTaHeadSource first
  | first :: rest => isValidatedPeTTaHeadSource first && isValidatedPeTTaList rest

/-- Validator for terms that are safe in operator position after `translatePeTTa`. -/
def isValidatedPeTTaHeadSource : Atom → Bool
  | .symbol "chain" => false
  | .symbol "collapse-bind" => false
  | .symbol "superpose-bind" => false
  | .symbol "switch" => false
  | .symbol "switch-minimal" => false
  | .symbol "atom-subst" => false
  | .symbol "nop" => false
  | .symbol "function" => false
  | .symbol "progn" => false
  | .symbol "prog1" => false
  | .symbol "foldall" => false
  | .symbol "@<" => false
  | .symbol "@>" => false
  | .expression (.symbol "progn" :: args) => isValidatedPeTTaPrognHeadArgs args
  | .expression (.symbol "prog1" :: args) => isValidatedPeTTaProg1HeadArgs args
  | .expression [.symbol "foldall", agg, goal, init] =>
      isFirstOrderReducerAtom agg && isValidatedPeTTaSource goal && isValidatedPeTTaSource init
  | .expression [.symbol "@<", a, b] =>
      isValidatedPeTTaSource a && isValidatedPeTTaSource b
  | .expression [.symbol "@>", a, b] =>
      isValidatedPeTTaSource a && isValidatedPeTTaSource b
  | a => isValidatedPeTTaSource a

/-- List helper for `isValidatedPeTTaSource`. -/
def isValidatedPeTTaList : List Atom → Bool
  | [] => true
  | x :: xs => isValidatedPeTTaSource x && isValidatedPeTTaList xs
end

example : isValidatedPeTTaSource (.expression
    [.symbol "foldall", .symbol "merge", .expression [.symbol "twohop-item"], .symbol "0"]) = true := by
  native_decide

example : isValidatedPeTTaSource (.expression
    [.symbol "foldall", .var "$f", .expression [.symbol "twohop-item"], .symbol "0"]) = false := by
  native_decide

example : isValidatedPeTTaSource (.expression
    [.symbol "foldall", .symbol "@<", .expression [.symbol "twohop-item"], .symbol "0"]) = false := by
  native_decide

example : isValidatedPeTTaSource (.expression
    [.symbol "prog1", .expression [.symbol "foldall", .symbol "merge",
      .expression [.symbol "twohop-item"], .symbol "0"], .symbol "done"]) = true := by
  native_decide

example : isValidatedPeTTaSource (.expression
    [.expression [.symbol "prog1", .symbol "chain"], .symbol "arg"]) = false := by
  native_decide

example : isValidatedPeTTaSource (.expression
    [.expression [.symbol "progn", .symbol "side", .symbol "prog1"], .symbol "arg"]) = false := by
  native_decide

theorem firstOrderReducerAtom_eq_symbol (a : Atom)
    (h : isFirstOrderReducerAtom a = true) :
    ∃ name, a = .symbol name := by
  cases a with
  | var _ => cases h
  | symbol name => exact ⟨name, rfl⟩
  | grounded _ => cases h
  | expression _ => cases h

private theorem stableCommon_of_firstOrderReducerAtom (a : Atom)
    (h : isFirstOrderReducerAtom a = true) :
    isStableCommonForm a = true := by
  obtain ⟨name, rfl⟩ := firstOrderReducerAtom_eq_symbol a h
  simp [isFirstOrderReducerAtom, isStableCommonForm, isForbiddenHeadSymbol] at h ⊢

theorem stableCommon_of_heBinderAtom (v : Atom)
    (h : isHEBinderAtom v = true) :
    isStableCommonForm v = true := by
  cases v with
  | var _ => simp [isStableCommonForm]
  | symbol _ => simp [isStableCommonForm]
  | grounded _ => cases h
  | expression _ => cases h

theorem stableCommonHead_of_stableCommonForm (a : Atom)
    (h : isStableCommonForm a = true)
    (hnot : isForbiddenHeadSymbol a = false) :
    isStableCommonHead a = true := by
  simp [isStableCommonHead, h, hnot]

theorem stableCommonForm_cons_of_head (hd : Atom) (args : List Atom)
    (hhd : isStableCommonHead hd = true) :
    isStableCommonForm (.expression (hd :: args)) = isStableCommonList args := by
  cases hd with
  | var _ =>
      simp [isStableCommonForm, isStableCommonExpr, isStableCommonHead, isForbiddenHeadSymbol]
  | symbol c =>
      by_cases hchain : c = "chain"
      · subst hchain
        have hfalse : False := by
          simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
        exact False.elim hfalse
      · by_cases hcollapse : c = "collapse-bind"
        · subst hcollapse
          have hfalse : False := by
            simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
          exact False.elim hfalse
        · by_cases hsuperpose : c = "superpose-bind"
          · subst hsuperpose
            have hfalse : False := by
              simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
            exact False.elim hfalse
          · by_cases hswitch : c = "switch"
            · subst hswitch
              have hfalse : False := by
                simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
              exact False.elim hfalse
            · by_cases hswitchm : c = "switch-minimal"
              · subst hswitchm
                have hfalse : False := by
                  simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                exact False.elim hfalse
              · by_cases hatomsubst : c = "atom-subst"
                · subst hatomsubst
                  have hfalse : False := by
                    simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                  exact False.elim hfalse
                · by_cases hnop : c = "nop"
                  · subst hnop
                    have hfalse : False := by
                      simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                    exact False.elim hfalse
                  · by_cases hfunction : c = "function"
                    · subst hfunction
                      have hfalse : False := by
                        simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                      exact False.elim hfalse
                    · by_cases hprogn : c = "progn"
                      · subst hprogn
                        have hfalse : False := by
                          simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                        exact False.elim hfalse
                      · by_cases hprog1 : c = "prog1"
                        · subst hprog1
                          have hfalse : False := by
                            simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                          exact False.elim hfalse
                        · by_cases hfoldall : c = "foldall"
                          · subst hfoldall
                            have hfalse : False := by
                              simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                            exact False.elim hfalse
                          · by_cases hlt : c = "@<"
                            · subst hlt
                              have hfalse : False := by
                                simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                              exact False.elim hfalse
                            · by_cases hgt : c = "@>"
                              · subst hgt
                                have hfalse : False := by
                                  simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                                exact False.elim hfalse
                              · simp [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                                  isForbiddenHeadSymbol, isStableCommonList, hchain, hcollapse,
                                  hsuperpose, hswitch, hswitchm, hatomsubst, hnop, hfunction,
                                  hprogn, hprog1, hfoldall, hlt, hgt]
  | grounded _ =>
      simp [isStableCommonForm, isStableCommonExpr, isStableCommonHead, isForbiddenHeadSymbol]
  | expression es =>
      have hform : isStableCommonForm (.expression es) = true := by
        simpa [isStableCommonHead, isForbiddenHeadSymbol] using hhd
      simp [isStableCommonForm, isStableCommonExpr, isStableCommonHead, isForbiddenHeadSymbol, hform]

private theorem stableCommon_selfSymbol :
    isStableCommonForm (.symbol "&self") = true := by
  simp [isStableCommonForm, isStableCommonExpr, isStableCommonHead, isForbiddenHeadSymbol]

/-- Shared atomspace handles currently admitted by the translator's theoremic
    common fragment. We require the handle itself to already lie in the stable
    common form so translation leaves it unchanged. -/
def isSharedAtomSpaceHandle : Atom → Bool :=
  isStableCommonForm

example : isSharedAtomSpaceHandle (.symbol "&self") = true := by
  simpa [isSharedAtomSpaceHandle] using stableCommon_selfSymbol

example : isSharedAtomSpaceHandle (.symbol "&kb") = true := by
  simp [isSharedAtomSpaceHandle, isStableCommonForm, isStableCommonExpr,
    isStableCommonHead, isForbiddenHeadSymbol]

example : isSharedAtomSpaceHandle
    (.expression [.symbol "chain", .symbol "x", .var "$y", .symbol "z"]) = false := by
  native_decide

private theorem sharedAtomSpaceHandle_preserves_stableCommonForm
    (space : Atom) (h : isSharedAtomSpaceHandle space = true) :
    isStableCommonForm space = true := by
  simpa [isSharedAtomSpaceHandle] using h

/-- Shared atomspace operational fragment parameterized by a stable explicit
    space handle.

    Positive examples:
    - `(match &self (edge a $x) $x)`
    - `(match &kb (edge a $x) $x)`
    - `(add-atom &bag (edge a b))`

    Negative examples:
    - `(new-space)` is allocator/runtime territory, not part of this fragment.
    - `(match (chain e $x b) pat tmpl)` is excluded because the handle itself is
      not already in the stable common form.
-/
def isSharedAtomSpaceFragment : Atom → Bool
  | .expression [.symbol "match", space, pat, tmpl] =>
      isSharedAtomSpaceHandle space && isStableCommonForm pat && isStableCommonForm tmpl
  | .expression [.symbol "get-atoms", space] =>
      isSharedAtomSpaceHandle space
  | .expression [.symbol "add-atom", space, payload] =>
      isSharedAtomSpaceHandle space && isStableCommonForm payload
  | .expression [.symbol "remove-atom", space, payload] =>
      isSharedAtomSpaceHandle space && isStableCommonForm payload
  | _ => false

example : isSharedAtomSpaceFragment
    (.expression [.symbol "match", .symbol "&kb",
      .expression [.symbol "edge", .symbol "a", .var "$x"], .var "$x"]) = true := by
  simp [isSharedAtomSpaceFragment, isSharedAtomSpaceHandle, isStableCommonForm,
    isStableCommonExpr, isStableCommonHead, isForbiddenHeadSymbol, isStableCommonList]

example : isSharedAtomSpaceFragment
    (.expression [.symbol "match",
      .expression [.symbol "chain", .symbol "e", .var "$x", .symbol "b"],
      .symbol "pat", .symbol "tmpl"]) = false := by
  native_decide

inductive SharedAtomSpaceOperationalBridge : Atom → Prop where
  | matchSpace (space pat tmpl : Atom)
      (hspace : isSharedAtomSpaceHandle space = true)
      (hpat : isStableCommonForm pat = true)
      (htmpl : isStableCommonForm tmpl = true) :
      SharedAtomSpaceOperationalBridge
        (.expression [.symbol "match", space, pat, tmpl])
  | getAtoms (space : Atom)
      (hspace : isSharedAtomSpaceHandle space = true) :
      SharedAtomSpaceOperationalBridge
        (.expression [.symbol "get-atoms", space])
  | addAtom (space payload : Atom)
      (hspace : isSharedAtomSpaceHandle space = true)
      (hpayload : isStableCommonForm payload = true) :
      SharedAtomSpaceOperationalBridge
        (.expression [.symbol "add-atom", space, payload])
  | removeAtom (space payload : Atom)
      (hspace : isSharedAtomSpaceHandle space = true)
      (hpayload : isStableCommonForm payload = true) :
      SharedAtomSpaceOperationalBridge
        (.expression [.symbol "remove-atom", space, payload])

theorem sharedAtomSpaceFragment_has_operational_bridge
    (a : Atom) (h : isSharedAtomSpaceFragment a = true) :
    SharedAtomSpaceOperationalBridge a := by
  cases a with
  | var _ => cases h
  | symbol _ => cases h
  | grounded _ => cases h
  | expression es =>
      cases es with
      | nil => cases h
      | cons hd args =>
          cases hd with
          | var _ => cases h
          | grounded _ => cases h
          | expression _ => cases h
          | symbol c =>
              cases args with
              | nil =>
                  have hfalse : False := by
                    simp [isSharedAtomSpaceFragment] at h
                  exact False.elim hfalse
              | cons a1 rest =>
                  cases rest with
                  | nil =>
                      by_cases hget : c = "get-atoms"
                      · subst hget
                        have hspace : isSharedAtomSpaceHandle a1 = true := by
                          simpa [isSharedAtomSpaceFragment] using h
                        exact .getAtoms a1 hspace
                      · simp [isSharedAtomSpaceFragment, hget] at h
                  | cons a2 rest =>
                      cases rest with
                      | nil =>
                          by_cases hadd : c = "add-atom"
                          · subst hadd
                            have hparts :
                                isSharedAtomSpaceHandle a1 = true ∧
                                  isStableCommonForm a2 = true := by
                              simpa [isSharedAtomSpaceFragment, Bool.and_eq_true] using h
                            exact .addAtom a1 a2 hparts.1 hparts.2
                          · by_cases hremove : c = "remove-atom"
                            · subst hremove
                              have hparts :
                                  isSharedAtomSpaceHandle a1 = true ∧
                                    isStableCommonForm a2 = true := by
                                simpa [isSharedAtomSpaceFragment, Bool.and_eq_true] using h
                              exact .removeAtom a1 a2 hparts.1 hparts.2
                            · simp [isSharedAtomSpaceFragment, hadd, hremove] at h
                      | cons a3 rest =>
                          cases rest with
                          | nil =>
                              by_cases hmatch : c = "match"
                              · subst hmatch
                                have hparts :
                                    (isSharedAtomSpaceHandle a1 = true ∧
                                      isStableCommonForm a2 = true) ∧
                                      isStableCommonForm a3 = true := by
                                  simpa [isSharedAtomSpaceFragment, Bool.and_eq_true] using h
                                exact .matchSpace a1 a2 a3 hparts.1.1 hparts.1.2 hparts.2
                              · simp [isSharedAtomSpaceFragment, hmatch] at h
                          | cons _ _ =>
                              have hfalse : False := by
                                simp [isSharedAtomSpaceFragment] at h
                              exact False.elim hfalse

theorem sharedAtomSpaceFragment_preserves_stableCommonForm
    (a : Atom) (h : isSharedAtomSpaceFragment a = true) :
    isStableCommonForm a = true := by
  cases a with
  | var _ => cases h
  | symbol _ => cases h
  | grounded _ => cases h
  | expression es =>
      cases es with
      | nil => cases h
      | cons hd args =>
          cases hd with
          | var _ => cases h
          | grounded _ => cases h
          | expression _ => cases h
          | symbol c =>
              cases args with
              | nil =>
                  have hfalse : False := by
                    simp [isSharedAtomSpaceFragment] at h
                  exact False.elim hfalse
              | cons a1 rest =>
                  cases rest with
                  | nil =>
                      by_cases hget : c = "get-atoms"
                      · subst hget
                        have hspace : isSharedAtomSpaceHandle a1 = true := by
                          simpa [isSharedAtomSpaceFragment] using h
                        have hspaceForm := sharedAtomSpaceHandle_preserves_stableCommonForm a1 hspace
                        have hhead : isStableCommonHead (.symbol "get-atoms") = true := by
                          simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
                        rw [stableCommonForm_cons_of_head (.symbol "get-atoms") [a1] hhead]
                        simp [isStableCommonList, hspaceForm]
                      · simp [isSharedAtomSpaceFragment, hget] at h
                  | cons a2 rest =>
                      cases rest with
                      | nil =>
                          by_cases hadd : c = "add-atom"
                          · subst hadd
                            have hparts :
                                isSharedAtomSpaceHandle a1 = true ∧
                                  isStableCommonForm a2 = true := by
                              simpa [isSharedAtomSpaceFragment, Bool.and_eq_true] using h
                            have hspaceForm := sharedAtomSpaceHandle_preserves_stableCommonForm a1 hparts.1
                            have hhead : isStableCommonHead (.symbol "add-atom") = true := by
                              simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
                            rw [stableCommonForm_cons_of_head (.symbol "add-atom") [a1, a2] hhead]
                            simp [isStableCommonList, hspaceForm, hparts.2]
                          · by_cases hremove : c = "remove-atom"
                            · subst hremove
                              have hparts :
                                  isSharedAtomSpaceHandle a1 = true ∧
                                    isStableCommonForm a2 = true := by
                                simpa [isSharedAtomSpaceFragment, Bool.and_eq_true] using h
                              have hspaceForm := sharedAtomSpaceHandle_preserves_stableCommonForm a1 hparts.1
                              have hhead : isStableCommonHead (.symbol "remove-atom") = true := by
                                simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
                              rw [stableCommonForm_cons_of_head (.symbol "remove-atom") [a1, a2] hhead]
                              simp [isStableCommonList, hspaceForm, hparts.2]
                            · simp [isSharedAtomSpaceFragment, hadd, hremove] at h
                      | cons a3 rest =>
                          cases rest with
                          | nil =>
                              by_cases hmatch : c = "match"
                              · subst hmatch
                                have hparts :
                                    (isSharedAtomSpaceHandle a1 = true ∧
                                      isStableCommonForm a2 = true) ∧
                                      isStableCommonForm a3 = true := by
                                  simpa [isSharedAtomSpaceFragment, Bool.and_eq_true] using h
                                have hspaceForm := sharedAtomSpaceHandle_preserves_stableCommonForm a1 hparts.1.1
                                have hhead : isStableCommonHead (.symbol "match") = true := by
                                  simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
                                rw [stableCommonForm_cons_of_head (.symbol "match") [a1, a2, a3] hhead]
                                simp [isStableCommonList, hspaceForm, hparts.1.2, hparts.2]
                              · simp [isSharedAtomSpaceFragment, hmatch] at h
                          | cons _ _ =>
                              have hfalse : False := by
                                simp [isSharedAtomSpaceFragment] at h
                              exact False.elim hfalse

/-- Shared default-atomspace operational fragment already modeled on both sides.

    This is the honest theoremic bridge for the current stateful translator work:
    the translators leave these `&self` forms unchanged as long as their payloads
    are already in the stable common form.

    Positive example:
    - `(match &self (edge a $x) $x)`
    - `(add-atom &self (edge a b))`

    Negative example:
    - `(new-space)` is intentionally outside this fragment.
    - `(match &db pat tmpl)` is outside the current default-atomspace theorem boundary.
-/
def isDefaultAtomSpaceSharedFragment : Atom → Bool
  | .expression [.symbol "match", .symbol "&self", pat, tmpl] =>
      isStableCommonForm pat && isStableCommonForm tmpl
  | .expression [.symbol "get-atoms", .symbol "&self"] => true
  | .expression [.symbol "add-atom", .symbol "&self", payload] =>
      isStableCommonForm payload
  | .expression [.symbol "remove-atom", .symbol "&self", payload] =>
      isStableCommonForm payload
  | _ => false

example : isDefaultAtomSpaceSharedFragment
    (.expression [.symbol "match", .symbol "&self",
      .expression [.symbol "edge", .symbol "a", .var "$x"], .var "$x"]) = true := by
  simp [isDefaultAtomSpaceSharedFragment, isStableCommonForm, isStableCommonExpr,
    isStableCommonHead, isForbiddenHeadSymbol, isStableCommonList]

example : isDefaultAtomSpaceSharedFragment (.expression [.symbol "new-space"]) = false := by
  rfl

inductive DefaultAtomSpaceOperationalBridge : Atom → Prop where
  | matchSelf (pat tmpl : Atom)
      (hpat : isStableCommonForm pat = true)
      (htmpl : isStableCommonForm tmpl = true) :
      DefaultAtomSpaceOperationalBridge
        (.expression [.symbol "match", .symbol "&self", pat, tmpl])
  | getAtomsSelf :
      DefaultAtomSpaceOperationalBridge
        (.expression [.symbol "get-atoms", .symbol "&self"])
  | addAtomSelf (payload : Atom)
      (hpayload : isStableCommonForm payload = true) :
      DefaultAtomSpaceOperationalBridge
        (.expression [.symbol "add-atom", .symbol "&self", payload])
  | removeAtomSelf (payload : Atom)
      (hpayload : isStableCommonForm payload = true) :
      DefaultAtomSpaceOperationalBridge
        (.expression [.symbol "remove-atom", .symbol "&self", payload])

theorem defaultAtomSpaceSharedFragment_has_operational_bridge
    (a : Atom) (h : isDefaultAtomSpaceSharedFragment a = true) :
    DefaultAtomSpaceOperationalBridge a := by
  cases a with
  | var _ => cases h
  | symbol _ => cases h
  | grounded _ => cases h
  | expression es =>
      cases es with
      | nil => cases h
      | cons hd args =>
          cases hd with
          | var _ => cases h
          | grounded _ => cases h
          | expression _ => cases h
          | symbol c =>
              cases args with
              | nil =>
                  have hfalse : False := by
                    simp [isDefaultAtomSpaceSharedFragment] at h
                  exact False.elim hfalse
              | cons a1 rest =>
                  cases rest with
                  | nil =>
                      by_cases hget : c = "get-atoms"
                      · subst hget
                        cases a1 with
                        | symbol s =>
                            by_cases hself : s = "&self"
                            · subst hself
                              exact .getAtomsSelf
                            · simp [isDefaultAtomSpaceSharedFragment, hself] at h
                        | var _ => cases h
                        | grounded _ => cases h
                        | expression _ => cases h
                      · simp [isDefaultAtomSpaceSharedFragment, hget] at h
                  | cons a2 rest =>
                      cases rest with
                      | nil =>
                          by_cases hadd : c = "add-atom"
                          · subst hadd
                            cases a1 with
                            | symbol s =>
                                by_cases hself : s = "&self"
                                · subst hself
                                  have hpayload : isStableCommonForm a2 = true := by
                                    simpa [isDefaultAtomSpaceSharedFragment] using h
                                  exact .addAtomSelf a2 hpayload
                                · simp [isDefaultAtomSpaceSharedFragment, hself] at h
                            | var _ => cases h
                            | grounded _ => cases h
                            | expression _ => cases h
                          · by_cases hremove : c = "remove-atom"
                            · subst hremove
                              cases a1 with
                              | symbol s =>
                                  by_cases hself : s = "&self"
                                  · subst hself
                                    have hpayload : isStableCommonForm a2 = true := by
                                      simpa [isDefaultAtomSpaceSharedFragment] using h
                                    exact .removeAtomSelf a2 hpayload
                                  · simp [isDefaultAtomSpaceSharedFragment, hself] at h
                              | var _ => cases h
                              | grounded _ => cases h
                              | expression _ => cases h
                            · simp [isDefaultAtomSpaceSharedFragment, hadd, hremove] at h
                      | cons a3 rest =>
                          cases rest with
                          | nil =>
                              by_cases hmatch : c = "match"
                              · subst hmatch
                                cases a1 with
                                | symbol s =>
                                    by_cases hself : s = "&self"
                                    · subst hself
                                      have hparts :
                                          isStableCommonForm a2 = true ∧
                                            isStableCommonForm a3 = true := by
                                        simpa [isDefaultAtomSpaceSharedFragment, Bool.and_eq_true] using h
                                      exact .matchSelf a2 a3 hparts.1 hparts.2
                                    · simp [isDefaultAtomSpaceSharedFragment, hself] at h
                                | var _ => cases h
                                | grounded _ => cases h
                                | expression _ => cases h
                              · simp [isDefaultAtomSpaceSharedFragment, hmatch] at h
                          | cons _ _ =>
                              have hfalse : False := by
                                simp [isDefaultAtomSpaceSharedFragment] at h
                              exact False.elim hfalse

theorem defaultAtomSpaceSharedFragment_preserves_stableCommonForm
    (a : Atom) (h : isDefaultAtomSpaceSharedFragment a = true) :
    isStableCommonForm a = true := by
  cases a with
  | var _ => cases h
  | symbol _ => cases h
  | grounded _ => cases h
  | expression es =>
      cases es with
      | nil => cases h
      | cons hd args =>
          cases hd with
          | var _ => cases h
          | grounded _ => cases h
          | expression _ => cases h
          | symbol c =>
              cases args with
              | nil =>
                  have hfalse : False := by
                    simp [isDefaultAtomSpaceSharedFragment] at h
                  exact False.elim hfalse
              | cons a1 rest =>
                  cases rest with
                  | nil =>
                      by_cases hget : c = "get-atoms"
                      · subst hget
                        cases a1 with
                        | symbol s =>
                            by_cases hself : s = "&self"
                            · subst hself
                              have hhead : isStableCommonHead (.symbol "get-atoms") = true := by
                                simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
                              rw [stableCommonForm_cons_of_head (.symbol "get-atoms") [.symbol "&self"] hhead]
                              simp [isStableCommonList, stableCommon_selfSymbol]
                            · simp [isDefaultAtomSpaceSharedFragment, hself] at h
                        | var _ => cases h
                        | grounded _ => cases h
                        | expression _ => cases h
                      · simp [isDefaultAtomSpaceSharedFragment, hget] at h
                  | cons a2 rest =>
                      cases rest with
                      | nil =>
                          by_cases hadd : c = "add-atom"
                          · subst hadd
                            cases a1 with
                            | symbol s =>
                                by_cases hself : s = "&self"
                                · subst hself
                                  have hpayload : isStableCommonForm a2 = true := by
                                    simpa [isDefaultAtomSpaceSharedFragment] using h
                                  have hhead : isStableCommonHead (.symbol "add-atom") = true := by
                                    simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
                                  rw [stableCommonForm_cons_of_head (.symbol "add-atom") [.symbol "&self", a2] hhead]
                                  simp [isStableCommonList, stableCommon_selfSymbol, hpayload]
                                · simp [isDefaultAtomSpaceSharedFragment, hself] at h
                            | var _ => cases h
                            | grounded _ => cases h
                            | expression _ => cases h
                          · by_cases hremove : c = "remove-atom"
                            · subst hremove
                              cases a1 with
                              | symbol s =>
                                  by_cases hself : s = "&self"
                                  · subst hself
                                    have hpayload : isStableCommonForm a2 = true := by
                                      simpa [isDefaultAtomSpaceSharedFragment] using h
                                    have hhead : isStableCommonHead (.symbol "remove-atom") = true := by
                                      simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
                                    rw [stableCommonForm_cons_of_head (.symbol "remove-atom") [.symbol "&self", a2] hhead]
                                    simp [isStableCommonList, stableCommon_selfSymbol, hpayload]
                                  · simp [isDefaultAtomSpaceSharedFragment, hself] at h
                              | var _ => cases h
                              | grounded _ => cases h
                              | expression _ => cases h
                            · simp [isDefaultAtomSpaceSharedFragment, hadd, hremove] at h
                      | cons a3 rest =>
                          cases rest with
                          | nil =>
                              by_cases hmatch : c = "match"
                              · subst hmatch
                                cases a1 with
                                | symbol s =>
                                    by_cases hself : s = "&self"
                                    · subst hself
                                      have hparts :
                                          isStableCommonForm a2 = true ∧
                                            isStableCommonForm a3 = true := by
                                        simpa [isDefaultAtomSpaceSharedFragment, Bool.and_eq_true] using h
                                      have hhead : isStableCommonHead (.symbol "match") = true := by
                                        simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
                                      rw [stableCommonForm_cons_of_head (.symbol "match") [.symbol "&self", a2, a3] hhead]
                                      simp [isStableCommonList, stableCommon_selfSymbol, hparts.1, hparts.2]
                                    · simp [isDefaultAtomSpaceSharedFragment, hself] at h
                                | var _ => cases h
                                | grounded _ => cases h
                                | expression _ => cases h
                              · simp [isDefaultAtomSpaceSharedFragment, hmatch] at h
                          | cons _ _ =>
                              have hfalse : False := by
                                simp [isDefaultAtomSpaceSharedFragment] at h
                              exact False.elim hfalse

/-- Shared state operational fragment already modeled on both runtimes.

    This extends the theoremic shared surface to the state core:
    `new-state`, `get-state`, and `change-state!`.

    Positive examples:
    - `(new-state 0)`
    - `(get-state &counter)`
    - `(change-state! (status (Goal lunch-order)) active)`

    Negative example:
    - `(get-state (chain e $x body))` is outside the fragment because the
      state reference itself is not in stable common form.
-/
def isSharedStateFragment : Atom → Bool
  | .expression [.symbol "new-state", init] =>
      isStableCommonForm init
  | .expression [.symbol "get-state", stateRef] =>
      isStableCommonForm stateRef
  | .expression [.symbol "change-state!", stateRef, value] =>
      isStableCommonForm stateRef && isStableCommonForm value
  | _ => false

example : isSharedStateFragment (.expression [.symbol "new-state", .symbol "zero"]) = true := by
  native_decide

example : isSharedStateFragment (.expression [.symbol "get-state", .symbol "&counter"]) = true := by
  native_decide

example : isSharedStateFragment
    (.expression [.symbol "get-state",
      .expression [.symbol "chain", .symbol "e", .var "$x", .symbol "body"]]) = false := by
  native_decide

inductive SharedStateOperationalBridge : Atom → Prop where
  | newState (init : Atom)
      (hinit : isStableCommonForm init = true) :
      SharedStateOperationalBridge
        (.expression [.symbol "new-state", init])
  | getState (stateRef : Atom)
      (href : isStableCommonForm stateRef = true) :
      SharedStateOperationalBridge
        (.expression [.symbol "get-state", stateRef])
  | changeState (stateRef value : Atom)
      (href : isStableCommonForm stateRef = true)
      (hvalue : isStableCommonForm value = true) :
      SharedStateOperationalBridge
        (.expression [.symbol "change-state!", stateRef, value])

theorem sharedStateFragment_has_operational_bridge
    (a : Atom) (h : isSharedStateFragment a = true) :
    SharedStateOperationalBridge a := by
  cases a with
  | var _ => cases h
  | symbol _ => cases h
  | grounded _ => cases h
  | expression es =>
      cases es with
      | nil => cases h
      | cons hd args =>
          cases hd with
          | var _ => cases h
          | grounded _ => cases h
          | expression _ => cases h
          | symbol c =>
              cases args with
              | nil =>
                  have hfalse : False := by
                    simp [isSharedStateFragment] at h
                  exact False.elim hfalse
              | cons a1 rest =>
                  cases rest with
                  | nil =>
                      by_cases hnew : c = "new-state"
                      · subst hnew
                        have hinit : isStableCommonForm a1 = true := by
                          simpa [isSharedStateFragment] using h
                        exact .newState a1 hinit
                      · by_cases hget : c = "get-state"
                        · subst hget
                          have href : isStableCommonForm a1 = true := by
                            simpa [isSharedStateFragment] using h
                          exact .getState a1 href
                        · simp [isSharedStateFragment, hnew, hget] at h
                  | cons a2 rest =>
                      cases rest with
                      | nil =>
                          by_cases hchange : c = "change-state!"
                          · subst hchange
                            have hparts :
                                isStableCommonForm a1 = true ∧
                                  isStableCommonForm a2 = true := by
                              simpa [isSharedStateFragment, Bool.and_eq_true] using h
                            exact .changeState a1 a2 hparts.1 hparts.2
                          · simp [isSharedStateFragment, hchange] at h
                      | cons _ _ =>
                          have hfalse : False := by
                            simp [isSharedStateFragment] at h
                          exact False.elim hfalse

theorem sharedStateFragment_preserves_stableCommonForm
    (a : Atom) (h : isSharedStateFragment a = true) :
    isStableCommonForm a = true := by
  cases a with
  | var _ => cases h
  | symbol _ => cases h
  | grounded _ => cases h
  | expression es =>
      cases es with
      | nil => cases h
      | cons hd args =>
          cases hd with
          | var _ => cases h
          | grounded _ => cases h
          | expression _ => cases h
          | symbol c =>
              cases args with
              | nil =>
                  have hfalse : False := by
                    simp [isSharedStateFragment] at h
                  exact False.elim hfalse
              | cons a1 rest =>
                  cases rest with
                  | nil =>
                      by_cases hnew : c = "new-state"
                      · subst hnew
                        have hinit : isStableCommonForm a1 = true := by
                          simpa [isSharedStateFragment] using h
                        have hhead : isStableCommonHead (.symbol "new-state") = true := by
                          simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
                        rw [stableCommonForm_cons_of_head (.symbol "new-state") [a1] hhead]
                        simp [isStableCommonList, hinit]
                      · by_cases hget : c = "get-state"
                        · subst hget
                          have href : isStableCommonForm a1 = true := by
                            simpa [isSharedStateFragment] using h
                          have hhead : isStableCommonHead (.symbol "get-state") = true := by
                            simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
                          rw [stableCommonForm_cons_of_head (.symbol "get-state") [a1] hhead]
                          simp [isStableCommonList, href]
                        · simp [isSharedStateFragment, hnew, hget] at h
                  | cons a2 rest =>
                      cases rest with
                      | nil =>
                          by_cases hchange : c = "change-state!"
                          · subst hchange
                            have hparts :
                                isStableCommonForm a1 = true ∧
                                  isStableCommonForm a2 = true := by
                              simpa [isSharedStateFragment, Bool.and_eq_true] using h
                            have hhead : isStableCommonHead (.symbol "change-state!") = true := by
                              simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
                            rw [stableCommonForm_cons_of_head (.symbol "change-state!") [a1, a2] hhead]
                            simp [isStableCommonList, hparts.1, hparts.2]
                          · simp [isSharedStateFragment, hchange] at h
                      | cons _ _ =>
                          have hfalse : False := by
                            simp [isSharedStateFragment] at h
                          exact False.elim hfalse

end Mettapedia.Languages.MeTTa.Translation
