import Mettapedia.GSLT.Parsing.CompilerCorrespondence

/-!
# Linear stream paths recovered from specialized Horn rules

After a parse relation has been specialized at a ground grammar term, its
difference-list arguments form a stream path.  This module specifies the
language-neutral fragment consumed by the packed parser compiler and checks
that path extraction is neither branching nor cyclic and leaves no recursive
call unused.
-/

namespace Mettapedia.GSLT.Parsing.HornStream

open CompilerCorrespondence

inductive StreamTerm where
  | var (identifier : Nat)
  | nil
  | consExact (codepoint : Codepoint) (tail : StreamTerm)
  | consAny (tail : StreamTerm)
  deriving DecidableEq, Repr

structure ParseCall where
  input : StreamTerm
  output : StreamTerm
  category : Category
  deriving DecidableEq, Repr

def outgoing (current : StreamTerm) (calls : List ParseCall) :
    List ParseCall :=
  calls.filter fun call => call.input = current

def linearize :
    Nat → List StreamTerm → StreamTerm → StreamTerm →
      List ParseCall → Option (List SourceSymbol)
  | 0, _, _, _, _ => none
  | fuel + 1, seen, current, finish, calls =>
      if current = finish then
        if calls.isEmpty then some [] else none
      else if current ∈ seen then none
      else
        match current with
        | .consExact codepoint tail => do
            let rest ← linearize fuel (current :: seen) tail finish calls
            pure (.exact codepoint :: rest)
        | .consAny tail => do
            let rest ← linearize fuel (current :: seen) tail finish calls
            pure (.any :: rest)
        | .var _ | .nil =>
            match outgoing current calls with
            | [call] => do
                let rest ← linearize fuel (current :: seen) call.output finish
                  (calls.erase call)
                pure (.call call.category :: rest)
            | _ => none

inductive Linearizes :
    List StreamTerm → StreamTerm → StreamTerm →
      List ParseCall → List SourceSymbol → Prop where
  | done (seen finish) : Linearizes seen finish finish [] []
  | exact (seen tail finish calls symbols codepoint)
      (notFinished : StreamTerm.consExact codepoint tail ≠ finish)
      (fresh : StreamTerm.consExact codepoint tail ∉ seen)
      (rest : Linearizes
        (StreamTerm.consExact codepoint tail :: seen)
        tail finish calls symbols) :
      Linearizes seen (.consExact codepoint tail) finish calls
        (.exact codepoint :: symbols)
  | any (seen tail finish calls symbols)
      (notFinished : StreamTerm.consAny tail ≠ finish)
      (fresh : StreamTerm.consAny tail ∉ seen)
      (rest : Linearizes
        (StreamTerm.consAny tail :: seen) tail finish calls symbols) :
      Linearizes seen (.consAny tail) finish calls (.any :: symbols)
  | callVar (seen identifier finish calls symbols call)
      (notFinished : StreamTerm.var identifier ≠ finish)
      (fresh : StreamTerm.var identifier ∉ seen)
      (unique : outgoing (.var identifier) calls = [call])
      (rest : Linearizes (.var identifier :: seen) call.output finish
        (calls.erase call) symbols) :
      Linearizes seen (.var identifier) finish calls
        (.call call.category :: symbols)
  | callNil (seen finish calls symbols call)
      (notFinished : StreamTerm.nil ≠ finish)
      (fresh : StreamTerm.nil ∉ seen)
      (unique : outgoing .nil calls = [call])
      (rest : Linearizes (.nil :: seen) call.output finish
        (calls.erase call) symbols) :
      Linearizes seen .nil finish calls (.call call.category :: symbols)

theorem linearize_complete
    {seen current finish calls symbols}
    (derivation : Linearizes seen current finish calls symbols) :
    ∃ fuel, linearize fuel seen current finish calls = some symbols := by
  induction derivation with
  | done seen finish =>
      exact ⟨1, by simp [linearize]⟩
  | exact seen tail finish calls symbols codepoint notFinished fresh _ ih =>
      obtain ⟨fuel, accepted⟩ := ih
      exact ⟨fuel + 1, by
        simp [linearize, notFinished, fresh, accepted]⟩
  | any seen tail finish calls symbols notFinished fresh _ ih =>
      obtain ⟨fuel, accepted⟩ := ih
      exact ⟨fuel + 1, by
        simp [linearize, notFinished, fresh, accepted]⟩
  | callVar seen identifier finish calls symbols call notFinished fresh
      unique _ ih =>
      obtain ⟨fuel, accepted⟩ := ih
      exact ⟨fuel + 1, by
        simp [linearize, notFinished, fresh, unique, accepted]⟩
  | callNil seen finish calls symbols call notFinished fresh unique _ ih =>
      obtain ⟨fuel, accepted⟩ := ih
      exact ⟨fuel + 1, by
        simp [linearize, notFinished, fresh, unique, accepted]⟩

theorem linearize_sound
    (fuel : Nat) (seen : List StreamTerm)
    (current finish : StreamTerm) (calls : List ParseCall)
    (symbols : List SourceSymbol)
    (accepted : linearize fuel seen current finish calls = some symbols) :
    Linearizes seen current finish calls symbols := by
  induction fuel generalizing seen current finish calls symbols with
  | zero => simp [linearize] at accepted
  | succ fuel inductionHypothesis =>
      by_cases finished : current = finish
      · subst current
        simp only [linearize, ↓reduceIte] at accepted
        cases calls with
        | nil =>
            simp at accepted
            subst symbols
            exact .done seen finish
        | cons call calls => simp at accepted
      · by_cases repeated : current ∈ seen
        · simp [linearize, finished, repeated] at accepted
        · cases current with
          | consExact codepoint tail =>
              simp only [linearize, finished, repeated, ↓reduceIte,
                Option.bind_eq_bind] at accepted
              cases recursive : linearize fuel
                  (.consExact codepoint tail :: seen) tail finish calls with
              | none => simp [recursive] at accepted
              | some rest =>
                  simp [recursive] at accepted
                  subst symbols
                  exact .exact seen tail finish calls rest codepoint finished
                    repeated
                    (inductionHypothesis _ _ _ _ _ recursive)
          | consAny tail =>
              simp only [linearize, finished, repeated, ↓reduceIte,
                Option.bind_eq_bind] at accepted
              cases recursive : linearize fuel
                  (.consAny tail :: seen) tail finish calls with
              | none => simp [recursive] at accepted
              | some rest =>
                  simp [recursive] at accepted
                  subst symbols
                  exact .any seen tail finish calls rest finished repeated
                    (inductionHypothesis _ _ _ _ _ recursive)
          | var identifier =>
              cases unique : outgoing (.var identifier) calls with
              | nil => simp [linearize, finished, repeated, unique] at accepted
              | cons call remaining =>
                  cases remaining with
                  | nil =>
                      simp only [linearize, finished, repeated, unique,
                        ↓reduceIte, Option.bind_eq_bind] at accepted
                      cases recursive : linearize fuel (.var identifier :: seen)
                          call.output finish (calls.erase call) with
                      | none => simp [recursive] at accepted
                      | some rest =>
                          simp [recursive] at accepted
                          subst symbols
                          exact .callVar seen identifier finish calls rest call
                            finished repeated unique
                            (inductionHypothesis _ _ _ _ _ recursive)
                  | cons another more =>
                      simp [linearize, finished, repeated, unique] at accepted
          | nil =>
              cases unique : outgoing .nil calls with
              | nil => simp [linearize, finished, repeated, unique] at accepted
              | cons call remaining =>
                  cases remaining with
                  | nil =>
                      simp only [linearize, finished, repeated, unique,
                        ↓reduceIte, Option.bind_eq_bind] at accepted
                      cases recursive : linearize fuel (.nil :: seen)
                          call.output finish (calls.erase call) with
                      | none => simp [recursive] at accepted
                      | some rest =>
                          simp [recursive] at accepted
                          subst symbols
                          exact .callNil seen finish calls rest call finished
                            repeated unique
                            (inductionHypothesis _ _ _ _ _ recursive)
                  | cons another more =>
                      simp [linearize, finished, repeated, unique] at accepted

theorem linearize_iff
    (seen : List StreamTerm) (current finish : StreamTerm)
    (calls : List ParseCall) (symbols : List SourceSymbol) :
    (∃ fuel, linearize fuel seen current finish calls = some symbols) ↔
      Linearizes seen current finish calls symbols :=
  ⟨fun ⟨fuel, accepted⟩ =>
      linearize_sound fuel seen current finish calls symbols accepted,
    linearize_complete⟩

/-! ## Executable positive and negative controls -/

def exactStart : StreamTerm := .consExact 97 (.consExact 98 (.var 0))

theorem exactPath_accepts :
    linearize 3 [] exactStart (.var 0) [] =
      some [.exact 97, .exact 98] := by
  decide

def wildcardStart : StreamTerm := .consAny (.var 0)

theorem wildcardPath_accepts :
    linearize 2 [] wildcardStart (.var 0) [] = some [.any] := by
  decide

def oneCall : ParseCall :=
  { input := .var 0, output := .var 1, category := "child" }

theorem uniqueCall_accepts :
    linearize 2 [] (.var 0) (.var 1) [oneCall] =
      some [.call "child"] := by
  decide

def competingCall : ParseCall :=
  { input := .var 0, output := .var 2, category := "other" }

theorem branchingCalls_reject :
    linearize 3 [] (.var 0) (.var 1) [oneCall, competingCall] = none := by
  decide

def cyclicCall : ParseCall :=
  { input := .var 0, output := .var 0, category := "cycle" }

theorem cyclicCall_rejects :
    linearize 3 [] (.var 0) (.var 1) [cyclicCall] = none := by
  decide

theorem leftoverCall_rejects :
    linearize 2 [] (.var 0) (.var 0) [oneCall] = none := by
  decide

end Mettapedia.GSLT.Parsing.HornStream
