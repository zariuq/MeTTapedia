import Mettapedia.GSLT.LanguageDef.LFTyping

/-!
# Beta-eta conversion for LF terms

This module extends the existing beta/delta normalization theorem for the LF
reference with eta contraction.  The executable normal form is proved sound
against an independently stated reduction relation.  Typing is deliberately
not folded into this layer: clients must establish that both compared terms
are well typed before using conversion in a typing rule.
-/

namespace Mettapedia.GSLT.LanguageDef.LFBetaEta

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping

/-- Remove the variable at `cutoff`, decrementing indices above it.  Failure
means that the removed variable occurs free. -/
def unbind (cutoff : Nat) : Term → Option Term
  | .srt sort => some (.srt sort)
  | .con name => some (.con name)
  | .var index =>
      if index < cutoff then some (.var index)
      else if index = cutoff then none
      else some (.var (index - 1))
  | .pi domain body => do
      pure (.pi (← unbind cutoff domain) (← unbind (cutoff + 1) body))
  | .lam domain body => do
      pure (.lam (← unbind cutoff domain) (← unbind (cutoff + 1) body))
  | .app function argument => do
      pure (.app (← unbind cutoff function) (← unbind cutoff argument))

/-- Beta, delta, and eta reduction, closed under every LF constructor. -/
inductive Reduces (signature : Sig) : Term → Term → Prop where
  | refl {term} : Reduces signature term term
  | beta {domain body argument} :
      Reduces signature (.app (.lam domain body) argument)
        (subst0 argument body)
  | delta {name body} :
      lookupBody signature name = some body →
      Reduces signature (.con name) body
  | eta {domain function reduced} :
      unbind 0 function = some reduced →
      Reduces signature (.lam domain (.app function (.var 0))) reduced
  | pi {domain domain' body body'} :
      Reduces signature domain domain' →
      Reduces signature body body' →
      Reduces signature (.pi domain body) (.pi domain' body')
  | lam {domain domain' body body'} :
      Reduces signature domain domain' →
      Reduces signature body body' →
      Reduces signature (.lam domain body) (.lam domain' body')
  | app {function function' argument argument'} :
      Reduces signature function function' →
      Reduces signature argument argument' →
      Reduces signature (.app function argument)
        (.app function' argument')
  | trans {first second third} :
      Reduces signature first second →
      Reduces signature second third →
      Reduces signature first third

/-- Conversion by reduction to one common beta-delta-eta reduct. -/
inductive Conv (signature : Sig) : Term → Term → Prop where
  | common {left right common} :
      Reduces signature left common →
      Reduces signature right common →
      Conv signature left right

/-- The existing beta/delta relation embeds into beta-delta-eta reduction. -/
theorem Reduces.ofBetaDelta {signature : Sig} {first second : Term}
    (reduction : LFTyping.Reduces signature first second) :
    Reduces signature first second := by
  induction reduction with
  | refl => exact .refl
  | beta => exact .beta
  | delta hbody => exact .delta hbody
  | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument
  | pi _ _ ihDomain ihBody => exact .pi ihDomain ihBody
  | lam _ _ ihDomain ihBody => exact .lam ihDomain ihBody
  | trans _ _ ihFirst ihSecond => exact .trans ihFirst ihSecond

/-- Contract eta redexes after recursively normalizing their components. -/
def etaNf : Term → Term
  | .srt sort => .srt sort
  | .con name => .con name
  | .var index => .var index
  | .pi domain body => .pi (etaNf domain) (etaNf body)
  | .app function argument => .app (etaNf function) (etaNf argument)
  | .lam domain body =>
      let normalizedDomain := etaNf domain
      let normalizedBody := etaNf body
      match normalizedBody with
      | .app function (.var 0) =>
          match unbind 0 function with
          | some reduced => reduced
          | none => .lam normalizedDomain normalizedBody
      | _ => .lam normalizedDomain normalizedBody

/-- Beta/delta normalization followed by eta contraction. -/
def normalForm (signature : Sig) (fuel : Nat) (term : Term) : Term :=
  etaNf (LFTyping.nf signature fuel term)

def convBool (signature : Sig) (fuel : Nat) (left right : Term) : Bool :=
  normalForm signature fuel left == normalForm signature fuel right

theorem etaNf_sound (signature : Sig) (term : Term) :
    Reduces signature term (etaNf term) := by
  induction term with
  | srt sort => exact .refl
  | con name => exact .refl
  | var index => exact .refl
  | pi domain body domainIH bodyIH =>
      exact .pi domainIH bodyIH
  | app function argument functionIH argumentIH =>
      exact .app functionIH argumentIH
  | lam domain body domainIH bodyIH =>
      rw [etaNf]
      generalize hdomain : etaNf domain = normalizedDomain
      generalize hbody : etaNf body = normalizedBody
      rw [hdomain] at domainIH
      rw [hbody] at bodyIH
      have hstructure :
          Reduces signature (.lam domain body)
            (.lam normalizedDomain normalizedBody) :=
        .lam domainIH bodyIH
      cases normalizedBody with
      | srt sort => exact hstructure
      | con name => exact hstructure
      | var index => exact hstructure
      | pi bodyDomain bodyBody => exact hstructure
      | lam bodyDomain bodyBody => exact hstructure
      | app function argument =>
          cases argument with
          | srt sort => exact hstructure
          | con name => exact hstructure
          | pi argumentDomain argumentBody => exact hstructure
          | lam argumentDomain argumentBody => exact hstructure
          | app argumentFunction argumentArgument => exact hstructure
          | var index =>
              cases index with
              | succ index => exact hstructure
              | zero =>
                  cases hunbind : unbind 0 function with
                  | none => simpa [hunbind] using hstructure
                  | some reduced =>
                      simpa [hunbind] using
                        Reduces.trans hstructure (Reduces.eta hunbind)

theorem normalForm_sound (signature : Sig) (fuel : Nat) (term : Term) :
    Reduces signature term (normalForm signature fuel term) :=
  Reduces.trans
    (Reduces.ofBetaDelta (LFTyping.nf_sound signature fuel term))
    (etaNf_sound signature (LFTyping.nf signature fuel term))

theorem convBool_sound {signature : Sig} {fuel : Nat} {left right : Term}
    (hconv : convBool signature fuel left right = true) :
    Conv signature left right := by
  unfold convBool at hconv
  have hequal :
      normalForm signature fuel left = normalForm signature fuel right :=
    of_decide_eq_true hconv
  exact .common (normalForm_sound signature fuel left)
    (hequal ▸ normalForm_sound signature fuel right)

theorem convBool_refl (signature : Sig) (fuel : Nat) (term : Term) :
    convBool signature fuel term term = true := by
  simp [convBool]

/-! ## Executable boundaries -/

private def typeTerm : Term := .srt .type
private def identity : Term := .lam typeTerm (.var 0)

example :
    convBool [] 32 (.app identity typeTerm) typeTerm = true := by
  decide

example :
    convBool [] 32
      (.lam typeTerm (.app (.var 1) (.var 0))) (.var 0) = true := by
  decide

/-- A captured occurrence blocks eta contraction. -/
example :
    convBool [] 32
      (.lam typeTerm (.app (.var 0) (.var 0))) (.var 0) = false := by
  decide

/-- Eta does not identify unrelated heads. -/
example : convBool [] 32 (.con "left") (.con "right") = false := by
  decide

#print axioms Reduces.ofBetaDelta
#print axioms etaNf_sound
#print axioms normalForm_sound
#print axioms convBool_sound

end Mettapedia.GSLT.LanguageDef.LFBetaEta
