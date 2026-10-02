import Mettapedia.Languages.VibeITP.Presentation.OperationsWf
import Mettapedia.Languages.VibeITP.Presentation.CompleteDefinitions

/-!
# Structural profiles of derived kernel statements

Every derivable statement has allocated application heads and their declared
arities. This structural profile also covers definition-generated eta terms
whose natural arities exceed the kernel's bound-variable formation bounds.
Successful statement instantiation preserves the same profile through its
actual symbol, value-depth and result-depth guards.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.Languages.VibeITP.Spec

theorem instantiateStatement_termShape (sig : Sig) (F : SymId)
    (value statement result : Term) (hvalue : TermShape sig value)
    (hstatement : TermShape sig statement)
    (hsuccess : instantiateStatement sig F value statement = some result) :
    TermShape sig result := by
  cases hs : sig F with
  | none => simp [instantiateStatement, hs] at hsuccess
  | some info =>
      simp only [instantiateStatement, hs] at hsuccess
      split at hsuccess
      · rename_i hguard
        have hF : IsFvarOf sig F info.arity := by
          simp [IsFvarOf, hs, kindOf, symArity, hguard.1]
        cases hi : instGo sig F info.arity value 0 statement with
        | none => simp [hi] at hsuccess
        | some output =>
            simp only [hi] at hsuccess
            split at hsuccess
            · simp only [Option.some.injEq] at hsuccess
              subst result
              exact inst_termShape sig F info.arity value 0 statement output
                hvalue hF hstatement hi
            · simp at hsuccess
      · simp at hsuccess

theorem derives_termShape {T : Theory} {n : Nat} (h : Hosted T n)
    {φ : Term} (d : Spec.Derives T φ) : TermShape T.sig φ := by
  induction d with
  | «axiom» hd =>
      exact wellFormed_termShape T.sig _ (h.axiomsWf _ hd).1
  | @definition definition hd =>
      exact admittedDefinition_termShape h definition hd
  | @modusPonens a b _ _ himpl _ =>
      obtain ⟨_, _, _, hargs⟩ := TermShape.app_iff.mp himpl
      exact hargs.of_mem (by simp)
  | @instantiate statement result value F _ hwf hsuccess hstatement =>
      exact instantiateStatement_termShape T.sig F value statement result
        (wellFormed_termShape T.sig value hwf) hstatement hsuccess
  | litIsNat _ =>
      exact .app (h.builtin .litIsNat) rfl (.cons (.lit _) .nil)
  | litLt _ _ =>
      exact .app (h.builtin .litLt) rfl (.cons (.lit _) (.cons (.lit _) .nil))
  | litAdd _ _ =>
      exact .app (h.builtin .eq) rfl
        (.cons (.app (h.builtin .litAdd) rfl (.cons (.lit _) (.cons (.lit _) .nil)))
          (.cons (.lit _) .nil))
  | litMul _ _ =>
      exact .app (h.builtin .eq) rfl
        (.cons (.app (h.builtin .litMul) rfl (.cons (.lit _) (.cons (.lit _) .nil)))
          (.cons (.lit _) .nil))
  | litDiv _ _ _ =>
      exact .app (h.builtin .eq) rfl
        (.cons (.app (h.builtin .litDiv) rfl (.cons (.lit _) (.cons (.lit _) .nil)))
          (.cons (.lit _) .nil))
  | litLength _ =>
      exact .app (h.builtin .eq) rfl
        (.cons (.app (h.builtin .litLength) rfl (.cons (.lit _) .nil))
          (.cons (.lit _) .nil))
  | litGet _ _ =>
      exact .app (h.builtin .eq) rfl
        (.cons (.app (h.builtin .litGet) rfl (.cons (.lit _) (.cons (.lit _) .nil)))
          (.cons (.lit _) .nil))

end Mettapedia.Languages.VibeITP.Presentation
