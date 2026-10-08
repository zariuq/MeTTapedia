import Mettapedia.OSLF.Syntax.SortedCommutativeSourceContexts
import Mettapedia.OSLF.Syntax.SortedCommutativeContextCategory

/-!
# Complete-value erasure under genuinely embedded source contexts

Every native base value, including auxiliary values, commutes with erasure
when it is filled into an actual embedded source context. The result is
earned on raw constructors and complete siblings and then on both equation
quotients. It does not extend to arbitrary administrative contexts, whose
erasure is already known to fail the complete-value action square.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source

open Mettapedia.OSLF.SortedCommutative

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

private theorem erase_embedContext_fill_heq {target : (signature arity).Srt}
    (context : RawContext (signature arity) (Parallel arity) (ULift.up ()) target)
    (supplied : SortedCommutativeInstruments.Value arity .base) :
    HEq (erase ((embedContext context).fill supplied)) (context.fill (erase supplied)) := by
  apply @RawContext.rec (signature arity) (Parallel arity) (ULift.up ())
    (fun _ context => HEq (erase ((embedContext context).fill supplied)) (context.fill (erase supplied))) (t := context)
  · rfl
  · intro constructor position siblings inner inductionHypothesis
    apply heq_of_eq
    apply congrArg (Term.node (signature := signature arity) (Parallel := Parallel arity) constructor)
    funext other
    by_cases same : other = position
    · subst other
      simp only [RawContext.insert, dite_true]
      change erase ((embedContext inner).fill supplied) = inner.fill (erase supplied)
      exact eq_of_heq inductionHypothesis
    · simp only [RawContext.insert, dif_neg same]
      change erase (embed (siblings other same)) = siblings other same
      exact erase_embed (siblings other same)
  · intro target parallel inner sibling inductionHypothesis
    change target = ULift.up () at parallel
    subst target
    exact heq_of_eq (congrArg₂ (Term.cut (signature := signature arity) (Parallel := Parallel arity) rfl)
      (eq_of_heq inductionHypothesis) (erase_embed sibling))
  · intro target parallel sibling inner inductionHypothesis
    change target = ULift.up () at parallel
    subst target
    exact heq_of_eq (congrArg₂ (Term.cut (signature := signature arity) (Parallel := Parallel arity) rfl)
      (erase_embed sibling) (eq_of_heq inductionHypothesis))

theorem erase_embedContext_fill (context : Context (arity := arity))
    (supplied : SortedCommutativeInstruments.Value arity .base) :
    erase ((embedContext context).fill supplied) = context.fill (erase supplied) :=
  eq_of_heq (erase_embedContext_fill_heq context supplied)

theorem retraction_embedded_context_fill
    (context : ContextClass (signature arity) (Parallel arity) (ULift.up ()) (ULift.up ()))
    (supplied : SortedCommutativeInstruments.ValueClass arity .base) :
    classRetraction ((contextEmbedding context).fill supplied) = context.fill (classRetraction supplied) :=
  Quotient.inductionOn₂ context supplied (fun raw value => congrArg classOf (erase_embedContext_fill raw value))

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source
