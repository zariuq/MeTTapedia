import Mettapedia.OSLF.Syntax.ContextualFamily

/-!
# Shared declaration interfaces for disjoint contextual families

The same constructor is used when a solver selects old holes, introduces
fresh helpers, or retains the surrounding declarations. Sharing this typed
interface keeps frame answers and their execution embeddings aligned.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualFamily

abbrev sumDeclarations {S : Signature} {First Second : Type}
    (first : First → MetaArity S) (second : Second → MetaArity S) : First ⊕ Second → MetaArity S
  | .inl identity => first identity
  | .inr identity => second identity

/-- Two distinguished arities and the unchanged surrounding declarations. -/
abbrev pairDeclarations {S : Signature} {Other : Type}
    (first second : MetaArity S) (others : Other → MetaArity S) : Bool ⊕ Other → MetaArity S :=
  sumDeclarations (fun marker => match marker with | false => first | true => second) others

end Mettapedia.OSLF.Binding.ContextualFamily
