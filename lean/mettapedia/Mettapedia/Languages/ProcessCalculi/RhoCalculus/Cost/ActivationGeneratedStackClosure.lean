import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedNormalizationClosure

/-!
# Exact authority stack stability in the generated decoder

Accepted stack syntax retains every literal authority key and its temporal
position under the authored normalizer. This does not identify a product
signature with several independently stored authority atoms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

inductive StackImage : Pattern → CostStack LiteralAuthority → Prop
  | empty : StackImage (.apply "$cost:apparatus-constructor:token-stack-empty" []) .empty
  | cons {head tail : Pattern} {stack : CostStack LiteralAuthority}
      (signature : TypedSignature head) (accepted : signature? head = some signature)
      (rest : StackImage tail stack) :
      StackImage (.apply "$cost:apparatus-constructor:token-stack-cons" [head, tail])
        (.cons signature.val stack)

theorem stack_parser_image {fuel : Nat} {source : Pattern} {stack : CostStack LiteralAuthority}
    (parsed : (stack? fuel source).map Subtype.val = some stack) : StackImage source stack := by
  induction fuel, source using stack?.induct generalizing stack with
  | case1 source => simp [stack?] at parsed
  | case2 fuel =>
    simp only [stack?, Option.map_some, Option.some.injEq] at parsed
    subst stack
    exact .empty
  | case3 fuel head tail ih =>
    cases sigParsed : signature? head with
    | none => simp [stack?, sigParsed] at parsed
    | some signature =>
      cases tailParsed : stack? fuel tail with
      | none => simp [stack?, sigParsed, tailParsed] at parsed
      | some rest =>
        simp only [stack?, sigParsed, tailParsed] at parsed
        change some (CostStack.cons signature.val rest.val) = some stack at parsed
        cases parsed
        exact .cons signature sigParsed (ih (by rw [tailParsed]; rfl))
  | case4 source fuel notEmpty notCons =>
    rw [stack?.eq_4 source fuel notEmpty notCons] at parsed
    contradiction

theorem StackImage.parser_eventually {source : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage source stack) :
    ∃ bound, ∀ fuel, bound ≤ fuel → (stack? fuel source).map Subtype.val = some stack := by
  induction image with
  | empty =>
    refine ⟨1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | cons signature accepted rest ih =>
    obtain ⟨bound, readback⟩ := ih
    refine ⟨bound + 1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [stack_cons_readout, accepted, readback fuel (by omega)]
      rfl

theorem StackImage.normalize_identity {source : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage source stack) :
    normalizeReflective wrappedRhoDeclaration source = source := by
  induction image with
  | empty => rfl
  | cons signature accepted rest ih =>
    simp only [normalizeReflective, normalizeReflectiveList]
    rw [signature?_accepted_normalization_identity accepted, ih]
    rfl

theorem stack?_accepted_normalization_identity {fuel : Nat} {source : Pattern}
    {stack : CostStack LiteralAuthority}
    (parsed : (stack? fuel source).map Subtype.val = some stack) :
    normalizeReflective wrappedRhoDeclaration source = source :=
  (stack_parser_image parsed).normalize_identity

theorem stack_parser_normalization_same {fuel : Nat} {source : Pattern}
    {stack : CostStack LiteralAuthority}
    (parsed : (stack? fuel source).map Subtype.val = some stack) :
    (stack? fuel (normalizeReflective wrappedRhoDeclaration source)).map Subtype.val =
      some stack := by
  rw [stack?_accepted_normalization_identity parsed]
  exact parsed

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
