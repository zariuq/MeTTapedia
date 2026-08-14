import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Basic

/-!
# Wrapping and reflection preservation

The cost endofunctor re-sorts communicated payloads and continuations to the
wrapped `CostTerm` sort.  These lemmas show that capture-avoiding lifting and
COMM substitution preserve the concrete runtime-supported grammar.  Only the
drop whose bound variable is opened by COMM exposes the communicated wrapped
term; literal quoted drops stay inert.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

mutual
  theorem CostName.runtimeSupported_lift {Ground : Type u}
      (amount cutoff : Nat) : ∀ name : CostName Ground,
      name.RuntimeSupported → (name.lift amount cutoff).RuntimeSupported
    | .bvar index, _ => by
        simp only [CostName.lift]
        split <;> simp [CostName.RuntimeSupported]
    | .quote term, supported => by
        simpa [CostName.lift, CostName.RuntimeSupported] using supported
    | .signature sig, supported => by
        simpa [CostName.lift, CostName.RuntimeSupported] using supported

  theorem CostProc.runtimeSupported_lift {Ground : Type u}
      (amount cutoff : Nat) : ∀ proc : CostProc Ground,
      proc.RuntimeSupported → (proc.lift amount cutoff).RuntimeSupported
    | .nil, _ => by simp [CostProc.lift, CostProc.RuntimeSupported]
    | .par left right, supported => by
        exact ⟨
          CostProc.runtimeSupported_lift amount cutoff left supported.1,
          CostProc.runtimeSupported_lift amount cutoff right supported.2⟩
    | .send channel payload, supported => by
        exact ⟨
          CostName.runtimeSupported_lift amount cutoff channel supported.1,
          CostTerm.runtimeSupported_lift amount cutoff payload supported.2⟩
    | .recv channel body, supported => by
        exact ⟨
          CostName.runtimeSupported_lift amount cutoff channel supported.1,
          CostTerm.runtimeSupported_lift amount (cutoff + 1) body supported.2⟩

  theorem CostTerm.runtimeSupported_lift {Ground : Type u}
      (amount cutoff : Nat) : ∀ term : CostTerm Ground,
      term.RuntimeSupported → (term.lift amount cutoff).RuntimeSupported
    | .nil, _ => by simp [CostTerm.lift, CostTerm.RuntimeSupported]
    | .signed proc sig, supported => by
        exact ⟨
          CostProc.runtimeSupported_lift amount cutoff proc supported.1,
          supported.2⟩
    | .par left right, supported => by
        exact ⟨
          CostTerm.runtimeSupported_lift amount cutoff left supported.1,
          CostTerm.runtimeSupported_lift amount cutoff right supported.2⟩
    | .drop name, supported => by
        exact CostName.runtimeSupported_lift amount cutoff name supported
    | .purse location stack, supported => by
        exact ⟨
          CostName.runtimeSupported_lift amount cutoff location supported.1,
          supported.2⟩
end

mutual
  theorem CostName.runtimeSupported_substitute {Ground : Type u}
      (replacement : CostTerm Ground) (replacement_supported : replacement.RuntimeSupported)
      (depth : Nat) : ∀ name : CostName Ground,
      name.RuntimeSupported →
        (CostName.substitute replacement depth name).RuntimeSupported
    | .bvar index, _ => by
        simp only [CostName.substitute]
        split
        · exact CostTerm.runtimeSupported_lift depth 0 replacement replacement_supported
        · split <;> simp [CostName.RuntimeSupported]
    | .quote term, supported => by
        simpa [CostName.substitute, CostName.RuntimeSupported] using supported
    | .signature sig, supported => by
        simpa [CostName.substitute, CostName.RuntimeSupported] using supported

  theorem CostProc.runtimeSupported_substitute {Ground : Type u}
      (replacement : CostTerm Ground) (replacement_supported : replacement.RuntimeSupported)
      (depth : Nat) : ∀ proc : CostProc Ground,
      proc.RuntimeSupported →
        (CostProc.substitute replacement depth proc).RuntimeSupported
    | .nil, _ => by simp [CostProc.substitute, CostProc.RuntimeSupported]
    | .par left right, supported => by
        exact ⟨
          CostProc.runtimeSupported_substitute replacement replacement_supported depth
            left supported.1,
          CostProc.runtimeSupported_substitute replacement replacement_supported depth
            right supported.2⟩
    | .send channel payload, supported => by
        exact ⟨
          CostName.runtimeSupported_substitute replacement replacement_supported depth
            channel supported.1,
          CostTerm.runtimeSupported_substitute replacement replacement_supported depth
            payload supported.2⟩
    | .recv channel body, supported => by
        exact ⟨
          CostName.runtimeSupported_substitute replacement replacement_supported depth
            channel supported.1,
          CostTerm.runtimeSupported_substitute replacement replacement_supported (depth + 1)
            body supported.2⟩

  theorem CostTerm.runtimeSupported_substitute {Ground : Type u}
      (replacement : CostTerm Ground) (replacement_supported : replacement.RuntimeSupported)
      (depth : Nat) : ∀ term : CostTerm Ground,
      term.RuntimeSupported →
        (CostTerm.substitute replacement depth term).RuntimeSupported
    | .nil, _ => by simp [CostTerm.substitute, CostTerm.RuntimeSupported]
    | .signed proc sig, supported => by
        exact ⟨
          CostProc.runtimeSupported_substitute replacement replacement_supported depth
            proc supported.1,
          supported.2⟩
    | .par left right, supported => by
        exact ⟨
          CostTerm.runtimeSupported_substitute replacement replacement_supported depth
            left supported.1,
          CostTerm.runtimeSupported_substitute replacement replacement_supported depth
            right supported.2⟩
    | .drop (.bvar index), _ => by
        simp only [CostTerm.substitute]
        split
        · exact CostTerm.runtimeSupported_lift depth 0 replacement replacement_supported
        · split <;> simp [CostTerm.RuntimeSupported, CostName.RuntimeSupported]
    | .drop (.quote term), supported => by
        simpa [CostTerm.substitute, CostTerm.RuntimeSupported] using supported
    | .drop (.signature sig), supported => by
        simpa [CostTerm.substitute, CostTerm.RuntimeSupported] using supported
    | .purse location stack, supported => by
        exact ⟨
          CostName.runtimeSupported_substitute replacement replacement_supported depth
            location supported.1,
          supported.2⟩
end

/-- COMM preserves the runtime-supported wrapped-term grammar. -/
theorem CostTerm.runtimeSupported_commSubst {Ground : Type u}
    {body payload : CostTerm Ground}
    (body_supported : body.RuntimeSupported)
    (payload_supported : payload.RuntimeSupported) :
    (body.commSubst payload).RuntimeSupported := by
  exact CostTerm.runtimeSupported_substitute payload payload_supported 0 body body_supported

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
