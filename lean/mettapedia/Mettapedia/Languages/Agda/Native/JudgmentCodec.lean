import Mettapedia.Languages.Agda.Native.ParameterCodec
import Mettapedia.Languages.Agda.Structural.AdministrativeStatics

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Codec
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.Languages.Agda.Structural

def putCoreJudgment : Statics.Judgment → Data
  | .context Γ => .pair (.atom 0) (context.put Γ)
  | .type Γ A => .pair (.atom 1) (.pair (context.put Γ) ((rawTerm Γ.1 .type).put A))
  | .term Γ A t => .pair (.atom 2) (.pair (context.put Γ)
      (.pair ((rawTerm Γ.1 .type).put A) ((rawTerm Γ.1 .term).put t.code)))
  | .typeEquality Γ A B => .pair (.atom 3) (.pair (context.put Γ)
      (.pair ((rawTerm Γ.1 .type).put A) ((rawTerm Γ.1 .type).put B)))
  | .termEquality Γ A t u => .pair (.atom 4) (.pair (context.put Γ)
      (.pair ((rawTerm Γ.1 .type).put A)
        (.pair ((rawTerm Γ.1 .term).put t.code) ((rawTerm Γ.1 .term).put u.code))))
  | .substitution Γ Δ σ => .pair (.atom 5)
      (.pair (context.put Γ) (.pair (context.put Δ) ((rawSub Δ.1 Γ.1).put σ)))

def getCoreJudgment : Data → Option Statics.Judgment
  | .pair (.atom 0) Γ => (context.get Γ).map (.context ·)
  | .pair (.atom 1) (.pair Γ A) => do
      let Γ ← context.get Γ
      return .type Γ (← (rawTerm Γ.1 .type).get A)
  | .pair (.atom 2) (.pair Γ (.pair A t)) => do
      let Γ ← context.get Γ
      let A ← (rawTerm Γ.1 .type).get A
      return .term Γ A ⟨← (rawTerm Γ.1 .term).get t⟩
  | .pair (.atom 3) (.pair Γ (.pair A B)) => do
      let Γ ← context.get Γ
      return .typeEquality Γ (← (rawTerm Γ.1 .type).get A) (← (rawTerm Γ.1 .type).get B)
  | .pair (.atom 4) (.pair Γ (.pair A (.pair t u))) => do
      let Γ ← context.get Γ
      let A ← (rawTerm Γ.1 .type).get A
      return .termEquality Γ A ⟨← (rawTerm Γ.1 .term).get t⟩ ⟨← (rawTerm Γ.1 .term).get u⟩
  | .pair (.atom 5) (.pair Γ (.pair Δ σ)) => do
      let Γ ← context.get Γ
      let Δ ← context.get Δ
      return .substitution Γ Δ (← (rawSub Δ.1 Γ.1).get σ)
  | _ => none

theorem get_putCoreJudgment (j : Statics.Judgment) : getCoreJudgment (putCoreJudgment j) = some j := by
  cases j with
  | context Γ =>
      rcases Γ with ⟨n, Γ⟩
      simp only [putCoreJudgment, getCoreJudgment, Codec.get_put]
      rfl
  | type Γ A =>
      rcases Γ with ⟨n, Γ⟩
      change Statics.RawTy n at A
      simp only [putCoreJudgment, getCoreJudgment, Codec.get_put, Bind.bind, Option.bind]
      rfl
  | term Γ A t =>
      rcases Γ with ⟨n, Γ⟩
      change Statics.RawTy n at A
      rcases t with ⟨t⟩
      change Statics.RawTm n at t
      simp only [putCoreJudgment, getCoreJudgment, Codec.get_put, Bind.bind, Option.bind]
      rfl
  | typeEquality Γ A B =>
      rcases Γ with ⟨n, Γ⟩
      change Statics.RawTy n at A B
      simp only [putCoreJudgment, getCoreJudgment, Codec.get_put, Bind.bind, Option.bind]
      rfl
  | termEquality Γ A t u =>
      rcases Γ with ⟨n, Γ⟩
      change Statics.RawTy n at A
      rcases t with ⟨t⟩
      rcases u with ⟨u⟩
      change Statics.RawTm n at t u
      simp only [putCoreJudgment, getCoreJudgment, Codec.get_put, Bind.bind, Option.bind]
      rfl
  | substitution Γ Δ σ =>
      rcases Γ with ⟨n, Γ⟩
      rcases Δ with ⟨m, Δ⟩
      change Statics.RawSub m n at σ
      simp only [putCoreJudgment, getCoreJudgment, Codec.get_put, Bind.bind, Option.bind]
      rfl

def coreJudgment : Codec Statics.Judgment := ⟨putCoreJudgment, getCoreJudgment, get_putCoreJudgment⟩

def putJudgment : AdministrativeStatics.Judgment → Data
  | .core j => .pair (.atom 0) (coreJudgment.put j)
  | @AdministrativeStatics.Judgment.spineAction n Γ A es B =>
      .pair (.atom 1) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A)
        (.pair ((rawTerm n .spine).put es) ((rawTerm n .type).put B))))
  | @AdministrativeStatics.Judgment.spineEquality n Γ A es fs B =>
      .pair (.atom 2) (.pair (context.put ⟨n, Γ⟩) (.pair ((rawTerm n .type).put A)
        (.pair ((rawTerm n .spine).put es)
          (.pair ((rawTerm n .spine).put fs) ((rawTerm n .type).put B)))))

def getJudgment : Data → Option AdministrativeStatics.Judgment
  | .pair (.atom 0) j => (coreJudgment.get j).map (.core ·)
  | .pair (.atom 1) (.pair Γ (.pair A (.pair es B))) => do
      let ⟨n, Γ⟩ ← context.get Γ
      return .spineAction Γ (← (rawTerm n .type).get A) (← (rawTerm n .spine).get es)
        (← (rawTerm n .type).get B)
  | .pair (.atom 2) (.pair Γ (.pair A (.pair es (.pair fs B)))) => do
      let ⟨n, Γ⟩ ← context.get Γ
      return .spineEquality Γ (← (rawTerm n .type).get A) (← (rawTerm n .spine).get es)
        (← (rawTerm n .spine).get fs) (← (rawTerm n .type).get B)
  | _ => none

theorem get_putJudgment (j : AdministrativeStatics.Judgment) : getJudgment (putJudgment j) = some j := by
  cases j <;> simp only [putJudgment, getJudgment, Codec.get_put, rawTerm_roundtrip, Bind.bind, Option.bind] <;> rfl

def judgment : Codec AdministrativeStatics.Judgment := ⟨putJudgment, getJudgment, get_putJudgment⟩

instance judgmentEq : DecidableEq AdministrativeStatics.Judgment := judgment.decEq

end Mettapedia.Languages.Agda.Native.Codec
