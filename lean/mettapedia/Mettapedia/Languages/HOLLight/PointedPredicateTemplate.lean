import Mettapedia.Languages.HOLLight.CheckedInferenceTrace
import Mettapedia.Logic.HOL.PointedPredicate
import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Languages.HOLLight.ExportReplay

/-!
# A retained generic pointed-predicate witness

Derived proof data retain one shared, finite primitive certificate. Independent
replay and registered-formation proofs check every node. Its exact endpoint is
the pointed predicate applied to the absent point, over a type parameter and a
predicate variable. The theorem has no hypotheses or logical axiom dependencies.

Source instantiation supplies arbitrary formed carriers and predicates; no
inhabitance of the original predicate is assumed. Private declarations retain
term and proof sharing. This is a cached proof schema, not a new inference rule
or an implementation-refinement theorem.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
namespace Mettapedia.Languages.HOLLight.PointedPredicateTemplate
open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open DefinitionAdapters SignatureFormation
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

private def t0 : Ty := Ty.var (Name.mk [] "PointedCarrierElement")
private def t1 : Ty := Ty.op TypeOp.bool []
private def t2 : Ty := Ty.op TypeOp.function [t0, t1]
private def t3 : Ty := Ty.op TypeOp.function [t2, t1]
private def t4 : Ty := Ty.op TypeOp.function [t1, t1]
private def t5 : Ty := Ty.op TypeOp.function [t4, t1]
private def t6 : Ty := Ty.op TypeOp.function [t4, t5]
private def s7 : SourceTerm := SourceTerm.const Const.equality t6
private def s8 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", ""] "x") t4
private def s9 : SourceTerm := SourceTerm.app s7 s8
private def s10 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", ""] "x") t1
private def s11 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t1 s10
private def s12 : SourceTerm := SourceTerm.app s7 s11
private def s13 : SourceTerm := SourceTerm.app s12 s11
private def s14 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t1 s13
private def s15 : SourceTerm := SourceTerm.app s9 s14
private def s16 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t4 s15
private def t17 : Ty := Ty.op TypeOp.function [t1, t4]
private def s18 : SourceTerm := SourceTerm.const Const.equality t17
private def t19 : Ty := Ty.op TypeOp.function [t17, t1]
private def t20 : Ty := Ty.op TypeOp.function [t19, t1]
private def t21 : Ty := Ty.op TypeOp.function [t19, t20]
private def s22 : SourceTerm := SourceTerm.const Const.equality t21
private def s23 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", "", "", ""] "x") t17
private def s24 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", ""] "x") t1
private def s25 : SourceTerm := SourceTerm.app s23 s24
private def s26 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", "", ""] "x") t1
private def s27 : SourceTerm := SourceTerm.app s25 s26
private def s28 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", ""] "x") t17 s27
private def s29 : SourceTerm := SourceTerm.app s22 s28
private def s30 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", "", "", "", ""] "x") t1
private def s31 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", ""] "x") t1 s30
private def s32 : SourceTerm := SourceTerm.app s7 s31
private def s33 : SourceTerm := SourceTerm.app s32 s31
private def s34 : SourceTerm := SourceTerm.app s23 s33
private def s35 : SourceTerm := SourceTerm.app s34 s33
private def s36 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", ""] "x") t17 s35
private def s37 : SourceTerm := SourceTerm.app s29 s36
private def s38 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", ""] "x") t1 s37
private def s39 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", ""] "x") t1 s38
private def s40 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", ""] "x") t1
private def s41 : SourceTerm := SourceTerm.app s39 s40
private def s42 : SourceTerm := SourceTerm.app s41 s10
private def s43 : SourceTerm := SourceTerm.app s18 s42
private def s44 : SourceTerm := SourceTerm.app s43 s40
private def s45 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t1 s44
private def s46 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t1 s45
private def s47 : SourceTerm := SourceTerm.var (Name.mk ["", ""] "x") t1
private def s48 : SourceTerm := SourceTerm.app s46 s47
private def s49 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", ""] "x") t1
private def s50 : SourceTerm := SourceTerm.app s48 s49
private def s51 : SourceTerm := SourceTerm.app s46 s50
private def s52 : SourceTerm := SourceTerm.var (Name.mk ["", "", ""] "x") t1
private def s53 : SourceTerm := SourceTerm.app s46 s52
private def s54 : SourceTerm := SourceTerm.app s53 s49
private def s55 : SourceTerm := SourceTerm.app s46 s54
private def s56 : SourceTerm := SourceTerm.app s55 s49
private def s57 : SourceTerm := SourceTerm.app s51 s56
private def s58 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t1 s57
private def s59 : SourceTerm := SourceTerm.app s16 s58
private def s60 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s59
private def s61 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s60
private def t62 : Ty := Ty.op TypeOp.function [t3, t1]
private def t63 : Ty := Ty.op TypeOp.function [t3, t62]
private def s64 : SourceTerm := SourceTerm.const Const.equality t63
private def s65 : SourceTerm := SourceTerm.var (Name.mk [""] "x") t3
private def s66 : SourceTerm := SourceTerm.app s64 s65
private def s67 : SourceTerm := SourceTerm.var (Name.mk ["", "", ""] "x") t4
private def s68 : SourceTerm := SourceTerm.app s7 s67
private def s69 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t1 s40
private def s70 : SourceTerm := SourceTerm.app s7 s69
private def s71 : SourceTerm := SourceTerm.app s70 s69
private def s72 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t1 s71
private def s73 : SourceTerm := SourceTerm.app s68 s72
private def s74 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t4 s73
private def s75 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s52
private def s76 : SourceTerm := SourceTerm.app s74 s75
private def s77 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t2 s76
private def s78 : SourceTerm := SourceTerm.app s66 s77
private def s79 : SourceTerm := SourceTerm.app s61 s78
private def s80 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", "", ""] "x") t17
private def s81 : SourceTerm := SourceTerm.app s80 s10
private def s82 : SourceTerm := SourceTerm.app s81 s24
private def s83 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", ""] "x") t17 s82
private def s84 : SourceTerm := SourceTerm.app s22 s83
private def s85 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", "", "", ""] "x") t1
private def s86 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", ""] "x") t1 s85
private def s87 : SourceTerm := SourceTerm.app s7 s86
private def s88 : SourceTerm := SourceTerm.app s87 s86
private def s89 : SourceTerm := SourceTerm.app s80 s88
private def s90 : SourceTerm := SourceTerm.app s89 s88
private def s91 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", ""] "x") t17 s90
private def s92 : SourceTerm := SourceTerm.app s84 s91
private def s93 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", ""] "x") t1 s92
private def s94 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t1 s93
private def s95 : SourceTerm := SourceTerm.app s94 s49
private def s96 : SourceTerm := SourceTerm.app s95 s40
private def s97 : SourceTerm := SourceTerm.app s18 s96
private def s98 : SourceTerm := SourceTerm.app s97 s49
private def s99 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t1 s98
private def s100 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t1 s99
private def t101 : Ty := Ty.op TypeOp.function [t2, t3]
private def s102 : SourceTerm := SourceTerm.const Const.equality t101
private def s103 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", ""] "x") t2
private def s104 : SourceTerm := SourceTerm.app s102 s103
private def s105 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t0 s13
private def s106 : SourceTerm := SourceTerm.app s104 s105
private def s107 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t2 s106
private def s108 : SourceTerm := SourceTerm.var (Name.mk ["", ""] "x") t2
private def s109 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", ""] "x") t0
private def s110 : SourceTerm := SourceTerm.app s108 s109
private def s111 : SourceTerm := SourceTerm.app s46 s110
private def s112 : SourceTerm := SourceTerm.app s111 s52
private def s113 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t0 s112
private def s114 : SourceTerm := SourceTerm.app s107 s113
private def s115 : SourceTerm := SourceTerm.app s100 s114
private def s116 : SourceTerm := SourceTerm.app s115 s52
private def s117 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s116
private def s118 : SourceTerm := SourceTerm.app s74 s117
private def s119 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t2 s118
private def s120 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", ""] "x") t4
private def s121 : SourceTerm := SourceTerm.app s7 s120
private def s122 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", ""] "x") t1 s24
private def s123 : SourceTerm := SourceTerm.app s7 s122
private def s124 : SourceTerm := SourceTerm.app s123 s122
private def s125 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t1 s124
private def s126 : SourceTerm := SourceTerm.app s121 s125
private def s127 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t4 s126
private def s128 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", "", "", "", ""] "x") t17
private def s129 : SourceTerm := SourceTerm.app s128 s26
private def s130 : SourceTerm := SourceTerm.app s129 s85
private def s131 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", ""] "x") t17 s130
private def s132 : SourceTerm := SourceTerm.app s22 s131
private def s133 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", "", "", "", "", ""] "x") t1
private def s134 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", "", ""] "x") t1 s133
private def s135 : SourceTerm := SourceTerm.app s7 s134
private def s136 : SourceTerm := SourceTerm.app s135 s134
private def s137 : SourceTerm := SourceTerm.app s128 s136
private def s138 : SourceTerm := SourceTerm.app s137 s136
private def s139 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", ""] "x") t17 s138
private def s140 : SourceTerm := SourceTerm.app s132 s139
private def s141 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", ""] "x") t1 s140
private def s142 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", ""] "x") t1 s141
private def s143 : SourceTerm := SourceTerm.app s142 s10
private def s144 : SourceTerm := SourceTerm.app s143 s24
private def s145 : SourceTerm := SourceTerm.app s18 s144
private def s146 : SourceTerm := SourceTerm.app s145 s10
private def s147 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", ""] "x") t1 s146
private def s148 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t1 s147
private def s149 : SourceTerm := SourceTerm.app s148 s52
private def s150 : SourceTerm := SourceTerm.app s148 s49
private def s151 : SourceTerm := SourceTerm.app s150 s40
private def s152 : SourceTerm := SourceTerm.app s149 s151
private def s153 : SourceTerm := SourceTerm.app s148 s152
private def s154 : SourceTerm := SourceTerm.app s153 s40
private def s155 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t1 s154
private def s156 : SourceTerm := SourceTerm.app s127 s155
private def s157 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t1 s156
private def s158 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s157
private def s159 : SourceTerm := SourceTerm.var (Name.mk [] "pointedCarrierProperty") t2
private def s160 : SourceTerm := SourceTerm.var (Name.mk ["", ""] "x") t0
private def s161 : SourceTerm := SourceTerm.app s159 s160
private def s162 : SourceTerm := SourceTerm.app s158 s161
private def s163 : SourceTerm := SourceTerm.var (Name.mk ["", "", ""] "x") t2
private def s164 : SourceTerm := SourceTerm.app s163 s160
private def s165 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t2 s164
private def s166 : SourceTerm := SourceTerm.app s66 s165
private def s167 : SourceTerm := SourceTerm.app s162 s166
private def s168 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t0 s167
private def s169 : SourceTerm := SourceTerm.app s119 s168
private def s170 : SourceTerm := SourceTerm.app s79 s169
private def s171 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t3 s170
private def s172 : SourceTerm := SourceTerm.app s171 s65
private def h173 : HOL.Ty AtomicTy := HOL.Ty.prop
private theorem q174 : t1.toHOL = h173 := Ty.toHOL_bool
private theorem v175 : ReverseTranslation.reverseTy h173 = t1 := (ReverseTranslation.reverseTy_eq_iff).mpr q174.symm
private def a176 : AtomicTy := ⟨t0, ⟨rfl,rfl⟩⟩
private def h177 : HOL.Ty AtomicTy := HOL.Ty.base a176
private theorem q178 : t0.toHOL = h177 := by change (a176.val).toHOL = HOL.Ty.base a176; exact Ty.toHOL_of_isAtomic a176.property
private theorem v179 : ReverseTranslation.reverseTy h177 = t0 := (ReverseTranslation.reverseTy_eq_iff).mpr q178.symm
private def h180 : HOL.Ty AtomicTy := HOL.Ty.arr h177 h173
private theorem q181 : t2.toHOL = h180 := (Ty.toHOL_function t0 t1).trans (congrArg₂ HOL.Ty.arr q178 q174)
private theorem v182 : ReverseTranslation.reverseTy h180 = t2 := (ReverseTranslation.reverseTy_eq_iff).mpr q181.symm
private def h183 : HOL.Ty AtomicTy := HOL.Ty.arr h180 h173
private theorem q184 : t3.toHOL = h183 := (Ty.toHOL_function t2 t1).trans (congrArg₂ HOL.Ty.arr q181 q174)
private theorem v185 : ReverseTranslation.reverseTy h183 = t3 := (ReverseTranslation.reverseTy_eq_iff).mpr q184.symm
private def h186 : HOL.Ty AtomicTy := HOL.Ty.arr h183 h173
private theorem q187 : t62.toHOL = h186 := (Ty.toHOL_function t3 t1).trans (congrArg₂ HOL.Ty.arr q184 q174)
private theorem v188 : ReverseTranslation.reverseTy h186 = t62 := (ReverseTranslation.reverseTy_eq_iff).mpr q187.symm
private def h189 : HOL.Ty AtomicTy := HOL.Ty.arr h173 h173
private theorem q190 : t4.toHOL = h189 := (Ty.toHOL_function t1 t1).trans (congrArg₂ HOL.Ty.arr q174 q174)
private theorem v191 : ReverseTranslation.reverseTy h189 = t4 := (ReverseTranslation.reverseTy_eq_iff).mpr q190.symm
private def h192 : HOL.Ty AtomicTy := HOL.Ty.arr h173 h189
private theorem q193 : t17.toHOL = h192 := (Ty.toHOL_function t1 t4).trans (congrArg₂ HOL.Ty.arr q174 q190)
private theorem v194 : ReverseTranslation.reverseTy h192 = t17 := (ReverseTranslation.reverseTy_eq_iff).mpr q193.symm
private def h195 : HOL.Ty AtomicTy := HOL.Ty.arr h189 h173
private theorem q196 : t5.toHOL = h195 := (Ty.toHOL_function t4 t1).trans (congrArg₂ HOL.Ty.arr q190 q174)
private theorem v197 : ReverseTranslation.reverseTy h195 = t5 := (ReverseTranslation.reverseTy_eq_iff).mpr q196.symm
private def h198 : HOL.Ty AtomicTy := HOL.Ty.arr h189 h195
private theorem q199 : t6.toHOL = h198 := (Ty.toHOL_function t4 t5).trans (congrArg₂ HOL.Ty.arr q190 q196)
private theorem v200 : ReverseTranslation.reverseTy h198 = t6 := (ReverseTranslation.reverseTy_eq_iff).mpr q199.symm
open DefinitionAdapters SignatureFormation

/-- Source syntax with a checked interpretation of its annotations.
The witness is evaluated over the same registered signature as the receipt. -/
private structure FormedHOL (signature : Signature) (witnesses : InstanceWitnesses)
    (frame : HOL.Ctx AtomicTy) (type : HOL.Ty AtomicTy) where
  term : HOL.Term Symbol frame type
  formed : annotationsFormedB signature witnesses (ReverseTranslation.reverseTermOpen term) = true

namespace FormedHOL

variable {signature : Signature} {witnesses : InstanceWitnesses}
variable {frame : HOL.Ctx AtomicTy} {domain type : HOL.Ty AtomicTy}

def var (index : HOL.Var frame type) : FormedHOL signature witnesses frame type :=
  ⟨.var index, by rw [ReverseTranslation.reverseTermOpen,
    ReverseTranslation.reverseTermWith, ReverseTranslation.VarEnv.loose, annotationsFormedB]⟩

def const (symbol : Symbol type)
    (checked : annotationsFormedB signature witnesses (ReverseTranslation.reverseSymbol symbol) = true) :
    FormedHOL signature witnesses frame type :=
  ⟨.const symbol, checked⟩

def app (function : FormedHOL signature witnesses frame (.arr domain type))
    (argument : FormedHOL signature witnesses frame domain) :
    FormedHOL signature witnesses frame type :=
  ⟨.app function.term argument.term, by
    simp only [ReverseTranslation.reverseTermOpen, ReverseTranslation.reverseTermWith,
      annotationsFormedB, Bool.and_eq_true]
    exact ⟨function.formed, argument.formed⟩⟩

def lam (body : FormedHOL signature witnesses (domain :: frame) type)
    (domainFormed : typeFormedB signature (ReverseTranslation.reverseTy domain) = true) :
    FormedHOL signature witnesses frame (.arr domain type) :=
  ⟨.lam body.term, by
    have bodyEqual := ReverseTranslation.reverseTermWith_congr
      (env := ReverseTranslation.VarEnv.loose.lift)
      (env' := ReverseTranslation.VarEnv.loose)
      (fun index => ReverseTranslation.VarEnv.lift_loose index) body.term
    simp only [ReverseTranslation.reverseTermOpen, ReverseTranslation.reverseTermWith,
      annotationsFormedB, Bool.and_eq_true, bodyEqual]
    exact ⟨domainFormed, body.formed⟩⟩

theorem canonical_formed (term : FormedHOL signature witnesses [] type) :
    annotationsFormedB signature witnesses
      (ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty term.term).term = true := by
  apply Eq.trans ?_ term.formed
  apply congrArg (annotationsFormedB signature witnesses)
  simp only [ReverseTranslation.reverseCanonical_term, ReverseTranslation.reverseTerm,
    ReverseTranslation.reverseTermOpen]
  exact ReverseTranslation.reverseTermWith_congr (fun {type} (index : HOL.Var [] type) => nomatch index) _

theorem emptyResult_formed (term : FormedHOL signature witnesses [] type) :
    theoremFormedB signature witnesses
      (Theorem.emptyResult ∅ (ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty term.term)) =
        true := by
  simpa [theoremFormedB, sequentFormedB, Theorem.emptyResult] using term.canonical_formed

end FormedHOL


private abbrev coreSignature := ContextControls.coreContext.signature
private abbrev coreWitnesses := ExportReplay.instanceCertificates coreSignature

private def e201 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h198 := .const (.constant Const.equality t6 q199) (by decide +kernel)
private def e202 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h189] ++ tail) h189 := .var (HOL.Var.vz)
private def e203 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h189] ++ tail) h195 := .app (e201 ([h189] ++ tail)) (e202 tail)
private def e205 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .var (HOL.Var.vz)
private def e206 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e205 tail) (by decide +kernel)
private def e207 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e206 tail)
private def e208 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e207 tail) (e206 tail)
private def e209 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e208 ([h173] ++ tail)) (by decide +kernel)
private def e210 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h189] ++ tail) h173 := .app (e203 tail) (e209 ([h189] ++ tail))
private def e211 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .lam (e210 tail) (by decide +kernel)
private def e212 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h192 := .const (.constant Const.equality t17 q193) (by decide +kernel)
private def h213 : HOL.Ty AtomicTy := HOL.Ty.arr h192 h173
private theorem q214 : t19.toHOL = h213 := (Ty.toHOL_function t17 t1).trans (congrArg₂ HOL.Ty.arr q193 q174)
private theorem v215 : ReverseTranslation.reverseTy h213 = t19 := (ReverseTranslation.reverseTy_eq_iff).mpr q214.symm
private def h216 : HOL.Ty AtomicTy := HOL.Ty.arr h213 h173
private theorem q217 : t20.toHOL = h216 := (Ty.toHOL_function t19 t1).trans (congrArg₂ HOL.Ty.arr q214 q174)
private theorem v218 : ReverseTranslation.reverseTy h216 = t20 := (ReverseTranslation.reverseTy_eq_iff).mpr q217.symm
private def h219 : HOL.Ty AtomicTy := HOL.Ty.arr h213 h216
private theorem q220 : t21.toHOL = h219 := (Ty.toHOL_function t19 t20).trans (congrArg₂ HOL.Ty.arr q214 q217)
private theorem v221 : ReverseTranslation.reverseTy h219 = t21 := (ReverseTranslation.reverseTy_eq_iff).mpr q220.symm
private def e222 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h219 := .const (.constant Const.equality t21 q220) (by decide +kernel)
private def e223 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h192 := .var (HOL.Var.vz)
private def e224 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192, h173, h173] ++ tail) h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e225 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192, h173, h173] ++ tail) h189 := .app (e223 ([h173, h173] ++ tail)) (e224 tail)
private def e226 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192, h173] ++ tail) h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e227 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192, h173, h173] ++ tail) h173 := .app (e225 tail) (e226 ([h173] ++ tail))
private def e228 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h213 := .lam (e227 tail) (by decide +kernel)
private def e229 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h216 := .app (e222 ([h173, h173] ++ tail)) (e228 tail)
private def e235 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h189 := .app (e223 tail) (e208 ([h192] ++ tail))
private def e236 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h173 := .app (e235 tail) (e208 ([h192] ++ tail))
private def e237 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .lam (e236 tail) (by decide +kernel)
private def e238 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h173 := .app (e229 tail) (e237 ([h173, h173] ++ tail))
private def e239 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .lam (e238 tail) (by decide +kernel)
private def e240 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h192 := .lam (e239 tail) (by decide +kernel)
private def e241 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e242 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h189 := .app (e240 ([h173, h173] ++ tail)) (e241 tail)
private def e244 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h173 := .app (e242 tail) (e205 ([h173] ++ tail))
private def e245 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h189 := .app (e212 ([h173, h173] ++ tail)) (e244 tail)
private def e246 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h173 := .app (e245 tail) (e241 tail)
private def e247 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .lam (e246 tail) (by decide +kernel)
private def e248 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h192 := .lam (e247 tail) (by decide +kernel)
private def e249 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173, h173] ++ tail) h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e250 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173, h173] ++ tail) h189 :=
  .app (e248 ([h173, h173, h173] ++ tail)) (e249 tail)
private def e252 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173, h173] ++ tail) h173 := .app (e250 tail) (e205 ([h173, h173] ++ tail))
private def e253 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173, h173] ++ tail) h189 :=
  .app (e248 ([h173, h173, h173] ++ tail)) (e252 tail)
private def e255 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h189 := .app (e248 ([h173, h173] ++ tail)) (e241 tail)
private def e256 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h173 := .app (e255 tail) (e205 ([h173] ++ tail))
private def e257 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h189 := .app (e248 ([h173, h173] ++ tail)) (e256 tail)
private def e258 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h173 := .app (e257 tail) (e205 ([h173] ++ tail))
private def e259 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173, h173] ++ tail) h173 := .app (e253 tail) (e258 ([h173] ++ tail))
private def e260 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h189 := .lam (e259 tail) (by decide +kernel)
private def e261 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h173 := .app (e211 ([h173, h173] ++ tail)) (e260 tail)
private def e262 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .lam (e261 tail) (by decide +kernel)
private def e263 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h192 := .lam (e262 tail) (by decide +kernel)
private def h264 : HOL.Ty AtomicTy := HOL.Ty.arr h183 h186
private theorem q265 : t63.toHOL = h264 := (Ty.toHOL_function t3 t62).trans (congrArg₂ HOL.Ty.arr q184 q187)
private theorem v266 : ReverseTranslation.reverseTy h264 = t63 := (ReverseTranslation.reverseTy_eq_iff).mpr q265.symm
private def e267 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h264 := .const (.constant Const.equality t63 q265) (by decide +kernel)
private def e268 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h183] ++ tail) h183 := .var (HOL.Var.vz)
private def e269 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h183] ++ tail) h186 := .app (e267 ([h183] ++ tail)) (e268 tail)
private def e283 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e211 tail) (e206 tail)
private def e284 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h183 := .lam (e283 ([h180] ++ tail)) (by decide +kernel)
private def e285 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h183] ++ tail) h173 := .app (e269 tail) (e284 ([h183] ++ tail))
private def e286 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h183] ++ tail) h189 := .app (e263 ([h183] ++ tail)) (e285 tail)
private def h315 : HOL.Ty AtomicTy := HOL.Ty.arr h180 h183
private theorem q316 : t101.toHOL = h315 := (Ty.toHOL_function t2 t3).trans (congrArg₂ HOL.Ty.arr q181 q184)
private theorem v317 : ReverseTranslation.reverseTy h315 = t101 := (ReverseTranslation.reverseTy_eq_iff).mpr q316.symm
private def e318 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h315 := .const (.constant Const.equality t101 q316) (by decide +kernel)
private def e319 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h180] ++ tail) h180 := .var (HOL.Var.vz)
private def e320 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h180] ++ tail) h183 := .app (e318 ([h180] ++ tail)) (e319 tail)
private def e326 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h180 := .lam (e208 ([h177] ++ tail)) (by decide +kernel)
private def e327 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h180] ++ tail) h173 := .app (e320 tail) (e326 ([h180] ++ tail))
private def e328 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h183 := .lam (e327 tail) (by decide +kernel)
private def e357 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177, h173, h180] ++ tail) h180 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e358 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177] ++ tail) h177 := .var (HOL.Var.vz)
private def e359 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177, h173, h180] ++ tail) h173 := .app (e357 tail) (e358 ([h173, h180] ++ tail))
private def e360 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177, h173, h180] ++ tail) h189 :=
  .app (e248 ([h177, h173, h180] ++ tail)) (e359 tail)
private def e361 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177, h173] ++ tail) h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e362 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177, h173, h180] ++ tail) h173 := .app (e360 tail) (e361 ([h180] ++ tail))
private def e363 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h180] ++ tail) h180 := .lam (e362 tail) (by decide +kernel)
private def e364 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h180] ++ tail) h173 := .app (e328 ([h173, h180] ++ tail)) (e363 tail)
private def e365 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h180] ++ tail) h189 := .app (e248 ([h173, h180] ++ tail)) (e364 tail)
private def e366 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h180] ++ tail) h173 := .app (e365 tail) (e205 ([h180] ++ tail))
private def e367 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h180] ++ tail) h189 := .lam (e366 tail) (by decide +kernel)
private def e368 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h180] ++ tail) h173 := .app (e211 ([h180] ++ tail)) (e367 tail)
private def e369 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h183 := .lam (e368 tail) (by decide +kernel)
private def e415 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173, h173] ++ tail) h173 := .app (e250 tail) (e256 ([h173] ++ tail))
private def e416 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173, h173] ++ tail) h189 :=
  .app (e248 ([h173, h173, h173] ++ tail)) (e415 tail)
private def e417 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173, h173] ++ tail) h173 := .app (e416 tail) (e205 ([h173, h173] ++ tail))
private def e418 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h189 := .lam (e417 tail) (by decide +kernel)
private def e419 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h173 := .app (e211 ([h173, h173] ++ tail)) (e418 tail)
private def e420 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .lam (e419 tail) (by decide +kernel)
private def e421 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h192 := .lam (e420 tail) (by decide +kernel)
private def e422 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h180 := .const (.variable ⟨Name.mk [] "pointedCarrierProperty", t2⟩ q181) (by decide +kernel)
private def e424 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177] ++ tail) h173 := .app (e422 ([h177] ++ tail)) (e358 tail)
private def e425 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177] ++ tail) h189 := .app (e421 ([h177] ++ tail)) (e424 tail)
private def e427 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177, h183] ++ tail) h183 := .var (HOL.Var.vs (HOL.Var.vz))
private def e428 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177, h183] ++ tail) h186 := .app (e267 ([h177, h183] ++ tail)) (e427 tail)
private def e430 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h180, h177] ++ tail) h177 := .var (HOL.Var.vs (HOL.Var.vz))
private def e431 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h180, h177] ++ tail) h173 := .app (e319 ([h177] ++ tail)) (e430 tail)
private def e432 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177] ++ tail) h183 := .lam (e431 tail) (by decide +kernel)
private def e433 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177, h183] ++ tail) h173 := .app (e428 tail) (e432 ([h183] ++ tail))
private def e434 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177, h183] ++ tail) h173 := .app (e425 ([h183] ++ tail)) (e433 tail)
private def e435 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h183] ++ tail) h180 := .lam (e434 tail) (by decide +kernel)
private def e436 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h183] ++ tail) h173 := .app (e369 ([h183] ++ tail)) (e435 tail)
private def e437 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h183] ++ tail) h173 := .app (e286 tail) (e436 tail)
private def e438 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h186 := .lam (e437 tail) (by decide +kernel)
private def e439 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h183 := .const (.variable ⟨Name.mk [""] "x", t3⟩ q184) (by decide +kernel)
private def e440 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e438 tail) (e439 tail)
private def c441 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e440 []).term
private theorem n442 : s172.toDB [] = c441.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k443 : CheckedSourceTerm := ⟨s172, t1, by rw [← DBTerm.inferType_toDB [] s172, n442]; exact c441.checked.trans (congrArg some v175)⟩
private def r444 : InferenceRequest := .beta k443
private def e446 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e440 tail)
private def e502 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h186 := .app (e267 tail) (e439 tail)
private def e518 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e502 tail) (e284 tail)
private def e519 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e263 tail) (e518 tail)
private def e663 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177] ++ tail) h173 := .app (e502 ([h177] ++ tail)) (e432 tail)
private def e664 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177] ++ tail) h173 := .app (e425 tail) (e663 tail)
private def e665 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h180 := .lam (e664 tail) (by decide +kernel)
private def e666 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e369 tail) (e665 tail)
private def e667 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e519 tail) (e666 tail)
private def e668 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e446 tail) (e667 tail)
private def c669 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e668 []).term
private def f670 : Theorem := Theorem.emptyResult ([].toFinset) c669
private def s671 : SourceTerm := SourceTerm.var (Name.mk ["", ""] "x") t4
private def s672 : SourceTerm := SourceTerm.app s7 s671
private def s673 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t1 s49
private def s674 : SourceTerm := SourceTerm.app s7 s673
private def s675 : SourceTerm := SourceTerm.app s674 s673
private def s676 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s675
private def s677 : SourceTerm := SourceTerm.app s672 s676
private def s678 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t4 s677
private def s679 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s47
private def s680 : SourceTerm := SourceTerm.app s678 s679
private def s681 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t2 s680
private def c682 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e284 []).term
private theorem n683 : s681.toDB [] = c682.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k684 : CheckedSourceTerm := ⟨s681, t3, by rw [← DBTerm.inferType_toDB [] s681, n683]; exact c682.checked.trans (congrArg some v185)⟩
private def r685 : InferenceRequest := .inst [(k684, s65)] f670
private def e686 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e438 tail) (e284 tail)
private def e687 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e686 tail)
private def e688 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h186 := .app (e267 tail) (e284 tail)
private def e689 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e688 tail) (e284 tail)
private def e690 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e263 tail) (e689 tail)
private def e707 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177] ++ tail) h173 := .app (e688 ([h177] ++ tail)) (e432 tail)
private def e708 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h177] ++ tail) h173 := .app (e425 tail) (e707 tail)
private def e709 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h180 := .lam (e708 tail) (by decide +kernel)
private def e710 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e369 tail) (e709 tail)
private def e711 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e690 tail) (e710 tail)
private def e712 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e687 tail) (e711 tail)
private def c713 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e712 []).term
private def f714 : Theorem := Theorem.emptyResult ([].toFinset) c713
private def c715 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e212 []).term
private def r716 : InferenceRequest := .refl c715
private def t717 : Ty := Ty.op TypeOp.function [t17, t19]
private def h718 : HOL.Ty AtomicTy := HOL.Ty.arr h192 h213
private theorem q719 : t717.toHOL = h718 := (Ty.toHOL_function t17 t19).trans (congrArg₂ HOL.Ty.arr q193 q214)
private theorem v720 : ReverseTranslation.reverseTy h718 = t717 := (ReverseTranslation.reverseTy_eq_iff).mpr q719.symm
private def e721 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h718 := .const (.constant Const.equality t717 q719) (by decide +kernel)
private def e722 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .app (e721 tail) (e212 tail)
private def e723 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e722 tail) (e212 tail)
private def c724 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e723 []).term
private def f725 : Theorem := Theorem.emptyResult ([].toFinset) c724
private def r726 : InferenceRequest := .mkComb f725 f714
private def e728 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e687 tail)
private def e729 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e711 tail)
private def e730 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e728 tail) (e729 tail)
private def c731 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e730 []).term
private def f732 : Theorem := Theorem.emptyResult ([].toFinset) c731
private def c733 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e686 []).term
private def r734 : InferenceRequest := .refl c733
private def e735 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e687 tail) (e686 tail)
private def c736 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e735 []).term
private def f737 : Theorem := Theorem.emptyResult ([].toFinset) c736
private def r738 : InferenceRequest := .mkComb f732 f737
private def e739 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e735 tail)
private def e740 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e729 tail) (e686 tail)
private def e741 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e739 tail) (e740 tail)
private def c742 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e741 []).term
private def f743 : Theorem := Theorem.emptyResult ([].toFinset) c742
private def r744 : InferenceRequest := .eqMp f743 f737
private def c745 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e740 []).term
private def f746 : Theorem := Theorem.emptyResult ([].toFinset) c745
private def c747 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e711 []).term
private def r748 : InferenceRequest := .assume c747
private def f749 : Theorem := Theorem.emptyResult ([c747].toFinset) c747
private def r750 : InferenceRequest := .deductAntisym f749 f746
private def e751 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e729 tail) (e740 tail)
private def c752 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e751 []).term
private def f753 : Theorem := Theorem.emptyResult ([c747].toFinset) c752
private def r754 : InferenceRequest := .eqMp f753 f749
private def f755 : Theorem := Theorem.emptyResult ([c747].toFinset) c745
private def r756 : InferenceRequest := .deductAntisym f749 f749
private def e757 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e729 tail) (e711 tail)
private def c758 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e757 []).term
private def f759 : Theorem := Theorem.emptyResult ([].toFinset) c758
private def r760 : InferenceRequest := .eqMp f759 f749
private def r761 : InferenceRequest := .eqMp f755 f749
private def f762 : Theorem := Theorem.emptyResult ([c747].toFinset) c733
private def e763 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h192 := .const (.variable ⟨Name.mk [""] "x", t17⟩ q193) (by decide +kernel)
private def c764 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e763 []).term
private def r765 : InferenceRequest := .refl c764
private def e766 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .app (e721 tail) (e763 tail)
private def e767 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e766 tail) (e763 tail)
private def c768 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e767 []).term
private def f769 : Theorem := Theorem.emptyResult ([].toFinset) c768
private def c772 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e206 []).term
private def r773 : InferenceRequest := .refl c772
private def c776 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e208 []).term
private def f777 : Theorem := Theorem.emptyResult ([].toFinset) c776
private def r778 : InferenceRequest := .deductAntisym f749 f777
private def e779 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e729 tail) (e208 tail)
private def c780 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e779 []).term
private def f781 : Theorem := Theorem.emptyResult ([c747].toFinset) c780
private def r782 : InferenceRequest := .deductAntisym f762 f777
private def e783 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e687 tail) (e208 tail)
private def c784 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e783 []).term
private def f785 : Theorem := Theorem.emptyResult ([c747].toFinset) c784
private def r786 : InferenceRequest := .mkComb f769 f781
private def e787 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e763 tail) (e711 tail)
private def e788 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e787 tail)
private def e789 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e763 tail) (e208 tail)
private def e790 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e788 tail) (e789 tail)
private def c791 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e790 []).term
private def f792 : Theorem := Theorem.emptyResult ([c747].toFinset) c791
private def r793 : InferenceRequest := .mkComb f792 f785
private def e794 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e787 tail) (e686 tail)
private def e795 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e794 tail)
private def e796 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e789 tail) (e208 tail)
private def e797 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e795 tail) (e796 tail)
private def c798 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e797 []).term
private def f799 : Theorem := Theorem.emptyResult ([c747].toFinset) c798
private def r800 : InferenceRequest := .abs ⟨Name.mk [""] "x", t17⟩ f799
private def e1038 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h189 := .app (e223 tail) (e711 ([h192] ++ tail))
private def e1263 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h173 := .app (e1038 tail) (e686 ([h192] ++ tail))
private def e1264 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .lam (e1263 tail) (by decide +kernel)
private def e1265 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h216 := .app (e222 tail) (e1264 tail)
private def e1274 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1265 tail) (e237 tail)
private def c1275 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1274 []).term
private def f1276 : Theorem := Theorem.emptyResult ([c747].toFinset) c1275
private def s1277 : SourceTerm := SourceTerm.var (Name.mk ["", "", ""] "x") t17
private def s1278 : SourceTerm := SourceTerm.var (Name.mk [""] "x") t1
private def s1279 : SourceTerm := SourceTerm.app s1277 s1278
private def s1280 : SourceTerm := SourceTerm.app s1279 s47
private def s1281 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t17 s1280
private def s1282 : SourceTerm := SourceTerm.app s22 s1281
private def s1283 : SourceTerm := SourceTerm.app s1277 s675
private def s1284 : SourceTerm := SourceTerm.app s1283 s675
private def s1285 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t17 s1284
private def s1286 : SourceTerm := SourceTerm.app s1282 s1285
private def s1287 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s1286
private def s1288 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s1287
private def s1289 : SourceTerm := SourceTerm.app s1288 s1278
private def e1309 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .const (.variable ⟨Name.mk [""] "x", t1⟩ q174) (by decide +kernel)
private def e1310 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e240 tail) (e1309 tail)
private def c1311 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1310 []).term
private theorem n1312 : s1289.toDB [] = c1311.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1313 : CheckedSourceTerm := ⟨s1289, t4, by rw [← DBTerm.inferType_toDB [] s1289, n1312]; exact c1311.checked.trans (congrArg some v191)⟩
private def r1314 : InferenceRequest := .beta k1313
private def e1315 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e1310 tail)
private def e1319 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h189 := .app (e223 tail) (e1309 ([h192] ++ tail))
private def e1321 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192, h173] ++ tail) h173 := .app (e1319 ([h173] ++ tail)) (e226 tail)
private def e1322 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h213 := .lam (e1321 tail) (by decide +kernel)
private def e1323 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h216 := .app (e222 ([h173] ++ tail)) (e1322 tail)
private def e1332 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e1323 tail) (e237 ([h173] ++ tail))
private def e1333 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e1332 tail) (by decide +kernel)
private def e1334 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1315 tail) (e1333 tail)
private def c1335 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1334 []).term
private def f1336 : Theorem := Theorem.emptyResult ([].toFinset) c1335
private def s1337 : SourceTerm := SourceTerm.app s100 s1278
private def s1338 : SourceTerm := SourceTerm.app s1337 s52
private def s1339 : SourceTerm := SourceTerm.app s100 s1338
private def s1340 : SourceTerm := SourceTerm.app s100 s47
private def s1341 : SourceTerm := SourceTerm.app s1340 s52
private def s1342 : SourceTerm := SourceTerm.app s100 s1341
private def s1343 : SourceTerm := SourceTerm.app s1342 s52
private def s1344 : SourceTerm := SourceTerm.app s1339 s1343
private def s1345 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s1344
private def s1346 : SourceTerm := SourceTerm.app s74 s1345
private def s1347 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s1346
private def s1348 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s1347
private def s1349 : SourceTerm := SourceTerm.app s64 s681
private def s1350 : SourceTerm := SourceTerm.app s1349 s681
private def s1351 : SourceTerm := SourceTerm.app s1348 s1350
private def s1352 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", ""] "x") t17
private def s1353 : SourceTerm := SourceTerm.app s1352 s40
private def s1354 : SourceTerm := SourceTerm.app s1353 s10
private def s1355 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", ""] "x") t17 s1354
private def s1356 : SourceTerm := SourceTerm.app s22 s1355
private def s1357 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", ""] "x") t1 s26
private def s1358 : SourceTerm := SourceTerm.app s7 s1357
private def s1359 : SourceTerm := SourceTerm.app s1358 s1357
private def s1360 : SourceTerm := SourceTerm.app s1352 s1359
private def s1361 : SourceTerm := SourceTerm.app s1360 s1359
private def s1362 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", ""] "x") t17 s1361
private def s1363 : SourceTerm := SourceTerm.app s1356 s1362
private def s1364 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t1 s1363
private def s1365 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t1 s1364
private def s1366 : SourceTerm := SourceTerm.app s1365 s52
private def s1367 : SourceTerm := SourceTerm.app s1366 s49
private def s1368 : SourceTerm := SourceTerm.app s18 s1367
private def s1369 : SourceTerm := SourceTerm.app s1368 s52
private def s1370 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t1 s1369
private def s1371 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s1370
private def s1372 : SourceTerm := SourceTerm.app s102 s163
private def s1373 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t0 s71
private def s1374 : SourceTerm := SourceTerm.app s1372 s1373
private def s1375 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t2 s1374
private def s1376 : SourceTerm := SourceTerm.var (Name.mk [""] "x") t2
private def s1377 : SourceTerm := SourceTerm.var (Name.mk ["", "", ""] "x") t0
private def s1378 : SourceTerm := SourceTerm.app s1376 s1377
private def s1379 : SourceTerm := SourceTerm.app s100 s1378
private def s1380 : SourceTerm := SourceTerm.app s1379 s47
private def s1381 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t0 s1380
private def s1382 : SourceTerm := SourceTerm.app s1375 s1381
private def s1383 : SourceTerm := SourceTerm.app s1371 s1382
private def s1384 : SourceTerm := SourceTerm.app s1383 s47
private def s1385 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s1384
private def s1386 : SourceTerm := SourceTerm.app s678 s1385
private def s1387 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t2 s1386
private def s1388 : SourceTerm := SourceTerm.app s48 s54
private def s1389 : SourceTerm := SourceTerm.app s46 s1388
private def s1390 : SourceTerm := SourceTerm.app s1389 s49
private def s1391 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t1 s1390
private def s1392 : SourceTerm := SourceTerm.app s16 s1391
private def s1393 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s1392
private def s1394 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s1393
private def s1395 : SourceTerm := SourceTerm.var (Name.mk [""] "x") t0
private def s1396 : SourceTerm := SourceTerm.app s159 s1395
private def s1397 : SourceTerm := SourceTerm.app s1394 s1396
private def s1398 : SourceTerm := SourceTerm.app s64 s77
private def s1399 : SourceTerm := SourceTerm.app s108 s1395
private def s1400 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t2 s1399
private def s1401 : SourceTerm := SourceTerm.app s1398 s1400
private def s1402 : SourceTerm := SourceTerm.app s1397 s1401
private def s1403 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t0 s1402
private def s1404 : SourceTerm := SourceTerm.app s1387 s1403
private def s1405 : SourceTerm := SourceTerm.app s1351 s1404
private theorem n1406 : s1405.toDB [] = c747.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1407 : CheckedSourceTerm := ⟨s1405, t1, by rw [← DBTerm.inferType_toDB [] s1405, n1406]; exact c747.checked.trans (congrArg some v175)⟩
private def r1408 : InferenceRequest := .inst [(k1407, s1278)] f1336
private def e1409 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e240 tail) (e711 tail)
private def e1410 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e1409 tail)
private def e1647 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192, h173] ++ tail) h173 := .app (e1038 ([h173] ++ tail)) (e226 tail)
private def e1648 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h213 := .lam (e1647 tail) (by decide +kernel)
private def e1649 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h216 := .app (e222 ([h173] ++ tail)) (e1648 tail)
private def e1650 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e1649 tail) (e237 ([h173] ++ tail))
private def e1651 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e1650 tail) (by decide +kernel)
private def e1652 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1410 tail) (e1651 tail)
private def c1653 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1652 []).term
private def f1654 : Theorem := Theorem.emptyResult ([].toFinset) c1653
private def r1655 : InferenceRequest := .mkComb f1654 f737
private def e1656 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1409 tail) (e686 tail)
private def e1657 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e1656 tail)
private def e1658 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1651 tail) (e686 tail)
private def e1659 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1657 tail) (e1658 tail)
private def c1660 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1659 []).term
private def f1661 : Theorem := Theorem.emptyResult ([].toFinset) c1660
private def s1662 : SourceTerm := SourceTerm.var (Name.mk ["", ""] "x") t17
private def s1663 : SourceTerm := SourceTerm.app s149 s40
private def s1664 : SourceTerm := SourceTerm.app s148 s1663
private def s1665 : SourceTerm := SourceTerm.app s148 s151
private def s1666 : SourceTerm := SourceTerm.app s1665 s40
private def s1667 : SourceTerm := SourceTerm.app s1664 s1666
private def s1668 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t1 s1667
private def s1669 : SourceTerm := SourceTerm.app s127 s1668
private def s1670 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t1 s1669
private def s1671 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s1670
private def s1672 : SourceTerm := SourceTerm.app s16 s673
private def s1673 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t2 s1672
private def s1674 : SourceTerm := SourceTerm.app s64 s1673
private def s1675 : SourceTerm := SourceTerm.app s1674 s1673
private def s1676 : SourceTerm := SourceTerm.app s1671 s1675
private def s1677 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", ""] "x") t2
private def s1678 : SourceTerm := SourceTerm.app s102 s1677
private def s1679 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t0 s124
private def s1680 : SourceTerm := SourceTerm.app s1678 s1679
private def s1681 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t2 s1680
private def s1682 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", ""] "x") t0
private def s1683 : SourceTerm := SourceTerm.app s163 s1682
private def s1684 : SourceTerm := SourceTerm.app s148 s1683
private def s1685 : SourceTerm := SourceTerm.app s1684 s49
private def s1686 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t0 s1685
private def s1687 : SourceTerm := SourceTerm.app s1681 s1686
private def s1688 : SourceTerm := SourceTerm.app s46 s1687
private def s1689 : SourceTerm := SourceTerm.app s1688 s49
private def s1690 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t1 s1689
private def s1691 : SourceTerm := SourceTerm.app s16 s1690
private def s1692 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t2 s1691
private def s1693 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", ""] "x") t4
private def s1694 : SourceTerm := SourceTerm.app s7 s1693
private def s1695 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", ""] "x") t1 s1359
private def s1696 : SourceTerm := SourceTerm.app s1694 s1695
private def s1697 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t4 s1696
private def s1698 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", "", "", "", "", ""] "x") t17
private def s1699 : SourceTerm := SourceTerm.app s1698 s85
private def s1700 : SourceTerm := SourceTerm.app s1699 s30
private def s1701 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", "", ""] "x") t17 s1700
private def s1702 : SourceTerm := SourceTerm.app s22 s1701
private def s1703 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", "", "", "", "", "", ""] "x") t1
private def s1704 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", "", "", ""] "x") t1 s1703
private def s1705 : SourceTerm := SourceTerm.app s7 s1704
private def s1706 : SourceTerm := SourceTerm.app s1705 s1704
private def s1707 : SourceTerm := SourceTerm.app s1698 s1706
private def s1708 : SourceTerm := SourceTerm.app s1707 s1706
private def s1709 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", "", ""] "x") t17 s1708
private def s1710 : SourceTerm := SourceTerm.app s1702 s1709
private def s1711 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", ""] "x") t1 s1710
private def s1712 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", ""] "x") t1 s1711
private def s1713 : SourceTerm := SourceTerm.app s1712 s24
private def s1714 : SourceTerm := SourceTerm.app s1713 s26
private def s1715 : SourceTerm := SourceTerm.app s18 s1714
private def s1716 : SourceTerm := SourceTerm.app s1715 s24
private def s1717 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", ""] "x") t1 s1716
private def s1718 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", ""] "x") t1 s1717
private def s1719 : SourceTerm := SourceTerm.app s1718 s49
private def s1720 : SourceTerm := SourceTerm.app s1718 s40
private def s1721 : SourceTerm := SourceTerm.app s1720 s10
private def s1722 : SourceTerm := SourceTerm.app s1719 s1721
private def s1723 : SourceTerm := SourceTerm.app s1718 s1722
private def s1724 : SourceTerm := SourceTerm.app s1723 s10
private def s1725 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t1 s1724
private def s1726 : SourceTerm := SourceTerm.app s1697 s1725
private def s1727 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t1 s1726
private def s1728 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t1 s1727
private def s1729 : SourceTerm := SourceTerm.app s159 s1377
private def s1730 : SourceTerm := SourceTerm.app s1728 s1729
private def s1731 : SourceTerm := SourceTerm.app s127 s69
private def s1732 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t2 s1731
private def s1733 : SourceTerm := SourceTerm.app s64 s1732
private def s1734 : SourceTerm := SourceTerm.app s103 s1377
private def s1735 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t2 s1734
private def s1736 : SourceTerm := SourceTerm.app s1733 s1735
private def s1737 : SourceTerm := SourceTerm.app s1730 s1736
private def s1738 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t0 s1737
private def s1739 : SourceTerm := SourceTerm.app s1692 s1738
private def s1740 : SourceTerm := SourceTerm.app s1676 s1739
private def s1741 : SourceTerm := SourceTerm.app s1662 s1740
private def s1742 : SourceTerm := SourceTerm.app s1741 s1278
private def s1743 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t17 s1742
private def s1744 : SourceTerm := SourceTerm.app s22 s1743
private def s1745 : SourceTerm := SourceTerm.app s7 s75
private def s1746 : SourceTerm := SourceTerm.app s1745 s75
private def s1747 : SourceTerm := SourceTerm.app s1662 s1746
private def s1748 : SourceTerm := SourceTerm.app s1747 s1746
private def s1749 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t17 s1748
private def s1750 : SourceTerm := SourceTerm.app s1744 s1749
private def s1751 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s1750
private def s1752 : SourceTerm := SourceTerm.app s1751 s1278
private def e1753 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1651 tail) (e1309 tail)
private def c1754 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1753 []).term
private theorem n1755 : s1752.toDB [] = c1754.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1756 : CheckedSourceTerm := ⟨s1752, t1, by rw [← DBTerm.inferType_toDB [] s1752, n1755]; exact c1754.checked.trans (congrArg some v175)⟩
private def r1757 : InferenceRequest := .beta k1756
private def e1758 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e1753 tail)
private def e1760 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h173 := .app (e1038 tail) (e1309 ([h192] ++ tail))
private def e1761 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .lam (e1760 tail) (by decide +kernel)
private def e1762 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h216 := .app (e222 tail) (e1761 tail)
private def e1763 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1762 tail) (e237 tail)
private def e1764 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1758 tail) (e1763 tail)
private def c1765 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1764 []).term
private def f1766 : Theorem := Theorem.emptyResult ([].toFinset) c1765
private def s1767 : SourceTerm := SourceTerm.app s171 s681
private theorem n1768 : s1767.toDB [] = c733.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1769 : CheckedSourceTerm := ⟨s1767, t1, by rw [← DBTerm.inferType_toDB [] s1767, n1768]; exact c733.checked.trans (congrArg some v175)⟩
private def r1770 : InferenceRequest := .inst [(k1769, s1278)] f1766
private def e1771 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e1658 tail)
private def e1772 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1771 tail) (e1274 tail)
private def c1773 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1772 []).term
private def f1774 : Theorem := Theorem.emptyResult ([].toFinset) c1773
private def r1775 : InferenceRequest := .trans f1661 f1774
private def e1776 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1657 tail) (e1274 tail)
private def c1777 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1776 []).term
private def f1778 : Theorem := Theorem.emptyResult ([].toFinset) c1777
private def r1779 : InferenceRequest := .mkComb f725 f1778
private def e1780 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e1657 tail)
private def e1781 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e1274 tail)
private def e1782 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1780 tail) (e1781 tail)
private def c1783 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1782 []).term
private def f1784 : Theorem := Theorem.emptyResult ([].toFinset) c1783
private def c1785 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1656 []).term
private def r1786 : InferenceRequest := .refl c1785
private def e1787 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1657 tail) (e1656 tail)
private def c1788 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1787 []).term
private def f1789 : Theorem := Theorem.emptyResult ([].toFinset) c1788
private def r1790 : InferenceRequest := .mkComb f1784 f1789
private def e1791 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e1787 tail)
private def e1792 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1781 tail) (e1656 tail)
private def e1793 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1791 tail) (e1792 tail)
private def c1794 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1793 []).term
private def f1795 : Theorem := Theorem.emptyResult ([].toFinset) c1794
private def r1796 : InferenceRequest := .eqMp f1795 f1789
private def c1797 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1792 []).term
private def f1798 : Theorem := Theorem.emptyResult ([].toFinset) c1797
private def r1799 : InferenceRequest := .eqMp f1798 f1276
private def f1800 : Theorem := Theorem.emptyResult ([c747].toFinset) c1785
private def r1801 : InferenceRequest := .assume c1785
private def f1802 : Theorem := Theorem.emptyResult ([c1785].toFinset) c1785
private def r1803 : InferenceRequest := .eqMp f1778 f1802
private def f1804 : Theorem := Theorem.emptyResult ([c1785].toFinset) c1275
private def e1806 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .lam (e241 tail) (by decide +kernel)
private def e1807 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h192 := .lam (e1806 tail) (by decide +kernel)
private def c1808 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1807 []).term
private def r1809 : InferenceRequest := .refl c1808
private def e1810 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .app (e721 tail) (e1807 tail)
private def e1811 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1810 tail) (e1807 tail)
private def c1812 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1811 []).term
private def f1813 : Theorem := Theorem.emptyResult ([].toFinset) c1812
private def r1814 : InferenceRequest := .mkComb f1804 f1813
private def e1815 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1264 tail) (e1807 tail)
private def e1816 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e1815 tail)
private def e1817 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e237 tail) (e1807 tail)
private def e1818 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1816 tail) (e1817 tail)
private def c1819 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1818 []).term
private def f1820 : Theorem := Theorem.emptyResult ([c1785].toFinset) c1819
private def s1821 : SourceTerm := SourceTerm.var (Name.mk [""] "x") t17
private def s1822 : SourceTerm := SourceTerm.app s1398 s77
private def s1823 : SourceTerm := SourceTerm.app s61 s1822
private def s1824 : SourceTerm := SourceTerm.app s1674 s165
private def s1825 : SourceTerm := SourceTerm.app s162 s1824
private def s1826 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t0 s1825
private def s1827 : SourceTerm := SourceTerm.app s119 s1826
private def s1828 : SourceTerm := SourceTerm.app s1823 s1827
private def s1829 : SourceTerm := SourceTerm.app s1821 s1828
private def s1830 : SourceTerm := SourceTerm.var (Name.mk ["", ""] "x") t3
private def s1831 : SourceTerm := SourceTerm.app s64 s1830
private def s1832 : SourceTerm := SourceTerm.app s1831 s1673
private def s1833 : SourceTerm := SourceTerm.app s1671 s1832
private def s1834 : SourceTerm := SourceTerm.app s1831 s1735
private def s1835 : SourceTerm := SourceTerm.app s1730 s1834
private def s1836 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t0 s1835
private def s1837 : SourceTerm := SourceTerm.app s1692 s1836
private def s1838 : SourceTerm := SourceTerm.app s1833 s1837
private def s1839 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t3 s1838
private def s1840 : SourceTerm := SourceTerm.app s1839 s77
private def s1841 : SourceTerm := SourceTerm.app s1829 s1840
private def s1842 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t17 s1841
private def s1843 : SourceTerm := SourceTerm.app s1842 s1821
private def e1844 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1264 tail) (e763 tail)
private def c1845 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1844 []).term
private theorem n1846 : s1843.toDB [] = c1845.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1847 : CheckedSourceTerm := ⟨s1843, t1, by rw [← DBTerm.inferType_toDB [] s1843, n1846]; exact c1845.checked.trans (congrArg some v175)⟩
private def r1848 : InferenceRequest := .beta k1847
private def e1849 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e1844 tail)
private def e1850 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1849 tail) (e794 tail)
private def c1851 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1850 []).term
private def f1852 : Theorem := Theorem.emptyResult ([].toFinset) c1851
private def s1853 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s1278
private def s1854 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s1853
private theorem n1855 : s1854.toDB [] = c1808.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1856 : CheckedSourceTerm := ⟨s1854, t17, by rw [← DBTerm.inferType_toDB [] s1854, n1855]; exact c1808.checked.trans (congrArg some v194)⟩
private def r1857 : InferenceRequest := .inst [(k1856, s1821)] f1852
private def e1858 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e1807 tail) (e711 tail)
private def e1859 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1858 tail) (e686 tail)
private def e1860 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1816 tail) (e1859 tail)
private def c1861 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1860 []).term
private def f1862 : Theorem := Theorem.emptyResult ([].toFinset) c1861
private def s1863 : SourceTerm := SourceTerm.app s1854 s1278
private def e1864 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e1807 tail) (e1309 tail)
private def c1865 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1864 []).term
private theorem n1866 : s1863.toDB [] = c1865.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1867 : CheckedSourceTerm := ⟨s1863, t4, by rw [← DBTerm.inferType_toDB [] s1863, n1866]; exact c1865.checked.trans (congrArg some v191)⟩
private def r1868 : InferenceRequest := .beta k1867
private def e1869 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e1864 tail)
private def e1871 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e1309 ([h173] ++ tail)) (by decide +kernel)
private def e1872 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1869 tail) (e1871 tail)
private def c1873 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1872 []).term
private def f1874 : Theorem := Theorem.emptyResult ([].toFinset) c1873
private def r1875 : InferenceRequest := .inst [(k1407, s1278)] f1874
private def e1876 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e1858 tail)
private def e2112 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e711 ([h173] ++ tail)) (by decide +kernel)
private def e2113 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1876 tail) (e2112 tail)
private def c2114 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2113 []).term
private def f2115 : Theorem := Theorem.emptyResult ([].toFinset) c2114
private def r2116 : InferenceRequest := .mkComb f2115 f737
private def e2117 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e1859 tail)
private def e2118 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2112 tail) (e686 tail)
private def e2119 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2117 tail) (e2118 tail)
private def c2120 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2119 []).term
private def f2121 : Theorem := Theorem.emptyResult ([].toFinset) c2120
private def s2122 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s1828
private def s2123 : SourceTerm := SourceTerm.app s2122 s1278
private def e2124 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2112 tail) (e1309 tail)
private def c2125 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2124 []).term
private theorem n2126 : s2123.toDB [] = c2125.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2127 : CheckedSourceTerm := ⟨s2123, t1, by rw [← DBTerm.inferType_toDB [] s2123, n2126]; exact c2125.checked.trans (congrArg some v175)⟩
private def r2128 : InferenceRequest := .beta k2127
private def e2129 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2124 tail)
private def e2130 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2129 tail) (e711 tail)
private def c2131 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2130 []).term
private def f2132 : Theorem := Theorem.emptyResult ([].toFinset) c2131
private def r2133 : InferenceRequest := .inst [(k1769, s1278)] f2132
private def e2134 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2118 tail)
private def e2135 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2134 tail) (e711 tail)
private def c2136 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2135 []).term
private def f2137 : Theorem := Theorem.emptyResult ([].toFinset) c2136
private def r2138 : InferenceRequest := .trans f2121 f2137
private def e2139 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2117 tail) (e711 tail)
private def c2140 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2139 []).term
private def f2141 : Theorem := Theorem.emptyResult ([].toFinset) c2140
private def r2142 : InferenceRequest := .trans f1862 f2141
private def e2143 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1816 tail) (e711 tail)
private def c2144 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2143 []).term
private def f2145 : Theorem := Theorem.emptyResult ([].toFinset) c2144
private def r2146 : InferenceRequest := .mkComb f725 f2145
private def e2147 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e1816 tail)
private def e2148 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2147 tail) (e729 tail)
private def c2149 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2148 []).term
private def f2150 : Theorem := Theorem.emptyResult ([].toFinset) c2149
private def c2151 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1815 []).term
private def r2152 : InferenceRequest := .refl c2151
private def e2153 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1816 tail) (e1815 tail)
private def c2154 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2153 []).term
private def f2155 : Theorem := Theorem.emptyResult ([].toFinset) c2154
private def r2156 : InferenceRequest := .mkComb f2150 f2155
private def e2157 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2153 tail)
private def e2158 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e729 tail) (e1815 tail)
private def e2159 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2157 tail) (e2158 tail)
private def c2160 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2159 []).term
private def f2161 : Theorem := Theorem.emptyResult ([].toFinset) c2160
private def r2162 : InferenceRequest := .eqMp f2161 f2155
private def c2163 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2158 []).term
private def f2164 : Theorem := Theorem.emptyResult ([].toFinset) c2163
private def s2165 : SourceTerm := SourceTerm.app s7 s679
private def s2166 : SourceTerm := SourceTerm.app s2165 s679
private def s2167 : SourceTerm := SourceTerm.app s1821 s2166
private def s2168 : SourceTerm := SourceTerm.app s2167 s2166
private def s2169 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t17 s2168
private def s2170 : SourceTerm := SourceTerm.app s2169 s1821
private def e2171 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e237 tail) (e763 tail)
private def c2172 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2171 []).term
private theorem n2173 : s2170.toDB [] = c2172.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2174 : CheckedSourceTerm := ⟨s2170, t1, by rw [← DBTerm.inferType_toDB [] s2170, n2173]; exact c2172.checked.trans (congrArg some v175)⟩
private def r2175 : InferenceRequest := .beta k2174
private def e2176 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2171 tail)
private def e2177 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2176 tail) (e796 tail)
private def c2178 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2177 []).term
private def f2179 : Theorem := Theorem.emptyResult ([].toFinset) c2178
private def r2180 : InferenceRequest := .inst [(k1856, s1821)] f2179
private def e2181 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e1817 tail)
private def e2182 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e1807 tail) (e208 tail)
private def e2183 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2182 tail) (e208 tail)
private def e2184 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2181 tail) (e2183 tail)
private def c2185 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2184 []).term
private def f2186 : Theorem := Theorem.emptyResult ([].toFinset) c2185
private def s2187 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s1278
private def s2188 : SourceTerm := SourceTerm.app s7 s2187
private def s2189 : SourceTerm := SourceTerm.app s2188 s2187
private theorem n2190 : s2189.toDB [] = c776.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2191 : CheckedSourceTerm := ⟨s2189, t1, by rw [← DBTerm.inferType_toDB [] s2189, n2190]; exact c776.checked.trans (congrArg some v175)⟩
private def r2192 : InferenceRequest := .inst [(k2191, s1278)] f1874
private def e2193 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e2182 tail)
private def e2200 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2193 tail) (e209 tail)
private def c2201 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2200 []).term
private def f2202 : Theorem := Theorem.emptyResult ([].toFinset) c2201
private def r2203 : InferenceRequest := .refl c776
private def e2204 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e208 tail)
private def e2205 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2204 tail) (e208 tail)
private def c2206 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2205 []).term
private def f2207 : Theorem := Theorem.emptyResult ([].toFinset) c2206
private def r2208 : InferenceRequest := .mkComb f2202 f2207
private def e2209 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2183 tail)
private def e2210 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e209 tail) (e208 tail)
private def e2211 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2209 tail) (e2210 tail)
private def c2212 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2211 []).term
private def f2213 : Theorem := Theorem.emptyResult ([].toFinset) c2212
private def s2214 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s2166
private def s2215 : SourceTerm := SourceTerm.app s2214 s1278
private def e2216 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e209 tail) (e1309 tail)
private def c2217 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2216 []).term
private theorem n2218 : s2215.toDB [] = c2217.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2219 : CheckedSourceTerm := ⟨s2215, t1, by rw [← DBTerm.inferType_toDB [] s2215, n2218]; exact c2217.checked.trans (congrArg some v175)⟩
private def r2220 : InferenceRequest := .beta k2219
private def e2221 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2216 tail)
private def e2222 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2221 tail) (e208 tail)
private def c2223 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2222 []).term
private def f2224 : Theorem := Theorem.emptyResult ([].toFinset) c2223
private def r2225 : InferenceRequest := .inst [(k2191, s1278)] f2224
private def e2226 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2210 tail)
private def e2227 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2226 tail) (e208 tail)
private def c2228 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2227 []).term
private def f2229 : Theorem := Theorem.emptyResult ([].toFinset) c2228
private def r2230 : InferenceRequest := .trans f2213 f2229
private def e2231 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2209 tail) (e208 tail)
private def c2232 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2231 []).term
private def f2233 : Theorem := Theorem.emptyResult ([].toFinset) c2232
private def r2234 : InferenceRequest := .trans f2186 f2233
private def e2235 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2181 tail) (e208 tail)
private def c2236 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2235 []).term
private def f2237 : Theorem := Theorem.emptyResult ([].toFinset) c2236
private def r2238 : InferenceRequest := .trans f2164 f1820
private def e2239 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e729 tail) (e1817 tail)
private def c2240 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2239 []).term
private def f2241 : Theorem := Theorem.emptyResult ([c1785].toFinset) c2240
private def r2242 : InferenceRequest := .trans f2241 f2237
private def f2243 : Theorem := Theorem.emptyResult ([c1785].toFinset) c780
private def r2244 : InferenceRequest := .mkComb f725 f2243
private def e2245 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e729 tail)
private def e2246 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2245 tail) (e2204 tail)
private def c2247 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2246 []).term
private def f2248 : Theorem := Theorem.emptyResult ([c1785].toFinset) c2247
private def r2249 : InferenceRequest := .refl c747
private def r2250 : InferenceRequest := .mkComb f2248 f759
private def e2251 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e757 tail)
private def e2252 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2204 tail) (e711 tail)
private def e2253 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2251 tail) (e2252 tail)
private def c2254 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2253 []).term
private def f2255 : Theorem := Theorem.emptyResult ([c1785].toFinset) c2254
private def r2256 : InferenceRequest := .eqMp f2255 f759
private def c2257 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2252 []).term
private def f2258 : Theorem := Theorem.emptyResult ([c1785].toFinset) c2257
private def r2259 : InferenceRequest := .eqMp f2258 f777
private def f2260 : Theorem := Theorem.emptyResult ([c1785].toFinset) c747
private def r2261 : InferenceRequest := .deductAntisym f1800 f2260
private def e2262 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1657 tail) (e711 tail)
private def c2263 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2262 []).term
private def f2264 : Theorem := Theorem.emptyResult ([].toFinset) c2263
private def s2265 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", ""] "x") t17
private def s2266 : SourceTerm := SourceTerm.app s2265 s52
private def s2267 : SourceTerm := SourceTerm.app s2266 s49
private def s2268 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t17 s2267
private def s2269 : SourceTerm := SourceTerm.app s22 s2268
private def s2270 : SourceTerm := SourceTerm.app s2265 s13
private def s2271 : SourceTerm := SourceTerm.app s2270 s13
private def s2272 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t17 s2271
private def s2273 : SourceTerm := SourceTerm.app s2269 s2272
private def s2274 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t1 s2273
private def s2275 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s2274
private def s2276 : SourceTerm := SourceTerm.app s2275 s1278
private def s2277 : SourceTerm := SourceTerm.app s2276 s47
private def s2278 : SourceTerm := SourceTerm.app s18 s2277
private def s2279 : SourceTerm := SourceTerm.app s2278 s1278
private def s2280 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s2279
private def s2281 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s2280
private def s2282 : SourceTerm := SourceTerm.app s2281 s1278
private def e2309 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e248 tail) (e1309 tail)
private def c2310 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2309 []).term
private theorem n2311 : s2282.toDB [] = c2310.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2312 : CheckedSourceTerm := ⟨s2282, t4, by rw [← DBTerm.inferType_toDB [] s2282, n2311]; exact c2310.checked.trans (congrArg some v191)⟩
private def r2313 : InferenceRequest := .beta k2312
private def e2314 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e2309 tail)
private def e2336 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e1310 ([h173] ++ tail)) (e205 tail)
private def e2337 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .app (e212 ([h173] ++ tail)) (e2336 tail)
private def e2338 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e2337 tail) (e1309 ([h173] ++ tail))
private def e2339 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e2338 tail) (by decide +kernel)
private def e2340 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2314 tail) (e2339 tail)
private def c2341 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2340 []).term
private def f2342 : Theorem := Theorem.emptyResult ([].toFinset) c2341
private def r2343 : InferenceRequest := .inst [(k1407, s1278)] f2342
private def e2344 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e248 tail) (e711 tail)
private def e2345 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e2344 tail)
private def e2347 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e1409 ([h173] ++ tail)) (e205 tail)
private def e2348 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .app (e212 ([h173] ++ tail)) (e2347 tail)
private def e2349 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e2348 tail) (e711 ([h173] ++ tail))
private def e2350 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e2349 tail) (by decide +kernel)
private def e2351 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2345 tail) (e2350 tail)
private def c2352 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2351 []).term
private def f2353 : Theorem := Theorem.emptyResult ([].toFinset) c2352
private def r2354 : InferenceRequest := .mkComb f2353 f737
private def e2355 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2344 tail) (e686 tail)
private def e2356 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2355 tail)
private def e2357 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2350 tail) (e686 tail)
private def e2358 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2356 tail) (e2357 tail)
private def c2359 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2358 []).term
private def f2360 : Theorem := Theorem.emptyResult ([].toFinset) c2359
private def s2361 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", ""] "x") t17
private def s2362 : SourceTerm := SourceTerm.app s2361 s47
private def s2363 : SourceTerm := SourceTerm.app s2362 s52
private def s2364 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t17 s2363
private def s2365 : SourceTerm := SourceTerm.app s22 s2364
private def s2366 : SourceTerm := SourceTerm.app s2361 s71
private def s2367 : SourceTerm := SourceTerm.app s2366 s71
private def s2368 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t17 s2367
private def s2369 : SourceTerm := SourceTerm.app s2365 s2368
private def s2370 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s2369
private def s2371 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s2370
private def s2372 : SourceTerm := SourceTerm.app s2371 s1828
private def s2373 : SourceTerm := SourceTerm.app s2372 s1278
private def s2374 : SourceTerm := SourceTerm.app s18 s2373
private def s2375 : SourceTerm := SourceTerm.app s2374 s1828
private def s2376 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s2375
private def s2377 : SourceTerm := SourceTerm.app s2376 s1278
private def e2378 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2350 tail) (e1309 tail)
private def c2379 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2378 []).term
private theorem n2380 : s2377.toDB [] = c2379.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2381 : CheckedSourceTerm := ⟨s2377, t1, by rw [← DBTerm.inferType_toDB [] s2377, n2380]; exact c2379.checked.trans (congrArg some v175)⟩
private def r2382 : InferenceRequest := .beta k2381
private def e2383 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2378 tail)
private def e2384 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1409 tail) (e1309 tail)
private def e2385 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2384 tail)
private def e2386 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2385 tail) (e711 tail)
private def e2387 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2383 tail) (e2386 tail)
private def c2388 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2387 []).term
private def f2389 : Theorem := Theorem.emptyResult ([].toFinset) c2388
private def r2390 : InferenceRequest := .inst [(k1769, s1278)] f2389
private def e2391 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2357 tail)
private def e2392 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2391 tail) (e2262 tail)
private def c2393 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2392 []).term
private def f2394 : Theorem := Theorem.emptyResult ([].toFinset) c2393
private def r2395 : InferenceRequest := .trans f2360 f2394
private def e2396 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2356 tail) (e2262 tail)
private def c2397 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2396 []).term
private def f2398 : Theorem := Theorem.emptyResult ([].toFinset) c2397
private def r2399 : InferenceRequest := .mkComb f725 f2398
private def e2400 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e2356 tail)
private def e2401 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2262 tail)
private def e2402 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2400 tail) (e2401 tail)
private def c2403 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2402 []).term
private def f2404 : Theorem := Theorem.emptyResult ([].toFinset) c2403
private def c2405 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2355 []).term
private def r2406 : InferenceRequest := .refl c2405
private def e2407 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2356 tail) (e2355 tail)
private def c2408 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2407 []).term
private def f2409 : Theorem := Theorem.emptyResult ([].toFinset) c2408
private def r2410 : InferenceRequest := .mkComb f2404 f2409
private def e2411 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2407 tail)
private def e2412 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2401 tail) (e2355 tail)
private def e2413 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2411 tail) (e2412 tail)
private def c2414 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2413 []).term
private def f2415 : Theorem := Theorem.emptyResult ([].toFinset) c2414
private def r2416 : InferenceRequest := .eqMp f2415 f2409
private def c2417 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2412 []).term
private def f2418 : Theorem := Theorem.emptyResult ([].toFinset) c2417
private def r2419 : InferenceRequest := .eqMp f2418 f2264
private def f2420 : Theorem := Theorem.emptyResult ([].toFinset) c2405
private def s2421 : SourceTerm := SourceTerm.app s1348 s1278
private def e2422 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e263 tail) (e1309 tail)
private def c2423 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2422 []).term
private theorem n2424 : s2421.toDB [] = c2423.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2425 : CheckedSourceTerm := ⟨s2421, t4, by rw [← DBTerm.inferType_toDB [] s2421, n2424]; exact c2423.checked.trans (congrArg some v191)⟩
private def r2426 : InferenceRequest := .beta k2425
private def e2427 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e2422 tail)
private def e2467 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e2309 ([h173] ++ tail)) (e205 tail)
private def e2468 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .app (e248 ([h173] ++ tail)) (e2467 tail)
private def e2473 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h173 := .app (e2468 ([h173] ++ tail)) (e258 tail)
private def e2474 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .lam (e2473 tail) (by decide +kernel)
private def e2475 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e211 ([h173] ++ tail)) (e2474 tail)
private def e2476 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e2475 tail) (by decide +kernel)
private def e2477 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2427 tail) (e2476 tail)
private def c2478 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2477 []).term
private def f2479 : Theorem := Theorem.emptyResult ([].toFinset) c2478
private def c2480 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e689 []).term
private theorem n2481 : s1350.toDB [] = c2480.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2482 : CheckedSourceTerm := ⟨s1350, t1, by rw [← DBTerm.inferType_toDB [] s1350, n2481]; exact c2480.checked.trans (congrArg some v175)⟩
private def r2483 : InferenceRequest := .inst [(k2482, s1278)] f2479
private def e2484 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e690 tail)
private def e2503 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e248 tail) (e689 tail)
private def e2504 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e2503 ([h173] ++ tail)) (e205 tail)
private def e2505 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .app (e248 ([h173] ++ tail)) (e2504 tail)
private def e2506 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173, h173] ++ tail) h173 := .app (e2505 ([h173] ++ tail)) (e258 tail)
private def e2507 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .lam (e2506 tail) (by decide +kernel)
private def e2508 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e211 ([h173] ++ tail)) (e2507 tail)
private def e2509 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e2508 tail) (by decide +kernel)
private def e2510 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2484 tail) (e2509 tail)
private def c2511 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2510 []).term
private def f2512 : Theorem := Theorem.emptyResult ([].toFinset) c2511
private def c2513 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e710 []).term
private def r2514 : InferenceRequest := .refl c2513
private def e2515 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e710 tail)
private def e2516 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2515 tail) (e710 tail)
private def c2517 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2516 []).term
private def f2518 : Theorem := Theorem.emptyResult ([].toFinset) c2517
private def r2519 : InferenceRequest := .mkComb f2512 f2518
private def e2520 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2509 tail) (e710 tail)
private def e2521 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e729 tail) (e2520 tail)
private def c2522 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2521 []).term
private def f2523 : Theorem := Theorem.emptyResult ([].toFinset) c2522
private def s2524 : SourceTerm := SourceTerm.app s1371 s1675
private def s2525 : SourceTerm := SourceTerm.app s2524 s47
private def s2526 : SourceTerm := SourceTerm.app s1371 s2525
private def s2527 : SourceTerm := SourceTerm.app s1371 s1278
private def s2528 : SourceTerm := SourceTerm.app s2527 s47
private def s2529 : SourceTerm := SourceTerm.app s1371 s2528
private def s2530 : SourceTerm := SourceTerm.app s2529 s47
private def s2531 : SourceTerm := SourceTerm.app s2526 s2530
private def s2532 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s2531
private def s2533 : SourceTerm := SourceTerm.app s678 s2532
private def s2534 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s2533
private def s2535 : SourceTerm := SourceTerm.app s2534 s1278
private def e2536 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2509 tail) (e1309 tail)
private def c2537 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2536 []).term
private theorem n2538 : s2535.toDB [] = c2537.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2539 : CheckedSourceTerm := ⟨s2535, t1, by rw [← DBTerm.inferType_toDB [] s2535, n2538]; exact c2537.checked.trans (congrArg some v175)⟩
private def r2540 : InferenceRequest := .beta k2539
private def e2541 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2536 tail)
private def e2585 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e2468 tail) (e205 tail)
private def e2586 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e2505 tail) (e2585 tail)
private def e2587 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e2586 tail) (by decide +kernel)
private def e2588 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e211 tail) (e2587 tail)
private def e2589 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2541 tail) (e2588 tail)
private def c2590 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2589 []).term
private def f2591 : Theorem := Theorem.emptyResult ([].toFinset) c2590
private theorem n2592 : s1404.toDB [] = c2513.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2593 : CheckedSourceTerm := ⟨s1404, t1, by rw [← DBTerm.inferType_toDB [] s1404, n2592]; exact c2513.checked.trans (congrArg some v175)⟩
private def r2594 : InferenceRequest := .inst [(k2593, s1278)] f2591
private def e2595 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2520 tail)
private def e2596 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e248 tail) (e710 tail)
private def e2597 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e2596 ([h173] ++ tail)) (e205 tail)
private def e2598 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .app (e248 ([h173] ++ tail)) (e2597 tail)
private def e2599 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e2598 tail) (e205 tail)
private def e2600 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e2505 tail) (e2599 tail)
private def e2601 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e2600 tail) (by decide +kernel)
private def e2602 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e211 tail) (e2601 tail)
private def e2603 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2595 tail) (e2602 tail)
private def c2604 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2603 []).term
private def f2605 : Theorem := Theorem.emptyResult ([].toFinset) c2604
private def r2606 : InferenceRequest := .trans f2523 f2605
private def e2607 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e729 tail) (e2602 tail)
private def c2608 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2607 []).term
private def f2609 : Theorem := Theorem.emptyResult ([].toFinset) c2608
private def r2610 : InferenceRequest := .mkComb f725 f2609
private def e2611 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2602 tail)
private def e2612 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2245 tail) (e2611 tail)
private def c2613 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2612 []).term
private def f2614 : Theorem := Theorem.emptyResult ([].toFinset) c2613
private def r2615 : InferenceRequest := .mkComb f2614 f759
private def e2616 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2611 tail) (e711 tail)
private def e2617 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2251 tail) (e2616 tail)
private def c2618 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2617 []).term
private def f2619 : Theorem := Theorem.emptyResult ([].toFinset) c2618
private def r2620 : InferenceRequest := .eqMp f2619 f759
private def c2621 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2616 []).term
private def f2622 : Theorem := Theorem.emptyResult ([].toFinset) c2621
private def c2623 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2602 []).term
private def r2624 : InferenceRequest := .assume c2623
private def f2625 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2623
private def r2626 : InferenceRequest := .deductAntisym f2625 f2622
private def e2627 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2611 tail) (e2616 tail)
private def c2628 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2627 []).term
private def f2629 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2628
private def r2630 : InferenceRequest := .eqMp f2629 f2625
private def f2631 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2621
private def r2632 : InferenceRequest := .deductAntisym f2625 f2625
private def e2633 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2611 tail) (e2602 tail)
private def c2634 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2633 []).term
private def f2635 : Theorem := Theorem.emptyResult ([].toFinset) c2634
private def r2636 : InferenceRequest := .eqMp f2635 f2625
private def r2637 : InferenceRequest := .eqMp f2631 f2625
private def f2638 : Theorem := Theorem.emptyResult ([c2623].toFinset) c747
private def r2639 : InferenceRequest := .deductAntisym f2625 f777
private def e2640 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2611 tail) (e208 tail)
private def c2641 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2640 []).term
private def f2642 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2641
private def r2643 : InferenceRequest := .deductAntisym f2638 f777
private def f2644 : Theorem := Theorem.emptyResult ([c2623].toFinset) c780
private def r2645 : InferenceRequest := .mkComb f769 f2642
private def e2646 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e763 tail) (e2602 tail)
private def e2647 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e2646 tail)
private def e2648 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2647 tail) (e789 tail)
private def c2649 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2648 []).term
private def f2650 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2649
private def r2651 : InferenceRequest := .mkComb f2650 f2644
private def e2652 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2646 tail) (e711 tail)
private def e2653 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2652 tail)
private def e2654 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2653 tail) (e796 tail)
private def c2655 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2654 []).term
private def f2656 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2655
private def r2657 : InferenceRequest := .abs ⟨Name.mk [""] "x", t17⟩ f2656
private def e2884 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h189 := .app (e223 tail) (e2602 ([h192] ++ tail))
private def e2885 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h173 := .app (e2884 tail) (e711 ([h192] ++ tail))
private def e2886 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .lam (e2885 tail) (by decide +kernel)
private def e2887 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h216 := .app (e222 tail) (e2886 tail)
private def e2888 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2887 tail) (e237 tail)
private def c2889 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2888 []).term
private def f2890 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2889
private def s2891 : SourceTerm := SourceTerm.var (Name.mk [""] "x") t4
private def s2892 : SourceTerm := SourceTerm.app s7 s2891
private def s2893 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s1746
private def s2894 : SourceTerm := SourceTerm.app s2892 s2893
private def s2895 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t4 s2894
private def s2896 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", ""] "x") t17
private def s2897 : SourceTerm := SourceTerm.app s2896 s49
private def s2898 : SourceTerm := SourceTerm.app s2897 s40
private def s2899 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t17 s2898
private def s2900 : SourceTerm := SourceTerm.app s22 s2899
private def s2901 : SourceTerm := SourceTerm.app s2896 s124
private def s2902 : SourceTerm := SourceTerm.app s2901 s124
private def s2903 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t17 s2902
private def s2904 : SourceTerm := SourceTerm.app s2900 s2903
private def s2905 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t1 s2904
private def s2906 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t1 s2905
private def s2907 : SourceTerm := SourceTerm.app s2906 s47
private def s2908 : SourceTerm := SourceTerm.app s2907 s52
private def s2909 : SourceTerm := SourceTerm.app s18 s2908
private def s2910 : SourceTerm := SourceTerm.app s2909 s47
private def s2911 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s2910
private def s2912 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s2911
private def s2913 : SourceTerm := SourceTerm.app s2912 s1822
private def s2914 : SourceTerm := SourceTerm.app s2913 s1278
private def s2915 : SourceTerm := SourceTerm.app s2912 s2914
private def s2916 : SourceTerm := SourceTerm.app s2912 s1827
private def s2917 : SourceTerm := SourceTerm.app s2916 s1278
private def s2918 : SourceTerm := SourceTerm.app s2912 s2917
private def s2919 : SourceTerm := SourceTerm.app s2918 s1278
private def s2920 : SourceTerm := SourceTerm.app s2915 s2919
private def s2921 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s2920
private def s2922 : SourceTerm := SourceTerm.app s2895 s2921
private theorem n2923 : s2922.toDB [] = c2623.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2924 : CheckedSourceTerm := ⟨s2922, t1, by rw [← DBTerm.inferType_toDB [] s2922, n2923]; exact c2623.checked.trans (congrArg some v175)⟩
private def r2925 : InferenceRequest := .inst [(k2924, s1278)] f1336
private def e2926 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e240 tail) (e2602 tail)
private def e2927 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e2926 tail)
private def e3155 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192, h173] ++ tail) h173 := .app (e2884 ([h173] ++ tail)) (e226 tail)
private def e3156 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h213 := .lam (e3155 tail) (by decide +kernel)
private def e3157 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h216 := .app (e222 ([h173] ++ tail)) (e3156 tail)
private def e3158 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e3157 tail) (e237 ([h173] ++ tail))
private def e3159 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e3158 tail) (by decide +kernel)
private def e3160 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2927 tail) (e3159 tail)
private def c3161 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3160 []).term
private def f3162 : Theorem := Theorem.emptyResult ([].toFinset) c3161
private def r3163 : InferenceRequest := .mkComb f3162 f759
private def e3164 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2926 tail) (e711 tail)
private def e3165 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3164 tail)
private def e3166 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3159 tail) (e711 tail)
private def e3167 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3165 tail) (e3166 tail)
private def c3168 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3167 []).term
private def f3169 : Theorem := Theorem.emptyResult ([].toFinset) c3168
private def s3170 : SourceTerm := SourceTerm.app s1733 s1732
private def s3171 : SourceTerm := SourceTerm.app s100 s3170
private def s3172 : SourceTerm := SourceTerm.app s3171 s52
private def s3173 : SourceTerm := SourceTerm.app s100 s3172
private def s3174 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", ""] "x") t2
private def s3175 : SourceTerm := SourceTerm.app s102 s3174
private def s3176 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", ""] "x") t0 s1359
private def s3177 : SourceTerm := SourceTerm.app s3175 s3176
private def s3178 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t2 s3177
private def s3179 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", ""] "x") t0
private def s3180 : SourceTerm := SourceTerm.app s103 s3179
private def s3181 : SourceTerm := SourceTerm.app s1718 s3180
private def s3182 : SourceTerm := SourceTerm.app s3181 s40
private def s3183 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t0 s3182
private def s3184 : SourceTerm := SourceTerm.app s3178 s3183
private def s3185 : SourceTerm := SourceTerm.app s148 s3184
private def s3186 : SourceTerm := SourceTerm.app s3185 s40
private def s3187 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t1 s3186
private def s3188 : SourceTerm := SourceTerm.app s127 s3187
private def s3189 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t2 s3188
private def s3190 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", ""] "x") t4
private def s3191 : SourceTerm := SourceTerm.app s7 s3190
private def s3192 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", ""] "x") t1 s88
private def s3193 : SourceTerm := SourceTerm.app s3191 s3192
private def s3194 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", ""] "x") t4 s3193
private def s3195 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", "", "", "", "", "", ""] "x") t17
private def s3196 : SourceTerm := SourceTerm.app s3195 s30
private def s3197 : SourceTerm := SourceTerm.app s3196 s133
private def s3198 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", "", "", ""] "x") t17 s3197
private def s3199 : SourceTerm := SourceTerm.app s22 s3198
private def s3200 : SourceTerm := SourceTerm.var (Name.mk ["", "", "", "", "", "", "", "", "", "", "", "", ""] "x") t1
private def s3201 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", "", "", "", ""] "x") t1 s3200
private def s3202 : SourceTerm := SourceTerm.app s7 s3201
private def s3203 : SourceTerm := SourceTerm.app s3202 s3201
private def s3204 : SourceTerm := SourceTerm.app s3195 s3203
private def s3205 : SourceTerm := SourceTerm.app s3204 s3203
private def s3206 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", "", "", ""] "x") t17 s3205
private def s3207 : SourceTerm := SourceTerm.app s3199 s3206
private def s3208 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", "", ""] "x") t1 s3207
private def s3209 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", "", ""] "x") t1 s3208
private def s3210 : SourceTerm := SourceTerm.app s3209 s26
private def s3211 : SourceTerm := SourceTerm.app s3210 s85
private def s3212 : SourceTerm := SourceTerm.app s18 s3211
private def s3213 : SourceTerm := SourceTerm.app s3212 s26
private def s3214 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", "", ""] "x") t1 s3213
private def s3215 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", "", ""] "x") t1 s3214
private def s3216 : SourceTerm := SourceTerm.app s3215 s40
private def s3217 : SourceTerm := SourceTerm.app s3215 s10
private def s3218 : SourceTerm := SourceTerm.app s3217 s24
private def s3219 : SourceTerm := SourceTerm.app s3216 s3218
private def s3220 : SourceTerm := SourceTerm.app s3215 s3219
private def s3221 : SourceTerm := SourceTerm.app s3220 s24
private def s3222 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", "", ""] "x") t1 s3221
private def s3223 : SourceTerm := SourceTerm.app s3194 s3222
private def s3224 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", "", ""] "x") t1 s3223
private def s3225 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t1 s3224
private def s3226 : SourceTerm := SourceTerm.app s159 s109
private def s3227 : SourceTerm := SourceTerm.app s3225 s3226
private def s3228 : SourceTerm := SourceTerm.app s1697 s11
private def s3229 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t2 s3228
private def s3230 : SourceTerm := SourceTerm.app s64 s3229
private def s3231 : SourceTerm := SourceTerm.app s1677 s109
private def s3232 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", "", ""] "x") t2 s3231
private def s3233 : SourceTerm := SourceTerm.app s3230 s3232
private def s3234 : SourceTerm := SourceTerm.app s3227 s3233
private def s3235 : SourceTerm := SourceTerm.abs (Name.mk ["", "", "", ""] "x") t0 s3234
private def s3236 : SourceTerm := SourceTerm.app s3189 s3235
private def s3237 : SourceTerm := SourceTerm.app s100 s3236
private def s3238 : SourceTerm := SourceTerm.app s3237 s52
private def s3239 : SourceTerm := SourceTerm.app s100 s3238
private def s3240 : SourceTerm := SourceTerm.app s3239 s52
private def s3241 : SourceTerm := SourceTerm.app s3173 s3240
private def s3242 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t1 s3241
private def s3243 : SourceTerm := SourceTerm.app s74 s3242
private def s3244 : SourceTerm := SourceTerm.app s1662 s3243
private def s3245 : SourceTerm := SourceTerm.app s3244 s1278
private def s3246 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t17 s3245
private def s3247 : SourceTerm := SourceTerm.app s22 s3246
private def s3248 : SourceTerm := SourceTerm.app s3247 s1749
private def s3249 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s3248
private def s3250 : SourceTerm := SourceTerm.app s3249 s1278
private def e3251 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3159 tail) (e1309 tail)
private def c3252 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3251 []).term
private theorem n3253 : s3250.toDB [] = c3252.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3254 : CheckedSourceTerm := ⟨s3250, t1, by rw [← DBTerm.inferType_toDB [] s3250, n3253]; exact c3252.checked.trans (congrArg some v175)⟩
private def r3255 : InferenceRequest := .beta k3254
private def e3256 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3251 tail)
private def e3257 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h173 := .app (e2884 tail) (e1309 ([h192] ++ tail))
private def e3258 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .lam (e3257 tail) (by decide +kernel)
private def e3259 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h216 := .app (e222 tail) (e3258 tail)
private def e3260 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3259 tail) (e237 tail)
private def e3261 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3256 tail) (e3260 tail)
private def c3262 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3261 []).term
private def f3263 : Theorem := Theorem.emptyResult ([].toFinset) c3262
private def r3264 : InferenceRequest := .inst [(k1407, s1278)] f3263
private def e3265 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3166 tail)
private def e3266 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3265 tail) (e2888 tail)
private def c3267 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3266 []).term
private def f3268 : Theorem := Theorem.emptyResult ([].toFinset) c3267
private def r3269 : InferenceRequest := .trans f3169 f3268
private def e3270 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3165 tail) (e2888 tail)
private def c3271 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3270 []).term
private def f3272 : Theorem := Theorem.emptyResult ([].toFinset) c3271
private def r3273 : InferenceRequest := .mkComb f725 f3272
private def e3274 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3165 tail)
private def e3275 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2888 tail)
private def e3276 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3274 tail) (e3275 tail)
private def c3277 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3276 []).term
private def f3278 : Theorem := Theorem.emptyResult ([].toFinset) c3277
private def c3279 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3164 []).term
private def r3280 : InferenceRequest := .refl c3279
private def e3281 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3165 tail) (e3164 tail)
private def c3282 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3281 []).term
private def f3283 : Theorem := Theorem.emptyResult ([].toFinset) c3282
private def r3284 : InferenceRequest := .mkComb f3278 f3283
private def e3285 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3281 tail)
private def e3286 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3275 tail) (e3164 tail)
private def e3287 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3285 tail) (e3286 tail)
private def c3288 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3287 []).term
private def f3289 : Theorem := Theorem.emptyResult ([].toFinset) c3288
private def r3290 : InferenceRequest := .eqMp f3289 f3283
private def c3291 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3286 []).term
private def f3292 : Theorem := Theorem.emptyResult ([].toFinset) c3291
private def r3293 : InferenceRequest := .eqMp f3292 f2890
private def f3294 : Theorem := Theorem.emptyResult ([c2623].toFinset) c3279
private def r3295 : InferenceRequest := .assume c3279
private def f3296 : Theorem := Theorem.emptyResult ([c3279].toFinset) c3279
private def r3297 : InferenceRequest := .eqMp f3272 f3296
private def f3298 : Theorem := Theorem.emptyResult ([c3279].toFinset) c2889
private def r3299 : InferenceRequest := .mkComb f3298 f1813
private def e3300 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2886 tail) (e1807 tail)
private def e3301 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3300 tail)
private def e3302 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3301 tail) (e1817 tail)
private def c3303 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3302 []).term
private def f3304 : Theorem := Theorem.emptyResult ([c3279].toFinset) c3303
private def s3305 : SourceTerm := SourceTerm.app s1371 s1739
private def s3306 : SourceTerm := SourceTerm.app s3305 s47
private def s3307 : SourceTerm := SourceTerm.app s1371 s3306
private def s3308 : SourceTerm := SourceTerm.app s3307 s47
private def s3309 : SourceTerm := SourceTerm.app s2526 s3308
private def s3310 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s3309
private def s3311 : SourceTerm := SourceTerm.app s678 s3310
private def s3312 : SourceTerm := SourceTerm.app s1821 s3311
private def s3313 : SourceTerm := SourceTerm.app s3312 s1828
private def s3314 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t17 s3313
private def s3315 : SourceTerm := SourceTerm.app s3314 s1821
private def e3316 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2886 tail) (e763 tail)
private def c3317 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3316 []).term
private theorem n3318 : s3315.toDB [] = c3317.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3319 : CheckedSourceTerm := ⟨s3315, t1, by rw [← DBTerm.inferType_toDB [] s3315, n3318]; exact c3317.checked.trans (congrArg some v175)⟩
private def r3320 : InferenceRequest := .beta k3319
private def e3321 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3316 tail)
private def e3322 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3321 tail) (e2652 tail)
private def c3323 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3322 []).term
private def f3324 : Theorem := Theorem.emptyResult ([].toFinset) c3323
private def r3325 : InferenceRequest := .inst [(k1856, s1821)] f3324
private def e3326 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e1807 tail) (e2602 tail)
private def e3327 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3326 tail) (e711 tail)
private def e3328 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3301 tail) (e3327 tail)
private def c3329 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3328 []).term
private def f3330 : Theorem := Theorem.emptyResult ([].toFinset) c3329
private def r3331 : InferenceRequest := .inst [(k2924, s1278)] f1874
private def e3332 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3326 tail)
private def e3501 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e2602 ([h173] ++ tail)) (by decide +kernel)
private def e3502 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3332 tail) (e3501 tail)
private def c3503 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3502 []).term
private def f3504 : Theorem := Theorem.emptyResult ([].toFinset) c3503
private def r3505 : InferenceRequest := .mkComb f3504 f759
private def e3506 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3327 tail)
private def e3507 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3501 tail) (e711 tail)
private def e3508 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3506 tail) (e3507 tail)
private def c3509 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3508 []).term
private def f3510 : Theorem := Theorem.emptyResult ([].toFinset) c3509
private def s3511 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s3311
private def s3512 : SourceTerm := SourceTerm.app s3511 s1278
private def e3513 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3501 tail) (e1309 tail)
private def c3514 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3513 []).term
private theorem n3515 : s3512.toDB [] = c3514.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3516 : CheckedSourceTerm := ⟨s3512, t1, by rw [← DBTerm.inferType_toDB [] s3512, n3515]; exact c3514.checked.trans (congrArg some v175)⟩
private def r3517 : InferenceRequest := .beta k3516
private def e3518 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3513 tail)
private def e3519 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3518 tail) (e2602 tail)
private def c3520 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3519 []).term
private def f3521 : Theorem := Theorem.emptyResult ([].toFinset) c3520
private def r3522 : InferenceRequest := .inst [(k1407, s1278)] f3521
private def e3523 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3507 tail)
private def e3524 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3523 tail) (e2602 tail)
private def c3525 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3524 []).term
private def f3526 : Theorem := Theorem.emptyResult ([].toFinset) c3525
private def r3527 : InferenceRequest := .trans f3510 f3526
private def e3528 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3506 tail) (e2602 tail)
private def c3529 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3528 []).term
private def f3530 : Theorem := Theorem.emptyResult ([].toFinset) c3529
private def r3531 : InferenceRequest := .trans f3330 f3530
private def e3532 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3301 tail) (e2602 tail)
private def c3533 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3532 []).term
private def f3534 : Theorem := Theorem.emptyResult ([].toFinset) c3533
private def r3535 : InferenceRequest := .mkComb f725 f3534
private def e3536 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3301 tail)
private def e3537 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3536 tail) (e2611 tail)
private def c3538 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3537 []).term
private def f3539 : Theorem := Theorem.emptyResult ([].toFinset) c3538
private def c3540 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3300 []).term
private def r3541 : InferenceRequest := .refl c3540
private def e3542 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3301 tail) (e3300 tail)
private def c3543 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3542 []).term
private def f3544 : Theorem := Theorem.emptyResult ([].toFinset) c3543
private def r3545 : InferenceRequest := .mkComb f3539 f3544
private def e3546 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3542 tail)
private def e3547 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2611 tail) (e3300 tail)
private def e3548 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3546 tail) (e3547 tail)
private def c3549 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3548 []).term
private def f3550 : Theorem := Theorem.emptyResult ([].toFinset) c3549
private def r3551 : InferenceRequest := .eqMp f3550 f3544
private def c3552 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3547 []).term
private def f3553 : Theorem := Theorem.emptyResult ([].toFinset) c3552
private def r3554 : InferenceRequest := .trans f3553 f3304
private def e3555 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2611 tail) (e1817 tail)
private def c3556 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3555 []).term
private def f3557 : Theorem := Theorem.emptyResult ([c3279].toFinset) c3556
private def r3558 : InferenceRequest := .trans f3557 f2237
private def f3559 : Theorem := Theorem.emptyResult ([c3279].toFinset) c2641
private def r3560 : InferenceRequest := .mkComb f725 f3559
private def e3561 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e2611 tail)
private def e3562 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3561 tail) (e2204 tail)
private def c3563 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3562 []).term
private def f3564 : Theorem := Theorem.emptyResult ([c3279].toFinset) c3563
private def r3565 : InferenceRequest := .refl c2623
private def r3566 : InferenceRequest := .mkComb f3564 f2635
private def e3567 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e2633 tail)
private def e3568 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2204 tail) (e2602 tail)
private def e3569 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3567 tail) (e3568 tail)
private def c3570 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3569 []).term
private def f3571 : Theorem := Theorem.emptyResult ([c3279].toFinset) c3570
private def r3572 : InferenceRequest := .eqMp f3571 f2635
private def c3573 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3568 []).term
private def f3574 : Theorem := Theorem.emptyResult ([c3279].toFinset) c3573
private def r3575 : InferenceRequest := .eqMp f3574 f777
private def f3576 : Theorem := Theorem.emptyResult ([c3279].toFinset) c2623
private def r3577 : InferenceRequest := .deductAntisym f3294 f3576
private def e3578 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3165 tail) (e2602 tail)
private def c3579 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3578 []).term
private def f3580 : Theorem := Theorem.emptyResult ([].toFinset) c3579
private def r3581 : InferenceRequest := .inst [(k2924, s1278)] f2342
private def e3582 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e248 tail) (e2602 tail)
private def e3583 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3582 tail)
private def e3585 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e2926 ([h173] ++ tail)) (e205 tail)
private def e3586 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .app (e212 ([h173] ++ tail)) (e3585 tail)
private def e3587 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e3586 tail) (e2602 ([h173] ++ tail))
private def e3588 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e3587 tail) (by decide +kernel)
private def e3589 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3583 tail) (e3588 tail)
private def c3590 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3589 []).term
private def f3591 : Theorem := Theorem.emptyResult ([].toFinset) c3590
private def r3592 : InferenceRequest := .mkComb f3591 f759
private def e3593 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3582 tail) (e711 tail)
private def e3594 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3593 tail)
private def e3595 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3588 tail) (e711 tail)
private def e3596 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3594 tail) (e3595 tail)
private def c3597 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3596 []).term
private def f3598 : Theorem := Theorem.emptyResult ([].toFinset) c3597
private def s3599 : SourceTerm := SourceTerm.app s2371 s3311
private def s3600 : SourceTerm := SourceTerm.app s3599 s1278
private def s3601 : SourceTerm := SourceTerm.app s18 s3600
private def s3602 : SourceTerm := SourceTerm.app s3601 s3311
private def s3603 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s3602
private def s3604 : SourceTerm := SourceTerm.app s3603 s1278
private def e3605 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3588 tail) (e1309 tail)
private def c3606 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3605 []).term
private theorem n3607 : s3604.toDB [] = c3606.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3608 : CheckedSourceTerm := ⟨s3604, t1, by rw [← DBTerm.inferType_toDB [] s3604, n3607]; exact c3606.checked.trans (congrArg some v175)⟩
private def r3609 : InferenceRequest := .beta k3608
private def e3610 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3605 tail)
private def e3611 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2926 tail) (e1309 tail)
private def e3612 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3611 tail)
private def e3613 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3612 tail) (e2602 tail)
private def e3614 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3610 tail) (e3613 tail)
private def c3615 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3614 []).term
private def f3616 : Theorem := Theorem.emptyResult ([].toFinset) c3615
private def r3617 : InferenceRequest := .inst [(k1407, s1278)] f3616
private def e3618 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3595 tail)
private def e3619 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3618 tail) (e3578 tail)
private def c3620 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3619 []).term
private def f3621 : Theorem := Theorem.emptyResult ([].toFinset) c3620
private def r3622 : InferenceRequest := .trans f3598 f3621
private def e3623 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3594 tail) (e3578 tail)
private def c3624 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3623 []).term
private def f3625 : Theorem := Theorem.emptyResult ([].toFinset) c3624
private def r3626 : InferenceRequest := .mkComb f725 f3625
private def e3627 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3594 tail)
private def e3628 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3578 tail)
private def e3629 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3627 tail) (e3628 tail)
private def c3630 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3629 []).term
private def f3631 : Theorem := Theorem.emptyResult ([].toFinset) c3630
private def c3632 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3593 []).term
private def r3633 : InferenceRequest := .refl c3632
private def e3634 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3594 tail) (e3593 tail)
private def c3635 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3634 []).term
private def f3636 : Theorem := Theorem.emptyResult ([].toFinset) c3635
private def r3637 : InferenceRequest := .mkComb f3631 f3636
private def e3638 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3634 tail)
private def e3639 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3628 tail) (e3593 tail)
private def e3640 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3638 tail) (e3639 tail)
private def c3641 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3640 []).term
private def f3642 : Theorem := Theorem.emptyResult ([].toFinset) c3641
private def r3643 : InferenceRequest := .eqMp f3642 f3636
private def c3644 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3639 []).term
private def f3645 : Theorem := Theorem.emptyResult ([].toFinset) c3644
private def r3646 : InferenceRequest := .eqMp f3645 f3580
private def f3647 : Theorem := Theorem.emptyResult ([].toFinset) c3632
private def e3649 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2503 tail) (e1309 tail)
private def c3650 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3649 []).term
private def r3651 : InferenceRequest := .assume c3650
private def f3652 : Theorem := Theorem.emptyResult ([c3650].toFinset) c3650
private def e3654 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2596 tail) (e1309 tail)
private def c3655 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3654 []).term
private def r3656 : InferenceRequest := .assume c3655
private def f3657 : Theorem := Theorem.emptyResult ([c3655].toFinset) c3655
private def r3658 : InferenceRequest := .deductAntisym f3657 f3652
private def e3659 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3654 tail)
private def e3660 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3659 tail) (e3649 tail)
private def c3661 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3660 []).term
private def f3662 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3661
private def r3663 : InferenceRequest := .eqMp f3662 f3657
private def f3664 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3650
private def r3665 : InferenceRequest := .deductAntisym f3652 f3664
private def e3666 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3649 tail)
private def e3667 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3666 tail) (e3649 tail)
private def c3668 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3667 []).term
private def f3669 : Theorem := Theorem.emptyResult ([c3655].toFinset) c3668
private def r3670 : InferenceRequest := .eqMp f3669 f3652
private def r3671 : InferenceRequest := .refl c682
private def f3672 : Theorem := Theorem.emptyResult ([].toFinset) c2480
private def r3673 : InferenceRequest := .deductAntisym f3657 f3672
private def e3674 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3659 tail) (e689 tail)
private def c3675 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3674 []).term
private def f3676 : Theorem := Theorem.emptyResult ([c3655].toFinset) c3675
private def r3677 : InferenceRequest := .eqMp f3676 f3657
private def f3678 : Theorem := Theorem.emptyResult ([c3655].toFinset) c2480
private def r3679 : InferenceRequest := .deductAntisym f3652 f3678
private def e3680 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3666 tail) (e689 tail)
private def c3681 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3680 []).term
private def f3682 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3681
private def r3683 : InferenceRequest := .eqMp f3682 f3652
private def f3684 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c2480
private def r3685 : InferenceRequest := .inst [(k2482, s1278)] f2342
private def e3686 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e2503 tail)
private def e3687 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e240 tail) (e689 tail)
private def e3688 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e3687 ([h173] ++ tail)) (e205 tail)
private def e3689 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .app (e212 ([h173] ++ tail)) (e3688 tail)
private def e3690 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e3689 tail) (e689 ([h173] ++ tail))
private def e3691 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e3690 tail) (by decide +kernel)
private def e3692 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3686 tail) (e3691 tail)
private def c3693 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3692 []).term
private def f3694 : Theorem := Theorem.emptyResult ([].toFinset) c3693
private def c3695 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e1309 []).term
private def r3696 : InferenceRequest := .refl c3695
private def e3697 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e1309 tail)
private def e3698 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3697 tail) (e1309 tail)
private def c3699 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3698 []).term
private def f3700 : Theorem := Theorem.emptyResult ([].toFinset) c3699
private def r3701 : InferenceRequest := .mkComb f3694 f3700
private def e3702 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3691 tail) (e1309 tail)
private def e3703 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3666 tail) (e3702 tail)
private def c3704 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3703 []).term
private def f3705 : Theorem := Theorem.emptyResult ([].toFinset) c3704
private def s3706 : SourceTerm := SourceTerm.app s2371 s1822
private def s3707 : SourceTerm := SourceTerm.app s3706 s1278
private def s3708 : SourceTerm := SourceTerm.app s18 s3707
private def s3709 : SourceTerm := SourceTerm.app s3708 s1822
private def s3710 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s3709
private def s3711 : SourceTerm := SourceTerm.app s3710 s1278
private def c3712 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3702 []).term
private theorem n3713 : s3711.toDB [] = c3712.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3714 : CheckedSourceTerm := ⟨s3711, t1, by rw [← DBTerm.inferType_toDB [] s3711, n3713]; exact c3712.checked.trans (congrArg some v175)⟩
private def r3715 : InferenceRequest := .beta k3714
private def e3716 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3702 tail)
private def e3718 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3687 tail) (e1309 tail)
private def e3719 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3718 tail)
private def e3720 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3719 tail) (e689 tail)
private def e3721 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3716 tail) (e3720 tail)
private def c3722 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3721 []).term
private def f3723 : Theorem := Theorem.emptyResult ([].toFinset) c3722
private theorem n3724 : s1278.toDB [] = c3695.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3725 : CheckedSourceTerm := ⟨s1278, t1, by rw [← DBTerm.inferType_toDB [] s1278, n3724]; exact c3695.checked.trans (congrArg some v175)⟩
private def r3726 : InferenceRequest := .inst [(k3725, s1278)] f3723
private def r3727 : InferenceRequest := .trans f3705 f3723
private def e3728 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3666 tail) (e3720 tail)
private def c3729 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3728 []).term
private def f3730 : Theorem := Theorem.emptyResult ([].toFinset) c3729
private def r3731 : InferenceRequest := .eqMp f3730 f3664
private def c3732 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3720 []).term
private def f3733 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3732
private def r3734 : InferenceRequest := .mkComb f725 f3733
private def e3735 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3719 tail)
private def e3736 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e689 tail)
private def e3737 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3735 tail) (e3736 tail)
private def c3738 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3737 []).term
private def f3739 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3738
private def c3740 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3718 []).term
private def r3741 : InferenceRequest := .refl c3740
private def e3742 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3719 tail) (e3718 tail)
private def c3743 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3742 []).term
private def f3744 : Theorem := Theorem.emptyResult ([].toFinset) c3743
private def r3745 : InferenceRequest := .mkComb f3739 f3744
private def e3746 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3742 tail)
private def e3747 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3736 tail) (e3718 tail)
private def e3748 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3746 tail) (e3747 tail)
private def c3749 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3748 []).term
private def f3750 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3749
private def r3751 : InferenceRequest := .eqMp f3750 f3744
private def c3752 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3747 []).term
private def f3753 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3752
private def r3754 : InferenceRequest := .eqMp f3753 f3684
private def f3755 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3740
private def r3756 : InferenceRequest := .inst [(k2482, s1278)] f1336
private def e3757 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3687 tail)
private def e3758 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h189 := .app (e223 tail) (e689 ([h192] ++ tail))
private def e3759 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192, h173] ++ tail) h173 := .app (e3758 ([h173] ++ tail)) (e226 tail)
private def e3760 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h213 := .lam (e3759 tail) (by decide +kernel)
private def e3761 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h216 := .app (e222 ([h173] ++ tail)) (e3760 tail)
private def e3762 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e3761 tail) (e237 ([h173] ++ tail))
private def e3763 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e3762 tail) (by decide +kernel)
private def e3764 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3757 tail) (e3763 tail)
private def c3765 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3764 []).term
private def f3766 : Theorem := Theorem.emptyResult ([].toFinset) c3765
private def r3767 : InferenceRequest := .mkComb f3766 f3700
private def e3768 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3763 tail) (e1309 tail)
private def e3769 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3719 tail) (e3768 tail)
private def c3770 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3769 []).term
private def f3771 : Theorem := Theorem.emptyResult ([].toFinset) c3770
private def s3772 : SourceTerm := SourceTerm.app s1662 s1675
private def s3773 : SourceTerm := SourceTerm.app s3772 s1278
private def s3774 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t17 s3773
private def s3775 : SourceTerm := SourceTerm.app s22 s3774
private def s3776 : SourceTerm := SourceTerm.app s3775 s1749
private def s3777 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s3776
private def s3778 : SourceTerm := SourceTerm.app s3777 s1278
private def c3779 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3768 []).term
private theorem n3780 : s3778.toDB [] = c3779.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3781 : CheckedSourceTerm := ⟨s3778, t1, by rw [← DBTerm.inferType_toDB [] s3778, n3780]; exact c3779.checked.trans (congrArg some v175)⟩
private def r3782 : InferenceRequest := .beta k3781
private def e3783 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3768 tail)
private def e3785 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h173 := .app (e3758 tail) (e1309 ([h192] ++ tail))
private def e3786 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .lam (e3785 tail) (by decide +kernel)
private def e3787 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h216 := .app (e222 tail) (e3786 tail)
private def e3788 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3787 tail) (e237 tail)
private def e3789 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3783 tail) (e3788 tail)
private def c3790 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3789 []).term
private def f3791 : Theorem := Theorem.emptyResult ([].toFinset) c3790
private def r3792 : InferenceRequest := .inst [(k3725, s1278)] f3791
private def r3793 : InferenceRequest := .trans f3771 f3791
private def e3794 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3719 tail) (e3788 tail)
private def c3795 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3794 []).term
private def f3796 : Theorem := Theorem.emptyResult ([].toFinset) c3795
private def r3797 : InferenceRequest := .eqMp f3796 f3755
private def c3798 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3788 []).term
private def f3799 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3798
private def e3800 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h192 := .lam (e206 ([h173] ++ tail)) (by decide +kernel)
private def c3801 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3800 []).term
private def r3802 : InferenceRequest := .refl c3801
private def e3803 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .app (e721 tail) (e3800 tail)
private def e3804 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3803 tail) (e3800 tail)
private def c3805 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3804 []).term
private def f3806 : Theorem := Theorem.emptyResult ([].toFinset) c3805
private def r3807 : InferenceRequest := .mkComb f3799 f3806
private def e3808 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3786 tail) (e3800 tail)
private def e3809 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3808 tail)
private def e3810 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e237 tail) (e3800 tail)
private def e3811 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3809 tail) (e3810 tail)
private def c3812 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3811 []).term
private def f3813 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3812
private def s3814 : SourceTerm := SourceTerm.app s3774 s1662
private def e3815 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h192 := .const (.variable ⟨Name.mk ["", ""] "x", t17⟩ q193) (by decide +kernel)
private def e3816 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3786 tail) (e3815 tail)
private def c3817 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3816 []).term
private theorem n3818 : s3814.toDB [] = c3817.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3819 : CheckedSourceTerm := ⟨s3814, t1, by rw [← DBTerm.inferType_toDB [] s3814, n3818]; exact c3817.checked.trans (congrArg some v175)⟩
private def r3820 : InferenceRequest := .beta k3819
private def e3821 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3816 tail)
private def e3822 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e3815 tail) (e689 tail)
private def e3823 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3822 tail) (e1309 tail)
private def e3824 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3821 tail) (e3823 tail)
private def c3825 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3824 []).term
private def f3826 : Theorem := Theorem.emptyResult ([].toFinset) c3825
private def s3827 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s679
private theorem n3828 : s3827.toDB [] = c3801.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3829 : CheckedSourceTerm := ⟨s3827, t17, by rw [← DBTerm.inferType_toDB [] s3827, n3828]; exact c3801.checked.trans (congrArg some v194)⟩
private def r3830 : InferenceRequest := .inst [(k3829, s1662)] f3826
private def e3831 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e3800 tail) (e689 tail)
private def e3832 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3831 tail) (e1309 tail)
private def e3833 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3809 tail) (e3832 tail)
private def c3834 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3833 []).term
private def f3835 : Theorem := Theorem.emptyResult ([].toFinset) c3834
private def s3836 : SourceTerm := SourceTerm.app s3827 s1278
private def e3837 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e3800 tail) (e1309 tail)
private def c3838 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3837 []).term
private theorem n3839 : s3836.toDB [] = c3838.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3840 : CheckedSourceTerm := ⟨s3836, t4, by rw [← DBTerm.inferType_toDB [] s3836, n3839]; exact c3838.checked.trans (congrArg some v191)⟩
private def r3841 : InferenceRequest := .beta k3840
private def e3842 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3837 tail)
private def e3843 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3842 tail) (e206 tail)
private def c3844 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3843 []).term
private def f3845 : Theorem := Theorem.emptyResult ([].toFinset) c3844
private def r3846 : InferenceRequest := .inst [(k2482, s1278)] f3845
private def e3847 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3831 tail)
private def e3848 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3847 tail) (e206 tail)
private def c3849 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3848 []).term
private def f3850 : Theorem := Theorem.emptyResult ([].toFinset) c3849
private def r3851 : InferenceRequest := .mkComb f3850 f3700
private def e3852 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3832 tail)
private def e3853 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e206 tail) (e1309 tail)
private def e3854 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3852 tail) (e3853 tail)
private def c3855 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3854 []).term
private def f3856 : Theorem := Theorem.emptyResult ([].toFinset) c3855
private def s3857 : SourceTerm := SourceTerm.app s2187 s1278
private def c3858 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3853 []).term
private theorem n3859 : s3857.toDB [] = c3858.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3860 : CheckedSourceTerm := ⟨s3857, t1, by rw [← DBTerm.inferType_toDB [] s3857, n3859]; exact c3858.checked.trans (congrArg some v175)⟩
private def r3861 : InferenceRequest := .beta k3860
private def e3862 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3853 tail)
private def e3863 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3862 tail) (e1309 tail)
private def c3864 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3863 []).term
private def f3865 : Theorem := Theorem.emptyResult ([].toFinset) c3864
private def r3866 : InferenceRequest := .inst [(k3725, s1278)] f3865
private def r3867 : InferenceRequest := .trans f3856 f3865
private def e3868 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3852 tail) (e1309 tail)
private def c3869 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3868 []).term
private def f3870 : Theorem := Theorem.emptyResult ([].toFinset) c3869
private def r3871 : InferenceRequest := .trans f3835 f3870
private def e3872 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3809 tail) (e1309 tail)
private def c3873 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3872 []).term
private def f3874 : Theorem := Theorem.emptyResult ([].toFinset) c3873
private def r3875 : InferenceRequest := .mkComb f725 f3874
private def e3876 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3809 tail)
private def e3877 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3876 tail) (e3697 tail)
private def c3878 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3877 []).term
private def f3879 : Theorem := Theorem.emptyResult ([].toFinset) c3878
private def c3880 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3808 []).term
private def r3881 : InferenceRequest := .refl c3880
private def e3882 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3809 tail) (e3808 tail)
private def c3883 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3882 []).term
private def f3884 : Theorem := Theorem.emptyResult ([].toFinset) c3883
private def r3885 : InferenceRequest := .mkComb f3879 f3884
private def e3886 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3882 tail)
private def e3887 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3697 tail) (e3808 tail)
private def e3888 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3886 tail) (e3887 tail)
private def c3889 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3888 []).term
private def f3890 : Theorem := Theorem.emptyResult ([].toFinset) c3889
private def r3891 : InferenceRequest := .eqMp f3890 f3884
private def c3892 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3887 []).term
private def f3893 : Theorem := Theorem.emptyResult ([].toFinset) c3892
private def r3894 : InferenceRequest := .inst [(k3829, s1821)] f2179
private def e3895 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3810 tail)
private def e3896 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e3800 tail) (e208 tail)
private def e3897 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3896 tail) (e208 tail)
private def e3898 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3895 tail) (e3897 tail)
private def c3899 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3898 []).term
private def f3900 : Theorem := Theorem.emptyResult ([].toFinset) c3899
private def r3901 : InferenceRequest := .inst [(k2191, s1278)] f3845
private def e3902 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3896 tail)
private def e3903 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3902 tail) (e206 tail)
private def c3904 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3903 []).term
private def f3905 : Theorem := Theorem.emptyResult ([].toFinset) c3904
private def r3906 : InferenceRequest := .mkComb f3905 f2207
private def e3907 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3897 tail)
private def e3908 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e206 tail) (e208 tail)
private def e3909 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3907 tail) (e3908 tail)
private def c3910 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3909 []).term
private def f3911 : Theorem := Theorem.emptyResult ([].toFinset) c3910
private def r3912 : InferenceRequest := .inst [(k2191, s1278)] f3865
private def e3913 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3908 tail)
private def e3914 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3913 tail) (e208 tail)
private def c3915 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3914 []).term
private def f3916 : Theorem := Theorem.emptyResult ([].toFinset) c3915
private def r3917 : InferenceRequest := .trans f3911 f3916
private def e3918 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3907 tail) (e208 tail)
private def c3919 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3918 []).term
private def f3920 : Theorem := Theorem.emptyResult ([].toFinset) c3919
private def r3921 : InferenceRequest := .trans f3900 f3920
private def e3922 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3895 tail) (e208 tail)
private def c3923 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3922 []).term
private def f3924 : Theorem := Theorem.emptyResult ([].toFinset) c3923
private def r3925 : InferenceRequest := .trans f3893 f3813
private def e3926 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3697 tail) (e3810 tail)
private def c3927 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3926 []).term
private def f3928 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3927
private def r3929 : InferenceRequest := .trans f3928 f3924
private def e3930 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3697 tail) (e208 tail)
private def c3931 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3930 []).term
private def f3932 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3931
private def r3933 : InferenceRequest := .mkComb f725 f3932
private def e3934 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3697 tail)
private def e3935 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3934 tail) (e2204 tail)
private def c3936 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3935 []).term
private def f3937 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3936
private def r3938 : InferenceRequest := .mkComb f3937 f3700
private def e3939 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3698 tail)
private def e3940 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2204 tail) (e1309 tail)
private def e3941 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3939 tail) (e3940 tail)
private def c3942 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3941 []).term
private def f3943 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3942
private def r3944 : InferenceRequest := .eqMp f3943 f3700
private def c3945 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3940 []).term
private def f3946 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3945
private def r3947 : InferenceRequest := .eqMp f3946 f777
private def f3948 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3695
private def r3949 : InferenceRequest := .deductAntisym f3657 f3948
private def e3950 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3659 tail) (e1309 tail)
private def c3951 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3950 []).term
private def f3952 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3951
private def r3953 : InferenceRequest := .eqMp f3952 f3657
private def r3954 : InferenceRequest := .deductAntisym f3652 f3948
private def e3955 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3666 tail) (e1309 tail)
private def c3956 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3955 []).term
private def f3957 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3956
private def r3958 : InferenceRequest := .eqMp f3957 f3652
private def c3959 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3815 []).term
private def r3960 : InferenceRequest := .refl c3959
private def e3961 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .app (e721 tail) (e3815 tail)
private def e3962 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3961 tail) (e3815 tail)
private def c3963 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3962 []).term
private def f3964 : Theorem := Theorem.emptyResult ([].toFinset) c3963
private def r3965 : InferenceRequest := .deductAntisym f3657 f777
private def e3966 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3659 tail) (e208 tail)
private def c3967 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3966 []).term
private def f3968 : Theorem := Theorem.emptyResult ([c3655].toFinset) c3967
private def r3969 : InferenceRequest := .deductAntisym f3948 f777
private def r3970 : InferenceRequest := .mkComb f3964 f3968
private def e3971 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e3815 tail) (e3654 tail)
private def e3972 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3971 tail)
private def e3973 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e3815 tail) (e208 tail)
private def e3974 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3972 tail) (e3973 tail)
private def c3975 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3974 []).term
private def f3976 : Theorem := Theorem.emptyResult ([c3655].toFinset) c3975
private def r3977 : InferenceRequest := .mkComb f3976 f3932
private def e3978 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3971 tail) (e1309 tail)
private def e3979 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3978 tail)
private def e3980 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3973 tail) (e208 tail)
private def e3981 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3979 tail) (e3980 tail)
private def c3982 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e3981 []).term
private def f3983 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3982
private def r3984 : InferenceRequest := .abs ⟨Name.mk ["", ""] "x", t17⟩ f3983
private def e4015 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h189 := .app (e223 tail) (e3654 ([h192] ++ tail))
private def e4016 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h173 := .app (e4015 tail) (e1309 ([h192] ++ tail))
private def e4017 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .lam (e4016 tail) (by decide +kernel)
private def e4018 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h216 := .app (e222 tail) (e4017 tail)
private def e4019 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4018 tail) (e237 tail)
private def c4020 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4019 []).term
private def f4021 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c4020
private def s4022 : SourceTerm := SourceTerm.app s2281 s1404
private def s4023 : SourceTerm := SourceTerm.app s4022 s1278
private theorem n4024 : s4023.toDB [] = c3655.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4025 : CheckedSourceTerm := ⟨s4023, t1, by rw [← DBTerm.inferType_toDB [] s4023, n4024]; exact c3655.checked.trans (congrArg some v175)⟩
private def r4026 : InferenceRequest := .inst [(k4025, s1278)] f1336
private def e4027 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e240 tail) (e3654 tail)
private def e4028 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4027 tail)
private def e4060 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192, h173] ++ tail) h173 := .app (e4015 ([h173] ++ tail)) (e226 tail)
private def e4061 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h213 := .lam (e4060 tail) (by decide +kernel)
private def e4062 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h216 := .app (e222 ([h173] ++ tail)) (e4061 tail)
private def e4063 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e4062 tail) (e237 ([h173] ++ tail))
private def e4064 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e4063 tail) (by decide +kernel)
private def e4065 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4028 tail) (e4064 tail)
private def c4066 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4065 []).term
private def f4067 : Theorem := Theorem.emptyResult ([].toFinset) c4066
private def r4068 : InferenceRequest := .mkComb f4067 f3700
private def e4069 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4027 tail) (e1309 tail)
private def e4070 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4069 tail)
private def e4071 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4064 tail) (e1309 tail)
private def e4072 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4070 tail) (e4071 tail)
private def c4073 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4072 []).term
private def f4074 : Theorem := Theorem.emptyResult ([].toFinset) c4073
private def s4075 : SourceTerm := SourceTerm.app s3237 s1278
private def s4076 : SourceTerm := SourceTerm.app s1277 s4075
private def s4077 : SourceTerm := SourceTerm.app s4076 s47
private def s4078 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t17 s4077
private def s4079 : SourceTerm := SourceTerm.app s22 s4078
private def s4080 : SourceTerm := SourceTerm.app s4079 s1285
private def s4081 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s4080
private def s4082 : SourceTerm := SourceTerm.app s4081 s47
private def e4083 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .const (.variable ⟨Name.mk ["", ""] "x", t1⟩ q174) (by decide +kernel)
private def e4084 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4064 tail) (e4083 tail)
private def c4085 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4084 []).term
private theorem n4086 : s4082.toDB [] = c4085.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4087 : CheckedSourceTerm := ⟨s4082, t1, by rw [← DBTerm.inferType_toDB [] s4082, n4086]; exact c4085.checked.trans (congrArg some v175)⟩
private def r4088 : InferenceRequest := .beta k4087
private def e4089 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4084 tail)
private def e4091 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h173 := .app (e4015 tail) (e4083 ([h192] ++ tail))
private def e4092 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .lam (e4091 tail) (by decide +kernel)
private def e4093 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h216 := .app (e222 tail) (e4092 tail)
private def e4094 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4093 tail) (e237 tail)
private def e4095 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4089 tail) (e4094 tail)
private def c4096 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4095 []).term
private def f4097 : Theorem := Theorem.emptyResult ([].toFinset) c4096
private def r4098 : InferenceRequest := .inst [(k3725, s47)] f4097
private def e4099 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4071 tail)
private def e4100 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4099 tail) (e4019 tail)
private def c4101 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4100 []).term
private def f4102 : Theorem := Theorem.emptyResult ([].toFinset) c4101
private def r4103 : InferenceRequest := .trans f4074 f4102
private def e4104 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4070 tail) (e4019 tail)
private def c4105 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4104 []).term
private def f4106 : Theorem := Theorem.emptyResult ([].toFinset) c4105
private def r4107 : InferenceRequest := .mkComb f725 f4106
private def e4108 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4070 tail)
private def e4109 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4019 tail)
private def e4110 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4108 tail) (e4109 tail)
private def c4111 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4110 []).term
private def f4112 : Theorem := Theorem.emptyResult ([].toFinset) c4111
private def c4113 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4069 []).term
private def r4114 : InferenceRequest := .refl c4113
private def e4115 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4070 tail) (e4069 tail)
private def c4116 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4115 []).term
private def f4117 : Theorem := Theorem.emptyResult ([].toFinset) c4116
private def r4118 : InferenceRequest := .mkComb f4112 f4117
private def e4119 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4115 tail)
private def e4120 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4109 tail) (e4069 tail)
private def e4121 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4119 tail) (e4120 tail)
private def c4122 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4121 []).term
private def f4123 : Theorem := Theorem.emptyResult ([].toFinset) c4122
private def r4124 : InferenceRequest := .eqMp f4123 f4117
private def c4125 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4120 []).term
private def f4126 : Theorem := Theorem.emptyResult ([].toFinset) c4125
private def r4127 : InferenceRequest := .eqMp f4126 f4021
private def f4128 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c4113
private def r4129 : InferenceRequest := .assume c4113
private def f4130 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4113
private def r4131 : InferenceRequest := .eqMp f4106 f4130
private def f4132 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4020
private def r4133 : InferenceRequest := .mkComb f4132 f1813
private def e4134 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4017 tail) (e1807 tail)
private def e4135 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4134 tail)
private def e4136 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4135 tail) (e1817 tail)
private def c4137 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4136 []).term
private def f4138 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4137
private def s4139 : SourceTerm := SourceTerm.app s3305 s1278
private def s4140 : SourceTerm := SourceTerm.app s1662 s4139
private def s4141 : SourceTerm := SourceTerm.app s4140 s1278
private def s4142 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t17 s4141
private def s4143 : SourceTerm := SourceTerm.app s4142 s1662
private def e4144 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4017 tail) (e3815 tail)
private def c4145 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4144 []).term
private theorem n4146 : s4143.toDB [] = c4145.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4147 : CheckedSourceTerm := ⟨s4143, t1, by rw [← DBTerm.inferType_toDB [] s4143, n4146]; exact c4145.checked.trans (congrArg some v175)⟩
private def r4148 : InferenceRequest := .beta k4147
private def e4149 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4144 tail)
private def e4150 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4149 tail) (e3978 tail)
private def c4151 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4150 []).term
private def f4152 : Theorem := Theorem.emptyResult ([].toFinset) c4151
private def r4153 : InferenceRequest := .inst [(k1856, s1662)] f4152
private def e4154 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e1807 tail) (e3654 tail)
private def e4155 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4154 tail) (e1309 tail)
private def e4156 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4135 tail) (e4155 tail)
private def c4157 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4156 []).term
private def f4158 : Theorem := Theorem.emptyResult ([].toFinset) c4157
private def r4159 : InferenceRequest := .inst [(k4025, s1278)] f1874
private def e4160 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4154 tail)
private def e4162 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e3654 ([h173] ++ tail)) (by decide +kernel)
private def e4163 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4160 tail) (e4162 tail)
private def c4164 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4163 []).term
private def f4165 : Theorem := Theorem.emptyResult ([].toFinset) c4164
private def r4166 : InferenceRequest := .mkComb f4165 f3700
private def e4167 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4155 tail)
private def e4168 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4162 tail) (e1309 tail)
private def e4169 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4167 tail) (e4168 tail)
private def c4170 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4169 []).term
private def f4171 : Theorem := Theorem.emptyResult ([].toFinset) c4170
private def s4172 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s4139
private def s4173 : SourceTerm := SourceTerm.app s4172 s47
private def e4174 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4162 tail) (e4083 tail)
private def c4175 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4174 []).term
private theorem n4176 : s4173.toDB [] = c4175.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4177 : CheckedSourceTerm := ⟨s4173, t1, by rw [← DBTerm.inferType_toDB [] s4173, n4176]; exact c4175.checked.trans (congrArg some v175)⟩
private def r4178 : InferenceRequest := .beta k4177
private def e4179 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4174 tail)
private def e4180 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4179 tail) (e3654 tail)
private def c4181 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4180 []).term
private def f4182 : Theorem := Theorem.emptyResult ([].toFinset) c4181
private def r4183 : InferenceRequest := .inst [(k3725, s47)] f4182
private def e4184 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4168 tail)
private def e4185 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4184 tail) (e3654 tail)
private def c4186 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4185 []).term
private def f4187 : Theorem := Theorem.emptyResult ([].toFinset) c4186
private def r4188 : InferenceRequest := .trans f4171 f4187
private def e4189 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4167 tail) (e3654 tail)
private def c4190 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4189 []).term
private def f4191 : Theorem := Theorem.emptyResult ([].toFinset) c4190
private def r4192 : InferenceRequest := .trans f4158 f4191
private def e4193 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4135 tail) (e3654 tail)
private def c4194 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4193 []).term
private def f4195 : Theorem := Theorem.emptyResult ([].toFinset) c4194
private def r4196 : InferenceRequest := .mkComb f725 f4195
private def e4197 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4135 tail)
private def e4198 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4197 tail) (e3659 tail)
private def c4199 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4198 []).term
private def f4200 : Theorem := Theorem.emptyResult ([].toFinset) c4199
private def c4201 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4134 []).term
private def r4202 : InferenceRequest := .refl c4201
private def e4203 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4135 tail) (e4134 tail)
private def c4204 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4203 []).term
private def f4205 : Theorem := Theorem.emptyResult ([].toFinset) c4204
private def r4206 : InferenceRequest := .mkComb f4200 f4205
private def e4207 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4203 tail)
private def e4208 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3659 tail) (e4134 tail)
private def e4209 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4207 tail) (e4208 tail)
private def c4210 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4209 []).term
private def f4211 : Theorem := Theorem.emptyResult ([].toFinset) c4210
private def r4212 : InferenceRequest := .eqMp f4211 f4205
private def c4213 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4208 []).term
private def f4214 : Theorem := Theorem.emptyResult ([].toFinset) c4213
private def r4215 : InferenceRequest := .trans f4214 f4138
private def e4216 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3659 tail) (e1817 tail)
private def c4217 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4216 []).term
private def f4218 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4217
private def r4219 : InferenceRequest := .trans f4218 f2237
private def f4220 : Theorem := Theorem.emptyResult ([c4113].toFinset) c3967
private def r4221 : InferenceRequest := .mkComb f725 f4220
private def e4222 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3659 tail)
private def e4223 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4222 tail) (e2204 tail)
private def c4224 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4223 []).term
private def f4225 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4224
private def r4226 : InferenceRequest := .refl c3655
private def e4227 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3659 tail) (e3654 tail)
private def c4228 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4227 []).term
private def f4229 : Theorem := Theorem.emptyResult ([].toFinset) c4228
private def r4230 : InferenceRequest := .mkComb f4225 f4229
private def e4231 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4227 tail)
private def e4232 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2204 tail) (e3654 tail)
private def e4233 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4231 tail) (e4232 tail)
private def c4234 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4233 []).term
private def f4235 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4234
private def r4236 : InferenceRequest := .eqMp f4235 f4229
private def c4237 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4232 []).term
private def f4238 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4237
private def r4239 : InferenceRequest := .eqMp f4238 f777
private def f4240 : Theorem := Theorem.emptyResult ([c4113].toFinset) c3655
private def r4241 : InferenceRequest := .deductAntisym f4128 f4240
private def e4242 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4070 tail) (e3654 tail)
private def c4243 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4242 []).term
private def f4244 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4243
private def r4245 : InferenceRequest := .inst [(k4025, s1278)] f2342
private def e4246 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e248 tail) (e3654 tail)
private def e4247 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4246 tail)
private def e4249 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e4027 ([h173] ++ tail)) (e205 tail)
private def e4250 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .app (e212 ([h173] ++ tail)) (e4249 tail)
private def e4251 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e4250 tail) (e3654 ([h173] ++ tail))
private def e4252 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e4251 tail) (by decide +kernel)
private def e4253 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4247 tail) (e4252 tail)
private def c4254 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4253 []).term
private def f4255 : Theorem := Theorem.emptyResult ([].toFinset) c4254
private def r4256 : InferenceRequest := .mkComb f4255 f3700
private def e4257 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4246 tail) (e1309 tail)
private def e4258 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4257 tail)
private def e4259 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4252 tail) (e1309 tail)
private def e4260 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4258 tail) (e4259 tail)
private def c4261 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4260 []).term
private def f4262 : Theorem := Theorem.emptyResult ([].toFinset) c4261
private def s4263 : SourceTerm := SourceTerm.app s2275 s4139
private def s4264 : SourceTerm := SourceTerm.app s4263 s47
private def s4265 : SourceTerm := SourceTerm.app s18 s4264
private def s4266 : SourceTerm := SourceTerm.app s4265 s4139
private def s4267 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s4266
private def s4268 : SourceTerm := SourceTerm.app s4267 s47
private def e4269 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4252 tail) (e4083 tail)
private def c4270 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4269 []).term
private theorem n4271 : s4268.toDB [] = c4270.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4272 : CheckedSourceTerm := ⟨s4268, t1, by rw [← DBTerm.inferType_toDB [] s4268, n4271]; exact c4270.checked.trans (congrArg some v175)⟩
private def r4273 : InferenceRequest := .beta k4272
private def e4274 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4269 tail)
private def e4275 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4027 tail) (e4083 tail)
private def e4276 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4275 tail)
private def e4277 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4276 tail) (e3654 tail)
private def e4278 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4274 tail) (e4277 tail)
private def c4279 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4278 []).term
private def f4280 : Theorem := Theorem.emptyResult ([].toFinset) c4279
private def r4281 : InferenceRequest := .inst [(k3725, s47)] f4280
private def e4282 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4259 tail)
private def e4283 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4282 tail) (e4242 tail)
private def c4284 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4283 []).term
private def f4285 : Theorem := Theorem.emptyResult ([].toFinset) c4284
private def r4286 : InferenceRequest := .trans f4262 f4285
private def e4287 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4258 tail) (e4242 tail)
private def c4288 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4287 []).term
private def f4289 : Theorem := Theorem.emptyResult ([].toFinset) c4288
private def r4290 : InferenceRequest := .mkComb f725 f4289
private def e4291 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4258 tail)
private def e4292 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4242 tail)
private def e4293 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4291 tail) (e4292 tail)
private def c4294 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4293 []).term
private def f4295 : Theorem := Theorem.emptyResult ([].toFinset) c4294
private def c4296 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4257 []).term
private def r4297 : InferenceRequest := .refl c4296
private def e4298 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4258 tail) (e4257 tail)
private def c4299 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4298 []).term
private def f4300 : Theorem := Theorem.emptyResult ([].toFinset) c4299
private def r4301 : InferenceRequest := .mkComb f4295 f4300
private def e4302 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4298 tail)
private def e4303 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4292 tail) (e4257 tail)
private def e4304 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4302 tail) (e4303 tail)
private def c4305 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4304 []).term
private def f4306 : Theorem := Theorem.emptyResult ([].toFinset) c4305
private def r4307 : InferenceRequest := .eqMp f4306 f4300
private def c4308 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4303 []).term
private def f4309 : Theorem := Theorem.emptyResult ([].toFinset) c4308
private def r4310 : InferenceRequest := .eqMp f4309 f4244
private def f4311 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4296
private def r4312 : InferenceRequest := .deductAntisym f3652 f4311
private def e4313 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3666 tail) (e4257 tail)
private def c4314 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4313 []).term
private def f4315 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4314
private def r4316 : InferenceRequest := .eqMp f4315 f3652
private def r4317 : InferenceRequest := .deductAntisym f3652 f777
private def e4318 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3666 tail) (e208 tail)
private def c4319 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4318 []).term
private def f4320 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4319
private def r4321 : InferenceRequest := .deductAntisym f4311 f777
private def e4322 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4258 tail) (e208 tail)
private def c4323 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4322 []).term
private def f4324 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4323
private def r4325 : InferenceRequest := .mkComb f3964 f4320
private def e4326 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e3815 tail) (e3649 tail)
private def e4327 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4326 tail)
private def e4328 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4327 tail) (e3973 tail)
private def c4329 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4328 []).term
private def f4330 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4329
private def r4331 : InferenceRequest := .mkComb f4330 f4324
private def e4332 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4326 tail) (e4257 tail)
private def e4333 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4332 tail)
private def e4334 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4333 tail) (e3980 tail)
private def c4335 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4334 []).term
private def f4336 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4335
private def r4337 : InferenceRequest := .abs ⟨Name.mk ["", ""] "x", t17⟩ f4336
private def e4340 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h189 := .app (e223 tail) (e3649 ([h192] ++ tail))
private def e4343 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h173 := .app (e4340 tail) (e4257 ([h192] ++ tail))
private def e4344 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .lam (e4343 tail) (by decide +kernel)
private def e4345 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h216 := .app (e222 tail) (e4344 tail)
private def e4346 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4345 tail) (e237 tail)
private def c4347 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4346 []).term
private def f4348 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4347
private def s4349 : SourceTerm := SourceTerm.app s2281 s1350
private def s4350 : SourceTerm := SourceTerm.app s4349 s1278
private theorem n4351 : s4350.toDB [] = c3650.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4352 : CheckedSourceTerm := ⟨s4350, t1, by rw [← DBTerm.inferType_toDB [] s4350, n4351]; exact c3650.checked.trans (congrArg some v175)⟩
private def r4353 : InferenceRequest := .inst [(k4352, s1278)] f1336
private def e4354 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e240 tail) (e3649 tail)
private def e4355 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4354 tail)
private def e4359 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192, h173] ++ tail) h173 := .app (e4340 ([h173] ++ tail)) (e226 tail)
private def e4360 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h213 := .lam (e4359 tail) (by decide +kernel)
private def e4361 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h216 := .app (e222 ([h173] ++ tail)) (e4360 tail)
private def e4362 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e4361 tail) (e237 ([h173] ++ tail))
private def e4363 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e4362 tail) (by decide +kernel)
private def e4364 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4355 tail) (e4363 tail)
private def c4365 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4364 []).term
private def f4366 : Theorem := Theorem.emptyResult ([].toFinset) c4365
private def r4367 : InferenceRequest := .mkComb f4366 f4300
private def e4368 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4354 tail) (e4257 tail)
private def e4369 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4368 tail)
private def e4370 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4363 tail) (e4257 tail)
private def e4371 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4369 tail) (e4370 tail)
private def c4372 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4371 []).term
private def f4373 : Theorem := Theorem.emptyResult ([].toFinset) c4372
private def s4374 : SourceTerm := SourceTerm.app s3171 s1278
private def s4375 : SourceTerm := SourceTerm.app s1277 s4374
private def s4376 : SourceTerm := SourceTerm.app s4375 s47
private def s4377 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t17 s4376
private def s4378 : SourceTerm := SourceTerm.app s22 s4377
private def s4379 : SourceTerm := SourceTerm.app s4378 s1285
private def s4380 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s4379
private def s4381 : SourceTerm := SourceTerm.app s4380 s47
private def e4382 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4363 tail) (e4083 tail)
private def c4383 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4382 []).term
private theorem n4384 : s4381.toDB [] = c4383.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4385 : CheckedSourceTerm := ⟨s4381, t1, by rw [← DBTerm.inferType_toDB [] s4381, n4384]; exact c4383.checked.trans (congrArg some v175)⟩
private def r4386 : InferenceRequest := .beta k4385
private def e4387 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4382 tail)
private def e4388 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h192] ++ tail) h173 := .app (e4340 tail) (e4083 ([h192] ++ tail))
private def e4389 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h213 := .lam (e4388 tail) (by decide +kernel)
private def e4390 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h216 := .app (e222 tail) (e4389 tail)
private def e4391 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4390 tail) (e237 tail)
private def e4392 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4387 tail) (e4391 tail)
private def c4393 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4392 []).term
private def f4394 : Theorem := Theorem.emptyResult ([].toFinset) c4393
private def s4395 : SourceTerm := SourceTerm.app s2281 s4023
private def s4396 : SourceTerm := SourceTerm.app s4395 s1278
private theorem n4397 : s4396.toDB [] = c4296.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4398 : CheckedSourceTerm := ⟨s4396, t1, by rw [← DBTerm.inferType_toDB [] s4396, n4397]; exact c4296.checked.trans (congrArg some v175)⟩
private def r4399 : InferenceRequest := .inst [(k4398, s47)] f4394
private def e4400 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4370 tail)
private def e4401 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4400 tail) (e4346 tail)
private def c4402 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4401 []).term
private def f4403 : Theorem := Theorem.emptyResult ([].toFinset) c4402
private def r4404 : InferenceRequest := .trans f4373 f4403
private def e4405 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4369 tail) (e4346 tail)
private def c4406 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4405 []).term
private def f4407 : Theorem := Theorem.emptyResult ([].toFinset) c4406
private def r4408 : InferenceRequest := .mkComb f725 f4407
private def e4409 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4369 tail)
private def e4410 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4346 tail)
private def e4411 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4409 tail) (e4410 tail)
private def c4412 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4411 []).term
private def f4413 : Theorem := Theorem.emptyResult ([].toFinset) c4412
private def c4414 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4368 []).term
private def r4415 : InferenceRequest := .refl c4414
private def e4416 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4369 tail) (e4368 tail)
private def c4417 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4416 []).term
private def f4418 : Theorem := Theorem.emptyResult ([].toFinset) c4417
private def r4419 : InferenceRequest := .mkComb f4413 f4418
private def e4420 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4416 tail)
private def e4421 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4410 tail) (e4368 tail)
private def e4422 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4420 tail) (e4421 tail)
private def c4423 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4422 []).term
private def f4424 : Theorem := Theorem.emptyResult ([].toFinset) c4423
private def r4425 : InferenceRequest := .eqMp f4424 f4418
private def c4426 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4421 []).term
private def f4427 : Theorem := Theorem.emptyResult ([].toFinset) c4426
private def r4428 : InferenceRequest := .eqMp f4427 f4348
private def f4429 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4414
private def r4430 : InferenceRequest := .assume c4414
private def f4431 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4414
private def r4432 : InferenceRequest := .eqMp f4407 f4431
private def f4433 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4347
private def r4434 : InferenceRequest := .mkComb f4433 f1813
private def e4435 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4344 tail) (e1807 tail)
private def e4436 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4435 tail)
private def e4437 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4436 tail) (e1817 tail)
private def c4438 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4437 []).term
private def f4439 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4438
private def s4440 : SourceTerm := SourceTerm.app s2524 s1278
private def s4441 : SourceTerm := SourceTerm.app s1662 s4440
private def s4442 : SourceTerm := SourceTerm.app s1371 s4139
private def s4443 : SourceTerm := SourceTerm.app s4442 s1278
private def s4444 : SourceTerm := SourceTerm.app s4441 s4443
private def s4445 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t17 s4444
private def s4446 : SourceTerm := SourceTerm.app s4445 s1662
private def e4447 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4344 tail) (e3815 tail)
private def c4448 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4447 []).term
private theorem n4449 : s4446.toDB [] = c4448.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4450 : CheckedSourceTerm := ⟨s4446, t1, by rw [← DBTerm.inferType_toDB [] s4446, n4449]; exact c4448.checked.trans (congrArg some v175)⟩
private def r4451 : InferenceRequest := .beta k4450
private def e4452 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4447 tail)
private def e4453 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4452 tail) (e4332 tail)
private def c4454 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4453 []).term
private def f4455 : Theorem := Theorem.emptyResult ([].toFinset) c4454
private def r4456 : InferenceRequest := .inst [(k1856, s1662)] f4455
private def e4457 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e1807 tail) (e3649 tail)
private def e4458 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4457 tail) (e4257 tail)
private def e4459 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4436 tail) (e4458 tail)
private def c4460 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4459 []).term
private def f4461 : Theorem := Theorem.emptyResult ([].toFinset) c4460
private def r4462 : InferenceRequest := .inst [(k4352, s1278)] f1874
private def e4463 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4457 tail)
private def e4465 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e3649 ([h173] ++ tail)) (by decide +kernel)
private def e4466 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4463 tail) (e4465 tail)
private def c4467 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4466 []).term
private def f4468 : Theorem := Theorem.emptyResult ([].toFinset) c4467
private def r4469 : InferenceRequest := .mkComb f4468 f4300
private def e4470 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4458 tail)
private def e4471 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4465 tail) (e4257 tail)
private def e4472 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4470 tail) (e4471 tail)
private def c4473 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4472 []).term
private def f4474 : Theorem := Theorem.emptyResult ([].toFinset) c4473
private def s4475 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s4440
private def s4476 : SourceTerm := SourceTerm.app s4475 s47
private def e4477 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4465 tail) (e4083 tail)
private def c4478 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4477 []).term
private theorem n4479 : s4476.toDB [] = c4478.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4480 : CheckedSourceTerm := ⟨s4476, t1, by rw [← DBTerm.inferType_toDB [] s4476, n4479]; exact c4478.checked.trans (congrArg some v175)⟩
private def r4481 : InferenceRequest := .beta k4480
private def e4482 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4477 tail)
private def e4483 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4482 tail) (e3649 tail)
private def c4484 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4483 []).term
private def f4485 : Theorem := Theorem.emptyResult ([].toFinset) c4484
private def r4486 : InferenceRequest := .inst [(k4398, s47)] f4485
private def e4487 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4471 tail)
private def e4488 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4487 tail) (e3649 tail)
private def c4489 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4488 []).term
private def f4490 : Theorem := Theorem.emptyResult ([].toFinset) c4489
private def r4491 : InferenceRequest := .trans f4474 f4490
private def e4492 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4470 tail) (e3649 tail)
private def c4493 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4492 []).term
private def f4494 : Theorem := Theorem.emptyResult ([].toFinset) c4493
private def r4495 : InferenceRequest := .trans f4461 f4494
private def e4496 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4436 tail) (e3649 tail)
private def c4497 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4496 []).term
private def f4498 : Theorem := Theorem.emptyResult ([].toFinset) c4497
private def r4499 : InferenceRequest := .mkComb f725 f4498
private def e4500 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4436 tail)
private def e4501 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4500 tail) (e3666 tail)
private def c4502 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4501 []).term
private def f4503 : Theorem := Theorem.emptyResult ([].toFinset) c4502
private def c4504 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4435 []).term
private def r4505 : InferenceRequest := .refl c4504
private def e4506 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4436 tail) (e4435 tail)
private def c4507 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4506 []).term
private def f4508 : Theorem := Theorem.emptyResult ([].toFinset) c4507
private def r4509 : InferenceRequest := .mkComb f4503 f4508
private def e4510 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4506 tail)
private def e4511 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3666 tail) (e4435 tail)
private def e4512 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4510 tail) (e4511 tail)
private def c4513 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4512 []).term
private def f4514 : Theorem := Theorem.emptyResult ([].toFinset) c4513
private def r4515 : InferenceRequest := .eqMp f4514 f4508
private def c4516 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4511 []).term
private def f4517 : Theorem := Theorem.emptyResult ([].toFinset) c4516
private def r4518 : InferenceRequest := .trans f4517 f4439
private def e4519 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3666 tail) (e1817 tail)
private def c4520 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4519 []).term
private def f4521 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4520
private def r4522 : InferenceRequest := .trans f4521 f2237
private def f4523 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4319
private def r4524 : InferenceRequest := .mkComb f725 f4523
private def e4525 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e3666 tail)
private def e4526 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4525 tail) (e2204 tail)
private def c4527 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4526 []).term
private def f4528 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4527
private def r4529 : InferenceRequest := .refl c3650
private def f4530 : Theorem := Theorem.emptyResult ([].toFinset) c3668
private def r4531 : InferenceRequest := .mkComb f4528 f4530
private def e4532 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e3667 tail)
private def e4533 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2204 tail) (e3649 tail)
private def e4534 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4532 tail) (e4533 tail)
private def c4535 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4534 []).term
private def f4536 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4535
private def r4537 : InferenceRequest := .eqMp f4536 f4530
private def c4538 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4533 []).term
private def f4539 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4538
private def r4540 : InferenceRequest := .eqMp f4539 f777
private def f4541 : Theorem := Theorem.emptyResult ([c4414].toFinset) c3650
private def r4542 : InferenceRequest := .deductAntisym f4429 f4541
private def e4543 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4369 tail) (e3649 tail)
private def c4544 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4543 []).term
private def f4545 : Theorem := Theorem.emptyResult ([].toFinset) c4544
private def r4546 : InferenceRequest := .inst [(k4352, s1278)] f2342
private def e4547 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e248 tail) (e3649 tail)
private def e4548 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4547 tail)
private def e4550 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e4354 ([h173] ++ tail)) (e205 tail)
private def e4551 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h189 := .app (e212 ([h173] ++ tail)) (e4550 tail)
private def e4552 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses ([h173] ++ tail) h173 := .app (e4551 tail) (e3649 ([h173] ++ tail))
private def e4553 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .lam (e4552 tail) (by decide +kernel)
private def e4554 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4548 tail) (e4553 tail)
private def c4555 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4554 []).term
private def f4556 : Theorem := Theorem.emptyResult ([].toFinset) c4555
private def r4557 : InferenceRequest := .mkComb f4556 f4300
private def e4558 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4547 tail) (e4257 tail)
private def e4559 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4558 tail)
private def e4560 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4553 tail) (e4257 tail)
private def e4561 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4559 tail) (e4560 tail)
private def c4562 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4561 []).term
private def f4563 : Theorem := Theorem.emptyResult ([].toFinset) c4562
private def s4564 : SourceTerm := SourceTerm.app s2275 s4440
private def s4565 : SourceTerm := SourceTerm.app s4564 s47
private def s4566 : SourceTerm := SourceTerm.app s18 s4565
private def s4567 : SourceTerm := SourceTerm.app s4566 s4440
private def s4568 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s4567
private def s4569 : SourceTerm := SourceTerm.app s4568 s47
private def e4570 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4553 tail) (e4083 tail)
private def c4571 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4570 []).term
private theorem n4572 : s4569.toDB [] = c4571.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4573 : CheckedSourceTerm := ⟨s4569, t1, by rw [← DBTerm.inferType_toDB [] s4569, n4572]; exact c4571.checked.trans (congrArg some v175)⟩
private def r4574 : InferenceRequest := .beta k4573
private def e4575 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4570 tail)
private def e4576 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4354 tail) (e4083 tail)
private def e4577 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4576 tail)
private def e4578 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4577 tail) (e3649 tail)
private def e4579 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4575 tail) (e4578 tail)
private def c4580 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4579 []).term
private def f4581 : Theorem := Theorem.emptyResult ([].toFinset) c4580
private def r4582 : InferenceRequest := .inst [(k4398, s47)] f4581
private def e4583 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4560 tail)
private def e4584 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4583 tail) (e4543 tail)
private def c4585 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4584 []).term
private def f4586 : Theorem := Theorem.emptyResult ([].toFinset) c4585
private def r4587 : InferenceRequest := .trans f4563 f4586
private def e4588 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4559 tail) (e4543 tail)
private def c4589 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4588 []).term
private def f4590 : Theorem := Theorem.emptyResult ([].toFinset) c4589
private def r4591 : InferenceRequest := .mkComb f725 f4590
private def e4592 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4559 tail)
private def e4593 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4543 tail)
private def e4594 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4592 tail) (e4593 tail)
private def c4595 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4594 []).term
private def f4596 : Theorem := Theorem.emptyResult ([].toFinset) c4595
private def c4597 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4558 []).term
private def r4598 : InferenceRequest := .refl c4597
private def e4599 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4559 tail) (e4558 tail)
private def c4600 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4599 []).term
private def f4601 : Theorem := Theorem.emptyResult ([].toFinset) c4600
private def r4602 : InferenceRequest := .mkComb f4596 f4601
private def e4603 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4599 tail)
private def e4604 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4593 tail) (e4558 tail)
private def e4605 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4603 tail) (e4604 tail)
private def c4606 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4605 []).term
private def f4607 : Theorem := Theorem.emptyResult ([].toFinset) c4606
private def r4608 : InferenceRequest := .eqMp f4607 f4601
private def c4609 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4604 []).term
private def f4610 : Theorem := Theorem.emptyResult ([].toFinset) c4609
private def r4611 : InferenceRequest := .eqMp f4610 f4545
private def f4612 : Theorem := Theorem.emptyResult ([].toFinset) c4597
private def r4613 : InferenceRequest := .deductAntisym f4612 f777
private def e4614 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4559 tail) (e208 tail)
private def c4615 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4614 []).term
private def f4616 : Theorem := Theorem.emptyResult ([].toFinset) c4615
private def r4617 : InferenceRequest := .abs ⟨Name.mk [""] "x", t1⟩ f4616
private def e4618 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e2601 tail)
private def e4619 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4618 tail) (e209 tail)
private def c4620 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4619 []).term
private def f4621 : Theorem := Theorem.emptyResult ([].toFinset) c4620
private def s4622 : SourceTerm := SourceTerm.app s2895 s2891
private def e4623 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .const (.variable ⟨Name.mk [""] "x", t4⟩ q190) (by decide +kernel)
private def e4624 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e211 tail) (e4623 tail)
private def c4625 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4624 []).term
private theorem n4626 : s4622.toDB [] = c4625.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4627 : CheckedSourceTerm := ⟨s4622, t1, by rw [← DBTerm.inferType_toDB [] s4622, n4626]; exact c4625.checked.trans (congrArg some v175)⟩
private def r4628 : InferenceRequest := .beta k4627
private def e4629 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4624 tail)
private def e4630 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4623 tail)
private def e4631 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4630 tail) (e209 tail)
private def e4632 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4629 tail) (e4631 tail)
private def c4633 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4632 []).term
private def f4634 : Theorem := Theorem.emptyResult ([].toFinset) c4633
private def c4635 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e2601 []).term
private theorem n4636 : s2921.toDB [] = c4635.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4637 : CheckedSourceTerm := ⟨s2921, t4, by rw [← DBTerm.inferType_toDB [] s2921, n4636]; exact c4635.checked.trans (congrArg some v191)⟩
private def r4638 : InferenceRequest := .inst [(k4637, s2891)] f4634
private def e4639 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2611 tail) (e4619 tail)
private def c4640 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4639 []).term
private def f4641 : Theorem := Theorem.emptyResult ([].toFinset) c4640
private def r4642 : InferenceRequest := .mkComb f725 f4641
private def e4643 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4619 tail)
private def e4644 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3561 tail) (e4643 tail)
private def c4645 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4644 []).term
private def f4646 : Theorem := Theorem.emptyResult ([].toFinset) c4645
private def r4647 : InferenceRequest := .mkComb f4646 f2635
private def e4648 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4643 tail) (e2602 tail)
private def e4649 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3567 tail) (e4648 tail)
private def c4650 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4649 []).term
private def f4651 : Theorem := Theorem.emptyResult ([].toFinset) c4650
private def r4652 : InferenceRequest := .eqMp f4651 f2635
private def c4653 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4648 []).term
private def f4654 : Theorem := Theorem.emptyResult ([].toFinset) c4653
private def r4655 : InferenceRequest := .eqMp f4654 f4621
private def f4656 : Theorem := Theorem.emptyResult ([].toFinset) c2623
private def r4657 : InferenceRequest := .eqMp f3625 f3647
private def r4658 : InferenceRequest := .mkComb f725 f3580
private def e4659 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3274 tail) (e2611 tail)
private def c4660 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4659 []).term
private def f4661 : Theorem := Theorem.emptyResult ([].toFinset) c4660
private def r4662 : InferenceRequest := .mkComb f4661 f3283
private def e4663 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2611 tail) (e3164 tail)
private def e4664 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e3285 tail) (e4663 tail)
private def c4665 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4664 []).term
private def f4666 : Theorem := Theorem.emptyResult ([].toFinset) c4665
private def r4667 : InferenceRequest := .eqMp f4666 f3283
private def c4668 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4663 []).term
private def f4669 : Theorem := Theorem.emptyResult ([].toFinset) c4668
private def r4670 : InferenceRequest := .eqMp f4669 f4656
private def f4671 : Theorem := Theorem.emptyResult ([].toFinset) c3279
private def r4672 : InferenceRequest := .eqMp f3272 f4671
private def f4673 : Theorem := Theorem.emptyResult ([].toFinset) c2889
private def r4674 : InferenceRequest := .mkComb f4673 f3806
private def e4675 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2886 tail) (e3800 tail)
private def e4676 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4675 tail)
private def e4677 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4676 tail) (e3810 tail)
private def c4678 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4677 []).term
private def f4679 : Theorem := Theorem.emptyResult ([].toFinset) c4678
private def r4680 : InferenceRequest := .inst [(k3829, s1821)] f3324
private def e4681 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e3800 tail) (e2602 tail)
private def e4682 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4681 tail) (e711 tail)
private def e4683 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4676 tail) (e4682 tail)
private def c4684 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4683 []).term
private def f4685 : Theorem := Theorem.emptyResult ([].toFinset) c4684
private def r4686 : InferenceRequest := .inst [(k2924, s1278)] f3845
private def e4687 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4681 tail)
private def e4688 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4687 tail) (e206 tail)
private def c4689 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4688 []).term
private def f4690 : Theorem := Theorem.emptyResult ([].toFinset) c4689
private def r4691 : InferenceRequest := .mkComb f4690 f759
private def e4692 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4682 tail)
private def e4693 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e206 tail) (e711 tail)
private def e4694 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4692 tail) (e4693 tail)
private def c4695 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4694 []).term
private def f4696 : Theorem := Theorem.emptyResult ([].toFinset) c4695
private def r4697 : InferenceRequest := .inst [(k1407, s1278)] f3865
private def e4698 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4693 tail)
private def e4699 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4698 tail) (e711 tail)
private def c4700 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4699 []).term
private def f4701 : Theorem := Theorem.emptyResult ([].toFinset) c4700
private def r4702 : InferenceRequest := .trans f4696 f4701
private def e4703 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4692 tail) (e711 tail)
private def c4704 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4703 []).term
private def f4705 : Theorem := Theorem.emptyResult ([].toFinset) c4704
private def r4706 : InferenceRequest := .trans f4685 f4705
private def e4707 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4676 tail) (e711 tail)
private def c4708 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4707 []).term
private def f4709 : Theorem := Theorem.emptyResult ([].toFinset) c4708
private def r4710 : InferenceRequest := .mkComb f725 f4709
private def e4711 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4676 tail)
private def e4712 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4711 tail) (e729 tail)
private def c4713 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4712 []).term
private def f4714 : Theorem := Theorem.emptyResult ([].toFinset) c4713
private def c4715 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4675 []).term
private def r4716 : InferenceRequest := .refl c4715
private def e4717 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4676 tail) (e4675 tail)
private def c4718 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4717 []).term
private def f4719 : Theorem := Theorem.emptyResult ([].toFinset) c4718
private def r4720 : InferenceRequest := .mkComb f4714 f4719
private def e4721 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4717 tail)
private def e4722 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e729 tail) (e4675 tail)
private def e4723 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4721 tail) (e4722 tail)
private def c4724 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4723 []).term
private def f4725 : Theorem := Theorem.emptyResult ([].toFinset) c4724
private def r4726 : InferenceRequest := .eqMp f4725 f4719
private def c4727 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4722 []).term
private def f4728 : Theorem := Theorem.emptyResult ([].toFinset) c4727
private def r4729 : InferenceRequest := .trans f4728 f4679
private def e4730 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e729 tail) (e3810 tail)
private def c4731 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4730 []).term
private def f4732 : Theorem := Theorem.emptyResult ([].toFinset) c4731
private def r4733 : InferenceRequest := .trans f4732 f3924
private def f4734 : Theorem := Theorem.emptyResult ([].toFinset) c780
private def r4735 : InferenceRequest := .mkComb f725 f4734
private def f4736 : Theorem := Theorem.emptyResult ([].toFinset) c2247
private def r4737 : InferenceRequest := .mkComb f4736 f759
private def f4738 : Theorem := Theorem.emptyResult ([].toFinset) c2254
private def r4739 : InferenceRequest := .eqMp f4738 f759
private def f4740 : Theorem := Theorem.emptyResult ([].toFinset) c2257
private def r4741 : InferenceRequest := .eqMp f4740 f777
private def f4742 : Theorem := Theorem.emptyResult ([].toFinset) c747
private def r4743 : InferenceRequest := .eqMp f2398 f2420
private def r4744 : InferenceRequest := .mkComb f725 f2264
private def e4745 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1780 tail) (e729 tail)
private def c4746 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4745 []).term
private def f4747 : Theorem := Theorem.emptyResult ([].toFinset) c4746
private def r4748 : InferenceRequest := .mkComb f4747 f1789
private def e4749 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e729 tail) (e1656 tail)
private def e4750 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1791 tail) (e4749 tail)
private def c4751 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4750 []).term
private def f4752 : Theorem := Theorem.emptyResult ([].toFinset) c4751
private def r4753 : InferenceRequest := .eqMp f4752 f1789
private def c4754 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4749 []).term
private def f4755 : Theorem := Theorem.emptyResult ([].toFinset) c4754
private def r4756 : InferenceRequest := .eqMp f4755 f4742
private def f4757 : Theorem := Theorem.emptyResult ([].toFinset) c1785
private def r4758 : InferenceRequest := .eqMp f1778 f4757
private def f4759 : Theorem := Theorem.emptyResult ([].toFinset) c1275
private def r4760 : InferenceRequest := .mkComb f4759 f3806
private def e4761 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e1264 tail) (e3800 tail)
private def e4762 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4761 tail)
private def e4763 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4762 tail) (e3810 tail)
private def c4764 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4763 []).term
private def f4765 : Theorem := Theorem.emptyResult ([].toFinset) c4764
private def r4766 : InferenceRequest := .inst [(k3829, s1821)] f1852
private def e4767 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e3800 tail) (e711 tail)
private def e4768 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4767 tail) (e686 tail)
private def e4769 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4762 tail) (e4768 tail)
private def c4770 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4769 []).term
private def f4771 : Theorem := Theorem.emptyResult ([].toFinset) c4770
private def r4772 : InferenceRequest := .inst [(k1407, s1278)] f3845
private def e4773 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4767 tail)
private def e4774 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4773 tail) (e206 tail)
private def c4775 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4774 []).term
private def f4776 : Theorem := Theorem.emptyResult ([].toFinset) c4775
private def r4777 : InferenceRequest := .mkComb f4776 f737
private def e4778 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4768 tail)
private def e4779 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e206 tail) (e686 tail)
private def e4780 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4778 tail) (e4779 tail)
private def c4781 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4780 []).term
private def f4782 : Theorem := Theorem.emptyResult ([].toFinset) c4781
private def r4783 : InferenceRequest := .inst [(k1769, s1278)] f3865
private def e4784 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4779 tail)
private def e4785 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4784 tail) (e686 tail)
private def c4786 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4785 []).term
private def f4787 : Theorem := Theorem.emptyResult ([].toFinset) c4786
private def r4788 : InferenceRequest := .trans f4782 f4787
private def e4789 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4778 tail) (e686 tail)
private def c4790 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4789 []).term
private def f4791 : Theorem := Theorem.emptyResult ([].toFinset) c4790
private def r4792 : InferenceRequest := .trans f4771 f4791
private def e4793 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4762 tail) (e686 tail)
private def c4794 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4793 []).term
private def f4795 : Theorem := Theorem.emptyResult ([].toFinset) c4794
private def r4796 : InferenceRequest := .mkComb f725 f4795
private def e4797 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h195 := .app (e201 tail) (e4762 tail)
private def e4798 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4797 tail) (e687 tail)
private def c4799 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4798 []).term
private def f4800 : Theorem := Theorem.emptyResult ([].toFinset) c4799
private def c4801 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4761 []).term
private def r4802 : InferenceRequest := .refl c4801
private def e4803 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4762 tail) (e4761 tail)
private def c4804 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4803 []).term
private def f4805 : Theorem := Theorem.emptyResult ([].toFinset) c4804
private def r4806 : InferenceRequest := .mkComb f4800 f4805
private def e4807 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h189 := .app (e212 tail) (e4803 tail)
private def e4808 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e687 tail) (e4761 tail)
private def e4809 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e4807 tail) (e4808 tail)
private def c4810 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4809 []).term
private def f4811 : Theorem := Theorem.emptyResult ([].toFinset) c4810
private def r4812 : InferenceRequest := .eqMp f4811 f4805
private def c4813 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4808 []).term
private def f4814 : Theorem := Theorem.emptyResult ([].toFinset) c4813
private def r4815 : InferenceRequest := .trans f4814 f4765
private def e4816 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e687 tail) (e3810 tail)
private def c4817 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4816 []).term
private def f4818 : Theorem := Theorem.emptyResult ([].toFinset) c4817
private def r4819 : InferenceRequest := .trans f4818 f3924
private def f4820 : Theorem := Theorem.emptyResult ([].toFinset) c784
private def r4821 : InferenceRequest := .mkComb f725 f4820
private def e4822 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e728 tail) (e2204 tail)
private def c4823 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4822 []).term
private def f4824 : Theorem := Theorem.emptyResult ([].toFinset) c4823
private def r4825 : InferenceRequest := .mkComb f4824 f737
private def e4826 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e2204 tail) (e686 tail)
private def e4827 (tail : HOL.Ctx AtomicTy) :
    FormedHOL coreSignature coreWitnesses tail h173 := .app (e739 tail) (e4826 tail)
private def c4828 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4827 []).term
private def f4829 : Theorem := Theorem.emptyResult ([].toFinset) c4828
private def r4830 : InferenceRequest := .eqMp f4829 f737
private def c4831 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (e4826 []).term
private def f4832 : Theorem := Theorem.emptyResult ([].toFinset) c4831
private def r4833 : InferenceRequest := .eqMp f4832 f777
private def f4834 : Theorem := Theorem.emptyResult ([].toFinset) c733

private theorem different : c3650 ≠ c3655 := by decide +kernel

theorem check199 : r3658.check = some f3662 := by
  apply (InferenceRequest.check_eq_some_iff _ _).mpr
  refine ⟨c3661,⟨rfl,rfl⟩,rfl,?_,rfl⟩
  change [c3650,c3655].toFinset =
    ([c3655].toFinset.erase c3650) ∪ ([c3650].toFinset.erase c3655)
  ext term
  simp [different,Ne.symm different,or_comm]

theorem check203 : r3670.check = some f3664 := by
  apply (InferenceRequest.check_eq_some_iff _ _).mpr
  refine ⟨c3650,c3650,⟨rfl,rfl⟩,rfl,rfl,?_,rfl⟩
  change [c3650,c3655].toFinset = [c3655].toFinset ∪ [c3650].toFinset
  ext term
  simp [or_comm]

theorem check210 : r3683.check = some f3684 := by
  apply (InferenceRequest.check_eq_some_iff _ _).mpr
  refine ⟨c3650,c2480,⟨rfl,rfl⟩,rfl,rfl,?_,rfl⟩
  change [c3650,c3655].toFinset = [c3650,c3655].toFinset ∪ [c3650].toFinset
  ext term
  simp [or_comm]

theorem check270 : r3949.check = some f3952 := by
  apply (InferenceRequest.check_eq_some_iff _ _).mpr
  refine ⟨c3951,⟨rfl,rfl⟩,rfl,?_,rfl⟩
  change [c3650,c3655].toFinset =
    ([c3655].toFinset.erase c3695) ∪ ([c3650,c3655].toFinset.erase c3655)
  have distinct : c3655 ≠ c3695 := by decide +kernel
  ext term
  simp [Ne.symm different,Ne.symm distinct]

theorem check274 : r3958.check = some f3948 := by
  apply (InferenceRequest.check_eq_some_iff _ _).mpr
  refine ⟨c3650,c3695,⟨rfl,rfl⟩,rfl,rfl,?_,rfl⟩
  change [c3650,c3655].toFinset = [c3650,c3655].toFinset ∪ [c3650].toFinset
  ext term
  simp [or_comm]


private def requestFormation (witness : RuleRequest) (conclusion : Theorem) : Bool :=
  ProofExecution.Registered.requestFormedB ContextControls.coreContext.signature
    (ExportReplay.instanceCertificates ContextControls.coreContext.signature) witness &&
    theoremFormedB ContextControls.coreContext.signature
      (ExportReplay.instanceCertificates ContextControls.coreContext.signature) conclusion

private def nodeFormed (node : ProofExecution.Receipt) : Bool :=
  requestFormation node.witness node.conclusion

private def closedCanonical {type : HOL.Ty AtomicTy}
    (term : HOL.ClosedTerm Symbol type) : CanonicalTerm :=
  ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty term

private def closedEquality {type : HOL.Ty AtomicTy}
    (left right : HOL.ClosedTerm Symbol type) : Theorem :=
  Theorem.emptyResult ∅ (CanonicalTerm.equalityOfSameType (closedCanonical left) (closedCanonical right) rfl)

private theorem closedReflexivity {type : HOL.Ty AtomicTy} (term : HOL.ClosedTerm Symbol type) :
    (InferenceRequest.refl (closedCanonical term)).check = some (closedEquality term term) :=
  EqualityExpansion.reflexivity_checked _

private theorem closedEqMp (left right : HOL.ClosedFormula Symbol) :
    (InferenceRequest.eqMp (closedEquality left right) (Theorem.emptyResult ∅ (closedCanonical left))).check =
      some (Theorem.emptyResult ∅ (closedCanonical right)) :=
  EqualityExpansion.eqMpResult_checked _ _ (closedCanonical left) (closedCanonical right)
    (EqualityExpansion.equality_view (closedCanonical left) (closedCanonical right) rfl) rfl

private theorem closedTrans {type : HOL.Ty AtomicTy} (left middle right : HOL.ClosedTerm Symbol type) :
    (InferenceRequest.trans (closedEquality left middle) (closedEquality middle right)).check =
      some (closedEquality left right) :=
  EqualityExpansion.transResult_checked _ _ (closedCanonical left) (closedCanonical middle)
    (closedCanonical right) rfl
    (EqualityExpansion.equality_view (closedCanonical left) (closedCanonical middle) rfl)
    (EqualityExpansion.equality_view (closedCanonical middle) (closedCanonical right) rfl)

private theorem closedApplication {input output : HOL.Ty AtomicTy}
    (f g : HOL.ClosedTerm Symbol (.arr input output)) (left right : HOL.ClosedTerm Symbol input) :
    (InferenceRequest.mkComb (closedEquality f g) (closedEquality left right)).check =
      some (closedEquality (.app f left) (.app g right)) :=
  EqualityExpansion.appResult_checked _ _ (closedCanonical f) (closedCanonical g)
    (closedCanonical left) (closedCanonical right) (closedCanonical (.app f left))
    (closedCanonical (.app g right)) rfl
    (EqualityExpansion.equality_view (closedCanonical f) (closedCanonical g) rfl)
    (EqualityExpansion.equality_view (closedCanonical left) (closedCanonical right) rfl)
    ⟨ReverseTranslation.reverseTy input, ReverseTranslation.reverseTy output, Ty.destFunction?_function _ _, rfl, rfl⟩
    ⟨ReverseTranslation.reverseTy input, ReverseTranslation.reverseTy output, Ty.destFunction?_function _ _, rfl, rfl⟩

private theorem formedResult {type : HOL.Ty AtomicTy} (request : InferenceRequest)
    (result : FormedHOL coreSignature coreWitnesses [] type)
    (arguments : ProofExecution.Registered.requestFormedB coreSignature coreWitnesses
      (.inference request) = true) :
    requestFormation (.inference request)
      (Theorem.emptyResult ∅ (closedCanonical result.term)) = true := by
  change (ProofExecution.Registered.requestFormedB coreSignature coreWitnesses (.inference request) &&
    theoremFormedB coreSignature coreWitnesses
      (Theorem.emptyResult ∅ (closedCanonical result.term))) = true
  rw [arguments, Bool.true_and]
  exact result.emptyResult_formed

private theorem formedReflRequest {type : HOL.Ty AtomicTy}
    (argument : FormedHOL coreSignature coreWitnesses [] type) :
    ProofExecution.Registered.requestFormedB coreSignature coreWitnesses
      (.inference (.refl (closedCanonical argument.term))) = true := by
  have termCheck : annotationsFormedB coreSignature coreWitnesses (closedCanonical argument.term).term = true :=
    argument.canonical_formed
  simp [ProofExecution.Registered.requestFormedB, InferenceFormation.check,
    InferenceFormation.types, InferenceFormation.terms, termCheck]

checked_hol_trace witnessTrace emptyAxiomPolicy requestFormation ("pointed-predicate-witness", 0) [
  f670 r444 []
    formed_by (formedResult r444 (e668 []) (by decide +kernel)),
  f714 r685 [0]
    formed_by (formedResult r685 (e712 []) (by decide +kernel)),
  f725 r716 [] checked_by (closedReflexivity (e212 []).term)
    formed_by (formedResult r716 (e723 []) (formedReflRequest (e212 []))),
  f732 r726 [2, 1] checked_by (closedApplication (e212 []).term (e212 []).term (e686 []).term (e711 []).term)
    formed_by (formedResult r726 (e730 []) rfl),
  f737 r734 [] checked_by (closedReflexivity (e686 []).term)
    formed_by (formedResult r734 (e735 []) (formedReflRequest (e686 []))),
  f743 r738 [3, 4] checked_by (closedApplication (e687 []).term (e729 []).term (e686 []).term (e686 []).term)
    formed_by (formedResult r738 (e741 []) rfl),
  f746 r744 [5, 4] checked_by (closedEqMp (e735 []).term (e740 []).term)
    formed_by (formedResult r744 (e740 []) rfl),
  f749 r748 [],
  f753 r750 [7, 6],
  f755 r754 [8, 7],
  f749 r748 [],
  f749 r748 [],
  f759 r756 [11, 10]
    formed_by (formedResult r756 (e757 []) rfl),
  f749 r760 [12, 11],
  f762 r761 [9, 13],
  f749 r748 [],
  f769 r765 [] checked_by (closedReflexivity (e763 []).term)
    formed_by (formedResult r765 (e767 []) (formedReflRequest (e763 []))),
  f777 r773 [] checked_by (closedReflexivity (e206 []).term)
    formed_by (formedResult r773 (e208 []) (formedReflRequest (e206 []))),
  f781 r778 [15, 17],
  f777 r773 [],
  f785 r782 [14, 19],
  f792 r786 [16, 18],
  f799 r793 [21, 20],
  f1276 r800 [22],
  f1336 r1314 []
    formed_by (formedResult r1314 (e1334 []) (by decide +kernel)),
  f1654 r1408 [24]
    formed_by (formedResult r1408 (e1652 []) (by decide +kernel)),
  f737 r734 [],
  f1661 r1655 [25, 26] checked_by (closedApplication (e1409 []).term (e1651 []).term (e686 []).term (e686 []).term)
    formed_by (formedResult r1655 (e1659 []) rfl),
  f1766 r1757 []
    formed_by (formedResult r1757 (e1764 []) (by decide +kernel)),
  f1774 r1770 [28]
    formed_by (formedResult r1770 (e1772 []) (by decide +kernel)),
  f1778 r1775 [27, 29] checked_by (closedTrans (e1656 []).term (e1658 []).term (e1274 []).term)
    formed_by (formedResult r1775 (e1776 []) rfl),
  f725 r716 [],
  f1784 r1779 [31, 30] checked_by (closedApplication (e212 []).term (e212 []).term (e1656 []).term (e1274 []).term)
    formed_by (formedResult r1779 (e1782 []) rfl),
  f1789 r1786 [] checked_by (closedReflexivity (e1656 []).term)
    formed_by (formedResult r1786 (e1787 []) (formedReflRequest (e1656 []))),
  f1795 r1790 [32, 33] checked_by (closedApplication (e1657 []).term (e1781 []).term (e1656 []).term (e1656 []).term)
    formed_by (formedResult r1790 (e1793 []) rfl),
  f1798 r1796 [34, 33] checked_by (closedEqMp (e1787 []).term (e1792 []).term)
    formed_by (formedResult r1796 (e1792 []) rfl),
  f1800 r1799 [35, 23],
  f1802 r1801 [],
  f1336 r1314 [],
  f1654 r1408 [38],
  f737 r734 [],
  f1661 r1655 [39, 40],
  f1766 r1757 [],
  f1774 r1770 [42],
  f1778 r1775 [41, 43],
  f1804 r1803 [44, 37],
  f1813 r1809 [] checked_by (closedReflexivity (e1807 []).term)
    formed_by (formedResult r1809 (e1811 []) (formedReflRequest (e1807 []))),
  f1820 r1814 [45, 46],
  f1852 r1848 []
    formed_by (formedResult r1848 (e1850 []) (by decide +kernel)),
  f1862 r1857 [48]
    formed_by (formedResult r1857 (e1860 []) (by decide +kernel)),
  f1874 r1868 []
    formed_by (formedResult r1868 (e1872 []) (by decide +kernel)),
  f2115 r1875 [50]
    formed_by (formedResult r1875 (e2113 []) (by decide +kernel)),
  f737 r734 [],
  f2121 r2116 [51, 52] checked_by (closedApplication (e1858 []).term (e2112 []).term (e686 []).term (e686 []).term)
    formed_by (formedResult r2116 (e2119 []) rfl),
  f2132 r2128 []
    formed_by (formedResult r2128 (e2130 []) (by decide +kernel)),
  f2137 r2133 [54]
    formed_by (formedResult r2133 (e2135 []) (by decide +kernel)),
  f2141 r2138 [53, 55] checked_by (closedTrans (e1859 []).term (e2118 []).term (e711 []).term)
    formed_by (formedResult r2138 (e2139 []) rfl),
  f2145 r2142 [49, 56] checked_by (closedTrans (e1815 []).term (e1859 []).term (e711 []).term)
    formed_by (formedResult r2142 (e2143 []) rfl),
  f725 r716 [],
  f2150 r2146 [58, 57] checked_by (closedApplication (e212 []).term (e212 []).term (e1815 []).term (e711 []).term)
    formed_by (formedResult r2146 (e2148 []) rfl),
  f2155 r2152 [] checked_by (closedReflexivity (e1815 []).term)
    formed_by (formedResult r2152 (e2153 []) (formedReflRequest (e1815 []))),
  f2161 r2156 [59, 60] checked_by (closedApplication (e1816 []).term (e729 []).term (e1815 []).term (e1815 []).term)
    formed_by (formedResult r2156 (e2159 []) rfl),
  f2164 r2162 [61, 60] checked_by (closedEqMp (e2153 []).term (e2158 []).term)
    formed_by (formedResult r2162 (e2158 []) rfl),
  f2179 r2175 []
    formed_by (formedResult r2175 (e2177 []) (by decide +kernel)),
  f2186 r2180 [63]
    formed_by (formedResult r2180 (e2184 []) (by decide +kernel)),
  f1874 r1868 [],
  f2202 r2192 [65]
    formed_by (formedResult r2192 (e2200 []) (by decide +kernel)),
  f2207 r2203 [] checked_by (closedReflexivity (e208 []).term)
    formed_by (formedResult r2203 (e2205 []) (formedReflRequest (e208 []))),
  f2213 r2208 [66, 67] checked_by (closedApplication (e2182 []).term (e209 []).term (e208 []).term (e208 []).term)
    formed_by (formedResult r2208 (e2211 []) rfl),
  f2224 r2220 []
    formed_by (formedResult r2220 (e2222 []) (by decide +kernel)),
  f2229 r2225 [69]
    formed_by (formedResult r2225 (e2227 []) (by decide +kernel)),
  f2233 r2230 [68, 70] checked_by (closedTrans (e2183 []).term (e2210 []).term (e208 []).term)
    formed_by (formedResult r2230 (e2231 []) rfl),
  f2237 r2234 [64, 71] checked_by (closedTrans (e1817 []).term (e2183 []).term (e208 []).term)
    formed_by (formedResult r2234 (e2235 []) rfl),
  f2241 r2238 [62, 47],
  f2243 r2242 [73, 72],
  f725 r716 [],
  f2248 r2244 [75, 74],
  f759 r2249 [] checked_by (closedReflexivity (e711 []).term)
    formed_by (formedResult r2249 (e757 []) (formedReflRequest (e711 []))),
  f2255 r2250 [76, 77],
  f2258 r2256 [78, 77],
  f777 r773 [],
  f2260 r2259 [79, 80],
  f2264 r2261 [36, 81]
    formed_by (formedResult r2261 (e2262 []) rfl),
  f2342 r2313 []
    formed_by (formedResult r2313 (e2340 []) (by decide +kernel)),
  f2353 r2343 [83]
    formed_by (formedResult r2343 (e2351 []) (by decide +kernel)),
  f737 r734 [],
  f2360 r2354 [84, 85] checked_by (closedApplication (e2344 []).term (e2350 []).term (e686 []).term (e686 []).term)
    formed_by (formedResult r2354 (e2358 []) rfl),
  f2389 r2382 []
    formed_by (formedResult r2382 (e2387 []) (by decide +kernel)),
  f2394 r2390 [87]
    formed_by (formedResult r2390 (e2392 []) (by decide +kernel)),
  f2398 r2395 [86, 88] checked_by (closedTrans (e2355 []).term (e2357 []).term (e2262 []).term)
    formed_by (formedResult r2395 (e2396 []) rfl),
  f725 r716 [],
  f2404 r2399 [90, 89] checked_by (closedApplication (e212 []).term (e212 []).term (e2355 []).term (e2262 []).term)
    formed_by (formedResult r2399 (e2402 []) rfl),
  f2409 r2406 [] checked_by (closedReflexivity (e2355 []).term)
    formed_by (formedResult r2406 (e2407 []) (formedReflRequest (e2355 []))),
  f2415 r2410 [91, 92] checked_by (closedApplication (e2356 []).term (e2401 []).term (e2355 []).term (e2355 []).term)
    formed_by (formedResult r2410 (e2413 []) rfl),
  f2418 r2416 [93, 92] checked_by (closedEqMp (e2407 []).term (e2412 []).term)
    formed_by (formedResult r2416 (e2412 []) rfl),
  f2420 r2419 [94, 82] checked_by (closedEqMp (e2262 []).term (e2355 []).term)
    formed_by (formedResult r2419 (e2355 []) rfl),
  f2479 r2426 []
    formed_by (formedResult r2426 (e2477 []) (by decide +kernel)),
  f2512 r2483 [96]
    formed_by (formedResult r2483 (e2510 []) (by decide +kernel)),
  f2518 r2514 [] checked_by (closedReflexivity (e710 []).term)
    formed_by (formedResult r2514 (e2516 []) (formedReflRequest (e710 []))),
  f2523 r2519 [97, 98] checked_by (closedApplication (e690 []).term (e2509 []).term (e710 []).term (e710 []).term)
    formed_by (formedResult r2519 (e2521 []) rfl),
  f2591 r2540 []
    formed_by (formedResult r2540 (e2589 []) (by decide +kernel)),
  f2605 r2594 [100]
    formed_by (formedResult r2594 (e2603 []) (by decide +kernel)),
  f2609 r2606 [99, 101] checked_by (closedTrans (e711 []).term (e2520 []).term (e2602 []).term)
    formed_by (formedResult r2606 (e2607 []) rfl),
  f725 r716 [],
  f2614 r2610 [103, 102] checked_by (closedApplication (e212 []).term (e212 []).term (e711 []).term (e2602 []).term)
    formed_by (formedResult r2610 (e2612 []) rfl),
  f759 r2249 [],
  f2619 r2615 [104, 105] checked_by (closedApplication (e729 []).term (e2611 []).term (e711 []).term (e711 []).term)
    formed_by (formedResult r2615 (e2617 []) rfl),
  f2622 r2620 [106, 105] checked_by (closedEqMp (e757 []).term (e2616 []).term)
    formed_by (formedResult r2620 (e2616 []) rfl),
  f2625 r2624 [],
  f2629 r2626 [108, 107],
  f2631 r2630 [109, 108],
  f2625 r2624 [],
  f2625 r2624 [],
  f2635 r2632 [112, 111]
    formed_by (formedResult r2632 (e2633 []) rfl),
  f2625 r2636 [113, 112],
  f2638 r2637 [110, 114],
  f2625 r2624 [],
  f769 r765 [],
  f777 r773 [],
  f2642 r2639 [116, 118],
  f777 r773 [],
  f2644 r2643 [115, 120],
  f2650 r2645 [117, 119],
  f2656 r2651 [122, 121],
  f2890 r2657 [123],
  f1336 r1314 [],
  f3162 r2925 [125]
    formed_by (formedResult r2925 (e3160 []) (by decide +kernel)),
  f759 r2249 [],
  f3169 r3163 [126, 127] checked_by (closedApplication (e2926 []).term (e3159 []).term (e711 []).term (e711 []).term)
    formed_by (formedResult r3163 (e3167 []) rfl),
  f3263 r3255 []
    formed_by (formedResult r3255 (e3261 []) (by decide +kernel)),
  f3268 r3264 [129]
    formed_by (formedResult r3264 (e3266 []) (by decide +kernel)),
  f3272 r3269 [128, 130] checked_by (closedTrans (e3164 []).term (e3166 []).term (e2888 []).term)
    formed_by (formedResult r3269 (e3270 []) rfl),
  f725 r716 [],
  f3278 r3273 [132, 131] checked_by (closedApplication (e212 []).term (e212 []).term (e3164 []).term (e2888 []).term)
    formed_by (formedResult r3273 (e3276 []) rfl),
  f3283 r3280 [] checked_by (closedReflexivity (e3164 []).term)
    formed_by (formedResult r3280 (e3281 []) (formedReflRequest (e3164 []))),
  f3289 r3284 [133, 134] checked_by (closedApplication (e3165 []).term (e3275 []).term (e3164 []).term (e3164 []).term)
    formed_by (formedResult r3284 (e3287 []) rfl),
  f3292 r3290 [135, 134] checked_by (closedEqMp (e3281 []).term (e3286 []).term)
    formed_by (formedResult r3290 (e3286 []) rfl),
  f3294 r3293 [136, 124],
  f3296 r3295 [],
  f1336 r1314 [],
  f3162 r2925 [139],
  f759 r2249 [],
  f3169 r3163 [140, 141],
  f3263 r3255 [],
  f3268 r3264 [143],
  f3272 r3269 [142, 144],
  f3298 r3297 [145, 138],
  f1813 r1809 [],
  f3304 r3299 [146, 147],
  f3324 r3320 []
    formed_by (formedResult r3320 (e3322 []) (by decide +kernel)),
  f3330 r3325 [149]
    formed_by (formedResult r3325 (e3328 []) (by decide +kernel)),
  f1874 r1868 [],
  f3504 r3331 [151]
    formed_by (formedResult r3331 (e3502 []) (by decide +kernel)),
  f759 r2249 [],
  f3510 r3505 [152, 153] checked_by (closedApplication (e3326 []).term (e3501 []).term (e711 []).term (e711 []).term)
    formed_by (formedResult r3505 (e3508 []) rfl),
  f3521 r3517 []
    formed_by (formedResult r3517 (e3519 []) (by decide +kernel)),
  f3526 r3522 [155]
    formed_by (formedResult r3522 (e3524 []) (by decide +kernel)),
  f3530 r3527 [154, 156] checked_by (closedTrans (e3327 []).term (e3507 []).term (e2602 []).term)
    formed_by (formedResult r3527 (e3528 []) rfl),
  f3534 r3531 [150, 157] checked_by (closedTrans (e3300 []).term (e3327 []).term (e2602 []).term)
    formed_by (formedResult r3531 (e3532 []) rfl),
  f725 r716 [],
  f3539 r3535 [159, 158] checked_by (closedApplication (e212 []).term (e212 []).term (e3300 []).term (e2602 []).term)
    formed_by (formedResult r3535 (e3537 []) rfl),
  f3544 r3541 [] checked_by (closedReflexivity (e3300 []).term)
    formed_by (formedResult r3541 (e3542 []) (formedReflRequest (e3300 []))),
  f3550 r3545 [160, 161] checked_by (closedApplication (e3301 []).term (e2611 []).term (e3300 []).term (e3300 []).term)
    formed_by (formedResult r3545 (e3548 []) rfl),
  f3553 r3551 [162, 161] checked_by (closedEqMp (e3542 []).term (e3547 []).term)
    formed_by (formedResult r3551 (e3547 []) rfl),
  f2179 r2175 [],
  f2186 r2180 [164],
  f1874 r1868 [],
  f2202 r2192 [166],
  f2207 r2203 [],
  f2213 r2208 [167, 168],
  f2224 r2220 [],
  f2229 r2225 [170],
  f2233 r2230 [169, 171],
  f2237 r2234 [165, 172],
  f3557 r3554 [163, 148],
  f3559 r3558 [174, 173],
  f725 r716 [],
  f3564 r3560 [176, 175],
  f2635 r3565 [] checked_by (closedReflexivity (e2602 []).term)
    formed_by (formedResult r3565 (e2633 []) (formedReflRequest (e2602 []))),
  f3571 r3566 [177, 178],
  f3574 r3572 [179, 178],
  f777 r773 [],
  f3576 r3575 [180, 181],
  f3580 r3577 [137, 182]
    formed_by (formedResult r3577 (e3578 []) rfl),
  f2342 r2313 [],
  f3591 r3581 [184]
    formed_by (formedResult r3581 (e3589 []) (by decide +kernel)),
  f759 r2249 [],
  f3598 r3592 [185, 186] checked_by (closedApplication (e3582 []).term (e3588 []).term (e711 []).term (e711 []).term)
    formed_by (formedResult r3592 (e3596 []) rfl),
  f3616 r3609 []
    formed_by (formedResult r3609 (e3614 []) (by decide +kernel)),
  f3621 r3617 [188]
    formed_by (formedResult r3617 (e3619 []) (by decide +kernel)),
  f3625 r3622 [187, 189] checked_by (closedTrans (e3593 []).term (e3595 []).term (e3578 []).term)
    formed_by (formedResult r3622 (e3623 []) rfl),
  f725 r716 [],
  f3631 r3626 [191, 190] checked_by (closedApplication (e212 []).term (e212 []).term (e3593 []).term (e3578 []).term)
    formed_by (formedResult r3626 (e3629 []) rfl),
  f3636 r3633 [] checked_by (closedReflexivity (e3593 []).term)
    formed_by (formedResult r3633 (e3634 []) (formedReflRequest (e3593 []))),
  f3642 r3637 [192, 193] checked_by (closedApplication (e3594 []).term (e3628 []).term (e3593 []).term (e3593 []).term)
    formed_by (formedResult r3637 (e3640 []) rfl),
  f3645 r3643 [194, 193] checked_by (closedEqMp (e3634 []).term (e3639 []).term)
    formed_by (formedResult r3643 (e3639 []) rfl),
  f3647 r3646 [195, 183] checked_by (closedEqMp (e3578 []).term (e3593 []).term)
    formed_by (formedResult r3646 (e3593 []) rfl),
  f3652 r3651 [],
  f3657 r3656 [],
  f3662 r3658 [198, 197] checked_by check199,
  f3664 r3663 [199, 198],
  f3652 r3651 [],
  f3669 r3665 [201, 200],
  f3664 r3670 [202, 201] checked_by check203,
  f3672 r3671 [] checked_by (closedReflexivity (e284 []).term)
    formed_by (formedResult r3671 (e689 []) (formedReflRequest (e284 []))),
  f3657 r3656 [],
  f3676 r3673 [205, 204],
  f3678 r3677 [206, 205],
  f3652 r3651 [],
  f3682 r3679 [208, 207],
  f3684 r3683 [209, 208] checked_by check210,
  f2342 r2313 [],
  f3694 r3685 [211]
    formed_by (formedResult r3685 (e3692 []) (by decide +kernel)),
  f3700 r3696 [] checked_by (closedReflexivity (e1309 []).term)
    formed_by (formedResult r3696 (e3698 []) (formedReflRequest (e1309 []))),
  f3705 r3701 [212, 213] checked_by (closedApplication (e2503 []).term (e3691 []).term (e1309 []).term (e1309 []).term)
    formed_by (formedResult r3701 (e3703 []) rfl),
  f3723 r3715 []
    formed_by (formedResult r3715 (e3721 []) (by decide +kernel)),
  f3723 r3726 [215]
    formed_by (formedResult r3726 (e3721 []) (by decide +kernel)),
  f3730 r3727 [214, 216] checked_by (closedTrans (e3649 []).term (e3702 []).term (e3720 []).term)
    formed_by (formedResult r3727 (e3728 []) rfl),
  f3733 r3731 [217, 203],
  f725 r716 [],
  f3739 r3734 [219, 218],
  f3744 r3741 [] checked_by (closedReflexivity (e3718 []).term)
    formed_by (formedResult r3741 (e3742 []) (formedReflRequest (e3718 []))),
  f3750 r3745 [220, 221],
  f3753 r3751 [222, 221],
  f3755 r3754 [223, 210],
  f1336 r1314 [],
  f3766 r3756 [225]
    formed_by (formedResult r3756 (e3764 []) (by decide +kernel)),
  f3700 r3696 [],
  f3771 r3767 [226, 227] checked_by (closedApplication (e3687 []).term (e3763 []).term (e1309 []).term (e1309 []).term)
    formed_by (formedResult r3767 (e3769 []) rfl),
  f3791 r3782 []
    formed_by (formedResult r3782 (e3789 []) (by decide +kernel)),
  f3791 r3792 [229]
    formed_by (formedResult r3792 (e3789 []) (by decide +kernel)),
  f3796 r3793 [228, 230] checked_by (closedTrans (e3718 []).term (e3768 []).term (e3788 []).term)
    formed_by (formedResult r3793 (e3794 []) rfl),
  f3799 r3797 [231, 224],
  f3806 r3802 [] checked_by (closedReflexivity (e3800 []).term)
    formed_by (formedResult r3802 (e3804 []) (formedReflRequest (e3800 []))),
  f3813 r3807 [232, 233],
  f3826 r3820 []
    formed_by (formedResult r3820 (e3824 []) (by decide +kernel)),
  f3835 r3830 [235]
    formed_by (formedResult r3830 (e3833 []) (by decide +kernel)),
  f3845 r3841 []
    formed_by (formedResult r3841 (e3843 []) (by decide +kernel)),
  f3850 r3846 [237]
    formed_by (formedResult r3846 (e3848 []) (by decide +kernel)),
  f3700 r3696 [],
  f3856 r3851 [238, 239] checked_by (closedApplication (e3831 []).term (e206 []).term (e1309 []).term (e1309 []).term)
    formed_by (formedResult r3851 (e3854 []) rfl),
  f3865 r3861 []
    formed_by (formedResult r3861 (e3863 []) (by decide +kernel)),
  f3865 r3866 [241]
    formed_by (formedResult r3866 (e3863 []) (by decide +kernel)),
  f3870 r3867 [240, 242] checked_by (closedTrans (e3832 []).term (e3853 []).term (e1309 []).term)
    formed_by (formedResult r3867 (e3868 []) rfl),
  f3874 r3871 [236, 243] checked_by (closedTrans (e3808 []).term (e3832 []).term (e1309 []).term)
    formed_by (formedResult r3871 (e3872 []) rfl),
  f725 r716 [],
  f3879 r3875 [245, 244] checked_by (closedApplication (e212 []).term (e212 []).term (e3808 []).term (e1309 []).term)
    formed_by (formedResult r3875 (e3877 []) rfl),
  f3884 r3881 [] checked_by (closedReflexivity (e3808 []).term)
    formed_by (formedResult r3881 (e3882 []) (formedReflRequest (e3808 []))),
  f3890 r3885 [246, 247] checked_by (closedApplication (e3809 []).term (e3697 []).term (e3808 []).term (e3808 []).term)
    formed_by (formedResult r3885 (e3888 []) rfl),
  f3893 r3891 [248, 247] checked_by (closedEqMp (e3882 []).term (e3887 []).term)
    formed_by (formedResult r3891 (e3887 []) rfl),
  f2179 r2175 [],
  f3900 r3894 [250]
    formed_by (formedResult r3894 (e3898 []) (by decide +kernel)),
  f3845 r3841 [],
  f3905 r3901 [252]
    formed_by (formedResult r3901 (e3903 []) (by decide +kernel)),
  f2207 r2203 [],
  f3911 r3906 [253, 254] checked_by (closedApplication (e3896 []).term (e206 []).term (e208 []).term (e208 []).term)
    formed_by (formedResult r3906 (e3909 []) rfl),
  f3865 r3861 [],
  f3916 r3912 [256]
    formed_by (formedResult r3912 (e3914 []) (by decide +kernel)),
  f3920 r3917 [255, 257] checked_by (closedTrans (e3897 []).term (e3908 []).term (e208 []).term)
    formed_by (formedResult r3917 (e3918 []) rfl),
  f3924 r3921 [251, 258] checked_by (closedTrans (e3810 []).term (e3897 []).term (e208 []).term)
    formed_by (formedResult r3921 (e3922 []) rfl),
  f3928 r3925 [249, 234],
  f3932 r3929 [260, 259],
  f725 r716 [],
  f3937 r3933 [262, 261],
  f3700 r3696 [],
  f3943 r3938 [263, 264],
  f3946 r3944 [265, 264],
  f777 r773 [],
  f3948 r3947 [266, 267],
  f3657 r3656 [],
  f3952 r3949 [269, 268] checked_by check270,
  f3948 r3953 [270, 269],
  f3652 r3651 [],
  f3957 r3954 [272, 271],
  f3948 r3958 [273, 272] checked_by check274,
  f3657 r3656 [],
  f3964 r3960 [] checked_by (closedReflexivity (e3815 []).term)
    formed_by (formedResult r3960 (e3962 []) (formedReflRequest (e3815 []))),
  f777 r773 [],
  f3968 r3965 [275, 277],
  f777 r773 [],
  f3932 r3969 [274, 279],
  f3976 r3970 [276, 278],
  f3983 r3977 [281, 280],
  f4021 r3984 [282],
  f1336 r1314 [],
  f4067 r4026 [284]
    formed_by (formedResult r4026 (e4065 []) (by decide +kernel)),
  f3700 r3696 [],
  f4074 r4068 [285, 286] checked_by (closedApplication (e4027 []).term (e4064 []).term (e1309 []).term (e1309 []).term)
    formed_by (formedResult r4068 (e4072 []) rfl),
  f4097 r4088 []
    formed_by (formedResult r4088 (e4095 []) (by decide +kernel)),
  f4102 r4098 [288]
    formed_by (formedResult r4098 (e4100 []) (by decide +kernel)),
  f4106 r4103 [287, 289] checked_by (closedTrans (e4069 []).term (e4071 []).term (e4019 []).term)
    formed_by (formedResult r4103 (e4104 []) rfl),
  f725 r716 [],
  f4112 r4107 [291, 290] checked_by (closedApplication (e212 []).term (e212 []).term (e4069 []).term (e4019 []).term)
    formed_by (formedResult r4107 (e4110 []) rfl),
  f4117 r4114 [] checked_by (closedReflexivity (e4069 []).term)
    formed_by (formedResult r4114 (e4115 []) (formedReflRequest (e4069 []))),
  f4123 r4118 [292, 293] checked_by (closedApplication (e4070 []).term (e4109 []).term (e4069 []).term (e4069 []).term)
    formed_by (formedResult r4118 (e4121 []) rfl),
  f4126 r4124 [294, 293] checked_by (closedEqMp (e4115 []).term (e4120 []).term)
    formed_by (formedResult r4124 (e4120 []) rfl),
  f4128 r4127 [295, 283],
  f4130 r4129 [],
  f1336 r1314 [],
  f4067 r4026 [298],
  f3700 r3696 [],
  f4074 r4068 [299, 300],
  f4097 r4088 [],
  f4102 r4098 [302],
  f4106 r4103 [301, 303],
  f4132 r4131 [304, 297],
  f1813 r1809 [],
  f4138 r4133 [305, 306],
  f4152 r4148 []
    formed_by (formedResult r4148 (e4150 []) (by decide +kernel)),
  f4158 r4153 [308]
    formed_by (formedResult r4153 (e4156 []) (by decide +kernel)),
  f1874 r1868 [],
  f4165 r4159 [310]
    formed_by (formedResult r4159 (e4163 []) (by decide +kernel)),
  f3700 r3696 [],
  f4171 r4166 [311, 312] checked_by (closedApplication (e4154 []).term (e4162 []).term (e1309 []).term (e1309 []).term)
    formed_by (formedResult r4166 (e4169 []) rfl),
  f4182 r4178 []
    formed_by (formedResult r4178 (e4180 []) (by decide +kernel)),
  f4187 r4183 [314]
    formed_by (formedResult r4183 (e4185 []) (by decide +kernel)),
  f4191 r4188 [313, 315] checked_by (closedTrans (e4155 []).term (e4168 []).term (e3654 []).term)
    formed_by (formedResult r4188 (e4189 []) rfl),
  f4195 r4192 [309, 316] checked_by (closedTrans (e4134 []).term (e4155 []).term (e3654 []).term)
    formed_by (formedResult r4192 (e4193 []) rfl),
  f725 r716 [],
  f4200 r4196 [318, 317] checked_by (closedApplication (e212 []).term (e212 []).term (e4134 []).term (e3654 []).term)
    formed_by (formedResult r4196 (e4198 []) rfl),
  f4205 r4202 [] checked_by (closedReflexivity (e4134 []).term)
    formed_by (formedResult r4202 (e4203 []) (formedReflRequest (e4134 []))),
  f4211 r4206 [319, 320] checked_by (closedApplication (e4135 []).term (e3659 []).term (e4134 []).term (e4134 []).term)
    formed_by (formedResult r4206 (e4209 []) rfl),
  f4214 r4212 [321, 320] checked_by (closedEqMp (e4203 []).term (e4208 []).term)
    formed_by (formedResult r4212 (e4208 []) rfl),
  f2179 r2175 [],
  f2186 r2180 [323],
  f1874 r1868 [],
  f2202 r2192 [325],
  f2207 r2203 [],
  f2213 r2208 [326, 327],
  f2224 r2220 [],
  f2229 r2225 [329],
  f2233 r2230 [328, 330],
  f2237 r2234 [324, 331],
  f4218 r4215 [322, 307],
  f4220 r4219 [333, 332],
  f725 r716 [],
  f4225 r4221 [335, 334],
  f4229 r4226 [] checked_by (closedReflexivity (e3654 []).term)
    formed_by (formedResult r4226 (e4227 []) (formedReflRequest (e3654 []))),
  f4235 r4230 [336, 337],
  f4238 r4236 [338, 337],
  f777 r773 [],
  f4240 r4239 [339, 340],
  f4244 r4241 [296, 341],
  f2342 r2313 [],
  f4255 r4245 [343]
    formed_by (formedResult r4245 (e4253 []) (by decide +kernel)),
  f3700 r3696 [],
  f4262 r4256 [344, 345] checked_by (closedApplication (e4246 []).term (e4252 []).term (e1309 []).term (e1309 []).term)
    formed_by (formedResult r4256 (e4260 []) rfl),
  f4280 r4273 []
    formed_by (formedResult r4273 (e4278 []) (by decide +kernel)),
  f4285 r4281 [347]
    formed_by (formedResult r4281 (e4283 []) (by decide +kernel)),
  f4289 r4286 [346, 348] checked_by (closedTrans (e4257 []).term (e4259 []).term (e4242 []).term)
    formed_by (formedResult r4286 (e4287 []) rfl),
  f725 r716 [],
  f4295 r4290 [350, 349] checked_by (closedApplication (e212 []).term (e212 []).term (e4257 []).term (e4242 []).term)
    formed_by (formedResult r4290 (e4293 []) rfl),
  f4300 r4297 [] checked_by (closedReflexivity (e4257 []).term)
    formed_by (formedResult r4297 (e4298 []) (formedReflRequest (e4257 []))),
  f4306 r4301 [351, 352] checked_by (closedApplication (e4258 []).term (e4292 []).term (e4257 []).term (e4257 []).term)
    formed_by (formedResult r4301 (e4304 []) rfl),
  f4309 r4307 [353, 352] checked_by (closedEqMp (e4298 []).term (e4303 []).term)
    formed_by (formedResult r4307 (e4303 []) rfl),
  f4311 r4310 [354, 342],
  f3652 r3651 [],
  f4315 r4312 [356, 355],
  f4311 r4316 [357, 356],
  f3652 r3651 [],
  f3964 r3960 [],
  f777 r773 [],
  f4320 r4317 [359, 361],
  f777 r773 [],
  f4324 r4321 [358, 363],
  f4330 r4325 [360, 362],
  f4336 r4331 [365, 364],
  f4348 r4337 [366],
  f1336 r1314 [],
  f4366 r4353 [368]
    formed_by (formedResult r4353 (e4364 []) (by decide +kernel)),
  f4300 r4297 [],
  f4373 r4367 [369, 370] checked_by (closedApplication (e4354 []).term (e4363 []).term (e4257 []).term (e4257 []).term)
    formed_by (formedResult r4367 (e4371 []) rfl),
  f4394 r4386 []
    formed_by (formedResult r4386 (e4392 []) (by decide +kernel)),
  f4403 r4399 [372]
    formed_by (formedResult r4399 (e4401 []) (by decide +kernel)),
  f4407 r4404 [371, 373] checked_by (closedTrans (e4368 []).term (e4370 []).term (e4346 []).term)
    formed_by (formedResult r4404 (e4405 []) rfl),
  f725 r716 [],
  f4413 r4408 [375, 374] checked_by (closedApplication (e212 []).term (e212 []).term (e4368 []).term (e4346 []).term)
    formed_by (formedResult r4408 (e4411 []) rfl),
  f4418 r4415 [] checked_by (closedReflexivity (e4368 []).term)
    formed_by (formedResult r4415 (e4416 []) (formedReflRequest (e4368 []))),
  f4424 r4419 [376, 377] checked_by (closedApplication (e4369 []).term (e4410 []).term (e4368 []).term (e4368 []).term)
    formed_by (formedResult r4419 (e4422 []) rfl),
  f4427 r4425 [378, 377] checked_by (closedEqMp (e4416 []).term (e4421 []).term)
    formed_by (formedResult r4425 (e4421 []) rfl),
  f4429 r4428 [379, 367],
  f4431 r4430 [],
  f1336 r1314 [],
  f4366 r4353 [382],
  f4300 r4297 [],
  f4373 r4367 [383, 384],
  f4394 r4386 [],
  f4403 r4399 [386],
  f4407 r4404 [385, 387],
  f4433 r4432 [388, 381],
  f1813 r1809 [],
  f4439 r4434 [389, 390],
  f4455 r4451 []
    formed_by (formedResult r4451 (e4453 []) (by decide +kernel)),
  f4461 r4456 [392]
    formed_by (formedResult r4456 (e4459 []) (by decide +kernel)),
  f1874 r1868 [],
  f4468 r4462 [394]
    formed_by (formedResult r4462 (e4466 []) (by decide +kernel)),
  f4300 r4297 [],
  f4474 r4469 [395, 396] checked_by (closedApplication (e4457 []).term (e4465 []).term (e4257 []).term (e4257 []).term)
    formed_by (formedResult r4469 (e4472 []) rfl),
  f4485 r4481 []
    formed_by (formedResult r4481 (e4483 []) (by decide +kernel)),
  f4490 r4486 [398]
    formed_by (formedResult r4486 (e4488 []) (by decide +kernel)),
  f4494 r4491 [397, 399] checked_by (closedTrans (e4458 []).term (e4471 []).term (e3649 []).term)
    formed_by (formedResult r4491 (e4492 []) rfl),
  f4498 r4495 [393, 400] checked_by (closedTrans (e4435 []).term (e4458 []).term (e3649 []).term)
    formed_by (formedResult r4495 (e4496 []) rfl),
  f725 r716 [],
  f4503 r4499 [402, 401] checked_by (closedApplication (e212 []).term (e212 []).term (e4435 []).term (e3649 []).term)
    formed_by (formedResult r4499 (e4501 []) rfl),
  f4508 r4505 [] checked_by (closedReflexivity (e4435 []).term)
    formed_by (formedResult r4505 (e4506 []) (formedReflRequest (e4435 []))),
  f4514 r4509 [403, 404] checked_by (closedApplication (e4436 []).term (e3666 []).term (e4435 []).term (e4435 []).term)
    formed_by (formedResult r4509 (e4512 []) rfl),
  f4517 r4515 [405, 404] checked_by (closedEqMp (e4506 []).term (e4511 []).term)
    formed_by (formedResult r4515 (e4511 []) rfl),
  f2179 r2175 [],
  f2186 r2180 [407],
  f1874 r1868 [],
  f2202 r2192 [409],
  f2207 r2203 [],
  f2213 r2208 [410, 411],
  f2224 r2220 [],
  f2229 r2225 [413],
  f2233 r2230 [412, 414],
  f2237 r2234 [408, 415],
  f4521 r4518 [406, 391],
  f4523 r4522 [417, 416],
  f725 r716 [],
  f4528 r4524 [419, 418],
  f4530 r4529 [] checked_by (closedReflexivity (e3649 []).term)
    formed_by (formedResult r4529 (e3667 []) (formedReflRequest (e3649 []))),
  f4536 r4531 [420, 421],
  f4539 r4537 [422, 421],
  f777 r773 [],
  f4541 r4540 [423, 424],
  f4545 r4542 [380, 425]
    formed_by (formedResult r4542 (e4543 []) rfl),
  f2342 r2313 [],
  f4556 r4546 [427]
    formed_by (formedResult r4546 (e4554 []) (by decide +kernel)),
  f4300 r4297 [],
  f4563 r4557 [428, 429] checked_by (closedApplication (e4547 []).term (e4553 []).term (e4257 []).term (e4257 []).term)
    formed_by (formedResult r4557 (e4561 []) rfl),
  f4581 r4574 []
    formed_by (formedResult r4574 (e4579 []) (by decide +kernel)),
  f4586 r4582 [431]
    formed_by (formedResult r4582 (e4584 []) (by decide +kernel)),
  f4590 r4587 [430, 432] checked_by (closedTrans (e4558 []).term (e4560 []).term (e4543 []).term)
    formed_by (formedResult r4587 (e4588 []) rfl),
  f725 r716 [],
  f4596 r4591 [434, 433] checked_by (closedApplication (e212 []).term (e212 []).term (e4558 []).term (e4543 []).term)
    formed_by (formedResult r4591 (e4594 []) rfl),
  f4601 r4598 [] checked_by (closedReflexivity (e4558 []).term)
    formed_by (formedResult r4598 (e4599 []) (formedReflRequest (e4558 []))),
  f4607 r4602 [435, 436] checked_by (closedApplication (e4559 []).term (e4593 []).term (e4558 []).term (e4558 []).term)
    formed_by (formedResult r4602 (e4605 []) rfl),
  f4610 r4608 [437, 436] checked_by (closedEqMp (e4599 []).term (e4604 []).term)
    formed_by (formedResult r4608 (e4604 []) rfl),
  f4612 r4611 [438, 426] checked_by (closedEqMp (e4543 []).term (e4558 []).term)
    formed_by (formedResult r4611 (e4558 []) rfl),
  f777 r773 [],
  f4616 r4613 [439, 440]
    formed_by (formedResult r4613 (e4614 []) rfl),
  f4621 r4617 [441]
    formed_by (formedResult r4617 (e4619 []) (by decide +kernel)),
  f4634 r4628 []
    formed_by (formedResult r4628 (e4632 []) (by decide +kernel)),
  f4641 r4638 [443]
    formed_by (formedResult r4638 (e4639 []) (by decide +kernel)),
  f725 r716 [],
  f4646 r4642 [445, 444] checked_by (closedApplication (e212 []).term (e212 []).term (e2602 []).term (e4619 []).term)
    formed_by (formedResult r4642 (e4644 []) rfl),
  f2635 r3565 [],
  f4651 r4647 [446, 447] checked_by (closedApplication (e2611 []).term (e4643 []).term (e2602 []).term (e2602 []).term)
    formed_by (formedResult r4647 (e4649 []) rfl),
  f4654 r4652 [448, 447] checked_by (closedEqMp (e2633 []).term (e4648 []).term)
    formed_by (formedResult r4652 (e4648 []) rfl),
  f4656 r4655 [449, 442] checked_by (closedEqMp (e4619 []).term (e2602 []).term)
    formed_by (formedResult r4655 (e2602 []) rfl),
  f2342 r2313 [],
  f3591 r3581 [451],
  f759 r2249 [],
  f3598 r3592 [452, 453],
  f3616 r3609 [],
  f3621 r3617 [455],
  f3625 r3622 [454, 456],
  f3580 r4657 [457, 196] checked_by (closedEqMp (e3593 []).term (e3578 []).term)
    formed_by (formedResult r4657 (e3578 []) rfl),
  f725 r716 [],
  f4661 r4658 [459, 458] checked_by (closedApplication (e212 []).term (e212 []).term (e3164 []).term (e2602 []).term)
    formed_by (formedResult r4658 (e4659 []) rfl),
  f3283 r3280 [],
  f4666 r4662 [460, 461] checked_by (closedApplication (e3165 []).term (e2611 []).term (e3164 []).term (e3164 []).term)
    formed_by (formedResult r4662 (e4664 []) rfl),
  f4669 r4667 [462, 461] checked_by (closedEqMp (e3281 []).term (e4663 []).term)
    formed_by (formedResult r4667 (e4663 []) rfl),
  f4671 r4670 [463, 450] checked_by (closedEqMp (e2602 []).term (e3164 []).term)
    formed_by (formedResult r4670 (e3164 []) rfl),
  f1336 r1314 [],
  f3162 r2925 [465],
  f759 r2249 [],
  f3169 r3163 [466, 467],
  f3263 r3255 [],
  f3268 r3264 [469],
  f3272 r3269 [468, 470],
  f4673 r4672 [471, 464] checked_by (closedEqMp (e3164 []).term (e2888 []).term)
    formed_by (formedResult r4672 (e2888 []) rfl),
  f3806 r3802 [],
  f4679 r4674 [472, 473] checked_by (closedApplication (e2886 []).term (e237 []).term (e3800 []).term (e3800 []).term)
    formed_by (formedResult r4674 (e4677 []) rfl),
  f3324 r3320 [],
  f4685 r4680 [475]
    formed_by (formedResult r4680 (e4683 []) (by decide +kernel)),
  f3845 r3841 [],
  f4690 r4686 [477]
    formed_by (formedResult r4686 (e4688 []) (by decide +kernel)),
  f759 r2249 [],
  f4696 r4691 [478, 479] checked_by (closedApplication (e4681 []).term (e206 []).term (e711 []).term (e711 []).term)
    formed_by (formedResult r4691 (e4694 []) rfl),
  f3865 r3861 [],
  f4701 r4697 [481]
    formed_by (formedResult r4697 (e4699 []) (by decide +kernel)),
  f4705 r4702 [480, 482] checked_by (closedTrans (e4682 []).term (e4693 []).term (e711 []).term)
    formed_by (formedResult r4702 (e4703 []) rfl),
  f4709 r4706 [476, 483] checked_by (closedTrans (e4675 []).term (e4682 []).term (e711 []).term)
    formed_by (formedResult r4706 (e4707 []) rfl),
  f725 r716 [],
  f4714 r4710 [485, 484] checked_by (closedApplication (e212 []).term (e212 []).term (e4675 []).term (e711 []).term)
    formed_by (formedResult r4710 (e4712 []) rfl),
  f4719 r4716 [] checked_by (closedReflexivity (e4675 []).term)
    formed_by (formedResult r4716 (e4717 []) (formedReflRequest (e4675 []))),
  f4725 r4720 [486, 487] checked_by (closedApplication (e4676 []).term (e729 []).term (e4675 []).term (e4675 []).term)
    formed_by (formedResult r4720 (e4723 []) rfl),
  f4728 r4726 [488, 487] checked_by (closedEqMp (e4717 []).term (e4722 []).term)
    formed_by (formedResult r4726 (e4722 []) rfl),
  f2179 r2175 [],
  f3900 r3894 [490],
  f3845 r3841 [],
  f3905 r3901 [492],
  f2207 r2203 [],
  f3911 r3906 [493, 494],
  f3865 r3861 [],
  f3916 r3912 [496],
  f3920 r3917 [495, 497],
  f3924 r3921 [491, 498],
  f4732 r4729 [489, 474] checked_by (closedTrans (e711 []).term (e4675 []).term (e3810 []).term)
    formed_by (formedResult r4729 (e4730 []) rfl),
  f4734 r4733 [500, 499] checked_by (closedTrans (e711 []).term (e3810 []).term (e208 []).term)
    formed_by (formedResult r4733 (e779 []) rfl),
  f725 r716 [],
  f4736 r4735 [502, 501] checked_by (closedApplication (e212 []).term (e212 []).term (e711 []).term (e208 []).term)
    formed_by (formedResult r4735 (e2246 []) rfl),
  f759 r2249 [],
  f4738 r4737 [503, 504] checked_by (closedApplication (e729 []).term (e2204 []).term (e711 []).term (e711 []).term)
    formed_by (formedResult r4737 (e2253 []) rfl),
  f4740 r4739 [505, 504] checked_by (closedEqMp (e757 []).term (e2252 []).term)
    formed_by (formedResult r4739 (e2252 []) rfl),
  f777 r773 [],
  f4742 r4741 [506, 507] checked_by (closedEqMp (e208 []).term (e711 []).term)
    formed_by (formedResult r4741 (e711 []) rfl),
  f2342 r2313 [],
  f2353 r2343 [509],
  f737 r734 [],
  f2360 r2354 [510, 511],
  f2389 r2382 [],
  f2394 r2390 [513],
  f2398 r2395 [512, 514],
  f2264 r4743 [515, 95] checked_by (closedEqMp (e2355 []).term (e2262 []).term)
    formed_by (formedResult r4743 (e2262 []) rfl),
  f725 r716 [],
  f4747 r4744 [517, 516] checked_by (closedApplication (e212 []).term (e212 []).term (e1656 []).term (e711 []).term)
    formed_by (formedResult r4744 (e4745 []) rfl),
  f1789 r1786 [],
  f4752 r4748 [518, 519] checked_by (closedApplication (e1657 []).term (e729 []).term (e1656 []).term (e1656 []).term)
    formed_by (formedResult r4748 (e4750 []) rfl),
  f4755 r4753 [520, 519] checked_by (closedEqMp (e1787 []).term (e4749 []).term)
    formed_by (formedResult r4753 (e4749 []) rfl),
  f4757 r4756 [521, 508] checked_by (closedEqMp (e711 []).term (e1656 []).term)
    formed_by (formedResult r4756 (e1656 []) rfl),
  f1336 r1314 [],
  f1654 r1408 [523],
  f737 r734 [],
  f1661 r1655 [524, 525],
  f1766 r1757 [],
  f1774 r1770 [527],
  f1778 r1775 [526, 528],
  f4759 r4758 [529, 522] checked_by (closedEqMp (e1656 []).term (e1274 []).term)
    formed_by (formedResult r4758 (e1274 []) rfl),
  f3806 r3802 [],
  f4765 r4760 [530, 531] checked_by (closedApplication (e1264 []).term (e237 []).term (e3800 []).term (e3800 []).term)
    formed_by (formedResult r4760 (e4763 []) rfl),
  f1852 r1848 [],
  f4771 r4766 [533]
    formed_by (formedResult r4766 (e4769 []) (by decide +kernel)),
  f3845 r3841 [],
  f4776 r4772 [535]
    formed_by (formedResult r4772 (e4774 []) (by decide +kernel)),
  f737 r734 [],
  f4782 r4777 [536, 537] checked_by (closedApplication (e4767 []).term (e206 []).term (e686 []).term (e686 []).term)
    formed_by (formedResult r4777 (e4780 []) rfl),
  f3865 r3861 [],
  f4787 r4783 [539]
    formed_by (formedResult r4783 (e4785 []) (by decide +kernel)),
  f4791 r4788 [538, 540] checked_by (closedTrans (e4768 []).term (e4779 []).term (e686 []).term)
    formed_by (formedResult r4788 (e4789 []) rfl),
  f4795 r4792 [534, 541] checked_by (closedTrans (e4761 []).term (e4768 []).term (e686 []).term)
    formed_by (formedResult r4792 (e4793 []) rfl),
  f725 r716 [],
  f4800 r4796 [543, 542] checked_by (closedApplication (e212 []).term (e212 []).term (e4761 []).term (e686 []).term)
    formed_by (formedResult r4796 (e4798 []) rfl),
  f4805 r4802 [] checked_by (closedReflexivity (e4761 []).term)
    formed_by (formedResult r4802 (e4803 []) (formedReflRequest (e4761 []))),
  f4811 r4806 [544, 545] checked_by (closedApplication (e4762 []).term (e687 []).term (e4761 []).term (e4761 []).term)
    formed_by (formedResult r4806 (e4809 []) rfl),
  f4814 r4812 [546, 545] checked_by (closedEqMp (e4803 []).term (e4808 []).term)
    formed_by (formedResult r4812 (e4808 []) rfl),
  f2179 r2175 [],
  f3900 r3894 [548],
  f3845 r3841 [],
  f3905 r3901 [550],
  f2207 r2203 [],
  f3911 r3906 [551, 552],
  f3865 r3861 [],
  f3916 r3912 [554],
  f3920 r3917 [553, 555],
  f3924 r3921 [549, 556],
  f4818 r4815 [547, 532] checked_by (closedTrans (e686 []).term (e4761 []).term (e3810 []).term)
    formed_by (formedResult r4815 (e4816 []) rfl),
  f4820 r4819 [558, 557] checked_by (closedTrans (e686 []).term (e3810 []).term (e208 []).term)
    formed_by (formedResult r4819 (e783 []) rfl),
  f725 r716 [],
  f4824 r4821 [560, 559] checked_by (closedApplication (e212 []).term (e212 []).term (e686 []).term (e208 []).term)
    formed_by (formedResult r4821 (e4822 []) rfl),
  f737 r734 [],
  f4829 r4825 [561, 562] checked_by (closedApplication (e687 []).term (e2204 []).term (e686 []).term (e686 []).term)
    formed_by (formedResult r4825 (e4827 []) rfl),
  f4832 r4830 [563, 562] checked_by (closedEqMp (e735 []).term (e4826 []).term)
    formed_by (formedResult r4830 (e4826 []) rfl),
  f777 r773 [],
  f4834 r4833 [564, 565] checked_by (closedEqMp (e208 []).term (e686 []).term)
    formed_by (formedResult r4833 (e686 []) rfl)
]

def result : Theorem := f4834
def certificate : ProofSystem.Certificate := (witnessTrace_suffix0, 566)
theorem accepted : (ProofSystem.checker emptyAxiomPolicy).check result certificate = true := by
  apply (ProofSystem.checker_check_iff emptyAxiomPolicy _ _).mpr
  exact ⟨witnessTrace_cache567, witnessTrace_trace0.replayed, rfl⟩
theorem graph_formed : certificate.1.all nodeFormed = true := witnessTrace_trace0.formed
#print axioms accepted
#print axioms graph_formed
end Mettapedia.Languages.HOLLight.PointedPredicateTemplate

namespace Mettapedia.Languages.HOLLight.PointedPredicateTemplate
open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open ReverseTranslation DefinitionAdapters SignatureFormation

def alphaName : Name := Name.global "PointedCarrierElement"
def alpha : AtomicTy := ⟨.var alphaName,⟨rfl,rfl⟩⟩
def element : HOL.Ty AtomicTy := .base alpha
def propertyVariable : SourceVar := ⟨Name.global "pointedCarrierProperty",Ty.function (.var alphaName) Ty.bool⟩
def property : HOL.ClosedTerm Symbol (.arr element .prop) :=
  .const (.variable propertyVariable (by
    change (Ty.function (.var alphaName) Ty.bool).toHOL = HOL.Ty.arr (HOL.Ty.base alpha) HOL.Ty.prop
    rw [Ty.toHOL_function,Ty.toHOL_bool]
    exact congrArg (fun source => HOL.Ty.arr source HOL.Ty.prop) (Ty.toHOL_of_isAtomic alpha.property)))

theorem exact_conclusion : result.sequent.concl =
    reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand
      (.app (HOL.PointedPredicate.predicate property) (HOL.PointedPredicate.none element))) := by
  apply CanonicalTerm.ext_term
  exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

theorem no_hypotheses : result.sequent.hyp = ∅ := rfl
theorem no_axioms : result.axioms = ∅ := rfl

theorem nodes_formed : ∀ node ∈ certificate.1,
    ProofExecution.Registered.requestFormedB ContextControls.coreContext.signature
      (ExportReplay.instanceCertificates ContextControls.coreContext.signature) node.witness = true ∧
    theoremFormedB ContextControls.coreContext.signature
      (ExportReplay.instanceCertificates ContextControls.coreContext.signature) node.conclusion = true := by
  intro node member
  have checked := (List.all_eq_true.mp graph_formed) node member
  change (ProofExecution.Registered.requestFormedB ContextControls.coreContext.signature
    (ExportReplay.instanceCertificates ContextControls.coreContext.signature) node.witness &&
    theoremFormedB ContextControls.coreContext.signature
      (ExportReplay.instanceCertificates ContextControls.coreContext.signature) node.conclusion) = true at checked
  simpa only [Bool.and_eq_true] using checked

#print axioms exact_conclusion
#print axioms no_hypotheses
#print axioms no_axioms
#print axioms nodes_formed

theorem result_in_graph : ∃ node ∈ certificate.1, node.conclusion = result := by
  have bound : certificate.2 < certificate.1.length := by decide +kernel
  exact ⟨certificate.1[certificate.2], List.getElem_mem bound, rfl⟩

theorem result_formed : TheoremFormed ContextControls.coreContext.signature result := by
  obtain ⟨node,member,equal⟩ := result_in_graph
  exact equal ▸ theoremFormedB_sound _ _ (nodes_formed node member).2

#print axioms result_in_graph
#print axioms result_formed
end Mettapedia.Languages.HOLLight.PointedPredicateTemplate
