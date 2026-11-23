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
private def e201 : HOL.Term Symbol [h189, h173, h173, h183] h198 := .const (.constant Const.equality t6 q199)
private def e202 : HOL.Term Symbol [h189, h173, h173, h183] h189 := .var (HOL.Var.vz)
private def e203 : HOL.Term Symbol [h189, h173, h173, h183] h195 := .app e201 e202
private def e204 : HOL.Term Symbol [h173, h189, h173, h173, h183] h198 := .const (.constant Const.equality t6 q199)
private def e205 : HOL.Term Symbol [h173, h173, h189, h173, h173, h183] h173 := .var (HOL.Var.vz)
private def e206 : HOL.Term Symbol [h173, h189, h173, h173, h183] h189 := .lam e205
private def e207 : HOL.Term Symbol [h173, h189, h173, h173, h183] h195 := .app e204 e206
private def e208 : HOL.Term Symbol [h173, h189, h173, h173, h183] h173 := .app e207 e206
private def e209 : HOL.Term Symbol [h189, h173, h173, h183] h189 := .lam e208
private def e210 : HOL.Term Symbol [h189, h173, h173, h183] h173 := .app e203 e209
private def e211 : HOL.Term Symbol [h173, h173, h183] h195 := .lam e210
private def e212 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183] h192 := .const (.constant Const.equality t17 q193)
private def h213 : HOL.Ty AtomicTy := HOL.Ty.arr h192 h173
private theorem q214 : t19.toHOL = h213 := (Ty.toHOL_function t17 t1).trans (congrArg₂ HOL.Ty.arr q193 q174)
private theorem v215 : ReverseTranslation.reverseTy h213 = t19 := (ReverseTranslation.reverseTy_eq_iff).mpr q214.symm
private def h216 : HOL.Ty AtomicTy := HOL.Ty.arr h213 h173
private theorem q217 : t20.toHOL = h216 := (Ty.toHOL_function t19 t1).trans (congrArg₂ HOL.Ty.arr q214 q174)
private theorem v218 : ReverseTranslation.reverseTy h216 = t20 := (ReverseTranslation.reverseTy_eq_iff).mpr q217.symm
private def h219 : HOL.Ty AtomicTy := HOL.Ty.arr h213 h216
private theorem q220 : t21.toHOL = h219 := (Ty.toHOL_function t19 t20).trans (congrArg₂ HOL.Ty.arr q214 q217)
private theorem v221 : ReverseTranslation.reverseTy h219 = t21 := (ReverseTranslation.reverseTy_eq_iff).mpr q220.symm
private def e222 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h183] h219 := .const (.constant Const.equality t21 q220)
private def e223 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183] h192 := .var (HOL.Var.vz)
private def e224 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e225 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183] h189 := .app e223 e224
private def e226 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e227 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183] h173 := .app e225 e226
private def e228 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h183] h213 := .lam e227
private def e229 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h183] h216 := .app e222 e228
private def e230 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183] h198 := .const (.constant Const.equality t6 q199)
private def e231 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h183] h173 := .var (HOL.Var.vz)
private def e232 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183] h189 := .lam e231
private def e233 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183] h195 := .app e230 e232
private def e234 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183] h173 := .app e233 e232
private def e235 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183] h189 := .app e223 e234
private def e236 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183] h173 := .app e235 e234
private def e237 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h183] h213 := .lam e236
private def e238 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h183] h173 := .app e229 e237
private def e239 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h183] h189 := .lam e238
private def e240 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183] h192 := .lam e239
private def e241 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e242 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183] h189 := .app e240 e241
private def e243 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183] h173 := .var (HOL.Var.vz)
private def e244 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183] h173 := .app e242 e243
private def e245 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183] h189 := .app e212 e244
private def e246 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183] h173 := .app e245 e241
private def e247 : HOL.Term Symbol [h173, h173, h173, h173, h183] h189 := .lam e246
private def e248 : HOL.Term Symbol [h173, h173, h173, h183] h192 := .lam e247
private def e249 : HOL.Term Symbol [h173, h173, h173, h183] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e250 : HOL.Term Symbol [h173, h173, h173, h183] h189 := .app e248 e249
private def e251 : HOL.Term Symbol [h173, h173, h173, h183] h173 := .var (HOL.Var.vz)
private def e252 : HOL.Term Symbol [h173, h173, h173, h183] h173 := .app e250 e251
private def e253 : HOL.Term Symbol [h173, h173, h173, h183] h189 := .app e248 e252
private def e254 : HOL.Term Symbol [h173, h173, h173, h183] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e255 : HOL.Term Symbol [h173, h173, h173, h183] h189 := .app e248 e254
private def e256 : HOL.Term Symbol [h173, h173, h173, h183] h173 := .app e255 e251
private def e257 : HOL.Term Symbol [h173, h173, h173, h183] h189 := .app e248 e256
private def e258 : HOL.Term Symbol [h173, h173, h173, h183] h173 := .app e257 e251
private def e259 : HOL.Term Symbol [h173, h173, h173, h183] h173 := .app e253 e258
private def e260 : HOL.Term Symbol [h173, h173, h183] h189 := .lam e259
private def e261 : HOL.Term Symbol [h173, h173, h183] h173 := .app e211 e260
private def e262 : HOL.Term Symbol [h173, h183] h189 := .lam e261
private def e263 : HOL.Term Symbol [h183] h192 := .lam e262
private def h264 : HOL.Ty AtomicTy := HOL.Ty.arr h183 h186
private theorem q265 : t63.toHOL = h264 := (Ty.toHOL_function t3 t62).trans (congrArg₂ HOL.Ty.arr q184 q187)
private theorem v266 : ReverseTranslation.reverseTy h264 = t63 := (ReverseTranslation.reverseTy_eq_iff).mpr q265.symm
private def e267 : HOL.Term Symbol [h183] h264 := .const (.constant Const.equality t63 q265)
private def e268 : HOL.Term Symbol [h183] h183 := .var (HOL.Var.vz)
private def e269 : HOL.Term Symbol [h183] h186 := .app e267 e268
private def e270 : HOL.Term Symbol [h189, h180, h183] h198 := .const (.constant Const.equality t6 q199)
private def e271 : HOL.Term Symbol [h189, h180, h183] h189 := .var (HOL.Var.vz)
private def e272 : HOL.Term Symbol [h189, h180, h183] h195 := .app e270 e271
private def e273 : HOL.Term Symbol [h173, h189, h180, h183] h198 := .const (.constant Const.equality t6 q199)
private def e274 : HOL.Term Symbol [h173, h173, h189, h180, h183] h173 := .var (HOL.Var.vz)
private def e275 : HOL.Term Symbol [h173, h189, h180, h183] h189 := .lam e274
private def e276 : HOL.Term Symbol [h173, h189, h180, h183] h195 := .app e273 e275
private def e277 : HOL.Term Symbol [h173, h189, h180, h183] h173 := .app e276 e275
private def e278 : HOL.Term Symbol [h189, h180, h183] h189 := .lam e277
private def e279 : HOL.Term Symbol [h189, h180, h183] h173 := .app e272 e278
private def e280 : HOL.Term Symbol [h180, h183] h195 := .lam e279
private def e281 : HOL.Term Symbol [h173, h180, h183] h173 := .var (HOL.Var.vz)
private def e282 : HOL.Term Symbol [h180, h183] h189 := .lam e281
private def e283 : HOL.Term Symbol [h180, h183] h173 := .app e280 e282
private def e284 : HOL.Term Symbol [h183] h183 := .lam e283
private def e285 : HOL.Term Symbol [h183] h173 := .app e269 e284
private def e286 : HOL.Term Symbol [h183] h189 := .app e263 e285
private def e287 : HOL.Term Symbol [h173, h173, h173, h180, h183] h192 := .const (.constant Const.equality t17 q193)
private def e288 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h183] h219 := .const (.constant Const.equality t21 q220)
private def e289 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183] h192 := .var (HOL.Var.vz)
private def e290 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e291 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183] h189 := .app e289 e290
private def e292 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e293 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183] h173 := .app e291 e292
private def e294 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h183] h213 := .lam e293
private def e295 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h183] h216 := .app e288 e294
private def e296 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183] h198 := .const (.constant Const.equality t6 q199)
private def e297 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h180, h183] h173 := .var (HOL.Var.vz)
private def e298 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183] h189 := .lam e297
private def e299 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183] h195 := .app e296 e298
private def e300 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183] h173 := .app e299 e298
private def e301 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183] h189 := .app e289 e300
private def e302 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183] h173 := .app e301 e300
private def e303 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h183] h213 := .lam e302
private def e304 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h183] h173 := .app e295 e303
private def e305 : HOL.Term Symbol [h173, h173, h173, h173, h180, h183] h189 := .lam e304
private def e306 : HOL.Term Symbol [h173, h173, h173, h180, h183] h192 := .lam e305
private def e307 : HOL.Term Symbol [h173, h173, h173, h180, h183] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e308 : HOL.Term Symbol [h173, h173, h173, h180, h183] h189 := .app e306 e307
private def e309 : HOL.Term Symbol [h173, h173, h173, h180, h183] h173 := .var (HOL.Var.vz)
private def e310 : HOL.Term Symbol [h173, h173, h173, h180, h183] h173 := .app e308 e309
private def e311 : HOL.Term Symbol [h173, h173, h173, h180, h183] h189 := .app e287 e310
private def e312 : HOL.Term Symbol [h173, h173, h173, h180, h183] h173 := .app e311 e307
private def e313 : HOL.Term Symbol [h173, h173, h180, h183] h189 := .lam e312
private def e314 : HOL.Term Symbol [h173, h180, h183] h192 := .lam e313
private def h315 : HOL.Ty AtomicTy := HOL.Ty.arr h180 h183
private theorem q316 : t101.toHOL = h315 := (Ty.toHOL_function t2 t3).trans (congrArg₂ HOL.Ty.arr q181 q184)
private theorem v317 : ReverseTranslation.reverseTy h315 = t101 := (ReverseTranslation.reverseTy_eq_iff).mpr q316.symm
private def e318 : HOL.Term Symbol [h180, h173, h180, h183] h315 := .const (.constant Const.equality t101 q316)
private def e319 : HOL.Term Symbol [h180, h173, h180, h183] h180 := .var (HOL.Var.vz)
private def e320 : HOL.Term Symbol [h180, h173, h180, h183] h183 := .app e318 e319
private def e321 : HOL.Term Symbol [h177, h180, h173, h180, h183] h198 := .const (.constant Const.equality t6 q199)
private def e322 : HOL.Term Symbol [h173, h177, h180, h173, h180, h183] h173 := .var (HOL.Var.vz)
private def e323 : HOL.Term Symbol [h177, h180, h173, h180, h183] h189 := .lam e322
private def e324 : HOL.Term Symbol [h177, h180, h173, h180, h183] h195 := .app e321 e323
private def e325 : HOL.Term Symbol [h177, h180, h173, h180, h183] h173 := .app e324 e323
private def e326 : HOL.Term Symbol [h180, h173, h180, h183] h180 := .lam e325
private def e327 : HOL.Term Symbol [h180, h173, h180, h183] h173 := .app e320 e326
private def e328 : HOL.Term Symbol [h173, h180, h183] h183 := .lam e327
private def e329 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183] h192 := .const (.constant Const.equality t17 q193)
private def e330 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h183] h219 := .const (.constant Const.equality t21 q220)
private def e331 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183] h192 := .var (HOL.Var.vz)
private def e332 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e333 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183] h189 := .app e331 e332
private def e334 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e335 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183] h173 := .app e333 e334
private def e336 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h183] h213 := .lam e335
private def e337 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h183] h216 := .app e330 e336
private def e338 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183] h198 := .const (.constant Const.equality t6 q199)
private def e339 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h177, h173, h180, h183] h173 := .var (HOL.Var.vz)
private def e340 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183] h189 := .lam e339
private def e341 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183] h195 := .app e338 e340
private def e342 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183] h173 := .app e341 e340
private def e343 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183] h189 := .app e331 e342
private def e344 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183] h173 := .app e343 e342
private def e345 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h183] h213 := .lam e344
private def e346 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h183] h173 := .app e337 e345
private def e347 : HOL.Term Symbol [h173, h173, h173, h177, h173, h180, h183] h189 := .lam e346
private def e348 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183] h192 := .lam e347
private def e349 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e350 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183] h189 := .app e348 e349
private def e351 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183] h173 := .var (HOL.Var.vz)
private def e352 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183] h173 := .app e350 e351
private def e353 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183] h189 := .app e329 e352
private def e354 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183] h173 := .app e353 e349
private def e355 : HOL.Term Symbol [h173, h177, h173, h180, h183] h189 := .lam e354
private def e356 : HOL.Term Symbol [h177, h173, h180, h183] h192 := .lam e355
private def e357 : HOL.Term Symbol [h177, h173, h180, h183] h180 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e358 : HOL.Term Symbol [h177, h173, h180, h183] h177 := .var (HOL.Var.vz)
private def e359 : HOL.Term Symbol [h177, h173, h180, h183] h173 := .app e357 e358
private def e360 : HOL.Term Symbol [h177, h173, h180, h183] h189 := .app e356 e359
private def e361 : HOL.Term Symbol [h177, h173, h180, h183] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e362 : HOL.Term Symbol [h177, h173, h180, h183] h173 := .app e360 e361
private def e363 : HOL.Term Symbol [h173, h180, h183] h180 := .lam e362
private def e364 : HOL.Term Symbol [h173, h180, h183] h173 := .app e328 e363
private def e365 : HOL.Term Symbol [h173, h180, h183] h189 := .app e314 e364
private def e366 : HOL.Term Symbol [h173, h180, h183] h173 := .app e365 e281
private def e367 : HOL.Term Symbol [h180, h183] h189 := .lam e366
private def e368 : HOL.Term Symbol [h180, h183] h173 := .app e280 e367
private def e369 : HOL.Term Symbol [h183] h183 := .lam e368
private def e370 : HOL.Term Symbol [h189, h173, h173, h177, h183] h198 := .const (.constant Const.equality t6 q199)
private def e371 : HOL.Term Symbol [h189, h173, h173, h177, h183] h189 := .var (HOL.Var.vz)
private def e372 : HOL.Term Symbol [h189, h173, h173, h177, h183] h195 := .app e370 e371
private def e373 : HOL.Term Symbol [h173, h189, h173, h173, h177, h183] h198 := .const (.constant Const.equality t6 q199)
private def e374 : HOL.Term Symbol [h173, h173, h189, h173, h173, h177, h183] h173 := .var (HOL.Var.vz)
private def e375 : HOL.Term Symbol [h173, h189, h173, h173, h177, h183] h189 := .lam e374
private def e376 : HOL.Term Symbol [h173, h189, h173, h173, h177, h183] h195 := .app e373 e375
private def e377 : HOL.Term Symbol [h173, h189, h173, h173, h177, h183] h173 := .app e376 e375
private def e378 : HOL.Term Symbol [h189, h173, h173, h177, h183] h189 := .lam e377
private def e379 : HOL.Term Symbol [h189, h173, h173, h177, h183] h173 := .app e372 e378
private def e380 : HOL.Term Symbol [h173, h173, h177, h183] h195 := .lam e379
private def e381 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183] h192 := .const (.constant Const.equality t17 q193)
private def e382 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h183] h219 := .const (.constant Const.equality t21 q220)
private def e383 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183] h192 := .var (HOL.Var.vz)
private def e384 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e385 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183] h189 := .app e383 e384
private def e386 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e387 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183] h173 := .app e385 e386
private def e388 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h183] h213 := .lam e387
private def e389 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h183] h216 := .app e382 e388
private def e390 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183] h198 := .const (.constant Const.equality t6 q199)
private def e391 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h177, h183] h173 := .var (HOL.Var.vz)
private def e392 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183] h189 := .lam e391
private def e393 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183] h195 := .app e390 e392
private def e394 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183] h173 := .app e393 e392
private def e395 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183] h189 := .app e383 e394
private def e396 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183] h173 := .app e395 e394
private def e397 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h183] h213 := .lam e396
private def e398 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h183] h173 := .app e389 e397
private def e399 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h177, h183] h189 := .lam e398
private def e400 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183] h192 := .lam e399
private def e401 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e402 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183] h189 := .app e400 e401
private def e403 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183] h173 := .var (HOL.Var.vz)
private def e404 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183] h173 := .app e402 e403
private def e405 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183] h189 := .app e381 e404
private def e406 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183] h173 := .app e405 e401
private def e407 : HOL.Term Symbol [h173, h173, h173, h173, h177, h183] h189 := .lam e406
private def e408 : HOL.Term Symbol [h173, h173, h173, h177, h183] h192 := .lam e407
private def e409 : HOL.Term Symbol [h173, h173, h173, h177, h183] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e410 : HOL.Term Symbol [h173, h173, h173, h177, h183] h189 := .app e408 e409
private def e411 : HOL.Term Symbol [h173, h173, h173, h177, h183] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e412 : HOL.Term Symbol [h173, h173, h173, h177, h183] h189 := .app e408 e411
private def e413 : HOL.Term Symbol [h173, h173, h173, h177, h183] h173 := .var (HOL.Var.vz)
private def e414 : HOL.Term Symbol [h173, h173, h173, h177, h183] h173 := .app e412 e413
private def e415 : HOL.Term Symbol [h173, h173, h173, h177, h183] h173 := .app e410 e414
private def e416 : HOL.Term Symbol [h173, h173, h173, h177, h183] h189 := .app e408 e415
private def e417 : HOL.Term Symbol [h173, h173, h173, h177, h183] h173 := .app e416 e413
private def e418 : HOL.Term Symbol [h173, h173, h177, h183] h189 := .lam e417
private def e419 : HOL.Term Symbol [h173, h173, h177, h183] h173 := .app e380 e418
private def e420 : HOL.Term Symbol [h173, h177, h183] h189 := .lam e419
private def e421 : HOL.Term Symbol [h177, h183] h192 := .lam e420
private def e422 : HOL.Term Symbol [h177, h183] h180 := .const (.variable ⟨Name.mk [] "pointedCarrierProperty", t2⟩ q181)
private def e423 : HOL.Term Symbol [h177, h183] h177 := .var (HOL.Var.vz)
private def e424 : HOL.Term Symbol [h177, h183] h173 := .app e422 e423
private def e425 : HOL.Term Symbol [h177, h183] h189 := .app e421 e424
private def e426 : HOL.Term Symbol [h177, h183] h264 := .const (.constant Const.equality t63 q265)
private def e427 : HOL.Term Symbol [h177, h183] h183 := .var (HOL.Var.vs (HOL.Var.vz))
private def e428 : HOL.Term Symbol [h177, h183] h186 := .app e426 e427
private def e429 : HOL.Term Symbol [h180, h177, h183] h180 := .var (HOL.Var.vz)
private def e430 : HOL.Term Symbol [h180, h177, h183] h177 := .var (HOL.Var.vs (HOL.Var.vz))
private def e431 : HOL.Term Symbol [h180, h177, h183] h173 := .app e429 e430
private def e432 : HOL.Term Symbol [h177, h183] h183 := .lam e431
private def e433 : HOL.Term Symbol [h177, h183] h173 := .app e428 e432
private def e434 : HOL.Term Symbol [h177, h183] h173 := .app e425 e433
private def e435 : HOL.Term Symbol [h183] h180 := .lam e434
private def e436 : HOL.Term Symbol [h183] h173 := .app e369 e435
private def e437 : HOL.Term Symbol [h183] h173 := .app e286 e436
private def e438 : HOL.Term Symbol [] h186 := .lam e437
private def e439 : HOL.Term Symbol [] h183 := .const (.variable ⟨Name.mk [""] "x", t3⟩ q184)
private def e440 : HOL.Term Symbol [] h173 := .app e438 e439
private def c441 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e440
private theorem n442 : s172.toDB [] = c441.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k443 : CheckedSourceTerm := ⟨s172, t1, by rw [← DBTerm.inferType_toDB [] s172, n442]; exact c441.checked.trans (congrArg some v175)⟩
private def r444 : InferenceRequest := .beta k443
private def e445 : HOL.Term Symbol [] h192 := .const (.constant Const.equality t17 q193)
private def e446 : HOL.Term Symbol [] h189 := .app e445 e440
private def e447 : HOL.Term Symbol [h189, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e448 : HOL.Term Symbol [h189, h173, h173] h189 := .var (HOL.Var.vz)
private def e449 : HOL.Term Symbol [h189, h173, h173] h195 := .app e447 e448
private def e450 : HOL.Term Symbol [h173, h189, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e451 : HOL.Term Symbol [h173, h173, h189, h173, h173] h173 := .var (HOL.Var.vz)
private def e452 : HOL.Term Symbol [h173, h189, h173, h173] h189 := .lam e451
private def e453 : HOL.Term Symbol [h173, h189, h173, h173] h195 := .app e450 e452
private def e454 : HOL.Term Symbol [h173, h189, h173, h173] h173 := .app e453 e452
private def e455 : HOL.Term Symbol [h189, h173, h173] h189 := .lam e454
private def e456 : HOL.Term Symbol [h189, h173, h173] h173 := .app e449 e455
private def e457 : HOL.Term Symbol [h173, h173] h195 := .lam e456
private def e458 : HOL.Term Symbol [h173, h173, h173, h173, h173] h192 := .const (.constant Const.equality t17 q193)
private def e459 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173] h219 := .const (.constant Const.equality t21 q220)
private def e460 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173] h192 := .var (HOL.Var.vz)
private def e461 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e462 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173] h189 := .app e460 e461
private def e463 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e464 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173] h173 := .app e462 e463
private def e465 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173] h213 := .lam e464
private def e466 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173] h216 := .app e459 e465
private def e467 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e468 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vz)
private def e469 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173] h189 := .lam e468
private def e470 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173] h195 := .app e467 e469
private def e471 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173] h173 := .app e470 e469
private def e472 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173] h189 := .app e460 e471
private def e473 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173] h173 := .app e472 e471
private def e474 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173] h213 := .lam e473
private def e475 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173] h173 := .app e466 e474
private def e476 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h189 := .lam e475
private def e477 : HOL.Term Symbol [h173, h173, h173, h173, h173] h192 := .lam e476
private def e478 : HOL.Term Symbol [h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e479 : HOL.Term Symbol [h173, h173, h173, h173, h173] h189 := .app e477 e478
private def e480 : HOL.Term Symbol [h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vz)
private def e481 : HOL.Term Symbol [h173, h173, h173, h173, h173] h173 := .app e479 e480
private def e482 : HOL.Term Symbol [h173, h173, h173, h173, h173] h189 := .app e458 e481
private def e483 : HOL.Term Symbol [h173, h173, h173, h173, h173] h173 := .app e482 e478
private def e484 : HOL.Term Symbol [h173, h173, h173, h173] h189 := .lam e483
private def e485 : HOL.Term Symbol [h173, h173, h173] h192 := .lam e484
private def e486 : HOL.Term Symbol [h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e487 : HOL.Term Symbol [h173, h173, h173] h189 := .app e485 e486
private def e488 : HOL.Term Symbol [h173, h173, h173] h173 := .var (HOL.Var.vz)
private def e489 : HOL.Term Symbol [h173, h173, h173] h173 := .app e487 e488
private def e490 : HOL.Term Symbol [h173, h173, h173] h189 := .app e485 e489
private def e491 : HOL.Term Symbol [h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e492 : HOL.Term Symbol [h173, h173, h173] h189 := .app e485 e491
private def e493 : HOL.Term Symbol [h173, h173, h173] h173 := .app e492 e488
private def e494 : HOL.Term Symbol [h173, h173, h173] h189 := .app e485 e493
private def e495 : HOL.Term Symbol [h173, h173, h173] h173 := .app e494 e488
private def e496 : HOL.Term Symbol [h173, h173, h173] h173 := .app e490 e495
private def e497 : HOL.Term Symbol [h173, h173] h189 := .lam e496
private def e498 : HOL.Term Symbol [h173, h173] h173 := .app e457 e497
private def e499 : HOL.Term Symbol [h173] h189 := .lam e498
private def e500 : HOL.Term Symbol [] h192 := .lam e499
private def e501 : HOL.Term Symbol [] h264 := .const (.constant Const.equality t63 q265)
private def e502 : HOL.Term Symbol [] h186 := .app e501 e439
private def e503 : HOL.Term Symbol [h189, h180] h198 := .const (.constant Const.equality t6 q199)
private def e504 : HOL.Term Symbol [h189, h180] h189 := .var (HOL.Var.vz)
private def e505 : HOL.Term Symbol [h189, h180] h195 := .app e503 e504
private def e506 : HOL.Term Symbol [h173, h189, h180] h198 := .const (.constant Const.equality t6 q199)
private def e507 : HOL.Term Symbol [h173, h173, h189, h180] h173 := .var (HOL.Var.vz)
private def e508 : HOL.Term Symbol [h173, h189, h180] h189 := .lam e507
private def e509 : HOL.Term Symbol [h173, h189, h180] h195 := .app e506 e508
private def e510 : HOL.Term Symbol [h173, h189, h180] h173 := .app e509 e508
private def e511 : HOL.Term Symbol [h189, h180] h189 := .lam e510
private def e512 : HOL.Term Symbol [h189, h180] h173 := .app e505 e511
private def e513 : HOL.Term Symbol [h180] h195 := .lam e512
private def e514 : HOL.Term Symbol [h173, h180] h173 := .var (HOL.Var.vz)
private def e515 : HOL.Term Symbol [h180] h189 := .lam e514
private def e516 : HOL.Term Symbol [h180] h173 := .app e513 e515
private def e517 : HOL.Term Symbol [] h183 := .lam e516
private def e518 : HOL.Term Symbol [] h173 := .app e502 e517
private def e519 : HOL.Term Symbol [] h189 := .app e500 e518
private def e520 : HOL.Term Symbol [h173, h173, h173, h180] h192 := .const (.constant Const.equality t17 q193)
private def e521 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180] h219 := .const (.constant Const.equality t21 q220)
private def e522 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180] h192 := .var (HOL.Var.vz)
private def e523 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e524 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180] h189 := .app e522 e523
private def e525 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e526 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180] h173 := .app e524 e525
private def e527 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180] h213 := .lam e526
private def e528 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180] h216 := .app e521 e527
private def e529 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180] h198 := .const (.constant Const.equality t6 q199)
private def e530 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h180] h173 := .var (HOL.Var.vz)
private def e531 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180] h189 := .lam e530
private def e532 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180] h195 := .app e529 e531
private def e533 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180] h173 := .app e532 e531
private def e534 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180] h189 := .app e522 e533
private def e535 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180] h173 := .app e534 e533
private def e536 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180] h213 := .lam e535
private def e537 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180] h173 := .app e528 e536
private def e538 : HOL.Term Symbol [h173, h173, h173, h173, h180] h189 := .lam e537
private def e539 : HOL.Term Symbol [h173, h173, h173, h180] h192 := .lam e538
private def e540 : HOL.Term Symbol [h173, h173, h173, h180] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e541 : HOL.Term Symbol [h173, h173, h173, h180] h189 := .app e539 e540
private def e542 : HOL.Term Symbol [h173, h173, h173, h180] h173 := .var (HOL.Var.vz)
private def e543 : HOL.Term Symbol [h173, h173, h173, h180] h173 := .app e541 e542
private def e544 : HOL.Term Symbol [h173, h173, h173, h180] h189 := .app e520 e543
private def e545 : HOL.Term Symbol [h173, h173, h173, h180] h173 := .app e544 e540
private def e546 : HOL.Term Symbol [h173, h173, h180] h189 := .lam e545
private def e547 : HOL.Term Symbol [h173, h180] h192 := .lam e546
private def e548 : HOL.Term Symbol [h180, h173, h180] h315 := .const (.constant Const.equality t101 q316)
private def e549 : HOL.Term Symbol [h180, h173, h180] h180 := .var (HOL.Var.vz)
private def e550 : HOL.Term Symbol [h180, h173, h180] h183 := .app e548 e549
private def e551 : HOL.Term Symbol [h177, h180, h173, h180] h198 := .const (.constant Const.equality t6 q199)
private def e552 : HOL.Term Symbol [h173, h177, h180, h173, h180] h173 := .var (HOL.Var.vz)
private def e553 : HOL.Term Symbol [h177, h180, h173, h180] h189 := .lam e552
private def e554 : HOL.Term Symbol [h177, h180, h173, h180] h195 := .app e551 e553
private def e555 : HOL.Term Symbol [h177, h180, h173, h180] h173 := .app e554 e553
private def e556 : HOL.Term Symbol [h180, h173, h180] h180 := .lam e555
private def e557 : HOL.Term Symbol [h180, h173, h180] h173 := .app e550 e556
private def e558 : HOL.Term Symbol [h173, h180] h183 := .lam e557
private def e559 : HOL.Term Symbol [h173, h173, h177, h173, h180] h192 := .const (.constant Const.equality t17 q193)
private def e560 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180] h219 := .const (.constant Const.equality t21 q220)
private def e561 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180] h192 := .var (HOL.Var.vz)
private def e562 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e563 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180] h189 := .app e561 e562
private def e564 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e565 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180] h173 := .app e563 e564
private def e566 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180] h213 := .lam e565
private def e567 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180] h216 := .app e560 e566
private def e568 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180] h198 := .const (.constant Const.equality t6 q199)
private def e569 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h177, h173, h180] h173 := .var (HOL.Var.vz)
private def e570 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180] h189 := .lam e569
private def e571 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180] h195 := .app e568 e570
private def e572 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180] h173 := .app e571 e570
private def e573 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180] h189 := .app e561 e572
private def e574 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180] h173 := .app e573 e572
private def e575 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180] h213 := .lam e574
private def e576 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180] h173 := .app e567 e575
private def e577 : HOL.Term Symbol [h173, h173, h173, h177, h173, h180] h189 := .lam e576
private def e578 : HOL.Term Symbol [h173, h173, h177, h173, h180] h192 := .lam e577
private def e579 : HOL.Term Symbol [h173, h173, h177, h173, h180] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e580 : HOL.Term Symbol [h173, h173, h177, h173, h180] h189 := .app e578 e579
private def e581 : HOL.Term Symbol [h173, h173, h177, h173, h180] h173 := .var (HOL.Var.vz)
private def e582 : HOL.Term Symbol [h173, h173, h177, h173, h180] h173 := .app e580 e581
private def e583 : HOL.Term Symbol [h173, h173, h177, h173, h180] h189 := .app e559 e582
private def e584 : HOL.Term Symbol [h173, h173, h177, h173, h180] h173 := .app e583 e579
private def e585 : HOL.Term Symbol [h173, h177, h173, h180] h189 := .lam e584
private def e586 : HOL.Term Symbol [h177, h173, h180] h192 := .lam e585
private def e587 : HOL.Term Symbol [h177, h173, h180] h180 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e588 : HOL.Term Symbol [h177, h173, h180] h177 := .var (HOL.Var.vz)
private def e589 : HOL.Term Symbol [h177, h173, h180] h173 := .app e587 e588
private def e590 : HOL.Term Symbol [h177, h173, h180] h189 := .app e586 e589
private def e591 : HOL.Term Symbol [h177, h173, h180] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e592 : HOL.Term Symbol [h177, h173, h180] h173 := .app e590 e591
private def e593 : HOL.Term Symbol [h173, h180] h180 := .lam e592
private def e594 : HOL.Term Symbol [h173, h180] h173 := .app e558 e593
private def e595 : HOL.Term Symbol [h173, h180] h189 := .app e547 e594
private def e596 : HOL.Term Symbol [h173, h180] h173 := .app e595 e514
private def e597 : HOL.Term Symbol [h180] h189 := .lam e596
private def e598 : HOL.Term Symbol [h180] h173 := .app e513 e597
private def e599 : HOL.Term Symbol [] h183 := .lam e598
private def e600 : HOL.Term Symbol [h189, h173, h173, h177] h198 := .const (.constant Const.equality t6 q199)
private def e601 : HOL.Term Symbol [h189, h173, h173, h177] h189 := .var (HOL.Var.vz)
private def e602 : HOL.Term Symbol [h189, h173, h173, h177] h195 := .app e600 e601
private def e603 : HOL.Term Symbol [h173, h189, h173, h173, h177] h198 := .const (.constant Const.equality t6 q199)
private def e604 : HOL.Term Symbol [h173, h173, h189, h173, h173, h177] h173 := .var (HOL.Var.vz)
private def e605 : HOL.Term Symbol [h173, h189, h173, h173, h177] h189 := .lam e604
private def e606 : HOL.Term Symbol [h173, h189, h173, h173, h177] h195 := .app e603 e605
private def e607 : HOL.Term Symbol [h173, h189, h173, h173, h177] h173 := .app e606 e605
private def e608 : HOL.Term Symbol [h189, h173, h173, h177] h189 := .lam e607
private def e609 : HOL.Term Symbol [h189, h173, h173, h177] h173 := .app e602 e608
private def e610 : HOL.Term Symbol [h173, h173, h177] h195 := .lam e609
private def e611 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177] h192 := .const (.constant Const.equality t17 q193)
private def e612 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177] h219 := .const (.constant Const.equality t21 q220)
private def e613 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177] h192 := .var (HOL.Var.vz)
private def e614 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e615 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177] h189 := .app e613 e614
private def e616 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e617 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177] h173 := .app e615 e616
private def e618 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177] h213 := .lam e617
private def e619 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177] h216 := .app e612 e618
private def e620 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177] h198 := .const (.constant Const.equality t6 q199)
private def e621 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h177] h173 := .var (HOL.Var.vz)
private def e622 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177] h189 := .lam e621
private def e623 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177] h195 := .app e620 e622
private def e624 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177] h173 := .app e623 e622
private def e625 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177] h189 := .app e613 e624
private def e626 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177] h173 := .app e625 e624
private def e627 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177] h213 := .lam e626
private def e628 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177] h173 := .app e619 e627
private def e629 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h177] h189 := .lam e628
private def e630 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177] h192 := .lam e629
private def e631 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e632 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177] h189 := .app e630 e631
private def e633 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177] h173 := .var (HOL.Var.vz)
private def e634 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177] h173 := .app e632 e633
private def e635 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177] h189 := .app e611 e634
private def e636 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177] h173 := .app e635 e631
private def e637 : HOL.Term Symbol [h173, h173, h173, h173, h177] h189 := .lam e636
private def e638 : HOL.Term Symbol [h173, h173, h173, h177] h192 := .lam e637
private def e639 : HOL.Term Symbol [h173, h173, h173, h177] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e640 : HOL.Term Symbol [h173, h173, h173, h177] h189 := .app e638 e639
private def e641 : HOL.Term Symbol [h173, h173, h173, h177] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e642 : HOL.Term Symbol [h173, h173, h173, h177] h189 := .app e638 e641
private def e643 : HOL.Term Symbol [h173, h173, h173, h177] h173 := .var (HOL.Var.vz)
private def e644 : HOL.Term Symbol [h173, h173, h173, h177] h173 := .app e642 e643
private def e645 : HOL.Term Symbol [h173, h173, h173, h177] h173 := .app e640 e644
private def e646 : HOL.Term Symbol [h173, h173, h173, h177] h189 := .app e638 e645
private def e647 : HOL.Term Symbol [h173, h173, h173, h177] h173 := .app e646 e643
private def e648 : HOL.Term Symbol [h173, h173, h177] h189 := .lam e647
private def e649 : HOL.Term Symbol [h173, h173, h177] h173 := .app e610 e648
private def e650 : HOL.Term Symbol [h173, h177] h189 := .lam e649
private def e651 : HOL.Term Symbol [h177] h192 := .lam e650
private def e652 : HOL.Term Symbol [h177] h180 := .const (.variable ⟨Name.mk [] "pointedCarrierProperty", t2⟩ q181)
private def e653 : HOL.Term Symbol [h177] h177 := .var (HOL.Var.vz)
private def e654 : HOL.Term Symbol [h177] h173 := .app e652 e653
private def e655 : HOL.Term Symbol [h177] h189 := .app e651 e654
private def e656 : HOL.Term Symbol [h177] h264 := .const (.constant Const.equality t63 q265)
private def e657 : HOL.Term Symbol [h177] h183 := .const (.variable ⟨Name.mk [""] "x", t3⟩ q184)
private def e658 : HOL.Term Symbol [h177] h186 := .app e656 e657
private def e659 : HOL.Term Symbol [h180, h177] h180 := .var (HOL.Var.vz)
private def e660 : HOL.Term Symbol [h180, h177] h177 := .var (HOL.Var.vs (HOL.Var.vz))
private def e661 : HOL.Term Symbol [h180, h177] h173 := .app e659 e660
private def e662 : HOL.Term Symbol [h177] h183 := .lam e661
private def e663 : HOL.Term Symbol [h177] h173 := .app e658 e662
private def e664 : HOL.Term Symbol [h177] h173 := .app e655 e663
private def e665 : HOL.Term Symbol [] h180 := .lam e664
private def e666 : HOL.Term Symbol [] h173 := .app e599 e665
private def e667 : HOL.Term Symbol [] h173 := .app e519 e666
private def e668 : HOL.Term Symbol [] h173 := .app e446 e667
private def c669 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e668
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
private def c682 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e517
private theorem n683 : s681.toDB [] = c682.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k684 : CheckedSourceTerm := ⟨s681, t3, by rw [← DBTerm.inferType_toDB [] s681, n683]; exact c682.checked.trans (congrArg some v185)⟩
private def r685 : InferenceRequest := .inst [(k684, s65)] f670
private def e686 : HOL.Term Symbol [] h173 := .app e438 e517
private def e687 : HOL.Term Symbol [] h189 := .app e445 e686
private def e688 : HOL.Term Symbol [] h186 := .app e501 e517
private def e689 : HOL.Term Symbol [] h173 := .app e688 e517
private def e690 : HOL.Term Symbol [] h189 := .app e500 e689
private def e691 : HOL.Term Symbol [h189, h180, h177] h198 := .const (.constant Const.equality t6 q199)
private def e692 : HOL.Term Symbol [h189, h180, h177] h189 := .var (HOL.Var.vz)
private def e693 : HOL.Term Symbol [h189, h180, h177] h195 := .app e691 e692
private def e694 : HOL.Term Symbol [h173, h189, h180, h177] h198 := .const (.constant Const.equality t6 q199)
private def e695 : HOL.Term Symbol [h173, h173, h189, h180, h177] h173 := .var (HOL.Var.vz)
private def e696 : HOL.Term Symbol [h173, h189, h180, h177] h189 := .lam e695
private def e697 : HOL.Term Symbol [h173, h189, h180, h177] h195 := .app e694 e696
private def e698 : HOL.Term Symbol [h173, h189, h180, h177] h173 := .app e697 e696
private def e699 : HOL.Term Symbol [h189, h180, h177] h189 := .lam e698
private def e700 : HOL.Term Symbol [h189, h180, h177] h173 := .app e693 e699
private def e701 : HOL.Term Symbol [h180, h177] h195 := .lam e700
private def e702 : HOL.Term Symbol [h173, h180, h177] h173 := .var (HOL.Var.vz)
private def e703 : HOL.Term Symbol [h180, h177] h189 := .lam e702
private def e704 : HOL.Term Symbol [h180, h177] h173 := .app e701 e703
private def e705 : HOL.Term Symbol [h177] h183 := .lam e704
private def e706 : HOL.Term Symbol [h177] h186 := .app e656 e705
private def e707 : HOL.Term Symbol [h177] h173 := .app e706 e662
private def e708 : HOL.Term Symbol [h177] h173 := .app e655 e707
private def e709 : HOL.Term Symbol [] h180 := .lam e708
private def e710 : HOL.Term Symbol [] h173 := .app e599 e709
private def e711 : HOL.Term Symbol [] h173 := .app e690 e710
private def e712 : HOL.Term Symbol [] h173 := .app e687 e711
private def c713 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e712
private def f714 : Theorem := Theorem.emptyResult ([].toFinset) c713
private def c715 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e445
private def r716 : InferenceRequest := .refl c715
private def t717 : Ty := Ty.op TypeOp.function [t17, t19]
private def h718 : HOL.Ty AtomicTy := HOL.Ty.arr h192 h213
private theorem q719 : t717.toHOL = h718 := (Ty.toHOL_function t17 t19).trans (congrArg₂ HOL.Ty.arr q193 q214)
private theorem v720 : ReverseTranslation.reverseTy h718 = t717 := (ReverseTranslation.reverseTy_eq_iff).mpr q719.symm
private def e721 : HOL.Term Symbol [] h718 := .const (.constant Const.equality t717 q719)
private def e722 : HOL.Term Symbol [] h213 := .app e721 e445
private def e723 : HOL.Term Symbol [] h173 := .app e722 e445
private def c724 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e723
private def f725 : Theorem := Theorem.emptyResult ([].toFinset) c724
private def r726 : InferenceRequest := .mkComb f725 f714
private def e727 : HOL.Term Symbol [] h198 := .const (.constant Const.equality t6 q199)
private def e728 : HOL.Term Symbol [] h195 := .app e727 e687
private def e729 : HOL.Term Symbol [] h189 := .app e445 e711
private def e730 : HOL.Term Symbol [] h173 := .app e728 e729
private def c731 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e730
private def f732 : Theorem := Theorem.emptyResult ([].toFinset) c731
private def c733 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e686
private def r734 : InferenceRequest := .refl c733
private def e735 : HOL.Term Symbol [] h173 := .app e687 e686
private def c736 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e735
private def f737 : Theorem := Theorem.emptyResult ([].toFinset) c736
private def r738 : InferenceRequest := .mkComb f732 f737
private def e739 : HOL.Term Symbol [] h189 := .app e445 e735
private def e740 : HOL.Term Symbol [] h173 := .app e729 e686
private def e741 : HOL.Term Symbol [] h173 := .app e739 e740
private def c742 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e741
private def f743 : Theorem := Theorem.emptyResult ([].toFinset) c742
private def r744 : InferenceRequest := .eqMp f743 f737
private def c745 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e740
private def f746 : Theorem := Theorem.emptyResult ([].toFinset) c745
private def c747 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e711
private def r748 : InferenceRequest := .assume c747
private def f749 : Theorem := Theorem.emptyResult ([c747].toFinset) c747
private def r750 : InferenceRequest := .deductAntisym f749 f746
private def e751 : HOL.Term Symbol [] h173 := .app e729 e740
private def c752 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e751
private def f753 : Theorem := Theorem.emptyResult ([c747].toFinset) c752
private def r754 : InferenceRequest := .eqMp f753 f749
private def f755 : Theorem := Theorem.emptyResult ([c747].toFinset) c745
private def r756 : InferenceRequest := .deductAntisym f749 f749
private def e757 : HOL.Term Symbol [] h173 := .app e729 e711
private def c758 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e757
private def f759 : Theorem := Theorem.emptyResult ([].toFinset) c758
private def r760 : InferenceRequest := .eqMp f759 f749
private def r761 : InferenceRequest := .eqMp f755 f749
private def f762 : Theorem := Theorem.emptyResult ([c747].toFinset) c733
private def e763 : HOL.Term Symbol [] h192 := .const (.variable ⟨Name.mk [""] "x", t17⟩ q193)
private def c764 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e763
private def r765 : InferenceRequest := .refl c764
private def e766 : HOL.Term Symbol [] h213 := .app e721 e763
private def e767 : HOL.Term Symbol [] h173 := .app e766 e763
private def c768 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e767
private def f769 : Theorem := Theorem.emptyResult ([].toFinset) c768
private def e770 : HOL.Term Symbol [h173] h173 := .var (HOL.Var.vz)
private def e771 : HOL.Term Symbol [] h189 := .lam e770
private def c772 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e771
private def r773 : InferenceRequest := .refl c772
private def e774 : HOL.Term Symbol [] h195 := .app e727 e771
private def e775 : HOL.Term Symbol [] h173 := .app e774 e771
private def c776 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e775
private def f777 : Theorem := Theorem.emptyResult ([].toFinset) c776
private def r778 : InferenceRequest := .deductAntisym f749 f777
private def e779 : HOL.Term Symbol [] h173 := .app e729 e775
private def c780 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e779
private def f781 : Theorem := Theorem.emptyResult ([c747].toFinset) c780
private def r782 : InferenceRequest := .deductAntisym f762 f777
private def e783 : HOL.Term Symbol [] h173 := .app e687 e775
private def c784 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e783
private def f785 : Theorem := Theorem.emptyResult ([c747].toFinset) c784
private def r786 : InferenceRequest := .mkComb f769 f781
private def e787 : HOL.Term Symbol [] h189 := .app e763 e711
private def e788 : HOL.Term Symbol [] h195 := .app e727 e787
private def e789 : HOL.Term Symbol [] h189 := .app e763 e775
private def e790 : HOL.Term Symbol [] h173 := .app e788 e789
private def c791 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e790
private def f792 : Theorem := Theorem.emptyResult ([c747].toFinset) c791
private def r793 : InferenceRequest := .mkComb f792 f785
private def e794 : HOL.Term Symbol [] h173 := .app e787 e686
private def e795 : HOL.Term Symbol [] h189 := .app e445 e794
private def e796 : HOL.Term Symbol [] h173 := .app e789 e775
private def e797 : HOL.Term Symbol [] h173 := .app e795 e796
private def c798 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e797
private def f799 : Theorem := Theorem.emptyResult ([c747].toFinset) c798
private def r800 : InferenceRequest := .abs ⟨Name.mk [""] "x", t17⟩ f799
private def e801 : HOL.Term Symbol [] h219 := .const (.constant Const.equality t21 q220)
private def e802 : HOL.Term Symbol [h192] h192 := .var (HOL.Var.vz)
private def e803 : HOL.Term Symbol [h189, h173, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e804 : HOL.Term Symbol [h189, h173, h173, h192] h189 := .var (HOL.Var.vz)
private def e805 : HOL.Term Symbol [h189, h173, h173, h192] h195 := .app e803 e804
private def e806 : HOL.Term Symbol [h173, h189, h173, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e807 : HOL.Term Symbol [h173, h173, h189, h173, h173, h192] h173 := .var (HOL.Var.vz)
private def e808 : HOL.Term Symbol [h173, h189, h173, h173, h192] h189 := .lam e807
private def e809 : HOL.Term Symbol [h173, h189, h173, h173, h192] h195 := .app e806 e808
private def e810 : HOL.Term Symbol [h173, h189, h173, h173, h192] h173 := .app e809 e808
private def e811 : HOL.Term Symbol [h189, h173, h173, h192] h189 := .lam e810
private def e812 : HOL.Term Symbol [h189, h173, h173, h192] h173 := .app e805 e811
private def e813 : HOL.Term Symbol [h173, h173, h192] h195 := .lam e812
private def e814 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h192 := .const (.constant Const.equality t17 q193)
private def e815 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h192] h219 := .const (.constant Const.equality t21 q220)
private def e816 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192] h192 := .var (HOL.Var.vz)
private def e817 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e818 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192] h189 := .app e816 e817
private def e819 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e820 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192] h173 := .app e818 e819
private def e821 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h192] h213 := .lam e820
private def e822 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h192] h216 := .app e815 e821
private def e823 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e824 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h192] h173 := .var (HOL.Var.vz)
private def e825 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192] h189 := .lam e824
private def e826 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192] h195 := .app e823 e825
private def e827 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192] h173 := .app e826 e825
private def e828 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192] h189 := .app e816 e827
private def e829 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192] h173 := .app e828 e827
private def e830 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h192] h213 := .lam e829
private def e831 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h192] h173 := .app e822 e830
private def e832 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h192] h189 := .lam e831
private def e833 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h192 := .lam e832
private def e834 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e835 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h189 := .app e833 e834
private def e836 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h173 := .var (HOL.Var.vz)
private def e837 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h173 := .app e835 e836
private def e838 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h189 := .app e814 e837
private def e839 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h173 := .app e838 e834
private def e840 : HOL.Term Symbol [h173, h173, h173, h173, h192] h189 := .lam e839
private def e841 : HOL.Term Symbol [h173, h173, h173, h192] h192 := .lam e840
private def e842 : HOL.Term Symbol [h173, h173, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e843 : HOL.Term Symbol [h173, h173, h173, h192] h189 := .app e841 e842
private def e844 : HOL.Term Symbol [h173, h173, h173, h192] h173 := .var (HOL.Var.vz)
private def e845 : HOL.Term Symbol [h173, h173, h173, h192] h173 := .app e843 e844
private def e846 : HOL.Term Symbol [h173, h173, h173, h192] h189 := .app e841 e845
private def e847 : HOL.Term Symbol [h173, h173, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e848 : HOL.Term Symbol [h173, h173, h173, h192] h189 := .app e841 e847
private def e849 : HOL.Term Symbol [h173, h173, h173, h192] h173 := .app e848 e844
private def e850 : HOL.Term Symbol [h173, h173, h173, h192] h189 := .app e841 e849
private def e851 : HOL.Term Symbol [h173, h173, h173, h192] h173 := .app e850 e844
private def e852 : HOL.Term Symbol [h173, h173, h173, h192] h173 := .app e846 e851
private def e853 : HOL.Term Symbol [h173, h173, h192] h189 := .lam e852
private def e854 : HOL.Term Symbol [h173, h173, h192] h173 := .app e813 e853
private def e855 : HOL.Term Symbol [h173, h192] h189 := .lam e854
private def e856 : HOL.Term Symbol [h192] h192 := .lam e855
private def e857 : HOL.Term Symbol [h192] h264 := .const (.constant Const.equality t63 q265)
private def e858 : HOL.Term Symbol [h189, h180, h192] h198 := .const (.constant Const.equality t6 q199)
private def e859 : HOL.Term Symbol [h189, h180, h192] h189 := .var (HOL.Var.vz)
private def e860 : HOL.Term Symbol [h189, h180, h192] h195 := .app e858 e859
private def e861 : HOL.Term Symbol [h173, h189, h180, h192] h198 := .const (.constant Const.equality t6 q199)
private def e862 : HOL.Term Symbol [h173, h173, h189, h180, h192] h173 := .var (HOL.Var.vz)
private def e863 : HOL.Term Symbol [h173, h189, h180, h192] h189 := .lam e862
private def e864 : HOL.Term Symbol [h173, h189, h180, h192] h195 := .app e861 e863
private def e865 : HOL.Term Symbol [h173, h189, h180, h192] h173 := .app e864 e863
private def e866 : HOL.Term Symbol [h189, h180, h192] h189 := .lam e865
private def e867 : HOL.Term Symbol [h189, h180, h192] h173 := .app e860 e866
private def e868 : HOL.Term Symbol [h180, h192] h195 := .lam e867
private def e869 : HOL.Term Symbol [h173, h180, h192] h173 := .var (HOL.Var.vz)
private def e870 : HOL.Term Symbol [h180, h192] h189 := .lam e869
private def e871 : HOL.Term Symbol [h180, h192] h173 := .app e868 e870
private def e872 : HOL.Term Symbol [h192] h183 := .lam e871
private def e873 : HOL.Term Symbol [h192] h186 := .app e857 e872
private def e874 : HOL.Term Symbol [h192] h173 := .app e873 e872
private def e875 : HOL.Term Symbol [h192] h189 := .app e856 e874
private def e876 : HOL.Term Symbol [h173, h173, h173, h180, h192] h192 := .const (.constant Const.equality t17 q193)
private def e877 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h192] h219 := .const (.constant Const.equality t21 q220)
private def e878 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192] h192 := .var (HOL.Var.vz)
private def e879 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e880 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192] h189 := .app e878 e879
private def e881 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e882 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192] h173 := .app e880 e881
private def e883 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h192] h213 := .lam e882
private def e884 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h192] h216 := .app e877 e883
private def e885 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192] h198 := .const (.constant Const.equality t6 q199)
private def e886 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h180, h192] h173 := .var (HOL.Var.vz)
private def e887 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192] h189 := .lam e886
private def e888 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192] h195 := .app e885 e887
private def e889 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192] h173 := .app e888 e887
private def e890 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192] h189 := .app e878 e889
private def e891 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192] h173 := .app e890 e889
private def e892 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h192] h213 := .lam e891
private def e893 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h192] h173 := .app e884 e892
private def e894 : HOL.Term Symbol [h173, h173, h173, h173, h180, h192] h189 := .lam e893
private def e895 : HOL.Term Symbol [h173, h173, h173, h180, h192] h192 := .lam e894
private def e896 : HOL.Term Symbol [h173, h173, h173, h180, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e897 : HOL.Term Symbol [h173, h173, h173, h180, h192] h189 := .app e895 e896
private def e898 : HOL.Term Symbol [h173, h173, h173, h180, h192] h173 := .var (HOL.Var.vz)
private def e899 : HOL.Term Symbol [h173, h173, h173, h180, h192] h173 := .app e897 e898
private def e900 : HOL.Term Symbol [h173, h173, h173, h180, h192] h189 := .app e876 e899
private def e901 : HOL.Term Symbol [h173, h173, h173, h180, h192] h173 := .app e900 e896
private def e902 : HOL.Term Symbol [h173, h173, h180, h192] h189 := .lam e901
private def e903 : HOL.Term Symbol [h173, h180, h192] h192 := .lam e902
private def e904 : HOL.Term Symbol [h180, h173, h180, h192] h315 := .const (.constant Const.equality t101 q316)
private def e905 : HOL.Term Symbol [h180, h173, h180, h192] h180 := .var (HOL.Var.vz)
private def e906 : HOL.Term Symbol [h180, h173, h180, h192] h183 := .app e904 e905
private def e907 : HOL.Term Symbol [h177, h180, h173, h180, h192] h198 := .const (.constant Const.equality t6 q199)
private def e908 : HOL.Term Symbol [h173, h177, h180, h173, h180, h192] h173 := .var (HOL.Var.vz)
private def e909 : HOL.Term Symbol [h177, h180, h173, h180, h192] h189 := .lam e908
private def e910 : HOL.Term Symbol [h177, h180, h173, h180, h192] h195 := .app e907 e909
private def e911 : HOL.Term Symbol [h177, h180, h173, h180, h192] h173 := .app e910 e909
private def e912 : HOL.Term Symbol [h180, h173, h180, h192] h180 := .lam e911
private def e913 : HOL.Term Symbol [h180, h173, h180, h192] h173 := .app e906 e912
private def e914 : HOL.Term Symbol [h173, h180, h192] h183 := .lam e913
private def e915 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192] h192 := .const (.constant Const.equality t17 q193)
private def e916 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h192] h219 := .const (.constant Const.equality t21 q220)
private def e917 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192] h192 := .var (HOL.Var.vz)
private def e918 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e919 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192] h189 := .app e917 e918
private def e920 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e921 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192] h173 := .app e919 e920
private def e922 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h192] h213 := .lam e921
private def e923 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h192] h216 := .app e916 e922
private def e924 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192] h198 := .const (.constant Const.equality t6 q199)
private def e925 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h177, h173, h180, h192] h173 := .var (HOL.Var.vz)
private def e926 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192] h189 := .lam e925
private def e927 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192] h195 := .app e924 e926
private def e928 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192] h173 := .app e927 e926
private def e929 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192] h189 := .app e917 e928
private def e930 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192] h173 := .app e929 e928
private def e931 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h192] h213 := .lam e930
private def e932 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h192] h173 := .app e923 e931
private def e933 : HOL.Term Symbol [h173, h173, h173, h177, h173, h180, h192] h189 := .lam e932
private def e934 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192] h192 := .lam e933
private def e935 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e936 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192] h189 := .app e934 e935
private def e937 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192] h173 := .var (HOL.Var.vz)
private def e938 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192] h173 := .app e936 e937
private def e939 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192] h189 := .app e915 e938
private def e940 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192] h173 := .app e939 e935
private def e941 : HOL.Term Symbol [h173, h177, h173, h180, h192] h189 := .lam e940
private def e942 : HOL.Term Symbol [h177, h173, h180, h192] h192 := .lam e941
private def e943 : HOL.Term Symbol [h177, h173, h180, h192] h180 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e944 : HOL.Term Symbol [h177, h173, h180, h192] h177 := .var (HOL.Var.vz)
private def e945 : HOL.Term Symbol [h177, h173, h180, h192] h173 := .app e943 e944
private def e946 : HOL.Term Symbol [h177, h173, h180, h192] h189 := .app e942 e945
private def e947 : HOL.Term Symbol [h177, h173, h180, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e948 : HOL.Term Symbol [h177, h173, h180, h192] h173 := .app e946 e947
private def e949 : HOL.Term Symbol [h173, h180, h192] h180 := .lam e948
private def e950 : HOL.Term Symbol [h173, h180, h192] h173 := .app e914 e949
private def e951 : HOL.Term Symbol [h173, h180, h192] h189 := .app e903 e950
private def e952 : HOL.Term Symbol [h173, h180, h192] h173 := .app e951 e869
private def e953 : HOL.Term Symbol [h180, h192] h189 := .lam e952
private def e954 : HOL.Term Symbol [h180, h192] h173 := .app e868 e953
private def e955 : HOL.Term Symbol [h192] h183 := .lam e954
private def e956 : HOL.Term Symbol [h189, h173, h173, h177, h192] h198 := .const (.constant Const.equality t6 q199)
private def e957 : HOL.Term Symbol [h189, h173, h173, h177, h192] h189 := .var (HOL.Var.vz)
private def e958 : HOL.Term Symbol [h189, h173, h173, h177, h192] h195 := .app e956 e957
private def e959 : HOL.Term Symbol [h173, h189, h173, h173, h177, h192] h198 := .const (.constant Const.equality t6 q199)
private def e960 : HOL.Term Symbol [h173, h173, h189, h173, h173, h177, h192] h173 := .var (HOL.Var.vz)
private def e961 : HOL.Term Symbol [h173, h189, h173, h173, h177, h192] h189 := .lam e960
private def e962 : HOL.Term Symbol [h173, h189, h173, h173, h177, h192] h195 := .app e959 e961
private def e963 : HOL.Term Symbol [h173, h189, h173, h173, h177, h192] h173 := .app e962 e961
private def e964 : HOL.Term Symbol [h189, h173, h173, h177, h192] h189 := .lam e963
private def e965 : HOL.Term Symbol [h189, h173, h173, h177, h192] h173 := .app e958 e964
private def e966 : HOL.Term Symbol [h173, h173, h177, h192] h195 := .lam e965
private def e967 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192] h192 := .const (.constant Const.equality t17 q193)
private def e968 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h192] h219 := .const (.constant Const.equality t21 q220)
private def e969 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192] h192 := .var (HOL.Var.vz)
private def e970 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e971 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192] h189 := .app e969 e970
private def e972 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e973 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192] h173 := .app e971 e972
private def e974 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h192] h213 := .lam e973
private def e975 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h192] h216 := .app e968 e974
private def e976 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192] h198 := .const (.constant Const.equality t6 q199)
private def e977 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h177, h192] h173 := .var (HOL.Var.vz)
private def e978 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192] h189 := .lam e977
private def e979 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192] h195 := .app e976 e978
private def e980 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192] h173 := .app e979 e978
private def e981 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192] h189 := .app e969 e980
private def e982 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192] h173 := .app e981 e980
private def e983 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h192] h213 := .lam e982
private def e984 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h192] h173 := .app e975 e983
private def e985 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h177, h192] h189 := .lam e984
private def e986 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192] h192 := .lam e985
private def e987 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e988 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192] h189 := .app e986 e987
private def e989 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192] h173 := .var (HOL.Var.vz)
private def e990 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192] h173 := .app e988 e989
private def e991 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192] h189 := .app e967 e990
private def e992 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192] h173 := .app e991 e987
private def e993 : HOL.Term Symbol [h173, h173, h173, h173, h177, h192] h189 := .lam e992
private def e994 : HOL.Term Symbol [h173, h173, h173, h177, h192] h192 := .lam e993
private def e995 : HOL.Term Symbol [h173, h173, h173, h177, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e996 : HOL.Term Symbol [h173, h173, h173, h177, h192] h189 := .app e994 e995
private def e997 : HOL.Term Symbol [h173, h173, h173, h177, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e998 : HOL.Term Symbol [h173, h173, h173, h177, h192] h189 := .app e994 e997
private def e999 : HOL.Term Symbol [h173, h173, h173, h177, h192] h173 := .var (HOL.Var.vz)
private def e1000 : HOL.Term Symbol [h173, h173, h173, h177, h192] h173 := .app e998 e999
private def e1001 : HOL.Term Symbol [h173, h173, h173, h177, h192] h173 := .app e996 e1000
private def e1002 : HOL.Term Symbol [h173, h173, h173, h177, h192] h189 := .app e994 e1001
private def e1003 : HOL.Term Symbol [h173, h173, h173, h177, h192] h173 := .app e1002 e999
private def e1004 : HOL.Term Symbol [h173, h173, h177, h192] h189 := .lam e1003
private def e1005 : HOL.Term Symbol [h173, h173, h177, h192] h173 := .app e966 e1004
private def e1006 : HOL.Term Symbol [h173, h177, h192] h189 := .lam e1005
private def e1007 : HOL.Term Symbol [h177, h192] h192 := .lam e1006
private def e1008 : HOL.Term Symbol [h177, h192] h180 := .const (.variable ⟨Name.mk [] "pointedCarrierProperty", t2⟩ q181)
private def e1009 : HOL.Term Symbol [h177, h192] h177 := .var (HOL.Var.vz)
private def e1010 : HOL.Term Symbol [h177, h192] h173 := .app e1008 e1009
private def e1011 : HOL.Term Symbol [h177, h192] h189 := .app e1007 e1010
private def e1012 : HOL.Term Symbol [h177, h192] h264 := .const (.constant Const.equality t63 q265)
private def e1013 : HOL.Term Symbol [h189, h180, h177, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1014 : HOL.Term Symbol [h189, h180, h177, h192] h189 := .var (HOL.Var.vz)
private def e1015 : HOL.Term Symbol [h189, h180, h177, h192] h195 := .app e1013 e1014
private def e1016 : HOL.Term Symbol [h173, h189, h180, h177, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1017 : HOL.Term Symbol [h173, h173, h189, h180, h177, h192] h173 := .var (HOL.Var.vz)
private def e1018 : HOL.Term Symbol [h173, h189, h180, h177, h192] h189 := .lam e1017
private def e1019 : HOL.Term Symbol [h173, h189, h180, h177, h192] h195 := .app e1016 e1018
private def e1020 : HOL.Term Symbol [h173, h189, h180, h177, h192] h173 := .app e1019 e1018
private def e1021 : HOL.Term Symbol [h189, h180, h177, h192] h189 := .lam e1020
private def e1022 : HOL.Term Symbol [h189, h180, h177, h192] h173 := .app e1015 e1021
private def e1023 : HOL.Term Symbol [h180, h177, h192] h195 := .lam e1022
private def e1024 : HOL.Term Symbol [h173, h180, h177, h192] h173 := .var (HOL.Var.vz)
private def e1025 : HOL.Term Symbol [h180, h177, h192] h189 := .lam e1024
private def e1026 : HOL.Term Symbol [h180, h177, h192] h173 := .app e1023 e1025
private def e1027 : HOL.Term Symbol [h177, h192] h183 := .lam e1026
private def e1028 : HOL.Term Symbol [h177, h192] h186 := .app e1012 e1027
private def e1029 : HOL.Term Symbol [h180, h177, h192] h180 := .var (HOL.Var.vz)
private def e1030 : HOL.Term Symbol [h180, h177, h192] h177 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1031 : HOL.Term Symbol [h180, h177, h192] h173 := .app e1029 e1030
private def e1032 : HOL.Term Symbol [h177, h192] h183 := .lam e1031
private def e1033 : HOL.Term Symbol [h177, h192] h173 := .app e1028 e1032
private def e1034 : HOL.Term Symbol [h177, h192] h173 := .app e1011 e1033
private def e1035 : HOL.Term Symbol [h192] h180 := .lam e1034
private def e1036 : HOL.Term Symbol [h192] h173 := .app e955 e1035
private def e1037 : HOL.Term Symbol [h192] h173 := .app e875 e1036
private def e1038 : HOL.Term Symbol [h192] h189 := .app e802 e1037
private def e1039 : HOL.Term Symbol [h189, h173, h173, h183, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1040 : HOL.Term Symbol [h189, h173, h173, h183, h192] h189 := .var (HOL.Var.vz)
private def e1041 : HOL.Term Symbol [h189, h173, h173, h183, h192] h195 := .app e1039 e1040
private def e1042 : HOL.Term Symbol [h173, h189, h173, h173, h183, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1043 : HOL.Term Symbol [h173, h173, h189, h173, h173, h183, h192] h173 := .var (HOL.Var.vz)
private def e1044 : HOL.Term Symbol [h173, h189, h173, h173, h183, h192] h189 := .lam e1043
private def e1045 : HOL.Term Symbol [h173, h189, h173, h173, h183, h192] h195 := .app e1042 e1044
private def e1046 : HOL.Term Symbol [h173, h189, h173, h173, h183, h192] h173 := .app e1045 e1044
private def e1047 : HOL.Term Symbol [h189, h173, h173, h183, h192] h189 := .lam e1046
private def e1048 : HOL.Term Symbol [h189, h173, h173, h183, h192] h173 := .app e1041 e1047
private def e1049 : HOL.Term Symbol [h173, h173, h183, h192] h195 := .lam e1048
private def e1050 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183, h192] h192 := .const (.constant Const.equality t17 q193)
private def e1051 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h183, h192] h219 := .const (.constant Const.equality t21 q220)
private def e1052 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183, h192] h192 := .var (HOL.Var.vz)
private def e1053 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1054 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183, h192] h189 := .app e1052 e1053
private def e1055 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1056 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183, h192] h173 := .app e1054 e1055
private def e1057 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h183, h192] h213 := .lam e1056
private def e1058 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h183, h192] h216 := .app e1051 e1057
private def e1059 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1060 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h183, h192] h173 := .var (HOL.Var.vz)
private def e1061 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183, h192] h189 := .lam e1060
private def e1062 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183, h192] h195 := .app e1059 e1061
private def e1063 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183, h192] h173 := .app e1062 e1061
private def e1064 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183, h192] h189 := .app e1052 e1063
private def e1065 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h183, h192] h173 := .app e1064 e1063
private def e1066 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h183, h192] h213 := .lam e1065
private def e1067 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h183, h192] h173 := .app e1058 e1066
private def e1068 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h183, h192] h189 := .lam e1067
private def e1069 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183, h192] h192 := .lam e1068
private def e1070 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1071 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183, h192] h189 := .app e1069 e1070
private def e1072 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183, h192] h173 := .var (HOL.Var.vz)
private def e1073 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183, h192] h173 := .app e1071 e1072
private def e1074 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183, h192] h189 := .app e1050 e1073
private def e1075 : HOL.Term Symbol [h173, h173, h173, h173, h173, h183, h192] h173 := .app e1074 e1070
private def e1076 : HOL.Term Symbol [h173, h173, h173, h173, h183, h192] h189 := .lam e1075
private def e1077 : HOL.Term Symbol [h173, h173, h173, h183, h192] h192 := .lam e1076
private def e1078 : HOL.Term Symbol [h173, h173, h173, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1079 : HOL.Term Symbol [h173, h173, h173, h183, h192] h189 := .app e1077 e1078
private def e1080 : HOL.Term Symbol [h173, h173, h173, h183, h192] h173 := .var (HOL.Var.vz)
private def e1081 : HOL.Term Symbol [h173, h173, h173, h183, h192] h173 := .app e1079 e1080
private def e1082 : HOL.Term Symbol [h173, h173, h173, h183, h192] h189 := .app e1077 e1081
private def e1083 : HOL.Term Symbol [h173, h173, h173, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1084 : HOL.Term Symbol [h173, h173, h173, h183, h192] h189 := .app e1077 e1083
private def e1085 : HOL.Term Symbol [h173, h173, h173, h183, h192] h173 := .app e1084 e1080
private def e1086 : HOL.Term Symbol [h173, h173, h173, h183, h192] h189 := .app e1077 e1085
private def e1087 : HOL.Term Symbol [h173, h173, h173, h183, h192] h173 := .app e1086 e1080
private def e1088 : HOL.Term Symbol [h173, h173, h173, h183, h192] h173 := .app e1082 e1087
private def e1089 : HOL.Term Symbol [h173, h173, h183, h192] h189 := .lam e1088
private def e1090 : HOL.Term Symbol [h173, h173, h183, h192] h173 := .app e1049 e1089
private def e1091 : HOL.Term Symbol [h173, h183, h192] h189 := .lam e1090
private def e1092 : HOL.Term Symbol [h183, h192] h192 := .lam e1091
private def e1093 : HOL.Term Symbol [h183, h192] h264 := .const (.constant Const.equality t63 q265)
private def e1094 : HOL.Term Symbol [h183, h192] h183 := .var (HOL.Var.vz)
private def e1095 : HOL.Term Symbol [h183, h192] h186 := .app e1093 e1094
private def e1096 : HOL.Term Symbol [h189, h180, h183, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1097 : HOL.Term Symbol [h189, h180, h183, h192] h189 := .var (HOL.Var.vz)
private def e1098 : HOL.Term Symbol [h189, h180, h183, h192] h195 := .app e1096 e1097
private def e1099 : HOL.Term Symbol [h173, h189, h180, h183, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1100 : HOL.Term Symbol [h173, h173, h189, h180, h183, h192] h173 := .var (HOL.Var.vz)
private def e1101 : HOL.Term Symbol [h173, h189, h180, h183, h192] h189 := .lam e1100
private def e1102 : HOL.Term Symbol [h173, h189, h180, h183, h192] h195 := .app e1099 e1101
private def e1103 : HOL.Term Symbol [h173, h189, h180, h183, h192] h173 := .app e1102 e1101
private def e1104 : HOL.Term Symbol [h189, h180, h183, h192] h189 := .lam e1103
private def e1105 : HOL.Term Symbol [h189, h180, h183, h192] h173 := .app e1098 e1104
private def e1106 : HOL.Term Symbol [h180, h183, h192] h195 := .lam e1105
private def e1107 : HOL.Term Symbol [h173, h180, h183, h192] h173 := .var (HOL.Var.vz)
private def e1108 : HOL.Term Symbol [h180, h183, h192] h189 := .lam e1107
private def e1109 : HOL.Term Symbol [h180, h183, h192] h173 := .app e1106 e1108
private def e1110 : HOL.Term Symbol [h183, h192] h183 := .lam e1109
private def e1111 : HOL.Term Symbol [h183, h192] h173 := .app e1095 e1110
private def e1112 : HOL.Term Symbol [h183, h192] h189 := .app e1092 e1111
private def e1113 : HOL.Term Symbol [h173, h173, h173, h180, h183, h192] h192 := .const (.constant Const.equality t17 q193)
private def e1114 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h183, h192] h219 := .const (.constant Const.equality t21 q220)
private def e1115 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183, h192] h192 := .var (HOL.Var.vz)
private def e1116 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1117 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183, h192] h189 := .app e1115 e1116
private def e1118 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1119 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183, h192] h173 := .app e1117 e1118
private def e1120 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h183, h192] h213 := .lam e1119
private def e1121 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h183, h192] h216 := .app e1114 e1120
private def e1122 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1123 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h180, h183, h192] h173 := .var (HOL.Var.vz)
private def e1124 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183, h192] h189 := .lam e1123
private def e1125 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183, h192] h195 := .app e1122 e1124
private def e1126 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183, h192] h173 := .app e1125 e1124
private def e1127 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183, h192] h189 := .app e1115 e1126
private def e1128 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h183, h192] h173 := .app e1127 e1126
private def e1129 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h183, h192] h213 := .lam e1128
private def e1130 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h183, h192] h173 := .app e1121 e1129
private def e1131 : HOL.Term Symbol [h173, h173, h173, h173, h180, h183, h192] h189 := .lam e1130
private def e1132 : HOL.Term Symbol [h173, h173, h173, h180, h183, h192] h192 := .lam e1131
private def e1133 : HOL.Term Symbol [h173, h173, h173, h180, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1134 : HOL.Term Symbol [h173, h173, h173, h180, h183, h192] h189 := .app e1132 e1133
private def e1135 : HOL.Term Symbol [h173, h173, h173, h180, h183, h192] h173 := .var (HOL.Var.vz)
private def e1136 : HOL.Term Symbol [h173, h173, h173, h180, h183, h192] h173 := .app e1134 e1135
private def e1137 : HOL.Term Symbol [h173, h173, h173, h180, h183, h192] h189 := .app e1113 e1136
private def e1138 : HOL.Term Symbol [h173, h173, h173, h180, h183, h192] h173 := .app e1137 e1133
private def e1139 : HOL.Term Symbol [h173, h173, h180, h183, h192] h189 := .lam e1138
private def e1140 : HOL.Term Symbol [h173, h180, h183, h192] h192 := .lam e1139
private def e1141 : HOL.Term Symbol [h180, h173, h180, h183, h192] h315 := .const (.constant Const.equality t101 q316)
private def e1142 : HOL.Term Symbol [h180, h173, h180, h183, h192] h180 := .var (HOL.Var.vz)
private def e1143 : HOL.Term Symbol [h180, h173, h180, h183, h192] h183 := .app e1141 e1142
private def e1144 : HOL.Term Symbol [h177, h180, h173, h180, h183, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1145 : HOL.Term Symbol [h173, h177, h180, h173, h180, h183, h192] h173 := .var (HOL.Var.vz)
private def e1146 : HOL.Term Symbol [h177, h180, h173, h180, h183, h192] h189 := .lam e1145
private def e1147 : HOL.Term Symbol [h177, h180, h173, h180, h183, h192] h195 := .app e1144 e1146
private def e1148 : HOL.Term Symbol [h177, h180, h173, h180, h183, h192] h173 := .app e1147 e1146
private def e1149 : HOL.Term Symbol [h180, h173, h180, h183, h192] h180 := .lam e1148
private def e1150 : HOL.Term Symbol [h180, h173, h180, h183, h192] h173 := .app e1143 e1149
private def e1151 : HOL.Term Symbol [h173, h180, h183, h192] h183 := .lam e1150
private def e1152 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183, h192] h192 := .const (.constant Const.equality t17 q193)
private def e1153 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h183, h192] h219 := .const (.constant Const.equality t21 q220)
private def e1154 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183, h192] h192 := .var (HOL.Var.vz)
private def e1155 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1156 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183, h192] h189 := .app e1154 e1155
private def e1157 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1158 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183, h192] h173 := .app e1156 e1157
private def e1159 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h183, h192] h213 := .lam e1158
private def e1160 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h183, h192] h216 := .app e1153 e1159
private def e1161 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1162 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h177, h173, h180, h183, h192] h173 := .var (HOL.Var.vz)
private def e1163 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183, h192] h189 := .lam e1162
private def e1164 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183, h192] h195 := .app e1161 e1163
private def e1165 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183, h192] h173 := .app e1164 e1163
private def e1166 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183, h192] h189 := .app e1154 e1165
private def e1167 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h183, h192] h173 := .app e1166 e1165
private def e1168 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h183, h192] h213 := .lam e1167
private def e1169 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h183, h192] h173 := .app e1160 e1168
private def e1170 : HOL.Term Symbol [h173, h173, h173, h177, h173, h180, h183, h192] h189 := .lam e1169
private def e1171 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183, h192] h192 := .lam e1170
private def e1172 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1173 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183, h192] h189 := .app e1171 e1172
private def e1174 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183, h192] h173 := .var (HOL.Var.vz)
private def e1175 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183, h192] h173 := .app e1173 e1174
private def e1176 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183, h192] h189 := .app e1152 e1175
private def e1177 : HOL.Term Symbol [h173, h173, h177, h173, h180, h183, h192] h173 := .app e1176 e1172
private def e1178 : HOL.Term Symbol [h173, h177, h173, h180, h183, h192] h189 := .lam e1177
private def e1179 : HOL.Term Symbol [h177, h173, h180, h183, h192] h192 := .lam e1178
private def e1180 : HOL.Term Symbol [h177, h173, h180, h183, h192] h180 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1181 : HOL.Term Symbol [h177, h173, h180, h183, h192] h177 := .var (HOL.Var.vz)
private def e1182 : HOL.Term Symbol [h177, h173, h180, h183, h192] h173 := .app e1180 e1181
private def e1183 : HOL.Term Symbol [h177, h173, h180, h183, h192] h189 := .app e1179 e1182
private def e1184 : HOL.Term Symbol [h177, h173, h180, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1185 : HOL.Term Symbol [h177, h173, h180, h183, h192] h173 := .app e1183 e1184
private def e1186 : HOL.Term Symbol [h173, h180, h183, h192] h180 := .lam e1185
private def e1187 : HOL.Term Symbol [h173, h180, h183, h192] h173 := .app e1151 e1186
private def e1188 : HOL.Term Symbol [h173, h180, h183, h192] h189 := .app e1140 e1187
private def e1189 : HOL.Term Symbol [h173, h180, h183, h192] h173 := .app e1188 e1107
private def e1190 : HOL.Term Symbol [h180, h183, h192] h189 := .lam e1189
private def e1191 : HOL.Term Symbol [h180, h183, h192] h173 := .app e1106 e1190
private def e1192 : HOL.Term Symbol [h183, h192] h183 := .lam e1191
private def e1193 : HOL.Term Symbol [h189, h173, h173, h177, h183, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1194 : HOL.Term Symbol [h189, h173, h173, h177, h183, h192] h189 := .var (HOL.Var.vz)
private def e1195 : HOL.Term Symbol [h189, h173, h173, h177, h183, h192] h195 := .app e1193 e1194
private def e1196 : HOL.Term Symbol [h173, h189, h173, h173, h177, h183, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1197 : HOL.Term Symbol [h173, h173, h189, h173, h173, h177, h183, h192] h173 := .var (HOL.Var.vz)
private def e1198 : HOL.Term Symbol [h173, h189, h173, h173, h177, h183, h192] h189 := .lam e1197
private def e1199 : HOL.Term Symbol [h173, h189, h173, h173, h177, h183, h192] h195 := .app e1196 e1198
private def e1200 : HOL.Term Symbol [h173, h189, h173, h173, h177, h183, h192] h173 := .app e1199 e1198
private def e1201 : HOL.Term Symbol [h189, h173, h173, h177, h183, h192] h189 := .lam e1200
private def e1202 : HOL.Term Symbol [h189, h173, h173, h177, h183, h192] h173 := .app e1195 e1201
private def e1203 : HOL.Term Symbol [h173, h173, h177, h183, h192] h195 := .lam e1202
private def e1204 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183, h192] h192 := .const (.constant Const.equality t17 q193)
private def e1205 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h219 := .const (.constant Const.equality t21 q220)
private def e1206 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h192 := .var (HOL.Var.vz)
private def e1207 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1208 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h189 := .app e1206 e1207
private def e1209 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1210 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h173 := .app e1208 e1209
private def e1211 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h213 := .lam e1210
private def e1212 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h216 := .app e1205 e1211
private def e1213 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h198 := .const (.constant Const.equality t6 q199)
private def e1214 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h173 := .var (HOL.Var.vz)
private def e1215 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h189 := .lam e1214
private def e1216 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h195 := .app e1213 e1215
private def e1217 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h173 := .app e1216 e1215
private def e1218 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h189 := .app e1206 e1217
private def e1219 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h173 := .app e1218 e1217
private def e1220 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h213 := .lam e1219
private def e1221 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h183, h192] h173 := .app e1212 e1220
private def e1222 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h177, h183, h192] h189 := .lam e1221
private def e1223 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183, h192] h192 := .lam e1222
private def e1224 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1225 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183, h192] h189 := .app e1223 e1224
private def e1226 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183, h192] h173 := .var (HOL.Var.vz)
private def e1227 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183, h192] h173 := .app e1225 e1226
private def e1228 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183, h192] h189 := .app e1204 e1227
private def e1229 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h183, h192] h173 := .app e1228 e1224
private def e1230 : HOL.Term Symbol [h173, h173, h173, h173, h177, h183, h192] h189 := .lam e1229
private def e1231 : HOL.Term Symbol [h173, h173, h173, h177, h183, h192] h192 := .lam e1230
private def e1232 : HOL.Term Symbol [h173, h173, h173, h177, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1233 : HOL.Term Symbol [h173, h173, h173, h177, h183, h192] h189 := .app e1231 e1232
private def e1234 : HOL.Term Symbol [h173, h173, h173, h177, h183, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1235 : HOL.Term Symbol [h173, h173, h173, h177, h183, h192] h189 := .app e1231 e1234
private def e1236 : HOL.Term Symbol [h173, h173, h173, h177, h183, h192] h173 := .var (HOL.Var.vz)
private def e1237 : HOL.Term Symbol [h173, h173, h173, h177, h183, h192] h173 := .app e1235 e1236
private def e1238 : HOL.Term Symbol [h173, h173, h173, h177, h183, h192] h173 := .app e1233 e1237
private def e1239 : HOL.Term Symbol [h173, h173, h173, h177, h183, h192] h189 := .app e1231 e1238
private def e1240 : HOL.Term Symbol [h173, h173, h173, h177, h183, h192] h173 := .app e1239 e1236
private def e1241 : HOL.Term Symbol [h173, h173, h177, h183, h192] h189 := .lam e1240
private def e1242 : HOL.Term Symbol [h173, h173, h177, h183, h192] h173 := .app e1203 e1241
private def e1243 : HOL.Term Symbol [h173, h177, h183, h192] h189 := .lam e1242
private def e1244 : HOL.Term Symbol [h177, h183, h192] h192 := .lam e1243
private def e1245 : HOL.Term Symbol [h177, h183, h192] h180 := .const (.variable ⟨Name.mk [] "pointedCarrierProperty", t2⟩ q181)
private def e1246 : HOL.Term Symbol [h177, h183, h192] h177 := .var (HOL.Var.vz)
private def e1247 : HOL.Term Symbol [h177, h183, h192] h173 := .app e1245 e1246
private def e1248 : HOL.Term Symbol [h177, h183, h192] h189 := .app e1244 e1247
private def e1249 : HOL.Term Symbol [h177, h183, h192] h264 := .const (.constant Const.equality t63 q265)
private def e1250 : HOL.Term Symbol [h177, h183, h192] h183 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1251 : HOL.Term Symbol [h177, h183, h192] h186 := .app e1249 e1250
private def e1252 : HOL.Term Symbol [h180, h177, h183, h192] h180 := .var (HOL.Var.vz)
private def e1253 : HOL.Term Symbol [h180, h177, h183, h192] h177 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1254 : HOL.Term Symbol [h180, h177, h183, h192] h173 := .app e1252 e1253
private def e1255 : HOL.Term Symbol [h177, h183, h192] h183 := .lam e1254
private def e1256 : HOL.Term Symbol [h177, h183, h192] h173 := .app e1251 e1255
private def e1257 : HOL.Term Symbol [h177, h183, h192] h173 := .app e1248 e1256
private def e1258 : HOL.Term Symbol [h183, h192] h180 := .lam e1257
private def e1259 : HOL.Term Symbol [h183, h192] h173 := .app e1192 e1258
private def e1260 : HOL.Term Symbol [h183, h192] h173 := .app e1112 e1259
private def e1261 : HOL.Term Symbol [h192] h186 := .lam e1260
private def e1262 : HOL.Term Symbol [h192] h173 := .app e1261 e872
private def e1263 : HOL.Term Symbol [h192] h173 := .app e1038 e1262
private def e1264 : HOL.Term Symbol [] h213 := .lam e1263
private def e1265 : HOL.Term Symbol [] h216 := .app e801 e1264
private def e1266 : HOL.Term Symbol [h192] h198 := .const (.constant Const.equality t6 q199)
private def e1267 : HOL.Term Symbol [h173, h192] h173 := .var (HOL.Var.vz)
private def e1268 : HOL.Term Symbol [h192] h189 := .lam e1267
private def e1269 : HOL.Term Symbol [h192] h195 := .app e1266 e1268
private def e1270 : HOL.Term Symbol [h192] h173 := .app e1269 e1268
private def e1271 : HOL.Term Symbol [h192] h189 := .app e802 e1270
private def e1272 : HOL.Term Symbol [h192] h173 := .app e1271 e1270
private def e1273 : HOL.Term Symbol [] h213 := .lam e1272
private def e1274 : HOL.Term Symbol [] h173 := .app e1265 e1273
private def c1275 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1274
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
private def e1290 : HOL.Term Symbol [h173, h173] h219 := .const (.constant Const.equality t21 q220)
private def e1291 : HOL.Term Symbol [h192, h173, h173] h192 := .var (HOL.Var.vz)
private def e1292 : HOL.Term Symbol [h192, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1293 : HOL.Term Symbol [h192, h173, h173] h189 := .app e1291 e1292
private def e1294 : HOL.Term Symbol [h192, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1295 : HOL.Term Symbol [h192, h173, h173] h173 := .app e1293 e1294
private def e1296 : HOL.Term Symbol [h173, h173] h213 := .lam e1295
private def e1297 : HOL.Term Symbol [h173, h173] h216 := .app e1290 e1296
private def e1298 : HOL.Term Symbol [h192, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1299 : HOL.Term Symbol [h173, h192, h173, h173] h173 := .var (HOL.Var.vz)
private def e1300 : HOL.Term Symbol [h192, h173, h173] h189 := .lam e1299
private def e1301 : HOL.Term Symbol [h192, h173, h173] h195 := .app e1298 e1300
private def e1302 : HOL.Term Symbol [h192, h173, h173] h173 := .app e1301 e1300
private def e1303 : HOL.Term Symbol [h192, h173, h173] h189 := .app e1291 e1302
private def e1304 : HOL.Term Symbol [h192, h173, h173] h173 := .app e1303 e1302
private def e1305 : HOL.Term Symbol [h173, h173] h213 := .lam e1304
private def e1306 : HOL.Term Symbol [h173, h173] h173 := .app e1297 e1305
private def e1307 : HOL.Term Symbol [h173] h189 := .lam e1306
private def e1308 : HOL.Term Symbol [] h192 := .lam e1307
private def e1309 : HOL.Term Symbol [] h173 := .const (.variable ⟨Name.mk [""] "x", t1⟩ q174)
private def e1310 : HOL.Term Symbol [] h189 := .app e1308 e1309
private def c1311 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1310
private theorem n1312 : s1289.toDB [] = c1311.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1313 : CheckedSourceTerm := ⟨s1289, t4, by rw [← DBTerm.inferType_toDB [] s1289, n1312]; exact c1311.checked.trans (congrArg some v191)⟩
private def r1314 : InferenceRequest := .beta k1313
private def e1315 : HOL.Term Symbol [] h195 := .app e727 e1310
private def e1316 : HOL.Term Symbol [h173] h219 := .const (.constant Const.equality t21 q220)
private def e1317 : HOL.Term Symbol [h192, h173] h192 := .var (HOL.Var.vz)
private def e1318 : HOL.Term Symbol [h192, h173] h173 := .const (.variable ⟨Name.mk [""] "x", t1⟩ q174)
private def e1319 : HOL.Term Symbol [h192, h173] h189 := .app e1317 e1318
private def e1320 : HOL.Term Symbol [h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1321 : HOL.Term Symbol [h192, h173] h173 := .app e1319 e1320
private def e1322 : HOL.Term Symbol [h173] h213 := .lam e1321
private def e1323 : HOL.Term Symbol [h173] h216 := .app e1316 e1322
private def e1324 : HOL.Term Symbol [h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1325 : HOL.Term Symbol [h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e1326 : HOL.Term Symbol [h192, h173] h189 := .lam e1325
private def e1327 : HOL.Term Symbol [h192, h173] h195 := .app e1324 e1326
private def e1328 : HOL.Term Symbol [h192, h173] h173 := .app e1327 e1326
private def e1329 : HOL.Term Symbol [h192, h173] h189 := .app e1317 e1328
private def e1330 : HOL.Term Symbol [h192, h173] h173 := .app e1329 e1328
private def e1331 : HOL.Term Symbol [h173] h213 := .lam e1330
private def e1332 : HOL.Term Symbol [h173] h173 := .app e1323 e1331
private def e1333 : HOL.Term Symbol [] h189 := .lam e1332
private def e1334 : HOL.Term Symbol [] h173 := .app e1315 e1333
private def c1335 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1334
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
private def e1409 : HOL.Term Symbol [] h189 := .app e1308 e711
private def e1410 : HOL.Term Symbol [] h195 := .app e727 e1409
private def e1411 : HOL.Term Symbol [h189, h173, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1412 : HOL.Term Symbol [h189, h173, h173, h192, h173] h189 := .var (HOL.Var.vz)
private def e1413 : HOL.Term Symbol [h189, h173, h173, h192, h173] h195 := .app e1411 e1412
private def e1414 : HOL.Term Symbol [h173, h189, h173, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1415 : HOL.Term Symbol [h173, h173, h189, h173, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e1416 : HOL.Term Symbol [h173, h189, h173, h173, h192, h173] h189 := .lam e1415
private def e1417 : HOL.Term Symbol [h173, h189, h173, h173, h192, h173] h195 := .app e1414 e1416
private def e1418 : HOL.Term Symbol [h173, h189, h173, h173, h192, h173] h173 := .app e1417 e1416
private def e1419 : HOL.Term Symbol [h189, h173, h173, h192, h173] h189 := .lam e1418
private def e1420 : HOL.Term Symbol [h189, h173, h173, h192, h173] h173 := .app e1413 e1419
private def e1421 : HOL.Term Symbol [h173, h173, h192, h173] h195 := .lam e1420
private def e1422 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h192 := .const (.constant Const.equality t17 q193)
private def e1423 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h192, h173] h219 := .const (.constant Const.equality t21 q220)
private def e1424 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192, h173] h192 := .var (HOL.Var.vz)
private def e1425 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1426 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192, h173] h189 := .app e1424 e1425
private def e1427 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1428 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192, h173] h173 := .app e1426 e1427
private def e1429 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h192, h173] h213 := .lam e1428
private def e1430 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h192, h173] h216 := .app e1423 e1429
private def e1431 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1432 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e1433 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192, h173] h189 := .lam e1432
private def e1434 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192, h173] h195 := .app e1431 e1433
private def e1435 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192, h173] h173 := .app e1434 e1433
private def e1436 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192, h173] h189 := .app e1424 e1435
private def e1437 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h192, h173] h173 := .app e1436 e1435
private def e1438 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h192, h173] h213 := .lam e1437
private def e1439 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h192, h173] h173 := .app e1430 e1438
private def e1440 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h192, h173] h189 := .lam e1439
private def e1441 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h192 := .lam e1440
private def e1442 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1443 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h189 := .app e1441 e1442
private def e1444 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e1445 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h173 := .app e1443 e1444
private def e1446 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h189 := .app e1422 e1445
private def e1447 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h173 := .app e1446 e1442
private def e1448 : HOL.Term Symbol [h173, h173, h173, h173, h192, h173] h189 := .lam e1447
private def e1449 : HOL.Term Symbol [h173, h173, h173, h192, h173] h192 := .lam e1448
private def e1450 : HOL.Term Symbol [h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1451 : HOL.Term Symbol [h173, h173, h173, h192, h173] h189 := .app e1449 e1450
private def e1452 : HOL.Term Symbol [h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e1453 : HOL.Term Symbol [h173, h173, h173, h192, h173] h173 := .app e1451 e1452
private def e1454 : HOL.Term Symbol [h173, h173, h173, h192, h173] h189 := .app e1449 e1453
private def e1455 : HOL.Term Symbol [h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1456 : HOL.Term Symbol [h173, h173, h173, h192, h173] h189 := .app e1449 e1455
private def e1457 : HOL.Term Symbol [h173, h173, h173, h192, h173] h173 := .app e1456 e1452
private def e1458 : HOL.Term Symbol [h173, h173, h173, h192, h173] h189 := .app e1449 e1457
private def e1459 : HOL.Term Symbol [h173, h173, h173, h192, h173] h173 := .app e1458 e1452
private def e1460 : HOL.Term Symbol [h173, h173, h173, h192, h173] h173 := .app e1454 e1459
private def e1461 : HOL.Term Symbol [h173, h173, h192, h173] h189 := .lam e1460
private def e1462 : HOL.Term Symbol [h173, h173, h192, h173] h173 := .app e1421 e1461
private def e1463 : HOL.Term Symbol [h173, h192, h173] h189 := .lam e1462
private def e1464 : HOL.Term Symbol [h192, h173] h192 := .lam e1463
private def e1465 : HOL.Term Symbol [h192, h173] h264 := .const (.constant Const.equality t63 q265)
private def e1466 : HOL.Term Symbol [h189, h180, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1467 : HOL.Term Symbol [h189, h180, h192, h173] h189 := .var (HOL.Var.vz)
private def e1468 : HOL.Term Symbol [h189, h180, h192, h173] h195 := .app e1466 e1467
private def e1469 : HOL.Term Symbol [h173, h189, h180, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1470 : HOL.Term Symbol [h173, h173, h189, h180, h192, h173] h173 := .var (HOL.Var.vz)
private def e1471 : HOL.Term Symbol [h173, h189, h180, h192, h173] h189 := .lam e1470
private def e1472 : HOL.Term Symbol [h173, h189, h180, h192, h173] h195 := .app e1469 e1471
private def e1473 : HOL.Term Symbol [h173, h189, h180, h192, h173] h173 := .app e1472 e1471
private def e1474 : HOL.Term Symbol [h189, h180, h192, h173] h189 := .lam e1473
private def e1475 : HOL.Term Symbol [h189, h180, h192, h173] h173 := .app e1468 e1474
private def e1476 : HOL.Term Symbol [h180, h192, h173] h195 := .lam e1475
private def e1477 : HOL.Term Symbol [h173, h180, h192, h173] h173 := .var (HOL.Var.vz)
private def e1478 : HOL.Term Symbol [h180, h192, h173] h189 := .lam e1477
private def e1479 : HOL.Term Symbol [h180, h192, h173] h173 := .app e1476 e1478
private def e1480 : HOL.Term Symbol [h192, h173] h183 := .lam e1479
private def e1481 : HOL.Term Symbol [h192, h173] h186 := .app e1465 e1480
private def e1482 : HOL.Term Symbol [h192, h173] h173 := .app e1481 e1480
private def e1483 : HOL.Term Symbol [h192, h173] h189 := .app e1464 e1482
private def e1484 : HOL.Term Symbol [h173, h173, h173, h180, h192, h173] h192 := .const (.constant Const.equality t17 q193)
private def e1485 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h192, h173] h219 := .const (.constant Const.equality t21 q220)
private def e1486 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192, h173] h192 := .var (HOL.Var.vz)
private def e1487 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1488 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192, h173] h189 := .app e1486 e1487
private def e1489 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1490 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192, h173] h173 := .app e1488 e1489
private def e1491 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h192, h173] h213 := .lam e1490
private def e1492 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h192, h173] h216 := .app e1485 e1491
private def e1493 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1494 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h180, h192, h173] h173 := .var (HOL.Var.vz)
private def e1495 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192, h173] h189 := .lam e1494
private def e1496 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192, h173] h195 := .app e1493 e1495
private def e1497 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192, h173] h173 := .app e1496 e1495
private def e1498 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192, h173] h189 := .app e1486 e1497
private def e1499 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h192, h173] h173 := .app e1498 e1497
private def e1500 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h192, h173] h213 := .lam e1499
private def e1501 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h192, h173] h173 := .app e1492 e1500
private def e1502 : HOL.Term Symbol [h173, h173, h173, h173, h180, h192, h173] h189 := .lam e1501
private def e1503 : HOL.Term Symbol [h173, h173, h173, h180, h192, h173] h192 := .lam e1502
private def e1504 : HOL.Term Symbol [h173, h173, h173, h180, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1505 : HOL.Term Symbol [h173, h173, h173, h180, h192, h173] h189 := .app e1503 e1504
private def e1506 : HOL.Term Symbol [h173, h173, h173, h180, h192, h173] h173 := .var (HOL.Var.vz)
private def e1507 : HOL.Term Symbol [h173, h173, h173, h180, h192, h173] h173 := .app e1505 e1506
private def e1508 : HOL.Term Symbol [h173, h173, h173, h180, h192, h173] h189 := .app e1484 e1507
private def e1509 : HOL.Term Symbol [h173, h173, h173, h180, h192, h173] h173 := .app e1508 e1504
private def e1510 : HOL.Term Symbol [h173, h173, h180, h192, h173] h189 := .lam e1509
private def e1511 : HOL.Term Symbol [h173, h180, h192, h173] h192 := .lam e1510
private def e1512 : HOL.Term Symbol [h180, h173, h180, h192, h173] h315 := .const (.constant Const.equality t101 q316)
private def e1513 : HOL.Term Symbol [h180, h173, h180, h192, h173] h180 := .var (HOL.Var.vz)
private def e1514 : HOL.Term Symbol [h180, h173, h180, h192, h173] h183 := .app e1512 e1513
private def e1515 : HOL.Term Symbol [h177, h180, h173, h180, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1516 : HOL.Term Symbol [h173, h177, h180, h173, h180, h192, h173] h173 := .var (HOL.Var.vz)
private def e1517 : HOL.Term Symbol [h177, h180, h173, h180, h192, h173] h189 := .lam e1516
private def e1518 : HOL.Term Symbol [h177, h180, h173, h180, h192, h173] h195 := .app e1515 e1517
private def e1519 : HOL.Term Symbol [h177, h180, h173, h180, h192, h173] h173 := .app e1518 e1517
private def e1520 : HOL.Term Symbol [h180, h173, h180, h192, h173] h180 := .lam e1519
private def e1521 : HOL.Term Symbol [h180, h173, h180, h192, h173] h173 := .app e1514 e1520
private def e1522 : HOL.Term Symbol [h173, h180, h192, h173] h183 := .lam e1521
private def e1523 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192, h173] h192 := .const (.constant Const.equality t17 q193)
private def e1524 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h192, h173] h219 := .const (.constant Const.equality t21 q220)
private def e1525 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192, h173] h192 := .var (HOL.Var.vz)
private def e1526 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1527 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192, h173] h189 := .app e1525 e1526
private def e1528 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1529 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192, h173] h173 := .app e1527 e1528
private def e1530 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h192, h173] h213 := .lam e1529
private def e1531 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h192, h173] h216 := .app e1524 e1530
private def e1532 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1533 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h177, h173, h180, h192, h173] h173 := .var (HOL.Var.vz)
private def e1534 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192, h173] h189 := .lam e1533
private def e1535 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192, h173] h195 := .app e1532 e1534
private def e1536 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192, h173] h173 := .app e1535 e1534
private def e1537 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192, h173] h189 := .app e1525 e1536
private def e1538 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h192, h173] h173 := .app e1537 e1536
private def e1539 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h192, h173] h213 := .lam e1538
private def e1540 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h192, h173] h173 := .app e1531 e1539
private def e1541 : HOL.Term Symbol [h173, h173, h173, h177, h173, h180, h192, h173] h189 := .lam e1540
private def e1542 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192, h173] h192 := .lam e1541
private def e1543 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1544 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192, h173] h189 := .app e1542 e1543
private def e1545 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192, h173] h173 := .var (HOL.Var.vz)
private def e1546 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192, h173] h173 := .app e1544 e1545
private def e1547 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192, h173] h189 := .app e1523 e1546
private def e1548 : HOL.Term Symbol [h173, h173, h177, h173, h180, h192, h173] h173 := .app e1547 e1543
private def e1549 : HOL.Term Symbol [h173, h177, h173, h180, h192, h173] h189 := .lam e1548
private def e1550 : HOL.Term Symbol [h177, h173, h180, h192, h173] h192 := .lam e1549
private def e1551 : HOL.Term Symbol [h177, h173, h180, h192, h173] h180 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1552 : HOL.Term Symbol [h177, h173, h180, h192, h173] h177 := .var (HOL.Var.vz)
private def e1553 : HOL.Term Symbol [h177, h173, h180, h192, h173] h173 := .app e1551 e1552
private def e1554 : HOL.Term Symbol [h177, h173, h180, h192, h173] h189 := .app e1550 e1553
private def e1555 : HOL.Term Symbol [h177, h173, h180, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1556 : HOL.Term Symbol [h177, h173, h180, h192, h173] h173 := .app e1554 e1555
private def e1557 : HOL.Term Symbol [h173, h180, h192, h173] h180 := .lam e1556
private def e1558 : HOL.Term Symbol [h173, h180, h192, h173] h173 := .app e1522 e1557
private def e1559 : HOL.Term Symbol [h173, h180, h192, h173] h189 := .app e1511 e1558
private def e1560 : HOL.Term Symbol [h173, h180, h192, h173] h173 := .app e1559 e1477
private def e1561 : HOL.Term Symbol [h180, h192, h173] h189 := .lam e1560
private def e1562 : HOL.Term Symbol [h180, h192, h173] h173 := .app e1476 e1561
private def e1563 : HOL.Term Symbol [h192, h173] h183 := .lam e1562
private def e1564 : HOL.Term Symbol [h189, h173, h173, h177, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1565 : HOL.Term Symbol [h189, h173, h173, h177, h192, h173] h189 := .var (HOL.Var.vz)
private def e1566 : HOL.Term Symbol [h189, h173, h173, h177, h192, h173] h195 := .app e1564 e1565
private def e1567 : HOL.Term Symbol [h173, h189, h173, h173, h177, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1568 : HOL.Term Symbol [h173, h173, h189, h173, h173, h177, h192, h173] h173 := .var (HOL.Var.vz)
private def e1569 : HOL.Term Symbol [h173, h189, h173, h173, h177, h192, h173] h189 := .lam e1568
private def e1570 : HOL.Term Symbol [h173, h189, h173, h173, h177, h192, h173] h195 := .app e1567 e1569
private def e1571 : HOL.Term Symbol [h173, h189, h173, h173, h177, h192, h173] h173 := .app e1570 e1569
private def e1572 : HOL.Term Symbol [h189, h173, h173, h177, h192, h173] h189 := .lam e1571
private def e1573 : HOL.Term Symbol [h189, h173, h173, h177, h192, h173] h173 := .app e1566 e1572
private def e1574 : HOL.Term Symbol [h173, h173, h177, h192, h173] h195 := .lam e1573
private def e1575 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192, h173] h192 := .const (.constant Const.equality t17 q193)
private def e1576 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h219 := .const (.constant Const.equality t21 q220)
private def e1577 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h192 := .var (HOL.Var.vz)
private def e1578 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1579 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h189 := .app e1577 e1578
private def e1580 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1581 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h173 := .app e1579 e1580
private def e1582 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h213 := .lam e1581
private def e1583 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h216 := .app e1576 e1582
private def e1584 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1585 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h173 := .var (HOL.Var.vz)
private def e1586 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h189 := .lam e1585
private def e1587 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h195 := .app e1584 e1586
private def e1588 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h173 := .app e1587 e1586
private def e1589 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h189 := .app e1577 e1588
private def e1590 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h173 := .app e1589 e1588
private def e1591 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h213 := .lam e1590
private def e1592 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h192, h173] h173 := .app e1583 e1591
private def e1593 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h177, h192, h173] h189 := .lam e1592
private def e1594 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192, h173] h192 := .lam e1593
private def e1595 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1596 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192, h173] h189 := .app e1594 e1595
private def e1597 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192, h173] h173 := .var (HOL.Var.vz)
private def e1598 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192, h173] h173 := .app e1596 e1597
private def e1599 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192, h173] h189 := .app e1575 e1598
private def e1600 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h192, h173] h173 := .app e1599 e1595
private def e1601 : HOL.Term Symbol [h173, h173, h173, h173, h177, h192, h173] h189 := .lam e1600
private def e1602 : HOL.Term Symbol [h173, h173, h173, h177, h192, h173] h192 := .lam e1601
private def e1603 : HOL.Term Symbol [h173, h173, h173, h177, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1604 : HOL.Term Symbol [h173, h173, h173, h177, h192, h173] h189 := .app e1602 e1603
private def e1605 : HOL.Term Symbol [h173, h173, h173, h177, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1606 : HOL.Term Symbol [h173, h173, h173, h177, h192, h173] h189 := .app e1602 e1605
private def e1607 : HOL.Term Symbol [h173, h173, h173, h177, h192, h173] h173 := .var (HOL.Var.vz)
private def e1608 : HOL.Term Symbol [h173, h173, h173, h177, h192, h173] h173 := .app e1606 e1607
private def e1609 : HOL.Term Symbol [h173, h173, h173, h177, h192, h173] h173 := .app e1604 e1608
private def e1610 : HOL.Term Symbol [h173, h173, h173, h177, h192, h173] h189 := .app e1602 e1609
private def e1611 : HOL.Term Symbol [h173, h173, h173, h177, h192, h173] h173 := .app e1610 e1607
private def e1612 : HOL.Term Symbol [h173, h173, h177, h192, h173] h189 := .lam e1611
private def e1613 : HOL.Term Symbol [h173, h173, h177, h192, h173] h173 := .app e1574 e1612
private def e1614 : HOL.Term Symbol [h173, h177, h192, h173] h189 := .lam e1613
private def e1615 : HOL.Term Symbol [h177, h192, h173] h192 := .lam e1614
private def e1616 : HOL.Term Symbol [h177, h192, h173] h180 := .const (.variable ⟨Name.mk [] "pointedCarrierProperty", t2⟩ q181)
private def e1617 : HOL.Term Symbol [h177, h192, h173] h177 := .var (HOL.Var.vz)
private def e1618 : HOL.Term Symbol [h177, h192, h173] h173 := .app e1616 e1617
private def e1619 : HOL.Term Symbol [h177, h192, h173] h189 := .app e1615 e1618
private def e1620 : HOL.Term Symbol [h177, h192, h173] h264 := .const (.constant Const.equality t63 q265)
private def e1621 : HOL.Term Symbol [h189, h180, h177, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1622 : HOL.Term Symbol [h189, h180, h177, h192, h173] h189 := .var (HOL.Var.vz)
private def e1623 : HOL.Term Symbol [h189, h180, h177, h192, h173] h195 := .app e1621 e1622
private def e1624 : HOL.Term Symbol [h173, h189, h180, h177, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1625 : HOL.Term Symbol [h173, h173, h189, h180, h177, h192, h173] h173 := .var (HOL.Var.vz)
private def e1626 : HOL.Term Symbol [h173, h189, h180, h177, h192, h173] h189 := .lam e1625
private def e1627 : HOL.Term Symbol [h173, h189, h180, h177, h192, h173] h195 := .app e1624 e1626
private def e1628 : HOL.Term Symbol [h173, h189, h180, h177, h192, h173] h173 := .app e1627 e1626
private def e1629 : HOL.Term Symbol [h189, h180, h177, h192, h173] h189 := .lam e1628
private def e1630 : HOL.Term Symbol [h189, h180, h177, h192, h173] h173 := .app e1623 e1629
private def e1631 : HOL.Term Symbol [h180, h177, h192, h173] h195 := .lam e1630
private def e1632 : HOL.Term Symbol [h173, h180, h177, h192, h173] h173 := .var (HOL.Var.vz)
private def e1633 : HOL.Term Symbol [h180, h177, h192, h173] h189 := .lam e1632
private def e1634 : HOL.Term Symbol [h180, h177, h192, h173] h173 := .app e1631 e1633
private def e1635 : HOL.Term Symbol [h177, h192, h173] h183 := .lam e1634
private def e1636 : HOL.Term Symbol [h177, h192, h173] h186 := .app e1620 e1635
private def e1637 : HOL.Term Symbol [h180, h177, h192, h173] h180 := .var (HOL.Var.vz)
private def e1638 : HOL.Term Symbol [h180, h177, h192, h173] h177 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1639 : HOL.Term Symbol [h180, h177, h192, h173] h173 := .app e1637 e1638
private def e1640 : HOL.Term Symbol [h177, h192, h173] h183 := .lam e1639
private def e1641 : HOL.Term Symbol [h177, h192, h173] h173 := .app e1636 e1640
private def e1642 : HOL.Term Symbol [h177, h192, h173] h173 := .app e1619 e1641
private def e1643 : HOL.Term Symbol [h192, h173] h180 := .lam e1642
private def e1644 : HOL.Term Symbol [h192, h173] h173 := .app e1563 e1643
private def e1645 : HOL.Term Symbol [h192, h173] h173 := .app e1483 e1644
private def e1646 : HOL.Term Symbol [h192, h173] h189 := .app e1317 e1645
private def e1647 : HOL.Term Symbol [h192, h173] h173 := .app e1646 e1320
private def e1648 : HOL.Term Symbol [h173] h213 := .lam e1647
private def e1649 : HOL.Term Symbol [h173] h216 := .app e1316 e1648
private def e1650 : HOL.Term Symbol [h173] h173 := .app e1649 e1331
private def e1651 : HOL.Term Symbol [] h189 := .lam e1650
private def e1652 : HOL.Term Symbol [] h173 := .app e1410 e1651
private def c1653 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1652
private def f1654 : Theorem := Theorem.emptyResult ([].toFinset) c1653
private def r1655 : InferenceRequest := .mkComb f1654 f737
private def e1656 : HOL.Term Symbol [] h173 := .app e1409 e686
private def e1657 : HOL.Term Symbol [] h189 := .app e445 e1656
private def e1658 : HOL.Term Symbol [] h173 := .app e1651 e686
private def e1659 : HOL.Term Symbol [] h173 := .app e1657 e1658
private def c1660 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1659
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
private def e1753 : HOL.Term Symbol [] h173 := .app e1651 e1309
private def c1754 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1753
private theorem n1755 : s1752.toDB [] = c1754.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1756 : CheckedSourceTerm := ⟨s1752, t1, by rw [← DBTerm.inferType_toDB [] s1752, n1755]; exact c1754.checked.trans (congrArg some v175)⟩
private def r1757 : InferenceRequest := .beta k1756
private def e1758 : HOL.Term Symbol [] h189 := .app e445 e1753
private def e1759 : HOL.Term Symbol [h192] h173 := .const (.variable ⟨Name.mk [""] "x", t1⟩ q174)
private def e1760 : HOL.Term Symbol [h192] h173 := .app e1038 e1759
private def e1761 : HOL.Term Symbol [] h213 := .lam e1760
private def e1762 : HOL.Term Symbol [] h216 := .app e801 e1761
private def e1763 : HOL.Term Symbol [] h173 := .app e1762 e1273
private def e1764 : HOL.Term Symbol [] h173 := .app e1758 e1763
private def c1765 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1764
private def f1766 : Theorem := Theorem.emptyResult ([].toFinset) c1765
private def s1767 : SourceTerm := SourceTerm.app s171 s681
private theorem n1768 : s1767.toDB [] = c733.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1769 : CheckedSourceTerm := ⟨s1767, t1, by rw [← DBTerm.inferType_toDB [] s1767, n1768]; exact c733.checked.trans (congrArg some v175)⟩
private def r1770 : InferenceRequest := .inst [(k1769, s1278)] f1766
private def e1771 : HOL.Term Symbol [] h189 := .app e445 e1658
private def e1772 : HOL.Term Symbol [] h173 := .app e1771 e1274
private def c1773 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1772
private def f1774 : Theorem := Theorem.emptyResult ([].toFinset) c1773
private def r1775 : InferenceRequest := .trans f1661 f1774
private def e1776 : HOL.Term Symbol [] h173 := .app e1657 e1274
private def c1777 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1776
private def f1778 : Theorem := Theorem.emptyResult ([].toFinset) c1777
private def r1779 : InferenceRequest := .mkComb f725 f1778
private def e1780 : HOL.Term Symbol [] h195 := .app e727 e1657
private def e1781 : HOL.Term Symbol [] h189 := .app e445 e1274
private def e1782 : HOL.Term Symbol [] h173 := .app e1780 e1781
private def c1783 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1782
private def f1784 : Theorem := Theorem.emptyResult ([].toFinset) c1783
private def c1785 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1656
private def r1786 : InferenceRequest := .refl c1785
private def e1787 : HOL.Term Symbol [] h173 := .app e1657 e1656
private def c1788 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1787
private def f1789 : Theorem := Theorem.emptyResult ([].toFinset) c1788
private def r1790 : InferenceRequest := .mkComb f1784 f1789
private def e1791 : HOL.Term Symbol [] h189 := .app e445 e1787
private def e1792 : HOL.Term Symbol [] h173 := .app e1781 e1656
private def e1793 : HOL.Term Symbol [] h173 := .app e1791 e1792
private def c1794 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1793
private def f1795 : Theorem := Theorem.emptyResult ([].toFinset) c1794
private def r1796 : InferenceRequest := .eqMp f1795 f1789
private def c1797 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1792
private def f1798 : Theorem := Theorem.emptyResult ([].toFinset) c1797
private def r1799 : InferenceRequest := .eqMp f1798 f1276
private def f1800 : Theorem := Theorem.emptyResult ([c747].toFinset) c1785
private def r1801 : InferenceRequest := .assume c1785
private def f1802 : Theorem := Theorem.emptyResult ([c1785].toFinset) c1785
private def r1803 : InferenceRequest := .eqMp f1778 f1802
private def f1804 : Theorem := Theorem.emptyResult ([c1785].toFinset) c1275
private def e1805 : HOL.Term Symbol [h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1806 : HOL.Term Symbol [h173] h189 := .lam e1805
private def e1807 : HOL.Term Symbol [] h192 := .lam e1806
private def c1808 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1807
private def r1809 : InferenceRequest := .refl c1808
private def e1810 : HOL.Term Symbol [] h213 := .app e721 e1807
private def e1811 : HOL.Term Symbol [] h173 := .app e1810 e1807
private def c1812 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1811
private def f1813 : Theorem := Theorem.emptyResult ([].toFinset) c1812
private def r1814 : InferenceRequest := .mkComb f1804 f1813
private def e1815 : HOL.Term Symbol [] h173 := .app e1264 e1807
private def e1816 : HOL.Term Symbol [] h189 := .app e445 e1815
private def e1817 : HOL.Term Symbol [] h173 := .app e1273 e1807
private def e1818 : HOL.Term Symbol [] h173 := .app e1816 e1817
private def c1819 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1818
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
private def e1844 : HOL.Term Symbol [] h173 := .app e1264 e763
private def c1845 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1844
private theorem n1846 : s1843.toDB [] = c1845.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1847 : CheckedSourceTerm := ⟨s1843, t1, by rw [← DBTerm.inferType_toDB [] s1843, n1846]; exact c1845.checked.trans (congrArg some v175)⟩
private def r1848 : InferenceRequest := .beta k1847
private def e1849 : HOL.Term Symbol [] h189 := .app e445 e1844
private def e1850 : HOL.Term Symbol [] h173 := .app e1849 e794
private def c1851 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1850
private def f1852 : Theorem := Theorem.emptyResult ([].toFinset) c1851
private def s1853 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s1278
private def s1854 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s1853
private theorem n1855 : s1854.toDB [] = c1808.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1856 : CheckedSourceTerm := ⟨s1854, t17, by rw [← DBTerm.inferType_toDB [] s1854, n1855]; exact c1808.checked.trans (congrArg some v194)⟩
private def r1857 : InferenceRequest := .inst [(k1856, s1821)] f1852
private def e1858 : HOL.Term Symbol [] h189 := .app e1807 e711
private def e1859 : HOL.Term Symbol [] h173 := .app e1858 e686
private def e1860 : HOL.Term Symbol [] h173 := .app e1816 e1859
private def c1861 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1860
private def f1862 : Theorem := Theorem.emptyResult ([].toFinset) c1861
private def s1863 : SourceTerm := SourceTerm.app s1854 s1278
private def e1864 : HOL.Term Symbol [] h189 := .app e1807 e1309
private def c1865 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1864
private theorem n1866 : s1863.toDB [] = c1865.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k1867 : CheckedSourceTerm := ⟨s1863, t4, by rw [← DBTerm.inferType_toDB [] s1863, n1866]; exact c1865.checked.trans (congrArg some v191)⟩
private def r1868 : InferenceRequest := .beta k1867
private def e1869 : HOL.Term Symbol [] h195 := .app e727 e1864
private def e1870 : HOL.Term Symbol [h173] h173 := .const (.variable ⟨Name.mk [""] "x", t1⟩ q174)
private def e1871 : HOL.Term Symbol [] h189 := .lam e1870
private def e1872 : HOL.Term Symbol [] h173 := .app e1869 e1871
private def c1873 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1872
private def f1874 : Theorem := Theorem.emptyResult ([].toFinset) c1873
private def r1875 : InferenceRequest := .inst [(k1407, s1278)] f1874
private def e1876 : HOL.Term Symbol [] h195 := .app e727 e1858
private def e1877 : HOL.Term Symbol [h189, h173, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1878 : HOL.Term Symbol [h189, h173, h173, h173] h189 := .var (HOL.Var.vz)
private def e1879 : HOL.Term Symbol [h189, h173, h173, h173] h195 := .app e1877 e1878
private def e1880 : HOL.Term Symbol [h173, h189, h173, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1881 : HOL.Term Symbol [h173, h173, h189, h173, h173, h173] h173 := .var (HOL.Var.vz)
private def e1882 : HOL.Term Symbol [h173, h189, h173, h173, h173] h189 := .lam e1881
private def e1883 : HOL.Term Symbol [h173, h189, h173, h173, h173] h195 := .app e1880 e1882
private def e1884 : HOL.Term Symbol [h173, h189, h173, h173, h173] h173 := .app e1883 e1882
private def e1885 : HOL.Term Symbol [h189, h173, h173, h173] h189 := .lam e1884
private def e1886 : HOL.Term Symbol [h189, h173, h173, h173] h173 := .app e1879 e1885
private def e1887 : HOL.Term Symbol [h173, h173, h173] h195 := .lam e1886
private def e1888 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h192 := .const (.constant Const.equality t17 q193)
private def e1889 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h173] h219 := .const (.constant Const.equality t21 q220)
private def e1890 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h173] h192 := .var (HOL.Var.vz)
private def e1891 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1892 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h173] h189 := .app e1890 e1891
private def e1893 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1894 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h173] h173 := .app e1892 e1893
private def e1895 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h173] h213 := .lam e1894
private def e1896 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h173] h216 := .app e1889 e1895
private def e1897 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1898 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vz)
private def e1899 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h173] h189 := .lam e1898
private def e1900 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h173] h195 := .app e1897 e1899
private def e1901 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h173] h173 := .app e1900 e1899
private def e1902 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h173] h189 := .app e1890 e1901
private def e1903 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h173] h173 := .app e1902 e1901
private def e1904 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h173] h213 := .lam e1903
private def e1905 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h173] h173 := .app e1896 e1904
private def e1906 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173] h189 := .lam e1905
private def e1907 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h192 := .lam e1906
private def e1908 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1909 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h189 := .app e1907 e1908
private def e1910 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vz)
private def e1911 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h173 := .app e1909 e1910
private def e1912 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h189 := .app e1888 e1911
private def e1913 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h173 := .app e1912 e1908
private def e1914 : HOL.Term Symbol [h173, h173, h173, h173, h173] h189 := .lam e1913
private def e1915 : HOL.Term Symbol [h173, h173, h173, h173] h192 := .lam e1914
private def e1916 : HOL.Term Symbol [h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1917 : HOL.Term Symbol [h173, h173, h173, h173] h189 := .app e1915 e1916
private def e1918 : HOL.Term Symbol [h173, h173, h173, h173] h173 := .var (HOL.Var.vz)
private def e1919 : HOL.Term Symbol [h173, h173, h173, h173] h173 := .app e1917 e1918
private def e1920 : HOL.Term Symbol [h173, h173, h173, h173] h189 := .app e1915 e1919
private def e1921 : HOL.Term Symbol [h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1922 : HOL.Term Symbol [h173, h173, h173, h173] h189 := .app e1915 e1921
private def e1923 : HOL.Term Symbol [h173, h173, h173, h173] h173 := .app e1922 e1918
private def e1924 : HOL.Term Symbol [h173, h173, h173, h173] h189 := .app e1915 e1923
private def e1925 : HOL.Term Symbol [h173, h173, h173, h173] h173 := .app e1924 e1918
private def e1926 : HOL.Term Symbol [h173, h173, h173, h173] h173 := .app e1920 e1925
private def e1927 : HOL.Term Symbol [h173, h173, h173] h189 := .lam e1926
private def e1928 : HOL.Term Symbol [h173, h173, h173] h173 := .app e1887 e1927
private def e1929 : HOL.Term Symbol [h173, h173] h189 := .lam e1928
private def e1930 : HOL.Term Symbol [h173] h192 := .lam e1929
private def e1931 : HOL.Term Symbol [h173] h264 := .const (.constant Const.equality t63 q265)
private def e1932 : HOL.Term Symbol [h189, h180, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1933 : HOL.Term Symbol [h189, h180, h173] h189 := .var (HOL.Var.vz)
private def e1934 : HOL.Term Symbol [h189, h180, h173] h195 := .app e1932 e1933
private def e1935 : HOL.Term Symbol [h173, h189, h180, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1936 : HOL.Term Symbol [h173, h173, h189, h180, h173] h173 := .var (HOL.Var.vz)
private def e1937 : HOL.Term Symbol [h173, h189, h180, h173] h189 := .lam e1936
private def e1938 : HOL.Term Symbol [h173, h189, h180, h173] h195 := .app e1935 e1937
private def e1939 : HOL.Term Symbol [h173, h189, h180, h173] h173 := .app e1938 e1937
private def e1940 : HOL.Term Symbol [h189, h180, h173] h189 := .lam e1939
private def e1941 : HOL.Term Symbol [h189, h180, h173] h173 := .app e1934 e1940
private def e1942 : HOL.Term Symbol [h180, h173] h195 := .lam e1941
private def e1943 : HOL.Term Symbol [h173, h180, h173] h173 := .var (HOL.Var.vz)
private def e1944 : HOL.Term Symbol [h180, h173] h189 := .lam e1943
private def e1945 : HOL.Term Symbol [h180, h173] h173 := .app e1942 e1944
private def e1946 : HOL.Term Symbol [h173] h183 := .lam e1945
private def e1947 : HOL.Term Symbol [h173] h186 := .app e1931 e1946
private def e1948 : HOL.Term Symbol [h173] h173 := .app e1947 e1946
private def e1949 : HOL.Term Symbol [h173] h189 := .app e1930 e1948
private def e1950 : HOL.Term Symbol [h173, h173, h173, h180, h173] h192 := .const (.constant Const.equality t17 q193)
private def e1951 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173] h219 := .const (.constant Const.equality t21 q220)
private def e1952 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173] h192 := .var (HOL.Var.vz)
private def e1953 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1954 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173] h189 := .app e1952 e1953
private def e1955 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1956 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173] h173 := .app e1954 e1955
private def e1957 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173] h213 := .lam e1956
private def e1958 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173] h216 := .app e1951 e1957
private def e1959 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1960 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h180, h173] h173 := .var (HOL.Var.vz)
private def e1961 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173] h189 := .lam e1960
private def e1962 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173] h195 := .app e1959 e1961
private def e1963 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173] h173 := .app e1962 e1961
private def e1964 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173] h189 := .app e1952 e1963
private def e1965 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173] h173 := .app e1964 e1963
private def e1966 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173] h213 := .lam e1965
private def e1967 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173] h173 := .app e1958 e1966
private def e1968 : HOL.Term Symbol [h173, h173, h173, h173, h180, h173] h189 := .lam e1967
private def e1969 : HOL.Term Symbol [h173, h173, h173, h180, h173] h192 := .lam e1968
private def e1970 : HOL.Term Symbol [h173, h173, h173, h180, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1971 : HOL.Term Symbol [h173, h173, h173, h180, h173] h189 := .app e1969 e1970
private def e1972 : HOL.Term Symbol [h173, h173, h173, h180, h173] h173 := .var (HOL.Var.vz)
private def e1973 : HOL.Term Symbol [h173, h173, h173, h180, h173] h173 := .app e1971 e1972
private def e1974 : HOL.Term Symbol [h173, h173, h173, h180, h173] h189 := .app e1950 e1973
private def e1975 : HOL.Term Symbol [h173, h173, h173, h180, h173] h173 := .app e1974 e1970
private def e1976 : HOL.Term Symbol [h173, h173, h180, h173] h189 := .lam e1975
private def e1977 : HOL.Term Symbol [h173, h180, h173] h192 := .lam e1976
private def e1978 : HOL.Term Symbol [h180, h173, h180, h173] h315 := .const (.constant Const.equality t101 q316)
private def e1979 : HOL.Term Symbol [h180, h173, h180, h173] h180 := .var (HOL.Var.vz)
private def e1980 : HOL.Term Symbol [h180, h173, h180, h173] h183 := .app e1978 e1979
private def e1981 : HOL.Term Symbol [h177, h180, h173, h180, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1982 : HOL.Term Symbol [h173, h177, h180, h173, h180, h173] h173 := .var (HOL.Var.vz)
private def e1983 : HOL.Term Symbol [h177, h180, h173, h180, h173] h189 := .lam e1982
private def e1984 : HOL.Term Symbol [h177, h180, h173, h180, h173] h195 := .app e1981 e1983
private def e1985 : HOL.Term Symbol [h177, h180, h173, h180, h173] h173 := .app e1984 e1983
private def e1986 : HOL.Term Symbol [h180, h173, h180, h173] h180 := .lam e1985
private def e1987 : HOL.Term Symbol [h180, h173, h180, h173] h173 := .app e1980 e1986
private def e1988 : HOL.Term Symbol [h173, h180, h173] h183 := .lam e1987
private def e1989 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173] h192 := .const (.constant Const.equality t17 q193)
private def e1990 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173] h219 := .const (.constant Const.equality t21 q220)
private def e1991 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173] h192 := .var (HOL.Var.vz)
private def e1992 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e1993 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173] h189 := .app e1991 e1992
private def e1994 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e1995 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173] h173 := .app e1993 e1994
private def e1996 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173] h213 := .lam e1995
private def e1997 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173] h216 := .app e1990 e1996
private def e1998 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173] h198 := .const (.constant Const.equality t6 q199)
private def e1999 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h177, h173, h180, h173] h173 := .var (HOL.Var.vz)
private def e2000 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173] h189 := .lam e1999
private def e2001 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173] h195 := .app e1998 e2000
private def e2002 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173] h173 := .app e2001 e2000
private def e2003 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173] h189 := .app e1991 e2002
private def e2004 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173] h173 := .app e2003 e2002
private def e2005 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173] h213 := .lam e2004
private def e2006 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173] h173 := .app e1997 e2005
private def e2007 : HOL.Term Symbol [h173, h173, h173, h177, h173, h180, h173] h189 := .lam e2006
private def e2008 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173] h192 := .lam e2007
private def e2009 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2010 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173] h189 := .app e2008 e2009
private def e2011 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173] h173 := .var (HOL.Var.vz)
private def e2012 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173] h173 := .app e2010 e2011
private def e2013 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173] h189 := .app e1989 e2012
private def e2014 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173] h173 := .app e2013 e2009
private def e2015 : HOL.Term Symbol [h173, h177, h173, h180, h173] h189 := .lam e2014
private def e2016 : HOL.Term Symbol [h177, h173, h180, h173] h192 := .lam e2015
private def e2017 : HOL.Term Symbol [h177, h173, h180, h173] h180 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2018 : HOL.Term Symbol [h177, h173, h180, h173] h177 := .var (HOL.Var.vz)
private def e2019 : HOL.Term Symbol [h177, h173, h180, h173] h173 := .app e2017 e2018
private def e2020 : HOL.Term Symbol [h177, h173, h180, h173] h189 := .app e2016 e2019
private def e2021 : HOL.Term Symbol [h177, h173, h180, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2022 : HOL.Term Symbol [h177, h173, h180, h173] h173 := .app e2020 e2021
private def e2023 : HOL.Term Symbol [h173, h180, h173] h180 := .lam e2022
private def e2024 : HOL.Term Symbol [h173, h180, h173] h173 := .app e1988 e2023
private def e2025 : HOL.Term Symbol [h173, h180, h173] h189 := .app e1977 e2024
private def e2026 : HOL.Term Symbol [h173, h180, h173] h173 := .app e2025 e1943
private def e2027 : HOL.Term Symbol [h180, h173] h189 := .lam e2026
private def e2028 : HOL.Term Symbol [h180, h173] h173 := .app e1942 e2027
private def e2029 : HOL.Term Symbol [h173] h183 := .lam e2028
private def e2030 : HOL.Term Symbol [h189, h173, h173, h177, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2031 : HOL.Term Symbol [h189, h173, h173, h177, h173] h189 := .var (HOL.Var.vz)
private def e2032 : HOL.Term Symbol [h189, h173, h173, h177, h173] h195 := .app e2030 e2031
private def e2033 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2034 : HOL.Term Symbol [h173, h173, h189, h173, h173, h177, h173] h173 := .var (HOL.Var.vz)
private def e2035 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173] h189 := .lam e2034
private def e2036 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173] h195 := .app e2033 e2035
private def e2037 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173] h173 := .app e2036 e2035
private def e2038 : HOL.Term Symbol [h189, h173, h173, h177, h173] h189 := .lam e2037
private def e2039 : HOL.Term Symbol [h189, h173, h173, h177, h173] h173 := .app e2032 e2038
private def e2040 : HOL.Term Symbol [h173, h173, h177, h173] h195 := .lam e2039
private def e2041 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173] h192 := .const (.constant Const.equality t17 q193)
private def e2042 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173] h219 := .const (.constant Const.equality t21 q220)
private def e2043 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173] h192 := .var (HOL.Var.vz)
private def e2044 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2045 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173] h189 := .app e2043 e2044
private def e2046 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2047 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173] h173 := .app e2045 e2046
private def e2048 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173] h213 := .lam e2047
private def e2049 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173] h216 := .app e2042 e2048
private def e2050 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2051 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h177, h173] h173 := .var (HOL.Var.vz)
private def e2052 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173] h189 := .lam e2051
private def e2053 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173] h195 := .app e2050 e2052
private def e2054 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173] h173 := .app e2053 e2052
private def e2055 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173] h189 := .app e2043 e2054
private def e2056 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173] h173 := .app e2055 e2054
private def e2057 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173] h213 := .lam e2056
private def e2058 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173] h173 := .app e2049 e2057
private def e2059 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h177, h173] h189 := .lam e2058
private def e2060 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173] h192 := .lam e2059
private def e2061 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2062 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173] h189 := .app e2060 e2061
private def e2063 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173] h173 := .var (HOL.Var.vz)
private def e2064 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173] h173 := .app e2062 e2063
private def e2065 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173] h189 := .app e2041 e2064
private def e2066 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173] h173 := .app e2065 e2061
private def e2067 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173] h189 := .lam e2066
private def e2068 : HOL.Term Symbol [h173, h173, h173, h177, h173] h192 := .lam e2067
private def e2069 : HOL.Term Symbol [h173, h173, h173, h177, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2070 : HOL.Term Symbol [h173, h173, h173, h177, h173] h189 := .app e2068 e2069
private def e2071 : HOL.Term Symbol [h173, h173, h173, h177, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2072 : HOL.Term Symbol [h173, h173, h173, h177, h173] h189 := .app e2068 e2071
private def e2073 : HOL.Term Symbol [h173, h173, h173, h177, h173] h173 := .var (HOL.Var.vz)
private def e2074 : HOL.Term Symbol [h173, h173, h173, h177, h173] h173 := .app e2072 e2073
private def e2075 : HOL.Term Symbol [h173, h173, h173, h177, h173] h173 := .app e2070 e2074
private def e2076 : HOL.Term Symbol [h173, h173, h173, h177, h173] h189 := .app e2068 e2075
private def e2077 : HOL.Term Symbol [h173, h173, h173, h177, h173] h173 := .app e2076 e2073
private def e2078 : HOL.Term Symbol [h173, h173, h177, h173] h189 := .lam e2077
private def e2079 : HOL.Term Symbol [h173, h173, h177, h173] h173 := .app e2040 e2078
private def e2080 : HOL.Term Symbol [h173, h177, h173] h189 := .lam e2079
private def e2081 : HOL.Term Symbol [h177, h173] h192 := .lam e2080
private def e2082 : HOL.Term Symbol [h177, h173] h180 := .const (.variable ⟨Name.mk [] "pointedCarrierProperty", t2⟩ q181)
private def e2083 : HOL.Term Symbol [h177, h173] h177 := .var (HOL.Var.vz)
private def e2084 : HOL.Term Symbol [h177, h173] h173 := .app e2082 e2083
private def e2085 : HOL.Term Symbol [h177, h173] h189 := .app e2081 e2084
private def e2086 : HOL.Term Symbol [h177, h173] h264 := .const (.constant Const.equality t63 q265)
private def e2087 : HOL.Term Symbol [h189, h180, h177, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2088 : HOL.Term Symbol [h189, h180, h177, h173] h189 := .var (HOL.Var.vz)
private def e2089 : HOL.Term Symbol [h189, h180, h177, h173] h195 := .app e2087 e2088
private def e2090 : HOL.Term Symbol [h173, h189, h180, h177, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2091 : HOL.Term Symbol [h173, h173, h189, h180, h177, h173] h173 := .var (HOL.Var.vz)
private def e2092 : HOL.Term Symbol [h173, h189, h180, h177, h173] h189 := .lam e2091
private def e2093 : HOL.Term Symbol [h173, h189, h180, h177, h173] h195 := .app e2090 e2092
private def e2094 : HOL.Term Symbol [h173, h189, h180, h177, h173] h173 := .app e2093 e2092
private def e2095 : HOL.Term Symbol [h189, h180, h177, h173] h189 := .lam e2094
private def e2096 : HOL.Term Symbol [h189, h180, h177, h173] h173 := .app e2089 e2095
private def e2097 : HOL.Term Symbol [h180, h177, h173] h195 := .lam e2096
private def e2098 : HOL.Term Symbol [h173, h180, h177, h173] h173 := .var (HOL.Var.vz)
private def e2099 : HOL.Term Symbol [h180, h177, h173] h189 := .lam e2098
private def e2100 : HOL.Term Symbol [h180, h177, h173] h173 := .app e2097 e2099
private def e2101 : HOL.Term Symbol [h177, h173] h183 := .lam e2100
private def e2102 : HOL.Term Symbol [h177, h173] h186 := .app e2086 e2101
private def e2103 : HOL.Term Symbol [h180, h177, h173] h180 := .var (HOL.Var.vz)
private def e2104 : HOL.Term Symbol [h180, h177, h173] h177 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2105 : HOL.Term Symbol [h180, h177, h173] h173 := .app e2103 e2104
private def e2106 : HOL.Term Symbol [h177, h173] h183 := .lam e2105
private def e2107 : HOL.Term Symbol [h177, h173] h173 := .app e2102 e2106
private def e2108 : HOL.Term Symbol [h177, h173] h173 := .app e2085 e2107
private def e2109 : HOL.Term Symbol [h173] h180 := .lam e2108
private def e2110 : HOL.Term Symbol [h173] h173 := .app e2029 e2109
private def e2111 : HOL.Term Symbol [h173] h173 := .app e1949 e2110
private def e2112 : HOL.Term Symbol [] h189 := .lam e2111
private def e2113 : HOL.Term Symbol [] h173 := .app e1876 e2112
private def c2114 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2113
private def f2115 : Theorem := Theorem.emptyResult ([].toFinset) c2114
private def r2116 : InferenceRequest := .mkComb f2115 f737
private def e2117 : HOL.Term Symbol [] h189 := .app e445 e1859
private def e2118 : HOL.Term Symbol [] h173 := .app e2112 e686
private def e2119 : HOL.Term Symbol [] h173 := .app e2117 e2118
private def c2120 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2119
private def f2121 : Theorem := Theorem.emptyResult ([].toFinset) c2120
private def s2122 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s1828
private def s2123 : SourceTerm := SourceTerm.app s2122 s1278
private def e2124 : HOL.Term Symbol [] h173 := .app e2112 e1309
private def c2125 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2124
private theorem n2126 : s2123.toDB [] = c2125.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2127 : CheckedSourceTerm := ⟨s2123, t1, by rw [← DBTerm.inferType_toDB [] s2123, n2126]; exact c2125.checked.trans (congrArg some v175)⟩
private def r2128 : InferenceRequest := .beta k2127
private def e2129 : HOL.Term Symbol [] h189 := .app e445 e2124
private def e2130 : HOL.Term Symbol [] h173 := .app e2129 e711
private def c2131 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2130
private def f2132 : Theorem := Theorem.emptyResult ([].toFinset) c2131
private def r2133 : InferenceRequest := .inst [(k1769, s1278)] f2132
private def e2134 : HOL.Term Symbol [] h189 := .app e445 e2118
private def e2135 : HOL.Term Symbol [] h173 := .app e2134 e711
private def c2136 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2135
private def f2137 : Theorem := Theorem.emptyResult ([].toFinset) c2136
private def r2138 : InferenceRequest := .trans f2121 f2137
private def e2139 : HOL.Term Symbol [] h173 := .app e2117 e711
private def c2140 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2139
private def f2141 : Theorem := Theorem.emptyResult ([].toFinset) c2140
private def r2142 : InferenceRequest := .trans f1862 f2141
private def e2143 : HOL.Term Symbol [] h173 := .app e1816 e711
private def c2144 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2143
private def f2145 : Theorem := Theorem.emptyResult ([].toFinset) c2144
private def r2146 : InferenceRequest := .mkComb f725 f2145
private def e2147 : HOL.Term Symbol [] h195 := .app e727 e1816
private def e2148 : HOL.Term Symbol [] h173 := .app e2147 e729
private def c2149 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2148
private def f2150 : Theorem := Theorem.emptyResult ([].toFinset) c2149
private def c2151 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1815
private def r2152 : InferenceRequest := .refl c2151
private def e2153 : HOL.Term Symbol [] h173 := .app e1816 e1815
private def c2154 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2153
private def f2155 : Theorem := Theorem.emptyResult ([].toFinset) c2154
private def r2156 : InferenceRequest := .mkComb f2150 f2155
private def e2157 : HOL.Term Symbol [] h189 := .app e445 e2153
private def e2158 : HOL.Term Symbol [] h173 := .app e729 e1815
private def e2159 : HOL.Term Symbol [] h173 := .app e2157 e2158
private def c2160 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2159
private def f2161 : Theorem := Theorem.emptyResult ([].toFinset) c2160
private def r2162 : InferenceRequest := .eqMp f2161 f2155
private def c2163 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2158
private def f2164 : Theorem := Theorem.emptyResult ([].toFinset) c2163
private def s2165 : SourceTerm := SourceTerm.app s7 s679
private def s2166 : SourceTerm := SourceTerm.app s2165 s679
private def s2167 : SourceTerm := SourceTerm.app s1821 s2166
private def s2168 : SourceTerm := SourceTerm.app s2167 s2166
private def s2169 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t17 s2168
private def s2170 : SourceTerm := SourceTerm.app s2169 s1821
private def e2171 : HOL.Term Symbol [] h173 := .app e1273 e763
private def c2172 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2171
private theorem n2173 : s2170.toDB [] = c2172.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2174 : CheckedSourceTerm := ⟨s2170, t1, by rw [← DBTerm.inferType_toDB [] s2170, n2173]; exact c2172.checked.trans (congrArg some v175)⟩
private def r2175 : InferenceRequest := .beta k2174
private def e2176 : HOL.Term Symbol [] h189 := .app e445 e2171
private def e2177 : HOL.Term Symbol [] h173 := .app e2176 e796
private def c2178 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2177
private def f2179 : Theorem := Theorem.emptyResult ([].toFinset) c2178
private def r2180 : InferenceRequest := .inst [(k1856, s1821)] f2179
private def e2181 : HOL.Term Symbol [] h189 := .app e445 e1817
private def e2182 : HOL.Term Symbol [] h189 := .app e1807 e775
private def e2183 : HOL.Term Symbol [] h173 := .app e2182 e775
private def e2184 : HOL.Term Symbol [] h173 := .app e2181 e2183
private def c2185 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2184
private def f2186 : Theorem := Theorem.emptyResult ([].toFinset) c2185
private def s2187 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s1278
private def s2188 : SourceTerm := SourceTerm.app s7 s2187
private def s2189 : SourceTerm := SourceTerm.app s2188 s2187
private theorem n2190 : s2189.toDB [] = c776.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2191 : CheckedSourceTerm := ⟨s2189, t1, by rw [← DBTerm.inferType_toDB [] s2189, n2190]; exact c776.checked.trans (congrArg some v175)⟩
private def r2192 : InferenceRequest := .inst [(k2191, s1278)] f1874
private def e2193 : HOL.Term Symbol [] h195 := .app e727 e2182
private def e2194 : HOL.Term Symbol [h173] h198 := .const (.constant Const.equality t6 q199)
private def e2195 : HOL.Term Symbol [h173, h173] h173 := .var (HOL.Var.vz)
private def e2196 : HOL.Term Symbol [h173] h189 := .lam e2195
private def e2197 : HOL.Term Symbol [h173] h195 := .app e2194 e2196
private def e2198 : HOL.Term Symbol [h173] h173 := .app e2197 e2196
private def e2199 : HOL.Term Symbol [] h189 := .lam e2198
private def e2200 : HOL.Term Symbol [] h173 := .app e2193 e2199
private def c2201 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2200
private def f2202 : Theorem := Theorem.emptyResult ([].toFinset) c2201
private def r2203 : InferenceRequest := .refl c776
private def e2204 : HOL.Term Symbol [] h189 := .app e445 e775
private def e2205 : HOL.Term Symbol [] h173 := .app e2204 e775
private def c2206 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2205
private def f2207 : Theorem := Theorem.emptyResult ([].toFinset) c2206
private def r2208 : InferenceRequest := .mkComb f2202 f2207
private def e2209 : HOL.Term Symbol [] h189 := .app e445 e2183
private def e2210 : HOL.Term Symbol [] h173 := .app e2199 e775
private def e2211 : HOL.Term Symbol [] h173 := .app e2209 e2210
private def c2212 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2211
private def f2213 : Theorem := Theorem.emptyResult ([].toFinset) c2212
private def s2214 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s2166
private def s2215 : SourceTerm := SourceTerm.app s2214 s1278
private def e2216 : HOL.Term Symbol [] h173 := .app e2199 e1309
private def c2217 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2216
private theorem n2218 : s2215.toDB [] = c2217.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2219 : CheckedSourceTerm := ⟨s2215, t1, by rw [← DBTerm.inferType_toDB [] s2215, n2218]; exact c2217.checked.trans (congrArg some v175)⟩
private def r2220 : InferenceRequest := .beta k2219
private def e2221 : HOL.Term Symbol [] h189 := .app e445 e2216
private def e2222 : HOL.Term Symbol [] h173 := .app e2221 e775
private def c2223 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2222
private def f2224 : Theorem := Theorem.emptyResult ([].toFinset) c2223
private def r2225 : InferenceRequest := .inst [(k2191, s1278)] f2224
private def e2226 : HOL.Term Symbol [] h189 := .app e445 e2210
private def e2227 : HOL.Term Symbol [] h173 := .app e2226 e775
private def c2228 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2227
private def f2229 : Theorem := Theorem.emptyResult ([].toFinset) c2228
private def r2230 : InferenceRequest := .trans f2213 f2229
private def e2231 : HOL.Term Symbol [] h173 := .app e2209 e775
private def c2232 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2231
private def f2233 : Theorem := Theorem.emptyResult ([].toFinset) c2232
private def r2234 : InferenceRequest := .trans f2186 f2233
private def e2235 : HOL.Term Symbol [] h173 := .app e2181 e775
private def c2236 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2235
private def f2237 : Theorem := Theorem.emptyResult ([].toFinset) c2236
private def r2238 : InferenceRequest := .trans f2164 f1820
private def e2239 : HOL.Term Symbol [] h173 := .app e729 e1817
private def c2240 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2239
private def f2241 : Theorem := Theorem.emptyResult ([c1785].toFinset) c2240
private def r2242 : InferenceRequest := .trans f2241 f2237
private def f2243 : Theorem := Theorem.emptyResult ([c1785].toFinset) c780
private def r2244 : InferenceRequest := .mkComb f725 f2243
private def e2245 : HOL.Term Symbol [] h195 := .app e727 e729
private def e2246 : HOL.Term Symbol [] h173 := .app e2245 e2204
private def c2247 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2246
private def f2248 : Theorem := Theorem.emptyResult ([c1785].toFinset) c2247
private def r2249 : InferenceRequest := .refl c747
private def r2250 : InferenceRequest := .mkComb f2248 f759
private def e2251 : HOL.Term Symbol [] h189 := .app e445 e757
private def e2252 : HOL.Term Symbol [] h173 := .app e2204 e711
private def e2253 : HOL.Term Symbol [] h173 := .app e2251 e2252
private def c2254 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2253
private def f2255 : Theorem := Theorem.emptyResult ([c1785].toFinset) c2254
private def r2256 : InferenceRequest := .eqMp f2255 f759
private def c2257 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2252
private def f2258 : Theorem := Theorem.emptyResult ([c1785].toFinset) c2257
private def r2259 : InferenceRequest := .eqMp f2258 f777
private def f2260 : Theorem := Theorem.emptyResult ([c1785].toFinset) c747
private def r2261 : InferenceRequest := .deductAntisym f1800 f2260
private def e2262 : HOL.Term Symbol [] h173 := .app e1657 e711
private def c2263 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2262
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
private def e2283 : HOL.Term Symbol [h173, h173] h192 := .const (.constant Const.equality t17 q193)
private def e2284 : HOL.Term Symbol [h173, h173, h173, h173] h219 := .const (.constant Const.equality t21 q220)
private def e2285 : HOL.Term Symbol [h192, h173, h173, h173, h173] h192 := .var (HOL.Var.vz)
private def e2286 : HOL.Term Symbol [h192, h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2287 : HOL.Term Symbol [h192, h173, h173, h173, h173] h189 := .app e2285 e2286
private def e2288 : HOL.Term Symbol [h192, h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2289 : HOL.Term Symbol [h192, h173, h173, h173, h173] h173 := .app e2287 e2288
private def e2290 : HOL.Term Symbol [h173, h173, h173, h173] h213 := .lam e2289
private def e2291 : HOL.Term Symbol [h173, h173, h173, h173] h216 := .app e2284 e2290
private def e2292 : HOL.Term Symbol [h192, h173, h173, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2293 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173] h173 := .var (HOL.Var.vz)
private def e2294 : HOL.Term Symbol [h192, h173, h173, h173, h173] h189 := .lam e2293
private def e2295 : HOL.Term Symbol [h192, h173, h173, h173, h173] h195 := .app e2292 e2294
private def e2296 : HOL.Term Symbol [h192, h173, h173, h173, h173] h173 := .app e2295 e2294
private def e2297 : HOL.Term Symbol [h192, h173, h173, h173, h173] h189 := .app e2285 e2296
private def e2298 : HOL.Term Symbol [h192, h173, h173, h173, h173] h173 := .app e2297 e2296
private def e2299 : HOL.Term Symbol [h173, h173, h173, h173] h213 := .lam e2298
private def e2300 : HOL.Term Symbol [h173, h173, h173, h173] h173 := .app e2291 e2299
private def e2301 : HOL.Term Symbol [h173, h173, h173] h189 := .lam e2300
private def e2302 : HOL.Term Symbol [h173, h173] h192 := .lam e2301
private def e2303 : HOL.Term Symbol [h173, h173] h189 := .app e2302 e1805
private def e2304 : HOL.Term Symbol [h173, h173] h173 := .app e2303 e2195
private def e2305 : HOL.Term Symbol [h173, h173] h189 := .app e2283 e2304
private def e2306 : HOL.Term Symbol [h173, h173] h173 := .app e2305 e1805
private def e2307 : HOL.Term Symbol [h173] h189 := .lam e2306
private def e2308 : HOL.Term Symbol [] h192 := .lam e2307
private def e2309 : HOL.Term Symbol [] h189 := .app e2308 e1309
private def c2310 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2309
private theorem n2311 : s2282.toDB [] = c2310.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2312 : CheckedSourceTerm := ⟨s2282, t4, by rw [← DBTerm.inferType_toDB [] s2282, n2311]; exact c2310.checked.trans (congrArg some v191)⟩
private def r2313 : InferenceRequest := .beta k2312
private def e2314 : HOL.Term Symbol [] h195 := .app e727 e2309
private def e2315 : HOL.Term Symbol [h173] h192 := .const (.constant Const.equality t17 q193)
private def e2316 : HOL.Term Symbol [h173, h173, h173] h219 := .const (.constant Const.equality t21 q220)
private def e2317 : HOL.Term Symbol [h192, h173, h173, h173] h192 := .var (HOL.Var.vz)
private def e2318 : HOL.Term Symbol [h192, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2319 : HOL.Term Symbol [h192, h173, h173, h173] h189 := .app e2317 e2318
private def e2320 : HOL.Term Symbol [h192, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2321 : HOL.Term Symbol [h192, h173, h173, h173] h173 := .app e2319 e2320
private def e2322 : HOL.Term Symbol [h173, h173, h173] h213 := .lam e2321
private def e2323 : HOL.Term Symbol [h173, h173, h173] h216 := .app e2316 e2322
private def e2324 : HOL.Term Symbol [h192, h173, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2325 : HOL.Term Symbol [h173, h192, h173, h173, h173] h173 := .var (HOL.Var.vz)
private def e2326 : HOL.Term Symbol [h192, h173, h173, h173] h189 := .lam e2325
private def e2327 : HOL.Term Symbol [h192, h173, h173, h173] h195 := .app e2324 e2326
private def e2328 : HOL.Term Symbol [h192, h173, h173, h173] h173 := .app e2327 e2326
private def e2329 : HOL.Term Symbol [h192, h173, h173, h173] h189 := .app e2317 e2328
private def e2330 : HOL.Term Symbol [h192, h173, h173, h173] h173 := .app e2329 e2328
private def e2331 : HOL.Term Symbol [h173, h173, h173] h213 := .lam e2330
private def e2332 : HOL.Term Symbol [h173, h173, h173] h173 := .app e2323 e2331
private def e2333 : HOL.Term Symbol [h173, h173] h189 := .lam e2332
private def e2334 : HOL.Term Symbol [h173] h192 := .lam e2333
private def e2335 : HOL.Term Symbol [h173] h189 := .app e2334 e1870
private def e2336 : HOL.Term Symbol [h173] h173 := .app e2335 e770
private def e2337 : HOL.Term Symbol [h173] h189 := .app e2315 e2336
private def e2338 : HOL.Term Symbol [h173] h173 := .app e2337 e1870
private def e2339 : HOL.Term Symbol [] h189 := .lam e2338
private def e2340 : HOL.Term Symbol [] h173 := .app e2314 e2339
private def c2341 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2340
private def f2342 : Theorem := Theorem.emptyResult ([].toFinset) c2341
private def r2343 : InferenceRequest := .inst [(k1407, s1278)] f2342
private def e2344 : HOL.Term Symbol [] h189 := .app e2308 e711
private def e2345 : HOL.Term Symbol [] h195 := .app e727 e2344
private def e2346 : HOL.Term Symbol [h173] h189 := .app e2334 e2111
private def e2347 : HOL.Term Symbol [h173] h173 := .app e2346 e770
private def e2348 : HOL.Term Symbol [h173] h189 := .app e2315 e2347
private def e2349 : HOL.Term Symbol [h173] h173 := .app e2348 e2111
private def e2350 : HOL.Term Symbol [] h189 := .lam e2349
private def e2351 : HOL.Term Symbol [] h173 := .app e2345 e2350
private def c2352 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2351
private def f2353 : Theorem := Theorem.emptyResult ([].toFinset) c2352
private def r2354 : InferenceRequest := .mkComb f2353 f737
private def e2355 : HOL.Term Symbol [] h173 := .app e2344 e686
private def e2356 : HOL.Term Symbol [] h189 := .app e445 e2355
private def e2357 : HOL.Term Symbol [] h173 := .app e2350 e686
private def e2358 : HOL.Term Symbol [] h173 := .app e2356 e2357
private def c2359 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2358
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
private def e2378 : HOL.Term Symbol [] h173 := .app e2350 e1309
private def c2379 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2378
private theorem n2380 : s2377.toDB [] = c2379.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2381 : CheckedSourceTerm := ⟨s2377, t1, by rw [← DBTerm.inferType_toDB [] s2377, n2380]; exact c2379.checked.trans (congrArg some v175)⟩
private def r2382 : InferenceRequest := .beta k2381
private def e2383 : HOL.Term Symbol [] h189 := .app e445 e2378
private def e2384 : HOL.Term Symbol [] h173 := .app e1409 e1309
private def e2385 : HOL.Term Symbol [] h189 := .app e445 e2384
private def e2386 : HOL.Term Symbol [] h173 := .app e2385 e711
private def e2387 : HOL.Term Symbol [] h173 := .app e2383 e2386
private def c2388 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2387
private def f2389 : Theorem := Theorem.emptyResult ([].toFinset) c2388
private def r2390 : InferenceRequest := .inst [(k1769, s1278)] f2389
private def e2391 : HOL.Term Symbol [] h189 := .app e445 e2357
private def e2392 : HOL.Term Symbol [] h173 := .app e2391 e2262
private def c2393 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2392
private def f2394 : Theorem := Theorem.emptyResult ([].toFinset) c2393
private def r2395 : InferenceRequest := .trans f2360 f2394
private def e2396 : HOL.Term Symbol [] h173 := .app e2356 e2262
private def c2397 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2396
private def f2398 : Theorem := Theorem.emptyResult ([].toFinset) c2397
private def r2399 : InferenceRequest := .mkComb f725 f2398
private def e2400 : HOL.Term Symbol [] h195 := .app e727 e2356
private def e2401 : HOL.Term Symbol [] h189 := .app e445 e2262
private def e2402 : HOL.Term Symbol [] h173 := .app e2400 e2401
private def c2403 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2402
private def f2404 : Theorem := Theorem.emptyResult ([].toFinset) c2403
private def c2405 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2355
private def r2406 : InferenceRequest := .refl c2405
private def e2407 : HOL.Term Symbol [] h173 := .app e2356 e2355
private def c2408 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2407
private def f2409 : Theorem := Theorem.emptyResult ([].toFinset) c2408
private def r2410 : InferenceRequest := .mkComb f2404 f2409
private def e2411 : HOL.Term Symbol [] h189 := .app e445 e2407
private def e2412 : HOL.Term Symbol [] h173 := .app e2401 e2355
private def e2413 : HOL.Term Symbol [] h173 := .app e2411 e2412
private def c2414 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2413
private def f2415 : Theorem := Theorem.emptyResult ([].toFinset) c2414
private def r2416 : InferenceRequest := .eqMp f2415 f2409
private def c2417 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2412
private def f2418 : Theorem := Theorem.emptyResult ([].toFinset) c2417
private def r2419 : InferenceRequest := .eqMp f2418 f2264
private def f2420 : Theorem := Theorem.emptyResult ([].toFinset) c2405
private def s2421 : SourceTerm := SourceTerm.app s1348 s1278
private def e2422 : HOL.Term Symbol [] h189 := .app e500 e1309
private def c2423 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2422
private theorem n2424 : s2421.toDB [] = c2423.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2425 : CheckedSourceTerm := ⟨s2421, t4, by rw [← DBTerm.inferType_toDB [] s2421, n2424]; exact c2423.checked.trans (congrArg some v191)⟩
private def r2426 : InferenceRequest := .beta k2425
private def e2427 : HOL.Term Symbol [] h195 := .app e727 e2422
private def e2428 : HOL.Term Symbol [h189, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2429 : HOL.Term Symbol [h189, h173] h189 := .var (HOL.Var.vz)
private def e2430 : HOL.Term Symbol [h189, h173] h195 := .app e2428 e2429
private def e2431 : HOL.Term Symbol [h173, h189, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2432 : HOL.Term Symbol [h173, h173, h189, h173] h173 := .var (HOL.Var.vz)
private def e2433 : HOL.Term Symbol [h173, h189, h173] h189 := .lam e2432
private def e2434 : HOL.Term Symbol [h173, h189, h173] h195 := .app e2431 e2433
private def e2435 : HOL.Term Symbol [h173, h189, h173] h173 := .app e2434 e2433
private def e2436 : HOL.Term Symbol [h189, h173] h189 := .lam e2435
private def e2437 : HOL.Term Symbol [h189, h173] h173 := .app e2430 e2436
private def e2438 : HOL.Term Symbol [h173] h195 := .lam e2437
private def e2439 : HOL.Term Symbol [h173, h173, h173, h173] h192 := .const (.constant Const.equality t17 q193)
private def e2440 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h219 := .const (.constant Const.equality t21 q220)
private def e2441 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173] h192 := .var (HOL.Var.vz)
private def e2442 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2443 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173] h189 := .app e2441 e2442
private def e2444 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2445 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173] h173 := .app e2443 e2444
private def e2446 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h213 := .lam e2445
private def e2447 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h216 := .app e2440 e2446
private def e2448 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2449 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vz)
private def e2450 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173] h189 := .lam e2449
private def e2451 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173] h195 := .app e2448 e2450
private def e2452 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173] h173 := .app e2451 e2450
private def e2453 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173] h189 := .app e2441 e2452
private def e2454 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173] h173 := .app e2453 e2452
private def e2455 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h213 := .lam e2454
private def e2456 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173] h173 := .app e2447 e2455
private def e2457 : HOL.Term Symbol [h173, h173, h173, h173, h173] h189 := .lam e2456
private def e2458 : HOL.Term Symbol [h173, h173, h173, h173] h192 := .lam e2457
private def e2459 : HOL.Term Symbol [h173, h173, h173, h173] h189 := .app e2458 e1921
private def e2460 : HOL.Term Symbol [h173, h173, h173, h173] h173 := .app e2459 e1918
private def e2461 : HOL.Term Symbol [h173, h173, h173, h173] h189 := .app e2439 e2460
private def e2462 : HOL.Term Symbol [h173, h173, h173, h173] h173 := .app e2461 e1921
private def e2463 : HOL.Term Symbol [h173, h173, h173] h189 := .lam e2462
private def e2464 : HOL.Term Symbol [h173, h173] h192 := .lam e2463
private def e2465 : HOL.Term Symbol [h173, h173] h173 := .const (.variable ⟨Name.mk [""] "x", t1⟩ q174)
private def e2466 : HOL.Term Symbol [h173, h173] h189 := .app e2464 e2465
private def e2467 : HOL.Term Symbol [h173, h173] h173 := .app e2466 e2195
private def e2468 : HOL.Term Symbol [h173, h173] h189 := .app e2464 e2467
private def e2469 : HOL.Term Symbol [h173, h173] h189 := .app e2464 e1805
private def e2470 : HOL.Term Symbol [h173, h173] h173 := .app e2469 e2195
private def e2471 : HOL.Term Symbol [h173, h173] h189 := .app e2464 e2470
private def e2472 : HOL.Term Symbol [h173, h173] h173 := .app e2471 e2195
private def e2473 : HOL.Term Symbol [h173, h173] h173 := .app e2468 e2472
private def e2474 : HOL.Term Symbol [h173] h189 := .lam e2473
private def e2475 : HOL.Term Symbol [h173] h173 := .app e2438 e2474
private def e2476 : HOL.Term Symbol [] h189 := .lam e2475
private def e2477 : HOL.Term Symbol [] h173 := .app e2427 e2476
private def c2478 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2477
private def f2479 : Theorem := Theorem.emptyResult ([].toFinset) c2478
private def c2480 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e689
private theorem n2481 : s1350.toDB [] = c2480.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2482 : CheckedSourceTerm := ⟨s1350, t1, by rw [← DBTerm.inferType_toDB [] s1350, n2481]; exact c2480.checked.trans (congrArg some v175)⟩
private def r2483 : InferenceRequest := .inst [(k2482, s1278)] f2479
private def e2484 : HOL.Term Symbol [] h195 := .app e727 e690
private def e2485 : HOL.Term Symbol [h173, h173] h264 := .const (.constant Const.equality t63 q265)
private def e2486 : HOL.Term Symbol [h189, h180, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2487 : HOL.Term Symbol [h189, h180, h173, h173] h189 := .var (HOL.Var.vz)
private def e2488 : HOL.Term Symbol [h189, h180, h173, h173] h195 := .app e2486 e2487
private def e2489 : HOL.Term Symbol [h173, h189, h180, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2490 : HOL.Term Symbol [h173, h173, h189, h180, h173, h173] h173 := .var (HOL.Var.vz)
private def e2491 : HOL.Term Symbol [h173, h189, h180, h173, h173] h189 := .lam e2490
private def e2492 : HOL.Term Symbol [h173, h189, h180, h173, h173] h195 := .app e2489 e2491
private def e2493 : HOL.Term Symbol [h173, h189, h180, h173, h173] h173 := .app e2492 e2491
private def e2494 : HOL.Term Symbol [h189, h180, h173, h173] h189 := .lam e2493
private def e2495 : HOL.Term Symbol [h189, h180, h173, h173] h173 := .app e2488 e2494
private def e2496 : HOL.Term Symbol [h180, h173, h173] h195 := .lam e2495
private def e2497 : HOL.Term Symbol [h173, h180, h173, h173] h173 := .var (HOL.Var.vz)
private def e2498 : HOL.Term Symbol [h180, h173, h173] h189 := .lam e2497
private def e2499 : HOL.Term Symbol [h180, h173, h173] h173 := .app e2496 e2498
private def e2500 : HOL.Term Symbol [h173, h173] h183 := .lam e2499
private def e2501 : HOL.Term Symbol [h173, h173] h186 := .app e2485 e2500
private def e2502 : HOL.Term Symbol [h173, h173] h173 := .app e2501 e2500
private def e2503 : HOL.Term Symbol [h173, h173] h189 := .app e2464 e2502
private def e2504 : HOL.Term Symbol [h173, h173] h173 := .app e2503 e2195
private def e2505 : HOL.Term Symbol [h173, h173] h189 := .app e2464 e2504
private def e2506 : HOL.Term Symbol [h173, h173] h173 := .app e2505 e2472
private def e2507 : HOL.Term Symbol [h173] h189 := .lam e2506
private def e2508 : HOL.Term Symbol [h173] h173 := .app e2438 e2507
private def e2509 : HOL.Term Symbol [] h189 := .lam e2508
private def e2510 : HOL.Term Symbol [] h173 := .app e2484 e2509
private def c2511 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2510
private def f2512 : Theorem := Theorem.emptyResult ([].toFinset) c2511
private def c2513 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e710
private def r2514 : InferenceRequest := .refl c2513
private def e2515 : HOL.Term Symbol [] h189 := .app e445 e710
private def e2516 : HOL.Term Symbol [] h173 := .app e2515 e710
private def c2517 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2516
private def f2518 : Theorem := Theorem.emptyResult ([].toFinset) c2517
private def r2519 : InferenceRequest := .mkComb f2512 f2518
private def e2520 : HOL.Term Symbol [] h173 := .app e2509 e710
private def e2521 : HOL.Term Symbol [] h173 := .app e729 e2520
private def c2522 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2521
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
private def e2536 : HOL.Term Symbol [] h173 := .app e2509 e1309
private def c2537 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2536
private theorem n2538 : s2535.toDB [] = c2537.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2539 : CheckedSourceTerm := ⟨s2535, t1, by rw [← DBTerm.inferType_toDB [] s2535, n2538]; exact c2537.checked.trans (congrArg some v175)⟩
private def r2540 : InferenceRequest := .beta k2539
private def e2541 : HOL.Term Symbol [] h189 := .app e445 e2536
private def e2542 : HOL.Term Symbol [h189] h198 := .const (.constant Const.equality t6 q199)
private def e2543 : HOL.Term Symbol [h189] h189 := .var (HOL.Var.vz)
private def e2544 : HOL.Term Symbol [h189] h195 := .app e2542 e2543
private def e2545 : HOL.Term Symbol [h173, h189] h198 := .const (.constant Const.equality t6 q199)
private def e2546 : HOL.Term Symbol [h173, h173, h189] h173 := .var (HOL.Var.vz)
private def e2547 : HOL.Term Symbol [h173, h189] h189 := .lam e2546
private def e2548 : HOL.Term Symbol [h173, h189] h195 := .app e2545 e2547
private def e2549 : HOL.Term Symbol [h173, h189] h173 := .app e2548 e2547
private def e2550 : HOL.Term Symbol [h189] h189 := .lam e2549
private def e2551 : HOL.Term Symbol [h189] h173 := .app e2544 e2550
private def e2552 : HOL.Term Symbol [] h195 := .lam e2551
private def e2553 : HOL.Term Symbol [h173, h173, h173] h192 := .const (.constant Const.equality t17 q193)
private def e2554 : HOL.Term Symbol [h173, h173, h173, h173, h173] h219 := .const (.constant Const.equality t21 q220)
private def e2555 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173] h192 := .var (HOL.Var.vz)
private def e2556 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2557 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173] h189 := .app e2555 e2556
private def e2558 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2559 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173] h173 := .app e2557 e2558
private def e2560 : HOL.Term Symbol [h173, h173, h173, h173, h173] h213 := .lam e2559
private def e2561 : HOL.Term Symbol [h173, h173, h173, h173, h173] h216 := .app e2554 e2560
private def e2562 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2563 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173] h173 := .var (HOL.Var.vz)
private def e2564 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173] h189 := .lam e2563
private def e2565 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173] h195 := .app e2562 e2564
private def e2566 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173] h173 := .app e2565 e2564
private def e2567 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173] h189 := .app e2555 e2566
private def e2568 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173] h173 := .app e2567 e2566
private def e2569 : HOL.Term Symbol [h173, h173, h173, h173, h173] h213 := .lam e2568
private def e2570 : HOL.Term Symbol [h173, h173, h173, h173, h173] h173 := .app e2561 e2569
private def e2571 : HOL.Term Symbol [h173, h173, h173, h173] h189 := .lam e2570
private def e2572 : HOL.Term Symbol [h173, h173, h173] h192 := .lam e2571
private def e2573 : HOL.Term Symbol [h173, h173, h173] h189 := .app e2572 e491
private def e2574 : HOL.Term Symbol [h173, h173, h173] h173 := .app e2573 e488
private def e2575 : HOL.Term Symbol [h173, h173, h173] h189 := .app e2553 e2574
private def e2576 : HOL.Term Symbol [h173, h173, h173] h173 := .app e2575 e491
private def e2577 : HOL.Term Symbol [h173, h173] h189 := .lam e2576
private def e2578 : HOL.Term Symbol [h173] h192 := .lam e2577
private def e2579 : HOL.Term Symbol [h173] h189 := .app e2578 e1948
private def e2580 : HOL.Term Symbol [h173] h173 := .app e2579 e770
private def e2581 : HOL.Term Symbol [h173] h189 := .app e2578 e2580
private def e2582 : HOL.Term Symbol [h173] h189 := .app e2578 e1870
private def e2583 : HOL.Term Symbol [h173] h173 := .app e2582 e770
private def e2584 : HOL.Term Symbol [h173] h189 := .app e2578 e2583
private def e2585 : HOL.Term Symbol [h173] h173 := .app e2584 e770
private def e2586 : HOL.Term Symbol [h173] h173 := .app e2581 e2585
private def e2587 : HOL.Term Symbol [] h189 := .lam e2586
private def e2588 : HOL.Term Symbol [] h173 := .app e2552 e2587
private def e2589 : HOL.Term Symbol [] h173 := .app e2541 e2588
private def c2590 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2589
private def f2591 : Theorem := Theorem.emptyResult ([].toFinset) c2590
private theorem n2592 : s1404.toDB [] = c2513.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k2593 : CheckedSourceTerm := ⟨s1404, t1, by rw [← DBTerm.inferType_toDB [] s1404, n2592]; exact c2513.checked.trans (congrArg some v175)⟩
private def r2594 : InferenceRequest := .inst [(k2593, s1278)] f2591
private def e2595 : HOL.Term Symbol [] h189 := .app e445 e2520
private def e2596 : HOL.Term Symbol [h173] h189 := .app e2578 e2110
private def e2597 : HOL.Term Symbol [h173] h173 := .app e2596 e770
private def e2598 : HOL.Term Symbol [h173] h189 := .app e2578 e2597
private def e2599 : HOL.Term Symbol [h173] h173 := .app e2598 e770
private def e2600 : HOL.Term Symbol [h173] h173 := .app e2581 e2599
private def e2601 : HOL.Term Symbol [] h189 := .lam e2600
private def e2602 : HOL.Term Symbol [] h173 := .app e2552 e2601
private def e2603 : HOL.Term Symbol [] h173 := .app e2595 e2602
private def c2604 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2603
private def f2605 : Theorem := Theorem.emptyResult ([].toFinset) c2604
private def r2606 : InferenceRequest := .trans f2523 f2605
private def e2607 : HOL.Term Symbol [] h173 := .app e729 e2602
private def c2608 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2607
private def f2609 : Theorem := Theorem.emptyResult ([].toFinset) c2608
private def r2610 : InferenceRequest := .mkComb f725 f2609
private def e2611 : HOL.Term Symbol [] h189 := .app e445 e2602
private def e2612 : HOL.Term Symbol [] h173 := .app e2245 e2611
private def c2613 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2612
private def f2614 : Theorem := Theorem.emptyResult ([].toFinset) c2613
private def r2615 : InferenceRequest := .mkComb f2614 f759
private def e2616 : HOL.Term Symbol [] h173 := .app e2611 e711
private def e2617 : HOL.Term Symbol [] h173 := .app e2251 e2616
private def c2618 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2617
private def f2619 : Theorem := Theorem.emptyResult ([].toFinset) c2618
private def r2620 : InferenceRequest := .eqMp f2619 f759
private def c2621 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2616
private def f2622 : Theorem := Theorem.emptyResult ([].toFinset) c2621
private def c2623 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2602
private def r2624 : InferenceRequest := .assume c2623
private def f2625 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2623
private def r2626 : InferenceRequest := .deductAntisym f2625 f2622
private def e2627 : HOL.Term Symbol [] h173 := .app e2611 e2616
private def c2628 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2627
private def f2629 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2628
private def r2630 : InferenceRequest := .eqMp f2629 f2625
private def f2631 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2621
private def r2632 : InferenceRequest := .deductAntisym f2625 f2625
private def e2633 : HOL.Term Symbol [] h173 := .app e2611 e2602
private def c2634 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2633
private def f2635 : Theorem := Theorem.emptyResult ([].toFinset) c2634
private def r2636 : InferenceRequest := .eqMp f2635 f2625
private def r2637 : InferenceRequest := .eqMp f2631 f2625
private def f2638 : Theorem := Theorem.emptyResult ([c2623].toFinset) c747
private def r2639 : InferenceRequest := .deductAntisym f2625 f777
private def e2640 : HOL.Term Symbol [] h173 := .app e2611 e775
private def c2641 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2640
private def f2642 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2641
private def r2643 : InferenceRequest := .deductAntisym f2638 f777
private def f2644 : Theorem := Theorem.emptyResult ([c2623].toFinset) c780
private def r2645 : InferenceRequest := .mkComb f769 f2642
private def e2646 : HOL.Term Symbol [] h189 := .app e763 e2602
private def e2647 : HOL.Term Symbol [] h195 := .app e727 e2646
private def e2648 : HOL.Term Symbol [] h173 := .app e2647 e789
private def c2649 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2648
private def f2650 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2649
private def r2651 : InferenceRequest := .mkComb f2650 f2644
private def e2652 : HOL.Term Symbol [] h173 := .app e2646 e711
private def e2653 : HOL.Term Symbol [] h189 := .app e445 e2652
private def e2654 : HOL.Term Symbol [] h173 := .app e2653 e796
private def c2655 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2654
private def f2656 : Theorem := Theorem.emptyResult ([c2623].toFinset) c2655
private def r2657 : InferenceRequest := .abs ⟨Name.mk [""] "x", t17⟩ f2656
private def e2658 : HOL.Term Symbol [h189, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2659 : HOL.Term Symbol [h189, h192] h189 := .var (HOL.Var.vz)
private def e2660 : HOL.Term Symbol [h189, h192] h195 := .app e2658 e2659
private def e2661 : HOL.Term Symbol [h173, h189, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2662 : HOL.Term Symbol [h173, h173, h189, h192] h173 := .var (HOL.Var.vz)
private def e2663 : HOL.Term Symbol [h173, h189, h192] h189 := .lam e2662
private def e2664 : HOL.Term Symbol [h173, h189, h192] h195 := .app e2661 e2663
private def e2665 : HOL.Term Symbol [h173, h189, h192] h173 := .app e2664 e2663
private def e2666 : HOL.Term Symbol [h189, h192] h189 := .lam e2665
private def e2667 : HOL.Term Symbol [h189, h192] h173 := .app e2660 e2666
private def e2668 : HOL.Term Symbol [h192] h195 := .lam e2667
private def e2669 : HOL.Term Symbol [h173, h173, h173, h192] h192 := .const (.constant Const.equality t17 q193)
private def e2670 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h219 := .const (.constant Const.equality t21 q220)
private def e2671 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192] h192 := .var (HOL.Var.vz)
private def e2672 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2673 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192] h189 := .app e2671 e2672
private def e2674 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2675 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192] h173 := .app e2673 e2674
private def e2676 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h213 := .lam e2675
private def e2677 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h216 := .app e2670 e2676
private def e2678 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2679 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h192] h173 := .var (HOL.Var.vz)
private def e2680 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192] h189 := .lam e2679
private def e2681 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192] h195 := .app e2678 e2680
private def e2682 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192] h173 := .app e2681 e2680
private def e2683 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192] h189 := .app e2671 e2682
private def e2684 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192] h173 := .app e2683 e2682
private def e2685 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h213 := .lam e2684
private def e2686 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192] h173 := .app e2677 e2685
private def e2687 : HOL.Term Symbol [h173, h173, h173, h173, h192] h189 := .lam e2686
private def e2688 : HOL.Term Symbol [h173, h173, h173, h192] h192 := .lam e2687
private def e2689 : HOL.Term Symbol [h173, h173, h173, h192] h189 := .app e2688 e847
private def e2690 : HOL.Term Symbol [h173, h173, h173, h192] h173 := .app e2689 e844
private def e2691 : HOL.Term Symbol [h173, h173, h173, h192] h189 := .app e2669 e2690
private def e2692 : HOL.Term Symbol [h173, h173, h173, h192] h173 := .app e2691 e847
private def e2693 : HOL.Term Symbol [h173, h173, h192] h189 := .lam e2692
private def e2694 : HOL.Term Symbol [h173, h192] h192 := .lam e2693
private def e2695 : HOL.Term Symbol [h173, h192] h264 := .const (.constant Const.equality t63 q265)
private def e2696 : HOL.Term Symbol [h189, h180, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2697 : HOL.Term Symbol [h189, h180, h173, h192] h189 := .var (HOL.Var.vz)
private def e2698 : HOL.Term Symbol [h189, h180, h173, h192] h195 := .app e2696 e2697
private def e2699 : HOL.Term Symbol [h173, h189, h180, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2700 : HOL.Term Symbol [h173, h173, h189, h180, h173, h192] h173 := .var (HOL.Var.vz)
private def e2701 : HOL.Term Symbol [h173, h189, h180, h173, h192] h189 := .lam e2700
private def e2702 : HOL.Term Symbol [h173, h189, h180, h173, h192] h195 := .app e2699 e2701
private def e2703 : HOL.Term Symbol [h173, h189, h180, h173, h192] h173 := .app e2702 e2701
private def e2704 : HOL.Term Symbol [h189, h180, h173, h192] h189 := .lam e2703
private def e2705 : HOL.Term Symbol [h189, h180, h173, h192] h173 := .app e2698 e2704
private def e2706 : HOL.Term Symbol [h180, h173, h192] h195 := .lam e2705
private def e2707 : HOL.Term Symbol [h173, h180, h173, h192] h173 := .var (HOL.Var.vz)
private def e2708 : HOL.Term Symbol [h180, h173, h192] h189 := .lam e2707
private def e2709 : HOL.Term Symbol [h180, h173, h192] h173 := .app e2706 e2708
private def e2710 : HOL.Term Symbol [h173, h192] h183 := .lam e2709
private def e2711 : HOL.Term Symbol [h173, h192] h186 := .app e2695 e2710
private def e2712 : HOL.Term Symbol [h173, h192] h173 := .app e2711 e2710
private def e2713 : HOL.Term Symbol [h173, h192] h189 := .app e2694 e2712
private def e2714 : HOL.Term Symbol [h173, h192] h173 := .app e2713 e1267
private def e2715 : HOL.Term Symbol [h173, h192] h189 := .app e2694 e2714
private def e2716 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192] h192 := .const (.constant Const.equality t17 q193)
private def e2717 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h192] h219 := .const (.constant Const.equality t21 q220)
private def e2718 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192] h192 := .var (HOL.Var.vz)
private def e2719 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2720 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192] h189 := .app e2718 e2719
private def e2721 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2722 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192] h173 := .app e2720 e2721
private def e2723 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h192] h213 := .lam e2722
private def e2724 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h192] h216 := .app e2717 e2723
private def e2725 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2726 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h180, h173, h192] h173 := .var (HOL.Var.vz)
private def e2727 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192] h189 := .lam e2726
private def e2728 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192] h195 := .app e2725 e2727
private def e2729 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192] h173 := .app e2728 e2727
private def e2730 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192] h189 := .app e2718 e2729
private def e2731 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192] h173 := .app e2730 e2729
private def e2732 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h192] h213 := .lam e2731
private def e2733 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h192] h173 := .app e2724 e2732
private def e2734 : HOL.Term Symbol [h173, h173, h173, h173, h180, h173, h192] h189 := .lam e2733
private def e2735 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192] h192 := .lam e2734
private def e2736 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2737 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192] h189 := .app e2735 e2736
private def e2738 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192] h173 := .var (HOL.Var.vz)
private def e2739 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192] h173 := .app e2737 e2738
private def e2740 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192] h189 := .app e2716 e2739
private def e2741 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192] h173 := .app e2740 e2736
private def e2742 : HOL.Term Symbol [h173, h173, h180, h173, h192] h189 := .lam e2741
private def e2743 : HOL.Term Symbol [h173, h180, h173, h192] h192 := .lam e2742
private def e2744 : HOL.Term Symbol [h180, h173, h180, h173, h192] h315 := .const (.constant Const.equality t101 q316)
private def e2745 : HOL.Term Symbol [h180, h173, h180, h173, h192] h180 := .var (HOL.Var.vz)
private def e2746 : HOL.Term Symbol [h180, h173, h180, h173, h192] h183 := .app e2744 e2745
private def e2747 : HOL.Term Symbol [h177, h180, h173, h180, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2748 : HOL.Term Symbol [h173, h177, h180, h173, h180, h173, h192] h173 := .var (HOL.Var.vz)
private def e2749 : HOL.Term Symbol [h177, h180, h173, h180, h173, h192] h189 := .lam e2748
private def e2750 : HOL.Term Symbol [h177, h180, h173, h180, h173, h192] h195 := .app e2747 e2749
private def e2751 : HOL.Term Symbol [h177, h180, h173, h180, h173, h192] h173 := .app e2750 e2749
private def e2752 : HOL.Term Symbol [h180, h173, h180, h173, h192] h180 := .lam e2751
private def e2753 : HOL.Term Symbol [h180, h173, h180, h173, h192] h173 := .app e2746 e2752
private def e2754 : HOL.Term Symbol [h173, h180, h173, h192] h183 := .lam e2753
private def e2755 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192] h192 := .const (.constant Const.equality t17 q193)
private def e2756 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h192] h219 := .const (.constant Const.equality t21 q220)
private def e2757 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192] h192 := .var (HOL.Var.vz)
private def e2758 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2759 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192] h189 := .app e2757 e2758
private def e2760 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2761 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192] h173 := .app e2759 e2760
private def e2762 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h192] h213 := .lam e2761
private def e2763 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h192] h216 := .app e2756 e2762
private def e2764 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2765 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h177, h173, h180, h173, h192] h173 := .var (HOL.Var.vz)
private def e2766 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192] h189 := .lam e2765
private def e2767 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192] h195 := .app e2764 e2766
private def e2768 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192] h173 := .app e2767 e2766
private def e2769 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192] h189 := .app e2757 e2768
private def e2770 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192] h173 := .app e2769 e2768
private def e2771 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h192] h213 := .lam e2770
private def e2772 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h192] h173 := .app e2763 e2771
private def e2773 : HOL.Term Symbol [h173, h173, h173, h177, h173, h180, h173, h192] h189 := .lam e2772
private def e2774 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192] h192 := .lam e2773
private def e2775 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2776 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192] h189 := .app e2774 e2775
private def e2777 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192] h173 := .var (HOL.Var.vz)
private def e2778 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192] h173 := .app e2776 e2777
private def e2779 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192] h189 := .app e2755 e2778
private def e2780 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192] h173 := .app e2779 e2775
private def e2781 : HOL.Term Symbol [h173, h177, h173, h180, h173, h192] h189 := .lam e2780
private def e2782 : HOL.Term Symbol [h177, h173, h180, h173, h192] h192 := .lam e2781
private def e2783 : HOL.Term Symbol [h177, h173, h180, h173, h192] h180 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2784 : HOL.Term Symbol [h177, h173, h180, h173, h192] h177 := .var (HOL.Var.vz)
private def e2785 : HOL.Term Symbol [h177, h173, h180, h173, h192] h173 := .app e2783 e2784
private def e2786 : HOL.Term Symbol [h177, h173, h180, h173, h192] h189 := .app e2782 e2785
private def e2787 : HOL.Term Symbol [h177, h173, h180, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2788 : HOL.Term Symbol [h177, h173, h180, h173, h192] h173 := .app e2786 e2787
private def e2789 : HOL.Term Symbol [h173, h180, h173, h192] h180 := .lam e2788
private def e2790 : HOL.Term Symbol [h173, h180, h173, h192] h173 := .app e2754 e2789
private def e2791 : HOL.Term Symbol [h173, h180, h173, h192] h189 := .app e2743 e2790
private def e2792 : HOL.Term Symbol [h173, h180, h173, h192] h173 := .app e2791 e2707
private def e2793 : HOL.Term Symbol [h180, h173, h192] h189 := .lam e2792
private def e2794 : HOL.Term Symbol [h180, h173, h192] h173 := .app e2706 e2793
private def e2795 : HOL.Term Symbol [h173, h192] h183 := .lam e2794
private def e2796 : HOL.Term Symbol [h189, h173, h173, h177, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2797 : HOL.Term Symbol [h189, h173, h173, h177, h173, h192] h189 := .var (HOL.Var.vz)
private def e2798 : HOL.Term Symbol [h189, h173, h173, h177, h173, h192] h195 := .app e2796 e2797
private def e2799 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2800 : HOL.Term Symbol [h173, h173, h189, h173, h173, h177, h173, h192] h173 := .var (HOL.Var.vz)
private def e2801 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173, h192] h189 := .lam e2800
private def e2802 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173, h192] h195 := .app e2799 e2801
private def e2803 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173, h192] h173 := .app e2802 e2801
private def e2804 : HOL.Term Symbol [h189, h173, h173, h177, h173, h192] h189 := .lam e2803
private def e2805 : HOL.Term Symbol [h189, h173, h173, h177, h173, h192] h173 := .app e2798 e2804
private def e2806 : HOL.Term Symbol [h173, h173, h177, h173, h192] h195 := .lam e2805
private def e2807 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192] h192 := .const (.constant Const.equality t17 q193)
private def e2808 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h219 := .const (.constant Const.equality t21 q220)
private def e2809 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h192 := .var (HOL.Var.vz)
private def e2810 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2811 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h189 := .app e2809 e2810
private def e2812 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2813 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h173 := .app e2811 e2812
private def e2814 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h213 := .lam e2813
private def e2815 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h216 := .app e2808 e2814
private def e2816 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2817 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h173 := .var (HOL.Var.vz)
private def e2818 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h189 := .lam e2817
private def e2819 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h195 := .app e2816 e2818
private def e2820 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h173 := .app e2819 e2818
private def e2821 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h189 := .app e2809 e2820
private def e2822 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h173 := .app e2821 e2820
private def e2823 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h213 := .lam e2822
private def e2824 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h192] h173 := .app e2815 e2823
private def e2825 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h177, h173, h192] h189 := .lam e2824
private def e2826 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192] h192 := .lam e2825
private def e2827 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2828 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192] h189 := .app e2826 e2827
private def e2829 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192] h173 := .var (HOL.Var.vz)
private def e2830 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192] h173 := .app e2828 e2829
private def e2831 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192] h189 := .app e2807 e2830
private def e2832 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192] h173 := .app e2831 e2827
private def e2833 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h192] h189 := .lam e2832
private def e2834 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192] h192 := .lam e2833
private def e2835 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2836 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192] h189 := .app e2834 e2835
private def e2837 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2838 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192] h189 := .app e2834 e2837
private def e2839 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192] h173 := .var (HOL.Var.vz)
private def e2840 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192] h173 := .app e2838 e2839
private def e2841 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192] h173 := .app e2836 e2840
private def e2842 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192] h189 := .app e2834 e2841
private def e2843 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192] h173 := .app e2842 e2839
private def e2844 : HOL.Term Symbol [h173, h173, h177, h173, h192] h189 := .lam e2843
private def e2845 : HOL.Term Symbol [h173, h173, h177, h173, h192] h173 := .app e2806 e2844
private def e2846 : HOL.Term Symbol [h173, h177, h173, h192] h189 := .lam e2845
private def e2847 : HOL.Term Symbol [h177, h173, h192] h192 := .lam e2846
private def e2848 : HOL.Term Symbol [h177, h173, h192] h180 := .const (.variable ⟨Name.mk [] "pointedCarrierProperty", t2⟩ q181)
private def e2849 : HOL.Term Symbol [h177, h173, h192] h177 := .var (HOL.Var.vz)
private def e2850 : HOL.Term Symbol [h177, h173, h192] h173 := .app e2848 e2849
private def e2851 : HOL.Term Symbol [h177, h173, h192] h189 := .app e2847 e2850
private def e2852 : HOL.Term Symbol [h177, h173, h192] h264 := .const (.constant Const.equality t63 q265)
private def e2853 : HOL.Term Symbol [h189, h180, h177, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2854 : HOL.Term Symbol [h189, h180, h177, h173, h192] h189 := .var (HOL.Var.vz)
private def e2855 : HOL.Term Symbol [h189, h180, h177, h173, h192] h195 := .app e2853 e2854
private def e2856 : HOL.Term Symbol [h173, h189, h180, h177, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e2857 : HOL.Term Symbol [h173, h173, h189, h180, h177, h173, h192] h173 := .var (HOL.Var.vz)
private def e2858 : HOL.Term Symbol [h173, h189, h180, h177, h173, h192] h189 := .lam e2857
private def e2859 : HOL.Term Symbol [h173, h189, h180, h177, h173, h192] h195 := .app e2856 e2858
private def e2860 : HOL.Term Symbol [h173, h189, h180, h177, h173, h192] h173 := .app e2859 e2858
private def e2861 : HOL.Term Symbol [h189, h180, h177, h173, h192] h189 := .lam e2860
private def e2862 : HOL.Term Symbol [h189, h180, h177, h173, h192] h173 := .app e2855 e2861
private def e2863 : HOL.Term Symbol [h180, h177, h173, h192] h195 := .lam e2862
private def e2864 : HOL.Term Symbol [h173, h180, h177, h173, h192] h173 := .var (HOL.Var.vz)
private def e2865 : HOL.Term Symbol [h180, h177, h173, h192] h189 := .lam e2864
private def e2866 : HOL.Term Symbol [h180, h177, h173, h192] h173 := .app e2863 e2865
private def e2867 : HOL.Term Symbol [h177, h173, h192] h183 := .lam e2866
private def e2868 : HOL.Term Symbol [h177, h173, h192] h186 := .app e2852 e2867
private def e2869 : HOL.Term Symbol [h180, h177, h173, h192] h180 := .var (HOL.Var.vz)
private def e2870 : HOL.Term Symbol [h180, h177, h173, h192] h177 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2871 : HOL.Term Symbol [h180, h177, h173, h192] h173 := .app e2869 e2870
private def e2872 : HOL.Term Symbol [h177, h173, h192] h183 := .lam e2871
private def e2873 : HOL.Term Symbol [h177, h173, h192] h173 := .app e2868 e2872
private def e2874 : HOL.Term Symbol [h177, h173, h192] h173 := .app e2851 e2873
private def e2875 : HOL.Term Symbol [h173, h192] h180 := .lam e2874
private def e2876 : HOL.Term Symbol [h173, h192] h173 := .app e2795 e2875
private def e2877 : HOL.Term Symbol [h173, h192] h189 := .app e2694 e2876
private def e2878 : HOL.Term Symbol [h173, h192] h173 := .app e2877 e1267
private def e2879 : HOL.Term Symbol [h173, h192] h189 := .app e2694 e2878
private def e2880 : HOL.Term Symbol [h173, h192] h173 := .app e2879 e1267
private def e2881 : HOL.Term Symbol [h173, h192] h173 := .app e2715 e2880
private def e2882 : HOL.Term Symbol [h192] h189 := .lam e2881
private def e2883 : HOL.Term Symbol [h192] h173 := .app e2668 e2882
private def e2884 : HOL.Term Symbol [h192] h189 := .app e802 e2883
private def e2885 : HOL.Term Symbol [h192] h173 := .app e2884 e1037
private def e2886 : HOL.Term Symbol [] h213 := .lam e2885
private def e2887 : HOL.Term Symbol [] h216 := .app e801 e2886
private def e2888 : HOL.Term Symbol [] h173 := .app e2887 e1273
private def c2889 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2888
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
private def e2926 : HOL.Term Symbol [] h189 := .app e1308 e2602
private def e2927 : HOL.Term Symbol [] h195 := .app e727 e2926
private def e2928 : HOL.Term Symbol [h189, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2929 : HOL.Term Symbol [h189, h192, h173] h189 := .var (HOL.Var.vz)
private def e2930 : HOL.Term Symbol [h189, h192, h173] h195 := .app e2928 e2929
private def e2931 : HOL.Term Symbol [h173, h189, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2932 : HOL.Term Symbol [h173, h173, h189, h192, h173] h173 := .var (HOL.Var.vz)
private def e2933 : HOL.Term Symbol [h173, h189, h192, h173] h189 := .lam e2932
private def e2934 : HOL.Term Symbol [h173, h189, h192, h173] h195 := .app e2931 e2933
private def e2935 : HOL.Term Symbol [h173, h189, h192, h173] h173 := .app e2934 e2933
private def e2936 : HOL.Term Symbol [h189, h192, h173] h189 := .lam e2935
private def e2937 : HOL.Term Symbol [h189, h192, h173] h173 := .app e2930 e2936
private def e2938 : HOL.Term Symbol [h192, h173] h195 := .lam e2937
private def e2939 : HOL.Term Symbol [h173, h173, h173, h192, h173] h192 := .const (.constant Const.equality t17 q193)
private def e2940 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h219 := .const (.constant Const.equality t21 q220)
private def e2941 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192, h173] h192 := .var (HOL.Var.vz)
private def e2942 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2943 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192, h173] h189 := .app e2941 e2942
private def e2944 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2945 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192, h173] h173 := .app e2943 e2944
private def e2946 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h213 := .lam e2945
private def e2947 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h216 := .app e2940 e2946
private def e2948 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2949 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e2950 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192, h173] h189 := .lam e2949
private def e2951 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192, h173] h195 := .app e2948 e2950
private def e2952 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192, h173] h173 := .app e2951 e2950
private def e2953 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192, h173] h189 := .app e2941 e2952
private def e2954 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h192, h173] h173 := .app e2953 e2952
private def e2955 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h213 := .lam e2954
private def e2956 : HOL.Term Symbol [h173, h173, h173, h173, h173, h192, h173] h173 := .app e2947 e2955
private def e2957 : HOL.Term Symbol [h173, h173, h173, h173, h192, h173] h189 := .lam e2956
private def e2958 : HOL.Term Symbol [h173, h173, h173, h192, h173] h192 := .lam e2957
private def e2959 : HOL.Term Symbol [h173, h173, h173, h192, h173] h189 := .app e2958 e1455
private def e2960 : HOL.Term Symbol [h173, h173, h173, h192, h173] h173 := .app e2959 e1452
private def e2961 : HOL.Term Symbol [h173, h173, h173, h192, h173] h189 := .app e2939 e2960
private def e2962 : HOL.Term Symbol [h173, h173, h173, h192, h173] h173 := .app e2961 e1455
private def e2963 : HOL.Term Symbol [h173, h173, h192, h173] h189 := .lam e2962
private def e2964 : HOL.Term Symbol [h173, h192, h173] h192 := .lam e2963
private def e2965 : HOL.Term Symbol [h173, h192, h173] h264 := .const (.constant Const.equality t63 q265)
private def e2966 : HOL.Term Symbol [h189, h180, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2967 : HOL.Term Symbol [h189, h180, h173, h192, h173] h189 := .var (HOL.Var.vz)
private def e2968 : HOL.Term Symbol [h189, h180, h173, h192, h173] h195 := .app e2966 e2967
private def e2969 : HOL.Term Symbol [h173, h189, h180, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2970 : HOL.Term Symbol [h173, h173, h189, h180, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e2971 : HOL.Term Symbol [h173, h189, h180, h173, h192, h173] h189 := .lam e2970
private def e2972 : HOL.Term Symbol [h173, h189, h180, h173, h192, h173] h195 := .app e2969 e2971
private def e2973 : HOL.Term Symbol [h173, h189, h180, h173, h192, h173] h173 := .app e2972 e2971
private def e2974 : HOL.Term Symbol [h189, h180, h173, h192, h173] h189 := .lam e2973
private def e2975 : HOL.Term Symbol [h189, h180, h173, h192, h173] h173 := .app e2968 e2974
private def e2976 : HOL.Term Symbol [h180, h173, h192, h173] h195 := .lam e2975
private def e2977 : HOL.Term Symbol [h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e2978 : HOL.Term Symbol [h180, h173, h192, h173] h189 := .lam e2977
private def e2979 : HOL.Term Symbol [h180, h173, h192, h173] h173 := .app e2976 e2978
private def e2980 : HOL.Term Symbol [h173, h192, h173] h183 := .lam e2979
private def e2981 : HOL.Term Symbol [h173, h192, h173] h186 := .app e2965 e2980
private def e2982 : HOL.Term Symbol [h173, h192, h173] h173 := .app e2981 e2980
private def e2983 : HOL.Term Symbol [h173, h192, h173] h189 := .app e2964 e2982
private def e2984 : HOL.Term Symbol [h173, h192, h173] h173 := .app e2983 e1325
private def e2985 : HOL.Term Symbol [h173, h192, h173] h189 := .app e2964 e2984
private def e2986 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192, h173] h192 := .const (.constant Const.equality t17 q193)
private def e2987 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h192, h173] h219 := .const (.constant Const.equality t21 q220)
private def e2988 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192, h173] h192 := .var (HOL.Var.vz)
private def e2989 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e2990 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192, h173] h189 := .app e2988 e2989
private def e2991 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e2992 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192, h173] h173 := .app e2990 e2991
private def e2993 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h192, h173] h213 := .lam e2992
private def e2994 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h192, h173] h216 := .app e2987 e2993
private def e2995 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e2996 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e2997 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192, h173] h189 := .lam e2996
private def e2998 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192, h173] h195 := .app e2995 e2997
private def e2999 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192, h173] h173 := .app e2998 e2997
private def e3000 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192, h173] h189 := .app e2988 e2999
private def e3001 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h192, h173] h173 := .app e3000 e2999
private def e3002 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h192, h173] h213 := .lam e3001
private def e3003 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h192, h173] h173 := .app e2994 e3002
private def e3004 : HOL.Term Symbol [h173, h173, h173, h173, h180, h173, h192, h173] h189 := .lam e3003
private def e3005 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192, h173] h192 := .lam e3004
private def e3006 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3007 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192, h173] h189 := .app e3005 e3006
private def e3008 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e3009 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192, h173] h173 := .app e3007 e3008
private def e3010 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192, h173] h189 := .app e2986 e3009
private def e3011 : HOL.Term Symbol [h173, h173, h173, h180, h173, h192, h173] h173 := .app e3010 e3006
private def e3012 : HOL.Term Symbol [h173, h173, h180, h173, h192, h173] h189 := .lam e3011
private def e3013 : HOL.Term Symbol [h173, h180, h173, h192, h173] h192 := .lam e3012
private def e3014 : HOL.Term Symbol [h180, h173, h180, h173, h192, h173] h315 := .const (.constant Const.equality t101 q316)
private def e3015 : HOL.Term Symbol [h180, h173, h180, h173, h192, h173] h180 := .var (HOL.Var.vz)
private def e3016 : HOL.Term Symbol [h180, h173, h180, h173, h192, h173] h183 := .app e3014 e3015
private def e3017 : HOL.Term Symbol [h177, h180, h173, h180, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3018 : HOL.Term Symbol [h173, h177, h180, h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e3019 : HOL.Term Symbol [h177, h180, h173, h180, h173, h192, h173] h189 := .lam e3018
private def e3020 : HOL.Term Symbol [h177, h180, h173, h180, h173, h192, h173] h195 := .app e3017 e3019
private def e3021 : HOL.Term Symbol [h177, h180, h173, h180, h173, h192, h173] h173 := .app e3020 e3019
private def e3022 : HOL.Term Symbol [h180, h173, h180, h173, h192, h173] h180 := .lam e3021
private def e3023 : HOL.Term Symbol [h180, h173, h180, h173, h192, h173] h173 := .app e3016 e3022
private def e3024 : HOL.Term Symbol [h173, h180, h173, h192, h173] h183 := .lam e3023
private def e3025 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192, h173] h192 := .const (.constant Const.equality t17 q193)
private def e3026 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h219 := .const (.constant Const.equality t21 q220)
private def e3027 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h192 := .var (HOL.Var.vz)
private def e3028 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e3029 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h189 := .app e3027 e3028
private def e3030 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3031 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h173 := .app e3029 e3030
private def e3032 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h213 := .lam e3031
private def e3033 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h216 := .app e3026 e3032
private def e3034 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3035 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e3036 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h189 := .lam e3035
private def e3037 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h195 := .app e3034 e3036
private def e3038 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h173 := .app e3037 e3036
private def e3039 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h189 := .app e3027 e3038
private def e3040 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h173 := .app e3039 e3038
private def e3041 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h213 := .lam e3040
private def e3042 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h192, h173] h173 := .app e3033 e3041
private def e3043 : HOL.Term Symbol [h173, h173, h173, h177, h173, h180, h173, h192, h173] h189 := .lam e3042
private def e3044 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192, h173] h192 := .lam e3043
private def e3045 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3046 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192, h173] h189 := .app e3044 e3045
private def e3047 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e3048 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192, h173] h173 := .app e3046 e3047
private def e3049 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192, h173] h189 := .app e3025 e3048
private def e3050 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h192, h173] h173 := .app e3049 e3045
private def e3051 : HOL.Term Symbol [h173, h177, h173, h180, h173, h192, h173] h189 := .lam e3050
private def e3052 : HOL.Term Symbol [h177, h173, h180, h173, h192, h173] h192 := .lam e3051
private def e3053 : HOL.Term Symbol [h177, h173, h180, h173, h192, h173] h180 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e3054 : HOL.Term Symbol [h177, h173, h180, h173, h192, h173] h177 := .var (HOL.Var.vz)
private def e3055 : HOL.Term Symbol [h177, h173, h180, h173, h192, h173] h173 := .app e3053 e3054
private def e3056 : HOL.Term Symbol [h177, h173, h180, h173, h192, h173] h189 := .app e3052 e3055
private def e3057 : HOL.Term Symbol [h177, h173, h180, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3058 : HOL.Term Symbol [h177, h173, h180, h173, h192, h173] h173 := .app e3056 e3057
private def e3059 : HOL.Term Symbol [h173, h180, h173, h192, h173] h180 := .lam e3058
private def e3060 : HOL.Term Symbol [h173, h180, h173, h192, h173] h173 := .app e3024 e3059
private def e3061 : HOL.Term Symbol [h173, h180, h173, h192, h173] h189 := .app e3013 e3060
private def e3062 : HOL.Term Symbol [h173, h180, h173, h192, h173] h173 := .app e3061 e2977
private def e3063 : HOL.Term Symbol [h180, h173, h192, h173] h189 := .lam e3062
private def e3064 : HOL.Term Symbol [h180, h173, h192, h173] h173 := .app e2976 e3063
private def e3065 : HOL.Term Symbol [h173, h192, h173] h183 := .lam e3064
private def e3066 : HOL.Term Symbol [h189, h173, h173, h177, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3067 : HOL.Term Symbol [h189, h173, h173, h177, h173, h192, h173] h189 := .var (HOL.Var.vz)
private def e3068 : HOL.Term Symbol [h189, h173, h173, h177, h173, h192, h173] h195 := .app e3066 e3067
private def e3069 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3070 : HOL.Term Symbol [h173, h173, h189, h173, h173, h177, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e3071 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173, h192, h173] h189 := .lam e3070
private def e3072 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173, h192, h173] h195 := .app e3069 e3071
private def e3073 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173, h192, h173] h173 := .app e3072 e3071
private def e3074 : HOL.Term Symbol [h189, h173, h173, h177, h173, h192, h173] h189 := .lam e3073
private def e3075 : HOL.Term Symbol [h189, h173, h173, h177, h173, h192, h173] h173 := .app e3068 e3074
private def e3076 : HOL.Term Symbol [h173, h173, h177, h173, h192, h173] h195 := .lam e3075
private def e3077 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192, h173] h192 := .const (.constant Const.equality t17 q193)
private def e3078 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h219 := .const (.constant Const.equality t21 q220)
private def e3079 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h192 := .var (HOL.Var.vz)
private def e3080 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e3081 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h189 := .app e3079 e3080
private def e3082 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3083 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h173 := .app e3081 e3082
private def e3084 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h213 := .lam e3083
private def e3085 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h216 := .app e3078 e3084
private def e3086 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3087 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e3088 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h189 := .lam e3087
private def e3089 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h195 := .app e3086 e3088
private def e3090 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h173 := .app e3089 e3088
private def e3091 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h189 := .app e3079 e3090
private def e3092 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h173 := .app e3091 e3090
private def e3093 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h213 := .lam e3092
private def e3094 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h173 := .app e3085 e3093
private def e3095 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h177, h173, h192, h173] h189 := .lam e3094
private def e3096 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192, h173] h192 := .lam e3095
private def e3097 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3098 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192, h173] h189 := .app e3096 e3097
private def e3099 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e3100 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192, h173] h173 := .app e3098 e3099
private def e3101 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192, h173] h189 := .app e3077 e3100
private def e3102 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h192, h173] h173 := .app e3101 e3097
private def e3103 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h192, h173] h189 := .lam e3102
private def e3104 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192, h173] h192 := .lam e3103
private def e3105 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e3106 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192, h173] h189 := .app e3104 e3105
private def e3107 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3108 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192, h173] h189 := .app e3104 e3107
private def e3109 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e3110 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192, h173] h173 := .app e3108 e3109
private def e3111 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192, h173] h173 := .app e3106 e3110
private def e3112 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192, h173] h189 := .app e3104 e3111
private def e3113 : HOL.Term Symbol [h173, h173, h173, h177, h173, h192, h173] h173 := .app e3112 e3109
private def e3114 : HOL.Term Symbol [h173, h173, h177, h173, h192, h173] h189 := .lam e3113
private def e3115 : HOL.Term Symbol [h173, h173, h177, h173, h192, h173] h173 := .app e3076 e3114
private def e3116 : HOL.Term Symbol [h173, h177, h173, h192, h173] h189 := .lam e3115
private def e3117 : HOL.Term Symbol [h177, h173, h192, h173] h192 := .lam e3116
private def e3118 : HOL.Term Symbol [h177, h173, h192, h173] h180 := .const (.variable ⟨Name.mk [] "pointedCarrierProperty", t2⟩ q181)
private def e3119 : HOL.Term Symbol [h177, h173, h192, h173] h177 := .var (HOL.Var.vz)
private def e3120 : HOL.Term Symbol [h177, h173, h192, h173] h173 := .app e3118 e3119
private def e3121 : HOL.Term Symbol [h177, h173, h192, h173] h189 := .app e3117 e3120
private def e3122 : HOL.Term Symbol [h177, h173, h192, h173] h264 := .const (.constant Const.equality t63 q265)
private def e3123 : HOL.Term Symbol [h189, h180, h177, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3124 : HOL.Term Symbol [h189, h180, h177, h173, h192, h173] h189 := .var (HOL.Var.vz)
private def e3125 : HOL.Term Symbol [h189, h180, h177, h173, h192, h173] h195 := .app e3123 e3124
private def e3126 : HOL.Term Symbol [h173, h189, h180, h177, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3127 : HOL.Term Symbol [h173, h173, h189, h180, h177, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e3128 : HOL.Term Symbol [h173, h189, h180, h177, h173, h192, h173] h189 := .lam e3127
private def e3129 : HOL.Term Symbol [h173, h189, h180, h177, h173, h192, h173] h195 := .app e3126 e3128
private def e3130 : HOL.Term Symbol [h173, h189, h180, h177, h173, h192, h173] h173 := .app e3129 e3128
private def e3131 : HOL.Term Symbol [h189, h180, h177, h173, h192, h173] h189 := .lam e3130
private def e3132 : HOL.Term Symbol [h189, h180, h177, h173, h192, h173] h173 := .app e3125 e3131
private def e3133 : HOL.Term Symbol [h180, h177, h173, h192, h173] h195 := .lam e3132
private def e3134 : HOL.Term Symbol [h173, h180, h177, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e3135 : HOL.Term Symbol [h180, h177, h173, h192, h173] h189 := .lam e3134
private def e3136 : HOL.Term Symbol [h180, h177, h173, h192, h173] h173 := .app e3133 e3135
private def e3137 : HOL.Term Symbol [h177, h173, h192, h173] h183 := .lam e3136
private def e3138 : HOL.Term Symbol [h177, h173, h192, h173] h186 := .app e3122 e3137
private def e3139 : HOL.Term Symbol [h180, h177, h173, h192, h173] h180 := .var (HOL.Var.vz)
private def e3140 : HOL.Term Symbol [h180, h177, h173, h192, h173] h177 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3141 : HOL.Term Symbol [h180, h177, h173, h192, h173] h173 := .app e3139 e3140
private def e3142 : HOL.Term Symbol [h177, h173, h192, h173] h183 := .lam e3141
private def e3143 : HOL.Term Symbol [h177, h173, h192, h173] h173 := .app e3138 e3142
private def e3144 : HOL.Term Symbol [h177, h173, h192, h173] h173 := .app e3121 e3143
private def e3145 : HOL.Term Symbol [h173, h192, h173] h180 := .lam e3144
private def e3146 : HOL.Term Symbol [h173, h192, h173] h173 := .app e3065 e3145
private def e3147 : HOL.Term Symbol [h173, h192, h173] h189 := .app e2964 e3146
private def e3148 : HOL.Term Symbol [h173, h192, h173] h173 := .app e3147 e1325
private def e3149 : HOL.Term Symbol [h173, h192, h173] h189 := .app e2964 e3148
private def e3150 : HOL.Term Symbol [h173, h192, h173] h173 := .app e3149 e1325
private def e3151 : HOL.Term Symbol [h173, h192, h173] h173 := .app e2985 e3150
private def e3152 : HOL.Term Symbol [h192, h173] h189 := .lam e3151
private def e3153 : HOL.Term Symbol [h192, h173] h173 := .app e2938 e3152
private def e3154 : HOL.Term Symbol [h192, h173] h189 := .app e1317 e3153
private def e3155 : HOL.Term Symbol [h192, h173] h173 := .app e3154 e1320
private def e3156 : HOL.Term Symbol [h173] h213 := .lam e3155
private def e3157 : HOL.Term Symbol [h173] h216 := .app e1316 e3156
private def e3158 : HOL.Term Symbol [h173] h173 := .app e3157 e1331
private def e3159 : HOL.Term Symbol [] h189 := .lam e3158
private def e3160 : HOL.Term Symbol [] h173 := .app e2927 e3159
private def c3161 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3160
private def f3162 : Theorem := Theorem.emptyResult ([].toFinset) c3161
private def r3163 : InferenceRequest := .mkComb f3162 f759
private def e3164 : HOL.Term Symbol [] h173 := .app e2926 e711
private def e3165 : HOL.Term Symbol [] h189 := .app e445 e3164
private def e3166 : HOL.Term Symbol [] h173 := .app e3159 e711
private def e3167 : HOL.Term Symbol [] h173 := .app e3165 e3166
private def c3168 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3167
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
private def e3251 : HOL.Term Symbol [] h173 := .app e3159 e1309
private def c3252 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3251
private theorem n3253 : s3250.toDB [] = c3252.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3254 : CheckedSourceTerm := ⟨s3250, t1, by rw [← DBTerm.inferType_toDB [] s3250, n3253]; exact c3252.checked.trans (congrArg some v175)⟩
private def r3255 : InferenceRequest := .beta k3254
private def e3256 : HOL.Term Symbol [] h189 := .app e445 e3251
private def e3257 : HOL.Term Symbol [h192] h173 := .app e2884 e1759
private def e3258 : HOL.Term Symbol [] h213 := .lam e3257
private def e3259 : HOL.Term Symbol [] h216 := .app e801 e3258
private def e3260 : HOL.Term Symbol [] h173 := .app e3259 e1273
private def e3261 : HOL.Term Symbol [] h173 := .app e3256 e3260
private def c3262 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3261
private def f3263 : Theorem := Theorem.emptyResult ([].toFinset) c3262
private def r3264 : InferenceRequest := .inst [(k1407, s1278)] f3263
private def e3265 : HOL.Term Symbol [] h189 := .app e445 e3166
private def e3266 : HOL.Term Symbol [] h173 := .app e3265 e2888
private def c3267 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3266
private def f3268 : Theorem := Theorem.emptyResult ([].toFinset) c3267
private def r3269 : InferenceRequest := .trans f3169 f3268
private def e3270 : HOL.Term Symbol [] h173 := .app e3165 e2888
private def c3271 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3270
private def f3272 : Theorem := Theorem.emptyResult ([].toFinset) c3271
private def r3273 : InferenceRequest := .mkComb f725 f3272
private def e3274 : HOL.Term Symbol [] h195 := .app e727 e3165
private def e3275 : HOL.Term Symbol [] h189 := .app e445 e2888
private def e3276 : HOL.Term Symbol [] h173 := .app e3274 e3275
private def c3277 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3276
private def f3278 : Theorem := Theorem.emptyResult ([].toFinset) c3277
private def c3279 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3164
private def r3280 : InferenceRequest := .refl c3279
private def e3281 : HOL.Term Symbol [] h173 := .app e3165 e3164
private def c3282 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3281
private def f3283 : Theorem := Theorem.emptyResult ([].toFinset) c3282
private def r3284 : InferenceRequest := .mkComb f3278 f3283
private def e3285 : HOL.Term Symbol [] h189 := .app e445 e3281
private def e3286 : HOL.Term Symbol [] h173 := .app e3275 e3164
private def e3287 : HOL.Term Symbol [] h173 := .app e3285 e3286
private def c3288 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3287
private def f3289 : Theorem := Theorem.emptyResult ([].toFinset) c3288
private def r3290 : InferenceRequest := .eqMp f3289 f3283
private def c3291 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3286
private def f3292 : Theorem := Theorem.emptyResult ([].toFinset) c3291
private def r3293 : InferenceRequest := .eqMp f3292 f2890
private def f3294 : Theorem := Theorem.emptyResult ([c2623].toFinset) c3279
private def r3295 : InferenceRequest := .assume c3279
private def f3296 : Theorem := Theorem.emptyResult ([c3279].toFinset) c3279
private def r3297 : InferenceRequest := .eqMp f3272 f3296
private def f3298 : Theorem := Theorem.emptyResult ([c3279].toFinset) c2889
private def r3299 : InferenceRequest := .mkComb f3298 f1813
private def e3300 : HOL.Term Symbol [] h173 := .app e2886 e1807
private def e3301 : HOL.Term Symbol [] h189 := .app e445 e3300
private def e3302 : HOL.Term Symbol [] h173 := .app e3301 e1817
private def c3303 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3302
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
private def e3316 : HOL.Term Symbol [] h173 := .app e2886 e763
private def c3317 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3316
private theorem n3318 : s3315.toDB [] = c3317.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3319 : CheckedSourceTerm := ⟨s3315, t1, by rw [← DBTerm.inferType_toDB [] s3315, n3318]; exact c3317.checked.trans (congrArg some v175)⟩
private def r3320 : InferenceRequest := .beta k3319
private def e3321 : HOL.Term Symbol [] h189 := .app e445 e3316
private def e3322 : HOL.Term Symbol [] h173 := .app e3321 e2652
private def c3323 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3322
private def f3324 : Theorem := Theorem.emptyResult ([].toFinset) c3323
private def r3325 : InferenceRequest := .inst [(k1856, s1821)] f3324
private def e3326 : HOL.Term Symbol [] h189 := .app e1807 e2602
private def e3327 : HOL.Term Symbol [] h173 := .app e3326 e711
private def e3328 : HOL.Term Symbol [] h173 := .app e3301 e3327
private def c3329 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3328
private def f3330 : Theorem := Theorem.emptyResult ([].toFinset) c3329
private def r3331 : InferenceRequest := .inst [(k2924, s1278)] f1874
private def e3332 : HOL.Term Symbol [] h195 := .app e727 e3326
private def e3333 : HOL.Term Symbol [h173, h173, h173, h180, h173, h173] h192 := .const (.constant Const.equality t17 q193)
private def e3334 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h173] h219 := .const (.constant Const.equality t21 q220)
private def e3335 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h173] h192 := .var (HOL.Var.vz)
private def e3336 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e3337 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h173] h189 := .app e3335 e3336
private def e3338 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3339 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h173] h173 := .app e3337 e3338
private def e3340 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h173] h213 := .lam e3339
private def e3341 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h173] h216 := .app e3334 e3340
private def e3342 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3343 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h180, h173, h173] h173 := .var (HOL.Var.vz)
private def e3344 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h173] h189 := .lam e3343
private def e3345 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h173] h195 := .app e3342 e3344
private def e3346 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h173] h173 := .app e3345 e3344
private def e3347 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h173] h189 := .app e3335 e3346
private def e3348 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h180, h173, h173] h173 := .app e3347 e3346
private def e3349 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h173] h213 := .lam e3348
private def e3350 : HOL.Term Symbol [h173, h173, h173, h173, h173, h180, h173, h173] h173 := .app e3341 e3349
private def e3351 : HOL.Term Symbol [h173, h173, h173, h173, h180, h173, h173] h189 := .lam e3350
private def e3352 : HOL.Term Symbol [h173, h173, h173, h180, h173, h173] h192 := .lam e3351
private def e3353 : HOL.Term Symbol [h173, h173, h173, h180, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3354 : HOL.Term Symbol [h173, h173, h173, h180, h173, h173] h189 := .app e3352 e3353
private def e3355 : HOL.Term Symbol [h173, h173, h173, h180, h173, h173] h173 := .var (HOL.Var.vz)
private def e3356 : HOL.Term Symbol [h173, h173, h173, h180, h173, h173] h173 := .app e3354 e3355
private def e3357 : HOL.Term Symbol [h173, h173, h173, h180, h173, h173] h189 := .app e3333 e3356
private def e3358 : HOL.Term Symbol [h173, h173, h173, h180, h173, h173] h173 := .app e3357 e3353
private def e3359 : HOL.Term Symbol [h173, h173, h180, h173, h173] h189 := .lam e3358
private def e3360 : HOL.Term Symbol [h173, h180, h173, h173] h192 := .lam e3359
private def e3361 : HOL.Term Symbol [h180, h173, h180, h173, h173] h315 := .const (.constant Const.equality t101 q316)
private def e3362 : HOL.Term Symbol [h180, h173, h180, h173, h173] h180 := .var (HOL.Var.vz)
private def e3363 : HOL.Term Symbol [h180, h173, h180, h173, h173] h183 := .app e3361 e3362
private def e3364 : HOL.Term Symbol [h177, h180, h173, h180, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3365 : HOL.Term Symbol [h173, h177, h180, h173, h180, h173, h173] h173 := .var (HOL.Var.vz)
private def e3366 : HOL.Term Symbol [h177, h180, h173, h180, h173, h173] h189 := .lam e3365
private def e3367 : HOL.Term Symbol [h177, h180, h173, h180, h173, h173] h195 := .app e3364 e3366
private def e3368 : HOL.Term Symbol [h177, h180, h173, h180, h173, h173] h173 := .app e3367 e3366
private def e3369 : HOL.Term Symbol [h180, h173, h180, h173, h173] h180 := .lam e3368
private def e3370 : HOL.Term Symbol [h180, h173, h180, h173, h173] h173 := .app e3363 e3369
private def e3371 : HOL.Term Symbol [h173, h180, h173, h173] h183 := .lam e3370
private def e3372 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h173] h192 := .const (.constant Const.equality t17 q193)
private def e3373 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h173] h219 := .const (.constant Const.equality t21 q220)
private def e3374 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h173] h192 := .var (HOL.Var.vz)
private def e3375 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e3376 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h173] h189 := .app e3374 e3375
private def e3377 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3378 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h173] h173 := .app e3376 e3377
private def e3379 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h173] h213 := .lam e3378
private def e3380 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h173] h216 := .app e3373 e3379
private def e3381 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3382 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h177, h173, h180, h173, h173] h173 := .var (HOL.Var.vz)
private def e3383 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h173] h189 := .lam e3382
private def e3384 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h173] h195 := .app e3381 e3383
private def e3385 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h173] h173 := .app e3384 e3383
private def e3386 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h173] h189 := .app e3374 e3385
private def e3387 : HOL.Term Symbol [h192, h173, h173, h173, h173, h177, h173, h180, h173, h173] h173 := .app e3386 e3385
private def e3388 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h173] h213 := .lam e3387
private def e3389 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h180, h173, h173] h173 := .app e3380 e3388
private def e3390 : HOL.Term Symbol [h173, h173, h173, h177, h173, h180, h173, h173] h189 := .lam e3389
private def e3391 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h173] h192 := .lam e3390
private def e3392 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3393 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h173] h189 := .app e3391 e3392
private def e3394 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h173] h173 := .var (HOL.Var.vz)
private def e3395 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h173] h173 := .app e3393 e3394
private def e3396 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h173] h189 := .app e3372 e3395
private def e3397 : HOL.Term Symbol [h173, h173, h177, h173, h180, h173, h173] h173 := .app e3396 e3392
private def e3398 : HOL.Term Symbol [h173, h177, h173, h180, h173, h173] h189 := .lam e3397
private def e3399 : HOL.Term Symbol [h177, h173, h180, h173, h173] h192 := .lam e3398
private def e3400 : HOL.Term Symbol [h177, h173, h180, h173, h173] h180 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e3401 : HOL.Term Symbol [h177, h173, h180, h173, h173] h177 := .var (HOL.Var.vz)
private def e3402 : HOL.Term Symbol [h177, h173, h180, h173, h173] h173 := .app e3400 e3401
private def e3403 : HOL.Term Symbol [h177, h173, h180, h173, h173] h189 := .app e3399 e3402
private def e3404 : HOL.Term Symbol [h177, h173, h180, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3405 : HOL.Term Symbol [h177, h173, h180, h173, h173] h173 := .app e3403 e3404
private def e3406 : HOL.Term Symbol [h173, h180, h173, h173] h180 := .lam e3405
private def e3407 : HOL.Term Symbol [h173, h180, h173, h173] h173 := .app e3371 e3406
private def e3408 : HOL.Term Symbol [h173, h180, h173, h173] h189 := .app e3360 e3407
private def e3409 : HOL.Term Symbol [h173, h180, h173, h173] h173 := .app e3408 e2497
private def e3410 : HOL.Term Symbol [h180, h173, h173] h189 := .lam e3409
private def e3411 : HOL.Term Symbol [h180, h173, h173] h173 := .app e2496 e3410
private def e3412 : HOL.Term Symbol [h173, h173] h183 := .lam e3411
private def e3413 : HOL.Term Symbol [h189, h173, h173, h177, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3414 : HOL.Term Symbol [h189, h173, h173, h177, h173, h173] h189 := .var (HOL.Var.vz)
private def e3415 : HOL.Term Symbol [h189, h173, h173, h177, h173, h173] h195 := .app e3413 e3414
private def e3416 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3417 : HOL.Term Symbol [h173, h173, h189, h173, h173, h177, h173, h173] h173 := .var (HOL.Var.vz)
private def e3418 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173, h173] h189 := .lam e3417
private def e3419 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173, h173] h195 := .app e3416 e3418
private def e3420 : HOL.Term Symbol [h173, h189, h173, h173, h177, h173, h173] h173 := .app e3419 e3418
private def e3421 : HOL.Term Symbol [h189, h173, h173, h177, h173, h173] h189 := .lam e3420
private def e3422 : HOL.Term Symbol [h189, h173, h173, h177, h173, h173] h173 := .app e3415 e3421
private def e3423 : HOL.Term Symbol [h173, h173, h177, h173, h173] h195 := .lam e3422
private def e3424 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h173] h192 := .const (.constant Const.equality t17 q193)
private def e3425 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h219 := .const (.constant Const.equality t21 q220)
private def e3426 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h192 := .var (HOL.Var.vz)
private def e3427 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e3428 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h189 := .app e3426 e3427
private def e3429 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3430 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h173 := .app e3428 e3429
private def e3431 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h213 := .lam e3430
private def e3432 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h216 := .app e3425 e3431
private def e3433 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3434 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h173 := .var (HOL.Var.vz)
private def e3435 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h189 := .lam e3434
private def e3436 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h195 := .app e3433 e3435
private def e3437 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h173 := .app e3436 e3435
private def e3438 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h189 := .app e3426 e3437
private def e3439 : HOL.Term Symbol [h192, h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h173 := .app e3438 e3437
private def e3440 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h213 := .lam e3439
private def e3441 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h173, h177, h173, h173] h173 := .app e3432 e3440
private def e3442 : HOL.Term Symbol [h173, h173, h173, h173, h173, h173, h177, h173, h173] h189 := .lam e3441
private def e3443 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h173] h192 := .lam e3442
private def e3444 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3445 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h173] h189 := .app e3443 e3444
private def e3446 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h173] h173 := .var (HOL.Var.vz)
private def e3447 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h173] h173 := .app e3445 e3446
private def e3448 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h173] h189 := .app e3424 e3447
private def e3449 : HOL.Term Symbol [h173, h173, h173, h173, h173, h177, h173, h173] h173 := .app e3448 e3444
private def e3450 : HOL.Term Symbol [h173, h173, h173, h173, h177, h173, h173] h189 := .lam e3449
private def e3451 : HOL.Term Symbol [h173, h173, h173, h177, h173, h173] h192 := .lam e3450
private def e3452 : HOL.Term Symbol [h173, h173, h173, h177, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e3453 : HOL.Term Symbol [h173, h173, h173, h177, h173, h173] h189 := .app e3451 e3452
private def e3454 : HOL.Term Symbol [h173, h173, h173, h177, h173, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3455 : HOL.Term Symbol [h173, h173, h173, h177, h173, h173] h189 := .app e3451 e3454
private def e3456 : HOL.Term Symbol [h173, h173, h173, h177, h173, h173] h173 := .var (HOL.Var.vz)
private def e3457 : HOL.Term Symbol [h173, h173, h173, h177, h173, h173] h173 := .app e3455 e3456
private def e3458 : HOL.Term Symbol [h173, h173, h173, h177, h173, h173] h173 := .app e3453 e3457
private def e3459 : HOL.Term Symbol [h173, h173, h173, h177, h173, h173] h189 := .app e3451 e3458
private def e3460 : HOL.Term Symbol [h173, h173, h173, h177, h173, h173] h173 := .app e3459 e3456
private def e3461 : HOL.Term Symbol [h173, h173, h177, h173, h173] h189 := .lam e3460
private def e3462 : HOL.Term Symbol [h173, h173, h177, h173, h173] h173 := .app e3423 e3461
private def e3463 : HOL.Term Symbol [h173, h177, h173, h173] h189 := .lam e3462
private def e3464 : HOL.Term Symbol [h177, h173, h173] h192 := .lam e3463
private def e3465 : HOL.Term Symbol [h177, h173, h173] h180 := .const (.variable ⟨Name.mk [] "pointedCarrierProperty", t2⟩ q181)
private def e3466 : HOL.Term Symbol [h177, h173, h173] h177 := .var (HOL.Var.vz)
private def e3467 : HOL.Term Symbol [h177, h173, h173] h173 := .app e3465 e3466
private def e3468 : HOL.Term Symbol [h177, h173, h173] h189 := .app e3464 e3467
private def e3469 : HOL.Term Symbol [h177, h173, h173] h264 := .const (.constant Const.equality t63 q265)
private def e3470 : HOL.Term Symbol [h189, h180, h177, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3471 : HOL.Term Symbol [h189, h180, h177, h173, h173] h189 := .var (HOL.Var.vz)
private def e3472 : HOL.Term Symbol [h189, h180, h177, h173, h173] h195 := .app e3470 e3471
private def e3473 : HOL.Term Symbol [h173, h189, h180, h177, h173, h173] h198 := .const (.constant Const.equality t6 q199)
private def e3474 : HOL.Term Symbol [h173, h173, h189, h180, h177, h173, h173] h173 := .var (HOL.Var.vz)
private def e3475 : HOL.Term Symbol [h173, h189, h180, h177, h173, h173] h189 := .lam e3474
private def e3476 : HOL.Term Symbol [h173, h189, h180, h177, h173, h173] h195 := .app e3473 e3475
private def e3477 : HOL.Term Symbol [h173, h189, h180, h177, h173, h173] h173 := .app e3476 e3475
private def e3478 : HOL.Term Symbol [h189, h180, h177, h173, h173] h189 := .lam e3477
private def e3479 : HOL.Term Symbol [h189, h180, h177, h173, h173] h173 := .app e3472 e3478
private def e3480 : HOL.Term Symbol [h180, h177, h173, h173] h195 := .lam e3479
private def e3481 : HOL.Term Symbol [h173, h180, h177, h173, h173] h173 := .var (HOL.Var.vz)
private def e3482 : HOL.Term Symbol [h180, h177, h173, h173] h189 := .lam e3481
private def e3483 : HOL.Term Symbol [h180, h177, h173, h173] h173 := .app e3480 e3482
private def e3484 : HOL.Term Symbol [h177, h173, h173] h183 := .lam e3483
private def e3485 : HOL.Term Symbol [h177, h173, h173] h186 := .app e3469 e3484
private def e3486 : HOL.Term Symbol [h180, h177, h173, h173] h180 := .var (HOL.Var.vz)
private def e3487 : HOL.Term Symbol [h180, h177, h173, h173] h177 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3488 : HOL.Term Symbol [h180, h177, h173, h173] h173 := .app e3486 e3487
private def e3489 : HOL.Term Symbol [h177, h173, h173] h183 := .lam e3488
private def e3490 : HOL.Term Symbol [h177, h173, h173] h173 := .app e3485 e3489
private def e3491 : HOL.Term Symbol [h177, h173, h173] h173 := .app e3468 e3490
private def e3492 : HOL.Term Symbol [h173, h173] h180 := .lam e3491
private def e3493 : HOL.Term Symbol [h173, h173] h173 := .app e3412 e3492
private def e3494 : HOL.Term Symbol [h173, h173] h189 := .app e2464 e3493
private def e3495 : HOL.Term Symbol [h173, h173] h173 := .app e3494 e2195
private def e3496 : HOL.Term Symbol [h173, h173] h189 := .app e2464 e3495
private def e3497 : HOL.Term Symbol [h173, h173] h173 := .app e3496 e2195
private def e3498 : HOL.Term Symbol [h173, h173] h173 := .app e2505 e3497
private def e3499 : HOL.Term Symbol [h173] h189 := .lam e3498
private def e3500 : HOL.Term Symbol [h173] h173 := .app e2438 e3499
private def e3501 : HOL.Term Symbol [] h189 := .lam e3500
private def e3502 : HOL.Term Symbol [] h173 := .app e3332 e3501
private def c3503 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3502
private def f3504 : Theorem := Theorem.emptyResult ([].toFinset) c3503
private def r3505 : InferenceRequest := .mkComb f3504 f759
private def e3506 : HOL.Term Symbol [] h189 := .app e445 e3327
private def e3507 : HOL.Term Symbol [] h173 := .app e3501 e711
private def e3508 : HOL.Term Symbol [] h173 := .app e3506 e3507
private def c3509 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3508
private def f3510 : Theorem := Theorem.emptyResult ([].toFinset) c3509
private def s3511 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s3311
private def s3512 : SourceTerm := SourceTerm.app s3511 s1278
private def e3513 : HOL.Term Symbol [] h173 := .app e3501 e1309
private def c3514 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3513
private theorem n3515 : s3512.toDB [] = c3514.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3516 : CheckedSourceTerm := ⟨s3512, t1, by rw [← DBTerm.inferType_toDB [] s3512, n3515]; exact c3514.checked.trans (congrArg some v175)⟩
private def r3517 : InferenceRequest := .beta k3516
private def e3518 : HOL.Term Symbol [] h189 := .app e445 e3513
private def e3519 : HOL.Term Symbol [] h173 := .app e3518 e2602
private def c3520 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3519
private def f3521 : Theorem := Theorem.emptyResult ([].toFinset) c3520
private def r3522 : InferenceRequest := .inst [(k1407, s1278)] f3521
private def e3523 : HOL.Term Symbol [] h189 := .app e445 e3507
private def e3524 : HOL.Term Symbol [] h173 := .app e3523 e2602
private def c3525 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3524
private def f3526 : Theorem := Theorem.emptyResult ([].toFinset) c3525
private def r3527 : InferenceRequest := .trans f3510 f3526
private def e3528 : HOL.Term Symbol [] h173 := .app e3506 e2602
private def c3529 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3528
private def f3530 : Theorem := Theorem.emptyResult ([].toFinset) c3529
private def r3531 : InferenceRequest := .trans f3330 f3530
private def e3532 : HOL.Term Symbol [] h173 := .app e3301 e2602
private def c3533 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3532
private def f3534 : Theorem := Theorem.emptyResult ([].toFinset) c3533
private def r3535 : InferenceRequest := .mkComb f725 f3534
private def e3536 : HOL.Term Symbol [] h195 := .app e727 e3301
private def e3537 : HOL.Term Symbol [] h173 := .app e3536 e2611
private def c3538 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3537
private def f3539 : Theorem := Theorem.emptyResult ([].toFinset) c3538
private def c3540 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3300
private def r3541 : InferenceRequest := .refl c3540
private def e3542 : HOL.Term Symbol [] h173 := .app e3301 e3300
private def c3543 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3542
private def f3544 : Theorem := Theorem.emptyResult ([].toFinset) c3543
private def r3545 : InferenceRequest := .mkComb f3539 f3544
private def e3546 : HOL.Term Symbol [] h189 := .app e445 e3542
private def e3547 : HOL.Term Symbol [] h173 := .app e2611 e3300
private def e3548 : HOL.Term Symbol [] h173 := .app e3546 e3547
private def c3549 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3548
private def f3550 : Theorem := Theorem.emptyResult ([].toFinset) c3549
private def r3551 : InferenceRequest := .eqMp f3550 f3544
private def c3552 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3547
private def f3553 : Theorem := Theorem.emptyResult ([].toFinset) c3552
private def r3554 : InferenceRequest := .trans f3553 f3304
private def e3555 : HOL.Term Symbol [] h173 := .app e2611 e1817
private def c3556 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3555
private def f3557 : Theorem := Theorem.emptyResult ([c3279].toFinset) c3556
private def r3558 : InferenceRequest := .trans f3557 f2237
private def f3559 : Theorem := Theorem.emptyResult ([c3279].toFinset) c2641
private def r3560 : InferenceRequest := .mkComb f725 f3559
private def e3561 : HOL.Term Symbol [] h195 := .app e727 e2611
private def e3562 : HOL.Term Symbol [] h173 := .app e3561 e2204
private def c3563 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3562
private def f3564 : Theorem := Theorem.emptyResult ([c3279].toFinset) c3563
private def r3565 : InferenceRequest := .refl c2623
private def r3566 : InferenceRequest := .mkComb f3564 f2635
private def e3567 : HOL.Term Symbol [] h189 := .app e445 e2633
private def e3568 : HOL.Term Symbol [] h173 := .app e2204 e2602
private def e3569 : HOL.Term Symbol [] h173 := .app e3567 e3568
private def c3570 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3569
private def f3571 : Theorem := Theorem.emptyResult ([c3279].toFinset) c3570
private def r3572 : InferenceRequest := .eqMp f3571 f2635
private def c3573 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3568
private def f3574 : Theorem := Theorem.emptyResult ([c3279].toFinset) c3573
private def r3575 : InferenceRequest := .eqMp f3574 f777
private def f3576 : Theorem := Theorem.emptyResult ([c3279].toFinset) c2623
private def r3577 : InferenceRequest := .deductAntisym f3294 f3576
private def e3578 : HOL.Term Symbol [] h173 := .app e3165 e2602
private def c3579 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3578
private def f3580 : Theorem := Theorem.emptyResult ([].toFinset) c3579
private def r3581 : InferenceRequest := .inst [(k2924, s1278)] f2342
private def e3582 : HOL.Term Symbol [] h189 := .app e2308 e2602
private def e3583 : HOL.Term Symbol [] h195 := .app e727 e3582
private def e3584 : HOL.Term Symbol [h173] h189 := .app e2334 e3500
private def e3585 : HOL.Term Symbol [h173] h173 := .app e3584 e770
private def e3586 : HOL.Term Symbol [h173] h189 := .app e2315 e3585
private def e3587 : HOL.Term Symbol [h173] h173 := .app e3586 e3500
private def e3588 : HOL.Term Symbol [] h189 := .lam e3587
private def e3589 : HOL.Term Symbol [] h173 := .app e3583 e3588
private def c3590 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3589
private def f3591 : Theorem := Theorem.emptyResult ([].toFinset) c3590
private def r3592 : InferenceRequest := .mkComb f3591 f759
private def e3593 : HOL.Term Symbol [] h173 := .app e3582 e711
private def e3594 : HOL.Term Symbol [] h189 := .app e445 e3593
private def e3595 : HOL.Term Symbol [] h173 := .app e3588 e711
private def e3596 : HOL.Term Symbol [] h173 := .app e3594 e3595
private def c3597 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3596
private def f3598 : Theorem := Theorem.emptyResult ([].toFinset) c3597
private def s3599 : SourceTerm := SourceTerm.app s2371 s3311
private def s3600 : SourceTerm := SourceTerm.app s3599 s1278
private def s3601 : SourceTerm := SourceTerm.app s18 s3600
private def s3602 : SourceTerm := SourceTerm.app s3601 s3311
private def s3603 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s3602
private def s3604 : SourceTerm := SourceTerm.app s3603 s1278
private def e3605 : HOL.Term Symbol [] h173 := .app e3588 e1309
private def c3606 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3605
private theorem n3607 : s3604.toDB [] = c3606.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3608 : CheckedSourceTerm := ⟨s3604, t1, by rw [← DBTerm.inferType_toDB [] s3604, n3607]; exact c3606.checked.trans (congrArg some v175)⟩
private def r3609 : InferenceRequest := .beta k3608
private def e3610 : HOL.Term Symbol [] h189 := .app e445 e3605
private def e3611 : HOL.Term Symbol [] h173 := .app e2926 e1309
private def e3612 : HOL.Term Symbol [] h189 := .app e445 e3611
private def e3613 : HOL.Term Symbol [] h173 := .app e3612 e2602
private def e3614 : HOL.Term Symbol [] h173 := .app e3610 e3613
private def c3615 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3614
private def f3616 : Theorem := Theorem.emptyResult ([].toFinset) c3615
private def r3617 : InferenceRequest := .inst [(k1407, s1278)] f3616
private def e3618 : HOL.Term Symbol [] h189 := .app e445 e3595
private def e3619 : HOL.Term Symbol [] h173 := .app e3618 e3578
private def c3620 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3619
private def f3621 : Theorem := Theorem.emptyResult ([].toFinset) c3620
private def r3622 : InferenceRequest := .trans f3598 f3621
private def e3623 : HOL.Term Symbol [] h173 := .app e3594 e3578
private def c3624 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3623
private def f3625 : Theorem := Theorem.emptyResult ([].toFinset) c3624
private def r3626 : InferenceRequest := .mkComb f725 f3625
private def e3627 : HOL.Term Symbol [] h195 := .app e727 e3594
private def e3628 : HOL.Term Symbol [] h189 := .app e445 e3578
private def e3629 : HOL.Term Symbol [] h173 := .app e3627 e3628
private def c3630 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3629
private def f3631 : Theorem := Theorem.emptyResult ([].toFinset) c3630
private def c3632 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3593
private def r3633 : InferenceRequest := .refl c3632
private def e3634 : HOL.Term Symbol [] h173 := .app e3594 e3593
private def c3635 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3634
private def f3636 : Theorem := Theorem.emptyResult ([].toFinset) c3635
private def r3637 : InferenceRequest := .mkComb f3631 f3636
private def e3638 : HOL.Term Symbol [] h189 := .app e445 e3634
private def e3639 : HOL.Term Symbol [] h173 := .app e3628 e3593
private def e3640 : HOL.Term Symbol [] h173 := .app e3638 e3639
private def c3641 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3640
private def f3642 : Theorem := Theorem.emptyResult ([].toFinset) c3641
private def r3643 : InferenceRequest := .eqMp f3642 f3636
private def c3644 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3639
private def f3645 : Theorem := Theorem.emptyResult ([].toFinset) c3644
private def r3646 : InferenceRequest := .eqMp f3645 f3580
private def f3647 : Theorem := Theorem.emptyResult ([].toFinset) c3632
private def e3648 : HOL.Term Symbol [] h189 := .app e2308 e689
private def e3649 : HOL.Term Symbol [] h173 := .app e3648 e1309
private def c3650 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3649
private def r3651 : InferenceRequest := .assume c3650
private def f3652 : Theorem := Theorem.emptyResult ([c3650].toFinset) c3650
private def e3653 : HOL.Term Symbol [] h189 := .app e2308 e710
private def e3654 : HOL.Term Symbol [] h173 := .app e3653 e1309
private def c3655 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3654
private def r3656 : InferenceRequest := .assume c3655
private def f3657 : Theorem := Theorem.emptyResult ([c3655].toFinset) c3655
private def r3658 : InferenceRequest := .deductAntisym f3657 f3652
private def e3659 : HOL.Term Symbol [] h189 := .app e445 e3654
private def e3660 : HOL.Term Symbol [] h173 := .app e3659 e3649
private def c3661 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3660
private def f3662 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3661
private def r3663 : InferenceRequest := .eqMp f3662 f3657
private def f3664 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3650
private def r3665 : InferenceRequest := .deductAntisym f3652 f3664
private def e3666 : HOL.Term Symbol [] h189 := .app e445 e3649
private def e3667 : HOL.Term Symbol [] h173 := .app e3666 e3649
private def c3668 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3667
private def f3669 : Theorem := Theorem.emptyResult ([c3655].toFinset) c3668
private def r3670 : InferenceRequest := .eqMp f3669 f3652
private def r3671 : InferenceRequest := .refl c682
private def f3672 : Theorem := Theorem.emptyResult ([].toFinset) c2480
private def r3673 : InferenceRequest := .deductAntisym f3657 f3672
private def e3674 : HOL.Term Symbol [] h173 := .app e3659 e689
private def c3675 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3674
private def f3676 : Theorem := Theorem.emptyResult ([c3655].toFinset) c3675
private def r3677 : InferenceRequest := .eqMp f3676 f3657
private def f3678 : Theorem := Theorem.emptyResult ([c3655].toFinset) c2480
private def r3679 : InferenceRequest := .deductAntisym f3652 f3678
private def e3680 : HOL.Term Symbol [] h173 := .app e3666 e689
private def c3681 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3680
private def f3682 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3681
private def r3683 : InferenceRequest := .eqMp f3682 f3652
private def f3684 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c2480
private def r3685 : InferenceRequest := .inst [(k2482, s1278)] f2342
private def e3686 : HOL.Term Symbol [] h195 := .app e727 e3648
private def e3687 : HOL.Term Symbol [h173] h189 := .app e2334 e1948
private def e3688 : HOL.Term Symbol [h173] h173 := .app e3687 e770
private def e3689 : HOL.Term Symbol [h173] h189 := .app e2315 e3688
private def e3690 : HOL.Term Symbol [h173] h173 := .app e3689 e1948
private def e3691 : HOL.Term Symbol [] h189 := .lam e3690
private def e3692 : HOL.Term Symbol [] h173 := .app e3686 e3691
private def c3693 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3692
private def f3694 : Theorem := Theorem.emptyResult ([].toFinset) c3693
private def c3695 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e1309
private def r3696 : InferenceRequest := .refl c3695
private def e3697 : HOL.Term Symbol [] h189 := .app e445 e1309
private def e3698 : HOL.Term Symbol [] h173 := .app e3697 e1309
private def c3699 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3698
private def f3700 : Theorem := Theorem.emptyResult ([].toFinset) c3699
private def r3701 : InferenceRequest := .mkComb f3694 f3700
private def e3702 : HOL.Term Symbol [] h173 := .app e3691 e1309
private def e3703 : HOL.Term Symbol [] h173 := .app e3666 e3702
private def c3704 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3703
private def f3705 : Theorem := Theorem.emptyResult ([].toFinset) c3704
private def s3706 : SourceTerm := SourceTerm.app s2371 s1822
private def s3707 : SourceTerm := SourceTerm.app s3706 s1278
private def s3708 : SourceTerm := SourceTerm.app s18 s3707
private def s3709 : SourceTerm := SourceTerm.app s3708 s1822
private def s3710 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s3709
private def s3711 : SourceTerm := SourceTerm.app s3710 s1278
private def c3712 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3702
private theorem n3713 : s3711.toDB [] = c3712.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3714 : CheckedSourceTerm := ⟨s3711, t1, by rw [← DBTerm.inferType_toDB [] s3711, n3713]; exact c3712.checked.trans (congrArg some v175)⟩
private def r3715 : InferenceRequest := .beta k3714
private def e3716 : HOL.Term Symbol [] h189 := .app e445 e3702
private def e3717 : HOL.Term Symbol [] h189 := .app e1308 e689
private def e3718 : HOL.Term Symbol [] h173 := .app e3717 e1309
private def e3719 : HOL.Term Symbol [] h189 := .app e445 e3718
private def e3720 : HOL.Term Symbol [] h173 := .app e3719 e689
private def e3721 : HOL.Term Symbol [] h173 := .app e3716 e3720
private def c3722 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3721
private def f3723 : Theorem := Theorem.emptyResult ([].toFinset) c3722
private theorem n3724 : s1278.toDB [] = c3695.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3725 : CheckedSourceTerm := ⟨s1278, t1, by rw [← DBTerm.inferType_toDB [] s1278, n3724]; exact c3695.checked.trans (congrArg some v175)⟩
private def r3726 : InferenceRequest := .inst [(k3725, s1278)] f3723
private def r3727 : InferenceRequest := .trans f3705 f3723
private def e3728 : HOL.Term Symbol [] h173 := .app e3666 e3720
private def c3729 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3728
private def f3730 : Theorem := Theorem.emptyResult ([].toFinset) c3729
private def r3731 : InferenceRequest := .eqMp f3730 f3664
private def c3732 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3720
private def f3733 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3732
private def r3734 : InferenceRequest := .mkComb f725 f3733
private def e3735 : HOL.Term Symbol [] h195 := .app e727 e3719
private def e3736 : HOL.Term Symbol [] h189 := .app e445 e689
private def e3737 : HOL.Term Symbol [] h173 := .app e3735 e3736
private def c3738 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3737
private def f3739 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3738
private def c3740 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3718
private def r3741 : InferenceRequest := .refl c3740
private def e3742 : HOL.Term Symbol [] h173 := .app e3719 e3718
private def c3743 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3742
private def f3744 : Theorem := Theorem.emptyResult ([].toFinset) c3743
private def r3745 : InferenceRequest := .mkComb f3739 f3744
private def e3746 : HOL.Term Symbol [] h189 := .app e445 e3742
private def e3747 : HOL.Term Symbol [] h173 := .app e3736 e3718
private def e3748 : HOL.Term Symbol [] h173 := .app e3746 e3747
private def c3749 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3748
private def f3750 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3749
private def r3751 : InferenceRequest := .eqMp f3750 f3744
private def c3752 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3747
private def f3753 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3752
private def r3754 : InferenceRequest := .eqMp f3753 f3684
private def f3755 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3740
private def r3756 : InferenceRequest := .inst [(k2482, s1278)] f1336
private def e3757 : HOL.Term Symbol [] h195 := .app e727 e3717
private def e3758 : HOL.Term Symbol [h192, h173] h189 := .app e1317 e1482
private def e3759 : HOL.Term Symbol [h192, h173] h173 := .app e3758 e1320
private def e3760 : HOL.Term Symbol [h173] h213 := .lam e3759
private def e3761 : HOL.Term Symbol [h173] h216 := .app e1316 e3760
private def e3762 : HOL.Term Symbol [h173] h173 := .app e3761 e1331
private def e3763 : HOL.Term Symbol [] h189 := .lam e3762
private def e3764 : HOL.Term Symbol [] h173 := .app e3757 e3763
private def c3765 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3764
private def f3766 : Theorem := Theorem.emptyResult ([].toFinset) c3765
private def r3767 : InferenceRequest := .mkComb f3766 f3700
private def e3768 : HOL.Term Symbol [] h173 := .app e3763 e1309
private def e3769 : HOL.Term Symbol [] h173 := .app e3719 e3768
private def c3770 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3769
private def f3771 : Theorem := Theorem.emptyResult ([].toFinset) c3770
private def s3772 : SourceTerm := SourceTerm.app s1662 s1675
private def s3773 : SourceTerm := SourceTerm.app s3772 s1278
private def s3774 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t17 s3773
private def s3775 : SourceTerm := SourceTerm.app s22 s3774
private def s3776 : SourceTerm := SourceTerm.app s3775 s1749
private def s3777 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s3776
private def s3778 : SourceTerm := SourceTerm.app s3777 s1278
private def c3779 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3768
private theorem n3780 : s3778.toDB [] = c3779.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3781 : CheckedSourceTerm := ⟨s3778, t1, by rw [← DBTerm.inferType_toDB [] s3778, n3780]; exact c3779.checked.trans (congrArg some v175)⟩
private def r3782 : InferenceRequest := .beta k3781
private def e3783 : HOL.Term Symbol [] h189 := .app e445 e3768
private def e3784 : HOL.Term Symbol [h192] h189 := .app e802 e874
private def e3785 : HOL.Term Symbol [h192] h173 := .app e3784 e1759
private def e3786 : HOL.Term Symbol [] h213 := .lam e3785
private def e3787 : HOL.Term Symbol [] h216 := .app e801 e3786
private def e3788 : HOL.Term Symbol [] h173 := .app e3787 e1273
private def e3789 : HOL.Term Symbol [] h173 := .app e3783 e3788
private def c3790 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3789
private def f3791 : Theorem := Theorem.emptyResult ([].toFinset) c3790
private def r3792 : InferenceRequest := .inst [(k3725, s1278)] f3791
private def r3793 : InferenceRequest := .trans f3771 f3791
private def e3794 : HOL.Term Symbol [] h173 := .app e3719 e3788
private def c3795 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3794
private def f3796 : Theorem := Theorem.emptyResult ([].toFinset) c3795
private def r3797 : InferenceRequest := .eqMp f3796 f3755
private def c3798 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3788
private def f3799 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3798
private def e3800 : HOL.Term Symbol [] h192 := .lam e2196
private def c3801 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3800
private def r3802 : InferenceRequest := .refl c3801
private def e3803 : HOL.Term Symbol [] h213 := .app e721 e3800
private def e3804 : HOL.Term Symbol [] h173 := .app e3803 e3800
private def c3805 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3804
private def f3806 : Theorem := Theorem.emptyResult ([].toFinset) c3805
private def r3807 : InferenceRequest := .mkComb f3799 f3806
private def e3808 : HOL.Term Symbol [] h173 := .app e3786 e3800
private def e3809 : HOL.Term Symbol [] h189 := .app e445 e3808
private def e3810 : HOL.Term Symbol [] h173 := .app e1273 e3800
private def e3811 : HOL.Term Symbol [] h173 := .app e3809 e3810
private def c3812 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3811
private def f3813 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3812
private def s3814 : SourceTerm := SourceTerm.app s3774 s1662
private def e3815 : HOL.Term Symbol [] h192 := .const (.variable ⟨Name.mk ["", ""] "x", t17⟩ q193)
private def e3816 : HOL.Term Symbol [] h173 := .app e3786 e3815
private def c3817 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3816
private theorem n3818 : s3814.toDB [] = c3817.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3819 : CheckedSourceTerm := ⟨s3814, t1, by rw [← DBTerm.inferType_toDB [] s3814, n3818]; exact c3817.checked.trans (congrArg some v175)⟩
private def r3820 : InferenceRequest := .beta k3819
private def e3821 : HOL.Term Symbol [] h189 := .app e445 e3816
private def e3822 : HOL.Term Symbol [] h189 := .app e3815 e689
private def e3823 : HOL.Term Symbol [] h173 := .app e3822 e1309
private def e3824 : HOL.Term Symbol [] h173 := .app e3821 e3823
private def c3825 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3824
private def f3826 : Theorem := Theorem.emptyResult ([].toFinset) c3825
private def s3827 : SourceTerm := SourceTerm.abs (Name.mk [""] "x") t1 s679
private theorem n3828 : s3827.toDB [] = c3801.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3829 : CheckedSourceTerm := ⟨s3827, t17, by rw [← DBTerm.inferType_toDB [] s3827, n3828]; exact c3801.checked.trans (congrArg some v194)⟩
private def r3830 : InferenceRequest := .inst [(k3829, s1662)] f3826
private def e3831 : HOL.Term Symbol [] h189 := .app e3800 e689
private def e3832 : HOL.Term Symbol [] h173 := .app e3831 e1309
private def e3833 : HOL.Term Symbol [] h173 := .app e3809 e3832
private def c3834 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3833
private def f3835 : Theorem := Theorem.emptyResult ([].toFinset) c3834
private def s3836 : SourceTerm := SourceTerm.app s3827 s1278
private def e3837 : HOL.Term Symbol [] h189 := .app e3800 e1309
private def c3838 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3837
private theorem n3839 : s3836.toDB [] = c3838.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3840 : CheckedSourceTerm := ⟨s3836, t4, by rw [← DBTerm.inferType_toDB [] s3836, n3839]; exact c3838.checked.trans (congrArg some v191)⟩
private def r3841 : InferenceRequest := .beta k3840
private def e3842 : HOL.Term Symbol [] h195 := .app e727 e3837
private def e3843 : HOL.Term Symbol [] h173 := .app e3842 e771
private def c3844 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3843
private def f3845 : Theorem := Theorem.emptyResult ([].toFinset) c3844
private def r3846 : InferenceRequest := .inst [(k2482, s1278)] f3845
private def e3847 : HOL.Term Symbol [] h195 := .app e727 e3831
private def e3848 : HOL.Term Symbol [] h173 := .app e3847 e771
private def c3849 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3848
private def f3850 : Theorem := Theorem.emptyResult ([].toFinset) c3849
private def r3851 : InferenceRequest := .mkComb f3850 f3700
private def e3852 : HOL.Term Symbol [] h189 := .app e445 e3832
private def e3853 : HOL.Term Symbol [] h173 := .app e771 e1309
private def e3854 : HOL.Term Symbol [] h173 := .app e3852 e3853
private def c3855 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3854
private def f3856 : Theorem := Theorem.emptyResult ([].toFinset) c3855
private def s3857 : SourceTerm := SourceTerm.app s2187 s1278
private def c3858 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3853
private theorem n3859 : s3857.toDB [] = c3858.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k3860 : CheckedSourceTerm := ⟨s3857, t1, by rw [← DBTerm.inferType_toDB [] s3857, n3859]; exact c3858.checked.trans (congrArg some v175)⟩
private def r3861 : InferenceRequest := .beta k3860
private def e3862 : HOL.Term Symbol [] h189 := .app e445 e3853
private def e3863 : HOL.Term Symbol [] h173 := .app e3862 e1309
private def c3864 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3863
private def f3865 : Theorem := Theorem.emptyResult ([].toFinset) c3864
private def r3866 : InferenceRequest := .inst [(k3725, s1278)] f3865
private def r3867 : InferenceRequest := .trans f3856 f3865
private def e3868 : HOL.Term Symbol [] h173 := .app e3852 e1309
private def c3869 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3868
private def f3870 : Theorem := Theorem.emptyResult ([].toFinset) c3869
private def r3871 : InferenceRequest := .trans f3835 f3870
private def e3872 : HOL.Term Symbol [] h173 := .app e3809 e1309
private def c3873 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3872
private def f3874 : Theorem := Theorem.emptyResult ([].toFinset) c3873
private def r3875 : InferenceRequest := .mkComb f725 f3874
private def e3876 : HOL.Term Symbol [] h195 := .app e727 e3809
private def e3877 : HOL.Term Symbol [] h173 := .app e3876 e3697
private def c3878 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3877
private def f3879 : Theorem := Theorem.emptyResult ([].toFinset) c3878
private def c3880 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3808
private def r3881 : InferenceRequest := .refl c3880
private def e3882 : HOL.Term Symbol [] h173 := .app e3809 e3808
private def c3883 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3882
private def f3884 : Theorem := Theorem.emptyResult ([].toFinset) c3883
private def r3885 : InferenceRequest := .mkComb f3879 f3884
private def e3886 : HOL.Term Symbol [] h189 := .app e445 e3882
private def e3887 : HOL.Term Symbol [] h173 := .app e3697 e3808
private def e3888 : HOL.Term Symbol [] h173 := .app e3886 e3887
private def c3889 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3888
private def f3890 : Theorem := Theorem.emptyResult ([].toFinset) c3889
private def r3891 : InferenceRequest := .eqMp f3890 f3884
private def c3892 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3887
private def f3893 : Theorem := Theorem.emptyResult ([].toFinset) c3892
private def r3894 : InferenceRequest := .inst [(k3829, s1821)] f2179
private def e3895 : HOL.Term Symbol [] h189 := .app e445 e3810
private def e3896 : HOL.Term Symbol [] h189 := .app e3800 e775
private def e3897 : HOL.Term Symbol [] h173 := .app e3896 e775
private def e3898 : HOL.Term Symbol [] h173 := .app e3895 e3897
private def c3899 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3898
private def f3900 : Theorem := Theorem.emptyResult ([].toFinset) c3899
private def r3901 : InferenceRequest := .inst [(k2191, s1278)] f3845
private def e3902 : HOL.Term Symbol [] h195 := .app e727 e3896
private def e3903 : HOL.Term Symbol [] h173 := .app e3902 e771
private def c3904 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3903
private def f3905 : Theorem := Theorem.emptyResult ([].toFinset) c3904
private def r3906 : InferenceRequest := .mkComb f3905 f2207
private def e3907 : HOL.Term Symbol [] h189 := .app e445 e3897
private def e3908 : HOL.Term Symbol [] h173 := .app e771 e775
private def e3909 : HOL.Term Symbol [] h173 := .app e3907 e3908
private def c3910 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3909
private def f3911 : Theorem := Theorem.emptyResult ([].toFinset) c3910
private def r3912 : InferenceRequest := .inst [(k2191, s1278)] f3865
private def e3913 : HOL.Term Symbol [] h189 := .app e445 e3908
private def e3914 : HOL.Term Symbol [] h173 := .app e3913 e775
private def c3915 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3914
private def f3916 : Theorem := Theorem.emptyResult ([].toFinset) c3915
private def r3917 : InferenceRequest := .trans f3911 f3916
private def e3918 : HOL.Term Symbol [] h173 := .app e3907 e775
private def c3919 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3918
private def f3920 : Theorem := Theorem.emptyResult ([].toFinset) c3919
private def r3921 : InferenceRequest := .trans f3900 f3920
private def e3922 : HOL.Term Symbol [] h173 := .app e3895 e775
private def c3923 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3922
private def f3924 : Theorem := Theorem.emptyResult ([].toFinset) c3923
private def r3925 : InferenceRequest := .trans f3893 f3813
private def e3926 : HOL.Term Symbol [] h173 := .app e3697 e3810
private def c3927 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3926
private def f3928 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3927
private def r3929 : InferenceRequest := .trans f3928 f3924
private def e3930 : HOL.Term Symbol [] h173 := .app e3697 e775
private def c3931 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3930
private def f3932 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3931
private def r3933 : InferenceRequest := .mkComb f725 f3932
private def e3934 : HOL.Term Symbol [] h195 := .app e727 e3697
private def e3935 : HOL.Term Symbol [] h173 := .app e3934 e2204
private def c3936 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3935
private def f3937 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3936
private def r3938 : InferenceRequest := .mkComb f3937 f3700
private def e3939 : HOL.Term Symbol [] h189 := .app e445 e3698
private def e3940 : HOL.Term Symbol [] h173 := .app e2204 e1309
private def e3941 : HOL.Term Symbol [] h173 := .app e3939 e3940
private def c3942 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3941
private def f3943 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3942
private def r3944 : InferenceRequest := .eqMp f3943 f3700
private def c3945 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3940
private def f3946 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3945
private def r3947 : InferenceRequest := .eqMp f3946 f777
private def f3948 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3695
private def r3949 : InferenceRequest := .deductAntisym f3657 f3948
private def e3950 : HOL.Term Symbol [] h173 := .app e3659 e1309
private def c3951 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3950
private def f3952 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3951
private def r3953 : InferenceRequest := .eqMp f3952 f3657
private def r3954 : InferenceRequest := .deductAntisym f3652 f3948
private def e3955 : HOL.Term Symbol [] h173 := .app e3666 e1309
private def c3956 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3955
private def f3957 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3956
private def r3958 : InferenceRequest := .eqMp f3957 f3652
private def c3959 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3815
private def r3960 : InferenceRequest := .refl c3959
private def e3961 : HOL.Term Symbol [] h213 := .app e721 e3815
private def e3962 : HOL.Term Symbol [] h173 := .app e3961 e3815
private def c3963 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3962
private def f3964 : Theorem := Theorem.emptyResult ([].toFinset) c3963
private def r3965 : InferenceRequest := .deductAntisym f3657 f777
private def e3966 : HOL.Term Symbol [] h173 := .app e3659 e775
private def c3967 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3966
private def f3968 : Theorem := Theorem.emptyResult ([c3655].toFinset) c3967
private def r3969 : InferenceRequest := .deductAntisym f3948 f777
private def r3970 : InferenceRequest := .mkComb f3964 f3968
private def e3971 : HOL.Term Symbol [] h189 := .app e3815 e3654
private def e3972 : HOL.Term Symbol [] h195 := .app e727 e3971
private def e3973 : HOL.Term Symbol [] h189 := .app e3815 e775
private def e3974 : HOL.Term Symbol [] h173 := .app e3972 e3973
private def c3975 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3974
private def f3976 : Theorem := Theorem.emptyResult ([c3655].toFinset) c3975
private def r3977 : InferenceRequest := .mkComb f3976 f3932
private def e3978 : HOL.Term Symbol [] h173 := .app e3971 e1309
private def e3979 : HOL.Term Symbol [] h189 := .app e445 e3978
private def e3980 : HOL.Term Symbol [] h173 := .app e3973 e775
private def e3981 : HOL.Term Symbol [] h173 := .app e3979 e3980
private def c3982 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e3981
private def f3983 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c3982
private def r3984 : InferenceRequest := .abs ⟨Name.mk ["", ""] "x", t17⟩ f3983
private def e3985 : HOL.Term Symbol [h173, h173, h192] h192 := .const (.constant Const.equality t17 q193)
private def e3986 : HOL.Term Symbol [h173, h173, h173, h173, h192] h219 := .const (.constant Const.equality t21 q220)
private def e3987 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192] h192 := .var (HOL.Var.vz)
private def e3988 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e3989 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192] h189 := .app e3987 e3988
private def e3990 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e3991 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192] h173 := .app e3989 e3990
private def e3992 : HOL.Term Symbol [h173, h173, h173, h173, h192] h213 := .lam e3991
private def e3993 : HOL.Term Symbol [h173, h173, h173, h173, h192] h216 := .app e3986 e3992
private def e3994 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192] h198 := .const (.constant Const.equality t6 q199)
private def e3995 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h192] h173 := .var (HOL.Var.vz)
private def e3996 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192] h189 := .lam e3995
private def e3997 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192] h195 := .app e3994 e3996
private def e3998 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192] h173 := .app e3997 e3996
private def e3999 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192] h189 := .app e3987 e3998
private def e4000 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192] h173 := .app e3999 e3998
private def e4001 : HOL.Term Symbol [h173, h173, h173, h173, h192] h213 := .lam e4000
private def e4002 : HOL.Term Symbol [h173, h173, h173, h173, h192] h173 := .app e3993 e4001
private def e4003 : HOL.Term Symbol [h173, h173, h173, h192] h189 := .lam e4002
private def e4004 : HOL.Term Symbol [h173, h173, h192] h192 := .lam e4003
private def e4005 : HOL.Term Symbol [h173, h173, h192] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e4006 : HOL.Term Symbol [h173, h173, h192] h189 := .app e4004 e4005
private def e4007 : HOL.Term Symbol [h173, h173, h192] h173 := .var (HOL.Var.vz)
private def e4008 : HOL.Term Symbol [h173, h173, h192] h173 := .app e4006 e4007
private def e4009 : HOL.Term Symbol [h173, h173, h192] h189 := .app e3985 e4008
private def e4010 : HOL.Term Symbol [h173, h173, h192] h173 := .app e4009 e4005
private def e4011 : HOL.Term Symbol [h173, h192] h189 := .lam e4010
private def e4012 : HOL.Term Symbol [h192] h192 := .lam e4011
private def e4013 : HOL.Term Symbol [h192] h189 := .app e4012 e1036
private def e4014 : HOL.Term Symbol [h192] h173 := .app e4013 e1759
private def e4015 : HOL.Term Symbol [h192] h189 := .app e802 e4014
private def e4016 : HOL.Term Symbol [h192] h173 := .app e4015 e1759
private def e4017 : HOL.Term Symbol [] h213 := .lam e4016
private def e4018 : HOL.Term Symbol [] h216 := .app e801 e4017
private def e4019 : HOL.Term Symbol [] h173 := .app e4018 e1273
private def c4020 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4019
private def f4021 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c4020
private def s4022 : SourceTerm := SourceTerm.app s2281 s1404
private def s4023 : SourceTerm := SourceTerm.app s4022 s1278
private theorem n4024 : s4023.toDB [] = c3655.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4025 : CheckedSourceTerm := ⟨s4023, t1, by rw [← DBTerm.inferType_toDB [] s4023, n4024]; exact c3655.checked.trans (congrArg some v175)⟩
private def r4026 : InferenceRequest := .inst [(k4025, s1278)] f1336
private def e4027 : HOL.Term Symbol [] h189 := .app e1308 e3654
private def e4028 : HOL.Term Symbol [] h195 := .app e727 e4027
private def e4029 : HOL.Term Symbol [h173, h173, h192, h173] h192 := .const (.constant Const.equality t17 q193)
private def e4030 : HOL.Term Symbol [h173, h173, h173, h173, h192, h173] h219 := .const (.constant Const.equality t21 q220)
private def e4031 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192, h173] h192 := .var (HOL.Var.vz)
private def e4032 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vs (HOL.Var.vz)))
private def e4033 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192, h173] h189 := .app e4031 e4032
private def e4034 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e4035 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192, h173] h173 := .app e4033 e4034
private def e4036 : HOL.Term Symbol [h173, h173, h173, h173, h192, h173] h213 := .lam e4035
private def e4037 : HOL.Term Symbol [h173, h173, h173, h173, h192, h173] h216 := .app e4030 e4036
private def e4038 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192, h173] h198 := .const (.constant Const.equality t6 q199)
private def e4039 : HOL.Term Symbol [h173, h192, h173, h173, h173, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e4040 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192, h173] h189 := .lam e4039
private def e4041 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192, h173] h195 := .app e4038 e4040
private def e4042 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192, h173] h173 := .app e4041 e4040
private def e4043 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192, h173] h189 := .app e4031 e4042
private def e4044 : HOL.Term Symbol [h192, h173, h173, h173, h173, h192, h173] h173 := .app e4043 e4042
private def e4045 : HOL.Term Symbol [h173, h173, h173, h173, h192, h173] h213 := .lam e4044
private def e4046 : HOL.Term Symbol [h173, h173, h173, h173, h192, h173] h173 := .app e4037 e4045
private def e4047 : HOL.Term Symbol [h173, h173, h173, h192, h173] h189 := .lam e4046
private def e4048 : HOL.Term Symbol [h173, h173, h192, h173] h192 := .lam e4047
private def e4049 : HOL.Term Symbol [h173, h173, h192, h173] h173 := .var (HOL.Var.vs (HOL.Var.vz))
private def e4050 : HOL.Term Symbol [h173, h173, h192, h173] h189 := .app e4048 e4049
private def e4051 : HOL.Term Symbol [h173, h173, h192, h173] h173 := .var (HOL.Var.vz)
private def e4052 : HOL.Term Symbol [h173, h173, h192, h173] h173 := .app e4050 e4051
private def e4053 : HOL.Term Symbol [h173, h173, h192, h173] h189 := .app e4029 e4052
private def e4054 : HOL.Term Symbol [h173, h173, h192, h173] h173 := .app e4053 e4049
private def e4055 : HOL.Term Symbol [h173, h192, h173] h189 := .lam e4054
private def e4056 : HOL.Term Symbol [h192, h173] h192 := .lam e4055
private def e4057 : HOL.Term Symbol [h192, h173] h189 := .app e4056 e1644
private def e4058 : HOL.Term Symbol [h192, h173] h173 := .app e4057 e1318
private def e4059 : HOL.Term Symbol [h192, h173] h189 := .app e1317 e4058
private def e4060 : HOL.Term Symbol [h192, h173] h173 := .app e4059 e1320
private def e4061 : HOL.Term Symbol [h173] h213 := .lam e4060
private def e4062 : HOL.Term Symbol [h173] h216 := .app e1316 e4061
private def e4063 : HOL.Term Symbol [h173] h173 := .app e4062 e1331
private def e4064 : HOL.Term Symbol [] h189 := .lam e4063
private def e4065 : HOL.Term Symbol [] h173 := .app e4028 e4064
private def c4066 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4065
private def f4067 : Theorem := Theorem.emptyResult ([].toFinset) c4066
private def r4068 : InferenceRequest := .mkComb f4067 f3700
private def e4069 : HOL.Term Symbol [] h173 := .app e4027 e1309
private def e4070 : HOL.Term Symbol [] h189 := .app e445 e4069
private def e4071 : HOL.Term Symbol [] h173 := .app e4064 e1309
private def e4072 : HOL.Term Symbol [] h173 := .app e4070 e4071
private def c4073 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4072
private def f4074 : Theorem := Theorem.emptyResult ([].toFinset) c4073
private def s4075 : SourceTerm := SourceTerm.app s3237 s1278
private def s4076 : SourceTerm := SourceTerm.app s1277 s4075
private def s4077 : SourceTerm := SourceTerm.app s4076 s47
private def s4078 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t17 s4077
private def s4079 : SourceTerm := SourceTerm.app s22 s4078
private def s4080 : SourceTerm := SourceTerm.app s4079 s1285
private def s4081 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s4080
private def s4082 : SourceTerm := SourceTerm.app s4081 s47
private def e4083 : HOL.Term Symbol [] h173 := .const (.variable ⟨Name.mk ["", ""] "x", t1⟩ q174)
private def e4084 : HOL.Term Symbol [] h173 := .app e4064 e4083
private def c4085 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4084
private theorem n4086 : s4082.toDB [] = c4085.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4087 : CheckedSourceTerm := ⟨s4082, t1, by rw [← DBTerm.inferType_toDB [] s4082, n4086]; exact c4085.checked.trans (congrArg some v175)⟩
private def r4088 : InferenceRequest := .beta k4087
private def e4089 : HOL.Term Symbol [] h189 := .app e445 e4084
private def e4090 : HOL.Term Symbol [h192] h173 := .const (.variable ⟨Name.mk ["", ""] "x", t1⟩ q174)
private def e4091 : HOL.Term Symbol [h192] h173 := .app e4015 e4090
private def e4092 : HOL.Term Symbol [] h213 := .lam e4091
private def e4093 : HOL.Term Symbol [] h216 := .app e801 e4092
private def e4094 : HOL.Term Symbol [] h173 := .app e4093 e1273
private def e4095 : HOL.Term Symbol [] h173 := .app e4089 e4094
private def c4096 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4095
private def f4097 : Theorem := Theorem.emptyResult ([].toFinset) c4096
private def r4098 : InferenceRequest := .inst [(k3725, s47)] f4097
private def e4099 : HOL.Term Symbol [] h189 := .app e445 e4071
private def e4100 : HOL.Term Symbol [] h173 := .app e4099 e4019
private def c4101 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4100
private def f4102 : Theorem := Theorem.emptyResult ([].toFinset) c4101
private def r4103 : InferenceRequest := .trans f4074 f4102
private def e4104 : HOL.Term Symbol [] h173 := .app e4070 e4019
private def c4105 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4104
private def f4106 : Theorem := Theorem.emptyResult ([].toFinset) c4105
private def r4107 : InferenceRequest := .mkComb f725 f4106
private def e4108 : HOL.Term Symbol [] h195 := .app e727 e4070
private def e4109 : HOL.Term Symbol [] h189 := .app e445 e4019
private def e4110 : HOL.Term Symbol [] h173 := .app e4108 e4109
private def c4111 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4110
private def f4112 : Theorem := Theorem.emptyResult ([].toFinset) c4111
private def c4113 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4069
private def r4114 : InferenceRequest := .refl c4113
private def e4115 : HOL.Term Symbol [] h173 := .app e4070 e4069
private def c4116 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4115
private def f4117 : Theorem := Theorem.emptyResult ([].toFinset) c4116
private def r4118 : InferenceRequest := .mkComb f4112 f4117
private def e4119 : HOL.Term Symbol [] h189 := .app e445 e4115
private def e4120 : HOL.Term Symbol [] h173 := .app e4109 e4069
private def e4121 : HOL.Term Symbol [] h173 := .app e4119 e4120
private def c4122 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4121
private def f4123 : Theorem := Theorem.emptyResult ([].toFinset) c4122
private def r4124 : InferenceRequest := .eqMp f4123 f4117
private def c4125 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4120
private def f4126 : Theorem := Theorem.emptyResult ([].toFinset) c4125
private def r4127 : InferenceRequest := .eqMp f4126 f4021
private def f4128 : Theorem := Theorem.emptyResult ([c3650, c3655].toFinset) c4113
private def r4129 : InferenceRequest := .assume c4113
private def f4130 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4113
private def r4131 : InferenceRequest := .eqMp f4106 f4130
private def f4132 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4020
private def r4133 : InferenceRequest := .mkComb f4132 f1813
private def e4134 : HOL.Term Symbol [] h173 := .app e4017 e1807
private def e4135 : HOL.Term Symbol [] h189 := .app e445 e4134
private def e4136 : HOL.Term Symbol [] h173 := .app e4135 e1817
private def c4137 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4136
private def f4138 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4137
private def s4139 : SourceTerm := SourceTerm.app s3305 s1278
private def s4140 : SourceTerm := SourceTerm.app s1662 s4139
private def s4141 : SourceTerm := SourceTerm.app s4140 s1278
private def s4142 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t17 s4141
private def s4143 : SourceTerm := SourceTerm.app s4142 s1662
private def e4144 : HOL.Term Symbol [] h173 := .app e4017 e3815
private def c4145 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4144
private theorem n4146 : s4143.toDB [] = c4145.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4147 : CheckedSourceTerm := ⟨s4143, t1, by rw [← DBTerm.inferType_toDB [] s4143, n4146]; exact c4145.checked.trans (congrArg some v175)⟩
private def r4148 : InferenceRequest := .beta k4147
private def e4149 : HOL.Term Symbol [] h189 := .app e445 e4144
private def e4150 : HOL.Term Symbol [] h173 := .app e4149 e3978
private def c4151 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4150
private def f4152 : Theorem := Theorem.emptyResult ([].toFinset) c4151
private def r4153 : InferenceRequest := .inst [(k1856, s1662)] f4152
private def e4154 : HOL.Term Symbol [] h189 := .app e1807 e3654
private def e4155 : HOL.Term Symbol [] h173 := .app e4154 e1309
private def e4156 : HOL.Term Symbol [] h173 := .app e4135 e4155
private def c4157 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4156
private def f4158 : Theorem := Theorem.emptyResult ([].toFinset) c4157
private def r4159 : InferenceRequest := .inst [(k4025, s1278)] f1874
private def e4160 : HOL.Term Symbol [] h195 := .app e727 e4154
private def e4161 : HOL.Term Symbol [h173] h173 := .app e2596 e1870
private def e4162 : HOL.Term Symbol [] h189 := .lam e4161
private def e4163 : HOL.Term Symbol [] h173 := .app e4160 e4162
private def c4164 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4163
private def f4165 : Theorem := Theorem.emptyResult ([].toFinset) c4164
private def r4166 : InferenceRequest := .mkComb f4165 f3700
private def e4167 : HOL.Term Symbol [] h189 := .app e445 e4155
private def e4168 : HOL.Term Symbol [] h173 := .app e4162 e1309
private def e4169 : HOL.Term Symbol [] h173 := .app e4167 e4168
private def c4170 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4169
private def f4171 : Theorem := Theorem.emptyResult ([].toFinset) c4170
private def s4172 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s4139
private def s4173 : SourceTerm := SourceTerm.app s4172 s47
private def e4174 : HOL.Term Symbol [] h173 := .app e4162 e4083
private def c4175 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4174
private theorem n4176 : s4173.toDB [] = c4175.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4177 : CheckedSourceTerm := ⟨s4173, t1, by rw [← DBTerm.inferType_toDB [] s4173, n4176]; exact c4175.checked.trans (congrArg some v175)⟩
private def r4178 : InferenceRequest := .beta k4177
private def e4179 : HOL.Term Symbol [] h189 := .app e445 e4174
private def e4180 : HOL.Term Symbol [] h173 := .app e4179 e3654
private def c4181 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4180
private def f4182 : Theorem := Theorem.emptyResult ([].toFinset) c4181
private def r4183 : InferenceRequest := .inst [(k3725, s47)] f4182
private def e4184 : HOL.Term Symbol [] h189 := .app e445 e4168
private def e4185 : HOL.Term Symbol [] h173 := .app e4184 e3654
private def c4186 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4185
private def f4187 : Theorem := Theorem.emptyResult ([].toFinset) c4186
private def r4188 : InferenceRequest := .trans f4171 f4187
private def e4189 : HOL.Term Symbol [] h173 := .app e4167 e3654
private def c4190 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4189
private def f4191 : Theorem := Theorem.emptyResult ([].toFinset) c4190
private def r4192 : InferenceRequest := .trans f4158 f4191
private def e4193 : HOL.Term Symbol [] h173 := .app e4135 e3654
private def c4194 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4193
private def f4195 : Theorem := Theorem.emptyResult ([].toFinset) c4194
private def r4196 : InferenceRequest := .mkComb f725 f4195
private def e4197 : HOL.Term Symbol [] h195 := .app e727 e4135
private def e4198 : HOL.Term Symbol [] h173 := .app e4197 e3659
private def c4199 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4198
private def f4200 : Theorem := Theorem.emptyResult ([].toFinset) c4199
private def c4201 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4134
private def r4202 : InferenceRequest := .refl c4201
private def e4203 : HOL.Term Symbol [] h173 := .app e4135 e4134
private def c4204 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4203
private def f4205 : Theorem := Theorem.emptyResult ([].toFinset) c4204
private def r4206 : InferenceRequest := .mkComb f4200 f4205
private def e4207 : HOL.Term Symbol [] h189 := .app e445 e4203
private def e4208 : HOL.Term Symbol [] h173 := .app e3659 e4134
private def e4209 : HOL.Term Symbol [] h173 := .app e4207 e4208
private def c4210 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4209
private def f4211 : Theorem := Theorem.emptyResult ([].toFinset) c4210
private def r4212 : InferenceRequest := .eqMp f4211 f4205
private def c4213 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4208
private def f4214 : Theorem := Theorem.emptyResult ([].toFinset) c4213
private def r4215 : InferenceRequest := .trans f4214 f4138
private def e4216 : HOL.Term Symbol [] h173 := .app e3659 e1817
private def c4217 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4216
private def f4218 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4217
private def r4219 : InferenceRequest := .trans f4218 f2237
private def f4220 : Theorem := Theorem.emptyResult ([c4113].toFinset) c3967
private def r4221 : InferenceRequest := .mkComb f725 f4220
private def e4222 : HOL.Term Symbol [] h195 := .app e727 e3659
private def e4223 : HOL.Term Symbol [] h173 := .app e4222 e2204
private def c4224 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4223
private def f4225 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4224
private def r4226 : InferenceRequest := .refl c3655
private def e4227 : HOL.Term Symbol [] h173 := .app e3659 e3654
private def c4228 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4227
private def f4229 : Theorem := Theorem.emptyResult ([].toFinset) c4228
private def r4230 : InferenceRequest := .mkComb f4225 f4229
private def e4231 : HOL.Term Symbol [] h189 := .app e445 e4227
private def e4232 : HOL.Term Symbol [] h173 := .app e2204 e3654
private def e4233 : HOL.Term Symbol [] h173 := .app e4231 e4232
private def c4234 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4233
private def f4235 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4234
private def r4236 : InferenceRequest := .eqMp f4235 f4229
private def c4237 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4232
private def f4238 : Theorem := Theorem.emptyResult ([c4113].toFinset) c4237
private def r4239 : InferenceRequest := .eqMp f4238 f777
private def f4240 : Theorem := Theorem.emptyResult ([c4113].toFinset) c3655
private def r4241 : InferenceRequest := .deductAntisym f4128 f4240
private def e4242 : HOL.Term Symbol [] h173 := .app e4070 e3654
private def c4243 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4242
private def f4244 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4243
private def r4245 : InferenceRequest := .inst [(k4025, s1278)] f2342
private def e4246 : HOL.Term Symbol [] h189 := .app e2308 e3654
private def e4247 : HOL.Term Symbol [] h195 := .app e727 e4246
private def e4248 : HOL.Term Symbol [h173] h189 := .app e2334 e4161
private def e4249 : HOL.Term Symbol [h173] h173 := .app e4248 e770
private def e4250 : HOL.Term Symbol [h173] h189 := .app e2315 e4249
private def e4251 : HOL.Term Symbol [h173] h173 := .app e4250 e4161
private def e4252 : HOL.Term Symbol [] h189 := .lam e4251
private def e4253 : HOL.Term Symbol [] h173 := .app e4247 e4252
private def c4254 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4253
private def f4255 : Theorem := Theorem.emptyResult ([].toFinset) c4254
private def r4256 : InferenceRequest := .mkComb f4255 f3700
private def e4257 : HOL.Term Symbol [] h173 := .app e4246 e1309
private def e4258 : HOL.Term Symbol [] h189 := .app e445 e4257
private def e4259 : HOL.Term Symbol [] h173 := .app e4252 e1309
private def e4260 : HOL.Term Symbol [] h173 := .app e4258 e4259
private def c4261 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4260
private def f4262 : Theorem := Theorem.emptyResult ([].toFinset) c4261
private def s4263 : SourceTerm := SourceTerm.app s2275 s4139
private def s4264 : SourceTerm := SourceTerm.app s4263 s47
private def s4265 : SourceTerm := SourceTerm.app s18 s4264
private def s4266 : SourceTerm := SourceTerm.app s4265 s4139
private def s4267 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s4266
private def s4268 : SourceTerm := SourceTerm.app s4267 s47
private def e4269 : HOL.Term Symbol [] h173 := .app e4252 e4083
private def c4270 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4269
private theorem n4271 : s4268.toDB [] = c4270.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4272 : CheckedSourceTerm := ⟨s4268, t1, by rw [← DBTerm.inferType_toDB [] s4268, n4271]; exact c4270.checked.trans (congrArg some v175)⟩
private def r4273 : InferenceRequest := .beta k4272
private def e4274 : HOL.Term Symbol [] h189 := .app e445 e4269
private def e4275 : HOL.Term Symbol [] h173 := .app e4027 e4083
private def e4276 : HOL.Term Symbol [] h189 := .app e445 e4275
private def e4277 : HOL.Term Symbol [] h173 := .app e4276 e3654
private def e4278 : HOL.Term Symbol [] h173 := .app e4274 e4277
private def c4279 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4278
private def f4280 : Theorem := Theorem.emptyResult ([].toFinset) c4279
private def r4281 : InferenceRequest := .inst [(k3725, s47)] f4280
private def e4282 : HOL.Term Symbol [] h189 := .app e445 e4259
private def e4283 : HOL.Term Symbol [] h173 := .app e4282 e4242
private def c4284 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4283
private def f4285 : Theorem := Theorem.emptyResult ([].toFinset) c4284
private def r4286 : InferenceRequest := .trans f4262 f4285
private def e4287 : HOL.Term Symbol [] h173 := .app e4258 e4242
private def c4288 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4287
private def f4289 : Theorem := Theorem.emptyResult ([].toFinset) c4288
private def r4290 : InferenceRequest := .mkComb f725 f4289
private def e4291 : HOL.Term Symbol [] h195 := .app e727 e4258
private def e4292 : HOL.Term Symbol [] h189 := .app e445 e4242
private def e4293 : HOL.Term Symbol [] h173 := .app e4291 e4292
private def c4294 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4293
private def f4295 : Theorem := Theorem.emptyResult ([].toFinset) c4294
private def c4296 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4257
private def r4297 : InferenceRequest := .refl c4296
private def e4298 : HOL.Term Symbol [] h173 := .app e4258 e4257
private def c4299 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4298
private def f4300 : Theorem := Theorem.emptyResult ([].toFinset) c4299
private def r4301 : InferenceRequest := .mkComb f4295 f4300
private def e4302 : HOL.Term Symbol [] h189 := .app e445 e4298
private def e4303 : HOL.Term Symbol [] h173 := .app e4292 e4257
private def e4304 : HOL.Term Symbol [] h173 := .app e4302 e4303
private def c4305 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4304
private def f4306 : Theorem := Theorem.emptyResult ([].toFinset) c4305
private def r4307 : InferenceRequest := .eqMp f4306 f4300
private def c4308 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4303
private def f4309 : Theorem := Theorem.emptyResult ([].toFinset) c4308
private def r4310 : InferenceRequest := .eqMp f4309 f4244
private def f4311 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4296
private def r4312 : InferenceRequest := .deductAntisym f3652 f4311
private def e4313 : HOL.Term Symbol [] h173 := .app e3666 e4257
private def c4314 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4313
private def f4315 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4314
private def r4316 : InferenceRequest := .eqMp f4315 f3652
private def r4317 : InferenceRequest := .deductAntisym f3652 f777
private def e4318 : HOL.Term Symbol [] h173 := .app e3666 e775
private def c4319 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4318
private def f4320 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4319
private def r4321 : InferenceRequest := .deductAntisym f4311 f777
private def e4322 : HOL.Term Symbol [] h173 := .app e4258 e775
private def c4323 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4322
private def f4324 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4323
private def r4325 : InferenceRequest := .mkComb f3964 f4320
private def e4326 : HOL.Term Symbol [] h189 := .app e3815 e3649
private def e4327 : HOL.Term Symbol [] h195 := .app e727 e4326
private def e4328 : HOL.Term Symbol [] h173 := .app e4327 e3973
private def c4329 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4328
private def f4330 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4329
private def r4331 : InferenceRequest := .mkComb f4330 f4324
private def e4332 : HOL.Term Symbol [] h173 := .app e4326 e4257
private def e4333 : HOL.Term Symbol [] h189 := .app e445 e4332
private def e4334 : HOL.Term Symbol [] h173 := .app e4333 e3980
private def c4335 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4334
private def f4336 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4335
private def r4337 : InferenceRequest := .abs ⟨Name.mk ["", ""] "x", t17⟩ f4336
private def e4338 : HOL.Term Symbol [h192] h189 := .app e4012 e874
private def e4339 : HOL.Term Symbol [h192] h173 := .app e4338 e1759
private def e4340 : HOL.Term Symbol [h192] h189 := .app e802 e4339
private def e4341 : HOL.Term Symbol [h192] h189 := .app e4012 e4014
private def e4342 : HOL.Term Symbol [h192] h173 := .app e4341 e1759
private def e4343 : HOL.Term Symbol [h192] h173 := .app e4340 e4342
private def e4344 : HOL.Term Symbol [] h213 := .lam e4343
private def e4345 : HOL.Term Symbol [] h216 := .app e801 e4344
private def e4346 : HOL.Term Symbol [] h173 := .app e4345 e1273
private def c4347 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4346
private def f4348 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4347
private def s4349 : SourceTerm := SourceTerm.app s2281 s1350
private def s4350 : SourceTerm := SourceTerm.app s4349 s1278
private theorem n4351 : s4350.toDB [] = c3650.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4352 : CheckedSourceTerm := ⟨s4350, t1, by rw [← DBTerm.inferType_toDB [] s4350, n4351]; exact c3650.checked.trans (congrArg some v175)⟩
private def r4353 : InferenceRequest := .inst [(k4352, s1278)] f1336
private def e4354 : HOL.Term Symbol [] h189 := .app e1308 e3649
private def e4355 : HOL.Term Symbol [] h195 := .app e727 e4354
private def e4356 : HOL.Term Symbol [h192, h173] h189 := .app e4056 e1482
private def e4357 : HOL.Term Symbol [h192, h173] h173 := .app e4356 e1318
private def e4358 : HOL.Term Symbol [h192, h173] h189 := .app e1317 e4357
private def e4359 : HOL.Term Symbol [h192, h173] h173 := .app e4358 e1320
private def e4360 : HOL.Term Symbol [h173] h213 := .lam e4359
private def e4361 : HOL.Term Symbol [h173] h216 := .app e1316 e4360
private def e4362 : HOL.Term Symbol [h173] h173 := .app e4361 e1331
private def e4363 : HOL.Term Symbol [] h189 := .lam e4362
private def e4364 : HOL.Term Symbol [] h173 := .app e4355 e4363
private def c4365 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4364
private def f4366 : Theorem := Theorem.emptyResult ([].toFinset) c4365
private def r4367 : InferenceRequest := .mkComb f4366 f4300
private def e4368 : HOL.Term Symbol [] h173 := .app e4354 e4257
private def e4369 : HOL.Term Symbol [] h189 := .app e445 e4368
private def e4370 : HOL.Term Symbol [] h173 := .app e4363 e4257
private def e4371 : HOL.Term Symbol [] h173 := .app e4369 e4370
private def c4372 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4371
private def f4373 : Theorem := Theorem.emptyResult ([].toFinset) c4372
private def s4374 : SourceTerm := SourceTerm.app s3171 s1278
private def s4375 : SourceTerm := SourceTerm.app s1277 s4374
private def s4376 : SourceTerm := SourceTerm.app s4375 s47
private def s4377 : SourceTerm := SourceTerm.abs (Name.mk ["", "", ""] "x") t17 s4376
private def s4378 : SourceTerm := SourceTerm.app s22 s4377
private def s4379 : SourceTerm := SourceTerm.app s4378 s1285
private def s4380 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s4379
private def s4381 : SourceTerm := SourceTerm.app s4380 s47
private def e4382 : HOL.Term Symbol [] h173 := .app e4363 e4083
private def c4383 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4382
private theorem n4384 : s4381.toDB [] = c4383.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4385 : CheckedSourceTerm := ⟨s4381, t1, by rw [← DBTerm.inferType_toDB [] s4381, n4384]; exact c4383.checked.trans (congrArg some v175)⟩
private def r4386 : InferenceRequest := .beta k4385
private def e4387 : HOL.Term Symbol [] h189 := .app e445 e4382
private def e4388 : HOL.Term Symbol [h192] h173 := .app e4340 e4090
private def e4389 : HOL.Term Symbol [] h213 := .lam e4388
private def e4390 : HOL.Term Symbol [] h216 := .app e801 e4389
private def e4391 : HOL.Term Symbol [] h173 := .app e4390 e1273
private def e4392 : HOL.Term Symbol [] h173 := .app e4387 e4391
private def c4393 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4392
private def f4394 : Theorem := Theorem.emptyResult ([].toFinset) c4393
private def s4395 : SourceTerm := SourceTerm.app s2281 s4023
private def s4396 : SourceTerm := SourceTerm.app s4395 s1278
private theorem n4397 : s4396.toDB [] = c4296.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4398 : CheckedSourceTerm := ⟨s4396, t1, by rw [← DBTerm.inferType_toDB [] s4396, n4397]; exact c4296.checked.trans (congrArg some v175)⟩
private def r4399 : InferenceRequest := .inst [(k4398, s47)] f4394
private def e4400 : HOL.Term Symbol [] h189 := .app e445 e4370
private def e4401 : HOL.Term Symbol [] h173 := .app e4400 e4346
private def c4402 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4401
private def f4403 : Theorem := Theorem.emptyResult ([].toFinset) c4402
private def r4404 : InferenceRequest := .trans f4373 f4403
private def e4405 : HOL.Term Symbol [] h173 := .app e4369 e4346
private def c4406 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4405
private def f4407 : Theorem := Theorem.emptyResult ([].toFinset) c4406
private def r4408 : InferenceRequest := .mkComb f725 f4407
private def e4409 : HOL.Term Symbol [] h195 := .app e727 e4369
private def e4410 : HOL.Term Symbol [] h189 := .app e445 e4346
private def e4411 : HOL.Term Symbol [] h173 := .app e4409 e4410
private def c4412 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4411
private def f4413 : Theorem := Theorem.emptyResult ([].toFinset) c4412
private def c4414 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4368
private def r4415 : InferenceRequest := .refl c4414
private def e4416 : HOL.Term Symbol [] h173 := .app e4369 e4368
private def c4417 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4416
private def f4418 : Theorem := Theorem.emptyResult ([].toFinset) c4417
private def r4419 : InferenceRequest := .mkComb f4413 f4418
private def e4420 : HOL.Term Symbol [] h189 := .app e445 e4416
private def e4421 : HOL.Term Symbol [] h173 := .app e4410 e4368
private def e4422 : HOL.Term Symbol [] h173 := .app e4420 e4421
private def c4423 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4422
private def f4424 : Theorem := Theorem.emptyResult ([].toFinset) c4423
private def r4425 : InferenceRequest := .eqMp f4424 f4418
private def c4426 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4421
private def f4427 : Theorem := Theorem.emptyResult ([].toFinset) c4426
private def r4428 : InferenceRequest := .eqMp f4427 f4348
private def f4429 : Theorem := Theorem.emptyResult ([c3650].toFinset) c4414
private def r4430 : InferenceRequest := .assume c4414
private def f4431 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4414
private def r4432 : InferenceRequest := .eqMp f4407 f4431
private def f4433 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4347
private def r4434 : InferenceRequest := .mkComb f4433 f1813
private def e4435 : HOL.Term Symbol [] h173 := .app e4344 e1807
private def e4436 : HOL.Term Symbol [] h189 := .app e445 e4435
private def e4437 : HOL.Term Symbol [] h173 := .app e4436 e1817
private def c4438 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4437
private def f4439 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4438
private def s4440 : SourceTerm := SourceTerm.app s2524 s1278
private def s4441 : SourceTerm := SourceTerm.app s1662 s4440
private def s4442 : SourceTerm := SourceTerm.app s1371 s4139
private def s4443 : SourceTerm := SourceTerm.app s4442 s1278
private def s4444 : SourceTerm := SourceTerm.app s4441 s4443
private def s4445 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t17 s4444
private def s4446 : SourceTerm := SourceTerm.app s4445 s1662
private def e4447 : HOL.Term Symbol [] h173 := .app e4344 e3815
private def c4448 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4447
private theorem n4449 : s4446.toDB [] = c4448.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4450 : CheckedSourceTerm := ⟨s4446, t1, by rw [← DBTerm.inferType_toDB [] s4446, n4449]; exact c4448.checked.trans (congrArg some v175)⟩
private def r4451 : InferenceRequest := .beta k4450
private def e4452 : HOL.Term Symbol [] h189 := .app e445 e4447
private def e4453 : HOL.Term Symbol [] h173 := .app e4452 e4332
private def c4454 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4453
private def f4455 : Theorem := Theorem.emptyResult ([].toFinset) c4454
private def r4456 : InferenceRequest := .inst [(k1856, s1662)] f4455
private def e4457 : HOL.Term Symbol [] h189 := .app e1807 e3649
private def e4458 : HOL.Term Symbol [] h173 := .app e4457 e4257
private def e4459 : HOL.Term Symbol [] h173 := .app e4436 e4458
private def c4460 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4459
private def f4461 : Theorem := Theorem.emptyResult ([].toFinset) c4460
private def r4462 : InferenceRequest := .inst [(k4352, s1278)] f1874
private def e4463 : HOL.Term Symbol [] h195 := .app e727 e4457
private def e4464 : HOL.Term Symbol [h173] h173 := .app e2579 e1870
private def e4465 : HOL.Term Symbol [] h189 := .lam e4464
private def e4466 : HOL.Term Symbol [] h173 := .app e4463 e4465
private def c4467 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4466
private def f4468 : Theorem := Theorem.emptyResult ([].toFinset) c4467
private def r4469 : InferenceRequest := .mkComb f4468 f4300
private def e4470 : HOL.Term Symbol [] h189 := .app e445 e4458
private def e4471 : HOL.Term Symbol [] h173 := .app e4465 e4257
private def e4472 : HOL.Term Symbol [] h173 := .app e4470 e4471
private def c4473 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4472
private def f4474 : Theorem := Theorem.emptyResult ([].toFinset) c4473
private def s4475 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s4440
private def s4476 : SourceTerm := SourceTerm.app s4475 s47
private def e4477 : HOL.Term Symbol [] h173 := .app e4465 e4083
private def c4478 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4477
private theorem n4479 : s4476.toDB [] = c4478.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4480 : CheckedSourceTerm := ⟨s4476, t1, by rw [← DBTerm.inferType_toDB [] s4476, n4479]; exact c4478.checked.trans (congrArg some v175)⟩
private def r4481 : InferenceRequest := .beta k4480
private def e4482 : HOL.Term Symbol [] h189 := .app e445 e4477
private def e4483 : HOL.Term Symbol [] h173 := .app e4482 e3649
private def c4484 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4483
private def f4485 : Theorem := Theorem.emptyResult ([].toFinset) c4484
private def r4486 : InferenceRequest := .inst [(k4398, s47)] f4485
private def e4487 : HOL.Term Symbol [] h189 := .app e445 e4471
private def e4488 : HOL.Term Symbol [] h173 := .app e4487 e3649
private def c4489 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4488
private def f4490 : Theorem := Theorem.emptyResult ([].toFinset) c4489
private def r4491 : InferenceRequest := .trans f4474 f4490
private def e4492 : HOL.Term Symbol [] h173 := .app e4470 e3649
private def c4493 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4492
private def f4494 : Theorem := Theorem.emptyResult ([].toFinset) c4493
private def r4495 : InferenceRequest := .trans f4461 f4494
private def e4496 : HOL.Term Symbol [] h173 := .app e4436 e3649
private def c4497 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4496
private def f4498 : Theorem := Theorem.emptyResult ([].toFinset) c4497
private def r4499 : InferenceRequest := .mkComb f725 f4498
private def e4500 : HOL.Term Symbol [] h195 := .app e727 e4436
private def e4501 : HOL.Term Symbol [] h173 := .app e4500 e3666
private def c4502 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4501
private def f4503 : Theorem := Theorem.emptyResult ([].toFinset) c4502
private def c4504 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4435
private def r4505 : InferenceRequest := .refl c4504
private def e4506 : HOL.Term Symbol [] h173 := .app e4436 e4435
private def c4507 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4506
private def f4508 : Theorem := Theorem.emptyResult ([].toFinset) c4507
private def r4509 : InferenceRequest := .mkComb f4503 f4508
private def e4510 : HOL.Term Symbol [] h189 := .app e445 e4506
private def e4511 : HOL.Term Symbol [] h173 := .app e3666 e4435
private def e4512 : HOL.Term Symbol [] h173 := .app e4510 e4511
private def c4513 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4512
private def f4514 : Theorem := Theorem.emptyResult ([].toFinset) c4513
private def r4515 : InferenceRequest := .eqMp f4514 f4508
private def c4516 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4511
private def f4517 : Theorem := Theorem.emptyResult ([].toFinset) c4516
private def r4518 : InferenceRequest := .trans f4517 f4439
private def e4519 : HOL.Term Symbol [] h173 := .app e3666 e1817
private def c4520 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4519
private def f4521 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4520
private def r4522 : InferenceRequest := .trans f4521 f2237
private def f4523 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4319
private def r4524 : InferenceRequest := .mkComb f725 f4523
private def e4525 : HOL.Term Symbol [] h195 := .app e727 e3666
private def e4526 : HOL.Term Symbol [] h173 := .app e4525 e2204
private def c4527 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4526
private def f4528 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4527
private def r4529 : InferenceRequest := .refl c3650
private def f4530 : Theorem := Theorem.emptyResult ([].toFinset) c3668
private def r4531 : InferenceRequest := .mkComb f4528 f4530
private def e4532 : HOL.Term Symbol [] h189 := .app e445 e3667
private def e4533 : HOL.Term Symbol [] h173 := .app e2204 e3649
private def e4534 : HOL.Term Symbol [] h173 := .app e4532 e4533
private def c4535 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4534
private def f4536 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4535
private def r4537 : InferenceRequest := .eqMp f4536 f4530
private def c4538 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4533
private def f4539 : Theorem := Theorem.emptyResult ([c4414].toFinset) c4538
private def r4540 : InferenceRequest := .eqMp f4539 f777
private def f4541 : Theorem := Theorem.emptyResult ([c4414].toFinset) c3650
private def r4542 : InferenceRequest := .deductAntisym f4429 f4541
private def e4543 : HOL.Term Symbol [] h173 := .app e4369 e3649
private def c4544 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4543
private def f4545 : Theorem := Theorem.emptyResult ([].toFinset) c4544
private def r4546 : InferenceRequest := .inst [(k4352, s1278)] f2342
private def e4547 : HOL.Term Symbol [] h189 := .app e2308 e3649
private def e4548 : HOL.Term Symbol [] h195 := .app e727 e4547
private def e4549 : HOL.Term Symbol [h173] h189 := .app e2334 e4464
private def e4550 : HOL.Term Symbol [h173] h173 := .app e4549 e770
private def e4551 : HOL.Term Symbol [h173] h189 := .app e2315 e4550
private def e4552 : HOL.Term Symbol [h173] h173 := .app e4551 e4464
private def e4553 : HOL.Term Symbol [] h189 := .lam e4552
private def e4554 : HOL.Term Symbol [] h173 := .app e4548 e4553
private def c4555 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4554
private def f4556 : Theorem := Theorem.emptyResult ([].toFinset) c4555
private def r4557 : InferenceRequest := .mkComb f4556 f4300
private def e4558 : HOL.Term Symbol [] h173 := .app e4547 e4257
private def e4559 : HOL.Term Symbol [] h189 := .app e445 e4558
private def e4560 : HOL.Term Symbol [] h173 := .app e4553 e4257
private def e4561 : HOL.Term Symbol [] h173 := .app e4559 e4560
private def c4562 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4561
private def f4563 : Theorem := Theorem.emptyResult ([].toFinset) c4562
private def s4564 : SourceTerm := SourceTerm.app s2275 s4440
private def s4565 : SourceTerm := SourceTerm.app s4564 s47
private def s4566 : SourceTerm := SourceTerm.app s18 s4565
private def s4567 : SourceTerm := SourceTerm.app s4566 s4440
private def s4568 : SourceTerm := SourceTerm.abs (Name.mk ["", ""] "x") t1 s4567
private def s4569 : SourceTerm := SourceTerm.app s4568 s47
private def e4570 : HOL.Term Symbol [] h173 := .app e4553 e4083
private def c4571 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4570
private theorem n4572 : s4569.toDB [] = c4571.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4573 : CheckedSourceTerm := ⟨s4569, t1, by rw [← DBTerm.inferType_toDB [] s4569, n4572]; exact c4571.checked.trans (congrArg some v175)⟩
private def r4574 : InferenceRequest := .beta k4573
private def e4575 : HOL.Term Symbol [] h189 := .app e445 e4570
private def e4576 : HOL.Term Symbol [] h173 := .app e4354 e4083
private def e4577 : HOL.Term Symbol [] h189 := .app e445 e4576
private def e4578 : HOL.Term Symbol [] h173 := .app e4577 e3649
private def e4579 : HOL.Term Symbol [] h173 := .app e4575 e4578
private def c4580 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4579
private def f4581 : Theorem := Theorem.emptyResult ([].toFinset) c4580
private def r4582 : InferenceRequest := .inst [(k4398, s47)] f4581
private def e4583 : HOL.Term Symbol [] h189 := .app e445 e4560
private def e4584 : HOL.Term Symbol [] h173 := .app e4583 e4543
private def c4585 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4584
private def f4586 : Theorem := Theorem.emptyResult ([].toFinset) c4585
private def r4587 : InferenceRequest := .trans f4563 f4586
private def e4588 : HOL.Term Symbol [] h173 := .app e4559 e4543
private def c4589 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4588
private def f4590 : Theorem := Theorem.emptyResult ([].toFinset) c4589
private def r4591 : InferenceRequest := .mkComb f725 f4590
private def e4592 : HOL.Term Symbol [] h195 := .app e727 e4559
private def e4593 : HOL.Term Symbol [] h189 := .app e445 e4543
private def e4594 : HOL.Term Symbol [] h173 := .app e4592 e4593
private def c4595 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4594
private def f4596 : Theorem := Theorem.emptyResult ([].toFinset) c4595
private def c4597 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4558
private def r4598 : InferenceRequest := .refl c4597
private def e4599 : HOL.Term Symbol [] h173 := .app e4559 e4558
private def c4600 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4599
private def f4601 : Theorem := Theorem.emptyResult ([].toFinset) c4600
private def r4602 : InferenceRequest := .mkComb f4596 f4601
private def e4603 : HOL.Term Symbol [] h189 := .app e445 e4599
private def e4604 : HOL.Term Symbol [] h173 := .app e4593 e4558
private def e4605 : HOL.Term Symbol [] h173 := .app e4603 e4604
private def c4606 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4605
private def f4607 : Theorem := Theorem.emptyResult ([].toFinset) c4606
private def r4608 : InferenceRequest := .eqMp f4607 f4601
private def c4609 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4604
private def f4610 : Theorem := Theorem.emptyResult ([].toFinset) c4609
private def r4611 : InferenceRequest := .eqMp f4610 f4545
private def f4612 : Theorem := Theorem.emptyResult ([].toFinset) c4597
private def r4613 : InferenceRequest := .deductAntisym f4612 f777
private def e4614 : HOL.Term Symbol [] h173 := .app e4559 e775
private def c4615 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4614
private def f4616 : Theorem := Theorem.emptyResult ([].toFinset) c4615
private def r4617 : InferenceRequest := .abs ⟨Name.mk [""] "x", t1⟩ f4616
private def e4618 : HOL.Term Symbol [] h195 := .app e727 e2601
private def e4619 : HOL.Term Symbol [] h173 := .app e4618 e2199
private def c4620 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4619
private def f4621 : Theorem := Theorem.emptyResult ([].toFinset) c4620
private def s4622 : SourceTerm := SourceTerm.app s2895 s2891
private def e4623 : HOL.Term Symbol [] h189 := .const (.variable ⟨Name.mk [""] "x", t4⟩ q190)
private def e4624 : HOL.Term Symbol [] h173 := .app e2552 e4623
private def c4625 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4624
private theorem n4626 : s4622.toDB [] = c4625.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4627 : CheckedSourceTerm := ⟨s4622, t1, by rw [← DBTerm.inferType_toDB [] s4622, n4626]; exact c4625.checked.trans (congrArg some v175)⟩
private def r4628 : InferenceRequest := .beta k4627
private def e4629 : HOL.Term Symbol [] h189 := .app e445 e4624
private def e4630 : HOL.Term Symbol [] h195 := .app e727 e4623
private def e4631 : HOL.Term Symbol [] h173 := .app e4630 e2199
private def e4632 : HOL.Term Symbol [] h173 := .app e4629 e4631
private def c4633 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4632
private def f4634 : Theorem := Theorem.emptyResult ([].toFinset) c4633
private def c4635 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e2601
private theorem n4636 : s2921.toDB [] = c4635.term := by exact (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)
private def k4637 : CheckedSourceTerm := ⟨s2921, t4, by rw [← DBTerm.inferType_toDB [] s2921, n4636]; exact c4635.checked.trans (congrArg some v191)⟩
private def r4638 : InferenceRequest := .inst [(k4637, s2891)] f4634
private def e4639 : HOL.Term Symbol [] h173 := .app e2611 e4619
private def c4640 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4639
private def f4641 : Theorem := Theorem.emptyResult ([].toFinset) c4640
private def r4642 : InferenceRequest := .mkComb f725 f4641
private def e4643 : HOL.Term Symbol [] h189 := .app e445 e4619
private def e4644 : HOL.Term Symbol [] h173 := .app e3561 e4643
private def c4645 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4644
private def f4646 : Theorem := Theorem.emptyResult ([].toFinset) c4645
private def r4647 : InferenceRequest := .mkComb f4646 f2635
private def e4648 : HOL.Term Symbol [] h173 := .app e4643 e2602
private def e4649 : HOL.Term Symbol [] h173 := .app e3567 e4648
private def c4650 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4649
private def f4651 : Theorem := Theorem.emptyResult ([].toFinset) c4650
private def r4652 : InferenceRequest := .eqMp f4651 f2635
private def c4653 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4648
private def f4654 : Theorem := Theorem.emptyResult ([].toFinset) c4653
private def r4655 : InferenceRequest := .eqMp f4654 f4621
private def f4656 : Theorem := Theorem.emptyResult ([].toFinset) c2623
private def r4657 : InferenceRequest := .eqMp f3625 f3647
private def r4658 : InferenceRequest := .mkComb f725 f3580
private def e4659 : HOL.Term Symbol [] h173 := .app e3274 e2611
private def c4660 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4659
private def f4661 : Theorem := Theorem.emptyResult ([].toFinset) c4660
private def r4662 : InferenceRequest := .mkComb f4661 f3283
private def e4663 : HOL.Term Symbol [] h173 := .app e2611 e3164
private def e4664 : HOL.Term Symbol [] h173 := .app e3285 e4663
private def c4665 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4664
private def f4666 : Theorem := Theorem.emptyResult ([].toFinset) c4665
private def r4667 : InferenceRequest := .eqMp f4666 f3283
private def c4668 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4663
private def f4669 : Theorem := Theorem.emptyResult ([].toFinset) c4668
private def r4670 : InferenceRequest := .eqMp f4669 f4656
private def f4671 : Theorem := Theorem.emptyResult ([].toFinset) c3279
private def r4672 : InferenceRequest := .eqMp f3272 f4671
private def f4673 : Theorem := Theorem.emptyResult ([].toFinset) c2889
private def r4674 : InferenceRequest := .mkComb f4673 f3806
private def e4675 : HOL.Term Symbol [] h173 := .app e2886 e3800
private def e4676 : HOL.Term Symbol [] h189 := .app e445 e4675
private def e4677 : HOL.Term Symbol [] h173 := .app e4676 e3810
private def c4678 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4677
private def f4679 : Theorem := Theorem.emptyResult ([].toFinset) c4678
private def r4680 : InferenceRequest := .inst [(k3829, s1821)] f3324
private def e4681 : HOL.Term Symbol [] h189 := .app e3800 e2602
private def e4682 : HOL.Term Symbol [] h173 := .app e4681 e711
private def e4683 : HOL.Term Symbol [] h173 := .app e4676 e4682
private def c4684 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4683
private def f4685 : Theorem := Theorem.emptyResult ([].toFinset) c4684
private def r4686 : InferenceRequest := .inst [(k2924, s1278)] f3845
private def e4687 : HOL.Term Symbol [] h195 := .app e727 e4681
private def e4688 : HOL.Term Symbol [] h173 := .app e4687 e771
private def c4689 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4688
private def f4690 : Theorem := Theorem.emptyResult ([].toFinset) c4689
private def r4691 : InferenceRequest := .mkComb f4690 f759
private def e4692 : HOL.Term Symbol [] h189 := .app e445 e4682
private def e4693 : HOL.Term Symbol [] h173 := .app e771 e711
private def e4694 : HOL.Term Symbol [] h173 := .app e4692 e4693
private def c4695 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4694
private def f4696 : Theorem := Theorem.emptyResult ([].toFinset) c4695
private def r4697 : InferenceRequest := .inst [(k1407, s1278)] f3865
private def e4698 : HOL.Term Symbol [] h189 := .app e445 e4693
private def e4699 : HOL.Term Symbol [] h173 := .app e4698 e711
private def c4700 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4699
private def f4701 : Theorem := Theorem.emptyResult ([].toFinset) c4700
private def r4702 : InferenceRequest := .trans f4696 f4701
private def e4703 : HOL.Term Symbol [] h173 := .app e4692 e711
private def c4704 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4703
private def f4705 : Theorem := Theorem.emptyResult ([].toFinset) c4704
private def r4706 : InferenceRequest := .trans f4685 f4705
private def e4707 : HOL.Term Symbol [] h173 := .app e4676 e711
private def c4708 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4707
private def f4709 : Theorem := Theorem.emptyResult ([].toFinset) c4708
private def r4710 : InferenceRequest := .mkComb f725 f4709
private def e4711 : HOL.Term Symbol [] h195 := .app e727 e4676
private def e4712 : HOL.Term Symbol [] h173 := .app e4711 e729
private def c4713 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4712
private def f4714 : Theorem := Theorem.emptyResult ([].toFinset) c4713
private def c4715 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4675
private def r4716 : InferenceRequest := .refl c4715
private def e4717 : HOL.Term Symbol [] h173 := .app e4676 e4675
private def c4718 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4717
private def f4719 : Theorem := Theorem.emptyResult ([].toFinset) c4718
private def r4720 : InferenceRequest := .mkComb f4714 f4719
private def e4721 : HOL.Term Symbol [] h189 := .app e445 e4717
private def e4722 : HOL.Term Symbol [] h173 := .app e729 e4675
private def e4723 : HOL.Term Symbol [] h173 := .app e4721 e4722
private def c4724 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4723
private def f4725 : Theorem := Theorem.emptyResult ([].toFinset) c4724
private def r4726 : InferenceRequest := .eqMp f4725 f4719
private def c4727 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4722
private def f4728 : Theorem := Theorem.emptyResult ([].toFinset) c4727
private def r4729 : InferenceRequest := .trans f4728 f4679
private def e4730 : HOL.Term Symbol [] h173 := .app e729 e3810
private def c4731 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4730
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
private def e4745 : HOL.Term Symbol [] h173 := .app e1780 e729
private def c4746 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4745
private def f4747 : Theorem := Theorem.emptyResult ([].toFinset) c4746
private def r4748 : InferenceRequest := .mkComb f4747 f1789
private def e4749 : HOL.Term Symbol [] h173 := .app e729 e1656
private def e4750 : HOL.Term Symbol [] h173 := .app e1791 e4749
private def c4751 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4750
private def f4752 : Theorem := Theorem.emptyResult ([].toFinset) c4751
private def r4753 : InferenceRequest := .eqMp f4752 f1789
private def c4754 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4749
private def f4755 : Theorem := Theorem.emptyResult ([].toFinset) c4754
private def r4756 : InferenceRequest := .eqMp f4755 f4742
private def f4757 : Theorem := Theorem.emptyResult ([].toFinset) c1785
private def r4758 : InferenceRequest := .eqMp f1778 f4757
private def f4759 : Theorem := Theorem.emptyResult ([].toFinset) c1275
private def r4760 : InferenceRequest := .mkComb f4759 f3806
private def e4761 : HOL.Term Symbol [] h173 := .app e1264 e3800
private def e4762 : HOL.Term Symbol [] h189 := .app e445 e4761
private def e4763 : HOL.Term Symbol [] h173 := .app e4762 e3810
private def c4764 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4763
private def f4765 : Theorem := Theorem.emptyResult ([].toFinset) c4764
private def r4766 : InferenceRequest := .inst [(k3829, s1821)] f1852
private def e4767 : HOL.Term Symbol [] h189 := .app e3800 e711
private def e4768 : HOL.Term Symbol [] h173 := .app e4767 e686
private def e4769 : HOL.Term Symbol [] h173 := .app e4762 e4768
private def c4770 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4769
private def f4771 : Theorem := Theorem.emptyResult ([].toFinset) c4770
private def r4772 : InferenceRequest := .inst [(k1407, s1278)] f3845
private def e4773 : HOL.Term Symbol [] h195 := .app e727 e4767
private def e4774 : HOL.Term Symbol [] h173 := .app e4773 e771
private def c4775 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4774
private def f4776 : Theorem := Theorem.emptyResult ([].toFinset) c4775
private def r4777 : InferenceRequest := .mkComb f4776 f737
private def e4778 : HOL.Term Symbol [] h189 := .app e445 e4768
private def e4779 : HOL.Term Symbol [] h173 := .app e771 e686
private def e4780 : HOL.Term Symbol [] h173 := .app e4778 e4779
private def c4781 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4780
private def f4782 : Theorem := Theorem.emptyResult ([].toFinset) c4781
private def r4783 : InferenceRequest := .inst [(k1769, s1278)] f3865
private def e4784 : HOL.Term Symbol [] h189 := .app e445 e4779
private def e4785 : HOL.Term Symbol [] h173 := .app e4784 e686
private def c4786 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4785
private def f4787 : Theorem := Theorem.emptyResult ([].toFinset) c4786
private def r4788 : InferenceRequest := .trans f4782 f4787
private def e4789 : HOL.Term Symbol [] h173 := .app e4778 e686
private def c4790 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4789
private def f4791 : Theorem := Theorem.emptyResult ([].toFinset) c4790
private def r4792 : InferenceRequest := .trans f4771 f4791
private def e4793 : HOL.Term Symbol [] h173 := .app e4762 e686
private def c4794 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4793
private def f4795 : Theorem := Theorem.emptyResult ([].toFinset) c4794
private def r4796 : InferenceRequest := .mkComb f725 f4795
private def e4797 : HOL.Term Symbol [] h195 := .app e727 e4762
private def e4798 : HOL.Term Symbol [] h173 := .app e4797 e687
private def c4799 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4798
private def f4800 : Theorem := Theorem.emptyResult ([].toFinset) c4799
private def c4801 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4761
private def r4802 : InferenceRequest := .refl c4801
private def e4803 : HOL.Term Symbol [] h173 := .app e4762 e4761
private def c4804 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4803
private def f4805 : Theorem := Theorem.emptyResult ([].toFinset) c4804
private def r4806 : InferenceRequest := .mkComb f4800 f4805
private def e4807 : HOL.Term Symbol [] h189 := .app e445 e4803
private def e4808 : HOL.Term Symbol [] h173 := .app e687 e4761
private def e4809 : HOL.Term Symbol [] h173 := .app e4807 e4808
private def c4810 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4809
private def f4811 : Theorem := Theorem.emptyResult ([].toFinset) c4810
private def r4812 : InferenceRequest := .eqMp f4811 f4805
private def c4813 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4808
private def f4814 : Theorem := Theorem.emptyResult ([].toFinset) c4813
private def r4815 : InferenceRequest := .trans f4814 f4765
private def e4816 : HOL.Term Symbol [] h173 := .app e687 e3810
private def c4817 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4816
private def f4818 : Theorem := Theorem.emptyResult ([].toFinset) c4817
private def r4819 : InferenceRequest := .trans f4818 f3924
private def f4820 : Theorem := Theorem.emptyResult ([].toFinset) c784
private def r4821 : InferenceRequest := .mkComb f725 f4820
private def e4822 : HOL.Term Symbol [] h173 := .app e728 e2204
private def c4823 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4822
private def f4824 : Theorem := Theorem.emptyResult ([].toFinset) c4823
private def r4825 : InferenceRequest := .mkComb f4824 f737
private def e4826 : HOL.Term Symbol [] h173 := .app e2204 e686
private def e4827 : HOL.Term Symbol [] h173 := .app e739 e4826
private def c4828 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4827
private def f4829 : Theorem := Theorem.emptyResult ([].toFinset) c4828
private def r4830 : InferenceRequest := .eqMp f4829 f737
private def c4831 : CanonicalTerm := ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty e4826
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

checked_hol_trace witnessTrace emptyAxiomPolicy requestFormation ("pointed-predicate-witness", 0) [
  f670 r444 [],
  f714 r685 [0],
  f725 r716 [],
  f732 r726 [2, 1],
  f737 r734 [],
  f743 r738 [3, 4],
  f746 r744 [5, 4],
  f749 r748 [],
  f753 r750 [7, 6],
  f755 r754 [8, 7],
  f749 r748 [],
  f749 r748 [],
  f759 r756 [11, 10],
  f749 r760 [12, 11],
  f762 r761 [9, 13],
  f749 r748 [],
  f769 r765 [],
  f777 r773 [],
  f781 r778 [15, 17],
  f777 r773 [],
  f785 r782 [14, 19],
  f792 r786 [16, 18],
  f799 r793 [21, 20],
  f1276 r800 [22],
  f1336 r1314 [],
  f1654 r1408 [24],
  f737 r734 [],
  f1661 r1655 [25, 26],
  f1766 r1757 [],
  f1774 r1770 [28],
  f1778 r1775 [27, 29],
  f725 r716 [],
  f1784 r1779 [31, 30],
  f1789 r1786 [],
  f1795 r1790 [32, 33],
  f1798 r1796 [34, 33],
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
  f1813 r1809 [],
  f1820 r1814 [45, 46],
  f1852 r1848 [],
  f1862 r1857 [48],
  f1874 r1868 [],
  f2115 r1875 [50],
  f737 r734 [],
  f2121 r2116 [51, 52],
  f2132 r2128 [],
  f2137 r2133 [54],
  f2141 r2138 [53, 55],
  f2145 r2142 [49, 56],
  f725 r716 [],
  f2150 r2146 [58, 57],
  f2155 r2152 [],
  f2161 r2156 [59, 60],
  f2164 r2162 [61, 60],
  f2179 r2175 [],
  f2186 r2180 [63],
  f1874 r1868 [],
  f2202 r2192 [65],
  f2207 r2203 [],
  f2213 r2208 [66, 67],
  f2224 r2220 [],
  f2229 r2225 [69],
  f2233 r2230 [68, 70],
  f2237 r2234 [64, 71],
  f2241 r2238 [62, 47],
  f2243 r2242 [73, 72],
  f725 r716 [],
  f2248 r2244 [75, 74],
  f759 r2249 [],
  f2255 r2250 [76, 77],
  f2258 r2256 [78, 77],
  f777 r773 [],
  f2260 r2259 [79, 80],
  f2264 r2261 [36, 81],
  f2342 r2313 [],
  f2353 r2343 [83],
  f737 r734 [],
  f2360 r2354 [84, 85],
  f2389 r2382 [],
  f2394 r2390 [87],
  f2398 r2395 [86, 88],
  f725 r716 [],
  f2404 r2399 [90, 89],
  f2409 r2406 [],
  f2415 r2410 [91, 92],
  f2418 r2416 [93, 92],
  f2420 r2419 [94, 82],
  f2479 r2426 [],
  f2512 r2483 [96],
  f2518 r2514 [],
  f2523 r2519 [97, 98],
  f2591 r2540 [],
  f2605 r2594 [100],
  f2609 r2606 [99, 101],
  f725 r716 [],
  f2614 r2610 [103, 102],
  f759 r2249 [],
  f2619 r2615 [104, 105],
  f2622 r2620 [106, 105],
  f2625 r2624 [],
  f2629 r2626 [108, 107],
  f2631 r2630 [109, 108],
  f2625 r2624 [],
  f2625 r2624 [],
  f2635 r2632 [112, 111],
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
  f3162 r2925 [125],
  f759 r2249 [],
  f3169 r3163 [126, 127],
  f3263 r3255 [],
  f3268 r3264 [129],
  f3272 r3269 [128, 130],
  f725 r716 [],
  f3278 r3273 [132, 131],
  f3283 r3280 [],
  f3289 r3284 [133, 134],
  f3292 r3290 [135, 134],
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
  f3324 r3320 [],
  f3330 r3325 [149],
  f1874 r1868 [],
  f3504 r3331 [151],
  f759 r2249 [],
  f3510 r3505 [152, 153],
  f3521 r3517 [],
  f3526 r3522 [155],
  f3530 r3527 [154, 156],
  f3534 r3531 [150, 157],
  f725 r716 [],
  f3539 r3535 [159, 158],
  f3544 r3541 [],
  f3550 r3545 [160, 161],
  f3553 r3551 [162, 161],
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
  f2635 r3565 [],
  f3571 r3566 [177, 178],
  f3574 r3572 [179, 178],
  f777 r773 [],
  f3576 r3575 [180, 181],
  f3580 r3577 [137, 182],
  f2342 r2313 [],
  f3591 r3581 [184],
  f759 r2249 [],
  f3598 r3592 [185, 186],
  f3616 r3609 [],
  f3621 r3617 [188],
  f3625 r3622 [187, 189],
  f725 r716 [],
  f3631 r3626 [191, 190],
  f3636 r3633 [],
  f3642 r3637 [192, 193],
  f3645 r3643 [194, 193],
  f3647 r3646 [195, 183],
  f3652 r3651 [],
  f3657 r3656 [],
  f3662 r3658 [198, 197] checked_by check199,
  f3664 r3663 [199, 198],
  f3652 r3651 [],
  f3669 r3665 [201, 200],
  f3664 r3670 [202, 201] checked_by check203,
  f3672 r3671 [],
  f3657 r3656 [],
  f3676 r3673 [205, 204],
  f3678 r3677 [206, 205],
  f3652 r3651 [],
  f3682 r3679 [208, 207],
  f3684 r3683 [209, 208] checked_by check210,
  f2342 r2313 [],
  f3694 r3685 [211],
  f3700 r3696 [],
  f3705 r3701 [212, 213],
  f3723 r3715 [],
  f3723 r3726 [215],
  f3730 r3727 [214, 216],
  f3733 r3731 [217, 203],
  f725 r716 [],
  f3739 r3734 [219, 218],
  f3744 r3741 [],
  f3750 r3745 [220, 221],
  f3753 r3751 [222, 221],
  f3755 r3754 [223, 210],
  f1336 r1314 [],
  f3766 r3756 [225],
  f3700 r3696 [],
  f3771 r3767 [226, 227],
  f3791 r3782 [],
  f3791 r3792 [229],
  f3796 r3793 [228, 230],
  f3799 r3797 [231, 224],
  f3806 r3802 [],
  f3813 r3807 [232, 233],
  f3826 r3820 [],
  f3835 r3830 [235],
  f3845 r3841 [],
  f3850 r3846 [237],
  f3700 r3696 [],
  f3856 r3851 [238, 239],
  f3865 r3861 [],
  f3865 r3866 [241],
  f3870 r3867 [240, 242],
  f3874 r3871 [236, 243],
  f725 r716 [],
  f3879 r3875 [245, 244],
  f3884 r3881 [],
  f3890 r3885 [246, 247],
  f3893 r3891 [248, 247],
  f2179 r2175 [],
  f3900 r3894 [250],
  f3845 r3841 [],
  f3905 r3901 [252],
  f2207 r2203 [],
  f3911 r3906 [253, 254],
  f3865 r3861 [],
  f3916 r3912 [256],
  f3920 r3917 [255, 257],
  f3924 r3921 [251, 258],
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
  f3964 r3960 [],
  f777 r773 [],
  f3968 r3965 [275, 277],
  f777 r773 [],
  f3932 r3969 [274, 279],
  f3976 r3970 [276, 278],
  f3983 r3977 [281, 280],
  f4021 r3984 [282],
  f1336 r1314 [],
  f4067 r4026 [284],
  f3700 r3696 [],
  f4074 r4068 [285, 286],
  f4097 r4088 [],
  f4102 r4098 [288],
  f4106 r4103 [287, 289],
  f725 r716 [],
  f4112 r4107 [291, 290],
  f4117 r4114 [],
  f4123 r4118 [292, 293],
  f4126 r4124 [294, 293],
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
  f4152 r4148 [],
  f4158 r4153 [308],
  f1874 r1868 [],
  f4165 r4159 [310],
  f3700 r3696 [],
  f4171 r4166 [311, 312],
  f4182 r4178 [],
  f4187 r4183 [314],
  f4191 r4188 [313, 315],
  f4195 r4192 [309, 316],
  f725 r716 [],
  f4200 r4196 [318, 317],
  f4205 r4202 [],
  f4211 r4206 [319, 320],
  f4214 r4212 [321, 320],
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
  f4229 r4226 [],
  f4235 r4230 [336, 337],
  f4238 r4236 [338, 337],
  f777 r773 [],
  f4240 r4239 [339, 340],
  f4244 r4241 [296, 341],
  f2342 r2313 [],
  f4255 r4245 [343],
  f3700 r3696 [],
  f4262 r4256 [344, 345],
  f4280 r4273 [],
  f4285 r4281 [347],
  f4289 r4286 [346, 348],
  f725 r716 [],
  f4295 r4290 [350, 349],
  f4300 r4297 [],
  f4306 r4301 [351, 352],
  f4309 r4307 [353, 352],
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
  f4366 r4353 [368],
  f4300 r4297 [],
  f4373 r4367 [369, 370],
  f4394 r4386 [],
  f4403 r4399 [372],
  f4407 r4404 [371, 373],
  f725 r716 [],
  f4413 r4408 [375, 374],
  f4418 r4415 [],
  f4424 r4419 [376, 377],
  f4427 r4425 [378, 377],
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
  f4455 r4451 [],
  f4461 r4456 [392],
  f1874 r1868 [],
  f4468 r4462 [394],
  f4300 r4297 [],
  f4474 r4469 [395, 396],
  f4485 r4481 [],
  f4490 r4486 [398],
  f4494 r4491 [397, 399],
  f4498 r4495 [393, 400],
  f725 r716 [],
  f4503 r4499 [402, 401],
  f4508 r4505 [],
  f4514 r4509 [403, 404],
  f4517 r4515 [405, 404],
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
  f4530 r4529 [],
  f4536 r4531 [420, 421],
  f4539 r4537 [422, 421],
  f777 r773 [],
  f4541 r4540 [423, 424],
  f4545 r4542 [380, 425],
  f2342 r2313 [],
  f4556 r4546 [427],
  f4300 r4297 [],
  f4563 r4557 [428, 429],
  f4581 r4574 [],
  f4586 r4582 [431],
  f4590 r4587 [430, 432],
  f725 r716 [],
  f4596 r4591 [434, 433],
  f4601 r4598 [],
  f4607 r4602 [435, 436],
  f4610 r4608 [437, 436],
  f4612 r4611 [438, 426],
  f777 r773 [],
  f4616 r4613 [439, 440],
  f4621 r4617 [441],
  f4634 r4628 [],
  f4641 r4638 [443],
  f725 r716 [],
  f4646 r4642 [445, 444],
  f2635 r3565 [],
  f4651 r4647 [446, 447],
  f4654 r4652 [448, 447],
  f4656 r4655 [449, 442],
  f2342 r2313 [],
  f3591 r3581 [451],
  f759 r2249 [],
  f3598 r3592 [452, 453],
  f3616 r3609 [],
  f3621 r3617 [455],
  f3625 r3622 [454, 456],
  f3580 r4657 [457, 196],
  f725 r716 [],
  f4661 r4658 [459, 458],
  f3283 r3280 [],
  f4666 r4662 [460, 461],
  f4669 r4667 [462, 461],
  f4671 r4670 [463, 450],
  f1336 r1314 [],
  f3162 r2925 [465],
  f759 r2249 [],
  f3169 r3163 [466, 467],
  f3263 r3255 [],
  f3268 r3264 [469],
  f3272 r3269 [468, 470],
  f4673 r4672 [471, 464],
  f3806 r3802 [],
  f4679 r4674 [472, 473],
  f3324 r3320 [],
  f4685 r4680 [475],
  f3845 r3841 [],
  f4690 r4686 [477],
  f759 r2249 [],
  f4696 r4691 [478, 479],
  f3865 r3861 [],
  f4701 r4697 [481],
  f4705 r4702 [480, 482],
  f4709 r4706 [476, 483],
  f725 r716 [],
  f4714 r4710 [485, 484],
  f4719 r4716 [],
  f4725 r4720 [486, 487],
  f4728 r4726 [488, 487],
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
  f4732 r4729 [489, 474],
  f4734 r4733 [500, 499],
  f725 r716 [],
  f4736 r4735 [502, 501],
  f759 r2249 [],
  f4738 r4737 [503, 504],
  f4740 r4739 [505, 504],
  f777 r773 [],
  f4742 r4741 [506, 507],
  f2342 r2313 [],
  f2353 r2343 [509],
  f737 r734 [],
  f2360 r2354 [510, 511],
  f2389 r2382 [],
  f2394 r2390 [513],
  f2398 r2395 [512, 514],
  f2264 r4743 [515, 95],
  f725 r716 [],
  f4747 r4744 [517, 516],
  f1789 r1786 [],
  f4752 r4748 [518, 519],
  f4755 r4753 [520, 519],
  f4757 r4756 [521, 508],
  f1336 r1314 [],
  f1654 r1408 [523],
  f737 r734 [],
  f1661 r1655 [524, 525],
  f1766 r1757 [],
  f1774 r1770 [527],
  f1778 r1775 [526, 528],
  f4759 r4758 [529, 522],
  f3806 r3802 [],
  f4765 r4760 [530, 531],
  f1852 r1848 [],
  f4771 r4766 [533],
  f3845 r3841 [],
  f4776 r4772 [535],
  f737 r734 [],
  f4782 r4777 [536, 537],
  f3865 r3861 [],
  f4787 r4783 [539],
  f4791 r4788 [538, 540],
  f4795 r4792 [534, 541],
  f725 r716 [],
  f4800 r4796 [543, 542],
  f4805 r4802 [],
  f4811 r4806 [544, 545],
  f4814 r4812 [546, 545],
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
  f4818 r4815 [547, 532],
  f4820 r4819 [558, 557],
  f725 r716 [],
  f4824 r4821 [560, 559],
  f737 r734 [],
  f4829 r4825 [561, 562],
  f4832 r4830 [563, 562],
  f777 r773 [],
  f4834 r4833 [564, 565]
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
