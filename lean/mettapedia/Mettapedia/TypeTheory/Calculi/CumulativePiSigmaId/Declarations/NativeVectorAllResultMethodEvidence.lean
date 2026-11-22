import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllResultAssembly
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorReplayTemplates

/-! Generated finite evidence; independently replayed by the checking companion. -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.Assembly.Evidence
open Presentation Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorReplayTemplates

private abbrev S (n : Nat) := StructuralConversionCode.StepCode Tower.Head decoder.Code n
private abbrev C (n : Nat) := StructuralConversionCode.Code Tower.Head decoder.Code n
private abbrev T (n : Nat) := StructuralTypingReplay.Code Tower.Head C n
private abbrev X (n : Nat) := StructuralTypingReplay.ContextCode Tower.Head C n

private def e3 : X 1 :=
.snoc (replay_844b001091b2055dfd9d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d9099ae41a1c6a1cb998) (replay_7a268c731e7a9afff236)

private def e6 : X 2 :=
.snoc (e3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd68df30b6526d2aba98) (replay_2ec113d8b40f7f163a79)

private def e10 : X 3 :=
.snoc (e6) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (replay_2a0decba183f967a7699)

private def e26 : X 4 :=
.snoc (e10) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (replay_be261adb759aa3486f8c)

private def e156 : T 6 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebe6539c4b4eb6ba35d4) (replay_6bde1c8708a73cc59d36)

private def e157 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_39e100ccd2d3487475a1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7016e26b82e148b9a138) (e156) (replay_fb92de9ad2d284eba393)

private def e165 : T 7 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c4be6c23d1c5d52d32e2) (replay_d46b9e98b3e6a82d2405) (replay_364e906c32a1fece265a)

private def e166 : T 6 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0b123886a2f1ca52dc20) (replay_811c48c79398f6d0dc39) (e165)

private def e168 : T 8 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eca3dc2b6caf4867e1d4) (replay_364e906c32a1fece265a)

private def e169 : T 7 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0b123886a2f1ca52dc20) (e165) (e168)

private def e170 : T 6 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7c74dd6d73ced3b4686) (e166) (e169)

private def e171 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e11e484bc56d77ac660e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fa43449128fc9673bc03) (e157) (e170)

private def e196 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eca3dc2b6caf4867e1d4) (replay_18e264ae7443180c79f8) (replay_b7b0d4f9c05076ab70ae)

private def e197 : T 8 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5fcd81028f8a0038e5e4) (replay_b0145ff60fc18bc29654) (e196)

private def e198 : T 7 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_088ec0f4742a888f4d7e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b237fdc24d2997bfa210) (replay_ef66033bccd33ddfc79b) (e197)

private def e199 : T 6 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eca3dc2b6caf4867e1d4) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b1a28e9d42d7f3e26777) (replay_ff33acd87c5b03c2f11e) (e198)

private def e200 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d44a3b8e82eed410af2f)

private def e201 : C 6 :=
.trans (e200) (e200)

private def e204 : S 6 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d146da0d1a9ab720cb6e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_07a1d7b4a030d2d416f2)

private def e206 : S 6 :=
.congAppFun (e204) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c29849df4a7f3412755d)

private def e208 : S 6 :=
.congPiDom (e206) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_92df12845a93a3adda6b)

private def e209 : C 6 :=
.single (e208)

private def e211 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_af3d43a7e754f8874e67)

private def e212 : C 6 :=
.trans (e209) (e211)

private def e213 : C 6 :=
.trans (e201) (e212)

private def e214 : C 6 :=
.trans (e213) (e211)

private def e215 : S 6 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7055a000b335b678e2ab) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c29849df4a7f3412755d)

private def e216 : S 6 :=
.congPiDom (e215) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_92df12845a93a3adda6b)

private def e217 : C 6 :=
.single (e216)

private def e219 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3806b9509ccb0f03f985)

private def e220 : C 6 :=
.trans (e217) (e219)

private def e221 : C 6 :=
.trans (e214) (e220)

private def e222 : C 6 :=
.symm (e219)

private def e223 : C 6 :=
.trans (e219) (e222)

private def e224 : C 6 :=
.trans (e221) (e223)

private def e225 : C 6 :=
.trans (e219) (e219)

private def e230 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3d14aa0ee1750cdf2678) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_05b075e7750afd998d8f)

private def e232 : S 10 :=
.congAppFun (e230) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b6263f8b29eb9d152bde)

private def e234 : S 10 :=
.congPiDom (e232) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c2e3450cdd2fc60e5bba)

private def e235 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53047c3473acacee0b84) (e234)

private def e236 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ed88dce83fa3ae5d4c4a) (e235)

private def e237 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (e236)

private def e239 : S 7 :=
.congPiDom (e237) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3dc40a95e5211ebc606d)

private def e240 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e4f6621568ccac500dc) (e239)

private def e241 : C 6 :=
.single (e240)

private def e243 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4b301fee20d48430e4e1)

private def e244 : C 6 :=
.trans (e241) (e243)

private def e245 : C 6 :=
.trans (e225) (e244)

private def e246 : C 6 :=
.trans (e245) (e243)

private def e248 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c4973f6eacdd028898bc) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b6263f8b29eb9d152bde)

private def e249 : S 10 :=
.congPiDom (e248) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c2e3450cdd2fc60e5bba)

private def e250 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53047c3473acacee0b84) (e249)

private def e251 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ed88dce83fa3ae5d4c4a) (e250)

private def e252 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (e251)

private def e253 : S 7 :=
.congPiDom (e252) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3dc40a95e5211ebc606d)

private def e254 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e4f6621568ccac500dc) (e253)

private def e255 : C 6 :=
.single (e254)

private def e257 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_65a3bf5f661897ba5d39)

private def e258 : C 6 :=
.trans (e255) (e257)

private def e259 : C 6 :=
.trans (e246) (e258)

private def e260 : C 6 :=
.symm (e257)

private def e261 : C 6 :=
.trans (e257) (e260)

private def e262 : C 6 :=
.trans (e259) (e261)

private def e263 : C 6 :=
.trans (e257) (e257)

private def e267 : S 11 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a8c8fc618452e2baa732) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1c1bdd3d0533bd5ac753)

private def e269 : S 11 :=
.congAppFun (e267) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43b596ae32b4a7f59f6a)

private def e270 : S 10 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_307e4da5e86f9f55da07) (e269)

private def e271 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53047c3473acacee0b84) (e270)

private def e272 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ed88dce83fa3ae5d4c4a) (e271)

private def e273 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (e272)

private def e274 : S 7 :=
.congPiDom (e273) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3dc40a95e5211ebc606d)

private def e275 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e4f6621568ccac500dc) (e274)

private def e276 : C 6 :=
.single (e275)

private def e278 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4c8284247228ed8cc579)

private def e279 : C 6 :=
.trans (e276) (e278)

private def e280 : C 6 :=
.trans (e263) (e279)

private def e281 : C 6 :=
.trans (e280) (e278)

private def e283 : S 11 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1f7880e8737675c0efb8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43b596ae32b4a7f59f6a)

private def e284 : S 10 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_307e4da5e86f9f55da07) (e283)

private def e285 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53047c3473acacee0b84) (e284)

private def e286 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ed88dce83fa3ae5d4c4a) (e285)

private def e287 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (e286)

private def e288 : S 7 :=
.congPiDom (e287) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3dc40a95e5211ebc606d)

private def e289 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e4f6621568ccac500dc) (e288)

private def e290 : C 6 :=
.single (e289)

private def e292 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c1e84873387dfd463aa7)

private def e293 : C 6 :=
.trans (e290) (e292)

private def e294 : C 6 :=
.trans (e281) (e293)

private def e295 : C 6 :=
.symm (e292)

private def e296 : C 6 :=
.trans (e292) (e295)

private def e297 : C 6 :=
.trans (e294) (e296)

private def e298 : C 6 :=
.trans (e262) (e297)

private def e299 : C 6 :=
.trans (e298) (e295)

private def e300 : C 6 :=
.trans (e219) (e299)

private def e301 : C 6 :=
.trans (e219) (e300)

private def e302 : C 6 :=
.trans (e301) (e295)

private def e303 : C 6 :=
.trans (e219) (e302)

private def e304 : C 6 :=
.trans (e219) (e303)

private def e305 : C 6 :=
.trans (e304) (e295)

private def e306 : C 6 :=
.trans (e219) (e305)

private def e307 : C 6 :=
.trans (e219) (e306)

private def e308 : C 6 :=
.trans (e307) (e295)

private def e309 : C 6 :=
.trans (e219) (e308)

private def e310 : C 6 :=
.trans (e292) (e292)

private def e314 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3d14aa0ee1750cdf2678) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2c3a73b45b381f28af93)

private def e315 : S 10 :=
.congAppFun (e314) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b6263f8b29eb9d152bde)

private def e316 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_28ef38dcd249a3861739) (e315)

private def e317 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56760c9c60918cbf3d6f) (e316)

private def e318 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_60ec318a62e44b6c9d5f) (e317)

private def e319 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e4f6621568ccac500dc) (e318)

private def e320 : C 6 :=
.single (e319)

private def e322 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_15a34ea6fc1bef5d0eec)

private def e323 : C 6 :=
.trans (e320) (e322)

private def e324 : C 6 :=
.trans (e310) (e323)

private def e325 : C 6 :=
.trans (e324) (e322)

private def e326 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_28ef38dcd249a3861739) (e248)

private def e327 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56760c9c60918cbf3d6f) (e326)

private def e328 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_60ec318a62e44b6c9d5f) (e327)

private def e329 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e4f6621568ccac500dc) (e328)

private def e330 : C 6 :=
.single (e329)

private def e332 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f5238981d0f24cf2f79e)

private def e333 : C 6 :=
.trans (e330) (e332)

private def e334 : C 6 :=
.trans (e325) (e333)

private def e335 : C 6 :=
.symm (e332)

private def e336 : C 6 :=
.trans (e332) (e335)

private def e337 : C 6 :=
.trans (e334) (e336)

private def e338 : C 6 :=
.trans (e292) (e337)

private def e339 : C 6 :=
.trans (e338) (e335)

private def e340 : C 6 :=
.trans (e292) (e339)

private def e341 : C 6 :=
.trans (e292) (e340)

private def e342 : C 6 :=
.trans (e341) (e335)

private def e343 : C 6 :=
.trans (e292) (e342)

private def e344 : C 6 :=
.trans (e309) (e343)

private def e345 : C 6 :=
.trans (e344) (e335)

private def e346 : C 6 :=
.trans (e219) (e345)

private def e347 : C 6 :=
.trans (e224) (e346)

private def e348 : C 6 :=
.trans (e347) (e335)

private def e349 : C 6 :=
.trans (e200) (e348)

private def e350 : T 6 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d44a3b8e82eed410af2f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fa34719ab4861ce3b645) (e171) (e199) (e349)

private def e352 : T 6 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (replay_811c48c79398f6d0dc39) (replay_f690a064aabb944975e0) (replay_f690a064aabb944975e0)

private def e353 : T 6 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (e352)

private def e354 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e4f6621568ccac500dc) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b57fae7b4fab92b5ea7) (e350) (e353)

private def e360 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eca3dc2b6caf4867e1d4) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eca3dc2b6caf4867e1d4) (replay_cf26163fe59a0dbcc31b) (replay_b7b0d4f9c05076ab70ae)

private def e361 : T 8 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7646540dd7e659fc407) (replay_3e07c8af8123696e3523) (e360)

private def e362 : T 7 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e1d07338c040d26dff49) (replay_e197ee63c3c9ea3d9b51) (e361)

private def e363 : T 6 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7e6cb354a8df3738086) (replay_811c48c79398f6d0dc39) (e362)

private def e370 : T 10 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd68df30b6526d2aba98) (replay_8dd06e568960d2567ea5) (replay_e78213c920befa21e944)

private def e372 : T 10 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_80d7abfcb57830595ef4) (e370) (replay_7fbeba8818273106d8c8)

private def e373 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43d55c8961861bb41778) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e8e4b831c3ede895f4ee) (e372) (replay_8dd06e568960d2567ea5)

private def e374 : T 10 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e373) (replay_7fbeba8818273106d8c8)

private def e375 : T 10 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b8578195b133fac70a1) (e374)

private def e376 : T 9 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7646540dd7e659fc407) (e360) (e375)

private def e377 : T 8 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e1d07338c040d26dff49) (e361) (e376)

private def e378 : T 7 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7e6cb354a8df3738086) (e362) (e377)

private def e379 : T 6 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_088ec0f4742a888f4d7e) (e363) (e378)

private def e380 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_75331d7791745b76e4ef) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ae4f42e3a7f47cd6d362) (e354) (e379)

private def e381 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2ac9d2a7e8083e27f05a) (e380) (replay_fb92de9ad2d284eba393)

private def e382 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea1e125d0ec89812d6af) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7055a000b335b678e2ab) (e381) (replay_fb92de9ad2d284eba393)

private def e390 : T 7 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (replay_e197ee63c3c9ea3d9b51)

private def e391 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7055a000b335b678e2ab) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0ef4b34943d70aaa2195) (replay_ce283a65c0631acae2f9) (e390)

private def e392 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_463cd5d893fe98804d67) (e391) (replay_e197ee63c3c9ea3d9b51)

private def e447 : C 4 :=
.trans (replay_22fcd52f36d27eb68401) (replay_ca60108fe6e223d68618)

private def e454 : C 4 :=
.trans (e447) (replay_412ad41ccb6b083dfc2a)

private def e455 : C 4 :=
.symm (replay_e28d47ca058d4a30f082)

private def e456 : C 4 :=
.trans (replay_e28d47ca058d4a30f082) (e455)

private def e457 : C 4 :=
.trans (e454) (e456)

private def e493 : C 4 :=
.symm (replay_3b9114e3e22667e336ee)

private def e494 : C 4 :=
.trans (replay_3b9114e3e22667e336ee) (e493)

private def e495 : C 4 :=
.trans (replay_a3b60ba0f451de1c571d) (e494)

private def e513 : C 4 :=
.trans (replay_61b63880132a7d929884) (replay_777728b99bb48d5639d4)

private def e514 : C 4 :=
.trans (e513) (replay_8624ae8f1896ec0b7635)

private def e527 : C 4 :=
.trans (e514) (replay_16529f17a5de5d3877bf)

private def e528 : C 4 :=
.symm (replay_6e788303dab2203fc3cc)

private def e529 : C 4 :=
.trans (replay_6e788303dab2203fc3cc) (e528)

private def e530 : C 4 :=
.trans (e527) (e529)

private def e531 : C 4 :=
.trans (e495) (e530)

private def e532 : C 4 :=
.trans (e531) (e528)

private def e533 : C 4 :=
.trans (replay_e28d47ca058d4a30f082) (e532)

private def e534 : C 4 :=
.trans (replay_e28d47ca058d4a30f082) (e533)

private def e535 : C 4 :=
.trans (e534) (e528)

private def e536 : C 4 :=
.trans (replay_e28d47ca058d4a30f082) (e535)

private def e537 : C 4 :=
.trans (replay_e28d47ca058d4a30f082) (e536)

private def e538 : C 4 :=
.trans (e537) (e528)

private def e539 : C 4 :=
.trans (replay_e28d47ca058d4a30f082) (e538)

private def e540 : C 4 :=
.trans (replay_e28d47ca058d4a30f082) (e539)

private def e541 : C 4 :=
.trans (e540) (e528)

private def e542 : C 4 :=
.trans (replay_e28d47ca058d4a30f082) (e541)

private def e568 : C 4 :=
.symm (replay_f4d774c5fbc1c3c8e18a)

private def e569 : C 4 :=
.trans (replay_f4d774c5fbc1c3c8e18a) (e568)

private def e570 : C 4 :=
.trans (replay_5b44aa3019758da7b6a5) (e569)

private def e571 : C 4 :=
.trans (replay_6e788303dab2203fc3cc) (e570)

private def e572 : C 4 :=
.trans (e571) (e568)

private def e573 : C 4 :=
.trans (replay_6e788303dab2203fc3cc) (e572)

private def e574 : C 4 :=
.trans (replay_6e788303dab2203fc3cc) (e573)

private def e575 : C 4 :=
.trans (e574) (e568)

private def e576 : C 4 :=
.trans (replay_6e788303dab2203fc3cc) (e575)

private def e577 : C 4 :=
.trans (e542) (e576)

private def e578 : C 4 :=
.trans (e577) (e568)

private def e579 : C 4 :=
.trans (replay_e28d47ca058d4a30f082) (e578)

private def e580 : C 4 :=
.trans (e457) (e579)

private def e581 : C 4 :=
.trans (e580) (e568)

private def e582 : C 4 :=
.trans (replay_89f2ff6b5cda72ace594) (e581)

private def e583 : T 4 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_401061806bcf8f317749) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_404b5de2e790e15a378c) (replay_96641d66eb368f59f29a) (replay_b41d017dd3808b1d0a20) (e582)

private def e587 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b85ac78fceba4809d7ed) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c4927d7ed31f637c42bd) (e583) (replay_74ee98dff50bb31e1ba0)

private def e608 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a08b915b3440d750f218) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_637e2208361746e72f13) (e587) (replay_93519d0d617524026cb7)

private def e609 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d7626e99262c9e21ec07) (e608) (replay_f89a0d3fd4af1bf7786d)

private def e610 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d2fe1eb531662373187) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c070633b7877d5417c64) (e609) (replay_f89a0d3fd4af1bf7786d)

private def e617 : T 4 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e610) (replay_ab222404a1b298e073e0)

private def e618 : T 3 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_897db4146fa986a8835c) (replay_be261adb759aa3486f8c) (e617)

private def e619 : T 2 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8ff6182553f1ec326b3b) (replay_2a0decba183f967a7699) (e618)

private def e620 : T 1 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd68df30b6526d2aba98) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_51eec7f52bc4a38ae682) (replay_2ec113d8b40f7f163a79) (e619)

private def e621 : T 0 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d9099ae41a1c6a1cb998) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7aa05895bba95790d433) (replay_7a268c731e7a9afff236) (e620)

private def e622 : T 7 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd72d6a3055c3dc99790) (e621)

private def e623 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d064c25dd26291905510) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_20a94ea8338ebcab79f3) (e622) (replay_e197ee63c3c9ea3d9b51)

private def e624 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cce8a3ce3397a9d6a0fb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_882d6b56834a7cc595c6) (e623) (replay_e197ee63c3c9ea3d9b51)

private def e625 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56572cec585184e29862) (e624) (replay_e197ee63c3c9ea3d9b51)

private def e626 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_61babc0a06ef8aba8578) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bda5d9afbc1daa58bcc) (e625) (replay_e197ee63c3c9ea3d9b51)

private def e637 : T 1 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd68df30b6526d2aba98) (replay_579b334deaab55db1c09) (replay_7b7ffdffff88fd07525e)

private def e670 : C 4 :=
.trans (replay_4917577ee7a963f4d446) (replay_332cb53a039cc4844568)

private def e677 : C 4 :=
.trans (e670) (replay_343f3582a5e6fcc35c51)

private def e678 : C 4 :=
.symm (replay_1ef9e98b5d957b34501c)

private def e679 : C 4 :=
.trans (replay_1ef9e98b5d957b34501c) (e678)

private def e680 : C 4 :=
.trans (e677) (e679)

private def e712 : C 4 :=
.symm (replay_df5039f7aebf0d6fee20)

private def e713 : C 4 :=
.trans (replay_df5039f7aebf0d6fee20) (e712)

private def e714 : C 4 :=
.trans (replay_12edbc43fc88433183d9) (e713)

private def e729 : C 4 :=
.trans (replay_87dc56f04aa29f132622) (replay_155efaaa5a4dfc7ab61f)

private def e730 : C 4 :=
.trans (e729) (replay_79fb5d93c6220bf677bb)

private def e742 : C 4 :=
.trans (e730) (replay_db01122b6caabf57215f)

private def e743 : C 4 :=
.symm (replay_3b8a18202ea4d77970ef)

private def e744 : C 4 :=
.trans (replay_3b8a18202ea4d77970ef) (e743)

private def e745 : C 4 :=
.trans (e742) (e744)

private def e746 : C 4 :=
.trans (e714) (e745)

private def e747 : C 4 :=
.trans (e746) (e743)

private def e748 : C 4 :=
.trans (replay_1ef9e98b5d957b34501c) (e747)

private def e749 : C 4 :=
.trans (replay_1ef9e98b5d957b34501c) (e748)

private def e750 : C 4 :=
.trans (e749) (e743)

private def e751 : C 4 :=
.trans (replay_1ef9e98b5d957b34501c) (e750)

private def e752 : C 4 :=
.trans (replay_1ef9e98b5d957b34501c) (e751)

private def e753 : C 4 :=
.trans (e752) (e743)

private def e754 : C 4 :=
.trans (replay_1ef9e98b5d957b34501c) (e753)

private def e755 : C 4 :=
.trans (replay_1ef9e98b5d957b34501c) (e754)

private def e756 : C 4 :=
.trans (e755) (e743)

private def e757 : C 4 :=
.trans (replay_1ef9e98b5d957b34501c) (e756)

private def e781 : C 4 :=
.symm (replay_351d109bc2376943f6b7)

private def e782 : C 4 :=
.trans (replay_351d109bc2376943f6b7) (e781)

private def e783 : C 4 :=
.trans (replay_f2925321eb8effe818ab) (e782)

private def e784 : C 4 :=
.trans (replay_3b8a18202ea4d77970ef) (e783)

private def e785 : C 4 :=
.trans (e784) (e781)

private def e786 : C 4 :=
.trans (replay_3b8a18202ea4d77970ef) (e785)

private def e787 : C 4 :=
.trans (replay_3b8a18202ea4d77970ef) (e786)

private def e788 : C 4 :=
.trans (e787) (e781)

private def e789 : C 4 :=
.trans (replay_3b8a18202ea4d77970ef) (e788)

private def e790 : C 4 :=
.trans (e757) (e789)

private def e791 : C 4 :=
.trans (e790) (e781)

private def e792 : C 4 :=
.trans (replay_1ef9e98b5d957b34501c) (e791)

private def e793 : C 4 :=
.trans (e680) (e792)

private def e794 : C 4 :=
.trans (e793) (e781)

private def e795 : C 4 :=
.trans (replay_82c598fa0a37dcdd0491) (e794)

private def e796 : T 4 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58fe618fc0a2e1e6f45e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fa34719ab4861ce3b645) (replay_f2e3de18fedd0b401227) (replay_94a3b7ece31e420af80f) (e795)

private def e797 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ef6e0e4f36d08ea7d9c5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ce5473ba2d9a755014a2) (e796) (replay_74ee98dff50bb31e1ba0)

private def e802 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ed88dce83fa3ae5d4c4a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5185e3c12dc65a8f34dd) (replay_534aece673191f529e08) (replay_534aece673191f529e08)

private def e803 : T 8 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e802) (replay_07c41680d17703d7171f)

private def e804 : T 8 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b8578195b133fac70a1) (e803)

private def e805 : T 7 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7646540dd7e659fc407) (replay_85991d854c553f3e4785) (e804)

private def e806 : T 6 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e1d07338c040d26dff49) (replay_99250ba2c83e1ee4203c) (e805)

private def e807 : T 5 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7e6cb354a8df3738086) (replay_8850b683f58bf593247f) (e806)

private def e808 : T 4 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_088ec0f4742a888f4d7e) (replay_a9c796b8ff0163b24c93) (e807)

private def e809 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38dcfc071d8c128428ec) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_305ed71e288652e70783) (e797) (e808)

private def e810 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b35f427e4a9d98e9180b) (e809) (replay_f89a0d3fd4af1bf7786d)

private def e811 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d2fe1eb531662373187) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a27060780ae3276936d3) (e810) (replay_f89a0d3fd4af1bf7786d)

private def e825 : T 6 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0b123886a2f1ca52dc20) (replay_40a4e5b94fc0e4e4dda6) (replay_4ec057243fb248f73891)

private def e826 : T 5 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7c74dd6d73ced3b4686) (replay_3b2208d0e18866e8bf53) (e825)

private def e827 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_df0f30f1ec3dce3eb86a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d9b222a9ccd79e463a7a) (replay_6b2965139ed23ce2e3db) (e826)

private def e828 : T 5 :=
.headType

private def e829 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4f93e456b4620d589d9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4f93e456b4620d589d9) (replay_cf26163fe59a0dbcc31b) (replay_b7b0d4f9c05076ab70ae)

private def e830 : T 8 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d3bc479f5fb249b99ac2) (replay_3e07c8af8123696e3523) (e829)

private def e831 : T 7 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c6b51e3ba4892036cdb0) (replay_e197ee63c3c9ea3d9b51) (e830)

private def e832 : T 6 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_45e80a32c899dfd6b11b) (replay_811c48c79398f6d0dc39) (e831)

private def e833 : T 8 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4f93e456b4620d589d9) (replay_3e07c8af8123696e3523) (replay_cf26163fe59a0dbcc31b)

private def e834 : T 7 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8d299427678534d5d57c) (replay_0432db7c6e4e1e541d38) (e833)

private def e835 : T 6 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fafdfa0063130741b0e7) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_196d73933a2b663cb491) (e832) (e834)

private def e836 : T 5 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4f93e456b4620d589d9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6aabb8dd5a1429128d77) (e828) (e835)

private def e837 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eed3a546a0810a4bb37)

private def e838 : C 5 :=
.trans (e837) (e837)

private def e841 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3945e65c35a525e9e92c) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_10a09856ff4a49f9d49f)

private def e843 : S 5 :=
.congAppFun (e841) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e845 : S 5 :=
.congPiDom (e843) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_30a1857aa99a4f7a1b30)

private def e846 : C 5 :=
.single (e845)

private def e848 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f9c6c18220641a056f61)

private def e849 : C 5 :=
.trans (e846) (e848)

private def e850 : C 5 :=
.trans (e838) (e849)

private def e851 : C 5 :=
.trans (e850) (e848)

private def e852 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e90387a90b9c8c3c4369) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e853 : S 5 :=
.congPiDom (e852) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_30a1857aa99a4f7a1b30)

private def e854 : C 5 :=
.single (e853)

private def e856 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d7c61d582e0a67467eed)

private def e857 : C 5 :=
.trans (e854) (e856)

private def e858 : C 5 :=
.trans (e851) (e857)

private def e859 : C 5 :=
.symm (e856)

private def e860 : C 5 :=
.trans (e856) (e859)

private def e861 : C 5 :=
.trans (e858) (e860)

private def e862 : C 5 :=
.trans (e856) (e856)

private def e865 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cd5320a4a07f9b6b73ff) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e867 : S 9 :=
.congAppFun (e865) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e869 : S 9 :=
.congPiDom (e867) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_03273856e13319178171)

private def e870 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_369043ee55c31306fc04) (e869)

private def e871 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca) (e870)

private def e872 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) (e871)

private def e874 : S 6 :=
.congPiDom (e872) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5656c0a1e40d2d0adb93)

private def e875 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c070633b7877d5417c64) (e874)

private def e876 : C 5 :=
.single (e875)

private def e878 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0d8bd56cff3673ff270f)

private def e879 : C 5 :=
.trans (e876) (e878)

private def e880 : C 5 :=
.trans (e862) (e879)

private def e881 : C 5 :=
.trans (e880) (e878)

private def e882 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_683a421a2ec88ad82286) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e883 : S 9 :=
.congPiDom (e882) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_03273856e13319178171)

private def e884 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_369043ee55c31306fc04) (e883)

private def e885 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca) (e884)

private def e886 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) (e885)

private def e887 : S 6 :=
.congPiDom (e886) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5656c0a1e40d2d0adb93)

private def e888 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c070633b7877d5417c64) (e887)

private def e889 : C 5 :=
.single (e888)

private def e891 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b92fee645f17413bf30d)

private def e892 : C 5 :=
.trans (e889) (e891)

private def e893 : C 5 :=
.trans (e881) (e892)

private def e894 : C 5 :=
.symm (e891)

private def e895 : C 5 :=
.trans (e891) (e894)

private def e896 : C 5 :=
.trans (e893) (e895)

private def e897 : C 5 :=
.trans (e891) (e891)

private def e900 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cc7edc238326af0e3cee) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_29e6362be00331af1526)

private def e902 : S 10 :=
.congAppFun (e900) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd8f671c52437c194141)

private def e903 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23593caaab521d12b976) (e902)

private def e904 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_369043ee55c31306fc04) (e903)

private def e905 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca) (e904)

private def e906 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) (e905)

private def e907 : S 6 :=
.congPiDom (e906) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5656c0a1e40d2d0adb93)

private def e908 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c070633b7877d5417c64) (e907)

private def e909 : C 5 :=
.single (e908)

private def e911 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1f8e5cdbf3ca1d030b77)

private def e912 : C 5 :=
.trans (e909) (e911)

private def e913 : C 5 :=
.trans (e897) (e912)

private def e914 : C 5 :=
.trans (e913) (e911)

private def e916 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_df96c216643bb607dff9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd8f671c52437c194141)

private def e917 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23593caaab521d12b976) (e916)

private def e918 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_369043ee55c31306fc04) (e917)

private def e919 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca) (e918)

private def e920 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) (e919)

private def e921 : S 6 :=
.congPiDom (e920) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5656c0a1e40d2d0adb93)

private def e922 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c070633b7877d5417c64) (e921)

private def e923 : C 5 :=
.single (e922)

private def e925 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6e6096956e837ec73fb5)

private def e926 : C 5 :=
.trans (e923) (e925)

private def e927 : C 5 :=
.trans (e914) (e926)

private def e928 : C 5 :=
.symm (e925)

private def e929 : C 5 :=
.trans (e925) (e928)

private def e930 : C 5 :=
.trans (e927) (e929)

private def e931 : C 5 :=
.trans (e896) (e930)

private def e932 : C 5 :=
.trans (e931) (e928)

private def e933 : C 5 :=
.trans (e856) (e932)

private def e934 : C 5 :=
.trans (e856) (e933)

private def e935 : C 5 :=
.trans (e934) (e928)

private def e936 : C 5 :=
.trans (e856) (e935)

private def e937 : C 5 :=
.trans (e856) (e936)

private def e938 : C 5 :=
.trans (e937) (e928)

private def e939 : C 5 :=
.trans (e856) (e938)

private def e940 : C 5 :=
.trans (e856) (e939)

private def e941 : C 5 :=
.trans (e940) (e928)

private def e942 : C 5 :=
.trans (e856) (e941)

private def e943 : C 5 :=
.trans (e925) (e925)

private def e947 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cd5320a4a07f9b6b73ff) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcc403caa19d1550c37)

private def e948 : S 9 :=
.congAppFun (e947) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e949 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c351605dcec825868e68) (e948)

private def e950 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (e949)

private def e951 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_569d8f7902f0377d05f7) (e950)

private def e952 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c070633b7877d5417c64) (e951)

private def e953 : C 5 :=
.single (e952)

private def e955 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0ea0b3b8212ec2f3fac4)

private def e956 : C 5 :=
.trans (e953) (e955)

private def e957 : C 5 :=
.trans (e943) (e956)

private def e958 : C 5 :=
.trans (e957) (e955)

private def e959 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c351605dcec825868e68) (e882)

private def e960 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (e959)

private def e961 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_569d8f7902f0377d05f7) (e960)

private def e962 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c070633b7877d5417c64) (e961)

private def e963 : C 5 :=
.single (e962)

private def e965 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_389990b5029e03a9f2a0)

private def e966 : C 5 :=
.trans (e963) (e965)

private def e967 : C 5 :=
.trans (e958) (e966)

private def e968 : C 5 :=
.symm (e965)

private def e969 : C 5 :=
.trans (e965) (e968)

private def e970 : C 5 :=
.trans (e967) (e969)

private def e971 : C 5 :=
.trans (e925) (e970)

private def e972 : C 5 :=
.trans (e971) (e968)

private def e973 : C 5 :=
.trans (e925) (e972)

private def e974 : C 5 :=
.trans (e925) (e973)

private def e975 : C 5 :=
.trans (e974) (e968)

private def e976 : C 5 :=
.trans (e925) (e975)

private def e977 : C 5 :=
.trans (e942) (e976)

private def e978 : C 5 :=
.trans (e977) (e968)

private def e979 : C 5 :=
.trans (e856) (e978)

private def e980 : C 5 :=
.trans (e861) (e979)

private def e981 : C 5 :=
.trans (e980) (e968)

private def e982 : C 5 :=
.trans (e837) (e981)

private def e983 : T 5 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eed3a546a0810a4bb37) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_404b5de2e790e15a378c) (e827) (e836) (e982)

private def e986 : T 5 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (replay_e8c0af6d55b0a0664088)

private def e987 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c070633b7877d5417c64) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_75fc559dd31e1b354316) (e983) (e986)

private def e990 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e2c1e2e15bb0cda87a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f1eda03ec62354b37392) (replay_07c41680d17703d7171f) (replay_07c41680d17703d7171f)

private def e991 : T 9 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (e990) (replay_8dd06e568960d2567ea5)

private def e992 : T 9 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_50d54f6ca4190fd6bc72) (e991)

private def e993 : T 8 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d3bc479f5fb249b99ac2) (replay_8036bcfeb0456385daaf) (e992)

private def e994 : T 7 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c6b51e3ba4892036cdb0) (replay_4a62f00bbd3e83841de6) (e993)

private def e995 : T 6 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_45e80a32c899dfd6b11b) (replay_5a7cceec38683602eacb) (e994)

private def e996 : T 5 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fafdfa0063130741b0e7) (replay_80aaec9f914651cac440) (e995)

private def e997 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_76cbbd042a63e503c23a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8a3ddd93b5dd8585de36) (e987) (e996)

private def e998 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3bd098284048916a723a) (e997) (replay_088a7fed4563d6a06e7a)

private def e999 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5331ca9ad2f18da19b3f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e90387a90b9c8c3c4369) (e998) (replay_088a7fed4563d6a06e7a)

private def e1000 : T 4 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (e811) (e999)

private def e1001 : T 3 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_740ec890a37b2842695e) (replay_be261adb759aa3486f8c) (e1000)

private def e1002 : T 2 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_958eb1fcf8807382497d) (replay_2a0decba183f967a7699) (e1001)

private def e1003 : T 1 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_80d7abfcb57830595ef4) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d290590ef4670695bc25) (e637) (e1002)

private def e1004 : T 0 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d9099ae41a1c6a1cb998) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_16fc13aa9e28f95869b3) (replay_7a268c731e7a9afff236) (e1003)

private def e1005 : T 7 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05b86c587b7291cc54) (e1004)

private def e1006 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d064c25dd26291905510) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b422fd9dac405e996ba9) (e1005) (replay_e197ee63c3c9ea3d9b51)

private def e1007 : T 7 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd68df30b6526d2aba98) (replay_e197ee63c3c9ea3d9b51) (replay_364e906c32a1fece265a)

private def e1008 : T 7 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_80d7abfcb57830595ef4) (e1007) (replay_534aece673191f529e08)

private def e1009 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_70aa1eb6b5fc777f1a97) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_393f1a4c93d4a984677d) (e1006) (e1008)

private def e1010 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1a7e215b2e10f9b6490e) (e1009) (replay_e197ee63c3c9ea3d9b51)

private def e1011 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_61babc0a06ef8aba8578) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_851fa6c145ef55c2208e) (e1010) (replay_e197ee63c3c9ea3d9b51)

private def e1012 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beaf96c439d2f4e74e7a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ca7f70fa5ba39fd3f253) (e1011) (replay_e197ee63c3c9ea3d9b51)

private def e1013 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_74251133736ce4f309d3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4771ebae3507c900a130) (e626) (e1012)

private def e1028 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38dcfc071d8c128428ec) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_305ed71e288652e70783) (e797) (replay_342a3e5c9d201e37271a)

private def e1029 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b35f427e4a9d98e9180b) (e1028) (replay_f89a0d3fd4af1bf7786d)

private def e1030 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d2fe1eb531662373187) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a27060780ae3276936d3) (e1029) (replay_f89a0d3fd4af1bf7786d)

private def e1031 : T 4 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1030) (replay_ab222404a1b298e073e0)

private def e1032 : T 3 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23e09003749289e9f868) (replay_be261adb759aa3486f8c) (e1031)

private def e1033 : T 2 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0d57e3d72177d769f8da) (replay_2a0decba183f967a7699) (e1032)

private def e1034 : T 1 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd68df30b6526d2aba98) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d49b64c606e9a898c42f) (replay_2ec113d8b40f7f163a79) (e1033)

private def e1035 : T 0 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d9099ae41a1c6a1cb998) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d7390df4c139c4a2ad89) (replay_7a268c731e7a9afff236) (e1034)

private def e1036 : T 7 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83f28e98241a6dba6c95) (e1035)

private def e1037 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d064c25dd26291905510) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9b196e7ac04b6e7e7096) (e1036) (replay_e197ee63c3c9ea3d9b51)

private def e1038 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cce8a3ce3397a9d6a0fb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f5ecc3527cb7fc5b117b) (e1037) (replay_e197ee63c3c9ea3d9b51)

private def e1039 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_857a0706292a503987bc) (e1038) (replay_e197ee63c3c9ea3d9b51)

private def e1040 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_61babc0a06ef8aba8578) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb95ad11973cf58b3d75) (e1039) (replay_e197ee63c3c9ea3d9b51)

private def e1041 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beaf96c439d2f4e74e7a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4771ebae3507c900a130) (e1040) (replay_e197ee63c3c9ea3d9b51)

private def e1042 : T 7 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e392) (e1013) (e1041)

private def e1043 : T 6 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e382) (e1042)

private def e1044 : T 6 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23e09003749289e9f868) (e1043)

private def e1045 : T 5 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0b123886a2f1ca52dc20) (replay_7dc6b8e83ee36a07c70d) (e1044)

private def e1046 : T 4 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7c74dd6d73ced3b4686) (replay_aec4c85cb0ac134bc5ba) (e1045)

private def e1048 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e4f6621568ccac500dc) (replay_f358fdbe24832d62b672) (replay_c88c45c22b9888b30470)

private def e1058 : T 5 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd72d6a3055c3dc99790) (e621)

private def e1059 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5978e1f6d4b31cb31598) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a20301261146c68a2bc3) (e1058) (replay_088a7fed4563d6a06e7a)

private def e1060 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a5c6fc596f7509be6eba) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7b5eff9df9b574500d25) (e1059) (replay_088a7fed4563d6a06e7a)

private def e1061 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_065c86a4bb0310e90152) (e1060) (replay_c88c45c22b9888b30470)

private def e1063 : T 5 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cbf15d421a0ecd2260a1) (replay_e745b811a26bc658ec14)

private def e1064 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5978e1f6d4b31cb31598) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c982ffd4ae8a1456b506) (e1063) (replay_088a7fed4563d6a06e7a)

private def e1065 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_25bb4742f53c566750d8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_61d729ec072a6887b3b7) (e1061) (e1064)

private def e1072 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7128d8b44a5eea52e7f8)

private def e1073 : C 5 :=
.trans (e1072) (e1072)

private def e1074 : C 5 :=
.trans (e1073) (e1072)

private def e1075 : C 5 :=
.trans (e1074) (e1072)

private def e1076 : C 5 :=
.trans (e1075) (e1072)

private def e1077 : C 5 :=
.trans (e1076) (e1072)

private def e1078 : C 5 :=
.trans (e1077) (e1072)

private def e1079 : decoder.Code 5 :=
.inherited (.declared (.inl (.inl ⟨2, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2))
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 3))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4]⟩)))

private def e1080 : S 5 :=
.root (e1079)

private def e1081 : S 5 :=
.congPiDom (e1080) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e588931236a24b22cb84)

private def e1082 : C 5 :=
.single (e1081)

private def e1084 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c78ddb585b6e3fe140e7)

private def e1085 : C 5 :=
.trans (e1082) (e1084)

private def e1086 : C 5 :=
.trans (e1078) (e1085)

private def e1087 : C 5 :=
.symm (e1084)

private def e1088 : C 5 :=
.trans (e1084) (e1087)

private def e1089 : C 5 :=
.trans (e1086) (e1088)

private def e1090 : C 5 :=
.trans (e1089) (e1084)

private def e1091 : C 5 :=
.trans (e1090) (e1087)

private def e1092 : C 5 :=
.trans (e1072) (e1091)

private def e1093 : T 5 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7128d8b44a5eea52e7f8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4e574fe3584e51e8790c) (e1065) (replay_f5a306917e0471b25969) (e1092)

private def e1101 : T 5 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05b86c587b7291cc54) (e1004)

private def e1102 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5978e1f6d4b31cb31598) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_69623034ec7d191c0aea) (e1101) (replay_088a7fed4563d6a06e7a)

private def e1103 : T 5 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd68df30b6526d2aba98) (replay_088a7fed4563d6a06e7a) (replay_ff33acd87c5b03c2f11e)

private def e1104 : T 5 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_80d7abfcb57830595ef4) (e1103) (replay_fb92de9ad2d284eba393)

private def e1105 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_309688c12a1ce983731b) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3c838a12f284703c77d3) (e1102) (e1104)

private def e1106 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4777b74b12da0e49bc9) (e1105) (replay_c88c45c22b9888b30470)

private def e1107 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_25bb4742f53c566750d8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d343f1dbfcf61f6b1a2e) (e1106) (e1064)

private def e1108 : T 5 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (replay_e8c0af6d55b0a0664088) (e352)

private def e1109 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8b407b7f762ec7a0add7)

private def e1110 : C 5 :=
.trans (e1109) (e1109)

private def e1111 : C 5 :=
.trans (e1110) (e1109)

private def e1112 : C 5 :=
.trans (e1111) (e1109)

private def e1113 : C 5 :=
.trans (e1112) (e1109)

private def e1114 : C 5 :=
.trans (e1113) (e1109)

private def e1115 : C 5 :=
.trans (e1114) (e1109)

private def e1116 : decoder.Code 5 :=
.inherited (.declared (.inl (.inl ⟨2, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4]⟩)))

private def e1117 : S 5 :=
.root (e1116)

private def e1119 : S 5 :=
.congPiDom (e1117) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7b3937391f90337a4426)

private def e1120 : C 5 :=
.single (e1119)

private def e1122 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6fb1be7619d2bb9eed22)

private def e1123 : C 5 :=
.trans (e1120) (e1122)

private def e1124 : C 5 :=
.trans (e1115) (e1123)

private def e1125 : C 5 :=
.symm (e1122)

private def e1126 : C 5 :=
.trans (e1122) (e1125)

private def e1127 : C 5 :=
.trans (e1124) (e1126)

private def e1128 : C 5 :=
.trans (e1122) (e1122)

private def e1129 : C 5 :=
.trans (e1128) (e1122)

private def e1130 : C 5 :=
.trans (e1129) (e1122)

private def e1131 : C 5 :=
.trans (e1130) (e1122)

private def e1132 : C 5 :=
.trans (e1131) (e1122)

private def e1133 : C 5 :=
.trans (e1132) (e1122)

private def e1134 : decoder.Code 6 :=
.inherited (.declared (.inl (.inl ⟨2, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2))
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 3))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5]⟩)))

private def e1135 : S 6 :=
.root (e1134)

private def e1136 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a2fa25f72f21de9dabb3) (e1135)

private def e1137 : C 5 :=
.single (e1136)

private def e1139 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9b03aec14dc2b5e845af)

private def e1140 : C 5 :=
.trans (e1137) (e1139)

private def e1141 : C 5 :=
.trans (e1133) (e1140)

private def e1142 : C 5 :=
.symm (e1139)

private def e1143 : C 5 :=
.trans (e1139) (e1142)

private def e1144 : C 5 :=
.trans (e1141) (e1143)

private def e1145 : C 5 :=
.trans (e1127) (e1144)

private def e1146 : C 5 :=
.trans (e1145) (e1142)

private def e1147 : C 5 :=
.trans (e1109) (e1146)

private def e1148 : T 5 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8b407b7f762ec7a0add7) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2ff527e667e033dd20bc) (e1107) (e1108) (e1147)

private def e1149 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a2fa25f72f21de9dabb3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3aa92ecdc050920d21ee) (e1148) (replay_088a7fed4563d6a06e7a)

private def e1150 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a2fa25f72f21de9dabb3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e588931236a24b22cb84) (e1093) (e1149)

private def e1156 : T 5 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83f28e98241a6dba6c95) (e1035)

private def e1157 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5978e1f6d4b31cb31598) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7c06c8da685c07a49345) (e1156) (replay_088a7fed4563d6a06e7a)

private def e1158 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a5c6fc596f7509be6eba) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3eddafbc5871a39810e4) (e1157) (replay_088a7fed4563d6a06e7a)

private def e1159 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2a395f51052d7be435f6) (e1158) (replay_c88c45c22b9888b30470)

private def e1160 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_25bb4742f53c566750d8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d194e48e5b0c9ca7ea0b) (e1159) (e1064)

private def e1161 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_22987b8d8a073174d5d3)

private def e1162 : C 5 :=
.trans (e1161) (e1161)

private def e1163 : C 5 :=
.trans (e1162) (e1161)

private def e1164 : C 5 :=
.trans (e1163) (e1161)

private def e1165 : C 5 :=
.trans (e1164) (e1161)

private def e1166 : C 5 :=
.trans (e1165) (e1161)

private def e1167 : C 5 :=
.trans (e1166) (e1161)

private def e1168 : S 5 :=
.congPiDom (e1117) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e588931236a24b22cb84)

private def e1169 : C 5 :=
.single (e1168)

private def e1170 : C 5 :=
.trans (e1169) (e1084)

private def e1171 : C 5 :=
.trans (e1167) (e1170)

private def e1172 : C 5 :=
.trans (e1171) (e1088)

private def e1173 : C 5 :=
.trans (e1172) (e1084)

private def e1174 : C 5 :=
.trans (e1173) (e1087)

private def e1175 : C 5 :=
.trans (e1161) (e1174)

private def e1176 : T 5 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_22987b8d8a073174d5d3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4e574fe3584e51e8790c) (e1160) (replay_f5a306917e0471b25969) (e1175)

private def e1177 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a2fa25f72f21de9dabb3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e588931236a24b22cb84) (e1176) (replay_088a7fed4563d6a06e7a)

private def e1178 : T 5 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1048) (e1150) (e1177)

private def e1179 : T 4 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_4cc623b12c4b86cfe50a) (e1178)

private def e1191 : T 5 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e55a5c7df4a3c442f8a5) (replay_212f5b8aa49c5ced1152)

private def e1192 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a27060780ae3276936d3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8c7354174e36de58a467) (e1191) (replay_3525b0875924370d4991)

private def e1193 : T 5 :=
.reflIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e1192)

private def e1194 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8190ca12c764c3fe675)

private def e1195 : C 5 :=
.trans (e1194) (e1194)

private def e1197 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dfa64be5a5e69455fa25)

private def e1198 : decoder.Code 5 :=
.delta (`CumulativeTower.AllResults.upper)

private def e1199 : S 5 :=
.root (e1198)

private def e1201 : S 5 :=
.congAppFun (e1199) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f76f44da44e23bb59ec9)

private def e1203 : S 5 :=
.congAppFun (e1201) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e51269d558adbeb16ee)

private def e1204 : S 5 :=
.congAppFun (e1203) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_10a09856ff4a49f9d49f)

private def e1205 : S 5 :=
.congAppFun (e1204) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e1207 : S 5 :=
.congAppFun (e1205) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4de9e816e9901b10a0d0)

private def e1209 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e1207) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e1210 : C 5 :=
.single (e1209)

private def e1212 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_76919da23fa3e06c23df)

private def e1213 : C 5 :=
.trans (e1210) (e1212)

private def e1214 : C 5 :=
.trans (e1197) (e1213)

private def e1215 : C 5 :=
.trans (e1214) (e1212)

private def e1217 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_13b6e2baa55c935d82ea) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f76f44da44e23bb59ec9)

private def e1218 : S 5 :=
.congAppFun (e1217) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e51269d558adbeb16ee)

private def e1219 : S 5 :=
.congAppFun (e1218) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_10a09856ff4a49f9d49f)

private def e1220 : S 5 :=
.congAppFun (e1219) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e1221 : S 5 :=
.congAppFun (e1220) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4de9e816e9901b10a0d0)

private def e1222 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e1221) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e1223 : C 5 :=
.single (e1222)

private def e1225 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b83de8b6c1f6adaa7a71)

private def e1226 : C 5 :=
.trans (e1223) (e1225)

private def e1227 : C 5 :=
.trans (e1215) (e1226)

private def e1228 : C 5 :=
.trans (e1227) (e1225)

private def e1230 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bd0b06ac8530616b7e3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e51269d558adbeb16ee)

private def e1231 : S 5 :=
.congAppFun (e1230) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_10a09856ff4a49f9d49f)

private def e1232 : S 5 :=
.congAppFun (e1231) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e1233 : S 5 :=
.congAppFun (e1232) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4de9e816e9901b10a0d0)

private def e1234 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e1233) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e1235 : C 5 :=
.single (e1234)

private def e1237 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_922d38c5102599521841)

private def e1238 : C 5 :=
.trans (e1235) (e1237)

private def e1239 : C 5 :=
.trans (e1228) (e1238)

private def e1240 : C 5 :=
.trans (e1239) (e1237)

private def e1242 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08a6bed65b76df8a9b3d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_10a09856ff4a49f9d49f)

private def e1243 : S 5 :=
.congAppFun (e1242) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e1244 : S 5 :=
.congAppFun (e1243) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4de9e816e9901b10a0d0)

private def e1245 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e1244) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e1246 : C 5 :=
.single (e1245)

private def e1248 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a3b1be356fe8b0b36eb1)

private def e1249 : C 5 :=
.trans (e1246) (e1248)

private def e1250 : C 5 :=
.trans (e1240) (e1249)

private def e1251 : C 5 :=
.trans (e1250) (e1248)

private def e1253 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5fe6baf587bf4ec7fb6a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e1254 : S 5 :=
.congAppFun (e1253) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4de9e816e9901b10a0d0)

private def e1255 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e1254) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e1256 : C 5 :=
.single (e1255)

private def e1258 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_534198158614bc12833f)

private def e1259 : C 5 :=
.trans (e1256) (e1258)

private def e1260 : C 5 :=
.trans (e1251) (e1259)

private def e1261 : C 5 :=
.trans (e1260) (e1258)

private def e1263 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_654fba80bd6b6fd066fb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4de9e816e9901b10a0d0)

private def e1264 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e1263) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e1265 : C 5 :=
.single (e1264)

private def e1267 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_361e1ef243c3944a5868)

private def e1268 : C 5 :=
.trans (e1267) (e1267)

private def e1269 : C 5 :=
.trans (e1268) (e1267)

private def e1270 : C 5 :=
.trans (e1269) (e1267)

private def e1271 : C 5 :=
.trans (e1270) (e1267)

private def e1272 : C 5 :=
.trans (e1271) (e1267)

private def e1273 : C 5 :=
.trans (e1272) (e1267)

private def e1274 : decoder.Code 5 :=
.inherited (.declared (.inl (.inl ⟨2, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                     `CumulativeTower.VecUpper.cons)
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.fst
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.snd
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.VecUpper.nil)
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                     `CumulativeTower.Vec.eliminate)
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2))
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 3)))))))
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                   `CumulativeTower.Nat.zero)))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.VecUpper)
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4]⟩)))

private def e1275 : S 5 :=
.root (e1274)

private def e1276 : S 5 :=
.congAppFun (e1275) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4de9e816e9901b10a0d0)

private def e1277 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e1276) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e1278 : C 5 :=
.single (e1277)

private def e1280 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1bc452641397eaf7de43)

private def e1281 : C 5 :=
.trans (e1278) (e1280)

private def e1282 : C 5 :=
.trans (e1273) (e1281)

private def e1283 : C 5 :=
.trans (e1282) (e1280)

private def e1285 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb4d2e5497f8b684d8d8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4de9e816e9901b10a0d0)

private def e1286 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e1285) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e1287 : C 5 :=
.single (e1286)

private def e1288 : C 5 :=
.trans (e1287) (e1195)

private def e1289 : C 5 :=
.trans (e1283) (e1288)

private def e1290 : C 5 :=
.trans (e1265) (e1289)

private def e1291 : C 5 :=
.trans (e1261) (e1290)

private def e1292 : C 5 :=
.symm (e1291)

private def e1293 : C 5 :=
.trans (e1194) (e1292)

private def e1294 : C 5 :=
.trans (e1195) (e1293)

private def e1295 : C 5 :=
.trans (e1197) (e1197)

private def e1297 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_141851f31c5c3555ad58)

private def e1299 : decoder.Code 5 :=
.delta (`CumulativeTower.AllResults.lower)

private def e1300 : S 5 :=
.root (e1299)

private def e1301 : S 5 :=
.congAppFun (e1300) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f76f44da44e23bb59ec9)

private def e1302 : S 5 :=
.congAppFun (e1301) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e51269d558adbeb16ee)

private def e1303 : S 5 :=
.congAppFun (e1302) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_10a09856ff4a49f9d49f)

private def e1304 : S 5 :=
.congAppFun (e1303) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e1306 : S 5 :=
.congAppFun (e1304) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e1307 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5ff5b42fc060dd1ae6f1) (e1306)

private def e1308 : C 5 :=
.single (e1307)

private def e1310 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4450196b0fb8b62d1bbb)

private def e1311 : C 5 :=
.trans (e1308) (e1310)

private def e1312 : C 5 :=
.trans (e1297) (e1311)

private def e1313 : C 5 :=
.trans (e1312) (e1310)

private def e1315 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41362e8ad5a3cb0dff21) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f76f44da44e23bb59ec9)

private def e1316 : S 5 :=
.congAppFun (e1315) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e51269d558adbeb16ee)

private def e1317 : S 5 :=
.congAppFun (e1316) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_10a09856ff4a49f9d49f)

private def e1318 : S 5 :=
.congAppFun (e1317) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e1319 : S 5 :=
.congAppFun (e1318) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e1320 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5ff5b42fc060dd1ae6f1) (e1319)

private def e1321 : C 5 :=
.single (e1320)

private def e1323 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a08090506ce311bd7a3a)

private def e1324 : C 5 :=
.trans (e1321) (e1323)

private def e1325 : C 5 :=
.trans (e1313) (e1324)

private def e1326 : C 5 :=
.trans (e1325) (e1323)

private def e1328 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c424953c895bf24290e0) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e51269d558adbeb16ee)

private def e1329 : S 5 :=
.congAppFun (e1328) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_10a09856ff4a49f9d49f)

private def e1330 : S 5 :=
.congAppFun (e1329) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e1331 : S 5 :=
.congAppFun (e1330) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e1332 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5ff5b42fc060dd1ae6f1) (e1331)

private def e1333 : C 5 :=
.single (e1332)

private def e1335 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6d64343ef667b987c6bc)

private def e1336 : C 5 :=
.trans (e1333) (e1335)

private def e1337 : C 5 :=
.trans (e1326) (e1336)

private def e1338 : C 5 :=
.trans (e1337) (e1335)

private def e1340 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6f91993fb9355f58a096) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_10a09856ff4a49f9d49f)

private def e1341 : S 5 :=
.congAppFun (e1340) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e1342 : S 5 :=
.congAppFun (e1341) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e1343 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5ff5b42fc060dd1ae6f1) (e1342)

private def e1344 : C 5 :=
.single (e1343)

private def e1346 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d1209211fd4ff24c6a5e)

private def e1347 : C 5 :=
.trans (e1344) (e1346)

private def e1348 : C 5 :=
.trans (e1338) (e1347)

private def e1349 : C 5 :=
.trans (e1348) (e1346)

private def e1351 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8d8c99413ec3ab71b3c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e1352 : S 5 :=
.congAppFun (e1351) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e1353 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5ff5b42fc060dd1ae6f1) (e1352)

private def e1354 : C 5 :=
.single (e1353)

private def e1356 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c5253a58a793fb72c204)

private def e1357 : C 5 :=
.trans (e1354) (e1356)

private def e1358 : C 5 :=
.trans (e1349) (e1357)

private def e1359 : C 5 :=
.trans (e1358) (e1356)

private def e1361 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_03f2dc1272cdf3621c35) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e1362 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5ff5b42fc060dd1ae6f1) (e1361)

private def e1363 : C 5 :=
.single (e1362)

private def e1365 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_aa5f90fa685ad7eb7230)

private def e1366 : C 5 :=
.trans (e1365) (e1365)

private def e1367 : C 5 :=
.trans (e1366) (e1365)

private def e1368 : C 5 :=
.trans (e1367) (e1365)

private def e1369 : C 5 :=
.trans (e1368) (e1365)

private def e1370 : C 5 :=
.trans (e1369) (e1365)

private def e1371 : C 5 :=
.trans (e1370) (e1365)

private def e1372 : decoder.Code 5 :=
.inherited (.declared (.inl (.inl ⟨2, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                     `CumulativeTower.VecUpper.cons)
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8))
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.fst
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.snd
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.VecUpper.nil)
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4)),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                     `CumulativeTower.Vec.eliminate)
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2)))))))
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                   `CumulativeTower.Nat.zero)))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.VecUpper)
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 6))
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4]⟩)))

private def e1373 : S 5 :=
.root (e1372)

private def e1374 : S 5 :=
.congAppFun (e1373) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e1375 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5ff5b42fc060dd1ae6f1) (e1374)

private def e1376 : C 5 :=
.single (e1375)

private def e1378 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7c2391a30b9070c66d20)

private def e1379 : C 5 :=
.trans (e1376) (e1378)

private def e1380 : C 5 :=
.trans (e1371) (e1379)

private def e1381 : C 5 :=
.trans (e1380) (e1378)

private def e1382 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb4d2e5497f8b684d8d8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e1383 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5ff5b42fc060dd1ae6f1) (e1382)

private def e1384 : C 5 :=
.single (e1383)

private def e1385 : C 5 :=
.trans (e1384) (e1295)

private def e1386 : C 5 :=
.trans (e1381) (e1385)

private def e1387 : C 5 :=
.trans (e1363) (e1386)

private def e1388 : C 5 :=
.trans (e1359) (e1387)

private def e1389 : C 5 :=
.symm (e1388)

private def e1390 : C 5 :=
.trans (e1197) (e1389)

private def e1391 : C 5 :=
.trans (e1295) (e1390)

private def e1392 : C 5 :=
.trans (e1294) (e1391)

private def e1393 : C 5 :=
.trans (e1194) (e1392)

private def e1394 : C 5 :=
.symm (e1297)

private def e1395 : C 5 :=
.trans (e1393) (e1394)

private def e1396 : C 5 :=
.trans (e1194) (e1395)

private def e1397 : T 5 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8190ca12c764c3fe675) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1193) (e1178) (e1396)

private def e1398 : T 4 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4e574fe3584e51e8790c) (e1179) (e1397)

private def e1449 : C 7 :=
.trans (replay_b4cf87fb600db2272b1c) (replay_9f7acb9ba3c027bb012f)

private def e1456 : C 7 :=
.trans (e1449) (replay_03e8e466c7d79566d240)

private def e1457 : C 7 :=
.symm (replay_b0fbaebf45708183975a)

private def e1458 : C 7 :=
.trans (replay_b0fbaebf45708183975a) (e1457)

private def e1459 : C 7 :=
.trans (e1456) (e1458)

private def e1492 : C 7 :=
.symm (replay_d86f4cac092cba1e9edd)

private def e1493 : C 7 :=
.trans (replay_d86f4cac092cba1e9edd) (e1492)

private def e1494 : C 7 :=
.trans (replay_281bf456bee54fc8418c) (e1493)

private def e1511 : C 7 :=
.trans (replay_122dfe31d97e8f891b69) (replay_e137911dd2a78cc1279d)

private def e1512 : C 7 :=
.trans (e1511) (replay_998a3aa3c6e631aa82ed)

private def e1525 : C 7 :=
.trans (e1512) (replay_6de9f732f6fe01e23196)

private def e1526 : C 7 :=
.symm (replay_39ba739bac3ef784d92a)

private def e1527 : C 7 :=
.trans (replay_39ba739bac3ef784d92a) (e1526)

private def e1528 : C 7 :=
.trans (e1525) (e1527)

private def e1529 : C 7 :=
.trans (e1494) (e1528)

private def e1530 : C 7 :=
.trans (e1529) (e1526)

private def e1531 : C 7 :=
.trans (replay_b0fbaebf45708183975a) (e1530)

private def e1532 : C 7 :=
.trans (replay_b0fbaebf45708183975a) (e1531)

private def e1533 : C 7 :=
.trans (e1532) (e1526)

private def e1534 : C 7 :=
.trans (replay_b0fbaebf45708183975a) (e1533)

private def e1535 : C 7 :=
.trans (replay_b0fbaebf45708183975a) (e1534)

private def e1536 : C 7 :=
.trans (e1535) (e1526)

private def e1537 : C 7 :=
.trans (replay_b0fbaebf45708183975a) (e1536)

private def e1538 : C 7 :=
.trans (replay_b0fbaebf45708183975a) (e1537)

private def e1539 : C 7 :=
.trans (e1538) (e1526)

private def e1540 : C 7 :=
.trans (replay_b0fbaebf45708183975a) (e1539)

private def e1566 : C 7 :=
.symm (replay_81b38a4292b8bf7eee14)

private def e1567 : C 7 :=
.trans (replay_81b38a4292b8bf7eee14) (e1566)

private def e1568 : C 7 :=
.trans (replay_472a333dd3b5d1ffcb39) (e1567)

private def e1569 : C 7 :=
.trans (replay_39ba739bac3ef784d92a) (e1568)

private def e1570 : C 7 :=
.trans (e1569) (e1566)

private def e1571 : C 7 :=
.trans (replay_39ba739bac3ef784d92a) (e1570)

private def e1572 : C 7 :=
.trans (replay_39ba739bac3ef784d92a) (e1571)

private def e1573 : C 7 :=
.trans (e1572) (e1566)

private def e1574 : C 7 :=
.trans (replay_39ba739bac3ef784d92a) (e1573)

private def e1575 : C 7 :=
.trans (e1540) (e1574)

private def e1576 : C 7 :=
.trans (e1575) (e1566)

private def e1577 : C 7 :=
.trans (replay_b0fbaebf45708183975a) (e1576)

private def e1578 : C 7 :=
.trans (e1459) (e1577)

private def e1579 : C 7 :=
.trans (e1578) (e1566)

private def e1580 : C 7 :=
.trans (replay_35d683e74518daf12740) (e1579)

private def e1581 : T 7 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c0aaf31bbcc06bb12148) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fa34719ab4861ce3b645) (replay_90f4092944132d540b65) (replay_4f91c106a310d3dffbc1) (e1580)

private def e1585 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7055a000b335b678e2ab) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a29128a05eed32aa34c6) (e1581) (replay_ffab124b380a29bf4936)

private def e1598 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_60ec318a62e44b6c9d5f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_355dea50cdf532962853) (e1585) (replay_fda089b4762d15cade6c)

private def e1599 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b54ab3d080b4805429a) (e1598) (replay_e197ee63c3c9ea3d9b51)

private def e1600 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_61babc0a06ef8aba8578) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_463cd5d893fe98804d67) (e1599) (replay_e197ee63c3c9ea3d9b51)

private def e1614 : T 8 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd72d6a3055c3dc99790) (e621)

private def e1615 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83774d5525e9e22ed9e1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_49d03262633c12b079b5) (e1614) (replay_534aece673191f529e08)

private def e1616 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0a7e9ff39cee93a516e0) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d511720bae07ffc5b226) (e1615) (replay_534aece673191f529e08)

private def e1617 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56760c9c60918cbf3d6f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e770e4dfe88f3d1868b5) (e1616) (replay_534aece673191f529e08)

private def e1618 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6164f46507e2b2c8afe0) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4563b2374deb9ad08756) (e1617) (replay_534aece673191f529e08)

private def e1626 : T 8 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05b86c587b7291cc54) (e1004)

private def e1627 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83774d5525e9e22ed9e1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_513008f63a82d721baf3) (e1626) (replay_534aece673191f529e08)

private def e1628 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b58f76c63882e11d87a9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c3aa6fc99c918b9531bd) (e1627) (replay_87793defc7b760df9b5d)

private def e1629 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56760c9c60918cbf3d6f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_12392b7af66212bac61d) (e1628) (replay_534aece673191f529e08)

private def e1630 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6164f46507e2b2c8afe0) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_06461d7038e739e78f96) (e1629) (replay_534aece673191f529e08)

private def e1631 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0414169e5ce74c2eaeff) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91a3417e737975260050) (e1630) (replay_534aece673191f529e08)

private def e1632 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b53c96dd3c862d772319) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43cd7be8392b3b43057e) (e1618) (e1631)

private def e1637 : T 8 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83f28e98241a6dba6c95) (e1035)

private def e1638 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83774d5525e9e22ed9e1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46b209e35101c27b2a4a) (e1637) (replay_534aece673191f529e08)

private def e1639 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0a7e9ff39cee93a516e0) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_aa1f3c041976279e8e17) (e1638) (replay_534aece673191f529e08)

private def e1640 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56760c9c60918cbf3d6f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_33cb78e1e3316c750fe1) (e1639) (replay_534aece673191f529e08)

private def e1641 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6164f46507e2b2c8afe0) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_95dc4ff5ff5ca4df7d6e) (e1640) (replay_534aece673191f529e08)

private def e1642 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0414169e5ce74c2eaeff) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43cd7be8392b3b43057e) (e1641) (replay_534aece673191f529e08)

private def e1643 : T 8 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_ac6edf2f011575ef77cc) (e1632) (e1642)

private def e1644 : T 7 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1600) (e1643)

private def e1694 : C 9 :=
.trans (replay_3be32a3cf696a520f5ae) (replay_965333efd8365157ded4)

private def e1701 : C 9 :=
.trans (e1694) (replay_d243d101085e6e84dcc6)

private def e1702 : C 9 :=
.symm (replay_123a5ae65bfcdebb77cf)

private def e1703 : C 9 :=
.trans (replay_123a5ae65bfcdebb77cf) (e1702)

private def e1704 : C 9 :=
.trans (e1701) (e1703)

private def e1739 : C 9 :=
.symm (replay_8ee1f1ea4adb15d2536f)

private def e1740 : C 9 :=
.trans (replay_8ee1f1ea4adb15d2536f) (e1739)

private def e1741 : C 9 :=
.trans (replay_886ca2f7fff2798c4d67) (e1740)

private def e1758 : C 9 :=
.trans (replay_25baaeb204fa0fc445cc) (replay_73f32aff7489882d854d)

private def e1759 : C 9 :=
.trans (e1758) (replay_210c0cb655f3e2e5deba)

private def e1772 : C 9 :=
.trans (e1759) (replay_4fe5d7bd22cbec91fb26)

private def e1773 : C 9 :=
.symm (replay_e340acdd2db3c199e7d2)

private def e1774 : C 9 :=
.trans (replay_e340acdd2db3c199e7d2) (e1773)

private def e1775 : C 9 :=
.trans (e1772) (e1774)

private def e1776 : C 9 :=
.trans (e1741) (e1775)

private def e1777 : C 9 :=
.trans (e1776) (e1773)

private def e1778 : C 9 :=
.trans (replay_123a5ae65bfcdebb77cf) (e1777)

private def e1779 : C 9 :=
.trans (replay_123a5ae65bfcdebb77cf) (e1778)

private def e1780 : C 9 :=
.trans (e1779) (e1773)

private def e1781 : C 9 :=
.trans (replay_123a5ae65bfcdebb77cf) (e1780)

private def e1782 : C 9 :=
.trans (replay_123a5ae65bfcdebb77cf) (e1781)

private def e1783 : C 9 :=
.trans (e1782) (e1773)

private def e1784 : C 9 :=
.trans (replay_123a5ae65bfcdebb77cf) (e1783)

private def e1785 : C 9 :=
.trans (replay_123a5ae65bfcdebb77cf) (e1784)

private def e1786 : C 9 :=
.trans (e1785) (e1773)

private def e1787 : C 9 :=
.trans (replay_123a5ae65bfcdebb77cf) (e1786)

private def e1814 : C 9 :=
.symm (replay_7d918bc20c4859998095)

private def e1815 : C 9 :=
.trans (replay_7d918bc20c4859998095) (e1814)

private def e1816 : C 9 :=
.trans (replay_3b35dcb485b0d575ded1) (e1815)

private def e1817 : C 9 :=
.trans (replay_e340acdd2db3c199e7d2) (e1816)

private def e1818 : C 9 :=
.trans (e1817) (e1814)

private def e1819 : C 9 :=
.trans (replay_e340acdd2db3c199e7d2) (e1818)

private def e1820 : C 9 :=
.trans (replay_e340acdd2db3c199e7d2) (e1819)

private def e1821 : C 9 :=
.trans (e1820) (e1814)

private def e1822 : C 9 :=
.trans (replay_e340acdd2db3c199e7d2) (e1821)

private def e1823 : C 9 :=
.trans (e1787) (e1822)

private def e1824 : C 9 :=
.trans (e1823) (e1814)

private def e1825 : C 9 :=
.trans (replay_123a5ae65bfcdebb77cf) (e1824)

private def e1826 : C 9 :=
.trans (e1704) (e1825)

private def e1827 : C 9 :=
.trans (e1826) (e1814)

private def e1828 : C 9 :=
.trans (replay_8ca49885f35b4e4cd952) (e1827)

private def e1829 : T 9 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e154fbed77bbef3e0f01) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fa34719ab4861ce3b645) (replay_fb60defb6850959f3c3b) (replay_569bb0b655c028c0fa14) (e1828)

private def e1833 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7bd2623d7ade2c187ee) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d1c89b3700d87ae188dc) (e1829) (replay_8f68fd41cbd38b75604c)

private def e1845 : T 13 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd68df30b6526d2aba98) (replay_8dab544be16d5febf71b) (replay_39520f2102ac9d665fff)

private def e1847 : T 13 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_80d7abfcb57830595ef4) (e1845) (replay_730a0c3ead453f836005)

private def e1848 : T 13 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b56a1922a5a71afc4661) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b5fdadc9bc8fe3a4b0aa) (e1847) (replay_8dab544be16d5febf71b)

private def e1849 : T 13 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1848) (replay_730a0c3ead453f836005)

private def e1850 : T 13 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b8578195b133fac70a1) (e1849)

private def e1851 : T 12 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7646540dd7e659fc407) (replay_c44554f2ec03401dae60) (e1850)

private def e1852 : T 11 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e1d07338c040d26dff49) (replay_0deba36dfc04bce93eef) (e1851)

private def e1853 : T 10 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7e6cb354a8df3738086) (replay_ed46235597880bcfdcf3) (e1852)

private def e1854 : T 9 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_088ec0f4742a888f4d7e) (replay_5b7174da1306c1fd124b) (e1853)

private def e1855 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_457e7c1aa2679ed701ee) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c6b4e97c573d939f7572) (e1833) (e1854)

private def e1856 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e056103386ad05d9d9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_942e3b1b8ce4b70c0845) (e1855) (replay_07c41680d17703d7171f)

private def e1857 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58bdea1e3c28d008f853) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_307e4da5e86f9f55da07) (e1856) (replay_07c41680d17703d7171f)

private def e1858 : T 8 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_534aece673191f529e08) (e1857)

private def e1865 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e056103386ad05d9d9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_307e4da5e86f9f55da07) (replay_f01d03acf0e8385b1342) (replay_7943c3e0fd7c8e285c77)

private def e1875 : T 9 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd72d6a3055c3dc99790) (e621)

private def e1876 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c537445f28d8d4cca5c8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_af9382af94a69e21fca6) (e1875) (replay_07c41680d17703d7171f)

private def e1877 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5185e3c12dc65a8f34dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56404232de5cd70ab714) (e1876) (replay_07c41680d17703d7171f)

private def e1878 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e056103386ad05d9d9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c3d172b4624b6e11b26d) (e1877) (replay_7943c3e0fd7c8e285c77)

private def e1885 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e056103386ad05d9d9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bde16b11ff66bda5c8d7) (replay_1f73f335c703f4e1292a) (replay_07c41680d17703d7171f)

private def e1886 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e2c1e2e15bb0cda87a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8b93c30311fd5361729c) (e1885) (replay_07c41680d17703d7171f)

private def e1887 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58bdea1e3c28d008f853) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a40f248fe594a62e2d0e) (e1886) (replay_07c41680d17703d7171f)

private def e1888 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_04a2886bde316b33b302) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ce557b152913180765a4) (e1878) (e1887)

private def e1934 : C 10 :=
.trans (replay_3b68318621758ff2b007) (replay_a71959968da9f2810ccc)

private def e1941 : C 10 :=
.trans (e1934) (replay_93ee2d65f1164b786699)

private def e1942 : C 10 :=
.symm (replay_64fa7d30378ce9e1c860)

private def e1943 : C 10 :=
.trans (replay_64fa7d30378ce9e1c860) (e1942)

private def e1944 : C 10 :=
.trans (e1941) (e1943)

private def e1980 : C 10 :=
.symm (replay_d2b07b59ff2ac67624a1)

private def e1981 : C 10 :=
.trans (replay_d2b07b59ff2ac67624a1) (e1980)

private def e1982 : C 10 :=
.trans (replay_478420457564b488b7bb) (e1981)

private def e2000 : C 10 :=
.trans (replay_2ccbd0a8acf33a57e275) (replay_188e8232d1c2f98c8249)

private def e2001 : C 10 :=
.trans (e2000) (replay_0e09bd84c2fb65b02d16)

private def e2014 : C 10 :=
.trans (e2001) (replay_6de0a5f2b6ea51206750)

private def e2015 : C 10 :=
.symm (replay_4f2aa86a55eb734ba868)

private def e2016 : C 10 :=
.trans (replay_4f2aa86a55eb734ba868) (e2015)

private def e2017 : C 10 :=
.trans (e2014) (e2016)

private def e2018 : C 10 :=
.trans (e1982) (e2017)

private def e2019 : C 10 :=
.trans (e2018) (e2015)

private def e2020 : C 10 :=
.trans (replay_64fa7d30378ce9e1c860) (e2019)

private def e2021 : C 10 :=
.trans (replay_64fa7d30378ce9e1c860) (e2020)

private def e2022 : C 10 :=
.trans (e2021) (e2015)

private def e2023 : C 10 :=
.trans (replay_64fa7d30378ce9e1c860) (e2022)

private def e2024 : C 10 :=
.trans (replay_64fa7d30378ce9e1c860) (e2023)

private def e2025 : C 10 :=
.trans (e2024) (e2015)

private def e2026 : C 10 :=
.trans (replay_64fa7d30378ce9e1c860) (e2025)

private def e2027 : C 10 :=
.trans (replay_64fa7d30378ce9e1c860) (e2026)

private def e2028 : C 10 :=
.trans (e2027) (e2015)

private def e2029 : C 10 :=
.trans (replay_64fa7d30378ce9e1c860) (e2028)

private def e2055 : C 10 :=
.symm (replay_847a0844b4a9dc6e9de0)

private def e2056 : C 10 :=
.trans (replay_847a0844b4a9dc6e9de0) (e2055)

private def e2057 : C 10 :=
.trans (replay_14743da4db237c9360ec) (e2056)

private def e2058 : C 10 :=
.trans (replay_4f2aa86a55eb734ba868) (e2057)

private def e2059 : C 10 :=
.trans (e2058) (e2055)

private def e2060 : C 10 :=
.trans (replay_4f2aa86a55eb734ba868) (e2059)

private def e2061 : C 10 :=
.trans (replay_4f2aa86a55eb734ba868) (e2060)

private def e2062 : C 10 :=
.trans (e2061) (e2055)

private def e2063 : C 10 :=
.trans (replay_4f2aa86a55eb734ba868) (e2062)

private def e2064 : C 10 :=
.trans (e2029) (e2063)

private def e2065 : C 10 :=
.trans (e2064) (e2055)

private def e2066 : C 10 :=
.trans (replay_64fa7d30378ce9e1c860) (e2065)

private def e2067 : C 10 :=
.trans (e1944) (e2066)

private def e2068 : C 10 :=
.trans (e2067) (e2055)

private def e2069 : C 10 :=
.trans (replay_3255046a4e38195667f1) (e2068)

private def e2070 : T 10 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c0ad6a36182aa22d8a29) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_404b5de2e790e15a378c) (replay_0987acba82150fea5c56) (replay_bf5cf61dc7256686b556) (e2069)

private def e2074 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_683a421a2ec88ad82286) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3bf7bc4937b4a8d675) (e2070) (replay_71189f869dd37629b9df)

private def e2081 : T 14 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd68df30b6526d2aba98) (replay_730a0c3ead453f836005) (replay_db148fd65b599d74a887)

private def e2083 : T 14 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_80d7abfcb57830595ef4) (e2081) (replay_2c304eb7e4ba83000148)

private def e2084 : T 14 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ce2c4836dd8e02f7720c) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d23443c318fa6d28ee8f) (e2083) (replay_730a0c3ead453f836005)

private def e2085 : T 14 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (e2084) (replay_2c304eb7e4ba83000148)

private def e2086 : T 14 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_50d54f6ca4190fd6bc72) (e2085)

private def e2087 : T 13 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d3bc479f5fb249b99ac2) (replay_026903513c8aa1a3c0ec) (e2086)

private def e2088 : T 12 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c6b51e3ba4892036cdb0) (replay_90a1a7c7eb898d3f1698) (e2087)

private def e2089 : T 11 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_45e80a32c899dfd6b11b) (replay_8cb9fc469614bc44e21f) (e2088)

private def e2090 : T 10 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fafdfa0063130741b0e7) (replay_f08d0c1b4df9c93cc0d2) (e2089)

private def e2091 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b294f6f5b0947f91e7dc) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2edfeff78e8f848ef00f) (e2074) (e2090)

private def e2092 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ffbcdddae5a4ba50f754) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_14a8f79d091054a49f83) (e2091) (replay_8dd06e568960d2567ea5)

private def e2093 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_de0d936cd54f5c2b0737) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_df96c216643bb607dff9) (e2092) (replay_8dd06e568960d2567ea5)

private def e2094 : T 9 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (replay_07c41680d17703d7171f) (e2093)

private def e2102 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_50d54f6ca4190fd6bc72) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e2094) (replay_7c17c9803ae92cfc6233)

private def e2103 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_07887d426b2fa3b06b04)

private def e2104 : C 9 :=
.trans (e2103) (e2103)

private def e2105 : C 9 :=
.trans (e2104) (e2103)

private def e2106 : C 9 :=
.trans (e2105) (e2103)

private def e2107 : C 9 :=
.trans (e2106) (e2103)

private def e2108 : C 9 :=
.trans (e2107) (e2103)

private def e2109 : C 9 :=
.trans (e2108) (e2103)

private def e2110 : decoder.Code 9 :=
.inherited (.declared (.inl (.inl ⟨3, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 12))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2))
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 3))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8]⟩)))

private def e2111 : S 9 :=
.root (e2110)

private def e2112 : S 9 :=
.congPiDom (e2111) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05)

private def e2113 : C 9 :=
.single (e2112)

private def e2115 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3464e39d7d13aed4179f)

private def e2116 : C 9 :=
.trans (e2115) (e2115)

private def e2119 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e430d20317f9c73b29a5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e2121 : S 9 :=
.congAppFun (e2119) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea50578066f1875556e5)

private def e2122 : S 9 :=
.congAppFun (e2121) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e2123 : S 9 :=
.congAppFun (e2122) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91a3417e737975260050)

private def e2124 : S 9 :=
.congPiDom (e2123) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05)

private def e2125 : C 9 :=
.single (e2124)

private def e2127 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e03f98f8670949f6175d)

private def e2128 : C 9 :=
.trans (e2125) (e2127)

private def e2129 : C 9 :=
.trans (e2116) (e2128)

private def e2130 : C 9 :=
.trans (e2129) (e2127)

private def e2132 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_33a0f5a9a39a48489031) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea50578066f1875556e5)

private def e2133 : S 9 :=
.congAppFun (e2132) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e2134 : S 9 :=
.congAppFun (e2133) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91a3417e737975260050)

private def e2135 : S 9 :=
.congPiDom (e2134) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05)

private def e2136 : C 9 :=
.single (e2135)

private def e2138 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f9a629d49a12dea22c51)

private def e2139 : C 9 :=
.trans (e2136) (e2138)

private def e2140 : C 9 :=
.trans (e2130) (e2139)

private def e2141 : C 9 :=
.trans (e2140) (e2138)

private def e2143 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d5b00a731e3d66266d34) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e2144 : S 9 :=
.congAppFun (e2143) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91a3417e737975260050)

private def e2145 : S 9 :=
.congPiDom (e2144) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05)

private def e2146 : C 9 :=
.single (e2145)

private def e2148 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_489539aa44735cd3a1cc)

private def e2149 : C 9 :=
.trans (e2146) (e2148)

private def e2150 : C 9 :=
.trans (e2141) (e2149)

private def e2151 : C 9 :=
.trans (e2150) (e2148)

private def e2153 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f2799545315fa87651c8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91a3417e737975260050)

private def e2154 : S 9 :=
.congPiDom (e2153) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05)

private def e2155 : C 9 :=
.single (e2154)

private def e2157 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0ed4930f2695c4e1d447)

private def e2158 : C 9 :=
.trans (e2155) (e2157)

private def e2159 : C 9 :=
.trans (e2151) (e2158)

private def e2160 : C 9 :=
.trans (e2113) (e2159)

private def e2161 : C 9 :=
.trans (e2109) (e2160)

private def e2162 : C 9 :=
.trans (e2157) (e2157)

private def e2164 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e48b53379ef509db2cd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea50578066f1875556e5)

private def e2166 : S 9 :=
.congSigmaDom (e2164) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9530908dcf6c5275717)

private def e2167 : S 9 :=
.congPiDom (e2166) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05)

private def e2168 : C 9 :=
.single (e2167)

private def e2170 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a972a67a4f13b697f398)

private def e2171 : C 9 :=
.trans (e2168) (e2170)

private def e2172 : C 9 :=
.trans (e2162) (e2171)

private def e2173 : C 9 :=
.symm (e2170)

private def e2174 : C 9 :=
.trans (e2170) (e2173)

private def e2175 : C 9 :=
.trans (e2172) (e2174)

private def e2176 : C 9 :=
.trans (e2175) (e2170)

private def e2177 : C 9 :=
.trans (e2176) (e2173)

private def e2178 : C 9 :=
.trans (e2161) (e2177)

private def e2179 : C 9 :=
.trans (e2178) (e2170)

private def e2180 : C 9 :=
.trans (e2179) (e2173)

private def e2181 : C 9 :=
.trans (e2103) (e2180)

private def e2182 : T 9 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_07887d426b2fa3b06b04) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3113b23543c4066f3ea8) (e1888) (e2102) (e2181)

private def e2192 : T 9 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05b86c587b7291cc54) (e1004)

private def e2193 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c537445f28d8d4cca5c8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_081f6aad3d12cc933697) (e2192) (replay_07c41680d17703d7171f)

private def e2194 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd68df30b6526d2aba98) (replay_07c41680d17703d7171f) (replay_b7b0d4f9c05076ab70ae)

private def e2195 : T 9 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_80d7abfcb57830595ef4) (e2194) (replay_8dd06e568960d2567ea5)

private def e2196 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2ef36b27edf683785e3e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4325f4e1d6bc657eced) (e2193) (e2195)

private def e2197 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e056103386ad05d9d9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3a498e1101a964a28c24) (e2196) (replay_7943c3e0fd7c8e285c77)

private def e2198 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_04a2886bde316b33b302) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7bef6126dc4a0cb6f358) (e2197) (e1887)

private def e2226 : C 10 :=
.trans (replay_b0af1a6b71f3e5efb722) (replay_63ad134561a3273d4b61)

private def e2233 : C 10 :=
.trans (e2226) (replay_f5a5ee36481a9244e106)

private def e2234 : C 10 :=
.symm (replay_aaf9e27e26346492a2c2)

private def e2235 : C 10 :=
.trans (replay_aaf9e27e26346492a2c2) (e2234)

private def e2236 : C 10 :=
.trans (e2233) (e2235)

private def e2266 : C 10 :=
.symm (replay_7cc0b9616f5928bf8640)

private def e2267 : C 10 :=
.trans (replay_7cc0b9616f5928bf8640) (e2266)

private def e2268 : C 10 :=
.trans (replay_6488e6f069b22cd77993) (e2267)

private def e2283 : C 10 :=
.trans (replay_d3cabcbe72e086ae4e48) (replay_aaaf61b9552aafa6c659)

private def e2284 : C 10 :=
.trans (e2283) (replay_d3d1e46981cea056f66d)

private def e2297 : C 10 :=
.trans (e2284) (replay_b943cee8cd11a270a877)

private def e2298 : C 10 :=
.symm (replay_75e85702dae7736fa8b4)

private def e2299 : C 10 :=
.trans (replay_75e85702dae7736fa8b4) (e2298)

private def e2300 : C 10 :=
.trans (e2297) (e2299)

private def e2301 : C 10 :=
.trans (e2268) (e2300)

private def e2302 : C 10 :=
.trans (e2301) (e2298)

private def e2303 : C 10 :=
.trans (replay_aaf9e27e26346492a2c2) (e2302)

private def e2304 : C 10 :=
.trans (replay_aaf9e27e26346492a2c2) (e2303)

private def e2305 : C 10 :=
.trans (e2304) (e2298)

private def e2306 : C 10 :=
.trans (replay_aaf9e27e26346492a2c2) (e2305)

private def e2307 : C 10 :=
.trans (replay_aaf9e27e26346492a2c2) (e2306)

private def e2308 : C 10 :=
.trans (e2307) (e2298)

private def e2309 : C 10 :=
.trans (replay_aaf9e27e26346492a2c2) (e2308)

private def e2310 : C 10 :=
.trans (replay_aaf9e27e26346492a2c2) (e2309)

private def e2311 : C 10 :=
.trans (e2310) (e2298)

private def e2312 : C 10 :=
.trans (replay_aaf9e27e26346492a2c2) (e2311)

private def e2336 : C 10 :=
.symm (replay_944acdca319785544480)

private def e2337 : C 10 :=
.trans (replay_944acdca319785544480) (e2336)

private def e2338 : C 10 :=
.trans (replay_b163de3a089fbf22d61a) (e2337)

private def e2339 : C 10 :=
.trans (replay_75e85702dae7736fa8b4) (e2338)

private def e2340 : C 10 :=
.trans (e2339) (e2336)

private def e2341 : C 10 :=
.trans (replay_75e85702dae7736fa8b4) (e2340)

private def e2342 : C 10 :=
.trans (replay_75e85702dae7736fa8b4) (e2341)

private def e2343 : C 10 :=
.trans (e2342) (e2336)

private def e2344 : C 10 :=
.trans (replay_75e85702dae7736fa8b4) (e2343)

private def e2345 : C 10 :=
.trans (e2312) (e2344)

private def e2346 : C 10 :=
.trans (e2345) (e2336)

private def e2347 : C 10 :=
.trans (replay_aaf9e27e26346492a2c2) (e2346)

private def e2348 : C 10 :=
.trans (e2236) (e2347)

private def e2349 : C 10 :=
.trans (e2348) (e2336)

private def e2350 : C 10 :=
.trans (replay_af81fa67013d611a7771) (e2349)

private def e2351 : T 10 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5284155d7283304dd04e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fa34719ab4861ce3b645) (replay_030ad53cab78c2f5ce25) (replay_269ab6e96ec062014711) (e2350)

private def e2352 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_307e4da5e86f9f55da07) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0f453802f734e64d2ba4) (e2351) (replay_71189f869dd37629b9df)

private def e2353 : T 14 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e2084) (replay_2c304eb7e4ba83000148)

private def e2354 : T 14 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b8578195b133fac70a1) (e2353)

private def e2355 : T 13 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7646540dd7e659fc407) (replay_7f3666ee4d524ac33d36) (e2354)

private def e2356 : T 12 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e1d07338c040d26dff49) (replay_65cfbcfdb47151e397fb) (e2355)

private def e2357 : T 11 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7e6cb354a8df3738086) (replay_301d0620346f66a82c71) (e2356)

private def e2358 : T 10 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_088ec0f4742a888f4d7e) (replay_b2ef58dbd0b820f90b19) (e2357)

private def e2359 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dc66c4550ea05fa8a82) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a165307c13c5e80f57a2) (e2352) (e2358)

private def e2360 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ffbcdddae5a4ba50f754) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fce151a8c88fcceb10d2) (e2359) (replay_8dd06e568960d2567ea5)

private def e2361 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_de0d936cd54f5c2b0737) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c4973f6eacdd028898bc) (e2360) (replay_8dd06e568960d2567ea5)

private def e2362 : T 9 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_07c41680d17703d7171f) (e2361)

private def e2409 : C 11 :=
.trans (replay_eac1540dcf5ad6d5167f) (replay_45c243bec42b79b7e1ab)

private def e2416 : C 11 :=
.trans (e2409) (replay_75bd5a977e40c3f5df67)

private def e2417 : C 11 :=
.symm (replay_98a799e5f3813e126e74)

private def e2418 : C 11 :=
.trans (replay_98a799e5f3813e126e74) (e2417)

private def e2419 : C 11 :=
.trans (e2416) (e2418)

private def e2452 : C 11 :=
.symm (replay_b4e3a8ac0319e82d697e)

private def e2453 : C 11 :=
.trans (replay_b4e3a8ac0319e82d697e) (e2452)

private def e2454 : C 11 :=
.trans (replay_c3e3c5edef01e56dcc1c) (e2453)

private def e2471 : C 11 :=
.trans (replay_b4df30bc953cdc3c4df3) (replay_d7ea25231f6a375a951b)

private def e2472 : C 11 :=
.trans (e2471) (replay_d766709ca1ca376223d4)

private def e2485 : C 11 :=
.trans (e2472) (replay_43d4700812b0fd930f55)

private def e2486 : C 11 :=
.symm (replay_c56d8bc91436750863bf)

private def e2487 : C 11 :=
.trans (replay_c56d8bc91436750863bf) (e2486)

private def e2488 : C 11 :=
.trans (e2485) (e2487)

private def e2489 : C 11 :=
.trans (e2454) (e2488)

private def e2490 : C 11 :=
.trans (e2489) (e2486)

private def e2491 : C 11 :=
.trans (replay_98a799e5f3813e126e74) (e2490)

private def e2492 : C 11 :=
.trans (replay_98a799e5f3813e126e74) (e2491)

private def e2493 : C 11 :=
.trans (e2492) (e2486)

private def e2494 : C 11 :=
.trans (replay_98a799e5f3813e126e74) (e2493)

private def e2495 : C 11 :=
.trans (replay_98a799e5f3813e126e74) (e2494)

private def e2496 : C 11 :=
.trans (e2495) (e2486)

private def e2497 : C 11 :=
.trans (replay_98a799e5f3813e126e74) (e2496)

private def e2498 : C 11 :=
.trans (replay_98a799e5f3813e126e74) (e2497)

private def e2499 : C 11 :=
.trans (e2498) (e2486)

private def e2500 : C 11 :=
.trans (replay_98a799e5f3813e126e74) (e2499)

private def e2526 : C 11 :=
.symm (replay_cc681c77d3378ef56658)

private def e2527 : C 11 :=
.trans (replay_cc681c77d3378ef56658) (e2526)

private def e2528 : C 11 :=
.trans (replay_e53df1d2e25dd78a6aaa) (e2527)

private def e2529 : C 11 :=
.trans (replay_c56d8bc91436750863bf) (e2528)

private def e2530 : C 11 :=
.trans (e2529) (e2526)

private def e2531 : C 11 :=
.trans (replay_c56d8bc91436750863bf) (e2530)

private def e2532 : C 11 :=
.trans (replay_c56d8bc91436750863bf) (e2531)

private def e2533 : C 11 :=
.trans (e2532) (e2526)

private def e2534 : C 11 :=
.trans (replay_c56d8bc91436750863bf) (e2533)

private def e2535 : C 11 :=
.trans (e2500) (e2534)

private def e2536 : C 11 :=
.trans (e2535) (e2526)

private def e2537 : C 11 :=
.trans (replay_98a799e5f3813e126e74) (e2536)

private def e2538 : C 11 :=
.trans (e2419) (e2537)

private def e2539 : C 11 :=
.trans (e2538) (e2526)

private def e2540 : C 11 :=
.trans (replay_2fa735a334f18834a861) (e2539)

private def e2541 : T 11 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79bf2d9bd7c77e1823c3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_404b5de2e790e15a378c) (replay_481a9aa371614c927569) (replay_c478c8a8b5798b38a1c5) (e2540)

private def e2545 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_df96c216643bb607dff9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_96b9158510328928b39b) (e2541) (replay_c93a4b141e1ddc8ceb10)

private def e2548 : T 15 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd68df30b6526d2aba98) (replay_2c304eb7e4ba83000148) (replay_2dfd2a610fc484ec894e)

private def e2550 : T 15 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_80d7abfcb57830595ef4) (e2548) (replay_7bbd6a1783772f9a6990)

private def e2551 : T 15 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1dcab4068fe977ee55c8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62290bcf78302eb1e870) (e2550) (replay_2c304eb7e4ba83000148)

private def e2552 : T 15 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (e2551) (replay_7bbd6a1783772f9a6990)

private def e2553 : T 15 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_50d54f6ca4190fd6bc72) (e2552)

private def e2554 : T 14 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d3bc479f5fb249b99ac2) (replay_1fd3900629d98a711342) (e2553)

private def e2555 : T 13 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c6b51e3ba4892036cdb0) (replay_39fd35ec10b3c1d27b07) (e2554)

private def e2556 : T 12 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_45e80a32c899dfd6b11b) (replay_8f8519791580d44d907d) (e2555)

private def e2557 : T 11 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fafdfa0063130741b0e7) (replay_141202d8fcfac7fb06cd) (e2556)

private def e2558 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bbbfb819dfb20b145875) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2ddf13902f33d10b9278) (e2545) (e2557)

private def e2559 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1bed53fd97751c172144) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_815ef5d05c8514ec459c) (e2558) (replay_7fbeba8818273106d8c8)

private def e2560 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4e0bd14f54be2011bbdb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b02738bed1f938162bff) (e2559) (replay_7fbeba8818273106d8c8)

private def e2561 : T 10 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (replay_8dd06e568960d2567ea5) (e2560)

private def e2562 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b8578195b133fac70a1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_50d54f6ca4190fd6bc72) (e2362) (e2561)

private def e2563 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d180dc59773623b8ec2f)

private def e2564 : C 9 :=
.trans (e2563) (e2563)

private def e2565 : C 9 :=
.trans (e2564) (e2563)

private def e2566 : C 9 :=
.trans (e2565) (e2563)

private def e2567 : C 9 :=
.trans (e2566) (e2563)

private def e2568 : C 9 :=
.trans (e2567) (e2563)

private def e2569 : C 9 :=
.trans (e2568) (e2563)

private def e2570 : decoder.Code 9 :=
.inherited (.declared (.inl (.inl ⟨3, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 12))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8]⟩)))

private def e2571 : S 9 :=
.root (e2570)

private def e2573 : S 9 :=
.congPiDom (e2571) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4f1ffa48d98996a6db77)

private def e2574 : C 9 :=
.single (e2573)

private def e2576 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd1a7edaddae24c33b2a)

private def e2577 : C 9 :=
.trans (e2576) (e2576)

private def e2579 : S 9 :=
.congAppFun (e2122) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c147bd3db1fd948411b6)

private def e2580 : S 9 :=
.congPiDom (e2579) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4f1ffa48d98996a6db77)

private def e2581 : C 9 :=
.single (e2580)

private def e2583 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e42dd2575b7051bf9e0)

private def e2584 : C 9 :=
.trans (e2581) (e2583)

private def e2585 : C 9 :=
.trans (e2577) (e2584)

private def e2586 : C 9 :=
.trans (e2585) (e2583)

private def e2587 : S 9 :=
.congAppFun (e2133) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c147bd3db1fd948411b6)

private def e2588 : S 9 :=
.congPiDom (e2587) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4f1ffa48d98996a6db77)

private def e2589 : C 9 :=
.single (e2588)

private def e2591 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6131458f019bf6f97173)

private def e2592 : C 9 :=
.trans (e2589) (e2591)

private def e2593 : C 9 :=
.trans (e2586) (e2592)

private def e2594 : C 9 :=
.trans (e2593) (e2591)

private def e2595 : S 9 :=
.congAppFun (e2143) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c147bd3db1fd948411b6)

private def e2596 : S 9 :=
.congPiDom (e2595) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4f1ffa48d98996a6db77)

private def e2597 : C 9 :=
.single (e2596)

private def e2599 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4f348e418a6e38c9f7bf)

private def e2600 : C 9 :=
.trans (e2597) (e2599)

private def e2601 : C 9 :=
.trans (e2594) (e2600)

private def e2602 : C 9 :=
.trans (e2601) (e2599)

private def e2603 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f2799545315fa87651c8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c147bd3db1fd948411b6)

private def e2604 : S 9 :=
.congPiDom (e2603) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4f1ffa48d98996a6db77)

private def e2605 : C 9 :=
.single (e2604)

private def e2607 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c179b902f09ad4e760aa)

private def e2608 : C 9 :=
.trans (e2605) (e2607)

private def e2609 : C 9 :=
.trans (e2602) (e2608)

private def e2610 : C 9 :=
.trans (e2574) (e2609)

private def e2611 : C 9 :=
.trans (e2569) (e2610)

private def e2612 : C 9 :=
.trans (e2607) (e2607)

private def e2614 : S 9 :=
.congSigmaDom (e2164) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e9c073bd7cf6856c0f8)

private def e2615 : S 9 :=
.congPiDom (e2614) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4f1ffa48d98996a6db77)

private def e2616 : C 9 :=
.single (e2615)

private def e2618 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_90beb425772a41e9474b)

private def e2619 : C 9 :=
.trans (e2616) (e2618)

private def e2620 : C 9 :=
.trans (e2612) (e2619)

private def e2621 : C 9 :=
.symm (e2618)

private def e2622 : C 9 :=
.trans (e2618) (e2621)

private def e2623 : C 9 :=
.trans (e2620) (e2622)

private def e2624 : C 9 :=
.trans (e2623) (e2618)

private def e2625 : C 9 :=
.trans (e2624) (e2621)

private def e2626 : C 9 :=
.trans (e2611) (e2625)

private def e2627 : C 9 :=
.trans (e2618) (e2618)

private def e2628 : C 9 :=
.trans (e2627) (e2618)

private def e2629 : C 9 :=
.trans (e2628) (e2618)

private def e2630 : C 9 :=
.trans (e2629) (e2618)

private def e2631 : C 9 :=
.trans (e2630) (e2618)

private def e2632 : C 9 :=
.trans (e2631) (e2618)

private def e2633 : decoder.Code 10 :=
.inherited (.declared (.inl (.inl ⟨3, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 13))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2))
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 3))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9]⟩)))

private def e2634 : S 10 :=
.root (e2633)

private def e2635 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53a3d94e880c845f90cc) (e2634)

private def e2636 : C 9 :=
.single (e2635)

private def e2638 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a18469eb3eeb0cc40e2f)

private def e2639 : C 9 :=
.trans (e2638) (e2638)

private def e2642 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9abfa21b0b877572d400) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7ab78a8c29b0a1fb1fa4)

private def e2644 : S 10 :=
.congAppFun (e2642) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5f1b5206711b41dd8873)

private def e2646 : S 10 :=
.congAppFun (e2644) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4a335c7ece839d5c562e)

private def e2647 : S 10 :=
.congAppFun (e2646) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9530908dcf6c5275717)

private def e2648 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53a3d94e880c845f90cc) (e2647)

private def e2649 : C 9 :=
.single (e2648)

private def e2651 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1bbee6ce5e6965bc112a)

private def e2652 : C 9 :=
.trans (e2649) (e2651)

private def e2653 : C 9 :=
.trans (e2639) (e2652)

private def e2654 : C 9 :=
.trans (e2653) (e2651)

private def e2656 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bd06193f1636289f6db8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5f1b5206711b41dd8873)

private def e2657 : S 10 :=
.congAppFun (e2656) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4a335c7ece839d5c562e)

private def e2658 : S 10 :=
.congAppFun (e2657) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9530908dcf6c5275717)

private def e2659 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53a3d94e880c845f90cc) (e2658)

private def e2660 : C 9 :=
.single (e2659)

private def e2662 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d68f5333c90c401d87f0)

private def e2663 : C 9 :=
.trans (e2660) (e2662)

private def e2664 : C 9 :=
.trans (e2654) (e2663)

private def e2665 : C 9 :=
.trans (e2664) (e2662)

private def e2667 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fdc97ffd338ea0dcd605) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4a335c7ece839d5c562e)

private def e2668 : S 10 :=
.congAppFun (e2667) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9530908dcf6c5275717)

private def e2669 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53a3d94e880c845f90cc) (e2668)

private def e2670 : C 9 :=
.single (e2669)

private def e2672 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5b30ffc4d200a30f756a)

private def e2673 : C 9 :=
.trans (e2670) (e2672)

private def e2674 : C 9 :=
.trans (e2665) (e2673)

private def e2675 : C 9 :=
.trans (e2674) (e2672)

private def e2677 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3796eb9c049c940c2c21) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9530908dcf6c5275717)

private def e2678 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53a3d94e880c845f90cc) (e2677)

private def e2679 : C 9 :=
.single (e2678)

private def e2681 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d4a46dc57607f404dce)

private def e2682 : C 9 :=
.trans (e2679) (e2681)

private def e2683 : C 9 :=
.trans (e2675) (e2682)

private def e2684 : C 9 :=
.trans (e2636) (e2683)

private def e2685 : C 9 :=
.trans (e2632) (e2684)

private def e2686 : C 9 :=
.trans (e2681) (e2681)

private def e2688 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8304ec2301382ae96f36) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5f1b5206711b41dd8873)

private def e2690 : S 10 :=
.congSigmaDom (e2688) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_151601d70406d501031f)

private def e2691 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53a3d94e880c845f90cc) (e2690)

private def e2692 : C 9 :=
.single (e2691)

private def e2694 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_811967a8e994dab69715)

private def e2695 : C 9 :=
.trans (e2692) (e2694)

private def e2696 : C 9 :=
.trans (e2686) (e2695)

private def e2697 : C 9 :=
.symm (e2694)

private def e2698 : C 9 :=
.trans (e2694) (e2697)

private def e2699 : C 9 :=
.trans (e2696) (e2698)

private def e2700 : C 9 :=
.trans (e2699) (e2694)

private def e2701 : C 9 :=
.trans (e2700) (e2697)

private def e2702 : C 9 :=
.trans (e2685) (e2701)

private def e2703 : C 9 :=
.trans (e2626) (e2702)

private def e2704 : C 9 :=
.trans (e2703) (e2697)

private def e2705 : C 9 :=
.trans (e2563) (e2704)

private def e2706 : T 9 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d180dc59773623b8ec2f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_14a0af32c0145b2cf8b7) (e2198) (e2562) (e2705)

private def e2707 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53a3d94e880c845f90cc) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b5fb0721673927e700a9) (e2706) (replay_07c41680d17703d7171f)

private def e2708 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c34919923848a2b3766f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05) (e2182) (e2707)

private def e2714 : T 9 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83f28e98241a6dba6c95) (e1035)

private def e2715 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c537445f28d8d4cca5c8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_735cf3379896fd355cf5) (e2714) (replay_07c41680d17703d7171f)

private def e2716 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5185e3c12dc65a8f34dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_461467197017cefa64f8) (e2715) (replay_07c41680d17703d7171f)

private def e2717 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e056103386ad05d9d9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_25a79c6a512df03ceac3) (e2716) (replay_7943c3e0fd7c8e285c77)

private def e2718 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_04a2886bde316b33b302) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9d53bc8a5fa50146bc6) (e2717) (e1887)

private def e2719 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b8578195b133fac70a1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e2362) (replay_7c17c9803ae92cfc6233)

private def e2720 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5fea12cfa61bad1bf56c)

private def e2721 : C 9 :=
.trans (e2720) (e2720)

private def e2722 : C 9 :=
.trans (e2721) (e2720)

private def e2723 : C 9 :=
.trans (e2722) (e2720)

private def e2724 : C 9 :=
.trans (e2723) (e2720)

private def e2725 : C 9 :=
.trans (e2724) (e2720)

private def e2726 : C 9 :=
.trans (e2725) (e2720)

private def e2727 : S 9 :=
.congPiDom (e2571) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05)

private def e2728 : C 9 :=
.single (e2727)

private def e2730 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7cdace3f96c8deb3f1be)

private def e2731 : C 9 :=
.trans (e2730) (e2730)

private def e2732 : S 9 :=
.congPiDom (e2579) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05)

private def e2733 : C 9 :=
.single (e2732)

private def e2735 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a89ec9758c4073f44f86)

private def e2736 : C 9 :=
.trans (e2733) (e2735)

private def e2737 : C 9 :=
.trans (e2731) (e2736)

private def e2738 : C 9 :=
.trans (e2737) (e2735)

private def e2739 : S 9 :=
.congPiDom (e2587) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05)

private def e2740 : C 9 :=
.single (e2739)

private def e2742 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_309821db71729e0eae96)

private def e2743 : C 9 :=
.trans (e2740) (e2742)

private def e2744 : C 9 :=
.trans (e2738) (e2743)

private def e2745 : C 9 :=
.trans (e2744) (e2742)

private def e2746 : S 9 :=
.congPiDom (e2595) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05)

private def e2747 : C 9 :=
.single (e2746)

private def e2749 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cfd254b2eb053d0aadbf)

private def e2750 : C 9 :=
.trans (e2747) (e2749)

private def e2751 : C 9 :=
.trans (e2745) (e2750)

private def e2752 : C 9 :=
.trans (e2751) (e2749)

private def e2753 : S 9 :=
.congPiDom (e2603) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05)

private def e2754 : C 9 :=
.single (e2753)

private def e2756 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_539d335a041a831a475b)

private def e2757 : C 9 :=
.trans (e2754) (e2756)

private def e2758 : C 9 :=
.trans (e2752) (e2757)

private def e2759 : C 9 :=
.trans (e2728) (e2758)

private def e2760 : C 9 :=
.trans (e2726) (e2759)

private def e2761 : C 9 :=
.trans (e2756) (e2756)

private def e2762 : S 9 :=
.congPiDom (e2614) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05)

private def e2763 : C 9 :=
.single (e2762)

private def e2765 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0329168d01f574932469)

private def e2766 : C 9 :=
.trans (e2763) (e2765)

private def e2767 : C 9 :=
.trans (e2761) (e2766)

private def e2768 : C 9 :=
.symm (e2765)

private def e2769 : C 9 :=
.trans (e2765) (e2768)

private def e2770 : C 9 :=
.trans (e2767) (e2769)

private def e2771 : C 9 :=
.trans (e2770) (e2765)

private def e2772 : C 9 :=
.trans (e2771) (e2768)

private def e2773 : C 9 :=
.trans (e2760) (e2772)

private def e2774 : C 9 :=
.trans (e2773) (e2765)

private def e2775 : C 9 :=
.trans (e2774) (e2768)

private def e2776 : C 9 :=
.trans (e2720) (e2775)

private def e2777 : T 9 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5fea12cfa61bad1bf56c) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f0f123abfc5045ff007f) (e2718) (e2719) (e2776)

private def e2778 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53a3d94e880c845f90cc) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05) (e2777) (replay_07c41680d17703d7171f)

private def e2779 : T 9 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1865) (e2708) (e2778)

private def e2780 : T 8 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b8578195b133fac70a1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1858) (e2779)

private def e2781 : T 7 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23e09003749289e9f868) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f0f123abfc5045ff007f) (e1644) (e2780)

private def e2782 : T 6 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_66455137451fba038b86) (replay_629e69ece1b1fb7e3753) (e2781)

private def e2783 : T 5 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1bfe7411e0715fdc3608) (replay_088a7fed4563d6a06e7a) (e2782)

private def e2784 : T 4 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beabd34e09ddd5a95e6a) (replay_909a1aacbbe83fd007eb) (e2783)

private def e2803 : T 3 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (replay_8ac3920e24449662ac7d) (replay_8ac3920e24449662ac7d) (replay_8ac3920e24449662ac7d)

private def e2804 : T 3 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4f93e456b4620d589d9) (e2803) (replay_9a8c52ee0ece732b2898)

private def e2805 : T 2 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9d09888446f1f703992) (replay_67648559da2b4f1cdeb2) (e2804)

private def e2810 : T 3 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_00835ccb59a9bb61fd8d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81c1a64876d9dea24387) (replay_8ac3920e24449662ac7d) (replay_8ac3920e24449662ac7d)

private def e2811 : T 3 :=
.reflIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_00835ccb59a9bb61fd8d) (replay_8ac3920e24449662ac7d)

private def e2812 : T 3 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_00dff80d06855bd328ad) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b85ac78fceba4809d7ed) (e2810) (e2811)

private def e2814 : T 5 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (replay_088a7fed4563d6a06e7a) (replay_088a7fed4563d6a06e7a) (replay_088a7fed4563d6a06e7a)

private def e2818 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_987df36b061ff751f22f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4e15442c25f694629c07) (replay_fb92de9ad2d284eba393) (replay_fb92de9ad2d284eba393)

private def e2819 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_178acf133714c5a1a603) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d0f4a08c893ea38d53fb) (e2818) (replay_fb92de9ad2d284eba393)

private def e2820 : T 5 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (e2814) (e2819)

private def e2821 : T 4 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e979c982a49a5e779dc2) (replay_f89a0d3fd4af1bf7786d) (e2820)

private def e2822 : T 3 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_42723fb932d076f649b0) (e2812) (e2821)

private def e2823 : T 2 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8140b3a563a0f9321107) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e88e4a70c4eab7de114f) (e2805) (e2822)

private def e2824 : T 1 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cb951c7f04492ec430ee) (replay_579b334deaab55db1c09) (e2823)

private def e2825 : T 0 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4f93e456b4620d589d9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_11fb8744af12c4e1d0c2) (replay_7a268c731e7a9afff236) (e2824)

private def e2826 : T 9 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e1361a4a26f6d05e372) (e2825)

private def e2828 : T 9 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_6377a49faab46f0b3589)

private def e2829 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23593caaab521d12b976) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a18fc26955d8ed2dbbac) (e2826) (e2828)

private def e2832 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e056103386ad05d9d9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c3d172b4624b6e11b26d) (e1877) (replay_07c41680d17703d7171f)

private def e2833 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58bdea1e3c28d008f853) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_aa49eda6ae6da9b5a162) (e2832) (replay_07c41680d17703d7171f)

private def e2835 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e056103386ad05d9d9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3a498e1101a964a28c24) (e2196) (replay_07c41680d17703d7171f)

private def e2836 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58bdea1e3c28d008f853) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46868324d5724081a32a) (e2835) (replay_07c41680d17703d7171f)

private def e2838 : T 9 :=
.sndElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_198d6bd75ff0377bcd7c) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e9c073bd7cf6856c0f8) (replay_07c41680d17703d7171f)

private def e2839 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c147bd3db1fd948411b6) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9530908dcf6c5275717) (e2836) (e2838)

private def e2840 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91a3417e737975260050) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7acbea17057f912a2e1f) (e2833) (e2839)

private def e2841 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43cd7be8392b3b43057e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2a40f50a9220bc974333) (e2829) (e2840)

private def e2850 : T 10 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd72d6a3055c3dc99790) (e621)

private def e2851 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b74e03acbfc24aeb10e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_55b9dc90ea76ca684af0) (e2850) (replay_8dd06e568960d2567ea5)

private def e2852 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f1eda03ec62354b37392) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fa8467eba76e35aa670f) (e2851) (replay_8dd06e568960d2567ea5)

private def e2853 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ffbcdddae5a4ba50f754) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4435115370761c68ffed) (e2852) (replay_8dd06e568960d2567ea5)

private def e2854 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_de0d936cd54f5c2b0737) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_07c82b89542f1a60ac75) (e2853) (replay_8dd06e568960d2567ea5)

private def e2860 : T 10 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05b86c587b7291cc54) (e1004)

private def e2861 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b74e03acbfc24aeb10e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f2f723e3d4ab04de6a3b) (e2860) (replay_8dd06e568960d2567ea5)

private def e2862 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5788cbd50333d7cba0b5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f3f8b5dabf41ee3b7a5b) (e2861) (e372)

private def e2863 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ffbcdddae5a4ba50f754) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_13ff2074f137754fa841) (e2862) (replay_8dd06e568960d2567ea5)

private def e2864 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_de0d936cd54f5c2b0737) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f5c9f180a5df98b3f6bb) (e2863) (replay_8dd06e568960d2567ea5)

private def e2866 : T 10 :=
.sndElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e48b53379ef509db2cd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6070d91bc17ad1d91bc8) (replay_8dd06e568960d2567ea5)

private def e2867 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e9c073bd7cf6856c0f8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_151601d70406d501031f) (e2864) (e2866)

private def e2868 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9530908dcf6c5275717) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5b38fe4a9e893712e8f5) (e2854) (e2867)

private def e2869 : T 10 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_38dd6b1b76e4eaa10164) (e2868) (replay_8dd06e568960d2567ea5)

private def e2870 : T 10 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4f93e456b4620d589d9) (e2869) (replay_e78213c920befa21e944)

private def e2871 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_acf7017ce42f9b0db39d) (replay_6377a49faab46f0b3589) (e2870)

private def e2880 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1bed53fd97751c172144) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1f7880e8737675c0efb8) (replay_d652d74b2d50fe7ed68a) (replay_7fbeba8818273106d8c8)

private def e2883 : T 12 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (replay_c1e92b3aeffe2c000a2a)

private def e2884 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1f7880e8737675c0efb8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_df5cbd2db79ad5eed082) (replay_d54011a6a8cb2a23b315) (e2883)

private def e2887 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_76bf2a76d66e1cc66026) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f7cab4144f5b47bea6ec) (e2884) (replay_5e73c6d8d007958b70e4)

private def e2888 : T 11 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e2880) (e2887)

private def e2911 : T 12 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_09b47c13d4d45db21f0e) (replay_6e057c2b1ec3bcbf6efc)

private def e2912 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1f7880e8737675c0efb8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a9bac2d8483eb2361229) (e2911) (e2883)

private def e2913 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_76bf2a76d66e1cc66026) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_86fff67b47fbe4cd99f0) (e2912) (replay_c1e92b3aeffe2c000a2a)

private def e2915 : T 12 :=
.fstElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_89e69438b08397b3b26c) (replay_c1e92b3aeffe2c000a2a)

private def e2916 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cbd13c1b0d830c739b7) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_061d46b0be70038a96e4) (e2913) (e2915)

private def e2917 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a7c6077368bfe7e62c76) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_34dba01e61e8a9ddf283) (e2916) (replay_c1e92b3aeffe2c000a2a)

private def e2918 : T 11 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23e09003749289e9f868) (e2888) (e2917)

private def e2923 : T 11 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd72d6a3055c3dc99790) (e621)

private def e2924 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9528e48ce4f30ad868d8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ed3d94411ef4bf7debc6) (e2923) (replay_7fbeba8818273106d8c8)

private def e2925 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e8e4b831c3ede895f4ee) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1d285175f7e2f048d272) (e2924) (replay_7fbeba8818273106d8c8)

private def e2926 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1bed53fd97751c172144) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_593dd3fefd54cf6e0cb1) (e2925) (replay_7fbeba8818273106d8c8)

private def e2927 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4e0bd14f54be2011bbdb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cec34bae2ebc177b1b5c) (e2926) (replay_7fbeba8818273106d8c8)

private def e2934 : T 11 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05b86c587b7291cc54) (e1004)

private def e2935 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9528e48ce4f30ad868d8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_45de3f87d637131f7c21) (e2934) (replay_7fbeba8818273106d8c8)

private def e2936 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_93bc1dc99b942fdecf01) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_139f85dac93b441234bc) (e2935) (replay_b7c1a32946869ad8b824)

private def e2937 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1bed53fd97751c172144) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47d8478054a39bbe7081) (e2936) (replay_7fbeba8818273106d8c8)

private def e2938 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4e0bd14f54be2011bbdb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3baa57bfa49a374cb598) (e2937) (replay_7fbeba8818273106d8c8)

private def e2940 : T 11 :=
.sndElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8304ec2301382ae96f36) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b006f548fe947033feb3) (replay_7fbeba8818273106d8c8)

private def e2941 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6070d91bc17ad1d91bc8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0caf5b45b395fbd0200b) (e2938) (e2940)

private def e2942 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_151601d70406d501031f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a7c6077368bfe7e62c76) (e2927) (e2941)

private def e2943 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5b38fe4a9e893712e8f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_aa0a81f376b61e120915) (e2918) (e2942)

private def e2944 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5b38fe4a9e893712e8f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_aa0a81f376b61e120915) (e2918) (replay_7fbeba8818273106d8c8)

private def e2945 : T 11 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_96656f23ea73a7756060) (e2943) (e2944)

private def e2946 : T 11 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e2945)

private def e2947 : T 10 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_acf7017ce42f9b0db39d) (e2870) (e2946)

private def e2948 : T 9 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_355f5fe51b324cac9ec6) (e2871) (e2947)

private def e2949 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4dbff59f06325eb1b2d4) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c4b8cd1cd40b8dfd83fd) (e2841) (e2948)

private def e2950 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_6377a49faab46f0b3589) (replay_7c17c9803ae92cfc6233)

private def e2958 : T 10 :=
.fstElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6070d91bc17ad1d91bc8) (replay_8dd06e568960d2567ea5)

private def e2959 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e48b53379ef509db2cd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_01b217c61da8aff85c88) (replay_b9c16285c0fa5ea2d735) (e2958)

private def e2960 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7acbea17057f912a2e1f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2dad9618308ff0113d64) (e2959) (replay_8dd06e568960d2567ea5)

private def e2961 : T 9 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23e09003749289e9f868) (e2950) (e2960)

private def e2962 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43cd7be8392b3b43057e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05) (e2961) (e2840)

private def e2963 : T 9 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1865) (e2962) (e2962)

private def e2964 : T 11 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e2880) (e2942) (replay_7fbeba8818273106d8c8)

private def e2965 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_76bf2a76d66e1cc66026) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f7cab4144f5b47bea6ec) (e2884) (replay_c1e92b3aeffe2c000a2a)

private def e2968 : T 13 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (replay_8dab544be16d5febf71b)

private def e2969 : T 13 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f7cab4144f5b47bea6ec) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_785d470a04a6647bb790) (replay_4066fb5b33379c35f222) (e2968)

private def e2970 : T 13 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2ff527e667e033dd20bc) (replay_b09ed5596b6916f74be9)

private def e2971 : T 13 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c2c7c8a4e5915c01ed88) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d7f6d5bd6ff0bc695995) (e2970) (replay_8dab544be16d5febf71b)

private def e2972 : T 13 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c2c7c8a4e5915c01ed88) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d73181edcb26dbe55a02) (e2969) (e2971)

private def e2973 : T 12 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e2965) (e2972)

private def e2980 : T 13 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_09b47c13d4d45db21f0e) (replay_6e057c2b1ec3bcbf6efc)

private def e2981 : T 13 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f7cab4144f5b47bea6ec) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2c4ba7cc84cba0b9c602) (e2980) (e2968)

private def e2982 : T 13 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c2c7c8a4e5915c01ed88) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0d5c2f698b2ca08e586b) (e2981) (replay_8dab544be16d5febf71b)

private def e2984 : T 13 :=
.fstElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_444a26688edced543b77) (replay_8dab544be16d5febf71b)

private def e2985 : T 13 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_63be3dfe28f667bec1df) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3c1b34a96babe84579aa) (e2982) (e2984)

private def e2986 : T 13 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4d666b839df4228f54d6) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9aaa273cc8e63d451349) (e2985) (replay_8dab544be16d5febf71b)

private def e2987 : T 12 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23e09003749289e9f868) (e2973) (e2986)

private def e2993 : T 12 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd72d6a3055c3dc99790) (e621)

private def e2994 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dd4fc597f6a31798810d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3dbe69f1b7ded9613e0d) (e2993) (replay_c1e92b3aeffe2c000a2a)

private def e2995 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f0e9a76be79e0b80849) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4a78b217a07e51d48579) (e2994) (replay_c1e92b3aeffe2c000a2a)

private def e2996 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_76bf2a76d66e1cc66026) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_867458a58ba4e4a8ce08) (e2995) (replay_c1e92b3aeffe2c000a2a)

private def e2997 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fe88179aa6c8dfa346aa) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_24d698de3ff209428a49) (e2996) (replay_c1e92b3aeffe2c000a2a)

private def e3004 : T 12 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05b86c587b7291cc54) (e1004)

private def e3005 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dd4fc597f6a31798810d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f7ea1fe3f5c18dcf547c) (e3004) (replay_c1e92b3aeffe2c000a2a)

private def e3006 : T 12 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd68df30b6526d2aba98) (replay_c1e92b3aeffe2c000a2a) (replay_13cf0c5003c2ff085491)

private def e3007 : T 12 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_80d7abfcb57830595ef4) (e3006) (replay_8dab544be16d5febf71b)

private def e3008 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5a2c5de69dc02b98119c) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_669b2d3b07fa630ad123) (e3005) (e3007)

private def e3009 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_76bf2a76d66e1cc66026) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_240ad5c9056ba654f71c) (e3008) (replay_c1e92b3aeffe2c000a2a)

private def e3010 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fe88179aa6c8dfa346aa) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d08050522e74f57393f2) (e3009) (replay_c1e92b3aeffe2c000a2a)

private def e3011 : T 12 :=
.sndElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cbd13c1b0d830c739b7) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_89e69438b08397b3b26c) (replay_c1e92b3aeffe2c000a2a)

private def e3012 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b006f548fe947033feb3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1d9546e4677c786bbc69) (e3010) (e3011)

private def e3013 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0caf5b45b395fbd0200b) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4d666b839df4228f54d6) (e2997) (e3012)

private def e3014 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a7c6077368bfe7e62c76) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_34dba01e61e8a9ddf283) (e2987) (e3013)

private def e3015 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a7c6077368bfe7e62c76) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_34dba01e61e8a9ddf283) (e2987) (replay_c1e92b3aeffe2c000a2a)

private def e3016 : T 12 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e2887) (e3014) (e3015)

private def e3017 : T 11 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e2964) (e3016)

private def e3018 : T 10 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23e09003749289e9f868) (replay_38dd6b1b76e4eaa10164) (e3017)

private def e3019 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_833055146ebc3616f75b) (e2963) (e3018)

private def e3020 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f06e046f1e5659359c2)

private def e3021 : C 9 :=
.trans (e3020) (e3020)

private def e3024 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e1b369f06b42c194f64e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3026 : S 9 :=
.congAppFun (e3024) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_676cb4918483cca919bf)

private def e3028 : S 9 :=
.congPiDom (e3026) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58fd50ec2e31064d341c)

private def e3029 : C 9 :=
.single (e3028)

private def e3031 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9f25a1e03df65a1dd21)

private def e3032 : C 9 :=
.trans (e3029) (e3031)

private def e3033 : C 9 :=
.trans (e3021) (e3032)

private def e3034 : C 9 :=
.trans (e3033) (e3031)

private def e3036 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_176fa5d6a3a7ab536af8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_676cb4918483cca919bf)

private def e3037 : S 9 :=
.congPiDom (e3036) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58fd50ec2e31064d341c)

private def e3038 : C 9 :=
.single (e3037)

private def e3040 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83bef5d70c6323d42a13)

private def e3041 : C 9 :=
.trans (e3038) (e3040)

private def e3042 : C 9 :=
.trans (e3034) (e3041)

private def e3043 : C 9 :=
.symm (e3040)

private def e3044 : C 9 :=
.trans (e3040) (e3043)

private def e3045 : C 9 :=
.trans (e3042) (e3044)

private def e3046 : C 9 :=
.trans (e3040) (e3040)

private def e3050 : S 12 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_745ed1840054d3c3275b) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2f252033ccef6a6a834a)

private def e3052 : S 12 :=
.congAppFun (e3050) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f6020bec2f79974210d6)

private def e3053 : S 11 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bffc762a78ee55672e43) (e3052)

private def e3054 : S 10 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7acbea17057f912a2e1f) (e3053)

private def e3055 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8707bb823eda37d85d61) (e3054)

private def e3056 : C 9 :=
.single (e3055)

private def e3058 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2e0e29a4add00986797b)

private def e3059 : C 9 :=
.trans (e3056) (e3058)

private def e3060 : C 9 :=
.trans (e3046) (e3059)

private def e3061 : C 9 :=
.trans (e3060) (e3058)

private def e3063 : S 12 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_758ceb9172ca1b424f6d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f6020bec2f79974210d6)

private def e3064 : S 11 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bffc762a78ee55672e43) (e3063)

private def e3065 : S 10 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7acbea17057f912a2e1f) (e3064)

private def e3066 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8707bb823eda37d85d61) (e3065)

private def e3067 : C 9 :=
.single (e3066)

private def e3069 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_928e0aa1c72b1667f890)

private def e3070 : C 9 :=
.trans (e3067) (e3069)

private def e3071 : C 9 :=
.trans (e3061) (e3070)

private def e3072 : C 9 :=
.symm (e3069)

private def e3073 : C 9 :=
.trans (e3069) (e3072)

private def e3074 : C 9 :=
.trans (e3071) (e3073)

private def e3075 : C 9 :=
.trans (e3040) (e3074)

private def e3076 : C 9 :=
.trans (e3075) (e3072)

private def e3077 : C 9 :=
.trans (e3040) (e3076)

private def e3078 : C 9 :=
.trans (e3040) (e3077)

private def e3079 : C 9 :=
.trans (e3078) (e3072)

private def e3080 : C 9 :=
.trans (e3040) (e3079)

private def e3081 : C 9 :=
.trans (e3045) (e3080)

private def e3082 : C 9 :=
.trans (e3081) (e3072)

private def e3083 : C 9 :=
.trans (e3020) (e3082)

private def e3084 : T 9 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f06e046f1e5659359c2) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_12f905a83669d167121c) (e2949) (e3019) (e3083)

private def e3086 : T 9 :=
.reflIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e2962)

private def e3087 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8707bb823eda37d85d61) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7956c485ab2e3d6ed2e2) (e3084) (e3086)

private def e3089 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e056103386ad05d9d9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_25a79c6a512df03ceac3) (e2716) (replay_07c41680d17703d7171f)

private def e3090 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58bdea1e3c28d008f853) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cdd00d5c8ca522367f0f) (e3089) (replay_07c41680d17703d7171f)

private def e3091 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c147bd3db1fd948411b6) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7acbea17057f912a2e1f) (e3090) (e2838)

private def e3092 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43cd7be8392b3b43057e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_18fb3e7bb1e7781ab5fd) (e3087) (e3091)

private def e3094 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c147bd3db1fd948411b6) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2f89518f608f0ee6e0e8) (replay_07c41680d17703d7171f) (e2838)

private def e3095 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a9523ff5b2f4bb053b85) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2e934858c006d366d528) (e3092) (e3094)

private def e3096 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_87dafa7fe183795b389a)

private def e3097 : C 9 :=
.trans (e3096) (e3096)

private def e3099 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ff7f49280c21442dc691) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3101 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3099) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3102 : C 9 :=
.single (e3101)

private def e3104 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_edf6bcdb32deac233a46)

private def e3105 : C 9 :=
.trans (e3104) (e3104)

private def e3106 : C 9 :=
.trans (e3105) (e3104)

private def e3107 : C 9 :=
.trans (e3106) (e3104)

private def e3108 : C 9 :=
.trans (e3107) (e3104)

private def e3109 : C 9 :=
.trans (e3102) (e3108)

private def e3110 : C 9 :=
.trans (e3097) (e3109)

private def e3112 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d1cd79c339065c280eec)

private def e3114 : decoder.Code 9 :=
.delta (`CumulativeTower.AllEvidence.raise)

private def e3115 : S 9 :=
.root (e3114)

private def e3116 : S 9 :=
.congAppFun (e3115) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e2c1e2e15bb0cda87a)

private def e3118 : S 9 :=
.congAppFun (e3116) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05cfdcba93e50df46b)

private def e3120 : S 9 :=
.congAppFun (e3118) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e3122 : S 9 :=
.congAppFun (e3120) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3123 : S 9 :=
.congAppFun (e3122) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3124 : S 9 :=
.congFst (e3123)

private def e3125 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e3124)

private def e3126 : S 9 :=
.congAppFun (e3125) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3127 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3126) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3128 : C 9 :=
.single (e3127)

private def e3130 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_252fb9388060c783a0a2)

private def e3131 : C 9 :=
.trans (e3128) (e3130)

private def e3132 : C 9 :=
.trans (e3112) (e3131)

private def e3133 : C 9 :=
.trans (e3132) (e3130)

private def e3135 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbd241c12d2ee675fdc7) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e2c1e2e15bb0cda87a)

private def e3136 : S 9 :=
.congAppFun (e3135) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05cfdcba93e50df46b)

private def e3137 : S 9 :=
.congAppFun (e3136) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e3138 : S 9 :=
.congAppFun (e3137) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3139 : S 9 :=
.congAppFun (e3138) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3140 : S 9 :=
.congFst (e3139)

private def e3141 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e3140)

private def e3142 : S 9 :=
.congAppFun (e3141) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3143 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3142) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3144 : C 9 :=
.single (e3143)

private def e3146 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_489af1d1c897a33775af)

private def e3147 : C 9 :=
.trans (e3144) (e3146)

private def e3148 : C 9 :=
.trans (e3133) (e3147)

private def e3149 : C 9 :=
.trans (e3148) (e3146)

private def e3151 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb977ceb6d257baeaed3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05cfdcba93e50df46b)

private def e3152 : S 9 :=
.congAppFun (e3151) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e3153 : S 9 :=
.congAppFun (e3152) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3154 : S 9 :=
.congAppFun (e3153) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3155 : S 9 :=
.congFst (e3154)

private def e3156 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e3155)

private def e3157 : S 9 :=
.congAppFun (e3156) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3158 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3157) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3159 : C 9 :=
.single (e3158)

private def e3161 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_285f39b8cfe4eb504506)

private def e3162 : C 9 :=
.trans (e3159) (e3161)

private def e3163 : C 9 :=
.trans (e3149) (e3162)

private def e3164 : C 9 :=
.trans (e3163) (e3161)

private def e3166 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62c0b114846e66e27825) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e3167 : S 9 :=
.congAppFun (e3166) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3168 : S 9 :=
.congAppFun (e3167) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3169 : S 9 :=
.congFst (e3168)

private def e3170 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e3169)

private def e3171 : S 9 :=
.congAppFun (e3170) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3172 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3171) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3173 : C 9 :=
.single (e3172)

private def e3175 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7dff26ba96b3b37838c2)

private def e3176 : C 9 :=
.trans (e3173) (e3175)

private def e3177 : C 9 :=
.trans (e3164) (e3176)

private def e3178 : C 9 :=
.trans (e3177) (e3175)

private def e3180 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b49376c9dff958f4c5ef) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3181 : S 9 :=
.congAppFun (e3180) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3182 : S 9 :=
.congFst (e3181)

private def e3183 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e3182)

private def e3184 : S 9 :=
.congAppFun (e3183) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3185 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3184) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3186 : C 9 :=
.single (e3185)

private def e3188 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cf5e1888e5d86b5f15a5)

private def e3189 : C 9 :=
.trans (e3188) (e3188)

private def e3190 : C 9 :=
.trans (e3189) (e3188)

private def e3191 : C 9 :=
.trans (e3190) (e3188)

private def e3192 : C 9 :=
.trans (e3191) (e3188)

private def e3193 : C 9 :=
.trans (e3192) (e3188)

private def e3194 : C 9 :=
.trans (e3193) (e3188)

private def e3195 : decoder.Code 9 :=
.inherited (.declared (.inl (.inl ⟨3, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pair
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.fst
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.snd
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                     `CumulativeTower.Vec.eliminate)
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2)))))))
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                   `CumulativeTower.Nat.zero)))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 14))
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                     `CumulativeTower.Vec.eliminate)
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 11))
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2))
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 3)))))))
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                   `CumulativeTower.Nat.zero)))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 15))
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8]⟩)))

private def e3196 : S 9 :=
.root (e3195)

private def e3197 : S 9 :=
.congAppFun (e3196) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3198 : S 9 :=
.congFst (e3197)

private def e3199 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e3198)

private def e3200 : S 9 :=
.congAppFun (e3199) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3201 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3200) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3202 : C 9 :=
.single (e3201)

private def e3204 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b0c30d1b7d2459bcbef)

private def e3205 : C 9 :=
.trans (e3204) (e3204)

private def e3207 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6298d5a9a5fb70600c5e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3208 : S 9 :=
.congAppFun (e3207) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea50578066f1875556e5)

private def e3209 : S 9 :=
.congAppFun (e3208) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3211 : S 9 :=
.congAppFun (e3209) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d12413b5519ee2f5b8e8)

private def e3212 : S 9 :=
.congAppFun (e3211) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3213 : S 9 :=
.congFst (e3212)

private def e3214 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e3213)

private def e3215 : S 9 :=
.congAppFun (e3214) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3216 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3215) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3217 : C 9 :=
.single (e3216)

private def e3219 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7cef028fb9ed2f9bc8d5)

private def e3220 : C 9 :=
.trans (e3217) (e3219)

private def e3221 : C 9 :=
.trans (e3205) (e3220)

private def e3222 : C 9 :=
.trans (e3221) (e3219)

private def e3224 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_80e9f87ead83ce958248) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea50578066f1875556e5)

private def e3225 : S 9 :=
.congAppFun (e3224) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3226 : S 9 :=
.congAppFun (e3225) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d12413b5519ee2f5b8e8)

private def e3227 : S 9 :=
.congAppFun (e3226) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3228 : S 9 :=
.congFst (e3227)

private def e3229 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e3228)

private def e3230 : S 9 :=
.congAppFun (e3229) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3231 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3230) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3232 : C 9 :=
.single (e3231)

private def e3234 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e9fa294d6bc14334d9)

private def e3235 : C 9 :=
.trans (e3232) (e3234)

private def e3236 : C 9 :=
.trans (e3222) (e3235)

private def e3237 : C 9 :=
.trans (e3236) (e3234)

private def e3239 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a11c7096ed6dbb3b5f3c) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3240 : S 9 :=
.congAppFun (e3239) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d12413b5519ee2f5b8e8)

private def e3241 : S 9 :=
.congAppFun (e3240) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3242 : S 9 :=
.congFst (e3241)

private def e3243 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e3242)

private def e3244 : S 9 :=
.congAppFun (e3243) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3245 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3244) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3246 : C 9 :=
.single (e3245)

private def e3248 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c50d6aee3bbc81ddd0f8)

private def e3249 : C 9 :=
.trans (e3246) (e3248)

private def e3250 : C 9 :=
.trans (e3237) (e3249)

private def e3251 : C 9 :=
.trans (e3250) (e3248)

private def e3253 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8e97b24d23d0cb38a5d9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d12413b5519ee2f5b8e8)

private def e3254 : S 9 :=
.congAppFun (e3253) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3255 : S 9 :=
.congFst (e3254)

private def e3256 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e3255)

private def e3257 : S 9 :=
.congAppFun (e3256) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3258 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3257) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3259 : C 9 :=
.single (e3258)

private def e3261 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9637328a4df87feb18ae)

private def e3262 : C 9 :=
.trans (e3259) (e3261)

private def e3263 : C 9 :=
.trans (e3251) (e3262)

private def e3264 : C 9 :=
.trans (e3202) (e3263)

private def e3265 : C 9 :=
.trans (e3194) (e3264)

private def e3266 : C 9 :=
.trans (e3186) (e3265)

private def e3267 : C 9 :=
.trans (e3178) (e3266)

private def e3268 : C 9 :=
.trans (e3267) (e3261)

private def e3270 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f6f65389ccfda695bbcf) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3271 : S 9 :=
.congFst (e3270)

private def e3272 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e3271)

private def e3273 : S 9 :=
.congAppFun (e3272) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3274 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3273) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3275 : C 9 :=
.single (e3274)

private def e3277 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c4588576eb26428fce02)

private def e3278 : C 9 :=
.trans (e3275) (e3277)

private def e3279 : C 9 :=
.trans (e3268) (e3278)

private def e3282 : S 9 :=
.betaSigmaFst (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a97388c54c77a8f2aaf2) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8bf21fc4c2eeac97045e)

private def e3283 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e3282)

private def e3284 : S 9 :=
.congAppFun (e3283) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e60cc1a5b8bc4e8f1cce)

private def e3285 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3284) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3286 : C 9 :=
.single (e3285)

private def e3287 : C 9 :=
.trans (e3286) (e3104)

private def e3288 : C 9 :=
.trans (e3279) (e3287)

private def e3289 : C 9 :=
.symm (e3288)

private def e3290 : C 9 :=
.trans (e3104) (e3289)

private def e3291 : C 9 :=
.trans (e3104) (e3290)

private def e3292 : C 9 :=
.trans (e3104) (e3291)

private def e3293 : C 9 :=
.trans (e3112) (e3112)

private def e3294 : C 9 :=
.trans (e3293) (e3112)

private def e3295 : C 9 :=
.trans (e3294) (e3112)

private def e3296 : C 9 :=
.symm (e3295)

private def e3297 : C 9 :=
.trans (e3292) (e3296)

private def e3298 : C 9 :=
.trans (e3107) (e3297)

private def e3300 : decoder.Code 9 :=
.delta (`CumulativeTower.AllResults.upper)

private def e3301 : S 9 :=
.root (e3300)

private def e3302 : S 9 :=
.congAppFun (e3301) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e2c1e2e15bb0cda87a)

private def e3303 : S 9 :=
.congAppFun (e3302) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_198d6bd75ff0377bcd7c)

private def e3304 : S 9 :=
.congAppFun (e3303) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3305 : S 9 :=
.congAppFun (e3304) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3307 : S 9 :=
.congAppFun (e3305) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a77afe932411a4df5783)

private def e3308 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3307)

private def e3309 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3308) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3310 : C 9 :=
.single (e3309)

private def e3312 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f8cddd9f580b70049fdb)

private def e3313 : C 9 :=
.trans (e3310) (e3312)

private def e3314 : C 9 :=
.trans (e3112) (e3313)

private def e3315 : C 9 :=
.trans (e3314) (e3312)

private def e3317 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_39da0be559b561a5558e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e2c1e2e15bb0cda87a)

private def e3318 : S 9 :=
.congAppFun (e3317) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_198d6bd75ff0377bcd7c)

private def e3319 : S 9 :=
.congAppFun (e3318) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3320 : S 9 :=
.congAppFun (e3319) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3321 : S 9 :=
.congAppFun (e3320) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a77afe932411a4df5783)

private def e3322 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3321)

private def e3323 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3322) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3324 : C 9 :=
.single (e3323)

private def e3326 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6f0ce390e7a9ae1fda3e)

private def e3327 : C 9 :=
.trans (e3324) (e3326)

private def e3328 : C 9 :=
.trans (e3315) (e3327)

private def e3329 : C 9 :=
.trans (e3328) (e3326)

private def e3331 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d3c43c5206d04a81cd1b) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_198d6bd75ff0377bcd7c)

private def e3332 : S 9 :=
.congAppFun (e3331) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3333 : S 9 :=
.congAppFun (e3332) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3334 : S 9 :=
.congAppFun (e3333) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a77afe932411a4df5783)

private def e3335 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3334)

private def e3336 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3335) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3337 : C 9 :=
.single (e3336)

private def e3339 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cf907fb04968381d1956)

private def e3340 : C 9 :=
.trans (e3337) (e3339)

private def e3341 : C 9 :=
.trans (e3329) (e3340)

private def e3342 : C 9 :=
.trans (e3341) (e3339)

private def e3344 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f17fd2f5dcdcae4261ac) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3345 : S 9 :=
.congAppFun (e3344) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3346 : S 9 :=
.congAppFun (e3345) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a77afe932411a4df5783)

private def e3347 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3346)

private def e3348 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3347) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3349 : C 9 :=
.single (e3348)

private def e3351 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7cede3b6b9ea99641e38)

private def e3352 : C 9 :=
.trans (e3349) (e3351)

private def e3353 : C 9 :=
.trans (e3342) (e3352)

private def e3354 : C 9 :=
.trans (e3353) (e3351)

private def e3356 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a7e3dd50cdd17337b5b9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3357 : S 9 :=
.congAppFun (e3356) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a77afe932411a4df5783)

private def e3358 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3357)

private def e3359 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3358) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3360 : C 9 :=
.single (e3359)

private def e3362 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9b741c61865cd8201354)

private def e3363 : C 9 :=
.trans (e3360) (e3362)

private def e3364 : C 9 :=
.trans (e3354) (e3363)

private def e3365 : C 9 :=
.trans (e3364) (e3362)

private def e3367 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7476078b94842f347d61) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a77afe932411a4df5783)

private def e3368 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3367)

private def e3369 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3368) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3370 : C 9 :=
.single (e3369)

private def e3372 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_94fb65bcf741e36aa176)

private def e3373 : C 9 :=
.trans (e3372) (e3372)

private def e3374 : C 9 :=
.trans (e3373) (e3372)

private def e3375 : C 9 :=
.trans (e3374) (e3372)

private def e3376 : C 9 :=
.trans (e3375) (e3372)

private def e3377 : C 9 :=
.trans (e3376) (e3372)

private def e3378 : C 9 :=
.trans (e3377) (e3372)

private def e3379 : C 9 :=
.trans (e3378) (e3372)

private def e3380 : C 9 :=
.trans (e3370) (e3379)

private def e3381 : C 9 :=
.trans (e3365) (e3380)

private def e3383 : S 9 :=
.congAppFun (e3118) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3384 : S 9 :=
.congAppFun (e3383) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3386 : S 9 :=
.congAppFun (e3384) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e3387 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3386)

private def e3388 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3387)

private def e3389 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3388) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3390 : C 9 :=
.single (e3389)

private def e3392 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_49b8ca23b8e69e3e932a)

private def e3393 : C 9 :=
.trans (e3390) (e3392)

private def e3394 : C 9 :=
.trans (e3372) (e3393)

private def e3395 : C 9 :=
.trans (e3394) (e3392)

private def e3396 : S 9 :=
.congAppFun (e3136) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3397 : S 9 :=
.congAppFun (e3396) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3398 : S 9 :=
.congAppFun (e3397) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e3399 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3398)

private def e3400 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3399)

private def e3401 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3400) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3402 : C 9 :=
.single (e3401)

private def e3404 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a237e8d4a4ffc28a6417)

private def e3405 : C 9 :=
.trans (e3402) (e3404)

private def e3406 : C 9 :=
.trans (e3395) (e3405)

private def e3407 : C 9 :=
.trans (e3406) (e3404)

private def e3408 : S 9 :=
.congAppFun (e3151) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3409 : S 9 :=
.congAppFun (e3408) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3410 : S 9 :=
.congAppFun (e3409) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e3411 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3410)

private def e3412 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3411)

private def e3413 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3412) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3414 : C 9 :=
.single (e3413)

private def e3416 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d62683e84820e7331935)

private def e3417 : C 9 :=
.trans (e3414) (e3416)

private def e3418 : C 9 :=
.trans (e3407) (e3417)

private def e3419 : C 9 :=
.trans (e3418) (e3416)

private def e3420 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62c0b114846e66e27825) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3421 : S 9 :=
.congAppFun (e3420) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3422 : S 9 :=
.congAppFun (e3421) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e3423 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3422)

private def e3424 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3423)

private def e3425 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3424) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3426 : C 9 :=
.single (e3425)

private def e3428 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_acdc60822b6abe4f1cf9)

private def e3429 : C 9 :=
.trans (e3426) (e3428)

private def e3430 : C 9 :=
.trans (e3419) (e3429)

private def e3431 : C 9 :=
.trans (e3430) (e3428)

private def e3433 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cae4a7cdf132eb9a1fef) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3434 : S 9 :=
.congAppFun (e3433) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e3435 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3434)

private def e3436 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3435)

private def e3437 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3436) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3438 : C 9 :=
.single (e3437)

private def e3440 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_41f0b8ad9d73172994dc)

private def e3441 : C 9 :=
.trans (e3440) (e3440)

private def e3442 : C 9 :=
.trans (e3441) (e3440)

private def e3443 : C 9 :=
.trans (e3442) (e3440)

private def e3444 : C 9 :=
.trans (e3443) (e3440)

private def e3445 : C 9 :=
.trans (e3444) (e3440)

private def e3446 : C 9 :=
.trans (e3445) (e3440)

private def e3447 : C 9 :=
.trans (e3438) (e3446)

private def e3448 : C 9 :=
.trans (e3431) (e3447)

private def e3449 : C 9 :=
.trans (e3448) (e3440)

private def e3451 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_60879b885adda11d0d33)

private def e3452 : S 9 :=
.congSnd (e3123)

private def e3453 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3452)

private def e3454 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3453)

private def e3455 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3454) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3456 : C 9 :=
.single (e3455)

private def e3458 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e71191dbaae6691859ed)

private def e3459 : C 9 :=
.trans (e3456) (e3458)

private def e3460 : C 9 :=
.trans (e3451) (e3459)

private def e3461 : C 9 :=
.trans (e3460) (e3458)

private def e3462 : S 9 :=
.congSnd (e3139)

private def e3463 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3462)

private def e3464 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3463)

private def e3465 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3464) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3466 : C 9 :=
.single (e3465)

private def e3468 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d30af2ec82855493fa20)

private def e3469 : C 9 :=
.trans (e3466) (e3468)

private def e3470 : C 9 :=
.trans (e3461) (e3469)

private def e3471 : C 9 :=
.trans (e3470) (e3468)

private def e3472 : S 9 :=
.congSnd (e3154)

private def e3473 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3472)

private def e3474 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3473)

private def e3475 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3474) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3476 : C 9 :=
.single (e3475)

private def e3478 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_27ecb2f6b3a1fd6202c5)

private def e3479 : C 9 :=
.trans (e3476) (e3478)

private def e3480 : C 9 :=
.trans (e3471) (e3479)

private def e3481 : C 9 :=
.trans (e3480) (e3478)

private def e3482 : S 9 :=
.congSnd (e3168)

private def e3483 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3482)

private def e3484 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3483)

private def e3485 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3484) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3486 : C 9 :=
.single (e3485)

private def e3488 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_015710bc59c1fca432bb)

private def e3489 : C 9 :=
.trans (e3486) (e3488)

private def e3490 : C 9 :=
.trans (e3481) (e3489)

private def e3491 : C 9 :=
.trans (e3490) (e3488)

private def e3492 : S 9 :=
.congSnd (e3181)

private def e3493 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3492)

private def e3494 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3493)

private def e3495 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3494) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3496 : C 9 :=
.single (e3495)

private def e3498 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8b082009c2e20f8d17c4)

private def e3499 : C 9 :=
.trans (e3498) (e3498)

private def e3500 : C 9 :=
.trans (e3499) (e3498)

private def e3501 : C 9 :=
.trans (e3500) (e3498)

private def e3502 : C 9 :=
.trans (e3501) (e3498)

private def e3503 : C 9 :=
.trans (e3502) (e3498)

private def e3504 : C 9 :=
.trans (e3503) (e3498)

private def e3505 : S 9 :=
.congSnd (e3197)

private def e3506 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3505)

private def e3507 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3506)

private def e3508 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3507) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3509 : C 9 :=
.single (e3508)

private def e3511 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6a01e34e26647e5a0ec7)

private def e3512 : C 9 :=
.trans (e3511) (e3511)

private def e3513 : S 9 :=
.congSnd (e3212)

private def e3514 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3513)

private def e3515 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3514)

private def e3516 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3515) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3517 : C 9 :=
.single (e3516)

private def e3519 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_75cbfc4d67ede59e9a3e)

private def e3520 : C 9 :=
.trans (e3517) (e3519)

private def e3521 : C 9 :=
.trans (e3512) (e3520)

private def e3522 : C 9 :=
.trans (e3521) (e3519)

private def e3523 : S 9 :=
.congSnd (e3227)

private def e3524 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3523)

private def e3525 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3524)

private def e3526 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3525) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3527 : C 9 :=
.single (e3526)

private def e3529 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e38887d07b99016b5b08)

private def e3530 : C 9 :=
.trans (e3527) (e3529)

private def e3531 : C 9 :=
.trans (e3522) (e3530)

private def e3532 : C 9 :=
.trans (e3531) (e3529)

private def e3533 : S 9 :=
.congSnd (e3241)

private def e3534 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3533)

private def e3535 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3534)

private def e3536 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3535) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3537 : C 9 :=
.single (e3536)

private def e3539 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_381defcf1c1eff59dcd6)

private def e3540 : C 9 :=
.trans (e3537) (e3539)

private def e3541 : C 9 :=
.trans (e3532) (e3540)

private def e3542 : C 9 :=
.trans (e3541) (e3539)

private def e3543 : S 9 :=
.congSnd (e3254)

private def e3544 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3543)

private def e3545 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3544)

private def e3546 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3545) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3547 : C 9 :=
.single (e3546)

private def e3549 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b8eabe200afb2f4d6c99)

private def e3550 : C 9 :=
.trans (e3547) (e3549)

private def e3551 : C 9 :=
.trans (e3542) (e3550)

private def e3552 : C 9 :=
.trans (e3509) (e3551)

private def e3553 : C 9 :=
.trans (e3504) (e3552)

private def e3554 : C 9 :=
.trans (e3496) (e3553)

private def e3555 : C 9 :=
.trans (e3491) (e3554)

private def e3556 : C 9 :=
.trans (e3555) (e3549)

private def e3557 : S 9 :=
.congSnd (e3270)

private def e3558 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3557)

private def e3559 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3558)

private def e3560 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3559) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3561 : C 9 :=
.single (e3560)

private def e3563 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2c0fcbd9aa4503246510)

private def e3564 : C 9 :=
.trans (e3561) (e3563)

private def e3565 : C 9 :=
.trans (e3556) (e3564)

private def e3566 : S 9 :=
.betaSigmaSnd (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a97388c54c77a8f2aaf2) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8bf21fc4c2eeac97045e)

private def e3567 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c) (e3566)

private def e3568 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2b69e93975277451aec3) (e3567)

private def e3569 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3568) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3570 : C 9 :=
.single (e3569)

private def e3571 : C 9 :=
.trans (e3446) (e3440)

private def e3572 : C 9 :=
.trans (e3570) (e3571)

private def e3573 : C 9 :=
.trans (e3565) (e3572)

private def e3574 : C 9 :=
.symm (e3573)

private def e3575 : C 9 :=
.trans (e3440) (e3574)

private def e3576 : C 9 :=
.trans (e3449) (e3575)

private def e3577 : C 9 :=
.trans (e3372) (e3576)

private def e3578 : C 9 :=
.trans (e3451) (e3451)

private def e3579 : C 9 :=
.trans (e3578) (e3451)

private def e3580 : C 9 :=
.trans (e3579) (e3451)

private def e3581 : C 9 :=
.trans (e3580) (e3451)

private def e3582 : C 9 :=
.trans (e3581) (e3451)

private def e3583 : C 9 :=
.trans (e3582) (e3451)

private def e3584 : C 9 :=
.trans (e3583) (e3451)

private def e3585 : C 9 :=
.symm (e3584)

private def e3586 : C 9 :=
.trans (e3577) (e3585)

private def e3587 : C 9 :=
.trans (e3381) (e3586)

private def e3588 : C 9 :=
.trans (e3298) (e3587)

private def e3590 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f230e591f170db964327)

private def e3591 : S 9 :=
.congAppFun (e3303) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e3592 : S 9 :=
.congAppFun (e3591) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3594 : S 9 :=
.congAppFun (e3592) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8aca099393e9328f87a)

private def e3595 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3594) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3596 : C 9 :=
.single (e3595)

private def e3598 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_52bde167a4eeb8beda9c)

private def e3599 : C 9 :=
.trans (e3596) (e3598)

private def e3600 : C 9 :=
.trans (e3590) (e3599)

private def e3601 : C 9 :=
.trans (e3600) (e3598)

private def e3602 : S 9 :=
.congAppFun (e3318) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e3603 : S 9 :=
.congAppFun (e3602) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3604 : S 9 :=
.congAppFun (e3603) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8aca099393e9328f87a)

private def e3605 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3604) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3606 : C 9 :=
.single (e3605)

private def e3608 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_51f0b40d1e35cee50fb6)

private def e3609 : C 9 :=
.trans (e3606) (e3608)

private def e3610 : C 9 :=
.trans (e3601) (e3609)

private def e3611 : C 9 :=
.trans (e3610) (e3608)

private def e3612 : S 9 :=
.congAppFun (e3331) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e3613 : S 9 :=
.congAppFun (e3612) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3614 : S 9 :=
.congAppFun (e3613) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8aca099393e9328f87a)

private def e3615 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3614) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3616 : C 9 :=
.single (e3615)

private def e3618 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4febe5b10935bf91e111)

private def e3619 : C 9 :=
.trans (e3616) (e3618)

private def e3620 : C 9 :=
.trans (e3611) (e3619)

private def e3621 : C 9 :=
.trans (e3620) (e3618)

private def e3622 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f17fd2f5dcdcae4261ac) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e3623 : S 9 :=
.congAppFun (e3622) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3624 : S 9 :=
.congAppFun (e3623) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8aca099393e9328f87a)

private def e3625 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3624) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3626 : C 9 :=
.single (e3625)

private def e3628 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3fbc1431f2a9639a8a1c)

private def e3629 : C 9 :=
.trans (e3626) (e3628)

private def e3630 : C 9 :=
.trans (e3621) (e3629)

private def e3631 : C 9 :=
.trans (e3630) (e3628)

private def e3633 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1bdd7a14696c514a554f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3634 : S 9 :=
.congAppFun (e3633) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8aca099393e9328f87a)

private def e3635 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3634) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3636 : C 9 :=
.single (e3635)

private def e3638 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_515cf48e886f640c9e0d)

private def e3639 : C 9 :=
.trans (e3636) (e3638)

private def e3640 : C 9 :=
.trans (e3631) (e3639)

private def e3641 : C 9 :=
.trans (e3640) (e3638)

private def e3643 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_895d3c5c49bdc6689932) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8aca099393e9328f87a)

private def e3644 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3643) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3645 : C 9 :=
.single (e3644)

private def e3647 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_490b3a2bf9c513232d5c)

private def e3648 : C 9 :=
.trans (e3647) (e3647)

private def e3649 : C 9 :=
.trans (e3648) (e3647)

private def e3650 : C 9 :=
.trans (e3649) (e3647)

private def e3651 : C 9 :=
.trans (e3650) (e3647)

private def e3652 : C 9 :=
.trans (e3651) (e3647)

private def e3653 : C 9 :=
.trans (e3652) (e3647)

private def e3654 : decoder.Code 9 :=
.inherited (.declared (.inl (.inl ⟨3, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                     `CumulativeTower.VecUpper.cons)
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 12))
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.fst
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.snd
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.VecUpper.nil)
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                     `CumulativeTower.Vec.eliminate)
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2))
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 3)))))))
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                   `CumulativeTower.Nat.zero)))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 14))
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.VecUpper)
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8]⟩)))

private def e3655 : S 9 :=
.root (e3654)

private def e3656 : S 9 :=
.congAppFun (e3655) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8aca099393e9328f87a)

private def e3657 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3656) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3658 : C 9 :=
.single (e3657)

private def e3660 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6d1cc274db5f9716d51f)

private def e3661 : C 9 :=
.trans (e3660) (e3660)

private def e3663 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fc86d1408f182201808a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3664 : S 9 :=
.congAppFun (e3663) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea50578066f1875556e5)

private def e3665 : S 9 :=
.congAppFun (e3664) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3666 : S 9 :=
.congAppFun (e3665) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c)

private def e3667 : S 9 :=
.congAppFun (e3666) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8aca099393e9328f87a)

private def e3668 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3667) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3669 : C 9 :=
.single (e3668)

private def e3671 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b5aa2145121e6017b196)

private def e3672 : C 9 :=
.trans (e3669) (e3671)

private def e3673 : C 9 :=
.trans (e3661) (e3672)

private def e3674 : C 9 :=
.trans (e3673) (e3671)

private def e3676 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2c80f0b7baf74584180d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea50578066f1875556e5)

private def e3677 : S 9 :=
.congAppFun (e3676) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3678 : S 9 :=
.congAppFun (e3677) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c)

private def e3679 : S 9 :=
.congAppFun (e3678) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8aca099393e9328f87a)

private def e3680 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3679) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3681 : C 9 :=
.single (e3680)

private def e3683 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5dee4707412c369b7e5f)

private def e3684 : C 9 :=
.trans (e3681) (e3683)

private def e3685 : C 9 :=
.trans (e3674) (e3684)

private def e3686 : C 9 :=
.trans (e3685) (e3683)

private def e3688 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b140272fe91f42a981df) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3689 : S 9 :=
.congAppFun (e3688) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c)

private def e3690 : S 9 :=
.congAppFun (e3689) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8aca099393e9328f87a)

private def e3691 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3690) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3692 : C 9 :=
.single (e3691)

private def e3694 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ca2246370b9a5a1d4b8e)

private def e3695 : C 9 :=
.trans (e3692) (e3694)

private def e3696 : C 9 :=
.trans (e3686) (e3695)

private def e3697 : C 9 :=
.trans (e3696) (e3694)

private def e3699 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_507a502f73a13d5e8b9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beff81da6623c170545c)

private def e3700 : S 9 :=
.congAppFun (e3699) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8aca099393e9328f87a)

private def e3701 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3700) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3702 : C 9 :=
.single (e3701)

private def e3704 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c02d0578923d7c8f3d97)

private def e3705 : C 9 :=
.trans (e3702) (e3704)

private def e3706 : C 9 :=
.trans (e3697) (e3705)

private def e3707 : C 9 :=
.trans (e3658) (e3706)

private def e3708 : C 9 :=
.trans (e3653) (e3707)

private def e3709 : C 9 :=
.trans (e3708) (e3704)

private def e3711 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a68a2a8b7bb33d675319) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8aca099393e9328f87a)

private def e3712 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e3711) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db658204f0bce545a9be)

private def e3713 : C 9 :=
.single (e3712)

private def e3714 : C 9 :=
.trans (e3713) (e3581)

private def e3715 : C 9 :=
.trans (e3709) (e3714)

private def e3716 : C 9 :=
.trans (e3645) (e3715)

private def e3717 : C 9 :=
.trans (e3641) (e3716)

private def e3718 : C 9 :=
.symm (e3717)

private def e3719 : C 9 :=
.trans (e3588) (e3718)

private def e3720 : C 9 :=
.trans (e3110) (e3719)

private def e3721 : C 9 :=
.trans (e3590) (e3590)

private def e3724 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ff7f49280c21442dc691) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a89b869b2163308823c5)

private def e3725 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3724)

private def e3726 : C 9 :=
.single (e3725)

private def e3728 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ba18f7f1f902c7a45b1f)

private def e3729 : C 9 :=
.trans (e3728) (e3728)

private def e3730 : C 9 :=
.trans (e3729) (e3728)

private def e3731 : C 9 :=
.trans (e3730) (e3728)

private def e3732 : C 9 :=
.trans (e3731) (e3728)

private def e3733 : C 9 :=
.trans (e3726) (e3732)

private def e3734 : C 9 :=
.trans (e3721) (e3733)

private def e3736 : decoder.Code 9 :=
.delta (`CumulativeTower.AllResults.lower)

private def e3737 : S 9 :=
.root (e3736)

private def e3738 : S 9 :=
.congAppFun (e3737) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e2c1e2e15bb0cda87a)

private def e3739 : S 9 :=
.congAppFun (e3738) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_198d6bd75ff0377bcd7c)

private def e3740 : S 9 :=
.congAppFun (e3739) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3741 : S 9 :=
.congAppFun (e3740) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3742 : S 9 :=
.congAppFun (e3741) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e3743 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eaee385f3d44f8c8710) (e3742)

private def e3744 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3743)

private def e3745 : C 9 :=
.single (e3744)

private def e3747 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ab83ffea6a0bc5fa620)

private def e3748 : C 9 :=
.trans (e3745) (e3747)

private def e3749 : C 9 :=
.trans (e3728) (e3748)

private def e3750 : C 9 :=
.trans (e3749) (e3747)

private def e3752 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_96f36c4de576ebeed9fb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e2c1e2e15bb0cda87a)

private def e3753 : S 9 :=
.congAppFun (e3752) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_198d6bd75ff0377bcd7c)

private def e3754 : S 9 :=
.congAppFun (e3753) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3755 : S 9 :=
.congAppFun (e3754) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3756 : S 9 :=
.congAppFun (e3755) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e3757 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eaee385f3d44f8c8710) (e3756)

private def e3758 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3757)

private def e3759 : C 9 :=
.single (e3758)

private def e3761 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2f67aa335103ce5d51d2)

private def e3762 : C 9 :=
.trans (e3759) (e3761)

private def e3763 : C 9 :=
.trans (e3750) (e3762)

private def e3764 : C 9 :=
.trans (e3763) (e3761)

private def e3766 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f33a02851fd218253499) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_198d6bd75ff0377bcd7c)

private def e3767 : S 9 :=
.congAppFun (e3766) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3768 : S 9 :=
.congAppFun (e3767) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3769 : S 9 :=
.congAppFun (e3768) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e3770 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eaee385f3d44f8c8710) (e3769)

private def e3771 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3770)

private def e3772 : C 9 :=
.single (e3771)

private def e3774 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f5a2fbfe92634d31c20)

private def e3775 : C 9 :=
.trans (e3772) (e3774)

private def e3776 : C 9 :=
.trans (e3764) (e3775)

private def e3777 : C 9 :=
.trans (e3776) (e3774)

private def e3779 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b8513bdc322d5e5c85a1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e3780 : S 9 :=
.congAppFun (e3779) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3781 : S 9 :=
.congAppFun (e3780) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e3782 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eaee385f3d44f8c8710) (e3781)

private def e3783 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3782)

private def e3784 : C 9 :=
.single (e3783)

private def e3786 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3ae462cd8e602bf92f66)

private def e3787 : C 9 :=
.trans (e3784) (e3786)

private def e3788 : C 9 :=
.trans (e3777) (e3787)

private def e3789 : C 9 :=
.trans (e3788) (e3786)

private def e3791 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_28ced2981c1ebab3522e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e3792 : S 9 :=
.congAppFun (e3791) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e3793 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eaee385f3d44f8c8710) (e3792)

private def e3794 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3793)

private def e3795 : C 9 :=
.single (e3794)

private def e3797 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_21fb3f715d99367f31dd)

private def e3798 : C 9 :=
.trans (e3795) (e3797)

private def e3799 : C 9 :=
.trans (e3789) (e3798)

private def e3800 : C 9 :=
.trans (e3799) (e3797)

private def e3802 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_284165a1d561d43df78c) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e3803 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eaee385f3d44f8c8710) (e3802)

private def e3804 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3803)

private def e3805 : C 9 :=
.single (e3804)

private def e3807 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_61f6c1d93f8a30b507b4)

private def e3808 : C 9 :=
.trans (e3807) (e3807)

private def e3809 : C 9 :=
.trans (e3808) (e3807)

private def e3810 : C 9 :=
.trans (e3809) (e3807)

private def e3811 : C 9 :=
.trans (e3810) (e3807)

private def e3812 : C 9 :=
.trans (e3811) (e3807)

private def e3813 : C 9 :=
.trans (e3812) (e3807)

private def e3814 : C 9 :=
.trans (e3813) (e3807)

private def e3815 : C 9 :=
.trans (e3805) (e3814)

private def e3816 : C 9 :=
.trans (e3800) (e3815)

private def e3817 : C 9 :=
.symm (e3814)

private def e3818 : C 9 :=
.trans (e3807) (e3817)

private def e3819 : C 9 :=
.trans (e3816) (e3818)

private def e3820 : C 9 :=
.trans (e3728) (e3819)

private def e3822 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5efe9e6ee4814d7a480e)

private def e3823 : S 9 :=
.congAppFun (e3739) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e3824 : S 9 :=
.congAppFun (e3823) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3825 : S 9 :=
.congAppFun (e3824) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3826 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3825)

private def e3827 : C 9 :=
.single (e3826)

private def e3829 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_49215d73c97b3cd99e55)

private def e3830 : C 9 :=
.trans (e3827) (e3829)

private def e3831 : C 9 :=
.trans (e3822) (e3830)

private def e3832 : C 9 :=
.trans (e3831) (e3829)

private def e3833 : S 9 :=
.congAppFun (e3753) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e3834 : S 9 :=
.congAppFun (e3833) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3835 : S 9 :=
.congAppFun (e3834) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3836 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3835)

private def e3837 : C 9 :=
.single (e3836)

private def e3839 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d9329a718e5a182a2474)

private def e3840 : C 9 :=
.trans (e3837) (e3839)

private def e3841 : C 9 :=
.trans (e3832) (e3840)

private def e3842 : C 9 :=
.trans (e3841) (e3839)

private def e3843 : S 9 :=
.congAppFun (e3766) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e3844 : S 9 :=
.congAppFun (e3843) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3845 : S 9 :=
.congAppFun (e3844) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3846 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3845)

private def e3847 : C 9 :=
.single (e3846)

private def e3849 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8618fa81397377b786e)

private def e3850 : C 9 :=
.trans (e3847) (e3849)

private def e3851 : C 9 :=
.trans (e3842) (e3850)

private def e3852 : C 9 :=
.trans (e3851) (e3849)

private def e3853 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b8513bdc322d5e5c85a1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e3854 : S 9 :=
.congAppFun (e3853) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3855 : S 9 :=
.congAppFun (e3854) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3856 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3855)

private def e3857 : C 9 :=
.single (e3856)

private def e3859 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e0483ae1ee812962bc89)

private def e3860 : C 9 :=
.trans (e3857) (e3859)

private def e3861 : C 9 :=
.trans (e3852) (e3860)

private def e3862 : C 9 :=
.trans (e3861) (e3859)

private def e3864 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e7bf54c8757ee60cf3a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e3865 : S 9 :=
.congAppFun (e3864) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3866 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3865)

private def e3867 : C 9 :=
.single (e3866)

private def e3869 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9ab142a8e5a50dbb8753)

private def e3870 : C 9 :=
.trans (e3867) (e3869)

private def e3871 : C 9 :=
.trans (e3862) (e3870)

private def e3872 : C 9 :=
.trans (e3871) (e3869)

private def e3874 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58dbe1e6fbe4d35289c4) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3875 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3874)

private def e3876 : C 9 :=
.single (e3875)

private def e3878 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0486d2773cf6c41be9bb)

private def e3879 : C 9 :=
.trans (e3878) (e3878)

private def e3880 : C 9 :=
.trans (e3879) (e3878)

private def e3881 : C 9 :=
.trans (e3880) (e3878)

private def e3882 : C 9 :=
.trans (e3881) (e3878)

private def e3883 : C 9 :=
.trans (e3882) (e3878)

private def e3884 : C 9 :=
.trans (e3883) (e3878)

private def e3885 : decoder.Code 9 :=
.inherited (.declared (.inl (.inl ⟨3, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                     `CumulativeTower.VecUpper.cons)
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 12))
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4))
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.fst
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.snd
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.VecUpper.nil)
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8)),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                     `CumulativeTower.Vec.eliminate)
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2)))))))
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                   `CumulativeTower.Nat.zero)))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 14))
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.VecUpper)
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2)))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8]⟩)))

private def e3886 : S 9 :=
.root (e3885)

private def e3887 : S 9 :=
.congAppFun (e3886) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3888 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3887)

private def e3889 : C 9 :=
.single (e3888)

private def e3891 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebab51e58d6e12318ea3)

private def e3892 : C 9 :=
.trans (e3891) (e3891)

private def e3894 : S 9 :=
.congAppFun (e3665) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff)

private def e3895 : S 9 :=
.congAppFun (e3894) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3896 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3895)

private def e3897 : C 9 :=
.single (e3896)

private def e3899 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4aab6f303bafb8dc421)

private def e3900 : C 9 :=
.trans (e3897) (e3899)

private def e3901 : C 9 :=
.trans (e3892) (e3900)

private def e3902 : C 9 :=
.trans (e3901) (e3899)

private def e3903 : S 9 :=
.congAppFun (e3677) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff)

private def e3904 : S 9 :=
.congAppFun (e3903) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3905 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3904)

private def e3906 : C 9 :=
.single (e3905)

private def e3908 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fde0a54cedda75768e7d)

private def e3909 : C 9 :=
.trans (e3906) (e3908)

private def e3910 : C 9 :=
.trans (e3902) (e3909)

private def e3911 : C 9 :=
.trans (e3910) (e3908)

private def e3912 : S 9 :=
.congAppFun (e3688) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff)

private def e3913 : S 9 :=
.congAppFun (e3912) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3914 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3913)

private def e3915 : C 9 :=
.single (e3914)

private def e3917 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2602f3114f75c87945c1)

private def e3918 : C 9 :=
.trans (e3915) (e3917)

private def e3919 : C 9 :=
.trans (e3911) (e3918)

private def e3920 : C 9 :=
.trans (e3919) (e3917)

private def e3921 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_507a502f73a13d5e8b9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff)

private def e3922 : S 9 :=
.congAppFun (e3921) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3923 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3922)

private def e3924 : C 9 :=
.single (e3923)

private def e3926 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d42e889f3cd0d79d6f92)

private def e3927 : C 9 :=
.trans (e3924) (e3926)

private def e3928 : C 9 :=
.trans (e3920) (e3927)

private def e3929 : C 9 :=
.trans (e3889) (e3928)

private def e3930 : C 9 :=
.trans (e3884) (e3929)

private def e3931 : C 9 :=
.trans (e3930) (e3926)

private def e3933 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ec064c5a5afeadcfde2d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e3934 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_81e17242e3807ca21c99) (e3933)

private def e3935 : C 9 :=
.single (e3934)

private def e3936 : C 9 :=
.trans (e3935) (e3811)

private def e3937 : C 9 :=
.trans (e3931) (e3936)

private def e3938 : C 9 :=
.trans (e3876) (e3937)

private def e3939 : C 9 :=
.trans (e3872) (e3938)

private def e3940 : C 9 :=
.symm (e3939)

private def e3941 : C 9 :=
.trans (e3820) (e3940)

private def e3942 : C 9 :=
.trans (e3734) (e3941)

private def e3943 : C 9 :=
.trans (e3720) (e3942)

private def e3944 : C 9 :=
.trans (e3096) (e3943)

private def e3945 : C 9 :=
.symm (e3822)

private def e3946 : C 9 :=
.trans (e3944) (e3945)

private def e3947 : C 9 :=
.trans (e3096) (e3946)

private def e3948 : T 9 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_87dafa7fe183795b389a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e3095) (e2779) (e3947)

private def e3949 : T 8 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f0f123abfc5045ff007f) (e2780) (e3948)

private def e3950 : T 7 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_66455137451fba038b86) (e2781) (e3949)

private def e3951 : T 6 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1bfe7411e0715fdc3608) (e2782) (e3950)

private def e3952 : T 5 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beabd34e09ddd5a95e6a) (e2783) (e3951)

private def e3953 : T 4 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9a1c6e27e481b4f8195f) (e2784) (e3952)

private def e3957 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_065c86a4bb0310e90152) (e1060) (replay_088a7fed4563d6a06e7a)

private def e3958 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5331ca9ad2f18da19b3f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_36b855cd183c87bb02c2) (e3957) (replay_088a7fed4563d6a06e7a)

private def e3962 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4777b74b12da0e49bc9) (e1105) (replay_088a7fed4563d6a06e7a)

private def e3963 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5331ca9ad2f18da19b3f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d7015a3cae846e11eaf5) (e3962) (replay_088a7fed4563d6a06e7a)

private def e3964 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8337ad982447bb9b9de5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c53931b4b7092fa26b36) (e3963) (replay_088a7fed4563d6a06e7a)

private def e3965 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bac685e13a2fd02b0bc2) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f4571ec60826300f8ca3) (e3958) (e3964)

private def e3967 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2a395f51052d7be435f6) (e1158) (replay_088a7fed4563d6a06e7a)

private def e3968 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5331ca9ad2f18da19b3f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_25037791ada4f23c2d8b) (e3967) (replay_088a7fed4563d6a06e7a)

private def e3969 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8337ad982447bb9b9de5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f4571ec60826300f8ca3) (e3968) (replay_088a7fed4563d6a06e7a)

private def e3970 : T 5 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_ab222404a1b298e073e0) (e3965) (e3969)

private def e3971 : T 4 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1030) (e3970)

private def e3972 : T 4 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23e09003749289e9f868) (e3971)

private def e3977 : T 7 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0b123886a2f1ca52dc20) (e165) (replay_364e906c32a1fece265a)

private def e3978 : T 6 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7c74dd6d73ced3b4686) (e166) (e3977)

private def e3979 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e11e484bc56d77ac660e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fa43449128fc9673bc03) (e157) (e3978)

private def e3984 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4f93e456b4620d589d9) (replay_18e264ae7443180c79f8) (replay_b7b0d4f9c05076ab70ae)

private def e3985 : T 8 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8d299427678534d5d57c) (replay_b0145ff60fc18bc29654) (e3984)

private def e3986 : T 7 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fafdfa0063130741b0e7) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_196d73933a2b663cb491) (replay_47c498e0b1f33021db6c) (e3985)

private def e3987 : T 6 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4f93e456b4620d589d9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6aabb8dd5a1429128d77) (replay_ff33acd87c5b03c2f11e) (e3986)

private def e3988 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b87849a278a7e06e7dff)

private def e3989 : C 6 :=
.trans (e3988) (e3988)

private def e3991 : S 6 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_def06f6a6eeca489f536) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_07a1d7b4a030d2d416f2)

private def e3992 : S 6 :=
.congAppFun (e3991) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c29849df4a7f3412755d)

private def e3994 : S 6 :=
.congPiDom (e3992) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8d432664f151582c0a17)

private def e3995 : C 6 :=
.single (e3994)

private def e3997 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9261219a74d2f05ac24)

private def e3998 : C 6 :=
.trans (e3995) (e3997)

private def e3999 : C 6 :=
.trans (e3989) (e3998)

private def e4000 : C 6 :=
.trans (e3999) (e3997)

private def e4001 : S 6 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d0f4a08c893ea38d53fb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c29849df4a7f3412755d)

private def e4002 : S 6 :=
.congPiDom (e4001) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8d432664f151582c0a17)

private def e4003 : C 6 :=
.single (e4002)

private def e4005 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4d989d7b1f261f1c9228)

private def e4006 : C 6 :=
.trans (e4003) (e4005)

private def e4007 : C 6 :=
.trans (e4000) (e4006)

private def e4008 : C 6 :=
.symm (e4005)

private def e4009 : C 6 :=
.trans (e4005) (e4008)

private def e4010 : C 6 :=
.trans (e4007) (e4009)

private def e4011 : C 6 :=
.trans (e4005) (e4005)

private def e4012 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cc7edc238326af0e3cee) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_05b075e7750afd998d8f)

private def e4013 : S 10 :=
.congAppFun (e4012) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b6263f8b29eb9d152bde)

private def e4015 : S 10 :=
.congPiDom (e4013) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_87efbeb07db02d4cda38)

private def e4016 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53047c3473acacee0b84) (e4015)

private def e4017 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ed88dce83fa3ae5d4c4a) (e4016)

private def e4018 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (e4017)

private def e4020 : S 7 :=
.congPiDom (e4018) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_31fec564e8ddf546b19c)

private def e4021 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e90387a90b9c8c3c4369) (e4020)

private def e4022 : C 6 :=
.single (e4021)

private def e4024 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e1aa458b24d012a127bf)

private def e4025 : C 6 :=
.trans (e4022) (e4024)

private def e4026 : C 6 :=
.trans (e4011) (e4025)

private def e4027 : C 6 :=
.trans (e4026) (e4024)

private def e4028 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_df96c216643bb607dff9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b6263f8b29eb9d152bde)

private def e4029 : S 10 :=
.congPiDom (e4028) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_87efbeb07db02d4cda38)

private def e4030 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53047c3473acacee0b84) (e4029)

private def e4031 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ed88dce83fa3ae5d4c4a) (e4030)

private def e4032 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (e4031)

private def e4033 : S 7 :=
.congPiDom (e4032) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_31fec564e8ddf546b19c)

private def e4034 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e90387a90b9c8c3c4369) (e4033)

private def e4035 : C 6 :=
.single (e4034)

private def e4037 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83596203408b77822497)

private def e4038 : C 6 :=
.trans (e4035) (e4037)

private def e4039 : C 6 :=
.trans (e4027) (e4038)

private def e4040 : C 6 :=
.symm (e4037)

private def e4041 : C 6 :=
.trans (e4037) (e4040)

private def e4042 : C 6 :=
.trans (e4039) (e4041)

private def e4043 : C 6 :=
.trans (e4037) (e4037)

private def e4044 : S 11 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_65561d1b7fcbb3a625a4) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1c1bdd3d0533bd5ac753)

private def e4045 : S 11 :=
.congAppFun (e4044) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43b596ae32b4a7f59f6a)

private def e4046 : S 10 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_683a421a2ec88ad82286) (e4045)

private def e4047 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53047c3473acacee0b84) (e4046)

private def e4048 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ed88dce83fa3ae5d4c4a) (e4047)

private def e4049 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (e4048)

private def e4050 : S 7 :=
.congPiDom (e4049) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_31fec564e8ddf546b19c)

private def e4051 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e90387a90b9c8c3c4369) (e4050)

private def e4052 : C 6 :=
.single (e4051)

private def e4054 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_98c43adc545cfc6e76ba)

private def e4055 : C 6 :=
.trans (e4052) (e4054)

private def e4056 : C 6 :=
.trans (e4043) (e4055)

private def e4057 : C 6 :=
.trans (e4056) (e4054)

private def e4058 : S 11 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b02738bed1f938162bff) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43b596ae32b4a7f59f6a)

private def e4059 : S 10 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_683a421a2ec88ad82286) (e4058)

private def e4060 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53047c3473acacee0b84) (e4059)

private def e4061 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ed88dce83fa3ae5d4c4a) (e4060)

private def e4062 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (e4061)

private def e4063 : S 7 :=
.congPiDom (e4062) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_31fec564e8ddf546b19c)

private def e4064 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e90387a90b9c8c3c4369) (e4063)

private def e4065 : C 6 :=
.single (e4064)

private def e4067 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_79a5fd8c3403e91e18eb)

private def e4068 : C 6 :=
.trans (e4065) (e4067)

private def e4069 : C 6 :=
.trans (e4057) (e4068)

private def e4070 : C 6 :=
.symm (e4067)

private def e4071 : C 6 :=
.trans (e4067) (e4070)

private def e4072 : C 6 :=
.trans (e4069) (e4071)

private def e4073 : C 6 :=
.trans (e4042) (e4072)

private def e4074 : C 6 :=
.trans (e4073) (e4070)

private def e4075 : C 6 :=
.trans (e4005) (e4074)

private def e4076 : C 6 :=
.trans (e4005) (e4075)

private def e4077 : C 6 :=
.trans (e4076) (e4070)

private def e4078 : C 6 :=
.trans (e4005) (e4077)

private def e4079 : C 6 :=
.trans (e4005) (e4078)

private def e4080 : C 6 :=
.trans (e4079) (e4070)

private def e4081 : C 6 :=
.trans (e4005) (e4080)

private def e4082 : C 6 :=
.trans (e4005) (e4081)

private def e4083 : C 6 :=
.trans (e4082) (e4070)

private def e4084 : C 6 :=
.trans (e4005) (e4083)

private def e4085 : C 6 :=
.trans (e4067) (e4067)

private def e4087 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cc7edc238326af0e3cee) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2c3a73b45b381f28af93)

private def e4088 : S 10 :=
.congAppFun (e4087) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b6263f8b29eb9d152bde)

private def e4089 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_28ef38dcd249a3861739) (e4088)

private def e4090 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56760c9c60918cbf3d6f) (e4089)

private def e4091 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3c0bc581b5c76103a008) (e4090)

private def e4092 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e90387a90b9c8c3c4369) (e4091)

private def e4093 : C 6 :=
.single (e4092)

private def e4095 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_942885619084b14fdee4)

private def e4096 : C 6 :=
.trans (e4093) (e4095)

private def e4097 : C 6 :=
.trans (e4085) (e4096)

private def e4098 : C 6 :=
.trans (e4097) (e4095)

private def e4099 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_28ef38dcd249a3861739) (e4028)

private def e4100 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56760c9c60918cbf3d6f) (e4099)

private def e4101 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3c0bc581b5c76103a008) (e4100)

private def e4102 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e90387a90b9c8c3c4369) (e4101)

private def e4103 : C 6 :=
.single (e4102)

private def e4105 : C 6 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9db5085ffad2e4b0856a)

private def e4106 : C 6 :=
.trans (e4103) (e4105)

private def e4107 : C 6 :=
.trans (e4098) (e4106)

private def e4108 : C 6 :=
.symm (e4105)

private def e4109 : C 6 :=
.trans (e4105) (e4108)

private def e4110 : C 6 :=
.trans (e4107) (e4109)

private def e4111 : C 6 :=
.trans (e4067) (e4110)

private def e4112 : C 6 :=
.trans (e4111) (e4108)

private def e4113 : C 6 :=
.trans (e4067) (e4112)

private def e4114 : C 6 :=
.trans (e4067) (e4113)

private def e4115 : C 6 :=
.trans (e4114) (e4108)

private def e4116 : C 6 :=
.trans (e4067) (e4115)

private def e4117 : C 6 :=
.trans (e4084) (e4116)

private def e4118 : C 6 :=
.trans (e4117) (e4108)

private def e4119 : C 6 :=
.trans (e4005) (e4118)

private def e4120 : C 6 :=
.trans (e4010) (e4119)

private def e4121 : C 6 :=
.trans (e4120) (e4108)

private def e4122 : C 6 :=
.trans (e3988) (e4121)

private def e4123 : T 6 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b87849a278a7e06e7dff) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_404b5de2e790e15a378c) (e3979) (e3987) (e4122)

private def e4124 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e90387a90b9c8c3c4369) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6e872420dce694944953) (e4123) (e353)

private def e4125 : T 10 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (e373) (replay_7fbeba8818273106d8c8)

private def e4126 : T 10 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_50d54f6ca4190fd6bc72) (e4125)

private def e4127 : T 9 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d3bc479f5fb249b99ac2) (e829) (e4126)

private def e4128 : T 8 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c6b51e3ba4892036cdb0) (e830) (e4127)

private def e4129 : T 7 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_45e80a32c899dfd6b11b) (e831) (e4128)

private def e4130 : T 6 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fafdfa0063130741b0e7) (e832) (e4129)

private def e4131 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_569d8f7902f0377d05f7) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1edfeaf482acab581d3e) (e4124) (e4130)

private def e4132 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6d27501b0eb014630e09) (e4131) (replay_fb92de9ad2d284eba393)

private def e4133 : T 6 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea1e125d0ec89812d6af) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d0f4a08c893ea38d53fb) (e4132) (replay_fb92de9ad2d284eba393)

private def e4141 : T 8 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (e802) (replay_07c41680d17703d7171f)

private def e4142 : T 8 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_50d54f6ca4190fd6bc72) (e4141)

private def e4143 : T 7 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d3bc479f5fb249b99ac2) (replay_4c4f4414acb960b7a430) (e4142)

private def e4144 : T 6 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c6b51e3ba4892036cdb0) (replay_9673219d6998fe9a6a18) (e4143)

private def e4145 : T 5 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_45e80a32c899dfd6b11b) (replay_3d0880162e3671a4b59b) (e4144)

private def e4146 : T 4 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fafdfa0063130741b0e7) (replay_ca42dd954d17dc8bcc9a) (e4145)

private def e4147 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a08b915b3440d750f218) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_637e2208361746e72f13) (e587) (e4146)

private def e4148 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7090374f1485408a1741) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d7626e99262c9e21ec07) (e4147) (replay_f89a0d3fd4af1bf7786d)

private def e4149 : T 4 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d2fe1eb531662373187) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c070633b7877d5417c64) (e4148) (replay_f89a0d3fd4af1bf7786d)

private def e4154 : T 7 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eca3dc2b6caf4867e1d4) (replay_4ec057243fb248f73891)

private def e4155 : T 6 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0b123886a2f1ca52dc20) (replay_40a4e5b94fc0e4e4dda6) (e4154)

private def e4156 : T 5 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7c74dd6d73ced3b4686) (replay_3b2208d0e18866e8bf53) (e4155)

private def e4157 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_df0f30f1ec3dce3eb86a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d9b222a9ccd79e463a7a) (replay_6b2965139ed23ce2e3db) (e4156)

private def e4158 : T 8 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eca3dc2b6caf4867e1d4) (replay_3e07c8af8123696e3523) (replay_cf26163fe59a0dbcc31b)

private def e4159 : T 7 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5fcd81028f8a0038e5e4) (replay_0432db7c6e4e1e541d38) (e4158)

private def e4160 : T 6 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_088ec0f4742a888f4d7e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b237fdc24d2997bfa210) (e363) (e4159)

private def e4161 : T 5 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eca3dc2b6caf4867e1d4) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b1a28e9d42d7f3e26777) (e828) (e4160)

private def e4162 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_77e6e870dcc2945ab3de)

private def e4163 : C 5 :=
.trans (e4162) (e4162)

private def e4165 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a43a52c313f164b3d555) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_10a09856ff4a49f9d49f)

private def e4166 : S 5 :=
.congAppFun (e4165) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e4168 : S 5 :=
.congPiDom (e4166) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_16211ee915694961e9ca)

private def e4169 : C 5 :=
.single (e4168)

private def e4171 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb3d6764afd071181d74)

private def e4172 : C 5 :=
.trans (e4169) (e4171)

private def e4173 : C 5 :=
.trans (e4163) (e4172)

private def e4174 : C 5 :=
.trans (e4173) (e4171)

private def e4175 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e4f6621568ccac500dc) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_673e4ecc26f1f0b1d4b3)

private def e4176 : S 5 :=
.congPiDom (e4175) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_16211ee915694961e9ca)

private def e4177 : C 5 :=
.single (e4176)

private def e4179 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e44140390b5b5fe8fb3)

private def e4180 : C 5 :=
.trans (e4177) (e4179)

private def e4181 : C 5 :=
.trans (e4174) (e4180)

private def e4182 : C 5 :=
.symm (e4179)

private def e4183 : C 5 :=
.trans (e4179) (e4182)

private def e4184 : C 5 :=
.trans (e4181) (e4183)

private def e4185 : C 5 :=
.trans (e4179) (e4179)

private def e4186 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b5e1523785aff7d931ca) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e4187 : S 9 :=
.congAppFun (e4186) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e4189 : S 9 :=
.congPiDom (e4187) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_63c0c214baaaef55258f)

private def e4190 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_369043ee55c31306fc04) (e4189)

private def e4191 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca) (e4190)

private def e4192 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) (e4191)

private def e4194 : S 6 :=
.congPiDom (e4192) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b9001bf39cc4983b5346)

private def e4195 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a27060780ae3276936d3) (e4194)

private def e4196 : C 5 :=
.single (e4195)

private def e4198 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8286708f6ac9265bfa07)

private def e4199 : C 5 :=
.trans (e4196) (e4198)

private def e4200 : C 5 :=
.trans (e4185) (e4199)

private def e4201 : C 5 :=
.trans (e4200) (e4198)

private def e4202 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_307e4da5e86f9f55da07) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e4203 : S 9 :=
.congPiDom (e4202) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_63c0c214baaaef55258f)

private def e4204 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_369043ee55c31306fc04) (e4203)

private def e4205 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca) (e4204)

private def e4206 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) (e4205)

private def e4207 : S 6 :=
.congPiDom (e4206) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b9001bf39cc4983b5346)

private def e4208 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a27060780ae3276936d3) (e4207)

private def e4209 : C 5 :=
.single (e4208)

private def e4211 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fabf1c969b1574301f81)

private def e4212 : C 5 :=
.trans (e4209) (e4211)

private def e4213 : C 5 :=
.trans (e4201) (e4212)

private def e4214 : C 5 :=
.symm (e4211)

private def e4215 : C 5 :=
.trans (e4211) (e4214)

private def e4216 : C 5 :=
.trans (e4213) (e4215)

private def e4217 : C 5 :=
.trans (e4211) (e4211)

private def e4218 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3d14aa0ee1750cdf2678) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_29e6362be00331af1526)

private def e4219 : S 10 :=
.congAppFun (e4218) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd8f671c52437c194141)

private def e4220 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7bd2623d7ade2c187ee) (e4219)

private def e4221 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_369043ee55c31306fc04) (e4220)

private def e4222 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca) (e4221)

private def e4223 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) (e4222)

private def e4224 : S 6 :=
.congPiDom (e4223) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b9001bf39cc4983b5346)

private def e4225 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a27060780ae3276936d3) (e4224)

private def e4226 : C 5 :=
.single (e4225)

private def e4228 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7b115948640f8b59ad2c)

private def e4229 : C 5 :=
.trans (e4226) (e4228)

private def e4230 : C 5 :=
.trans (e4217) (e4229)

private def e4231 : C 5 :=
.trans (e4230) (e4228)

private def e4232 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c4973f6eacdd028898bc) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd8f671c52437c194141)

private def e4233 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7bd2623d7ade2c187ee) (e4232)

private def e4234 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_369043ee55c31306fc04) (e4233)

private def e4235 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3531df46ccfd426e0cca) (e4234)

private def e4236 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_545fb4a3c03c82a175c1) (e4235)

private def e4237 : S 6 :=
.congPiDom (e4236) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b9001bf39cc4983b5346)

private def e4238 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a27060780ae3276936d3) (e4237)

private def e4239 : C 5 :=
.single (e4238)

private def e4241 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6d390f147392e0220f9a)

private def e4242 : C 5 :=
.trans (e4239) (e4241)

private def e4243 : C 5 :=
.trans (e4231) (e4242)

private def e4244 : C 5 :=
.symm (e4241)

private def e4245 : C 5 :=
.trans (e4241) (e4244)

private def e4246 : C 5 :=
.trans (e4243) (e4245)

private def e4247 : C 5 :=
.trans (e4216) (e4246)

private def e4248 : C 5 :=
.trans (e4247) (e4244)

private def e4249 : C 5 :=
.trans (e4179) (e4248)

private def e4250 : C 5 :=
.trans (e4179) (e4249)

private def e4251 : C 5 :=
.trans (e4250) (e4244)

private def e4252 : C 5 :=
.trans (e4179) (e4251)

private def e4253 : C 5 :=
.trans (e4179) (e4252)

private def e4254 : C 5 :=
.trans (e4253) (e4244)

private def e4255 : C 5 :=
.trans (e4179) (e4254)

private def e4256 : C 5 :=
.trans (e4179) (e4255)

private def e4257 : C 5 :=
.trans (e4256) (e4244)

private def e4258 : C 5 :=
.trans (e4179) (e4257)

private def e4259 : C 5 :=
.trans (e4241) (e4241)

private def e4260 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b5e1523785aff7d931ca) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcc403caa19d1550c37)

private def e4261 : S 9 :=
.congAppFun (e4260) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e4262 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c351605dcec825868e68) (e4261)

private def e4263 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (e4262)

private def e4264 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_75331d7791745b76e4ef) (e4263)

private def e4265 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a27060780ae3276936d3) (e4264)

private def e4266 : C 5 :=
.single (e4265)

private def e4268 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_043fb251af4665f4d69c)

private def e4269 : C 5 :=
.trans (e4266) (e4268)

private def e4270 : C 5 :=
.trans (e4259) (e4269)

private def e4271 : C 5 :=
.trans (e4270) (e4268)

private def e4272 : S 8 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c351605dcec825868e68) (e4202)

private def e4273 : S 7 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (e4272)

private def e4274 : S 6 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_75331d7791745b76e4ef) (e4273)

private def e4275 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a27060780ae3276936d3) (e4274)

private def e4276 : C 5 :=
.single (e4275)

private def e4278 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_25391acfd85aee057329)

private def e4279 : C 5 :=
.trans (e4276) (e4278)

private def e4280 : C 5 :=
.trans (e4271) (e4279)

private def e4281 : C 5 :=
.symm (e4278)

private def e4282 : C 5 :=
.trans (e4278) (e4281)

private def e4283 : C 5 :=
.trans (e4280) (e4282)

private def e4284 : C 5 :=
.trans (e4241) (e4283)

private def e4285 : C 5 :=
.trans (e4284) (e4281)

private def e4286 : C 5 :=
.trans (e4241) (e4285)

private def e4287 : C 5 :=
.trans (e4241) (e4286)

private def e4288 : C 5 :=
.trans (e4287) (e4281)

private def e4289 : C 5 :=
.trans (e4241) (e4288)

private def e4290 : C 5 :=
.trans (e4258) (e4289)

private def e4291 : C 5 :=
.trans (e4290) (e4281)

private def e4292 : C 5 :=
.trans (e4179) (e4291)

private def e4293 : C 5 :=
.trans (e4184) (e4292)

private def e4294 : C 5 :=
.trans (e4293) (e4281)

private def e4295 : C 5 :=
.trans (e4162) (e4294)

private def e4296 : T 5 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_77e6e870dcc2945ab3de) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fa34719ab4861ce3b645) (e4157) (e4161) (e4295)

private def e4297 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a27060780ae3276936d3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cf77fe7a5f6e39c63032) (e4296) (e986)

private def e4298 : T 9 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e990) (replay_8dd06e568960d2567ea5)

private def e4299 : T 9 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b8578195b133fac70a1) (e4298)

private def e4300 : T 8 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7646540dd7e659fc407) (replay_c69e1bf9ab563402ad4c) (e4299)

private def e4301 : T 7 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e1d07338c040d26dff49) (replay_73b42d71dc0e57c9a9de) (e4300)

private def e4302 : T 6 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7e6cb354a8df3738086) (replay_5ec50523c2085f963d11) (e4301)

private def e4303 : T 5 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_088ec0f4742a888f4d7e) (replay_827a3e78871e902abbf5) (e4302)

private def e4304 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7283ed2d25f76e4f5fa6) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_31185dbddd1d8b9683a6) (e4297) (e4303)

private def e4305 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6f4154d4d0501fa10b71) (e4304) (replay_088a7fed4563d6a06e7a)

private def e4306 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5331ca9ad2f18da19b3f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3e4f6621568ccac500dc) (e4305) (replay_088a7fed4563d6a06e7a)

private def e4307 : T 4 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e4149) (e4306)

private def e4308 : T 3 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_897db4146fa986a8835c) (replay_be261adb759aa3486f8c) (e4307)

private def e4309 : T 2 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8ff6182553f1ec326b3b) (replay_2a0decba183f967a7699) (e4308)

private def e4310 : T 1 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_80d7abfcb57830595ef4) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_51eec7f52bc4a38ae682) (e637) (e4309)

private def e4311 : T 0 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d9099ae41a1c6a1cb998) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0b5780754692a70b4821) (replay_7a268c731e7a9afff236) (e4310)

private def e4312 : T 7 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8b8b2762f64034c755e4) (e4311)

private def e4313 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d064c25dd26291905510) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9a3c7f2aaf59bc512f2a) (e4312) (replay_e197ee63c3c9ea3d9b51)

private def e4314 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_70aa1eb6b5fc777f1a97) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4b236ec7e809846ad556) (e4313) (e1008)

private def e4315 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9918c4835afcd2815d8a) (e4314) (replay_e197ee63c3c9ea3d9b51)

private def e4316 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_61babc0a06ef8aba8578) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0666ff1dfb2a5aa7440f) (e4315) (replay_e197ee63c3c9ea3d9b51)

private def e4317 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_74251133736ce4f309d3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_30415f090fc802aba167) (e4316) (replay_e197ee63c3c9ea3d9b51)

private def e4318 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_beaf96c439d2f4e74e7a) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4771ebae3507c900a130) (e1040) (e4317)

private def e4319 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_74251133736ce4f309d3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4771ebae3507c900a130) (e626) (replay_e197ee63c3c9ea3d9b51)

private def e4320 : T 7 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e392) (e4318) (e4319)

private def e4321 : T 6 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e4133) (e4320)

private def e4322 : T 6 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_897db4146fa986a8835c) (e4321)

private def e4323 : T 5 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0b123886a2f1ca52dc20) (replay_7dc6b8e83ee36a07c70d) (e4322)

private def e4324 : T 4 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7c74dd6d73ced3b4686) (replay_aec4c85cb0ac134bc5ba) (e4323)

private def e4330 : T 5 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8b8b2762f64034c755e4) (e4311)

private def e4331 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5978e1f6d4b31cb31598) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_39fd70a023f1267129bf) (e4330) (replay_088a7fed4563d6a06e7a)

private def e4332 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_309688c12a1ce983731b) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_817958e66ce0d5db1ffe) (e4331) (e1104)

private def e4333 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3bb382d71a95efa9d15f) (e4332) (replay_c88c45c22b9888b30470)

private def e4334 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_25bb4742f53c566750d8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5b21252c6523c15a310e) (e4333) (e1064)

private def e4335 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6cce867c69373ac28f17)

private def e4336 : C 5 :=
.trans (e4335) (e4335)

private def e4337 : C 5 :=
.trans (e4336) (e4335)

private def e4338 : C 5 :=
.trans (e4337) (e4335)

private def e4339 : C 5 :=
.trans (e4338) (e4335)

private def e4340 : C 5 :=
.trans (e4339) (e4335)

private def e4341 : C 5 :=
.trans (e4340) (e4335)

private def e4343 : S 5 :=
.congPiDom (e1080) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_410960f95e257622ed4c)

private def e4344 : C 5 :=
.single (e4343)

private def e4346 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_64911bfd4db0d74227e4)

private def e4347 : C 5 :=
.trans (e4344) (e4346)

private def e4348 : C 5 :=
.trans (e4341) (e4347)

private def e4349 : C 5 :=
.symm (e4346)

private def e4350 : C 5 :=
.trans (e4346) (e4349)

private def e4351 : C 5 :=
.trans (e4348) (e4350)

private def e4352 : C 5 :=
.trans (e4346) (e4346)

private def e4353 : C 5 :=
.trans (e4352) (e4346)

private def e4354 : C 5 :=
.trans (e4353) (e4346)

private def e4355 : C 5 :=
.trans (e4354) (e4346)

private def e4356 : C 5 :=
.trans (e4355) (e4346)

private def e4357 : C 5 :=
.trans (e4356) (e4346)

private def e4358 : decoder.Code 6 :=
.inherited (.declared (.inl (.inl ⟨2, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5]⟩)))

private def e4359 : S 6 :=
.root (e4358)

private def e4360 : S 5 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a2fa25f72f21de9dabb3) (e4359)

private def e4361 : C 5 :=
.single (e4360)

private def e4362 : C 5 :=
.trans (e4361) (e1139)

private def e4363 : C 5 :=
.trans (e4357) (e4362)

private def e4364 : C 5 :=
.trans (e4363) (e1143)

private def e4365 : C 5 :=
.trans (e4351) (e4364)

private def e4366 : C 5 :=
.trans (e4365) (e1142)

private def e4367 : C 5 :=
.trans (e4335) (e4366)

private def e4368 : T 5 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6cce867c69373ac28f17) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2ff527e667e033dd20bc) (e4334) (e1108) (e4367)

private def e4369 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a2fa25f72f21de9dabb3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3aa92ecdc050920d21ee) (e4368) (replay_088a7fed4563d6a06e7a)

private def e4370 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a2fa25f72f21de9dabb3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e588931236a24b22cb84) (e1176) (e4369)

private def e4371 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a2fa25f72f21de9dabb3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e588931236a24b22cb84) (e1093) (replay_088a7fed4563d6a06e7a)

private def e4372 : T 5 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1048) (e4370) (e4371)

private def e4373 : T 4 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_4cc623b12c4b86cfe50a) (e4372)

private def e4375 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3d8a94dad8251df02860)

private def e4377 : S 5 :=
.congAppFun (e1304) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5420194af32f2b048e6c)

private def e4378 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e4377) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e4379 : C 5 :=
.single (e4378)

private def e4381 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb36badc369bcce14f9e)

private def e4382 : C 5 :=
.trans (e4379) (e4381)

private def e4383 : C 5 :=
.trans (e4375) (e4382)

private def e4384 : C 5 :=
.trans (e4383) (e4381)

private def e4385 : S 5 :=
.congAppFun (e1318) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5420194af32f2b048e6c)

private def e4386 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e4385) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e4387 : C 5 :=
.single (e4386)

private def e4389 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_88f7347013ec51dd1c6e)

private def e4390 : C 5 :=
.trans (e4387) (e4389)

private def e4391 : C 5 :=
.trans (e4384) (e4390)

private def e4392 : C 5 :=
.trans (e4391) (e4389)

private def e4393 : S 5 :=
.congAppFun (e1330) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5420194af32f2b048e6c)

private def e4394 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e4393) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e4395 : C 5 :=
.single (e4394)

private def e4397 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a2776139bd57624b9824)

private def e4398 : C 5 :=
.trans (e4395) (e4397)

private def e4399 : C 5 :=
.trans (e4392) (e4398)

private def e4400 : C 5 :=
.trans (e4399) (e4397)

private def e4401 : S 5 :=
.congAppFun (e1341) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5420194af32f2b048e6c)

private def e4402 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e4401) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e4403 : C 5 :=
.single (e4402)

private def e4405 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_89240f863d20b9056543)

private def e4406 : C 5 :=
.trans (e4403) (e4405)

private def e4407 : C 5 :=
.trans (e4400) (e4406)

private def e4408 : C 5 :=
.trans (e4407) (e4405)

private def e4409 : S 5 :=
.congAppFun (e1351) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5420194af32f2b048e6c)

private def e4410 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e4409) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e4411 : C 5 :=
.single (e4410)

private def e4413 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_517797b38165468b3e72)

private def e4414 : C 5 :=
.trans (e4411) (e4413)

private def e4415 : C 5 :=
.trans (e4408) (e4414)

private def e4416 : C 5 :=
.trans (e4415) (e4413)

private def e4417 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_03f2dc1272cdf3621c35) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5420194af32f2b048e6c)

private def e4418 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e4417) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e4419 : C 5 :=
.single (e4418)

private def e4421 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83e5b896a076d14aa3c7)

private def e4422 : C 5 :=
.trans (e4421) (e4421)

private def e4423 : C 5 :=
.trans (e4422) (e4421)

private def e4424 : C 5 :=
.trans (e4423) (e4421)

private def e4425 : C 5 :=
.trans (e4424) (e4421)

private def e4426 : C 5 :=
.trans (e4425) (e4421)

private def e4427 : C 5 :=
.trans (e4426) (e4421)

private def e4428 : S 5 :=
.congAppFun (e1373) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5420194af32f2b048e6c)

private def e4429 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e4428) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e4430 : C 5 :=
.single (e4429)

private def e4432 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_222f23c6831291ba4e6b)

private def e4433 : C 5 :=
.trans (e4430) (e4432)

private def e4434 : C 5 :=
.trans (e4427) (e4433)

private def e4435 : C 5 :=
.trans (e4434) (e4432)

private def e4436 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eb4d2e5497f8b684d8d8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5420194af32f2b048e6c)

private def e4437 : S 5 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (e4436) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bbcc6ac1880b5bc9d35)

private def e4438 : C 5 :=
.single (e4437)

private def e4439 : C 5 :=
.trans (e4438) (e1195)

private def e4440 : C 5 :=
.trans (e4435) (e4439)

private def e4441 : C 5 :=
.trans (e4419) (e4440)

private def e4442 : C 5 :=
.trans (e4416) (e4441)

private def e4443 : C 5 :=
.symm (e4442)

private def e4444 : C 5 :=
.trans (e1194) (e4443)

private def e4445 : C 5 :=
.trans (e1195) (e4444)

private def e4446 : C 5 :=
.trans (e4375) (e4375)

private def e4448 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d8c29a40acdb3a1ba84b)

private def e4450 : S 5 :=
.congAppFun (e1205) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e4451 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a34d521debc01e94518d) (e4450)

private def e4452 : C 5 :=
.single (e4451)

private def e4454 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db1e7e82853fd1e7734e)

private def e4455 : C 5 :=
.trans (e4452) (e4454)

private def e4456 : C 5 :=
.trans (e4448) (e4455)

private def e4457 : C 5 :=
.trans (e4456) (e4454)

private def e4458 : S 5 :=
.congAppFun (e1220) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e4459 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a34d521debc01e94518d) (e4458)

private def e4460 : C 5 :=
.single (e4459)

private def e4462 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_721b4245bd666d6cf9f2)

private def e4463 : C 5 :=
.trans (e4460) (e4462)

private def e4464 : C 5 :=
.trans (e4457) (e4463)

private def e4465 : C 5 :=
.trans (e4464) (e4462)

private def e4466 : S 5 :=
.congAppFun (e1232) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e4467 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a34d521debc01e94518d) (e4466)

private def e4468 : C 5 :=
.single (e4467)

private def e4470 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ce7aa35e18e87e8d2352)

private def e4471 : C 5 :=
.trans (e4468) (e4470)

private def e4472 : C 5 :=
.trans (e4465) (e4471)

private def e4473 : C 5 :=
.trans (e4472) (e4470)

private def e4474 : S 5 :=
.congAppFun (e1243) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e4475 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a34d521debc01e94518d) (e4474)

private def e4476 : C 5 :=
.single (e4475)

private def e4478 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5a5204ecf032061c563f)

private def e4479 : C 5 :=
.trans (e4476) (e4478)

private def e4480 : C 5 :=
.trans (e4473) (e4479)

private def e4481 : C 5 :=
.trans (e4480) (e4478)

private def e4482 : S 5 :=
.congAppFun (e1253) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e4483 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a34d521debc01e94518d) (e4482)

private def e4484 : C 5 :=
.single (e4483)

private def e4486 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_013b536ab065139e3ce9)

private def e4487 : C 5 :=
.trans (e4484) (e4486)

private def e4488 : C 5 :=
.trans (e4481) (e4487)

private def e4489 : C 5 :=
.trans (e4488) (e4486)

private def e4490 : S 5 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_654fba80bd6b6fd066fb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e4491 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a34d521debc01e94518d) (e4490)

private def e4492 : C 5 :=
.single (e4491)

private def e4494 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7994ab7708b42c2dfa46)

private def e4495 : C 5 :=
.trans (e4494) (e4494)

private def e4496 : C 5 :=
.trans (e4495) (e4494)

private def e4497 : C 5 :=
.trans (e4496) (e4494)

private def e4498 : C 5 :=
.trans (e4497) (e4494)

private def e4499 : C 5 :=
.trans (e4498) (e4494)

private def e4500 : C 5 :=
.trans (e4499) (e4494)

private def e4501 : S 5 :=
.congAppFun (e1275) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5828ffe8fb218f9a07e9)

private def e4502 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a34d521debc01e94518d) (e4501)

private def e4503 : C 5 :=
.single (e4502)

private def e4505 : C 5 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_caa23154d34c347a9902)

private def e4506 : C 5 :=
.trans (e4503) (e4505)

private def e4507 : C 5 :=
.trans (e4500) (e4506)

private def e4508 : C 5 :=
.trans (e4507) (e4505)

private def e4509 : S 5 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ebbeadb7fa87ad5fc506) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a34d521debc01e94518d) (e1382)

private def e4510 : C 5 :=
.single (e4509)

private def e4511 : C 5 :=
.trans (e4510) (e4446)

private def e4512 : C 5 :=
.trans (e4508) (e4511)

private def e4513 : C 5 :=
.trans (e4492) (e4512)

private def e4514 : C 5 :=
.trans (e4489) (e4513)

private def e4515 : C 5 :=
.symm (e4514)

private def e4516 : C 5 :=
.trans (e4375) (e4515)

private def e4517 : C 5 :=
.trans (e4446) (e4516)

private def e4518 : C 5 :=
.trans (e4445) (e4517)

private def e4519 : C 5 :=
.trans (e1194) (e4518)

private def e4520 : C 5 :=
.symm (e4448)

private def e4521 : C 5 :=
.trans (e4519) (e4520)

private def e4522 : C 5 :=
.trans (e1194) (e4521)

private def e4523 : T 5 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c8190ca12c764c3fe675) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1193) (e4372) (e4522)

private def e4524 : T 4 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4e574fe3584e51e8790c) (e4373) (e4523)

private def e4556 : C 7 :=
.trans (replay_14cccbd52fde40349f1e) (replay_3b99f7bed1c0f6f7b413)

private def e4563 : C 7 :=
.trans (e4556) (replay_b2aa3a7671ed45a37066)

private def e4564 : C 7 :=
.symm (replay_05e9a3e6048cffcd49ca)

private def e4565 : C 7 :=
.trans (replay_05e9a3e6048cffcd49ca) (e4564)

private def e4566 : C 7 :=
.trans (e4563) (e4565)

private def e4596 : C 7 :=
.symm (replay_8df455f94ca42b2cd447)

private def e4597 : C 7 :=
.trans (replay_8df455f94ca42b2cd447) (e4596)

private def e4598 : C 7 :=
.trans (replay_afa165c5d4e2317f1151) (e4597)

private def e4613 : C 7 :=
.trans (replay_e3f696a43616d6542540) (replay_a42a42dddcc11030523b)

private def e4614 : C 7 :=
.trans (e4613) (replay_b0b5e70f4c3c548a5304)

private def e4627 : C 7 :=
.trans (e4614) (replay_e5d66ab7f12349712d6a)

private def e4628 : C 7 :=
.symm (replay_802339c4a77ba7f6b8b5)

private def e4629 : C 7 :=
.trans (replay_802339c4a77ba7f6b8b5) (e4628)

private def e4630 : C 7 :=
.trans (e4627) (e4629)

private def e4631 : C 7 :=
.trans (e4598) (e4630)

private def e4632 : C 7 :=
.trans (e4631) (e4628)

private def e4633 : C 7 :=
.trans (replay_05e9a3e6048cffcd49ca) (e4632)

private def e4634 : C 7 :=
.trans (replay_05e9a3e6048cffcd49ca) (e4633)

private def e4635 : C 7 :=
.trans (e4634) (e4628)

private def e4636 : C 7 :=
.trans (replay_05e9a3e6048cffcd49ca) (e4635)

private def e4637 : C 7 :=
.trans (replay_05e9a3e6048cffcd49ca) (e4636)

private def e4638 : C 7 :=
.trans (e4637) (e4628)

private def e4639 : C 7 :=
.trans (replay_05e9a3e6048cffcd49ca) (e4638)

private def e4640 : C 7 :=
.trans (replay_05e9a3e6048cffcd49ca) (e4639)

private def e4641 : C 7 :=
.trans (e4640) (e4628)

private def e4642 : C 7 :=
.trans (replay_05e9a3e6048cffcd49ca) (e4641)

private def e4666 : C 7 :=
.symm (replay_9ab9d18a394622a6d49c)

private def e4667 : C 7 :=
.trans (replay_9ab9d18a394622a6d49c) (e4666)

private def e4668 : C 7 :=
.trans (replay_9c83f75934ef70c96f23) (e4667)

private def e4669 : C 7 :=
.trans (replay_802339c4a77ba7f6b8b5) (e4668)

private def e4670 : C 7 :=
.trans (e4669) (e4666)

private def e4671 : C 7 :=
.trans (replay_802339c4a77ba7f6b8b5) (e4670)

private def e4672 : C 7 :=
.trans (replay_802339c4a77ba7f6b8b5) (e4671)

private def e4673 : C 7 :=
.trans (e4672) (e4666)

private def e4674 : C 7 :=
.trans (replay_802339c4a77ba7f6b8b5) (e4673)

private def e4675 : C 7 :=
.trans (e4642) (e4674)

private def e4676 : C 7 :=
.trans (e4675) (e4666)

private def e4677 : C 7 :=
.trans (replay_05e9a3e6048cffcd49ca) (e4676)

private def e4678 : C 7 :=
.trans (e4566) (e4677)

private def e4679 : C 7 :=
.trans (e4678) (e4666)

private def e4680 : C 7 :=
.trans (replay_4dab3437bf1a01d0d06c) (e4679)

private def e4681 : T 7 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8b4750ea4865a31225d0) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_404b5de2e790e15a378c) (replay_0c98ca10692a8e74c78f) (replay_65e0c8e88a962c4e90ce) (e4680)

private def e4682 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d0f4a08c893ea38d53fb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e43db659e3238c828d2a) (e4681) (replay_ffab124b380a29bf4936)

private def e4689 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3c0bc581b5c76103a008) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_25754ce3a95bf2ac1065) (e4682) (replay_33e2254c77bb5c3a755e)

private def e4690 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f9a03288a6b4e36d75e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ac24a0a340e807ff46d1) (e4689) (replay_e197ee63c3c9ea3d9b51)

private def e4691 : T 7 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_61babc0a06ef8aba8578) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e8d9cb5ddbad2ec36aaf) (e4690) (replay_e197ee63c3c9ea3d9b51)

private def e4696 : T 8 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8b8b2762f64034c755e4) (e4311)

private def e4697 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83774d5525e9e22ed9e1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cd4d68304b85b6ea680) (e4696) (replay_534aece673191f529e08)

private def e4698 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b58f76c63882e11d87a9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8c0c56fa85e0ed9c6378) (e4697) (replay_87793defc7b760df9b5d)

private def e4699 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_56760c9c60918cbf3d6f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6a559ab14da0702c31d0) (e4698) (replay_534aece673191f529e08)

private def e4700 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6164f46507e2b2c8afe0) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1c6ad556b7e726bf44f3) (e4699) (replay_534aece673191f529e08)

private def e4701 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b53c96dd3c862d772319) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c147bd3db1fd948411b6) (e4700) (replay_534aece673191f529e08)

private def e4702 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0414169e5ce74c2eaeff) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43cd7be8392b3b43057e) (e1641) (e4701)

private def e4703 : T 8 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b53c96dd3c862d772319) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43cd7be8392b3b43057e) (e1618) (replay_534aece673191f529e08)

private def e4704 : T 8 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_ac6edf2f011575ef77cc) (e4702) (e4703)

private def e4705 : T 7 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e4691) (e4704)

private def e4729 : C 9 :=
.trans (replay_3dcaa86edfae438ca9bc) (replay_84b74d269795e684261a)

private def e4736 : C 9 :=
.trans (e4729) (replay_27b532003e453a9d684f)

private def e4737 : C 9 :=
.symm (replay_786bd379cbaa7ded4b1e)

private def e4738 : C 9 :=
.trans (replay_786bd379cbaa7ded4b1e) (e4737)

private def e4739 : C 9 :=
.trans (e4736) (e4738)

private def e4770 : C 9 :=
.symm (replay_be6161fedb8057b37a20)

private def e4771 : C 9 :=
.trans (replay_be6161fedb8057b37a20) (e4770)

private def e4772 : C 9 :=
.trans (replay_acb9325c2083574f6bee) (e4771)

private def e4786 : C 9 :=
.trans (replay_fa54c921a2e1c7de3179) (replay_8d521c0487b569c98dea)

private def e4787 : C 9 :=
.trans (e4786) (replay_687507273d8c682192f9)

private def e4799 : C 9 :=
.trans (e4787) (replay_cc60bec2bf616356f0cf)

private def e4800 : C 9 :=
.symm (replay_b7708d30c6d4c4cda7a9)

private def e4801 : C 9 :=
.trans (replay_b7708d30c6d4c4cda7a9) (e4800)

private def e4802 : C 9 :=
.trans (e4799) (e4801)

private def e4803 : C 9 :=
.trans (e4772) (e4802)

private def e4804 : C 9 :=
.trans (e4803) (e4800)

private def e4805 : C 9 :=
.trans (replay_786bd379cbaa7ded4b1e) (e4804)

private def e4806 : C 9 :=
.trans (replay_786bd379cbaa7ded4b1e) (e4805)

private def e4807 : C 9 :=
.trans (e4806) (e4800)

private def e4808 : C 9 :=
.trans (replay_786bd379cbaa7ded4b1e) (e4807)

private def e4809 : C 9 :=
.trans (replay_786bd379cbaa7ded4b1e) (e4808)

private def e4810 : C 9 :=
.trans (e4809) (e4800)

private def e4811 : C 9 :=
.trans (replay_786bd379cbaa7ded4b1e) (e4810)

private def e4812 : C 9 :=
.trans (replay_786bd379cbaa7ded4b1e) (e4811)

private def e4813 : C 9 :=
.trans (e4812) (e4800)

private def e4814 : C 9 :=
.trans (replay_786bd379cbaa7ded4b1e) (e4813)

private def e4837 : C 9 :=
.symm (replay_cf451debd08fef0d077a)

private def e4838 : C 9 :=
.trans (replay_cf451debd08fef0d077a) (e4837)

private def e4839 : C 9 :=
.trans (replay_b9181b891b8253fe6ce1) (e4838)

private def e4840 : C 9 :=
.trans (replay_b7708d30c6d4c4cda7a9) (e4839)

private def e4841 : C 9 :=
.trans (e4840) (e4837)

private def e4842 : C 9 :=
.trans (replay_b7708d30c6d4c4cda7a9) (e4841)

private def e4843 : C 9 :=
.trans (replay_b7708d30c6d4c4cda7a9) (e4842)

private def e4844 : C 9 :=
.trans (e4843) (e4837)

private def e4845 : C 9 :=
.trans (replay_b7708d30c6d4c4cda7a9) (e4844)

private def e4846 : C 9 :=
.trans (e4814) (e4845)

private def e4847 : C 9 :=
.trans (e4846) (e4837)

private def e4848 : C 9 :=
.trans (replay_786bd379cbaa7ded4b1e) (e4847)

private def e4849 : C 9 :=
.trans (e4739) (e4848)

private def e4850 : C 9 :=
.trans (e4849) (e4837)

private def e4851 : C 9 :=
.trans (replay_e21ac326fbc5a0c1888d) (e4850)

private def e4852 : T 9 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91feb772ae723aed1602) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_404b5de2e790e15a378c) (replay_8f43a735b842cb7523bc) (replay_719e93de639617d1a169) (e4851)

private def e4853 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23593caaab521d12b976) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_662c3dd4cd3b98ff3a2f) (e4852) (replay_8f68fd41cbd38b75604c)

private def e4858 : T 13 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (e1848) (replay_730a0c3ead453f836005)

private def e4859 : T 13 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_50d54f6ca4190fd6bc72) (e4858)

private def e4860 : T 12 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d3bc479f5fb249b99ac2) (replay_0dfcd936da11ba5961d0) (e4859)

private def e4861 : T 11 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c6b51e3ba4892036cdb0) (replay_fe796ff5aeef66f8dc35) (e4860)

private def e4862 : T 10 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_45e80a32c899dfd6b11b) (replay_13b3cc3ae79611258bfb) (e4861)

private def e4863 : T 9 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fafdfa0063130741b0e7) (replay_8478c25f21b5e72000e4) (e4862)

private def e4864 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_20047ddd1d4fe86023f6) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2031aba0209be2a5cb64) (e4853) (e4863)

private def e4865 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e056103386ad05d9d9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_74f9490a4cec0739cd11) (e4864) (replay_07c41680d17703d7171f)

private def e4866 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58bdea1e3c28d008f853) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_683a421a2ec88ad82286) (e4865) (replay_07c41680d17703d7171f)

private def e4867 : T 8 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (replay_534aece673191f529e08) (e4866)

private def e4875 : T 9 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8b8b2762f64034c755e4) (e4311)

private def e4876 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c537445f28d8d4cca5c8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e18357cd4454c60d304) (e4875) (replay_07c41680d17703d7171f)

private def e4877 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2ef36b27edf683785e3e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_57f2de1a81069d53bc57) (e4876) (e2195)

private def e4878 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e056103386ad05d9d9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_61ff19a605c7a340584e) (e4877) (replay_7943c3e0fd7c8e285c77)

private def e4879 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_04a2886bde316b33b302) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5fe258e75919e91cae58) (e4878) (e1887)

private def e4907 : C 11 :=
.trans (replay_7835b0909f791a09b724) (replay_c8aac366b22a6d2f80a7)

private def e4914 : C 11 :=
.trans (e4907) (replay_e4def31c514d73e072f4)

private def e4915 : C 11 :=
.symm (replay_bde18cda457e4d6e5a9f)

private def e4916 : C 11 :=
.trans (replay_bde18cda457e4d6e5a9f) (e4915)

private def e4917 : C 11 :=
.trans (e4914) (e4916)

private def e4947 : C 11 :=
.symm (replay_49a98e1975d2f2b35d44)

private def e4948 : C 11 :=
.trans (replay_49a98e1975d2f2b35d44) (e4947)

private def e4949 : C 11 :=
.trans (replay_f96a95be3d768fca2dba) (e4948)

private def e4964 : C 11 :=
.trans (replay_57fe8ba0e999a3932721) (replay_7f267439a329937baba5)

private def e4965 : C 11 :=
.trans (e4964) (replay_fab3bce7305375a9047a)

private def e4978 : C 11 :=
.trans (e4965) (replay_a392178186b07b70dd0b)

private def e4979 : C 11 :=
.symm (replay_51ab5b560199f805d93a)

private def e4980 : C 11 :=
.trans (replay_51ab5b560199f805d93a) (e4979)

private def e4981 : C 11 :=
.trans (e4978) (e4980)

private def e4982 : C 11 :=
.trans (e4949) (e4981)

private def e4983 : C 11 :=
.trans (e4982) (e4979)

private def e4984 : C 11 :=
.trans (replay_bde18cda457e4d6e5a9f) (e4983)

private def e4985 : C 11 :=
.trans (replay_bde18cda457e4d6e5a9f) (e4984)

private def e4986 : C 11 :=
.trans (e4985) (e4979)

private def e4987 : C 11 :=
.trans (replay_bde18cda457e4d6e5a9f) (e4986)

private def e4988 : C 11 :=
.trans (replay_bde18cda457e4d6e5a9f) (e4987)

private def e4989 : C 11 :=
.trans (e4988) (e4979)

private def e4990 : C 11 :=
.trans (replay_bde18cda457e4d6e5a9f) (e4989)

private def e4991 : C 11 :=
.trans (replay_bde18cda457e4d6e5a9f) (e4990)

private def e4992 : C 11 :=
.trans (e4991) (e4979)

private def e4993 : C 11 :=
.trans (replay_bde18cda457e4d6e5a9f) (e4992)

private def e5017 : C 11 :=
.symm (replay_99e40603cc15ba113f09)

private def e5018 : C 11 :=
.trans (replay_99e40603cc15ba113f09) (e5017)

private def e5019 : C 11 :=
.trans (replay_6590e1027f25e055c59b) (e5018)

private def e5020 : C 11 :=
.trans (replay_51ab5b560199f805d93a) (e5019)

private def e5021 : C 11 :=
.trans (e5020) (e5017)

private def e5022 : C 11 :=
.trans (replay_51ab5b560199f805d93a) (e5021)

private def e5023 : C 11 :=
.trans (replay_51ab5b560199f805d93a) (e5022)

private def e5024 : C 11 :=
.trans (e5023) (e5017)

private def e5025 : C 11 :=
.trans (replay_51ab5b560199f805d93a) (e5024)

private def e5026 : C 11 :=
.trans (e4993) (e5025)

private def e5027 : C 11 :=
.trans (e5026) (e5017)

private def e5028 : C 11 :=
.trans (replay_bde18cda457e4d6e5a9f) (e5027)

private def e5029 : C 11 :=
.trans (e4917) (e5028)

private def e5030 : C 11 :=
.trans (e5029) (e5017)

private def e5031 : C 11 :=
.trans (replay_872e2ac0c2f1db314175) (e5030)

private def e5032 : T 11 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3bab1b502735210f7920) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fa34719ab4861ce3b645) (replay_cf4324c475a7d556d45d) (replay_5d3ee164d0fd58f61332) (e5031)

private def e5033 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c4973f6eacdd028898bc) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6806caf1582d938d9203) (e5032) (replay_c93a4b141e1ddc8ceb10)

private def e5034 : T 15 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e2551) (replay_7bbd6a1783772f9a6990)

private def e5035 : T 15 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b8578195b133fac70a1) (e5034)

private def e5036 : T 14 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c7646540dd7e659fc407) (replay_6b7bbe559cee7162f069) (e5035)

private def e5037 : T 13 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e1d07338c040d26dff49) (replay_7c586ac2dc75f6944927) (e5036)

private def e5038 : T 12 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7e6cb354a8df3738086) (replay_6b41ac6edbef14999e2b) (e5037)

private def e5039 : T 11 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_088ec0f4742a888f4d7e) (replay_96538965c8af472f10f5) (e5038)

private def e5040 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7eb92b847aba15e06319) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7c34b2caceb9e7e9be7) (e5033) (e5039)

private def e5041 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1bed53fd97751c172144) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3aae42e08117325f8f16) (e5040) (replay_7fbeba8818273106d8c8)

private def e5042 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4e0bd14f54be2011bbdb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1f7880e8737675c0efb8) (e5041) (replay_7fbeba8818273106d8c8)

private def e5043 : T 10 :=
.sigmaForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5d3e7b0e50ed7249e009) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_8dd06e568960d2567ea5) (e5042)

private def e5044 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_50d54f6ca4190fd6bc72) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b8578195b133fac70a1) (e2094) (e5043)

private def e5045 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ac568e80b57a006474d9)

private def e5046 : C 9 :=
.trans (e5045) (e5045)

private def e5047 : C 9 :=
.trans (e5046) (e5045)

private def e5048 : C 9 :=
.trans (e5047) (e5045)

private def e5049 : C 9 :=
.trans (e5048) (e5045)

private def e5050 : C 9 :=
.trans (e5049) (e5045)

private def e5051 : C 9 :=
.trans (e5050) (e5045)

private def e5053 : S 9 :=
.congPiDom (e2111) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_be9bb8a2096c9f61993f)

private def e5054 : C 9 :=
.single (e5053)

private def e5056 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83b658fbfd2f49b339cb)

private def e5057 : C 9 :=
.trans (e5056) (e5056)

private def e5058 : S 9 :=
.congPiDom (e2123) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_be9bb8a2096c9f61993f)

private def e5059 : C 9 :=
.single (e5058)

private def e5061 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0b1ac8f307967f591ea7)

private def e5062 : C 9 :=
.trans (e5059) (e5061)

private def e5063 : C 9 :=
.trans (e5057) (e5062)

private def e5064 : C 9 :=
.trans (e5063) (e5061)

private def e5065 : S 9 :=
.congPiDom (e2134) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_be9bb8a2096c9f61993f)

private def e5066 : C 9 :=
.single (e5065)

private def e5068 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c58c532479067eaa6dad)

private def e5069 : C 9 :=
.trans (e5066) (e5068)

private def e5070 : C 9 :=
.trans (e5064) (e5069)

private def e5071 : C 9 :=
.trans (e5070) (e5068)

private def e5072 : S 9 :=
.congPiDom (e2144) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_be9bb8a2096c9f61993f)

private def e5073 : C 9 :=
.single (e5072)

private def e5075 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_09920e99fb9d479c3f9b)

private def e5076 : C 9 :=
.trans (e5073) (e5075)

private def e5077 : C 9 :=
.trans (e5071) (e5076)

private def e5078 : C 9 :=
.trans (e5077) (e5075)

private def e5079 : S 9 :=
.congPiDom (e2153) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_be9bb8a2096c9f61993f)

private def e5080 : C 9 :=
.single (e5079)

private def e5082 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_139389591ee089d86a80)

private def e5083 : C 9 :=
.trans (e5080) (e5082)

private def e5084 : C 9 :=
.trans (e5078) (e5083)

private def e5085 : C 9 :=
.trans (e5054) (e5084)

private def e5086 : C 9 :=
.trans (e5051) (e5085)

private def e5087 : C 9 :=
.trans (e5082) (e5082)

private def e5088 : S 9 :=
.congPiDom (e2166) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_be9bb8a2096c9f61993f)

private def e5089 : C 9 :=
.single (e5088)

private def e5091 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9068a476d4f3499950f9)

private def e5092 : C 9 :=
.trans (e5089) (e5091)

private def e5093 : C 9 :=
.trans (e5087) (e5092)

private def e5094 : C 9 :=
.symm (e5091)

private def e5095 : C 9 :=
.trans (e5091) (e5094)

private def e5096 : C 9 :=
.trans (e5093) (e5095)

private def e5097 : C 9 :=
.trans (e5096) (e5091)

private def e5098 : C 9 :=
.trans (e5097) (e5094)

private def e5099 : C 9 :=
.trans (e5086) (e5098)

private def e5100 : C 9 :=
.trans (e5091) (e5091)

private def e5101 : C 9 :=
.trans (e5100) (e5091)

private def e5102 : C 9 :=
.trans (e5101) (e5091)

private def e5103 : C 9 :=
.trans (e5102) (e5091)

private def e5104 : C 9 :=
.trans (e5103) (e5091)

private def e5105 : C 9 :=
.trans (e5104) (e5091)

private def e5106 : decoder.Code 10 :=
.inherited (.declared (.inl (.inl ⟨3, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 5,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 13))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 9]⟩)))

private def e5107 : S 10 :=
.root (e5106)

private def e5108 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c34919923848a2b3766f) (e5107)

private def e5109 : C 9 :=
.single (e5108)

private def e5111 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c385aa627acdaa16f268)

private def e5112 : C 9 :=
.trans (e5111) (e5111)

private def e5113 : S 10 :=
.congAppFun (e2646) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e9c073bd7cf6856c0f8)

private def e5114 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c34919923848a2b3766f) (e5113)

private def e5115 : C 9 :=
.single (e5114)

private def e5117 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6113d21a40b905f1a073)

private def e5118 : C 9 :=
.trans (e5115) (e5117)

private def e5119 : C 9 :=
.trans (e5112) (e5118)

private def e5120 : C 9 :=
.trans (e5119) (e5117)

private def e5121 : S 10 :=
.congAppFun (e2657) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e9c073bd7cf6856c0f8)

private def e5122 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c34919923848a2b3766f) (e5121)

private def e5123 : C 9 :=
.single (e5122)

private def e5125 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_60cd431410827077c52f)

private def e5126 : C 9 :=
.trans (e5123) (e5125)

private def e5127 : C 9 :=
.trans (e5120) (e5126)

private def e5128 : C 9 :=
.trans (e5127) (e5125)

private def e5129 : S 10 :=
.congAppFun (e2667) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e9c073bd7cf6856c0f8)

private def e5130 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c34919923848a2b3766f) (e5129)

private def e5131 : C 9 :=
.single (e5130)

private def e5133 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c192fd063ed6ac528bac)

private def e5134 : C 9 :=
.trans (e5131) (e5133)

private def e5135 : C 9 :=
.trans (e5128) (e5134)

private def e5136 : C 9 :=
.trans (e5135) (e5133)

private def e5137 : S 10 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3796eb9c049c940c2c21) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e9c073bd7cf6856c0f8)

private def e5138 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c34919923848a2b3766f) (e5137)

private def e5139 : C 9 :=
.single (e5138)

private def e5141 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_723a53e8c2c48eaf476f)

private def e5142 : C 9 :=
.trans (e5139) (e5141)

private def e5143 : C 9 :=
.trans (e5136) (e5142)

private def e5144 : C 9 :=
.trans (e5109) (e5143)

private def e5145 : C 9 :=
.trans (e5105) (e5144)

private def e5146 : C 9 :=
.trans (e5141) (e5141)

private def e5147 : S 10 :=
.congSigmaDom (e2688) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6070d91bc17ad1d91bc8)

private def e5148 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c34919923848a2b3766f) (e5147)

private def e5149 : C 9 :=
.single (e5148)

private def e5151 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_34a4bad7eaab1e6f0a74)

private def e5152 : C 9 :=
.trans (e5149) (e5151)

private def e5153 : C 9 :=
.trans (e5146) (e5152)

private def e5154 : C 9 :=
.symm (e5151)

private def e5155 : C 9 :=
.trans (e5151) (e5154)

private def e5156 : C 9 :=
.trans (e5153) (e5155)

private def e5157 : C 9 :=
.trans (e5156) (e5151)

private def e5158 : C 9 :=
.trans (e5157) (e5154)

private def e5159 : C 9 :=
.trans (e5145) (e5158)

private def e5160 : C 9 :=
.trans (e5099) (e5159)

private def e5161 : C 9 :=
.trans (e5160) (e5154)

private def e5162 : C 9 :=
.trans (e5045) (e5161)

private def e5163 : T 9 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ac568e80b57a006474d9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f1549bf852781838d6c5) (e4879) (e5044) (e5162)

private def e5164 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c34919923848a2b3766f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f955f7cb06972bacc054) (e5163) (replay_07c41680d17703d7171f)

private def e5165 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53a3d94e880c845f90cc) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05) (e2777) (e5164)

private def e5166 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c34919923848a2b3766f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05) (e2182) (replay_07c41680d17703d7171f)

private def e5167 : T 9 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1865) (e5165) (e5166)

private def e5168 : T 8 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_50d54f6ca4190fd6bc72) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e4867) (e5167)

private def e5169 : T 7 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_897db4146fa986a8835c) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3113b23543c4066f3ea8) (e4705) (e5168)

private def e5170 : T 6 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e739772b6969f56d5a19) (replay_629e69ece1b1fb7e3753) (e5169)

private def e5171 : T 5 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08ae2de3ec478e9612f9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_512bcf58ddc7c9e66ce6) (replay_088a7fed4563d6a06e7a) (e5170)

private def e5172 : T 4 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2006796238039c1078f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e39390df5491d175ad39) (replay_909a1aacbbe83fd007eb) (e5171)

private def e5183 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9e056103386ad05d9d9f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_61ff19a605c7a340584e) (e4877) (replay_07c41680d17703d7171f)

private def e5184 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58bdea1e3c28d008f853) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5546162d36cc597cdb84) (e5183) (replay_07c41680d17703d7171f)

private def e5185 : T 9 :=
.sndElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_198d6bd75ff0377bcd7c) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9530908dcf6c5275717) (replay_07c41680d17703d7171f)

private def e5186 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91a3417e737975260050) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e9c073bd7cf6856c0f8) (e5184) (e5185)

private def e5187 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c147bd3db1fd948411b6) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7acbea17057f912a2e1f) (e3090) (e5186)

private def e5188 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43cd7be8392b3b43057e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2a40f50a9220bc974333) (e2829) (e5187)

private def e5193 : T 10 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83f28e98241a6dba6c95) (e1035)

private def e5194 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b74e03acbfc24aeb10e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_16a566944e1d08fae3e4) (e5193) (replay_8dd06e568960d2567ea5)

private def e5195 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f1eda03ec62354b37392) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d6131b032b3a43f01241) (e5194) (replay_8dd06e568960d2567ea5)

private def e5196 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ffbcdddae5a4ba50f754) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_584b7a8ba57af589e021) (e5195) (replay_8dd06e568960d2567ea5)

private def e5197 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_de0d936cd54f5c2b0737) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7552a3121e7db764fb44) (e5196) (replay_8dd06e568960d2567ea5)

private def e5202 : T 10 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8b8b2762f64034c755e4) (e4311)

private def e5203 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b74e03acbfc24aeb10e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f35cb17c60147663cca5) (e5202) (replay_8dd06e568960d2567ea5)

private def e5204 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5788cbd50333d7cba0b5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9407535fd0b11a14f9c8) (e5203) (e372)

private def e5205 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ffbcdddae5a4ba50f754) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_adfe04c2291c6b7b0371) (e5204) (replay_8dd06e568960d2567ea5)

private def e5206 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_de0d936cd54f5c2b0737) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d4f2241246a516c4fc26) (e5205) (replay_8dd06e568960d2567ea5)

private def e5207 : T 10 :=
.sndElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e48b53379ef509db2cd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_151601d70406d501031f) (replay_8dd06e568960d2567ea5)

private def e5208 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c9530908dcf6c5275717) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6070d91bc17ad1d91bc8) (e5206) (e5207)

private def e5209 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e9c073bd7cf6856c0f8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5b38fe4a9e893712e8f5) (e5197) (e5208)

private def e5210 : T 10 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_38dd6b1b76e4eaa10164) (e5209) (replay_8dd06e568960d2567ea5)

private def e5211 : T 10 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b4f93e456b4620d589d9) (e5210) (replay_e78213c920befa21e944)

private def e5212 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_acf7017ce42f9b0db39d) (replay_6377a49faab46f0b3589) (e5211)

private def e5213 : T 12 :=
.fstElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1d9546e4677c786bbc69) (replay_c1e92b3aeffe2c000a2a)

private def e5214 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cbd13c1b0d830c739b7) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_061d46b0be70038a96e4) (e2913) (e5213)

private def e5215 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a7c6077368bfe7e62c76) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_34dba01e61e8a9ddf283) (e5214) (replay_c1e92b3aeffe2c000a2a)

private def e5216 : T 11 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23e09003749289e9f868) (e2888) (e5215)

private def e5221 : T 11 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83f28e98241a6dba6c95) (e1035)

private def e5222 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9528e48ce4f30ad868d8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ea5834bee7e411742514) (e5221) (replay_7fbeba8818273106d8c8)

private def e5223 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e8e4b831c3ede895f4ee) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3ab7520bfa07e623d7d0) (e5222) (replay_7fbeba8818273106d8c8)

private def e5224 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1bed53fd97751c172144) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dfb9c791ede41fcd2253) (e5223) (replay_7fbeba8818273106d8c8)

private def e5225 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4e0bd14f54be2011bbdb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_570744564ca3c9765efd) (e5224) (replay_7fbeba8818273106d8c8)

private def e5230 : T 11 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8b8b2762f64034c755e4) (e4311)

private def e5231 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9528e48ce4f30ad868d8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_09e94c579babb8a90780) (e5230) (replay_7fbeba8818273106d8c8)

private def e5232 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_93bc1dc99b942fdecf01) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b39c02f7146484d873a8) (e5231) (replay_b7c1a32946869ad8b824)

private def e5233 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1bed53fd97751c172144) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9fcb3fa794dac924e4cb) (e5232) (replay_7fbeba8818273106d8c8)

private def e5234 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4e0bd14f54be2011bbdb) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b7f8bde1c2a0af14ec64) (e5233) (replay_7fbeba8818273106d8c8)

private def e5235 : T 11 :=
.sndElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8304ec2301382ae96f36) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0caf5b45b395fbd0200b) (replay_7fbeba8818273106d8c8)

private def e5236 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_151601d70406d501031f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b006f548fe947033feb3) (e5234) (e5235)

private def e5237 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6070d91bc17ad1d91bc8) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a7c6077368bfe7e62c76) (e5225) (e5236)

private def e5238 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5b38fe4a9e893712e8f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_aa0a81f376b61e120915) (e5216) (e5237)

private def e5239 : T 11 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5b38fe4a9e893712e8f5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_aa0a81f376b61e120915) (e5216) (replay_7fbeba8818273106d8c8)

private def e5240 : T 11 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_96656f23ea73a7756060) (e5238) (e5239)

private def e5241 : T 11 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e5240)

private def e5242 : T 10 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_acf7017ce42f9b0db39d) (e5211) (e5241)

private def e5243 : T 9 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_355f5fe51b324cac9ec6) (e5212) (e5242)

private def e5244 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_72bb25e1161b081ef37d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8e03b2cc365a2a1c6d76) (e5188) (e5243)

private def e5245 : T 10 :=
.fstElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_151601d70406d501031f) (replay_8dd06e568960d2567ea5)

private def e5246 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e48b53379ef509db2cd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_01b217c61da8aff85c88) (replay_b9c16285c0fa5ea2d735) (e5245)

private def e5247 : T 10 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7acbea17057f912a2e1f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2dad9618308ff0113d64) (e5246) (replay_8dd06e568960d2567ea5)

private def e5248 : T 9 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23e09003749289e9f868) (e2950) (e5247)

private def e5249 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43cd7be8392b3b43057e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0c0b22ad1b74f63f5d05) (e5248) (e5187)

private def e5250 : T 9 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e1865) (e5249) (e5249)

private def e5251 : T 11 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e2880) (e5237) (replay_7fbeba8818273106d8c8)

private def e5253 : T 13 :=
.fstElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3f5d15f6442f72be0125) (replay_8dab544be16d5febf71b)

private def e5254 : T 13 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_63be3dfe28f667bec1df) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3c1b34a96babe84579aa) (e2982) (e5253)

private def e5255 : T 13 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4d666b839df4228f54d6) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9aaa273cc8e63d451349) (e5254) (replay_8dab544be16d5febf71b)

private def e5256 : T 12 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23e09003749289e9f868) (e2973) (e5255)

private def e5261 : T 12 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_83f28e98241a6dba6c95) (e1035)

private def e5262 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dd4fc597f6a31798810d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4d65817f051162d79f0c) (e5261) (replay_c1e92b3aeffe2c000a2a)

private def e5263 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f0e9a76be79e0b80849) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f3d99153bae982e1b915) (e5262) (replay_c1e92b3aeffe2c000a2a)

private def e5264 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_76bf2a76d66e1cc66026) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_384aea72601acaf4b13b) (e5263) (replay_c1e92b3aeffe2c000a2a)

private def e5265 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fe88179aa6c8dfa346aa) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3b1376f6375b7c440c77) (e5264) (replay_c1e92b3aeffe2c000a2a)

private def e5270 : T 12 :=
.const (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8b8b2762f64034c755e4) (e4311)

private def e5271 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dd4fc597f6a31798810d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_177609853a4bdcb3d459) (e5270) (replay_c1e92b3aeffe2c000a2a)

private def e5272 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5a2c5de69dc02b98119c) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e561c744a96f1e0ebf7a) (e5271) (e3007)

private def e5273 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_76bf2a76d66e1cc66026) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e893caebf17a03ea61a7) (e5272) (replay_c1e92b3aeffe2c000a2a)

private def e5274 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fe88179aa6c8dfa346aa) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a2cef221b1df54bf01ef) (e5273) (replay_c1e92b3aeffe2c000a2a)

private def e5275 : T 12 :=
.sndElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cbd13c1b0d830c739b7) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1d9546e4677c786bbc69) (replay_c1e92b3aeffe2c000a2a)

private def e5276 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0caf5b45b395fbd0200b) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_89e69438b08397b3b26c) (e5274) (e5275)

private def e5277 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b006f548fe947033feb3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4d666b839df4228f54d6) (e5265) (e5276)

private def e5278 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a7c6077368bfe7e62c76) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_34dba01e61e8a9ddf283) (e5256) (e5277)

private def e5279 : T 12 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a7c6077368bfe7e62c76) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_34dba01e61e8a9ddf283) (e5256) (replay_c1e92b3aeffe2c000a2a)

private def e5280 : T 12 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e2887) (e5278) (e5279)

private def e5281 : T 11 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e5251) (e5280)

private def e5282 : T 10 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23e09003749289e9f868) (replay_38dd6b1b76e4eaa10164) (e5281)

private def e5283 : T 9 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_833055146ebc3616f75b) (e5250) (e5282)

private def e5284 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_31bfe4563ac329da223f)

private def e5285 : C 9 :=
.trans (e5284) (e5284)

private def e5288 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d809ecba20934473962b) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5290 : S 9 :=
.congAppFun (e5288) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e30f2ce22ac293e50b5)

private def e5292 : S 9 :=
.congPiDom (e5290) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d922c2df4451da166257)

private def e5293 : C 9 :=
.single (e5292)

private def e5295 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1a87df6a7935d37c8c72)

private def e5296 : C 9 :=
.trans (e5293) (e5295)

private def e5297 : C 9 :=
.trans (e5285) (e5296)

private def e5298 : C 9 :=
.trans (e5297) (e5295)

private def e5300 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9c611ec0ec08d7477240) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_0e30f2ce22ac293e50b5)

private def e5301 : S 9 :=
.congPiDom (e5300) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d922c2df4451da166257)

private def e5302 : C 9 :=
.single (e5301)

private def e5304 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f64dfaade917e4144bc9)

private def e5305 : C 9 :=
.trans (e5302) (e5304)

private def e5306 : C 9 :=
.trans (e5298) (e5305)

private def e5307 : C 9 :=
.symm (e5304)

private def e5308 : C 9 :=
.trans (e5304) (e5307)

private def e5309 : C 9 :=
.trans (e5306) (e5308)

private def e5310 : C 9 :=
.trans (e5304) (e5304)

private def e5313 : S 12 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2bfc9664a4ba1b2a16f3) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2f252033ccef6a6a834a)

private def e5314 : S 12 :=
.congAppFun (e5313) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f6020bec2f79974210d6)

private def e5315 : S 11 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9464041a56fece3db0f7) (e5314)

private def e5316 : S 10 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7acbea17057f912a2e1f) (e5315)

private def e5317 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_965fa5e7f34174f21daf) (e5316)

private def e5318 : C 9 :=
.single (e5317)

private def e5320 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b5f0e1ae601477772d4e)

private def e5321 : C 9 :=
.trans (e5318) (e5320)

private def e5322 : C 9 :=
.trans (e5310) (e5321)

private def e5323 : C 9 :=
.trans (e5322) (e5320)

private def e5325 : S 12 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8355f01bfda2f127d5df) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f6020bec2f79974210d6)

private def e5326 : S 11 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9464041a56fece3db0f7) (e5325)

private def e5327 : S 10 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7acbea17057f912a2e1f) (e5326)

private def e5328 : S 9 :=
.congPiCod (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_965fa5e7f34174f21daf) (e5327)

private def e5329 : C 9 :=
.single (e5328)

private def e5331 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_588afb5dc6b946216aa7)

private def e5332 : C 9 :=
.trans (e5329) (e5331)

private def e5333 : C 9 :=
.trans (e5323) (e5332)

private def e5334 : C 9 :=
.symm (e5331)

private def e5335 : C 9 :=
.trans (e5331) (e5334)

private def e5336 : C 9 :=
.trans (e5333) (e5335)

private def e5337 : C 9 :=
.trans (e5304) (e5336)

private def e5338 : C 9 :=
.trans (e5337) (e5334)

private def e5339 : C 9 :=
.trans (e5304) (e5338)

private def e5340 : C 9 :=
.trans (e5304) (e5339)

private def e5341 : C 9 :=
.trans (e5340) (e5334)

private def e5342 : C 9 :=
.trans (e5304) (e5341)

private def e5343 : C 9 :=
.trans (e5309) (e5342)

private def e5344 : C 9 :=
.trans (e5343) (e5334)

private def e5345 : C 9 :=
.trans (e5284) (e5344)

private def e5346 : T 9 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_31bfe4563ac329da223f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_12f905a83669d167121c) (e5244) (e5283) (e5345)

private def e5347 : T 9 :=
.reflIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5249)

private def e5348 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_965fa5e7f34174f21daf) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2ad3d6a3ae1a88c613e1) (e5346) (e5347)

private def e5349 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91a3417e737975260050) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7acbea17057f912a2e1f) (e2833) (e5185)

private def e5350 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_43cd7be8392b3b43057e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a3a1435e63015ae7f5e3) (e5348) (e5349)

private def e5352 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_91a3417e737975260050) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6bee6232e445da9d488f) (replay_07c41680d17703d7171f) (e5185)

private def e5353 : T 9 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_461be56eee80a1033f9e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_01117dd69395b026a3ae) (e5350) (e5352)

private def e5354 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_40bd47d032ac48565488)

private def e5355 : C 9 :=
.trans (e5354) (e5354)

private def e5356 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ff7f49280c21442dc691) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5358 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5356) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5359 : C 9 :=
.single (e5358)

private def e5361 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e6c830f8c6c24ea3ce5a)

private def e5362 : C 9 :=
.trans (e5361) (e5361)

private def e5363 : C 9 :=
.trans (e5362) (e5361)

private def e5364 : C 9 :=
.trans (e5363) (e5361)

private def e5365 : C 9 :=
.trans (e5364) (e5361)

private def e5366 : C 9 :=
.trans (e5359) (e5365)

private def e5367 : C 9 :=
.trans (e5355) (e5366)

private def e5369 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fc2415e20f522bbfb24)

private def e5370 : decoder.Code 9 :=
.delta (`CumulativeTower.AllEvidence.lower)

private def e5371 : S 9 :=
.root (e5370)

private def e5372 : S 9 :=
.congAppFun (e5371) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e2c1e2e15bb0cda87a)

private def e5373 : S 9 :=
.congAppFun (e5372) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05cfdcba93e50df46b)

private def e5374 : S 9 :=
.congAppFun (e5373) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e5375 : S 9 :=
.congAppFun (e5374) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e5376 : S 9 :=
.congAppFun (e5375) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e5377 : S 9 :=
.congFst (e5376)

private def e5378 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e5377)

private def e5379 : S 9 :=
.congAppFun (e5378) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5380 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5379) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5381 : C 9 :=
.single (e5380)

private def e5383 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_53d4d6b82cecfbed67a1)

private def e5384 : C 9 :=
.trans (e5381) (e5383)

private def e5385 : C 9 :=
.trans (e5369) (e5384)

private def e5386 : C 9 :=
.trans (e5385) (e5383)

private def e5388 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7ee944fc1ac0fe2b701d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62e2c1e2e15bb0cda87a)

private def e5389 : S 9 :=
.congAppFun (e5388) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05cfdcba93e50df46b)

private def e5390 : S 9 :=
.congAppFun (e5389) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e5391 : S 9 :=
.congAppFun (e5390) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e5392 : S 9 :=
.congAppFun (e5391) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e5393 : S 9 :=
.congFst (e5392)

private def e5394 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e5393)

private def e5395 : S 9 :=
.congAppFun (e5394) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5396 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5395) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5397 : C 9 :=
.single (e5396)

private def e5399 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_32c02446a7e5b9548527)

private def e5400 : C 9 :=
.trans (e5397) (e5399)

private def e5401 : C 9 :=
.trans (e5386) (e5400)

private def e5402 : C 9 :=
.trans (e5401) (e5399)

private def e5404 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4126c369f6012a898de6) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bb05cfdcba93e50df46b)

private def e5405 : S 9 :=
.congAppFun (e5404) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e5406 : S 9 :=
.congAppFun (e5405) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e5407 : S 9 :=
.congAppFun (e5406) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e5408 : S 9 :=
.congFst (e5407)

private def e5409 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e5408)

private def e5410 : S 9 :=
.congAppFun (e5409) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5411 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5410) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5412 : C 9 :=
.single (e5411)

private def e5414 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_70beec9da33638d0e0a3)

private def e5415 : C 9 :=
.trans (e5412) (e5414)

private def e5416 : C 9 :=
.trans (e5402) (e5415)

private def e5417 : C 9 :=
.trans (e5416) (e5414)

private def e5419 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9c8cd2b96f5e50f40775) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_969f5c4050c59417fa55)

private def e5420 : S 9 :=
.congAppFun (e5419) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e5421 : S 9 :=
.congAppFun (e5420) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e5422 : S 9 :=
.congFst (e5421)

private def e5423 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e5422)

private def e5424 : S 9 :=
.congAppFun (e5423) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5425 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5424) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5426 : C 9 :=
.single (e5425)

private def e5428 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a4abd31d4661e4d64951)

private def e5429 : C 9 :=
.trans (e5426) (e5428)

private def e5430 : C 9 :=
.trans (e5417) (e5429)

private def e5431 : C 9 :=
.trans (e5430) (e5428)

private def e5433 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fdb8ace2b2cf0f6c92cf) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_38f6d713e98910bb6fa6)

private def e5434 : S 9 :=
.congAppFun (e5433) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e5435 : S 9 :=
.congFst (e5434)

private def e5436 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e5435)

private def e5437 : S 9 :=
.congAppFun (e5436) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5438 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5437) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5439 : C 9 :=
.single (e5438)

private def e5441 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6b2923fcc7aee3bada5d)

private def e5442 : C 9 :=
.trans (e5441) (e5441)

private def e5443 : C 9 :=
.trans (e5442) (e5441)

private def e5444 : C 9 :=
.trans (e5443) (e5441)

private def e5445 : C 9 :=
.trans (e5444) (e5441)

private def e5446 : C 9 :=
.trans (e5445) (e5441)

private def e5447 : C 9 :=
.trans (e5446) (e5441)

private def e5448 : decoder.Code 9 :=
.inherited (.declared (.inl (.inl ⟨3, [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 3,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 4,
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pair
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.fst
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.snd
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0)))))))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.pi
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                     `CumulativeTower.Vec.eliminate)
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 10))
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                             (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2))
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 3)))))))
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                   `CumulativeTower.Nat.zero)))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 14))
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1))
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 0))
       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                     `CumulativeTower.Vec.eliminate)
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 11))
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.head
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.LevelTower.Head.sort
                         (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.max
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 0)
                           (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.param 2)))))))
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.id
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const `CumulativeTower.Nat.zero)
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.const
                   `CumulativeTower.Nat.zero)))
             (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
               (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                 (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                   (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                     (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.sigma
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.app
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.lam
                           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 15))
                         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
                       (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))))))
           (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 2))
         (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 1)))),
 Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tm.var 8]⟩)))

private def e5449 : S 9 :=
.root (e5448)

private def e5450 : S 9 :=
.congAppFun (e5449) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e5451 : S 9 :=
.congFst (e5450)

private def e5452 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e5451)

private def e5453 : S 9 :=
.congAppFun (e5452) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5454 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5453) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5455 : C 9 :=
.single (e5454)

private def e5457 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f4b59553e906d6df8dc4)

private def e5458 : C 9 :=
.trans (e5457) (e5457)

private def e5460 : S 9 :=
.congAppFun (e3209) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e144e587203f104c28a8)

private def e5461 : S 9 :=
.congAppFun (e5460) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e5462 : S 9 :=
.congFst (e5461)

private def e5463 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e5462)

private def e5464 : S 9 :=
.congAppFun (e5463) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5465 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5464) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5466 : C 9 :=
.single (e5465)

private def e5468 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fd5d8fe58e880af4edce)

private def e5469 : C 9 :=
.trans (e5466) (e5468)

private def e5470 : C 9 :=
.trans (e5458) (e5469)

private def e5471 : C 9 :=
.trans (e5470) (e5468)

private def e5472 : S 9 :=
.congAppFun (e3225) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e144e587203f104c28a8)

private def e5473 : S 9 :=
.congAppFun (e5472) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e5474 : S 9 :=
.congFst (e5473)

private def e5475 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e5474)

private def e5476 : S 9 :=
.congAppFun (e5475) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5477 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5476) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5478 : C 9 :=
.single (e5477)

private def e5480 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9f599fe4da04d6cfa60b)

private def e5481 : C 9 :=
.trans (e5478) (e5480)

private def e5482 : C 9 :=
.trans (e5471) (e5481)

private def e5483 : C 9 :=
.trans (e5482) (e5480)

private def e5484 : S 9 :=
.congAppFun (e3239) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e144e587203f104c28a8)

private def e5485 : S 9 :=
.congAppFun (e5484) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e5486 : S 9 :=
.congFst (e5485)

private def e5487 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e5486)

private def e5488 : S 9 :=
.congAppFun (e5487) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5489 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5488) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5490 : C 9 :=
.single (e5489)

private def e5492 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8cd738c1faf0a97d2620)

private def e5493 : C 9 :=
.trans (e5490) (e5492)

private def e5494 : C 9 :=
.trans (e5483) (e5493)

private def e5495 : C 9 :=
.trans (e5494) (e5492)

private def e5496 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8e97b24d23d0cb38a5d9) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e144e587203f104c28a8)

private def e5497 : S 9 :=
.congAppFun (e5496) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e5498 : S 9 :=
.congFst (e5497)

private def e5499 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e5498)

private def e5500 : S 9 :=
.congAppFun (e5499) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5501 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5500) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5502 : C 9 :=
.single (e5501)

private def e5504 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3b9a2401bbb0239c71eb)

private def e5505 : C 9 :=
.trans (e5502) (e5504)

private def e5506 : C 9 :=
.trans (e5495) (e5505)

private def e5507 : C 9 :=
.trans (e5455) (e5506)

private def e5508 : C 9 :=
.trans (e5447) (e5507)

private def e5509 : C 9 :=
.trans (e5439) (e5508)

private def e5510 : C 9 :=
.trans (e5431) (e5509)

private def e5511 : C 9 :=
.trans (e5510) (e5504)

private def e5513 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_eec65f4c9e46b0e3d66e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e5514 : S 9 :=
.congFst (e5513)

private def e5515 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e5514)

private def e5516 : S 9 :=
.congAppFun (e5515) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5517 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5516) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5518 : C 9 :=
.single (e5517)

private def e5520 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4bc9aea04d3751ef8369)

private def e5521 : C 9 :=
.trans (e5518) (e5520)

private def e5522 : C 9 :=
.trans (e5511) (e5521)

private def e5524 : S 9 :=
.betaSigmaFst (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a97388c54c77a8f2aaf2) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f46704837e79054f88f)

private def e5525 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b18cdd29e7c1bfd5a735) (e5524)

private def e5526 : S 9 :=
.congAppFun (e5525) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_47cb3d06c5a352c9771a)

private def e5527 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5526) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5528 : C 9 :=
.single (e5527)

private def e5529 : C 9 :=
.trans (e5528) (e5361)

private def e5530 : C 9 :=
.trans (e5522) (e5529)

private def e5531 : C 9 :=
.symm (e5530)

private def e5532 : C 9 :=
.trans (e5361) (e5531)

private def e5533 : C 9 :=
.trans (e5361) (e5532)

private def e5534 : C 9 :=
.trans (e5361) (e5533)

private def e5535 : C 9 :=
.trans (e5369) (e5369)

private def e5536 : C 9 :=
.trans (e5535) (e5369)

private def e5537 : C 9 :=
.trans (e5536) (e5369)

private def e5538 : C 9 :=
.symm (e5537)

private def e5539 : C 9 :=
.trans (e5534) (e5538)

private def e5540 : C 9 :=
.trans (e5364) (e5539)

private def e5543 : S 9 :=
.congAppFun (e3741) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ac9a8299506bb35a9268)

private def e5544 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5543)

private def e5545 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5544) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5546 : C 9 :=
.single (e5545)

private def e5548 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_779f4f988f21549771e4)

private def e5549 : C 9 :=
.trans (e5546) (e5548)

private def e5550 : C 9 :=
.trans (e5369) (e5549)

private def e5551 : C 9 :=
.trans (e5550) (e5548)

private def e5552 : S 9 :=
.congAppFun (e3755) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ac9a8299506bb35a9268)

private def e5553 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5552)

private def e5554 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5553) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5555 : C 9 :=
.single (e5554)

private def e5557 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_57cb661c6d7e67d7dc65)

private def e5558 : C 9 :=
.trans (e5555) (e5557)

private def e5559 : C 9 :=
.trans (e5551) (e5558)

private def e5560 : C 9 :=
.trans (e5559) (e5557)

private def e5561 : S 9 :=
.congAppFun (e3768) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ac9a8299506bb35a9268)

private def e5562 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5561)

private def e5563 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5562) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5564 : C 9 :=
.single (e5563)

private def e5566 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d23d8585fa3418e0e82c)

private def e5567 : C 9 :=
.trans (e5564) (e5566)

private def e5568 : C 9 :=
.trans (e5560) (e5567)

private def e5569 : C 9 :=
.trans (e5568) (e5566)

private def e5570 : S 9 :=
.congAppFun (e3780) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ac9a8299506bb35a9268)

private def e5571 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5570)

private def e5572 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5571) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5573 : C 9 :=
.single (e5572)

private def e5575 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_05abb9c3444c05206adb)

private def e5576 : C 9 :=
.trans (e5573) (e5575)

private def e5577 : C 9 :=
.trans (e5569) (e5576)

private def e5578 : C 9 :=
.trans (e5577) (e5575)

private def e5579 : S 9 :=
.congAppFun (e3791) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ac9a8299506bb35a9268)

private def e5580 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5579)

private def e5581 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5580) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5582 : C 9 :=
.single (e5581)

private def e5584 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_30c883df9ceb45eb85ca)

private def e5585 : C 9 :=
.trans (e5582) (e5584)

private def e5586 : C 9 :=
.trans (e5578) (e5585)

private def e5587 : C 9 :=
.trans (e5586) (e5584)

private def e5588 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_284165a1d561d43df78c) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ac9a8299506bb35a9268)

private def e5589 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5588)

private def e5590 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5589) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5591 : C 9 :=
.single (e5590)

private def e5593 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_84f4942897dfda2ce2be)

private def e5594 : C 9 :=
.trans (e5593) (e5593)

private def e5595 : C 9 :=
.trans (e5594) (e5593)

private def e5596 : C 9 :=
.trans (e5595) (e5593)

private def e5597 : C 9 :=
.trans (e5596) (e5593)

private def e5598 : C 9 :=
.trans (e5597) (e5593)

private def e5599 : C 9 :=
.trans (e5598) (e5593)

private def e5600 : C 9 :=
.trans (e5599) (e5593)

private def e5601 : C 9 :=
.trans (e5591) (e5600)

private def e5602 : C 9 :=
.trans (e5587) (e5601)

private def e5603 : S 9 :=
.congAppFun (e5373) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e5604 : S 9 :=
.congAppFun (e5603) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e5605 : S 9 :=
.congAppFun (e5604) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e5606 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5605)

private def e5607 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5606)

private def e5608 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5607) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5609 : C 9 :=
.single (e5608)

private def e5611 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cf6d6b0b84e7af639c6b)

private def e5612 : C 9 :=
.trans (e5609) (e5611)

private def e5613 : C 9 :=
.trans (e5593) (e5612)

private def e5614 : C 9 :=
.trans (e5613) (e5611)

private def e5615 : S 9 :=
.congAppFun (e5389) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e5616 : S 9 :=
.congAppFun (e5615) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e5617 : S 9 :=
.congAppFun (e5616) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e5618 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5617)

private def e5619 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5618)

private def e5620 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5619) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5621 : C 9 :=
.single (e5620)

private def e5623 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2d0609e75ede930f501e)

private def e5624 : C 9 :=
.trans (e5621) (e5623)

private def e5625 : C 9 :=
.trans (e5614) (e5624)

private def e5626 : C 9 :=
.trans (e5625) (e5623)

private def e5627 : S 9 :=
.congAppFun (e5404) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e5628 : S 9 :=
.congAppFun (e5627) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e5629 : S 9 :=
.congAppFun (e5628) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e5630 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5629)

private def e5631 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5630)

private def e5632 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5631) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5633 : C 9 :=
.single (e5632)

private def e5635 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_367c39a53492663048dd)

private def e5636 : C 9 :=
.trans (e5633) (e5635)

private def e5637 : C 9 :=
.trans (e5626) (e5636)

private def e5638 : C 9 :=
.trans (e5637) (e5635)

private def e5639 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9c8cd2b96f5e50f40775) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_392da6367ef5b8ce2820)

private def e5640 : S 9 :=
.congAppFun (e5639) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e5641 : S 9 :=
.congAppFun (e5640) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e5642 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5641)

private def e5643 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5642)

private def e5644 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5643) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5645 : C 9 :=
.single (e5644)

private def e5647 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b3e23b4ded679ff613ef)

private def e5648 : C 9 :=
.trans (e5645) (e5647)

private def e5649 : C 9 :=
.trans (e5638) (e5648)

private def e5650 : C 9 :=
.trans (e5649) (e5647)

private def e5652 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6a7aebe9453ca836e683) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_6ec5fb851516271acc72)

private def e5653 : S 9 :=
.congAppFun (e5652) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e5654 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5653)

private def e5655 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5654)

private def e5656 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5655) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5657 : C 9 :=
.single (e5656)

private def e5659 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_23cdc2118e9a62136569)

private def e5660 : C 9 :=
.trans (e5659) (e5659)

private def e5661 : C 9 :=
.trans (e5660) (e5659)

private def e5662 : C 9 :=
.trans (e5661) (e5659)

private def e5663 : C 9 :=
.trans (e5662) (e5659)

private def e5664 : C 9 :=
.trans (e5663) (e5659)

private def e5665 : C 9 :=
.trans (e5664) (e5659)

private def e5666 : C 9 :=
.trans (e5657) (e5665)

private def e5667 : C 9 :=
.trans (e5650) (e5666)

private def e5668 : C 9 :=
.trans (e5667) (e5659)

private def e5670 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a8b08f1393c30352c10f)

private def e5671 : S 9 :=
.congSnd (e5376)

private def e5672 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5671)

private def e5673 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5672)

private def e5674 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5673) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5675 : C 9 :=
.single (e5674)

private def e5677 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3b773fca1790e3ce891a)

private def e5678 : C 9 :=
.trans (e5675) (e5677)

private def e5679 : C 9 :=
.trans (e5670) (e5678)

private def e5680 : C 9 :=
.trans (e5679) (e5677)

private def e5681 : S 9 :=
.congSnd (e5392)

private def e5682 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5681)

private def e5683 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5682)

private def e5684 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5683) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5685 : C 9 :=
.single (e5684)

private def e5687 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_01fdf482f6fed4b4e4ca)

private def e5688 : C 9 :=
.trans (e5685) (e5687)

private def e5689 : C 9 :=
.trans (e5680) (e5688)

private def e5690 : C 9 :=
.trans (e5689) (e5687)

private def e5691 : S 9 :=
.congSnd (e5407)

private def e5692 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5691)

private def e5693 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5692)

private def e5694 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5693) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5695 : C 9 :=
.single (e5694)

private def e5697 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fb609461875bb036ae66)

private def e5698 : C 9 :=
.trans (e5695) (e5697)

private def e5699 : C 9 :=
.trans (e5690) (e5698)

private def e5700 : C 9 :=
.trans (e5699) (e5697)

private def e5701 : S 9 :=
.congSnd (e5421)

private def e5702 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5701)

private def e5703 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5702)

private def e5704 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5703) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5705 : C 9 :=
.single (e5704)

private def e5707 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9d2d5d86cf10e26a43be)

private def e5708 : C 9 :=
.trans (e5705) (e5707)

private def e5709 : C 9 :=
.trans (e5700) (e5708)

private def e5710 : C 9 :=
.trans (e5709) (e5707)

private def e5711 : S 9 :=
.congSnd (e5434)

private def e5712 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5711)

private def e5713 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5712)

private def e5714 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5713) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5715 : C 9 :=
.single (e5714)

private def e5717 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1e03b98937769ef88a37)

private def e5718 : C 9 :=
.trans (e5717) (e5717)

private def e5719 : C 9 :=
.trans (e5718) (e5717)

private def e5720 : C 9 :=
.trans (e5719) (e5717)

private def e5721 : C 9 :=
.trans (e5720) (e5717)

private def e5722 : C 9 :=
.trans (e5721) (e5717)

private def e5723 : C 9 :=
.trans (e5722) (e5717)

private def e5724 : S 9 :=
.congSnd (e5450)

private def e5725 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5724)

private def e5726 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5725)

private def e5727 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5726) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5728 : C 9 :=
.single (e5727)

private def e5730 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_28d0e9a502ba7a2f0d6a)

private def e5731 : C 9 :=
.trans (e5730) (e5730)

private def e5732 : S 9 :=
.congSnd (e5461)

private def e5733 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5732)

private def e5734 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5733)

private def e5735 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5734) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5736 : C 9 :=
.single (e5735)

private def e5738 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fb0839260a41dfb180dc)

private def e5739 : C 9 :=
.trans (e5736) (e5738)

private def e5740 : C 9 :=
.trans (e5731) (e5739)

private def e5741 : C 9 :=
.trans (e5740) (e5738)

private def e5742 : S 9 :=
.congSnd (e5473)

private def e5743 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5742)

private def e5744 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5743)

private def e5745 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5744) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5746 : C 9 :=
.single (e5745)

private def e5748 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_08c9537f5ef92a03c157)

private def e5749 : C 9 :=
.trans (e5746) (e5748)

private def e5750 : C 9 :=
.trans (e5741) (e5749)

private def e5751 : C 9 :=
.trans (e5750) (e5748)

private def e5752 : S 9 :=
.congSnd (e5485)

private def e5753 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5752)

private def e5754 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5753)

private def e5755 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5754) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5756 : C 9 :=
.single (e5755)

private def e5758 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_fc4cb4332155f2926be2)

private def e5759 : C 9 :=
.trans (e5756) (e5758)

private def e5760 : C 9 :=
.trans (e5751) (e5759)

private def e5761 : C 9 :=
.trans (e5760) (e5758)

private def e5762 : S 9 :=
.congSnd (e5497)

private def e5763 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5762)

private def e5764 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5763)

private def e5765 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5764) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5766 : C 9 :=
.single (e5765)

private def e5768 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a05e9ff92957a9cea51c)

private def e5769 : C 9 :=
.trans (e5766) (e5768)

private def e5770 : C 9 :=
.trans (e5761) (e5769)

private def e5771 : C 9 :=
.trans (e5728) (e5770)

private def e5772 : C 9 :=
.trans (e5723) (e5771)

private def e5773 : C 9 :=
.trans (e5715) (e5772)

private def e5774 : C 9 :=
.trans (e5710) (e5773)

private def e5775 : C 9 :=
.trans (e5774) (e5768)

private def e5776 : S 9 :=
.congSnd (e5513)

private def e5777 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5776)

private def e5778 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5777)

private def e5779 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5778) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5780 : C 9 :=
.single (e5779)

private def e5782 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1b9cd622a2075d43f606)

private def e5783 : C 9 :=
.trans (e5780) (e5782)

private def e5784 : C 9 :=
.trans (e5775) (e5783)

private def e5785 : S 9 :=
.betaSigmaSnd (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a97388c54c77a8f2aaf2) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8f46704837e79054f88f)

private def e5786 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbe8d03f4033747fe0ff) (e5785)

private def e5787 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2cc992b0e32cdbbd28d5) (e5786)

private def e5788 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5787) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5789 : C 9 :=
.single (e5788)

private def e5790 : C 9 :=
.trans (e5665) (e5659)

private def e5791 : C 9 :=
.trans (e5789) (e5790)

private def e5792 : C 9 :=
.trans (e5784) (e5791)

private def e5793 : C 9 :=
.symm (e5792)

private def e5794 : C 9 :=
.trans (e5659) (e5793)

private def e5795 : C 9 :=
.trans (e5668) (e5794)

private def e5796 : C 9 :=
.trans (e5593) (e5795)

private def e5797 : C 9 :=
.trans (e5670) (e5670)

private def e5798 : C 9 :=
.trans (e5797) (e5670)

private def e5799 : C 9 :=
.trans (e5798) (e5670)

private def e5800 : C 9 :=
.trans (e5799) (e5670)

private def e5801 : C 9 :=
.trans (e5800) (e5670)

private def e5802 : C 9 :=
.trans (e5801) (e5670)

private def e5803 : C 9 :=
.trans (e5802) (e5670)

private def e5804 : C 9 :=
.symm (e5803)

private def e5805 : C 9 :=
.trans (e5796) (e5804)

private def e5806 : C 9 :=
.trans (e5602) (e5805)

private def e5807 : C 9 :=
.trans (e5540) (e5806)

private def e5809 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bba98d584dd704e80177)

private def e5811 : S 9 :=
.congAppFun (e3824) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d232ac145fbe3a5491b3)

private def e5812 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5811) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5813 : C 9 :=
.single (e5812)

private def e5815 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9c4fef90ad768ef0be00)

private def e5816 : C 9 :=
.trans (e5813) (e5815)

private def e5817 : C 9 :=
.trans (e5809) (e5816)

private def e5818 : C 9 :=
.trans (e5817) (e5815)

private def e5819 : S 9 :=
.congAppFun (e3834) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d232ac145fbe3a5491b3)

private def e5820 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5819) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5821 : C 9 :=
.single (e5820)

private def e5823 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_b33e11b880c51bb8fd52)

private def e5824 : C 9 :=
.trans (e5821) (e5823)

private def e5825 : C 9 :=
.trans (e5818) (e5824)

private def e5826 : C 9 :=
.trans (e5825) (e5823)

private def e5827 : S 9 :=
.congAppFun (e3844) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d232ac145fbe3a5491b3)

private def e5828 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5827) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5829 : C 9 :=
.single (e5828)

private def e5831 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9c9b05689f453d1fd731)

private def e5832 : C 9 :=
.trans (e5829) (e5831)

private def e5833 : C 9 :=
.trans (e5826) (e5832)

private def e5834 : C 9 :=
.trans (e5833) (e5831)

private def e5835 : S 9 :=
.congAppFun (e3854) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d232ac145fbe3a5491b3)

private def e5836 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5835) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5837 : C 9 :=
.single (e5836)

private def e5839 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9edc58007f9e9b8dc0c2)

private def e5840 : C 9 :=
.trans (e5837) (e5839)

private def e5841 : C 9 :=
.trans (e5834) (e5840)

private def e5842 : C 9 :=
.trans (e5841) (e5839)

private def e5843 : S 9 :=
.congAppFun (e3864) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d232ac145fbe3a5491b3)

private def e5844 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5843) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5845 : C 9 :=
.single (e5844)

private def e5847 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_208adb080506182b79e0)

private def e5848 : C 9 :=
.trans (e5845) (e5847)

private def e5849 : C 9 :=
.trans (e5842) (e5848)

private def e5850 : C 9 :=
.trans (e5849) (e5847)

private def e5851 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58dbe1e6fbe4d35289c4) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d232ac145fbe3a5491b3)

private def e5852 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5851) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5853 : C 9 :=
.single (e5852)

private def e5855 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_577c7bf1c8e0e9a3cea3)

private def e5856 : C 9 :=
.trans (e5855) (e5855)

private def e5857 : C 9 :=
.trans (e5856) (e5855)

private def e5858 : C 9 :=
.trans (e5857) (e5855)

private def e5859 : C 9 :=
.trans (e5858) (e5855)

private def e5860 : C 9 :=
.trans (e5859) (e5855)

private def e5861 : C 9 :=
.trans (e5860) (e5855)

private def e5862 : S 9 :=
.congAppFun (e3886) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d232ac145fbe3a5491b3)

private def e5863 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5862) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5864 : C 9 :=
.single (e5863)

private def e5866 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_cd55c68e6fa2ba390508)

private def e5867 : C 9 :=
.trans (e5866) (e5866)

private def e5868 : S 9 :=
.congAppFun (e3894) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d232ac145fbe3a5491b3)

private def e5869 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5868) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5870 : C 9 :=
.single (e5869)

private def e5872 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_dbbb0b49d9df19ac0e25)

private def e5873 : C 9 :=
.trans (e5870) (e5872)

private def e5874 : C 9 :=
.trans (e5867) (e5873)

private def e5875 : C 9 :=
.trans (e5874) (e5872)

private def e5876 : S 9 :=
.congAppFun (e3903) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d232ac145fbe3a5491b3)

private def e5877 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5876) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5878 : C 9 :=
.single (e5877)

private def e5880 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e15235f5dba40e8121b3)

private def e5881 : C 9 :=
.trans (e5878) (e5880)

private def e5882 : C 9 :=
.trans (e5875) (e5881)

private def e5883 : C 9 :=
.trans (e5882) (e5880)

private def e5884 : S 9 :=
.congAppFun (e3912) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d232ac145fbe3a5491b3)

private def e5885 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5884) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5886 : C 9 :=
.single (e5885)

private def e5888 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_4cf44244417b49bcffde)

private def e5889 : C 9 :=
.trans (e5886) (e5888)

private def e5890 : C 9 :=
.trans (e5883) (e5889)

private def e5891 : C 9 :=
.trans (e5890) (e5888)

private def e5892 : S 9 :=
.congAppFun (e3921) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d232ac145fbe3a5491b3)

private def e5893 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5892) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5894 : C 9 :=
.single (e5893)

private def e5896 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_de1ec7204564da5a8fe4)

private def e5897 : C 9 :=
.trans (e5894) (e5896)

private def e5898 : C 9 :=
.trans (e5891) (e5897)

private def e5899 : C 9 :=
.trans (e5864) (e5898)

private def e5900 : C 9 :=
.trans (e5861) (e5899)

private def e5901 : C 9 :=
.trans (e5900) (e5896)

private def e5902 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ec064c5a5afeadcfde2d) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_d232ac145fbe3a5491b3)

private def e5903 : S 9 :=
.congIdLeft (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (e5902) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a71fc09fd03210e94123)

private def e5904 : C 9 :=
.single (e5903)

private def e5905 : C 9 :=
.trans (e5904) (e5800)

private def e5906 : C 9 :=
.trans (e5901) (e5905)

private def e5907 : C 9 :=
.trans (e5853) (e5906)

private def e5908 : C 9 :=
.trans (e5850) (e5907)

private def e5909 : C 9 :=
.symm (e5908)

private def e5910 : C 9 :=
.trans (e5807) (e5909)

private def e5911 : C 9 :=
.trans (e5367) (e5910)

private def e5912 : C 9 :=
.trans (e5809) (e5809)

private def e5915 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_ff7f49280c21442dc691) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_acbd62657884c9a6f7ef)

private def e5916 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e5915)

private def e5917 : C 9 :=
.single (e5916)

private def e5919 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1246c7760865df30dfc5)

private def e5920 : C 9 :=
.trans (e5919) (e5919)

private def e5921 : C 9 :=
.trans (e5920) (e5919)

private def e5922 : C 9 :=
.trans (e5921) (e5919)

private def e5923 : C 9 :=
.trans (e5922) (e5919)

private def e5924 : C 9 :=
.trans (e5917) (e5923)

private def e5925 : C 9 :=
.trans (e5912) (e5924)

private def e5926 : S 9 :=
.congAppFun (e3305) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e5927 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eaee385f3d44f8c8710) (e5926)

private def e5928 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e5927)

private def e5929 : C 9 :=
.single (e5928)

private def e5931 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_58a0e553f02d23bb0db0)

private def e5932 : C 9 :=
.trans (e5929) (e5931)

private def e5933 : C 9 :=
.trans (e5919) (e5932)

private def e5934 : C 9 :=
.trans (e5933) (e5931)

private def e5935 : S 9 :=
.congAppFun (e3320) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e5936 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eaee385f3d44f8c8710) (e5935)

private def e5937 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e5936)

private def e5938 : C 9 :=
.single (e5937)

private def e5940 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_db8b6f0d9318517b52d7)

private def e5941 : C 9 :=
.trans (e5938) (e5940)

private def e5942 : C 9 :=
.trans (e5934) (e5941)

private def e5943 : C 9 :=
.trans (e5942) (e5940)

private def e5944 : S 9 :=
.congAppFun (e3333) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e5945 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eaee385f3d44f8c8710) (e5944)

private def e5946 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e5945)

private def e5947 : C 9 :=
.single (e5946)

private def e5949 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7c2962bc77651cbad310)

private def e5950 : C 9 :=
.trans (e5947) (e5949)

private def e5951 : C 9 :=
.trans (e5943) (e5950)

private def e5952 : C 9 :=
.trans (e5951) (e5949)

private def e5953 : S 9 :=
.congAppFun (e3345) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e5954 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eaee385f3d44f8c8710) (e5953)

private def e5955 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e5954)

private def e5956 : C 9 :=
.single (e5955)

private def e5958 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_003e1fbc6b6de7d429e0)

private def e5959 : C 9 :=
.trans (e5956) (e5958)

private def e5960 : C 9 :=
.trans (e5952) (e5959)

private def e5961 : C 9 :=
.trans (e5960) (e5958)

private def e5962 : S 9 :=
.congAppFun (e3356) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e5963 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eaee385f3d44f8c8710) (e5962)

private def e5964 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e5963)

private def e5965 : C 9 :=
.single (e5964)

private def e5967 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_78f6a243345804627058)

private def e5968 : C 9 :=
.trans (e5965) (e5967)

private def e5969 : C 9 :=
.trans (e5961) (e5968)

private def e5970 : C 9 :=
.trans (e5969) (e5967)

private def e5971 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7476078b94842f347d61) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3979198e3a749251a51e)

private def e5972 : S 9 :=
.congAppArg (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_1eaee385f3d44f8c8710) (e5971)

private def e5973 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e5972)

private def e5974 : C 9 :=
.single (e5973)

private def e5976 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f322f831ebc00804d5a2)

private def e5977 : C 9 :=
.trans (e5976) (e5976)

private def e5978 : C 9 :=
.trans (e5977) (e5976)

private def e5979 : C 9 :=
.trans (e5978) (e5976)

private def e5980 : C 9 :=
.trans (e5979) (e5976)

private def e5981 : C 9 :=
.trans (e5980) (e5976)

private def e5982 : C 9 :=
.trans (e5981) (e5976)

private def e5983 : C 9 :=
.trans (e5982) (e5976)

private def e5984 : C 9 :=
.trans (e5974) (e5983)

private def e5985 : C 9 :=
.trans (e5970) (e5984)

private def e5986 : C 9 :=
.symm (e5983)

private def e5987 : C 9 :=
.trans (e5976) (e5986)

private def e5988 : C 9 :=
.trans (e5985) (e5987)

private def e5989 : C 9 :=
.trans (e5919) (e5988)

private def e5991 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f700c4d444779e92c2cf)

private def e5992 : S 9 :=
.congAppFun (e3592) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e5993 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e5992)

private def e5994 : C 9 :=
.single (e5993)

private def e5996 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e62f47e60a393abd8fe0)

private def e5997 : C 9 :=
.trans (e5994) (e5996)

private def e5998 : C 9 :=
.trans (e5991) (e5997)

private def e5999 : C 9 :=
.trans (e5998) (e5996)

private def e6000 : S 9 :=
.congAppFun (e3603) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e6001 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e6000)

private def e6002 : C 9 :=
.single (e6001)

private def e6004 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_be7a8869fe803f475461)

private def e6005 : C 9 :=
.trans (e6002) (e6004)

private def e6006 : C 9 :=
.trans (e5999) (e6005)

private def e6007 : C 9 :=
.trans (e6006) (e6004)

private def e6008 : S 9 :=
.congAppFun (e3613) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e6009 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e6008)

private def e6010 : C 9 :=
.single (e6009)

private def e6012 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bbee40c1c00af7c422c9)

private def e6013 : C 9 :=
.trans (e6010) (e6012)

private def e6014 : C 9 :=
.trans (e6007) (e6013)

private def e6015 : C 9 :=
.trans (e6014) (e6012)

private def e6016 : S 9 :=
.congAppFun (e3623) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e6017 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e6016)

private def e6018 : C 9 :=
.single (e6017)

private def e6020 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9577e279019878fea8d8)

private def e6021 : C 9 :=
.trans (e6018) (e6020)

private def e6022 : C 9 :=
.trans (e6015) (e6021)

private def e6023 : C 9 :=
.trans (e6022) (e6020)

private def e6024 : S 9 :=
.congAppFun (e3633) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e6025 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e6024)

private def e6026 : C 9 :=
.single (e6025)

private def e6028 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_40f376353bc7c0a24147)

private def e6029 : C 9 :=
.trans (e6026) (e6028)

private def e6030 : C 9 :=
.trans (e6023) (e6029)

private def e6031 : C 9 :=
.trans (e6030) (e6028)

private def e6032 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_895d3c5c49bdc6689932) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e6033 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e6032)

private def e6034 : C 9 :=
.single (e6033)

private def e6036 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3524575f891ac05db046)

private def e6037 : C 9 :=
.trans (e6036) (e6036)

private def e6038 : C 9 :=
.trans (e6037) (e6036)

private def e6039 : C 9 :=
.trans (e6038) (e6036)

private def e6040 : C 9 :=
.trans (e6039) (e6036)

private def e6041 : C 9 :=
.trans (e6040) (e6036)

private def e6042 : C 9 :=
.trans (e6041) (e6036)

private def e6043 : S 9 :=
.congAppFun (e3655) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e6044 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e6043)

private def e6045 : C 9 :=
.single (e6044)

private def e6047 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_25222179c5628bb51720)

private def e6048 : C 9 :=
.trans (e6047) (e6047)

private def e6049 : S 9 :=
.congAppFun (e3666) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e6050 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e6049)

private def e6051 : C 9 :=
.single (e6050)

private def e6053 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c5b69c2231a12bf63d64)

private def e6054 : C 9 :=
.trans (e6051) (e6053)

private def e6055 : C 9 :=
.trans (e6048) (e6054)

private def e6056 : C 9 :=
.trans (e6055) (e6053)

private def e6057 : S 9 :=
.congAppFun (e3678) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e6058 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e6057)

private def e6059 : C 9 :=
.single (e6058)

private def e6061 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_78b2ca2c29f2e4da6171)

private def e6062 : C 9 :=
.trans (e6059) (e6061)

private def e6063 : C 9 :=
.trans (e6056) (e6062)

private def e6064 : C 9 :=
.trans (e6063) (e6061)

private def e6065 : S 9 :=
.congAppFun (e3689) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e6066 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e6065)

private def e6067 : C 9 :=
.single (e6066)

private def e6069 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_36f521c7fdf113ef59c4)

private def e6070 : C 9 :=
.trans (e6067) (e6069)

private def e6071 : C 9 :=
.trans (e6064) (e6070)

private def e6072 : C 9 :=
.trans (e6071) (e6069)

private def e6073 : S 9 :=
.congAppFun (e3699) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e6074 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e6073)

private def e6075 : C 9 :=
.single (e6074)

private def e6077 : C 9 :=
.refl (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_7347b9e9a771f951d887)

private def e6078 : C 9 :=
.trans (e6075) (e6077)

private def e6079 : C 9 :=
.trans (e6072) (e6078)

private def e6080 : C 9 :=
.trans (e6045) (e6079)

private def e6081 : C 9 :=
.trans (e6042) (e6080)

private def e6082 : C 9 :=
.trans (e6081) (e6077)

private def e6083 : S 9 :=
.betaPi (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_a68a2a8b7bb33d675319) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_46822c41966942c14476)

private def e6084 : S 9 :=
.congIdRight (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2fe352697cee79e049c1) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_2be3dd17d7f26442f298) (e6083)

private def e6085 : C 9 :=
.single (e6084)

private def e6086 : C 9 :=
.trans (e6085) (e5980)

private def e6087 : C 9 :=
.trans (e6082) (e6086)

private def e6088 : C 9 :=
.trans (e6034) (e6087)

private def e6089 : C 9 :=
.trans (e6031) (e6088)

private def e6090 : C 9 :=
.symm (e6089)

private def e6091 : C 9 :=
.trans (e5989) (e6090)

private def e6092 : C 9 :=
.trans (e5925) (e6091)

private def e6093 : C 9 :=
.trans (e5911) (e6092)

private def e6094 : C 9 :=
.trans (e5354) (e6093)

private def e6095 : C 9 :=
.symm (e5991)

private def e6096 : C 9 :=
.trans (e6094) (e6095)

private def e6097 : C 9 :=
.trans (e5354) (e6096)

private def e6098 : T 9 :=
.convert (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_40bd47d032ac48565488) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e5353) (e5167) (e6097)

private def e6099 : T 8 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3113b23543c4066f3ea8) (e5168) (e6098)

private def e6100 : T 7 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e739772b6969f56d5a19) (e5169) (e6099)

private def e6101 : T 6 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_512bcf58ddc7c9e66ce6) (e5170) (e6100)

private def e6102 : T 5 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_e39390df5491d175ad39) (e5171) (e6101)

private def e6103 : T 4 :=
.lamIntro (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_62ce3f6e3cb9391001b3) (e5172) (e6102)

private def e6106 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_02c898a5fa9dca7e390e) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_3bb382d71a95efa9d15f) (e4332) (replay_088a7fed4563d6a06e7a)

private def e6107 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_5331ca9ad2f18da19b3f) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_c37c1558480d4f5b13d8) (e6106) (replay_088a7fed4563d6a06e7a)

private def e6108 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bac685e13a2fd02b0bc2) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_45cc30860220f5c4ca80) (e6107) (replay_088a7fed4563d6a06e7a)

private def e6109 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_8337ad982447bb9b9de5) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f4571ec60826300f8ca3) (e3968) (e6108)

private def e6110 : T 5 :=
.appElim (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_bac685e13a2fd02b0bc2) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_f4571ec60826300f8ca3) (e3958) (replay_088a7fed4563d6a06e7a)

private def e6111 : T 5 :=
.idForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (replay_ab222404a1b298e073e0) (e6109) (e6110)

private def e6112 : T 4 :=
.piForm (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_182c33fe793f56022840) (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_9dcfb49953f0cbf1e6dd) (e610) (e6111)

private def e6113 : T 4 :=
.cumul (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax.syntax_897db4146fa986a8835c) (e6112)

def forwardMotiveSubmission : FormationSensitiveElaboration.Submission Tower.Head decoder.Code 4 :=
{ context := e26, term := e1046 }

def forwardNilSubmission : FormationSensitiveElaboration.Submission Tower.Head decoder.Code 4 :=
{ context := e26, term := e1398 }

def forwardConsSubmission : FormationSensitiveElaboration.Submission Tower.Head decoder.Code 4 :=
{ context := e26, term := e3953 }

def forwardFamilySubmission : FormationSensitiveElaboration.Submission Tower.Head decoder.Code 4 :=
{ context := e26, term := e3972 }

def backwardMotiveSubmission : FormationSensitiveElaboration.Submission Tower.Head decoder.Code 4 :=
{ context := e26, term := e4324 }

def backwardNilSubmission : FormationSensitiveElaboration.Submission Tower.Head decoder.Code 4 :=
{ context := e26, term := e4524 }

def backwardConsSubmission : FormationSensitiveElaboration.Submission Tower.Head decoder.Code 4 :=
{ context := e26, term := e6103 }

def backwardFamilySubmission : FormationSensitiveElaboration.Submission Tower.Head decoder.Code 4 :=
{ context := e26, term := e6113 }


end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.Assembly.Evidence
