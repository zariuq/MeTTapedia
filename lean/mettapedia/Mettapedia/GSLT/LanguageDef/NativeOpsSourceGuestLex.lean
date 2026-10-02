import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot
import Mettapedia.GSLT.Parsing.SourceAccumulatorLex
import Mettapedia.GSLT.Parsing.SExprTokenRoundTrip
import Batteries.Tactic.OpenPrivate

/-! Original quoted-lexer transitions over arbitrary preceding tokens. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestLex

open Mettapedia.GSLT.Parsing.SourceAccumulatorLex
open NativeOpsSourceGuestSnapshot
open private tokenizeWith parserDialectOf from Algorithms.MeTTa.Simple.Parser

def point_000 : Point := ⟨false, false, []⟩
def point_001 : Point := ⟨true, false, [Char.ofNat 49, Char.ofNat 118, Char.ofNat 95, Char.ofNat 101, Char.ofNat 100, Char.ofNat 111, Char.ofNat 99, Char.ofNat 95, Char.ofNat 101, Char.ofNat 118, Char.ofNat 105, Char.ofNat 116, Char.ofNat 97, Char.ofNat 110, Char.ofNat 34]⟩
def point_002 : Point := ⟨true, false, [Char.ofNat 116, Char.ofNat 101, Char.ofNat 99, Char.ofNat 34]⟩
def point_003 : Point := ⟨true, false, [Char.ofNat 105, Char.ofNat 116, Char.ofNat 97, Char.ofNat 110, Char.ofNat 95, Char.ofNat 116, Char.ofNat 108, Char.ofNat 115, Char.ofNat 103, Char.ofNat 95, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 99, Char.ofNat 34]⟩
def point_004 : Point := ⟨false, false, []⟩
def point_005 : Point := ⟨true, false, [Char.ofNat 110, Char.ofNat 95, Char.ofNat 116, Char.ofNat 108, Char.ofNat 115, Char.ofNat 103, Char.ofNat 95, Char.ofNat 97, Char.ofNat 116, Char.ofNat 116, Char.ofNat 101, Char.ofNat 99, Char.ofNat 34]⟩
def point_006 : Point := ⟨false, false, [Char.ofNat 111, Char.ofNat 99, Char.ofNat 83, Char.ofNat 110, Char.ofNat 111, Char.ofNat 105, Char.ofNat 116, Char.ofNat 117, Char.ofNat 99, Char.ofNat 101, Char.ofNat 120, Char.ofNat 69]⟩
def point_007 : Point := ⟨false, false, []⟩
def point_008 : Point := ⟨false, false, [Char.ofNat 98, Char.ofNat 111]⟩
def point_009 : Point := ⟨false, false, []⟩
def point_010 : Point := ⟨false, false, []⟩
def point_011 : Point := ⟨false, false, [Char.ofNat 97]⟩
def point_012 : Point := ⟨false, false, []⟩
def point_013 : Point := ⟨false, false, []⟩
def point_014 : Point := ⟨false, false, []⟩
def point_015 : Point := ⟨false, false, [Char.ofNat 108, Char.ofNat 101, Char.ofNat 105, Char.ofNat 102]⟩
def point_016 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 97, Char.ofNat 118]⟩
def point_017 : Point := ⟨false, false, []⟩
def point_018 : Point := ⟨false, false, []⟩
def point_019 : Point := ⟨false, false, [Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 105, Char.ofNat 102]⟩
def point_020 : Point := ⟨false, false, []⟩
def point_021 : Point := ⟨false, false, [Char.ofNat 121, Char.ofNat 116, Char.ofNat 105, Char.ofNat 114, Char.ofNat 97]⟩
def point_022 : Point := ⟨false, false, [Char.ofNat 99, Char.ofNat 111, Char.ofNat 108, Char.ofNat 98]⟩
def point_023 : Point := ⟨false, false, [Char.ofNat 110, Char.ofNat 101, Char.ofNat 100, Char.ofNat 105, Char.ofNat 45, Char.ofNat 116, Char.ofNat 120, Char.ofNat 101, Char.ofNat 110]⟩
def point_024 : Point := ⟨false, false, [Char.ofNat 49]⟩
def point_025 : Point := ⟨false, false, []⟩
def point_026 : Point := ⟨false, false, []⟩
def point_027 : Point := ⟨false, false, [Char.ofNat 108]⟩
def point_028 : Point := ⟨false, false, [Char.ofNat 115]⟩
def point_029 : Point := ⟨false, false, []⟩
def point_030 : Point := ⟨false, false, []⟩
def point_031 : Point := ⟨false, false, [Char.ofNat 97, Char.ofNat 100]⟩
def point_032 : Point := ⟨false, false, []⟩
def point_033 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 114]⟩
def point_034 : Point := ⟨false, false, []⟩
def point_035 : Point := ⟨false, false, []⟩
def point_036 : Point := ⟨false, false, []⟩
def point_037 : Point := ⟨false, false, []⟩
def point_038 : Point := ⟨false, false, [Char.ofNat 115, Char.ofNat 103, Char.ofNat 114, Char.ofNat 97]⟩
def point_039 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 114, Char.ofNat 45, Char.ofNat 109, Char.ofNat 114, Char.ofNat 101, Char.ofNat 116]⟩
def point_040 : Point := ⟨false, false, []⟩
def point_041 : Point := ⟨false, false, []⟩
def point_042 : Point := ⟨false, false, []⟩
def point_043 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 101, Char.ofNat 98, Char.ofNat 109, Char.ofNat 117, Char.ofNat 110]⟩
def point_044 : Point := ⟨false, false, []⟩
def point_045 : Point := ⟨false, false, []⟩
def point_046 : Point := ⟨false, false, []⟩
def point_047 : Point := ⟨false, false, [Char.ofNat 102, Char.ofNat 102, Char.ofNat 111, Char.ofNat 116, Char.ofNat 117, Char.ofNat 99]⟩
def point_048 : Point := ⟨false, false, [Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 105, Char.ofNat 102]⟩
def point_049 : Point := ⟨false, false, []⟩
def point_050 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 116]⟩
def point_051 : Point := ⟨false, false, [Char.ofNat 108, Char.ofNat 97, Char.ofNat 99]⟩
def point_052 : Point := ⟨false, false, [Char.ofNat 104, Char.ofNat 99]⟩
def point_053 : Point := ⟨false, false, []⟩
def point_054 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 116, Char.ofNat 45, Char.ofNat 101, Char.ofNat 101, Char.ofNat 114, Char.ofNat 102]⟩
def point_055 : Point := ⟨false, false, [Char.ofNat 111, Char.ofNat 108, Char.ofNat 98]⟩
def point_056 : Point := ⟨false, false, [Char.ofNat 97, Char.ofNat 108, Char.ofNat 101, Char.ofNat 114]⟩
def point_057 : Point := ⟨false, false, [Char.ofNat 97, Char.ofNat 99]⟩
def point_058 : Point := ⟨false, false, []⟩
def point_059 : Point := ⟨false, false, []⟩
def point_060 : Point := ⟨false, false, []⟩
def point_061 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 97, Char.ofNat 118]⟩
def point_062 : Point := ⟨false, false, []⟩
def point_063 : Point := ⟨false, false, []⟩
def point_064 : Point := ⟨false, false, [Char.ofNat 111, Char.ofNat 108, Char.ofNat 98]⟩
def point_065 : Point := ⟨false, false, []⟩
def point_066 : Point := ⟨false, false, []⟩
def point_067 : Point := ⟨false, false, [Char.ofNat 111, Char.ofNat 98]⟩
def point_068 : Point := ⟨false, false, []⟩
def point_069 : Point := ⟨false, false, []⟩
def point_070 : Point := ⟨false, false, [Char.ofNat 100, Char.ofNat 108, Char.ofNat 105, Char.ofNat 104, Char.ofNat 99]⟩
def point_071 : Point := ⟨false, false, []⟩
def point_072 : Point := ⟨false, false, [Char.ofNat 99, Char.ofNat 111, Char.ofNat 108, Char.ofNat 98]⟩
def point_073 : Point := ⟨false, false, []⟩
def point_074 : Point := ⟨false, false, []⟩
def point_075 : Point := ⟨false, false, [Char.ofNat 45, Char.ofNat 110, Char.ofNat 105, Char.ofNat 116, Char.ofNat 108, Char.ofNat 105, Char.ofNat 117, Char.ofNat 98]⟩
def point_076 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 117, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]⟩
def point_077 : Point := ⟨false, false, [Char.ofNat 110, Char.ofNat 114, Char.ofNat 117, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]⟩
def point_078 : Point := ⟨false, false, [Char.ofNat 116, Char.ofNat 110, Char.ofNat 101, Char.ofNat 100, Char.ofNat 105, Char.ofNat 45, Char.ofNat 116, Char.ofNat 120, Char.ofNat 101, Char.ofNat 110]⟩
def point_079 : Point := ⟨false, false, []⟩
def point_080 : Point := ⟨false, false, []⟩
def point_081 : Point := ⟨false, false, []⟩
def point_082 : Point := ⟨false, false, []⟩
def point_083 : Point := ⟨false, false, []⟩
def point_084 : Point := ⟨false, false, [Char.ofNat 102]⟩
def point_085 : Point := ⟨false, false, []⟩
def point_086 : Point := ⟨false, false, []⟩
def point_087 : Point := ⟨false, false, []⟩
def point_088 : Point := ⟨false, false, []⟩
def point_089 : Point := ⟨false, false, []⟩
def point_090 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 111, Char.ofNat 101, Char.ofNat 104, Char.ofNat 84]⟩
def point_091 : Point := ⟨false, false, []⟩
def point_092 : Point := ⟨false, false, []⟩
def point_093 : Point := ⟨false, false, [Char.ofNat 111, Char.ofNat 108, Char.ofNat 98]⟩
def point_094 : Point := ⟨false, false, []⟩
def point_095 : Point := ⟨false, false, []⟩
def point_096 : Point := ⟨false, false, []⟩
def point_097 : Point := ⟨false, false, []⟩
def point_098 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 114]⟩
def point_099 : Point := ⟨false, false, []⟩
def point_100 : Point := ⟨false, false, []⟩
def point_101 : Point := ⟨false, false, []⟩
def point_102 : Point := ⟨false, false, [Char.ofNat 102]⟩
def point_103 : Point := ⟨false, false, []⟩
def point_104 : Point := ⟨false, false, []⟩
def point_105 : Point := ⟨false, false, [Char.ofNat 104, Char.ofNat 116]⟩
def point_106 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 97, Char.ofNat 118]⟩
def point_107 : Point := ⟨false, false, [Char.ofNat 105, Char.ofNat 108]⟩
def point_108 : Point := ⟨false, false, []⟩
def point_109 : Point := ⟨false, false, [Char.ofNat 98, Char.ofNat 109, Char.ofNat 121, Char.ofNat 115]⟩
def point_110 : Point := ⟨false, false, []⟩
def point_111 : Point := ⟨false, false, []⟩
def point_112 : Point := ⟨false, false, []⟩
def point_113 : Point := ⟨false, false, []⟩
def point_114 : Point := ⟨false, false, []⟩
def point_115 : Point := ⟨false, false, []⟩
def point_116 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 108]⟩
def point_117 : Point := ⟨false, false, [Char.ofNat 114]⟩
def point_118 : Point := ⟨false, false, [Char.ofNat 108, Char.ofNat 105, Char.ofNat 104, Char.ofNat 119]⟩
def point_119 : Point := ⟨false, false, []⟩
def point_120 : Point := ⟨false, false, []⟩
def point_121 : Point := ⟨false, false, [Char.ofNat 116, Char.ofNat 101, Char.ofNat 114]⟩
def point_122 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 97, Char.ofNat 118, Char.ofNat 102]⟩
def point_123 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 101, Char.ofNat 84]⟩
def point_124 : Point := ⟨false, false, [Char.ofNat 103, Char.ofNat 114, Char.ofNat 97, Char.ofNat 45, Char.ofNat 115, Char.ofNat 104, Char.ofNat 108]⟩
def point_125 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 101, Char.ofNat 84]⟩
def point_126 : Point := ⟨false, false, []⟩
def point_127 : Point := ⟨false, false, [Char.ofNat 111, Char.ofNat 105, Char.ofNat 116, Char.ofNat 105, Char.ofNat 110, Char.ofNat 105, Char.ofNat 102, Char.ofNat 101, Char.ofNat 68]⟩
def point_128 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 105, Char.ofNat 102]⟩
def point_129 : Point := ⟨false, false, [Char.ofNat 108, Char.ofNat 98]⟩
def point_130 : Point := ⟨false, false, []⟩
def point_131 : Point := ⟨false, false, [Char.ofNat 111, Char.ofNat 108, Char.ofNat 98]⟩
def point_132 : Point := ⟨false, false, []⟩
def point_133 : Point := ⟨false, false, [Char.ofNat 116, Char.ofNat 115]⟩
def point_134 : Point := ⟨false, false, []⟩
def point_135 : Point := ⟨false, false, []⟩
def point_136 : Point := ⟨false, false, [Char.ofNat 105, Char.ofNat 106]⟩
def point_137 : Point := ⟨false, false, []⟩
def point_138 : Point := ⟨false, false, []⟩
def point_139 : Point := ⟨false, false, []⟩
def point_140 : Point := ⟨false, false, []⟩
def point_141 : Point := ⟨false, false, [Char.ofNat 118]⟩
def point_142 : Point := ⟨false, false, [Char.ofNat 116, Char.ofNat 101, Char.ofNat 115]⟩
def point_143 : Point := ⟨false, false, []⟩
def point_144 : Point := ⟨false, false, [Char.ofNat 107, Char.ofNat 99, Char.ofNat 111, Char.ofNat 108, Char.ofNat 98]⟩
def point_145 : Point := ⟨false, false, []⟩
def point_146 : Point := ⟨false, false, [Char.ofNat 104, Char.ofNat 116, Char.ofNat 103, Char.ofNat 110, Char.ofNat 101, Char.ofNat 108]⟩
def point_147 : Point := ⟨false, false, [Char.ofNat 97, Char.ofNat 118, Char.ofNat 114, Char.ofNat 101, Char.ofNat 115, Char.ofNat 98, Char.ofNat 111]⟩
def point_148 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 97]⟩
def point_149 : Point := ⟨false, false, []⟩
def point_150 : Point := ⟨false, false, [Char.ofNat 84]⟩
def point_151 : Point := ⟨false, false, [Char.ofNat 108, Char.ofNat 101, Char.ofNat 105, Char.ofNat 102]⟩
def point_152 : Point := ⟨false, false, []⟩
def point_153 : Point := ⟨false, false, [Char.ofNat 105]⟩
def point_154 : Point := ⟨false, false, []⟩
def point_155 : Point := ⟨false, false, [Char.ofNat 102]⟩
def point_156 : Point := ⟨false, false, []⟩
def point_157 : Point := ⟨false, false, []⟩
def point_158 : Point := ⟨false, false, []⟩
def point_159 : Point := ⟨false, false, []⟩
def point_160 : Point := ⟨false, false, [Char.ofNat 114]⟩
def point_161 : Point := ⟨false, false, []⟩
def point_162 : Point := ⟨false, false, [Char.ofNat 48]⟩
def point_163 : Point := ⟨false, false, [Char.ofNat 52, Char.ofNat 54, Char.ofNat 117]⟩
def point_164 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 111, Char.ofNat 99, Char.ofNat 101, Char.ofNat 114]⟩
def point_165 : Point := ⟨false, false, []⟩
def point_166 : Point := ⟨false, false, [Char.ofNat 108, Char.ofNat 98]⟩
def point_167 : Point := ⟨false, false, [Char.ofNat 115, Char.ofNat 97, Char.ofNat 101, Char.ofNat 109]⟩
def point_168 : Point := ⟨false, false, []⟩
def point_169 : Point := ⟨false, false, [Char.ofNat 99]⟩
def point_170 : Point := ⟨false, false, [Char.ofNat 117]⟩
def point_171 : Point := ⟨false, false, [Char.ofNat 108, Char.ofNat 97, Char.ofNat 99]⟩
def point_172 : Point := ⟨false, false, []⟩
def point_173 : Point := ⟨false, false, []⟩
def point_174 : Point := ⟨false, false, [Char.ofNat 99]⟩
def point_175 : Point := ⟨false, false, [Char.ofNat 117]⟩
def point_176 : Point := ⟨false, false, []⟩
def point_177 : Point := ⟨false, false, [Char.ofNat 117]⟩
def point_178 : Point := ⟨false, false, []⟩
def point_179 : Point := ⟨false, false, [Char.ofNat 99, Char.ofNat 101, Char.ofNat 114]⟩
def point_180 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 97, Char.ofNat 118]⟩
def point_181 : Point := ⟨false, false, []⟩
def point_182 : Point := ⟨false, false, []⟩
def point_183 : Point := ⟨false, false, [Char.ofNat 101]⟩
def point_184 : Point := ⟨false, false, [Char.ofNat 111, Char.ofNat 99, Char.ofNat 111, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 80]⟩
def point_185 : Point := ⟨false, false, [Char.ofNat 110]⟩
def point_186 : Point := ⟨false, false, [Char.ofNat 112, Char.ofNat 97, Char.ofNat 99]⟩
def point_187 : Point := ⟨false, false, []⟩
def point_188 : Point := ⟨false, false, []⟩
def point_189 : Point := ⟨false, false, [Char.ofNat 119]⟩
def point_190 : Point := ⟨false, false, []⟩
def point_191 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 114]⟩
def point_192 : Point := ⟨false, false, [Char.ofNat 54, Char.ofNat 117]⟩
def point_193 : Point := ⟨false, false, []⟩
def point_194 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 80]⟩
def point_195 : Point := ⟨false, false, []⟩
def point_196 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 97, Char.ofNat 118]⟩
def point_197 : Point := ⟨false, false, []⟩
def point_198 : Point := ⟨false, false, []⟩
def point_199 : Point := ⟨false, false, [Char.ofNat 102, Char.ofNat 101, Char.ofNat 114]⟩
def point_200 : Point := ⟨false, false, []⟩
def point_201 : Point := ⟨false, false, [Char.ofNat 117]⟩
def point_202 : Point := ⟨false, false, [Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 105, Char.ofNat 102]⟩
def point_203 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 116]⟩
def point_204 : Point := ⟨false, false, []⟩
def point_205 : Point := ⟨false, false, []⟩
def point_206 : Point := ⟨false, false, [Char.ofNat 52, Char.ofNat 54, Char.ofNat 117]⟩
def point_207 : Point := ⟨false, false, [Char.ofNat 102]⟩
def point_208 : Point := ⟨false, false, []⟩
def point_209 : Point := ⟨false, false, [Char.ofNat 80]⟩
def point_210 : Point := ⟨false, false, [Char.ofNat 105]⟩
def point_211 : Point := ⟨false, false, [Char.ofNat 108, Char.ofNat 98]⟩
def point_212 : Point := ⟨false, false, []⟩
def point_213 : Point := ⟨false, false, []⟩
def point_214 : Point := ⟨false, false, [Char.ofNat 97, Char.ofNat 118]⟩
def point_215 : Point := ⟨false, false, []⟩
def point_216 : Point := ⟨false, false, []⟩
def point_217 : Point := ⟨false, false, []⟩
def point_218 : Point := ⟨false, false, []⟩
def point_219 : Point := ⟨false, false, [Char.ofNat 108]⟩
def point_220 : Point := ⟨false, false, [Char.ofNat 100, Char.ofNat 114, Char.ofNat 111, Char.ofNat 119, Char.ofNat 45, Char.ofNat 100, Char.ofNat 114, Char.ofNat 111, Char.ofNat 99, Char.ofNat 101, Char.ofNat 114]⟩
def point_221 : Point := ⟨false, false, [Char.ofNat 115, Char.ofNat 114, Char.ofNat 101, Char.ofNat 100, Char.ofNat 110, Char.ofNat 105, Char.ofNat 98]⟩
def point_222 : Point := ⟨false, false, [Char.ofNat 118]⟩
def point_223 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 115, Char.ofNat 108, Char.ofNat 97, Char.ofNat 102]⟩
def point_224 : Point := ⟨false, false, []⟩
def point_225 : Point := ⟨false, false, []⟩
def point_226 : Point := ⟨false, false, []⟩
def point_227 : Point := ⟨false, false, [Char.ofNat 114]⟩
def point_228 : Point := ⟨false, false, []⟩
def point_229 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 108]⟩
def point_230 : Point := ⟨false, false, [Char.ofNat 52, Char.ofNat 54, Char.ofNat 117]⟩
def point_231 : Point := ⟨false, false, [Char.ofNat 97, Char.ofNat 118]⟩
def point_232 : Point := ⟨false, false, [Char.ofNat 99, Char.ofNat 111, Char.ofNat 108, Char.ofNat 98]⟩
def point_233 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 115, Char.ofNat 108, Char.ofNat 97, Char.ofNat 102]⟩
def point_234 : Point := ⟨false, false, []⟩
def point_235 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 114]⟩
def point_236 : Point := ⟨false, false, [Char.ofNat 100, Char.ofNat 108, Char.ofNat 101, Char.ofNat 105, Char.ofNat 102]⟩
def point_237 : Point := ⟨false, false, []⟩
def point_238 : Point := ⟨false, false, []⟩
def point_239 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 111, Char.ofNat 99, Char.ofNat 101, Char.ofNat 114]⟩
def point_240 : Point := ⟨false, false, [Char.ofNat 115]⟩
def point_241 : Point := ⟨false, false, [Char.ofNat 108, Char.ofNat 97, Char.ofNat 99]⟩
def point_242 : Point := ⟨false, false, [Char.ofNat 110, Char.ofNat 111, Char.ofNat 105, Char.ofNat 116, Char.ofNat 97, Char.ofNat 110, Char.ofNat 105, Char.ofNat 116, Char.ofNat 115, Char.ofNat 101, Char.ofNat 100]⟩
def point_243 : Point := ⟨false, false, []⟩
def point_244 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 105, Char.ofNat 102]⟩
def point_245 : Point := ⟨false, false, [Char.ofNat 97, Char.ofNat 118]⟩
def point_246 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 108, Char.ofNat 108, Char.ofNat 97, Char.ofNat 104, Char.ofNat 99]⟩
def point_247 : Point := ⟨false, false, [Char.ofNat 102]⟩
def point_248 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 104, Char.ofNat 116, Char.ofNat 45, Char.ofNat 116, Char.ofNat 101, Char.ofNat 103]⟩
def point_249 : Point := ⟨false, false, []⟩
def point_250 : Point := ⟨false, false, [Char.ofNat 103]⟩
def point_251 : Point := ⟨false, false, [Char.ofNat 110, Char.ofNat 97, Char.ofNat 116, Char.ofNat 115, Char.ofNat 110, Char.ofNat 105]⟩
def point_252 : Point := ⟨false, false, [Char.ofNat 100, Char.ofNat 114, Char.ofNat 111, Char.ofNat 119, Char.ofNat 45, Char.ofNat 108, Char.ofNat 111, Char.ofNat 99, Char.ofNat 111, Char.ofNat 116, Char.ofNat 111, Char.ofNat 114, Char.ofNat 112]⟩
def point_253 : Point := ⟨false, false, [Char.ofNat 102, Char.ofNat 101]⟩
def point_254 : Point := ⟨false, false, [Char.ofNat 108, Char.ofNat 108, Char.ofNat 97, Char.ofNat 99]⟩
def point_255 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 102, Char.ofNat 102, Char.ofNat 101]⟩
def point_256 : Point := ⟨false, false, [Char.ofNat 118]⟩
def point_257 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 111, Char.ofNat 99, Char.ofNat 101, Char.ofNat 114]⟩
def point_258 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 104, Char.ofNat 116, Char.ofNat 45, Char.ofNat 116, Char.ofNat 117, Char.ofNat 112]⟩
def point_259 : Point := ⟨false, false, [Char.ofNat 105]⟩
def point_260 : Point := ⟨false, false, [Char.ofNat 100, Char.ofNat 114, Char.ofNat 111, Char.ofNat 99, Char.ofNat 101, Char.ofNat 114]⟩
def point_261 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 102, Char.ofNat 102, Char.ofNat 101]⟩
def point_262 : Point := ⟨false, false, [Char.ofNat 108, Char.ofNat 98]⟩
def point_263 : Point := ⟨false, false, [Char.ofNat 109, Char.ofNat 101, Char.ofNat 114, Char.ofNat 111, Char.ofNat 101, Char.ofNat 104, Char.ofNat 116, Char.ofNat 45, Char.ofNat 116, Char.ofNat 117, Char.ofNat 112]⟩
def point_264 : Point := ⟨false, false, []⟩
def point_265 : Point := ⟨false, false, [Char.ofNat 116]⟩
def point_266 : Point := ⟨false, false, [Char.ofNat 101, Char.ofNat 114]⟩
def point_267 : Point := ⟨false, false, [Char.ofNat 111]⟩
def point_268 : Point := ⟨false, false, [Char.ofNat 45, Char.ofNat 100, Char.ofNat 114, Char.ofNat 111, Char.ofNat 99, Char.ofNat 101, Char.ofNat 114]⟩
def point_269 : Point := ⟨false, false, [Char.ofNat 48]⟩
def point_270 : Point := ⟨false, false, [Char.ofNat 97, Char.ofNat 118]⟩
def point_271 : Point := ⟨false, false, [Char.ofNat 97, Char.ofNat 118]⟩
def point_272 : Point := ⟨false, false, []⟩
def point_273 : Point := ⟨false, false, []⟩
def point_274 : Point := ⟨false, false, []⟩
def point_275 : Point := ⟨false, false, [Char.ofNat 65]⟩
def point_276 : Point := ⟨false, false, []⟩
def point_277 : Point := ⟨false, false, []⟩
def point_278 : Point := ⟨false, false, [Char.ofNat 114, Char.ofNat 112]⟩
def point_279 : Point := ⟨false, false, []⟩
def point_280 : Point := ⟨false, false, [Char.ofNat 115]⟩
def point_281 : Point := ⟨false, false, []⟩
def emitted_000 : List String := ["(", "gslt-native-ops-v1", "VibeITPKernel", "(", "opaque", "BinaryRecord", "\"CettaGsltNativeRecordV1\"", "\"gslt_native_io_v1.h\"", ")", "(", "opaque", "ExecutionScope", "\"CettaGsltNativeExecutionScopeV1\"", "\"gslt_native_io_v1.h\"", ")", "(", "opaque", "Observation", "\"CettaNativeCodeObservationV1\""]
theorem step_000 : Agreement point_000 point_001
    componentChars_000 emitted_000 := by
  intro rest priorTokens
  cbv

def emitted_001 : List String := ["\"native_code_v1.h\"", ")", "(", "extern", "record-opcode", "\"cetta_gslt_native_record_opcode_v1\"", "(", "(", "record", "(", "ref", "BinaryRecord", ")", ")", ")", "u64", "effect", ")", "(", "extern", "record-word", "\"cetta_gslt_native_record_word_v1\"", "(", "(", "record", "(", "ref", "BinaryRecord", ")", ")", "(", "operand", "u64", ")", ")", "u64", "effect", ")", "(", "extern", "record-count"]
theorem step_001 : Agreement point_001 point_002
    componentChars_001 emitted_001 := by
  intro rest priorTokens
  cbv

def emitted_002 : List String := ["\"cetta_gslt_native_record_count_v1\"", "(", "(", "record", "(", "ref", "BinaryRecord", ")", ")", "(", "operand", "u64", ")", ")", "u64", "effect", ")", "(", "extern", "record-bytes", "\"cetta_gslt_native_record_bytes_v1\"", "(", "(", "record", "(", "ref", "BinaryRecord", ")", ")", "(", "operand", "u64", ")", ")", "bytes", "effect", ")", "(", "extern", "record-next-word"]
theorem step_002 : Agreement point_002 point_003
    componentChars_002 emitted_002 := by
  intro rest priorTokens
  cbv

def emitted_003 : List String := ["\"cetta_gslt_native_record_word_next_v1\"", "(", "(", "record", "(", "ref", "BinaryRecord", ")", ")", "(", "operand", "u64", ")", "(", "position", "(", "ref", "u64", ")", ")", "(", "word", "(", "ref", "u64", ")", ")", ")", "bool", "effect", ")", "(", "extern", "execute-native", "\"cetta_gslt_native_execute_v1\"", "(", "(", "scope", "(", "ref", "ExecutionScope", ")", ")", "(", "code", "bytes", ")", "(", "input1", "bytes", ")", "(", "input2", "bytes", ")"]
theorem step_003 : Agreement point_003 point_004
    componentChars_003 emitted_003 := by
  intro rest priorTokens
  cbv

def emitted_004 : List String := ["(", "length", "u64", ")", "(", "observation", "(", "ref", "(", "ref", "Observation", ")", ")", ")", ")", "u64", "effect", ")", "(", "extern", "execution-output", "\"cetta_gslt_native_execution_output_v1\"", "(", "(", "scope", "(", "ref", "ExecutionScope", ")", ")", "(", "observation", "(", "ref", "Observation", ")", ")", ")", "bytes", "pure", ")", "(", "extern", "execution-matches"]
theorem step_004 : Agreement point_004 point_005
    componentChars_004 emitted_004 := by
  intro rest priorTokens
  cbv

def emitted_005 : List String := ["\"cetta_gslt_native_execution_matches_v1\"", "(", "(", "scope", "(", "ref", "ExecutionScope", ")", ")", "(", "observation", "(", "ref", "Observation", ")", ")", "(", "code", "bytes", ")", "(", "input1", "bytes", ")", "(", "input2", "bytes", ")", "(", "output", "bytes", ")", ")", "bool", "pure", ")", "(", "extern", "execution-free", "\"cetta_gslt_native_execution_free_v1\"", "(", "(", "scope", "(", "ref"]
theorem step_005 : Agreement point_005 point_006
    componentChars_005 emitted_005 := by
  intro rest priorTokens
  cbv

def emitted_006 : List String := ["ExecutionScope", ")", ")", "(", "observation", "(", "ref", "Observation", ")", ")", ")", "unit", "effect", ")", "(", "record", "Symbol", "(", "(", "kind", "u64", ")", "(", "arity", "u64", ")", "(", "binders", "(", "array", "u64", ")", ")", "(", "identity", "(", "array", "u64", ")", ")", "(", "rc", "u64", ")", "(", "immortal", "bool", ")", ")", ")", "(", "record", "Term", "(", "(", "symbol", "(", "ref", "Symbol", ")", ")", "(", "number", "u64", ")", "(", "literal", "bytes", ")"]
theorem step_006 : Agreement point_006 point_007
    componentChars_006 emitted_006 := by
  intro rest priorTokens
  cbv

def emitted_007 : List String := ["(", "args", "(", "array", "(", "ref", "Term", ")", ")", ")", "(", "depth", "u64", ")", "(", "has-fvar", "bool", ")", "(", "rc", "u64", ")", ")", ")", "(", "record", "Theorem", "(", "(", "statement", "(", "ref", "Term", ")", ")", "(", "owner", "(", "ref", "Theory", ")", ")", "(", "origin", "u64", ")", "(", "revision", "(", "array", "u64", ")", ")", "(", "identity", "(", "array", "u64", ")", ")", "("]
theorem step_007 : Agreement point_007 point_008
    componentChars_007 emitted_007 := by
  intro rest priorTokens
  cbv

def emitted_008 : List String := ["observation", "(", "ref", "Observation", ")", ")", "(", "execution-scope", "(", "ref", "ExecutionScope", ")", ")", "(", "execution-premise", "(", "ref", "Term", ")", ")", ")", ")", "(", "record", "Definition", "(", "(", "symbol", "(", "ref", "Symbol", ")", ")", "(", "theorem", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "record", "HintCursor", "(", "(", "position", "u64", ")", ")", ")", "(", "record", "Theory", "(", "(", "next-identity", "(", "array", "u64", ")", ")"]
theorem step_008 : Agreement point_008 point_009
    componentChars_008 emitted_008 := by
  intro rest priorTokens
  cbv

def emitted_009 : List String := ["(", "builtins", "(", "array", "(", "ref", "Symbol", ")", ")", ")", "(", "revision", "(", "array", "u64", ")", ")", "(", "admissions", "(", "ref", "Admission", ")", ")", ")", ")", "(", "record", "Admission", "(", "(", "kind", "u64", ")", "(", "statement", "(", "ref", "Term", ")", ")", "(", "symbol", "(", "ref", "Symbol", ")", ")", "(", "fvars", "(", "array", "(", "ref", "Symbol", ")", ")", ")", "(", "hints", "(", "array", "u64", ")", ")"]
theorem step_009 : Agreement point_009 point_010
    componentChars_009 emitted_009 := by
  intro rest priorTokens
  cbv

def emitted_010 : List String := ["(", "revision", "(", "array", "u64", ")", ")", "(", "previous", "(", "ref", "Admission", ")", ")", ")", ")", "(", "record", "Measure", "(", "(", "capacities", "(", "array", "u64", ")", ")", "(", "words", "u64", ")", "(", "terms", "u64", ")", "(", "symbols", "u64", ")", "(", "error", "u64", ")", ")", ")", "(", "record", "Protocol", "(", "(", "execution-scope", "(", "ref", "ExecutionScope", ")", ")", "(", "theory", "(", "ref", "Theory", ")", ")", "(", "symbols", "("]
theorem step_010 : Agreement point_010 point_011
    componentChars_010 emitted_010 := by
  intro rest priorTokens
  cbv

def emitted_011 : List String := ["array", "(", "ref", "Symbol", ")", ")", ")", "(", "terms", "(", "array", "(", "ref", "Term", ")", ")", ")", "(", "theorems", "(", "array", "(", "ref", "Theorem", ")", ")", ")", "(", "challenges", "(", "array", "(", "ref", "Term", ")", ")", ")", "(", "proof", "bool", ")", "(", "error", "u64", ")", "(", "physical-error", "u64", ")", "(", "initial", "u64", ")", "(", "satisfied", "u64", ")"]
theorem step_011 : Agreement point_011 point_012
    componentChars_011 emitted_011 := by
  intro rest priorTokens
  cbv

def emitted_012 : List String := ["(", "aux-words", "(", "array", "u64", ")", ")", "(", "aux-terms", "(", "array", "(", "ref", "Term", ")", ")", ")", "(", "aux-symbols", "(", "array", "(", "ref", "Symbol", ")", ")", ")", ")", ")", "(", "function", "symbol-retain", "(", "(", "s", "(", "ref", "Symbol", ")", ")", ")", "(", "ref", "Symbol", ")", "(", "block", "(", "if", "(", "and", "(", "ne", "(", "var", "s", ")", "(", "null", "(", "ref", "Symbol", ")", ")", ")"]
theorem step_012 : Agreement point_012 point_013
    componentChars_012 emitted_012 := by
  intro rest priorTokens
  cbv

def emitted_013 : List String := ["(", "not", "(", "field", "(", "var", "s", ")", "immortal", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "rc", ")", "(", "add", "(", "field", "(", "var", "s", ")", "rc", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "block", ")", ")", "(", "return", "(", "var", "s", ")", ")", ")", ")", "(", "function", "symbol-free", "(", "(", "s", "(", "ref", "Symbol", ")", ")", ")", "unit", "(", "block", "(", "if", "(", "or", "(", "eq", "(", "var", "s", ")", "(", "null", "(", "ref", "Symbol", ")", ")", ")"]
theorem step_013 : Agreement point_013 point_014
    componentChars_013 emitted_013 := by
  intro rest priorTokens
  cbv

def emitted_014 : List String := ["(", "field", "(", "var", "s", ")", "immortal", ")", ")", "(", "block", "(", "return", ")", ")", "(", "block", ")", ")", "(", "if", "(", "gt", "(", "field", "(", "var", "s", ")", "rc", ")", "(", "u64", "1", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "rc", ")", "(", "sub", "(", "field", "(", "var", "s", ")", "rc", ")", "(", "u64", "1", ")", ")", ")", "(", "return", ")", ")", "(", "block", ")", ")", "(", "free", "(", "field", "(", "var", "s", ")", "binders", ")", ")", "(", "free", "("]
theorem step_014 : Agreement point_014 point_015
    componentChars_014 emitted_014 := by
  intro rest priorTokens
  cbv

def emitted_015 : List String := ["field", "(", "var", "s", ")", "identity", ")", ")", "(", "free", "(", "var", "s", ")", ")", "(", "return", ")", ")", ")", "(", "function", "copy-words", "(", "(", "words", "(", "array", "u64", ")", ")", ")", "(", "array", "u64", ")", "(", "block", "(", "let", "out", "(", "array", "u64", ")", "(", "new-array", "u64", "(", "length", "(", "var", "words", ")", ")", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "("]
theorem step_015 : Agreement point_015 point_016
    componentChars_015 emitted_015 := by
  intro rest priorTokens
  cbv

def emitted_016 : List String := ["var", "words", ")", ")", ")", "(", "block", "(", "set", "(", "index", "(", "var", "out", ")", "(", "var", "i", ")", ")", "(", "index", "(", "var", "words", ")", "(", "var", "i", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "return", "(", "var", "out", ")", ")", ")", ")", "(", "function", "advance-identity", "(", "(", "thy", "(", "ref", "Theory", ")", ")", ")", "unit", "(", "block", "(", "let", "words", "(", "array"]
theorem step_016 : Agreement point_016 point_017
    componentChars_016 emitted_016 := by
  intro rest priorTokens
  cbv

def emitted_017 : List String := ["u64", ")", "(", "field", "(", "var", "thy", ")", "next-identity", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "var", "words", ")", ")", ")", "(", "block", "(", "set", "(", "index", "(", "var", "words", ")", "(", "var", "i", ")", ")", "(", "add", "(", "index", "(", "var", "words", ")", "(", "var", "i", ")", ")", "(", "u64", "1", ")", ")", ")", "(", "if", "(", "ne", "(", "index", "(", "var", "words", ")", "(", "var", "i", ")"]
theorem step_017 : Agreement point_017 point_018
    componentChars_017 emitted_017 := by
  intro rest priorTokens
  cbv

def emitted_018 : List String := [")", "(", "u64", "0", ")", ")", "(", "block", "(", "return", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "let", "grown", "(", "array", "u64", ")", "(", "new-array", "u64", "(", "add", "(", "length", "(", "var", "words", ")", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "set", "(", "index", "(", "var", "grown", ")", "(", "length", "(", "var", "words", ")", ")", ")", "(", "u64", "1", ")", ")", "(", "set", "("]
theorem step_018 : Agreement point_018 point_019
    componentChars_018 emitted_018 := by
  intro rest priorTokens
  cbv

def emitted_019 : List String := ["field", "(", "var", "thy", ")", "next-identity", ")", "(", "var", "grown", ")", ")", "(", "free", "(", "var", "words", ")", ")", "(", "return", ")", ")", ")", "(", "function", "symbol-new", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "kind", "u64", ")", "(", "arity", "u64", ")", "(", "binders", "(", "array", "u64", ")", ")", ")", "(", "ref", "Symbol", ")", "(", "block", "(", "if", "(", "or", "(", "gt", "(", "var", "kind", ")", "(", "u64", "1", ")", ")"]
theorem step_019 : Agreement point_019 point_020
    componentChars_019 emitted_019 := by
  intro rest priorTokens
  cbv

def emitted_020 : List String := ["(", "and", "(", "eq", "(", "var", "kind", ")", "(", "u64", "0", ")", ")", "(", "ne", "(", "var", "arity", ")", "(", "length", "(", "var", "binders", ")", ")", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Symbol", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "s", "(", "ref", "Symbol", ")", "(", "new", "Symbol", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "kind", ")", "(", "var", "kind", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")"]
theorem step_020 : Agreement point_020 point_021
    componentChars_020 emitted_020 := by
  intro rest priorTokens
  cbv

def emitted_021 : List String := ["arity", ")", "(", "var", "arity", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "rc", ")", "(", "u64", "1", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "binders", ")", "(", "new-array", "u64", "(", "var", "arity", ")", ")", ")", "(", "if", "(", "eq", "(", "var", "kind", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "var", "arity", ")", ")", "("]
theorem step_021 : Agreement point_021 point_022
    componentChars_021 emitted_021 := by
  intro rest priorTokens
  cbv

def emitted_022 : List String := ["block", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "binders", ")", "(", "var", "i", ")", ")", "(", "index", "(", "var", "binders", ")", "(", "var", "i", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "identity", ")", "(", "call", "copy-words", "(", "field", "(", "var", "thy", ")"]
theorem step_022 : Agreement point_022 point_023
    componentChars_022 emitted_022 := by
  intro rest priorTokens
  cbv

def emitted_023 : List String := ["next-identity", ")", ")", ")", "(", "effect", "(", "call", "advance-identity", "(", "var", "thy", ")", ")", ")", "(", "return", "(", "var", "s", ")", ")", ")", ")", "(", "function", "term-retain", "(", "(", "t", "(", "ref", "Term", ")", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "if", "(", "ne", "(", "var", "t", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "t", ")", "rc", ")", "(", "add", "(", "field", "(", "var", "t", ")", "rc", ")", "(", "u64"]
theorem step_023 : Agreement point_023 point_024
    componentChars_023 emitted_023 := by
  intro rest priorTokens
  cbv

def emitted_024 : List String := ["1", ")", ")", ")", ")", "(", "block", ")", ")", "(", "return", "(", "var", "t", ")", ")", ")", ")", "(", "function", "term-free", "(", "(", "t", "(", "ref", "Term", ")", ")", ")", "unit", "(", "block", "(", "if", "(", "eq", "(", "var", "t", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "return", ")", ")", "(", "block", ")", ")", "(", "if", "(", "gt", "(", "field", "(", "var", "t", ")", "rc", ")", "(", "u64", "1", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "t", ")", "rc", ")", "(", "sub"]
theorem step_024 : Agreement point_024 point_025
    componentChars_024 emitted_024 := by
  intro rest priorTokens
  cbv

def emitted_025 : List String := ["(", "field", "(", "var", "t", ")", "rc", ")", "(", "u64", "1", ")", ")", ")", "(", "return", ")", ")", "(", "block", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "t", ")", "args", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "term-free", "(", "index", "(", "field", "(", "var", "t", ")", "args", ")", "(", "var", "i", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")"]
theorem step_025 : Agreement point_025 point_026
    componentChars_025 emitted_025 := by
  intro rest priorTokens
  cbv

def emitted_026 : List String := ["(", "u64", "1", ")", ")", ")", ")", ")", "(", "free", "(", "field", "(", "var", "t", ")", "args", ")", ")", "(", "free", "(", "field", "(", "var", "t", ")", "literal", ")", ")", "(", "effect", "(", "call", "symbol-free", "(", "field", "(", "var", "t", ")", "symbol", ")", ")", ")", "(", "free", "(", "var", "t", ")", ")", "(", "return", ")", ")", ")", "(", "function", "free-terms", "(", "(", "terms", "(", "array", "(", "ref", "Term", ")", ")", ")", ")", "unit", "(", "block", "("]
theorem step_026 : Agreement point_026 point_027
    componentChars_026 emitted_026 := by
  intro rest priorTokens
  cbv

def emitted_027 : List String := ["let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "var", "terms", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "term-free", "(", "index", "(", "var", "terms", ")", "(", "var", "i", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "free", "(", "var", "terms", ")", ")", "(", "return", ")", ")", ")", "(", "function", "term-empty", "(", "("]
theorem step_027 : Agreement point_027 point_028
    componentChars_027 emitted_027 := by
  intro rest priorTokens
  cbv

def emitted_028 : List String := ["s", "(", "ref", "Symbol", ")", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "let", "t", "(", "ref", "Term", ")", "(", "new", "Term", ")", ")", "(", "set", "(", "field", "(", "var", "t", ")", "symbol", ")", "(", "call", "symbol-retain", "(", "var", "s", ")", ")", ")", "(", "set", "(", "field", "(", "var", "t", ")", "rc", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "var", "t", ")", ")", ")", ")", "(", "function", "term-bvar", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "index", "u64", ")"]
theorem step_028 : Agreement point_028 point_029
    componentChars_028 emitted_028 := by
  intro rest priorTokens
  cbv

def emitted_029 : List String := [")", "(", "ref", "Term", ")", "(", "block", "(", "let", "depth", "u64", "(", "add", "(", "var", "index", ")", "(", "u64", "1", ")", ")", ")", "(", "if", "(", "lt", "(", "var", "depth", ")", "(", "var", "index", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "t", "(", "ref", "Term", ")", "(", "call", "term-empty", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "u64", "0", ")", ")", ")", ")", "("]
theorem step_029 : Agreement point_029 point_030
    componentChars_029 emitted_029 := by
  intro rest priorTokens
  cbv

def emitted_030 : List String := ["set", "(", "field", "(", "var", "t", ")", "number", ")", "(", "var", "index", ")", ")", "(", "set", "(", "field", "(", "var", "t", ")", "depth", ")", "(", "var", "depth", ")", ")", "(", "return", "(", "var", "t", ")", ")", ")", ")", "(", "function", "term-literal", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "data", "bytes", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "if", "(", "lt", "(", "add", "(", "length", "(", "var", "data", ")", ")", "(", "u64", "8", ")", ")", "(", "length", "(", "var"]
theorem step_030 : Agreement point_030 point_031
    componentChars_030 emitted_030 := by
  intro rest priorTokens
  cbv

def emitted_031 : List String := ["data", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "t", "(", "ref", "Term", ")", "(", "call", "term-empty", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "set", "(", "field", "(", "var", "t", ")", "literal", ")", "(", "new-array", "byte", "(", "length", "(", "var", "data", ")", ")", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while"]
theorem step_031 : Agreement point_031 point_032
    componentChars_031 emitted_031 := by
  intro rest priorTokens
  cbv

def emitted_032 : List String := ["(", "lt", "(", "var", "i", ")", "(", "length", "(", "var", "data", ")", ")", ")", "(", "block", "(", "set", "(", "index", "(", "field", "(", "var", "t", ")", "literal", ")", "(", "var", "i", ")", ")", "(", "index", "(", "var", "data", ")", "(", "var", "i", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "return", "(", "var", "t", ")", ")", ")", ")", "(", "function", "term-number", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "n", "u64", ")", ")", "("]
theorem step_032 : Agreement point_032 point_033
    componentChars_032 emitted_032 := by
  intro rest priorTokens
  cbv

def emitted_033 : List String := ["ref", "Term", ")", "(", "block", "(", "let", "count", "u64", "(", "u64", "8", ")", ")", "(", "if", "(", "lt", "(", "var", "n", ")", "(", "u64", "256", ")", ")", "(", "block", "(", "set", "(", "var", "count", ")", "(", "u64", "1", ")", ")", ")", "(", "block", ")", ")", "(", "let", "data", "bytes", "(", "new-array", "byte", "(", "var", "count", ")", ")", ")", "(", "let", "rest", "u64", "(", "var", "n", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")"]
theorem step_033 : Agreement point_033 point_034
    componentChars_033 emitted_033 := by
  intro rest priorTokens
  cbv

def emitted_034 : List String := ["(", "var", "count", ")", ")", "(", "block", "(", "set", "(", "index", "(", "var", "data", ")", "(", "var", "i", ")", ")", "(", "to-byte", "(", "var", "rest", ")", ")", ")", "(", "set", "(", "var", "rest", ")", "(", "shr", "(", "var", "rest", ")", "(", "u64", "8", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "let", "t", "(", "ref", "Term", ")", "(", "call", "term-literal", "(", "var", "thy", ")", "(", "var", "data", ")"]
theorem step_034 : Agreement point_034 point_035
    componentChars_034 emitted_034 := by
  intro rest priorTokens
  cbv

def emitted_035 : List String := [")", ")", "(", "free", "(", "var", "data", ")", ")", "(", "return", "(", "var", "t", ")", ")", ")", ")", "(", "function", "term-app", "(", "(", "s", "(", "ref", "Symbol", ")", ")", "(", "args", "(", "array", "(", "ref", "Term", ")", ")", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "if", "(", "or", "(", "eq", "(", "var", "s", ")", "(", "null", "(", "ref", "Symbol", ")", ")", ")", "(", "or", "(", "gt", "(", "field", "(", "var", "s", ")", "kind", ")", "(", "u64", "1", ")", ")"]
theorem step_035 : Agreement point_035 point_036
    componentChars_035 emitted_035 := by
  intro rest priorTokens
  cbv

def emitted_036 : List String := ["(", "ne", "(", "field", "(", "var", "s", ")", "arity", ")", "(", "length", "(", "var", "args", ")", ")", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "var", "args", ")", ")", ")", "(", "block", "(", "if", "(", "eq", "(", "index", "(", "var", "args", ")", "(", "var", "i", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")"]
theorem step_036 : Agreement point_036 point_037
    componentChars_036 emitted_036 := by
  intro rest priorTokens
  cbv

def emitted_037 : List String := ["(", "block", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "let", "t", "(", "ref", "Term", ")", "(", "call", "term-empty", "(", "var", "s", ")", ")", ")", "(", "set", "(", "field", "(", "var", "t", ")", "has-fvar", ")", "(", "eq", "(", "field", "(", "var", "s", ")", "kind", ")", "(", "u64", "1", ")", ")", ")", "(", "set", "(", "field", "(", "var", "t", ")"]
theorem step_037 : Agreement point_037 point_038
    componentChars_037 emitted_037 := by
  intro rest priorTokens
  cbv

def emitted_038 : List String := ["args", ")", "(", "new-array", "(", "ref", "Term", ")", "(", "length", "(", "var", "args", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "var", "args", ")", ")", ")", "(", "block", "(", "let", "a", "(", "ref", "Term", ")", "(", "index", "(", "var", "args", ")", "(", "var", "i", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "t", ")", "args", ")", "(", "var", "i", ")", ")", "(", "call"]
theorem step_038 : Agreement point_038 point_039
    componentChars_038 emitted_038 := by
  intro rest priorTokens
  cbv

def emitted_039 : List String := ["term-retain", "(", "var", "a", ")", ")", ")", "(", "set", "(", "field", "(", "var", "t", ")", "has-fvar", ")", "(", "or", "(", "field", "(", "var", "t", ")", "has-fvar", ")", "(", "field", "(", "var", "a", ")", "has-fvar", ")", ")", ")", "(", "let", "binders", "u64", "(", "index", "(", "field", "(", "var", "s", ")", "binders", ")", "(", "var", "i", ")", ")", ")", "(", "if", "(", "and", "(", "gt", "(", "field", "(", "var", "a", ")", "depth", ")", "(", "var", "binders", ")", ")"]
theorem step_039 : Agreement point_039 point_040
    componentChars_039 emitted_039 := by
  intro rest priorTokens
  cbv

def emitted_040 : List String := ["(", "gt", "(", "sub", "(", "field", "(", "var", "a", ")", "depth", ")", "(", "var", "binders", ")", ")", "(", "field", "(", "var", "t", ")", "depth", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "t", ")", "depth", ")", "(", "sub", "(", "field", "(", "var", "a", ")", "depth", ")", "(", "var", "binders", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "return", "(", "var", "t", ")", ")", ")", ")"]
theorem step_040 : Agreement point_040 point_041
    componentChars_040 emitted_040 := by
  intro rest priorTokens
  cbv

def emitted_041 : List String := ["(", "function", "term-equal", "(", "(", "a", "(", "ref", "Term", ")", ")", "(", "b", "(", "ref", "Term", ")", ")", ")", "bool", "(", "block", "(", "if", "(", "eq", "(", "var", "a", ")", "(", "var", "b", ")", ")", "(", "block", "(", "return", "(", "bool", "true", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "or", "(", "eq", "(", "var", "a", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "eq", "(", "var", "b", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")"]
theorem step_041 : Agreement point_041 point_042
    componentChars_041 emitted_041 := by
  intro rest priorTokens
  cbv

def emitted_042 : List String := ["(", "block", ")", ")", "(", "if", "(", "ne", "(", "field", "(", "var", "a", ")", "symbol", ")", "(", "field", "(", "var", "b", ")", "symbol", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "kind", "u64", "(", "field", "(", "field", "(", "var", "a", ")", "symbol", ")", "kind", ")", ")", "(", "if", "(", "eq", "(", "var", "kind", ")", "(", "u64", "2", ")", ")", "(", "block", "(", "return", "(", "eq", "(", "field", "(", "var", "a", ")"]
theorem step_042 : Agreement point_042 point_043
    componentChars_042 emitted_042 := by
  intro rest priorTokens
  cbv

def emitted_043 : List String := ["number", ")", "(", "field", "(", "var", "b", ")", "number", ")", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "eq", "(", "var", "kind", ")", "(", "u64", "3", ")", ")", "(", "block", "(", "if", "(", "ne", "(", "length", "(", "field", "(", "var", "a", ")", "literal", ")", ")", "(", "length", "(", "field", "(", "var", "b", ")", "literal", ")", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")"]
theorem step_043 : Agreement point_043 point_044
    componentChars_043 emitted_043 := by
  intro rest priorTokens
  cbv

def emitted_044 : List String := ["(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "a", ")", "literal", ")", ")", ")", "(", "block", "(", "if", "(", "ne", "(", "index", "(", "field", "(", "var", "a", ")", "literal", ")", "(", "var", "i", ")", ")", "(", "index", "(", "field", "(", "var", "b", ")", "literal", ")", "(", "var", "i", ")", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "set", "("]
theorem step_044 : Agreement point_044 point_045
    componentChars_044 emitted_044 := by
  intro rest priorTokens
  cbv

def emitted_045 : List String := ["var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "return", "(", "bool", "true", ")", ")", ")", "(", "block", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "a", ")", "args", ")", ")", ")", "(", "block", "(", "if", "(", "not", "(", "call", "term-equal", "(", "index", "(", "field", "(", "var", "a", ")", "args", ")", "(", "var", "i", ")", ")"]
theorem step_045 : Agreement point_045 point_046
    componentChars_045 emitted_045 := by
  intro rest priorTokens
  cbv

def emitted_046 : List String := ["(", "index", "(", "field", "(", "var", "b", ")", "args", ")", "(", "var", "i", ")", ")", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "return", "(", "bool", "true", ")", ")", ")", ")", "(", "function", "shift", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "amount", "u64", ")", "("]
theorem step_046 : Agreement point_046 point_047
    componentChars_046 emitted_046 := by
  intro rest priorTokens
  cbv

def emitted_047 : List String := ["cutoff", "u64", ")", "(", "t", "(", "ref", "Term", ")", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "if", "(", "or", "(", "eq", "(", "var", "amount", ")", "(", "u64", "0", ")", ")", "(", "le", "(", "field", "(", "var", "t", ")", "depth", ")", "(", "var", "cutoff", ")", ")", ")", "(", "block", "(", "return", "(", "call", "term-retain", "(", "var", "t", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "s", "(", "ref", "Symbol", ")", "(", "field", "(", "var", "t", ")", "symbol", ")", ")", "(", "if", "(", "eq", "("]
theorem step_047 : Agreement point_047 point_048
    componentChars_047 emitted_047 := by
  intro rest priorTokens
  cbv

def emitted_048 : List String := ["field", "(", "var", "s", ")", "kind", ")", "(", "u64", "2", ")", ")", "(", "block", "(", "let", "index", "u64", "(", "add", "(", "field", "(", "var", "t", ")", "number", ")", "(", "var", "amount", ")", ")", ")", "(", "if", "(", "lt", "(", "var", "index", ")", "(", "field", "(", "var", "t", ")", "number", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "return", "(", "call", "term-bvar", "(", "var"]
theorem step_048 : Agreement point_048 point_049
    componentChars_048 emitted_048 := by
  intro rest priorTokens
  cbv

def emitted_049 : List String := ["thy", ")", "(", "var", "index", ")", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "eq", "(", "field", "(", "var", "s", ")", "kind", ")", "(", "u64", "3", ")", ")", "(", "block", "(", "return", "(", "call", "term-retain", "(", "var", "t", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "children", "(", "array", "(", "ref", "Term", ")", ")", "(", "new-array", "(", "ref", "Term", ")", "(", "field", "(", "var", "s", ")", "arity", ")", ")", ")", "(", "let", "same", "bool", "(", "bool"]
theorem step_049 : Agreement point_049 point_050
    componentChars_049 emitted_049 := by
  intro rest priorTokens
  cbv

def emitted_050 : List String := ["true", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "field", "(", "var", "s", ")", "arity", ")", ")", "(", "block", "(", "let", "nested", "u64", "(", "add", "(", "var", "cutoff", ")", "(", "index", "(", "field", "(", "var", "s", ")", "binders", ")", "(", "var", "i", ")", ")", ")", ")", "(", "if", "(", "lt", "(", "var", "nested", ")", "(", "var", "cutoff", ")", ")", "(", "block", "(", "effect", "("]
theorem step_050 : Agreement point_050 point_051
    componentChars_050 emitted_050 := by
  intro rest priorTokens
  cbv

def emitted_051 : List String := ["call", "free-terms", "(", "var", "children", ")", ")", ")", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "old", "(", "ref", "Term", ")", "(", "index", "(", "field", "(", "var", "t", ")", "args", ")", "(", "var", "i", ")", ")", ")", "(", "let", "child", "(", "ref", "Term", ")", "(", "call", "shift", "(", "var", "thy", ")", "(", "var", "amount", ")", "(", "var", "nested", ")", "(", "var", "old", ")", ")", ")", "(", "set", "(", "index", "(", "var"]
theorem step_051 : Agreement point_051 point_052
    componentChars_051 emitted_051 := by
  intro rest priorTokens
  cbv

def emitted_052 : List String := ["children", ")", "(", "var", "i", ")", ")", "(", "var", "child", ")", ")", "(", "if", "(", "eq", "(", "var", "child", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "free-terms", "(", "var", "children", ")", ")", ")", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "same", ")", "(", "and", "(", "var", "same", ")", "(", "eq", "(", "var", "child", ")", "(", "var", "old", ")", ")", ")", ")"]
theorem step_052 : Agreement point_052 point_053
    componentChars_052 emitted_052 := by
  intro rest priorTokens
  cbv

def emitted_053 : List String := ["(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "let", "out", "(", "ref", "Term", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "if", "(", "var", "same", ")", "(", "block", "(", "set", "(", "var", "out", ")", "(", "call", "term-retain", "(", "var", "t", ")", ")", ")", ")", "(", "block", "(", "set", "(", "var", "out", ")", "(", "call", "term-app", "(", "var", "s", ")", "(", "var", "children", ")", ")", ")", ")", ")", "(", "effect", "(", "call"]
theorem step_053 : Agreement point_053 point_054
    componentChars_053 emitted_053 := by
  intro rest priorTokens
  cbv

def emitted_054 : List String := ["free-terms", "(", "var", "children", ")", ")", ")", "(", "return", "(", "var", "out", ")", ")", ")", ")", "(", "function", "subst-go", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "arguments", "(", "array", "(", "ref", "Term", ")", ")", ")", "(", "offset", "u64", ")", "(", "t", "(", "ref", "Term", ")", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "if", "(", "le", "(", "field", "(", "var", "t", ")", "depth", ")", "(", "var", "offset", ")", ")", "("]
theorem step_054 : Agreement point_054 point_055
    componentChars_054 emitted_054 := by
  intro rest priorTokens
  cbv

def emitted_055 : List String := ["block", "(", "return", "(", "call", "term-retain", "(", "var", "t", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "s", "(", "ref", "Symbol", ")", "(", "field", "(", "var", "t", ")", "symbol", ")", ")", "(", "if", "(", "eq", "(", "field", "(", "var", "s", ")", "kind", ")", "(", "u64", "2", ")", ")", "(", "block", "(", "let", "relative", "u64", "(", "sub", "(", "field", "(", "var", "t", ")", "number", ")", "(", "var", "offset", ")", ")", ")", "(", "if", "(", "lt", "(", "var"]
theorem step_055 : Agreement point_055 point_056
    componentChars_055 emitted_055 := by
  intro rest priorTokens
  cbv

def emitted_056 : List String := ["relative", ")", "(", "length", "(", "var", "arguments", ")", ")", ")", "(", "block", "(", "return", "(", "call", "shift", "(", "var", "thy", ")", "(", "var", "offset", ")", "(", "u64", "0", ")", "(", "index", "(", "var", "arguments", ")", "(", "sub", "(", "sub", "(", "length", "(", "var", "arguments", ")", ")", "(", "u64", "1", ")", ")", "(", "var", "relative", ")", ")", ")", ")", ")", ")", "(", "block", "(", "return", "("]
theorem step_056 : Agreement point_056 point_057
    componentChars_056 emitted_056 := by
  intro rest priorTokens
  cbv

def emitted_057 : List String := ["call", "term-bvar", "(", "var", "thy", ")", "(", "var", "relative", ")", ")", ")", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "eq", "(", "field", "(", "var", "s", ")", "kind", ")", "(", "u64", "3", ")", ")", "(", "block", "(", "return", "(", "call", "term-retain", "(", "var", "t", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "children", "(", "array", "(", "ref", "Term", ")", ")", "(", "new-array", "(", "ref", "Term", ")", "(", "field", "(", "var", "s", ")", "arity", ")", ")", ")"]
theorem step_057 : Agreement point_057 point_058
    componentChars_057 emitted_057 := by
  intro rest priorTokens
  cbv

def emitted_058 : List String := ["(", "let", "same", "bool", "(", "bool", "true", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "field", "(", "var", "s", ")", "arity", ")", ")", "(", "block", "(", "let", "nested", "u64", "(", "add", "(", "var", "offset", ")", "(", "index", "(", "field", "(", "var", "s", ")", "binders", ")", "(", "var", "i", ")", ")", ")", ")", "(", "if", "(", "lt", "(", "var", "nested", ")", "(", "var", "offset", ")", ")"]
theorem step_058 : Agreement point_058 point_059
    componentChars_058 emitted_058 := by
  intro rest priorTokens
  cbv

def emitted_059 : List String := ["(", "block", "(", "effect", "(", "call", "free-terms", "(", "var", "children", ")", ")", ")", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "old", "(", "ref", "Term", ")", "(", "index", "(", "field", "(", "var", "t", ")", "args", ")", "(", "var", "i", ")", ")", ")", "(", "let", "child", "(", "ref", "Term", ")", "(", "call", "subst-go", "(", "var", "thy", ")", "(", "var", "arguments", ")", "(", "var", "nested", ")", "(", "var", "old", ")", ")", ")"]
theorem step_059 : Agreement point_059 point_060
    componentChars_059 emitted_059 := by
  intro rest priorTokens
  cbv

def emitted_060 : List String := ["(", "set", "(", "index", "(", "var", "children", ")", "(", "var", "i", ")", ")", "(", "var", "child", ")", ")", "(", "if", "(", "eq", "(", "var", "child", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "free-terms", "(", "var", "children", ")", ")", ")", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "same", ")", "(", "and", "(", "var", "same", ")", "(", "eq", "("]
theorem step_060 : Agreement point_060 point_061
    componentChars_060 emitted_060 := by
  intro rest priorTokens
  cbv

def emitted_061 : List String := ["var", "child", ")", "(", "var", "old", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "let", "out", "(", "ref", "Term", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "if", "(", "var", "same", ")", "(", "block", "(", "set", "(", "var", "out", ")", "(", "call", "term-retain", "(", "var", "t", ")", ")", ")", ")", "(", "block", "(", "set", "(", "var", "out", ")", "(", "call", "term-app", "(", "var", "s", ")", "(", "var", "children", ")", ")", ")", ")"]
theorem step_061 : Agreement point_061 point_062
    componentChars_061 emitted_061 := by
  intro rest priorTokens
  cbv

def emitted_062 : List String := [")", "(", "effect", "(", "call", "free-terms", "(", "var", "children", ")", ")", ")", "(", "return", "(", "var", "out", ")", ")", ")", ")", "(", "function", "subst-bvars", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "arguments", "(", "array", "(", "ref", "Term", ")", ")", ")", "(", "offset", "u64", ")", "(", "t", "(", "ref", "Term", ")", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "if", "(", "eq", "(", "length", "(", "var"]
theorem step_062 : Agreement point_062 point_063
    componentChars_062 emitted_062 := by
  intro rest priorTokens
  cbv

def emitted_063 : List String := ["arguments", ")", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "return", "(", "call", "term-retain", "(", "var", "t", ")", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "eq", "(", "var", "t", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "var", "arguments", ")", ")", ")", "("]
theorem step_063 : Agreement point_063 point_064
    componentChars_063 emitted_063 := by
  intro rest priorTokens
  cbv

def emitted_064 : List String := ["block", "(", "if", "(", "eq", "(", "index", "(", "var", "arguments", ")", "(", "var", "i", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "return", "(", "call", "subst-go", "(", "var", "thy", ")", "(", "var", "arguments", ")", "(", "var", "offset", ")", "(", "var", "t", ")", ")", ")", ")", ")"]
theorem step_064 : Agreement point_064 point_065
    componentChars_064 emitted_064 := by
  intro rest priorTokens
  cbv

def emitted_065 : List String := ["(", "function", "inst-go", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "fvar", "(", "ref", "Symbol", ")", ")", "(", "value", "(", "ref", "Term", ")", ")", "(", "offset", "u64", ")", "(", "t", "(", "ref", "Term", ")", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "if", "(", "not", "(", "field", "(", "var", "t", ")", "has-fvar", ")", ")", "(", "block", "(", "return", "(", "call", "term-retain", "(", "var", "t", ")", ")", ")", ")", "(", "block", ")", ")"]
theorem step_065 : Agreement point_065 point_066
    componentChars_065 emitted_065 := by
  intro rest priorTokens
  cbv

def emitted_066 : List String := ["(", "let", "s", "(", "ref", "Symbol", ")", "(", "field", "(", "var", "t", ")", "symbol", ")", ")", "(", "if", "(", "gt", "(", "field", "(", "var", "s", ")", "kind", ")", "(", "u64", "1", ")", ")", "(", "block", "(", "return", "(", "call", "term-retain", "(", "var", "t", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "children", "(", "array", "(", "ref", "Term", ")", ")", "(", "new-array", "(", "ref", "Term", ")", "(", "field", "(", "var", "s", ")", "arity", ")", ")", ")", "(", "let", "same"]
theorem step_066 : Agreement point_066 point_067
    componentChars_066 emitted_066 := by
  intro rest priorTokens
  cbv

def emitted_067 : List String := ["bool", "(", "bool", "true", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "field", "(", "var", "s", ")", "arity", ")", ")", "(", "block", "(", "let", "nested", "u64", "(", "add", "(", "var", "offset", ")", "(", "index", "(", "field", "(", "var", "s", ")", "binders", ")", "(", "var", "i", ")", ")", ")", ")", "(", "if", "(", "lt", "(", "var", "nested", ")", "(", "var", "offset", ")", ")", "(", "block", "("]
theorem step_067 : Agreement point_067 point_068
    componentChars_067 emitted_067 := by
  intro rest priorTokens
  cbv

def emitted_068 : List String := ["effect", "(", "call", "free-terms", "(", "var", "children", ")", ")", ")", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "old", "(", "ref", "Term", ")", "(", "index", "(", "field", "(", "var", "t", ")", "args", ")", "(", "var", "i", ")", ")", ")", "(", "let", "child", "(", "ref", "Term", ")", "(", "call", "inst-go", "(", "var", "thy", ")", "(", "var", "fvar", ")", "(", "var", "value", ")", "(", "var", "nested", ")", "(", "var", "old", ")", ")", ")"]
theorem step_068 : Agreement point_068 point_069
    componentChars_068 emitted_068 := by
  intro rest priorTokens
  cbv

def emitted_069 : List String := ["(", "set", "(", "index", "(", "var", "children", ")", "(", "var", "i", ")", ")", "(", "var", "child", ")", ")", "(", "if", "(", "eq", "(", "var", "child", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "free-terms", "(", "var", "children", ")", ")", ")", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "same", ")", "(", "and", "(", "var", "same", ")", "(", "eq", "(", "var"]
theorem step_069 : Agreement point_069 point_070
    componentChars_069 emitted_069 := by
  intro rest priorTokens
  cbv

def emitted_070 : List String := ["child", ")", "(", "var", "old", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "let", "out", "(", "ref", "Term", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "if", "(", "eq", "(", "var", "s", ")", "(", "var", "fvar", ")", ")", "(", "block", "(", "let", "shifted", "(", "ref", "Term", ")", "(", "call", "shift", "(", "var", "thy", ")", "(", "var", "offset", ")", "(", "field", "(", "var", "fvar", ")", "arity", ")", "(", "var"]
theorem step_070 : Agreement point_070 point_071
    componentChars_070 emitted_070 := by
  intro rest priorTokens
  cbv

def emitted_071 : List String := ["value", ")", ")", ")", "(", "if", "(", "ne", "(", "var", "shifted", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "set", "(", "var", "out", ")", "(", "call", "subst-bvars", "(", "var", "thy", ")", "(", "var", "children", ")", "(", "u64", "0", ")", "(", "var", "shifted", ")", ")", ")", "(", "effect", "(", "call", "term-free", "(", "var", "shifted", ")", ")", ")", ")", "(", "block", ")", ")", ")", "("]
theorem step_071 : Agreement point_071 point_072
    componentChars_071 emitted_071 := by
  intro rest priorTokens
  cbv

def emitted_072 : List String := ["block", "(", "if", "(", "var", "same", ")", "(", "block", "(", "set", "(", "var", "out", ")", "(", "call", "term-retain", "(", "var", "t", ")", ")", ")", ")", "(", "block", "(", "set", "(", "var", "out", ")", "(", "call", "term-app", "(", "var", "s", ")", "(", "var", "children", ")", ")", ")", ")", ")", ")", ")", "(", "effect", "(", "call", "free-terms", "(", "var", "children", ")", ")", ")", "(", "return", "(", "var", "out", ")", ")", ")", ")", "(", "function", "instantiate"]
theorem step_072 : Agreement point_072 point_073
    componentChars_072 emitted_072 := by
  intro rest priorTokens
  cbv

def emitted_073 : List String := ["(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "fvar", "(", "ref", "Symbol", ")", ")", "(", "value", "(", "ref", "Term", ")", ")", "(", "t", "(", "ref", "Term", ")", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "if", "(", "or", "(", "eq", "(", "var", "fvar", ")", "(", "null", "(", "ref", "Symbol", ")", ")", ")", "(", "or", "(", "eq", "(", "var", "value", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "eq", "(", "var", "t", ")", "(", "null", "(", "ref", "Term", ")", ")", ")"]
theorem step_073 : Agreement point_073 point_074
    componentChars_073 emitted_073 := by
  intro rest priorTokens
  cbv

def emitted_074 : List String := [")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "ne", "(", "field", "(", "var", "fvar", ")", "kind", ")", "(", "u64", "1", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "return", "(", "call", "inst-go", "(", "var", "thy", ")", "(", "var", "fvar", ")", "(", "var", "value", ")", "(", "u64", "0", ")", "(", "var", "t", ")", ")", ")", ")", ")", "(", "function"]
theorem step_074 : Agreement point_074 point_075
    componentChars_074 emitted_074 := by
  intro rest priorTokens
  cbv

def emitted_075 : List String := ["builtin-arity", "(", "(", "slot", "u64", ")", ")", "u64", "(", "block", "(", "switch", "(", "var", "slot", ")", "(", "case", "2", "(", "block", "(", "return", "(", "u64", "2", ")", ")", ")", ")", "(", "case", "3", "(", "block", "(", "return", "(", "u64", "2", ")", ")", ")", ")", "(", "case", "4", "(", "block", "(", "return", "(", "u64", "1", ")", ")", ")", ")", "(", "case", "5", "(", "block", "(", "return", "(", "u64", "2", ")", ")", ")", ")", "(", "case", "6", "(", "block", "("]
theorem step_075 : Agreement point_075 point_076
    componentChars_075 emitted_075 := by
  intro rest priorTokens
  cbv

def emitted_076 : List String := ["return", "(", "u64", "2", ")", ")", ")", ")", "(", "case", "7", "(", "block", "(", "return", "(", "u64", "2", ")", ")", ")", ")", "(", "case", "8", "(", "block", "(", "return", "(", "u64", "2", ")", ")", ")", ")", "(", "case", "9", "(", "block", "(", "return", "(", "u64", "1", ")", ")", ")", ")", "(", "case", "10", "(", "block", "(", "return", "(", "u64", "2", ")", ")", ")", ")", "(", "case", "11", "(", "block", "(", "return", "(", "u64", "4", ")", ")", ")", ")", "(", "case", "12", "(", "block", "("]
theorem step_076 : Agreement point_076 point_077
    componentChars_076 emitted_076 := by
  intro rest priorTokens
  cbv

def emitted_077 : List String := ["return", "(", "u64", "4", ")", ")", ")", ")", "(", "default", "(", "block", "(", "return", "(", "u64", "0", ")", ")", ")", ")", ")", ")", ")", "(", "function", "theory-initial", "(", ")", "(", "ref", "Theory", ")", "(", "block", "(", "let", "thy", "(", "ref", "Theory", ")", "(", "new", "Theory", ")", ")", "(", "set", "(", "field", "(", "var", "thy", ")", "revision", ")", "(", "new-array", "u64", "(", "u64", "1", ")", ")", ")", "(", "set", "(", "field", "(", "var", "thy", ")"]
theorem step_077 : Agreement point_077 point_078
    componentChars_077 emitted_077 := by
  intro rest priorTokens
  cbv

def emitted_078 : List String := ["next-identity", ")", "(", "new-array", "u64", "(", "u64", "1", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "thy", ")", "next-identity", ")", "(", "u64", "0", ")", ")", "(", "u64", "13", ")", ")", "(", "set", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "new-array", "(", "ref", "Symbol", ")", "(", "u64", "13", ")", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "u64", "13", ")", ")", "(", "block"]
theorem step_078 : Agreement point_078 point_079
    componentChars_078 emitted_078 := by
  intro rest priorTokens
  cbv

def emitted_079 : List String := ["(", "let", "s", "(", "ref", "Symbol", ")", "(", "new", "Symbol", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "kind", ")", "(", "u64", "0", ")", ")", "(", "if", "(", "eq", "(", "var", "i", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "kind", ")", "(", "u64", "2", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "eq", "(", "var", "i", ")", "(", "u64", "1", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "kind", ")", "(", "u64", "3", ")", ")", ")", "(", "block", ")", ")"]
theorem step_079 : Agreement point_079 point_080
    componentChars_079 emitted_079 := by
  intro rest priorTokens
  cbv

def emitted_080 : List String := ["(", "set", "(", "field", "(", "var", "s", ")", "arity", ")", "(", "call", "builtin-arity", "(", "var", "i", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "binders", ")", "(", "new-array", "u64", "(", "field", "(", "var", "s", ")", "arity", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "identity", ")", "(", "new-array", "u64", "(", "u64", "1", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "identity", ")"]
theorem step_080 : Agreement point_080 point_081
    componentChars_080 emitted_080 := by
  intro rest priorTokens
  cbv

def emitted_081 : List String := ["(", "u64", "0", ")", ")", "(", "var", "i", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "rc", ")", "(", "u64", "1", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "immortal", ")", "(", "bool", "true", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "var", "i", ")", ")", "(", "var", "s", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "return", "(", "var", "thy", ")", ")", ")", ")"]
theorem step_081 : Agreement point_081 point_082
    componentChars_081 emitted_081 := by
  intro rest priorTokens
  cbv

def emitted_082 : List String := ["(", "function", "theorem-new", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "statement", "(", "ref", "Term", ")", ")", "(", "origin", "u64", ")", ")", "(", "ref", "Theorem", ")", "(", "block", "(", "if", "(", "eq", "(", "var", "statement", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "gt", "(", "field", "(", "var", "statement", ")", "depth", ")", "(", "u64", "0", ")", ")"]
theorem step_082 : Agreement point_082 point_083
    componentChars_082 emitted_082 := by
  intro rest priorTokens
  cbv

def emitted_083 : List String := ["(", "block", "(", "effect", "(", "call", "term-free", "(", "var", "statement", ")", ")", ")", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "thm", "(", "ref", "Theorem", ")", "(", "new", "Theorem", ")", ")", "(", "set", "(", "field", "(", "var", "thm", ")", "statement", ")", "(", "var", "statement", ")", ")", "(", "set", "(", "field", "(", "var", "thm", ")", "owner", ")", "(", "var", "thy", ")", ")", "(", "set", "("]
theorem step_083 : Agreement point_083 point_084
    componentChars_083 emitted_083 := by
  intro rest priorTokens
  cbv

def emitted_084 : List String := ["field", "(", "var", "thm", ")", "origin", ")", "(", "var", "origin", ")", ")", "(", "set", "(", "field", "(", "var", "thm", ")", "revision", ")", "(", "call", "copy-words", "(", "field", "(", "var", "thy", ")", "revision", ")", ")", ")", "(", "set", "(", "field", "(", "var", "thm", ")", "identity", ")", "(", "call", "copy-words", "(", "field", "(", "var", "thy", ")", "next-identity", ")", ")", ")", "(", "effect", "(", "call", "advance-identity", "(", "var", "thy", ")"]
theorem step_084 : Agreement point_084 point_085
    componentChars_084 emitted_084 := by
  intro rest priorTokens
  cbv

def emitted_085 : List String := [")", ")", "(", "return", "(", "var", "thm", ")", ")", ")", ")", "(", "function", "theorem-free", "(", "(", "thm", "(", "ref", "Theorem", ")", ")", ")", "unit", "(", "block", "(", "if", "(", "eq", "(", "var", "thm", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", "(", "block", "(", "return", ")", ")", "(", "block", ")", ")", "(", "effect", "(", "call", "term-free", "(", "field", "(", "var", "thm", ")", "statement", ")", ")", ")", "(", "effect", "(", "call", "term-free"]
theorem step_085 : Agreement point_085 point_086
    componentChars_085 emitted_085 := by
  intro rest priorTokens
  cbv

def emitted_086 : List String := ["(", "field", "(", "var", "thm", ")", "execution-premise", ")", ")", ")", "(", "effect", "(", "call", "execution-free", "(", "field", "(", "var", "thm", ")", "execution-scope", ")", "(", "field", "(", "var", "thm", ")", "observation", ")", ")", ")", "(", "free", "(", "field", "(", "var", "thm", ")", "revision", ")", ")", "(", "free", "(", "field", "(", "var", "thm", ")", "identity", ")", ")", "(", "free", "(", "var", "thm", ")", ")", "(", "return", ")"]
theorem step_086 : Agreement point_086 point_087
    componentChars_086 emitted_086 := by
  intro rest priorTokens
  cbv

def emitted_087 : List String := [")", ")", "(", "function", "app1", "(", "(", "s", "(", "ref", "Symbol", ")", ")", "(", "a", "(", "ref", "Term", ")", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "let", "args", "(", "array", "(", "ref", "Term", ")", ")", "(", "new-array", "(", "ref", "Term", ")", "(", "u64", "1", ")", ")", ")", "(", "set", "(", "index", "(", "var", "args", ")", "(", "u64", "0", ")", ")", "(", "var", "a", ")", ")", "(", "let", "t", "(", "ref", "Term", ")", "(", "call", "term-app", "(", "var", "s", ")", "(", "var", "args", ")", ")", ")"]
theorem step_087 : Agreement point_087 point_088
    componentChars_087 emitted_087 := by
  intro rest priorTokens
  cbv

def emitted_088 : List String := ["(", "effect", "(", "call", "free-terms", "(", "var", "args", ")", ")", ")", "(", "return", "(", "var", "t", ")", ")", ")", ")", "(", "function", "app2", "(", "(", "s", "(", "ref", "Symbol", ")", ")", "(", "a", "(", "ref", "Term", ")", ")", "(", "b", "(", "ref", "Term", ")", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "let", "args", "(", "array", "(", "ref", "Term", ")", ")", "(", "new-array", "(", "ref", "Term", ")", "(", "u64", "2", ")", ")", ")", "(", "set", "(", "index", "(", "var", "args", ")", "(", "u64", "0", ")"]
theorem step_088 : Agreement point_088 point_089
    componentChars_088 emitted_088 := by
  intro rest priorTokens
  cbv

def emitted_089 : List String := [")", "(", "var", "a", ")", ")", "(", "set", "(", "index", "(", "var", "args", ")", "(", "u64", "1", ")", ")", "(", "var", "b", ")", ")", "(", "let", "t", "(", "ref", "Term", ")", "(", "call", "term-app", "(", "var", "s", ")", "(", "var", "args", ")", ")", ")", "(", "effect", "(", "call", "free-terms", "(", "var", "args", ")", ")", ")", "(", "return", "(", "var", "t", ")", ")", ")", ")", "(", "function", "modus-ponens", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "implication", "(", "ref"]
theorem step_089 : Agreement point_089 point_090
    componentChars_089 emitted_089 := by
  intro rest priorTokens
  cbv

def emitted_090 : List String := ["Theorem", ")", ")", "(", "premise", "(", "ref", "Theorem", ")", ")", ")", "(", "ref", "Theorem", ")", "(", "block", "(", "if", "(", "or", "(", "eq", "(", "var", "implication", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", "(", "eq", "(", "var", "premise", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")"]
theorem step_090 : Agreement point_090 point_091
    componentChars_090 emitted_090 := by
  intro rest priorTokens
  cbv

def emitted_091 : List String := ["(", "if", "(", "or", "(", "ne", "(", "field", "(", "var", "implication", ")", "owner", ")", "(", "var", "thy", ")", ")", "(", "ne", "(", "field", "(", "var", "premise", ")", "owner", ")", "(", "var", "thy", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "p", "(", "ref", "Term", ")", "(", "field", "(", "var", "implication", ")", "statement", ")", ")", "(", "if", "(", "ne", "(", "field", "(", "var"]
theorem step_091 : Agreement point_091 point_092
    componentChars_091 emitted_091 := by
  intro rest priorTokens
  cbv

def emitted_092 : List String := ["p", ")", "symbol", ")", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "u64", "2", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "not", "(", "call", "term-equal", "(", "index", "(", "field", "(", "var", "p", ")", "args", ")", "(", "u64", "0", ")", ")", "(", "field", "(", "var", "premise", ")", "statement", ")", ")", ")", "("]
theorem step_092 : Agreement point_092 point_093
    componentChars_092 emitted_092 := by
  intro rest priorTokens
  cbv

def emitted_093 : List String := ["block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "return", "(", "call", "theorem-new", "(", "var", "thy", ")", "(", "call", "term-retain", "(", "index", "(", "field", "(", "var", "p", ")", "args", ")", "(", "u64", "1", ")", ")", ")", "(", "u64", "15", ")", ")", ")", ")", ")", "(", "function", "instantiate-theorem", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "thm", "(", "ref", "Theorem", ")", ")"]
theorem step_093 : Agreement point_093 point_094
    componentChars_093 emitted_093 := by
  intro rest priorTokens
  cbv

def emitted_094 : List String := ["(", "fvar", "(", "ref", "Symbol", ")", ")", "(", "value", "(", "ref", "Term", ")", ")", ")", "(", "ref", "Theorem", ")", "(", "block", "(", "if", "(", "or", "(", "eq", "(", "var", "thm", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", "(", "or", "(", "eq", "(", "var", "fvar", ")", "(", "null", "(", "ref", "Symbol", ")", ")", ")", "(", "eq", "(", "var", "value", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", ")", "(", "block", "(", "return", "(", "null", "("]
theorem step_094 : Agreement point_094 point_095
    componentChars_094 emitted_094 := by
  intro rest priorTokens
  cbv

def emitted_095 : List String := ["ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "or", "(", "ne", "(", "field", "(", "var", "thm", ")", "owner", ")", "(", "var", "thy", ")", ")", "(", "or", "(", "ne", "(", "field", "(", "var", "fvar", ")", "kind", ")", "(", "u64", "1", ")", ")", "(", "gt", "(", "field", "(", "var", "value", ")", "depth", ")", "(", "field", "(", "var", "fvar", ")", "arity", ")", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")"]
theorem step_095 : Agreement point_095 point_096
    componentChars_095 emitted_095 := by
  intro rest priorTokens
  cbv

def emitted_096 : List String := ["(", "block", ")", ")", "(", "return", "(", "call", "theorem-new", "(", "var", "thy", ")", "(", "call", "instantiate", "(", "var", "thy", ")", "(", "var", "fvar", ")", "(", "var", "value", ")", "(", "field", "(", "var", "thm", ")", "statement", ")", ")", "(", "u64", "16", ")", ")", ")", ")", ")", "(", "function", "literal-theorem", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "opcode", "u64", ")", "(", "a", "u64", ")", "(", "b", "u64", ")"]
theorem step_096 : Agreement point_096 point_097
    componentChars_096 emitted_096 := by
  intro rest priorTokens
  cbv

def emitted_097 : List String := ["(", "literal", "(", "ref", "Term", ")", ")", ")", "(", "ref", "Theorem", ")", "(", "block", "(", "let", "statement", "(", "ref", "Term", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "let", "operation", "(", "ref", "Term", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "let", "result", "u64", "(", "u64", "0", ")", ")", "(", "if", "(", "eq", "(", "var", "opcode", ")", "(", "u64", "18", ")", ")", "(", "block", "("]
theorem step_097 : Agreement point_097 point_098
    componentChars_097 emitted_097 := by
  intro rest priorTokens
  cbv

def emitted_098 : List String := ["return", "(", "call", "theorem-new", "(", "var", "thy", ")", "(", "call", "app1", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "u64", "4", ")", ")", "(", "call", "term-number", "(", "var", "thy", ")", "(", "var", "a", ")", ")", ")", "(", "var", "opcode", ")", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "eq", "(", "var", "opcode", ")", "(", "u64", "19", ")", ")", "(", "block", "("]
theorem step_098 : Agreement point_098 point_099
    componentChars_098 emitted_098 := by
  intro rest priorTokens
  cbv

def emitted_099 : List String := ["if", "(", "ge", "(", "var", "a", ")", "(", "var", "b", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "return", "(", "call", "theorem-new", "(", "var", "thy", ")", "(", "call", "app2", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "u64", "5", ")", ")", "(", "call", "term-number", "(", "var", "thy", ")", "(", "var", "a", ")", ")"]
theorem step_099 : Agreement point_099 point_100
    componentChars_099 emitted_099 := by
  intro rest priorTokens
  cbv

def emitted_100 : List String := ["(", "call", "term-number", "(", "var", "thy", ")", "(", "var", "b", ")", ")", ")", "(", "var", "opcode", ")", ")", ")", ")", "(", "block", ")", ")", "(", "switch", "(", "var", "opcode", ")", "(", "case", "20", "(", "block", "(", "set", "(", "var", "result", ")", "(", "add", "(", "var", "a", ")", "(", "var", "b", ")", ")", ")", ")", ")", "(", "case", "21", "(", "block", "(", "set", "(", "var", "result", ")", "(", "mul", "(", "var", "a", ")", "(", "var", "b", ")", ")", ")", ")", ")", "(", "case"]
theorem step_100 : Agreement point_100 point_101
    componentChars_100 emitted_100 := by
  intro rest priorTokens
  cbv

def emitted_101 : List String := ["22", "(", "block", "(", "if", "(", "eq", "(", "var", "b", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "result", ")", "(", "div", "(", "var", "a", ")", "(", "var", "b", ")", ")", ")", ")", ")", "(", "case", "23", "(", "block", "(", "if", "(", "or", "(", "eq", "(", "var", "literal", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "ne", "(", "field", "("]
theorem step_101 : Agreement point_101 point_102
    componentChars_101 emitted_101 := by
  intro rest priorTokens
  cbv

def emitted_102 : List String := ["field", "(", "var", "literal", ")", "symbol", ")", "kind", ")", "(", "u64", "3", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "result", ")", "(", "length", "(", "field", "(", "var", "literal", ")", "literal", ")", ")", ")", ")", ")", "(", "case", "24", "(", "block", "(", "if", "(", "or", "(", "eq", "(", "var", "literal", ")", "(", "null", "(", "ref", "Term", ")", ")", ")"]
theorem step_102 : Agreement point_102 point_103
    componentChars_102 emitted_102 := by
  intro rest priorTokens
  cbv

def emitted_103 : List String := ["(", "ne", "(", "field", "(", "field", "(", "var", "literal", ")", "symbol", ")", "kind", ")", "(", "u64", "3", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "ge", "(", "var", "b", ")", "(", "length", "(", "field", "(", "var", "literal", ")", "literal", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")"]
theorem step_103 : Agreement point_103 point_104
    componentChars_103 emitted_103 := by
  intro rest priorTokens
  cbv

def emitted_104 : List String := ["(", "set", "(", "var", "result", ")", "(", "to-u64", "(", "index", "(", "field", "(", "var", "literal", ")", "literal", ")", "(", "var", "b", ")", ")", ")", ")", ")", ")", "(", "default", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", ")", ")", "(", "if", "(", "le", "(", "var", "opcode", ")", "(", "u64", "22", ")", ")", "(", "block", "(", "set", "(", "var", "operation", ")", "(", "call", "app2", "(", "index", "(", "field", "(", "var"]
theorem step_104 : Agreement point_104 point_105
    componentChars_104 emitted_104 := by
  intro rest priorTokens
  cbv

def emitted_105 : List String := ["thy", ")", "builtins", ")", "(", "sub", "(", "var", "opcode", ")", "(", "u64", "14", ")", ")", ")", "(", "call", "term-number", "(", "var", "thy", ")", "(", "var", "a", ")", ")", "(", "call", "term-number", "(", "var", "thy", ")", "(", "var", "b", ")", ")", ")", ")", ")", "(", "block", "(", "if", "(", "eq", "(", "var", "opcode", ")", "(", "u64", "23", ")", ")", "(", "block", "(", "set", "(", "var", "operation", ")", "(", "call", "app1", "(", "index", "(", "field", "("]
theorem step_105 : Agreement point_105 point_106
    componentChars_105 emitted_105 := by
  intro rest priorTokens
  cbv

def emitted_106 : List String := ["var", "thy", ")", "builtins", ")", "(", "u64", "9", ")", ")", "(", "call", "term-retain", "(", "var", "literal", ")", ")", ")", ")", ")", "(", "block", "(", "set", "(", "var", "operation", ")", "(", "call", "app2", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "u64", "10", ")", ")", "(", "call", "term-retain", "(", "var"]
theorem step_106 : Agreement point_106 point_107
    componentChars_106 emitted_106 := by
  intro rest priorTokens
  cbv

def emitted_107 : List String := ["literal", ")", ")", "(", "call", "term-number", "(", "var", "thy", ")", "(", "var", "b", ")", ")", ")", ")", ")", ")", ")", ")", "(", "set", "(", "var", "statement", ")", "(", "call", "app2", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "u64", "3", ")", ")", "(", "var", "operation", ")", "(", "call", "term-number", "(", "var", "thy", ")", "(", "var", "result", ")", ")", ")", ")", "(", "return", "(", "call", "theorem-new"]
theorem step_107 : Agreement point_107 point_108
    componentChars_107 emitted_107 := by
  intro rest priorTokens
  cbv

def emitted_108 : List String := ["(", "var", "thy", ")", "(", "var", "statement", ")", "(", "var", "opcode", ")", ")", ")", ")", ")", "(", "function", "check-fvar-hints", "(", "(", "fvars", "(", "array", "(", "ref", "Symbol", ")", ")", ")", "(", "hints", "(", "array", "u64", ")", ")", "(", "t", "(", "ref", "Term", ")", ")", "(", "cursor", "(", "ref", "HintCursor", ")", ")", ")", "bool", "(", "block", "(", "let", "s", "(", "ref", "Symbol", ")", "(", "field", "(", "var", "t", ")"]
theorem step_108 : Agreement point_108 point_109
    componentChars_108 emitted_108 := by
  intro rest priorTokens
  cbv

def emitted_109 : List String := ["symbol", ")", ")", "(", "if", "(", "eq", "(", "field", "(", "var", "s", ")", "kind", ")", "(", "u64", "1", ")", ")", "(", "block", "(", "if", "(", "ge", "(", "field", "(", "var", "cursor", ")", "position", ")", "(", "length", "(", "var", "hints", ")", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "ne", "(", "var", "s", ")", "(", "index", "(", "var", "fvars", ")", "(", "index", "(", "var", "hints", ")", "(", "field"]
theorem step_109 : Agreement point_109 point_110
    componentChars_109 emitted_109 := by
  intro rest priorTokens
  cbv

def emitted_110 : List String := ["(", "var", "cursor", ")", "position", ")", ")", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "field", "(", "var", "cursor", ")", "position", ")", "(", "add", "(", "field", "(", "var", "cursor", ")", "position", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var"]
theorem step_110 : Agreement point_110 point_111
    componentChars_110 emitted_110 := by
  intro rest priorTokens
  cbv

def emitted_111 : List String := ["t", ")", "args", ")", ")", ")", "(", "block", "(", "if", "(", "not", "(", "call", "check-fvar-hints", "(", "var", "fvars", ")", "(", "var", "hints", ")", "(", "index", "(", "field", "(", "var", "t", ")", "args", ")", "(", "var", "i", ")", ")", "(", "var", "cursor", ")", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64"]
theorem step_111 : Agreement point_111 point_112
    componentChars_111 emitted_111 := by
  intro rest priorTokens
  cbv

def emitted_112 : List String := ["1", ")", ")", ")", ")", ")", "(", "return", "(", "bool", "true", ")", ")", ")", ")", "(", "function", "eta-symbol", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "s", "(", "ref", "Symbol", ")", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "if", "(", "or", "(", "eq", "(", "var", "s", ")", "(", "null", "(", "ref", "Symbol", ")", ")", ")", "(", "gt", "(", "field", "(", "var", "s", ")", "kind", ")", "(", "u64", "1", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")"]
theorem step_112 : Agreement point_112 point_113
    componentChars_112 emitted_112 := by
  intro rest priorTokens
  cbv

def emitted_113 : List String := ["(", "let", "args", "(", "array", "(", "ref", "Term", ")", ")", "(", "new-array", "(", "ref", "Term", ")", "(", "field", "(", "var", "s", ")", "arity", ")", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "field", "(", "var", "s", ")", "arity", ")", ")", "(", "block", "(", "let", "relative", "u64", "(", "sub", "(", "sub", "(", "field", "(", "var", "s", ")", "arity", ")", "(", "u64", "1", ")", ")", "(", "var", "i", ")", ")", ")"]
theorem step_113 : Agreement point_113 point_114
    componentChars_113 emitted_113 := by
  intro rest priorTokens
  cbv

def emitted_114 : List String := ["(", "let", "bvar", "u64", "(", "add", "(", "var", "relative", ")", "(", "index", "(", "field", "(", "var", "s", ")", "binders", ")", "(", "var", "i", ")", ")", ")", ")", "(", "if", "(", "lt", "(", "var", "bvar", ")", "(", "var", "relative", ")", ")", "(", "block", "(", "effect", "(", "call", "free-terms", "(", "var", "args", ")", ")", ")", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "index", "(", "var", "args", ")", "(", "var", "i", ")"]
theorem step_114 : Agreement point_114 point_115
    componentChars_114 emitted_114 := by
  intro rest priorTokens
  cbv

def emitted_115 : List String := [")", "(", "call", "term-bvar", "(", "var", "thy", ")", "(", "var", "bvar", ")", ")", ")", "(", "if", "(", "eq", "(", "index", "(", "var", "args", ")", "(", "var", "i", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "free-terms", "(", "var", "args", ")", ")", ")", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "("]
theorem step_115 : Agreement point_115 point_116
    componentChars_115 emitted_115 := by
  intro rest priorTokens
  cbv

def emitted_116 : List String := ["let", "t", "(", "ref", "Term", ")", "(", "call", "term-app", "(", "var", "s", ")", "(", "var", "args", ")", ")", ")", "(", "effect", "(", "call", "free-terms", "(", "var", "args", ")", ")", ")", "(", "return", "(", "var", "t", ")", ")", ")", ")", "(", "function", "define-constant", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "fvars", "(", "array", "(", "ref", "Symbol", ")", ")", ")", "(", "hints", "(", "array", "u64", ")", ")", "(", "value", "("]
theorem step_116 : Agreement point_116 point_117
    componentChars_116 emitted_116 := by
  intro rest priorTokens
  cbv

def emitted_117 : List String := ["ref", "Term", ")", ")", ")", "Definition", "(", "block", "(", "let", "failure", "Definition", "(", "zero", "Definition", ")", ")", "(", "if", "(", "or", "(", "eq", "(", "var", "value", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "gt", "(", "field", "(", "var", "value", ")", "depth", ")", "(", "u64", "0", ")", ")", ")", "(", "block", "(", "return", "(", "var", "failure", ")", ")", ")", "(", "block", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "("]
theorem step_117 : Agreement point_117 point_118
    componentChars_117 emitted_117 := by
  intro rest priorTokens
  cbv

def emitted_118 : List String := ["while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "var", "fvars", ")", ")", ")", "(", "block", "(", "let", "f", "(", "ref", "Symbol", ")", "(", "index", "(", "var", "fvars", ")", "(", "var", "i", ")", ")", ")", "(", "if", "(", "or", "(", "eq", "(", "var", "f", ")", "(", "null", "(", "ref", "Symbol", ")", ")", ")", "(", "ne", "(", "field", "(", "var", "f", ")", "kind", ")", "(", "u64", "1", ")", ")", ")", "(", "block", "(", "return", "(", "var", "failure", ")", ")", ")", "(", "block", ")", ")"]
theorem step_118 : Agreement point_118 point_119
    componentChars_118 emitted_118 := by
  intro rest priorTokens
  cbv

def emitted_119 : List String := ["(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "var", "hints", ")", ")", ")", "(", "block", "(", "if", "(", "ge", "(", "index", "(", "var", "hints", ")", "(", "var", "i", ")", ")", "(", "length", "(", "var", "fvars", ")", ")", ")", "(", "block", "(", "return", "(", "var", "failure", ")", ")", ")", "(", "block", ")", ")"]
theorem step_119 : Agreement point_119 point_120
    componentChars_119 emitted_119 := by
  intro rest priorTokens
  cbv

def emitted_120 : List String := ["(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "let", "cursor", "(", "ref", "HintCursor", ")", "(", "new", "HintCursor", ")", ")", "(", "let", "valid", "bool", "(", "call", "check-fvar-hints", "(", "var", "fvars", ")", "(", "var", "hints", ")", "(", "var", "value", ")", "(", "var", "cursor", ")", ")", ")", "(", "free", "(", "var", "cursor", ")", ")", "(", "if", "(", "not", "(", "var", "valid", ")", ")", "(", "block", "("]
theorem step_120 : Agreement point_120 point_121
    componentChars_120 emitted_120 := by
  intro rest priorTokens
  cbv

def emitted_121 : List String := ["return", "(", "var", "failure", ")", ")", ")", "(", "block", ")", ")", "(", "let", "binders", "(", "array", "u64", ")", "(", "new-array", "u64", "(", "length", "(", "var", "fvars", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "var", "fvars", ")", ")", ")", "(", "block", "(", "set", "(", "index", "(", "var", "binders", ")", "(", "var", "i", ")", ")", "(", "field", "(", "index", "(", "var"]
theorem step_121 : Agreement point_121 point_122
    componentChars_121 emitted_121 := by
  intro rest priorTokens
  cbv

def emitted_122 : List String := ["fvars", ")", "(", "var", "i", ")", ")", "arity", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "let", "symbol", "(", "ref", "Symbol", ")", "(", "call", "symbol-new", "(", "var", "thy", ")", "(", "u64", "0", ")", "(", "length", "(", "var", "fvars", ")", ")", "(", "var", "binders", ")", ")", ")", "(", "free", "(", "var", "binders", ")", ")", "(", "let", "lhs-args", "(", "array", "(", "ref", "Term", ")", ")", "(", "new-array", "(", "ref"]
theorem step_122 : Agreement point_122 point_123
    componentChars_122 emitted_122 := by
  intro rest priorTokens
  cbv

def emitted_123 : List String := ["Term", ")", "(", "length", "(", "var", "fvars", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "var", "fvars", ")", ")", ")", "(", "block", "(", "set", "(", "index", "(", "var", "lhs-args", ")", "(", "var", "i", ")", ")", "(", "call", "eta-symbol", "(", "var", "thy", ")", "(", "index", "(", "var", "fvars", ")", "(", "var", "i", ")", ")", ")", ")", "(", "if", "(", "eq", "(", "index", "(", "var"]
theorem step_123 : Agreement point_123 point_124
    componentChars_123 emitted_123 := by
  intro rest priorTokens
  cbv

def emitted_124 : List String := ["lhs-args", ")", "(", "var", "i", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "free-terms", "(", "var", "lhs-args", ")", ")", ")", "(", "effect", "(", "call", "symbol-free", "(", "var", "symbol", ")", ")", ")", "(", "return", "(", "var", "failure", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "let", "lhs", "(", "ref"]
theorem step_124 : Agreement point_124 point_125
    componentChars_124 emitted_124 := by
  intro rest priorTokens
  cbv

def emitted_125 : List String := ["Term", ")", "(", "call", "term-app", "(", "var", "symbol", ")", "(", "var", "lhs-args", ")", ")", ")", "(", "effect", "(", "call", "free-terms", "(", "var", "lhs-args", ")", ")", ")", "(", "let", "statement", "(", "ref", "Term", ")", "(", "call", "app2", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "u64", "3", ")", ")", "(", "var", "lhs", ")", "(", "call", "term-retain", "(", "var"]
theorem step_125 : Agreement point_125 point_126
    componentChars_125 emitted_125 := by
  intro rest priorTokens
  cbv

def emitted_126 : List String := ["value", ")", ")", ")", ")", "(", "let", "thm", "(", "ref", "Theorem", ")", "(", "call", "theorem-new", "(", "var", "thy", ")", "(", "var", "statement", ")", "(", "u64", "17", ")", ")", ")", "(", "if", "(", "eq", "(", "var", "thm", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "symbol-free", "(", "var", "symbol", ")", ")", ")", "(", "return", "(", "var", "failure", ")", ")", ")", "(", "block", ")", ")", "(", "let", "result"]
theorem step_126 : Agreement point_126 point_127
    componentChars_126 emitted_126 := by
  intro rest priorTokens
  cbv

def emitted_127 : List String := ["Definition", "(", "zero", "Definition", ")", ")", "(", "set", "(", "field", "(", "var", "result", ")", "symbol", ")", "(", "var", "symbol", ")", ")", "(", "set", "(", "field", "(", "var", "result", ")", "theorem", ")", "(", "var", "thm", ")", ")", "(", "return", "(", "var", "result", ")", ")", ")", ")", "(", "function", "advance-revision", "(", "(", "thy", "(", "ref", "Theory", ")", ")", ")", "unit", "(", "block", "(", "let", "words", "(", "array", "u64", ")", "("]
theorem step_127 : Agreement point_127 point_128
    componentChars_127 emitted_127 := by
  intro rest priorTokens
  cbv

def emitted_128 : List String := ["field", "(", "var", "thy", ")", "revision", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "var", "words", ")", ")", ")", "(", "block", "(", "set", "(", "index", "(", "var", "words", ")", "(", "var", "i", ")", ")", "(", "add", "(", "index", "(", "var", "words", ")", "(", "var", "i", ")", ")", "(", "u64", "1", ")", ")", ")", "(", "if", "(", "ne", "(", "index", "(", "var", "words", ")", "(", "var", "i", ")", ")", "(", "u64", "0", ")", ")", "("]
theorem step_128 : Agreement point_128 point_129
    componentChars_128 emitted_128 := by
  intro rest priorTokens
  cbv

def emitted_129 : List String := ["block", "(", "return", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "let", "grown", "(", "array", "u64", ")", "(", "new-array", "u64", "(", "add", "(", "length", "(", "var", "words", ")", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "set", "(", "index", "(", "var", "grown", ")", "(", "length", "(", "var", "words", ")", ")", ")", "(", "u64", "1", ")", ")", "(", "set", "(", "field", "(", "var", "thy", ")", "revision", ")", "(", "var"]
theorem step_129 : Agreement point_129 point_130
    componentChars_129 emitted_129 := by
  intro rest priorTokens
  cbv

def emitted_130 : List String := ["grown", ")", ")", "(", "free", "(", "var", "words", ")", ")", "(", "return", ")", ")", ")", "(", "function", "admit-theorem", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "thm", "(", "ref", "Theorem", ")", ")", "(", "symbol", "(", "ref", "Symbol", ")", ")", "(", "fvars", "(", "array", "(", "ref", "Symbol", ")", ")", ")", "(", "hints", "(", "array", "u64", ")", ")", ")", "bool", "("]
theorem step_130 : Agreement point_130 point_131
    componentChars_130 emitted_130 := by
  intro rest priorTokens
  cbv

def emitted_131 : List String := ["block", "(", "if", "(", "or", "(", "eq", "(", "var", "thm", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", "(", "ne", "(", "field", "(", "var", "thm", ")", "owner", ")", "(", "var", "thy", ")", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "effect", "(", "call", "advance-revision", "(", "var", "thy", ")", ")", ")", "(", "free", "(", "field", "(", "var", "thm", ")", "revision", ")", ")", "(", "set", "(", "field", "(", "var", "thm", ")"]
theorem step_131 : Agreement point_131 point_132
    componentChars_131 emitted_131 := by
  intro rest priorTokens
  cbv

def emitted_132 : List String := ["revision", ")", "(", "call", "copy-words", "(", "field", "(", "var", "thy", ")", "revision", ")", ")", ")", "(", "let", "admitted", "(", "ref", "Admission", ")", "(", "new", "Admission", ")", ")", "(", "set", "(", "field", "(", "var", "admitted", ")", "kind", ")", "(", "field", "(", "var", "thm", ")", "origin", ")", ")", "(", "set", "(", "field", "(", "var", "admitted", ")", "statement", ")", "(", "call", "term-retain", "(", "field", "(", "var", "thm", ")"]
theorem step_132 : Agreement point_132 point_133
    componentChars_132 emitted_132 := by
  intro rest priorTokens
  cbv

def emitted_133 : List String := ["statement", ")", ")", ")", "(", "set", "(", "field", "(", "var", "admitted", ")", "symbol", ")", "(", "call", "symbol-retain", "(", "var", "symbol", ")", ")", ")", "(", "set", "(", "field", "(", "var", "admitted", ")", "fvars", ")", "(", "new-array", "(", "ref", "Symbol", ")", "(", "length", "(", "var", "fvars", ")", ")", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "var", "fvars", ")", ")", ")", "("]
theorem step_133 : Agreement point_133 point_134
    componentChars_133 emitted_133 := by
  intro rest priorTokens
  cbv

def emitted_134 : List String := ["block", "(", "set", "(", "index", "(", "field", "(", "var", "admitted", ")", "fvars", ")", "(", "var", "i", ")", ")", "(", "call", "symbol-retain", "(", "index", "(", "var", "fvars", ")", "(", "var", "i", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "set", "(", "field", "(", "var", "admitted", ")", "hints", ")", "(", "call", "copy-words", "(", "var", "hints", ")", ")", ")"]
theorem step_134 : Agreement point_134 point_135
    componentChars_134 emitted_134 := by
  intro rest priorTokens
  cbv

def emitted_135 : List String := ["(", "set", "(", "field", "(", "var", "admitted", ")", "revision", ")", "(", "call", "copy-words", "(", "field", "(", "var", "thy", ")", "revision", ")", ")", ")", "(", "set", "(", "field", "(", "var", "admitted", ")", "previous", ")", "(", "field", "(", "var", "thy", ")", "admissions", ")", ")", "(", "set", "(", "field", "(", "var", "thy", ")", "admissions", ")", "(", "var", "admitted", ")", ")", "(", "return", "(", "bool", "true", ")", ")", ")", ")", "(", "function"]
theorem step_135 : Agreement point_135 point_136
    componentChars_135 emitted_135 := by
  intro rest priorTokens
  cbv

def emitted_136 : List String := ["jit-theorem", "(", "(", "thy", "(", "ref", "Theory", ")", ")", "(", "safe", "(", "ref", "Theorem", ")", ")", "(", "physical-status", "(", "ref", "u64", ")", ")", "(", "scope", "(", "ref", "ExecutionScope", ")", ")", ")", "(", "ref", "Theorem", ")", "(", "block", "(", "set", "(", "load", "(", "var", "physical-status", ")", ")", "(", "u64", "0", ")", ")", "(", "if", "(", "or", "(", "eq", "(", "var", "safe", ")", "(", "null", "(", "ref", "Theorem", ")"]
theorem step_136 : Agreement point_136 point_137
    componentChars_136 emitted_136 := by
  intro rest priorTokens
  cbv

def emitted_137 : List String := [")", ")", "(", "ne", "(", "field", "(", "var", "safe", ")", "owner", ")", "(", "var", "thy", ")", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "premise", "(", "ref", "Term", ")", "(", "field", "(", "var", "safe", ")", "statement", ")", ")", "(", "if", "(", "ne", "(", "field", "(", "var", "premise", ")", "symbol", ")", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "u64", "11", ")", ")", ")", "("]
theorem step_137 : Agreement point_137 point_138
    componentChars_137 emitted_137 := by
  intro rest priorTokens
  cbv

def emitted_138 : List String := ["block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "u64", "4", ")", ")", "(", "block", "(", "if", "(", "ne", "(", "field", "(", "index", "(", "field", "(", "var", "premise", ")", "args", ")", "(", "var", "i", ")", ")", "symbol", ")", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "u64", "1", ")"]
theorem step_138 : Agreement point_138 point_139
    componentChars_138 emitted_138 := by
  intro rest priorTokens
  cbv

def emitted_139 : List String := [")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "let", "code", "bytes", "(", "field", "(", "index", "(", "field", "(", "var", "premise", ")", "args", ")", "(", "u64", "0", ")", ")", "literal", ")", ")", "(", "let", "input1", "bytes", "(", "field", "(", "index", "(", "field", "(", "var", "premise", ")", "args", ")"]
theorem step_139 : Agreement point_139 point_140
    componentChars_139 emitted_139 := by
  intro rest priorTokens
  cbv

def emitted_140 : List String := ["(", "u64", "1", ")", ")", "literal", ")", ")", "(", "let", "input2", "bytes", "(", "field", "(", "index", "(", "field", "(", "var", "premise", ")", "args", ")", "(", "u64", "2", ")", ")", "literal", ")", ")", "(", "let", "length-bytes", "bytes", "(", "field", "(", "index", "(", "field", "(", "var", "premise", ")", "args", ")", "(", "u64", "3", ")", ")", "literal", ")", ")", "(", "let", "output-length", "u64", "(", "u64", "0", ")", ")", "(", "if", "(", "eq", "(", "length", "("]
theorem step_140 : Agreement point_140 point_141
    componentChars_140 emitted_140 := by
  intro rest priorTokens
  cbv

def emitted_141 : List String := ["var", "length-bytes", ")", ")", "(", "u64", "1", ")", ")", "(", "block", "(", "set", "(", "var", "output-length", ")", "(", "to-u64", "(", "index", "(", "var", "length-bytes", ")", "(", "u64", "0", ")", ")", ")", ")", ")", "(", "block", "(", "if", "(", "ne", "(", "length", "(", "var", "length-bytes", ")", ")", "(", "u64", "8", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "("]
theorem step_141 : Agreement point_141 point_142
    componentChars_141 emitted_141 := by
  intro rest priorTokens
  cbv

def emitted_142 : List String := ["set", "(", "var", "i", ")", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "u64", "8", ")", ")", "(", "block", "(", "set", "(", "var", "output-length", ")", "(", "bor", "(", "var", "output-length", ")", "(", "shl", "(", "to-u64", "(", "index", "(", "var", "length-bytes", ")", "(", "var", "i", ")", ")", ")", "(", "mul", "(", "var", "i", ")", "(", "u64", "8", ")", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")"]
theorem step_142 : Agreement point_142 point_143
    componentChars_142 emitted_142 := by
  intro rest priorTokens
  cbv

def emitted_143 : List String := ["(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "if", "(", "ge", "(", "var", "output-length", ")", "(", "u64", "256", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", ")", ")", "(", "if", "(", "lt", "(", "add", "(", "var", "output-length", ")", "(", "u64", "8", ")", ")", "(", "var", "output-length", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "("]
theorem step_143 : Agreement point_143 point_144
    componentChars_143 emitted_143 := by
  intro rest priorTokens
  cbv

def emitted_144 : List String := ["block", ")", ")", "(", "let", "observation", "(", "ref", "Observation", ")", "(", "null", "(", "ref", "Observation", ")", ")", ")", "(", "let", "status", "u64", "(", "call", "execute-native", "(", "var", "scope", ")", "(", "var", "code", ")", "(", "var", "input1", ")", "(", "var", "input2", ")", "(", "var", "output-length", ")", "(", "address", "(", "var", "observation", ")", ")", ")", ")"]
theorem step_144 : Agreement point_144 point_145
    componentChars_144 emitted_144 := by
  intro rest priorTokens
  cbv

def emitted_145 : List String := ["(", "if", "(", "ne", "(", "var", "status", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "set", "(", "load", "(", "var", "physical-status", ")", ")", "(", "var", "status", ")", ")", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "output", "bytes", "(", "call", "execution-output", "(", "var", "scope", ")", "(", "var", "observation", ")", ")", ")", "(", "if", "(", "or", "(", "ne", "("]
theorem step_145 : Agreement point_145 point_146
    componentChars_145 emitted_145 := by
  intro rest priorTokens
  cbv

def emitted_146 : List String := ["length", "(", "var", "output", ")", ")", "(", "var", "output-length", ")", ")", "(", "not", "(", "call", "execution-matches", "(", "var", "scope", ")", "(", "var", "observation", ")", "(", "var", "code", ")", "(", "var", "input1", ")", "(", "var", "input2", ")", "(", "var", "output", ")", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "execution-free", "(", "var", "scope", ")", "(", "var"]
theorem step_146 : Agreement point_146 point_147
    componentChars_146 emitted_146 := by
  intro rest priorTokens
  cbv

def emitted_147 : List String := ["observation", ")", ")", ")", "(", "set", "(", "load", "(", "var", "physical-status", ")", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "args", "(", "array", "(", "ref", "Term", ")", ")", "(", "new-array", "(", "ref", "Term", ")", "(", "u64", "4", ")", ")", ")", "(", "set", "(", "index", "(", "var", "args", ")", "(", "u64", "0", ")", ")", "(", "index", "(", "field", "(", "var", "premise", ")"]
theorem step_147 : Agreement point_147 point_148
    componentChars_147 emitted_147 := by
  intro rest priorTokens
  cbv

def emitted_148 : List String := ["args", ")", "(", "u64", "0", ")", ")", ")", "(", "set", "(", "index", "(", "var", "args", ")", "(", "u64", "1", ")", ")", "(", "index", "(", "field", "(", "var", "premise", ")", "args", ")", "(", "u64", "1", ")", ")", ")", "(", "set", "(", "index", "(", "var", "args", ")", "(", "u64", "2", ")", ")", "(", "index", "(", "field", "(", "var", "premise", ")", "args", ")", "(", "u64", "2", ")", ")", ")", "(", "let", "output-term", "(", "ref", "Term", ")", "(", "call", "term-literal", "(", "var", "thy", ")", "(", "var", "output", ")", ")", ")"]
theorem step_148 : Agreement point_148 point_149
    componentChars_148 emitted_148 := by
  intro rest priorTokens
  cbv

def emitted_149 : List String := ["(", "set", "(", "index", "(", "var", "args", ")", "(", "u64", "3", ")", ")", "(", "var", "output-term", ")", ")", "(", "let", "statement", "(", "ref", "Term", ")", "(", "call", "term-app", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "u64", "12", ")", ")", "(", "var", "args", ")", ")", ")", "(", "free", "(", "var", "args", ")", ")", "(", "effect", "(", "call", "term-free", "(", "var", "output-term", ")", ")", ")", "(", "let", "thm", "(", "ref"]
theorem step_149 : Agreement point_149 point_150
    componentChars_149 emitted_149 := by
  intro rest priorTokens
  cbv

def emitted_150 : List String := ["Theorem", ")", "(", "call", "theorem-new", "(", "var", "thy", ")", "(", "var", "statement", ")", "(", "u64", "25", ")", ")", ")", "(", "if", "(", "eq", "(", "var", "thm", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "execution-free", "(", "var", "scope", ")", "(", "var", "observation", ")", ")", ")", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "("]
theorem step_150 : Agreement point_150 point_151
    componentChars_150 emitted_150 := by
  intro rest priorTokens
  cbv

def emitted_151 : List String := ["field", "(", "var", "thm", ")", "observation", ")", "(", "var", "observation", ")", ")", "(", "set", "(", "field", "(", "var", "thm", ")", "execution-scope", ")", "(", "var", "scope", ")", ")", "(", "set", "(", "field", "(", "var", "thm", ")", "execution-premise", ")", "(", "call", "term-retain", "(", "var", "premise", ")", ")", ")", "(", "return", "(", "var", "thm", ")", ")", ")", ")", "(", "function", "measure-initial", "(", ")", "(", "ref", "Measure", ")"]
theorem step_151 : Agreement point_151 point_152
    componentChars_151 emitted_151 := by
  intro rest priorTokens
  cbv

def emitted_152 : List String := ["(", "block", "(", "let", "m", "(", "ref", "Measure", ")", "(", "new", "Measure", ")", ")", "(", "set", "(", "field", "(", "var", "m", ")", "capacities", ")", "(", "new-array", "u64", "(", "u64", "4", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "m", ")", "capacities", ")", "(", "u64", "0", ")", ")", "(", "u64", "13", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "m", ")", "capacities", ")", "(", "u64", "1", ")", ")", "(", "u64", "1", ")", ")", "(", "set", "("]
theorem step_152 : Agreement point_152 point_153
    componentChars_152 emitted_152 := by
  intro rest priorTokens
  cbv

def emitted_153 : List String := ["index", "(", "field", "(", "var", "m", ")", "capacities", ")", "(", "u64", "2", ")", ")", "(", "u64", "1", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "m", ")", "capacities", ")", "(", "u64", "3", ")", ")", "(", "u64", "1", ")", ")", "(", "set", "(", "field", "(", "var", "m", ")", "words", ")", "(", "u64", "1", ")", ")", "(", "set", "(", "field", "(", "var", "m", ")", "terms", ")", "(", "u64", "1", ")", ")", "(", "set", "(", "field", "(", "var", "m", ")", "symbols", ")", "(", "u64", "1", ")", ")", "(", "return", "("]
theorem step_153 : Agreement point_153 point_154
    componentChars_153 emitted_153 := by
  intro rest priorTokens
  cbv

def emitted_154 : List String := ["var", "m", ")", ")", ")", ")", "(", "function", "measure-slot", "(", "(", "m", "(", "ref", "Measure", ")", ")", "(", "space", "u64", ")", "(", "index", "u64", ")", ")", "unit", "(", "block", "(", "if", "(", "eq", "(", "var", "index", ")", "(", "u64", "18446744073709551615", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "m", ")", "error", ")", "(", "u64", "10", ")", ")", "(", "return", ")", ")", "(", "block", ")", ")", "(", "if", "(", "ge", "(", "var", "index", ")", "(", "index", "("]
theorem step_154 : Agreement point_154 point_155
    componentChars_154 emitted_154 := by
  intro rest priorTokens
  cbv

def emitted_155 : List String := ["field", "(", "var", "m", ")", "capacities", ")", "(", "var", "space", ")", ")", ")", "(", "block", "(", "set", "(", "index", "(", "field", "(", "var", "m", ")", "capacities", ")", "(", "var", "space", ")", ")", "(", "add", "(", "var", "index", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "block", ")", ")", "(", "return", ")", ")", ")", "(", "function", "measure-list", "(", "(", "m", "(", "ref", "Measure", ")", ")", "(", "record", "(", "ref", "BinaryRecord", ")", ")"]
theorem step_155 : Agreement point_155 point_156
    componentChars_155 emitted_155 := by
  intro rest priorTokens
  cbv

def emitted_156 : List String := ["(", "operand", "u64", ")", "(", "space", "u64", ")", ")", "unit", "(", "block", "(", "let", "count", "u64", "(", "call", "record-count", "(", "var", "record", ")", "(", "var", "operand", ")", ")", ")", "(", "let", "position", "u64", "(", "u64", "0", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "let", "slot", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "var", "count", ")", ")"]
theorem step_156 : Agreement point_156 point_157
    componentChars_156 emitted_156 := by
  intro rest priorTokens
  cbv

def emitted_157 : List String := ["(", "block", "(", "if", "(", "not", "(", "call", "record-next-word", "(", "var", "record", ")", "(", "var", "operand", ")", "(", "address", "(", "var", "position", ")", ")", "(", "address", "(", "var", "slot", ")", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "m", ")", "error", ")", "(", "u64", "9", ")", ")", "(", "return", ")", ")", "(", "block", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "var", "space", ")"]
theorem step_157 : Agreement point_157 point_158
    componentChars_157 emitted_157 := by
  intro rest priorTokens
  cbv

def emitted_158 : List String := ["(", "var", "slot", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "return", ")", ")", ")", "(", "function", "measure-step", "(", "(", "m", "(", "ref", "Measure", ")", ")", "(", "record", "(", "ref", "BinaryRecord", ")", ")", ")", "bool", "(", "block", "(", "if", "(", "ne", "(", "field", "(", "var", "m", ")", "error", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")"]
theorem step_158 : Agreement point_158 point_159
    componentChars_158 emitted_158 := by
  intro rest priorTokens
  cbv

def emitted_159 : List String := ["(", "switch", "(", "call", "record-opcode", "(", "var", "record", ")", ")", "(", "case", "0", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "0", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "case", "1", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "0", ")", "(", "call"]
theorem step_159 : Agreement point_159 point_160
    componentChars_159 emitted_159 := by
  intro rest priorTokens
  cbv

def emitted_160 : List String := ["record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "let", "n0", "u64", "(", "call", "record-count", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", "(", "if", "(", "gt", "(", "var", "n0", ")", "(", "field", "(", "var", "m", ")", "words", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "m", ")", "words", ")", "(", "var", "n0", ")", ")", ")", "(", "block", ")", ")", ")", ")", "(", "case", "2", "(", "block", "(", "effect", "("]
theorem step_160 : Agreement point_160 point_161
    componentChars_160 emitted_160 := by
  intro rest priorTokens
  cbv

def emitted_161 : List String := ["call", "measure-slot", "(", "var", "m", ")", "(", "u64", "0", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "0", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "case", "3", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64"]
theorem step_161 : Agreement point_161 point_162
    componentChars_161 emitted_161 := by
  intro rest priorTokens
  cbv

def emitted_162 : List String := ["0", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", ")", ")", "(", "case", "4", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "case", "5", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "("]
theorem step_162 : Agreement point_162 point_163
    componentChars_162 emitted_162 := by
  intro rest priorTokens
  cbv

def emitted_163 : List String := ["u64", "1", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "case", "6", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "0", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call", "record-word", "(", "var"]
theorem step_163 : Agreement point_163 point_164
    componentChars_163 emitted_163 := by
  intro rest priorTokens
  cbv

def emitted_164 : List String := ["record", ")", "(", "u64", "2", ")", ")", ")", ")", "(", "let", "n1", "u64", "(", "call", "record-count", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", "(", "if", "(", "gt", "(", "var", "n1", ")", "(", "field", "(", "var", "m", ")", "terms", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "m", ")", "terms", ")", "(", "var", "n1", ")", ")", ")", "(", "block", ")", ")", "(", "effect", "(", "call", "measure-list", "(", "var", "m", ")", "(", "var", "record", ")", "(", "u64", "1", ")", "(", "u64", "1", ")", ")"]
theorem step_164 : Agreement point_164 point_165
    componentChars_164 emitted_164 := by
  intro rest priorTokens
  cbv

def emitted_165 : List String := [")", ")", ")", "(", "case", "7", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "case", "8", "("]
theorem step_165 : Agreement point_165 point_166
    componentChars_165 emitted_165 := by
  intro rest priorTokens
  cbv

def emitted_166 : List String := ["block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", ")", ")", "(", "case", "9", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call"]
theorem step_166 : Agreement point_166 point_167
    componentChars_166 emitted_166 := by
  intro rest priorTokens
  cbv

def emitted_167 : List String := ["measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "case", "10", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call"]
theorem step_167 : Agreement point_167 point_168
    componentChars_167 emitted_167 := by
  intro rest priorTokens
  cbv

def emitted_168 : List String := ["record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "case", "11", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", ")", ")", "(", "case", "12", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "("]
theorem step_168 : Agreement point_168 point_169
    componentChars_168 emitted_168 := by
  intro rest priorTokens
  cbv

def emitted_169 : List String := ["call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "case", "13", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call", "record-word", "(", "var", "record", ")", "("]
theorem step_169 : Agreement point_169 point_170
    componentChars_169 emitted_169 := by
  intro rest priorTokens
  cbv

def emitted_170 : List String := ["u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "3", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "case", "14", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "3", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "effect", "("]
theorem step_170 : Agreement point_170 point_171
    componentChars_170 emitted_170 := by
  intro rest priorTokens
  cbv

def emitted_171 : List String := ["call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "case", "15", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")"]
theorem step_171 : Agreement point_171 point_172
    componentChars_171 emitted_171 := by
  intro rest priorTokens
  cbv

def emitted_172 : List String := ["(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", ")", ")", ")", ")", "(", "case", "16", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")"]
theorem step_172 : Agreement point_172 point_173
    componentChars_172 emitted_172 := by
  intro rest priorTokens
  cbv

def emitted_173 : List String := ["(", "u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "0", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "("]
theorem step_173 : Agreement point_173 point_174
    componentChars_173 emitted_173 := by
  intro rest priorTokens
  cbv

def emitted_174 : List String := ["call", "record-word", "(", "var", "record", ")", "(", "u64", "3", ")", ")", ")", ")", ")", ")", "(", "case", "17", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "0", ")", "(", "call", "record-word", "(", "var", "record", ")", "("]
theorem step_174 : Agreement point_174 point_175
    componentChars_174 emitted_174 := by
  intro rest priorTokens
  cbv

def emitted_175 : List String := ["u64", "3", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "4", ")", ")", ")", ")", "(", "let", "n0", "u64", "(", "call", "record-count", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", "(", "if", "(", "gt", "(", "var", "n0", ")", "(", "field", "(", "var", "m", ")", "symbols", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "m", ")", "symbols", ")"]
theorem step_175 : Agreement point_175 point_176
    componentChars_175 emitted_175 := by
  intro rest priorTokens
  cbv

def emitted_176 : List String := ["(", "var", "n0", ")", ")", ")", "(", "block", ")", ")", "(", "let", "n1", "u64", "(", "call", "record-count", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", "(", "if", "(", "gt", "(", "var", "n1", ")", "(", "field", "(", "var", "m", ")", "words", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "m", ")", "words", ")", "(", "var", "n1", ")", ")", ")", "(", "block", ")", ")", "(", "effect", "(", "call", "measure-list", "(", "var", "m", ")", "(", "var", "record", ")", "(", "u64", "0", ")", "("]
theorem step_176 : Agreement point_176 point_177
    componentChars_176 emitted_176 := by
  intro rest priorTokens
  cbv

def emitted_177 : List String := ["u64", "0", ")", ")", ")", ")", ")", "(", "case", "18", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "case", "19", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")"]
theorem step_177 : Agreement point_177 point_178
    componentChars_177 emitted_177 := by
  intro rest priorTokens
  cbv

def emitted_178 : List String := ["(", "u64", "2", ")", ")", ")", ")", ")", ")", "(", "case", "20", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", ")", ")", ")", ")", "(", "case", "21", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var"]
theorem step_178 : Agreement point_178 point_179
    componentChars_178 emitted_178 := by
  intro rest priorTokens
  cbv

def emitted_179 : List String := ["record", ")", "(", "u64", "2", ")", ")", ")", ")", ")", ")", "(", "case", "22", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", ")", ")", ")", ")", "(", "case", "23", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call", "record-word", "("]
theorem step_179 : Agreement point_179 point_180
    componentChars_179 emitted_179 := by
  intro rest priorTokens
  cbv

def emitted_180 : List String := ["var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", "(", "case", "24", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "("]
theorem step_180 : Agreement point_180 point_181
    componentChars_180 emitted_180 := by
  intro rest priorTokens
  cbv

def emitted_181 : List String := ["effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", ")", ")", ")", ")", "(", "case", "25", "(", "block", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var"]
theorem step_181 : Agreement point_181 point_182
    componentChars_181 emitted_181 := by
  intro rest priorTokens
  cbv

def emitted_182 : List String := ["m", ")", "(", "u64", "2", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "effect", "(", "call", "measure-slot", "(", "var", "m", ")", "(", "u64", "1", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", ")", ")", ")", ")", "(", "default", "(", "block", "(", "set", "(", "field", "(", "var", "m", ")", "error", ")", "(", "u64", "9", ")", ")", ")", ")", ")", "(", "return", "(", "eq", "(", "field", "(", "var", "m", ")"]
theorem step_182 : Agreement point_182 point_183
    componentChars_182 emitted_182 := by
  intro rest priorTokens
  cbv

def emitted_183 : List String := ["error", ")", "(", "u64", "0", ")", ")", ")", ")", ")", "(", "function", "protocol-initial", "(", "(", "m", "(", "ref", "Measure", ")", ")", "(", "scope", "(", "ref", "ExecutionScope", ")", ")", ")", "(", "ref", "Protocol", ")", "(", "block", "(", "if", "(", "ne", "(", "field", "(", "var", "m", ")", "error", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "return", "(", "null", "(", "ref", "Protocol", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "s", "(", "ref", "Protocol", ")", "(", "new"]
theorem step_183 : Agreement point_183 point_184
    componentChars_183 emitted_183 := by
  intro rest priorTokens
  cbv

def emitted_184 : List String := ["Protocol", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "execution-scope", ")", "(", "var", "scope", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "call", "theory-initial", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "symbols", ")", "(", "new-array", "(", "ref", "Symbol", ")", "(", "index", "(", "field", "(", "var", "m", ")", "capacities", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "terms", ")", "("]
theorem step_184 : Agreement point_184 point_185
    componentChars_184 emitted_184 := by
  intro rest priorTokens
  cbv

def emitted_185 : List String := ["new-array", "(", "ref", "Term", ")", "(", "index", "(", "field", "(", "var", "m", ")", "capacities", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "theorems", ")", "(", "new-array", "(", "ref", "Theorem", ")", "(", "index", "(", "field", "(", "var", "m", ")", "capacities", ")", "(", "u64", "2", ")", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "challenges", ")", "(", "new-array", "(", "ref", "Term", ")", "(", "index", "(", "field", "(", "var", "m", ")"]
theorem step_185 : Agreement point_185 point_186
    componentChars_185 emitted_185 := by
  intro rest priorTokens
  cbv

def emitted_186 : List String := ["capacities", ")", "(", "u64", "3", ")", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "aux-words", ")", "(", "new-array", "u64", "(", "field", "(", "var", "m", ")", "words", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "aux-terms", ")", "(", "new-array", "(", "ref", "Term", ")", "(", "field", "(", "var", "m", ")", "terms", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "aux-symbols", ")", "(", "new-array", "(", "ref", "Symbol", ")", "(", "field", "(", "var", "m", ")"]
theorem step_186 : Agreement point_186 point_187
    componentChars_186 emitted_186 := by
  intro rest priorTokens
  cbv

def emitted_187 : List String := ["symbols", ")", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "u64", "13", ")", ")", "(", "block", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "symbols", ")", "(", "var", "i", ")", ")", "(", "index", "(", "field", "(", "field", "(", "var", "s", ")", "theory", ")", "builtins", ")", "(", "var", "i", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64"]
theorem step_187 : Agreement point_187 point_188
    componentChars_187 emitted_187 := by
  intro rest priorTokens
  cbv

def emitted_188 : List String := ["1", ")", ")", ")", ")", ")", "(", "return", "(", "var", "s", ")", ")", ")", ")", "(", "function", "protocol-enter-proof", "(", "(", "s", "(", "ref", "Protocol", ")", ")", ")", "bool", "(", "block", "(", "if", "(", "or", "(", "field", "(", "var", "s", ")", "proof", ")", "(", "ne", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "0", ")", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "("]
theorem step_188 : Agreement point_188 point_189
    componentChars_188 emitted_188 := by
  intro rest priorTokens
  cbv

def emitted_189 : List String := ["while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "challenges", ")", ")", ")", "(", "block", "(", "if", "(", "ne", "(", "index", "(", "field", "(", "var", "s", ")", "challenges", ")", "(", "var", "i", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "initial", ")", "(", "add", "(", "field", "(", "var", "s", ")", "initial", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "block", ")", ")"]
theorem step_189 : Agreement point_189 point_190
    componentChars_189 emitted_189 := by
  intro rest priorTokens
  cbv

def emitted_190 : List String := ["(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "proof", ")", "(", "bool", "true", ")", ")", "(", "return", "(", "bool", "true", ")", ")", ")", ")", "(", "function", "protocol-words", "(", "(", "s", "(", "ref", "Protocol", ")", ")", "(", "record", "(", "ref", "BinaryRecord", ")", ")", "(", "operand", "u64", ")", ")", "(", "array", "u64", ")", "(", "block", "(", "let", "count", "u64", "(", "call"]
theorem step_190 : Agreement point_190 point_191
    componentChars_190 emitted_190 := by
  intro rest priorTokens
  cbv

def emitted_191 : List String := ["record-count", "(", "var", "record", ")", "(", "var", "operand", ")", ")", ")", "(", "if", "(", "gt", "(", "var", "count", ")", "(", "length", "(", "field", "(", "var", "s", ")", "aux-words", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "zero", "(", "array", "u64", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "words", "(", "array", "u64", ")", "(", "slice", "(", "field", "(", "var", "s", ")", "aux-words", ")", "("]
theorem step_191 : Agreement point_191 point_192
    componentChars_191 emitted_191 := by
  intro rest priorTokens
  cbv

def emitted_192 : List String := ["u64", "0", ")", "(", "var", "count", ")", ")", ")", "(", "let", "position", "u64", "(", "u64", "0", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "var", "count", ")", ")", "(", "block", "(", "if", "(", "not", "(", "call", "record-next-word", "(", "var", "record", ")", "(", "var", "operand", ")", "(", "address", "(", "var", "position", ")", ")"]
theorem step_192 : Agreement point_192 point_193
    componentChars_192 emitted_192 := by
  intro rest priorTokens
  cbv

def emitted_193 : List String := ["(", "address", "(", "index", "(", "var", "words", ")", "(", "var", "i", ")", ")", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "9", ")", ")", "(", "return", "(", "zero", "(", "array", "u64", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "return", "(", "var", "words", ")", ")", ")", ")", "(", "function", "get-symbols", "(", "(", "s", "(", "ref"]
theorem step_193 : Agreement point_193 point_194
    componentChars_193 emitted_193 := by
  intro rest priorTokens
  cbv

def emitted_194 : List String := ["Protocol", ")", ")", "(", "i", "u64", ")", ")", "(", "ref", "Symbol", ")", "(", "block", "(", "if", "(", "ge", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "symbols", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "null", "(", "ref", "Symbol", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "value", "(", "ref", "Symbol", ")", "(", "index", "(", "field", "(", "var", "s", ")", "symbols", ")", "(", "var", "i", ")"]
theorem step_194 : Agreement point_194 point_195
    componentChars_194 emitted_194 := by
  intro rest priorTokens
  cbv

def emitted_195 : List String := [")", ")", "(", "if", "(", "eq", "(", "var", "value", ")", "(", "null", "(", "ref", "Symbol", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "2", ")", ")", ")", "(", "block", ")", ")", "(", "return", "(", "var", "value", ")", ")", ")", ")", "(", "function", "put-symbols", "(", "(", "s", "(", "ref", "Protocol", ")", ")", "(", "i", "u64", ")", "(", "value", "(", "ref", "Symbol", ")", ")", ")", "bool", "(", "block", "(", "if", "(", "ne", "(", "field", "("]
theorem step_195 : Agreement point_195 point_196
    componentChars_195 emitted_195 := by
  intro rest priorTokens
  cbv

def emitted_196 : List String := ["var", "s", ")", "error", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "effect", "(", "call", "symbol-free", "(", "var", "value", ")", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "eq", "(", "var", "value", ")", "(", "null", "(", "ref", "Symbol", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "7", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "ge", "(", "var"]
theorem step_196 : Agreement point_196 point_197
    componentChars_196 emitted_196 := by
  intro rest priorTokens
  cbv

def emitted_197 : List String := ["i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "symbols", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "symbol-free", "(", "var", "value", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "ne", "(", "index", "(", "field", "(", "var", "s", ")", "symbols", ")", "(", "var", "i", ")", ")", "(", "null", "(", "ref", "Symbol", ")", ")", ")"]
theorem step_197 : Agreement point_197 point_198
    componentChars_197 emitted_197 := by
  intro rest priorTokens
  cbv

def emitted_198 : List String := ["(", "block", "(", "effect", "(", "call", "symbol-free", "(", "var", "value", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "3", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "symbols", ")", "(", "var", "i", ")", ")", "(", "var", "value", ")", ")", "(", "return", "(", "bool", "true", ")", ")", ")", ")", "(", "function", "get-terms", "(", "(", "s", "("]
theorem step_198 : Agreement point_198 point_199
    componentChars_198 emitted_198 := by
  intro rest priorTokens
  cbv

def emitted_199 : List String := ["ref", "Protocol", ")", ")", "(", "i", "u64", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "if", "(", "ge", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "terms", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "value", "(", "ref", "Term", ")", "(", "index", "(", "field", "(", "var", "s", ")", "terms", ")", "(", "var", "i", ")", ")", ")"]
theorem step_199 : Agreement point_199 point_200
    componentChars_199 emitted_199 := by
  intro rest priorTokens
  cbv

def emitted_200 : List String := ["(", "if", "(", "eq", "(", "var", "value", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "2", ")", ")", ")", "(", "block", ")", ")", "(", "return", "(", "var", "value", ")", ")", ")", ")", "(", "function", "put-terms", "(", "(", "s", "(", "ref", "Protocol", ")", ")", "(", "i", "u64", ")", "(", "value", "(", "ref", "Term", ")", ")", ")", "bool", "(", "block", "(", "if", "(", "ne", "(", "field", "(", "var", "s", ")", "error", ")", "("]
theorem step_200 : Agreement point_200 point_201
    componentChars_200 emitted_200 := by
  intro rest priorTokens
  cbv

def emitted_201 : List String := ["u64", "0", ")", ")", "(", "block", "(", "effect", "(", "call", "term-free", "(", "var", "value", ")", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "eq", "(", "var", "value", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "7", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "ge", "(", "var", "i", ")", "(", "length", "("]
theorem step_201 : Agreement point_201 point_202
    componentChars_201 emitted_201 := by
  intro rest priorTokens
  cbv

def emitted_202 : List String := ["field", "(", "var", "s", ")", "terms", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "term-free", "(", "var", "value", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "ne", "(", "index", "(", "field", "(", "var", "s", ")", "terms", ")", "(", "var", "i", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "effect", "(", "call"]
theorem step_202 : Agreement point_202 point_203
    componentChars_202 emitted_202 := by
  intro rest priorTokens
  cbv

def emitted_203 : List String := ["term-free", "(", "var", "value", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "3", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "terms", ")", "(", "var", "i", ")", ")", "(", "var", "value", ")", ")", "(", "return", "(", "bool", "true", ")", ")", ")", ")", "(", "function", "get-theorems", "(", "(", "s", "(", "ref", "Protocol", ")", ")", "(", "i", "u64", ")", ")", "(", "ref"]
theorem step_203 : Agreement point_203 point_204
    componentChars_203 emitted_203 := by
  intro rest priorTokens
  cbv

def emitted_204 : List String := ["Theorem", ")", "(", "block", "(", "if", "(", "ge", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "theorems", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "value", "(", "ref", "Theorem", ")", "(", "index", "(", "field", "(", "var", "s", ")", "theorems", ")", "(", "var", "i", ")", ")", ")", "(", "if", "(", "eq", "("]
theorem step_204 : Agreement point_204 point_205
    componentChars_204 emitted_204 := by
  intro rest priorTokens
  cbv

def emitted_205 : List String := ["var", "value", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "2", ")", ")", ")", "(", "block", ")", ")", "(", "return", "(", "var", "value", ")", ")", ")", ")", "(", "function", "put-theorems", "(", "(", "s", "(", "ref", "Protocol", ")", ")", "(", "i", "u64", ")", "(", "value", "(", "ref", "Theorem", ")", ")", ")", "bool", "(", "block", "(", "if", "(", "ne", "(", "field", "(", "var", "s", ")", "error", ")", "("]
theorem step_205 : Agreement point_205 point_206
    componentChars_205 emitted_205 := by
  intro rest priorTokens
  cbv

def emitted_206 : List String := ["u64", "0", ")", ")", "(", "block", "(", "effect", "(", "call", "theorem-free", "(", "var", "value", ")", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "eq", "(", "var", "value", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "7", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "ge", "(", "var", "i", ")", "(", "length", "("]
theorem step_206 : Agreement point_206 point_207
    componentChars_206 emitted_206 := by
  intro rest priorTokens
  cbv

def emitted_207 : List String := ["field", "(", "var", "s", ")", "theorems", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "theorem-free", "(", "var", "value", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "ne", "(", "index", "(", "field", "(", "var", "s", ")", "theorems", ")", "(", "var", "i", ")", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", "(", "block"]
theorem step_207 : Agreement point_207 point_208
    componentChars_207 emitted_207 := by
  intro rest priorTokens
  cbv

def emitted_208 : List String := ["(", "effect", "(", "call", "theorem-free", "(", "var", "value", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "3", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "theorems", ")", "(", "var", "i", ")", ")", "(", "var", "value", ")", ")", "(", "return", "(", "bool", "true", ")", ")", ")", ")", "(", "function", "get-challenges", "(", "(", "s", "(", "ref"]
theorem step_208 : Agreement point_208 point_209
    componentChars_208 emitted_208 := by
  intro rest priorTokens
  cbv

def emitted_209 : List String := ["Protocol", ")", ")", "(", "i", "u64", ")", ")", "(", "ref", "Term", ")", "(", "block", "(", "if", "(", "ge", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "challenges", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "value", "(", "ref", "Term", ")", "(", "index", "(", "field", "(", "var", "s", ")", "challenges", ")", "(", "var"]
theorem step_209 : Agreement point_209 point_210
    componentChars_209 emitted_209 := by
  intro rest priorTokens
  cbv

def emitted_210 : List String := ["i", ")", ")", ")", "(", "if", "(", "eq", "(", "var", "value", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "2", ")", ")", ")", "(", "block", ")", ")", "(", "return", "(", "var", "value", ")", ")", ")", ")", "(", "function", "protocol-terms", "(", "(", "s", "(", "ref", "Protocol", ")", ")", "(", "record", "(", "ref", "BinaryRecord", ")", ")", "(", "operand", "u64", ")", ")", "(", "array", "(", "ref", "Term", ")", ")", "("]
theorem step_210 : Agreement point_210 point_211
    componentChars_210 emitted_210 := by
  intro rest priorTokens
  cbv

def emitted_211 : List String := ["block", "(", "let", "count", "u64", "(", "call", "record-count", "(", "var", "record", ")", "(", "var", "operand", ")", ")", ")", "(", "if", "(", "gt", "(", "var", "count", ")", "(", "length", "(", "field", "(", "var", "s", ")", "aux-terms", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "zero", "(", "array", "(", "ref", "Term", ")", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "values", "(", "array"]
theorem step_211 : Agreement point_211 point_212
    componentChars_211 emitted_211 := by
  intro rest priorTokens
  cbv

def emitted_212 : List String := ["(", "ref", "Term", ")", ")", "(", "slice", "(", "field", "(", "var", "s", ")", "aux-terms", ")", "(", "u64", "0", ")", "(", "var", "count", ")", ")", ")", "(", "let", "position", "u64", "(", "u64", "0", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "let", "slot", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "var", "count", ")", ")", "(", "block", "(", "if", "(", "not", "(", "call", "record-next-word", "(", "var", "record", ")", "(", "var"]
theorem step_212 : Agreement point_212 point_213
    componentChars_212 emitted_212 := by
  intro rest priorTokens
  cbv

def emitted_213 : List String := ["operand", ")", "(", "address", "(", "var", "position", ")", ")", "(", "address", "(", "var", "slot", ")", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "9", ")", ")", "(", "return", "(", "zero", "(", "array", "(", "ref", "Term", ")", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "index", "(", "var", "values", ")", "(", "var", "i", ")", ")", "(", "call", "get-terms", "(", "var", "s", ")", "(", "var", "slot", ")", ")", ")", "(", "set", "("]
theorem step_213 : Agreement point_213 point_214
    componentChars_213 emitted_213 := by
  intro rest priorTokens
  cbv

def emitted_214 : List String := ["var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "return", "(", "var", "values", ")", ")", ")", ")", "(", "function", "protocol-symbols", "(", "(", "s", "(", "ref", "Protocol", ")", ")", "(", "record", "(", "ref", "BinaryRecord", ")", ")", "(", "operand", "u64", ")", ")", "(", "array", "(", "ref", "Symbol", ")", ")", "(", "block", "(", "let", "count", "u64", "(", "call", "record-count", "(", "var", "record", ")", "(", "var", "operand", ")", ")", ")"]
theorem step_214 : Agreement point_214 point_215
    componentChars_214 emitted_214 := by
  intro rest priorTokens
  cbv

def emitted_215 : List String := ["(", "if", "(", "gt", "(", "var", "count", ")", "(", "length", "(", "field", "(", "var", "s", ")", "aux-symbols", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "zero", "(", "array", "(", "ref", "Symbol", ")", ")", ")", ")", ")", "(", "block", ")", ")", "(", "let", "values", "(", "array", "(", "ref", "Symbol", ")", ")", "(", "slice", "(", "field", "(", "var", "s", ")", "aux-symbols", ")", "(", "u64", "0", ")", "(", "var", "count", ")", ")", ")"]
theorem step_215 : Agreement point_215 point_216
    componentChars_215 emitted_215 := by
  intro rest priorTokens
  cbv

def emitted_216 : List String := ["(", "let", "position", "u64", "(", "u64", "0", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "let", "slot", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "var", "count", ")", ")", "(", "block", "(", "if", "(", "not", "(", "call", "record-next-word", "(", "var", "record", ")", "(", "var", "operand", ")", "(", "address", "(", "var", "position", ")", ")", "(", "address", "(", "var", "slot", ")", ")", ")", ")"]
theorem step_216 : Agreement point_216 point_217
    componentChars_216 emitted_216 := by
  intro rest priorTokens
  cbv

def emitted_217 : List String := ["(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "9", ")", ")", "(", "return", "(", "zero", "(", "array", "(", "ref", "Symbol", ")", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "index", "(", "var", "values", ")", "(", "var", "i", ")", ")", "(", "call", "get-symbols", "(", "var", "s", ")", "(", "var", "slot", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "return", "(", "var", "values", ")", ")", ")", ")"]
theorem step_217 : Agreement point_217 point_218
    componentChars_217 emitted_217 := by
  intro rest priorTokens
  cbv

def emitted_218 : List String := ["(", "function", "protocol-step", "(", "(", "s", "(", "ref", "Protocol", ")", ")", "(", "record", "(", "ref", "BinaryRecord", ")", ")", ")", "bool", "(", "block", "(", "if", "(", "ne", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "switch", "(", "call", "record-opcode", "(", "var", "record", ")", ")", "(", "case", "0", "(", "block", "("]
theorem step_218 : Agreement point_218 point_219
    componentChars_218 emitted_218 := by
  intro rest priorTokens
  cbv

def emitted_219 : List String := ["let", "sym", "(", "ref", "Symbol", ")", "(", "call", "symbol-new", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "u64", "1", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", "(", "zero", "(", "array", "u64", ")", ")", ")", ")", "(", "effect", "(", "call", "advance-revision", "(", "field", "(", "var", "s", ")", "theory", ")", ")", ")", "(", "effect", "(", "call", "put-symbols", "(", "var", "s", ")", "(", "call"]
theorem step_219 : Agreement point_219 point_220
    componentChars_219 emitted_219 := by
  intro rest priorTokens
  cbv

def emitted_220 : List String := ["record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "var", "sym", ")", ")", ")", ")", ")", "(", "case", "1", "(", "block", "(", "let", "binders", "(", "array", "u64", ")", "(", "call", "protocol-words", "(", "var", "s", ")", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", "(", "let", "sym", "(", "ref", "Symbol", ")", "(", "call", "symbol-new", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "u64", "0", ")", "(", "length", "(", "var"]
theorem step_220 : Agreement point_220 point_221
    componentChars_220 emitted_220 := by
  intro rest priorTokens
  cbv

def emitted_221 : List String := ["binders", ")", ")", "(", "var", "binders", ")", ")", ")", "(", "effect", "(", "call", "advance-revision", "(", "field", "(", "var", "s", ")", "theory", ")", ")", ")", "(", "effect", "(", "call", "put-symbols", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "var", "sym", ")", ")", ")", ")", ")", "(", "case", "2", "(", "block", "(", "let", "i", "u64", "(", "call", "record-word", "("]
theorem step_221 : Agreement point_221 point_222
    componentChars_221 emitted_221 := by
  intro rest priorTokens
  cbv

def emitted_222 : List String := ["var", "record", ")", "(", "u64", "0", ")", ")", ")", "(", "let", "j", "u64", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", "(", "if", "(", "or", "(", "ge", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "symbols", ")", ")", ")", "(", "ge", "(", "var", "j", ")", "(", "length", "(", "field", "(", "var", "s", ")", "symbols", ")", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "bool"]
theorem step_222 : Agreement point_222 point_223
    componentChars_222 emitted_222 := by
  intro rest priorTokens
  cbv

def emitted_223 : List String := ["false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "prior", "(", "ref", "Symbol", ")", "(", "index", "(", "field", "(", "var", "s", ")", "symbols", ")", "(", "var", "i", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "symbols", ")", "(", "var", "i", ")", ")", "(", "index", "(", "field", "(", "var", "s", ")", "symbols", ")", "(", "var", "j", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "symbols", ")", "(", "var", "j", ")", ")", "(", "var", "prior", ")", ")"]
theorem step_223 : Agreement point_223 point_224
    componentChars_223 emitted_223 := by
  intro rest priorTokens
  cbv

def emitted_224 : List String := [")", ")", "(", "case", "3", "(", "block", "(", "let", "i", "u64", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", "(", "if", "(", "lt", "(", "var", "i", ")", "(", "u64", "13", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "5", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "value", "(", "ref", "Symbol", ")", "(", "call", "get-symbols", "("]
theorem step_224 : Agreement point_224 point_225
    componentChars_224 emitted_224 := by
  intro rest priorTokens
  cbv

def emitted_225 : List String := ["var", "s", ")", "(", "var", "i", ")", ")", ")", "(", "if", "(", "ne", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "effect", "(", "call", "symbol-free", "(", "var", "value", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "symbols", ")", "(", "var", "i", ")", ")", "(", "null", "(", "ref", "Symbol", ")", ")", ")", ")", ")", "(", "case"]
theorem step_225 : Agreement point_225 point_226
    componentChars_225 emitted_225 := by
  intro rest priorTokens
  cbv

def emitted_226 : List String := ["4", "(", "block", "(", "effect", "(", "call", "put-terms", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "call", "term-bvar", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", ")", ")", ")", "(", "case", "5", "(", "block", "(", "effect", "(", "call", "put-terms", "(", "var", "s", ")", "(", "call"]
theorem step_226 : Agreement point_226 point_227
    componentChars_226 emitted_226 := by
  intro rest priorTokens
  cbv

def emitted_227 : List String := ["record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "call", "term-literal", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "call", "record-bytes", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", ")", ")", ")", "(", "case", "6", "(", "block", "(", "let", "sym", "(", "ref", "Symbol", ")", "(", "call", "get-symbols", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")"]
theorem step_227 : Agreement point_227 point_228
    componentChars_227 emitted_227 := by
  intro rest priorTokens
  cbv

def emitted_228 : List String := ["(", "let", "args", "(", "array", "(", "ref", "Term", ")", ")", "(", "call", "protocol-terms", "(", "var", "s", ")", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", "(", "effect", "(", "call", "put-terms", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", "(", "call", "term-app", "(", "var", "sym", ")", "(", "var", "args", ")", ")", ")", ")", ")", ")", "(", "case", "7", "(", "block", "("]
theorem step_228 : Agreement point_228 point_229
    componentChars_228 emitted_228 := by
  intro rest priorTokens
  cbv

def emitted_229 : List String := ["let", "i", "u64", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", "(", "let", "j", "u64", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", "(", "if", "(", "or", "(", "ge", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "terms", ")", ")", ")", "(", "ge", "(", "var", "j", ")", "(", "length", "(", "field", "(", "var", "s", ")", "terms", ")", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "("]
theorem step_229 : Agreement point_229 point_230
    componentChars_229 emitted_229 := by
  intro rest priorTokens
  cbv

def emitted_230 : List String := ["u64", "1", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "prior", "(", "ref", "Term", ")", "(", "index", "(", "field", "(", "var", "s", ")", "terms", ")", "(", "var", "i", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "terms", ")", "(", "var", "i", ")", ")", "(", "index", "(", "field", "(", "var", "s", ")", "terms", ")", "(", "var", "j", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "terms", ")", "(", "var", "j", ")", ")", "("]
theorem step_230 : Agreement point_230 point_231
    componentChars_230 emitted_230 := by
  intro rest priorTokens
  cbv

def emitted_231 : List String := ["var", "prior", ")", ")", ")", ")", "(", "case", "8", "(", "block", "(", "let", "i", "u64", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", "(", "let", "value", "(", "ref", "Term", ")", "(", "call", "get-terms", "(", "var", "s", ")", "(", "var", "i", ")", ")", ")", "(", "if", "(", "ne", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "("]
theorem step_231 : Agreement point_231 point_232
    componentChars_231 emitted_231 := by
  intro rest priorTokens
  cbv

def emitted_232 : List String := ["block", ")", ")", "(", "effect", "(", "call", "term-free", "(", "var", "value", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "terms", ")", "(", "var", "i", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", ")", "(", "case", "9", "(", "block", "(", "if", "(", "field", "(", "var", "s", ")", "proof", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "6", ")", ")", "(", "return", "(", "bool"]
theorem step_232 : Agreement point_232 point_233
    componentChars_232 emitted_232 := by
  intro rest priorTokens
  cbv

def emitted_233 : List String := ["false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "t", "(", "ref", "Term", ")", "(", "call", "get-terms", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "let", "thm", "(", "ref", "Theorem", ")", "(", "call", "theorem-new", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "call", "term-retain", "(", "var", "t", ")", ")", "(", "u64", "9", ")", ")", ")", "(", "effect", "(", "call", "admit-theorem"]
theorem step_233 : Agreement point_233 point_234
    componentChars_233 emitted_233 := by
  intro rest priorTokens
  cbv

def emitted_234 : List String := ["(", "field", "(", "var", "s", ")", "theory", ")", "(", "var", "thm", ")", "(", "null", "(", "ref", "Symbol", ")", ")", "(", "zero", "(", "array", "(", "ref", "Symbol", ")", ")", ")", "(", "zero", "(", "array", "u64", ")", ")", ")", ")", "(", "effect", "(", "call", "put-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "var", "thm", ")", ")", ")", ")", ")", "(", "case", "10", "(", "block", "(", "let", "thm", "("]
theorem step_234 : Agreement point_234 point_235
    componentChars_234 emitted_234 := by
  intro rest priorTokens
  cbv

def emitted_235 : List String := ["ref", "Theorem", ")", "(", "call", "get-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "let", "t", "(", "ref", "Term", ")", "(", "call", "get-terms", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "if", "(", "or", "(", "eq", "(", "var", "thm", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", "(", "not", "(", "call", "term-equal", "("]
theorem step_235 : Agreement point_235 point_236
    componentChars_235 emitted_235 := by
  intro rest priorTokens
  cbv

def emitted_236 : List String := ["field", "(", "var", "thm", ")", "statement", ")", "(", "var", "t", ")", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "8", ")", ")", ")", "(", "block", "(", "let", "prior", "(", "ref", "Term", ")", "(", "field", "(", "var", "thm", ")", "statement", ")", ")", "(", "set", "(", "field", "(", "var", "thm", ")", "statement", ")", "(", "call", "term-retain", "(", "var", "t", ")", ")", ")", "(", "effect", "(", "call", "term-free", "(", "var", "prior", ")", ")", ")", ")", ")", ")", ")", "("]
theorem step_236 : Agreement point_236 point_237
    componentChars_236 emitted_236 := by
  intro rest priorTokens
  cbv

def emitted_237 : List String := ["case", "11", "(", "block", "(", "let", "i", "u64", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", "(", "let", "value", "(", "ref", "Theorem", ")", "(", "call", "get-theorems", "(", "var", "s", ")", "(", "var", "i", ")", ")", ")", "(", "if", "(", "ne", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "effect", "("]
theorem step_237 : Agreement point_237 point_238
    componentChars_237 emitted_237 := by
  intro rest priorTokens
  cbv

def emitted_238 : List String := ["call", "theorem-free", "(", "var", "value", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "theorems", ")", "(", "var", "i", ")", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", ")", ")", "(", "case", "12", "(", "block", "(", "let", "i", "u64", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", "(", "let", "j", "u64", "(", "call", "record-word", "(", "var"]
theorem step_238 : Agreement point_238 point_239
    componentChars_238 emitted_238 := by
  intro rest priorTokens
  cbv

def emitted_239 : List String := ["record", ")", "(", "u64", "1", ")", ")", ")", "(", "if", "(", "or", "(", "ge", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "theorems", ")", ")", ")", "(", "ge", "(", "var", "j", ")", "(", "length", "(", "field", "(", "var", "s", ")", "theorems", ")", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "prior", "(", "ref", "Theorem", ")", "(", "index", "(", "field", "(", "var"]
theorem step_239 : Agreement point_239 point_240
    componentChars_239 emitted_239 := by
  intro rest priorTokens
  cbv

def emitted_240 : List String := ["s", ")", "theorems", ")", "(", "var", "i", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "theorems", ")", "(", "var", "i", ")", ")", "(", "index", "(", "field", "(", "var", "s", ")", "theorems", ")", "(", "var", "j", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "theorems", ")", "(", "var", "j", ")", ")", "(", "var", "prior", ")", ")", ")", ")", "(", "case", "13", "(", "block", "(", "let", "t", "(", "ref", "Term", ")", "("]
theorem step_240 : Agreement point_240 point_241
    componentChars_240 emitted_240 := by
  intro rest priorTokens
  cbv

def emitted_241 : List String := ["call", "get-terms", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "let", "destination", "u64", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", "(", "if", "(", "ne", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "0", ")", ")", "(", "block", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "ge", "(", "var"]
theorem step_241 : Agreement point_241 point_242
    componentChars_241 emitted_241 := by
  intro rest priorTokens
  cbv

def emitted_242 : List String := ["destination", ")", "(", "length", "(", "field", "(", "var", "s", ")", "challenges", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "1", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "if", "(", "ne", "(", "index", "(", "field", "(", "var", "s", ")", "challenges", ")", "(", "var", "destination", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "3", ")", ")", ")", "(", "block", "("]
theorem step_242 : Agreement point_242 point_243
    componentChars_242 emitted_242 := by
  intro rest priorTokens
  cbv

def emitted_243 : List String := ["set", "(", "index", "(", "field", "(", "var", "s", ")", "challenges", ")", "(", "var", "destination", ")", ")", "(", "call", "term-retain", "(", "var", "t", ")", ")", ")", "(", "if", "(", "field", "(", "var", "s", ")", "proof", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "initial", ")", "(", "add", "(", "field", "(", "var", "s", ")", "initial", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "block", ")", ")", ")", ")", ")", ")", "(", "case", "14", "(", "block", "(", "if", "(", "not", "("]
theorem step_243 : Agreement point_243 point_244
    componentChars_243 emitted_243 := by
  intro rest priorTokens
  cbv

def emitted_244 : List String := ["field", "(", "var", "s", ")", "proof", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "6", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "challenge", "(", "ref", "Term", ")", "(", "call", "get-challenges", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "let", "thm", "(", "ref", "Theorem", ")", "(", "call", "get-theorems", "("]
theorem step_244 : Agreement point_244 point_245
    componentChars_244 emitted_244 := by
  intro rest priorTokens
  cbv

def emitted_245 : List String := ["var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "if", "(", "or", "(", "eq", "(", "var", "thm", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", "(", "not", "(", "call", "term-equal", "(", "var", "challenge", ")", "(", "field", "(", "var", "thm", ")", "statement", ")", ")", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "8", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "term-free", "(", "var"]
theorem step_245 : Agreement point_245 point_246
    componentChars_245 emitted_245 := by
  intro rest priorTokens
  cbv

def emitted_246 : List String := ["challenge", ")", ")", ")", "(", "set", "(", "index", "(", "field", "(", "var", "s", ")", "challenges", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "set", "(", "field", "(", "var", "s", ")", "satisfied", ")", "(", "add", "(", "field", "(", "var", "s", ")", "satisfied", ")", "(", "u64", "1", ")", ")", ")", ")", ")", ")", ")", "(", "case", "15", "(", "block", "(", "if", "(", "not", "("]
theorem step_246 : Agreement point_246 point_247
    componentChars_246 emitted_246 := by
  intro rest priorTokens
  cbv

def emitted_247 : List String := ["field", "(", "var", "s", ")", "proof", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "6", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "implication", "(", "ref", "Theorem", ")", "(", "call", "get-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "let", "premise", "(", "ref", "Theorem", ")", "(", "call"]
theorem step_247 : Agreement point_247 point_248
    componentChars_247 emitted_247 := by
  intro rest priorTokens
  cbv

def emitted_248 : List String := ["get-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "effect", "(", "call", "put-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", "(", "call", "modus-ponens", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "var", "implication", ")", "(", "var", "premise", ")", ")", ")", ")", ")", ")", "(", "case", "16", "(", "block"]
theorem step_248 : Agreement point_248 point_249
    componentChars_248 emitted_248 := by
  intro rest priorTokens
  cbv

def emitted_249 : List String := ["(", "if", "(", "not", "(", "field", "(", "var", "s", ")", "proof", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "6", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "thm", "(", "ref", "Theorem", ")", "(", "call", "get-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "let", "fvar", "(", "ref", "Symbol", ")", "(", "call"]
theorem step_249 : Agreement point_249 point_250
    componentChars_249 emitted_249 := by
  intro rest priorTokens
  cbv

def emitted_250 : List String := ["get-symbols", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "let", "value", "(", "ref", "Term", ")", "(", "call", "get-terms", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", ")", ")", "(", "effect", "(", "call", "put-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "3", ")", ")", "(", "call"]
theorem step_250 : Agreement point_250 point_251
    componentChars_250 emitted_250 := by
  intro rest priorTokens
  cbv

def emitted_251 : List String := ["instantiate-theorem", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "var", "thm", ")", "(", "var", "fvar", ")", "(", "var", "value", ")", ")", ")", ")", ")", ")", "(", "case", "17", "(", "block", "(", "let", "fvars", "(", "array", "(", "ref", "Symbol", ")", ")", "(", "call", "protocol-symbols", "(", "var", "s", ")", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", "(", "let", "hints", "(", "array", "u64", ")", "(", "call"]
theorem step_251 : Agreement point_251 point_252
    componentChars_251 emitted_251 := by
  intro rest priorTokens
  cbv

def emitted_252 : List String := ["protocol-words", "(", "var", "s", ")", "(", "var", "record", ")", "(", "u64", "1", ")", ")", ")", "(", "let", "value", "(", "ref", "Term", ")", "(", "call", "get-terms", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", ")", ")", "(", "let", "df", "Definition", "(", "call", "define-constant", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "var", "fvars", ")", "(", "var", "hints", ")", "(", "var", "value", ")", ")", ")", "("]
theorem step_252 : Agreement point_252 point_253
    componentChars_252 emitted_252 := by
  intro rest priorTokens
  cbv

def emitted_253 : List String := ["effect", "(", "call", "admit-theorem", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "field", "(", "var", "df", ")", "theorem", ")", "(", "field", "(", "var", "df", ")", "symbol", ")", "(", "var", "fvars", ")", "(", "var", "hints", ")", ")", ")", "(", "effect", "(", "call", "put-symbols", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "3", ")", ")", "(", "field", "(", "var", "df", ")", "symbol", ")", ")", ")", "(", "effect", "("]
theorem step_253 : Agreement point_253 point_254
    componentChars_253 emitted_253 := by
  intro rest priorTokens
  cbv

def emitted_254 : List String := ["call", "put-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "4", ")", ")", "(", "field", "(", "var", "df", ")", "theorem", ")", ")", ")", ")", ")", "(", "case", "18", "(", "block", "(", "if", "(", "not", "(", "field", "(", "var", "s", ")", "proof", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "6", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "("]
theorem step_254 : Agreement point_254 point_255
    componentChars_254 emitted_254 := by
  intro rest priorTokens
  cbv

def emitted_255 : List String := ["effect", "(", "call", "put-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "call", "literal-theorem", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "u64", "18", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", "(", "u64", "0", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", ")", ")", ")", "(", "case", "19", "(", "block", "(", "if", "(", "not", "(", "field", "("]
theorem step_255 : Agreement point_255 point_256
    componentChars_255 emitted_255 := by
  intro rest priorTokens
  cbv

def emitted_256 : List String := ["var", "s", ")", "proof", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "6", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "effect", "(", "call", "put-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", "(", "call", "literal-theorem", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "u64", "19", ")", "(", "call", "record-word", "(", "var"]
theorem step_256 : Agreement point_256 point_257
    componentChars_256 emitted_256 := by
  intro rest priorTokens
  cbv

def emitted_257 : List String := ["record", ")", "(", "u64", "0", ")", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", ")", ")", ")", "(", "case", "20", "(", "block", "(", "if", "(", "not", "(", "field", "(", "var", "s", ")", "proof", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "6", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "effect", "(", "call"]
theorem step_257 : Agreement point_257 point_258
    componentChars_257 emitted_257 := by
  intro rest priorTokens
  cbv

def emitted_258 : List String := ["put-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", "(", "call", "literal-theorem", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "u64", "20", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", ")", ")", ")", "(", "case", "21", "(", "block", "("]
theorem step_258 : Agreement point_258 point_259
    componentChars_258 emitted_258 := by
  intro rest priorTokens
  cbv

def emitted_259 : List String := ["if", "(", "not", "(", "field", "(", "var", "s", ")", "proof", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "6", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "effect", "(", "call", "put-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", "(", "call", "literal-theorem", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "u64", "21", ")", "(", "call"]
theorem step_259 : Agreement point_259 point_260
    componentChars_259 emitted_259 := by
  intro rest priorTokens
  cbv

def emitted_260 : List String := ["record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", ")", ")", ")", "(", "case", "22", "(", "block", "(", "if", "(", "not", "(", "field", "(", "var", "s", ")", "proof", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "6", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "("]
theorem step_260 : Agreement point_260 point_261
    componentChars_260 emitted_260 := by
  intro rest priorTokens
  cbv

def emitted_261 : List String := ["effect", "(", "call", "put-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", "(", "call", "literal-theorem", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "u64", "22", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", ")", ")", ")", ")", "(", "case", "23", "("]
theorem step_261 : Agreement point_261 point_262
    componentChars_261 emitted_261 := by
  intro rest priorTokens
  cbv

def emitted_262 : List String := ["block", "(", "if", "(", "not", "(", "field", "(", "var", "s", ")", "proof", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "6", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "literal", "(", "ref", "Term", ")", "(", "call", "get-terms", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call"]
theorem step_262 : Agreement point_262 point_263
    componentChars_262 emitted_262 := by
  intro rest priorTokens
  cbv

def emitted_263 : List String := ["put-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "call", "literal-theorem", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "u64", "23", ")", "(", "u64", "0", ")", "(", "u64", "0", ")", "(", "var", "literal", ")", ")", ")", ")", ")", ")", "(", "case", "24", "(", "block", "(", "if", "(", "not", "(", "field", "(", "var", "s", ")", "proof", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "6", ")", ")"]
theorem step_263 : Agreement point_263 point_264
    componentChars_263 emitted_263 := by
  intro rest priorTokens
  cbv

def emitted_264 : List String := ["(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "literal", "(", "ref", "Term", ")", "(", "call", "get-terms", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "effect", "(", "call", "put-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", "(", "call", "literal-theorem", "(", "field", "(", "var", "s", ")"]
theorem step_264 : Agreement point_264 point_265
    componentChars_264 emitted_264 := by
  intro rest priorTokens
  cbv

def emitted_265 : List String := ["theory", ")", "(", "u64", "24", ")", "(", "u64", "0", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "var", "literal", ")", ")", ")", ")", ")", ")", "(", "case", "25", "(", "block", "(", "if", "(", "not", "(", "field", "(", "var", "s", ")", "proof", ")", ")", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "6", ")", ")", "(", "return", "(", "bool", "false", ")", ")", ")", "(", "block", ")", ")", "(", "let", "safe", "("]
theorem step_265 : Agreement point_265 point_266
    componentChars_265 emitted_265 := by
  intro rest priorTokens
  cbv

def emitted_266 : List String := ["ref", "Theorem", ")", "(", "call", "get-theorems", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "0", ")", ")", ")", ")", "(", "let", "thm", "(", "ref", "Theorem", ")", "(", "call", "jit-theorem", "(", "field", "(", "var", "s", ")", "theory", ")", "(", "var", "safe", ")", "(", "address", "(", "field", "(", "var", "s", ")", "physical-error", ")", ")", "(", "field", "(", "var", "s", ")", "execution-scope", ")", ")", ")", "(", "let"]
theorem step_266 : Agreement point_266 point_267
    componentChars_266 emitted_266 := by
  intro rest priorTokens
  cbv

def emitted_267 : List String := ["output", "(", "ref", "Term", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "if", "(", "ne", "(", "var", "thm", ")", "(", "null", "(", "ref", "Theorem", ")", ")", ")", "(", "block", "(", "set", "(", "var", "output", ")", "(", "call", "term-retain", "(", "index", "(", "field", "(", "field", "(", "var", "thm", ")", "statement", ")", "args", ")", "(", "u64", "3", ")", ")", ")", ")", ")", "(", "block", ")", ")", "(", "effect", "(", "call", "put-theorems", "(", "var", "s", ")", "(", "call"]
theorem step_267 : Agreement point_267 point_268
    componentChars_267 emitted_267 := by
  intro rest priorTokens
  cbv

def emitted_268 : List String := ["record-word", "(", "var", "record", ")", "(", "u64", "1", ")", ")", "(", "var", "thm", ")", ")", ")", "(", "effect", "(", "call", "put-terms", "(", "var", "s", ")", "(", "call", "record-word", "(", "var", "record", ")", "(", "u64", "2", ")", ")", "(", "var", "output", ")", ")", ")", ")", ")", "(", "default", "(", "block", "(", "set", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64", "9", ")", ")", ")", ")", ")", "(", "return", "(", "eq", "(", "field", "(", "var", "s", ")", "error", ")", "(", "u64"]
theorem step_268 : Agreement point_268 point_269
    componentChars_268 emitted_268 := by
  intro rest priorTokens
  cbv

def emitted_269 : List String := ["0", ")", ")", ")", ")", ")", "(", "function", "protocol-remaining", "(", "(", "s", "(", "ref", "Protocol", ")", ")", ")", "u64", "(", "block", "(", "let", "count", "u64", "(", "u64", "0", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "challenges", ")", ")", ")", "(", "block", "(", "if", "(", "ne", "(", "index", "(", "field", "(", "var", "s", ")", "challenges", ")", "("]
theorem step_269 : Agreement point_269 point_270
    componentChars_269 emitted_269 := by
  intro rest priorTokens
  cbv

def emitted_270 : List String := ["var", "i", ")", ")", "(", "null", "(", "ref", "Term", ")", ")", ")", "(", "block", "(", "set", "(", "var", "count", ")", "(", "add", "(", "var", "count", ")", "(", "u64", "1", ")", ")", ")", ")", "(", "block", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "return", "(", "var", "count", ")", ")", ")", ")", "(", "function", "protocol-free", "(", "(", "s", "(", "ref", "Protocol", ")", ")", ")", "unit", "(", "block", "(", "if", "(", "eq", "("]
theorem step_270 : Agreement point_270 point_271
    componentChars_270 emitted_270 := by
  intro rest priorTokens
  cbv

def emitted_271 : List String := ["var", "s", ")", "(", "null", "(", "ref", "Protocol", ")", ")", ")", "(", "block", "(", "return", ")", ")", "(", "block", ")", ")", "(", "let", "i", "u64", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "symbols", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "symbol-free", "(", "index", "(", "field", "(", "var", "s", ")", "symbols", ")", "(", "var", "i", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "("]
theorem step_271 : Agreement point_271 point_272
    componentChars_271 emitted_271 := by
  intro rest priorTokens
  cbv

def emitted_272 : List String := ["var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "terms", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "term-free", "(", "index", "(", "field", "(", "var", "s", ")", "terms", ")", "(", "var", "i", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "("]
theorem step_272 : Agreement point_272 point_273
    componentChars_272 emitted_272 := by
  intro rest priorTokens
  cbv

def emitted_273 : List String := ["u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "theorems", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "theorem-free", "(", "index", "(", "field", "(", "var", "s", ")", "theorems", ")", "(", "var", "i", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var"]
theorem step_273 : Agreement point_273 point_274
    componentChars_273 emitted_273 := by
  intro rest priorTokens
  cbv

def emitted_274 : List String := ["i", ")", "(", "length", "(", "field", "(", "var", "s", ")", "challenges", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "term-free", "(", "index", "(", "field", "(", "var", "s", ")", "challenges", ")", "(", "var", "i", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "let", "thy", "(", "ref", "Theory", ")", "(", "field", "(", "var", "s", ")", "theory", ")", ")", "(", "let", "admission", "(", "ref"]
theorem step_274 : Agreement point_274 point_275
    componentChars_274 emitted_274 := by
  intro rest priorTokens
  cbv

def emitted_275 : List String := ["Admission", ")", "(", "field", "(", "var", "thy", ")", "admissions", ")", ")", "(", "while", "(", "ne", "(", "var", "admission", ")", "(", "null", "(", "ref", "Admission", ")", ")", ")", "(", "block", "(", "let", "prior", "(", "ref", "Admission", ")", "(", "field", "(", "var", "admission", ")", "previous", ")", ")", "(", "effect", "(", "call", "term-free", "(", "field", "(", "var", "admission", ")", "statement", ")", ")", ")"]
theorem step_275 : Agreement point_275 point_276
    componentChars_275 emitted_275 := by
  intro rest priorTokens
  cbv

def emitted_276 : List String := ["(", "effect", "(", "call", "symbol-free", "(", "field", "(", "var", "admission", ")", "symbol", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "length", "(", "field", "(", "var", "admission", ")", "fvars", ")", ")", ")", "(", "block", "(", "effect", "(", "call", "symbol-free", "(", "index", "(", "field", "(", "var", "admission", ")", "fvars", ")", "(", "var", "i", ")"]
theorem step_276 : Agreement point_276 point_277
    componentChars_276 emitted_276 := by
  intro rest priorTokens
  cbv

def emitted_277 : List String := [")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "free", "(", "field", "(", "var", "admission", ")", "fvars", ")", ")", "(", "free", "(", "field", "(", "var", "admission", ")", "hints", ")", ")", "(", "free", "(", "field", "(", "var", "admission", ")", "revision", ")", ")", "(", "free", "(", "var", "admission", ")", ")", "(", "set", "(", "var", "admission", ")", "(", "var"]
theorem step_277 : Agreement point_277 point_278
    componentChars_277 emitted_277 := by
  intro rest priorTokens
  cbv

def emitted_278 : List String := ["prior", ")", ")", ")", ")", "(", "set", "(", "var", "i", ")", "(", "u64", "0", ")", ")", "(", "while", "(", "lt", "(", "var", "i", ")", "(", "u64", "13", ")", ")", "(", "block", "(", "let", "builtin", "(", "ref", "Symbol", ")", "(", "index", "(", "field", "(", "var", "thy", ")", "builtins", ")", "(", "var", "i", ")", ")", ")", "(", "free", "(", "field", "(", "var", "builtin", ")", "binders", ")", ")", "(", "free", "(", "field", "(", "var", "builtin", ")", "identity", ")", ")"]
theorem step_278 : Agreement point_278 point_279
    componentChars_278 emitted_278 := by
  intro rest priorTokens
  cbv

def emitted_279 : List String := ["(", "free", "(", "var", "builtin", ")", ")", "(", "set", "(", "var", "i", ")", "(", "add", "(", "var", "i", ")", "(", "u64", "1", ")", ")", ")", ")", ")", "(", "free", "(", "field", "(", "var", "thy", ")", "builtins", ")", ")", "(", "free", "(", "field", "(", "var", "thy", ")", "next-identity", ")", ")", "(", "free", "(", "field", "(", "var", "thy", ")", "revision", ")", ")", "(", "free", "(", "var", "thy", ")", ")", "(", "free", "(", "field", "(", "var", "s", ")", "symbols", ")", ")", "(", "free", "(", "field", "(", "var"]
theorem step_279 : Agreement point_279 point_280
    componentChars_279 emitted_279 := by
  intro rest priorTokens
  cbv

def emitted_280 : List String := ["s", ")", "terms", ")", ")", "(", "free", "(", "field", "(", "var", "s", ")", "theorems", ")", ")", "(", "free", "(", "field", "(", "var", "s", ")", "challenges", ")", ")", "(", "free", "(", "field", "(", "var", "s", ")", "aux-words", ")", ")", "(", "free", "(", "field", "(", "var", "s", ")", "aux-terms", ")", ")", "(", "free", "(", "field", "(", "var", "s", ")", "aux-symbols", ")", ")", "(", "free", "(", "var", "s", ")", ")", "(", "return", ")", ")", ")", ")"]
theorem step_280 : Agreement point_280 point_281
    componentChars_280 emitted_280 := by
  intro rest priorTokens
  cbv

def input_281 : List Char := []
def tokens_281 : List String := []
theorem replay_281 : Agreement point_281 point_281
    input_281 tokens_281 := agreement_empty point_281

def input_280 : List Char := componentChars_280 ++ input_281
def tokens_280 : List String := emitted_280 ++ tokens_281
theorem replay_280 : Agreement point_280 point_281
    input_280 tokens_280 :=
  agreement_append point_280 point_281 point_281
    componentChars_280 input_281 emitted_280 tokens_281
    step_280 replay_281

def input_279 : List Char := componentChars_279 ++ input_280
def tokens_279 : List String := emitted_279 ++ tokens_280
theorem replay_279 : Agreement point_279 point_281
    input_279 tokens_279 :=
  agreement_append point_279 point_280 point_281
    componentChars_279 input_280 emitted_279 tokens_280
    step_279 replay_280

def input_278 : List Char := componentChars_278 ++ input_279
def tokens_278 : List String := emitted_278 ++ tokens_279
theorem replay_278 : Agreement point_278 point_281
    input_278 tokens_278 :=
  agreement_append point_278 point_279 point_281
    componentChars_278 input_279 emitted_278 tokens_279
    step_278 replay_279

def input_277 : List Char := componentChars_277 ++ input_278
def tokens_277 : List String := emitted_277 ++ tokens_278
theorem replay_277 : Agreement point_277 point_281
    input_277 tokens_277 :=
  agreement_append point_277 point_278 point_281
    componentChars_277 input_278 emitted_277 tokens_278
    step_277 replay_278

def input_276 : List Char := componentChars_276 ++ input_277
def tokens_276 : List String := emitted_276 ++ tokens_277
theorem replay_276 : Agreement point_276 point_281
    input_276 tokens_276 :=
  agreement_append point_276 point_277 point_281
    componentChars_276 input_277 emitted_276 tokens_277
    step_276 replay_277

def input_275 : List Char := componentChars_275 ++ input_276
def tokens_275 : List String := emitted_275 ++ tokens_276
theorem replay_275 : Agreement point_275 point_281
    input_275 tokens_275 :=
  agreement_append point_275 point_276 point_281
    componentChars_275 input_276 emitted_275 tokens_276
    step_275 replay_276

def input_274 : List Char := componentChars_274 ++ input_275
def tokens_274 : List String := emitted_274 ++ tokens_275
theorem replay_274 : Agreement point_274 point_281
    input_274 tokens_274 :=
  agreement_append point_274 point_275 point_281
    componentChars_274 input_275 emitted_274 tokens_275
    step_274 replay_275

def input_273 : List Char := componentChars_273 ++ input_274
def tokens_273 : List String := emitted_273 ++ tokens_274
theorem replay_273 : Agreement point_273 point_281
    input_273 tokens_273 :=
  agreement_append point_273 point_274 point_281
    componentChars_273 input_274 emitted_273 tokens_274
    step_273 replay_274

def input_272 : List Char := componentChars_272 ++ input_273
def tokens_272 : List String := emitted_272 ++ tokens_273
theorem replay_272 : Agreement point_272 point_281
    input_272 tokens_272 :=
  agreement_append point_272 point_273 point_281
    componentChars_272 input_273 emitted_272 tokens_273
    step_272 replay_273

def input_271 : List Char := componentChars_271 ++ input_272
def tokens_271 : List String := emitted_271 ++ tokens_272
theorem replay_271 : Agreement point_271 point_281
    input_271 tokens_271 :=
  agreement_append point_271 point_272 point_281
    componentChars_271 input_272 emitted_271 tokens_272
    step_271 replay_272

def input_270 : List Char := componentChars_270 ++ input_271
def tokens_270 : List String := emitted_270 ++ tokens_271
theorem replay_270 : Agreement point_270 point_281
    input_270 tokens_270 :=
  agreement_append point_270 point_271 point_281
    componentChars_270 input_271 emitted_270 tokens_271
    step_270 replay_271

def input_269 : List Char := componentChars_269 ++ input_270
def tokens_269 : List String := emitted_269 ++ tokens_270
theorem replay_269 : Agreement point_269 point_281
    input_269 tokens_269 :=
  agreement_append point_269 point_270 point_281
    componentChars_269 input_270 emitted_269 tokens_270
    step_269 replay_270

def input_268 : List Char := componentChars_268 ++ input_269
def tokens_268 : List String := emitted_268 ++ tokens_269
theorem replay_268 : Agreement point_268 point_281
    input_268 tokens_268 :=
  agreement_append point_268 point_269 point_281
    componentChars_268 input_269 emitted_268 tokens_269
    step_268 replay_269

def input_267 : List Char := componentChars_267 ++ input_268
def tokens_267 : List String := emitted_267 ++ tokens_268
theorem replay_267 : Agreement point_267 point_281
    input_267 tokens_267 :=
  agreement_append point_267 point_268 point_281
    componentChars_267 input_268 emitted_267 tokens_268
    step_267 replay_268

def input_266 : List Char := componentChars_266 ++ input_267
def tokens_266 : List String := emitted_266 ++ tokens_267
theorem replay_266 : Agreement point_266 point_281
    input_266 tokens_266 :=
  agreement_append point_266 point_267 point_281
    componentChars_266 input_267 emitted_266 tokens_267
    step_266 replay_267

def input_265 : List Char := componentChars_265 ++ input_266
def tokens_265 : List String := emitted_265 ++ tokens_266
theorem replay_265 : Agreement point_265 point_281
    input_265 tokens_265 :=
  agreement_append point_265 point_266 point_281
    componentChars_265 input_266 emitted_265 tokens_266
    step_265 replay_266

def input_264 : List Char := componentChars_264 ++ input_265
def tokens_264 : List String := emitted_264 ++ tokens_265
theorem replay_264 : Agreement point_264 point_281
    input_264 tokens_264 :=
  agreement_append point_264 point_265 point_281
    componentChars_264 input_265 emitted_264 tokens_265
    step_264 replay_265

def input_263 : List Char := componentChars_263 ++ input_264
def tokens_263 : List String := emitted_263 ++ tokens_264
theorem replay_263 : Agreement point_263 point_281
    input_263 tokens_263 :=
  agreement_append point_263 point_264 point_281
    componentChars_263 input_264 emitted_263 tokens_264
    step_263 replay_264

def input_262 : List Char := componentChars_262 ++ input_263
def tokens_262 : List String := emitted_262 ++ tokens_263
theorem replay_262 : Agreement point_262 point_281
    input_262 tokens_262 :=
  agreement_append point_262 point_263 point_281
    componentChars_262 input_263 emitted_262 tokens_263
    step_262 replay_263

def input_261 : List Char := componentChars_261 ++ input_262
def tokens_261 : List String := emitted_261 ++ tokens_262
theorem replay_261 : Agreement point_261 point_281
    input_261 tokens_261 :=
  agreement_append point_261 point_262 point_281
    componentChars_261 input_262 emitted_261 tokens_262
    step_261 replay_262

def input_260 : List Char := componentChars_260 ++ input_261
def tokens_260 : List String := emitted_260 ++ tokens_261
theorem replay_260 : Agreement point_260 point_281
    input_260 tokens_260 :=
  agreement_append point_260 point_261 point_281
    componentChars_260 input_261 emitted_260 tokens_261
    step_260 replay_261

def input_259 : List Char := componentChars_259 ++ input_260
def tokens_259 : List String := emitted_259 ++ tokens_260
theorem replay_259 : Agreement point_259 point_281
    input_259 tokens_259 :=
  agreement_append point_259 point_260 point_281
    componentChars_259 input_260 emitted_259 tokens_260
    step_259 replay_260

def input_258 : List Char := componentChars_258 ++ input_259
def tokens_258 : List String := emitted_258 ++ tokens_259
theorem replay_258 : Agreement point_258 point_281
    input_258 tokens_258 :=
  agreement_append point_258 point_259 point_281
    componentChars_258 input_259 emitted_258 tokens_259
    step_258 replay_259

def input_257 : List Char := componentChars_257 ++ input_258
def tokens_257 : List String := emitted_257 ++ tokens_258
theorem replay_257 : Agreement point_257 point_281
    input_257 tokens_257 :=
  agreement_append point_257 point_258 point_281
    componentChars_257 input_258 emitted_257 tokens_258
    step_257 replay_258

def input_256 : List Char := componentChars_256 ++ input_257
def tokens_256 : List String := emitted_256 ++ tokens_257
theorem replay_256 : Agreement point_256 point_281
    input_256 tokens_256 :=
  agreement_append point_256 point_257 point_281
    componentChars_256 input_257 emitted_256 tokens_257
    step_256 replay_257

def input_255 : List Char := componentChars_255 ++ input_256
def tokens_255 : List String := emitted_255 ++ tokens_256
theorem replay_255 : Agreement point_255 point_281
    input_255 tokens_255 :=
  agreement_append point_255 point_256 point_281
    componentChars_255 input_256 emitted_255 tokens_256
    step_255 replay_256

def input_254 : List Char := componentChars_254 ++ input_255
def tokens_254 : List String := emitted_254 ++ tokens_255
theorem replay_254 : Agreement point_254 point_281
    input_254 tokens_254 :=
  agreement_append point_254 point_255 point_281
    componentChars_254 input_255 emitted_254 tokens_255
    step_254 replay_255

def input_253 : List Char := componentChars_253 ++ input_254
def tokens_253 : List String := emitted_253 ++ tokens_254
theorem replay_253 : Agreement point_253 point_281
    input_253 tokens_253 :=
  agreement_append point_253 point_254 point_281
    componentChars_253 input_254 emitted_253 tokens_254
    step_253 replay_254

def input_252 : List Char := componentChars_252 ++ input_253
def tokens_252 : List String := emitted_252 ++ tokens_253
theorem replay_252 : Agreement point_252 point_281
    input_252 tokens_252 :=
  agreement_append point_252 point_253 point_281
    componentChars_252 input_253 emitted_252 tokens_253
    step_252 replay_253

def input_251 : List Char := componentChars_251 ++ input_252
def tokens_251 : List String := emitted_251 ++ tokens_252
theorem replay_251 : Agreement point_251 point_281
    input_251 tokens_251 :=
  agreement_append point_251 point_252 point_281
    componentChars_251 input_252 emitted_251 tokens_252
    step_251 replay_252

def input_250 : List Char := componentChars_250 ++ input_251
def tokens_250 : List String := emitted_250 ++ tokens_251
theorem replay_250 : Agreement point_250 point_281
    input_250 tokens_250 :=
  agreement_append point_250 point_251 point_281
    componentChars_250 input_251 emitted_250 tokens_251
    step_250 replay_251

def input_249 : List Char := componentChars_249 ++ input_250
def tokens_249 : List String := emitted_249 ++ tokens_250
theorem replay_249 : Agreement point_249 point_281
    input_249 tokens_249 :=
  agreement_append point_249 point_250 point_281
    componentChars_249 input_250 emitted_249 tokens_250
    step_249 replay_250

def input_248 : List Char := componentChars_248 ++ input_249
def tokens_248 : List String := emitted_248 ++ tokens_249
theorem replay_248 : Agreement point_248 point_281
    input_248 tokens_248 :=
  agreement_append point_248 point_249 point_281
    componentChars_248 input_249 emitted_248 tokens_249
    step_248 replay_249

def input_247 : List Char := componentChars_247 ++ input_248
def tokens_247 : List String := emitted_247 ++ tokens_248
theorem replay_247 : Agreement point_247 point_281
    input_247 tokens_247 :=
  agreement_append point_247 point_248 point_281
    componentChars_247 input_248 emitted_247 tokens_248
    step_247 replay_248

def input_246 : List Char := componentChars_246 ++ input_247
def tokens_246 : List String := emitted_246 ++ tokens_247
theorem replay_246 : Agreement point_246 point_281
    input_246 tokens_246 :=
  agreement_append point_246 point_247 point_281
    componentChars_246 input_247 emitted_246 tokens_247
    step_246 replay_247

def input_245 : List Char := componentChars_245 ++ input_246
def tokens_245 : List String := emitted_245 ++ tokens_246
theorem replay_245 : Agreement point_245 point_281
    input_245 tokens_245 :=
  agreement_append point_245 point_246 point_281
    componentChars_245 input_246 emitted_245 tokens_246
    step_245 replay_246

def input_244 : List Char := componentChars_244 ++ input_245
def tokens_244 : List String := emitted_244 ++ tokens_245
theorem replay_244 : Agreement point_244 point_281
    input_244 tokens_244 :=
  agreement_append point_244 point_245 point_281
    componentChars_244 input_245 emitted_244 tokens_245
    step_244 replay_245

def input_243 : List Char := componentChars_243 ++ input_244
def tokens_243 : List String := emitted_243 ++ tokens_244
theorem replay_243 : Agreement point_243 point_281
    input_243 tokens_243 :=
  agreement_append point_243 point_244 point_281
    componentChars_243 input_244 emitted_243 tokens_244
    step_243 replay_244

def input_242 : List Char := componentChars_242 ++ input_243
def tokens_242 : List String := emitted_242 ++ tokens_243
theorem replay_242 : Agreement point_242 point_281
    input_242 tokens_242 :=
  agreement_append point_242 point_243 point_281
    componentChars_242 input_243 emitted_242 tokens_243
    step_242 replay_243

def input_241 : List Char := componentChars_241 ++ input_242
def tokens_241 : List String := emitted_241 ++ tokens_242
theorem replay_241 : Agreement point_241 point_281
    input_241 tokens_241 :=
  agreement_append point_241 point_242 point_281
    componentChars_241 input_242 emitted_241 tokens_242
    step_241 replay_242

def input_240 : List Char := componentChars_240 ++ input_241
def tokens_240 : List String := emitted_240 ++ tokens_241
theorem replay_240 : Agreement point_240 point_281
    input_240 tokens_240 :=
  agreement_append point_240 point_241 point_281
    componentChars_240 input_241 emitted_240 tokens_241
    step_240 replay_241

def input_239 : List Char := componentChars_239 ++ input_240
def tokens_239 : List String := emitted_239 ++ tokens_240
theorem replay_239 : Agreement point_239 point_281
    input_239 tokens_239 :=
  agreement_append point_239 point_240 point_281
    componentChars_239 input_240 emitted_239 tokens_240
    step_239 replay_240

def input_238 : List Char := componentChars_238 ++ input_239
def tokens_238 : List String := emitted_238 ++ tokens_239
theorem replay_238 : Agreement point_238 point_281
    input_238 tokens_238 :=
  agreement_append point_238 point_239 point_281
    componentChars_238 input_239 emitted_238 tokens_239
    step_238 replay_239

def input_237 : List Char := componentChars_237 ++ input_238
def tokens_237 : List String := emitted_237 ++ tokens_238
theorem replay_237 : Agreement point_237 point_281
    input_237 tokens_237 :=
  agreement_append point_237 point_238 point_281
    componentChars_237 input_238 emitted_237 tokens_238
    step_237 replay_238

def input_236 : List Char := componentChars_236 ++ input_237
def tokens_236 : List String := emitted_236 ++ tokens_237
theorem replay_236 : Agreement point_236 point_281
    input_236 tokens_236 :=
  agreement_append point_236 point_237 point_281
    componentChars_236 input_237 emitted_236 tokens_237
    step_236 replay_237

def input_235 : List Char := componentChars_235 ++ input_236
def tokens_235 : List String := emitted_235 ++ tokens_236
theorem replay_235 : Agreement point_235 point_281
    input_235 tokens_235 :=
  agreement_append point_235 point_236 point_281
    componentChars_235 input_236 emitted_235 tokens_236
    step_235 replay_236

def input_234 : List Char := componentChars_234 ++ input_235
def tokens_234 : List String := emitted_234 ++ tokens_235
theorem replay_234 : Agreement point_234 point_281
    input_234 tokens_234 :=
  agreement_append point_234 point_235 point_281
    componentChars_234 input_235 emitted_234 tokens_235
    step_234 replay_235

def input_233 : List Char := componentChars_233 ++ input_234
def tokens_233 : List String := emitted_233 ++ tokens_234
theorem replay_233 : Agreement point_233 point_281
    input_233 tokens_233 :=
  agreement_append point_233 point_234 point_281
    componentChars_233 input_234 emitted_233 tokens_234
    step_233 replay_234

def input_232 : List Char := componentChars_232 ++ input_233
def tokens_232 : List String := emitted_232 ++ tokens_233
theorem replay_232 : Agreement point_232 point_281
    input_232 tokens_232 :=
  agreement_append point_232 point_233 point_281
    componentChars_232 input_233 emitted_232 tokens_233
    step_232 replay_233

def input_231 : List Char := componentChars_231 ++ input_232
def tokens_231 : List String := emitted_231 ++ tokens_232
theorem replay_231 : Agreement point_231 point_281
    input_231 tokens_231 :=
  agreement_append point_231 point_232 point_281
    componentChars_231 input_232 emitted_231 tokens_232
    step_231 replay_232

def input_230 : List Char := componentChars_230 ++ input_231
def tokens_230 : List String := emitted_230 ++ tokens_231
theorem replay_230 : Agreement point_230 point_281
    input_230 tokens_230 :=
  agreement_append point_230 point_231 point_281
    componentChars_230 input_231 emitted_230 tokens_231
    step_230 replay_231

def input_229 : List Char := componentChars_229 ++ input_230
def tokens_229 : List String := emitted_229 ++ tokens_230
theorem replay_229 : Agreement point_229 point_281
    input_229 tokens_229 :=
  agreement_append point_229 point_230 point_281
    componentChars_229 input_230 emitted_229 tokens_230
    step_229 replay_230

def input_228 : List Char := componentChars_228 ++ input_229
def tokens_228 : List String := emitted_228 ++ tokens_229
theorem replay_228 : Agreement point_228 point_281
    input_228 tokens_228 :=
  agreement_append point_228 point_229 point_281
    componentChars_228 input_229 emitted_228 tokens_229
    step_228 replay_229

def input_227 : List Char := componentChars_227 ++ input_228
def tokens_227 : List String := emitted_227 ++ tokens_228
theorem replay_227 : Agreement point_227 point_281
    input_227 tokens_227 :=
  agreement_append point_227 point_228 point_281
    componentChars_227 input_228 emitted_227 tokens_228
    step_227 replay_228

def input_226 : List Char := componentChars_226 ++ input_227
def tokens_226 : List String := emitted_226 ++ tokens_227
theorem replay_226 : Agreement point_226 point_281
    input_226 tokens_226 :=
  agreement_append point_226 point_227 point_281
    componentChars_226 input_227 emitted_226 tokens_227
    step_226 replay_227

def input_225 : List Char := componentChars_225 ++ input_226
def tokens_225 : List String := emitted_225 ++ tokens_226
theorem replay_225 : Agreement point_225 point_281
    input_225 tokens_225 :=
  agreement_append point_225 point_226 point_281
    componentChars_225 input_226 emitted_225 tokens_226
    step_225 replay_226

def input_224 : List Char := componentChars_224 ++ input_225
def tokens_224 : List String := emitted_224 ++ tokens_225
theorem replay_224 : Agreement point_224 point_281
    input_224 tokens_224 :=
  agreement_append point_224 point_225 point_281
    componentChars_224 input_225 emitted_224 tokens_225
    step_224 replay_225

def input_223 : List Char := componentChars_223 ++ input_224
def tokens_223 : List String := emitted_223 ++ tokens_224
theorem replay_223 : Agreement point_223 point_281
    input_223 tokens_223 :=
  agreement_append point_223 point_224 point_281
    componentChars_223 input_224 emitted_223 tokens_224
    step_223 replay_224

def input_222 : List Char := componentChars_222 ++ input_223
def tokens_222 : List String := emitted_222 ++ tokens_223
theorem replay_222 : Agreement point_222 point_281
    input_222 tokens_222 :=
  agreement_append point_222 point_223 point_281
    componentChars_222 input_223 emitted_222 tokens_223
    step_222 replay_223

def input_221 : List Char := componentChars_221 ++ input_222
def tokens_221 : List String := emitted_221 ++ tokens_222
theorem replay_221 : Agreement point_221 point_281
    input_221 tokens_221 :=
  agreement_append point_221 point_222 point_281
    componentChars_221 input_222 emitted_221 tokens_222
    step_221 replay_222

def input_220 : List Char := componentChars_220 ++ input_221
def tokens_220 : List String := emitted_220 ++ tokens_221
theorem replay_220 : Agreement point_220 point_281
    input_220 tokens_220 :=
  agreement_append point_220 point_221 point_281
    componentChars_220 input_221 emitted_220 tokens_221
    step_220 replay_221

def input_219 : List Char := componentChars_219 ++ input_220
def tokens_219 : List String := emitted_219 ++ tokens_220
theorem replay_219 : Agreement point_219 point_281
    input_219 tokens_219 :=
  agreement_append point_219 point_220 point_281
    componentChars_219 input_220 emitted_219 tokens_220
    step_219 replay_220

def input_218 : List Char := componentChars_218 ++ input_219
def tokens_218 : List String := emitted_218 ++ tokens_219
theorem replay_218 : Agreement point_218 point_281
    input_218 tokens_218 :=
  agreement_append point_218 point_219 point_281
    componentChars_218 input_219 emitted_218 tokens_219
    step_218 replay_219

def input_217 : List Char := componentChars_217 ++ input_218
def tokens_217 : List String := emitted_217 ++ tokens_218
theorem replay_217 : Agreement point_217 point_281
    input_217 tokens_217 :=
  agreement_append point_217 point_218 point_281
    componentChars_217 input_218 emitted_217 tokens_218
    step_217 replay_218

def input_216 : List Char := componentChars_216 ++ input_217
def tokens_216 : List String := emitted_216 ++ tokens_217
theorem replay_216 : Agreement point_216 point_281
    input_216 tokens_216 :=
  agreement_append point_216 point_217 point_281
    componentChars_216 input_217 emitted_216 tokens_217
    step_216 replay_217

def input_215 : List Char := componentChars_215 ++ input_216
def tokens_215 : List String := emitted_215 ++ tokens_216
theorem replay_215 : Agreement point_215 point_281
    input_215 tokens_215 :=
  agreement_append point_215 point_216 point_281
    componentChars_215 input_216 emitted_215 tokens_216
    step_215 replay_216

def input_214 : List Char := componentChars_214 ++ input_215
def tokens_214 : List String := emitted_214 ++ tokens_215
theorem replay_214 : Agreement point_214 point_281
    input_214 tokens_214 :=
  agreement_append point_214 point_215 point_281
    componentChars_214 input_215 emitted_214 tokens_215
    step_214 replay_215

def input_213 : List Char := componentChars_213 ++ input_214
def tokens_213 : List String := emitted_213 ++ tokens_214
theorem replay_213 : Agreement point_213 point_281
    input_213 tokens_213 :=
  agreement_append point_213 point_214 point_281
    componentChars_213 input_214 emitted_213 tokens_214
    step_213 replay_214

def input_212 : List Char := componentChars_212 ++ input_213
def tokens_212 : List String := emitted_212 ++ tokens_213
theorem replay_212 : Agreement point_212 point_281
    input_212 tokens_212 :=
  agreement_append point_212 point_213 point_281
    componentChars_212 input_213 emitted_212 tokens_213
    step_212 replay_213

def input_211 : List Char := componentChars_211 ++ input_212
def tokens_211 : List String := emitted_211 ++ tokens_212
theorem replay_211 : Agreement point_211 point_281
    input_211 tokens_211 :=
  agreement_append point_211 point_212 point_281
    componentChars_211 input_212 emitted_211 tokens_212
    step_211 replay_212

def input_210 : List Char := componentChars_210 ++ input_211
def tokens_210 : List String := emitted_210 ++ tokens_211
theorem replay_210 : Agreement point_210 point_281
    input_210 tokens_210 :=
  agreement_append point_210 point_211 point_281
    componentChars_210 input_211 emitted_210 tokens_211
    step_210 replay_211

def input_209 : List Char := componentChars_209 ++ input_210
def tokens_209 : List String := emitted_209 ++ tokens_210
theorem replay_209 : Agreement point_209 point_281
    input_209 tokens_209 :=
  agreement_append point_209 point_210 point_281
    componentChars_209 input_210 emitted_209 tokens_210
    step_209 replay_210

def input_208 : List Char := componentChars_208 ++ input_209
def tokens_208 : List String := emitted_208 ++ tokens_209
theorem replay_208 : Agreement point_208 point_281
    input_208 tokens_208 :=
  agreement_append point_208 point_209 point_281
    componentChars_208 input_209 emitted_208 tokens_209
    step_208 replay_209

def input_207 : List Char := componentChars_207 ++ input_208
def tokens_207 : List String := emitted_207 ++ tokens_208
theorem replay_207 : Agreement point_207 point_281
    input_207 tokens_207 :=
  agreement_append point_207 point_208 point_281
    componentChars_207 input_208 emitted_207 tokens_208
    step_207 replay_208

def input_206 : List Char := componentChars_206 ++ input_207
def tokens_206 : List String := emitted_206 ++ tokens_207
theorem replay_206 : Agreement point_206 point_281
    input_206 tokens_206 :=
  agreement_append point_206 point_207 point_281
    componentChars_206 input_207 emitted_206 tokens_207
    step_206 replay_207

def input_205 : List Char := componentChars_205 ++ input_206
def tokens_205 : List String := emitted_205 ++ tokens_206
theorem replay_205 : Agreement point_205 point_281
    input_205 tokens_205 :=
  agreement_append point_205 point_206 point_281
    componentChars_205 input_206 emitted_205 tokens_206
    step_205 replay_206

def input_204 : List Char := componentChars_204 ++ input_205
def tokens_204 : List String := emitted_204 ++ tokens_205
theorem replay_204 : Agreement point_204 point_281
    input_204 tokens_204 :=
  agreement_append point_204 point_205 point_281
    componentChars_204 input_205 emitted_204 tokens_205
    step_204 replay_205

def input_203 : List Char := componentChars_203 ++ input_204
def tokens_203 : List String := emitted_203 ++ tokens_204
theorem replay_203 : Agreement point_203 point_281
    input_203 tokens_203 :=
  agreement_append point_203 point_204 point_281
    componentChars_203 input_204 emitted_203 tokens_204
    step_203 replay_204

def input_202 : List Char := componentChars_202 ++ input_203
def tokens_202 : List String := emitted_202 ++ tokens_203
theorem replay_202 : Agreement point_202 point_281
    input_202 tokens_202 :=
  agreement_append point_202 point_203 point_281
    componentChars_202 input_203 emitted_202 tokens_203
    step_202 replay_203

def input_201 : List Char := componentChars_201 ++ input_202
def tokens_201 : List String := emitted_201 ++ tokens_202
theorem replay_201 : Agreement point_201 point_281
    input_201 tokens_201 :=
  agreement_append point_201 point_202 point_281
    componentChars_201 input_202 emitted_201 tokens_202
    step_201 replay_202

def input_200 : List Char := componentChars_200 ++ input_201
def tokens_200 : List String := emitted_200 ++ tokens_201
theorem replay_200 : Agreement point_200 point_281
    input_200 tokens_200 :=
  agreement_append point_200 point_201 point_281
    componentChars_200 input_201 emitted_200 tokens_201
    step_200 replay_201

def input_199 : List Char := componentChars_199 ++ input_200
def tokens_199 : List String := emitted_199 ++ tokens_200
theorem replay_199 : Agreement point_199 point_281
    input_199 tokens_199 :=
  agreement_append point_199 point_200 point_281
    componentChars_199 input_200 emitted_199 tokens_200
    step_199 replay_200

def input_198 : List Char := componentChars_198 ++ input_199
def tokens_198 : List String := emitted_198 ++ tokens_199
theorem replay_198 : Agreement point_198 point_281
    input_198 tokens_198 :=
  agreement_append point_198 point_199 point_281
    componentChars_198 input_199 emitted_198 tokens_199
    step_198 replay_199

def input_197 : List Char := componentChars_197 ++ input_198
def tokens_197 : List String := emitted_197 ++ tokens_198
theorem replay_197 : Agreement point_197 point_281
    input_197 tokens_197 :=
  agreement_append point_197 point_198 point_281
    componentChars_197 input_198 emitted_197 tokens_198
    step_197 replay_198

def input_196 : List Char := componentChars_196 ++ input_197
def tokens_196 : List String := emitted_196 ++ tokens_197
theorem replay_196 : Agreement point_196 point_281
    input_196 tokens_196 :=
  agreement_append point_196 point_197 point_281
    componentChars_196 input_197 emitted_196 tokens_197
    step_196 replay_197

def input_195 : List Char := componentChars_195 ++ input_196
def tokens_195 : List String := emitted_195 ++ tokens_196
theorem replay_195 : Agreement point_195 point_281
    input_195 tokens_195 :=
  agreement_append point_195 point_196 point_281
    componentChars_195 input_196 emitted_195 tokens_196
    step_195 replay_196

def input_194 : List Char := componentChars_194 ++ input_195
def tokens_194 : List String := emitted_194 ++ tokens_195
theorem replay_194 : Agreement point_194 point_281
    input_194 tokens_194 :=
  agreement_append point_194 point_195 point_281
    componentChars_194 input_195 emitted_194 tokens_195
    step_194 replay_195

def input_193 : List Char := componentChars_193 ++ input_194
def tokens_193 : List String := emitted_193 ++ tokens_194
theorem replay_193 : Agreement point_193 point_281
    input_193 tokens_193 :=
  agreement_append point_193 point_194 point_281
    componentChars_193 input_194 emitted_193 tokens_194
    step_193 replay_194

def input_192 : List Char := componentChars_192 ++ input_193
def tokens_192 : List String := emitted_192 ++ tokens_193
theorem replay_192 : Agreement point_192 point_281
    input_192 tokens_192 :=
  agreement_append point_192 point_193 point_281
    componentChars_192 input_193 emitted_192 tokens_193
    step_192 replay_193

def input_191 : List Char := componentChars_191 ++ input_192
def tokens_191 : List String := emitted_191 ++ tokens_192
theorem replay_191 : Agreement point_191 point_281
    input_191 tokens_191 :=
  agreement_append point_191 point_192 point_281
    componentChars_191 input_192 emitted_191 tokens_192
    step_191 replay_192

def input_190 : List Char := componentChars_190 ++ input_191
def tokens_190 : List String := emitted_190 ++ tokens_191
theorem replay_190 : Agreement point_190 point_281
    input_190 tokens_190 :=
  agreement_append point_190 point_191 point_281
    componentChars_190 input_191 emitted_190 tokens_191
    step_190 replay_191

def input_189 : List Char := componentChars_189 ++ input_190
def tokens_189 : List String := emitted_189 ++ tokens_190
theorem replay_189 : Agreement point_189 point_281
    input_189 tokens_189 :=
  agreement_append point_189 point_190 point_281
    componentChars_189 input_190 emitted_189 tokens_190
    step_189 replay_190

def input_188 : List Char := componentChars_188 ++ input_189
def tokens_188 : List String := emitted_188 ++ tokens_189
theorem replay_188 : Agreement point_188 point_281
    input_188 tokens_188 :=
  agreement_append point_188 point_189 point_281
    componentChars_188 input_189 emitted_188 tokens_189
    step_188 replay_189

def input_187 : List Char := componentChars_187 ++ input_188
def tokens_187 : List String := emitted_187 ++ tokens_188
theorem replay_187 : Agreement point_187 point_281
    input_187 tokens_187 :=
  agreement_append point_187 point_188 point_281
    componentChars_187 input_188 emitted_187 tokens_188
    step_187 replay_188

def input_186 : List Char := componentChars_186 ++ input_187
def tokens_186 : List String := emitted_186 ++ tokens_187
theorem replay_186 : Agreement point_186 point_281
    input_186 tokens_186 :=
  agreement_append point_186 point_187 point_281
    componentChars_186 input_187 emitted_186 tokens_187
    step_186 replay_187

def input_185 : List Char := componentChars_185 ++ input_186
def tokens_185 : List String := emitted_185 ++ tokens_186
theorem replay_185 : Agreement point_185 point_281
    input_185 tokens_185 :=
  agreement_append point_185 point_186 point_281
    componentChars_185 input_186 emitted_185 tokens_186
    step_185 replay_186

def input_184 : List Char := componentChars_184 ++ input_185
def tokens_184 : List String := emitted_184 ++ tokens_185
theorem replay_184 : Agreement point_184 point_281
    input_184 tokens_184 :=
  agreement_append point_184 point_185 point_281
    componentChars_184 input_185 emitted_184 tokens_185
    step_184 replay_185

def input_183 : List Char := componentChars_183 ++ input_184
def tokens_183 : List String := emitted_183 ++ tokens_184
theorem replay_183 : Agreement point_183 point_281
    input_183 tokens_183 :=
  agreement_append point_183 point_184 point_281
    componentChars_183 input_184 emitted_183 tokens_184
    step_183 replay_184

def input_182 : List Char := componentChars_182 ++ input_183
def tokens_182 : List String := emitted_182 ++ tokens_183
theorem replay_182 : Agreement point_182 point_281
    input_182 tokens_182 :=
  agreement_append point_182 point_183 point_281
    componentChars_182 input_183 emitted_182 tokens_183
    step_182 replay_183

def input_181 : List Char := componentChars_181 ++ input_182
def tokens_181 : List String := emitted_181 ++ tokens_182
theorem replay_181 : Agreement point_181 point_281
    input_181 tokens_181 :=
  agreement_append point_181 point_182 point_281
    componentChars_181 input_182 emitted_181 tokens_182
    step_181 replay_182

def input_180 : List Char := componentChars_180 ++ input_181
def tokens_180 : List String := emitted_180 ++ tokens_181
theorem replay_180 : Agreement point_180 point_281
    input_180 tokens_180 :=
  agreement_append point_180 point_181 point_281
    componentChars_180 input_181 emitted_180 tokens_181
    step_180 replay_181

def input_179 : List Char := componentChars_179 ++ input_180
def tokens_179 : List String := emitted_179 ++ tokens_180
theorem replay_179 : Agreement point_179 point_281
    input_179 tokens_179 :=
  agreement_append point_179 point_180 point_281
    componentChars_179 input_180 emitted_179 tokens_180
    step_179 replay_180

def input_178 : List Char := componentChars_178 ++ input_179
def tokens_178 : List String := emitted_178 ++ tokens_179
theorem replay_178 : Agreement point_178 point_281
    input_178 tokens_178 :=
  agreement_append point_178 point_179 point_281
    componentChars_178 input_179 emitted_178 tokens_179
    step_178 replay_179

def input_177 : List Char := componentChars_177 ++ input_178
def tokens_177 : List String := emitted_177 ++ tokens_178
theorem replay_177 : Agreement point_177 point_281
    input_177 tokens_177 :=
  agreement_append point_177 point_178 point_281
    componentChars_177 input_178 emitted_177 tokens_178
    step_177 replay_178

def input_176 : List Char := componentChars_176 ++ input_177
def tokens_176 : List String := emitted_176 ++ tokens_177
theorem replay_176 : Agreement point_176 point_281
    input_176 tokens_176 :=
  agreement_append point_176 point_177 point_281
    componentChars_176 input_177 emitted_176 tokens_177
    step_176 replay_177

def input_175 : List Char := componentChars_175 ++ input_176
def tokens_175 : List String := emitted_175 ++ tokens_176
theorem replay_175 : Agreement point_175 point_281
    input_175 tokens_175 :=
  agreement_append point_175 point_176 point_281
    componentChars_175 input_176 emitted_175 tokens_176
    step_175 replay_176

def input_174 : List Char := componentChars_174 ++ input_175
def tokens_174 : List String := emitted_174 ++ tokens_175
theorem replay_174 : Agreement point_174 point_281
    input_174 tokens_174 :=
  agreement_append point_174 point_175 point_281
    componentChars_174 input_175 emitted_174 tokens_175
    step_174 replay_175

def input_173 : List Char := componentChars_173 ++ input_174
def tokens_173 : List String := emitted_173 ++ tokens_174
theorem replay_173 : Agreement point_173 point_281
    input_173 tokens_173 :=
  agreement_append point_173 point_174 point_281
    componentChars_173 input_174 emitted_173 tokens_174
    step_173 replay_174

def input_172 : List Char := componentChars_172 ++ input_173
def tokens_172 : List String := emitted_172 ++ tokens_173
theorem replay_172 : Agreement point_172 point_281
    input_172 tokens_172 :=
  agreement_append point_172 point_173 point_281
    componentChars_172 input_173 emitted_172 tokens_173
    step_172 replay_173

def input_171 : List Char := componentChars_171 ++ input_172
def tokens_171 : List String := emitted_171 ++ tokens_172
theorem replay_171 : Agreement point_171 point_281
    input_171 tokens_171 :=
  agreement_append point_171 point_172 point_281
    componentChars_171 input_172 emitted_171 tokens_172
    step_171 replay_172

def input_170 : List Char := componentChars_170 ++ input_171
def tokens_170 : List String := emitted_170 ++ tokens_171
theorem replay_170 : Agreement point_170 point_281
    input_170 tokens_170 :=
  agreement_append point_170 point_171 point_281
    componentChars_170 input_171 emitted_170 tokens_171
    step_170 replay_171

def input_169 : List Char := componentChars_169 ++ input_170
def tokens_169 : List String := emitted_169 ++ tokens_170
theorem replay_169 : Agreement point_169 point_281
    input_169 tokens_169 :=
  agreement_append point_169 point_170 point_281
    componentChars_169 input_170 emitted_169 tokens_170
    step_169 replay_170

def input_168 : List Char := componentChars_168 ++ input_169
def tokens_168 : List String := emitted_168 ++ tokens_169
theorem replay_168 : Agreement point_168 point_281
    input_168 tokens_168 :=
  agreement_append point_168 point_169 point_281
    componentChars_168 input_169 emitted_168 tokens_169
    step_168 replay_169

def input_167 : List Char := componentChars_167 ++ input_168
def tokens_167 : List String := emitted_167 ++ tokens_168
theorem replay_167 : Agreement point_167 point_281
    input_167 tokens_167 :=
  agreement_append point_167 point_168 point_281
    componentChars_167 input_168 emitted_167 tokens_168
    step_167 replay_168

def input_166 : List Char := componentChars_166 ++ input_167
def tokens_166 : List String := emitted_166 ++ tokens_167
theorem replay_166 : Agreement point_166 point_281
    input_166 tokens_166 :=
  agreement_append point_166 point_167 point_281
    componentChars_166 input_167 emitted_166 tokens_167
    step_166 replay_167

def input_165 : List Char := componentChars_165 ++ input_166
def tokens_165 : List String := emitted_165 ++ tokens_166
theorem replay_165 : Agreement point_165 point_281
    input_165 tokens_165 :=
  agreement_append point_165 point_166 point_281
    componentChars_165 input_166 emitted_165 tokens_166
    step_165 replay_166

def input_164 : List Char := componentChars_164 ++ input_165
def tokens_164 : List String := emitted_164 ++ tokens_165
theorem replay_164 : Agreement point_164 point_281
    input_164 tokens_164 :=
  agreement_append point_164 point_165 point_281
    componentChars_164 input_165 emitted_164 tokens_165
    step_164 replay_165

def input_163 : List Char := componentChars_163 ++ input_164
def tokens_163 : List String := emitted_163 ++ tokens_164
theorem replay_163 : Agreement point_163 point_281
    input_163 tokens_163 :=
  agreement_append point_163 point_164 point_281
    componentChars_163 input_164 emitted_163 tokens_164
    step_163 replay_164

def input_162 : List Char := componentChars_162 ++ input_163
def tokens_162 : List String := emitted_162 ++ tokens_163
theorem replay_162 : Agreement point_162 point_281
    input_162 tokens_162 :=
  agreement_append point_162 point_163 point_281
    componentChars_162 input_163 emitted_162 tokens_163
    step_162 replay_163

def input_161 : List Char := componentChars_161 ++ input_162
def tokens_161 : List String := emitted_161 ++ tokens_162
theorem replay_161 : Agreement point_161 point_281
    input_161 tokens_161 :=
  agreement_append point_161 point_162 point_281
    componentChars_161 input_162 emitted_161 tokens_162
    step_161 replay_162

def input_160 : List Char := componentChars_160 ++ input_161
def tokens_160 : List String := emitted_160 ++ tokens_161
theorem replay_160 : Agreement point_160 point_281
    input_160 tokens_160 :=
  agreement_append point_160 point_161 point_281
    componentChars_160 input_161 emitted_160 tokens_161
    step_160 replay_161

def input_159 : List Char := componentChars_159 ++ input_160
def tokens_159 : List String := emitted_159 ++ tokens_160
theorem replay_159 : Agreement point_159 point_281
    input_159 tokens_159 :=
  agreement_append point_159 point_160 point_281
    componentChars_159 input_160 emitted_159 tokens_160
    step_159 replay_160

def input_158 : List Char := componentChars_158 ++ input_159
def tokens_158 : List String := emitted_158 ++ tokens_159
theorem replay_158 : Agreement point_158 point_281
    input_158 tokens_158 :=
  agreement_append point_158 point_159 point_281
    componentChars_158 input_159 emitted_158 tokens_159
    step_158 replay_159

def input_157 : List Char := componentChars_157 ++ input_158
def tokens_157 : List String := emitted_157 ++ tokens_158
theorem replay_157 : Agreement point_157 point_281
    input_157 tokens_157 :=
  agreement_append point_157 point_158 point_281
    componentChars_157 input_158 emitted_157 tokens_158
    step_157 replay_158

def input_156 : List Char := componentChars_156 ++ input_157
def tokens_156 : List String := emitted_156 ++ tokens_157
theorem replay_156 : Agreement point_156 point_281
    input_156 tokens_156 :=
  agreement_append point_156 point_157 point_281
    componentChars_156 input_157 emitted_156 tokens_157
    step_156 replay_157

def input_155 : List Char := componentChars_155 ++ input_156
def tokens_155 : List String := emitted_155 ++ tokens_156
theorem replay_155 : Agreement point_155 point_281
    input_155 tokens_155 :=
  agreement_append point_155 point_156 point_281
    componentChars_155 input_156 emitted_155 tokens_156
    step_155 replay_156

def input_154 : List Char := componentChars_154 ++ input_155
def tokens_154 : List String := emitted_154 ++ tokens_155
theorem replay_154 : Agreement point_154 point_281
    input_154 tokens_154 :=
  agreement_append point_154 point_155 point_281
    componentChars_154 input_155 emitted_154 tokens_155
    step_154 replay_155

def input_153 : List Char := componentChars_153 ++ input_154
def tokens_153 : List String := emitted_153 ++ tokens_154
theorem replay_153 : Agreement point_153 point_281
    input_153 tokens_153 :=
  agreement_append point_153 point_154 point_281
    componentChars_153 input_154 emitted_153 tokens_154
    step_153 replay_154

def input_152 : List Char := componentChars_152 ++ input_153
def tokens_152 : List String := emitted_152 ++ tokens_153
theorem replay_152 : Agreement point_152 point_281
    input_152 tokens_152 :=
  agreement_append point_152 point_153 point_281
    componentChars_152 input_153 emitted_152 tokens_153
    step_152 replay_153

def input_151 : List Char := componentChars_151 ++ input_152
def tokens_151 : List String := emitted_151 ++ tokens_152
theorem replay_151 : Agreement point_151 point_281
    input_151 tokens_151 :=
  agreement_append point_151 point_152 point_281
    componentChars_151 input_152 emitted_151 tokens_152
    step_151 replay_152

def input_150 : List Char := componentChars_150 ++ input_151
def tokens_150 : List String := emitted_150 ++ tokens_151
theorem replay_150 : Agreement point_150 point_281
    input_150 tokens_150 :=
  agreement_append point_150 point_151 point_281
    componentChars_150 input_151 emitted_150 tokens_151
    step_150 replay_151

def input_149 : List Char := componentChars_149 ++ input_150
def tokens_149 : List String := emitted_149 ++ tokens_150
theorem replay_149 : Agreement point_149 point_281
    input_149 tokens_149 :=
  agreement_append point_149 point_150 point_281
    componentChars_149 input_150 emitted_149 tokens_150
    step_149 replay_150

def input_148 : List Char := componentChars_148 ++ input_149
def tokens_148 : List String := emitted_148 ++ tokens_149
theorem replay_148 : Agreement point_148 point_281
    input_148 tokens_148 :=
  agreement_append point_148 point_149 point_281
    componentChars_148 input_149 emitted_148 tokens_149
    step_148 replay_149

def input_147 : List Char := componentChars_147 ++ input_148
def tokens_147 : List String := emitted_147 ++ tokens_148
theorem replay_147 : Agreement point_147 point_281
    input_147 tokens_147 :=
  agreement_append point_147 point_148 point_281
    componentChars_147 input_148 emitted_147 tokens_148
    step_147 replay_148

def input_146 : List Char := componentChars_146 ++ input_147
def tokens_146 : List String := emitted_146 ++ tokens_147
theorem replay_146 : Agreement point_146 point_281
    input_146 tokens_146 :=
  agreement_append point_146 point_147 point_281
    componentChars_146 input_147 emitted_146 tokens_147
    step_146 replay_147

def input_145 : List Char := componentChars_145 ++ input_146
def tokens_145 : List String := emitted_145 ++ tokens_146
theorem replay_145 : Agreement point_145 point_281
    input_145 tokens_145 :=
  agreement_append point_145 point_146 point_281
    componentChars_145 input_146 emitted_145 tokens_146
    step_145 replay_146

def input_144 : List Char := componentChars_144 ++ input_145
def tokens_144 : List String := emitted_144 ++ tokens_145
theorem replay_144 : Agreement point_144 point_281
    input_144 tokens_144 :=
  agreement_append point_144 point_145 point_281
    componentChars_144 input_145 emitted_144 tokens_145
    step_144 replay_145

def input_143 : List Char := componentChars_143 ++ input_144
def tokens_143 : List String := emitted_143 ++ tokens_144
theorem replay_143 : Agreement point_143 point_281
    input_143 tokens_143 :=
  agreement_append point_143 point_144 point_281
    componentChars_143 input_144 emitted_143 tokens_144
    step_143 replay_144

def input_142 : List Char := componentChars_142 ++ input_143
def tokens_142 : List String := emitted_142 ++ tokens_143
theorem replay_142 : Agreement point_142 point_281
    input_142 tokens_142 :=
  agreement_append point_142 point_143 point_281
    componentChars_142 input_143 emitted_142 tokens_143
    step_142 replay_143

def input_141 : List Char := componentChars_141 ++ input_142
def tokens_141 : List String := emitted_141 ++ tokens_142
theorem replay_141 : Agreement point_141 point_281
    input_141 tokens_141 :=
  agreement_append point_141 point_142 point_281
    componentChars_141 input_142 emitted_141 tokens_142
    step_141 replay_142

def input_140 : List Char := componentChars_140 ++ input_141
def tokens_140 : List String := emitted_140 ++ tokens_141
theorem replay_140 : Agreement point_140 point_281
    input_140 tokens_140 :=
  agreement_append point_140 point_141 point_281
    componentChars_140 input_141 emitted_140 tokens_141
    step_140 replay_141

def input_139 : List Char := componentChars_139 ++ input_140
def tokens_139 : List String := emitted_139 ++ tokens_140
theorem replay_139 : Agreement point_139 point_281
    input_139 tokens_139 :=
  agreement_append point_139 point_140 point_281
    componentChars_139 input_140 emitted_139 tokens_140
    step_139 replay_140

def input_138 : List Char := componentChars_138 ++ input_139
def tokens_138 : List String := emitted_138 ++ tokens_139
theorem replay_138 : Agreement point_138 point_281
    input_138 tokens_138 :=
  agreement_append point_138 point_139 point_281
    componentChars_138 input_139 emitted_138 tokens_139
    step_138 replay_139

def input_137 : List Char := componentChars_137 ++ input_138
def tokens_137 : List String := emitted_137 ++ tokens_138
theorem replay_137 : Agreement point_137 point_281
    input_137 tokens_137 :=
  agreement_append point_137 point_138 point_281
    componentChars_137 input_138 emitted_137 tokens_138
    step_137 replay_138

def input_136 : List Char := componentChars_136 ++ input_137
def tokens_136 : List String := emitted_136 ++ tokens_137
theorem replay_136 : Agreement point_136 point_281
    input_136 tokens_136 :=
  agreement_append point_136 point_137 point_281
    componentChars_136 input_137 emitted_136 tokens_137
    step_136 replay_137

def input_135 : List Char := componentChars_135 ++ input_136
def tokens_135 : List String := emitted_135 ++ tokens_136
theorem replay_135 : Agreement point_135 point_281
    input_135 tokens_135 :=
  agreement_append point_135 point_136 point_281
    componentChars_135 input_136 emitted_135 tokens_136
    step_135 replay_136

def input_134 : List Char := componentChars_134 ++ input_135
def tokens_134 : List String := emitted_134 ++ tokens_135
theorem replay_134 : Agreement point_134 point_281
    input_134 tokens_134 :=
  agreement_append point_134 point_135 point_281
    componentChars_134 input_135 emitted_134 tokens_135
    step_134 replay_135

def input_133 : List Char := componentChars_133 ++ input_134
def tokens_133 : List String := emitted_133 ++ tokens_134
theorem replay_133 : Agreement point_133 point_281
    input_133 tokens_133 :=
  agreement_append point_133 point_134 point_281
    componentChars_133 input_134 emitted_133 tokens_134
    step_133 replay_134

def input_132 : List Char := componentChars_132 ++ input_133
def tokens_132 : List String := emitted_132 ++ tokens_133
theorem replay_132 : Agreement point_132 point_281
    input_132 tokens_132 :=
  agreement_append point_132 point_133 point_281
    componentChars_132 input_133 emitted_132 tokens_133
    step_132 replay_133

def input_131 : List Char := componentChars_131 ++ input_132
def tokens_131 : List String := emitted_131 ++ tokens_132
theorem replay_131 : Agreement point_131 point_281
    input_131 tokens_131 :=
  agreement_append point_131 point_132 point_281
    componentChars_131 input_132 emitted_131 tokens_132
    step_131 replay_132

def input_130 : List Char := componentChars_130 ++ input_131
def tokens_130 : List String := emitted_130 ++ tokens_131
theorem replay_130 : Agreement point_130 point_281
    input_130 tokens_130 :=
  agreement_append point_130 point_131 point_281
    componentChars_130 input_131 emitted_130 tokens_131
    step_130 replay_131

def input_129 : List Char := componentChars_129 ++ input_130
def tokens_129 : List String := emitted_129 ++ tokens_130
theorem replay_129 : Agreement point_129 point_281
    input_129 tokens_129 :=
  agreement_append point_129 point_130 point_281
    componentChars_129 input_130 emitted_129 tokens_130
    step_129 replay_130

def input_128 : List Char := componentChars_128 ++ input_129
def tokens_128 : List String := emitted_128 ++ tokens_129
theorem replay_128 : Agreement point_128 point_281
    input_128 tokens_128 :=
  agreement_append point_128 point_129 point_281
    componentChars_128 input_129 emitted_128 tokens_129
    step_128 replay_129

def input_127 : List Char := componentChars_127 ++ input_128
def tokens_127 : List String := emitted_127 ++ tokens_128
theorem replay_127 : Agreement point_127 point_281
    input_127 tokens_127 :=
  agreement_append point_127 point_128 point_281
    componentChars_127 input_128 emitted_127 tokens_128
    step_127 replay_128

def input_126 : List Char := componentChars_126 ++ input_127
def tokens_126 : List String := emitted_126 ++ tokens_127
theorem replay_126 : Agreement point_126 point_281
    input_126 tokens_126 :=
  agreement_append point_126 point_127 point_281
    componentChars_126 input_127 emitted_126 tokens_127
    step_126 replay_127

def input_125 : List Char := componentChars_125 ++ input_126
def tokens_125 : List String := emitted_125 ++ tokens_126
theorem replay_125 : Agreement point_125 point_281
    input_125 tokens_125 :=
  agreement_append point_125 point_126 point_281
    componentChars_125 input_126 emitted_125 tokens_126
    step_125 replay_126

def input_124 : List Char := componentChars_124 ++ input_125
def tokens_124 : List String := emitted_124 ++ tokens_125
theorem replay_124 : Agreement point_124 point_281
    input_124 tokens_124 :=
  agreement_append point_124 point_125 point_281
    componentChars_124 input_125 emitted_124 tokens_125
    step_124 replay_125

def input_123 : List Char := componentChars_123 ++ input_124
def tokens_123 : List String := emitted_123 ++ tokens_124
theorem replay_123 : Agreement point_123 point_281
    input_123 tokens_123 :=
  agreement_append point_123 point_124 point_281
    componentChars_123 input_124 emitted_123 tokens_124
    step_123 replay_124

def input_122 : List Char := componentChars_122 ++ input_123
def tokens_122 : List String := emitted_122 ++ tokens_123
theorem replay_122 : Agreement point_122 point_281
    input_122 tokens_122 :=
  agreement_append point_122 point_123 point_281
    componentChars_122 input_123 emitted_122 tokens_123
    step_122 replay_123

def input_121 : List Char := componentChars_121 ++ input_122
def tokens_121 : List String := emitted_121 ++ tokens_122
theorem replay_121 : Agreement point_121 point_281
    input_121 tokens_121 :=
  agreement_append point_121 point_122 point_281
    componentChars_121 input_122 emitted_121 tokens_122
    step_121 replay_122

def input_120 : List Char := componentChars_120 ++ input_121
def tokens_120 : List String := emitted_120 ++ tokens_121
theorem replay_120 : Agreement point_120 point_281
    input_120 tokens_120 :=
  agreement_append point_120 point_121 point_281
    componentChars_120 input_121 emitted_120 tokens_121
    step_120 replay_121

def input_119 : List Char := componentChars_119 ++ input_120
def tokens_119 : List String := emitted_119 ++ tokens_120
theorem replay_119 : Agreement point_119 point_281
    input_119 tokens_119 :=
  agreement_append point_119 point_120 point_281
    componentChars_119 input_120 emitted_119 tokens_120
    step_119 replay_120

def input_118 : List Char := componentChars_118 ++ input_119
def tokens_118 : List String := emitted_118 ++ tokens_119
theorem replay_118 : Agreement point_118 point_281
    input_118 tokens_118 :=
  agreement_append point_118 point_119 point_281
    componentChars_118 input_119 emitted_118 tokens_119
    step_118 replay_119

def input_117 : List Char := componentChars_117 ++ input_118
def tokens_117 : List String := emitted_117 ++ tokens_118
theorem replay_117 : Agreement point_117 point_281
    input_117 tokens_117 :=
  agreement_append point_117 point_118 point_281
    componentChars_117 input_118 emitted_117 tokens_118
    step_117 replay_118

def input_116 : List Char := componentChars_116 ++ input_117
def tokens_116 : List String := emitted_116 ++ tokens_117
theorem replay_116 : Agreement point_116 point_281
    input_116 tokens_116 :=
  agreement_append point_116 point_117 point_281
    componentChars_116 input_117 emitted_116 tokens_117
    step_116 replay_117

def input_115 : List Char := componentChars_115 ++ input_116
def tokens_115 : List String := emitted_115 ++ tokens_116
theorem replay_115 : Agreement point_115 point_281
    input_115 tokens_115 :=
  agreement_append point_115 point_116 point_281
    componentChars_115 input_116 emitted_115 tokens_116
    step_115 replay_116

def input_114 : List Char := componentChars_114 ++ input_115
def tokens_114 : List String := emitted_114 ++ tokens_115
theorem replay_114 : Agreement point_114 point_281
    input_114 tokens_114 :=
  agreement_append point_114 point_115 point_281
    componentChars_114 input_115 emitted_114 tokens_115
    step_114 replay_115

def input_113 : List Char := componentChars_113 ++ input_114
def tokens_113 : List String := emitted_113 ++ tokens_114
theorem replay_113 : Agreement point_113 point_281
    input_113 tokens_113 :=
  agreement_append point_113 point_114 point_281
    componentChars_113 input_114 emitted_113 tokens_114
    step_113 replay_114

def input_112 : List Char := componentChars_112 ++ input_113
def tokens_112 : List String := emitted_112 ++ tokens_113
theorem replay_112 : Agreement point_112 point_281
    input_112 tokens_112 :=
  agreement_append point_112 point_113 point_281
    componentChars_112 input_113 emitted_112 tokens_113
    step_112 replay_113

def input_111 : List Char := componentChars_111 ++ input_112
def tokens_111 : List String := emitted_111 ++ tokens_112
theorem replay_111 : Agreement point_111 point_281
    input_111 tokens_111 :=
  agreement_append point_111 point_112 point_281
    componentChars_111 input_112 emitted_111 tokens_112
    step_111 replay_112

def input_110 : List Char := componentChars_110 ++ input_111
def tokens_110 : List String := emitted_110 ++ tokens_111
theorem replay_110 : Agreement point_110 point_281
    input_110 tokens_110 :=
  agreement_append point_110 point_111 point_281
    componentChars_110 input_111 emitted_110 tokens_111
    step_110 replay_111

def input_109 : List Char := componentChars_109 ++ input_110
def tokens_109 : List String := emitted_109 ++ tokens_110
theorem replay_109 : Agreement point_109 point_281
    input_109 tokens_109 :=
  agreement_append point_109 point_110 point_281
    componentChars_109 input_110 emitted_109 tokens_110
    step_109 replay_110

def input_108 : List Char := componentChars_108 ++ input_109
def tokens_108 : List String := emitted_108 ++ tokens_109
theorem replay_108 : Agreement point_108 point_281
    input_108 tokens_108 :=
  agreement_append point_108 point_109 point_281
    componentChars_108 input_109 emitted_108 tokens_109
    step_108 replay_109

def input_107 : List Char := componentChars_107 ++ input_108
def tokens_107 : List String := emitted_107 ++ tokens_108
theorem replay_107 : Agreement point_107 point_281
    input_107 tokens_107 :=
  agreement_append point_107 point_108 point_281
    componentChars_107 input_108 emitted_107 tokens_108
    step_107 replay_108

def input_106 : List Char := componentChars_106 ++ input_107
def tokens_106 : List String := emitted_106 ++ tokens_107
theorem replay_106 : Agreement point_106 point_281
    input_106 tokens_106 :=
  agreement_append point_106 point_107 point_281
    componentChars_106 input_107 emitted_106 tokens_107
    step_106 replay_107

def input_105 : List Char := componentChars_105 ++ input_106
def tokens_105 : List String := emitted_105 ++ tokens_106
theorem replay_105 : Agreement point_105 point_281
    input_105 tokens_105 :=
  agreement_append point_105 point_106 point_281
    componentChars_105 input_106 emitted_105 tokens_106
    step_105 replay_106

def input_104 : List Char := componentChars_104 ++ input_105
def tokens_104 : List String := emitted_104 ++ tokens_105
theorem replay_104 : Agreement point_104 point_281
    input_104 tokens_104 :=
  agreement_append point_104 point_105 point_281
    componentChars_104 input_105 emitted_104 tokens_105
    step_104 replay_105

def input_103 : List Char := componentChars_103 ++ input_104
def tokens_103 : List String := emitted_103 ++ tokens_104
theorem replay_103 : Agreement point_103 point_281
    input_103 tokens_103 :=
  agreement_append point_103 point_104 point_281
    componentChars_103 input_104 emitted_103 tokens_104
    step_103 replay_104

def input_102 : List Char := componentChars_102 ++ input_103
def tokens_102 : List String := emitted_102 ++ tokens_103
theorem replay_102 : Agreement point_102 point_281
    input_102 tokens_102 :=
  agreement_append point_102 point_103 point_281
    componentChars_102 input_103 emitted_102 tokens_103
    step_102 replay_103

def input_101 : List Char := componentChars_101 ++ input_102
def tokens_101 : List String := emitted_101 ++ tokens_102
theorem replay_101 : Agreement point_101 point_281
    input_101 tokens_101 :=
  agreement_append point_101 point_102 point_281
    componentChars_101 input_102 emitted_101 tokens_102
    step_101 replay_102

def input_100 : List Char := componentChars_100 ++ input_101
def tokens_100 : List String := emitted_100 ++ tokens_101
theorem replay_100 : Agreement point_100 point_281
    input_100 tokens_100 :=
  agreement_append point_100 point_101 point_281
    componentChars_100 input_101 emitted_100 tokens_101
    step_100 replay_101

def input_099 : List Char := componentChars_099 ++ input_100
def tokens_099 : List String := emitted_099 ++ tokens_100
theorem replay_099 : Agreement point_099 point_281
    input_099 tokens_099 :=
  agreement_append point_099 point_100 point_281
    componentChars_099 input_100 emitted_099 tokens_100
    step_099 replay_100

def input_098 : List Char := componentChars_098 ++ input_099
def tokens_098 : List String := emitted_098 ++ tokens_099
theorem replay_098 : Agreement point_098 point_281
    input_098 tokens_098 :=
  agreement_append point_098 point_099 point_281
    componentChars_098 input_099 emitted_098 tokens_099
    step_098 replay_099

def input_097 : List Char := componentChars_097 ++ input_098
def tokens_097 : List String := emitted_097 ++ tokens_098
theorem replay_097 : Agreement point_097 point_281
    input_097 tokens_097 :=
  agreement_append point_097 point_098 point_281
    componentChars_097 input_098 emitted_097 tokens_098
    step_097 replay_098

def input_096 : List Char := componentChars_096 ++ input_097
def tokens_096 : List String := emitted_096 ++ tokens_097
theorem replay_096 : Agreement point_096 point_281
    input_096 tokens_096 :=
  agreement_append point_096 point_097 point_281
    componentChars_096 input_097 emitted_096 tokens_097
    step_096 replay_097

def input_095 : List Char := componentChars_095 ++ input_096
def tokens_095 : List String := emitted_095 ++ tokens_096
theorem replay_095 : Agreement point_095 point_281
    input_095 tokens_095 :=
  agreement_append point_095 point_096 point_281
    componentChars_095 input_096 emitted_095 tokens_096
    step_095 replay_096

def input_094 : List Char := componentChars_094 ++ input_095
def tokens_094 : List String := emitted_094 ++ tokens_095
theorem replay_094 : Agreement point_094 point_281
    input_094 tokens_094 :=
  agreement_append point_094 point_095 point_281
    componentChars_094 input_095 emitted_094 tokens_095
    step_094 replay_095

def input_093 : List Char := componentChars_093 ++ input_094
def tokens_093 : List String := emitted_093 ++ tokens_094
theorem replay_093 : Agreement point_093 point_281
    input_093 tokens_093 :=
  agreement_append point_093 point_094 point_281
    componentChars_093 input_094 emitted_093 tokens_094
    step_093 replay_094

def input_092 : List Char := componentChars_092 ++ input_093
def tokens_092 : List String := emitted_092 ++ tokens_093
theorem replay_092 : Agreement point_092 point_281
    input_092 tokens_092 :=
  agreement_append point_092 point_093 point_281
    componentChars_092 input_093 emitted_092 tokens_093
    step_092 replay_093

def input_091 : List Char := componentChars_091 ++ input_092
def tokens_091 : List String := emitted_091 ++ tokens_092
theorem replay_091 : Agreement point_091 point_281
    input_091 tokens_091 :=
  agreement_append point_091 point_092 point_281
    componentChars_091 input_092 emitted_091 tokens_092
    step_091 replay_092

def input_090 : List Char := componentChars_090 ++ input_091
def tokens_090 : List String := emitted_090 ++ tokens_091
theorem replay_090 : Agreement point_090 point_281
    input_090 tokens_090 :=
  agreement_append point_090 point_091 point_281
    componentChars_090 input_091 emitted_090 tokens_091
    step_090 replay_091

def input_089 : List Char := componentChars_089 ++ input_090
def tokens_089 : List String := emitted_089 ++ tokens_090
theorem replay_089 : Agreement point_089 point_281
    input_089 tokens_089 :=
  agreement_append point_089 point_090 point_281
    componentChars_089 input_090 emitted_089 tokens_090
    step_089 replay_090

def input_088 : List Char := componentChars_088 ++ input_089
def tokens_088 : List String := emitted_088 ++ tokens_089
theorem replay_088 : Agreement point_088 point_281
    input_088 tokens_088 :=
  agreement_append point_088 point_089 point_281
    componentChars_088 input_089 emitted_088 tokens_089
    step_088 replay_089

def input_087 : List Char := componentChars_087 ++ input_088
def tokens_087 : List String := emitted_087 ++ tokens_088
theorem replay_087 : Agreement point_087 point_281
    input_087 tokens_087 :=
  agreement_append point_087 point_088 point_281
    componentChars_087 input_088 emitted_087 tokens_088
    step_087 replay_088

def input_086 : List Char := componentChars_086 ++ input_087
def tokens_086 : List String := emitted_086 ++ tokens_087
theorem replay_086 : Agreement point_086 point_281
    input_086 tokens_086 :=
  agreement_append point_086 point_087 point_281
    componentChars_086 input_087 emitted_086 tokens_087
    step_086 replay_087

def input_085 : List Char := componentChars_085 ++ input_086
def tokens_085 : List String := emitted_085 ++ tokens_086
theorem replay_085 : Agreement point_085 point_281
    input_085 tokens_085 :=
  agreement_append point_085 point_086 point_281
    componentChars_085 input_086 emitted_085 tokens_086
    step_085 replay_086

def input_084 : List Char := componentChars_084 ++ input_085
def tokens_084 : List String := emitted_084 ++ tokens_085
theorem replay_084 : Agreement point_084 point_281
    input_084 tokens_084 :=
  agreement_append point_084 point_085 point_281
    componentChars_084 input_085 emitted_084 tokens_085
    step_084 replay_085

def input_083 : List Char := componentChars_083 ++ input_084
def tokens_083 : List String := emitted_083 ++ tokens_084
theorem replay_083 : Agreement point_083 point_281
    input_083 tokens_083 :=
  agreement_append point_083 point_084 point_281
    componentChars_083 input_084 emitted_083 tokens_084
    step_083 replay_084

def input_082 : List Char := componentChars_082 ++ input_083
def tokens_082 : List String := emitted_082 ++ tokens_083
theorem replay_082 : Agreement point_082 point_281
    input_082 tokens_082 :=
  agreement_append point_082 point_083 point_281
    componentChars_082 input_083 emitted_082 tokens_083
    step_082 replay_083

def input_081 : List Char := componentChars_081 ++ input_082
def tokens_081 : List String := emitted_081 ++ tokens_082
theorem replay_081 : Agreement point_081 point_281
    input_081 tokens_081 :=
  agreement_append point_081 point_082 point_281
    componentChars_081 input_082 emitted_081 tokens_082
    step_081 replay_082

def input_080 : List Char := componentChars_080 ++ input_081
def tokens_080 : List String := emitted_080 ++ tokens_081
theorem replay_080 : Agreement point_080 point_281
    input_080 tokens_080 :=
  agreement_append point_080 point_081 point_281
    componentChars_080 input_081 emitted_080 tokens_081
    step_080 replay_081

def input_079 : List Char := componentChars_079 ++ input_080
def tokens_079 : List String := emitted_079 ++ tokens_080
theorem replay_079 : Agreement point_079 point_281
    input_079 tokens_079 :=
  agreement_append point_079 point_080 point_281
    componentChars_079 input_080 emitted_079 tokens_080
    step_079 replay_080

def input_078 : List Char := componentChars_078 ++ input_079
def tokens_078 : List String := emitted_078 ++ tokens_079
theorem replay_078 : Agreement point_078 point_281
    input_078 tokens_078 :=
  agreement_append point_078 point_079 point_281
    componentChars_078 input_079 emitted_078 tokens_079
    step_078 replay_079

def input_077 : List Char := componentChars_077 ++ input_078
def tokens_077 : List String := emitted_077 ++ tokens_078
theorem replay_077 : Agreement point_077 point_281
    input_077 tokens_077 :=
  agreement_append point_077 point_078 point_281
    componentChars_077 input_078 emitted_077 tokens_078
    step_077 replay_078

def input_076 : List Char := componentChars_076 ++ input_077
def tokens_076 : List String := emitted_076 ++ tokens_077
theorem replay_076 : Agreement point_076 point_281
    input_076 tokens_076 :=
  agreement_append point_076 point_077 point_281
    componentChars_076 input_077 emitted_076 tokens_077
    step_076 replay_077

def input_075 : List Char := componentChars_075 ++ input_076
def tokens_075 : List String := emitted_075 ++ tokens_076
theorem replay_075 : Agreement point_075 point_281
    input_075 tokens_075 :=
  agreement_append point_075 point_076 point_281
    componentChars_075 input_076 emitted_075 tokens_076
    step_075 replay_076

def input_074 : List Char := componentChars_074 ++ input_075
def tokens_074 : List String := emitted_074 ++ tokens_075
theorem replay_074 : Agreement point_074 point_281
    input_074 tokens_074 :=
  agreement_append point_074 point_075 point_281
    componentChars_074 input_075 emitted_074 tokens_075
    step_074 replay_075

def input_073 : List Char := componentChars_073 ++ input_074
def tokens_073 : List String := emitted_073 ++ tokens_074
theorem replay_073 : Agreement point_073 point_281
    input_073 tokens_073 :=
  agreement_append point_073 point_074 point_281
    componentChars_073 input_074 emitted_073 tokens_074
    step_073 replay_074

def input_072 : List Char := componentChars_072 ++ input_073
def tokens_072 : List String := emitted_072 ++ tokens_073
theorem replay_072 : Agreement point_072 point_281
    input_072 tokens_072 :=
  agreement_append point_072 point_073 point_281
    componentChars_072 input_073 emitted_072 tokens_073
    step_072 replay_073

def input_071 : List Char := componentChars_071 ++ input_072
def tokens_071 : List String := emitted_071 ++ tokens_072
theorem replay_071 : Agreement point_071 point_281
    input_071 tokens_071 :=
  agreement_append point_071 point_072 point_281
    componentChars_071 input_072 emitted_071 tokens_072
    step_071 replay_072

def input_070 : List Char := componentChars_070 ++ input_071
def tokens_070 : List String := emitted_070 ++ tokens_071
theorem replay_070 : Agreement point_070 point_281
    input_070 tokens_070 :=
  agreement_append point_070 point_071 point_281
    componentChars_070 input_071 emitted_070 tokens_071
    step_070 replay_071

def input_069 : List Char := componentChars_069 ++ input_070
def tokens_069 : List String := emitted_069 ++ tokens_070
theorem replay_069 : Agreement point_069 point_281
    input_069 tokens_069 :=
  agreement_append point_069 point_070 point_281
    componentChars_069 input_070 emitted_069 tokens_070
    step_069 replay_070

def input_068 : List Char := componentChars_068 ++ input_069
def tokens_068 : List String := emitted_068 ++ tokens_069
theorem replay_068 : Agreement point_068 point_281
    input_068 tokens_068 :=
  agreement_append point_068 point_069 point_281
    componentChars_068 input_069 emitted_068 tokens_069
    step_068 replay_069

def input_067 : List Char := componentChars_067 ++ input_068
def tokens_067 : List String := emitted_067 ++ tokens_068
theorem replay_067 : Agreement point_067 point_281
    input_067 tokens_067 :=
  agreement_append point_067 point_068 point_281
    componentChars_067 input_068 emitted_067 tokens_068
    step_067 replay_068

def input_066 : List Char := componentChars_066 ++ input_067
def tokens_066 : List String := emitted_066 ++ tokens_067
theorem replay_066 : Agreement point_066 point_281
    input_066 tokens_066 :=
  agreement_append point_066 point_067 point_281
    componentChars_066 input_067 emitted_066 tokens_067
    step_066 replay_067

def input_065 : List Char := componentChars_065 ++ input_066
def tokens_065 : List String := emitted_065 ++ tokens_066
theorem replay_065 : Agreement point_065 point_281
    input_065 tokens_065 :=
  agreement_append point_065 point_066 point_281
    componentChars_065 input_066 emitted_065 tokens_066
    step_065 replay_066

def input_064 : List Char := componentChars_064 ++ input_065
def tokens_064 : List String := emitted_064 ++ tokens_065
theorem replay_064 : Agreement point_064 point_281
    input_064 tokens_064 :=
  agreement_append point_064 point_065 point_281
    componentChars_064 input_065 emitted_064 tokens_065
    step_064 replay_065

def input_063 : List Char := componentChars_063 ++ input_064
def tokens_063 : List String := emitted_063 ++ tokens_064
theorem replay_063 : Agreement point_063 point_281
    input_063 tokens_063 :=
  agreement_append point_063 point_064 point_281
    componentChars_063 input_064 emitted_063 tokens_064
    step_063 replay_064

def input_062 : List Char := componentChars_062 ++ input_063
def tokens_062 : List String := emitted_062 ++ tokens_063
theorem replay_062 : Agreement point_062 point_281
    input_062 tokens_062 :=
  agreement_append point_062 point_063 point_281
    componentChars_062 input_063 emitted_062 tokens_063
    step_062 replay_063

def input_061 : List Char := componentChars_061 ++ input_062
def tokens_061 : List String := emitted_061 ++ tokens_062
theorem replay_061 : Agreement point_061 point_281
    input_061 tokens_061 :=
  agreement_append point_061 point_062 point_281
    componentChars_061 input_062 emitted_061 tokens_062
    step_061 replay_062

def input_060 : List Char := componentChars_060 ++ input_061
def tokens_060 : List String := emitted_060 ++ tokens_061
theorem replay_060 : Agreement point_060 point_281
    input_060 tokens_060 :=
  agreement_append point_060 point_061 point_281
    componentChars_060 input_061 emitted_060 tokens_061
    step_060 replay_061

def input_059 : List Char := componentChars_059 ++ input_060
def tokens_059 : List String := emitted_059 ++ tokens_060
theorem replay_059 : Agreement point_059 point_281
    input_059 tokens_059 :=
  agreement_append point_059 point_060 point_281
    componentChars_059 input_060 emitted_059 tokens_060
    step_059 replay_060

def input_058 : List Char := componentChars_058 ++ input_059
def tokens_058 : List String := emitted_058 ++ tokens_059
theorem replay_058 : Agreement point_058 point_281
    input_058 tokens_058 :=
  agreement_append point_058 point_059 point_281
    componentChars_058 input_059 emitted_058 tokens_059
    step_058 replay_059

def input_057 : List Char := componentChars_057 ++ input_058
def tokens_057 : List String := emitted_057 ++ tokens_058
theorem replay_057 : Agreement point_057 point_281
    input_057 tokens_057 :=
  agreement_append point_057 point_058 point_281
    componentChars_057 input_058 emitted_057 tokens_058
    step_057 replay_058

def input_056 : List Char := componentChars_056 ++ input_057
def tokens_056 : List String := emitted_056 ++ tokens_057
theorem replay_056 : Agreement point_056 point_281
    input_056 tokens_056 :=
  agreement_append point_056 point_057 point_281
    componentChars_056 input_057 emitted_056 tokens_057
    step_056 replay_057

def input_055 : List Char := componentChars_055 ++ input_056
def tokens_055 : List String := emitted_055 ++ tokens_056
theorem replay_055 : Agreement point_055 point_281
    input_055 tokens_055 :=
  agreement_append point_055 point_056 point_281
    componentChars_055 input_056 emitted_055 tokens_056
    step_055 replay_056

def input_054 : List Char := componentChars_054 ++ input_055
def tokens_054 : List String := emitted_054 ++ tokens_055
theorem replay_054 : Agreement point_054 point_281
    input_054 tokens_054 :=
  agreement_append point_054 point_055 point_281
    componentChars_054 input_055 emitted_054 tokens_055
    step_054 replay_055

def input_053 : List Char := componentChars_053 ++ input_054
def tokens_053 : List String := emitted_053 ++ tokens_054
theorem replay_053 : Agreement point_053 point_281
    input_053 tokens_053 :=
  agreement_append point_053 point_054 point_281
    componentChars_053 input_054 emitted_053 tokens_054
    step_053 replay_054

def input_052 : List Char := componentChars_052 ++ input_053
def tokens_052 : List String := emitted_052 ++ tokens_053
theorem replay_052 : Agreement point_052 point_281
    input_052 tokens_052 :=
  agreement_append point_052 point_053 point_281
    componentChars_052 input_053 emitted_052 tokens_053
    step_052 replay_053

def input_051 : List Char := componentChars_051 ++ input_052
def tokens_051 : List String := emitted_051 ++ tokens_052
theorem replay_051 : Agreement point_051 point_281
    input_051 tokens_051 :=
  agreement_append point_051 point_052 point_281
    componentChars_051 input_052 emitted_051 tokens_052
    step_051 replay_052

def input_050 : List Char := componentChars_050 ++ input_051
def tokens_050 : List String := emitted_050 ++ tokens_051
theorem replay_050 : Agreement point_050 point_281
    input_050 tokens_050 :=
  agreement_append point_050 point_051 point_281
    componentChars_050 input_051 emitted_050 tokens_051
    step_050 replay_051

def input_049 : List Char := componentChars_049 ++ input_050
def tokens_049 : List String := emitted_049 ++ tokens_050
theorem replay_049 : Agreement point_049 point_281
    input_049 tokens_049 :=
  agreement_append point_049 point_050 point_281
    componentChars_049 input_050 emitted_049 tokens_050
    step_049 replay_050

def input_048 : List Char := componentChars_048 ++ input_049
def tokens_048 : List String := emitted_048 ++ tokens_049
theorem replay_048 : Agreement point_048 point_281
    input_048 tokens_048 :=
  agreement_append point_048 point_049 point_281
    componentChars_048 input_049 emitted_048 tokens_049
    step_048 replay_049

def input_047 : List Char := componentChars_047 ++ input_048
def tokens_047 : List String := emitted_047 ++ tokens_048
theorem replay_047 : Agreement point_047 point_281
    input_047 tokens_047 :=
  agreement_append point_047 point_048 point_281
    componentChars_047 input_048 emitted_047 tokens_048
    step_047 replay_048

def input_046 : List Char := componentChars_046 ++ input_047
def tokens_046 : List String := emitted_046 ++ tokens_047
theorem replay_046 : Agreement point_046 point_281
    input_046 tokens_046 :=
  agreement_append point_046 point_047 point_281
    componentChars_046 input_047 emitted_046 tokens_047
    step_046 replay_047

def input_045 : List Char := componentChars_045 ++ input_046
def tokens_045 : List String := emitted_045 ++ tokens_046
theorem replay_045 : Agreement point_045 point_281
    input_045 tokens_045 :=
  agreement_append point_045 point_046 point_281
    componentChars_045 input_046 emitted_045 tokens_046
    step_045 replay_046

def input_044 : List Char := componentChars_044 ++ input_045
def tokens_044 : List String := emitted_044 ++ tokens_045
theorem replay_044 : Agreement point_044 point_281
    input_044 tokens_044 :=
  agreement_append point_044 point_045 point_281
    componentChars_044 input_045 emitted_044 tokens_045
    step_044 replay_045

def input_043 : List Char := componentChars_043 ++ input_044
def tokens_043 : List String := emitted_043 ++ tokens_044
theorem replay_043 : Agreement point_043 point_281
    input_043 tokens_043 :=
  agreement_append point_043 point_044 point_281
    componentChars_043 input_044 emitted_043 tokens_044
    step_043 replay_044

def input_042 : List Char := componentChars_042 ++ input_043
def tokens_042 : List String := emitted_042 ++ tokens_043
theorem replay_042 : Agreement point_042 point_281
    input_042 tokens_042 :=
  agreement_append point_042 point_043 point_281
    componentChars_042 input_043 emitted_042 tokens_043
    step_042 replay_043

def input_041 : List Char := componentChars_041 ++ input_042
def tokens_041 : List String := emitted_041 ++ tokens_042
theorem replay_041 : Agreement point_041 point_281
    input_041 tokens_041 :=
  agreement_append point_041 point_042 point_281
    componentChars_041 input_042 emitted_041 tokens_042
    step_041 replay_042

def input_040 : List Char := componentChars_040 ++ input_041
def tokens_040 : List String := emitted_040 ++ tokens_041
theorem replay_040 : Agreement point_040 point_281
    input_040 tokens_040 :=
  agreement_append point_040 point_041 point_281
    componentChars_040 input_041 emitted_040 tokens_041
    step_040 replay_041

def input_039 : List Char := componentChars_039 ++ input_040
def tokens_039 : List String := emitted_039 ++ tokens_040
theorem replay_039 : Agreement point_039 point_281
    input_039 tokens_039 :=
  agreement_append point_039 point_040 point_281
    componentChars_039 input_040 emitted_039 tokens_040
    step_039 replay_040

def input_038 : List Char := componentChars_038 ++ input_039
def tokens_038 : List String := emitted_038 ++ tokens_039
theorem replay_038 : Agreement point_038 point_281
    input_038 tokens_038 :=
  agreement_append point_038 point_039 point_281
    componentChars_038 input_039 emitted_038 tokens_039
    step_038 replay_039

def input_037 : List Char := componentChars_037 ++ input_038
def tokens_037 : List String := emitted_037 ++ tokens_038
theorem replay_037 : Agreement point_037 point_281
    input_037 tokens_037 :=
  agreement_append point_037 point_038 point_281
    componentChars_037 input_038 emitted_037 tokens_038
    step_037 replay_038

def input_036 : List Char := componentChars_036 ++ input_037
def tokens_036 : List String := emitted_036 ++ tokens_037
theorem replay_036 : Agreement point_036 point_281
    input_036 tokens_036 :=
  agreement_append point_036 point_037 point_281
    componentChars_036 input_037 emitted_036 tokens_037
    step_036 replay_037

def input_035 : List Char := componentChars_035 ++ input_036
def tokens_035 : List String := emitted_035 ++ tokens_036
theorem replay_035 : Agreement point_035 point_281
    input_035 tokens_035 :=
  agreement_append point_035 point_036 point_281
    componentChars_035 input_036 emitted_035 tokens_036
    step_035 replay_036

def input_034 : List Char := componentChars_034 ++ input_035
def tokens_034 : List String := emitted_034 ++ tokens_035
theorem replay_034 : Agreement point_034 point_281
    input_034 tokens_034 :=
  agreement_append point_034 point_035 point_281
    componentChars_034 input_035 emitted_034 tokens_035
    step_034 replay_035

def input_033 : List Char := componentChars_033 ++ input_034
def tokens_033 : List String := emitted_033 ++ tokens_034
theorem replay_033 : Agreement point_033 point_281
    input_033 tokens_033 :=
  agreement_append point_033 point_034 point_281
    componentChars_033 input_034 emitted_033 tokens_034
    step_033 replay_034

def input_032 : List Char := componentChars_032 ++ input_033
def tokens_032 : List String := emitted_032 ++ tokens_033
theorem replay_032 : Agreement point_032 point_281
    input_032 tokens_032 :=
  agreement_append point_032 point_033 point_281
    componentChars_032 input_033 emitted_032 tokens_033
    step_032 replay_033

def input_031 : List Char := componentChars_031 ++ input_032
def tokens_031 : List String := emitted_031 ++ tokens_032
theorem replay_031 : Agreement point_031 point_281
    input_031 tokens_031 :=
  agreement_append point_031 point_032 point_281
    componentChars_031 input_032 emitted_031 tokens_032
    step_031 replay_032

def input_030 : List Char := componentChars_030 ++ input_031
def tokens_030 : List String := emitted_030 ++ tokens_031
theorem replay_030 : Agreement point_030 point_281
    input_030 tokens_030 :=
  agreement_append point_030 point_031 point_281
    componentChars_030 input_031 emitted_030 tokens_031
    step_030 replay_031

def input_029 : List Char := componentChars_029 ++ input_030
def tokens_029 : List String := emitted_029 ++ tokens_030
theorem replay_029 : Agreement point_029 point_281
    input_029 tokens_029 :=
  agreement_append point_029 point_030 point_281
    componentChars_029 input_030 emitted_029 tokens_030
    step_029 replay_030

def input_028 : List Char := componentChars_028 ++ input_029
def tokens_028 : List String := emitted_028 ++ tokens_029
theorem replay_028 : Agreement point_028 point_281
    input_028 tokens_028 :=
  agreement_append point_028 point_029 point_281
    componentChars_028 input_029 emitted_028 tokens_029
    step_028 replay_029

def input_027 : List Char := componentChars_027 ++ input_028
def tokens_027 : List String := emitted_027 ++ tokens_028
theorem replay_027 : Agreement point_027 point_281
    input_027 tokens_027 :=
  agreement_append point_027 point_028 point_281
    componentChars_027 input_028 emitted_027 tokens_028
    step_027 replay_028

def input_026 : List Char := componentChars_026 ++ input_027
def tokens_026 : List String := emitted_026 ++ tokens_027
theorem replay_026 : Agreement point_026 point_281
    input_026 tokens_026 :=
  agreement_append point_026 point_027 point_281
    componentChars_026 input_027 emitted_026 tokens_027
    step_026 replay_027

def input_025 : List Char := componentChars_025 ++ input_026
def tokens_025 : List String := emitted_025 ++ tokens_026
theorem replay_025 : Agreement point_025 point_281
    input_025 tokens_025 :=
  agreement_append point_025 point_026 point_281
    componentChars_025 input_026 emitted_025 tokens_026
    step_025 replay_026

def input_024 : List Char := componentChars_024 ++ input_025
def tokens_024 : List String := emitted_024 ++ tokens_025
theorem replay_024 : Agreement point_024 point_281
    input_024 tokens_024 :=
  agreement_append point_024 point_025 point_281
    componentChars_024 input_025 emitted_024 tokens_025
    step_024 replay_025

def input_023 : List Char := componentChars_023 ++ input_024
def tokens_023 : List String := emitted_023 ++ tokens_024
theorem replay_023 : Agreement point_023 point_281
    input_023 tokens_023 :=
  agreement_append point_023 point_024 point_281
    componentChars_023 input_024 emitted_023 tokens_024
    step_023 replay_024

def input_022 : List Char := componentChars_022 ++ input_023
def tokens_022 : List String := emitted_022 ++ tokens_023
theorem replay_022 : Agreement point_022 point_281
    input_022 tokens_022 :=
  agreement_append point_022 point_023 point_281
    componentChars_022 input_023 emitted_022 tokens_023
    step_022 replay_023

def input_021 : List Char := componentChars_021 ++ input_022
def tokens_021 : List String := emitted_021 ++ tokens_022
theorem replay_021 : Agreement point_021 point_281
    input_021 tokens_021 :=
  agreement_append point_021 point_022 point_281
    componentChars_021 input_022 emitted_021 tokens_022
    step_021 replay_022

def input_020 : List Char := componentChars_020 ++ input_021
def tokens_020 : List String := emitted_020 ++ tokens_021
theorem replay_020 : Agreement point_020 point_281
    input_020 tokens_020 :=
  agreement_append point_020 point_021 point_281
    componentChars_020 input_021 emitted_020 tokens_021
    step_020 replay_021

def input_019 : List Char := componentChars_019 ++ input_020
def tokens_019 : List String := emitted_019 ++ tokens_020
theorem replay_019 : Agreement point_019 point_281
    input_019 tokens_019 :=
  agreement_append point_019 point_020 point_281
    componentChars_019 input_020 emitted_019 tokens_020
    step_019 replay_020

def input_018 : List Char := componentChars_018 ++ input_019
def tokens_018 : List String := emitted_018 ++ tokens_019
theorem replay_018 : Agreement point_018 point_281
    input_018 tokens_018 :=
  agreement_append point_018 point_019 point_281
    componentChars_018 input_019 emitted_018 tokens_019
    step_018 replay_019

def input_017 : List Char := componentChars_017 ++ input_018
def tokens_017 : List String := emitted_017 ++ tokens_018
theorem replay_017 : Agreement point_017 point_281
    input_017 tokens_017 :=
  agreement_append point_017 point_018 point_281
    componentChars_017 input_018 emitted_017 tokens_018
    step_017 replay_018

def input_016 : List Char := componentChars_016 ++ input_017
def tokens_016 : List String := emitted_016 ++ tokens_017
theorem replay_016 : Agreement point_016 point_281
    input_016 tokens_016 :=
  agreement_append point_016 point_017 point_281
    componentChars_016 input_017 emitted_016 tokens_017
    step_016 replay_017

def input_015 : List Char := componentChars_015 ++ input_016
def tokens_015 : List String := emitted_015 ++ tokens_016
theorem replay_015 : Agreement point_015 point_281
    input_015 tokens_015 :=
  agreement_append point_015 point_016 point_281
    componentChars_015 input_016 emitted_015 tokens_016
    step_015 replay_016

def input_014 : List Char := componentChars_014 ++ input_015
def tokens_014 : List String := emitted_014 ++ tokens_015
theorem replay_014 : Agreement point_014 point_281
    input_014 tokens_014 :=
  agreement_append point_014 point_015 point_281
    componentChars_014 input_015 emitted_014 tokens_015
    step_014 replay_015

def input_013 : List Char := componentChars_013 ++ input_014
def tokens_013 : List String := emitted_013 ++ tokens_014
theorem replay_013 : Agreement point_013 point_281
    input_013 tokens_013 :=
  agreement_append point_013 point_014 point_281
    componentChars_013 input_014 emitted_013 tokens_014
    step_013 replay_014

def input_012 : List Char := componentChars_012 ++ input_013
def tokens_012 : List String := emitted_012 ++ tokens_013
theorem replay_012 : Agreement point_012 point_281
    input_012 tokens_012 :=
  agreement_append point_012 point_013 point_281
    componentChars_012 input_013 emitted_012 tokens_013
    step_012 replay_013

def input_011 : List Char := componentChars_011 ++ input_012
def tokens_011 : List String := emitted_011 ++ tokens_012
theorem replay_011 : Agreement point_011 point_281
    input_011 tokens_011 :=
  agreement_append point_011 point_012 point_281
    componentChars_011 input_012 emitted_011 tokens_012
    step_011 replay_012

def input_010 : List Char := componentChars_010 ++ input_011
def tokens_010 : List String := emitted_010 ++ tokens_011
theorem replay_010 : Agreement point_010 point_281
    input_010 tokens_010 :=
  agreement_append point_010 point_011 point_281
    componentChars_010 input_011 emitted_010 tokens_011
    step_010 replay_011

def input_009 : List Char := componentChars_009 ++ input_010
def tokens_009 : List String := emitted_009 ++ tokens_010
theorem replay_009 : Agreement point_009 point_281
    input_009 tokens_009 :=
  agreement_append point_009 point_010 point_281
    componentChars_009 input_010 emitted_009 tokens_010
    step_009 replay_010

def input_008 : List Char := componentChars_008 ++ input_009
def tokens_008 : List String := emitted_008 ++ tokens_009
theorem replay_008 : Agreement point_008 point_281
    input_008 tokens_008 :=
  agreement_append point_008 point_009 point_281
    componentChars_008 input_009 emitted_008 tokens_009
    step_008 replay_009

def input_007 : List Char := componentChars_007 ++ input_008
def tokens_007 : List String := emitted_007 ++ tokens_008
theorem replay_007 : Agreement point_007 point_281
    input_007 tokens_007 :=
  agreement_append point_007 point_008 point_281
    componentChars_007 input_008 emitted_007 tokens_008
    step_007 replay_008

def input_006 : List Char := componentChars_006 ++ input_007
def tokens_006 : List String := emitted_006 ++ tokens_007
theorem replay_006 : Agreement point_006 point_281
    input_006 tokens_006 :=
  agreement_append point_006 point_007 point_281
    componentChars_006 input_007 emitted_006 tokens_007
    step_006 replay_007

def input_005 : List Char := componentChars_005 ++ input_006
def tokens_005 : List String := emitted_005 ++ tokens_006
theorem replay_005 : Agreement point_005 point_281
    input_005 tokens_005 :=
  agreement_append point_005 point_006 point_281
    componentChars_005 input_006 emitted_005 tokens_006
    step_005 replay_006

def input_004 : List Char := componentChars_004 ++ input_005
def tokens_004 : List String := emitted_004 ++ tokens_005
theorem replay_004 : Agreement point_004 point_281
    input_004 tokens_004 :=
  agreement_append point_004 point_005 point_281
    componentChars_004 input_005 emitted_004 tokens_005
    step_004 replay_005

def input_003 : List Char := componentChars_003 ++ input_004
def tokens_003 : List String := emitted_003 ++ tokens_004
theorem replay_003 : Agreement point_003 point_281
    input_003 tokens_003 :=
  agreement_append point_003 point_004 point_281
    componentChars_003 input_004 emitted_003 tokens_004
    step_003 replay_004

def input_002 : List Char := componentChars_002 ++ input_003
def tokens_002 : List String := emitted_002 ++ tokens_003
theorem replay_002 : Agreement point_002 point_281
    input_002 tokens_002 :=
  agreement_append point_002 point_003 point_281
    componentChars_002 input_003 emitted_002 tokens_003
    step_002 replay_003

def input_001 : List Char := componentChars_001 ++ input_002
def tokens_001 : List String := emitted_001 ++ tokens_002
theorem replay_001 : Agreement point_001 point_281
    input_001 tokens_001 :=
  agreement_append point_001 point_002 point_281
    componentChars_001 input_002 emitted_001 tokens_002
    step_001 replay_002

def input_000 : List Char := componentChars_000 ++ input_001
def tokens_000 : List String := emitted_000 ++ tokens_001
theorem replay_000 : Agreement point_000 point_281
    input_000 tokens_000 :=
  agreement_append point_000 point_001 point_281
    componentChars_000 input_001 emitted_000 tokens_001
    step_000 replay_001

theorem input_characters_exact : input_000 = componentChars := rfl

theorem tokens_exact : tokens_000 =
    Mettapedia.GSLT.Parsing.SExprTokenRoundTrip.tokens sourceSyntax := by rfl

theorem lexed_exact : Mettapedia.GSLT.Parsing.SourceLexSegments.lex input_000 [] [] =
    Mettapedia.GSLT.Parsing.SExprTokenRoundTrip.tokens sourceSyntax := by
  exact (original_lexer_replay input_000 tokens_000 replay_000).trans tokens_exact

theorem tokenized_exact : tokenizeWith (parserDialectOf MeTTailCore.MeTTaSyntax.petta)
    componentText = Mettapedia.GSLT.Parsing.SExprTokenRoundTrip.tokens sourceSyntax :=
  Mettapedia.GSLT.Parsing.SourceLexSegments.tokenized_of_initial
    componentText componentChars input_000 [] []
    (Mettapedia.GSLT.Parsing.SExprTokenRoundTrip.tokens sourceSyntax)
    rfl input_characters_exact rfl rfl lexed_exact

end Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestLex
