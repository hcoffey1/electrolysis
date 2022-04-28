import collections.generated
import core.generated
import syntax_pos.generated

noncomputable theory

open bool
open [class] classical
open [notation] function
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

inductive rustc_errors.Level :=
| Bug {} : rustc_errors.Level
| Fatal {} : rustc_errors.Level
| PhaseFatal {} : rustc_errors.Level
| Error {} : rustc_errors.Level
| Warning {} : rustc_errors.Level
| Note {} : rustc_errors.Level
| Help {} : rustc_errors.Level
| Cancelled {} : rustc_errors.Level

definition rustc_errors.Level.discr (self : rustc_errors.Level) : isize := match self with
| rustc_errors.Level.Bug := 0
| rustc_errors.Level.Fatal := 1
| rustc_errors.Level.PhaseFatal := 2
| rustc_errors.Level.Error := 3
| rustc_errors.Level.Warning := 4
| rustc_errors.Level.Note := 5
| rustc_errors.Level.Help := 6
| rustc_errors.Level.Cancelled := 7
end

structure rustc_errors.CodeSuggestion := mk {} ::
(msp : (syntax_pos.MultiSpan))
(substitutes : (collections.vec.Vec (collections.string.String)))

inductive rustc_errors.RenderSpan :=
| FullSpan {} : (syntax_pos.MultiSpan) → rustc_errors.RenderSpan
| Suggestion {} : (rustc_errors.CodeSuggestion) → rustc_errors.RenderSpan

structure rustc_errors.diagnostic.SubDiagnostic := mk {} ::
(level : (rustc_errors.Level))
(message : (collections.string.String))
(span : (syntax_pos.MultiSpan))
(render_span : (core.option.Option (rustc_errors.RenderSpan)))

structure rustc_errors.diagnostic.Diagnostic := mk {} ::
(level : (rustc_errors.Level))
(message : (collections.string.String))
(code : (core.option.Option (collections.string.String)))
(span : (syntax_pos.MultiSpan))
(children : (collections.vec.Vec (rustc_errors.diagnostic.SubDiagnostic)))

