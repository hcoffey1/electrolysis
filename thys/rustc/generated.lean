import core.generated
import rustc_errors.generated

noncomputable theory

open bool
open [class] classical
open [notation] function
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

inductive rustc.lint.Level :=
| Allow {} : rustc.lint.Level
| Warn {} : rustc.lint.Level
| Deny {} : rustc.lint.Level
| Forbid {} : rustc.lint.Level

definition rustc.lint.Level.discr (self : rustc.lint.Level) : isize := match self with
| rustc.lint.Level.Allow := 0
| rustc.lint.Level.Warn := 1
| rustc.lint.Level.Deny := 2
| rustc.lint.Level.Forbid := 3
end

structure rustc.lint.Lint := mk {} ::
(name : string)
(default_level : (rustc.lint.Level))
(desc : string)

structure rustc.lint.LintId := mk {} ::
(lint : (rustc.lint.Lint))

structure rustc.lint.context.EarlyLint := mk {} ::
(id : (rustc.lint.LintId))
(diagnostic : (rustc_errors.diagnostic.Diagnostic))

