import collections.generated
import core.generated

noncomputable theory

open bool
open [class] classical
open [notation] function
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

inductive syntax_pos.BytePos :=
mk {} : u32 → syntax_pos.BytePos

inductive syntax_pos.ExpnId :=
mk {} : u32 → syntax_pos.ExpnId

structure syntax_pos.Span := mk {} ::
(lo : (syntax_pos.BytePos))
(hi : (syntax_pos.BytePos))
(expn_id : (syntax_pos.ExpnId))

structure syntax_pos.MultiSpan := mk {} ::
(primary_spans : (collections.vec.Vec (syntax_pos.Span)))
(span_labels : (collections.vec.Vec ((syntax_pos.Span) × (collections.string.String))))

