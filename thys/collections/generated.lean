import collections.pre
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
open collections

definition collections.«[T]».len {T : Type₁} (selfₐ : (slice T)) : sem (usize) :=
let' «self$2» ← selfₐ;
let' t3 ← «self$2»;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».len T t3;
let' ret ← «$tmp»;
return (ret)


definition collections.«[T]».is_empty {T : Type₁} (selfₐ : (slice T)) : sem (bool) :=
let' «self$2» ← selfₐ;
let' t3 ← «self$2»;
dostep «$tmp» ← @core.slice.SliceExt.is_empty (slice T) T (@core.«[T] as core.slice.SliceExt» T) t3;
let' ret ← «$tmp»;
return (ret)


definition collections.«[T]».get {T : Type₁} (selfₐ : (slice T)) (indexₐ : usize) : sem ((core.option.Option T)) :=
let' «self$3» ← selfₐ;
let' «index$4» ← indexₐ;
let' t5 ← «self$3»;
let' t6 ← «index$4»;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».get T t5 t6;
let' ret ← «$tmp»;
return (ret)


