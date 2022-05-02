import core.pre

noncomputable theory

open bool
open [class] classical
open [notation] function
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit
open core

structure core.ops.Range (Idx : Type₁) := mk {} ::
(start : Idx)
(«end» : Idx)

structure core.ops.RangeFrom (Idx : Type₁) := mk {} ::
(start : Idx)

structure core.ops.RangeTo (Idx : Type₁) := mk {} ::
(«end» : Idx)

structure core.ops.RangeInclusive.Empty.struct (Idx : Type₁) := mk {} ::
(«at» : Idx)



structure core.ops.RangeInclusive.NonEmpty.struct (Idx : Type₁) := mk {} ::
(start : Idx)
(«end» : Idx)

inductive core.ops.RangeInclusive (Idx : Type₁) :=
| Empty {} : core.ops.RangeInclusive.Empty.struct Idx → core.ops.RangeInclusive Idx
| NonEmpty {} : core.ops.RangeInclusive.NonEmpty.struct Idx → core.ops.RangeInclusive Idx

structure core.ops.RangeToInclusive (Idx : Type₁) := mk {} ::
(«end» : Idx)

inductive core.num.FpCategory :=
| Nan {} : core.num.FpCategory
| Infinite {} : core.num.FpCategory
| Zero {} : core.num.FpCategory
| Subnormal {} : core.num.FpCategory
| Normal {} : core.num.FpCategory

definition core.num.FpCategory.discr (self : core.num.FpCategory) : isize := match self with
| core.num.FpCategory.Nan := 0
| core.num.FpCategory.Infinite := 1
| core.num.FpCategory.Zero := 2
| core.num.FpCategory.Subnormal := 3
| core.num.FpCategory.Normal := 4
end

structure core.num.Float [class] (Self : Type₁) :=
(nan : (sem (Self)))
(infinity : (sem (Self)))
(neg_infinity : (sem (Self)))
(neg_zero : (sem (Self)))
(zero : (sem (Self)))
(one : (sem (Self)))
(is_nan : (Self → sem (bool)))
(is_infinite : (Self → sem (bool)))
(is_finite : (Self → sem (bool)))
(is_normal : (Self → sem (bool)))
(classify : (Self → sem ((core.num.FpCategory))))
(integer_decode : (Self → sem ((u64 × i16 × i8))))
(abs : (Self → sem (Self)))
(signum : (Self → sem (Self)))
(is_sign_positive : (Self → sem (bool)))
(is_sign_negative : (Self → sem (bool)))
(recip : (Self → sem (Self)))
(powi : (Self → i32 → sem (Self)))
(to_degrees : (Self → sem (Self)))
(to_radians : (Self → sem (Self)))

structure core.clone.Clone [class] (Self : Type₁) :=
(clone : (Self → sem (Self)))

structure core.marker.Copy [class] (Self : Type₁) extends core.clone.Clone Self := mk

attribute [coercion] core.marker.Copy.to_Clone

structure core.marker.PhantomData (T : Type₁) := mk {} ::

structure core.ops.BitAnd [class] (Self : Type₁) (RHS : Type₁) («<Self as ops.BitAnd<RHS>>.Output» : Type₁) :=
(bitand : (Self → RHS → sem («<Self as ops.BitAnd<RHS>>.Output»)))

definition core.«u32 as core.ops.BitAnd».bitand (selfₐ : u32) (rhsₐ : u32) : sem (u32) :=
let' «self$3» ← selfₐ;
let' «rhs$4» ← rhsₐ;
let' t5 ← «self$3»;
let' t6 ← «rhs$4»;
let' ret ← bitand u32.bits t5 t6;
return (ret)


definition core.«&'a u32 as core.ops.BitAnd<u32>».bitand (selfₐ : u32) (otherₐ : u32) : sem (u32) :=
let' «self$3» ← selfₐ;
let' «other$4» ← otherₐ;
let' t5 ← «self$3»;
let' t6 ← «other$4»;
dostep «$tmp» ← @core.«u32 as core.ops.BitAnd».bitand t5 t6;
let' ret ← «$tmp»;
return (ret)


definition core.«&'a u32 as core.ops.BitAnd<u32>» [instance] := ⦃
  core.ops.BitAnd u32 u32 u32,
  bitand := @core.«&'a u32 as core.ops.BitAnd<u32>».bitand
⦄

structure core.ops.RangeFull := mk {} ::

structure core.cmp.PartialEq [class] (Self : Type₁) (Rhs : Type₁) :=
(eq : (Self → Rhs → sem (bool)))

structure core.cmp.Eq [class] (Self : Type₁) extends core.cmp.PartialEq Self Self := mk

attribute [coercion] core.cmp.Eq.to_PartialEq

structure core.cmp.AssertParamIsEq (T : Type₁) := mk {} ::
(«$_field» : (core.marker.PhantomData T))

inductive core.cmp.Ordering :=
| Less {} : core.cmp.Ordering
| Equal {} : core.cmp.Ordering
| Greater {} : core.cmp.Ordering

definition core.cmp.Ordering.discr (self : core.cmp.Ordering) : isize := match self with
| core.cmp.Ordering.Less := -1
| core.cmp.Ordering.Equal := 0
| core.cmp.Ordering.Greater := 1
end

structure core.cmp.PartialOrd [class] (Self : Type₁) (Rhs : Type₁) extends core.cmp.PartialEq Self Rhs :=
(partial_cmp : (Self → Rhs → sem ((core.option.Option (core.cmp.Ordering)))))

attribute [coercion] core.cmp.PartialOrd.to_PartialEq

structure core.cmp.Ord [class] (Self : Type₁) extends core.cmp.Eq Self, core.cmp.PartialOrd Self Self :=
(cmp : (Self → Self → sem ((core.cmp.Ordering))))

attribute [coercion] core.cmp.Ord.to_Eq core.cmp.Ord.to_PartialOrd

definition core.cmp.PartialOrd.lt {Self : Type₁} {Rhs : Type₁} [«core.cmp.PartialOrd Self Rhs» : core.cmp.PartialOrd Self Rhs] (selfₐ : Self) (otherₐ : Rhs) : sem (bool) :=
let' «self$3» ← selfₐ;
let' «other$4» ← otherₐ;
let' t6 ← «self$3»;
let' t7 ← «other$4»;
dostep «$tmp» ← @core.cmp.PartialOrd.partial_cmp Self Rhs «core.cmp.PartialOrd Self Rhs» t6 t7;
let' t5 ← «$tmp»;
match t5 with
| core.option.Option.None :=
let' ret ← ff;
return (ret)
 | core.option.Option.Some «» :=
do «$tmp0» ← match t5 with
| core.option.Option.None := mzero
 | core.option.Option.Some «$0» := return «$0»
end
;
match «$tmp0» with
| core.cmp.Ordering.Less :=
let' ret ← tt;
return (ret)
 | core.cmp.Ordering.Equal :=
let' ret ← ff;
return (ret)
 | core.cmp.Ordering.Greater :=
let' ret ← ff;
return (ret)
end
end


definition core.cmp.PartialOrd.le {Self : Type₁} {Rhs : Type₁} [«core.cmp.PartialOrd Self Rhs» : core.cmp.PartialOrd Self Rhs] (selfₐ : Self) (otherₐ : Rhs) : sem (bool) :=
let' «self$3» ← selfₐ;
let' «other$4» ← otherₐ;
let' t6 ← «self$3»;
let' t7 ← «other$4»;
dostep «$tmp» ← @core.cmp.PartialOrd.partial_cmp Self Rhs «core.cmp.PartialOrd Self Rhs» t6 t7;
let' t5 ← «$tmp»;
match t5 with
| core.option.Option.None :=
let' ret ← ff;
return (ret)
 | core.option.Option.Some «» :=
do «$tmp0» ← match t5 with
| core.option.Option.None := mzero
 | core.option.Option.Some «$0» := return «$0»
end
;
match «$tmp0» with
| core.cmp.Ordering.Less :=
let' ret ← tt;
return (ret)
 | core.cmp.Ordering.Equal :=
let' ret ← tt;
return (ret)
 | core.cmp.Ordering.Greater :=
let' ret ← ff;
return (ret)
end
end


definition core.cmp.min {T : Type₁} [«core.cmp.Ord T» : core.cmp.Ord T] (v1ₐ : T) (v2ₐ : T) : sem (T) :=
let' «v1$3» ← v1ₐ;
let' «v2$4» ← v2ₐ;
let' t6 ← «v1$3»;
let' t8 ← «v2$4»;
dostep «$tmp» ← @core.cmp.PartialOrd.le T T «core.cmp.Ord T» t6 t8;
let' t5 ← «$tmp»;
if t5 = bool.tt then
let' t9 ← «v1$3»;
let' ret ← t9;
return (ret)
else
let' t10 ← «v2$4»;
let' ret ← t10;
return (ret)


definition core.cmp.PartialOrd.ge {Self : Type₁} {Rhs : Type₁} [«core.cmp.PartialOrd Self Rhs» : core.cmp.PartialOrd Self Rhs] (selfₐ : Self) (otherₐ : Rhs) : sem (bool) :=
let' «self$3» ← selfₐ;
let' «other$4» ← otherₐ;
let' t6 ← «self$3»;
let' t7 ← «other$4»;
dostep «$tmp» ← @core.cmp.PartialOrd.partial_cmp Self Rhs «core.cmp.PartialOrd Self Rhs» t6 t7;
let' t5 ← «$tmp»;
match t5 with
| core.option.Option.None :=
let' ret ← ff;
return (ret)
 | core.option.Option.Some «» :=
do «$tmp0» ← match t5 with
| core.option.Option.None := mzero
 | core.option.Option.Some «$0» := return «$0»
end
;
match «$tmp0» with
| core.cmp.Ordering.Less :=
let' ret ← ff;
return (ret)
 | core.cmp.Ordering.Equal :=
let' ret ← tt;
return (ret)
 | core.cmp.Ordering.Greater :=
let' ret ← tt;
return (ret)
end
end


definition core.cmp.max {T : Type₁} [«core.cmp.Ord T» : core.cmp.Ord T] (v1ₐ : T) (v2ₐ : T) : sem (T) :=
let' «v1$3» ← v1ₐ;
let' «v2$4» ← v2ₐ;
let' t6 ← «v2$4»;
let' t8 ← «v1$3»;
dostep «$tmp» ← @core.cmp.PartialOrd.ge T T «core.cmp.Ord T» t6 t8;
let' t5 ← «$tmp»;
if t5 = bool.tt then
let' t9 ← «v2$4»;
let' ret ← t9;
return (ret)
else
let' t10 ← «v1$3»;
let' ret ← t10;
return (ret)


definition core.«u32 as core.clone.Clone».clone (selfₐ : u32) : sem (u32) :=
let' «self$2» ← selfₐ;
let' t3 ← «self$2»;
let' ret ← t3;
return (ret)


definition core.«u32 as core.clone.Clone» [instance] := ⦃
  core.clone.Clone u32,
  clone := @core.«u32 as core.clone.Clone».clone
⦄

structure core.default.Default [class] (Self : Type₁) :=
(default : (sem (Self)))

definition core.«i32 as core.default.Default».default : sem (i32) :=
let' ret ← (0 : int);
return (ret)


definition core.«i32 as core.default.Default» [instance] := ⦃
  core.default.Default i32,
  default := @core.«i32 as core.default.Default».default
⦄

inductive core.char.CharTryFromError :=
mk {} : unit → core.char.CharTryFromError

definition core.char.from_digit.«$_MSG_FILE_LINE» : sem (string × string × u32) :=
let' ret ← ("from_digit: radix is too high (maximum 36)", "/home/hayden/.rustup/toolchains/nightly-2016-11-22-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/src/libcore/char.rs", (294 : nat));
return (ret)


definition core.char.from_digit (numₐ : u32) (radixₐ : u32) : sem ((core.option.Option char32)) :=
let' «num$3» ← numₐ;
let' «radix$4» ← radixₐ;
let' t7 ← «radix$4»;
let' t6 ← t7 >ᵇ (36 : nat);
if t6 = bool.tt then
let' t11 ← core.char.from_digit.«$_MSG_FILE_LINE»;
let' t10 ← t11;
mzero
else
let' t5 ← ⋆;
let' t13 ← «num$3»;
let' t14 ← «radix$4»;
let' t12 ← t13 <ᵇ t14;
if t12 = bool.tt then
let' t16 ← «num$3»;
do «$tmp0» ← (unsigned_to_unsigned u8.bits t16);
let' «num$15» ← «$tmp0»;
let' t18 ← «num$15»;
let' t17 ← t18 <ᵇ (10 : nat);
if t17 = bool.tt then
let' t21 ← «num$15»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add u8.bits (48 : nat) t21);
let' t22 ← «$tmp0»;
let' t20 ← t22.1;
do «$tmp0» ← (unsigned_to_char char32.bits t20);
let' t19 ← «$tmp0»;
let' ret ← core.option.Option.Some t19;
return (ret)
else
let' t26 ← «num$15»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add u8.bits (97 : nat) t26);
let' t27 ← «$tmp0»;
let' t25 ← t27.1;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sub u8.bits t25 (10 : nat));
let' t28 ← «$tmp0»;
let' t24 ← t28.1;
do «$tmp0» ← (unsigned_to_char char32.bits t24);
let' t23 ← «$tmp0»;
let' ret ← core.option.Option.Some t23;
return (ret)
else
let' ret ← core.option.Option.None;
return (ret)


inductive core.char.EscapeUnicodeState :=
| Done {} : core.char.EscapeUnicodeState
| RightBrace {} : core.char.EscapeUnicodeState
| Value {} : core.char.EscapeUnicodeState
| LeftBrace {} : core.char.EscapeUnicodeState
| «Type» {} : core.char.EscapeUnicodeState
| Backslash {} : core.char.EscapeUnicodeState

definition core.char.EscapeUnicodeState.discr (self : core.char.EscapeUnicodeState) : isize := match self with
| core.char.EscapeUnicodeState.Done := 0
| core.char.EscapeUnicodeState.RightBrace := 1
| core.char.EscapeUnicodeState.Value := 2
| core.char.EscapeUnicodeState.LeftBrace := 3
| core.char.EscapeUnicodeState.«Type» := 4
| core.char.EscapeUnicodeState.Backslash := 5
end

structure core.char.EscapeUnicode := mk {} ::
(c : char32)
(state : (core.char.EscapeUnicodeState))
(hex_digit_idx : usize)

inductive core.char.EscapeDefaultState :=
| Done {} : core.char.EscapeDefaultState
| Char {} : char32 → core.char.EscapeDefaultState
| Backslash {} : char32 → core.char.EscapeDefaultState
| Unicode {} : (core.char.EscapeUnicode) → core.char.EscapeDefaultState

structure core.char.EscapeDefault := mk {} ::
(state : (core.char.EscapeDefaultState))

inductive core.char.EscapeDebug :=
mk {} : (core.char.EscapeDefault) → core.char.EscapeDebug

inductive core.char.InvalidSequence :=
mk {} : unit → core.char.InvalidSequence

structure core.iter.iterator.Iterator [class] (Self : Type₁) («<Self as iter.iterator.Iterator>.Item» : Type₁) :=
(next : (Self → sem ((core.option.Option «<Self as iter.iterator.Iterator>.Item») × Self)))

structure core.slice.SliceExt [class] (Self : Type₁) («<Self as slice.SliceExt>.Item» : Type₁) :=
(len : (Self → sem (usize)))

definition core.slice.SliceExt.is_empty {Self : Type₁} («<Self as slice.SliceExt>.Item» : Type₁) [«core.slice.SliceExt Self» : core.slice.SliceExt Self «<Self as slice.SliceExt>.Item»] (selfₐ : Self) : sem (bool) :=
let' «self$2» ← selfₐ;
let' t4 ← «self$2»;
dostep «$tmp» ← @core.slice.SliceExt.len Self «<Self as slice.SliceExt>.Item» «core.slice.SliceExt Self» t4;
let' t3 ← «$tmp»;
let' ret ← t3 =ᵇ (0 : nat);
return (ret)


definition core.«[T] as core.slice.SliceExt».get {T : Type₁} (selfₐ : (slice T)) (indexₐ : usize) : sem ((core.option.Option T)) :=
let' «self$3» ← selfₐ;
let' «index$4» ← indexₐ;
let' t6 ← «index$4»;
let' t8 ← «self$3»;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».len T t8;
let' t7 ← «$tmp»;
let' t5 ← t6 <ᵇ t7;
if t5 = bool.tt then
let' t11 ← «index$4»;
let' t12 ← list.length «self$3»;
let' t13 ← t11 <ᵇ t12;
do «$tmp0» ← core.«[T] as core.slice.SliceExt».get_unchecked «self$3» t11;
let' t10 ← «$tmp0»;
let' t9 ← t10;
let' ret ← core.option.Option.Some t9;
return (ret)
else
let' ret ← core.option.Option.None;
return (ret)


definition core.«[T] as core.slice.SliceExt» [instance] {T : Type₁} := ⦃
  core.slice.SliceExt (slice T) T,
  len := @core.«[T] as core.slice.SliceExt».len T
⦄

section
parameters {T : Type₁} [«core.cmp.Ord T» : core.cmp.Ord T]

structure core.«[T] as core.slice.SliceExt».binary_search.closure_5642 (U0 : Type₁) := (val : U0)

include T «core.cmp.Ord T»


definition core.«[T] as core.slice.SliceExt».binary_search.closure_5642.fn («$a1» : (core.«[T] as core.slice.SliceExt».binary_search.closure_5642 T)) (pₐ : T) : sem ((core.cmp.Ordering) × (core.«[T] as core.slice.SliceExt».binary_search.closure_5642 T)) :=
let' «p$3» ← pₐ;
let' t4 ← «p$3»;
let' t5 ← (core.«[T] as core.slice.SliceExt».binary_search.closure_5642.val «$a1»);
dostep «$tmp» ← @core.cmp.Ord.cmp T «core.cmp.Ord T» t4 t5;
let' ret ← «$tmp»;
return (ret, «$a1»)



definition core.«[T] as core.slice.SliceExt».binary_search.closure_5642.inst [instance] : core.ops.FnMut (core.«[T] as core.slice.SliceExt».binary_search.closure_5642 T) T (core.cmp.Ordering) :=
core.ops.FnMut.mk_simple (λ self args, let' pₐ ← args;
  core.«[T] as core.slice.SliceExt».binary_search.closure_5642.fn self pₐ
)

end

inductive core.result.Result (T : Type₁) (E : Type₁) :=
| Ok {} : T → core.result.Result T E
| Err {} : E → core.result.Result T E

section
open core.ops

/-
/// Implements slicing with syntax `&self[begin .. end]`.
///
/// Returns a slice of self for the index range [`begin`..`end`).
///
/// This operation is `O(1)`.
///
/// # Panics
///
/// Requires that `begin <= end` and `end <= self.len()`,
/// otherwise slicing will panic.
-/
definition core.«[T] as core.ops.Index<core.ops.Range<usize>>».index {T : Type₁} (self : slice T) (index : Range usize) : sem (slice T) :=
sem.guard (Range.start index ≤ Range.«end» index ∧ Range.«end» index ≤ list.length self)
$ return (list.firstn (Range.«end» index - Range.start index) (list.dropn (Range.start index) self))

end

definition core.«[T] as core.ops.Index<core.ops.RangeTo<usize>>».index {T : Type₁} (selfₐ : (slice T)) (indexₐ : (core.ops.RangeTo usize)) : sem ((slice T)) :=
let' «self$3» ← selfₐ;
let' «index$4» ← indexₐ;
let' t6 ← «self$3»;
let' t8 ← (0 : nat);
let' t10 ← (core.ops.RangeTo.«end» «index$4»);
let' t9 ← t10;
let' t7 ← core.ops.Range.mk t8 t9;
dostep «$tmp» ← @core.«[T] as core.ops.Index<core.ops.Range<usize>>».index T t6 t7;
let' t5 ← «$tmp»;
let' ret ← t5;
return (ret)


definition core.«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index {T : Type₁} (selfₐ : (slice T)) (indexₐ : (core.ops.RangeFrom usize)) : sem ((slice T)) :=
let' «self$3» ← selfₐ;
let' «index$4» ← indexₐ;
let' t6 ← «self$3»;
let' t9 ← (core.ops.RangeFrom.start «index$4»);
let' t8 ← t9;
let' t11 ← «self$3»;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».len T t11;
let' t10 ← «$tmp»;
let' t7 ← core.ops.Range.mk t8 t10;
dostep «$tmp» ← @core.«[T] as core.ops.Index<core.ops.Range<usize>>».index T t6 t7;
let' t5 ← «$tmp»;
let' ret ← t5;
return (ret)


definition core.«[T] as core.slice.SliceExt».split_at {T : Type₁} (selfₐ : (slice T)) (midₐ : usize) : sem (((slice T) × (slice T))) :=
let' «self$3» ← selfₐ;
let' «mid$4» ← midₐ;
let' t8 ← «self$3»;
let' t11 ← «mid$4»;
let' t10 ← t11;
let' t9 ← core.ops.RangeTo.mk t10;
dostep «$tmp» ← @core.«[T] as core.ops.Index<core.ops.RangeTo<usize>>».index T t8 t9;
let' t7 ← «$tmp»;
let' t6 ← t7;
let' t5 ← t6;
let' t15 ← «self$3»;
let' t18 ← «mid$4»;
let' t17 ← t18;
let' t16 ← core.ops.RangeFrom.mk t17;
dostep «$tmp» ← @core.«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index T t15 t16;
let' t14 ← «$tmp»;
let' t13 ← t14;
let' t12 ← t13;
let' ret ← (t5, t12);
return (ret)


section
parameters {T : Type₁} {F : Type₁} [«core.ops.FnMut F T» : core.ops.FnMut F T (core.cmp.Ordering)]
include T F «core.ops.FnMut F T»
definition core.«[T] as core.slice.SliceExt».binary_search_by.loop_4 (state__ : (F × usize × (slice T))) : sem (sum ((F × usize × (slice T))) ((core.result.Result usize usize))) :=
match state__ with («f$4», «base$5», «s$7») :=
let' t13 ← «s$7»;
let' t16 ← «s$7»;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».len T t16;
let' t15 ← «$tmp»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.shrs usize.bits t15 (1 : int));
let' t17 ← «$tmp0»;
let' t14 ← t17.1;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».split_at T t13 t14;
let' t12 ← «$tmp»;
let' «head$10» ← t12.1;
let' «tail$11» ← t12.2;
let' t20 ← «tail$11»;
dostep «$tmp» ← @core.slice.SliceExt.is_empty (slice T) T (@core.«[T] as core.slice.SliceExt» T) t20;
let' t19 ← «$tmp»;
if t19 = bool.tt then
do tmp__ ← let' t22 ← «base$5»;
let' ret ← core.result.Result.Err t22;
return (ret)
;
return (sum.inr tmp__)else
let' t18 ← ⋆;
let' t24 ← @lens.id F;
do «$tmp» ← lens.get t24 «f$4»;
let' t28 ← list.length «tail$11»;
let' t29 ← (0 : nat) <ᵇ t28;
do «$tmp0» ← core.«[T] as core.slice.SliceExt».get_unchecked «tail$11» (0 : nat);
let' t27 ← «$tmp0»;
let' t26 ← t27;
let' t25 ← t26;
do «$tmp0» ← lens.get t24 «f$4»;
dostep «$tmp» ← @core.ops.FnMut.call_mut F T (core.cmp.Ordering) «core.ops.FnMut F T» «$tmp0» t25;
match «$tmp» with (t23, «t24$») :=
do «f$4» ← lens.set t24 «f$4» «t24$»;
match t23 with
| core.cmp.Ordering.Less :=
let' t32 ← «head$10»;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».len T t32;
let' t31 ← «$tmp»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits t31 (1 : nat));
let' t33 ← «$tmp0»;
let' t30 ← t33.1;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits «base$5» t30);
let' t34 ← «$tmp0»;
let' «base$5» ← t34.1;
let' t37 ← «tail$11»;
let' t39 ← (1 : nat);
let' t38 ← core.ops.RangeFrom.mk t39;
dostep «$tmp» ← @core.«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index T t37 t38;
let' t36 ← «$tmp»;
let' t35 ← t36;
let' «s$7» ← t35;
let' t6 ← ⋆;
return (sum.inl («f$4», «base$5», «s$7»))
 | core.cmp.Ordering.Equal :=
do tmp__ ← let' t42 ← «base$5»;
let' t44 ← «head$10»;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».len T t44;
let' t43 ← «$tmp»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits t42 t43);
let' t45 ← «$tmp0»;
let' t41 ← t45.1;
let' ret ← core.result.Result.Ok t41;
return (ret)
;
return (sum.inr tmp__) | core.cmp.Ordering.Greater :=
let' «s$7» ← «head$10»;
return (sum.inl («f$4», «base$5», «s$7»))
end
end
end


definition core.«[T] as core.slice.SliceExt».binary_search_by (selfₐ : (slice T)) (fₐ : F) : sem ((core.result.Result usize usize)) :=
let' «self$3» ← selfₐ;
let' «f$4» ← fₐ;
let' «base$5» ← (0 : nat);
let' t8 ← «self$3»;
let' «s$7» ← t8;
loop (core.«[T] as core.slice.SliceExt».binary_search_by.loop_4) («f$4», «base$5», «s$7»)

end

definition core.«[T] as core.slice.SliceExt».binary_search {T : Type₁} [«core.cmp.Ord T» : core.cmp.Ord T] (selfₐ : (slice T)) (xₐ : T) : sem ((core.result.Result usize usize)) :=
let' «self$3» ← selfₐ;
let' «x$4» ← xₐ;
let' t5 ← «self$3»;
let' t7 ← «x$4»;
let' t6 ← core.«[T] as core.slice.SliceExt».binary_search.closure_5642.mk t7;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».binary_search_by T (core.«[T] as core.slice.SliceExt».binary_search.closure_5642 T) (@core.«[T] as core.slice.SliceExt».binary_search.closure_5642.inst T «core.cmp.Ord T») t5 t6;
let' ret ← «$tmp»;
return (ret)


structure core.hash.sip.State := mk {} ::
(v0 : u64)
(v2 : u64)
(v1 : u64)
(v3 : u64)

structure core.hash.sip.Sip [class] (Self : Type₁) :=
(c_rounds : ((core.hash.sip.State) → sem (unit × (core.hash.sip.State))))
(d_rounds : ((core.hash.sip.State) → sem (unit × (core.hash.sip.State))))

structure core.hash.sip.Hasher (S : Type₁) := mk {} ::
(k0 : u64)
(k1 : u64)
(length : usize)
(state : (core.hash.sip.State))
(tail : u64)
(ntail : usize)
(«$_marker» : (core.marker.PhantomData S))

definition core.hash.sip.«Hasher<S>».reset {S : Type₁} [«core.hash.sip.Sip S» : core.hash.sip.Sip S] (selfₐ : (core.hash.sip.Hasher S)) : sem (unit × (core.hash.sip.Hasher S)) :=
let' «self$2» ← @lens.id (core.hash.sip.Hasher S);
do «$tmp1» ← lens.get «self$2» selfₐ;
do selfₐ ← lens.set «self$2» selfₐ (let' («$tmp» : (core.hash.sip.Hasher S)) ← «$tmp1»; ⦃ (core.hash.sip.Hasher S), length := (0 : nat), «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «self$2» selfₐ;
return ((core.hash.sip.Hasher.k0 «$tmp0»));
let' t3 ← «$tmp0»;
do «$tmp1» ← do «$tmp0» ← lens.get «self$2» selfₐ;
return ((core.hash.sip.Hasher.state «$tmp0»));
do «$tmp2» ← lens.get «self$2» selfₐ;
do selfₐ ← lens.set «self$2» selfₐ (let' («$tmp» : (core.hash.sip.Hasher S)) ← «$tmp2»; ⦃ (core.hash.sip.Hasher S), state := (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := bitxor u64.bits t3 (8317987319222330741 : nat), «$tmp» ⦄), «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «self$2» selfₐ;
return ((core.hash.sip.Hasher.k1 «$tmp0»));
let' t4 ← «$tmp0»;
do «$tmp1» ← do «$tmp0» ← lens.get «self$2» selfₐ;
return ((core.hash.sip.Hasher.state «$tmp0»));
do «$tmp2» ← lens.get «self$2» selfₐ;
do selfₐ ← lens.set «self$2» selfₐ (let' («$tmp» : (core.hash.sip.Hasher S)) ← «$tmp2»; ⦃ (core.hash.sip.Hasher S), state := (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := bitxor u64.bits t4 (7237128888997146477 : nat), «$tmp» ⦄), «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «self$2» selfₐ;
return ((core.hash.sip.Hasher.k0 «$tmp0»));
let' t5 ← «$tmp0»;
do «$tmp1» ← do «$tmp0» ← lens.get «self$2» selfₐ;
return ((core.hash.sip.Hasher.state «$tmp0»));
do «$tmp2» ← lens.get «self$2» selfₐ;
do selfₐ ← lens.set «self$2» selfₐ (let' («$tmp» : (core.hash.sip.Hasher S)) ← «$tmp2»; ⦃ (core.hash.sip.Hasher S), state := (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := bitxor u64.bits t5 (7816392313619706465 : nat), «$tmp» ⦄), «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «self$2» selfₐ;
return ((core.hash.sip.Hasher.k1 «$tmp0»));
let' t6 ← «$tmp0»;
do «$tmp1» ← do «$tmp0» ← lens.get «self$2» selfₐ;
return ((core.hash.sip.Hasher.state «$tmp0»));
do «$tmp2» ← lens.get «self$2» selfₐ;
do selfₐ ← lens.set «self$2» selfₐ (let' («$tmp» : (core.hash.sip.Hasher S)) ← «$tmp2»; ⦃ (core.hash.sip.Hasher S), state := (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := bitxor u64.bits t6 (8387220255154660723 : nat), «$tmp» ⦄), «$tmp» ⦄);
do «$tmp1» ← lens.get «self$2» selfₐ;
do selfₐ ← lens.set «self$2» selfₐ (let' («$tmp» : (core.hash.sip.Hasher S)) ← «$tmp1»; ⦃ (core.hash.sip.Hasher S), ntail := (0 : nat), «$tmp» ⦄);
let' ret ← ⋆;
return (⋆, selfₐ)


structure core.hash.sip.Sip13Rounds := mk {} ::

structure core.hash.sip.SipHasher13 := mk {} ::
(hasher : (core.hash.sip.Hasher (core.hash.sip.Sip13Rounds)))

structure core.hash.sip.Sip24Rounds := mk {} ::

structure core.hash.sip.SipHasher24 := mk {} ::
(hasher : (core.hash.sip.Hasher (core.hash.sip.Sip24Rounds)))

inductive core.hash.sip.SipHasher :=
mk {} : (core.hash.sip.SipHasher24) → core.hash.sip.SipHasher

definition core.hash.sip.«Hasher<S>».new_with_keys {S : Type₁} [«core.hash.sip.Sip S» : core.hash.sip.Sip S] (key0ₐ : u64) (key1ₐ : u64) : sem ((core.hash.sip.Hasher S)) :=
let' «key0$3» ← key0ₐ;
let' «key1$4» ← key1ₐ;
let' t6 ← «key0$3»;
let' t7 ← «key1$4»;
let' t8 ← core.hash.sip.State.mk (0 : nat) (0 : nat) (0 : nat) (0 : nat);
let' t9 ← core.marker.PhantomData.mk;
let' «state$5» ← core.hash.sip.Hasher.mk t6 t7 (0 : nat) t8 (0 : nat) (0 : nat) t9;
let' t11 ← @lens.id (core.hash.sip.Hasher S);
do «$tmp» ← lens.get t11 «state$5»;
do «$tmp0» ← lens.get t11 «state$5»;
dostep «$tmp» ← @core.hash.sip.«Hasher<S>».reset S «core.hash.sip.Sip S» «$tmp0»;
match «$tmp» with (t10, «t11$») :=
do «state$5» ← lens.set t11 «state$5» «t11$»;
let' t12 ← «state$5»;
let' ret ← t12;
return (ret)
end


definition core.u64.wrapping_add (selfₐ : u64) (rhsₐ : u64) : sem (u64) :=
let' «self$3» ← selfₐ;
let' «rhs$4» ← rhsₐ;
let' t5 ← «self$3»;
let' t6 ← «rhs$4»;
dostep «$tmp» ← core.intrinsics.overflowing_add u64.bits t5 t6;
let' ret ← «$tmp»;
return (ret)


definition core.u64.rotate_left (selfₐ : u64) (nₐ : u32) : sem (u64) :=
let' «self$3» ← selfₐ;
let' «n$4» ← nₐ;
let' t6 ← «n$4»;
let' t7 ← (64 : nat) =ᵇ (0 : nat);
do «$tmp0» ← checked.rem u32.bits t6 (64 : nat);
let' «n$5» ← «$tmp0»;
let' t9 ← «self$3»;
let' t10 ← «n$5»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.shl u64.bits t9 t10);
let' t11 ← «$tmp0»;
let' t8 ← t11.1;
let' t13 ← «self$3»;
let' t16 ← «n$5»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sub u32.bits (64 : nat) t16);
let' t17 ← «$tmp0»;
let' t15 ← t17.1;
let' t18 ← (64 : nat) =ᵇ (0 : nat);
do «$tmp0» ← checked.rem u32.bits t15 (64 : nat);
let' t14 ← «$tmp0»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.shr u64.bits t13 t14);
let' t19 ← «$tmp0»;
let' t12 ← t19.1;
let' ret ← bitor u64.bits t8 t12;
return (ret)


definition core.«core.hash.sip.Sip24Rounds as core.hash.sip.Sip».c_rounds (stateₐ : (core.hash.sip.State)) : sem (unit × (core.hash.sip.State)) :=
let' «state$2» ← @lens.id (core.hash.sip.State);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t5 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t6 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t5 t6;
let' t4 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t4, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t8 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t8 (13 : nat);
let' t7 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t7, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t9 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t9);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t11 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t11 (32 : nat);
let' t10 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t10, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t13 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t14 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t13 t14;
let' t12 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t12, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t16 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t16 (16 : nat);
let' t15 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t15, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t17 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t17);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t19 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t20 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t19 t20;
let' t18 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t18, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t22 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t22 (21 : nat);
let' t21 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t21, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t23 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t23);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t25 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t26 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t25 t26;
let' t24 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t24, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t28 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t28 (17 : nat);
let' t27 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t27, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t29 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t29);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t31 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t31 (32 : nat);
let' t30 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t30, «$tmp» ⦄);
let' t3 ← ⋆;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t34 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t35 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t34 t35;
let' t33 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t33, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t37 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t37 (13 : nat);
let' t36 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t36, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t38 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t38);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t40 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t40 (32 : nat);
let' t39 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t39, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t42 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t43 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t42 t43;
let' t41 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t41, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t45 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t45 (16 : nat);
let' t44 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t44, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t46 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t46);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t48 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t49 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t48 t49;
let' t47 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t47, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t51 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t51 (21 : nat);
let' t50 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t50, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t52 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t52);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t54 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t55 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t54 t55;
let' t53 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t53, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t57 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t57 (17 : nat);
let' t56 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t56, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t58 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t58);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t60 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t60 (32 : nat);
let' t59 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t59, «$tmp» ⦄);
let' t32 ← ⋆;
let' ret ← ⋆;
return (⋆, stateₐ)


definition core.«core.hash.sip.Sip24Rounds as core.hash.sip.Sip».d_rounds (stateₐ : (core.hash.sip.State)) : sem (unit × (core.hash.sip.State)) :=
let' «state$2» ← @lens.id (core.hash.sip.State);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t5 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t6 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t5 t6;
let' t4 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t4, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t8 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t8 (13 : nat);
let' t7 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t7, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t9 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t9);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t11 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t11 (32 : nat);
let' t10 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t10, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t13 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t14 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t13 t14;
let' t12 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t12, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t16 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t16 (16 : nat);
let' t15 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t15, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t17 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t17);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t19 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t20 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t19 t20;
let' t18 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t18, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t22 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t22 (21 : nat);
let' t21 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t21, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t23 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t23);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t25 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t26 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t25 t26;
let' t24 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t24, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t28 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t28 (17 : nat);
let' t27 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t27, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t29 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t29);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t31 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t31 (32 : nat);
let' t30 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t30, «$tmp» ⦄);
let' t3 ← ⋆;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t34 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t35 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t34 t35;
let' t33 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t33, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t37 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t37 (13 : nat);
let' t36 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t36, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t38 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t38);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t40 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t40 (32 : nat);
let' t39 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t39, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t42 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t43 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t42 t43;
let' t41 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t41, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t45 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t45 (16 : nat);
let' t44 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t44, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t46 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t46);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t48 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t49 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t48 t49;
let' t47 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t47, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t51 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t51 (21 : nat);
let' t50 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t50, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t52 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t52);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t54 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t55 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t54 t55;
let' t53 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t53, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t57 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t57 (17 : nat);
let' t56 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t56, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t58 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t58);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t60 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t60 (32 : nat);
let' t59 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t59, «$tmp» ⦄);
let' t32 ← ⋆;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t63 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t64 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t63 t64;
let' t62 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t62, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t66 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t66 (13 : nat);
let' t65 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t65, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t67 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t67);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t69 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t69 (32 : nat);
let' t68 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t68, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t71 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t72 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t71 t72;
let' t70 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t70, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t74 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t74 (16 : nat);
let' t73 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t73, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t75 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t75);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t77 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t78 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t77 t78;
let' t76 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t76, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t80 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t80 (21 : nat);
let' t79 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t79, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t81 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t81);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t83 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t84 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t83 t84;
let' t82 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t82, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t86 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t86 (17 : nat);
let' t85 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t85, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t87 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t87);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t89 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t89 (32 : nat);
let' t88 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t88, «$tmp» ⦄);
let' t61 ← ⋆;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t92 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t93 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t92 t93;
let' t91 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t91, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t95 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t95 (13 : nat);
let' t94 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t94, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t96 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t96);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t98 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t98 (32 : nat);
let' t97 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t97, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t100 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t101 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t100 t101;
let' t99 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t99, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t103 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t103 (16 : nat);
let' t102 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t102, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t104 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t104);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t106 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t107 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t106 t107;
let' t105 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t105, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t109 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t109 (21 : nat);
let' t108 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t108, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t110 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t110);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t112 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t113 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t112 t113;
let' t111 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t111, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t115 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t115 (17 : nat);
let' t114 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t114, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t116 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t116);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t118 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t118 (32 : nat);
let' t117 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t117, «$tmp» ⦄);
let' t90 ← ⋆;
let' ret ← ⋆;
return (⋆, stateₐ)


definition core.«core.hash.sip.Sip24Rounds as core.hash.sip.Sip» [instance] := ⦃
  core.hash.sip.Sip (core.hash.sip.Sip24Rounds),
  c_rounds := @core.«core.hash.sip.Sip24Rounds as core.hash.sip.Sip».c_rounds,
  d_rounds := @core.«core.hash.sip.Sip24Rounds as core.hash.sip.Sip».d_rounds
⦄

definition core.hash.sip.SipHasher24.new_with_keys (key0ₐ : u64) (key1ₐ : u64) : sem ((core.hash.sip.SipHasher24)) :=
let' «key0$3» ← key0ₐ;
let' «key1$4» ← key1ₐ;
let' t6 ← «key0$3»;
let' t7 ← «key1$4»;
dostep «$tmp» ← @core.hash.sip.«Hasher<S>».new_with_keys (core.hash.sip.Sip24Rounds) (@core.«core.hash.sip.Sip24Rounds as core.hash.sip.Sip») t6 t7;
let' t5 ← «$tmp»;
let' ret ← core.hash.sip.SipHasher24.mk t5;
return (ret)


definition core.hash.sip.SipHasher24.new : sem ((core.hash.sip.SipHasher24)) :=
dostep «$tmp» ← @core.hash.sip.SipHasher24.new_with_keys (0 : nat) (0 : nat);
let' ret ← «$tmp»;
return (ret)


definition core.«core.hash.sip.Sip13Rounds as core.hash.sip.Sip».c_rounds (stateₐ : (core.hash.sip.State)) : sem (unit × (core.hash.sip.State)) :=
let' «state$2» ← @lens.id (core.hash.sip.State);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t5 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t6 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t5 t6;
let' t4 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t4, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t8 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t8 (13 : nat);
let' t7 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t7, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t9 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t9);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t11 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t11 (32 : nat);
let' t10 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t10, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t13 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t14 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t13 t14;
let' t12 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t12, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t16 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t16 (16 : nat);
let' t15 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t15, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t17 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t17);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t19 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t20 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t19 t20;
let' t18 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t18, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t22 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t22 (21 : nat);
let' t21 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t21, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t23 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t23);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t25 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t26 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t25 t26;
let' t24 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t24, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t28 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t28 (17 : nat);
let' t27 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t27, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t29 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t29);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t31 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t31 (32 : nat);
let' t30 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t30, «$tmp» ⦄);
let' t3 ← ⋆;
let' ret ← ⋆;
return (⋆, stateₐ)


definition core.«core.hash.sip.Sip13Rounds as core.hash.sip.Sip».d_rounds (stateₐ : (core.hash.sip.State)) : sem (unit × (core.hash.sip.State)) :=
let' «state$2» ← @lens.id (core.hash.sip.State);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t5 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t6 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t5 t6;
let' t4 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t4, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t8 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t8 (13 : nat);
let' t7 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t7, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t9 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t9);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t11 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t11 (32 : nat);
let' t10 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t10, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t13 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t14 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t13 t14;
let' t12 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t12, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t16 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t16 (16 : nat);
let' t15 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t15, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t17 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t17);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t19 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t20 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t19 t20;
let' t18 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t18, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t22 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t22 (21 : nat);
let' t21 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t21, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t23 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t23);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t25 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t26 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t25 t26;
let' t24 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t24, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t28 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t28 (17 : nat);
let' t27 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t27, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t29 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t29);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t31 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t31 (32 : nat);
let' t30 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t30, «$tmp» ⦄);
let' t3 ← ⋆;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t34 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t35 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t34 t35;
let' t33 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t33, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t37 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t37 (13 : nat);
let' t36 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t36, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t38 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t38);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t40 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t40 (32 : nat);
let' t39 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t39, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t42 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t43 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t42 t43;
let' t41 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t41, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t45 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t45 (16 : nat);
let' t44 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t44, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t46 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t46);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t48 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t49 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t48 t49;
let' t47 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t47, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t51 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t51 (21 : nat);
let' t50 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t50, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t52 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t52);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t54 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t55 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t54 t55;
let' t53 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t53, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t57 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t57 (17 : nat);
let' t56 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t56, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t58 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t58);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t60 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t60 (32 : nat);
let' t59 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t59, «$tmp» ⦄);
let' t32 ← ⋆;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t63 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t64 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t63 t64;
let' t62 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t62, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t66 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t66 (13 : nat);
let' t65 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t65, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t67 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t67);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t69 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t69 (32 : nat);
let' t68 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t68, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t71 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t72 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t71 t72;
let' t70 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t70, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t74 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t74 (16 : nat);
let' t73 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t73, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t75 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t75);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t77 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t78 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t77 t78;
let' t76 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v0 := t76, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
let' t80 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t80 (21 : nat);
let' t79 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := t79, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v0 «$tmp0»));
let' t81 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v3 «$tmp0»));
return (bitxor u64.bits «$tmp0» t81);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v3 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t83 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t84 ← «$tmp0»;
dostep «$tmp» ← @core.u64.wrapping_add t83 t84;
let' t82 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t82, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
let' t86 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t86 (17 : nat);
let' t85 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := t85, «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t87 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v1 «$tmp0»));
return (bitxor u64.bits «$tmp0» t87);
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v1 := «$tmp0», «$tmp» ⦄);
do «$tmp0» ← do «$tmp0» ← lens.get «state$2» stateₐ;
return ((core.hash.sip.State.v2 «$tmp0»));
let' t89 ← «$tmp0»;
dostep «$tmp» ← @core.u64.rotate_left t89 (32 : nat);
let' t88 ← «$tmp»;
do «$tmp1» ← lens.get «state$2» stateₐ;
do stateₐ ← lens.set «state$2» stateₐ (let' («$tmp» : (core.hash.sip.State)) ← «$tmp1»; ⦃ (core.hash.sip.State), v2 := t88, «$tmp» ⦄);
let' t61 ← ⋆;
let' ret ← ⋆;
return (⋆, stateₐ)


definition core.«core.hash.sip.Sip13Rounds as core.hash.sip.Sip» [instance] := ⦃
  core.hash.sip.Sip (core.hash.sip.Sip13Rounds),
  c_rounds := @core.«core.hash.sip.Sip13Rounds as core.hash.sip.Sip».c_rounds,
  d_rounds := @core.«core.hash.sip.Sip13Rounds as core.hash.sip.Sip».d_rounds
⦄

definition core.hash.sip.SipHasher13.new_with_keys (key0ₐ : u64) (key1ₐ : u64) : sem ((core.hash.sip.SipHasher13)) :=
let' «key0$3» ← key0ₐ;
let' «key1$4» ← key1ₐ;
let' t6 ← «key0$3»;
let' t7 ← «key1$4»;
dostep «$tmp» ← @core.hash.sip.«Hasher<S>».new_with_keys (core.hash.sip.Sip13Rounds) (@core.«core.hash.sip.Sip13Rounds as core.hash.sip.Sip») t6 t7;
let' t5 ← «$tmp»;
let' ret ← core.hash.sip.SipHasher13.mk t5;
return (ret)


definition core.hash.sip.SipHasher13.new : sem ((core.hash.sip.SipHasher13)) :=
dostep «$tmp» ← @core.hash.sip.SipHasher13.new_with_keys (0 : nat) (0 : nat);
let' ret ← «$tmp»;
return (ret)


definition core.hash.sip.SipHasher.new_with_keys (key0ₐ : u64) (key1ₐ : u64) : sem ((core.hash.sip.SipHasher)) :=
let' «key0$3» ← key0ₐ;
let' «key1$4» ← key1ₐ;
let' t6 ← «key0$3»;
let' t7 ← «key1$4»;
dostep «$tmp» ← @core.hash.sip.SipHasher24.new_with_keys t6 t7;
let' t5 ← «$tmp»;
let' ret ← core.hash.sip.SipHasher.mk t5;
return (ret)


definition core.hash.sip.SipHasher.new : sem ((core.hash.sip.SipHasher)) :=
dostep «$tmp» ← @core.hash.sip.SipHasher.new_with_keys (0 : nat) (0 : nat);
let' ret ← «$tmp»;
return (ret)


