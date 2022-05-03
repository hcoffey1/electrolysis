import examples.pre
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
open examples

section
parameters {T : Type₁} [«core.cmp.Ord T» : core.cmp.Ord T]
include T «core.cmp.Ord T»
definition examples.search.binary_search.loop_2 «item$3» «arr$4» (state__ : (usize × usize)) : sem (sum ((usize × usize)) ((core.option.Option usize))) :=
match state__ with («left$5», «right$6») :=
let' t10 ← «left$5»;
let' t11 ← «right$6»;
let' t9 ← t10 <ᵇ t11;
if t9 = bool.tt then
let' t14 ← «left$5»;
let' t17 ← «right$6»;
let' t18 ← «left$5»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sub usize.bits t17 t18);
let' t19 ← «$tmp0»;
let' t16 ← t19.1;
let' t20 ← (2 : nat) =ᵇ (0 : nat);
do «$tmp0» ← checked.div usize.bits t16 (2 : nat);
let' t15 ← «$tmp0»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits t14 t15);
let' t21 ← «$tmp0»;
let' «mid$13» ← t21.1;
let' t23 ← «item$3»;
let' t26 ← «mid$13»;
let' t27 ← list.length «arr$4»;
let' t28 ← t26 <ᵇ t27;
do «$tmp0» ← core.«[T] as core.slice.SliceExt».get_unchecked «arr$4» t26;
let' t25 ← «$tmp0»;
let' t24 ← t25;
dostep «$tmp» ← @core.cmp.Ord.cmp T «core.cmp.Ord T» t23 t24;
let' t22 ← «$tmp»;
match t22 with
| core.cmp.Ordering.Less :=
let' t29 ← «mid$13»;
let' «right$6» ← t29;
return (sum.inl («left$5», «right$6»))
 | core.cmp.Ordering.Equal :=
do tmp__ ← let' t31 ← «mid$13»;
let' ret ← core.option.Option.Some t31;
return (ret)
;
return (sum.inr tmp__) | core.cmp.Ordering.Greater :=
let' t32 ← «mid$13»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits t32 (1 : nat));
let' t33 ← «$tmp0»;
let' «left$5» ← t33.1;
return (sum.inl («left$5», «right$6»))
end
else
do tmp__ ← let' t8 ← ⋆;
let' ret ← core.option.Option.None;
return (ret)
;
return (sum.inr tmp__)end


definition examples.search.binary_search (itemₐ : T) (arrₐ : (slice T)) : sem ((core.option.Option usize)) :=
let' «item$3» ← itemₐ;
let' «arr$4» ← arrₐ;
let' «left$5» ← (0 : nat);
let' t7 ← «arr$4»;
dostep «$tmp» ← @collections.«[T]».len T t7;
let' «right$6» ← «$tmp»;
loop (examples.search.binary_search.loop_2 «item$3» «arr$4») («left$5», «right$6»)

end

