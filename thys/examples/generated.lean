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
definition examples.search.ternary_search.loop_6 «target$5» «list$6» (state__ : (usize × usize)) : sem (sum ((usize × usize)) ((core.option.Option usize))) :=
match state__ with («start$7», «end$8») :=
let' t17 ← «start$7»;
let' t18 ← «end$8»;
let' t16 ← t17 ≤ᵇ t18;
if t16 = bool.tt then
let' t20 ← «start$7»;
let' t23 ← «end$8»;
let' t24 ← «start$7»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sub usize.bits t23 t24);
let' t25 ← «$tmp0»;
let' t22 ← t25.1;
let' t26 ← (3 : nat) =ᵇ (0 : nat);
do «$tmp0» ← checked.div usize.bits t22 (3 : nat);
let' t21 ← «$tmp0»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits t20 t21);
let' t27 ← «$tmp0»;
let' «mid1$19» ← t27.1;
let' t29 ← «end$8»;
let' t32 ← «end$8»;
let' t33 ← «start$7»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sub usize.bits t32 t33);
let' t34 ← «$tmp0»;
let' t31 ← t34.1;
let' t35 ← (3 : nat) =ᵇ (0 : nat);
do «$tmp0» ← checked.div usize.bits t31 (3 : nat);
let' t30 ← «$tmp0»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sub usize.bits t29 t30);
let' t36 ← «$tmp0»;
let' «mid2$28» ← t36.1;
let' t38 ← «target$5»;
let' t41 ← «mid1$19»;
let' t42 ← list.length «list$6»;
let' t43 ← t41 <ᵇ t42;
do «$tmp0» ← core.«[T] as core.slice.SliceExt».get_unchecked «list$6» t41;
let' t40 ← «$tmp0»;
let' t39 ← t40;
dostep «$tmp» ← @core.cmp.Ord.cmp T «core.cmp.Ord T» t38 t39;
let' t37 ← «$tmp»;
match t37 with
| core.cmp.Ordering.Less :=
let' t44 ← «mid1$19»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sub usize.bits t44 (1 : nat));
let' t45 ← «$tmp0»;
let' «end$8» ← t45.1;
return (sum.inl («start$7», «end$8»))
 | core.cmp.Ordering.Equal :=
do tmp__ ← let' t47 ← «mid1$19»;
let' ret ← core.option.Option.Some t47;
return (ret)
;
return (sum.inr tmp__) | core.cmp.Ordering.Greater :=
let' t49 ← «target$5»;
let' t52 ← «mid2$28»;
let' t53 ← list.length «list$6»;
let' t54 ← t52 <ᵇ t53;
do «$tmp0» ← core.«[T] as core.slice.SliceExt».get_unchecked «list$6» t52;
let' t51 ← «$tmp0»;
let' t50 ← t51;
dostep «$tmp» ← @core.cmp.Ord.cmp T «core.cmp.Ord T» t49 t50;
let' t48 ← «$tmp»;
match t48 with
| core.cmp.Ordering.Less :=
let' t59 ← «mid1$19»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits t59 (1 : nat));
let' t60 ← «$tmp0»;
let' «start$7» ← t60.1;
let' t61 ← «mid2$28»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sub usize.bits t61 (1 : nat));
let' t62 ← «$tmp0»;
let' «end$8» ← t62.1;
let' t14 ← ⋆;
return (sum.inl («start$7», «end$8»))
 | core.cmp.Ordering.Equal :=
do tmp__ ← let' t58 ← «mid2$28»;
let' ret ← core.option.Option.Some t58;
return (ret)
;
return (sum.inr tmp__) | core.cmp.Ordering.Greater :=
let' t55 ← «mid2$28»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits t55 (1 : nat));
let' t56 ← «$tmp0»;
let' «start$7» ← t56.1;
return (sum.inl («start$7», «end$8»))
end
end
else
do tmp__ ← let' t15 ← ⋆;
let' ret ← core.option.Option.None;
return (ret)
;
return (sum.inr tmp__)end


definition examples.search.ternary_search (targetₐ : T) (listₐ : (slice T)) (startₐ : usize) (endₐ : usize) : sem ((core.option.Option usize)) :=
let' «target$5» ← targetₐ;
let' «list$6» ← listₐ;
let' «start$7» ← startₐ;
let' «end$8» ← endₐ;
let' t11 ← «list$6»;
dostep «$tmp» ← @collections.«[T]».is_empty T t11;
let' t10 ← «$tmp»;
if t10 = bool.tt then
let' ret ← core.option.Option.None;
return (ret)
else
let' t9 ← ⋆;
loop (examples.search.ternary_search.loop_6 «target$5» «list$6») («start$7», «end$8»)

end

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

