import rand.pre
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
open rand

structure rand.distributions.range.Range (X : Type₁) := mk {} ::
(low : X)
(range : X)
(accept_zone : X)

structure rand.chacha.ChaChaRng := mk {} ::
(buffer : (array u32 16))
(state : (array u32 16))
(index : usize)

structure rand.reseeding.ReseedingRng (R : Type₁) (Rsdr : Type₁) := mk {} ::
(rng : R)
(generation_threshold : usize)
(bytes_generated : usize)
(reseeder : Rsdr)

structure rand.Rng [class] (Self : Type₁) :=
(next_u32 : (Self → sem (u32 × Self)))

structure rand.reseeding.Reseeder [class] (Self : Type₁) (R : Type₁) :=
(reseed : (Self → R → sem (unit × Self × R)))

definition rand.reseeding.«ReseedingRng<R, Rsdr>».new {R : Type₁} {Rsdr : Type₁} [«rand.Rng R» : rand.Rng R] [«rand.reseeding.Reseeder Rsdr R» : rand.reseeding.Reseeder Rsdr R] (rngₐ : R) (generation_thresholdₐ : usize) (reseederₐ : Rsdr) : sem ((rand.reseeding.ReseedingRng R Rsdr)) :=
let' «rng$4» ← rngₐ;
let' «generation_threshold$5» ← generation_thresholdₐ;
let' «reseeder$6» ← reseederₐ;
let' t7 ← «rng$4»;
let' t9 ← «generation_threshold$5»;
let' t10 ← «reseeder$6»;
let' ret ← rand.reseeding.ReseedingRng.mk t7 t9 (0 : nat) t10;
return (ret)


definition rand.reseeding.«ReseedingRng<R, Rsdr>».reseed_if_necessary {R : Type₁} {Rsdr : Type₁} [«rand.Rng R» : rand.Rng R] [«rand.reseeding.Reseeder Rsdr R» : rand.reseeding.Reseeder Rsdr R] (selfₐ : (rand.reseeding.ReseedingRng R Rsdr)) : sem (unit × (rand.reseeding.ReseedingRng R Rsdr)) :=
let' «self$2» ← @lens.id (rand.reseeding.ReseedingRng R Rsdr);
do «$tmp0» ← do «$tmp0» ← lens.get «self$2» selfₐ;
return ((rand.reseeding.ReseedingRng.bytes_generated «$tmp0»));
let' t4 ← «$tmp0»;
do «$tmp0» ← do «$tmp0» ← lens.get «self$2» selfₐ;
return ((rand.reseeding.ReseedingRng.generation_threshold «$tmp0»));
let' t5 ← «$tmp0»;
let' t3 ← t4 ≥ᵇ t5;
if t3 = bool.tt then
let' t7 ← (lens.mk (return ∘ rand.reseeding.ReseedingRng.reseeder) (λ (o : (rand.reseeding.ReseedingRng R Rsdr)) i, return (let' («$tmp» : (rand.reseeding.ReseedingRng R Rsdr)) ← o; ⦃ (rand.reseeding.ReseedingRng R Rsdr), reseeder := i, «$tmp» ⦄)) ∘ₗ «self$2»);
do «$tmp» ← lens.get t7 selfₐ;
let' t9 ← (lens.mk (return ∘ rand.reseeding.ReseedingRng.rng) (λ (o : (rand.reseeding.ReseedingRng R Rsdr)) i, return (let' («$tmp» : (rand.reseeding.ReseedingRng R Rsdr)) ← o; ⦃ (rand.reseeding.ReseedingRng R Rsdr), rng := i, «$tmp» ⦄)) ∘ₗ «self$2»);
do «$tmp» ← lens.get t9 selfₐ;
let' t8 ← (t9);
do «$tmp» ← lens.get t8 selfₐ;
do «$tmp0» ← lens.get t7 selfₐ;
do «$tmp1» ← lens.get t8 selfₐ;
dostep «$tmp» ← @rand.reseeding.Reseeder.reseed Rsdr R «rand.reseeding.Reseeder Rsdr R» «$tmp0» «$tmp1»;
match «$tmp» with (t6, «t7$», «t8$») :=
do selfₐ ← lens.set t8 selfₐ «t8$»;
do selfₐ ← lens.set t7 selfₐ «t7$»;
do «$tmp1» ← lens.get «self$2» selfₐ;
do selfₐ ← lens.set «self$2» selfₐ (let' («$tmp» : (rand.reseeding.ReseedingRng R Rsdr)) ← «$tmp1»; ⦃ (rand.reseeding.ReseedingRng R Rsdr), bytes_generated := (0 : nat), «$tmp» ⦄);
let' ret ← ⋆;
return (⋆, selfₐ)
end
else
let' ret ← ⋆;
return (⋆, selfₐ)


structure rand.reseeding.ReseedWithDefault := mk {} ::

