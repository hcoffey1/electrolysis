#**************
# Hayden Coffey
# 
#**************

baseModules=move.olean \
			sem.olean \
			bitvec.olean \
			asymptotic.olean \
			loop_combinator.olean 

dirModules=core \
		   fixedbitset \
		   alloc \
		   rand \
		   examples \
		   collections

targets=$(baseModules)\
		$(dirModules)

all: $(targets)

.PHONY: clean $(dirModules)

#Lean2 breaks when running multiple instances
MAKEFLAGS=--jobs=1

#Typecheck base modules
move.olean: move.lean
sem.olean: sem.lean
bitvec.olean: bitvec.lean move.olean
asymptotic.olean: asymptotic.lean move.olean
loop_combinator.olean: loop_combinator.lean asymptotic.olean sem.olean
$(baseModules):
	/usr/bin/time --verbose $(LEAN2_BIN) -M 16384 -o $@ $<

#Typecheck subdirectories
core: bitvec.olean loop_combinator.olean
rand: core
examples: core
alloc: core 
collections: core
fixedbitset: core collections
$(dirModules):
	$(MAKE) -C $@ 

clean:
	-rm -f *.olean
	$(MAKE) -C core clean
	$(MAKE) -C fixedbitset clean
	$(MAKE) -C collections clean
	$(MAKE) -C alloc clean
	$(MAKE) -C rand clean
	$(MAKE) -C examples clean 
