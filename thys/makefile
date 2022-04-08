#**************
# Hayden Coffey
# 
#**************

targets=move.olean \
		sem.olean \
		bitvec.olean \
		asymptotic.olean \
		loop_combinator.olean \
		core

all: $(targets)

.PHONY: clean core

#Lean2 breaks when running multiple instances
MAKEFLAGS=--jobs=1

move.olean: move.lean
	$(LEAN2_BIN) -o $@ $<

sem.olean: sem.lean
	$(LEAN2_BIN) -o $@ $<

bitvec.olean: move.olean 
bitvec.olean: bitvec.lean
	$(LEAN2_BIN) -o $@ $<

asymptotic.olean: move.olean 
asymptotic.olean: asymptotic.lean
	$(LEAN2_BIN) -o $@ $<

loop_combinator.olean: sem.olean asymptotic.olean
loop_combinator.olean: loop_combinator.lean
	$(LEAN2_BIN) -o $@ $<

core: $(targets) 
	$(MAKE) -C core

clean:
	rm *.olean
	$(MAKE) -C core clean
