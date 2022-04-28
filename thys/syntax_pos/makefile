#**************
# genDep.py created makefile 
# 
#**************

targets=generated.olean 

all: $(targets)

.PHONY: clean

#Lean2 breaks when running multiple instances
MAKEFLAGS=--jobs=1

generated.olean: generated.lean
$(targets):
	$(LEAN2_BIN) -o $@ $<

clean:
	rm - f * .olean