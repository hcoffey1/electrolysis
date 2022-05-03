#**************
# Hayden Coffey
# 
#**************

targets=generated.olean thy.olean

all: $(targets)

.PHONY: clean 

#Lean2 breaks when running multiple instances
MAKEFLAGS=--jobs=1

generated.olean: generated.lean
thy.olean: thy.lean generated.olean
$(targets):
	/usr/bin/time --verbose $(LEAN2_BIN) -o $@ $<

clean:
	rm -f *.olean
