#**************
# Hayden Coffey
# 
#**************

#targets=generated.olean thy.olean pre.olean
targets=generated.olean pre.olean

all: $(targets)

.PHONY: clean 

#Lean2 breaks when running multiple instances
MAKEFLAGS=--jobs=1

pre.olean: pre.lean
generated.olean: generated.lean pre.olean
#thy.olean: thy.lean generated.olean
$(targets):
	/usr/bin/time --verbose $(LEAN2_BIN) -o $@ $<

clean:
	rm -f *.olean
