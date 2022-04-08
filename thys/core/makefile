#**************
# Hayden Coffey
# 
#**************

targets=generated.olean

all: $(targets)

.PHONY: clean 

#Lean2 breaks when running multiple instances
MAKEFLAGS=--jobs=1

pre.olean: pre.lean
	$(LEAN2_BIN) -o $@ $<

generated.olean: pre.olean
generated.olean: generated.lean
	$(LEAN2_BIN) -o $@ $<

#%.ll: %.cc
#	$(CUSTOM_CC) -o $@ $< -std=c++14 $(cxxFlags) $(flags) -S -emit-llvm -fverbose-asm

#%.o: %.cc
#	$(CUSTOM_CC) -c -o $@ $< -std=c++14 $(cxxFlags) $(flags)
#

#tool.so: tool.o
#	$(CXX) -shared -fPIC -o $@ $< $(cxxFlags) $(ldFlags) $(flags)

#src_dir: export CFLAGS=-DCUSTOM_MACRO
#src_dir:
#	$(MAKE) -C src_dir

#clean:
#	$(MAKE) -C src_dir clean

clean:
	rm *.olean

