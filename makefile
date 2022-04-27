#**************
# Hayden Coffey
# 
#**************

#generatedLean=./thys/alloc/generated.lean \
#			  ./thys/collections/generated.lean \
#			  ./thys/core/generated.lean \
#			  ./thys/fixedbitset/generated.lean

targets=thys trans

all: $(targets)

.PHONY: clean thys trans

trans: 
	cargo run core
	cargo run collections
	cargo run alloc
	cargo run fixedbitset
	cargo run rand 

thys: trans
	$(MAKE) -C thys

clean:
	$(MAKE) -C thys clean
