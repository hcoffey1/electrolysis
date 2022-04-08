#**************
# Hayden Coffey
# 
#**************

targets=thys

all: $(targets)

.PHONY: clean thys

thys:
	$(MAKE) -C thys

clean:
	$(MAKE) -C thys clean
