#**************
# Hayden Coffey
# 
#**************

targets=thys

all: $(targets)

.PHONY: clean thys trans

thys: trans
	$(MAKE) -C thys

clean:
	$(MAKE) -C thys clean
