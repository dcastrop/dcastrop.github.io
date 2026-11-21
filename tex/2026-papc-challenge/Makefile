# Build and publish every deck, one after another (never in parallel).
DECKS = papc-challenge level-1 \
        level-2f level-3f level-4f level-5f \
        level-2t level-3t level-4t level-5t \
        level-6 level-7 level-8 level-9

all:
	for d in $(DECKS); do $(MAKE) -C $$d publish || exit 1; done

clean:
	for d in $(DECKS); do $(MAKE) -C $$d clean; done

.PHONY: all clean
