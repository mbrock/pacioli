AGDA ?= agda
AGDA_FILE := src/index.agda
HTML_DIR := html
CSS_FILE := assets/agda-dark.css
HTML_CSS := agda-dark.css

.PHONY: all html

all:
	$(AGDA) $(AGDA_FILE)

html:
	mkdir -p $(HTML_DIR)
	cp $(CSS_FILE) $(HTML_DIR)/$(HTML_CSS)
	$(AGDA) --html --html-dir=$(HTML_DIR) --css=$(HTML_CSS) --highlight-occurrences $(AGDA_FILE)
