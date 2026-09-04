DECK := gromov_filling_mother_deck
CHECK_DIR := .build/$(shell hostname -s)
CHECK_PDF := $(CHECK_DIR)/$(DECK).pdf
export SOURCE_DATE_EPOCH = 1788316969

.PHONY: all check clean distclean

all: $(DECK).pdf

$(DECK).pdf: $(DECK).tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(DECK).tex

check:
	@mkdir -p $(CHECK_DIR)
	latexmk -g -pdf -interaction=nonstopmode -halt-on-error -outdir=$(CHECK_DIR) $(DECK).tex
	@! grep -Eiq 'LaTeX Error|Undefined control sequence|undefined (references|citations)|Token not allowed in a PDF string|Overfull|Underfull' $(CHECK_DIR)/$(DECK).log
	@set -eu; \
		pages="$$(pdfinfo $(CHECK_PDF) | awk '/^Pages:/ {print $$2}')"; \
		title="$$(pdfinfo $(CHECK_PDF) | sed -n 's/^Title:[[:space:]]*//p')"; \
		author="$$(pdfinfo $(CHECK_PDF) | sed -n 's/^Author:[[:space:]]*//p')"; \
		test "$$pages" = "38"; \
		test "$$title" = "How Much Area Does a Circle Force? Gromov's Filling-Area Conjecture"; \
		test "$$author" = "Le Chen; Xiaolong Li; Yimin Zhong"
	@pdffonts $(CHECK_PDF) | awk 'NR > 2 && ($$(NF-4) != "yes" || $$(NF-3) != "yes") { bad = 1 } END { exit bad }'
	gs -q -dNOPAUSE -dBATCH -sDEVICE=nullpage $(CHECK_PDF)

clean:
	latexmk -c $(DECK).tex

distclean:
	latexmk -C $(DECK).tex
