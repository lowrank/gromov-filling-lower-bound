DECK := gromov_filling_mother_deck
export SOURCE_DATE_EPOCH = 1788316969

.PHONY: all check clean distclean

all: $(DECK).pdf

$(DECK).pdf: $(DECK).tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(DECK).tex

check: $(DECK).pdf
	@! grep -Eiq 'LaTeX Error|Undefined control sequence|undefined (references|citations)|Token not allowed in a PDF string|Overfull|Underfull' $(DECK).log
	@set -eu; \
		pages="$$(pdfinfo $(DECK).pdf | awk '/^Pages:/ {print $$2}')"; \
		title="$$(pdfinfo $(DECK).pdf | sed -n 's/^Title:[[:space:]]*//p')"; \
		author="$$(pdfinfo $(DECK).pdf | sed -n 's/^Author:[[:space:]]*//p')"; \
		test "$$pages" = "38"; \
		test "$$title" = "How Much Area Does a Circle Force? Gromov's Filling-Area Conjecture"; \
		test "$$author" = "Le Chen; Xiaolong Li; Yimin Zhong"
	@pdffonts $(DECK).pdf | awk 'NR > 2 && ($$(NF-4) != "yes" || $$(NF-3) != "yes") { bad = 1 } END { exit bad }'
	gs -q -dNOPAUSE -dBATCH -sDEVICE=nullpage $(DECK).pdf

clean:
	latexmk -c $(DECK).tex

distclean:
	latexmk -C $(DECK).tex
