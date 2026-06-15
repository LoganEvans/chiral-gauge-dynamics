PAPER = paper.tex
PDF = $(PAPER:.tex=.pdf)
PROTON_RADIUS_PDF = proton-radius/jlab-hall-C-polarization-transfer.pdf

# Tell Make that the PDF depends on EVERY .tex file in this directory
TEX_FILES = $(wildcard *.tex)

# Switch to LuaLaTeX natively for UTF-8 and Lean 4 Unicode support
LATEXMK_FLAGS = -lualatex -shell-escape -interaction=nonstopmode -silent

# ANSI Color Codes for terminal output
GREEN  := \033[1;32m
RED    := \033[1;31m
RESET  := \033[0m

.PHONY: all clean fullclean

all: $(PDF) $(PROTON_RADIUS_PDF)

# Generate the labeled summary file whenever the base code summary or python script changes
code-summary-labeled.txt: code-summary.txt label_code.py
	@echo "Sanitizing AI context payload..."
	@sed -i 's/𝓝/nhds /g' code-summary.txt
	@echo "Injecting minted LaTeX labels..."
	@python3 label_code.py

$(PROTON_RADIUS_PDF): proton-radius/analysis.py proton-radius/graph.py
	@echo "Generating Proton Radius Analysis Graph..."
	@cd proton-radius && python3 graph.py

$(PDF): $(TEX_FILES) code-summary-labeled.txt $(PROTON_RADIUS_PDF)
	@echo "Building $(PDF)..."
	@if latexmk $(LATEXMK_FLAGS) $(PAPER); then \
		printf "$(GREEN)✅ Success: $(PDF) has been successfully built!$(RESET)\n"; \
	else \
		printf "$(RED)❌ Failure: latexmk encountered an error. Check paper.log.$(RESET)\n"; \
		exit 1; \
	fi

clean:
	@latexmk -silent -c $(PAPER)
	@rm -rf _minted*
	@rm -f $(PAPER:.tex=Notes.bib)
	@rm -f *.leanrefs
	@rm -f *.upa *.upb

fullclean: clean
	@latexmk -silent -C $(PAPER)
	@rm -f $(PDF)
	@rm -f $(PROTON_RADIUS_PDF)
	@rm -f code-summary-labeled.txt
