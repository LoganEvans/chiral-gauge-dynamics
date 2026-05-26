PAPER = paper.tex
PDF = $(PAPER:.tex=.pdf)

# Compile in the current directory to prevent revtex/bibtex path crashes
# -silent: Suppresses noisy pdflatex output (full logs remain in paper.log)
LATEXMK_FLAGS = -pdf -shell-escape -interaction=nonstopmode -silent

.PHONY: all clean fullclean arxiv

# The default target acts as a wrapper. Because it's .PHONY, it ALWAYS runs.
all:
	@# Mutual Exclusion: If ANY arXiv artifacts exist, force a clean before building standard PDF
	@if ls arxiv* >/dev/null 2>&1; then \
		echo "================================================="; \
		echo "🧹 arXiv artifacts detected. Cleaning first..."; \
		echo "================================================="; \
		$(MAKE) clean; \
		rm -rf arxiv*; \
		rm -f $(PDF); \
	fi
	@# Now that the coast is clear, actually evaluate and build the PDF
	@$(MAKE) $(PDF)

$(PDF): $(PAPER)
	latexmk $(LATEXMK_FLAGS) $(PAPER)

# Clean standard auxiliary files
clean:
	latexmk -silent -c $(PAPER)
	rm -rf _minted*
	rm -f $(PAPER:.tex=Notes.bib)

# Clean everything, including the PDF
fullclean: clean
	latexmk -silent -C $(PAPER)
	rm -rf arxiv*
	rm -f $(PDF)

# ---------------------------------------------------------
# ARXIV SUBMISSION BUNDLER
# ---------------------------------------------------------
arxiv:
	@echo "================================================="
	@echo "🧹 Forcing a clean rebuild for arXiv package..."
	@echo "================================================="
	@$(MAKE) fullclean
	@$(MAKE) all
	@echo "================================================="
	@echo "📦 Preparing arXiv submission bundle..."
	@echo "================================================="
	@mkdir -p arxiv_build
	
	@cp $(PAPER) arxiv_build/
	@cp $(PAPER:.tex=.bbl) arxiv_build/ 2>/dev/null || true
	
	@# Safely copy minted caches ONLY if they exist 
	@if ls -d _minted* >/dev/null 2>&1; then \
		cp -r _minted* arxiv_build/; \
	fi
	
	@cp *.pdf *.png *.jpg arxiv_build/ 2>/dev/null || true
	@rm -f arxiv_build/$(PDF)
	
	@# Inject frozencache into minted for arXiv
	@sed 's/\\usepackage{minted}/\\usepackage\[frozencache\]{minted}/g' arxiv_build/$(PAPER) > arxiv_build/$(PAPER).tmp
	@mv arxiv_build/$(PAPER).tmp arxiv_build/$(PAPER)
	
	@cd arxiv_build && zip -r ../arxiv_submission.zip . > /dev/null
	@echo "✅ Success: arxiv_submission.zip is ready for upload!"
