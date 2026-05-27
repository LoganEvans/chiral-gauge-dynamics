# FILENAME: paper/Makefile

PAPER = paper.tex
PDF = $(PAPER:.tex=.pdf)

# Switch to LuaLaTeX natively for UTF-8 and Lean 4 Unicode support
LATEXMK_FLAGS = -lualatex -shell-escape -interaction=nonstopmode -silent

# ANSI Color Codes for terminal output
GREEN  := \033[1;32m
YELLOW := \033[1;33m
RED    := \033[1;31m
RESET  := \033[0m

.PHONY: all clean fullclean FORCE

all: $(PDF)

# Depend on FORCE so Make doesn't skip the build if only included files changed.
$(PDF): FORCE
	@old_hash=$$(cksum $(PDF) 2>/dev/null || echo "none"); \
	if latexmk $(LATEXMK_FLAGS) $(PAPER); then \
		new_hash=$$(cksum $(PDF) 2>/dev/null || echo "none"); \
		if [ "$$old_hash" = "$$new_hash" ]; then \
			printf "$(YELLOW)🟡 Success: $(PDF) is already up to date.$(RESET)\n"; \
		else \
			printf "$(GREEN)✅ Success: $(PDF) has been successfully built!$(RESET)\n"; \
		fi; \
	else \
		printf "$(RED)❌ Failure: latexmk encountered an error. Check paper.log.$(RESET)\n"; \
		exit 1; \
	fi

clean:
	@latexmk -silent -c $(PAPER)
	@rm -rf _minted*
	@rm -f $(PAPER:.tex=Notes.bib)

fullclean: clean
	@latexmk -silent -C $(PAPER)
	@rm -f $(PDF)
