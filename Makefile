NIX_FILES = $(shell git ls-files '*.nix' 'nix/*.nix')
SHELL_FILES = $(shell git ls-files '*.sh')
CHANGED_SHELL_FILES = $(shell git diff --diff-filter=d --name-only `git merge-base HEAD origin/main` | grep '.*\.sh$$')

NIX_FMT = nixpkgs-fmt

# Run Shellcheck with access to any file that's sourced, relative to the script's own directory
SHELLCHECK = shellcheck --external-sources --source-path=SCRIPTDIR

.PHONY: format-nix
## format-nix: auto-format Nix source code using `nixpkgs-fmt`
format-nix:
	@if command -v $(NIX_FMT) > /dev/null; then \
		echo "running $(NIX_FMT)"; \
		$(NIX_FMT) $(NIX_FILES); \
	else \
		echo "$(NIX_FMT) is not installed; skipping"; \
	fi

.PHONY: check-format-nix
## check-format-nix: check Nix source code using `nixpkgs-fmt`
check-format-nix:
	@if command -v $(NIX_FMT) > /dev/null; then \
		echo "running $(NIX_FMT) --check"; \
		$(NIX_FMT) --check $(NIX_FILES); \
	else \
		echo "$(NIX_FMT) is not installed; skipping"; \
	fi

.PHONY: lint-shell
## lint-shell: lint shell scripts using `shellcheck`
lint-shell:
	@echo running shellcheck
	@$(SHELLCHECK) $(SHELL_FILES)

.PHONY: lint-shell-changed
## lint-shell-changed: lint shell scripts using `shellcheck` (changed files only)
lint-shell-changed:
	@echo running shellcheck
	@if [ -n "$(CHANGED_SHELL_FILES)" ]; then \
		$(SHELLCHECK) $(CHANGED_SHELL_FILES); \
	fi

.PHONY: build
## build: build polytt
build: 
	dune build

.PHONY: clean
## clean: erase build artifacts
clean:
	dune clean

.PHONY: test
## test: run polytt test suite
test:
	dune clean
	dune test
