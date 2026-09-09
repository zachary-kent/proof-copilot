# Common tasks. Everything assumes `. ./env.sh` has been sourced.
.PHONY: help toolchain install test fast canary lint typecheck bench bench-run ladder docs-index goldens clean

help:
	@grep -E '^[a-z-]+:.*?## .*$$' $(MAKEFILE_LIST) | awk 'BEGIN{FS=":.*?## "}{printf "  %-12s %s\n", $$1, $$2}'

toolchain:  ## build the pinned Rocq/Iris/coq-lsp opam switch (Phase 0)
	./scripts/setup-toolchain.sh

install:  ## create the venv and install pcp with dev extras
	uv venv --python 3.11 .venv
	uv pip install --python .venv/bin/python -e '.[mcp,dev]' \
		'pytanque @ git+https://github.com/LLM4Rocq/pytanque'

test:  ## the whole suite
	.venv/bin/python -m pytest -q

fast:  ## everything that does not need Rocq or petanque
	.venv/bin/python -m pytest -q -m "not rocq and not petanque"

canary:  ## the golden end-to-end run of the daily loop (PLAN.md 8.11)
	.venv/bin/python -m pytest -q tests/test_canary.py

lint:  ## ruff over the package and the tests
	.venv/bin/ruff check pcp tests eval

typecheck:  ## mypy over the package
	.venv/bin/mypy pcp

bench:  ## rebuild the benchmark ladder (needs PCP_BENCH_SRC with ported sources)
	./eval/corpus/bench/build.sh

bench-run:  ## run one rung sandboxed and recorded: make bench-run RUNG=rwcas
	.venv/bin/python eval/harness.py \
		--corpus eval/corpus/bench/$(RUNG) --reference .pcp/reference/$(RUNG) \
		--sandbox --runner $(or $(RUNNER),claude) --record .pcp/records

ladder:  ## the design-rung ladder, spec-only (no hints, no library): make ladder STAMP=tonight
	.venv/bin/python eval/ladder.py --stamp $(or $(STAMP),$(shell date +%Y%m%d_%H%M%S)) --brief spec-only --no-carry --no-paper

docs-index:  ## index every Iris/std++ declaration for offline retrieval
	.venv/bin/pcp docs

goldens:  ## re-extract the real-Iris golden corpus after a toolchain bump
	.venv/bin/python eval/extract_goldens.py --limit-files 40 --limit-lemmas 12

clean:
	rm -rf .pytest_cache .ruff_cache .mypy_cache .pcp/work .pcp/eval
	find . -name __pycache__ -type d -prune -exec rm -rf {} +
