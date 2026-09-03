# Common tasks. Everything assumes `. ./env.sh` has been sourced.
.PHONY: help toolchain install test canary fast goldens bench bench-run docs-index lint clean

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

fast:  ## everything that does not need Rocq
	.venv/bin/python -m pytest -q -k 'not rocq' --ignore=tests/test_state_layer.py

canary:  ## the golden end-to-end run of the daily loop (PLAN.md 8.11)
	.venv/bin/python -m pytest -q tests/test_canary.py

bench:  ## rebuild the benchmark ladder (needs PCP_BENCH_SRC with ported sources)
	./eval/corpus/bench/build.sh

bench-run:  ## run one rung sandboxed and recorded: make bench-run RUNG=rwcas
	.venv/bin/python eval/harness.py \
		--corpus eval/corpus/bench/$(RUNG) --reference .pcp/reference/$(RUNG) \
		--sandbox --runner $(or $(RUNNER),claude) --record .pcp/records

docs-index:  ## index every Iris/std++ declaration for offline retrieval
	.venv/bin/pcp docs

goldens:  ## re-extract the real-Iris golden corpus after a toolchain bump
	.venv/bin/python eval/extract_goldens.py --limit-files 40 --limit-lemmas 12

clean:
	rm -rf .pytest_cache .pcp/work .pcp/eval **/__pycache__
