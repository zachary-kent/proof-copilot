"""``pcp sketch``: compile the annotation DSL into a plan ``.v``."""

from __future__ import annotations

import argparse

from pcp.cli.common import absolute
from pcp.errors import UsageError
from pcp.util.io import atomic_write_text, json_dumps, read_text


def cmd_sketch(args: argparse.Namespace) -> int:
    from pcp.orch.sketch import compile_sketch

    src = absolute(args.file)
    if src is None or not src.exists():
        raise UsageError(f"{args.file}: no such sketch")
    sketch = compile_sketch(read_text(src))
    if args.json:
        print(json_dumps(sketch.to_json()))
        return 0
    out = absolute(args.out)
    assert out is not None
    atomic_write_text(out, sketch.render_plan())
    print(sketch.render_summary())
    print(f"\nwrote {out}")
    return 0
