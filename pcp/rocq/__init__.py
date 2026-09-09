"""Rocq source text and the ``coqc`` path.  No petanque, no Iris model.

This package is what ``pcp.orch`` is allowed to know about Rocq: how to lex a file into
sentences and declarations, how to validate that a worker's patch is a proof body and
nothing else, how to assemble a development from frozen statements plus bodies, how to
compile it, and how to read ``Print Assumptions``.
"""
