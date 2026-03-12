# guardgen/__init__.py
# Ensure built-in predicates are registered on import.
from . import registry  # noqa: F401
from .predicates import *  # registers sll, store_tree, sllseg  # noqa: F401,F403
from .translate import gen_coq_guard, gen_coq_from_bool  # noqa: F401
