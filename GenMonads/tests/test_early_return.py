import textwrap

from GenMonads.early_return import detect_early_return_shape, find_first_top_level_loop


def test_detect_early_return_shape_loop_with_both_pre_and_body_early_returns():
    """Multi-merge-style function shape: an early-return guard before the
    loop AND an early-return inside the loop body must surface both flags.
    """
    source = textwrap.dedent(
        """\
        struct list * f(struct list * x, struct list * y) {
            if (x == 0) {
                return y;
            }
            while (x != 0) {
                if (y == 0) {
                    return x;
                }
                x = x->next;
            }
            return x;
        }
        """
    )

    info = detect_early_return_shape(source)

    assert info["has_top_level_loop"] is True
    assert info["has_pre_loop_early_return"] is True
    assert info["has_loop_body_early_return"] is True
    assert info["needs_early_result"] is True


def test_detect_early_return_shape_post_loop_return_only():
    source = textwrap.dedent(
        """\
        int demo(int x) {
            while (x) {
                x = x - 1;
            }
            return x;
        }
        """
    )

    info = detect_early_return_shape(source)

    assert info["has_top_level_loop"] is True
    assert info["has_pre_loop_early_return"] is False
    assert info["has_loop_body_early_return"] is False
    assert info["needs_early_result"] is False


def test_detect_early_return_shape_pre_loop_only():
    source = textwrap.dedent(
        """\
        int demo(int x) {
            if (x == 0) {
                return 0;
            }
            while (x) {
                x = x - 1;
            }
            return x;
        }
        """
    )

    info = detect_early_return_shape(source)

    assert info["has_top_level_loop"] is True
    assert info["has_pre_loop_early_return"] is True
    assert info["has_loop_body_early_return"] is False


def test_find_first_top_level_loop_finds_loop_inside_if_else():
    body = textwrap.dedent(
        """\
            if (x) {
                while (y) {
                    y = 0;
                }
            }
            while (z) {
                z = 0;
            }
        """
    )

    loop_info = find_first_top_level_loop(body)

    assert loop_info is not None
    assert body[int(loop_info["start"]):].startswith("while (y)")


def test_detect_early_return_shape_loop_inside_else_with_pre_return():
    source = textwrap.dedent(
        """\
        struct list * sll_append(struct list * x, struct list * y)
        {
            struct list *t, *u;
            if (x == 0) {
                return y;
            } else {
                t = x;
                u = t->next;
                while (u) {
                    t = u;
                    u = t->next;
                }
                t->next = y;
                return x;
            }
        }
        """
    )

    info = detect_early_return_shape(source)

    assert info["has_top_level_loop"] is True
    assert info["has_pre_loop_early_return"] is True
    assert info["has_loop_body_early_return"] is False
    assert info["needs_early_result"] is True
