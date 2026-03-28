import textwrap

from GenMonads.early_return import detect_early_return_shape, find_first_top_level_loop


def test_detect_early_return_shape_for_sll_multi_merge():
    with open("shape_invdataset/sll/sll_multi_merge.c", "r", encoding="utf-8") as f:
        content = f.read()

    info = detect_early_return_shape(content)

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


def test_find_first_top_level_loop_ignores_nested_loop_before_real_one():
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
    assert body[int(loop_info["start"]):].startswith("while (z)")
