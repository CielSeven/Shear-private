#ifndef GLIBC_SLIST_RAW_H
#define GLIBC_SLIST_RAW_H

#include <stddef.h>
#include <stdlib.h>

#define SLIST_HEAD(name, type) \
struct name { \
    struct type *slh_first; \
}

#define SLIST_ENTRY(type) \
struct { \
    struct type *sle_next; \
}

#define SLIST_INIT(head) do { \
    (head)->slh_first = NULL; \
} while (0)

#define SLIST_EMPTY(head) ((head)->slh_first == NULL)
#define SLIST_FIRST(head) ((head)->slh_first)
#define SLIST_NEXT(elm, field) ((elm)->field.sle_next)

#define SLIST_INSERT_HEAD(head, elm, field) do { \
    (elm)->field.sle_next = (head)->slh_first; \
    (head)->slh_first = (elm); \
} while (0)

#define SLIST_INSERT_AFTER(slistelm, elm, field) do { \
    (elm)->field.sle_next = (slistelm)->field.sle_next; \
    (slistelm)->field.sle_next = (elm); \
} while (0)

#define SLIST_REMOVE_HEAD(head, field) do { \
    (head)->slh_first = (head)->slh_first->field.sle_next; \
} while (0)

#define SLIST_FOREACH(var, head, field) \
    for ((var) = (head)->slh_first; (var) != NULL; (var) = (var)->field.sle_next)

struct glibc_slist_node {
    int data;
    SLIST_ENTRY(glibc_slist_node) link;
};

SLIST_HEAD(glibc_slist, glibc_slist_node);

static inline struct glibc_slist_node *glibc_slist_new_node(int data)
{
    struct glibc_slist_node *node;

    node = malloc(sizeof(*node));
    if (node != NULL) {
        node->data = data;
        node->link.sle_next = NULL;
    }
    return node;
}

static inline void glibc_slist_insert_tail(struct glibc_slist *head,
                                           struct glibc_slist_node *node)
{
    struct glibc_slist_node *pos;

    node->link.sle_next = NULL;
    if (SLIST_EMPTY(head)) {
        SLIST_INSERT_HEAD(head, node, link);
        return;
    }

    pos = SLIST_FIRST(head);
    while (SLIST_NEXT(pos, link) != NULL) {
        pos = SLIST_NEXT(pos, link);
    }
    SLIST_INSERT_AFTER(pos, node, link);
}

#endif
