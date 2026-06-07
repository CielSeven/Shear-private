#ifndef ZEPHYR_SLIST_RAW_H
#define ZEPHYR_SLIST_RAW_H

#include <stddef.h>
#include <stdlib.h>

typedef struct _snode {
    struct _snode *next;
} sys_snode_t;

typedef struct _slist {
    sys_snode_t *head;
    sys_snode_t *tail;
} sys_slist_t;

struct zephyr_slist_item {
    sys_snode_t node;
    int data;
};

#define SYS_SLIST_FOR_EACH_NODE(list, node) \
    for ((node) = (list)->head; (node) != NULL; (node) = (node)->next)

static inline struct zephyr_slist_item *zephyr_slist_item_from_node(sys_snode_t *node)
{
    return (struct zephyr_slist_item *)((char *)node - offsetof(struct zephyr_slist_item, node));
}

static inline void sys_slist_init(sys_slist_t *list)
{
    list->head = NULL;
    list->tail = NULL;
}

static inline int sys_slist_is_empty(sys_slist_t *list)
{
    return list->head == NULL;
}

static inline sys_snode_t *sys_slist_peek_head(sys_slist_t *list)
{
    return list->head;
}

static inline sys_snode_t *sys_slist_peek_tail(sys_slist_t *list)
{
    return list->tail;
}

static inline sys_snode_t *sys_slist_peek_next(sys_snode_t *node)
{
    return node == NULL ? NULL : node->next;
}

static inline void sys_slist_prepend(sys_slist_t *list, sys_snode_t *node)
{
    node->next = list->head;
    list->head = node;
    if (list->tail == NULL) {
        list->tail = node;
    }
}

static inline void sys_slist_append(sys_slist_t *list, sys_snode_t *node)
{
    node->next = NULL;
    if (list->tail == NULL) {
        list->head = node;
        list->tail = node;
        return;
    }

    list->tail->next = node;
    list->tail = node;
}

static inline void sys_slist_append_list(sys_slist_t *list, void *head, void *tail)
{
    sys_snode_t *first;
    sys_snode_t *last;

    first = head;
    last = tail;
    if (first == NULL) {
        return;
    }

    if (list->tail == NULL) {
        list->head = first;
    } else {
        list->tail->next = first;
    }
    list->tail = last;
}

static inline void sys_slist_merge_slist(sys_slist_t *list, sys_slist_t *list_to_append)
{
    sys_slist_append_list(list, list_to_append->head, list_to_append->tail);
    sys_slist_init(list_to_append);
}

static inline sys_snode_t *sys_slist_get(sys_slist_t *list)
{
    sys_snode_t *node;

    node = list->head;
    if (node == NULL) {
        return NULL;
    }

    list->head = node->next;
    if (list->head == NULL) {
        list->tail = NULL;
    }
    node->next = NULL;
    return node;
}

static inline void sys_slist_insert(sys_slist_t *list, sys_snode_t *prev, sys_snode_t *node)
{
    if (prev == NULL) {
        sys_slist_prepend(list, node);
        return;
    }

    node->next = prev->next;
    prev->next = node;
    if (list->tail == prev) {
        list->tail = node;
    }
}

static inline struct zephyr_slist_item *zephyr_slist_new_item(int data)
{
    struct zephyr_slist_item *item;

    item = malloc(sizeof(*item));
    if (item != NULL) {
        item->node.next = NULL;
        item->data = data;
    }
    return item;
}

#endif
