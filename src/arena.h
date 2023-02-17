#pragma once

#include <stddef.h>
#include <stdalign.h>

typedef struct Arena Arena;
typedef struct GArena GArena;

void arena_init(Arena *arena);
void arena_destroy(Arena *arena);

void *arena_alloc(Arena *arena, size_t size);

size_t arena_save(Arena *arena);
void arena_restore(Arena *arena, size_t pos);


void garena_init(GArena *arena);
void garena_destroy(GArena *arena);

void *garena_alloc(GArena *arena, size_t size, size_t alignment);

size_t garena_save(GArena *arena);
void *garena_restore(GArena *arena, size_t pos);


#define move_to_arena(arena, garena, start, type) \
	move_to_arena_((arena), (garena), (start), alignof(type))
void *move_to_arena_(Arena *arena, GArena *garena, size_t start, size_t alignment);


void *garena_mem(GArena *arena);
void *garena_from(GArena *arena, size_t start, size_t alignment);

#define garena_cnt(arena, type) \
	garena_cnt_from_((arena), 0, sizeof(type))

#define garena_cnt_from(arena, start, type) \
	garena_cnt_from_((arena), (start), sizeof(type))

size_t garena_cnt_from_(GArena *arena, size_t start, size_t elem_size);

#define garena_push(arena, type) \
	((type *)garena_alloc((arena), sizeof(type), alignof(type)))

#define garena_push_value(arena, type, value) \
	do { \
		type tmp_pushed_ = (value); \
		*garena_push((arena), type) = tmp_pushed_; \
	} while (0)


typedef struct ArenaChunk ArenaChunk;
struct Arena {
	ArenaChunk *current;
	size_t prev_size_sum;
};

struct ArenaChunk {
	size_t size;
	size_t pos;
	ArenaChunk *prev;
	// Allocated chunk memory follows.
};

struct GArena {
	unsigned char *mem;
	size_t pos;
	size_t capacity;
};
