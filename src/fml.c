// FML language interpreters/runtimes
// Michal Vlasák, FIT CTU, 2023

#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdalign.h>
#include <string.h>
#include <assert.h>
#include <inttypes.h>
#include <setjmp.h>
#include <errno.h>
#include <time.h>

#include "parser.h"


#define garena_array(arena, type) \
	((type *) garena_mem((arena)))

#define garena_array_from(arena, start, type) \
	((type *) garena_from((arena), (start), alignof(type)))

#define container_of(member_ptr, type, member) \
	((type *) ((u8 *)(1 ? (member_ptr) : &((type *) 0)->member) - offsetof(type, member)))

#ifdef __GNUC__
#define printf_attr(n) __attribute__((__format__(__printf__, n, n + 1)))
#else
#define printf_attr(n)
#endif

#define UNREACHABLE() unreachable(__FILE__, __LINE__)
static _Noreturn void
unreachable(char *file, size_t line)
{
	fprintf(stderr, "ERROR: unreachable code reached at %s:%zu\n", file, line);
	exit(EXIT_FAILURE);
}

// FNV-1a hash
// http://www.isthe.com/chongo/tech/comp/fnv/
u64
str_hash(Str id)
{
	u64 h = UINT64_C(14695981039346656037);
	for (size_t i = 0; i < id.len; i++) {
		// beware of unwanted sign extension!
		h ^= id.str[i];
		h *= UINT64_C(1099511628211);
	}
	return h;
}

typedef struct Heap Heap;

typedef struct Error Error;
struct Error {
	Error *next;
	char *kind;
	const u8 *pos;
	u8 *msg;
};

typedef struct {
	Arena arena;
	Str source;
	Error *error_head;
	Error *error_tail;
	jmp_buf loc;

	// For freeing the heap on error
	Heap *heap;
} ErrorContext;

void
error_context_init(ErrorContext *ec)
{
	arena_init(&ec->arena);
	ec->source = (Str) {0};
	ec->error_head = NULL;
	ec->error_tail = NULL;
	ec->heap = NULL;
}

u8 *
arena_vaprintf(Arena *arena, const char *fmt, va_list ap)
{
	va_list ap_orig;
	// save original va_list (vprintf changes it)
	va_copy(ap_orig, ap);

	size_t available = arena->current->size - arena->current->pos;
	void *mem = ((u8 *) arena->current) + arena->current->pos;
	int len = vsnprintf(mem, available, fmt, ap);
	assert(len >= 0);
	len += 1; // terminating null
	if ((size_t) len <= available) {
		arena->current->pos += (size_t) len;
	} else {
		mem = arena_alloc(arena, (size_t) len);
		vsnprintf(mem, (size_t) len, fmt, ap_orig);
	}
	va_end(ap_orig);
	return mem;
}


static void
verror(ErrorContext *ec, const u8 *pos, char *kind, bool fatal, const char *fmt, va_list ap)
{
	Error *error = arena_alloc(&ec->arena, sizeof(*error));
	error->msg = arena_vaprintf(&ec->arena, fmt, ap);
	error->pos = pos;
	error->kind = kind;
	error->next = NULL;
	if (ec->error_tail) {
		ec->error_tail->next = error;
	}
	ec->error_tail = error;
	if (!ec->error_head) {
		ec->error_head = error;
	}
	if (fatal) {
		longjmp(ec->loc, 1);
	}
}

static void
parser_verror(void *user_data, const u8 *err_pos, const char *msg, va_list ap)
{
	ErrorContext *ec = user_data;
	verror(ec, err_pos, "parse", false, msg, ap);
}

Ast *
parse_source(ErrorContext *ec, Arena *arena, Str source)
{
	size_t arena_start = arena_save(arena);
	GArena scratch;
	garena_init(&scratch);
	ec->source = source;
	Ast *ast = parse(arena, &scratch, source, parser_verror, ec);
	garena_destroy(&scratch);
	if (!ast) {
		arena_restore(arena, arena_start);
		longjmp(ec->loc, 1);
	}
	return ast;
}

typedef enum {
	VK_NULL,
	VK_BOOLEAN,
	VK_INTEGER,
	VK_GCVALUE,
	VK_FUNCTION,
} ValueKind;

typedef enum {
	GK_ARRAY,
	GK_OBJECT,

	GK_PRINTING,
} GcValueKind;

typedef struct GcValue GcValue;

typedef struct {
	ValueKind kind;
	union {
		bool boolean;
		i32 integer;
		GcValue *gcvalue;

		// For AST interpreter.
		AstFunction *function;
		// For BC interpreter.
		u16 function_index;
	};
} Value;

struct GcValue {
	GcValueKind kind;
	GcValue *prev;
};

typedef struct {
	GcValue gcvalue;
	size_t length;
	Value values[];
} Array;

typedef struct {
	Str name;
	Value value;
} Field;

typedef struct {
	GcValue gcvalue;
	Value parent;
	size_t field_cnt;
	Field fields[];
} Object;

typedef struct {
	GcValue gcvalue;
	Ast *ast;
} Function;

static void printf_attr(2)
exec_error(ErrorContext *ec, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	verror(ec, NULL, "execution", true, msg, ap);
	va_end(ap);
}

struct Heap {
	ErrorContext *ec;
	void (*gc_func)(Heap *heap);
	FILE *log;
	//u8 *mem;
	size_t pos;
	size_t size;
};

static void
heap_log(Heap *heap, const char *event)
{
	if (!heap->log) {
		return;
	}
	struct timespec ts;
	if (!time_get(&ts)) {
		exec_error(heap->ec, "Failed to get time");
	}
	long long sec = ts.tv_sec;
	long nsec = ts.tv_nsec;
	fprintf(heap->log, "%lld%09ld,%s,%zu\n", sec, nsec, event, heap->pos);
}


static void
heap_init(Heap *heap, ErrorContext *ec, void (*gc_func)(Heap *heap), size_t size, FILE *log)
{
	// We don't have GC, so we can't really deal with having less amount of
	// memory, so we set our heap size unconditionally.
	if (size == 0 || true) {
		size = 1280;
	}
	// MiB
	size = size * 1024 * 1024;
	*heap = (Heap) {
		.ec = ec,
		.gc_func = gc_func,
		.log = log,
		.pos = 0,
		.size = size,
	};
	if (heap->log) {
		fputs("timestamp,event,heap\n", heap->log);
		heap_log(heap, "S");
	}
	ec->heap = heap;
}

void
heap_destroy(Heap *heap)
{
	heap_log(heap, "E");
	if (heap->log && fclose(heap->log) != 0) {
		exec_error(heap->ec, "Failed to write to heap log: %s", strerror(errno));
	}
}

static size_t
align(size_t pos, size_t alignment)
{
	return (pos + (alignment - 1)) & ~(alignment - 1);
}

static void *
heap_alloc(Heap *heap, size_t size)
{
	size_t pos = align(heap->pos, 8);
	if (pos + size > heap->size) {
		heap_log(heap, "B");
		heap->gc_func(heap);
		heap_log(heap, "A");
		pos = align(heap->pos, 8);
		if (pos + size > heap->size) {
			exec_error(heap->ec, "Heap space exhausted");
		}
	}
	heap->pos = pos + size;
	return malloc(size);
}

Value
make_null(Heap *heap)
{
	(void) heap;
	return (Value) { .kind = VK_NULL };
}

Value
make_boolean(Heap *heap, bool value)
{
	(void) heap;
	return (Value) { .kind = VK_BOOLEAN, .boolean = value };
}

Value
make_integer(Heap *heap, i32 value)
{
	(void) heap;
	return (Value) { .kind = VK_INTEGER, .integer = value };
}

static GcValue *last;

Value
make_array(Heap *heap, size_t length)
{
	Array *array = heap_alloc(heap, sizeof(*array) + length * sizeof(array->values[0]));
	array->gcvalue = (GcValue) { .kind = GK_ARRAY };
	array->length = length;

	array->gcvalue.prev = last;
	last = &array->gcvalue;

	return (Value) { .kind = VK_GCVALUE, .gcvalue = &array->gcvalue };
}

Value
make_object(Heap *heap, size_t field_cnt)
{
	Object *object = heap_alloc(heap, sizeof(*object) + field_cnt * sizeof(object->fields[0]));
	object->gcvalue = (GcValue) { .kind = GK_OBJECT };
	// NOTE: Caller has to set parent!
	//object->parent = make_null();
	object->field_cnt = field_cnt;

	object->gcvalue.prev = last;
	last = &object->gcvalue;

	return (Value) { .kind = VK_GCVALUE, .gcvalue = &object->gcvalue };
}

Value
make_function_ast(Heap *heap, AstFunction *function)
{
	(void) heap;
	return (Value) { .kind = VK_FUNCTION, .function = function };
}

Value
make_function_bc(Heap *heap, u16 function_index)
{
	(void) heap;
	return (Value) { .kind = VK_FUNCTION, .function_index = function_index };
}

bool
value_is_null(Value value)
{
	return value.kind == VK_NULL;
}

bool
value_is_bool(Value value)
{
	return value.kind == VK_BOOLEAN;
}

bool
value_as_bool(Value value)
{
	assert(value.kind == VK_BOOLEAN);
	return value.boolean;
}

bool
value_is_integer(Value value)
{
	return value.kind == VK_INTEGER;
}

i32
value_as_integer(Value value)
{
	assert(value.kind == VK_INTEGER);
	return value.integer;
}

bool
value_is_array(Value value)
{
	return value.kind == VK_GCVALUE && value.gcvalue->kind == GK_ARRAY;
}

Array *
value_as_array(Value value)
{
	assert(value.kind == VK_GCVALUE);
	assert(value.gcvalue->kind == GK_ARRAY);
	return (Array *) value.gcvalue;
}

bool
value_is_object(Value value)
{
	return value.kind == VK_GCVALUE && value.gcvalue->kind == GK_OBJECT;
}

Object *
value_as_object(Value value)
{
	assert(value.kind == VK_GCVALUE);
	assert(value.gcvalue->kind == GK_OBJECT);
	return (Object *) value.gcvalue;
}

bool
value_is_function(Value value)
{
	return value.kind == VK_FUNCTION;
}

AstFunction *
value_as_function_ast(Value value)
{
	assert(value.kind == VK_FUNCTION);
	return value.function;
}

u16
value_as_function_bc(Value value)
{
	assert(value.kind == VK_FUNCTION);
	return (u16) value.function_index;
}

void
value_print(Value value)
{
	switch (value.kind) {
	case VK_NULL:
		printf("%s", "null");
		break;
	case VK_BOOLEAN:
		printf("%s", value_as_bool(value) ? "true" : "false");
		break;
	case VK_INTEGER:
		printf("%"PRIi32, value_as_integer(value));
		break;
	case VK_GCVALUE:
		switch (value.gcvalue->kind) {
		case GK_ARRAY: {
			printf("[");
			Array *array = value_as_array(value);
			array->gcvalue.kind = GK_PRINTING;
			for (size_t i = 0; i < array->length; i++) {
				if (i != 0) {
					printf(", ");
				}
				value_print(array->values[i]);
			}
			printf("]");
			array->gcvalue.kind = GK_ARRAY;
			break;
		}
		case GK_OBJECT:
			printf("object(");
			Object *object = value_as_object(value);
			object->gcvalue.kind = GK_PRINTING;

			Value parent = object->parent;
			bool prev = false;
			if (!value_is_null(parent)) {
				printf("..=");
				value_print(parent);
				prev = true;
			}
			Field *fields = calloc(object->field_cnt, sizeof(*fields));
			for (size_t i = 0; i < object->field_cnt; i++) {
				fields[i] = object->fields[i];
				for (size_t j = i; j > 0 && str_cmp(fields[j - 1].name, fields[j].name) > 0; j--) {
					Field tmp = fields[j - 1];
					fields[j - 1] = fields[j];
					fields[j] = tmp;
				}
			}

			for (size_t i = 0; i < object->field_cnt; i++) {
				if (prev) {
					printf(", ");
				}
				Str name = fields[i].name;
				printf("%.*s=", (int)name.len, name.str);
				value_print(fields[i].value);
				prev = true;
			}
			printf(")");
			free(fields);
			object->gcvalue.kind = GK_OBJECT;
			break;
		case GK_PRINTING:
			printf("...");
			break;
		}
		break;
	case VK_FUNCTION:
		printf("function");
		break;
	}
}

static void
builtin_print(ErrorContext *ec, Str format, Value *arguments, size_t argument_cnt)
{
	bool in_escape = false;
	size_t arg_index = 0;
	for (size_t i = 0; i < format.len; i++) {
		u8 c = format.str[i];
		if (in_escape) {
			in_escape = false;
			switch (c) {
			case  'n': c = '\n'; break;
			case  't': c = '\t'; break;
			case  'r': c = '\r'; break;
			case  '~': c =  '~'; break;
			case  '"': c =  '"'; break;
			case '\\': c = '\\'; break;
			default:
				exec_error(ec, "Invalid escape sequence: '\\%c'", c);
			}
			putchar(c);
		} else {
			switch (c) {
			case '\\': in_escape = true; break;
			case '~':
				if (arg_index >= argument_cnt) {
					exec_error(ec, "More format string placeholders (%zu+) than arguments (%zu)", arg_index + 1, argument_cnt);
				}
				value_print(arguments[arg_index]);
				arg_index += 1;
				break;
			default:
				putchar(c);
			}
		}
	}
	fflush(stdout);
}

bool
value_to_bool(Value value)
{
	if (value.kind == VK_NULL || (value.kind == VK_BOOLEAN && value_as_bool(value) == false)) {
		return false;
	}
	return true;
}

size_t
value_as_size(ErrorContext *ec, Value value)
{
	if (!value_is_integer(value)) {
		exec_error(ec, "Value is not an integer");
	}
	i32 int_index = value_as_integer(value);
	if (int_index < 0) {
		exec_error(ec, "Value is negative");
	}
	return (size_t) int_index;
}

Value *
array_index(ErrorContext *ec, Value array_value, Value index_value)
{
	Array *array = value_as_array(array_value);
	size_t index = value_as_size(ec, index_value);
	if (index >= array->length) {
		exec_error(ec, "Array indexed out of bounds");
	}
	return &array->values[index];
}

Value *
value_field_try(Value value, Value *receiver, Str name)
{
	if (!value_is_object(value)) {
		// We did not find the field, but we have the eldest parent
		// object on which we can call a primitive method (hopefully)
		*receiver = value;
		return NULL;
	}
	Object *object = value_as_object(value);
	for (size_t i = 0; i < object->field_cnt; i++) {
		if (str_eq(object->fields[i].name, name)) {
			// We found the field, set the receiver Object to the
			// field's owner
			receiver->gcvalue = &object->gcvalue;
			return &object->fields[i].value;
		}
	}
	return value_field_try(object->parent, receiver, name);
}

Value *
value_field(ErrorContext *ec, Value value, Value *receiver, Str name)
{
	Value *field = value_field_try(value, receiver, name);
	if (!field) {
		exec_error(ec, "failed to find field '%.*s' in object", (int)name.len, name.str);
	}
	return field;
}

Value *
value_method_try(ErrorContext *ec, Value value, Value *receiver, Str name)
{
	bool was_object = value_is_object(value);
	Value *field = value_field_try(value, receiver, name);
	if (was_object && value_is_null(*receiver)) {
		exec_error(ec, "undefined method '%.*s' for object", (int)name.len, name.str);
	}
	if (field && !value_is_function(*field)) {
		exec_error(ec, "Method in method call is not a function");
	}
	return field;
}

Value
value_call_primitive_method(ErrorContext *ec, Heap *heap, Value target, Str method, Value *arguments, size_t argument_cnt)
{
	const u8 *method_name = method.str;
	size_t method_name_len = method.len;
	#define METHOD(name) \
			if (sizeof(name) - 1 == method_name_len && memcmp(name, method_name, method_name_len) == 0) /* body */

	METHOD("==") {
		if (argument_cnt != 1) goto err;
		if (target.kind != arguments[0].kind) return make_boolean(heap, false);
		switch (target.kind) {
		case VK_NULL: return make_boolean(heap, true);
		case VK_BOOLEAN: return make_boolean(heap, value_as_bool(target) == value_as_bool(arguments[0]));
		case VK_INTEGER: return make_boolean(heap, value_as_integer(target) == value_as_integer(arguments[0]));
		default: goto err;
		}
	}
	METHOD("!=") {
		if (argument_cnt != 1) goto err;
		if (target.kind != arguments[0].kind) return make_boolean(heap, true);
		switch (target.kind) {
		case VK_NULL: return make_boolean(heap, false);
		case VK_BOOLEAN: return make_boolean(heap, value_as_bool(target) != value_as_bool(arguments[0]));
		case VK_INTEGER: return make_boolean(heap, value_as_integer(target) != value_as_integer(arguments[0]));
		default: goto err;
		}
	}

	switch (target.kind) {
	case VK_NULL:
		break;
	case VK_BOOLEAN: {
		if (argument_cnt != 1) goto err;
		if (arguments[0].kind != VK_BOOLEAN) goto err;
		bool left = value_as_bool(target);
		bool right = value_as_bool(arguments[0]);
		METHOD("&") return make_boolean(heap, left && right);
		METHOD("|") return make_boolean(heap, left || right);
		break;
	}
	case VK_INTEGER: {
		if (argument_cnt != 1) goto err;
		if (arguments[0].kind != VK_INTEGER) goto err;
		i32 left = value_as_integer(target);
		i32 right = value_as_integer(arguments[0]);
		METHOD("+") return make_integer(heap, left + right);
		METHOD("-") return make_integer(heap, left - right);
		METHOD("*") return make_integer(heap, left * right);
		METHOD("/") {
				if (right == 0) {
					exec_error(ec, "Division by zero");
					return make_integer(heap, 0);
				} else {
					return make_integer(heap, left / right);
				}
		}
		METHOD("%") {
				if (right == 0) {
					exec_error(ec, "Modulo by zero");
					return make_integer(heap, 0);
				} else {
					return make_integer(heap, left % right);
				}
		}
		METHOD("<=") return make_boolean(heap, left <= right);
		METHOD("<") return make_boolean(heap, left < right);
		METHOD(">=") return make_boolean(heap, left >= right);
		METHOD(">") return make_boolean(heap, left > right);
		break;
	}
	case VK_GCVALUE:
		switch (target.gcvalue->kind) {
		case GK_ARRAY:
			METHOD("get") {
				if (argument_cnt != 1) goto err;
				Value *lvalue = array_index(ec, target, arguments[0]);
				return *lvalue;
			}
			METHOD("set") {
				if (argument_cnt != 2) goto err;
				Value *lvalue = array_index(ec, target, arguments[0]);
				return *lvalue = arguments[1];
			}
			break;
		case GK_OBJECT:
			break;
		case GK_PRINTING:
			UNREACHABLE();
			break;
		}
		break;
	case VK_FUNCTION:
		break;
	}
err:
	exec_error(ec, "Invalid method '%.*s' called on value (invalid types or number of arguments)", (int) method_name_len, method_name);
	return make_null(heap);
}

// A simple hash table.
// Inspired by: http://www.craftinginterpreters.com/hash-tables.html

typedef struct {
	Str key;
	Value value;
} Entry;

typedef struct {
	Entry *entries;
	size_t entry_cnt;
	size_t capacity;
} Table;

void
table_init(Table *table, size_t capacity)
{
	table->entry_cnt = 0;
	if (capacity == 0) {
		table->capacity = 0;
		table->entries = NULL;
	} else {
		table->capacity = 1;
		while (table->capacity < capacity) {
			table->capacity *= 2;
		}
		table->entries = calloc(table->capacity, sizeof(*table->entries));
	}
}

void
table_destroy(Table *table)
{
	free(table->entries);
}

Entry *
table_find_entry(Entry *entries, size_t capacity, Str key)
{
	u64 hash = str_hash(key);
	// NOTE: We guarantee that the capacity is a power of two. The modulo
	// operation thus simplifies to simple binary AND.
	size_t mask = capacity - 1;
	for (size_t index = hash & mask;; index = (index + 1) & mask) {
		Entry *entry = &entries[index];
		if (entry->key.str == NULL || str_eq(entry->key, key)) {
			return entry;
		}
	}
}

void
table_grow(Table *table)
{
	size_t capacity = table->capacity ? table->capacity * 2 : 8;
	// TODO: intialize memory if not zero allocated
	Entry *entries = calloc(capacity, sizeof(*entries));
	for (size_t i = 0; i < table->capacity; i++) {
		Entry *old = &table->entries[i];
		if (old->key.str == NULL) {
			continue;
		}
		Entry *new = table_find_entry(entries, capacity, old->key);
		*new = *old;
	}
	free(table->entries);
	table->entries = entries;
	table->capacity = capacity;
}

Value *
table_get(Table *table, Str key)
{
	if (table->entry_cnt == 0) {
		return NULL;
	}
	Entry *entry = table_find_entry(table->entries, table->capacity, key);
	if (entry->key.str == NULL) {
		return NULL;
	}
	return &entry->value;
}

bool
table_insert(Table *table, Str key, Value value)
{
	if (table->entry_cnt + 1 >= table->capacity / 2) {
		table_grow(table);
	}
	Entry *entry = table_find_entry(table->entries, table->capacity, key);
	bool new = entry->key.str == NULL;
	if (new) {
		table->entry_cnt += 1;
		entry->key = key;
	}
	entry->value = value;
	return new;
}

typedef struct Environment Environment;
struct Environment {
	Environment *prev;
	Table env;
};

typedef struct {
	ErrorContext *ec;
	Environment *env;
	Environment *global_env;
	Heap heap;
} InterpreterState;

void
env_push(Environment **prev)
{
	Environment *env = calloc(sizeof(*env), 1);
	table_init(&env->env, 0);
	env->prev = *prev;
	*prev = env;
}

void
env_pop(Environment **env)
{
	Environment *old = *env;
	(*env) = (*env)->prev;
	table_destroy(&old->env);
	free(old);
}

void
env_define(Environment *env, Str name, Value value)
{
	table_insert(&env->env, name, value);
}

Value *
env_lookup_raw(Environment *env, Str name)
{
	if (!env) {
		return NULL;
	}
	Value *lvalue = table_get(&env->env, name);
	if (lvalue) {
		return lvalue;
	}
	return env_lookup_raw(env->prev, name);
}

Value *
env_lookup(InterpreterState *is, Str name)
{
	Value *lvalue = env_lookup_raw(is->env, name);
	if (!lvalue) {
		//exec_error(is->ec, "Unknown reference to '%.*s'", name.len, name.str);
		// Name not found, should be a global whose
		// definition we will yet see.
		Value null = make_null(&is->heap);
		// TODO: could be improved by having env_define return an lvalue
		env_define(is->global_env, name, null);
		return env_lookup_raw(is->global_env, name);
	}
	return lvalue;
}

static Value interpreter_call_method(InterpreterState *is, Value object, bool function_call, Str method, Ast **ast_arguments, size_t argument_cnt);

static Value
interpret(InterpreterState *is, Ast *ast)
{
	switch (ast->kind) {
	case AST_NULL: {
		return make_null(&is->heap);
	}
	case AST_BOOLEAN: {
		AstBoolean *boolean = (AstBoolean *) ast;
		return make_boolean(&is->heap, boolean->value);
	}
	case AST_INTEGER: {
		AstInteger *integer = (AstInteger *) ast;
		return make_integer(&is->heap, integer->value);
	}
	case AST_ARRAY: {
		AstArray *array = (AstArray *) ast;
		Value size_value = interpret(is, array->size);
		size_t size = value_as_size(is->ec, size_value);
		Value array_value = make_array(&is->heap, size);
		Array *array_obj = value_as_array(array_value);
		for (size_t i = 0; i < size; i++) {
			env_push(&is->env);
			array_obj->values[i] = interpret(is, array->initializer);
			env_pop(&is->env);
		}
		return array_value;
	}
	case AST_OBJECT: {
		AstObject *object = (AstObject *) ast;
		Value parent = interpret(is, object->extends);
		Value object_value = make_object(&is->heap, object->member_cnt);
		Object *object_obj = value_as_object(object_value);
		object_obj->parent = parent;
		for (size_t i = 0; i < object->member_cnt; i++) {
			Ast *ast_member = object->members[i];
			switch (ast_member->kind) {
			case AST_DEFINITION: {
				AstDefinition *definition = (AstDefinition *) ast_member;
				object_obj->fields[i].name = definition->name;
				env_push(&is->env);
				object_obj->fields[i].value = interpret(is, definition->value);
				env_pop(&is->env);
				break;
			}
			default:
				UNREACHABLE();
			}
		}
		return object_value;
	}
	case AST_FUNCTION: {
		AstFunction *function = (AstFunction *) ast;
		return make_function_ast(&is->heap, function);
	}

	case AST_DEFINITION: {
		AstDefinition *definition = (AstDefinition *) ast;
		Value value = interpret(is, definition->value);
		env_define(is->env, definition->name, value);
		return value;
	}

	case AST_VARIABLE_ACCESS: {
		AstVariableAccess *variable_access = (AstVariableAccess *) ast;
		Value *lvalue = env_lookup(is, variable_access->name);
		return *lvalue;
	}
	case AST_VARIABLE_ASSIGNMENT: {
		AstVariableAssignment *variable_assignment = (AstVariableAssignment *) ast;
		Value value = interpret(is, variable_assignment->value);
		Value *lvalue = env_lookup(is, variable_assignment->name);
		return *lvalue = value;
	}

	case AST_INDEX_ACCESS: {
		AstIndexAccess *index_access = (AstIndexAccess *) ast;
		Value object = interpret(is, index_access->object);
		return interpreter_call_method(is, object, false, STR("get"), &index_access->index, 1);
	}
	case AST_INDEX_ASSIGNMENT: {
		AstIndexAssignment *index_assignment = (AstIndexAssignment *) ast;
		Value object = interpret(is, index_assignment->object);
		Ast *arguments[2] = {index_assignment->index, index_assignment->value};
		return interpreter_call_method(is, object, false, STR("set"), &arguments[0], 2);
	}

	case AST_FIELD_ACCESS: {
		AstFieldAccess *field_access = (AstFieldAccess *) ast;
		Value object = interpret(is, field_access->object);
		Value *lvalue = value_field(is->ec, object, &object, field_access->field);
		return *lvalue;
	}
	case AST_FIELD_ASSIGNMENT: {
		AstFieldAssignment *field_assignment = (AstFieldAssignment *) ast;
		Value object = interpret(is, field_assignment->object);
		Value value = interpret(is, field_assignment->value);
		Value *lvalue = value_field(is->ec, object, &object, field_assignment->field);
		return *lvalue = value;
	}

	case AST_FUNCTION_CALL: {
		AstFunctionCall *function_call = (AstFunctionCall *) ast;
		Value function = interpret(is, function_call->function);
		return interpreter_call_method(is, function, true, STR(""), function_call->arguments, function_call->argument_cnt);
	}
	case AST_METHOD_CALL: {
		AstMethodCall *method_call = (AstMethodCall *) ast;
		Value object = interpret(is, method_call->object);
		return interpreter_call_method(is, object, false, method_call->name, method_call->arguments, method_call->argument_cnt);
	}

	case AST_CONDITIONAL: {
		AstConditional *conditional = (AstConditional *) ast;
		Value condition = interpret(is, conditional->condition);
		env_push(&is->env);
		Value result;
		if (value_to_bool(condition)) {
			result = interpret(is, conditional->consequent);
		} else {
			result = interpret(is, conditional->alternative);
		}
		env_pop(&is->env);
		return result;
	}
	case AST_LOOP: {
		AstLoop *loop = (AstLoop *) ast;
		while (value_to_bool(interpret(is, loop->condition))) {
			env_push(&is->env);
			interpret(is, loop->body);
			env_pop(&is->env);
		}
		return make_null(&is->heap);
	}
	case AST_PRINT: {
		AstPrint *print = (AstPrint *) ast;
		Value *arguments = calloc(print->argument_cnt, sizeof(*arguments));
		for (size_t i = 0; i < print->argument_cnt; i++) {
			arguments[i] = interpret(is, print->arguments[i]);
		}
		builtin_print(is->ec, print->format, arguments, print->argument_cnt);
		free(arguments);
		return make_null(&is->heap);
	}
	case AST_BLOCK: {
		AstBlock *block = (AstBlock *) ast;
		env_push(&is->env);
		Value value = interpret(is, block->expressions[0]);
		for (size_t i = 1; i < block->expression_cnt; i++) {
			value = interpret(is, block->expressions[i]);
		}
		env_pop(&is->env);
		return value;
	}
	case AST_TOP: {
		AstTop *top = (AstTop *) ast;
		Value value = interpret(is, top->expressions[0]);
		for (size_t i = 1; i < top->expression_cnt; i++) {
			value = interpret(is, top->expressions[i]);
		}
		return value;
	}
	}
	UNREACHABLE();
}

static Value
interpreter_call_method(InterpreterState *is, Value object, bool function_call, Str method, Ast **ast_arguments, size_t argument_cnt)
{
	Value return_value;
	Value *arguments = calloc(argument_cnt, sizeof(*arguments));

	for (size_t i = 0; i < argument_cnt; i++) {
		arguments[i] = interpret(is, ast_arguments[i]);
	}

	AstFunction *function = NULL;
	if (function_call) {
		if (!value_is_function(object)) {
			exec_error(is->ec, "Function call target is not a function");
		}
		function = value_as_function_ast(object);
	} else {
		Value *function_value = value_method_try(is->ec, object, &object, method);
		function = function_value ? value_as_function_ast(*function_value) : NULL;
	}
	if (function) {
		if (argument_cnt != function->parameter_cnt) {
			exec_error(is->ec, "Wrong number of arguments: %zu expected, got %zu", function->parameter_cnt, argument_cnt);
		}

		// Starting with _only_ the global environment, add the function
		// arguments to the scope
		Environment *saved_env = is->env;
		is->env = is->global_env;
		env_push(&is->env);
		if (!function_call) {
			env_define(is->env, STR("this"), object);
		}
		for (size_t i = 0; i < argument_cnt; i++) {
			env_define(is->env, function->parameters[i], arguments[i]);
		}
		return_value = interpret(is, function->body);
		env_pop(&is->env);
		is->env = saved_env;
	} else {
		return_value = value_call_primitive_method(is->ec, &is->heap, object, method, &arguments[0], argument_cnt);
	}
	free(arguments);
	return return_value;
}

static void
gc_none(Heap *heap)
{
	(void) heap;
}

void
interpret_ast(ErrorContext *ec, Arena *arena, Ast *ast, size_t heap_size, FILE *heap_log)
{
	InterpreterState *is = arena_alloc(arena, sizeof(*is));
	*is = (InterpreterState) {
		.ec = ec,
		.env = NULL,
		.global_env = NULL,
		.heap = {0},
	};
	env_push(&is->env);
	is->global_env = is->env;
	heap_init(&is->heap, ec, gc_none, heap_size, heap_log);
	env_define(is->env, STR("this"), make_null(&is->heap));
	interpret(is, ast);
	env_pop(&is->env);
}

// Parse little endian numbers from byte array. Beware of implicit promotion from uint8_t to signed int.
// https://commandcenter.blogspot.com/2012/04/byte-order-fallacy.html
// https://www.reddit.com/r/C_Programming/comments/bjuk3v/the_byte_order_fallacy/embbwq2/

static u32
read_u32(u8 **src)
{
	u8 *pos = *src;
	u32 res = (((u32) pos[3]) << 24) | (((u32) pos[2]) << 16)
		| (((u32) pos[1]) <<  8) | (((u32) pos[0]) <<  0);
	*src += 4;
	return res;
}

static uint16_t
read_u16(u8 **src)
{
	u8 *pos = *src;
	u16 res = (((u32) pos[1]) <<  8) | (((u32) pos[0]) <<  0);
	*src += 2;
	return res;
}

static uint8_t
read_u8(u8 **src)
{
	return *(*src)++;
}

//                    F,    M,    L,   \n
u8 FML_MAGIC[] = { 0x46, 0x4D, 0x4C, 0x0A };

typedef enum {
	CK_NULL = 0x01,
	CK_BOOLEAN = 0x04,
	CK_INTEGER = 0x00,
	CK_STRING = 0x02,
	CK_FUNCTION = 0x03,
	CK_CLASS = 0x05,
} ConstantKind;

typedef enum {
	OP_CONSTANT = 0x01,
	OP_ARRAY = 0x03,
	OP_OBJECT = 0x04,
	OP_GET_LOCAL = 0x0A,
	OP_SET_LOCAL = 0x09,
	OP_GET_GLOBAL = 0x0C,
	OP_SET_GLOBAL = 0x0B,
	OP_GET_FIELD = 0x05,
	OP_SET_FIELD = 0x06,
	OP_JUMP = 0x0E,
	OP_BRANCH = 0x0D,
	OP_CALL_FUNCTION = 0x08,
	OP_CALL_METHOD = 0x07,
	OP_PRINT = 0x02,
	OP_DROP = 0x00,
	OP_RETURN = 0x0F,
} OpCode;

typedef struct {
	int length;
	int pop;
	int push;
} OpDesc;

static OpDesc op_desc[] = {
	[OP_CONSTANT]      = { 3,  0, 1 },
	[OP_ARRAY]         = { 1,  2, 1 },
	[OP_OBJECT]        = { 3, -1, 1 },
	[OP_GET_LOCAL]     = { 3,  0, 1 },
	[OP_SET_LOCAL]     = { 3,  1, 1 },
	[OP_GET_GLOBAL]    = { 3,  0, 1 },
	[OP_SET_GLOBAL]    = { 3,  1, 1 },
	[OP_GET_FIELD]     = { 3,  1, 1 },
	[OP_SET_FIELD]     = { 3,  2, 1 },
	[OP_JUMP]          = { 3,  0, 0 },
	[OP_BRANCH]        = { 3,  1, 0 },
	[OP_CALL_FUNCTION] = { 2, -1, 1 },
	[OP_CALL_METHOD]   = { 4, -1, 1 },
	[OP_PRINT]         = { 4, -1, 1 },
	[OP_DROP]          = { 1,  1, 0 },
	[OP_RETURN]        = { 1,  1, 1 },
};

typedef struct {
	OpCode op;
	union {
		u32 jump_dest;
		struct { u16 index; u8 arg_cnt; };
	};
} Instruction;

typedef struct {
	u16 local_cnt;
	u8 parameter_cnt;
	u8 *instruction_start;
	size_t instruction_len;
	size_t max_ostack_height;
} CFunction;

typedef struct {
	// Can't be u16 * due to alignment problems
	u8 *members;
	u16 member_cnt;
} Class;

typedef struct {
	ConstantKind kind;
	union {
		bool boolean;
		i32 integer;
		Str string;
		CFunction function;
		Class class;
	};
} Constant;

typedef struct {
	Constant *constants;
	size_t constant_cnt;
	Class global_class;
	u16 entry_point;
} Program;

static void printf_attr(2)
bc_error(ErrorContext *ec, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	verror(ec, NULL, "bytecode", true, msg, ap);
	va_end(ap);
}

typedef struct {
	ErrorContext *ec;
	Arena *arena;
	Program *program;
} VerificationState;

static void
verify_constant_kind(VerificationState *vs, u16 constant_index, ConstantKind expected_kind)
{
	if (constant_index >= vs->program->constant_cnt) {
		bc_error(vs->ec, "Constant index %"PRIu16" out of bounds, have only %zu constants", constant_index, vs->program->constant_cnt);
	}
	u16 actual_kind = vs->program->constants[constant_index].kind;
	if (vs->program->constants[constant_index].kind != expected_kind) {
		bc_error(vs->ec, "Expected constant '%"PRIu16"' to be %d, but it is %d", constant_index, expected_kind, actual_kind);
	}
}

static int
cmp_u32(const void *a_, const void *b_)
{
	const u32 *a = a_;
	const u32 *b = b_;
	return (*a > *b) - (*b > *a);
}

static void
update_height(VerificationState *vs, CFunction *function, u8 *height, u8 pop, u8 push)
{
	if (pop > *height) {
		bc_error(vs->ec, "Operand stack underflow detected");
	}
	*height -= pop;
	if (push > (UINT8_MAX - 1) - *height) {
		bc_error(vs->ec, "Operand stack overflow detected (only %d elements supported per function call)", UINT8_MAX - 1);
	}
	*height += push;
	if (*height > function->max_ostack_height) {
		function->max_ostack_height = *height;
	}
}

static void
verify_function(VerificationState *vs, CFunction *function)
{
	size_t arena_pos = arena_save(vs->arena);
	Program *program = vs->program;
	size_t local_cnt = function->parameter_cnt + function->local_cnt;
	size_t instruction_len = function->instruction_len;
	u8 *start = function->instruction_start;
	u8 *end = start + instruction_len;

	Instruction *insts = arena_alloc(vs->arena, instruction_len * sizeof(insts[0]));
	u32 *instruction_starts = arena_alloc(vs->arena, (instruction_len + 1) * sizeof(instruction_starts[0]));

	bool seen_return = false;

	// Pass 1: Calculate the number of instructions as well as their
	// positions in the bytecode. Also verify some immediate arguments to
	// constants - i.e. that indices into local frame and correct kinds of
	// constants are used. Jump offsets will be verified later.
	size_t instruction_cnt = 0;
	for (u8 *ip = start; ip < end; instruction_cnt++) {
		Instruction *inst = &insts[instruction_cnt];
		instruction_starts[instruction_cnt] = ip - start;
		switch (inst->op = read_u8(&ip)) {
		case OP_CONSTANT: {
			inst->index = read_u16(&ip);
			Constant *constant = &program->constants[inst->index];
			switch (constant->kind) {
			case CK_NULL:
			case CK_BOOLEAN:
			case CK_INTEGER:
			case CK_FUNCTION:
				break;
			default:
				bc_error(vs->ec, "Expected constant '%"PRIu16"' (an argument to the constant instruction) to be null, boolean, integer or function, but it is %d", inst->index, constant->kind);
			}
			break;
		}
		case OP_ARRAY:
			break;
		case OP_OBJECT: {
			inst->index = read_u16(&ip);
			verify_constant_kind(vs, inst->index, CK_CLASS);
			break;
		}
		case OP_GET_LOCAL:
		case OP_SET_LOCAL: {
			inst->index = read_u16(&ip);
			if (inst->index >= local_cnt) {
				bc_error(vs->ec, "Local index '%"PRIu16"' out of bounds (function has %zu locals)", inst->index, local_cnt);
			}
			break;
		}
		case OP_GET_GLOBAL:
		case OP_SET_GLOBAL: {
			inst->index = read_u16(&ip);
			verify_constant_kind(vs, inst->index, CK_STRING);
			Str name = program->constants[inst->index].string;
			u8 *globals = program->global_class.members;
			size_t global_cnt = program->global_class.member_cnt;
			for (size_t i = 0; i < global_cnt; i++) {
				u16 global_name_index = read_u16(&globals);
				Str global_name = program->constants[global_name_index].string;
				if (str_eq(name, global_name)) {
					goto found;
				}
			}
			bc_error(vs->ec, "Set/get of a global which is not in globals: '%.*s'", (int) name.len, name.str);
			found:
			break;
		}
		case OP_GET_FIELD:
		case OP_SET_FIELD: {
			inst->index = read_u16(&ip);
			verify_constant_kind(vs, inst->index, CK_STRING);
			break;
		}
		case OP_JUMP:
		case OP_BRANCH: {
			i16 offset = (i16) read_u16(&ip);
			inst->jump_dest = (ip - start) + offset;
			// rough check for _really_ out of bounds
			if (ip + offset >= end) {
				bc_error(vs->ec, "Jump out of bounds (destination '%zu', bytecode length '%zu')", (size_t) inst->jump_dest, instruction_len);
			}
			break;
		}
		case OP_CALL_FUNCTION: {
			inst->arg_cnt = read_u8(&ip);
			break;
		}
		case OP_CALL_METHOD: {
			inst->index = read_u16(&ip);
			inst->arg_cnt = read_u8(&ip);
			verify_constant_kind(vs, inst->index, CK_STRING);
			break;
		}
		case OP_PRINT: {
			inst->index = read_u16(&ip);
			inst->arg_cnt = read_u8(&ip);
			verify_constant_kind(vs, inst->index, CK_STRING);

			Str format = program->constants[inst->index].string;
			size_t placeholder_cnt = 0;
			for (size_t i = 0; i < format.len; i++) {
				switch (format.str[i]) {
				case '\\': i++; continue;
				case '~': placeholder_cnt += 1;
				}
			}
			if (placeholder_cnt != inst->arg_cnt) {
				bc_error(vs->ec, "Invalid number of print arguments: %zu expected, got %zu", placeholder_cnt, (size_t) inst->arg_cnt);
			}
			break;
		}
		case OP_DROP:
			break;
		case OP_RETURN:
			seen_return = true;
			break;
		default: {
			bc_error(vs->ec, "Unknown opcode 0x%02zx", (size_t) ip[-1]);
		}
		}
	}
	instruction_starts[instruction_cnt] = instruction_len;

	// Check that the bytecode ends with unconditional control flow change.
	// Otherwise we could get out of bounds while interpreting the bytecode.
	switch (insts[instruction_cnt - 1].op) {
	case OP_JUMP:
	case OP_RETURN:
		break;
	default:
		bc_error(vs->ec, "Bytecode doesn't end with return or jump");
	}


	if (!seen_return) {
		bc_error(vs->ec, "Bytecode doesn't have any OP_RETURN");
	}

	size_t instruction_cnt_max = UINT16_MAX;
	if (instruction_cnt > instruction_cnt_max) {
		bc_error(vs->ec, "Validator currently supports only %zu instructions, but have %zu", instruction_cnt_max, instruction_cnt);
	}


	// Pass 2: Update jump destinations and collect all basic block starts.
	GArena gblock_starts;
	garena_init(&gblock_starts);
	// first basic block starts at instruction 0
	garena_push_value(&gblock_starts, u32, 0);
	for (size_t i = 0; i < instruction_cnt; i++) {
		Instruction *inst = &insts[i];
		switch (insts[i].op) {
		case OP_JUMP:
		case OP_BRANCH: {
			u32 dest = inst->jump_dest;
			u32 pos = 0;
			// we have a sentinal at:
			//     instruction_starts[instruction_cnt]
			// and also already guaranteed that all jump destinations
			// do not go beyond that sentinel
			while (instruction_starts[pos] < dest) {
				pos++;
			}
			if (instruction_starts[pos] != dest) {
				bc_error(vs->ec, "Jump destination is not a start of instruction (destination '%zu', instruction at '%zu')", (size_t) dest, (size_t) instruction_starts[pos]);
			}
			// write absolute destination in instruction counts
			inst->jump_dest = pos;
			// the jump destination starts a new basic block
			garena_push_value(&gblock_starts, u32, pos);
			// since this instruction is a jump/branch then the next
			// instruction (if any) starts a new basic block
			if (i < instruction_cnt - 1) {
				garena_push_value(&gblock_starts, u32, i + 1);
			}
			break;
		case OP_RETURN:
			// the next instruction (if any) starts a new basic
			// block
			if (i < instruction_cnt - 1) {
				garena_push_value(&gblock_starts, u32, i + 1);
			}
			break;
		default:
			break;
		}
		}
	}
	// a dummy "one past end" instruction start
	garena_push_value(&gblock_starts, u32, instruction_cnt);

	// Deduplicate and sort block starts.
	u32 *block_starts = garena_array(&gblock_starts, u32);
	size_t block_start_cnt = garena_cnt(&gblock_starts, u32);
	qsort(block_starts, block_start_cnt, sizeof(u32), cmp_u32);
	u32 *read = block_starts;
	u32 *write = block_starts;
	while (read < block_starts + block_start_cnt) {
		if (*read != *write) {
			write += 1;
			*write = *read;
		}
		read += 1;
	}
	size_t block_cnt = write - block_starts;

	// Construct Control Flow Graph as an array of edges.
	typedef struct { u32 from; u32 to; } Edge;
	u8 *prev_stack_heights_out = arena_alloc(vs->arena, block_cnt * sizeof(prev_stack_heights_out[0]));
	u8 *stack_heights_out = arena_alloc(vs->arena, block_cnt * sizeof(stack_heights_out[0]));
	GArena gcfg;
	garena_init(&gcfg);
	for (size_t i = 0; i < block_cnt; i++) {
		prev_stack_heights_out[i] = UINT8_MAX;
		stack_heights_out[i] = 0;
		Instruction *inst = &insts[block_starts[i + 1] - 1];
		switch (inst->op) {
		case OP_JUMP:
		case OP_BRANCH: {
			u32 dest = inst->jump_dest;
			size_t pos = 0;
			while (block_starts[pos] < dest) {
				pos++;
			}
			garena_push_value(&gcfg, Edge, ((Edge) { .from = i, .to = pos }));
			break;
		default:
			break;
		}
		}
		if (inst->op != OP_JUMP) {
			garena_push_value(&gcfg, Edge, ((Edge) { .from = i, .to = i + 1 }));
		}
	}
	Edge *edges = garena_array(&gcfg, Edge);
	size_t edge_cnt = garena_cnt(&gcfg, Edge);

	// Check that for each instruction the operand stack height is the same
	// across all possible control flows using iterative data flow analysis.
	//
	// While the current iteration doesn't equal the previous iteration for
	// each basic block start, join the stack heights from all predecessors
	// and simulate stack height for all basic block instructions, checking
	// that we don't underflow or overflow the operand stack (the
	// verification supports only operand stack heights up to 254 for each
	// call frame).
	//
	// `UINT8_MAX` is our bottom (i.e. we don't know anything),
	// while other values represent concrete stack heights. If we find
	// concrete but different stack heights among predecessors, we can fail
	// immediately.
	//
	// We only actually start simulating a block if any predecessor has
	// concrete stack height. Since we also don't iterate over the blocks in
	// sensible order (i.e. reverse preorder) and don't use any worklist
	// this is necessarily very inefficient. At least we use basic blocks.
	function->max_ostack_height = 0;
	while (memcmp(prev_stack_heights_out, stack_heights_out, block_cnt * sizeof(stack_heights_out[0])) != 0) {
		for (size_t b = 0; b < block_cnt; b++) {
			// The entry block has initial stack height of 0. This
			// is how we get going.
			u8 height_in = b == 0 ? 0 : UINT8_MAX;
			// We don't store incomign stack height for each block,
			// instead we get it by joining stack heights from
			// predecessors on each iteration.
			for (size_t e = 0; e < edge_cnt; e++) {
				if (edges[e].to != b) {
					continue;
				}
				u8 out = prev_stack_heights_out[edges[e].from];
				if (out == UINT8_MAX) {
					continue;
				} else if (height_in == UINT8_MAX) {
					height_in = out;
				} else if (out != height_in) {
					bc_error(vs->ec, "Inconsistent stack height (%"PRIu8" vs %"PRIu8")", out, height_in);
				}
			}
			if (height_in == UINT8_MAX) {
				stack_heights_out[b] = UINT8_MAX;
				continue;
			}
			u8 height = height_in;
			size_t block_start = block_starts[b];
			size_t block_end = block_starts[b + 1];
			for (size_t i = block_start; i < block_end; i++) {
				Instruction *inst = &insts[i];
				switch (inst->op) {
				case OP_OBJECT: {
					Constant *constant = &program->constants[inst->index];
					Class *class = &constant->class;
					update_height(vs, function, &height, 1 + class->member_cnt, 1);
					break;
				}
				case OP_CALL_FUNCTION: {
					update_height(vs, function, &height, inst->arg_cnt + 1, 1);
					break;
				}
				case OP_CALL_METHOD:
				case OP_PRINT: {
					update_height(vs, function, &height, inst->arg_cnt, 1);
					break;
				}
				default: {
					OpDesc *desc = &op_desc[inst->op];
					update_height(vs, function, &height, desc->pop, desc->push);
					break;
				}
				}
			}
			stack_heights_out[b] = height;
			// Above analysis ensures that for OP_RETURN there is
			// _at least_ one value on the stack (by conceptually
			// making it pop and push one value and forbidding
			// the stack height to go below 0), but we also check
			// whether the outgoing height is is indeed 1 (i.e.
			// there aren't more values).
			if (insts[block_end - 1].op == OP_RETURN && height != 1) {
				bc_error(vs->ec, "Stack height %zu at OP_RETURN, expected 1", (size_t) height);
			}
		}
		u8 *tmp = stack_heights_out;
		stack_heights_out = prev_stack_heights_out;
		prev_stack_heights_out = tmp;
	}

	// Sanity check, there shouldn't be a bottom by now.
	for (size_t i = 0; i < block_cnt; i++) {
		assert(stack_heights_out[i] != UINT8_MAX);
	}

	garena_destroy(&gblock_starts);
	garena_destroy(&gcfg);
	arena_restore(vs->arena, arena_pos);
}

static void
verify_class(VerificationState *vs, Class *class)
{
	u8 *members = class->members;
	for (size_t i = 0; i < class->member_cnt; i++) {
		u16 member_name_index = read_u16(&members);
		verify_constant_kind(vs, member_name_index, CK_STRING);
	}
}

static void
verify_program(ErrorContext *ec, Arena *arena, Program *program)
{
	VerificationState vs_ = {
		.ec = ec,
		.arena = arena,
		.program = program,
	};
	VerificationState *vs = &vs_;
	verify_class(vs, &program->global_class);
	verify_constant_kind(vs, program->entry_point, CK_FUNCTION);
	for (u16 i = 0; i < program->constant_cnt; i++) {
		Constant *constant = &program->constants[i];
		switch (constant->kind) {
		case CK_NULL:
		case CK_BOOLEAN:
		case CK_INTEGER:
		case CK_STRING:
			break;
		case CK_FUNCTION:
			verify_function(vs, &constant->function);
			break;
		case CK_CLASS:
			verify_class(vs, &constant->class);
			break;
		}
	}
}


static void
read_class(u8 **input, Class *class)
{
	class->member_cnt = read_u16(input);
	class->members = *input;
	for (size_t i = 0; i < class->member_cnt; i++) {
		read_u16(input);
	}
}

static bool
constant_eq(Constant *a, Constant *b)
{
	if (a->kind != b->kind) {
		return false;
	}
	switch (a->kind) {
	case CK_NULL:
		return true;
	case CK_BOOLEAN:
		return a->boolean == b->boolean;
	case CK_INTEGER:
		return a->integer == b->integer;
	case CK_STRING:
		return str_eq(a->string, b->string);
	case CK_FUNCTION:
		return false;
	case CK_CLASS:
		return false;
	}
	return false;
}

static void
read_constant(ErrorContext *ec, u8 **input, Constant *constant)
{
	ConstantKind kind = read_u8(input);
	constant->kind = kind;
	switch (kind) {
	case CK_NULL:
		break;
	case CK_BOOLEAN: {
		u8 b = read_u8(input);
		if (b > 1) {
			bc_error(ec, "Boolean is %d not 0 or 1", (int) b);
		}
		constant->boolean = b == 1;
		break;
	}
	case CK_INTEGER:
		constant->integer = (i32) read_u32(input);
		break;
	case CK_STRING:
		constant->string.len = read_u32(input);
		constant->string.str = *input;
		*input += constant->string.len;
		break;
	case CK_FUNCTION:
		constant->function = (CFunction) {0};
		constant->function.parameter_cnt = read_u8(input);
		constant->function.local_cnt = read_u16(input);
		constant->function.instruction_len = read_u32(input);
		constant->function.instruction_start = *input;
		*input += constant->function.instruction_len;
		break;
	case CK_CLASS: {
		read_class(input, &constant->class);
		break;
	}
	default:
		bc_error(ec, "Invalid constant tag '%d'", (int) kind);
	}
}

static bool
read_program(ErrorContext *ec, Arena *arena, Program *program, u8 *input, size_t input_len)
{
	u8 *input_start = input;
	size_t min_len = sizeof(FML_MAGIC) + 6;
	if (input_len < min_len) {
		bc_error(ec, "The bytecode is too small (%zu bytes, need at least %zu)", input_len, min_len);
	}
	if (memcmp(input, FML_MAGIC, sizeof(FML_MAGIC)) != 0) {
		bc_error(ec, "FML bytecode magic header not found");
	}
	input += sizeof(FML_MAGIC);
	program->constant_cnt = read_u16(&input);
	program->constants = arena_alloc(arena, program->constant_cnt * sizeof(program->constants[0]));
	for (size_t i = 0; i < program->constant_cnt; i++) {
		read_constant(ec, &input, &program->constants[i]);
	}
	read_class(&input, &program->global_class);
	program->entry_point = read_u16(&input);
	if (input != input_start + input_len) {
		bc_error(ec, "Trailing bytes left after parsing bytecode");
	}
	return true;
}

typedef struct {
	ErrorContext *ec;
	Arena *arena;
	Heap heap;
	Program *program;
	Value global;
	Value *stack;
	size_t stack_pos;
	size_t stack_len;
	Value *frame_stack;
	size_t frame_stack_pos;
	size_t frame_stack_len;
	size_t bp;
} VM;


static Value
make_null_vm(VM *vm)
{
	(void) vm;
	return make_null(&vm->heap);
}

static Value
vm_peek(VM *vm)
{
	// beware of the unintuitive check below due to unsigned integer
	// wrap around
	assert(vm->stack_pos < vm->stack_len);
	return vm->stack[vm->stack_pos];
}

static Value *
vm_peek_n(VM *vm, size_t n)
{
	size_t pos = vm->stack_pos - (n - 1);
	assert(pos < vm->stack_len);
	return &vm->stack[pos];
}

static Value
vm_pop(VM *vm)
{
	assert(vm->stack_pos < vm->stack_len);
	return vm->stack[vm->stack_pos--];
}


static void
vm_pop_n(VM *vm, size_t n)
{
	assert(vm->stack_pos - (n - 1) < vm->stack_len);
	vm->stack_pos -= n;
}

static void
vm_push(VM *vm, Value value)
{
	if (vm->stack_pos == vm->stack_len) {
		exec_error(vm->ec, "Operand stack space exhausted");
	}
	vm->stack[++vm->stack_pos] = value;
}

static Str
constant_string(VM *vm, u8 **ip)
{
	u16 constant_index = read_u16(ip);
	Constant *constant = &vm->program->constants[constant_index];
	assert(constant->kind == CK_STRING);
	return constant->string;
}

static Value
vm_instantiate_class(VM *vm, Class *class, Value (*make_value)(VM *vm))
{
	Value object_value = make_object(&vm->heap, class->member_cnt);
	Object *object = value_as_object(object_value);
	Constant *constants = vm->program->constants;

	u16 *members = (u16 *) class->members;
	for (size_t i = class->member_cnt; i--;) {
		u8 *member_name_pos = (u8 *) &members[i];
		u16 member_name = read_u16(&member_name_pos);
		Constant *name = &constants[member_name];
		assert(name->kind == CK_STRING);
		object->fields[i].name = name->string;
		object->fields[i].value = make_value(vm);
	}
	object->parent = make_value(vm);
	return object_value;
}

static void
vm_call_method(VM *vm, u16 function_index, u8 argument_cnt)
{
	Constant *function_constant = &vm->program->constants[function_index];
	assert(function_constant->kind == CK_FUNCTION);
	CFunction *function = &function_constant->function;
	if (argument_cnt != function->parameter_cnt) {
		exec_error(vm->ec, "Wrong number of arguments: %zu expected, got %zu", (size_t) function->parameter_cnt, (size_t) argument_cnt);
	}

	size_t local_cnt = argument_cnt + function->local_cnt;
	size_t saved_bp = vm->bp;
	vm->bp = vm->frame_stack_pos;
	vm->frame_stack_pos += local_cnt;

	if (vm->frame_stack_pos > vm->frame_stack_len) {
		exec_error(vm->ec, "Frame stack space exhausted, too much recursion?");
	}

	Value *arguments = vm_peek_n(vm, argument_cnt);
	vm_pop_n(vm, argument_cnt);
	Value *locals = &vm->frame_stack[vm->bp];
	for (size_t i = 0; i < argument_cnt; i++) {
		locals[i] = arguments[i];
	}
	for (size_t i = argument_cnt; i < local_cnt; i++) {
		locals[i] = make_null(&vm->heap);
	}

	for (u8 *ip = function->instruction_start;;) {
		switch (read_u8(&ip)) {
		case OP_CONSTANT: {
			u16 constant_index = read_u16(&ip);
			Constant *constant = &vm->program->constants[constant_index];
			Value value;
			switch (constant->kind) {
			case CK_NULL:
				value = make_null(&vm->heap);
				break;
			case CK_BOOLEAN:
				value = make_boolean(&vm->heap, constant->boolean);
				break;
			case CK_INTEGER:
				value = make_integer(&vm->heap, constant->integer);
				break;
			case CK_FUNCTION:
				value = make_function_bc(&vm->heap, constant_index);
				break;
			default:
				assert(false);
			}
			vm_push(vm, value);
			break;
		}
		case OP_ARRAY: {
			Value initializer = vm_pop(vm);
			Value size_value = vm_pop(vm);
			size_t size = value_as_size(vm->ec, size_value);
			Value array_value = make_array(&vm->heap, size);
			Array *array = value_as_array(array_value);
			for (size_t i = 0; i < size; i++) {
				array->values[i] = initializer;
			}
			vm_push(vm, array_value);
			break;
		}
		case OP_OBJECT: {
			u16 constant_index = read_u16(&ip);
			Constant *constant = &vm->program->constants[constant_index];
			assert(constant->kind == CK_CLASS);
			Value object = vm_instantiate_class(vm, &constant->class, vm_pop);
			vm_push(vm, object);
			break;
		}
		case OP_GET_LOCAL: {
			u16 local_index = read_u16(&ip);
			vm_push(vm, locals[local_index]);
			break;
		}
		case OP_SET_LOCAL: {
			u16 local_index = read_u16(&ip);
			locals[local_index] = vm_peek(vm);
			break;
		}
		case OP_GET_GLOBAL: {
			Str name = constant_string(vm, &ip);
			Value *lvalue = value_field(vm->ec, vm->global, &vm->global, name);
			vm_push(vm, *lvalue);
			break;
		}
		case OP_SET_GLOBAL: {
			Str name = constant_string(vm, &ip);
			Value *lvalue = value_field(vm->ec, vm->global, &vm->global, name);
			*lvalue = vm_peek(vm);
			break;
		}
		case OP_GET_FIELD: {
			Str name = constant_string(vm, &ip);
			Value object = vm_pop(vm);
			Value *lvalue = value_field(vm->ec, object, &object, name);
			vm_push(vm, *lvalue);
			break;
		}
		case OP_SET_FIELD: {
			Str name = constant_string(vm, &ip);
			Value value = vm_pop(vm);
			Value object = vm_pop(vm);
			Value *lvalue = value_field(vm->ec, object, &object, name);
			*lvalue = value;
			vm_push(vm, value);
			break;
		}
		case OP_JUMP: {
			i16 offset = (i16) read_u16(&ip);
			ip += offset;
			break;
		}
		case OP_BRANCH: {
			i16 offset = (i16) read_u16(&ip);
			Value condition = vm_pop(vm);
			if (value_to_bool(condition)) {
				ip += offset;
			}
			break;
		}
		case OP_CALL_FUNCTION: {
			u8 argument_cnt = read_u8(&ip);
			Value *function = vm_peek_n(vm, argument_cnt + 1);
			if (!value_is_function(*function)) {
				exec_error(vm->ec, "Function call target is not a function");
			}
			u16 function_index = value_as_function_bc(*function);
			// Receiver (this) is null for functions
			*function = make_null(&vm->heap);
			vm_call_method(vm, function_index, argument_cnt + 1);
			break;
		}
		case OP_CALL_METHOD: {
			Str name = constant_string(vm, &ip);
			u8 argument_cnt = read_u8(&ip);
			Value *lobject = vm_peek_n(vm, argument_cnt);
			Value *function_value = value_method_try(vm->ec, *lobject, lobject, name);
			if (function_value) {
				u16 function_index = value_as_function_bc(*function_value);
				vm_call_method(vm, function_index, argument_cnt);
			} else {
				Value *arguments = vm_peek_n(vm, argument_cnt - 1);
				Value return_value = value_call_primitive_method(vm->ec, &vm->heap, *lobject, name, arguments, argument_cnt - 1);
				vm_pop_n(vm, argument_cnt);
				vm_push(vm, return_value);
			}
			break;
		}
		case OP_PRINT: {
			Str format_string = constant_string(vm, &ip);
			u8 argument_cnt = read_u8(&ip);
			Value *arguments = vm_peek_n(vm, argument_cnt);
			builtin_print(vm->ec, format_string, arguments, argument_cnt);
			vm_pop_n(vm, argument_cnt);
			vm_push(vm, make_null(&vm->heap));
			break;
		}
		case OP_DROP: {
			vm_pop(vm);
			break;
		}
		case OP_RETURN: {
			vm->frame_stack_pos = vm->bp;
			vm->bp = saved_bp;
			return;
		}
		}
	}
}

static void
gc_vm(Heap *heap)
{
	VM *vm = container_of(heap, VM, heap);
	(void) vm;
}

static void
vm_run(ErrorContext *ec, Arena *arena, Program *program, size_t heap_size, FILE *heap_log)
{
	verify_program(ec, arena, program);
	VM *vm = arena_alloc(arena, sizeof(*vm));
	*vm = (VM) {
		.ec = ec,
		.heap = {0},
		.arena = arena,
		.program = program,
		.stack = arena_alloc(arena, 1024 * sizeof(Value)),
		.stack_pos = (size_t) -1,
		.stack_len = 1024,
		.frame_stack = arena_alloc(arena, 1024 * sizeof(Value)),
		.frame_stack_pos = 0,
		.frame_stack_len = 1024,
		.bp = 0,
	};
	heap_init(&vm->heap, ec, gc_vm, heap_size, heap_log);
	vm->global = vm_instantiate_class(vm, &program->global_class, make_null_vm);
	// push `this` as an argument
	vm_push(vm, make_null(&vm->heap));
	vm_call_method(vm, program->entry_point, 1);
	// Check that the program left exactly one value on the stack
	assert(vm->stack_pos == 0);
}

typedef struct {
	ErrorContext *ec;
	Arena *arena;
	GArena constants; // Constant array
	GArena instructions; // u8 array
	GArena globals; // u16 array (but unaligned when serialized)
	bool in_block;
	Environment *env;
	u16 local_cnt;
	bool had_error;
} CompilerState;

static void printf_attr(2)
compile_error(CompilerState *cs, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	cs->had_error = true;
	verror(cs->ec, NULL, "compile", false, msg, ap);
	va_end(ap);
}

static size_t
inst_pos(CompilerState *cs)
{
	return garena_save(&cs->instructions);
}

static void
inst_write_u8(CompilerState *cs, u8 b)
{
	u8 *pos = garena_alloc(&cs->instructions, 1, 1);
	pos[0] = b;
}

static void
inst_write_u16(CompilerState *cs, u16 b)
{
	u8 *pos = garena_alloc(&cs->instructions, 2, 1);
	pos[0] = b >> 0;
	pos[1] = b >> 8;
}

static u16
add_constant(CompilerState *cs, Constant constant)
{
	size_t index = garena_cnt(&cs->constants, Constant);
	for (size_t i = index; i--;) {
		if (constant_eq(&garena_array(&cs->constants, Constant)[i], &constant)) {
			return i;
		}
	}
	garena_push_value(&cs->constants, Constant, constant);
	if (index == 0x10000) {
		compile_error(cs, "Too many constants (only 65536 allowed)");
	}
	return index;
}

static u16
add_string(CompilerState *cs, Str name)
{
	return add_constant(cs, (Constant) {
		.kind = CK_STRING,
		.string = name,
	});
}

static u16
add_global_name_once(CompilerState *cs, Str name)
{
	u16 name_index = add_string(cs, name);
	size_t cnt = garena_cnt(&cs->globals, u16);
	u16 *globals = garena_array(&cs->globals, u16);
	for (size_t i = cnt; i--;) {
		if (globals[i] == name_index) {
			return name_index;
		}
	}
	garena_push_value(&cs->globals, u16, name_index);
	return name_index;
}

static void
inst_constant(CompilerState *cs, Constant constant)
{
	inst_write_u16(cs, add_constant(cs, constant));
}

static void
inst_string(CompilerState *cs, Str name)
{
	inst_write_u16(cs, add_string(cs, name));
}

static void
literal(CompilerState *cs, Constant constant)
{
	inst_write_u8(cs, OP_CONSTANT);
	inst_constant(cs, constant);
}

static u16
add_function(CompilerState *cs, size_t start, u16 parameter_cnt)
{
	parameter_cnt += 1; // for 'this'
	size_t instruction_len = garena_cnt_from(&cs->instructions, start, u8);
	u8 *instruction_start = move_to_arena(cs->arena, &cs->instructions, start, u8);
	return add_constant(cs, (Constant) {
		.kind = CK_FUNCTION,
		.function = (CFunction) {
			.local_cnt = cs->local_cnt - parameter_cnt,
			.parameter_cnt = parameter_cnt,
			.instruction_start = instruction_start,
			.instruction_len = instruction_len,
		},
	});
}

static void
op(CompilerState *cs, OpCode op)
{
	inst_write_u8(cs, op);
}

static void
op_index(CompilerState *cs, OpCode op, u16 index)
{
	inst_write_u8(cs, op);
	inst_write_u16(cs, index);
}

static void
op_string(CompilerState *cs, OpCode op, Str string)
{
	inst_write_u8(cs, op);
	inst_string(cs, string);
}

static void
op_string_cnt(CompilerState *cs, OpCode op, Str string, u8 count)
{
	inst_write_u8(cs, op);
	inst_string(cs, string);
	inst_write_u8(cs, count);
}

static void
jump(CompilerState *cs, OpCode op, size_t *pos)
{
	inst_write_u8(cs, op);
	*pos = inst_pos(cs);
	inst_write_u16(cs, 0x0000);
}

static void
jump_fixup(CompilerState *cs, size_t pos, size_t target)
{
	int diff = target - (pos + 2);
	if (diff > INT16_MAX || diff < INT16_MIN) {
		compile_error(cs, "Jump offset too large (%d, allowed %d to %d)", diff, INT16_MIN, INT16_MAX);
	}
	u16 offset = (i16) diff;
	u8 *dest = garena_mem(&cs->instructions);
	dest[pos + 0] = offset >> 0;
	dest[pos + 1] = offset >> 8;
}

static void
jump_to(CompilerState *cs, OpCode op, size_t target)
{
	size_t pos;
	jump(cs, op, &pos);
	jump_fixup(cs, pos, target);
}

static u16
define_local(CompilerState *cs, Str name)
{
	env_define(cs->env, name, make_integer(NULL, cs->local_cnt));
	return cs->local_cnt++;
}

static bool
lookup_local(CompilerState *cs, Str name, u16 *index)
{
	Value *local_index = env_lookup_raw(cs->env, name);
	if (local_index) {
		*index = (u16) value_as_integer(*local_index);
		return true;
	}
	return false;
}

static void
compile(CompilerState *cs, Ast *ast)
{
	switch (ast->kind) {
	case AST_NULL: {
		literal(cs, (Constant) { .kind = CK_NULL });
		return;
	}
	case AST_BOOLEAN: {
		AstBoolean *boolean = (AstBoolean *) ast;
		literal(cs, (Constant) {
			.kind = CK_BOOLEAN,
			.boolean = boolean->value,
		});
		return;
	}
	case AST_INTEGER: {
		AstInteger *integer = (AstInteger *) ast;
		literal(cs, (Constant) {
			.kind = CK_INTEGER,
			.integer = integer->value,
		});
		return;
	}
	case AST_ARRAY: {
		AstArray *array = (AstArray *) ast;

		// Try low hanging fruit "simple initializers" that can't change
		switch (array->initializer->kind) {
		case AST_NULL:
		case AST_BOOLEAN:
		case AST_INTEGER:
		case AST_VARIABLE_ACCESS:
			compile(cs, array->size);
			compile(cs, array->initializer);
			op(cs, OP_ARRAY);
			return;
		default:;
		}

		u16 size_var = cs->local_cnt++;
		u16 i_var = cs->local_cnt++;
		u16 array_var = cs->local_cnt++;

		literal(cs, (Constant) { .kind = CK_INTEGER, .integer = 0 });
		op_index(cs, OP_SET_LOCAL, i_var);
		op(cs, OP_DROP);

		compile(cs, array->size);
		op_index(cs, OP_SET_LOCAL, size_var);
		// Dummy initializer
		literal(cs, (Constant) { .kind = CK_NULL });
		op(cs, OP_ARRAY);
		op_index(cs, OP_SET_LOCAL, array_var);

		size_t condition_to_init;
		size_t condition_to_after;

		size_t condition = inst_pos(cs);
		op_index(cs, OP_GET_LOCAL, i_var);
		op_index(cs, OP_GET_LOCAL, size_var);
		op_string_cnt(cs, OP_CALL_METHOD, STR("<"), 2);
		jump(cs, OP_BRANCH, &condition_to_init);
		jump(cs, OP_JUMP, &condition_to_after);
		size_t init = inst_pos(cs);
		op_index(cs, OP_GET_LOCAL, i_var);
		bool saved_in_block = cs->in_block;
		cs->in_block = true;
		env_push(&cs->env);
		compile(cs, array->initializer);
		cs->in_block = saved_in_block;
		env_pop(&cs->env);
		op_string_cnt(cs, OP_CALL_METHOD, STR("set"), 3);
		op(cs, OP_DROP);
		op_index(cs, OP_GET_LOCAL, i_var);
		literal(cs, (Constant) { .kind = CK_INTEGER, .integer = 1 });
		op_string_cnt(cs, OP_CALL_METHOD, STR("+"), 2);
		op_index(cs, OP_SET_LOCAL, i_var);
		op(cs, OP_DROP);
		op_index(cs, OP_GET_LOCAL, array_var);
		jump_to(cs, OP_JUMP, condition);

		jump_fixup(cs, condition_to_init, init);
		jump_fixup(cs, condition_to_after, inst_pos(cs));
		return;
	}
	case AST_OBJECT: {
		AstObject *object = (AstObject *) ast;
		compile(cs, object->extends);
		bool saved_in_block = cs->in_block;

		// each individual definition value is compiled in it's own local
		// scope
		cs->in_block = true;
		u16 *members = arena_alloc(cs->arena, object->member_cnt * sizeof(*members));
		for (size_t i = 0; i < object->member_cnt; i++) {
			assert(object->members[i]->kind == AST_DEFINITION);
			AstDefinition *definition = (AstDefinition *) object->members[i];
			members[i] = add_string(cs, definition->name);
			env_push(&cs->env);
			compile(cs, definition->value);
			env_pop(&cs->env);
		}
		// NOTE: due to losing alignment when serializing, we refer to
		// members with `u8` pointers while compiling them as if they
		// were u16
		u16 class_index = add_constant(cs, (Constant) {
			.kind = CK_CLASS,
			.class = (Class) {
				.member_cnt = object->member_cnt,
				.members = (u8 *) members,
			},
		});
		op_index(cs, OP_OBJECT, class_index);

		cs->in_block = saved_in_block;
		return;
	}
	case AST_FUNCTION: {
		AstFunction *function = (AstFunction *) ast;
		Environment *saved_environment = cs->env;
		u16 saved_local_cnt = cs->local_cnt;
		size_t start = garena_save(&cs->instructions);
		bool saved_in_block = cs->in_block;

		cs->local_cnt = 0;
		cs->in_block = true;

		// Start with empty environment
		cs->env = NULL;
		env_push(&cs->env);
		define_local(cs, STR("this"));
		for (size_t i = 0; i < function->parameter_cnt; i++) {
			define_local(cs, function->parameters[i]);
		}
		compile(cs, function->body);
		op(cs, OP_RETURN);
		env_pop(&cs->env);

		u16 function_constant = add_function(cs, start, function->parameter_cnt);
		op_index(cs, OP_CONSTANT, function_constant);
		cs->env = saved_environment;
		cs->local_cnt = saved_local_cnt;
		cs->in_block = saved_in_block;
		return;
	}

	case AST_DEFINITION: {
		AstDefinition *definition = (AstDefinition *) ast;
		compile(cs, definition->value);
		if (cs->in_block) {
			u16 local = define_local(cs, definition->name);
			op_index(cs, OP_SET_LOCAL, local);
		} else {
			u16 global = add_global_name_once(cs, definition->name);
			op_index(cs, OP_SET_GLOBAL, global);
		}
		return;
	}

	case AST_VARIABLE_ACCESS: {
		AstVariableAccess *variable_access = (AstVariableAccess *) ast;
		u16 local;
		if (lookup_local(cs, variable_access->name, &local)) {
			op_index(cs, OP_GET_LOCAL, local);
		} else {
			u16 global = add_global_name_once(cs, variable_access->name);
			op_index(cs, OP_GET_GLOBAL, global);
		}
		return;
	}
	case AST_VARIABLE_ASSIGNMENT: {
		AstVariableAssignment *variable_assignment = (AstVariableAssignment *) ast;
		compile(cs, variable_assignment->value);
		u16 local;
		if (lookup_local(cs, variable_assignment->name, &local)) {
			op_index(cs, OP_SET_LOCAL, local);
		} else {
			u16 global = add_global_name_once(cs, variable_assignment->name);
			op_index(cs, OP_SET_GLOBAL, global);
		}
		return;
	}

	case AST_INDEX_ACCESS: {
		AstIndexAccess *index_access = (AstIndexAccess *) ast;
		compile(cs, index_access->object);
		compile(cs, index_access->index);
		op_string_cnt(cs, OP_CALL_METHOD, STR("get"), 2);
		return;
	}
	case AST_INDEX_ASSIGNMENT: {
		AstIndexAssignment *index_assignment = (AstIndexAssignment *) ast;
		compile(cs, index_assignment->object);
		compile(cs, index_assignment->index);
		compile(cs, index_assignment->value);
		op_string_cnt(cs, OP_CALL_METHOD, STR("set"), 3);
		return;
	}

	case AST_FIELD_ACCESS: {
		AstFieldAccess *field_access = (AstFieldAccess *) ast;
		compile(cs, field_access->object);
		op_string(cs, OP_GET_FIELD, field_access->field);
		return;
	}
	case AST_FIELD_ASSIGNMENT: {
		AstFieldAssignment *field_assignment = (AstFieldAssignment *) ast;
		compile(cs, field_assignment->object);
		compile(cs, field_assignment->value);
		op_string(cs, OP_SET_FIELD, field_assignment->field);
		return;
	}

	case AST_FUNCTION_CALL: {
		AstFunctionCall *function_call = (AstFunctionCall *) ast;
		compile(cs, function_call->function);
		for (size_t i = 0; i < function_call->argument_cnt; i++) {
			compile(cs, function_call->arguments[i]);
		}
		op(cs, OP_CALL_FUNCTION);
		inst_write_u8(cs, function_call->argument_cnt);
		return;
	}
	case AST_METHOD_CALL: {
		AstMethodCall *method_call = (AstMethodCall *) ast;
		compile(cs, method_call->object);
		for (size_t i = 0; i < method_call->argument_cnt; i++) {
			compile(cs, method_call->arguments[i]);
		}
		op_string_cnt(cs, OP_CALL_METHOD, method_call->name, method_call->argument_cnt + 1);
		return;
	}

	case AST_CONDITIONAL: {
		AstConditional *conditional = (AstConditional *) ast;
		size_t cond_to_consequent;
		size_t cond_to_alternative;
		size_t consequent_to_after;

		compile(cs, conditional->condition);
		jump(cs, OP_BRANCH, &cond_to_consequent);
		jump(cs, OP_JUMP, &cond_to_alternative);
		size_t consequent = inst_pos(cs);
		{
			env_push(&cs->env);
			bool saved_in_block = cs->in_block;
			cs->in_block = true;
			compile(cs, conditional->consequent);
			cs->in_block = saved_in_block;
			env_pop(&cs->env);
		}
		jump(cs, OP_JUMP, &consequent_to_after);
		size_t alternative = inst_pos(cs);
		{
			env_push(&cs->env);
			bool saved_in_block = cs->in_block;
			cs->in_block = true;
			compile(cs, conditional->alternative);
			cs->in_block = saved_in_block;
			env_pop(&cs->env);
		}

		jump_fixup(cs, cond_to_consequent, consequent);
		jump_fixup(cs, cond_to_alternative, alternative);
		jump_fixup(cs, consequent_to_after, inst_pos(cs));
		return;
	}
	case AST_LOOP: {
		AstLoop *loop = (AstLoop *) ast;
		size_t condition_to_body;
		size_t condition_to_after;

		literal(cs, (Constant) { .kind = CK_NULL });
		size_t condition = inst_pos(cs);
		compile(cs, loop->condition);
		jump(cs, OP_BRANCH, &condition_to_body);
		jump(cs, OP_JUMP, &condition_to_after);
		size_t body = inst_pos(cs);
		// Drop value from previous iteration (or the initial null)
		op(cs, OP_DROP);
		env_push(&cs->env);
		bool saved_in_block = cs->in_block;
		cs->in_block = true;
		compile(cs, loop->body);
		cs->in_block = saved_in_block;
		env_pop(&cs->env);
		jump_to(cs, OP_JUMP, condition);

		jump_fixup(cs, condition_to_body, body);
		jump_fixup(cs, condition_to_after, inst_pos(cs));
		return;
	}
	case AST_PRINT: {
		AstPrint *print = (AstPrint *) ast;
		for (size_t i = 0; i < print->argument_cnt; i++) {
			compile(cs, print->arguments[i]);
		}
		op_string_cnt(cs, OP_PRINT, print->format, print->argument_cnt);
		return;
	}
	case AST_BLOCK: {
		AstBlock *block = (AstBlock *) ast;
		bool saved_in_block = cs->in_block;
		cs->in_block = true;
		env_push(&cs->env);
		compile(cs, block->expressions[0]);
		for (size_t i = 1; i < block->expression_cnt; i++) {
			op(cs, OP_DROP);
			compile(cs, block->expressions[i]);
		}
		env_pop(&cs->env);
		cs->in_block = saved_in_block;
		return;
	}
	case AST_TOP: {
		AstTop *top = (AstTop *) ast;
		compile(cs, top->expressions[0]);
		for (size_t i = 1; i < top->expression_cnt; i++) {
			op(cs, OP_DROP);
			compile(cs, top->expressions[i]);
		}
		// emit OP_RETURN in outer level (in case there is a AST_NULL
		// instead of AST_TOP as the top level).
		return;
	}
	}
	UNREACHABLE();
}

void
compile_ast(ErrorContext *ec, Arena *arena, Program *program, Ast *ast)
{
	size_t arena_start = arena_save(arena);
	CompilerState cs = {
		.ec = ec,
		.arena = arena,
		.constants = {0},
		.instructions = {0},
		.globals = {0},
		.in_block = false,
		.env = NULL,
		.local_cnt = 0,
	};
	garena_init(&cs.constants);
	garena_init(&cs.instructions);
	garena_init(&cs.globals);

	env_push(&cs.env);
	define_local(&cs, STR("this"));
	compile(&cs, ast);
	env_pop(&cs.env);
	op(&cs, OP_RETURN);

	u16 entry_point = add_function(&cs, 0, 0);

	program->constant_cnt = garena_cnt(&cs.constants, Constant);
	program->constants = move_to_arena(cs.arena, &cs.constants, 0, Constant);

	size_t global_cnt = garena_cnt_from(&cs.globals, 0, u16);
	u16 *globals = move_to_arena(cs.arena, &cs.globals, 0, u16);
	// NOTE: due to losing alignment when serializing, we refer to
	// members with `u8` pointers while compiling them as if they
	// were u16
	program->global_class = (Class) {
		.member_cnt = global_cnt,
		.members = (u8 *) globals,
	};

	program->entry_point = entry_point;

	garena_destroy(&cs.constants);
	garena_destroy(&cs.instructions);
	garena_destroy(&cs.globals);

	verify_program(ec, arena, program);

	if (cs.had_error) {
		arena_restore(arena, arena_start);
		longjmp(cs.ec->loc, 1);
	}
}

static void
write_u32(FILE *f, u32 num)
{
	fputc(num >> 0, f);
	fputc(num >> 8, f);
	fputc(num >> 16, f);
	fputc(num >> 24, f);
}

static void
write_u16(FILE *f, u16 num)
{
	fputc(num >> 0, f);
	fputc(num >> 8, f);
}

static void
write_u8(FILE *f, u8 num)
{
	fputc(num, f);
}

static void
write_class(FILE *f, Class *class)
{
	write_u16(f, class->member_cnt);
	u8 *members = class->members;
	for (size_t i = 0; i < class->member_cnt; i++) {
		u16 member = read_u16(&members);
		write_u16(f, member);
	}
}

static void
write_constant(FILE *f, Constant *constant)
{
	write_u8(f, constant->kind);
	switch (constant->kind) {
	case CK_NULL:
		break;
	case CK_BOOLEAN: {
		write_u8(f, (u8) constant->boolean);
		break;
	}
	case CK_INTEGER:
		write_u32(f, constant->integer);
		break;
	case CK_STRING:
		write_u32(f, constant->string.len);
		fwrite(constant->string.str, constant->string.len, 1, f);
		break;
	case CK_FUNCTION:
		write_u8(f, constant->function.parameter_cnt);
		write_u16(f, constant->function.local_cnt);
		write_u32(f, constant->function.instruction_len);
		fwrite(constant->function.instruction_start, constant->function.instruction_len, 1, f);
		break;
	case CK_CLASS: {
		write_class(f, &constant->class);
		break;
	}
	default:
		UNREACHABLE();
	}
}

void
write_program(Program *program, FILE *f)
{
	fwrite(FML_MAGIC, sizeof(FML_MAGIC), 1, f);
	write_u16(f, program->constant_cnt);
	for (size_t i = 0; i < program->constant_cnt; i++) {
		write_constant(f, &program->constants[i]);
	}
	write_class(f, &program->global_class);
	write_u16(f, program->entry_point);
}

typedef struct {
	FILE *f;
	bool prev;
} OutputState;

const char *ast_kind_repr[] = {
	"AST_NULL",
	"AST_BOOLEAN",
	"AST_INTEGER",
	"AST_ARRAY",
	"AST_OBJECT",
	"AST_FUNCTION",
	"AST_DEFINITION",
	"AST_VARIABLE_ACCESS",
	"AST_VARIABLE_ASSIGNMENT",
	"AST_INDEX_ACCESS",
	"AST_INDEX_ASSIGNMENT",
	"AST_FIELD_ACCESS",
	"AST_FIELD_ASSIGNMENT",
	"AST_FUNCTION_CALL",
	"AST_METHOD_CALL",
	"AST_CONDITIONAL",
	"AST_LOOP",
	"AST_PRINT",
	"AST_BLOCK",
	"AST_TOP",
};

void
write_ast_begin(OutputState *os, char *name, AstKind kind, int indent, bool first)
{
	fprintf(os->f, "%s(Ast%s) {\n", first ? "" : "&", name);
	fprintf(os->f, "%*s.base = (Ast) { .kind = %s },\n", indent, "", ast_kind_repr[kind]);
}
void
write_ast_end(OutputState *os, int indent, bool first)
{
	fprintf(os->f, "%*s}%s\n", indent - 4, "", first ? "" : ".base,");
}
void write_ast_field(OutputState *os, char *name, Ast *value, int indent);
void write_ast_field_string(OutputState *os, char *name, Str string, int indent);
void write_ast_field_boolean(OutputState *os, char *name, bool value, int indent);
void write_ast_field_integer(OutputState *os, char *name, i32 value, int indent);
void write_ast_field_array(OutputState *os, char *name, Ast **values, size_t value_cnt, int indent);
void write_ast_field_string_array(OutputState *os, char *name, Str *values, size_t value_cnt, int indent);

void
write_ast(OutputState *os, Ast *ast, int indent, bool first)
{
	//indent += 4;
	switch (ast->kind) {
	case AST_NULL: {
		//AstNull *null = (AstNull *) ast;
		write_ast_begin(os, "Null", ast->kind, indent, first);
		//fprintf(os->f, "null");
		write_ast_end(os, indent, first);
		return;
	}
	case AST_BOOLEAN: {
		AstBoolean *boolean = (AstBoolean *) ast;
		write_ast_begin(os, "Boolean", ast->kind, indent, first);
		write_ast_field_boolean(os, "value", boolean->value, indent);
		write_ast_end(os, indent, first);
		return;
	}
	case AST_INTEGER: {
		AstInteger *integer = (AstInteger *) ast;
		write_ast_begin(os, "Integer", ast->kind, indent, first);
		write_ast_field_integer(os, "value", integer->value, indent);
		write_ast_end(os, indent, first);
		return;
	}
	case AST_ARRAY: {
		AstArray *array = (AstArray *) ast;
		write_ast_begin(os, "Array", ast->kind, indent, first);
		write_ast_field(os, "size", array->size, indent);
		write_ast_field(os, "initializer", array->initializer, indent);
		write_ast_end(os, indent, first);
		return;
	}
	case AST_OBJECT: {
		AstObject *object = (AstObject *) ast;
		write_ast_begin(os, "Object", ast->kind, indent, first);
		write_ast_field(os, "extends", object->extends, indent);
		write_ast_field_array(os, "member", object->members, object->member_cnt, indent);
		write_ast_end(os, indent, first);
		return;
	}
	case AST_FUNCTION: {
		AstFunction *function = (AstFunction *) ast;
		write_ast_begin(os, "Function", ast->kind, indent, first);
		write_ast_field(os, "body", function->body, indent);
		write_ast_field_string_array(os, "parameter", function->parameters, function->parameter_cnt, indent);
		write_ast_end(os, indent, first);
		return;
	}

	case AST_DEFINITION: {
		AstDefinition *definition = (AstDefinition *) ast;
		write_ast_begin(os, "Definition", ast->kind, indent, first);
		write_ast_field_string(os, "name", definition->name, indent);
		write_ast_field(os, "value", definition->value, indent);
		write_ast_end(os, indent, first);
		return;
	}

	case AST_VARIABLE_ACCESS: {
		AstVariableAccess *variable_access = (AstVariableAccess *) ast;
		write_ast_begin(os, "VariableAccess", ast->kind, indent, first);
		write_ast_field_string(os, "name", variable_access->name, indent);
		write_ast_end(os, indent, first);
		return;
	}
	case AST_VARIABLE_ASSIGNMENT: {
		AstVariableAssignment *variable_assignment = (AstVariableAssignment *) ast;
		write_ast_begin(os, "VariableAssignment", ast->kind, indent, first);
		write_ast_field_string(os, "name", variable_assignment->name, indent);
		write_ast_field(os, "value", variable_assignment->value, indent);
		write_ast_end(os, indent, first);
		return;
	}

	case AST_INDEX_ACCESS: {
		AstIndexAccess *index_access = (AstIndexAccess *) ast;
		write_ast_begin(os, "IndexAccess", ast->kind, indent, first);
		write_ast_field(os, "object", index_access->object, indent);
		write_ast_field(os, "index", index_access->index, indent);
		write_ast_end(os, indent, first);
		return;
	}
	case AST_INDEX_ASSIGNMENT: {
		AstIndexAssignment *index_assignment = (AstIndexAssignment *) ast;
		write_ast_begin(os, "IndexAssignment", ast->kind, indent, first);
		write_ast_field(os, "object", index_assignment->object, indent);
		write_ast_field(os, "index", index_assignment->index, indent);
		write_ast_field(os, "value", index_assignment->value, indent);
		write_ast_end(os, indent, first);
		return;
	}

	case AST_FIELD_ACCESS: {
		AstFieldAccess *field_access = (AstFieldAccess *) ast;
		write_ast_begin(os, "FieldAccess", ast->kind, indent, first);
		write_ast_field(os, "object", field_access->object, indent);
		write_ast_field_string(os, "field", field_access->field, indent);
		write_ast_end(os, indent, first);
		return;
	}
	case AST_FIELD_ASSIGNMENT: {
		AstFieldAssignment *field_assignment = (AstFieldAssignment *) ast;
		write_ast_begin(os, "FieldAssignment", ast->kind, indent, first);
		write_ast_field(os, "object", field_assignment->object, indent);
		write_ast_field_string(os, "field", field_assignment->field, indent);
		write_ast_field(os, "value", field_assignment->value, indent);
		write_ast_end(os, indent, first);
		return;
	}

	case AST_FUNCTION_CALL: {
		AstFunctionCall *function_call = (AstFunctionCall *) ast;
		write_ast_begin(os, "FunctionCall", ast->kind, indent, first);
		write_ast_field(os, "function", function_call->function, indent);
		write_ast_field_array(os, "argument", function_call->arguments, function_call->argument_cnt, indent);
		write_ast_end(os, indent, first);
		return;
	}
	case AST_METHOD_CALL: {
		AstMethodCall *method_call = (AstMethodCall *) ast;
		write_ast_begin(os, "MethodCall", ast->kind, indent, first);
		write_ast_field(os, "object", method_call->object, indent);
		write_ast_field_string(os, "name", method_call->name, indent);
		write_ast_field_array(os, "argument", method_call->arguments, method_call->argument_cnt, indent);
		write_ast_end(os, indent, first);
		return;
	}

	case AST_CONDITIONAL: {
		AstConditional *conditional = (AstConditional *) ast;
		write_ast_begin(os, "Conditional", ast->kind, indent, first);
		write_ast_field(os, "condition", conditional->condition, indent);
		write_ast_field(os, "consequent", conditional->consequent, indent);
		write_ast_field(os, "alternative", conditional->alternative, indent);
		write_ast_end(os, indent, first);
		return;
	}
	case AST_LOOP: {
		AstLoop *loop = (AstLoop *) ast;
		write_ast_begin(os, "Loop", ast->kind, indent, first);
		write_ast_field(os, "condition", loop->condition, indent);
		write_ast_field(os, "body", loop->body, indent);
		write_ast_end(os, indent, first);
		return;
	}
	case AST_PRINT: {
		AstPrint *print = (AstPrint *) ast;
		write_ast_begin(os, "Print", ast->kind, indent, first);
		write_ast_field_string(os, "format", print->format, indent);
		write_ast_field_array(os, "argument", print->arguments, print->argument_cnt, indent);
		write_ast_end(os, indent, first);
		return;
	}
	case AST_BLOCK: {
		write_ast_begin(os, "Block", ast->kind, indent, first);
		AstBlock *block = (AstBlock *) ast;
		write_ast_field_array(os, "expression", block->expressions, block->expression_cnt, indent);
		write_ast_end(os, indent, first);
		return;
	}
	case AST_TOP: {
		write_ast_begin(os, "Top", ast->kind, indent, first);
		AstTop *top = (AstTop *) ast;
		write_ast_field_array(os, "expression", top->expressions, top->expression_cnt, indent);
		write_ast_end(os, indent, first);
		return;
	}
	}
	UNREACHABLE();
}

void
write_ast_key(OutputState *os, char *key, int indent)
{
	fprintf(os->f, "%*s.%s = ", indent, "", key);
}

void
write_ast_keys(OutputState *os, char *key, char *type, int indent)
{
	fprintf(os->f, "%*s.%ss = (%s[]) {", indent, "", key, type);
}

void
write_ast_field(OutputState *os, char *name, Ast *value, int indent)
{
	write_ast_key(os, name, indent);
	write_ast(os, value, indent + 4, false);
}

void
write_ast_string(OutputState *os, Str string)
{
	fprintf(os->f, "STR(\"");
	for (size_t i = 0; i < string.len; i++) {
		u8 c = string.str[i];
		if (c == '\\') {
			fputc(c, os->f);
		}
		fputc(c, os->f);
	}
	fprintf(os->f, "\")");
}

void
write_ast_field_string(OutputState *os, char *name, Str value, int indent)
{
	write_ast_key(os, name, indent);
	write_ast_string(os, value);
	fprintf(os->f, ",\n");
}

void
write_ast_field_boolean(OutputState *os, char *name, bool value, int indent)
{
	write_ast_key(os, name, indent);
	fprintf(os->f, value ? "true" : "false");
	fprintf(os->f, ",\n");
}

void
write_ast_field_integer(OutputState *os, char *name, i32 value, int indent)
{
	write_ast_key(os, name, indent);
	fprintf(os->f, "%"PRIi32, value);
	fprintf(os->f, ",\n");
}

void
write_ast_field_array(OutputState *os, char *name, Ast **values, size_t value_cnt, int indent)
{
	write_ast_keys(os, name, "Ast*", indent);
	if (value_cnt == 0) {
		fprintf(os->f, "},\n");
	} else {
		fprintf(os->f, "\n");
		indent += 4;
		for (size_t i = 0; i < value_cnt; i++) {
			fprintf(os->f, "%*s", indent, "");
			write_ast(os, values[i], indent + 4, false);
		}
		indent -= 4;
		fprintf(os->f, "%*s},\n", indent, "");
	}
	fprintf(os->f, "%*s.%s_cnt = %zu,\n", indent, "", name, value_cnt);
}

void
write_ast_field_string_array(OutputState *os, char *name, Str *strings, size_t string_cnt, int indent)
{
	write_ast_keys(os, name, "Str", indent);
	if (string_cnt == 0) {
		fprintf(os->f, "},\n");
	} else {
		fprintf(os->f, "\n");
		indent += 4;
		for (size_t i = 0; i < string_cnt; i++) {
			fprintf(os->f, "%*s", indent, "");
			write_ast_string(os, strings[i]);
			fprintf(os->f, ",\n");
		}
		indent -= 4;
		fprintf(os->f, "%*s},\n", indent, "");
	}
	fprintf(os->f, "%*s.%s_cnt = %zu,\n", indent, "", name, string_cnt);
}

void
print_members(Class *class, Program *program, FILE *f)
{
	u8 *members = class->members;
	for (size_t i = 0; i < class->member_cnt; i++) {
		if (i != 0) {
			fprintf(f, ", ");
		}
		u16 member_name = read_u16(&members);
		Constant *name = &program->constants[member_name];
		assert(name->kind == CK_STRING);
		fprintf(f, "#%"PRIu16"=\"%.*s\"", member_name, (int) name->string.len, name->string.str);
	}
}

void
print_constant(Program *program, u16 constant_index, FILE *f, bool raw)
{
	if (!raw) {
		fprintf(f, "#%"PRIu16"=", constant_index);
	}
	Constant *constant = &program->constants[constant_index];
	switch (constant->kind) {
	case CK_NULL:
		fprintf(f, "null");
		break;
	case CK_BOOLEAN: {
		fprintf(f, "%s", constant->boolean ? "true" : "false");
		break;
	}
	case CK_INTEGER:
		fprintf(f, "%"PRIi32, constant->integer);
		break;
	case CK_STRING:
		fprintf(f, "\"%.*s\"", (int) constant->string.len, constant->string.str);
		break;
	case CK_FUNCTION: {
		CFunction *function = &constant->function;
		fprintf(f, "Function(params: %"PRIi8", locals: %"PRIi8", length: %zu)\n", function->parameter_cnt, function->local_cnt, function->instruction_len);
		u8 *start = function->instruction_start;
		for (u8 *ip = start;;) {
			fprintf(f, "%18zu: ", ip - start);
			switch (read_u8(&ip)) {
			case OP_CONSTANT: {
				u16 constant_index = read_u16(&ip);
				Constant *constant = &program->constants[constant_index];
				switch (constant->kind) {
				case CK_NULL:
				case CK_BOOLEAN:
				case CK_INTEGER:
					fprintf(f, "constant ");
					print_constant(program, constant_index, f, false);
					break;
				case CK_FUNCTION:
					fprintf(f, "function #%"PRIu16, constant_index);
					break;
				default:
					assert(false);
				}
				break;
			}
			case OP_ARRAY: {
				fprintf(f, "array");
				break;
			}
			case OP_OBJECT: {
				u16 constant_index = read_u16(&ip);
				fprintf(f, "object #%"PRIu16, constant_index);
				break;
			}
			case OP_GET_LOCAL: {
				u16 local_index = read_u16(&ip);
				fprintf(f, "get local %"PRIu16, local_index);
				break;
			}
			case OP_SET_LOCAL: {
				u16 local_index = read_u16(&ip);
				fprintf(f, "set local %"PRIu16, local_index);
				break;
			}
			case OP_GET_GLOBAL: {
				fprintf(f, "get global ");
				u16 constant_index = read_u16(&ip);
				print_constant(program, constant_index, f, false);
				break;
			}
			case OP_SET_GLOBAL: {
				fprintf(f, "set global ");
				u16 constant_index = read_u16(&ip);
				print_constant(program, constant_index, f, false);
				break;
			}
			case OP_GET_FIELD: {
				fprintf(f, "get field ");
				u16 constant_index = read_u16(&ip);
				print_constant(program, constant_index, f, false);
				break;
			}
			case OP_SET_FIELD: {
				fprintf(f, "set field ");
				u16 constant_index = read_u16(&ip);
				print_constant(program, constant_index, f, false);
				break;
			}
			case OP_JUMP: {
				i16 offset = (i16) read_u16(&ip);
				fprintf(f, "jump %+"PRIi16"=%zu", offset, (size_t)(ip - start) + offset);
				break;
			}
			case OP_BRANCH: {
				i16 offset = (i16) read_u16(&ip);
				fprintf(f, "branch %+"PRIi16"=%zu", offset, (size_t)(ip - start) + offset);
				break;
			}
			case OP_CALL_FUNCTION: {
				u8 argument_cnt = read_u8(&ip);
				fprintf(f, "call function %"PRIu8, argument_cnt);
				break;
			}
			case OP_CALL_METHOD: {
				fprintf(f, "call method ");
				u16 constant_index = read_u16(&ip);
				print_constant(program, constant_index, f, false);
				u8 argument_cnt = read_u8(&ip);
				fprintf(f, " %"PRIu8, argument_cnt);
				break;
			}
			case OP_PRINT: {
				fprintf(f, "print ");
				u16 constant_index = read_u16(&ip);
				print_constant(program, constant_index, f, false);
				u8 argument_cnt = read_u8(&ip);
				fprintf(f, " %"PRIu8, argument_cnt);
				break;
			}
			case OP_DROP: {
				fprintf(f, "drop");
				break;
			}
			case OP_RETURN: {
				fprintf(f, "return");
				return;
			}
			}
			fprintf(f, "\n");
		}
		break;
	}
	case CK_CLASS:
		fprintf(f, "Class(");
		print_members(&constant->class, program, f);
		fprintf(f, ")");
		break;
	default:
		UNREACHABLE();
	}
}

void
disassemble(Program *program, FILE *f)
{
	fprintf(f, "Constant Pool:\n");
	for (u16 i = 0; i < program->constant_cnt; i++) {
		fprintf(f, "%5"PRIu16": ", i);
		print_constant(program, i, f, true);
		fprintf(f, "\n");
	}
	fprintf(f, "Entry: #%"PRIu16"\n", program->entry_point);
	fprintf(f, "Globals: ");
	print_members(&program->global_class, program, f);
	fprintf(f, "\n");
}

static void printf_attr(2)
argument_error(ErrorContext *ec, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	verror(ec, NULL, "argument", true, msg, ap);
	va_end(ap);
}


static Str
read_file(ErrorContext *ec, Arena *arena, const char *name)
{
	errno = 0;
	FILE *f = fopen(name, "rb");
	if (!f) {
		argument_error(ec, "Failed to open file '%s': %s", name, strerror(errno));
	}
	if (fseek(f, 0, SEEK_END) != 0) {
		argument_error(ec, "Failed seek in file '%s': %s", name, strerror(errno));
	}
	long tell = ftell(f);
	if (tell < 0) {
		argument_error(ec, "Failed to ftell a file '%s': %s", name, strerror(errno));
	}
	size_t fsize = (size_t) tell;
	assert(fseek(f, 0, SEEK_SET) == 0);
	u8 *buf = arena_alloc(arena, fsize);
	size_t read;
	if ((read = fread(buf, 1, fsize, f)) != fsize) {
		if (feof(f)) {
			fsize = read;
		} else {
			argument_error(ec, "Failed to read file '%s'", name);
		}
	}
	assert(fclose(f) == 0);
	return (Str) { .str = buf, .len = fsize };
}

static const char cmd_parse_help[] = \
	"USAGE:\n"
	"    fml parse [OPTIONS] FILE\n"
	"\n"
	"ARGS:\n"
	"    FILE    The file to parse\n"
	"\n"
	"OPTIONS:\n"
	"    --top   Parse whole program, not just single expression\n"
;

static void
cmd_parse(ErrorContext *ec, Arena *arena, int argc, const char **argv)
{
	enum { PARSE_EXPRESSION, PARSE_TOP } kind = PARSE_EXPRESSION;
	while (argc > 0 && argv[0][0] == '-') {
		if (strcmp(argv[0], "--top") == 0) {
			kind = PARSE_TOP;
		} else {
			argument_error(ec, "Unknown flag '%s'", argv[0]);
		}
		argc--;
		argv++;
	}
	if (argc != 1) {
		argument_error(ec, "Expected FILE as a single positional argument\n");
	}
	Str source = read_file(ec, arena, argv[0]);
	Ast *ast = parse_source(ec, arena, source);
	OutputState os = { .f = stdout };
	if (kind == PARSE_EXPRESSION && ast->kind == AST_TOP) {
		ast = ((AstTop *)ast)->expressions[0];
	}
	write_ast(&os, ast, 4, true);
}

static const char cmd_run_help[] = \
	"USAGE:\n"
	"    fml run [OPTIONS] FILE\n"
	"\n"
	"ARGS:\n"
	"    FILE    The file to run\n"
	"\n"
	"OPTIONS:\n"
	"    --heap-log LOG_FILE   Heap log file, if none no logging is done\n"
	"    --heap-size MBs       Maximum heap size in mebibytes\n"
;

static void
cmd_run(ErrorContext *ec, Arena *arena, int argc, const char **argv)
{
	size_t heap_size = 0;
	FILE *heap_log = NULL;
	while (argc > 0 && argv[0][0] == '-') {
		if (strcmp(argv[0], "--heap-log") == 0) {
			argc--;
			argv++;
			heap_log = fopen(argv[0], "wb");
			if (!heap_log) {
				argument_error(ec, "Failed to open heap log '%s': %s", argv[0], strerror(errno));
			}
		} else if (strcmp(argv[0], "--heap-size") == 0) {
			argc--;
			argv++;
			char *end;
			errno = 0;
			long long num = strtoll(argv[0], &end, 10);
			if (errno != 0 || end == argv[0] || num < 0 || (unsigned long long) num > SIZE_MAX) {
				argument_error(ec, "Invalid heap size '%s'", argv[0]);
			}
			heap_size = (size_t) num;
		} else {
			argument_error(ec, "Unknown flag '%s'", argv[0]);
		}
		argc--;
		argv++;
	}
	if (argc != 1) {
		argument_error(ec, "Expected FILE as a single argument\n");
	}
	Str source = read_file(ec, arena, argv[0]);
	Ast *ast = parse_source(ec, arena, source);
	Program program;
	compile_ast(ec, arena, &program, ast);
	vm_run(ec, arena, &program, heap_size, heap_log);
}

static const char cmd_ast_interpret_help[] = \
	"USAGE:\n"
	"    fml ast_interpret FILE\n"
	"\n"
	"ARGS:\n"
	"    FILE    The source file to interpret with AST interpreter\n"
;

static void
cmd_ast_interpret(ErrorContext *ec, Arena *arena, int argc, const char **argv)
{
	if (argc != 1) {
		argument_error(ec, "Expected FILE as a single argument\n");
	}
	Str source = read_file(ec, arena, argv[0]);
	Ast *ast = parse_source(ec, arena, source);
	interpret_ast(ec, arena, ast, 0, NULL);
}

static const char cmd_bc_compile_help[] = \
	"USAGE:\n"
	"    fml bc_compile FILE\n"
	"\n"
	"ARGS:\n"
	"    FILE    The source file to compile to bytecode\n"
;

static void
cmd_bc_compile(ErrorContext *ec, Arena *arena, int argc, const char **argv)
{
	if (argc != 1) {
		argument_error(ec, "Expected FILE as a single argument\n");
	}
	Str source = read_file(ec, arena, argv[0]);
	Ast *ast = parse_source(ec, arena, source);
	Program program;
	compile_ast(ec, arena, &program, ast);
	write_program(&program, stdout);
	fflush(stdout);
	if (ferror(stdout)) {
		argument_error(ec, "Failed to write bytecode to stdout");
	}
}

static const char cmd_bc_interpret_help[] = \
	"USAGE:\n"
	"    fml bc_interpret FILE\n"
	"\n"
	"ARGS:\n"
	"    FILE    The bytecode file to interpret\n"
;

static void
cmd_bc_interpret(ErrorContext *ec, Arena *arena, int argc, const char **argv)
{
	if (argc != 1) {
		argument_error(ec, "Expected FILE as a single argument\n");
	}
	Str source = read_file(ec, arena, argv[0]);
	Program program;
	read_program(ec, arena, &program, (u8 *) source.str, source.len);
	vm_run(ec, arena, &program, 0, NULL);
}

static const char cmd_bc_disassemble_help[] = \
	"USAGE:\n"
	"    fml bc_disassemble FILE\n"
	"\n"
	"ARGS:\n"
	"    FILE    The bytecode file to disassemble\n"
;

static void
cmd_bc_disassemble(ErrorContext *ec, Arena *arena, int argc, const char **argv)
{
	if (argc != 1) {
		argument_error(ec, "Expected FILE as a single argument\n");
	}
	Str source = read_file(ec, arena, argv[0]);
	Program program;
	read_program(ec, arena, &program, (u8 *) source.str, source.len);
	disassemble(&program, stdout);
}

static const char cmd_bc_dump_help[] = \
	"USAGE:\n"
	"    fml bc_dump FILE\n"
	"\n"
	"ARGS:\n"
	"    FILE    The source file to compile and disassemble\n"
;

static void
cmd_bc_dump(ErrorContext *ec, Arena *arena, int argc, const char **argv)
{
	if (argc != 1) {
		argument_error(ec, "Expected FILE as a single argument\n");
	}
	Str source = read_file(ec, arena, argv[0]);
	Ast *ast = parse_source(ec, arena, source);
	Program program;
	compile_ast(ec, arena, &program, ast);
	disassemble(&program, stdout);
}

static const char cmd_bc_verify_help[] = \
	"Verify:\n"
	" - correct constant kinds are used,\n"
	" - jump targets being starts of instructions,\n"
	" - operand stack heights being consistent across control flow,\n"
	" - used global variable names,\n"
	" - and maybe other things.\n"
	"\n"
	"USAGE:\n"
	"    fml bc_verify FILE\n"
	"\n"
	"ARGS:\n"
	"    FILE    The bytecode file to verify\n"
;

static void
cmd_bc_verify(ErrorContext *ec, Arena *arena, int argc, const char **argv)
{
	if (argc != 1) {
		argument_error(ec, "Expected FILE as a single argument\n");
	}
	Str source = read_file(ec, arena, argv[0]);
	Program program;
	read_program(ec, arena, &program, (u8 *) source.str, source.len);
	verify_program(ec, arena, &program);
}

static const char cmd_help_help[] = \
	"USAGE:\n"
	"    fml help [COMMAND]\n"
	"\n"
	"ARGS:\n"
	"    COMMAND    Get help about COMMAND, otherwise get help about fml\n"
;

void print_help(FILE *file, const char *command);

static void
cmd_help(ErrorContext *ec, Arena *arena, int argc, const char **argv)
{
	(void) arena;
	if (argc == 0) {
		print_help(stdout, NULL);
		return;
	} else if (argc != 1) {
		argument_error(ec, "Expected COMMAND as an argument\n");
		return;
	}
	print_help(stdout, argv[0]);

}

static struct {
	const char *name;
	void (*func)(ErrorContext *ec, Arena *arena, int argc, const char **argv);
	const char *short_help;
	const char *help;
} commands[] = {
	#define CMD(name, short_help) { #name, cmd_##name, short_help, cmd_##name ##_help },
	CMD(run, "Run a program with the bytecode interpreter")
	CMD(bc_compile, "Compile a program to bytecode")
	CMD(bc_interpret, "Interpret bytecode")
	CMD(bc_disassemble, "Disassemble bytecode")
	CMD(bc_dump, "Compile program and print disassembly")
	CMD(bc_verify, "Statically verify some bytecode properties")
	CMD(ast_interpret, "Run a program with AST interpreter")
	CMD(parse, "Parse a source file and print it as AST")
	CMD(help, "Get help about fml or subcommand")
	#undef CMD
};

void
print_help(FILE *file, const char *command)
{
	if (command) {
		for (size_t i = 0; i < sizeof(commands) / sizeof(commands[0]); i++) {
			if (strcmp(command, commands[i].name) != 0) {
				continue;
			}
			fprintf(file, "fml-%s\n", command);
			fprintf(file, "%s\n\n", commands[i].short_help);
			fprintf(file, "%s", commands[i].help);
			return;
		}
		file = stderr;
		fprintf(file, "Unknown command '%s'", command);
		// fallthrough
	}
	fprintf(file, "USAGE:\n");
	fprintf(file, "    fml SUBCOMMAND [OPTIONS] [ARGS]\n");
	fprintf(file, "\n");
	fprintf(file, "SUBCOMMANDS:\n");
	for (size_t i = 0; i < sizeof(commands) / sizeof(commands[0]); i++) {
		fprintf(file, "    %-18s%s\n", commands[i].name, commands[i].short_help);
	}
	return;
}

int
main(int argc, const char **argv) {
#ifdef _WIN32
	// Set standard output mode to "binary" on Windows.
	// https://nullprogram.com/blog/2021/12/30/
	int _setmode(int, int);
	_setmode(1, 0x8000);
#endif

	Arena arena_;
	Arena *arena = &arena_;
	arena_init(arena);

	ErrorContext ec;
	error_context_init(&ec);

	if (setjmp(ec.loc) != 0) {
		goto end;
	}

	if (argc < 2) {
		fprintf(stderr, "Expected a command as first argument\n");
		print_help(stderr, NULL);
		return EXIT_FAILURE;
	}

	const char *command = argv[1];
	size_t command_cnt = sizeof(commands) / sizeof(commands[0]);
	for (size_t i = 0; i < command_cnt; i++) {
		if (strcmp(command, commands[i].name) != 0) {
			continue;
		}
		if (argc >= 3 && (strcmp(argv[2], "-h") == 0 || strcmp(argv[2], "--help") == 0)) {
			print_help(stdout, command);
			goto end;
		}
		commands[i].func(&ec, arena, argc - 2, argv + 2);
		goto end;
	}

	fprintf(stderr, "Unknown command '%s'\n", command);
	print_help(stderr, NULL);

end:
	for (Error *err = ec.error_head; err; err = err->next) {
		if (!err->pos) {
			fprintf(stderr, "%s error: %s\n", err->kind, err->msg);
			continue;
		}
		const u8 *line_start = ec.source.str;
		size_t line = 0;
		const u8 *pos = ec.source.str;
		for (; pos < err->pos; pos++) {
			if (*pos == '\n') {
				line_start = pos + 1;
				line++;
			}
		}
		size_t col = pos - line_start;
		const u8 *source_end = ec.source.str + ec.source.len;
		const u8 *line_end = pos;
		for (; line_end < source_end && *line_end != '\n'; line_end++) {}
		fprintf(stderr, "[%zu:%zu]: %s error: %s\n", line + 1, col + 1, err->kind, err->msg);
		fprintf(stderr, "  %.*s\n", (int) (line_end - line_start), line_start);
		fprintf(stderr, "  %*s\n", (int) (pos - line_start + 1), "^");
	}
	while (last) {
		GcValue *prev = last->prev;
		free(last);
		last = prev;
	}
	arena_destroy(&ec.arena);
	if (ec.heap) {
		heap_destroy(ec.heap);
	}
	arena_destroy(arena);
	return ec.error_head ? EXIT_FAILURE : EXIT_SUCCESS;
}
