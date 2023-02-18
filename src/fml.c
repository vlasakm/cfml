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

#include "parser.h"


#define garena_array(arena, type) \
	((type *) garena_mem((arena)))

#define garena_array_from(arena, start, type) \
	((type *) garena_from((arena), (start), alignof(type)))


#define UNREACHABLE() unreachable(__FILE__, __LINE__)
static _Noreturn void
unreachable(char *file, size_t line)
{
	fprintf(stderr, "ERROR: unreachable code reached at %s:%zu\n", file, line);
	exit(EXIT_FAILURE);
}

bool
str_eq(Str a, Str b)
{
	return a.len == b.len && memcmp(a.str, b.str, a.len) == 0;
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
} ErrorContext;

void
error_context_init(ErrorContext *ec)
{
	arena_init(&ec->arena);
	ec->source = (Str) {0};
	ec->error_head = NULL;
	ec->error_tail = NULL;
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

static void
exec_error(ErrorContext *ec, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	verror(ec, NULL, "execution", true, msg, ap);
	va_end(ap);
}

Value
make_null(void)
{
	return (Value) { .kind = VK_NULL };
}

Value
make_boolean(bool value)
{
	return (Value) { .kind = VK_BOOLEAN, .boolean = value };
}

Value
make_integer(i32 value)
{
	return (Value) { .kind = VK_INTEGER, .integer = value };
}

GcValue *last;

Value
make_array(size_t length)
{
	Array *array = malloc(sizeof(*array) + length * sizeof(array->values[0]));
	array->gcvalue = (GcValue) { .kind = GK_ARRAY };
	array->length = length;

	array->gcvalue.prev = last;
	last = &array->gcvalue;

	return (Value) { .kind = VK_GCVALUE, .gcvalue = &array->gcvalue };
}

Value
make_object(size_t field_cnt)
{
	Object *object = malloc(sizeof(*object) + field_cnt * sizeof(object->fields[0]));
	object->gcvalue = (GcValue) { .kind = GK_OBJECT };
	// NOTE: Caller has to set parent!
	//object->parent = make_null();
	object->field_cnt = field_cnt;

	object->gcvalue.prev = last;
	last = &object->gcvalue;

	return (Value) { .kind = VK_GCVALUE, .gcvalue = &object->gcvalue };
}

Value
make_function_ast(AstFunction *function)
{
	return (Value) { .kind = VK_FUNCTION, .function = function };
}

Value
make_function_bc(u16 function_index)
{
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

static int
str_cmp(Str a, Str b)
{
	int cmp = memcmp(a.str, b.str, a.len < b.len ? a.len : b.len);
	return cmp == 0 ? (a.len > b.len) - (b.len > a.len) : cmp;
}

void
value_print(Value value)
{
	switch (value.kind) {
	case VK_NULL:
		printf("%s", "null");
		break;
	case VK_BOOLEAN:
		printf("%s", value.boolean ? "true" : "false");
		break;
	case VK_INTEGER:
		printf("%"PRIi32, value.integer);
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
	if (value.kind == VK_NULL || (value.kind == VK_BOOLEAN && value.boolean == false)) {
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
		exec_error(ec, "Value is negataive");
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
value_call_primitive_method(ErrorContext *ec, Value target, Str method, Value *arguments, size_t argument_cnt)
{
	const u8 *method_name = method.str;
	size_t method_name_len = method.len;
	#define METHOD(name) \
			if (sizeof(name) - 1 == method_name_len && memcmp(name, method_name, method_name_len) == 0) /* body*/

	METHOD("==") {
		if (argument_cnt != 1) goto err;
		if (target.kind != arguments[0].kind) return make_boolean(false);
		switch (target.kind) {
		case VK_NULL: return make_boolean(true);
		case VK_BOOLEAN: return make_boolean(value_as_bool(target) == value_as_bool(arguments[0]));
		case VK_INTEGER: return make_boolean(value_as_integer(target) == value_as_integer(arguments[0]));
		default: goto err;
		}
	}
	METHOD("!=") {
		if (argument_cnt != 1) goto err;
		if (target.kind != arguments[0].kind) return make_boolean(true);
		switch (target.kind) {
		case VK_NULL: return make_boolean(false);
		case VK_BOOLEAN: return make_boolean(value_as_bool(target) != value_as_bool(arguments[0]));
		case VK_INTEGER: return make_boolean(value_as_integer(target) != value_as_integer(arguments[0]));
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
		METHOD("&") return make_boolean(left && right);
		METHOD("|") return make_boolean(left || right);
		break;
	}
	case VK_INTEGER: {
		if (argument_cnt != 1) goto err;
		if (arguments[0].kind != VK_INTEGER) goto err;
		i32 left = value_as_integer(target);
		i32 right = value_as_integer(arguments[0]);
		METHOD("+") return make_integer(left + right);
		METHOD("-") return make_integer(left - right);
		METHOD("*") return make_integer(left * right);
		METHOD("/") {
				if (right == 0) {
					exec_error(ec, "Division by zero");
					return make_integer(0);
				} else {
					return make_integer(left / right);
				}
		}
		METHOD("%") {
				if (right == 0) {
					exec_error(ec, "Modulo by zero");
					return make_integer(0);
				} else {
					return make_integer(left % right);
				}
		}
		METHOD("<=") return make_boolean(left <= right);
		METHOD("<") return make_boolean(left < right);
		METHOD(">=") return make_boolean(left >= right);
		METHOD(">") return make_boolean(left > right);
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
		case GK_OBJECT:
			break;
		case GK_PRINTING:
			UNREACHABLE();
		}
	case VK_FUNCTION:
		break;
	}
err:
	exec_error(ec, "Invalid method '%.*s' called on value (invalid types or number of arguments)", method_name_len, method_name);
	return make_null();
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
} InterpreterState;

Environment *
env_create(Environment *prev)
{
	Environment *env = calloc(sizeof(*env), 1);
	env->prev = prev;
	table_init(&env->env, 0);
	return env;
}

void
env_destroy(Environment *env)
{
	table_destroy(&env->env);
	free(env);
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
		// Name not found, should be a global whose
		// definition we will yet see.
		Value null = make_null();
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
		return make_null();
	}
	case AST_BOOLEAN: {
		AstBoolean *boolean = (AstBoolean *) ast;
		return make_boolean(boolean->value);
	}
	case AST_INTEGER: {
		AstInteger *integer = (AstInteger *) ast;
		return make_integer(integer->value);
	}
	case AST_ARRAY: {
		AstArray *array = (AstArray *) ast;
		Value size_value = interpret(is, array->size);
		size_t size = value_as_size(is->ec, size_value);
		Value array_value = make_array(size);
		Array *array_obj = value_as_array(array_value);
		Environment *saved_env = is->env;
		for (size_t i = 0; i < size; i++) {
			is->env = env_create(saved_env);
			array_obj->values[i] = interpret(is, array->initializer);
			env_destroy(is->env);
			is->env = saved_env;
		}
		return array_value;
	}
	case AST_OBJECT: {
		AstObject *object = (AstObject *) ast;
		Value parent = interpret(is, object->extends);
		Value object_value = make_object(object->member_cnt);
		Object *object_obj = value_as_object(object_value);
		object_obj->parent = parent;
		for (size_t i = 0; i < object->member_cnt; i++) {
			Ast *ast_member = object->members[i];
			switch (ast_member->kind) {
			case AST_DEFINITION: {
				AstDefinition *definition = (AstDefinition *) ast_member;
				object_obj->fields[i].name = definition->name;
				object_obj->fields[i].value = interpret(is, definition->value);
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
		return make_function_ast(function);
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
		if (value_to_bool(condition)) {
			return interpret(is, conditional->consequent);
		} else {
			return interpret(is, conditional->alternative);
		}
	}
	case AST_LOOP: {
		AstLoop *loop = (AstLoop *) ast;
		while (value_to_bool(interpret(is, loop->condition))) {
			interpret(is, loop->body);
		}
		return make_null();
	}
	case AST_PRINT: {
		AstPrint *print = (AstPrint *) ast;
		Value *arguments = calloc(print->argument_cnt, sizeof(*arguments));
		for (size_t i = 0; i < print->argument_cnt; i++) {
			arguments[i] = interpret(is, print->arguments[i]);
		}
		builtin_print(is->ec, print->format, arguments, print->argument_cnt);
		free(arguments);
		return make_null();
	}
	case AST_BLOCK: {
		AstBlock *block = (AstBlock *) ast;
		Environment *saved_env = is->env;
		is->env = env_create(is->env);
		Value value = interpret(is, block->expressions[0]);
		for (size_t i = 1; i < block->expression_cnt; i++) {
			value = interpret(is, block->expressions[i]);
		}
		env_destroy(is->env);
		is->env = saved_env;
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
		is->env = env_create(is->global_env);
		for (size_t i = 0; i < argument_cnt; i++) {
			env_define(is->env, function->parameters[i], arguments[i]);
		}
		if (!function_call) {
			env_define(is->env, STR("this"), object);
		}
		return_value = interpret(is, function->body);
		env_destroy(is->env);
		is->env = saved_env;
	} else {
		return_value = value_call_primitive_method(is->ec, object, method, &arguments[0], argument_cnt);
	}
	free(arguments);
	return return_value;
}

void
interpret_ast(ErrorContext *ec, Ast *ast)
{
	Environment *env = env_create(NULL);
	InterpreterState is = {
		.ec = ec,
		.env = env,
		.global_env = env,
	};
	env_define(is.env, STR("this"), make_null());
	interpret(&is, ast);
	env_destroy(env);
}

// Parse little endian numbers from byte array. Beware of implicit promotion from uint8_t to signed int.
// https://commandcenter.blogspot.com/2012/04/byte-order-fallacy.html
// https://www.reddit.com/r/C_Programming/comments/bjuk3v/the_byte_order_fallacy/embbwq2/

static u32
read_u32(u8 **src)
{
	u8 *pos = *src;
	u32 res = (((u32) pos[3]) << 24) | (pos[2] << 16) | (pos[1] << 8) | (pos[0] << 0);
	*src += 4;
	return res;
}

static uint16_t
read_u16(u8 **src)
{
	u8 *pos = *src;
	u16 res = ((uint16_t) (pos[1] << 8) | (pos[0] << 0));
	*src += 2;
	return res;
}

static uint8_t
read_u8(u8 **src)
{
	return *(*src)++;
}


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
	u16 local_cnt;
	u8 parameter_cnt;
	u8 *instruction_start;
	size_t instruction_len;
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
		u16 slot;
		CFunction method;
		Class class;
	};
} Constant;

typedef struct {
	Constant *constants;
	size_t constant_cnt;
	Class global_class;
	u16 entry_point;
} Program;

static void
bc_error(ErrorContext *ec, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	verror(ec, NULL, "bytecode", true, msg, ap);
	va_end(ap);
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
		break;
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
		constant->method.parameter_cnt = read_u8(input);
		constant->method.local_cnt = read_u16(input);
		constant->method.instruction_len = read_u32(input);
		constant->method.instruction_start = *input;
		*input += constant->method.instruction_len;
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
	if (input_len < 6) {
		bc_error(ec, "The bytecode is too small (%zu bytes, need at least 6)", input_len);
	}
	program->constant_cnt = read_u16(&input);
	program->constants = arena_alloc(arena, program->constant_cnt * sizeof(*program->constants));
	for (size_t i = 0; i < program->constant_cnt; i++) {
		read_constant(ec, &input, &program->constants[i]);
	}
	read_class(&input, &program->global_class);
	program->entry_point = read_u16(&input);
	return true;
}

typedef struct {
	ErrorContext *ec;
	Arena *arena;
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
	return make_null();
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
	if (vm->stack_pos + 1 >= vm->stack_len) {
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
	Value object_value = make_object(class->member_cnt);
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
vm_call_method(VM *vm, u16 method_index, u8 argument_cnt)
{
	Constant *method_constant = &vm->program->constants[method_index];
	assert(method_constant->kind == CK_FUNCTION);
	CFunction *method = &method_constant->method;
	if (argument_cnt != method->parameter_cnt) {
		exec_error(vm->ec, "Wrong number of arguments: %zu expected, got %zu", method->parameter_cnt, argument_cnt);
	}

	size_t local_cnt = argument_cnt + method->local_cnt;
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
		locals[i] = make_null();
	}

	for (u8 *ip = method->instruction_start;;) {
		switch (read_u8(&ip)) {
		case OP_CONSTANT: {
			u16 constant_index = read_u16(&ip);
			Constant *constant = &vm->program->constants[constant_index];
			Value value;
			switch (constant->kind) {
			case CK_NULL:
				value = make_null();
				break;
			case CK_BOOLEAN:
				value = make_boolean(constant->boolean);
				break;
			case CK_INTEGER:
				value = make_integer(constant->integer);
				break;
			case CK_FUNCTION:
				value = make_function_bc(constant_index);
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
			Value array_value = make_array(size);
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
			i16 offset = read_u16(&ip);
			ip += offset;
			break;
		}
		case OP_BRANCH: {
			i16 offset = read_u16(&ip);
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
			u16 method_index = value_as_function_bc(*function);
			// Receiver (this) is null for functions
			*function = make_null();
			vm_call_method(vm, method_index, argument_cnt + 1);
			break;
		}
		case OP_CALL_METHOD: {
			Str name = constant_string(vm, &ip);
			u8 argument_cnt = read_u8(&ip);
			Value *lobject = vm_peek_n(vm, argument_cnt);
			Value *method_value = value_method_try(vm->ec, *lobject, lobject, name);
			if (method_value) {
				u16 method_index = value_as_function_bc(*method_value);
				vm_call_method(vm, method_index, argument_cnt);
			} else {
				Value *arguments = vm_peek_n(vm, argument_cnt - 1);
				Value return_value = value_call_primitive_method(vm->ec, *lobject, name, arguments, argument_cnt - 1);
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
			vm_push(vm, make_null());
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
vm_run(ErrorContext *ec, Arena *arena, Program *program)
{
	VM vm = {
		.ec = ec,
		.arena = arena,
		.program = program,
		.global = make_null(),
		.stack = arena_alloc(arena, 1024 * sizeof(Value)),
		.stack_pos = -1,
		.stack_len = 1024,
		.frame_stack = arena_alloc(arena, 1024 * sizeof(Value)),
		.frame_stack_pos = 0,
		.frame_stack_len = 1024,
		.bp = 0,
	};
	vm.global = vm_instantiate_class(&vm, &program->global_class, make_null_vm);
	// push `this` as an argument
	vm.stack[++vm.stack_pos] = make_null();
	vm_call_method(&vm, program->entry_point, 1);
	// Check that the program left exactly one value on the stack
	assert(vm.stack_pos == 0);
}

typedef struct {
	ErrorContext *ec;
	Arena *arena;
	GArena constants; // Constant array
	GArena instructions; // u8 array
	GArena members; // u16 array (but unaligned when serialized)
	bool in_object;
	bool in_block;
	bool in_definition;
	Environment *env;
	u16 local_cnt;
	bool had_error;
} CompilerState;

static void
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

static Class
create_class(CompilerState *cs, size_t start)
{
	size_t member_cnt = garena_cnt_from(&cs->members, start, u16);
	u16 *members = move_to_arena(cs->arena, &cs->members, start, u16);
	for (size_t i = 0; i < member_cnt; i++) {
		for (size_t j = i + 1; j < member_cnt; j++) {
			// can be constant index comparison since we deduplicate
			// constants
			if (members[i] != members[j]) {
				continue;
			}
			const char *type = cs->in_object ? "Member" : "Global";
			Str name = garena_array(&cs->constants, Constant)[members[i]].string;
			if (members[i] == members[j]) {
				compile_error(cs, "%s '%.*s' already defined", type, (int) name.len, name.str);
			}
		}
	}
	// NOTE: due to losing alignment when serializing, we refer to
	// members with `u8` pointers while compiling them as if they
	// were u16
	return (Class) {
		.member_cnt = member_cnt,
		.members = (u8 *) members,
	};
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
		Environment *saved_environment = cs->env;
		cs->env = env_create(cs->env);
		compile(cs, array->initializer);
		env_destroy(cs->env);
		cs->env = saved_environment;
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
		bool saved_in_object = cs->in_object;
		bool saved_in_definition = cs->in_definition;
		size_t start = garena_save(&cs->members);

		cs->in_object = true;
		cs->in_definition = false;
		for (size_t i = 0; i < object->member_cnt; i++) {
			Ast *ast_member = object->members[i];
			switch (ast_member->kind) {
			case AST_DEFINITION:
				compile(cs, ast_member);
				break;
			default: UNREACHABLE();
			}
		}

		Class class = create_class(cs, start);
		u16 class_index = add_constant(cs, (Constant) { .kind = CK_CLASS, .class = class });
		op_index(cs, OP_OBJECT, class_index);

		cs->in_object = saved_in_object;
		cs->in_definition = saved_in_definition;
		return;
	}
	case AST_FUNCTION: {
		AstFunction *function = (AstFunction *) ast;
		Environment *saved_environment = cs->env;
		u16 saved_local_cnt = cs->local_cnt;
		size_t start = garena_save(&cs->instructions);
		bool saved_in_block = cs->in_block;
		bool saved_in_object = cs->in_object;

		cs->local_cnt = 0;
		cs->in_block = true;
		cs->in_object = false;

		// Start with empty environment
		cs->env = env_create(NULL);
		env_define(cs->env, STR("this"), make_integer(cs->local_cnt++));
		for (size_t i = 0; i < function->parameter_cnt; i++) {
			env_define(cs->env, function->parameters[i], make_integer(cs->local_cnt++));
		}
		compile(cs, function->body);
		op(cs, OP_RETURN);
		env_destroy(cs->env);

		size_t instruction_len = garena_cnt_from(&cs->instructions, start, u8);
		u8 *instruction_start = move_to_arena(cs->arena, &cs->instructions, start, u8);
		literal(cs, (Constant) {
		       .kind = CK_FUNCTION,
		       .method = (CFunction) {
				.local_cnt = cs->local_cnt - function->parameter_cnt - 1,
				.parameter_cnt = function->parameter_cnt + 1,
				.instruction_start = instruction_start,
				.instruction_len = instruction_len,
			},
		});
		cs->env = saved_environment;
		cs->local_cnt = saved_local_cnt;
		cs->in_block = saved_in_block;
		cs->in_object = saved_in_object;
		return;
	}

	case AST_DEFINITION: {
		AstDefinition *definition = (AstDefinition *) ast;
		bool saved_in_definition = cs->in_definition;
		cs->in_definition = true;
		compile(cs, definition->value);
		cs->in_definition = saved_in_definition;
		if (cs->in_object || !cs->in_block) {
			u16 name = add_string(cs, definition->name);
			garena_push_value(&cs->members, u16, name);
			if (!cs->in_object) {
				op_string(cs, OP_SET_GLOBAL, definition->name);
			} else if (cs->in_definition) {
				compile_error(cs, "Nested definition (in definition) in object not allowed");
			}
		} else {
			env_define(cs->env, definition->name, make_integer(cs->local_cnt));
			op_index(cs, OP_SET_LOCAL, cs->local_cnt);
			cs->local_cnt += 1;
		}
		return;
	}

	case AST_VARIABLE_ACCESS: {
		AstVariableAccess *variable_access = (AstVariableAccess *) ast;
		Value *local_index = env_lookup_raw(cs->env, variable_access->name);
		if (local_index) {
			op_index(cs, OP_GET_LOCAL, value_as_integer(*local_index));
		} else {
			op_string(cs, OP_GET_GLOBAL, variable_access->name);
		}
		return;
	}
	case AST_VARIABLE_ASSIGNMENT: {
		AstVariableAssignment *variable_assignment = (AstVariableAssignment *) ast;
		compile(cs, variable_assignment->value);
		Value *local_index = env_lookup_raw(cs->env, variable_assignment->name);
		if (local_index) {
			op_index(cs, OP_SET_LOCAL, value_as_integer(*local_index));
		} else {
			op_string(cs, OP_SET_GLOBAL, variable_assignment->name);
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
		compile(cs, conditional->consequent);
		jump(cs, OP_JUMP, &consequent_to_after);
		size_t alternative = inst_pos(cs);
		compile(cs, conditional->alternative);

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
		compile(cs, loop->body);
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
		Environment *saved_environment = cs->env;
		bool saved_in_block = cs->in_block;
		cs->in_block = true;
		cs->env = env_create(cs->env);
		compile(cs, block->expressions[0]);
		for (size_t i = 1; i < block->expression_cnt; i++) {
			op(cs, OP_DROP);
			compile(cs, block->expressions[i]);
		}
		env_destroy(cs->env);
		cs->env = saved_environment;
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
		.members = {0},
		.in_object = false,
		.in_block = false,
		.in_definition = false,
		.env = env_create(NULL),
		.local_cnt = 0,
	};
	garena_init(&cs.constants);
	garena_init(&cs.instructions);
	garena_init(&cs.members);

	size_t start = garena_save(&cs.instructions);
	env_define(cs.env, STR("this"), make_integer(cs.local_cnt++));
	compile(&cs, ast);
	op(&cs, OP_RETURN);

	size_t instruction_len = garena_cnt_from(&cs.instructions, start, u8);
	u8 *instruction_start = move_to_arena(cs.arena, &cs.instructions, start, u8);
	u16 entry_point = add_constant(&cs, (Constant) {
	       .kind = CK_FUNCTION,
	       .method = (CFunction) {
			.local_cnt = cs.local_cnt - 1,
			.parameter_cnt = 1,
			.instruction_start = instruction_start,
			.instruction_len = instruction_len,
		},
	});

	program->constant_cnt = garena_cnt(&cs.constants, Constant);
	program->constants = move_to_arena(cs.arena, &cs.constants, 0, Constant);

	program->global_class = create_class(&cs, 0);

	program->entry_point = entry_point;

	env_destroy(cs.env);
	garena_destroy(&cs.constants);
	garena_destroy(&cs.instructions);
	garena_destroy(&cs.members);

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
		write_u8(f, constant->method.parameter_cnt);
		write_u16(f, constant->method.local_cnt);
		write_u32(f, constant->method.instruction_len);
		fwrite(constant->method.instruction_start, constant->method.instruction_len, 1, f);
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
	}
	fprintf(os->f, "%*s},\n", indent, "");
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
		CFunction *method = &constant->method;
		fprintf(f, "Function(params: %"PRIi8", locals: %"PRIi8", length: %zu)\n", method->parameter_cnt, method->local_cnt, method->instruction_len);
		u8 *start = method->instruction_start;
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
				i16 offset = read_u16(&ip);
				fprintf(f, "jump %+"PRIi16"=%zu", offset, (size_t)(ip - start) + offset);
				break;
			}
			case OP_BRANCH: {
				i16 offset = read_u16(&ip);
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
	for (size_t i = 0; i < program->constant_cnt; i++) {
		fprintf(f, "%5zu: ", i);
		print_constant(program, i, f, true);
		fprintf(f, "\n");
	}
	fprintf(f, "Entry: #%"PRIu16"\n", program->entry_point);
	fprintf(f, "Globals: ");
	print_members(&program->global_class, program, f);
	fprintf(f, "\n");
}

static void
argument_error(ErrorContext *ec, const char *msg, ...)
{
	va_list ap;
	va_start(ap, msg);
	verror(ec, NULL, "argument", true, msg, ap);
	va_end(ap);
}


Str
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
	size_t fsize = ftell(f);
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

void
print_help(FILE *f)
{
	fprintf(f,
		"Usage:\n"
		"    fml -h                 Print this message.\n"
		"    fml --help             Print this message.\n"
		"    fml help               Print this message.\n"
		"    fml parse FILE         Parse a single expression from fml source FILE.\n"
		"    fml parse_top FILE     Parse a full program from fml source FILE.\n"
		"    fml run_ast FILE       Parse fml source FILE and interpret the AST.\n"
		"    fml run FILE           Parse from fml source FILE, compile it to bytecode and execute it.\n"
		"    fml execute FILE       Parse bytecode from FILE and execut it.\n"
		"    fml compile FILE       Parse fml source FILE and compile it to bytecode\n"
		"    fml disassemble FILE   Parse bytecode from FILE and print bytecode disassembly.\n"
		"    fml dump FILE          Parse fml source FILE, compile it and bytecode disassembly.\n"
	);
}

int
main(int argc, const char **argv) {
	if (argc == 2 && (strcmp(argv[1], "-h") == 0
			|| strcmp(argv[1], "--help") == 0 || strcmp(argv[1], "help") == 0)) {
		print_help(stdout);
		return EXIT_SUCCESS;
	}

	if (argc < 3) {
		fprintf(stderr, "Expected a command and file as arguments\n");
		print_help(stderr);
		return EXIT_FAILURE;
	}

	Arena arena_;
	Arena *arena = &arena_;
	arena_init(arena);

	ErrorContext ec;
	error_context_init(&ec);

	if (setjmp(ec.loc) != 0) {
		goto end;
	}
	Str source = read_file(&ec, arena, argv[2]);

	if (strcmp(argv[1], "parse") == 0) {
		Ast *ast = parse_source(&ec, arena, source);
		if (ast->kind == AST_TOP) {
			ast = ((AstTop *)ast)->expressions[0];
		}
		OutputState os = { .f = stdout };
		write_ast(&os, ast, 4, true);
	} else if (strcmp(argv[1], "parse_top") == 0) {
		Ast *ast = parse_source(&ec, arena, source);
		OutputState os = { .f = stdout };
		write_ast(&os, ast, 4, true);
	} else if (strcmp(argv[1], "run_ast") == 0) {
		Ast *ast = parse_source(&ec, arena, source);
		interpret_ast(&ec, ast);
	} else if (strcmp(argv[1], "run") == 0) {
		Ast *ast = parse_source(&ec, arena, source);
		Program program;
		compile_ast(&ec, arena, &program, ast);
		vm_run(&ec, arena, &program);
	} else if (strcmp(argv[1], "execute") == 0) {
		Program program;
		read_program(&ec, arena, &program, (u8 *) source.str, source.len);
		vm_run(&ec, arena, &program);
	} else if (strcmp(argv[1], "compile") == 0) {
		Ast *ast = parse_source(&ec, arena, source);
		Program program;
		compile_ast(&ec, arena, &program, ast);
		write_program(&program, stdout);
		fflush(stdout);
	} else if (strcmp(argv[1], "disassemble") == 0) {
		Program program;
		read_program(&ec, arena, &program, (u8 *) source.str, source.len);
		disassemble(&program, stdout);
	} else if (strcmp(argv[1], "dump") == 0) {
		Ast *ast = parse_source(&ec, arena, source);
		Program program;
		compile_ast(&ec, arena, &program, ast);
		disassemble(&program, stdout);
	}

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
	arena_destroy(arena);
	return ec.error_head ? EXIT_FAILURE : EXIT_SUCCESS;
}