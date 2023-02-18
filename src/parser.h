#pragma once

#include <stddef.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdalign.h>
#include <string.h>

#include "arena.h"

// See the bottom of this file for parser API.

// This header mainly defines the AST emitted by the reference FML parser and
// a few utility types.

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t  i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;

// `Str` is a pair of pointer and length and represents an immutable string. It
// can be constructed from C string literals with the below `STR` macro.
typedef struct {
	const u8 *str;
	size_t len;
} Str;
#define STR(lit) (Str) { .str = (const u8 *) lit, .len = sizeof(lit) - 1 }

// See https://courses.fit.cvut.cz/NI-RUN/specs/ast.html for details about the
// AST.

typedef enum {
	AST_NULL,
	AST_BOOLEAN,
	AST_INTEGER,
	AST_ARRAY,
	AST_OBJECT,
	AST_FUNCTION,
	AST_DEFINITION,
	AST_VARIABLE_ACCESS,
	AST_VARIABLE_ASSIGNMENT,
	AST_INDEX_ACCESS,
	AST_INDEX_ASSIGNMENT,
	AST_FIELD_ACCESS,
	AST_FIELD_ASSIGNMENT,
	AST_FUNCTION_CALL,
	AST_METHOD_CALL,
	AST_CONDITIONAL,
	AST_LOOP,
	AST_PRINT,
	AST_BLOCK,
	AST_TOP,
} AstKind;

typedef struct {
	AstKind kind;
} Ast;

typedef struct {
	Ast base;
} AstNull;

typedef struct {
	Ast base;
	bool value;
} AstBoolean;

typedef struct {
	Ast base;
	i32 value;
} AstInteger;

typedef struct {
	Ast base;
	Ast *size;
	Ast *initializer;
} AstArray;

typedef struct {
	Ast base;
	Ast *extends;
	Ast **members;
	size_t member_cnt;
} AstObject;

typedef struct {
	Ast base;
	Str *parameters;
	size_t parameter_cnt;
	Ast *body;
} AstFunction;

typedef struct {
	Ast base;
	Str name;
	Ast *value;
} AstDefinition;

typedef struct {
	Ast base;
	Str name;
} AstVariableAccess;

typedef struct {
	Ast base;
	Str name;
	Ast *value;
} AstVariableAssignment;

typedef struct {
	Ast base;
	Ast *object;
	Ast *index;
} AstIndexAccess;

typedef struct {
	Ast base;
	Ast *object;
	Ast *index;
	Ast *value;
} AstIndexAssignment;

typedef struct {
	Ast base;
	Ast *object;
	Str field;
} AstFieldAccess;

typedef struct {
	Ast base;
	Ast *object;
	Str field;
	Ast *value;
} AstFieldAssignment;

typedef struct {
	Ast base;
	Ast *function;
	Ast **arguments;
	size_t argument_cnt;
} AstFunctionCall;

typedef struct {
	Ast base;
	Ast* object;
	Str name;
	Ast **arguments;
	size_t argument_cnt;
} AstMethodCall;

typedef struct {
	Ast base;
	Ast *condition;
	Ast *consequent;
	Ast *alternative;
} AstConditional;

typedef struct {
	Ast base;
	Ast *condition;
	Ast *body;
} AstLoop;

typedef struct {
	Ast base;
	Str format;
	Ast **arguments;
	size_t argument_cnt;
} AstPrint;

typedef struct {
	Ast base;
	Ast **expressions;
	size_t expression_cnt;
} AstBlock;

typedef struct {
	Ast base;
	Ast **expressions;
	size_t expression_cnt;
} AstTop;

// Parser takes a source code (`Str`) as input and produces AST (`Ast`) as an
// output. The function `parse` is the most general way of using the parser. It
// receives an `Arena` in which the `Ast` will be allocated (the user is
// responsible for deallocation) and `GArena` which will be used as scratch
// space (parser may allocate in it, but returns it to the previous state).
//
// In case of any encountered errors, `NULL` is ultimately returned, errors are
// reported to the caller with a callback function and the space allocated in
// the `Arena` by the parser is deallocated (restored to the state at the start
// of parsing).
//
// For simplicity, the `parse_src` function can be used instead. It uses the
// predefined example `parser_error_cb` callback, which is defined to report
// errors to standard error (see it also for details about the callback
// behavior).

Ast *parse_src(Arena *arena, Str source);

Ast *parse(
	Arena *arena,
	GArena *scratch,
	Str source,
	void (*error_callback)(
		void *user_data,
		const u8 *err_pos,
		const char *msg,
		va_list ap
	),
	void *user_data
);

void parser_error_cb(
	void *user_data,
	const u8 *err_pos,
	const char *msg,
	va_list ap
);
