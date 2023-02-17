#pragma once

#include <stddef.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdalign.h>
#include <string.h>

#include "arena.h"

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t  i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;

typedef struct {
	const u8 *str;
	size_t len;
} Str;
#define STR(lit) (Str) { .str = (const u8 *) lit, .len = sizeof(lit) - 1 }

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
