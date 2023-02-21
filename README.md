# FML

This is an implementation of FML, written in C11, as of 2023 serving as a
reference implementation for the language. The canonical repository is
https://gitlab.fit.cvut.cz/vlasami6/cfml.

The language itself is created for teaching about runtime systems and their
implementations in the
[NI-RUN course at FIT CTU](https://courses.fit.cvut.cz/NI-RUN), see
[the specification](https://courses.fit.cvut.cz/NI-RUN/specs/fml.html) for more
information about the language.

Some parts of the reference implementation (the parser and AST definition) are
used by the
[template repository](https://courses.fit.cvut.cz/NI-RUN/tasks/index.html#template-repository)
(https://gitlab.fit.cvut.cz/vlasami6/ni-run-template).

The reference implementation is meant to cross check student implementations
through
[FMLtest](https://courses.fit.cvut.cz/NI-RUN/tasks/index.html#template-repository)
(https://github.com/kondziu/FMLtest).

## Downloading

Clone the repository with git over https:

```
git clone https://gitlab.fit.cvut.cz/vlasami6/cfml.git
```

or through ssh:

```
git clone git@gitlab.fit.cvut.cz:vlasami6/cfml.git
```

or if you fancy SSH aliases:

```
# .ssh/config
Host fitlab
        HostName gitlab.fit.cvut.cz
        User git
```

```
git clone fitlab:vlasami6/cfml
```


## Building

`cfml` uses the [Meson](https://mesonbuild.com/) build system. A release build
can be compiled with:

```
meson setup builddir --buildtype release
meson compile -C builddir
```

An `fml` binary is then built at `builddir/fml`. All build artifacts are
contained in the `builddir` directory (you are free to choose any other name)
and can be safely deleted.

Or more simply:

```
gcc -O2 -o fml src/*.c
```

Customize compile flags as you like.

## Installation

You can just copy the built file. It's all there is anyway.

Or you can use `meson install` at your own risk.

## Usage

The binary has several subcommands that instruct it on what to do. You should start with `help`:

```
builddir/fml help
```

Which shows:

```
USAGE:
    fml SUBCOMMAND [OPTIONS] [ARGS]

SUBCOMMANDS:
    run               Run a program with the bytecode interpreter
    bc_compile        Compile a program to bytecode
    bc_interpret      Interpret bytecode
    bc_disassemble    Disassemble bytecode
    bc_dump           Compile program and print disassembly
    ast_interpret     Run a program with AST interpreter
    parse             Parse a source file and print it as AST
    help              Get help about fml or subcommand
```

Some commands can be further customized with "options" (`--option`), some have
arguments (`--option argument`). Commands also take positional arguments (after
options), for most commands this is a path of file to act on. Use `fml help
subcommand` to learn more about some subcommand. E.g.

```
builddir/fml help run
```

Brief description of commands, their help messages and examples of use on the
following file `example.fml` are below.

```
// example.fml
print("1 + 1 = ~\n", 1 + 1);
```

### run

Take a FML source file and run it. (Through bytecode compilation and
interpretation.)

```
USAGE:
    fml run [OPTIONS] FILE

ARGS:
    FILE    The file to run

OPTIONS:
    --heap-log LOG_FILE   Heap log file, if none no logging is done
    --heap-size MBs       Maximum heap size in mebibytes
```

Example:

```
$ builddir/fml run example.fml
1 + 2 = 3
```

### bc_compile

Take a FML source file, compile it to bytecode and serialize the bytecode into standard output.

```
USAGE:
    fml bc_compile FILE

ARGS:
    FILE    The source file to compile to bytecode
```

Example:

```
$ builddir/fml bc_compile example.fml > example.bc
$ hexdump -C example.bc
00000000  06 00 00 01 00 00 00 00  02 00 00 00 02 01 00 00  |................|
00000010  00 2b 02 01 00 00 00 61  02 0b 00 00 00 31 20 2b  |.+.....a.....1 +|
00000020  20 32 20 3d 20 7e 5c 6e  03 01 00 00 16 00 00 00  | 2 = ~\n........|
00000030  01 00 00 01 01 00 07 02  00 02 0b 03 00 00 0c 03  |................|
00000040  00 02 04 00 01 0f 01 00  03 00 05 00              |............|
0000004c
```

### bc_interpret

Take a bytecode file as an argument and run it with the bytecode interpreter.

```
USAGE:
    fml bc_interpret FILE

ARGS:
    FILE    The bytecode file to interpret
```

Example:

```
$ builddir/fml bc_interpret example.bc
1 + 2 = 3
```

### bc_disassemble

Take a bytecode file as an argument and output it's human readable
representation ("disassembly") to standard output.

```
USAGE:
    fml bc_disassemble FILE

ARGS:
    FILE    The bytecode file to disassemble
```

Example:

```
$ builddir/fml bc_disassemble example.bc
Constant Pool:
    0: 1
    1: 2
    2: "+"
    3: "a"
    4: "1 + 2 = ~\n"
    5: Function(params: 1, locals: 0, length: 22)
                 0: constant #0=1
                 3: constant #1=2
                 6: call method #2="+" 2
                10: set global #3="a"
                13: drop
                14: get global #3="a"
                17: print #4="1 + 2 = ~\n" 1
                21: return
Entry: #5
Globals: #3="a"
```

### bc_dump

Take a FML source file as an argument, compile it to bytecode and print human
readable representation ("disassembly") of the bytecode to standard output.

```
USAGE:
    fml bc_dump FILE

ARGS:
    FILE    The source file to compile and disassemble
```

Example:

```
$ builddir/fml bc_dump example.fml
Constant Pool:
    0: 1
    1: 2
    2: "+"
    3: "a"
    4: "1 + 2 = ~\n"
    5: Function(params: 1, locals: 0, length: 22)
                 0: constant #0=1
                 3: constant #1=2
                 6: call method #2="+" 2
                10: set global #3="a"
                13: drop
                14: get global #3="a"
                17: print #4="1 + 2 = ~\n" 1
                21: return
Entry: #5
Globals: #3="a"
```

### `ast_interpret`

Take a FML source file as an argument and run it with the AST interpreter.

```
USAGE:
    fml ast_interpret FILE

ARGS:
    FILE    The source file to interpret with AST interpreter
```

```
$ builddir/fml ast_interpret example.fml
1 + 2 = 3
```

### `parse`

Parse an FML source file and print it's AST as C99 designated initializers to
standard output. Only first expression printed by default. Use `--top` to print
the full AST.

```
USAGE:
    fml parse [OPTIONS] FILE

ARGS:
    FILE    The file to parse

OPTIONS:
    --top   Parse whole program, not just single expression
```

Example:

```
$ builddir/fml parse example.fml
(AstDefinition) {
    .base = (Ast) { .kind = AST_DEFINITION },
    .name = STR("a"),
    .value = &(AstMethodCall) {
        .base = (Ast) { .kind = AST_METHOD_CALL },
        .object = &(AstInteger) {
            .base = (Ast) { .kind = AST_INTEGER },
            .value = 1,
        }.base,
        .name = STR("+"),
        .arguments = (Ast*[]) {
            &(AstInteger) {
                .base = (Ast) { .kind = AST_INTEGER },
                .value = 2,
            }.base,
        },
        .argument_cnt = 1,
    }.base,
}
```

```
$ builddir/fml parse --top example.fml
(AstTop) {
    .base = (Ast) { .kind = AST_TOP },
    .expressions = (Ast*[]) {
        &(AstDefinition) {
            .base = (Ast) { .kind = AST_DEFINITION },
            .name = STR("a"),
            .value = &(AstMethodCall) {
                .base = (Ast) { .kind = AST_METHOD_CALL },
                .object = &(AstInteger) {
                    .base = (Ast) { .kind = AST_INTEGER },
                    .value = 1,
                }.base,
                .name = STR("+"),
                .arguments = (Ast*[]) {
                    &(AstInteger) {
                        .base = (Ast) { .kind = AST_INTEGER },
                        .value = 2,
                    }.base,
                },
                .argument_cnt = 1,
            }.base,
        }.base,
        &(AstPrint) {
            .base = (Ast) { .kind = AST_PRINT },
            .format = STR("1 + 2 = ~\\n"),
            .arguments = (Ast*[]) {
                &(AstVariableAccess) {
                    .base = (Ast) { .kind = AST_VARIABLE_ACCESS },
                    .name = STR("a"),
                }.base,
            },
            .argument_cnt = 1,
        }.base,
    },
    .expression_cnt = 2,
}
```
