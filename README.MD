# D++ _(Dpp)_

_Better than C++ and D combined because there's D and there's pp_

---

## What is D++?

A KIV/FJP project at UWB Pilsen. The goal is to create a programming language that is better than C++ and D combined.

## Usage

You will need [Rust](https://www.rust-lang.org/) installed on your machine to compile it.

You will either need to clone this repo:

```shell
> git clone https://github.com/Doomshade/dppc.git --depth 1
```

or download `dppc.zip` and extract it.

Then you will need to compile the compiler:

```shell
> cd dppc
> cargo run --release
```

Now you can run the compiler:

```shell
> ./target/release/dppc.exe <input_file> <output_file>
```

[//]: # (Or just download the executable)

## Examples

You can find examples in the `examples` folder.

## Syntax

TODO: Add BNFE

### Keywords

| Keyword  | Description               | Equivalent to |
|----------|---------------------------|---------------|
| `nopp`   | no value                  | `void`        |
| `xxlpp`  | 64 bit number             | `long`        |
| `pp`     | 32 bit number             | `int`         |
| `spp`    | 16 bit number             | `short`       |
| `xspp`   | 8 bit number              | `byte`        |
| `p`      | character                 | `char`        |
| `thread` | String                    | `String`      |
| `boob`   | boolean value             | `bool`        |
| `say`    | Prints a string to stdout | `print`       |
| `yell`   | Prints a string to stderr | `printerr`    |
| `bye`    | Return from a function    | `return`      |

### Grammar

```BNF
<digit> ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
<letter> ::= a | b | c | d | e | f | g | h | i | j | k | l | m | n | o | p
          | q | r | s | t | u | v | w | x | y | z | A | B | C | D | E | F
          | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V
          | W | X | Y | Z
<operator> ::= + | - | * | / | %
<data-type> ::= xxlpp | pp | spp | xspp | nopp | thread | boob | p
<return> ::= bye <expression> ;
<string> ::= " <letter> | <digit> | <operator> | <string> "
<literal> ::= <digit> | <literal> <digit> | <string>
<identifier> ::= <letter> | <identifier> <letter> | <identifier> <digit>
<type> ::= <identifier>
<expression> ::= <literal> | <identifier> | <operator> <expression> | <expression> <operator> <expression> | ( <expression> ) | 
<statement> ::= <expression> | <type> <identifier> = <expression> | <type> <identifier> = <expression> <operator> <expression>
<statements> ::= <statement> | <statements> <statement>
<function> ::= <type> <identifier> ( <type> <identifier> ) <block>
<block> ::= { <statements> }
<program> ::= <function> 
```
