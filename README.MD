# D++ _(Dpp)_

_Better than C++ and D combined because there's D and there's pp_

---

## What is D++?

A KIV/FJP project at UWB Pilsen. The goal is to create a programming language that is better than C++ and D combined.

## Usage

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

## Examples

You can find examples in the `examples` folder.

## Syntax

### Keywords

| Keyword   | Description               | Equivalent to |
|-----------|---------------------------|---------------|
| `nogf`    | void                      | `void`        |
| `bigpp`   | 64 bit number             | `long`        |
| `pp`      | 32 bit number             | `int`         |
| `smolpp`  | 16 bit number             | `short`       |
| `tinypp`  | 8 bit number              | `byte`        |
| `gfsays`  | Prints a string to stdout | `print`       |
| `gfyells` | Prints a string to stderr | `printerr`    |
| `bye`     | Prints a string to stderr | `printerr`    |
