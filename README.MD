# Dpp

_Better than C++ and D combined because there's D and there's pp_

---

## What is Dpp?

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
> cargo build --release
``` 

Now you can run the compiler:

```shell
> ./target/release/dpp.exe <input_file> <output_file>
```

[//]: # (Or just download the executable)

## Examples

You can find examples in the `examples` folder.

## Grammar

See `grammar.pdf`
