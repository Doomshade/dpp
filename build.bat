@ECHO OFF
commonvars=--color=always --package dpp --bin dpp
cargo build $commonvars
cargo run $commonvars
cd out/dpp
nasm -f win32 first_simple_example.asm
gcc first_simple_example.obj -g
a.exe
