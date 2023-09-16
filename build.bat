@ECHO OFF
commonvars=--color=always --package dpp --bin dpp
cargo build $commonvars
cargo run $commonvars
cd out/dpp
nasm -f win32 -o oof.obj first_simple_example.asm
gcc oof.obj -o hello_world.exe