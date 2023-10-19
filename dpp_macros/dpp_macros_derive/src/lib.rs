use proc_macro::TokenStream;

use quote::quote;
use syn;

#[proc_macro_derive(PosMacro)]
pub fn pos_macro_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();
    impl_pos_macro(&ast)
}

fn impl_pos_macro(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let gen = quote! {
        impl<'a> PosMacro for #name<'a> {
            #[must_use]
            fn row(&self) -> u32 {
                self.position.0
            }

            #[must_use]
            fn col(&self) -> u32 {
                self.position.1
            }
        }
    };
    gen.into()
}

#[proc_macro_derive(HelloMacro)]
pub fn hello_macro_derive(input: TokenStream) -> TokenStream {
    // Construct a representation of Rust code as a syntax tree
    // that we can manipulate
    let ast = syn::parse(input).unwrap();

    // Build the trait implementation
    impl_hello_macro(&ast)
}

fn impl_hello_macro(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let gen = quote! {
        impl<'a> HelloMacro for #name<'a> {
            fn hello_macro() {
                println!("Hello, Macro! My name is {}!", stringify!(#name));
            }
        }
    };
    gen.into()
}
