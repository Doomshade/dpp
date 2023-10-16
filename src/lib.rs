use proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use syn;

#[proc_macro_derive(PositionalMacro)]
pub fn positional_macro_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();

    impl_positional_macro(&ast)
}

fn impl_positional_macro(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let gen = quote!{
        impl PositionalMacro for #name {
            fn row(&self) -> u32 {
                self.position.0
            }
            fn col(&self) -> u32 {
                self.position.1
            }
        }
    };

    gen.into()
}
