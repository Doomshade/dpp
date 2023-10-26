use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;

use quote::{quote, quote_spanned};
use syn;
use syn::spanned::Spanned;
use syn::{Data, Fields};

#[proc_macro_derive(Pos)]
pub fn pos_macro_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();
    impl_pos_macro(&ast)
}

fn impl_pos_macro(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;
    match &ast.data {
        Data::Enum(data_enum) => {
            let mut pos_functions = TokenStream2::new();

            for variant in &data_enum.variants {
                let variant_name = &variant.ident;
                let fields_in_variant = match &variant.fields {
                    Fields::Unnamed(_) => quote_spanned! {variant.span()=> (..) },
                    Fields::Unit => quote_spanned! { variant.span()=> },
                    Fields::Named(_) => quote_spanned! {variant.span()=> {position, ..} },
                };

                let function = quote_spanned! {
                    variant.span() => #name::#variant_name #fields_in_variant => *position,
                };

                pos_functions.extend(function);
            }

            let gen = quote! {
                impl<'a> Pos for #name<'a> {

                    #[must_use]
                    fn position(&self) -> (u32, u32) {
                        match self {
                            #pos_functions
                        }
                    }
                }
            };
            gen.into()
        }
        Data::Struct(_) => {
            let gen = quote! {
                impl<'a> Pos for #name<'a> {
                    #[must_use]
                    fn position(&self) -> (u32, u32) {
                        self.position
                    }
                }
            };
            gen.into()
        }
        Data::Union(_) => {
            todo!("Not implemented for union");
        }
    }
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
