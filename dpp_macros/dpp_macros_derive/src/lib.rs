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
            let mut variant_checker_functions = TokenStream2::new();

            for variant in &data_enum.variants {
                let variant_name = &variant.ident;

                let fields_in_variant = match &variant.fields {
                    Fields::Unnamed(_) => quote_spanned! {variant.span()=> (..) },
                    Fields::Unit => quote_spanned! { variant.span()=> },
                    Fields::Named(_) => quote_spanned! {variant.span()=> {..} },
                };

                variant_checker_functions.extend(quote_spanned! {
                    variant.span() => {

                    #[must_use]
                    fn row(&self) -> u32 {
                        match self {
                                #name::#variant_name #fields_in_variant => {
                                    &#variant_name.position
                                }
                            }
                    }

                    #[must_use]
                    fn col(&self) -> u32 {
                        self.position.1
                    }
                    }
                })
            }

            let gen = quote! {
                impl<'a> PosMacro for #name<'a> {
                    #variant_checker_functions
                }
            };
            gen.into()
        }
        Data::Struct(_) => {
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
