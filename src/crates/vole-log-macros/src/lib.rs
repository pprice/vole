//! Proc macros for Vole compiler timing instrumentation.
//!
//! Provides `#[compile_timed]` which expands to a `#[tracing::instrument]`
//! attribute targeting the `vole::compile_timing` span target.
//!
//! # Usage
//!
//! ```ignore
//! #[compile_timed(DEBUG)]
//! fn lower_test_bodies(...) { ... }
//!
//! #[compile_timed(TRACE, fields(name = %display_name))]
//! fn compile_function(...) { ... }
//! ```

use proc_macro::TokenStream;
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{Ident, Token, parse_macro_input};

/// Parsed arguments for `#[compile_timed(LEVEL, fields(...))]`.
struct CompileTimedArgs {
    level: Ident,
    fields: Option<proc_macro2::TokenStream>,
}

impl Parse for CompileTimedArgs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let level: Ident = input.parse()?;

        // Validate the level identifier
        let level_str = level.to_string();
        if !matches!(
            level_str.as_str(),
            "TRACE" | "DEBUG" | "INFO" | "WARN" | "ERROR"
        ) {
            return Err(syn::Error::new(
                level.span(),
                format!(
                    "expected tracing level (TRACE, DEBUG, INFO, WARN, ERROR), found `{level_str}`"
                ),
            ));
        }

        let fields = if input.peek(Token![,]) {
            input.parse::<Token![,]>()?;

            // Expect `fields(...)`
            let fields_ident: Ident = input.parse()?;
            if fields_ident != "fields" {
                return Err(syn::Error::new(
                    fields_ident.span(),
                    format!("expected `fields`, found `{fields_ident}`"),
                ));
            }

            let content;
            syn::parenthesized!(content in input);
            let tokens: proc_macro2::TokenStream = content.parse()?;
            Some(tokens)
        } else {
            None
        };

        Ok(CompileTimedArgs { level, fields })
    }
}

/// Attribute macro that expands to `#[tracing::instrument(...)]` with the
/// `vole::compile_timing` target.
///
/// # Arguments
///
/// - Level: `TRACE`, `DEBUG`, `INFO`, `WARN`, or `ERROR`
/// - Optional fields: `fields(name = %display_name, path = %file_path)`
///
/// # Examples
///
/// ```ignore
/// #[compile_timed(DEBUG)]
/// fn lower_test_bodies(...) { ... }
///
/// #[compile_timed(TRACE, fields(name = %display_name))]
/// fn compile_function(...) { ... }
/// ```
#[proc_macro_attribute]
pub fn compile_timed(attr: TokenStream, item: TokenStream) -> TokenStream {
    let args = parse_macro_input!(attr as CompileTimedArgs);
    let item = proc_macro2::TokenStream::from(item);

    let level_str = args.level.to_string().to_lowercase();
    let level_lit = syn::LitStr::new(&level_str, args.level.span());

    let output = if let Some(fields) = args.fields {
        quote! {
            #[tracing::instrument(
                target = "vole::compile_timing",
                level = #level_lit,
                skip_all,
                fields(#fields)
            )]
            #item
        }
    } else {
        quote! {
            #[tracing::instrument(
                target = "vole::compile_timing",
                level = #level_lit,
                skip_all,
            )]
            #item
        }
    };

    output.into()
}
