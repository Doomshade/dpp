use crate::parse::parser::TranslationUnit;

trait Emitter<'a, T>
where
    T: std::io::Write,
{
    fn emit_all(
        &mut self,
        writer: &mut std::io::BufWriter<T>,
        translation_unit: TranslationUnit<'a>,
    ) -> std::io::Result<()>;
}

pub mod emitter;
