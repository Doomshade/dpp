use crate::parse::parser::TranslationUnit;

trait Emitter<'a, T>
where
    T: std::io::Write,
{
    fn emit_all(
        &mut self,
        writer: std::io::BufWriter<T>,
        translation_unit: TranslationUnit,
    ) -> std::io::Result<()>;
}

pub mod emitter;
