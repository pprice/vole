use vergen::{BuildBuilder, CargoBuilder, Emitter};
use vergen_gitcl::GitclBuilder;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let build = BuildBuilder::default().build_date(true).build()?;

    let cargo = CargoBuilder::default()
        .debug(true)
        .target_triple(true)
        .build()?;

    let gitcl = GitclBuilder::default().sha(true).dirty(true).build()?;

    Emitter::default()
        .add_instructions(&build)?
        .add_instructions(&cargo)?
        .add_instructions(&gitcl)?
        .emit()?;

    Ok(())
}
