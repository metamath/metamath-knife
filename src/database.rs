#[derive(Default,Debug)]
pub struct DbOptions {
    pub autosplit: bool,
    pub jobs: u32,
    pub timing: bool,
    pub verify: bool,
}
