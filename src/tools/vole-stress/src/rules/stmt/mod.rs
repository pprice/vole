//! Statement rule registration.
//!
//! Each statement rule struct is listed in [`all`] -- the single source of
//! truth for which statement rules exist.  Adding a new rule means creating
//! its implementation file and adding one line here.

use crate::rule::StmtRule;

/// Return every registered statement rule.
///
/// Rules are listed explicitly (no inventory magic) so that the set of active
/// rules is visible at a glance.
pub fn all() -> Vec<Box<dyn StmtRule>> {
    vec![]
}
