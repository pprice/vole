//! Expression rule registration.
//!
//! Each expression rule struct is listed in [`all`] -- the single source of
//! truth for which expression rules exist.  Adding a new rule means creating
//! its implementation file and adding one line here.

use crate::rule::ExprRule;

/// Return every registered expression rule.
///
/// Rules are listed explicitly (no inventory magic) so that the set of active
/// rules is visible at a glance.
pub fn all() -> Vec<Box<dyn ExprRule>> {
    vec![]
}
