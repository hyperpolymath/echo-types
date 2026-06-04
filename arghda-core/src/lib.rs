// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! arghda-core: proof-workspace manager for Agda.
//!
//! Public surface is intentionally small: `Workspace`, the lint traits,
//! and the diagnostic types. The CLI in `main.rs` is a thin consumer.

pub mod diagnostic;
pub mod lint;
pub mod watcher;
pub mod workspace;

pub use diagnostic::{Diagnostic, LintReport, Severity};
pub use lint::{LintRule, default_rules, run_lints};
pub use workspace::{State, Workspace};
