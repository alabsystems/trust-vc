//! The TLC configuration of a protocol obligation, read by this lane.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! A success is `Verified` only for the spec as written, so the config may
//! select what is checked and nothing else. ty's own config reader takes more,
//! and a success on it was a success of another model: `CONSTRAINT`,
//! `ACTION_CONSTRAINT`, `VIEW` and `SYMMETRY` explore part of the state
//! space, `CONSTANT Op <- Other` replaces a definition, a second `INIT` or
//! `NEXT` replaces the first, and a `NEXT` block keeps only its first line.
//! This reader admits none of that, nor any other directive, and the file
//! `ty` reads is written from what it admitted ([`Request::canonical`]),
//! never the obligation's own text. That each name is an operator the module
//! defines without parameters is checked against what `ty` read
//! (`source.units`, in [`super::document`]).

/// What an obligation asks `ty` to check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Request {
    pub(super) init: String,
    pub(super) next: String,
    pub(super) invariants: Vec<String>,
    pub(super) properties: Vec<String>,
    /// `CHECK_DEADLOCK` when given; `ty`, like TLC, checks deadlock otherwise.
    pub(super) check_deadlock: Option<bool>,
}

impl Request {
    /// Read a config: `INIT <name>` and `NEXT <name>` once each, one or more
    /// `INVARIANT <name>` or `PROPERTY <name>` lines, and at most one
    /// `CHECK_DEADLOCK TRUE|FALSE`, each on its own line. Every name is a
    /// TLA+ identifier.
    pub(super) fn parse(text: &str) -> Result<Self, String> {
        let mut init = None;
        let mut next = None;
        let mut check_deadlock = None;
        let mut invariants = Vec::new();
        let mut properties = Vec::new();
        for line in text.lines() {
            let (directive, value) = match line.split_whitespace().collect::<Vec<_>>()[..] {
                [] => continue,
                [directive, value] => (directive, value),
                _ => return Err(format!("`{}` is not `<DIRECTIVE> <name>`", line.trim())),
            };
            match directive {
                "INIT" => once(&mut init, identifier(value)?, directive)?,
                "NEXT" => once(&mut next, identifier(value)?, directive)?,
                "INVARIANT" => invariants.push(identifier(value)?),
                "PROPERTY" => properties.push(identifier(value)?),
                "CHECK_DEADLOCK" => {
                    let check = match value {
                        "TRUE" => true,
                        "FALSE" => false,
                        _ => return Err(format!("CHECK_DEADLOCK `{value}` is not TRUE or FALSE")),
                    };
                    once(&mut check_deadlock, check, directive)?;
                }
                _ => {
                    return Err(format!(
                        "`{directive}` is not a directive this lane reads (INIT, NEXT, INVARIANT, \
                         PROPERTY, CHECK_DEADLOCK)"
                    ))
                }
            }
        }
        let (Some(init), Some(next)) = (init, next) else {
            return Err("the config names no INIT or no NEXT".to_string());
        };
        if invariants.is_empty() && properties.is_empty() {
            return Err(
                "the config names no INVARIANT or PROPERTY: nothing would be checked".to_string(),
            );
        }
        Ok(Self {
            init,
            next,
            invariants,
            properties,
            check_deadlock,
        })
    }

    /// The config file `ty` reads, one directive per line.
    pub(super) fn canonical(&self) -> String {
        let mut text = format!("INIT {}\nNEXT {}\n", self.init, self.next);
        for name in &self.invariants {
            text.push_str(&format!("INVARIANT {name}\n"));
        }
        for name in &self.properties {
            text.push_str(&format!("PROPERTY {name}\n"));
        }
        if let Some(check) = self.check_deadlock {
            text.push_str(if check {
                "CHECK_DEADLOCK TRUE\n"
            } else {
                "CHECK_DEADLOCK FALSE\n"
            });
        }
        text
    }

    /// Every operator the config names.
    pub(super) fn names(&self) -> impl Iterator<Item = &str> {
        [&self.init, &self.next]
            .into_iter()
            .chain(&self.invariants)
            .chain(&self.properties)
            .map(String::as_str)
    }
}

fn once<T>(slot: &mut Option<T>, value: T, directive: &str) -> Result<(), String> {
    if slot.replace(value).is_some() {
        return Err(format!("{directive} is given more than once"));
    }
    Ok(())
}

/// `name`, when it is a TLA+ identifier: letters, digits and `_`, with a
/// letter. The config `ty` reads is written from these names.
fn identifier(name: &str) -> Result<String, String> {
    let identifier = name.chars().all(|c| c == '_' || c.is_ascii_alphanumeric())
        && name.chars().any(|c| c.is_ascii_alphabetic());
    if identifier {
        Ok(name.to_string())
    } else {
        Err(format!("`{name}` is not a TLA+ identifier"))
    }
}
