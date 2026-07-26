// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::format::{format_function_line, format_generics, format_type};
use super::ApiSurfaceError;
use rustdoc_types::{
    Id, Impl, Item, ItemEnum, MacroKind, Struct, StructKind, Trait, Use, VariantKind, Visibility,
};
use std::collections::BTreeSet;

pub(super) struct ApiSurfaceCollector<'a> {
    krate: &'a rustdoc_types::Crate,
    lines: BTreeSet<String>,
    visited_modules: BTreeSet<(Id, String)>,
}

impl<'a> ApiSurfaceCollector<'a> {
    pub(super) fn new(krate: &'a rustdoc_types::Crate) -> Self {
        Self {
            krate,
            lines: BTreeSet::new(),
            visited_modules: BTreeSet::new(),
        }
    }

    pub(super) fn collect(mut self, crate_root: &str) -> Result<Vec<String>, ApiSurfaceError> {
        self.traverse_module(self.krate.root, crate_root, true)?;
        Ok(self.lines.into_iter().collect())
    }

    fn traverse_module(
        &mut self,
        module_id: Id,
        module_path: &str,
        is_root: bool,
    ) -> Result<(), ApiSurfaceError> {
        if !self
            .visited_modules
            .insert((module_id, module_path.to_owned()))
        {
            return Ok(());
        }

        let module_item = self.item(module_id)?.clone();
        let ItemEnum::Module(module) = module_item.inner else {
            return Err(ApiSurfaceError::UnexpectedItemKind {
                context: "module",
                id: module_id,
            });
        };

        if !is_root && !module.is_stripped {
            self.lines.insert(format!("module {module_path}"));
        }
        for child_id in module.items {
            self.process_public_item(child_id, module_path)?;
        }
        Ok(())
    }

    fn process_public_item(
        &mut self,
        item_id: Id,
        parent_path: &str,
    ) -> Result<(), ApiSurfaceError> {
        let item = self.item(item_id)?.clone();
        if !is_public_visibility(&item.visibility) {
            return Ok(());
        }

        match &item.inner {
            ItemEnum::Module(module) => {
                if module.is_stripped {
                    return Ok(());
                }
                let path = join_path(parent_path, self.item_name(&item, "module")?);
                self.traverse_module(item.id, &path, false)
            }
            ItemEnum::Use(use_item) => self.process_use(use_item, parent_path),
            ItemEnum::Struct(struct_) => {
                let path = join_path(parent_path, self.item_name(&item, "struct")?);
                self.record_struct(&path, struct_)
            }
            ItemEnum::Union(union_) => {
                let path = join_path(parent_path, self.item_name(&item, "union")?);
                self.lines.insert(format!(
                    "union {}{}",
                    path,
                    format_generics(&union_.generics)
                ));
                self.record_plain_fields(&path, &union_.fields)?;
                self.record_inherent_items(&path, &union_.impls)
            }
            ItemEnum::Enum(enum_) => {
                let path = join_path(parent_path, self.item_name(&item, "enum")?);
                self.lines
                    .insert(format!("enum {}{}", path, format_generics(&enum_.generics)));
                for variant_id in &enum_.variants {
                    self.record_variant(*variant_id, &path)?;
                }
                self.record_inherent_items(&path, &enum_.impls)
            }
            ItemEnum::Trait(trait_) => {
                let path = join_path(parent_path, self.item_name(&item, "trait")?);
                self.lines.insert(format!(
                    "trait {}{}",
                    path,
                    format_generics(&trait_.generics)
                ));
                self.record_trait_items(&path, trait_)
            }
            ItemEnum::TraitAlias(trait_alias) => {
                let path = join_path(parent_path, self.item_name(&item, "trait alias")?);
                self.lines.insert(format!(
                    "trait_alias {}{}",
                    path,
                    format_generics(&trait_alias.generics)
                ));
                Ok(())
            }
            ItemEnum::Function(function) => {
                let path = join_path(parent_path, self.item_name(&item, "function")?);
                self.lines.insert(format_function_line(&path, function));
                Ok(())
            }
            ItemEnum::TypeAlias(type_alias) => {
                let path = join_path(parent_path, self.item_name(&item, "type alias")?);
                self.lines.insert(format!(
                    "type {}{} = {}",
                    path,
                    format_generics(&type_alias.generics),
                    format_type(&type_alias.type_)
                ));
                Ok(())
            }
            ItemEnum::Constant { type_, .. } => {
                let path = join_path(parent_path, self.item_name(&item, "const")?);
                self.lines
                    .insert(format!("const {path}: {}", format_type(type_)));
                Ok(())
            }
            ItemEnum::Static(static_) => {
                let path = join_path(parent_path, self.item_name(&item, "static")?);
                let keyword = if static_.is_mutable {
                    "static mut"
                } else {
                    "static"
                };
                self.lines
                    .insert(format!("{keyword} {path}: {}", format_type(&static_.type_)));
                Ok(())
            }
            ItemEnum::ProcMacro(proc_macro) => {
                let path = join_path(parent_path, self.item_name(&item, "proc macro")?);
                let line = match proc_macro.kind {
                    MacroKind::Bang => format!("proc_macro {path}!"),
                    MacroKind::Attr => format!("proc_macro_attribute {path}"),
                    MacroKind::Derive => format!("proc_macro_derive {path}"),
                };
                self.lines.insert(line);
                Ok(())
            }
            ItemEnum::Macro(_) => {
                let path = join_path(parent_path, self.item_name(&item, "macro")?);
                self.lines.insert(format!("macro {path}"));
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn process_use(&mut self, use_item: &Use, parent_path: &str) -> Result<(), ApiSurfaceError> {
        if use_item.is_glob {
            self.lines
                .insert(format!("pub use {parent_path}::{}::*", use_item.source));
            return Ok(());
        }

        let alias_path = join_path(parent_path, &use_item.name);
        self.lines
            .insert(format!("pub use {alias_path} = {}", use_item.source));
        if let Some(target_id) = use_item.id {
            self.record_reexport_target(target_id, &alias_path)?;
        }
        Ok(())
    }

    fn record_reexport_target(
        &mut self,
        target_id: Id,
        alias_path: &str,
    ) -> Result<(), ApiSurfaceError> {
        let Some(item) = self.krate.index.get(&target_id).cloned() else {
            return if self.krate.paths.contains_key(&target_id) {
                Ok(())
            } else {
                Err(ApiSurfaceError::MissingItem { id: target_id })
            };
        };
        match &item.inner {
            ItemEnum::Module(_) => self.traverse_module(target_id, alias_path, false),
            ItemEnum::Struct(struct_) => self.record_struct(alias_path, struct_),
            ItemEnum::Union(union_) => {
                self.lines.insert(format!(
                    "union {}{}",
                    alias_path,
                    format_generics(&union_.generics)
                ));
                self.record_plain_fields(alias_path, &union_.fields)?;
                self.record_inherent_items(alias_path, &union_.impls)
            }
            ItemEnum::Enum(enum_) => {
                self.lines.insert(format!(
                    "enum {}{}",
                    alias_path,
                    format_generics(&enum_.generics)
                ));
                for variant_id in &enum_.variants {
                    self.record_variant(*variant_id, alias_path)?;
                }
                self.record_inherent_items(alias_path, &enum_.impls)
            }
            ItemEnum::Trait(trait_) => {
                self.lines.insert(format!(
                    "trait {}{}",
                    alias_path,
                    format_generics(&trait_.generics)
                ));
                self.record_trait_items(alias_path, trait_)
            }
            ItemEnum::TraitAlias(trait_alias) => {
                self.lines.insert(format!(
                    "trait_alias {}{}",
                    alias_path,
                    format_generics(&trait_alias.generics)
                ));
                Ok(())
            }
            ItemEnum::Function(function) => {
                self.lines
                    .insert(format_function_line(alias_path, function));
                Ok(())
            }
            ItemEnum::TypeAlias(type_alias) => {
                self.lines.insert(format!(
                    "type {}{} = {}",
                    alias_path,
                    format_generics(&type_alias.generics),
                    format_type(&type_alias.type_)
                ));
                Ok(())
            }
            ItemEnum::Constant { type_, .. } => {
                self.lines
                    .insert(format!("const {alias_path}: {}", format_type(type_)));
                Ok(())
            }
            ItemEnum::Static(static_) => {
                let keyword = if static_.is_mutable {
                    "static mut"
                } else {
                    "static"
                };
                self.lines.insert(format!(
                    "{keyword} {alias_path}: {}",
                    format_type(&static_.type_)
                ));
                Ok(())
            }
            ItemEnum::ProcMacro(proc_macro) => {
                let line = match proc_macro.kind {
                    MacroKind::Bang => format!("proc_macro {alias_path}!"),
                    MacroKind::Attr => format!("proc_macro_attribute {alias_path}"),
                    MacroKind::Derive => format!("proc_macro_derive {alias_path}"),
                };
                self.lines.insert(line);
                Ok(())
            }
            ItemEnum::Macro(_) => {
                self.lines.insert(format!("macro {alias_path}"));
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn record_struct(&mut self, path: &str, struct_: &Struct) -> Result<(), ApiSurfaceError> {
        self.lines.insert(format!(
            "struct {}{}",
            path,
            format_generics(&struct_.generics)
        ));
        match &struct_.kind {
            StructKind::Unit => {}
            StructKind::Plain { fields, .. } => self.record_plain_fields(path, fields)?,
            StructKind::Tuple(fields) => {
                for (index, field_id) in fields.iter().enumerate() {
                    if let Some(field_id) = field_id {
                        self.record_field(*field_id, &format!("{path}::{index}"))?;
                    }
                }
            }
        }
        self.record_inherent_items(path, &struct_.impls)
    }

    fn record_plain_fields(
        &mut self,
        parent_path: &str,
        fields: &[Id],
    ) -> Result<(), ApiSurfaceError> {
        for field_id in fields {
            let field = self.item(*field_id)?.clone();
            if !is_public_visibility(&field.visibility) {
                continue;
            }
            let name = self.item_name(&field, "field")?;
            self.record_field(*field_id, &join_path(parent_path, name))?;
        }
        Ok(())
    }

    fn record_field(&mut self, field_id: Id, field_path: &str) -> Result<(), ApiSurfaceError> {
        let field = self.item(field_id)?.clone();
        let ItemEnum::StructField(type_) = field.inner else {
            return Err(ApiSurfaceError::UnexpectedItemKind {
                context: "field",
                id: field_id,
            });
        };
        self.lines
            .insert(format!("field {field_path}: {}", format_type(&type_)));
        Ok(())
    }

    fn record_variant(&mut self, variant_id: Id, enum_path: &str) -> Result<(), ApiSurfaceError> {
        let variant_item = self.item(variant_id)?.clone();
        if !is_public_visibility(&variant_item.visibility) {
            return Ok(());
        }

        let variant_name = self.item_name(&variant_item, "variant")?.to_owned();
        let ItemEnum::Variant(variant) = &variant_item.inner else {
            return Err(ApiSurfaceError::UnexpectedItemKind {
                context: "variant",
                id: variant_id,
            });
        };

        let variant_path = join_path(enum_path, &variant_name);
        self.lines.insert(format!("variant {variant_path}"));
        match &variant.kind {
            VariantKind::Plain => {}
            VariantKind::Tuple(fields) => {
                for (index, field_id) in fields.iter().enumerate() {
                    if let Some(field_id) = field_id {
                        self.record_field(*field_id, &format!("{variant_path}::{index}"))?;
                    }
                }
            }
            VariantKind::Struct { fields, .. } => {
                for field_id in fields {
                    let field = self.item(*field_id)?.clone();
                    if !is_public_visibility(&field.visibility) {
                        continue;
                    }
                    let name = self.item_name(&field, "variant field")?;
                    self.record_field(*field_id, &join_path(&variant_path, name))?;
                }
            }
        }
        Ok(())
    }

    fn record_trait_items(
        &mut self,
        trait_path: &str,
        trait_: &Trait,
    ) -> Result<(), ApiSurfaceError> {
        for item_id in &trait_.items {
            self.record_associated_item(*item_id, trait_path)?;
        }
        Ok(())
    }

    fn record_inherent_items(
        &mut self,
        owner_path: &str,
        impls: &[Id],
    ) -> Result<(), ApiSurfaceError> {
        for impl_id in impls {
            let impl_item = self.item(*impl_id)?.clone();
            let ItemEnum::Impl(impl_) = impl_item.inner else {
                return Err(ApiSurfaceError::UnexpectedItemKind {
                    context: "impl",
                    id: *impl_id,
                });
            };
            if should_skip_impl(&impl_) {
                continue;
            }
            for item_id in &impl_.items {
                self.record_associated_item(*item_id, owner_path)?;
            }
        }
        Ok(())
    }

    fn record_associated_item(
        &mut self,
        item_id: Id,
        owner_path: &str,
    ) -> Result<(), ApiSurfaceError> {
        let item = self.item(item_id)?.clone();
        if !is_public_visibility(&item.visibility) {
            return Ok(());
        }

        let path = join_path(owner_path, self.item_name(&item, "associated item")?);
        match item.inner {
            ItemEnum::Function(function) => {
                self.lines.insert(format_function_line(&path, &function));
            }
            ItemEnum::AssocConst { type_, .. } => {
                self.lines
                    .insert(format!("const {path}: {}", format_type(&type_)));
            }
            ItemEnum::AssocType { type_, .. } => {
                let line = match type_ {
                    Some(type_) => format!("type {path} = {}", format_type(&type_)),
                    None => format!("type {path}"),
                };
                self.lines.insert(line);
            }
            _ => {}
        }
        Ok(())
    }

    fn item(&self, item_id: Id) -> Result<&Item, ApiSurfaceError> {
        self.krate
            .index
            .get(&item_id)
            .ok_or(ApiSurfaceError::MissingItem { id: item_id })
    }

    fn item_name<'b>(
        &self,
        item: &'b Item,
        context: &'static str,
    ) -> Result<&'b str, ApiSurfaceError> {
        item.name
            .as_deref()
            .ok_or(ApiSurfaceError::MissingItemName {
                context,
                id: item.id,
            })
    }
}

fn join_path(parent: &str, name: &str) -> String {
    format!("{parent}::{name}")
}

fn should_skip_impl(impl_: &Impl) -> bool {
    impl_.trait_.is_some() || impl_.is_synthetic || impl_.blanket_impl.is_some()
}

fn is_public_visibility(visibility: &Visibility) -> bool {
    matches!(visibility, Visibility::Public | Visibility::Default)
}
