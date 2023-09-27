// TODO: Config camelCase
use clippy_utils::diagnostics::span_lint_and_then;
use clippy_utils::get_trait_def_id;
use clippy_utils::sugg::DiagnosticExt;
use rustc_errors::Applicability;
use rustc_hir::*;
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::{declare_tool_lint, impl_lint_pass};

declare_clippy_lint! {
    /// ### What it does
    ///
    /// ### Why is this bad?
    ///
    /// ### Example
    /// ```rust
    /// // example code where clippy issues a warning
    /// ```
    /// Use instead:
    /// ```rust
    /// // example code which does not raise clippy warning
    /// ```
    #[clippy::version = "1.74.0"]
    pub CAMEL_CASE_JSON,
    correctness,
    "default lint description"
}

#[derive(Default)]
pub struct CamelCaseJson {
    json_schema: Option<def_id::DefId>,
}

impl_lint_pass!(CamelCaseJson => [CAMEL_CASE_JSON]);

impl<'tcx> LateLintPass<'tcx> for CamelCaseJson {
    fn check_crate(&mut self, cx: &LateContext<'tcx>) {
        static PATH: &[&str] = &["schemars", "JsonSchema"];

        self.json_schema = get_trait_def_id(cx, PATH);
    }

    fn check_item(&mut self, cx: &LateContext<'tcx>, item: &'tcx Item<'tcx>) {
        let is_struct_or_enum = matches!(item.kind, ItemKind::Struct(_, _) | ItemKind::Enum(_, _));

        if is_struct_or_enum {
            if let Some(json_schema_did) = &self.json_schema {
                let ty = cx.tcx.type_of(item.owner_id).instantiate_identity();

                if clippy_utils::ty::implements_trait(cx, ty, *json_schema_did, &[]) {
                    if !has_serde_rename_attr(cx, item.hir_id()) {
                        span_lint_and_then(
                            cx,
                            CAMEL_CASE_JSON,
                            item.span,
                            "сообщения для общения с внешним миром (через брокер сообщений) должны быть в camelCase",
                            |diag| {
                                diag.suggest_item_with_attr(
                                    cx,
                                    item.span,
                                    "добавьте атрибут serde",
                                    "#[serde(rename_all = \"camelCase\")]",
                                    Applicability::MachineApplicable,
                                );
                            },
                        );
                    }
                }
            }
        }
    }
}

fn has_serde_rename_attr(cx: &LateContext<'_>, hir_id: HirId) -> bool {
    cx.tcx.hir().attrs(hir_id).iter().any(|attr| {
        if attr.has_name(sym!(serde)) {
            if let Some(items) = attr.meta_item_list() {
                for item in items {
                    if let Some((ident, value)) = item.meta_item().and_then(|meta| {
                        if let Some(ident) = meta.ident()
                         && let Some(value) = meta.name_value_literal() {
                            return Some((ident, value))
                        } else {
                            None
                        }
                    }) {
                        let ident = ident.to_string();
                        let value = value.as_token_lit().to_string();

                        if ident.starts_with("rename_all") && value.starts_with("\"camelCase\"") {
                            return true;
                        }
                    }
                }
            }
        }
        false
    })
}
